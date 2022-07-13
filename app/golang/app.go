package main

import (
	"context"
	crand "crypto/rand"
	"crypto/sha512"
	"encoding/gob"
	"encoding/hex"
	"fmt"
	"html/template"
	"io"
	"log"
	"net/http"
	"net/url"
	"os"
	"os/signal"
	"path"
	"regexp"
	"strconv"
	"strings"
	"sync"
	"syscall"
	"time"

	"github.com/bradfitz/gomemcache/memcache"
	gsm "github.com/bradleypeabody/gorilla-sessions-memcache"
	"github.com/go-chi/chi/v5"
	_ "github.com/go-sql-driver/mysql"
	"github.com/gorilla/sessions"
	"github.com/jmoiron/sqlx"
	_ "github.com/mazrean/isucon-go-tools"
	isucache "github.com/mazrean/isucon-go-tools/cache"
	isudb "github.com/mazrean/isucon-go-tools/db"
	isuhttp "github.com/mazrean/isucon-go-tools/http"
	isupool "github.com/mazrean/isucon-go-tools/pool"
	"golang.org/x/sync/errgroup"
	"golang.org/x/sync/semaphore"
)

var (
	db    *sqlx.DB
	store *gsm.MemcacheStore
)

const (
	postsPerPage  = 20
	ISO8601Format = "2006-01-02T15:04:05-07:00"
	UploadLimit   = 10 * 1024 * 1024 // 10mb
)

type User struct {
	CreatedAt   time.Time `db:"created_at"`
	AccountName string    `db:"account_name"`
	Passhash    string    `db:"passhash"`
	ID          int       `db:"id"`
	Authority   int       `db:"authority"`
	DelFlg      int       `db:"del_flg"`
}

type Post struct {
	CreatedAt time.Time `db:"created_at"`
	Body      string    `db:"body"`
	Mime      string    `db:"mime"`
	CSRFToken string
	Imgdata   []byte `db:"imgdata"`
	ID        int    `db:"id"`
	UserID    int    `db:"user_id"`
}

type PostDetail struct {
	*Post
	User         *User
	CommentCount int
	Comments     []Comment
}

type Comment struct {
	User      User      `db:"user"`
	CreatedAt time.Time `db:"created_at"`
	Comment   string    `db:"comment"`
	ID        int       `db:"id"`
	PostID    int       `db:"post_id"`
	UserID    int       `db:"user_id"`
}

func init() {
	memdAddr := os.Getenv("ISUCONP_MEMCACHED_ADDRESS")
	if memdAddr == "" {
		memdAddr = "localhost:11211"
	}
	memcacheClient := memcache.New(memdAddr)
	store = gsm.NewMemcacheStore(memcacheClient, "iscogram_", []byte("sendagaya"))
	log.SetFlags(log.Ldate | log.Ltime | log.Lshortfile)
}

func dbInitialize() {
	isucache.AllPurge()

	sqls := []string{
		"DELETE FROM users WHERE id > 1000",
		"DELETE FROM posts WHERE id > 10000",
		"DELETE FROM comments WHERE id > 100000",
		"UPDATE users SET del_flg = 0",
		"UPDATE users SET del_flg = 1 WHERE id % 50 = 0",
	}

	for _, sql := range sqls {
		db.Exec(sql)
	}
}

func tryLogin(accountName, password string) *User {
	var u *User
	userCache.Range(func(i int, user *User) bool {
		if user.AccountName == accountName && user.DelFlg == 0 {
			u = user
			return false
		}

		return true
	})
	if u == nil {
		return nil
	}

	if calculatePasshash(u.AccountName, password) == u.Passhash {
		return u
	} else {
		return nil
	}
}

func validateUser(accountName, password string) bool {
	return regexp.MustCompile(`\A[0-9a-zA-Z_]{3,}\z`).MatchString(accountName) &&
		regexp.MustCompile(`\A[0-9a-zA-Z_]{6,}\z`).MatchString(password)
}

// 今回のGo実装では言語側のエスケープの仕組みが使えないのでOSコマンドインジェクション対策できない
// 取り急ぎPHPのescapeshellarg関数を参考に自前で実装
// cf: http://jp2.php.net/manual/ja/function.escapeshellarg.php
func escapeshellarg(arg string) string {
	return "'" + strings.Replace(arg, "'", "'\\''", -1) + "'"
}

func digest(src string) string {
	// opensslのバージョンによっては (stdin)= というのがつくので取る
	/*out, err := exec.Command("/bin/bash", "-c", `printf "%s" `+escapeshellarg(src)+` | openssl dgst -sha512 | sed 's/^.*= //'`).Output()
	if err != nil {
		log.Print(err)
		return ""
	}*/
	h := sha512.New()
	_, err := h.Write([]byte(src))
	if err != nil {
		log.Print(err)
		return ""
	}

	return strings.TrimSuffix(hex.EncodeToString(h.Sum(nil)), "\n")
}

func calculateSalt(accountName string) string {
	return digest(accountName)
}

func calculatePasshash(accountName, password string) string {
	return digest(password + ":" + calculateSalt(accountName))
}

func getSession(r *http.Request) *sessions.Session {
	session, _ := store.Get(r, "isuconp-go.session")

	return session
}

func getSessionUser(r *http.Request) User {
	session := getSession(r)
	uid, ok := session.Values["user_id"]
	if !ok || uid == nil {
		return User{}
	}

	u := &User{}

	userID, ok := uid.(int)
	if ok {
		u, ok = userCache.Load(userID)
	}

	if !ok {
		err := db.Get(&u, "SELECT * FROM `users` WHERE `id` = ?", uid)
		if err != nil {
			return User{}
		}

		return *u
	}

	return *u
}

func getFlash(w http.ResponseWriter, r *http.Request, key string) string {
	session := getSession(r)
	value, ok := session.Values[key]

	if !ok || value == nil {
		return ""
	} else {
		delete(session.Values, key)
		session.Save(r, w)
		return value.(string)
	}
}

type CommentInfo struct {
	Count    int
	Comments []Comment
}

var postCommentCache = isucache.NewAtomicMap[int, *CommentInfo]("post_comment")

const (
	initialGobPath = "./post_comment.gob"
	lastGobPath    = "./post_comment_last.gob"
)

func initPostCommentCache() error {
	_, err := os.Stat(initialGobPath)
	if err == nil {
		f, err := os.Open(initialGobPath)
		if err != nil {
			return err
		}
		defer f.Close()

		m := map[int]*CommentInfo{}
		err = gob.NewDecoder(f).Decode(&m)
		if err != nil {
			return err
		}

		postCommentCache.Purge()
		for k, v := range m {
			postCommentCache.Store(k, v)
		}

		return nil
	}

	postWithComments := []struct {
		PostID       int `db:"post_id"`
		CommentCount int `db:"count"`
	}{}
	err = db.Select(&postWithComments, "SELECT `post_id`, COUNT(*) AS `count` FROM `comments` GROUP BY `post_id`")
	if err != nil {
		return fmt.Errorf("failed to get post with comment count: %w", err)
	}

	m := make(map[int]*CommentInfo, len(postWithComments))
	eg := &errgroup.Group{}
	sw := semaphore.NewWeighted(100)

	for _, postWithComment := range postWithComments {
		postWithComment := postWithComment
		_ = sw.Acquire(context.Background(), 1)
		eg.Go(func() error {
			defer sw.Release(1)

			var comments []Comment
			err = db.Select(&comments, "SELECT `comments`.*, "+
				"`users`.`id` AS `user.id`, `users`.`passhash` AS `user.passhash`, `users`.`account_name` AS `user.account_name`, `users`.`authority` AS `user.authority`, `users`.`created_at` AS `user.created_at` "+
				"FROM `comments` JOIN `users` ON `comments`.`user_id`=`users`.`id` WHERE `comments`.`post_id` = ? ORDER BY `comments`.`created_at` DESC LIMIT 3", postWithComment.PostID)
			if err != nil {
				return fmt.Errorf("failed to get comments: %w", err)
			}

			// reverse
			for i, j := 0, len(comments)-1; i < j; i, j = i+1, j-1 {
				comments[i], comments[j] = comments[j], comments[i]
			}

			m[postWithComment.PostID] = &CommentInfo{
				Count:    postWithComment.CommentCount,
				Comments: comments,
			}
			postCommentCache.Store(postWithComment.PostID, &CommentInfo{
				Count:    postWithComment.CommentCount,
				Comments: comments,
			})

			return nil
		})
	}

	err = eg.Wait()
	if err != nil {
		return fmt.Errorf("failed in errgroup: %w", err)
	}

	f, err := os.Create(initialGobPath)
	if err != nil {
		log.Printf("failed to create gob file: %s", err)
		return nil
	}
	defer f.Close()

	err = gob.NewEncoder(f).Encode(m)
	if err != nil {
		log.Printf("failed to encode post comment cache: %s\n", err)
		return nil
	}

	return nil
}

var userCache = isucache.NewAtomicMap[int, *User]("user")

func initUserCache() error {
	userCache.Purge()

	users := []*User{}
	err := db.Select(&users, "SELECT * FROM `users`")
	if err != nil {
		return fmt.Errorf("failed to get users: %w", err)
	}

	for _, u := range users {
		userCache.Store(u.ID, u)
	}

	return nil
}

func makePosts(results []*Post, csrfToken string, allComments bool) ([]*PostDetail, error) {
	posts := make([]*PostDetail, 0, len(results))

	for _, p := range results {
		postDetail := &PostDetail{
			Post:         p,
			CommentCount: 0,
		}

		var ok bool
		postDetail.User, ok = userCache.Load(p.UserID)
		if !ok {
			postDetail.User = &User{}
			err := db.Get(postDetail.User, "SELECT * FROM `users` WHERE `id` = ?", p.UserID)
			if err != nil {
				return nil, err
			}
		}

		p.CSRFToken = csrfToken

		if postDetail.User.DelFlg != 0 {
			continue
		}

		commentInfo, ok := postCommentCache.Load(p.ID)
		if !ok {
			postDetail.CommentCount = 0
			postDetail.Comments = []Comment{}
		} else {
			postDetail.CommentCount = commentInfo.Count
			if !allComments {
				postDetail.Comments = commentInfo.Comments
			} else {
				err := db.Select(&postDetail.Comments, "SELECT `comments`.*, "+
					"`users`.`id` AS `user.id`, `users`.`passhash` AS `user.passhash`, `users`.`account_name` AS `user.account_name`, `users`.`authority` AS `user.authority`, `users`.`created_at` AS `user.created_at` "+
					"FROM `comments` JOIN `users` ON `comments`.`user_id`=`users`.`id` WHERE `comments`.`post_id` = ? ORDER BY `comments`.`created_at` ASC", p.ID)
				if err != nil {
					return nil, err
				}
			}
		}

		posts = append(posts, postDetail)
	}

	return posts, nil
}

func imageURL(p Post) string {
	ext := ""
	if p.Mime == "image/jpeg" {
		ext = ".jpg"
	} else if p.Mime == "image/png" {
		ext = ".png"
	} else if p.Mime == "image/gif" {
		ext = ".gif"
	}

	return "/image/" + strconv.Itoa(p.ID) + ext
}

func isLogin(u User) bool {
	return u.ID != 0
}

func getCSRFToken(r *http.Request) string {
	session := getSession(r)
	csrfToken, ok := session.Values["csrf_token"]
	if !ok {
		return ""
	}
	return csrfToken.(string)
}

func secureRandomStr(b int) string {
	k := make([]byte, b)
	if _, err := crand.Read(k); err != nil {
		panic(err)
	}
	return fmt.Sprintf("%x", k)
}

func getTemplPath(filename string) string {
	return path.Join("templates", filename)
}

func getInitialize(w http.ResponseWriter, r *http.Request) {
	isucache.AllPurge()

	dbInitialize()
	err := initPostCommentCache()
	if err != nil {
		log.Println(err)
	}

	err = initPostCache()
	if err != nil {
		log.Printf("Failed to initialize post cache: %s.", err.Error())
	}

	err = initUserCache()
	if err != nil {
		log.Printf("Failed to initialize user cache: %s.", err.Error())
	}

	err = initUserCommentCache()
	if err != nil {
		log.Printf("Failed to initialize user comment cache: %s.", err.Error())
	}

	w.WriteHeader(http.StatusOK)
}

var (
	loginTemplate = template.Must(template.ParseFiles(
		getTemplPath("layout.html"),
		getTemplPath("login.html")),
	)
)

func getLogin(w http.ResponseWriter, r *http.Request) {
	me := getSessionUser(r)

	if isLogin(me) {
		http.Redirect(w, r, "/", http.StatusFound)
		return
	}

	loginTemplate.Execute(w, struct {
		Me    User
		Flash string
	}{me, getFlash(w, r, "notice")})
}

func postLogin(w http.ResponseWriter, r *http.Request) {
	if isLogin(getSessionUser(r)) {
		http.Redirect(w, r, "/", http.StatusFound)
		return
	}

	u := tryLogin(r.FormValue("account_name"), r.FormValue("password"))

	if u != nil {
		session := getSession(r)
		session.Values["user_id"] = u.ID
		session.Values["csrf_token"] = secureRandomStr(16)
		session.Save(r, w)

		http.Redirect(w, r, "/", http.StatusFound)
	} else {
		session := getSession(r)
		session.Values["notice"] = "アカウント名かパスワードが間違っています"
		session.Save(r, w)

		http.Redirect(w, r, "/login", http.StatusFound)
	}
}

var registerTemplate = template.Must(template.ParseFiles(
	getTemplPath("layout.html"),
	getTemplPath("register.html")),
)

func getRegister(w http.ResponseWriter, r *http.Request) {
	if isLogin(getSessionUser(r)) {
		http.Redirect(w, r, "/", http.StatusFound)
		return
	}

	registerTemplate.Execute(w, struct {
		Me    User
		Flash string
	}{User{}, getFlash(w, r, "notice")})
}

func postRegister(w http.ResponseWriter, r *http.Request) {
	if isLogin(getSessionUser(r)) {
		http.Redirect(w, r, "/", http.StatusFound)
		return
	}

	accountName, password := r.FormValue("account_name"), r.FormValue("password")

	validated := validateUser(accountName, password)
	if !validated {
		session := getSession(r)
		session.Values["notice"] = "アカウント名は3文字以上、パスワードは6文字以上である必要があります"
		session.Save(r, w)

		http.Redirect(w, r, "/register", http.StatusFound)
		return
	}

	exist := false
	userCache.Range(func(i int, u *User) bool {
		if u.AccountName == accountName {
			exist = true
			return false
		}

		return true
	})

	if exist {
		session := getSession(r)
		session.Values["notice"] = "アカウント名がすでに使われています"
		session.Save(r, w)

		http.Redirect(w, r, "/register", http.StatusFound)
		return
	}

	query := "INSERT INTO `users` (`account_name`, `passhash`) VALUES (?,?)"
	result, err := db.Exec(query, accountName, calculatePasshash(accountName, password))
	if err != nil {
		log.Print(err)
		return
	}

	uid, err := result.LastInsertId()
	if err != nil {
		log.Print(err)
		return
	}

	u := User{}
	err = db.Get(&u, "SELECT * FROM `users` WHERE `id` = ?", uid)
	if err != nil {
		log.Print(err)
		return
	}
	userCache.Store(u.ID, &u)

	session := getSession(r)
	session.Values["user_id"] = int(uid)
	session.Values["csrf_token"] = secureRandomStr(16)
	session.Save(r, w)

	http.Redirect(w, r, "/", http.StatusFound)
}

func getLogout(w http.ResponseWriter, r *http.Request) {
	session := getSession(r)
	delete(session.Values, "user_id")
	session.Options = &sessions.Options{MaxAge: -1}
	session.Save(r, w)

	http.Redirect(w, r, "/", http.StatusFound)
}

var (
	postCache       = []*Post{}
	postCacheLocker = sync.RWMutex{}
)

func initPostCache() error {
	var posts []*Post
	err := db.Select(&posts, "SELECT * FROM `posts` ORDER BY `created_at` DESC")
	if err != nil {
		return err
	}

	postCacheLocker.Lock()
	postCache = posts
	postCacheLocker.Unlock()

	return nil
}

var (
	fmap = template.FuncMap{
		"imageURL": imageURL,
	}
	indexTemplate = template.Must(template.New("layout.html").Funcs(fmap).ParseFiles(
		getTemplPath("layout.html"),
		getTemplPath("index.html"),
		getTemplPath("posts.html"),
		getTemplPath("post.html"),
	))
)

var postsPool = isupool.NewSlice("posts", func() *[]*Post {
	posts := make([]*Post, 0, postsPerPage)
	return &posts
})

func getIndex(w http.ResponseWriter, r *http.Request) {
	me := getSessionUser(r)

	postCacheLocker.RLock()
	results := *postsPool.Get()
	for _, post := range postCache {
		results = append(results, post)

		if len(results) >= postsPerPage {
			break
		}
	}
	postCacheLocker.RUnlock()

	posts, err := makePosts(results, getCSRFToken(r), false)
	if err != nil {
		log.Print(err)
		return
	}

	indexTemplate.Execute(w, struct {
		Me        *User
		CSRFToken string
		Flash     string
		Posts     []*PostDetail
	}{&me, getCSRFToken(r), getFlash(w, r, "notice"), posts})
	postsPool.Put(&results)
}

var accountNameTemplate = template.Must(template.New("layout.html").Funcs(fmap).ParseFiles(
	getTemplPath("layout.html"),
	getTemplPath("user.html"),
	getTemplPath("posts.html"),
	getTemplPath("post.html"),
))

var userCommentCache = isucache.NewMap[int, int]("user_comment")

func initUserCommentCache() error {
	var users []struct {
		UserID int `db:"user_id"`
		Count  int `db:"count"`
	}
	err := db.Select(&users, "SELECT `user_id`, COUNT(*) AS `count` FROM `comments` GROUP BY `user_id`")
	if err != nil {
		return err
	}

	for _, user := range users {
		userCommentCache.Store(user.UserID, user.Count)
	}

	return nil
}

func getAccountName(w http.ResponseWriter, r *http.Request) {
	accountName := chi.URLParam(r, "accountName")
	var user *User
	userCache.Range(func(i int, u *User) bool {
		if u.AccountName == accountName && u.DelFlg == 0 {
			user = u
			return false
		}

		return true
	})
	if user == nil {
		w.WriteHeader(http.StatusNotFound)
		return
	}

	results := []*Post{}
	postIDs := []int{}
	postCacheLocker.RLock()
	for _, post := range postCache {
		if post.UserID == user.ID {
			results = append(results, post)

			if len(results) >= postsPerPage {
				break
			}
		}
	}
	postCacheLocker.RUnlock()

	posts, err := makePosts(results, getCSRFToken(r), false)
	if err != nil {
		log.Print(err)
		return
	}

	commentCount, ok := userCommentCache.Load(user.ID)
	if !ok {
		log.Print("userCommentCache not found")
		return
	}

	postCacheLocker.RLock()
	for _, post := range postCache {
		if post.UserID == user.ID {
			postIDs = append(postIDs, post.ID)
		}
	}
	postCacheLocker.RUnlock()
	postCount := len(postIDs)

	commentedCount := 0
	if postCount > 0 {
		for _, postID := range postIDs {
			commentInfo, ok := postCommentCache.Load(postID)
			if ok {
				commentedCount += commentInfo.Count
			}
		}
	}

	me := getSessionUser(r)

	accountNameTemplate.Execute(w, struct {
		User           *User
		Me             User
		Posts          []*PostDetail
		PostCount      int
		CommentCount   int
		CommentedCount int
	}{user, me, posts, postCount, commentCount, commentedCount})
}

var postsTemplate = template.Must(template.New("posts.html").Funcs(fmap).ParseFiles(
	getTemplPath("posts.html"),
	getTemplPath("post.html"),
))

func getPosts(w http.ResponseWriter, r *http.Request) {
	m, err := url.ParseQuery(r.URL.RawQuery)
	if err != nil {
		w.WriteHeader(http.StatusInternalServerError)
		log.Print(err)
		return
	}
	maxCreatedAt := m.Get("max_created_at")
	if maxCreatedAt == "" {
		return
	}

	t, err := time.Parse(ISO8601Format, maxCreatedAt)
	if err != nil {
		log.Print(err)
		return
	}

	postCacheLocker.RLock()
	results := *postsPool.Get()
	for _, post := range postCache {
		if post.CreatedAt.Before(t) {
			results = append(results, post)

			if len(results) >= postsPerPage {
				break
			}
		}
	}
	postCacheLocker.RUnlock()

	posts, err := makePosts(results, getCSRFToken(r), false)
	if err != nil {
		log.Print(err)
		return
	}

	if len(posts) == 0 {
		w.WriteHeader(http.StatusNotFound)
		return
	}

	postsTemplate.Execute(w, posts)
	postsPool.Put(&results)
}

var postIdTemplate = template.Must(template.New("layout.html").Funcs(fmap).ParseFiles(
	getTemplPath("layout.html"),
	getTemplPath("post_id.html"),
	getTemplPath("post.html"),
))

func getPostsID(w http.ResponseWriter, r *http.Request) {
	pidStr := chi.URLParam(r, "id")
	pid, err := strconv.Atoi(pidStr)
	if err != nil {
		w.WriteHeader(http.StatusNotFound)
		return
	}

	results := []*Post{}
	postCacheLocker.RLock()
	for _, post := range postCache {
		if post.ID == pid {
			results = append(results, post)

			if len(results) >= postsPerPage {
				break
			}
		}
	}
	postCacheLocker.RUnlock()

	posts, err := makePosts(results, getCSRFToken(r), true)
	if err != nil {
		log.Print(err)
		return
	}

	if len(posts) == 0 {
		w.WriteHeader(http.StatusNotFound)
		return
	}

	p := posts[0]

	me := getSessionUser(r)

	postIdTemplate.Execute(w, struct {
		Me   User
		Post *PostDetail
	}{me, p})
}

func postIndex(w http.ResponseWriter, r *http.Request) {
	me := getSessionUser(r)
	if !isLogin(me) {
		http.Redirect(w, r, "/login", http.StatusFound)
		return
	}

	if r.FormValue("csrf_token") != getCSRFToken(r) {
		w.WriteHeader(http.StatusUnprocessableEntity)
		return
	}

	file, header, err := r.FormFile("file")
	if err != nil {
		session := getSession(r)
		session.Values["notice"] = "画像が必須です"
		session.Save(r, w)

		http.Redirect(w, r, "/", http.StatusFound)
		return
	}

	ext := ""
	mime := ""
	if file != nil {
		// 投稿のContent-Typeからファイルのタイプを決定する
		contentType := header.Header["Content-Type"][0]
		if strings.Contains(contentType, "jpeg") {
			ext = "jpg"
			mime = "image/jpeg"
		} else if strings.Contains(contentType, "png") {
			ext = "png"
			mime = "image/png"
		} else if strings.Contains(contentType, "gif") {
			ext = "gif"
			mime = "image/gif"
		} else {
			session := getSession(r)
			session.Values["notice"] = "投稿できる画像形式はjpgとpngとgifだけです"
			session.Save(r, w)

			http.Redirect(w, r, "/", http.StatusFound)
			return
		}
	}

	tx, err := db.Beginx()
	if err != nil {
		log.Print(err)
		return
	}

	result, err := db.Exec("INSERT INTO `posts` (`user_id`, `body`, `mime`) VALUES (?,?,?)",
		me.ID,
		r.FormValue("body"),
		mime,
	)
	if err != nil {
		tx.Rollback()
		log.Print(err)
		return
	}

	pid, err := result.LastInsertId()
	if err != nil {
		log.Print(err)

		err := tx.Rollback()
		if err != nil {
			log.Print(err)
		}

		return
	}

	filePath := fmt.Sprintf("%s/%d.%s", imgDir, pid, ext)
	f, err := os.Create(filePath)
	if err != nil {
		log.Print(err)

		err := tx.Rollback()
		if err != nil {
			log.Print(err)
		}

		return
	}

	n, err := io.Copy(f, file)
	if err != nil {
		log.Print(err)

		err := tx.Rollback()
		if err != nil {
			log.Printf("%d bytes: %s\n", n, err)
		}

		return
	}

	if n > UploadLimit {
		err := tx.Rollback()
		if err != nil {
			log.Print(err)
		}

		session := getSession(r)
		session.Values["notice"] = "ファイルサイズが大きすぎます"
		session.Save(r, w)

		err = os.Remove(filePath)
		if err != nil {
			log.Print(err)
		}

		http.Redirect(w, r, "/", http.StatusFound)
		return
	}

	post := Post{}
	err = tx.Get(&post, "SELECT * FROM `posts` WHERE `id` = ?", pid)
	if err != nil {
		log.Print(err)

		err := tx.Rollback()
		if err != nil {
			log.Print(err)
		}

		http.Redirect(w, r, "/", http.StatusFound)
		return
	}

	postCacheLocker.Lock()
	newPostCache := make([]*Post, 0, len(postCache)+1)
	newPostCache = append(newPostCache, &post)
	newPostCache = append(newPostCache, postCache...)
	postCache = newPostCache
	postCacheLocker.Unlock()

	err = tx.Commit()
	if err != nil {
		log.Print(err)
		return
	}

	http.Redirect(w, r, "/posts/"+strconv.FormatInt(pid, 10), http.StatusFound)
}

const (
	imgDir = "../public/image"
)

func initImage() error {
	err := os.MkdirAll(imgDir, 0777)
	if err != nil && !os.IsExist(err) {
		return fmt.Errorf("failed to create image directory: %w", err)
	}

	var (
		posts  = make([]Post, 0, 1000)
		offset = 0
		first  = true
	)
	for ; first || len(posts) == 1000; offset += 1000 {
		err = db.Select(&posts, "SELECT `id`, `mime`, `imgdata` FROM `posts` LIMIT 1000 OFFSET ?", offset)
		if err != nil {
			return fmt.Errorf("failed to select posts: %w", err)
		}

		eg := &errgroup.Group{}

		for _, p := range posts {
			var ext string
			switch p.Mime {
			case "image/jpeg":
				ext = "jpg"
			case "image/png":
				ext = "png"
			case "image/gif":
				ext = "gif"
			default:
				continue
			}

			p := p

			eg.Go(func() error {
				f, err := os.Create(fmt.Sprintf("%s/%d.%s", imgDir, p.ID, ext))
				if err != nil {
					return fmt.Errorf("failed to create image file: %w", err)
				}
				defer f.Close()

				_, err = f.Write(p.Imgdata)
				if err != nil {
					return fmt.Errorf("failed to write image file: %w", err)
				}

				return nil
			})
		}

		err := eg.Wait()
		if err != nil {
			return fmt.Errorf("failed in errgroup: %w", err)
		}
	}

	return nil
}

func getImage(w http.ResponseWriter, r *http.Request) {
	pidStr := chi.URLParam(r, "id")
	pid, err := strconv.Atoi(pidStr)
	if err != nil {
		w.WriteHeader(http.StatusNotFound)
		return
	}

	post := Post{}
	err = db.Get(&post, "SELECT `mime`, `imgdata` FROM `posts` WHERE `id` = ?", pid)
	if err != nil {
		log.Print(err)
		return
	}

	ext := chi.URLParam(r, "ext")

	if ext == "jpg" && post.Mime == "image/jpeg" ||
		ext == "png" && post.Mime == "image/png" ||
		ext == "gif" && post.Mime == "image/gif" {
		w.Header().Set("Content-Type", post.Mime)
		_, err := w.Write(post.Imgdata)
		if err != nil {
			log.Print(err)
			return
		}
		return
	}

	w.WriteHeader(http.StatusNotFound)
}

func postComment(w http.ResponseWriter, r *http.Request) {
	me := getSessionUser(r)
	if !isLogin(me) {
		http.Redirect(w, r, "/login", http.StatusFound)
		return
	}

	if r.FormValue("csrf_token") != getCSRFToken(r) {
		w.WriteHeader(http.StatusUnprocessableEntity)
		return
	}

	postID, err := strconv.Atoi(r.FormValue("post_id"))
	if err != nil {
		log.Print("post_idは整数のみです")
		return
	}

	query := "INSERT INTO `comments` (`post_id`, `user_id`, `comment`) VALUES (?,?,?)"
	result, err := db.Exec(query, postID, me.ID, r.FormValue("comment"))
	if err != nil {
		log.Print(err)
		return
	}

	cid, err := result.LastInsertId()
	if err != nil {
		log.Printf("LastInsertId error:%v\n", err)
		return
	}

	comment := Comment{}
	err = db.Get(&comment, "SELECT * FROM `comments` WHERE `id` = ?", cid)
	if err != nil {
		log.Print(err)
		return
	}
	comment.User = me

	commentInfo, ok := postCommentCache.Load(postID)
	if !ok {
		commentInfo = &CommentInfo{}
	}

	comments := make([]Comment, 0, 3)
	if commentInfo.Count > 3 {
		comments = append(comments, commentInfo.Comments[1:]...)
	} else {
		comments = append(comments, commentInfo.Comments...)
	}
	comments = append(comments, comment)

	postCommentCache.Store(postID, &CommentInfo{
		Comments: comments,
		Count:    commentInfo.Count + 1,
	})

	num, ok := userCommentCache.Load(me.ID)
	if !ok {
		num = 0
	}
	userCommentCache.Store(me.ID, num+1)

	http.Redirect(w, r, fmt.Sprintf("/posts/%d", postID), http.StatusFound)
}

var adminBannedTemplate = template.Must(template.ParseFiles(
	getTemplPath("layout.html"),
	getTemplPath("banned.html")),
)

func getAdminBanned(w http.ResponseWriter, r *http.Request) {
	me := getSessionUser(r)
	if !isLogin(me) {
		http.Redirect(w, r, "/", http.StatusFound)
		return
	}

	if me.Authority == 0 {
		w.WriteHeader(http.StatusForbidden)
		return
	}

	var users []*User
	userCache.Range(func(key int, u *User) bool {
		if u.Authority == 0 && u.DelFlg == 0 {
			users = append(users, u)
		}

		return true
	})

	adminBannedTemplate.Execute(w, struct {
		Me        User
		CSRFToken string
		Users     []*User
	}{me, getCSRFToken(r), users})
}

func postAdminBanned(w http.ResponseWriter, r *http.Request) {
	me := getSessionUser(r)
	if !isLogin(me) {
		http.Redirect(w, r, "/", http.StatusFound)
		return
	}

	if me.Authority == 0 {
		w.WriteHeader(http.StatusForbidden)
		return
	}

	if r.FormValue("csrf_token") != getCSRFToken(r) {
		w.WriteHeader(http.StatusUnprocessableEntity)
		return
	}

	query := "UPDATE `users` SET `del_flg` = ? WHERE `id` = ?"

	err := r.ParseForm()
	if err != nil {
		log.Print(err)
		return
	}

	for _, id := range r.Form["uid[]"] {
		db.Exec(query, 1, id)

		uid, err := strconv.Atoi(id)
		if err != nil {
			log.Print(err)
			continue
		}
		user, ok := userCache.Load(uid)
		if !ok {
			continue
		}
		userCache.Store(uid, &User{
			ID:          user.ID,
			AccountName: user.AccountName,
			Passhash:    user.Passhash,
			CreatedAt:   user.CreatedAt,
			Authority:   user.Authority,
			DelFlg:      1,
		})
	}

	http.Redirect(w, r, "/admin/banned", http.StatusFound)
}

func main() {
	sig := make(chan os.Signal, 1)
	signal.Notify(sig, syscall.SIGTERM, syscall.SIGINT)
	go func() {
		<-sig
		f, err := os.Create(lastGobPath)
		if err != nil {
			log.Print(err)
			return
		}
		defer f.Close()

		m := map[int]*CommentInfo{}
		postCommentCache.Range(func(key int, value *CommentInfo) bool {
			m[key] = value
			return true
		})
		err = gob.NewEncoder(f).Encode(m)
		if err != nil {
			log.Print(err)
			return
		}

		os.Exit(0)
	}()

	_, err := os.Stat(lastGobPath)
	if err == nil {
		func() {
			f, err := os.Open(lastGobPath)
			if err != nil {
				log.Print(err)
				return
			}
			defer f.Close()

			m := map[int]*CommentInfo{}
			err = gob.NewDecoder(f).Decode(&m)
			if err != nil {
				log.Print(err)
				return
			}

			postCommentCache.Purge()
			for key, value := range m {
				postCommentCache.Store(key, value)
			}
		}()
	}

	host := os.Getenv("ISUCONP_DB_HOST")
	if host == "" {
		host = "localhost"
	}
	port := os.Getenv("ISUCONP_DB_PORT")
	if port == "" {
		port = "3306"
	}
	_, err = strconv.Atoi(port)
	if err != nil {
		log.Fatalf("Failed to read DB port number from an environment variable ISUCONP_DB_PORT.\nError: %s", err.Error())
	}
	user := os.Getenv("ISUCONP_DB_USER")
	if user == "" {
		user = "root"
	}
	password := os.Getenv("ISUCONP_DB_PASSWORD")
	dbname := os.Getenv("ISUCONP_DB_NAME")
	if dbname == "" {
		dbname = "isuconp"
	}

	dsn := fmt.Sprintf(
		"%s:%s@tcp(%s:%s)/%s?charset=utf8mb4&parseTime=true&loc=Local",
		user,
		password,
		host,
		port,
		dbname,
	)

	isudb.SetRetry(true)
	db, err = isudb.DBMetricsSetup(sqlx.Open)("mysql", dsn)
	if err != nil {
		log.Fatalf("Failed to connect to DB: %s.", err.Error())
	}
	defer db.Close()

	err = initPostCache()
	if err != nil {
		log.Fatalf("Failed to initialize post cache: %s.", err.Error())
	}

	err = initUserCache()
	if err != nil {
		log.Fatalf("Failed to initialize user cache: %s.", err.Error())
	}

	err = initUserCommentCache()
	if err != nil {
		log.Fatalf("Failed to initialize user comment cache: %s.", err.Error())
	}

	r := chi.NewRouter()

	r.Get("/initialize", getInitialize)
	r.Get("/login", getLogin)
	r.Post("/login", postLogin)
	r.Get("/register", getRegister)
	r.Post("/register", postRegister)
	r.Get("/logout", getLogout)
	r.Get("/", getIndex)
	r.Get("/posts", getPosts)
	r.Get("/posts/{id}", getPostsID)
	r.Post("/", postIndex)
	r.Get("/image/{id}.{ext}", getImage)
	r.Post("/comment", postComment)
	r.Get("/admin/banned", getAdminBanned)
	r.Post("/admin/banned", postAdminBanned)
	r.Get(`/@{accountName:[a-zA-Z]+}`, getAccountName)
	r.Get("/*", func(w http.ResponseWriter, r *http.Request) {
		http.FileServer(http.Dir("../public")).ServeHTTP(w, r)
	})

	log.Fatal(isuhttp.ListenAndServe(":8080", r))
}
