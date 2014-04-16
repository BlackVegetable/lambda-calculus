#lang racket

;;; Lambda Calculus Emulator
;;; 
;;; Primary Author: Devin Ekins
;;; Contact:        DevinJ.Ekins@gmail.com
;;; Special Thanks: Matt Flatt
;;; 
;;; 
;;; Execute program for instructions.

(require rackunit
         racket/pretty)

;; An ExprE is either:
;;   - (VarE symbol)
;;   - (FuncE symbol ExprE) ~ Play that FuncE music, white boy! ~ 
;;   - (AppE ExprE ExprE)

;; An ExprT is either:
;;   - (VarE symbol)
;;   - (FuncT symbol TypeT ExprT)
;;   - (AppE ExprT ExprT)

;; A TypeT is either:
;;   - symbol
;;   - ArrowT

;; An ArrowT is:
;;   - (TypeT -> TypeT)

(struct VarE (sym) #:transparent)
(struct FuncE (var expr) #:transparent)
(struct AppE (expr1 expr2) #:transparent)
(struct FuncT (var type expr) #:transparent) ; STLC
(struct TypeT (type) #:transparent) ; STLC
(struct ArrowT (type1 type2) #:transparent) ; STLC

;; VarE TypeT
(struct TypeBinding (var type)) ; STLC

;; user-parse (string --> ExprE)
(define (user-parse user-input)
  (parse ;(begin (apply-currying (string->list user-input)))
                (apply-currying (string->list user-input))))

;; typed-user-parse (string --> ExprT)
(define (typed-user-parse user-input)
  (typed-parse (string->list user-input)))

(define (char->symbol input)
  (string->symbol (string input)))

(check-equal? (char->symbol #\v)
              'v)

;; char-letter? : char -> boolean
;;  Recognize lowercase a through z
(define (char-letter? c)
  (<= (char->integer #\a) (char->integer c) (char->integer #\z)))

;; char-cap-letter? : char -> boolean
;;  Recognize uppercase A through Z
(define (char-cap-letter? c)
  (<= (char->integer #\A) (char->integer c) (char->integer #\Z)))

;; balance-parentheses : list-of-chars list-of-char integer
;;  Splits `chars` into a list of characters within an initial set of
;;  matching parentheses (balancing parentheses within those) and
;;  characters afterward. The intent is that `chars` starts out with
;;  the initial opening parentheses consumed (i.e., not at the start
;;  of the list). The `pre-accum` argument accumulates the characters
;;  within the parentheses in reverse order, and it should start out
;;  empty. The `depth` accumulator records the number of open parentheses
;;  awaiting a close parenthesis, and so it should start out as 1.
(define (balance-parentheses chars pre-accum depth)
  (cond
   [(empty? chars) (error "missing closing parenthesis")]
   [(equal? (first chars) #\))
    (if (= 1 depth)
        (values (reverse pre-accum) (rest chars))
        (balance-parentheses (rest chars) (cons #\) pre-accum) (sub1 depth)))]
   [(equal? (first chars) #\()
    (balance-parentheses (rest chars) (cons #\( pre-accum) (add1 depth))]
   [else
    (balance-parentheses (rest chars) (cons (first chars) pre-accum) depth)]))

(check-equal? (list (string->list "a(x(y))z") (string->list "def"))
              (call-with-values
                  (lambda () (balance-parentheses (string->list "a(x(y))z)def") empty 1))
                list))

;; build-app: ExprE ExprE char -> ExprE
(define (build-app function argument arg-first-char)
  ;; Just applying function to argument would make application
  ;; associate to the right, and we want application to associate
  ;; to the left. So, we have to look ahead for a parenthesis (with
  ;; would force a right associate), and rearrange if it's not there
  ;; and the argument is an application:
  (cond
   [(equal? #\( arg-first-char)
    ;; Parenthesized argument forces association to the right:
    (AppE function argument)]
   [(AppE? argument)
    ;; App to an application argument, so rearrange:
    (AppE (AppE function (AppE-expr1 argument))
          (AppE-expr2 argument))]
   [else
    ;; App to something else, so no need to rearrange:
    (AppE function argument)]))

;; make-arg-list (list of char -> list of char)
;; Takes a list of chars and returns a subset of that list that occurs
;; prior to a period character including that period (if it exists.)
(define (make-arg-list list-of-char)
  (cond
    [(empty? list-of-char) empty]
    [(equal? (first list-of-char) #\.) (list #\.)]
    [else (cons (first list-of-char) (make-arg-list (rest list-of-char)))]))

(check-equal? (make-arg-list (list #\λ #\a #\b #\c #\. #\d))
              (list #\λ #\a #\b #\c #\.))
(check-equal? (make-arg-list (list #\λ #\a #\b))
              (list #\λ #\a #\b))
(check-equal? (make-arg-list (list #\λ #\a #\.))
              (list #\λ #\a #\.))
                                   
;; Converts a list of function arguments terminated by a period into a list of curried single argument functions.
(define (rewrite-arity list-of-char is-first)
  (cond
    [(equal? #\. (first list-of-char)) empty]
    [is-first (cons (first list-of-char)(cons (second list-of-char) (cons #\. (rewrite-arity (rest (rest list-of-char)) #f))))]
    [else (cons #\λ (cons (first list-of-char) (cons #\. (rewrite-arity (rest list-of-char) #f))))]))

(check-equal? (rewrite-arity (list #\λ #\a #\b #\c #\.) #t)
              (list #\λ #\a #\. #\λ #\b #\. #\λ #\c #\.))
(check-equal? (rewrite-arity (list #\λ #\a #\.) #t)
              (list #\λ #\a #\.))

;; rest-x
;; applies rest x times.
(define (rest-x lyst x)
  (cond
    [(x . <= . 0) lyst]
    [(x . > . 0) (rest-x (rest lyst) (sub1 x))]))

(check-equal? (rest-x (list 1 2 3 4 5) 3)
              (list 4 5))
(check-equal? (rest-x (list 1 2 3 4 5) 0)
              (list 1 2 3 4 5))
(check-equal? (rest-x (list 1 2 3 4 5) -2)
              (list 1 2 3 4 5))
(check-equal? (rest-x (list 'a (list 2 3)) 1)
              (list (list 2 3)))

;; apply-currying
;; List of char -> list of char
;; Turns input containing multiple arity functions into equivalent input containing
;; only single-arity functions. Will not discover bad input.
(define (apply-currying list-of-char)
  (cond
    [(empty? list-of-char) empty]
    [else
     (define current (first list-of-char))
     (cond
       [(equal? current #\λ)
        (cond
          [(equal? (third list-of-char) #\.) (append (take list-of-char 3) (apply-currying (rest-x list-of-char 3)))]
          [else 
           (define args-list  (make-arg-list list-of-char))
           (define args-length (length args-list)) ; λabc. --> 5
           (define curried-args (rewrite-arity args-list #t)) ; λa.λb.λc.
           (append curried-args (apply-currying (rest-x list-of-char args-length)))])]
       [else (append (list current) (apply-currying (rest list-of-char)))])]))

(check-equal? (apply-currying (list #\( #\λ #\a #\b #\c #\. #\d #\) #\( #\λ #\e #\f #\. #\g #\h #\) #\i)) ; (λabc.d)(λef.gh)i
              (list #\( #\λ #\a #\. #\λ #\b #\. #\λ #\c #\. #\d #\) #\( #\λ #\e #\. #\λ #\f #\. #\g #\h #\) #\i)) ; (λa.λb.λc.d)(λe.λf.gh)i
(check-equal? (apply-currying (string->list "(λxyz.ab)(λgh.i)(λj.k)v"))
              (string->list "(λx.λy.λz.ab)(λg.λh.i)(λj.k)v"))
(check-equal? (apply-currying (string->list "λx.x"))
              (string->list "λx.x"))
             

;; <expr> = <id>
;;        | λ<id>.<expr>
;;        | <expr><expr>
;;        | (<expr>)
;; <id> = a | ... | z

;; parse (list of char --> ExprE)
;; Takes a string and converts it into lambda calculus objects.
;; Throws an error if it receives bad input. Its behavior is undefined
;; in the event of a meteorite impact.
(define (parse list-of-char)
  (cond
   [(empty? list-of-char) (error "invalid input")]
   [else
    (define current (first list-of-char))
    (cond
     [(equal? current #\λ)
      (if (or (empty? (rest list-of-char)) 
              (not (char-letter? (second list-of-char)))
              (not (equal? (third list-of-char) #\.))) ; Mulitple arity functions have been Curried by this point.
          (error "Invalid function given.")
          (FuncE (VarE (char->symbol (second list-of-char)))
                 (parse (rest (rest (rest list-of-char))))))]
     [(equal? current #\()
      (define-values (in-parens after-parens) (balance-parentheses (rest list-of-char) null 1))
      (cond
       [(null? after-parens)
        ;; A single expression with parentheses:
        (parse in-parens)]
       [else
        (define function (parse in-parens))
        (define argument (parse after-parens))
        (build-app function argument (first after-parens))])]
     [(char-letter? current)
      (cond
       [(empty? (rest list-of-char))
        ;; This is *only* character
        (VarE (char->symbol current))]
       [else
        (build-app (VarE (char->symbol current))
                   (parse (rest list-of-char))
                   (second list-of-char))])])]))

(check-equal? (user-parse "x")
              (VarE 'x))
(check-equal? (user-parse "λx.x")
              (FuncE (VarE 'x) (parse (list #\x))))
(check-equal? (user-parse "λx.x")
              (FuncE (VarE 'x) (VarE 'x)))
(check-equal? (user-parse "xy")
              (AppE (VarE 'x) (VarE 'y)))
(check-equal? (user-parse "(λx.xy)d")
              (AppE (FuncE (VarE 'x)(AppE (VarE 'x)(VarE 'y)))(VarE 'd)))
(check-equal? (user-parse "xyz")
              (AppE (AppE (VarE 'x) (VarE 'y)) (VarE 'z)))
(check-equal? (user-parse "(xy)z")
              (AppE (AppE (VarE 'x) (VarE 'y)) (VarE 'z)))
(check-equal? (user-parse "x(yz)")
              (AppE (VarE 'x) (AppE (VarE 'y) (VarE 'z))))
(check-equal? (user-parse "xλx.x")
              (AppE (VarE 'x) (FuncE (VarE 'x) (VarE 'x))))
(check-equal? (user-parse "λx.xy")
              (FuncE (VarE 'x) (AppE (VarE 'x) (VarE 'y))))
(check-equal? (user-parse "(λx.xy)z")
              (AppE (FuncE (VarE 'x) (AppE (VarE 'x) (VarE 'y)))
                    (VarE 'z)))

;; <expr> = <id>
;;        | λ<id>:<type>.<expr>
;;        | <expr><expr>
;;        | (<expr>)
;; <id> = a | ... | z
;; <type> = A | ... | Z
;;        | <type>-><type>

;; typed-parse (list of char --> ExprT)
;; Takes a string and converts it into simply typed lambda calculus objects.
;; Throws an error if it receives bad input. Its behavior is undefined
;; in the event of a plauge of Hobbits.
(define (typed-parse list-of-char)
  (cond
   [(empty? list-of-char) (error "invalid input")]
   [else
    (define current (first list-of-char))
    (cond
     [(equal? current #\λ)
      (cond
       [(or (empty? (rest list-of-char)) 
            (not (char-letter? (second list-of-char)))
            (empty? (rest (rest list-of-char)) )
            (not (equal? (third list-of-char) #\:)))
        (error "Invalid function given.")]
       [else
        (define-values (type rest-of-input)
          (parse-type (rest (rest (rest list-of-char)))))
        (if (not (equal? (first rest-of-input) #\.)) ; Currying is not implicit in STLC syntax.
            (error "Invalid function given.")
            (FuncT (VarE (char->symbol (second list-of-char)))
                   type
                   (typed-parse (rest rest-of-input))))])]
     [(equal? current #\()
      (define-values (in-parens after-parens) (balance-parentheses (rest list-of-char) null 1))
      (cond
       [(null? after-parens)
        ;; A single expression with parentheses:
        (typed-parse in-parens)]
       [else
        (define function (typed-parse in-parens))
        (define argument (typed-parse after-parens))
        (build-app function argument (first after-parens))])]
     [(char-letter? current)
      (cond
       [(empty? (rest list-of-char))
        ;; This is *only* character
        (VarE (char->symbol current))]
       [else
        (build-app (VarE (char->symbol current))
                   (typed-parse (rest list-of-char))
                   (second list-of-char))])])]))

(define (parse-type list-of-char)
  (cond
   [(and (not (empty? list-of-char))
         (char-cap-letter? (first list-of-char)))
    (maybe-arrow (TypeT (char->symbol (first list-of-char)))
                 (rest list-of-char))]
   [(and (not (empty? list-of-char))
         (equal? (first list-of-char) #\())
    (define-values (in-parens after-parens) (balance-parentheses (rest list-of-char) null 1))
    (define-values (type pre-rest-of-input) (parse-type in-parens))
    (unless (empty? pre-rest-of-input)
      (error "Invalid type given."))
    (maybe-arrow type after-parens)]
   [else
    (error "Invalid type given.")]))

(define (maybe-arrow type list-of-char)
  (cond
   [(and (not (empty? list-of-char))
         (equal? (first list-of-char) #\-)
         (not (empty? (rest list-of-char)))
         (equal? (second list-of-char) #\>))
    (define-values (result-type rest-of-input)
      (parse-type (rest (rest list-of-char))))
    (values (ArrowT type result-type)
            rest-of-input)]
   [else (values type list-of-char)]))

(check-equal? (typed-user-parse "x")
              (VarE 'x))
(check-equal? (typed-user-parse "λx:N.x")
              (FuncT (VarE 'x)(TypeT 'N) (typed-parse (list #\x))))
(check-equal? (typed-user-parse "λx:N.x")
              (FuncT (VarE 'x)(TypeT 'N) (VarE 'x)))
(check-equal? (typed-user-parse "xy")
              (AppE (VarE 'x) (VarE 'y)))
(check-equal? (typed-user-parse "(λx:S.xy)d")
              (AppE (FuncT (VarE 'x)(TypeT 'S)(AppE (VarE 'x)(VarE 'y)))(VarE 'd)))
(check-equal? (typed-user-parse "xyz")
              (AppE (AppE (VarE 'x) (VarE 'y)) (VarE 'z)))
(check-equal? (typed-user-parse "(xy)z")
              (AppE (AppE (VarE 'x) (VarE 'y)) (VarE 'z)))
(check-equal? (typed-user-parse "x(yz)")
              (AppE (VarE 'x) (AppE (VarE 'y) (VarE 'z))))
(check-equal? (typed-user-parse "xλx:N.x")
              (AppE (VarE 'x) (FuncT (VarE 'x)(TypeT 'N) (VarE 'x))))
(check-equal? (typed-user-parse "λx:B.xy")
              (FuncT (VarE 'x) (TypeT 'B)(AppE (VarE 'x) (VarE 'y))))
(check-equal? (typed-user-parse "(λx:N.xy)z")
              (AppE (FuncT (VarE 'x)(TypeT 'N) (AppE (VarE 'x) (VarE 'y)))
                    (VarE 'z)))
(check-equal? (typed-user-parse "(λx:N->B.xy)z")
              (AppE (FuncT (VarE 'x) (ArrowT (TypeT 'N) (TypeT 'B))
                           (AppE (VarE 'x) (VarE 'y)))
                    (VarE 'z)))
(check-equal? (typed-user-parse "(λx:N->B->C.xy)z")
              (AppE (FuncT (VarE 'x) (ArrowT (TypeT 'N)
                                             (ArrowT (TypeT 'B)
                                                     (TypeT 'C)))
                           (AppE (VarE 'x) (VarE 'y)))
                    (VarE 'z)))
(check-equal? (typed-user-parse "(λx:(N->B)->C.xy)z")
              (AppE (FuncT (VarE 'x) (ArrowT (ArrowT (TypeT 'N)
                                                     (TypeT 'B))
                                             (TypeT 'C))
                           (AppE (VarE 'x) (VarE 'y)))
                    (VarE 'z)))

;; replace-if-equal (VarE ExprE ExprE) -> ExprE
(define (replace-if-equal to-match candidate replacement)
  (cond
    [(VarE? candidate) (if (equal? to-match candidate)
                           replacement
                           candidate)]
    [(FuncE? candidate) (FuncE (FuncE-var candidate)
                               (replace-if-equal to-match (FuncE-expr candidate) replacement))]
    [(AppE? candidate) (AppE (replace-if-equal to-match (AppE-expr1 candidate) replacement) 
                             (replace-if-equal to-match (AppE-expr2 candidate) replacement))]))

(check-equal? (replace-if-equal (VarE 'a) (VarE 'a) (FuncE (VarE 'x)(VarE 'y)))
              (FuncE (VarE 'x)(VarE 'y)))
(check-equal? (replace-if-equal (VarE 'a) (VarE 'b) (AppE (VarE 'c)(VarE 'd)))
              (VarE 'b))
(check-equal? (replace-if-equal (VarE 'a) (FuncE (VarE 'b) (AppE (VarE 'b)(VarE 'c))) (VarE 'z))
              (FuncE (VarE 'b)(AppE (VarE 'b)(VarE 'c))))
(check-equal? (replace-if-equal (VarE 'f)(FuncE (VarE 's)(VarE 'f))(VarE 'g))
              (FuncE (VarE 's)(VarE 'g)))

;; consume (FuncE ExprE --> ExprE)
;; Takes a function and applies it with the expression as its argument.
;; The name "apply" was taken.
(define (consume fun arg)
  ; Find any matching symbols in the function argument and body.
  ; Replace them with the variable or function being applied to.
  (let* ([param (FuncE-var fun)]
         [body (FuncE-expr fun)])
    ; arg can either be a variable or a function.
    (replace-if-equal param body arg)))

;; Some example functions:
(define identity-func (FuncE (VarE 'id)(VarE 'id)))
(define first-func (FuncE (VarE 'fst)(FuncE (VarE 'scd)(VarE 'fst))))
(define second-func (FuncE (VarE 'fst) identity-func))

(check-equal? (consume identity-func (VarE 'y))
              (VarE 'y))
(check-equal? (consume identity-func identity-func)
              identity-func)
(check-equal? (consume first-func (VarE 'x))
              (FuncE (VarE 'scd)(VarE 'x)))
(check-equal? (consume (consume first-func (VarE 'x)) (VarE 'y))
              (VarE 'x))
(check-equal? (consume (consume second-func (VarE 'x)) (VarE 'y))
              (VarE 'y))

(define (FuncT->FuncE func)
  (FuncE (FuncT-var func)
         (FuncT-expr func)))

(check-equal? (FuncT->FuncE (FuncT (VarE 'x)(TypeT 'B)(AppE (FuncT (VarE 'y)(TypeT 'B)(VarE 'z))(VarE 'a))))
              (FuncE (VarE 'x)(AppE (FuncT (VarE 'y)(TypeT 'B)(VarE 'z))(VarE 'a))))

;; interp (ExprE environment --> ExprE)
;; Does not contain the rename operator, and may fail if duplicate names are used!
;; Used for both typed and untyped Lambda Calculus.  STLC should interp the same as untyped.
;; Only the type checker cares about the types.
(define (interp expr)
  (cond
    [(VarE? expr)(VarE (VarE-sym expr))]
    [(FuncE? expr)(FuncE (interp (FuncE-var expr)) 
                         (interp (FuncE-expr expr)))]
    [(FuncT? expr)(interp (FuncT->FuncE expr))]
    [(AppE? expr)
     (cond
       [(and (FuncT? (AppE-expr1 expr))(FuncT? (AppE-expr2 expr)))
        (consume (interp (FuncT->FuncE (AppE-expr1 expr)))
                 (interp (FuncT->FuncE (AppE-expr2 expr))))]
       [(FuncT? (AppE-expr1 expr))
        (consume (interp (FuncT->FuncE (AppE-expr1 expr)))
                 (interp (AppE-expr2 expr)))]
       [(FuncT? (AppE-expr2 expr))
        (AppE (interp (AppE-expr1 expr))
              (interp (FuncT->FuncE (AppE-expr2 expr))))]
       [(FuncE? (AppE-expr1 expr))
        (consume (interp (AppE-expr1 expr))
                 (interp (AppE-expr2 expr)))]
       [else (AppE (interp (AppE-expr1 expr))
                   (interp (AppE-expr2 expr)))])]
    [else (error "Failed to interp!")]))

(check-equal? (interp (VarE 'x))
              (VarE 'x))
(check-equal? (interp (FuncE (VarE 'x) (AppE (VarE 'x) (VarE 'y))))
              (FuncE (VarE 'x) (AppE (VarE 'x)(VarE 'y))))
(check-equal? (interp (AppE (VarE 'x)(VarE 'y)))
              (AppE (VarE 'x)(VarE 'y)))
(check-equal? (interp (AppE (FuncE (VarE 'x)(AppE (VarE 'x)(VarE 'y)))(VarE 'd)))
              (AppE (VarE 'd)(VarE 'y)))
(check-equal? (interp (AppE (FuncT (VarE 'x)(TypeT 'B)(AppE (VarE 'x)(VarE 'y)))(VarE 'd)))
              (AppE (VarE 'd)(VarE 'y)))

(define (lookup var vals)
  (cond
    [(empty? vals) (TypeT #f)]
    [else (if (equal? var (TypeBinding-var (first vals)))
              (TypeBinding-type (first vals))
              (lookup var (rest vals)))]))

;; expr->string (ExprE -> String)
;; Formats an ExprE into a String with parenthesis used to avoid function ambiguity.
(define (expr->string expr)
  (cond
    [(VarE? expr) (symbol->string (VarE-sym expr))]
    [(FuncE? expr)(string-append "(λ" (expr->string (FuncE-var expr)) "." (expr->string (FuncE-expr expr)) ")" )]
    [(FuncT? expr)(expr->string (FuncT->FuncE expr))]
    [(AppE? expr) (string-append (expr->string (AppE-expr1 expr)) (expr->string (AppE-expr2 expr)))]))
 
(check-equal? (expr->string (VarE 'x))
              "x")
(check-equal? (expr->string (AppE (VarE 'x) (VarE 'y)))
              "xy")
(check-equal? (expr->string (FuncE (VarE 'x) (AppE (VarE 'x)(VarE 'x))))
              "(λx.xx)")
(check-equal? (expr->string (AppE (FuncE (VarE 'x)(AppE (VarE 'x)(VarE 'y)))(VarE 'd)))
              "(λx.xy)d")

(define (type->string tp)
  (cond
    [(ArrowT? tp) 
     (define first-arrow? (ArrowT? (ArrowT-type1 tp)))
     (define first-void? (void? (ArrowT-type1 tp)))
     (define second-arrow? (ArrowT? (ArrowT-type2 tp)))
     (define second-void? (void? (ArrowT-type2 tp)))
     (string-append (if first-arrow? "(" "")
                    (if first-void? "BAD-TYPE" (type->string (ArrowT-type1 tp)))
                    (if first-arrow? ")" "")
                    "->"
                    (if second-arrow? "(" "")
                    (if second-void? "BAD-TYPE" (type->string (ArrowT-type2 tp)))
                    (if second-arrow? ")" ""))]
    [(TypeT? tp) (if (TypeT-type tp)
                     (symbol->string (TypeT-type tp))
                     "BAD-TYPE")]))

(check-equal? (type->string (TypeT 'B)) "B")
(check-equal? (type->string (ArrowT (TypeT 'B)(TypeT 'N))) "B->N")
(check-equal? (type->string (ArrowT (ArrowT (TypeT 'S)(TypeT 'B))(TypeT 'B))) "(S->B)->B")
(check-equal? (type->string (ArrowT (TypeT 'N)(TypeT #f))) "N->BAD-TYPE")


;; input-of
;; ArrowT -> type
;; An unexpectedly simple function.
(define (input-of arrow)
  (if (ArrowT? arrow)
      (ArrowT-type1 arrow)
      (error "input-of only applies to ArrowT types.")))

(check-equal? (input-of (ArrowT (TypeT 'A)(TypeT 'B)))
              (TypeT 'A))
(check-equal? (input-of (ArrowT 
                         (ArrowT (TypeT 'C)(TypeT 'D))
                         (TypeT 'E)))
              (ArrowT (TypeT 'C)(TypeT 'D)))
(check-equal? (input-of (ArrowT (TypeT 'A)
                                (ArrowT (TypeT 'B)
                                        (TypeT 'C))))
              (TypeT 'A))
(check-equal? (input-of (ArrowT
                         (ArrowT
                          (TypeT 'A)
                          (ArrowT
                           (TypeT 'B)
                           (TypeT 'C)))
                         (ArrowT
                          (ArrowT
                           (TypeT 'D)
                           (TypeT 'E))
                          (TypeT 'F))))
              (ArrowT
               (TypeT 'A)
               (ArrowT
                (TypeT 'B)
                (TypeT 'C))))
        
;; output-of
;; ArrowT -> type
;; An unexpectedly simple function.
(define (output-of arrow)
  (if (ArrowT? arrow)
      (ArrowT-type2 arrow)
      (error "output-of only applies to ArrowT types.")))

(check-equal? (output-of (ArrowT (TypeT 'A)(TypeT 'B)))
              (TypeT 'B))
(check-equal? (output-of (ArrowT 
                          (ArrowT (TypeT 'C)(TypeT 'D))
                          (TypeT 'E)))
              (TypeT 'E))
(check-equal? (output-of (ArrowT (TypeT 'A)
                                (ArrowT (TypeT 'B)
                                        (TypeT 'C))))
              (ArrowT (TypeT 'B)
                      (TypeT 'C)))
(check-equal? (output-of (ArrowT
                         (ArrowT
                          (TypeT 'A)
                          (ArrowT
                           (TypeT 'B)
                           (TypeT 'C)))
                         (ArrowT
                          (ArrowT
                           (TypeT 'D)
                           (TypeT 'E))
                          (TypeT 'F))))
              (ArrowT
               (ArrowT
                (TypeT 'D)
                (TypeT 'E))
               (TypeT 'F)))


;; typecheck (ExprT TypeEnv -> TypeT or #f)
(define (typecheck a tenv)
  (cond
    [(VarE? a) (lookup a tenv)]
    [(FuncT? a) (ArrowT (FuncT-type a)
                        (typecheck (FuncT-expr a)
                                   (cons (TypeBinding (FuncT-var a) (FuncT-type a))
                                         tenv)))]
    [(AppE? a) (cond
                 [(FuncT? (AppE-expr1 a))
                  (define func-type (FuncT-type (AppE-expr1 a)))
                  (cond
                    [(ArrowT? func-type)
                     (define input-type (ArrowT-type1 func-type))
                     (define output-type (ArrowT-type2 func-type))
                     (define arg-type (typecheck (AppE-expr2 a) tenv))
                     (if (equal? input-type arg-type)
                         output-type
                         (begin (display "\nTypes do not match. Expected input: ")
                                (display (type->string input-type))
                                (display " vs Actual input: ")
                                (display (type->string arg-type))
                                (TypeT #f)))]
                    [else (begin (display "\nNo type possible. [This equation contains a free variable: ")
                                 (display (expr->string (AppE-expr1 a)))
                                 (display "]")
                                 (TypeT #f))])]
                 [else (AppE-expr1 a)  ; We can't evaluate it, but we can still type-check it.
                  (define left-type (typecheck (AppE-expr1 a) tenv))
                  (define right-type (typecheck (AppE-expr2 a) tenv))
                  (cond
                    [(and (ArrowT? left-type)(equal? right-type (input-of left-type)))(output-of left-type)]
                    [else (begin (display "\nType-check failure. Type of left-side: ")
                                 (display (type->string left-type))
                                 (display " vs Type of right-side (argument): ")
                                 (display (type->string right-type))
                                 (display "\n")
                                 (TypeT #f))])])]))           

#| NOISY TESTS!
(check-equal? (typecheck (VarE 'x) empty) (TypeT #f)) 
(check-equal? (typecheck (typed-user-parse "(λx:(N->B)->S.x)(λv:N.yv)j") 
                         (list (TypeBinding (VarE 'y)(ArrowT (TypeT 'N)
                                                             (ArrowT (TypeT 'N)
                                                                     (TypeT 'B))))
                               (TypeBinding (VarE 'j)(TypeT 'N)))) 
              (TypeT #f))
(check-equal? (typecheck (typed-user-parse "(λx:(N->B)->S.k)(λv:N->N->B.y)j") 
                         (list (TypeBinding (VarE 'y)(ArrowT (TypeT 'N)
                                                             (TypeT 'B)))
                               (TypeBinding (VarE 'j)(TypeT 'N)))) 
              (TypeT 'S))
(check-equal? (typecheck (typed-user-parse "(λx:A->A.xx)(λx:A->A.xx)") empty)
                         (TypeT #f))
|#

;; Let's test the basic rules of type inference according to en.wikipedia.org/wiki/Simply_typed_lambda_calculus :
; 1. If x has type N in the context, we know that x has type N.
(check-equal? (typecheck (VarE 'x) (list (TypeBinding (VarE 'x) (TypeT 'N)))) 
              (TypeT 'N))

; 2. If, in a certain context with x having type N, e has type V, then, in the same context without x, λx:N.e has type N->V .
(check-equal? (typecheck (FuncT (VarE 'x)(TypeT 'N)(VarE 'e))(list (TypeBinding (VarE 'e)(TypeT 'V))))
              (ArrowT (TypeT 'N)(TypeT 'V)))

; 3. If, in a certain context, e has type N->T and d has type N then (ed) has type T.
(check-equal? (typecheck (AppE (VarE 'e)(VarE 'd))(list (TypeBinding (VarE 'e)(ArrowT (TypeT 'N)(TypeT 'T)))
                                                        (TypeBinding (VarE 'd)(TypeT 'N))))
              (TypeT 'T))

;; Now let's test some basic "closed terms":
; 1. The identify function or L-combinator.
(check-equal? (typecheck (FuncT (VarE 'x)(TypeT 'T)(VarE 'x)) empty)
              (ArrowT (TypeT 'T)(TypeT 'T)))

; 2. The K-combinator:
(check-equal? (typecheck (FuncT (VarE 'x)(TypeT 'O)(FuncT (VarE 'y)(TypeT 'T)(VarE 'x))) empty)
              (ArrowT (TypeT 'O)(ArrowT (TypeT 'T)(TypeT 'O))))

; 3. The S-combinator:
(check-equal? (typecheck (typed-user-parse "λx:T->U->V.λy:T->U.λz:T.xz(yz)") empty)
              (ArrowT
               (ArrowT
                (TypeT 'T)
                (ArrowT
                 (TypeT 'U)
                 (TypeT 'V)))
               (ArrowT
                (ArrowT
                 (TypeT 'T)
                 (TypeT 'U))
                (ArrowT
                 (TypeT 'T)
                 (TypeT 'V)))))
              
;; evaluate (String ->)
;; The main user function in this program.
;; Displays the intermediate and final results of a lambda calculus expression
;; given to it as a string.  The final result is also displayed in string format.
(define (evaluate user-input-string)
  (let* ([expr (user-parse user-input-string)]
         [result (interp expr)])
    (begin 
      (pretty-display "internal representation: ")
      (pretty-display expr)
      (pretty-display "\nreduced representation: ")
      (pretty-display result)
      (pretty-display "\nreduced form: ") 
      (pretty-display (expr->string result)))))

;; typed-evaluate (String ->)
;; The main user function for typed input in this program.
;; Currently preforms identically to the untyped "evaluate" but
;; allows for and ignores typed syntax.  Does not support implicit currying.
;; Does not yet perform type inference.
(define (typed-evaluate user-input-string)
  (let* ([expr (typed-user-parse user-input-string)]
         [result (interp expr)])
    (begin 
      (pretty-display "internal representation: ")
      (pretty-display expr)
      (pretty-display "\nreduced representation: ")
      (pretty-display result)
      (pretty-display "\nreduced form: ") 
      (pretty-display (expr->string result))
      (pretty-display "\nType information: ")
      (pretty-display (type->string (typecheck expr empty))))))



(pretty-display "\nWelcome to the Lambda Calculus Emulator.\nTo get started, call evaluate with a string representation of your expression.\n")
(pretty-display "Example: (evaluate \"(λx.xy)z\")\n")
(pretty-display "Hint: You can type the lambda character (λ) in Dr. Racket by hitting CTRL-\\\n")
(pretty-display "Variable identifiers must all be lowercase English characters.\nThis version of the emulator does not attempt renaming operators.")
(pretty-display "Thus, it is recommended that you use unique identifiers when the semantic intention is for two variables to be separate.\n")
(pretty-display "To use Simply Typed Lambda Calculus, use the typed-evaluate function instead.")
(pretty-display "Types are represented as uppercase English characters. (Multiple arity lambdas are not permitted in STLC.)")
(pretty-display "Example: (typed-evaluate \"(λx:A.λy:A.x)\")\n")

              
