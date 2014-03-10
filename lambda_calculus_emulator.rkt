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

(struct ExprE (content) #:transparent)
(struct VarE (sym) #:transparent)
(struct FuncE (var expr) #:transparent)
(struct AppE (expr1 expr2) #:transparent)

;; user-parse (string --> ExprE)
(define (user-parse user-input)
  (parse (string->list user-input)))

(define (char->symbol input)
  (string->symbol (string input)))

(check-equal? (char->symbol #\v)
              'v)

;; char-letter? : char -> boolean
;;  Recognize lowercase a through z
(define (char-letter? c)
  (<= (char->integer #\a) (char->integer c) (char->integer #\z)))

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
          [(equal? (third list-of-char) #\.) (cons (drop-right list-of-char 3) (apply-currying (take-right list-of-char 3)))]
          [else 
           (define args-list (make-arg-list list-of-char))
           (define args-length (length args-list)) ; λabc. --> 3
           (define curried-args (rewrite-arity args-list #t)) ; λa.λb.λc.
           (cons curried-args (apply-currying (take-right list-of-char args-length)))])]
       [else (cons current (apply-currying (rest list-of-char)))])]))

;; This test fails currently.  Currying needs some work. TODO
;(check-equal? (apply-currying (list #\( #\λ #\a #\b #\c #\. #\d #\) #\( #\λ #\e #\f #\. #\g #\h #\) #\i))
;                              (list #\( #\λ #\a #\. #\λ #\b #\. #\λ #\c #\. #\d #\) #\( #\λ #\e #\. #\λ #\f #\. #\g #\h #\) #\i))

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
              (not (equal? (third list-of-char) #\.))) ; Presently only single arity functions are permitted. 
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
    ; Can arg be an application that is in reduced form (contains only free variables)?
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

;; interp (ExprE environment --> ExprE)
;; Does not contain the rename operator, and may fail if duplicate names are used!
(define (interp expr)
  (cond
    [(VarE? expr)(VarE (VarE-sym expr))]
    [(FuncE? expr)(FuncE (interp (FuncE-var expr)) 
                         (interp (FuncE-expr expr)))]
    [(AppE? expr)
     (cond
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

;; expr->string (String ->)
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

;; expr->string (ExprE -> String)
;; Formats an ExprE into a String with parenthesis used to avoid function ambiguity.
(define (expr->string expr)
  (cond
    [(VarE? expr) (symbol->string (VarE-sym expr))]
    [(FuncE? expr)(string-append "(λ" (expr->string (FuncE-var expr)) "." (expr->string (FuncE-expr expr)) ")" )]
    [(AppE? expr) (string-append (expr->string (AppE-expr1 expr)) (expr->string (AppE-expr2 expr)))]))
 
(check-equal? (expr->string (VarE 'x))
              "x")
(check-equal? (expr->string (AppE (VarE 'x) (VarE 'y)))
              "xy")
(check-equal? (expr->string (FuncE (VarE 'x) (AppE (VarE 'x)(VarE 'x))))
              "(λx.xx)")
(check-equal? (expr->string (AppE (FuncE (VarE 'x)(AppE (VarE 'x)(VarE 'y)))(VarE 'd)))
              "(λx.xy)d")

(pretty-display "Welcome to the Lambda Calculus Emulator.\nTo get started, call evaluate with a string representation of your expression.\n")
(pretty-display "Example: (evaluate \"(λx.xy)z\")\n")
(pretty-display "Hint: You can type the lambda character (λ) in Dr. Racket by hitting CTRL-\\\n")
(pretty-display "Variable identifiers must all be lowercase English characters.\nThis version of the emulator does not attempt renaming operators.")
(pretty-display "Thus, it is recommended that you use unique identifiers when the semantic intention is for two variables to be separate.\n")
(pretty-display "Additionally, lambdas may only have one argument in this version -- which is technically consistent with lambda calculus")
(pretty-display "as it was initially defined.")

              
