;;; Derivatives of Regular Expressions

;;; A regular expression matcher based on regular expression derivatives. This
;;; is based loosely on Matt Might's regular expression derivative work.

;;; [1] http://matt.might.net/articles/implementation-of-regular-expression-matching-in-scheme-with-derivatives/

;;; [2] http://www.ccs.neu.edu/home/turon/re-deriv.pdf

(use-modules (srfi srfi-9))

(define-record-type dre-null-t          ; The empty language; the null set
  (dre-null-raw) dre-null?)

(define-record-type dre-empty-t         ; The empty string
  (dre-empty-raw) dre-empty?)

(define-record-type dre-chars-t         ; Set of characters
  (dre-chars-raw positive chars) dre-chars?
  (positive dre-chars-pos?)
  (chars dre-chars-set))

(define-record-type dre-concat-t        ; Concatenation; sequence
  (dre-concat-raw left right) dre-concat?
  (left dre-concat-left)
  (right dre-concat-right))

(define-record-type dre-or-t            ; Logical or; alternation; union
  (dre-or-raw left right) dre-or?
  (left dre-or-left)
  (right dre-or-right))

(define-record-type dre-closure-t       ; Kleene closure; repetition
  (dre-closure-raw regex) dre-closure?
  (regex dre-closure-regex))

(define-record-type dre-and-t           ; Logical and; intersection
  (dre-and-raw left right) dre-and?
  (left dre-and-left)
  (right dre-and-right))

(define-record-type dre-negation-t      ; Complement
  (dre-negation-raw regex) dre-negation?
  (regex dre-negation-regex))

(define (dre? re)
  (or (dre-null? re)
      (dre-empty? re)
      (dre-chars? re)
      (dre-concat? re)
      (dre-or? re)
      (dre-closure? re)
      (dre-and? re)
      (dre-negation? re)
      ))

;; Section 4.1 of re-deriv. This assumes the regular expressions are in
;; canonical form, as per the constructors below.

(define (dre-equal? left right)
  (cond
   ((not (dre? left))  #f)
   ((not (dre? right)) #f)
   ((and (dre-and? left) (dre-and? right))
    (let ((l1 (dre-and-left left))
          (l2 (dre-and-right left))
          (r1 (dre-and-left right))
          (r2 (dre-and-right right)))
      (or (and (dre-equal? l1 r1)
               (dre-equal? l2 r2))
          (and (dre-equal? l1 r2)
               (dre-equal? l2 r1)))))
   ((and (dre-or? left) (dre-or? right))
    (let ((l1 (dre-or-left left))
          (l2 (dre-or-right left))
          (r1 (dre-or-left right))
          (r2 (dre-or-right right)))
      (or (and (dre-equal? l1 r1)
               (dre-equal? l2 r2))
          (and (dre-equal? l1 r2)
               (dre-equal? l2 r1)))))
   (#t (equal? left right))
   ))

(define (dre-chars-member? re ch)
  (let ((is-member (member ch (dre-chars-set re))))
    (if (dre-chars-pos? re) is-member (not is-member)) ))

(define dre-null (dre-null-raw))

(define dre-empty (dre-empty-raw))

;; These constructors enforce canonical forms as per Section 4.1 of re-deriv.

(define (dre-chars chars) (dre-chars-raw #t chars))
(define (dre-chars-neg chars) (dre-chars-raw #f chars))

(define (dre-concat left right)
  (cond
   ((not (dre? left))  (error "not a regular expression: " left))
   ((not (dre? right)) (error "not a regular expression: " right))
   ((dre-null? left)   left)
   ((dre-null? right)  right)
   ((dre-empty? left)  right)
   ((dre-empty? right) left)
   ((dre-concat? left) (dre-concat-raw (dre-concat-left left)
                                       (dre-concat-raw (dre-concat-right left)
                                                       right)))
   (#t                 (dre-concat-raw left right))
   ))

(define (dre-or left right)
  (cond
   ((not (dre? left))       (error "not a regular expression: " left))
   ((not (dre? right))      (error "not a regular expression: " right))
   ((dre-null? left)        right)
   ((dre-null? right)       left)
   ((dre-equal? left right) left)
   ((and (dre-negation? left)
         (dre-null? (dre-negation-regex left))) left)
   ((dre-or? left)          (dre-or-raw (dre-or-left left)
                                        (dre-and-raw (dre-and-right left)
                                                     right)))
   (#t (dre-or-raw left     right))
   ))

(define (dre-closure regex)
  (cond
   ((not (dre? regex))   (error "not a regular expression: " regex))
   ((dre-null? regex)    dre-empty)
   ((dre-empty? regex)   dre-empty)
   ((dre-closure? regex) regex)
   (#t (dre-closure-raw  regex))
   ))

(define (dre-and left right)
  (cond
   ((not (dre? left))       (error "not a regular expression: " left))
   ((not (dre? right))      (error "not a regular expression: " right))
   ((dre-null? left)        left)
   ((dre-null? right)       right)
   ((dre-equal? left right) left)
   ((dre-and? left)         (dre-and-raw (dre-and-left left)
                                         (dre-and-raw (dre-and-right left)
                                                      right)))
   ((and (dre-negation? left)
         (dre-null? (dre-negation-regex left))) right)
   (#t                      (dre-and-raw left right))
   ))

(define (dre-negation regex)
  (if (dre-negation? regex)
      (dre-negation-regex regex)
      (dre-negation-raw regex))
  )

(define (nu re)
  (cond
   ((not (dre? re))    (error "not a regular expression: " re))
   ((dre-empty? re)    dre-empty)
   ((dre-chars? re)    dre-null)
   ((dre-null? re)     dre-null)
   ((dre-concat? re)   (dre-and (nu (dre-concat-left re))
                                (nu (dre-concat-right re))))
   ((dre-or? re)       (dre-or (nu (dre-or-left re))
                               (nu (dre-or-right re))))
   ((dre-closure? re)  dre-empty)
   ((dre-and? re)      (dre-and (nu (dre-and-left re))
                                (nu (dre-and-right re))))
   ((dre-negation? re) (if (dre-equal? (nu (dre-negation-regex re)) dre-null)
                           dre-empty
                           dre-null))
   ))

(define (delta re ch)
  (cond
   ((not (dre? re))    (error "not a regular expression: " re))
   ((dre-empty? re)    dre-null)
   ((dre-null? re)     dre-null)
   ((dre-chars? re)    (if (dre-chars-member? re ch) dre-empty dre-null))
   ((dre-concat? re)   (dre-or (dre-concat (delta (dre-concat-left re) ch)
                                           (dre-concat-right re))
                               (dre-concat (nu (dre-concat-left re))
                                           (delta (dre-concat-right re) ch))))
   ((dre-closure? re)  (dre-concat (delta (dre-closure-regex re) ch) re))
   ((dre-or? re)       (dre-or (delta (dre-or-left re) ch)
                               (delta (dre-or-right re) ch)))
   ((dre-and? re)      (dre-and (delta (dre-and-left re) ch)
                                (delta (dre-and-right re) ch)))
   ((dre-negation? re) (dre-negation (delta (dre-negation-regex re) ch)))
   ))

(define (dre-match-list? re list)
  (cond
   ((null? list) (dre-empty? (nu re)))
   (#t           (dre-match-list? (delta re (car list)) (cdr list)))
   ))

(define (dre-match? re str) (dre-match-list? re (string->list str)))

;;; http://matt.might.net/articles/parsing-regex-with-recursive-descent/

;; <regex> ::= <term> '|' <regex>
;;           | <term>
;;
;; <term> ::= { <factor> }
;;
;; <factor> ::= <base> { '*' }
;;
;; <base> ::= <char>
;;          | '(' <regex> ')'
;;          | '[' <set> ']'
;;
;; <set> ::= { <char> }
;;         | '^' { <char> }
;;
;; <char> ::= <character>
;;          | '\' <character>

(define (string->dre str)
  (let ((cur 0))

    (define (peek)
      (if (more) (string-ref str cur) (error "unexpected end of string")))
    (define (eat ch)
      (if (char=? ch (peek)) (set! cur (+ cur 1))
          (error "unexpected character:" ch (peek))))
    (define (next)
      (let ((ch (peek))) (eat ch) ch))
    (define (more)
      (< cur (string-length str)))

    (define (regex)
      (let ((trm (term)))
        (cond
         ((and (more) (char=? (peek) #\|))
          (eat #\|)
          (dre-or trm (regex)))
         (#t trm)
         )))

    (define (term)
      (let loop ((fact dre-empty))
        (cond
         ((and (more) (and (not (char=? (peek) #\)))
                           (not (char=? (peek) #\|))))
          (loop (dre-concat fact (factor))))
         (#t fact)
         )))

    (define (factor)
      (let loop ((b (base)))
        (cond
         ((and (more) (char=? (peek) #\*))
          (eat #\*)
          (loop (dre-closure b)))
         (#t b)
         )))

    (define (base)
      (cond
       ((char=? (peek) #\()
        ;; parenthesized sub-pattern
        (eat #\()
        (let ((r (regex)))
          (eat #\))
          r))
       ((char=? (peek) #\[)
        ;; character set
        (eat #\[)
        (let ((s (set)))
          (eat #\])
          s))
       (#t
        ;; single character
        (dre-chars (list (char))))
       ))

    (define (set)
      (cond
       ((char=? (peek) #\^)
        ;; negated set
        (eat #\^)
        (dre-chars-neg (chars)))
       (#t
        ;; positive set
        (dre-chars (chars)))
       ))

    (define (chars)
      (let loop ((ch '()))
        (if (char=? (peek) #\])
            ch
            (loop (cons (char) ch)))))

    (define (char)
      (cond
       ((char=? (peek) #\\)
        ;; quoted character
        (eat #\\)
        (next))
       (#t
        ;; unquoted character
        (next))
       ))

    (let ((r (regex)))
      (if (more)
          (error "incomplete regular expression:" (substring str cur))
          r))
    ))
