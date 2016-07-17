;;; Derivatives of Regular Expressions

;;; A regular expression matcher based on regular expression derivatives. This
;;; is based loosely on Matt Might's regular expression derivative work.

;;; [1] http://matt.might.net/articles/implementation-of-regular-expression-matching-in-scheme-with-derivatives/

;;; [2] http://www.ccs.neu.edu/home/turon/re-deriv.pdf

(use-modules (srfi srfi-1))             ; Lists: fold, etc.
(use-modules (srfi srfi-9))             ; Record types

;; ---------------------------

(define-record-type set-t               ; A set structure
  (set-raw elts) set?
  (elts set-elts))

(define (unique lst)
  (let loop ([acc '()]
             [l lst])
    (if (null? l)
        (reverse acc)
        (loop (cons (car l) acc) (delete (car l) (cdr l))) )) )

(define (set . elts)
  (set-raw (unique elts)))

(define (list->set lst)
  (set-raw (unique lst)))

(define (set-union s1 s2)
  (cond
   [(not (set? s1)) (error "not a set:" s1)]
   [(not (set? s2)) (error "not a set:" s2)]
   [else (set-raw (unique (append (set-elts s1) (set-elts s2))))]
   ))

(define (set-intersection s1 s2)
  (cond
   [(not (set? s1)) (error "not a set:" s1)]
   [(not (set? s2)) (error "not a set:" s2)]
   [else (let* ([e1 (set-elts s1)]
                [e2 (set-elts s2)]
                [intersection (filter (lambda (elt) (member elt e1)) e2)])
           (set-raw (unique intersection)))]
   ))

(define (set-member? set elt)
  (if (set? set)
      (member elt (set-elts set))
      (error "not a set:" set)))

(define (set-empty? set)
  (if (set? set)
      (null? (set-elts set))
      (error "not a set:" set)))

(define (set-find set pred)
  (if (set? set)
      (find pred (set-elts set))
      (error "not a set:" set)))

;; ===========================

;; These constructors enforce canonical forms as per Section 4.1 of re-deriv.

;; ---------------------------

(define-record-type dre-null-t          ; The empty language; the null set
  (dre-null-raw) dre-null?)

(define dre-null (dre-null-raw))

;; ---------------------------

(define-record-type dre-empty-t         ; The empty string
  (dre-empty-raw) dre-empty?)

(define dre-empty (dre-empty-raw))

;; ---------------------------

(define-record-type dre-chars-t         ; Set of characters
  (dre-chars-raw positive chars) dre-chars?
  (positive dre-chars-pos?)
  (chars dre-chars-set))

(define (dre-chars chars)
  (dre-chars-raw #t (list->set chars)))

(define (dre-chars-neg chars)
  (dre-chars-raw #f (list->set chars)))

(define dre-chars-sigma (dre-chars-neg '()))

(define (dre-chars-member? re ch)
  (let ([is-member (set-member? (dre-chars-set re) ch)])
    (if (dre-chars-pos? re) is-member (not is-member)) ))

(define (dre-chars-empty? chars)
  (cond
   [(not (dre-chars? chars)) (error "not a character set:" chars)]
   [(dre-chars-pos? chars)   (set-empty? (dre-chars-set chars))]
   [else                     #f]
   ))

(define (dre-chars-intersection l r)
  (cond
   [(and (dre-chars-pos? l) (dre-chars-pos? r))
    ;; both positive: simple intersection
    (dre-chars-raw #t (set-intersection (dre-chars-set l) (dre-chars-set r)))]
   [(dre-chars-pos? l)
    ;; l positive, r negative: elts in l also in r by dre-chars-member?
    (dre-chars (fold (lambda (elt acc) (if (dre-chars-member? r elt)
                                           (cons elt acc)
                                           acc))
                     '()
                     (set-elts (dre-chars-set l))))]
   [(dre-chars-pos? r)
    ;; l negative, r positive: the mathematician's answer
    (dre-chars-intersection r l)]
   [else
    ;; both negative: slightly less simple union
    (dre-chars-raw #f (set-union (dre-chars-set l) (dre-chars-set r)))]
   ))

(define (dre-chars-choice chars)
  (cond
   [(not (dre-chars? chars))
    (error "not a character set:" chars)]
   [(and (dre-chars-pos? chars) (not (dre-chars-empty? chars)))
    (car (set-elts (dre-chars-set chars)))]
   [else (gensym)]                      ; Not a character
   ))

;; ---------------------------

(define-record-type dre-concat-t        ; Concatenation; sequence
  (dre-concat-raw left right) dre-concat?
  (left dre-concat-left)
  (right dre-concat-right))

(define (dre-concat left right)
  ;; (r ∙ s) ∙ t => r ∙ (s ∙ t)
  ;; ∅ ∙ r       => ∅
  ;; r ∙ ∅       => ∅
  ;; ϵ ∙ r       => r
  ;; r ∙ ϵ       => r
  (cond
   [(not (dre? left))  (error "not a regular expression: " left)]
   [(not (dre? right)) (error "not a regular expression: " right)]
   [(dre-null? left)   left]
   [(dre-null? right)  right]
   [(dre-empty? left)  right]
   [(dre-empty? right) left]
   [(dre-concat? left) (dre-concat-raw (dre-concat-left left)
                                       (dre-concat-raw (dre-concat-right left)
                                                       right))]
   [else               (dre-concat-raw left right)]
   ))

;; ---------------------------

(define-record-type dre-or-t            ; Logical or; alternation; union
  (dre-or-raw left right) dre-or?
  (left dre-or-left)
  (right dre-or-right))

(define (dre-or left right)
  ;; r + r       => r
  ;; r + s       => s + r (see dre-equal?)
  ;; (r + s) + t => r + (s + t)
  ;; ∅ + r       => r
  ;; ¬∅ + r      => ¬∅
  (cond
   [(not (dre? left))       (error "not a regular expression: " left)]
   [(not (dre? right))      (error "not a regular expression: " right)]
   [(dre-null? left)        right]
   [(dre-null? right)       left]
   [(dre-equal? left right) left]
   [(and (dre-negation? left)
         (dre-null? (dre-negation-regex left))) left]
   [(dre-or? left)          (dre-or-raw (dre-or-left left)
                                        (dre-and-raw (dre-and-right left)
                                                     right))]
   [else (dre-or-raw left   right)]
   ))

;; ---------------------------

(define-record-type dre-closure-t       ; Kleene closure; repetition
  (dre-closure-raw regex) dre-closure?
  (regex dre-closure-regex))

(define (dre-closure regex)
  ;; (r*)* => r*
  ;; ϵ*    => ϵ
  ;; ∅*    => ϵ
  (cond
   [(not (dre? regex))    (error "not a regular expression: " regex)]
   [(dre-null? regex)     dre-empty]
   [(dre-empty? regex)    dre-empty]
   [(dre-closure? regex)  regex]
   [else (dre-closure-raw regex)]
   ))

;; ---------------------------

(define-record-type dre-and-t           ; Logical and; intersection
  (dre-and-raw left right) dre-and?
  (left dre-and-left)
  (right dre-and-right))

(define (dre-and left right)
  ;; r & r       => r
  ;; r & s       => s & r (see dre-equal?)
  ;; (r & s) & t => r & (s & t)
  ;; ∅ & r       => ∅
  ;; ¬∅ & r      => r
  (cond
   [(not (dre? left))       (error "not a regular expression: " left)]
   [(not (dre? right))      (error "not a regular expression: " right)]
   [(dre-null? left)        left]
   [(dre-null? right)       right]
   [(dre-equal? left right) left]
   [(dre-and? left)         (dre-and-raw (dre-and-left left)
                                         (dre-and-raw (dre-and-right left)
                                                      right))]
   [(and (dre-negation? left)
         (dre-null? (dre-negation-regex left))) right]
   [else                    (dre-and-raw left right)]
   ))

;; ---------------------------

(define-record-type dre-negation-t      ; Complement
  (dre-negation-raw regex) dre-negation?
  (regex dre-negation-regex))

(define (dre-negation regex)
  ;; ¬(¬r) => r
  (if (dre-negation? regex)
      (dre-negation-regex regex)
      (dre-negation-raw regex))
  )

;; ===========================

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
   [(not (dre? left))  #f]
   [(not (dre? right)) #f]
   [(and (dre-and? left) (dre-and? right))
    (let ([l1 (dre-and-left left)]
          [l2 (dre-and-right left)]
          [r1 (dre-and-left right)]
          [r2 (dre-and-right right)])
      (or (and (dre-equal? l1 r1)
               (dre-equal? l2 r2))
          (and (dre-equal? l1 r2)
               (dre-equal? l2 r1))))]
   [(and (dre-or? left) (dre-or? right))
    (let ([l1 (dre-or-left left)]
          [l2 (dre-or-right left)]
          [r1 (dre-or-left right)]
          [r2 (dre-or-right right)])
      (or (and (dre-equal? l1 r1)
               (dre-equal? l2 r2))
          (and (dre-equal? l1 r2)
               (dre-equal? l2 r1))))]
   [else (equal? left right)]
   ))

;; ===========================

(define (nu re)
  (cond
   [(not (dre? re))    (error "not a regular expression: " re)]
   [(dre-empty? re)    dre-empty]
   [(dre-chars? re)    dre-null]
   [(dre-null? re)     dre-null]
   [(dre-concat? re)   (dre-and (nu (dre-concat-left re))
                                (nu (dre-concat-right re)))]
   [(dre-or? re)       (dre-or (nu (dre-or-left re))
                               (nu (dre-or-right re)))]
   [(dre-closure? re)  dre-empty]
   [(dre-and? re)      (dre-and (nu (dre-and-left re))
                                (nu (dre-and-right re)))]
   [(dre-negation? re) (if (dre-equal? (nu (dre-negation-regex re)) dre-null)
                           dre-empty
                           dre-null)]
   ))

(define (delta re ch)
  (cond
   [(not (dre? re))    (error "not a regular expression: " re)]
   [(dre-empty? re)    dre-null]
   [(dre-null? re)     dre-null]
   [(dre-chars? re)    (if (dre-chars-member? re ch) dre-empty dre-null)]
   [(dre-concat? re)   (dre-or (dre-concat (delta (dre-concat-left re) ch)
                                           (dre-concat-right re))
                               (dre-concat (nu (dre-concat-left re))
                                           (delta (dre-concat-right re) ch)))]
   [(dre-closure? re)  (dre-concat (delta (dre-closure-regex re) ch) re)]
   [(dre-or? re)       (dre-or (delta (dre-or-left re) ch)
                               (delta (dre-or-right re) ch))]
   [(dre-and? re)      (dre-and (delta (dre-and-left re) ch)
                                (delta (dre-and-right re) ch))]
   [(dre-negation? re) (dre-negation (delta (dre-negation-regex re) ch))]
   ))

(define (dre-match-list? re list)
  (cond
   [(null? list) (dre-empty? (nu re))]
   [else         (dre-match-list? (delta re (car list)) (cdr list))]
   ))

(define (dre-match? re str) (dre-match-list? re (string->list str)))

;; ===========================

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
  (let ([cur 0])

    (define (peek)
      (if (more) (string-ref str cur) (error "unexpected end of string")))
    (define (eat ch)
      (if (char=? ch (peek)) (set! cur (+ cur 1))
          (error "unexpected character:" ch (peek))))
    (define (next)
      (let ([ch (peek)]) (eat ch) ch))
    (define (more)
      (< cur (string-length str)))

    (define (regex)
      (let ([trm (term)])
        (cond
         [(and (more) (char=? (peek) #\|))
          (eat #\|)
          (dre-or trm (regex))]
         [else trm]
         )))

    (define (term)
      (let loop ([fact dre-empty])
        (cond
         [(and (more) (and (not (char=? (peek) #\)))
                           (not (char=? (peek) #\|))))
          (loop (dre-concat fact (factor)))]
         [else fact]
         )))

    (define (factor)
      (let loop ([b (base)])
        (cond
         [(and (more) (char=? (peek) #\*))
          (eat #\*)
          (loop (dre-closure b))]
         [else b]
         )))

    (define (base)
      (cond
       [(char=? (peek) #\()
        ;; parenthesized sub-pattern
        (eat #\()
        (let ([r (regex)])
          (eat #\))
          r)]
       [(char=? (peek) #\[)
        ;; character set
        (eat #\[)
        (let ([s (set)])
          (eat #\])
          s)]
       [(char=? (peek) #\.)
        ;; any character
        (eat #\.)
        (dre-chars-neg '(#\newline))]
       [else
        ;; single character
        (dre-chars (list (char)))]
       ))

    (define (set)
      (cond
       [(char=? (peek) #\^)
        ;; negated set
        (eat #\^)
        (dre-chars-neg (chars))]
       [else
        ;; positive set
        (dre-chars (chars))]
       ))

    (define (chars)
      (let loop ([ch '()])
        (if (char=? (peek) #\])
            ch
            (loop (cons (char) ch)))))

    (define (char)
      (cond
       [(char=? (peek) #\\)
        ;; quoted character
        (eat #\\)
        (next)]
       [else
        ;; unquoted character
        (next)]
       ))

    (let ([r (regex)])
      (if (more)
          (error "incomplete regular expression:" (substring str cur))
          r))
    ))

;; ===========================

;;; Section 4.2 Computing character set derivative classes

(define (C-hat r s)
  (let ([set-r (set-elts r)]
        [set-s (set-elts s)])
    (list->set
     (fold (lambda (elt-r acc-r)
             (append (fold (lambda (elt-s acc-s)
                             (cons (dre-chars-intersection elt-r elt-s)
                                   acc-s))
                           '()
                           set-s)
                     acc-r))
           '()
           set-r))))

(define (C re)
  (cond
   [(dre-empty? re)    (set dre-chars-sigma)]
   [(dre-chars? re)    (set re (dre-chars-neg (set-elts (dre-chars-set re))))]
   [(dre-concat? re)   (let ([r (dre-concat-left re)]
                             [s (dre-concat-right re)])
                         (if (dre-empty? (nu r))
                             (C-hat (C r) (C s))
                             (C r)))]
   [(dre-or? re)       (C-hat (C (dre-or-left re)) (C (dre-or-right re)))]
   [(dre-and? re)      (C-hat (C (dre-and-left re)) (C (dre-and-right re)))]
   [(dre-closure? re)  (C (dre-closure-regex re))]
   [(dre-negation? re) (C (dre-negation-regex re))]
   [(dre-null? re)     (set)]
   [else (error "unhelpful regular expression:" re)]
   ))

(define-record-type dre-transition-t    ; <state, input, state'> transition
  (dre-transition state input state') dre-transition?
  (state dre-transition-origin)
  (input dre-transition-input)
  (state' dre-transition-destination))

(define-record-type dre-machine-t       ; Finite state machine
  (dre-machine states start terminating transitions) dre-machine?
  (states dre-machine-states)
  (start dre-machine-start)
  (terminating dre-machine-terminating)
  (transitions dre-machine-transitions))

(define-record-type dre-state-t         ; A state in the machine
  (dre-state-raw n re) dre-state?
  (n dre-state-number)
  (re dre-state-regex))

(define dre-state
  (let ([state-count 0])
    (lambda (re)
      (set! state-count (+ state-count 1))
      (dre-state-raw state-count re))))

(define (dre->dfa r)

  (define (goto q S engine)
    (let* ([Q (car engine)]
           [d (cdr engine)]
           [c (dre-chars-choice S)]
           [qc (delta (dre-state-regex q) c)]
           [q' (set-find Q (lambda (q') (dre-equal? (dre-state-regex q') qc)))])
      (if q'
          (cons Q (set-union d (set (dre-transition q S q'))))
          (let ([q' (dre-state qc)])
            (explore (set-union Q (set q'))
                     (set-union d (set (dre-transition q S q')))
                     q')) )))

  (define (explore Q d q)
    (fold (lambda (S engine) (goto q S engine))
          (cons Q d)
          (set-elts (C (dre-state-regex q)))))

  (let* ([q0 (dre-state r)]
         [engine (explore (set q0) (set) q0)]
         [states (car engine)]
         [transitions (cdr engine)]
         [F (remove (lambda (q)
                      (not (dre-empty? (nu (dre-state-regex q)))))
                    (set-elts states))])
    (dre-machine states q0 F transitions)
    ))

;; ===========================

(define (display-dfa machine)

  (define (display-state st)
    (display (dre-state-number st)))

  (define (display-terminating sts)
    (if (null? sts)
        '()
        (begin (display-state (car sts))
               (display " ")
               (display-terminating (cdr sts)))))

  (define (display-chars chs)
    (if (dre-chars-pos? chs)
        (display (set-elts (dre-chars-set chs)))
        (begin (display "not ")
               (display (set-elts (dre-chars-set chs))))))

  (define (display-transition trans)
    (display-state (dre-transition-origin trans))
    (display " -- ")
    (display-chars (dre-transition-input trans))
    (display " -> ")
    (display-state (dre-transition-destination trans))
    )

  (define (display-transitions trans)
    (if (null? trans)
        '()
        (begin (display-transition (car trans))
               (newline)
               (display-transitions (cdr trans)))))

  (cond
   [(not (dre-machine? machine)) (error "not a DFA:" machine)]
   [else
    (display "Start: ")
    (display-state (dre-machine-start machine))
    (newline)
    (display "Final: ")
    (display-terminating (dre-machine-terminating machine))
    (newline)
    (display "Transitions:")
    (newline)
    (display-transitions (set-elts (dre-machine-transitions machine)))]
   ))

;; ===========================

(define t (string->dre "ab(c|d)*"))
(define u (dre->dfa t))
(display-dfa u)
