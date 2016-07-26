;;; Translated from https://github.com/tomerfiliba/tau/raw/master/earley3.py


(use-modules (srfi srfi-1))             ; List library
(use-modules (srfi srfi-9))             ; Record types
(use-modules (srfi srfi-9 gnu))         ; Custom record printers
(use-modules (srfi srfi-42))            ; List comprehensions

;;; --------------------------

(define-record-type production-t
  (production-raw terms) production?
  (terms production-terms))

(define (production . terms) (production-raw terms))

(define (production-length prod) (length (production-terms prod)))

(define (production=? lft rht)
  (and (production? lft) (production? rht)
       (equal? (production-terms lft) (production-terms rht))))

(set-record-type-printer!
 production-t
 (lambda (record port)
   (write-char #\[ port)
   (let loop ([elts (production-terms record)])
     (unless (null? elts)
       (display (car elts) port)
       (unless (null? (cdr elts)) (write-char #\space port))
       (loop (cdr elts))))
   (write-char #\] port)))

;;; --------------------------

(define-record-type rule-t
  (rule-raw name productions) rule?
  (name        rule-name)
  (productions rule-productions rule-productions!))

(define (rule name . prods)
  (unless (and (string? name)
               (every production? prods))
    (error "bad rule arguments:" name prods))
  (rule-raw name prods))

(define (rule-add-production! rule prod)
  (unless (and (rule? rule)
               (production? prod))
    (error "cannot add production:" rule prod))
  (rule-productions! rule (append (rule-productions rule) (list prod))))

(define (rule=? lft rht)
  (and (rule? lft) (rule? rht)
       (string=? (rule-name lft) (rule-name rht))
       (every production=? (rule-productions lft) (rule-productions rht))))

(set-record-type-printer!
 rule-t
 (lambda (rec port)
   (display (rule-name rec) port)
   (display " -> " port)
   (let loop ([prods (rule-productions rec)])
     (unless (null? prods)
       (display (car prods) port)
       (unless (null? (cdr prods)) (write-char #\| port))
       (loop (cdr prods))))))

;;; --------------------------

(define-record-type state-t
  (state-raw name production dot-index start-column end-column rules) state?
  (name         state-name)
  (production   state-production)
  (dot-index    state-dot)
  (start-column state-start)
  (end-column   state-end state-end!)
  (rules        state-rules))

(define (new-state name production dot-index start-column)
  (unless (and (string? name)
               (production? production)
               (number? dot-index)
               (column? start-column))
    (error "bad state arguments:" name production dot-index start-column))
  (state-raw name
             production
             dot-index
             start-column
             '()
             (filter rule? (production-terms production))))

(define (state=? lft rht)
  (and (state? lft) (state? rht)
       (string=? (state-name lft) (state-name rht))
       (production=? (state-production lft) (state-production rht))
       (= (state-dot lft) (state-dot rht))
       (column=? (state-start lft) (state-start rht))))

(define (state-completed? st)
  (and (state? st)
       (>= (state-dot st)
           (production-length (state-production st)))))

(define (state-next-term st)
  (unless (state? st) (error "not a state:" st))
  (if (state-completed? st)
      #f
      (list-ref (production-terms (state-production st)) (state-dot st))))

(define (insert pos elt lst)
  (append (take lst pos) (list elt) (drop lst pos)))

(set-record-type-printer!
 state-t
 (lambda (rec port)
   (let ([terms (production-terms (state-production rec))])
     (display "<" port)
     (display (state-name rec) port)
     (display " -> " port)
     (display (insert (state-dot rec) "$" terms) port)
     (display " [" port)
     (display (state-start rec) port)
     (display "-" port)
     (display (state-end rec) port)
     (display "]" port)
     (display ">" port))))

;;; --------------------------

(define-record-type column-t
  (column-raw index token visited unvisited) column?
  (index  column-index)
  (token  column-token)
  (visited column-visited-states column-visited-states!)
  (unvisited column-unvisited-states column-unvisited-states!))

(define (column index token)
  (column-raw index token '() '()))

(define (column=? lft rht)
  (and (column? lft) (column? rht) (= (column-index lft) (column-index rht))))

(define (column-states col)
  (append (column-visited-states col) (column-unvisited-states col)))

(define (column-add-state! col st)
  (unless (find (lambda (s) (state=? st s)) (column-states col))
    (column-unvisited-states! col (append (column-unvisited-states col) (list st)))
    (state-end! st col)))

(define (column-unvisited? col)
  (not (null? (column-unvisited-states col))))

(define (column-next-unvisited! col)
  (if (column-unvisited? col)
      (let* ([visited   (column-visited-states col)]
             [unvisited (column-unvisited-states col)]
             [next (car unvisited)])
        (column-unvisited-states! col (cdr unvisited))
        (column-visited-states! col (append visited (list next)))
        next)
      (error "no unvisited states available")))

(set-record-type-printer!
 column-t
 (lambda (rec port)
   (display (column-index rec) port)))

;;; --------------------------

(define (predict col rule)
  (let loop ([prods (rule-productions rule)])
    (unless (null? prods)
      (column-add-state! col (new-state (rule-name rule) (car prods) 0 col))
      (loop (cdr prods)))))

(define (complete col state)
  (when (state-completed? state)
    (let loop ([sts (column-states (state-start state))])
      (unless (null? sts)
        (let* ([st (car sts)]
               [term (state-next-term st)])
          (when (and (rule? term) (equal? (rule-name term) (state-name state)))
            (column-add-state! col (new-state (state-name st)
                                              (state-production st)
                                              (+ (state-dot st) 1)
                                              (state-start st)))))
        (loop (cdr sts))))))

(define (scan col state token)
  (when (and (column? col) (equal? token (column-token col)))
    (let ([name       (state-name state)]
          [production (state-production state)]
          [dot        (+ (state-dot state) 1)]
          [start-col  (state-start state)])
      (column-add-state! col (new-state name production dot start-col)))))

;;; --------------------------

(define GAMMA "GAMMA")

(define (visit-state col col')
  (let ([st (column-next-unvisited! col)])
    (cond
     [(state-completed? st)
      (complete col st)]
     [else
      (let ([term (state-next-term st)])
        (cond
         [(rule? term) (predict col term)]
         [col'         (scan col' st term)]
         ))]
     )))

(define (process-table table)
  (let outer ([i 0])
    (when (< i (length table))
      (let ([col (list-ref table i)])
        (let inner ()
          (when (column-unvisited? col)
            (visit-state col (if (< (+ i 1) (length table))
                                 (list-ref table (+ i 1))
                                 '()))
            (inner))))
      (outer (+ i 1)))))

(define (parse rule text)
  (let* ([tokens (cons '() text)]
         [table (list-ec (: tok (index i) tokens) (column i tok))]
         [col0 (list-ref table 0)])
    (column-add-state! col0 (new-state GAMMA (production rule) 0 col0))
    (process-table table)
    (let ([final (filter (lambda (st) (and (string=? (state-name st) GAMMA)
                                           (state-completed? st)))
                         (column-states (last table)))])
      (if (null? final) #f (car final)))))

;;; --------------------------

;; EXPR := SYM
;;       | EXPR OP EXPR
;;
;; SYM := 'a
;;
;; OP := '+
(define aexpr
  (let* ([sym  (rule "SYM" (production 'a))]
         [op   (rule "OP"  (production '+))]
         [expr (rule "EXPR")])
    (rule-add-production! expr (production sym))
    (rule-add-production! expr (production expr op expr))
    expr))
