;;; The Earley Parsing Algorithm, Dustin Mitchell, 2001
;;;
;;; Practical Earley Parsing, John Aycock and R. Nigel Horspool, 2002.

(use-modules (srfi srfi-1))             ; List library
(use-modules (srfi srfi-9))             ; Record types

;;; --------------------------

(define-record-type rule-t
  (rule-raw name production) rule?
  (name rule-name)
  (production rule-production))

(define (rule name production)
  (unless (and (string? name)
               (list? production)
               (every (lambda (t) (or (string? t) (symbol? t))) production))
    (error "bad rule:" name production))
  (rule-raw name production))

(define terminal?    symbol?)
(define nonterminal? string?)

(define terminal=? eq?)
(define nonterminal=? string=?)

(define rule=? equal?)

(define (rule-length r)
  (unless (rule? r) (error "not a rule:" r))
  (length (rule-production r)))

(define (rule-named? r str)
  (unless (rule? r) (error "not a rule:" r))
  (unless (string? str) (error "bad rule-name:" str))
  (string=? (rule-name r) str))

(define (rule-term r n)
  (unless (rule? r) (error "not a rule:" r))
  (if (< n (rule-length r))
      (list-ref (rule-production r) n)
      (error "term out of range:" r n)))

;;; --------------------------

;;; An Earley item
(define-record-type item-t
  (item-raw rule pos start trees) item?
  (rule  item-rule)
  (pos   item-pos)
  (start item-start)
  (trees item-trees item-trees!))

(define (item rule n start trees)
  (unless (and (rule? rule)
               (number? n)
               (state? start))
    (error "bad item:" rule start))
  (item-raw rule n start trees))

(define (item=? st1 st2)
  (and (rule=? (item-rule st1) (item-rule st2))
       (= (item-pos st1) (item-pos st2))
       (state=? (item-start st1) (item-start st2))
       (equal? (item-trees st1) (item-trees st2))))

(define (item-name st)
  (unless (item? st) (error "not a item:" st))
  (rule-name (item-rule st)))

(define (item-named? st str)
  (unless (item? st) (error "not a item:" st))
  (rule-named? (item-rule st) str))

(define (next st)
  (unless (item? st) (error "not a item:" st))
  (if (item-final? st)
      (error "cannot get next symbol:" st)
      (rule-term (item-rule st) (item-pos st))))

(define (item-final? st)
  (unless (item? st) (error "not a item:" st))
  (>= (item-pos st) (rule-length (item-rule st))))

(define (item-terminal? st)
  (and (item? st)
       (not (item-final? st))
       (terminal? (next st))))

(define (item-nonterminal? st)
  (and (item? st)
       (not (item-final? st))
       (nonterminal? (next st))))

;; (define (append-tree! st tre)
;;   (unless (item? st) (error "bad item:" st))
;;   (item-trees! st (append (item-trees st) (list tre))))

;;; --------------------------

(define-record-type state-t
  (state-raw id item-set) state?
  (id state-id)
  (item-set state-items state-items!))

(define state
  (let ([ctr 0])
    (lambda sts
      (unless (every item? sts) (error "bad state:" sts))
      (set! ctr (+ ctr 1))
      (state-raw ctr sts))))

(define (state=? ss1 ss2)
  (= (state-id ss1) (state-id ss2)))

(define (state-empty? ss)
  (null? (state-items ss)))

(define (append-item! ss st)
  (unless (and (state? ss)
               (item? st))
    (error "cannot append item:" ss st))
  (state-items! ss (append (state-items ss) (list st))))

;;; --------------------------

(define GAMMA "GAMMA")

(define (predict grammar ss st)
  ;; If st is nonterminal, and its next symbol is N, then for each rule <N ->
  ;; alpha> in the grammar, add the item <N -ss-> .alpha> to ss.
  ;;
  ;; Create each new item with an empty list.
  (unless (every rule? grammar) (error "bad grammar:" grammar))
  (unless (state? ss) (error "bad state:" ss))
  (unless (item-nonterminal? st) (error "bad item:" st))
  (let ([nxt (next st)])
    (map (lambda (r) (item r 0 ss '()))
         (filter (lambda (r) (rule-named? r nxt)) grammar))))

(define (complete st)
  ;; If st in final, then for each 'parent' item in (item-start st) with the
  ;; dot immediately preceeding N, add a similar item to [this state] with
  ;; the dot moved to the right.
  ;;
  ;; Each new item carries a copy of the parent item's list, to which is
  ;; appended the list for s as a single element.
  (unless (item-final? st) (error "bad item:" st))
  (let* ([name (item-name st)]
         [ssp (item-start st)]
         [itemsp (state-items ssp)])
    (map (lambda (s) (item (item-rule s)
                            (+ (item-pos s) 1)
                            (item-start s)
                            (append (item-trees s) (list (list name (item-trees st))))))
         (filter (lambda (s) (and (item-nonterminal? s)
                                  (nonterminal=? (next s) name))) itemsp))))

(define (predict/complete grammar ss st)
  (cond [(item-nonterminal? st) (predict grammar ss st)]
        [(item-final? st)       (complete st)]
        [else                    '()]))

(define (expand! grammar ss st)
  (unless (find (lambda (s) (item=? st s)) (state-items ss))
    (append-item! ss st)
    (for-each (lambda (s) (expand! grammar ss s)) (predict/complete grammar ss st))
    ss))

(define (scan grammar ss trm)
  ;; For all s in state ss, if s is terminal and its next symbol is trm,
  ;; then create a new state ssn and add a copy of s to ssn with the dot
  ;; moved one symbol to the right.
  ;;
  ;; Append trm to the list for the new item.
  (let ([matches (filter (lambda (s) (and (item-terminal? s)
                                          (terminal=? (next s) trm)))
                         (state-items ss))]
        [ssn (state)])
    (for-each (lambda (s) (expand! grammar ssn (item (item-rule s)
                                                     (+ (item-pos s) 1)
                                                     (item-start s)
                                                     (append (item-trees s) (list trm)))))
              matches)
    ssn))

(define (parse grammar start-symbol input)
  (unless (and (every rule? grammar)
               (string? start-symbol))
    (error "bad grammar:" grammar start-symbol))
  (unless (every terminal? input) "bad input:" input)
  (let* ([ss0 (state)]
         [r0  (rule GAMMA (list start-symbol 'END))]
         [s0  (item r0 0 ss0 '())])
    (expand! grammar ss0 s0)
    (let loop ([current ss0]
               [in      input])
      (if (null? in)
          (scan grammar current 'END)
          (begin
            (loop (scan grammar current (car in)) (cdr in)))))))
(define recognize parse)

;;; --------------------------

;; EXPR := SYM
;;       | EXPR OP EXPR
;;
;; SYM := 'a
;;
;; OP := '+
(define aexp (list (rule "EXPR" '("SYM"))
                   (rule "EXPR" '("EXPR" "OP" "EXPR"))
                   (rule "SYM"  '(a))
                   (rule "OP"   '(+))))

;; Ambiguous grammar
(define amb (list (rule "E" '("T"))
                  (rule "E" '("E" + "E"))
                  (rule "T" '("F"))
                  (rule "T" '("T" * "T"))
                  (rule "F" '(a))))
