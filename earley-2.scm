;;; The Earley Parsing Algorithm, Dustin Mitchell, 2001
;;;
;;; Practical Earley Parsing, John Aycock and R. Nigel Horspool, 2002.
;;;
;;; Earley Parsing Explained http://loup-vaillant.fr/tutorials/earley-parsing/
;;;
;;; (Finding nullable symbols) https://github.com/jeffreykegler/kollos/blob/master/notes/misc/loup2.md

(use-modules (srfi srfi-1))             ; List library
(use-modules (srfi srfi-9))             ; Record types
(use-modules (srfi srfi-9 gnu))         ; Custom record printers

(define (insert pos elt lst)
  (append (take lst pos) (list elt) (drop lst pos)))

;;; --------------------------

(define terminal?    symbol?)
(define nonterminal? string?)

(define terminal=? eq?)
(define nonterminal=? string=?)

;;; --------------------------

(define-record-type rule-t
  (rule-raw name production) rule?
  (name rule-name)
  (production rule-production))

;;; An Earley item
(define-record-type item-t
  (item-raw rule pos start tree) item?
  (rule  item-rule)
  (pos   item-pos)
  (start item-start)
  (tree item-tree item-tree!))

;;; The state of an Earley parse: a set of items
(define-record-type state-t
  (state-raw id item-set) state?
  (id state-id)
  (item-set state-items state-items!))

;;; --------------------------

(define (rule name production)
  (unless (and (string? name)
               (list? production)
               (every (lambda (t) (or (terminal? t) (nonterminal? t))) production))
    (error "bad rule:" name production))
  (rule-raw name production))

(define rule=? equal?)

(define (rule-length r)
  (unless (rule? r) (error "not a rule:" r))
  (length (rule-production r)))

(define (rule-named? r str)
  (unless (rule? r) (error "not a rule:" r))
  (unless (string? str) (error "bad rule-name:" str))
  (string=? (rule-name r) str))

(define (rule-empty? r)
  (null? (rule-production r)))

(define (rule-term r n)
  (unless (rule? r) (error "not a rule:" r))
  (if (< n (rule-length r))
      (list-ref (rule-production r) n)
      (error "term out of range:" r n)))

(define (rule-nonterminals r)
  (filter nonterminal? (rule-production r)))

(define (rule-contains? r nonterm)
  (find (lambda (p) (nonterminal=? nonterm p)) (rule-nonterminals r)))

;;; --------------------------

(define (nullable grammar)
  (let* ([initial (map rule-name (filter rule-empty? grammar))])
    (let loop ([nbl initial]
               [work initial])
      (if (null? work)
          nbl
          (let* ([sym (car work)]
                 [nullable? (lambda (s) (member s nbl))]
                 ;; work-rules = rules containing sym in RHS
                 [work-rules (filter (lambda (r) (rule-contains? r sym)) grammar)]
                 ;; poss = names of work-rules whose LHS are not known to be
                 ;; nullable, and whose RHS are all nullable; i.e. a new
                 ;; nullable symbol.
                 [poss (map rule-name
                            (filter (lambda (r)
                                      (and (not (nullable? (rule-name r)))
                                           (every nullable? (rule-nonterminals r))))
                                    work-rules))])
            (loop (append nbl poss) (append (cdr work) poss)))))))

;;; --------------------------

(define (item rule n start tree)
  (unless (and (rule? rule)
               (number? n)
               (state? start))
    (error "bad item:" rule start))
  (item-raw rule n start tree))

(define (item=? st1 st2)
  (and (rule=? (item-rule st1) (item-rule st2))
       (= (item-pos st1) (item-pos st2))
       (state=? (item-start st1) (item-start st2))
       (equal? (item-tree st1) (item-tree st2))))

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

(set-record-type-printer!
 item-t
 (lambda (rec port)
   (let ([terms (rule-production (item-rule rec))])
     (display (item-name rec) port)
     (display " -> " port)
     (display (insert (item-pos rec) "⚫" terms) port)
     (display " (" port)
     (display (state-id (item-start rec)) port)
     (display ")" port))))

;;; --------------------------

(define state-ctr -1)

(define state
  (lambda sts
    (unless (every item? sts) (error "bad state:" sts))
    (set! state-ctr (+ state-ctr 1))
    (state-raw state-ctr sts)))

(define (state=? ss1 ss2)
  (= (state-id ss1) (state-id ss2)))

(define (state-empty? ss)
  (null? (state-items ss)))

(define (append-item! ss st)
  (unless (and (state? ss)
               (item? st))
    (error "cannot append item:" ss st))
  (state-items! ss (append (state-items ss) (list st))))

(set-record-type-printer!
  state-t
  (lambda (rec port)
    (display "--- " port)
    (display (state-id rec) port)
    (display " ---" port)
    (newline port)
    (let loop ([items (state-items rec)])
      (unless (null? items)
        (display (car items) port)
        (newline port)
        (loop (cdr items))))))

;;; --------------------------

(define GAMMA "GAMMA")

(define (parse grammar start-symbol input)

  (define nulling (nullable grammar))

  (define (nulling? nonterm) (member nonterm nulling))

  (define (predict ss st)
    ;; If st is nonterminal, and its next symbol is N, then for each rule <N ->
    ;; alpha> in the grammar, add the item <N -ss-> .alpha> to ss.
    ;;
    ;; Create each new item with an empty list.
    (unless (every rule? grammar) (error "bad grammar:" grammar))
    (unless (state? ss) (error "bad state:" ss))
    (unless (item-nonterminal? st) (error "bad item:" st))
    (let* ([nxt (next st)]
           [predicted (map (lambda (r) (item r 0 ss '()))
                           (filter (lambda (r) (rule-named? r nxt)) grammar))])
      (if (nulling? nxt)
          (cons (item (item-rule st)
                      (+ (item-pos st) 1)
                      (item-start st)
                      (item-tree st))
                predicted)
          predicted)
      ))

  (define (complete st)
    ;; If st in final, then for each 'parent' item in (item-start st) with the
    ;; dot immediately preceeding N, add a similar item to [this state] with the
    ;; dot moved to the right.
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
                             (append (item-tree s)
                                     (list (list name (item-tree st))))))
           (filter (lambda (s) (and (item-nonterminal? s)
                                    (nonterminal=? (next s) name))) itemsp))))

  (define (predict/complete ss st)
    (cond [(item-nonterminal? st) (predict ss st)]
          [(item-final? st)       (complete st)]
          [else                    '()]))

  (define (expand! ss st)
    (unless (find (lambda (s) (item=? st s)) (state-items ss))
      (append-item! ss st)
      (for-each (lambda (s) (expand! ss s)) (predict/complete ss st))
      ss))

  (define (scan old trm)
    ;; For all s in state old, if s is terminal and its next symbol is trm,
    ;; then create a new state new and add a copy of s to new with the dot
    ;; moved one symbol to the right.
    ;;
    ;; Append trm to the list for the new item.
    (let ([matches (filter (lambda (s) (and (item-terminal? s)
                                            (terminal=? (next s) trm)))
                           (state-items old))]
          [new (state)])
      (for-each (lambda (s) (expand! new (item (item-rule s)
                                               (+ (item-pos s) 1)
                                               (item-start s)
                                               (append (item-tree s) (list trm)))))
                matches)
      new))

  (unless (and (every rule? grammar)
               (string? start-symbol))
    (error "bad grammar:" grammar start-symbol))
  (unless (every terminal? input) "bad input:" input)
  (set! state-ctr -1)
  (let* ([ss0 (state)]
         [r0  (rule GAMMA (list start-symbol))]
         [s0  (item r0 0 ss0 '())])
    (expand! ss0 s0)
    (let loop ([current ss0]
               [in      input])
      (cond
       [(state-empty? current) #f]
       [(null? in) current]
       [else (loop (scan current (car in)) (cdr in))]))))

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

;; Grammar with empty rules
(define nul (list (rule "S" '("A" "A" "A" "A"))
                  (rule "A" '(a))
                  (rule "A" '("E"))
                  (rule "E" '())))
