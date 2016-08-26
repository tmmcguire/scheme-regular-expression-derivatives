
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

;;; A grammar rule
(define-record-type rule-t
  (rule-raw name production) rule?
  (name       rule-name)
  (production rule-production))

;;; --------------------------

(define-record-type state-t
  (state-raw id previous items) state?
  (id       state-id)
  (previous state-prev)
  (items    state-items state-items!))

;;; --------------------------

;; Earley items are (s,j,w) where s is a nonterminal or an LR(0) item (a rule +
;; a position), j is an integer (linking to an Earley state), and w is an SPPF
;; node with a label of the form (s,j,l)

(define-record-type label-t
  (label-raw rule pos) label?
  (rule label-rule)
  (pos  label-pos))

(define-record-type node-t
  (node-raw label start end families) node?
  (label    node-label)
  (start    node-start)
  (end      node-end)
  (families node-families node-families!))

(define-record-type item-t
  (item-raw rule pos start node) item?
  (rule  item-rule)
  (pos   item-pos)
  (start item-start)
  (node  item-node))

;;; --------------------------

(define (rule name production)
  (unless (and (nonterminal? name)
               (list? production)
               (every (lambda (t) (or (terminal? t) (nonterminal? t)))
                      production))
    (error "bad rule:" name production))
  (rule-raw name production))

(define rule=? equal?)

(define (rule-length r)
  (unless (rule? r) (error "not a rule:" r))
  (length (rule-production r)))

(define (rule-empty? r)
  (unless (rule? r) (error "not a rule:" r))
  (null? (rule-production r)))

(define (rule-start-nonterminal? r)
  (nonterminal? (rule-term r 0)))

(define (rule-named? r str)
  (unless (rule? r) (error "not a rule:" r))
  (unless (nonterminal? str) (error "bad rule-name:" str))
  (nonterminal=? (rule-name r) str))

(define (rule-term r n)
  (unless (rule? r) (error "not a rule:" r))
  (if (< n (rule-length r))
      (list-ref (rule-production r) n)
      (error "term out of range:" r n)))

(define (rule-nonterminals r)
  (unless (rule? r) (error "not a rule:" r))
  (filter nonterminal? (rule-production r)))

(define (rule-contains? r nonterm)
  (unless (rule? r) (error "not a rule:" r))
  (unless (nonterminal? nonterm) (error "not a nonterminal:" nonterm))
  (find (lambda (p) (nonterminal=? nonterm p)) (rule-nonterminals r)))

;;; --------------------------

(define STATE-COUNTER -1)

(define (state previous . items)
  (unless (and (or (null? previous) (state? previous))
               (every item? items))
    (error "bad state: previous"))
  (set! STATE-COUNTER (+ STATE-COUNTER 1))
  (state-raw STATE-COUNTER previous items))

(define (state=? st1 st2)
  (and (state? st1)
       (state? st2)
       (= (state-id st1) (state-id st2))))

(define (item-exists? state item)
  (find (lambda (i) (item=? i item)) (state-items state)))

(define (state-add-item! state item)
  (unless (state? state) (error "not a state:" state))
  (unless (item? item) (error "not an item:" item))
  (unless (item-exists state item)
    (state-items! state (cons item (state-items state)))))

(define (state-add-items! state items)
  (map (lambda (i) (state-add-item! state i)) items))

(set-record-type-printer!
 state-t
 (lambda (rec port)
   (simple-format port "--- State ~A:\n" (state-id rec))
   (let loop ([items (reverse (state-items rec))])
     (unless (null? items)
       (simple-format port "~A\n" (car items))
       (loop (cdr items))))))

;;; --------------------------

(define (label rule pos)
  (unless (and (rule? rule)
               (number? pos)
               (>= pos 0)
               (<= pos (rule-length rule)))
    (error "bad node label:" rule pos))
  (label-raw rule pos))

(define (label=? l1 l2)
  (cond
   [(and (label? l1) (label? l2))
    (and (rule=? (label-rule l1) (label-rule l2))
         (= (label-pos l1) (label-pos l2)))]
   [(and (nonterminal? l1) (nonterminal? l2))
    (nonterminal=? l1 l2)]
   [else
    #f]))

;;; --------------------------

(define (item rule pos start node)
  (unless (and (rule? rule)
               (number? pos)
               (>= pos 0)
               (<= pos (rule-length rule))
               (state? start)
               (node? node))
    (error "bad item:" rule pos start node))
  (item-raw rule pos start node))

(define (item=? i1 i2)
  (and (item?   i1)
       (item?   i2)
       (rule=?  (item-rule i1)  (item-rule i2))
       (=       (item-pos i1)   (item-pos i2))
       (state=? (item-start i1) (item-start i2))
       (node=?  (item-node i1)  (item-node i2))))

(define (item-name it)
  (unless (item? it) (error "not a item:" it))
  (rule-name (item-rule it)))

(define (item-final? it)
  (unless (item? it) (error "not a item:" it))
  (>= (item-pos it) (rule-length (item-rule it))))

(set-record-type-printer!
 item-t
 (lambda (rec port)
   (simple-format port "~A -> ~A (~A) ~A"
                  (item-name rec)
                  (insert (item-pos rec) "⚫" (rule-production (item-rule rec)))
                  (state-id (item-start rec))
                  (item-node rec))))

;;; --------------------------

(define (node label start end)
  (unless (and (or (nonterminal? label)
                   (label? label))
               (state? start)
               (state? end))
    (error "bad node:" label start end))
  (node-raw label start end '()))

(define null-node (node-raw #f #f #f '()))

(define (null-node? node)
  (not (node-label node)))

(define NODES (list null-node))

(define node=? eq?)

(define (node-labeled? node label start end)
  (and (label=? (node-label node) label)
       (state=? (node-start node) start)
       (state=? (node-end   node) end)))

(define (find-or-add-node! label start end)
  (let ([found (find (lambda (n) (node-labeled? node label start end)) NODES)])
    (cond
     [found found]
     [else (let ([new (node label start end)])
             (set! NODES (cons new NODES))
             new)])))

(set-record-type-printer!
 node-t
 (lambda (rec port)
   (if (null-node? rec)
       (display "null" port)
       (simple-format port "(~A, ~A, ~A)"
                      (node-label rec)
                      (state-id (node-start rec))
                      (state-id (node-end rec))))))

;;; --------------------------

(define (family=? f1 f2)
  (and (= (length f1) (length f2))
       (every node=? f1 f2)))

(define (add-family-if-missing! n family)
  (let ([family (find (lambda (f) (family=? f family)) (node-families n))])
    (unless family (node-families! n (append (node-families n) (list family)))))
  n)

;;; --------------------------

(define (make-node item end w v)
  (if (and (= (item-pos item) 1) (not (item-final? item)))
      v
      (let* ([s (if (item-final? item)
                    (item-name item)
                    (label (item-rule item) (item-pos item)))]
             [y (find-or-add-node! s (item-start item) end)])
        (add-family-if-missing! y (if (null-node? w) (list v) (list w v))))))


;;; --------------------------

(define (reset-state)
  (set! STATE-COUNTER -1)
  (set! NODES (list null-node)))

;;; --------------------------

(define GAMMA "GAMMA")

;; for all (S -> alpha) in P {
;;   if alpha in Sigma_N  add (S -> . alpha, 0, null) to E0
;;   if alpha = a1 alpha' add (S -> . alpha, 0, null) to Q'
;; }
;;
;; Note: introducing new pseudo-rule, GAMMA -> start; Q' trivial
(define (initialize-e0 grammar start)
  (let* ([e0   (state '())]
         [r0   (rule GAMMA (list start))]
         [item (item r0 0 e0 null-node)])
    (state-add-item! e0 item)
    e0))



;; (define (initialize-e0 grammar start)
;;   (let ([s-rules (filter (lambda (r) (and (rule-named? r start)
;;                                           (or (rule-empty? r)
;;                                               (rule-start-nonterminal? r))))
;;                          grammar)]
;;         [e0 (state '())])
;;     (state-add-items! e0 (map (lambda (r) (item r 0 e0 null-node)) s-rules))
;;     e0))

;; (define (parse grammar start input)
;;   (let ([R  '()]
;;         [Q' '()]
;;         [V  '()])))

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

;; (define aexp1 (parse aexp "EXPR" '(a)))
;; (define aexp2 (parse aexp "EXPR" '(a + a)))
;; (define aexp3 (parse aexp "EXPR" '(a + a + a)))
;; (define aexp4 (parse aexp "EXPR" '(a + a + a + a)))

;; Ambiguous grammar
(define amb (list (rule "E" '("T"))
                  (rule "E" '("E" + "E"))
                  (rule "T" '("F"))
                  (rule "T" '("T" * "T"))
                  (rule "F" '(a))))

;; (define amb1 (parse amb "E" '(a)))
;; (define amb2 (parse amb "E" '(a + a)))
;; (define amb3 (parse amb "E" '(a + a + a)))

;; Grammar with empty rules
(define nul (list (rule "S" '("A" "A" "A" "A"))
                  (rule "A" '(a))
                  (rule "A" '("E"))
                  (rule "E" '())))

;; (define nul1 (parse nul "S" '(a)))

;; Grammar from SPPF
(define ss (list (rule "S" '("S" "S"))
                 (rule "S" '(b))))

;; (define ss1 (parse ss "S" '(b b b)))
