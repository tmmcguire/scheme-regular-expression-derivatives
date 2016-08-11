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

;;; A grammar rule
(define-record-type rule-t
  (rule-raw name production) rule?
  (name rule-name)
  (production rule-production))

;;; An Earley item
(define-record-type item-t
  (item-raw rule pos start parent pred reduct) item?
  (rule   item-rule)
  (pos    item-pos)
  (start  item-start)
  (parent item-parent item-parent!)
  (pred   item-pred   item-pred!)
  (reduct item-reduct item-reduct!))

;;; The state of an Earley parse: a set of items
(define-record-type state-t
  (state-raw id previous item-set) state?
  (id state-id)
  (previous state-prev)
  (item-set state-items state-items!))

;;; SPPF predecessor pointers
(define-record-type predecessor-t
  (predecessor label dest) predecessor?
  (label pred-label)
  (dest pred-dest))

;;; SPPF reduction pointers
(define-record-type reduction-t
  (reduction label dest) reduction?
  (label reduct-label)
  (dest reduct-dest))

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

(define (item rule pos start pred reduct)
  (unless (and (rule? rule)
               (number? pos)
               (state? start)
               (every predecessor? pred)
               (every reduction? reduct))
    (error "bad item:" rule pos start pred reduct))
  (item-raw rule pos start #f pred reduct))

(define (item=? it1 it2)
  (and (rule=? (item-rule it1) (item-rule it2))
       (= (item-pos it1) (item-pos it2))
       (state=? (item-start it1) (item-start it2))))

(define (item-name it)
  (unless (item? it) (error "not a item:" it))
  (rule-name (item-rule it)))

(define (item-named? it str)
  (unless (item? it) (error "not a item:" it))
  (rule-named? (item-rule it) str))

(define (item-final? it)
  (unless (item? it) (error "not a item:" it))
  (>= (item-pos it) (rule-length (item-rule it))))

(define (next it)
  (unless (item? it) (error "not a item:" it))
  (if (item-final? it)
      (error "cannot get next symbol:" it)
      (rule-term (item-rule it) (item-pos it))))

(define (prev it)
  (unless (item? it) (error "not an item:" it))
  (if (> (item-pos it) 0)
      (rule-term (item-rule it) (- (item-pos it) 1))
      #f))

(define (item-terminal? it)
  (and (item? it)
       (not (item-final? it))
       (terminal? (next it))))

(define (item-nonterminal? it)
  (and (item? it)
       (not (item-final? it))
       (nonterminal? (next it))))

(define (item-append-preds! it preds)
  (item-pred! it (append (item-pred it) preds)))

(define (item-append-reducts! it reducts)
  (item-reduct! it (append (item-reduct it) reducts)))

(define (display-item-t rec port)
  (let ([terms (rule-production (item-rule rec))])
    (display (item-name rec) port)
    (display " -> " port)
    (display (insert (item-pos rec) "⚫" terms) port)
    (display " (" port)
    (display (state-id (item-start rec)) port)
    (display ")" port) ))

(define (display-ptr type lab dst port)
  (display " -" port)
  (display type port)
  (display "-" port)
  (display (state-id lab) port)
  (display "-> [" port)
  (display-item-t dst port)
  (display "]"))

(set-record-type-printer!
 item-t
 (lambda (rec port)
   (let ([preds (item-pred rec)]
         [reducts (item-reduct rec)])
     (display-item-t rec port)
     (map (lambda (r) (display-ptr "p" (pred-label r) (pred-dest r) port)) preds)
     (map (lambda (r) (display-ptr "r" (reduct-label r) (reduct-dest r) port)) reducts))))

;;; --------------------------

(define state-ctr -1)

(define (state prev . its)
  (unless (every item? its) (error "bad items:" its))
  (set! state-ctr (+ state-ctr 1))
  (let ([new (state-raw state-ctr prev its)])
    (map (lambda (it) (item-parent! it new)) its)
    new))

(define (state=? st1 st2)
  (= (state-id st1) (state-id st2)))

(define (state-empty? st)
  (null? (state-items st)))

(define (append-item! st it)
  (unless (and (state? st)
               (item? it))
    (error "cannot append item:" st it))
  (item-parent! it st)
  (state-items! st (append (state-items st) (list it))))

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

  (define (predict st it)
    ;; If it is nonterminal, and its next symbol is N, then for each rule <N ->
    ;; alpha> in the grammar, add the item <N -st-> .alpha> to st.
    ;;
    ;; Create each new item with an empty list.
    (unless (every rule? grammar) (error "bad grammar:" grammar))
    (unless (state? st) (error "bad state:" st))
    (unless (item-nonterminal? it) (error "bad item:" it))
    (let* ([nxt (next it)]
           [predicted (map (lambda (r) (item r 0 st '() '()))
                           (filter (lambda (r) (rule-named? r nxt)) grammar))])
      (if (nulling? nxt)
          (cons (item (item-rule it)
                      (+ (item-pos it) 1)
                      (item-start it)
                      '()
                      '())
                predicted)
          predicted)
      ))

  (define (complete it)
    ;; If it in final, then for each 'parent' item in (item-start it) with the
    ;; dot immediately preceeding N, add a similar item to [this state] with the
    ;; dot moved to the right.
    ;;
    ;; Each new item carries a copy of the parent item's list, to which is
    ;; appended the list for s as a single element.
    (unless (item-final? it) (error "bad item:" it))
    (let* ([name (item-name it)]
           [ssp (item-start it)]
           [itemsp (state-items ssp)])
      (map (lambda (s) (item (item-rule s)
                             (+ (item-pos s) 1)
                             (item-start s)
                             (if (> (item-pos s) 0)
                                 (list (predecessor ssp s))
                                 '())
                             (list (reduction ssp it))))
           (filter (lambda (s) (and (item-nonterminal? s)
                                    (nonterminal=? (next s) name))) itemsp))))

  (define (predict/complete st it)
    (cond [(item-nonterminal? it) (predict st it)]
          [(item-final? it)       (complete it)]
          [else                    '()]))

  (define (expand! st it)
    (let ([existing (find (lambda (s) (item=? it s)) (state-items st))])
      (if existing
          (begin (item-append-preds! existing (item-pred it))
                 (item-append-reducts! existing (item-reduct it)))
          (begin (append-item! st it)
                 (for-each (lambda (s) (expand! st s)) (predict/complete st it))))
      st))

  (define (scan old trm)
    ;; For all s in state old, if s is terminal and its next symbol is trm,
    ;; then create a new state new and add a copy of s to new with the dot
    ;; moved one symbol to the right.
    ;;
    ;; Append trm to the list for the new item.
    (let* ([matches (filter (lambda (s) (and (item-terminal? s)
                                             (terminal=? (next s) trm)))
                            (state-items old))]
           [preds (filter (lambda (i) (> (item-pos i) 0)) matches)]
           [ptrs (map (lambda (p) (predecessor old p)) preds)]
           [new (state old)])
      (for-each (lambda (s) (expand! new (item (item-rule s)
                                               (+ (item-pos s) 1)
                                               (item-start s)
                                               ptrs
                                               '())))
                matches)
      new))

  (unless (and (every rule? grammar)
               (string? start-symbol))
    (error "bad grammar:" grammar start-symbol))
  (unless (every terminal? input) "bad input:" input)
  (set! state-ctr -1)
  (let* ([st0 (state #f)]
         [r0  (rule GAMMA (list start-symbol))]
         [s0  (item r0 0 st0 '() '())])
    (expand! st0 s0)
    (let loop ([current st0]
               [in      input]
               [states  '()])
      (cond
       [(state-empty? current) #f]
       [(null? in) (append states (list current))]
       [else (loop (scan current (car in))
                   (cdr in)
                   (append states (list current)))]))))

(define recognize parse)

;;; --------------------------



;;; SPPF notes---backpointer version

;;; Set E0 to be the items (S -> . alpha, 0).  // initial state

;;; For i > 0 initialize Ei by adding p = (A -> alpha ai . beta, j)
;;; for each q = (A -> alpha . ai beta,j) in Ei-1 and, if alpha /= epsilon
;;; creating a predecessor pointer labelled i-1 from q to p.
;;;
;;; // Hypothesis: switch p and q in last phrase.

;;; Before initializing Ei+1 complete Ei as follows.
;;; For each item (B -> gamma . D delta, k) in Ei and
;;; each rule D -> rho, add (D -> . rho, i) to Ei.

;;; For each item t = (B -> rho ., k) in Ei and each corresponding item
;;; q = (D -> rho . B mu, h) in Ek, if there is no item
;;; p = (d -> rho B . mu, h) in Ei, create one.
;;; Add a reduction pointer labeled k from p to t and,
;;; if rho /= epsilon, a predecessor pointer labeled k from p to q.


(define-record-type sppf-t
  (sppf-raw id label start end children families) sppf?
  (id sppf-id)
  (label sppf-label)
  (start sppf-start)
  (end sppf-end)
  (children sppf-children sppf-children!)
  (families sppf-families sppf-families!))

(define-record-type item-label-t
  (item-label-raw rule pos) item-label?
  (rule item-label-rule)
  (pos  item-label-pos))

;; If it is (A -> alpha a . beta, j), then label is for (A -> alpha .a beta, j)
;; i.e. the position is moved back one.
(define (item->label it)
  (item-label-raw (item-rule it) (- (item-pos it) 1)))

(set-record-type-printer!
 item-label-t
 (lambda (rec port)
   (let* ([rule  (item-label-rule rec)]
          [name  (rule-name rule)]
          [terms (rule-production rule)]
          [pos   (item-label-pos rec)])
     (display name port)
     (display " -> " port)
     (display (insert pos "⚫" terms) port))))

(set-record-type-printer!
 sppf-t
 (lambda (rec port)
   (display "SPPF-" port)
   (display (sppf-id rec) port)
   (display " " port)
   (display (sppf-label rec) port)
   (display " children: " port)
   (display (sppf-children rec) port)
   (display " families: " port)
   (display (sppf-families rec) port)
   ))

(define sppf-counter -1)

(define (sppf label start end . children)
  (set! sppf-counter (+ sppf-counter 1))
  (sppf-raw sppf-counter label start end children '()))

(define (sppf-label=? l1 l2)
  (or (and (nonterminal? l1)
           (nonterminal? l2)
           (nonterminal=? l1 l2))
      (and (item-label? l1)
           (item-label? l2)
           (rule=? (item-label-rule l1) (item-label-rule l2))
           (= (item-label-pos l1) (item-label-pos l2)))))

(define (sppf=? n1 n2)
  (= (sppf-id n1) (sppf-id n2)))

(define (sppf-matching? l label start end)
  (and (sppf-label=? (sppf-label l) label)
       (state=? (sppf-start l) start)
       (state=? (sppf-end l) end)))

(define (family=? f1 f2)
  (and (= (length f1) (length f2))
       (every sppf=? f1 f2)))

(define (find-family node family)
  (find (lambda (f) (family=? f family)) (sppf-families node)))

(define (add-family-if-missing! u . v)
  (let ([family (find-family u v)])
    (unless family (sppf-families! u (append (sppf-families u) (list v))))))

(define nodes '())

(define (find-sppf label start end)
  (find (lambda (node) (sppf-matching? node label start end)) nodes))

(define (find-or-add-sppf! label start end . children)
  (let ([found (find-sppf label start end)])
    (cond
     [found found]
     [else  (let ([new (apply sppf (list label start end children))])
              (set! nodes (cons new nodes))
              new)])))

(define processed '())

(define (processed? it)
  (find (lambda (i) (item=? i it)) processed))

(define (processed! it)
  (set! processed (cons it processed)))

;; Case 1
;; If it = (A -> ., j)
(define (item-case1? it)
  (rule-empty? (item-rule it)))

;; If there is no SPPF node v labeled (A,i,i), create one with child node epsilon.
;; if u does not have a family (v) then add the family (v) to u.
(define (item-case1! u it)
  (let* ([A (item-name it)]
         [i (item-parent it)]
         [node (find-or-add-sppf! A i i '())])
    (add-family-if-missing! u node)))

;; Case 2
;; If it = (A -> a . beta, j) where a terminal
(define (item-case2? it)
  (let ([a (prev it)])
    (and a
         (= (item-pos it) 1)
         (terminal? a))))

;; If there is no SPPF node v labeled (a, i-1, i), create one
;; if u does not have a family (v) then add the family (v) to u.
(define (item-case2! u it)
  (let* ([a (prev it)]
         [i (item-parent it)]
         [i-1 (state-prev i)]
         [node (find-or-add-sppf! a i-1 i)])
    (add-family-if-missing! u node)))

;; Case 3
;; if it = (A -> C . beta, j) where C nonterminal
(define (item-case3? it)
  (let ([C (prev it)])
    (and C
         (= (item-pos it) 1)
         (nonterminal? C))))

;; If there is no SPPF node v labeled (C, j, i), create one
;; if u does not have a family (v), then add the family (v) to u.
;; For each reduction pointer from v labeled j:
;;   suppose that the pointer points to q
;;   if q is not marked as processed, build-tree(v, q)
(define (item-case3! u it)
  (let* ([C (prev it)]
         [j (item-start it)]
         [i (item-parent it)]
         [node (find-or-add-sppf! C j i)])
    (add-family-if-missing! u node)
    (for-each (lambda (r-ptr) (build-tree node (reduct-dest r-ptr)))
              (filter (lambda (r-ptr) (and (state=? (reduct-label r-ptr) j)
                                           (not (processed? (reduct-dest r-ptr)))))
                      (item-reduct it)))))

;; Case 4
;; if it = (A -> alpha' a . beta, j) where a terminal, alpha' not empty
(define (item-case4? it)
  (let ([a (prev it)])
    (and a
         (> (item-pos it) 1)
         (terminal? a))))

;; If there is no SPPF node v labeled (a, i-1, i) create one
;; If there is no SPPF node w labeled (A -> alpha' . a beta, j, i-1) create one
;; for each target p' of a predecessor pointer labeled i-1 from p:
;;    if p' is not marked as processed build-tree(w, p')
;; if u does not have a family (w,v) add the family (w,v) to u
(define (item-case4! u it)
  (let* ([a (prev it)]
         [A (item-name it)]
         [i (item-parent it)]
         [i-1 (state-prev i)]
         [j (item-start it)]
         [v (find-or-add-sppf! a i-1 i)]
         [w (find-or-add-sppf! (item->label it) j i-1)])
    (add-family-if-missing! u w v)
    (for-each (lambda (p-ptr) (build-tree w (pred-dest p-ptr)))
              (filter (lambda (p-ptr) (and (state=? (pred-label p-ptr) i-1)
                                           (not (processed? (pred-dest p-ptr)))))
                      (item-pred it)))))

;; Case 5
;; if it = (a -> alpha' C . beta, j) where C nonterminal, alpha' not empty
(define (item-case5? it)
  (let ([C (prev it)])
    (and C
         (> (item-pos it) 1)
         (nonterminal? C))))

;; for each reduction pointer from p:
;;   suppose that the pointer is labeled l and points to q
;;   if there is no SPPF node v labeled (C, l, i) create one
;;   if q is not marked as processed build-tree(v, q)
;;   if there is no SPPF node w labeled (A -> alpha' . C beta, j, l) create one
;;   for each target p' of a predecessor pointer labeled l from p:
;;     if p' is not marked as processed build-tree(w, p')
;;   if u does not have a family (w,v) add the family (w,v) to u
(define (item-case5! u it)
  (let loop ([r-ptrs (item-reduct it)])
    (unless (null? r-ptrs)
      (let* ([r-ptr (car r-ptrs)]
             [l (reduct-label r-ptr)]
             [q (reduct-dest r-ptr)]
             [C (prev it)]
             [i (item-parent it)]
             [j (item-start it)]
             [v (find-or-add-sppf! C l i)]
             [w (find-or-add-sppf! (item->label it) j l)])
        (add-family-if-missing! u w v)
        (unless (processed? q)
          (build-tree v q))
        (for-each (lambda (p-ptr) (build-tree w (pred-dest p-ptr)))
                  (filter (lambda (p-ptr) (and (state=? (pred-label p-ptr) l)
                                               (not (processed? (pred-dest p-ptr)))))
                          (item-pred it)))
        (loop (cdr r-ptrs))))))

(define (build-tree u p)
  (processed! p)
  (cond
   [(item-case1? p) (item-case1! u p)]
   [(item-case2? p) (item-case2! u p)]
   [(item-case3? p) (item-case3! u p)]
   [(item-case4? p) (item-case4! u p)]
   [(item-case5? p) (item-case5! u p)]))

(define (build-sppf s0 sn)
  (set! sppf-counter -1)
  (set! nodes '())
  (set! processed '())
  (let ([u0 (sppf GAMMA s0 sn)])
    (for-each (lambda (it) (build-tree u0 it))
              (filter (lambda (it) (and (item-final? it)
                                        (nonterminal=? (item-name it) GAMMA)
                                        (state=? (item-start it) s0)))
                      (state-items sn)))
    u0))

;;; --------------------------

(define (sppf->node-name sppf)
  (simple-format #f "sppf~A" (sppf-id sppf)))

(define (sppf->dot-node n)
  (simple-format #f "~A [label=\"~A\\n~A\"];\n"
                 (sppf->node-name n)
                 (sppf-id n)
                 (sppf-label n)))

(define sppf-family->dot
  (let ([i -1])
    (lambda (origin family)
      (cond
       [(> (length family) 1)
        (set! i (+ i 1))
        (simple-format #f "~A -> xx~A;\nxx~A -> ~A;\nxx~A -> ~A;\n"
                       (sppf->node-name origin)
                       i
                       i
                       (sppf->node-name (car family))
                       i
                       (sppf->node-name (cadr family)))]
       [(= (length family) 1)
        (simple-format #f "~A -> ~A;\n"
                       (sppf->node-name origin)
                       (sppf->node-name (car family)))]))))

(define (sppf->dot-edges node)
  (map (lambda (f) (sppf-family->dot node f)) (sppf-families node)))

(define (sppf->dot)
  (let ([n (map sppf->dot-node nodes)]
        [e (concatenate (map sppf->dot-edges nodes))])
    (display "digraph test {\n")
    (display "node [label=\"\"]\n")
    (for-each display n)
    (for-each display e)
    (display "}\n")))

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

(define aexp1 (parse aexp "EXPR" '(a)))
(define aexp2 (parse aexp "EXPR" '(a + a)))
(define aexp3 (parse aexp "EXPR" '(a + a + a)))
(define aexp4 (parse aexp "EXPR" '(a + a + a + a)))

;; Ambiguous grammar
(define amb (list (rule "E" '("T"))
                  (rule "E" '("E" + "E"))
                  (rule "T" '("F"))
                  (rule "T" '("T" * "T"))
                  (rule "F" '(a))))

(define amb1 (parse amb "E" '(a)))
(define amb2 (parse amb "E" '(a + a)))
(define amb3 (parse amb "E" '(a + a + a)))

;; Grammar with empty rules
(define nul (list (rule "S" '("A" "A" "A" "A"))
                  (rule "A" '(a))
                  (rule "A" '("E"))
                  (rule "E" '())))

(define nul1 (parse nul "S" '(a)))

;; Grammar from SPPF
(define ss (list (rule "S" '("S" "S"))
                 (rule "S" '(b))))

(define ss1 (parse ss "S" '(b b b)))

;; (define q (parse aexp "EXPR" '(a + a)))

;; (define* (find-item state symbol #:key (completed #f) (starting-at 0))
;;   (let ([pred (lambda (item)
;;                 (and (item-named? item symbol)
;;                      (if completed (item-final? item) #t)
;;                      (equal? (state-id (item-start item)) starting-at)))])
;;     (filter pred (state-items state))))

;; (define (find-item pred state)
;;   (filter pred (state-items state)))

;; (define (item-name-p symbol)
;;   (lambda (it) (item-named? it symbol)))

;; (define (completed-p)
;;   (lambda (it) (item-final? it)))

;; (define (starting-at-p id)
;;   (lambda (it) (= (state-id (item-start it)) id)))

;; (define (and-p . preds)
;;   (lambda (it)
;;     (let loop ([p preds])
;;       (if (null? p)
;;           #t
;;           (if ((car p) it)
;;               (loop (cdr p))
;;               #f)))))
