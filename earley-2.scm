;;; The Earley Parsing Algorithm, Dustin Mitchell, 2001

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

(define-record-type state-t
  (state-raw rule pos start trees) state?
  (rule  state-rule)
  (pos   state-pos)
  (start state-start)
  (trees state-trees state-trees!))

(define (state rule n start trees)
  (unless (and (rule? rule)
               (number? n)
               (state-set? start))
    (error "bad state:" rule start))
  (state-raw rule n start trees))

(define (state=? st1 st2)
  (and (rule=? (state-rule st1) (state-rule st2))
       (= (state-pos st1) (state-pos st2))
       (state-set=? (state-start st1) (state-start st2))
       (equal? (state-trees st1) (state-trees st2))))

(define (state-name st)
  (unless (state? st) (error "not a state:" st))
  (rule-name (state-rule st)))

(define (state-named? st str)
  (unless (state? st) (error "not a state:" st))
  (rule-named? (state-rule st) str))

(define (next st)
  (unless (state? st) (error "not a state:" st))
  (if (state-final? st)
      (error "cannot get next symbol:" st)
      (rule-term (state-rule st) (state-pos st))))

(define (state-final? st)
  (unless (state? st) (error "not a state:" st))
  (>= (state-pos st) (rule-length (state-rule st))))

(define (state-terminal? st)
  (and (state? st)
       (not (state-final? st))
       (terminal? (next st))))

(define (state-nonterminal? st)
  (and (state? st)
       (not (state-final? st))
       (nonterminal? (next st))))

;; (define (append-tree! st tre)
;;   (unless (state? st) (error "bad state:" st))
;;   (state-trees! st (append (state-trees st) (list tre))))

;;; --------------------------

(define-record-type state-set-t
  (state-set-raw id st-set) state-set?
  (id state-set-id)
  (st-set state-set-states state-set-states!))

(define state-set
  (let ([ctr 0])
    (lambda sts
      (unless (every state? sts) (error "bad state-set:" sts))
      (set! ctr (+ ctr 1))
      (state-set-raw ctr sts))))

(define (state-set=? ss1 ss2)
  (= (state-set-id ss1) (state-set-id ss2)))

(define (state-set-empty? ss)
  (null? (state-set-states ss)))

(define (append-state! ss st)
  (unless (and (state-set? ss)
               (state? st))
    (error "cannot append state:" ss st))
  (state-set-states! ss (append (state-set-states ss) (list st))))

;;; --------------------------

(define GAMMA "GAMMA")

(define (predict grammar ss st)
  ;; If st is nonterminal, and its next symbol is N, then for each rule <N ->
  ;; alpha> in the grammar, add the state <N -ss-> .alpha> to ss.
  ;;
  ;; Create each new state with an empty list.
  (unless (every rule? grammar) (error "bad grammar:" grammar))
  (unless (state-set? ss) (error "bad state-set:" ss))
  (unless (state-nonterminal? st) (error "bad state:" st))
  (let ([nxt (next st)])
    (map (lambda (r) (state r 0 ss '()))
         (filter (lambda (r) (rule-named? r nxt)) grammar))))

(define (complete st)
  ;; If st in final, then for each 'parent' state in (state-start st) with the
  ;; dot immediately preceeding N, add a similar state to [this state-set] with
  ;; the dot moved to the right.
  ;;
  ;; Each new state carries a copy of the parent state's list, to which is
  ;; appended the list for s as a single element.
  (unless (state-final? st) (error "bad state:" st))
  (let* ([name (state-name st)]
         [ssp (state-start st)]
         [statesp (state-set-states ssp)])
    (map (lambda (s) (state (state-rule s)
                            (+ (state-pos s) 1)
                            (state-start s)
                            (append (state-trees s) (list (list name (state-trees st))))))
         (filter (lambda (s) (and (state-nonterminal? s)
                                  (nonterminal=? (next s) name))) statesp))))

(define (predict/complete grammar ss st)
  (cond [(state-nonterminal? st) (predict grammar ss st)]
        [(state-final? st)       (complete st)]
        [else                    '()]))

(define (expand! grammar ss st)
  (unless (find (lambda (s) (state=? st s)) (state-set-states ss))
    (append-state! ss st)
    (for-each (lambda (s) (expand! grammar ss s)) (predict/complete grammar ss st))
    ss))

(define (scan grammar ss trm)
  ;; For all s in state-set ss, if s is terminal and its next symbol is trm,
  ;; then create a new state-set ssn and add a copy of s to ssn with the dot
  ;; moved one symbol to the right.
  ;;
  ;; Append trm to the list for the new state.
  (let ([matches (filter (lambda (s) (and (state-terminal? s)
                                          (terminal=? (next s) trm)))
                         (state-set-states ss))]
        [ssn (state-set)])
    (for-each (lambda (s) (expand! grammar ssn (state (state-rule s)
                                                      (+ (state-pos s) 1)
                                                      (state-start s)
                                                      (append (state-trees s) (list trm)))))
              matches)
    ssn))

(define (parse grammar start-symbol input)
  (unless (and (every rule? grammar)
               (string? start-symbol))
    (error "bad grammar:" grammar start-symbol))
  (unless (every terminal? input) "bad input:" input)
  (let* ([ss0 (state-set)]
         [r0  (rule GAMMA (list start-symbol 'END))]
         [s0  (state r0 0 ss0 '())])
    (expand! grammar ss0 s0)
    (let loop ([current ss0]
               [in      input])
      (if (null? in)
          (scan grammar current 'END)
          (begin
            (loop (scan grammar current (car in)) (cdr in)))))))

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
