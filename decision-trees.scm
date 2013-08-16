#!/usr/bin/env chicken-scheme

;; [[file:~/prg/org/decision-trees.org::*Implementation][Implementation:1]]

(use debug
     define-record-and-printer
     files
     format
     graphviz
     matchable
     random-bsd
     shell
     srfi-1
     srfi-69
     statistics
     test)

(define (log-b z b)
  (/ (log z) (log b)))

(define log-2 (cute log-b <> 2))

(define (frequencies instances attribute)
  (let ((frequencies (make-hash-table))
        (index (attribute-index attribute)))
    (for-each (lambda (value)
                (hash-table-update!/default frequencies
                                            value
                                            add1
                                            0))
      (attribute-values instances attribute))
    frequencies))

(define (probabilities instances attribute)
  (let ((n (length instances))
        (frequencies (frequencies instances attribute)))
    (hash-table-walk frequencies
      (lambda (value frequency)
        (hash-table-set! frequencies value (/ frequency n))))
    frequencies))

(define (entropy instances attribute)
  (let ((probabilities (probabilities instances attribute)))
    (hash-table-fold
     probabilities
     (lambda (value probability entropy)
       (- entropy (* probability (log-2 probability))))
     0)))

(define-record-and-printer attribute
  name
  type
  domain
  index)

(define (attribute-values instances attribute)
  (map (cute list-ref <> (attribute-index attribute))
       instances))

(define (continuous? attribute)
  (eq? (attribute-type attribute) 'continuous))

(define (discrete? attribute)
  (eq? (attribute-type attribute) 'discrete))

(define sample-size (make-parameter 1000))

(define (maybe-sample-domain instances attribute)
  (if (discrete? attribute)
      (attribute-domain attribute)
      (random-sample
       (sample-size)
       (delete-duplicates
        (attribute-values instances attribute)))))

(define (select-instances instances predicate attribute)
  (let ((index (attribute-index attribute)))
    (filter (lambda (instance)
              (predicate (list-ref instance index)))
            instances)))

(define (continuous-predicate comparandum)
  (lambda (comparator) (< comparator comparandum)))

(define (discrete-predicate comparandum)
  (lambda (comparator) (eq? comparator comparandum)))

(define (attribute-predicate attribute value)
  (if (continuous? attribute)
      (continuous-predicate value)
      (discrete-predicate value)))

(define (partition-instances instances attribute key)
  (let ((partition (make-hash-table))
        (index (attribute-index attribute)))
    (for-each (lambda (instance)
                (hash-table-update!/default
                 partition
                 (key (list-ref instance index))
                 (cute cons instance <>)
                 '()))
      instances)
    partition))

(define (partition-instances/discrete instances attribute)
  (partition-instances instances attribute values))

(define (partition-instances/continuous instances attribute value)
  (partition-instances instances attribute (cute <= <> value)))

(define (partition-entropy instances partition target)
  (hash-table-fold partition
                   (lambda (value subinstances partition-entropy)
                     (+ (* (/ (length subinstances) (length instances))
                           (entropy subinstances target))
                        partition-entropy))
                   0))

(define (attribute-entropy instances input target)
  (if (discrete? input)
      (let ((partition (partition-instances/discrete instances input)))
        (values (partition-entropy instances
                                   partition
                                   target)
                partition))
      (let iter ((old-partition-entropy +inf.0)
                 (old-partition (make-hash-table))
                 (domain (maybe-sample-domain instances input)))
        (if (null? domain)
            (values old-partition-entropy old-partition)
            (let* ((value (car domain))
                   (new-partition (partition-instances/continuous instances input value))
                   (new-partition-entropy (partition-entropy instances new-partition target)))
              (if (< new-partition-entropy old-partition-entropy)
                  (iter new-partition-entropy
                        new-partition
                        (cdr domain))
                  (iter old-partition-entropy
                        old-partition
                        (cdr domain))))))))

(define (information-gain instances input target)
  (call-with-values (lambda () (attribute-entropy instances input target))
    (lambda (attribute-entropy partition)
      (values
       (- (entropy instances target) attribute-entropy)
       partition))))

(define-record-and-printer node
  description
  attribute
  predicate
  value
  probability
  entropy
  edges)

(define-record-and-printer edge
  value
  child)

(define-record-and-printer no-label)
(define no-label (make-no-label))

(define (id3 n instances inputs target root)
  (let ((superfrequencies (frequencies instances target)))
    (if (= (hash-table-size superfrequencies) 1)
        (begin
          (node-attribute-set! root target)
          (node-entropy-set! root (entropy instances target))
          (node-probability-set! root (/ (length instances) n))
          (node-value-set! root (car (hash-table-keys superfrequencies)))
          root)
        (if (null? inputs)
            (begin
              (node-attribute-set! root target)
              (node-entropy-set! root (entropy instances target))
              (node-probability-set! root (/ (length instances) n))
              (node-value-set!
               root
               (car
                (hash-table-fold
                 superfrequencies
                 (lambda (value frequency max-value-frequency)
                   (match max-value-frequency
                     ((max-value . max-frequency)
                      (if (> frequency max-frequency)
                          (cons value frequency)
                          max-value-frequency))))
                 (cons #f -inf.0))))
              root)
            (let iter ((test-inputs inputs)
                       (best-input #f)
                       (best-information-gain -inf.0)
                       (best-partition (make-hash-table)))
              ;; (debug test-inputs best-input best-information-gain best-partition)
              (if (null? test-inputs)
                  (begin
                    (node-description-set!
                     root
                     (if (continuous? best-input)
                         (format "~a <= ~a"
                                 (attribute-name best-input)
                                 (fold max -inf.0
                                       (attribute-values (hash-table-ref/default
                                                          best-partition
                                                          #t
                                                          '()) best-input)))
                         (format "~a?"
                                 (attribute-name best-input))))
                    (node-predicate-set!
                     root
                     (if (continuous? best-input)
                         (lambda (value input-value)
                           (eq?
                            (<= value
                                (fold max -inf.0 (attribute-values subinstances best-input)))
                            input-value)) 
                         (lambda (value input-value) (eq? value input-value))))
                    (node-attribute-set! root best-input) 
                    (node-edges-set!
                     root
                     (hash-table-map
                      best-partition
                      (lambda (input-value subinstances)
                        (make-edge
                         input-value
                         (id3 n
                              subinstances
                              (delete best-input inputs eq?)
                              target
                              (make-node #f #f #f #f #f #f '()))))))
                    root)
                  (let ((input (car test-inputs)))
                    (call-with-values (lambda () (information-gain instances input target))
                      (lambda (information-gain partition)
                        (if (> information-gain best-information-gain)
                            (iter (cdr test-inputs)
                                  input
                                  information-gain
                                  partition)
                            (iter (cdr test-inputs)
                                  best-input
                                  best-information-gain
                                  best-partition)))))))))))

(define (maybe-create-label labels node)
  (hash-table-update! labels node values gensym))

;; (trace maybe-create-label)

(define (write-tree-as-dot root)
  (write-dot-preamble)
  (let ((labels (make-hash-table)))
    (let iter ((root root))
      (let ((root-label (maybe-create-label labels root)))
        (if (null? (node-edges root))
            (write-node root-label
                        `((label . ,(format "~a (p: ~,2f, H: ~,2f)"
                                            (node-value root)
                                            (node-probability root)
                                            (node-entropy root)))
                          (shape . plaintext)))
            (write-node root-label
                        `((label . ,(node-description root)))))
        (let ((edges (node-edges root)))
          (for-each (lambda (edge)
                      (let* ((child (edge-child edge))
                             (child-label (maybe-create-label labels child)))
                        (iter child)
                        (write-edge root-label
                                    child-label
                                    `((label . ,(edge-value edge))))))
            edges)))))
  (write-dot-postscript))

(define (write-tree-to-png root png)
  (let ((dot (create-temporary-file ".dot")))
    (with-output-to-file dot
        (lambda () (write-tree-as-dot root)))
    (run (dot -Tpng -o ,png < ,dot))))

(let ((x (make-attribute "x" 'continuous #f 0))
      (y (make-attribute "y" 'discrete '(#t #f) 1))
      (z (make-attribute "z" 'discrete '(#t #f) 2)))
  (let ((instances (list-tabulate 100
                                  (lambda (i) (let* ((x (random-real))
                                                (y (< (random-real) 0.5))
                                                (z (< (random-real) 0.5)))
                                           (list x y z))))))
    (let ((root (make-node #f #f #f #f #f #f '())))
      (id3 (length instances) instances (list x y) z root)
      (write-tree-to-png root "decision-trees.png")
      (run (sxiv "decision-trees.png")))))

;; Implementation:1 ends here
