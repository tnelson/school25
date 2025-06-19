#lang racket/base
(require (for-syntax racket/base racket/syntax syntax/srcloc)
         (only-in forge/lang/ast next_state raise-forge-error
                  node/int/constant? node/formula? node/int/constant-value)
         forge/lang/deparse)
(provide nexts)

; Manufactures a procedure closing over the provided syntax location.
(define (build-nexts loc)
  (letrec ([builder
           (lambda (n e)
             (cond [(node/int/constant? n) (builder (node/int/constant-value n) e)]
                   [(not (integer? n)) (raise-forge-error
                                        #:msg (format "The first argument to nexts (~a) was not an integer." n)
                                        #:context loc)]
                   [(not (node/formula? e)) (raise-forge-error
                                          #:msg (format "The second argument to nexts (~a) was not a boolean-valued formula." (deparse e))
                                          #:context loc)]
                   [(<= n 1) (next_state e)]
                   [else (builder (- n 1) (next_state e))]))])
    builder))

; Macro to capture the original syntax location, to make better error messages if needed.
(define-syntax (nexts stx)
  (syntax-case stx ()
    [_ (quasisyntax/loc stx (build-nexts #,(build-source-location stx)))]))