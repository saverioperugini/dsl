# dialogsthesis

Current files

* `rewrite.hs` -- Haskell rewrite rules (no uparrow notation)
* `rewrite_stack.hs` -- Haskell dialog-stack rewrite rules that support uparrow notation
* `stack_semantics.hs` -- Haskell implementation of the formal semantics of arrow dialogs. (Slightly different from rewrite_stack.hs).
* `dialogs_stack.rkt` -- Scheme stager-builder that supports uparrow notation.
* `process.exs` -- Elixir stager using processes
* `process.go` -- Golang stager using processes and channels

For evaluation run `make` in the `evaluation/` directory, then run `graphs.py` to display a histogram.
