#!/bin/bash

for i in {0..9}; do
  runhaskell gen-episodes.hs $i | racket mine-expr.rkt
  echo ""
done
