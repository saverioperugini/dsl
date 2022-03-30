#!/bin/bash

for i in {0..3}; do
  runhaskell gen-episodes.hs $i | racket mine-expr.rkt
  echo ""
done
