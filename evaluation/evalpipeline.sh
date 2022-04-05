#!/bin/bash

echo "##################"
echo "# AUTO GENERATED #"
echo "##################"
echo ""

echo -n "nums = [ "
for i in {0..999}; do
  runhaskell gen-episodes.hs $i | racket mine-expr.rkt
  echo -n ","
done

echo "]"
echo ""
echo "if __name__ == '__main__':"
echo "  main()"
