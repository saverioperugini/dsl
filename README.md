# Dialog Specification Language (DSL)

## Current Files

* `README.md`:        This file.
* `rewrite.hs`:       Implementation of DSL rewrite rules (without support for the W mnemonic and uparrow operator)
* `ArrowBackend.hs`:  Implementation of DSL rewrite rules (with support for the W mnemonic and uparrow operator)
* `ArrowFrontend.hs`: Implementation of a textual front-end for DSL dialog systems.

## Getting Started Guide

### System Requirements

The following software must be installed to verify the claims listed below.

* The Glasgow Haskell Compiler,
  available at <https://www.haskell.org/ghc/>
  (Latest version: GHC 9.12.1, released 16 December 2024)

* The Racket Programming Language Interpreter,
  available at <https://racket-lang.org/>
  (Latest version: 8.15, released 4 November 2024)

* The Python Programming Language Interpreter,
  available at <https://www.python.org/>
  (Latest version: 3.13.1, released 7 October 2024)

* The Matplotlib Python visualization package: `pip install matplotlib`

* Commands that must be in the user's command search path
    - `ghci` must be in the user's command path
    - `runhaskell` must be in the user's command path
    - `racket` must be in the user's command path
        - `racket` is installed as `/Applications/Racket v8.15/bin/racket` on MacOS X,
          and typically `C:\Program Files\Racket\racket.exe` on Windows
    - `python3` must be in the user's command path

## Overview of Claims

1. We operationalize the formal semantics of DSL in a Haskell functional
programming implementation.

2. The Haskell implementation of the simplification/staging rules
provides a proof of concept that the formal semantics are sufficient to
implement a dialog system specified with the language.

3. We evaluate DSL from a theoretical perspective.  Specifically, we
demonstrate that dialog specifications are compressed by to a higher degree
when written in DSL using the new abstractions (i.e., the W mnemonic and arrow
operator).

These claims are made in the abstract of the article as well as
in a variety of places in the body of the article.

## Step-by-Step Instructions

### Verifying Claim 1

***Claim 1.*** We operationalize the formal semantics of DSL in a Haskell functional
programming implementation.

* The source file `rewrite.hs` supports claim (1) in that it is a Haskell
implementation of the dialogue rewrite and simplification rules in Appendix B
of the article (i.e., the formal semantics of DSL without the W mnemonic and
arrow operator).  This source code file is discussed in Section 3.5.1 of the
article and a snippet of it is given in Listing 1.

* The source file `ArrowBackend.hs` supports claim (1) in that
it is a Haskell implementation of the full set of reduction rules for DSL
expressions with the W mnemonic and arrow operator in Section 3.4.2 of the
article (i.e., the formal semantics of DSL including the W mnemonic and arrow
operator).  This source code file is discussed in Section 3.5.2 and snippets
of it are given in Listings 2 and 3.

### Verifying Claim 2

***Claim 2.*** The Haskell implementation of the simplification/staging rules
provides a proof of concept that the formal semantics are sufficient to
implement a dialog system specified with the language.


* The source file `ArrowFrontend.hs` supports claim (2) in that it is a 
Haskell front end to a dialog system, which is built from `ArrowBackend.hs`, of
the DSL expression given in `example_dialog.png`

This example dialog system can be run and tested using the `ghci` tool as part
of the The Glasgow Haskell Compiler software suite (available at
<https://www.haskell.org/ghc/>) as shown in the transcript below.

```bash
$ ghci ArrowFrontend.hs 
GHCi, version 9.6.6: https://www.haskell.org/ghc/  :? for help
[1 of 3] Compiling ArrowBackend     ( ArrowBackend.hs, interpreted )
[2 of 3] Compiling Main             ( ArrowFrontend.hs, interpreted )
Ok, two modules loaded.
ghci> main
[sys] What protein would you like? [steak, chicken]
[usr] chicken
[sys] Ok.
[sys] What rice would you like? [white, brown]
[usr] white
[sys] Ok.
[sys] What beans would you like? [black, pinto]
[usr] pinto
[sys] Ok.
[sys] What side would you like? [chips, salsa, tortilla]
[usr] salsa
[sys] Ok.
[sys] Would you like a plant-based meal? [vegetarian, vegan, not-plant-based]
[usr] vegan
[sys] Ok.
[sys] Set a lifestyle preference? [paleo, keto, no-lifestyle]
[usr] keto
[sys] Ok.
[sys] Are you avoiding any ingredients? [gluten, dairy, soy, not-avoiding]
[usr] not-avoiding
[sys] Ok.
Dialogue complete!
ghci> 
```
### Verifying Claim 3

***Claim 3.*** We evaluate DSL from a theoretical perspective.  Specifically, we
demonstrate that dialog specifications are compressed by to a higher degree
when written in DSL using the new abstractions (i.e., the W mnemonic and arrow
operator).

The objective of the code in the `evaluation/` directory is to 
run the experiments on a synthetic data set as described in Section 4 (particularly
subsection 4.1) and generate the results show in subsection 4.2, including the
histograms given in Figure 6.

To verify claim 3,
   - Run `make` in the `evaluation/` directory.
   - Run `python3 graphs.py` to display a histogram.

To run `make` in the `evaluation/` directory then user must have Haskell,
Racket, and Python installed (see section System Requirements above) and must
have both `runhaskell` and `racket` in the command path (see section System
Requirements above).

The `runhaskell` tool is part of the The Glasgow Haskell Compiler software
suite (available at <https://www.haskell.org/ghc/>) as shown in the transcript
below.

To run `python3 graphs.py` to display a histogram the user must have Python
installed, `python3` in the command path, and the Matplotlib Python package 
installed (see section System Requirements above).

```bash
$ make
echo "import GenEpisodes" > TestDialogs.hs
echo "" >> TestDialogs.hs
echo "main = GenEpisodes.mainLoop testDialogs" >> TestDialogs.hs
echo "" >> TestDialogs.hs
echo "testDialogs :: [Dialog]" >> TestDialogs.hs
echo "testDialogs = [" >> TestDialogs.hs
python3 random_dialogs.py 1000 >> TestDialogs.hs
echo "  ]" >> TestDialogs.hs
runhaskell TestDialogs.hs | racket mine-expr.rkt > numbers.txt
$
$ ls
GenEpisodes.hs        TestDialogs_best.hs*   mine-expr.rkt*
Makefile              TestDialogs_best_5.hs* numbers.txt
TestDialogs.hs        graphs.py             random_dialogs.py*
$
$ python3 graphs.py  # the generated graphs.py program requires matplotlib
Matplotlib is building the font cache; this may take a moment.
...
...
(graphs open here on user's system)
...
...
The average episode length is  54.879
There were 67 dialogs that previously had no reduction
The average is 6.749999999999986
Previously-reduced counts (blue): [280, 41, 41, 40, 26, 33, 105, 104, 42, 38, 27, 6, 13, 0, 60, 0, 16, 1, 0, 37, 0, 0, 3, 1, 0, 0, 1, 17, 1]
Not previously-reduced counts: [0, 13, 13, 10, 6, 9, 0, 10, 0, 3, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0]
```

The graphs that open are the graphs that are given in Figure 6 (left and right)
in Section 4.2 of the article.
