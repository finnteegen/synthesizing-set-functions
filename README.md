
# Synthesizing Set Functions

This repository contains examples for the synthesis of set functions for the functional logic programming language [Curry](http://www.curry-language.org/) as proposed in the paper [Synthesizing Set Functions](https://arxiv.org/abs/1808.07401) presented at [WFLP 2018](http://ppdp-lopstr-18.cs.uni-frankfurt.de/wflp18.html).

## Contents

| Folder | Content |
|-|-|
| Simple | Examples for the simple synthesis of set functions |
| Sharing | Examples for the synthesis of set functions with support for call-time choice  |
| Nested | Examples for the synthesis of set functions with support for nested set functions |
| NestedSharing | Examples for the synthesis of set functions with support for call-time choice and nested set functions |

## How to try

Simply clone this repository and load one of the example `.curry` files into the REPL of the Curry system of your choice, e.g., [PAKCS](https://www.informatik.uni-kiel.de/~pakcs/) or [KiCS2](https://www-ps.informatik.uni-kiel.de/kics2/).

## How to test

To test all examples (in particular, if you modify some code), run the shell script

    ./testall.sh

if you have the Curry test tool [CurryCheck](http://dx.doi.org/10.1007/978-3-319-63139-4_13) installed (see the [PAKCS](https://www.informatik.uni-kiel.de/~pakcs/) or [KiCS2](https://www-ps.informatik.uni-kiel.de/kics2/) manuals how to install CurryCheck).

