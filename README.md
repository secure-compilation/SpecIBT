# Extending SLH to Speculative Control-Flow Hijacking Attacks

## Requirements

The development uses the [Rocq prover](https://rocq-prover.org).

We tested this with version 8.20.1, when it was still called Coq.

Installation instructions for these versions are available here:
https://web.archive.org/web/20250305221757/https://coq.inria.fr/download

From OPAM just run:

    $ opam install coq.8.20.1

The testing experiments in `Testing*.v` additionally depend on
the [QuickChick](https://github.com/QuickChick/QuickChick) library.
We tested with version 2.1.1.

    $ opam install coq-quickchick

## Building

For having Rocq check our proofs run `make` in the root directory of the development.
