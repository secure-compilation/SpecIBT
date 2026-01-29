# SpecIBT: Formally Verified Protection Against Speculative Control-Flow Hijacking

## List of Claims

We claim that the artifact provides a Coq development of the definitions and proofs
presented in the paper (with minor simplifications for presentation purposes)
and compiles without any issues.

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
1. Install opam in your system with the version at least 2.1.5.
2. In artifact directory, install a local opam switch and install the dependencies:
   ```
   opam switch create SpecIBT 4.14.1 &&
   eval $(opam env) &&
   opam pin add rocq-prover 9.0.0 -y &&
   opam repo add rocq-released https://rocq-prover.org/opam/released &&
   opam config env &&
   opam pin add coq-quickchick 2.1.0 -y &&
   make
   ```

## Mapping from the paper to the Coq development
TODO