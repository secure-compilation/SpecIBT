# SpecIBT: Formally Verified Protection Against Speculative Control-Flow Hijacking

## List of Claims

We claim that the artifact provides a Coq development of the definitions and proofs
presented in the paper (with minor simplifications for presentation purposes)
and compiles without any issues.

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

### Section 3: Key Ideas

Lemma 1 --> `seq_spec_safety_preservation_init` in Safe.v

### Section 4: Defining SpecIBT

Fig. 3 --> `exp`, `inst` in MiniCET.v
Fig. 4 --> `binop`, `eval_binop`, `eval` in MiniCET.v
Fig. 5 --> `spec_eval_small_step` in MiniCET_Index.v
Fig. 6 --> `uslh_inst`, `uslh_blk`, `uslh_prog` in MiniCET.v
Fig. 7 --> `ideal_eval_small_step_inst` in MiniCET_Index.v

### Section 5: Formal Results for SpecIBT

Lemma 2 --> `ultimate_slh_bcc_init` in MiniCET_Index.v
Lemma 3 --> `ideal_eval_relative_secure` in MiniCET_Index.v
Theorem 1 --> `spec_eval_relative_secure` in MiniCET_Index.v

### Section 6: Translation to Machine Code

Fig. 8 --> `spec_eval_small_step` in MoreLinearProof.v
Lemma 4 --> `minicet_linear_bcc` in MoreLinearProof.v
Lemma 5 --> `spec_eval_relative_secure_spec_mir_mc` in MoreLinearProof.v
Theorem 2 --> `spec_eval_relative_secure_machine` in MoreLinearProof.v

## Testing

make test testing_sync

