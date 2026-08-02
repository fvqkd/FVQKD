# FVQKD: Formal verification of BB84 finite-key security

FVQKD is a Rocq/Coq development for finite-key security proofs of quantum key
distribution protocols.  Its main result is a machine-checked composable
security proof for BB84, following Tomamichel, Lim, Gisin, and Renner,
"Tight finite-key analysis for quantum cryptography," Nature Communications 3, 634 (2012).

The development builds on CoqQ, MathComp, and MathComp-Analysis.
CoqQ (ported to Rocq 9.1) is installed from its own repository,
https://github.com/fvqkd/CoqQ, pinned to the tag `rocq91-v1.0` by
`scripts/setup-opam-switch`.  All proof-bearing claims in `src/` close with
`Qed`; the main BB84 theorem uses only the standard classical axioms inherited from MathComp-Analysis' `boolp` library.

## Requirements

- opam 2.1 or newer.
- OCaml 5.2.1, Rocq/Coq 9.1.1, dune 3.17 or newer.
- MathComp 2.5.0 and MathComp-Analysis 1.16.0 (CoqQ is installed from its repository by the setup script).

## Build

From the repository root:

```sh
make
```

On slower hardware, raise it for the whole build:

```sh
COQ_DEFAULT_TIMEOUT=120 make
```
