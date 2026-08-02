(* -------------------------------------------------------------------- *)
(* def.v — Matrix-level definitions                                      *)
(* -------------------------------------------------------------------- *)
(* Module: utils.mx.def                                   *)
(* TeX source: none (library utility)                                    *)
(* TeX labels: none                                                      *)
(* -------------------------------------------------------------------- *)
(* Owns pure matrix-level DEFINITIONS only. Matrix-level lemmas live in  *)
(* mx/prop.v. Ambient set-labelled infrastructure lives in               *)
(* utils/labelled/{sys,op,lift}.v.                                       *)
(* Contents: sqrtmx, lnmx, castmx_sq, bigten, tuple_tensmx, pauli_X,     *)
(*           pauli_Z, max_mixed, lambda_max, sigma23_fwd, mxswap23,      *)
(*           mxswap12.                                                   *)
(* -------------------------------------------------------------------- *)

(* --- Library imports --- *)
From HB Require Import structures.
From mathcomp Require Import all_boot all_order all_algebra finmap fingroup perm.
From quantum.external Require Import spectral complex.
From mathcomp.classical Require Import boolp classical_sets.
From mathcomp Require Import interval_inference.
From mathcomp.reals Require Import reals.
From mathcomp.analysis.topology_theory Require Import topology.
From mathcomp.analysis.normedtype_theory Require Import normedtype.
From mathcomp.analysis Require Import sequences exp ereal.
From mathcomp.real_closed Require Import mxtens.
Require Import mathcomp.algebra.archimedean.
From quantum Require Import mcextra mcaextra notation hermitian quantum
  cpo mxpred extnum ctopology svd mxnorm hspace.

Import Order.TTheory GRing.Theory Num.Theory Num.Def MxLownerOrder.
Import VectorInternalTheory.

(* --- FVQKD imports --- *)
From utils Require Import arith.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Open Scope ring_scope.

Section FvqkdReal.
Variable R : realType.
Notation C := (@hermitian.C R).
Notation chsType := (@chsType R).

(* ================================================================== *)
(* Square root of a PSD matrix                                         *)
(*   sqrtmx M = U^*t * diag(sqrt(Re(λ))) * U                         *)
(* ================================================================== *)

(* sqrtmx *)
(* infra: no tex label — fundamental & reusable (mathcomp-style) *)
(* consumer: sqrtmx is used downstream by the BB84 secrecy proof. *)
Definition sqrtmx {n : nat} (A : 'M[C]_n) : 'M[C]_n :=
  let U := spectralmx A in
  let eigenvals := spectral_diag A in
  let sqrt_eigenvals := \row_i (Num.sqrt (@complex.Re R (eigenvals 0 i)))%:C in
  U^*t *m diag_mx sqrt_eigenvals *m U.

(* ================================================================== *)
(* Matrix logarithm (base 2)                                           *)
(*   lnmx M = U^*t * diag(log2(Re(λ))) * U   (with 0 log 0 = 0)     *)
(* ================================================================== *)

(* lnmx *)
(* infra: no tex label — fundamental & reusable (mathcomp-style) *)
(* consumer: lnmx is used downstream by the BB84 secrecy proof. *)
Definition lnmx {n : nat} (A : 'M[C]_n) : 'M[C]_n :=
  let U := spectralmx A in
  let eigenvals := spectral_diag A in
  let log_eigenvals := \row_i (if eigenvals 0 i == 0 then 0
    else (log2 (@complex.Re R (eigenvals 0 i)))%:C) in
  U^*t *m diag_mx log_eigenvals *m U.

(* ================================================================== *)
(* castmx_sq: square matrix cast utility                               *)
(* ================================================================== *)

(* castmx_sq *)
(* infra: no tex label — fundamental & reusable (mathcomp-style) *)
(* consumer: castmx_sq is used downstream by the BB84 secrecy proof. *)
Definition castmx_sq {n n' : nat} (eq_n : n = n') (A : 'M[C]_n) : 'M[C]_(n') :=
  castmx (eq_n, eq_n) A.

(* ================================================================== *)
(* Iterated tensor power: A^{⊗k}                                       *)
(* ================================================================== *)

Fixpoint bigten {n : nat} (A : 'M[C]_n) (k : nat) : 'M[C]_(n^k) :=
  match k with
  | 0 => 1%:M
  | S k' => castmx (esym (expnSr n k'), esym (expnSr n k')) ((bigten A k') *t A)
  end.

(* Variable iterated tensor product over a tuple of same-sized matrices. *)
(* tuple_tensmx *)
(* infra: no tex label — raw matrix-level product-state construction. *)
Fixpoint tuple_tensmx {d : nat} (n : nat) {struct n}
    : n.-tuple 'M[C]_d -> 'M[C]_(d ^ n) :=
  match n return n.-tuple 'M[C]_d -> 'M[C]_(d ^ n) with
  | 0 => fun _ => 1%:M
  | n'.+1 => fun t =>
      castmx_sq (esym (expnSr d n'))
        ((tuple_tensmx (tfirst_tuple t)) *t tlast t)
  end.

Arguments tuple_tensmx {d n} _.

(* ================================================================== *)
(* Pauli matrices (for BB84 qubit analysis)                            *)
(* ================================================================== *)

(* Pauli X (bit-flip) *)

(* Pauli Z (phase-flip) *)

(* ================================================================== *)
(* Maximally mixed state on n-dim system: I_n / n                      *)
(* ================================================================== *)

(* ================================================================== *)
(* Largest eigenvalue                                                   *)
(* ================================================================== *)

(* ================================================================== *)
(* System swap: H_A ⊗ H_B ⊗ H_C → H_A ⊗ H_C ⊗ H_B (and variants)     *)
(* ================================================================== *)

(* Index permutation underlying mxswap23 *)
(* sigma23 *)
(* infra: no tex label — fundamental & reusable (mathcomp-style) *)
Definition sigma23 {a b c : nat}
    (i : 'I_((a * c) * b)) : 'I_((a * b) * c) :=
  mxtens_index
    (mxtens_index
      ((mxtens_unindex (mxtens_unindex i).1).1, (mxtens_unindex i).2),
     (mxtens_unindex (mxtens_unindex i).1).2).

(* Swap 2nd and 3rd tensor factors: H_A⊗H_B⊗H_C → H_A⊗H_C⊗H_B *)
(* mxswap23 *)
(* infra: no tex label — fundamental & reusable (mathcomp-style) *)
Definition mxswap23 {a b c : nat}
    (rho : 'M[C]_((a * b) * c)) : 'M[C]_((a * c) * b) :=
  \matrix_(i, j) rho (@sigma23 a b c i) (@sigma23 a b c j).

(* Swap 1st and 2nd tensor factors: H_A⊗H_B⊗H_C → H_B⊗H_A⊗H_C *)

End FvqkdReal.

Arguments tuple_tensmx {R d n} _.
