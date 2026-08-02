(* -------------------------------------------------------------------- *)
(* def.v — bipartite maximally-entangled state + two-register measurement *)
(* -------------------------------------------------------------------- *)
(* Module: utils.entangle.def                                       *)
(* TeX source: none (reusable quantum-information infrastructure)        *)
(* -------------------------------------------------------------------- *)
(* Reusable constructions for the entanglement-based (EB) source of      *)
(* BB84: a literal bipartite maximally-entangled state over two          *)
(* disjoint labelled registers A, A' identified by an index map g, and   *)
(* the superoperators that measure one half.  CoqQ has no built-in       *)
(* maximally-entangled state, so it is constructed here from the         *)
(* computational basis deltav and the vector tensor product.            *)
(*                                                                      *)
(* This file is definitions only (lemmas live in prop.v).               *)
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
From quantum.dirac Require Import hstensor.

Import Order.TTheory GRing.Theory Num.Theory Num.Def MxLownerOrder.
Import VectorInternalTheory.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Open Scope ring_scope.
Local Open Scope lfun_scope.

Section EntangleDef.
Variable R : realType.
Notation C := (@hermitian.C R).
Notation chsType := (@chsType R).

(* ================================================================== *)
(* Bipartite paired state (maximally entangled iff g is a bijection)    *)
(* ================================================================== *)
(* Over two disjoint labelled registers A, B and an index map           *)
(* g : 'Idx_A -> 'Idx_B, the (unnormalized) paired vector is             *)
(*   Phi0 := sum_i |i>_A (x) |g i>_B.                                    *)
(* This is a maximally entangled (EPR) state exactly when g is bijective  *)
(* (equivalently, dim 'H_A = dim 'H_B in the intended use); the canonical *)
(* EPR case is g = id. For a non-injective g, for example a constant map, *)
(* Phi0 can be separable. The downstream collapse, density, and ensemble  *)
(* lemmas hold for any g because they use only orthonormality of {|i>}    *)
(* and pointwise evaluation of g. A caller that needs a genuine EPR       *)
(* source must provide bijectivity (or use g = id).                      *)
(* The outer parentheses around the summand are required: without them,  *)
(* the (x)v precedence drops (g i) out of the binder.                    *)

Definition max_entangled_raw (L : finType) (HL : L -> chsType)
    (A B : {set L}) (g : 'Idx[HL]_A -> 'Idx[HL]_B) : 'H[HL]_(A :|: B) :=
  \sum_(i : 'Idx[HL]_A) ((deltav i) ⊗v (deltav (g i))).

(* Normalized maximally-entangled state: |Phi| = 1 (see prop.v). *)
Definition max_entangled (L : finType) (HL : L -> chsType)
    (A B : {set L}) (g : 'Idx[HL]_A -> 'Idx[HL]_B) : 'H[HL]_(A :|: B) :=
  (sqrtC (dim ('H[HL]_A))%:R)^-1 *: max_entangled_raw g.

(* ================================================================== *)
(* Two-register measurement superoperators                              *)
(* ================================================================== *)
(* Measuring the A-half of a bipartite A (x) B state with a Kraus       *)
(* family {k i} acting on A (and identity on B): meas_left.  The        *)
(* B-half version is meas_right.  The single-element (projective) form   *)
(* is meas_left_elem, used to read out one outcome of the EB source.    *)

Definition meas_left (L : finType) (HL : L -> chsType)
    (A B : {set L}) (F : finType) (k : F -> 'F[HL]_A)
    : 'SO[HL]_(A :|: B) :=
  krausso (fun i => (k i) \⊗ (\1 : 'F[HL]_B)).

Definition meas_right (L : finType) (HL : L -> chsType)
    (A B : {set L}) (F : finType) (k : F -> 'F[HL]_B)
    : 'SO[HL]_(A :|: B) :=
  krausso (fun i => (\1 : 'F[HL]_A) \⊗ (k i)).

(* Single Kraus element (e.g. a projector |e_x><e_x|) on the A-half. *)
Definition meas_left_elem (L : finType) (HL : L -> chsType)
    (A B : {set L}) (k : 'F[HL]_A) : 'SO[HL]_(A :|: B) :=
  formso (k \⊗ (\1 : 'F[HL]_B)).

(* ================================================================== *)
(* Matrix-level maximally-entangled (Bell) state for the EB source       *)
(* ================================================================== *)
(* bb84_source_model carries a plain density MATRIX (not a labelled      *)
(* operator), so the entanglement-based source state is built here at    *)
(* the matrix level.  For dimension d the unnormalized Bell vector is    *)
(*   |Phi_d> := sum_(i:'I_d) |i> (x) |i>   (g = id, genuine EPR),        *)
(* and max_entangled_dmx_raw d := |Phi_d><Phi_d| is its (unnormalized)   *)
(* density.  rho_eb n is the BB84 source-model state: the normalized     *)
(* maximally-entangled density between Alice (dim 2^n) and the signal    *)
(* (dim 2^n) with a trivial 1-dimensional Eve factor in the middle,      *)
(* matching the na*nb*nc = 2^n*1*2^n layout of bb84_src_rho.  Its        *)
(* component kets are orthonormal (eb_basis_dot in prop.v), so it is a   *)
(* genuine pure entangled density (PSD by form_psd, contrast the         *)
(* prepare-and-measure source, a product/separable state).              *)

Definition max_entangled_mx_raw (d : nat) : 'cV[C]_(d * d) :=
  \sum_(i : 'I_d) (delta_mx i (0 : 'I_1) *t delta_mx i (0 : 'I_1)).

Definition max_entangled_dmx_raw (d : nat) : 'M[C]_(d * d) :=
  max_entangled_mx_raw d *m (max_entangled_mx_raw d)^*t.

Definition rho_eb_vec (n : nat) : 'cV[C]_(2 ^ n * 1 * 2 ^ n) :=
  (sqrtC ((2 ^ n)%:R : C))^-1 *:
    \sum_(i : 'I_(2 ^ n))
      ((delta_mx i (0 : 'I_1) *t delta_mx (0 : 'I_1) (0 : 'I_1))
        *t delta_mx i (0 : 'I_1)).

Definition rho_eb (n : nat) : 'M[C]_(2 ^ n * 1 * 2 ^ n) :=
  rho_eb_vec n *m (rho_eb_vec n)^*t.

End EntangleDef.
