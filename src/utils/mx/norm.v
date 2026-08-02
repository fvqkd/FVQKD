(* -------------------------------------------------------------------- *)
(* norm.v — Operator-norm bounds for POVM sqrt products                 *)
(* -------------------------------------------------------------------- *)
(* Module: utils.mx.norm                                  *)
(* Proof-core source: operator norm bound used by EUR eqn:mo9            *)
(*                                                                       *)
(* For a matrix A the operator-norm squared bounds ||A||² · I ≥ A A†.   *)
(* Specialised to A = √M_x √N_z (POVM sqrt product), this gives the     *)
(* √N_z M_x √N_z ≤ c · I inequality from the paper's eqn:mo9.           *)
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

From utils.mx Require Import def prop.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Open Scope ring_scope.

Section FvqkdReal.
Variable R : realType.
Notation C := (@hermitian.C R).
Notation chsType := (@chsType R).

(* ================================================================== *)
(* Op-norm bound for √N_z M_x √N_z in a POVM pair                      *)
(* Matrix proof-core used by EUR's canonical eqn:mo9 lemma              *)
(* ================================================================== *)

Section SqrtProdOpBound.
Variable (na nx nz : nat).

(* Matrix proof-core for the operator-norm bound.                         *)
(* math: √N_z M_x √N_z = (√N_z √M_x)(√N_z √M_x)† ≤ ||·||_∞² I_A           *)
(* path: utils:sqrtmx_prod_op_bound -> eur:sqrtmx_prod_overlap_bound -> *)
(*   eur:ucr_pure_smooth -> eur:entropic_uncertainty_relation -> *)
(*   eur:entropic_uncertainty_relation -> *)
(*   bb84:entropic_uncertainty_relation_bb84 -> bb84:bb84_secret *)
Lemma sqrtmx_prod_op_bound
    (M : 'I_nx -> 'M[C]_na) (N : 'I_nz -> 'M[C]_na)
    (x : 'I_nx) (z : 'I_nz) :
  (forall i, M i \is psdmx) ->
  (forall j, N j \is psdmx) ->
  sqrtmx (N z) *m M x *m sqrtmx (N z) <=
  ((@complex.Re R (i2norm (sqrtmx (M x) *m sqrtmx (N z)))) ^+ 2)%:C
    *: (1%:M : 'M[C]_na).
Proof.
  move=> HM HN.
  set A : 'M[C]_na := sqrtmx (M x) *m sqrtmx (N z).
  have HMxh : sqrtmx (M x) \is hermmx by apply/sqrtmx_herm/psdmx_herm/HM.
  have HNzh : sqrtmx (N z) \is hermmx by apply/sqrtmx_herm/psdmx_herm/HN.
  have EA : A^*t *m A = sqrtmx (N z) *m M x *m sqrtmx (N z).
    rewrite /A adjmxM -!(hermmxP _ HMxh) -!(hermmxP _ HNzh).
    by rewrite -mulmxA (mulmxA (sqrtmx (M x))) sqrtmxK// mulmxA.
  rewrite -EA le_lownerE; apply/psdmx_dot => u.
  set c : C := ((@complex.Re R (i2norm A)) ^+ 2)%:C.
  have Hc1M : c *: (1%:M : 'M[C]_na) = c%:M.
    by rewrite scale_scalar_mx mulr1.
  rewrite Hc1M.
  rewrite nnegrE mulmxBr mulmxBl linearB/= subr_ge0.
  rewrite mul_mx_scalar -scalemxAl linearZ/=.
  rewrite (mulmxA u^*t A^*t A) -(mulmxA (u^*t *m A^*t) A u) -adjmxM.
  rewrite dotV_l2norm dotV_l2norm.
  have Hreal : i2norm A \is Num.real by apply/ger0_real/i2norm_ge0.
  have Hi2c : (@complex.Re R (i2norm A))%:C = i2norm A by apply: RRe_real.
  rewrite /c realcX Hi2c.
  have Hb : l2norm (A *m u) <= i2norm A * l2norm u by apply: i2norm_dotr.
  rewrite -exprMn.
  apply: lerXn2r => //; rewrite nnegrE.
  - by apply: l2norm_ge0.
  - by apply: mulr_ge0; [apply: i2norm_ge0 | apply: l2norm_ge0].
Qed.

End SqrtProdOpBound.

End FvqkdReal.
