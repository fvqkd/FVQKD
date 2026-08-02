(* -------------------------------------------------------------------- *)
(* arith.v — log2, binary entropy h(), for BB84                        *)
(* -------------------------------------------------------------------- *)
(* Module: utils.arith                                    *)
(* TeX source: none (library utility)                                   *)
(* TeX labels: none                                                      *)
(* -------------------------------------------------------------------- *)
(* --- Library imports --- *)
From HB Require Import structures.
From mathcomp Require Import all_boot all_order all_algebra finmap fingroup perm.
From quantum.external Require Import spectral complex.
From mathcomp.classical Require Import boolp classical_sets mathcomp_extra.
From mathcomp Require Import interval_inference.
From mathcomp.reals Require Import reals real_interval.
From mathcomp.analysis.topology_theory Require Import topology.
From mathcomp.analysis.normedtype_theory Require Import normedtype.
From mathcomp.analysis Require Import sequences exp convex ereal.
From mathcomp.real_closed Require Import mxtens.
Require Import mathcomp.algebra.archimedean.
From quantum Require Import mcextra mcaextra notation hermitian quantum
  cpo mxpred extnum ctopology svd mxnorm hspace.
Import Order.TTheory GRing.Theory Num.Theory Num.Def MxLownerOrder.
Import VectorInternalTheory.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Section FvqkdReal.
Variable R : realType.
Notation C := (@hermitian.C R).
Notation chsType := (@chsType R).
(* ================================================================== *)
(* Binary logarithm: log2(x) = ln(x) / ln(2)                          *)
(* All entropies measured in bits (log base 2).                        *)
(* ================================================================== *)
(* log2 *)
(* infra: no tex label — fundamental & reusable (mathcomp-style) *)
(* consumer: log2 is used downstream by the BB84 secrecy proof. *)
Definition log2 (x : R) : R := ln x / ln 2%:R.
(* elog2 *)
(* infra: no tex label — entropy-facing extended-real log2 *)
Definition elog2 (x : R) : extended R :=
  if (0 < x)%R then EFin (log2 x) else @ENInf R.
(* ln2_gt0 *)
(* infra: no tex label — fundamental & reusable (mathcomp-style) *)
(* consumer: ln2_gt0 is used downstream by the BB84 secrecy proof. *)
(* path: utils:ln2_gt0 -> bb84:bb84_secret *)
Lemma ln2_gt0 : (0 < ln 2 :> R).
Proof.
  by apply: ln_gt0; rewrite -nat1r -{1}[1%R]addr0 ltrD2l.
Qed.
(* log2_2 *)
(* infra: no tex label — fundamental & reusable (mathcomp-style) *)
(* consumer: log2_2 is used downstream by the BB84 secrecy proof. *)
(* path: utils:log2_2 -> utils:ln2_gt0 -> bb84:bb84_secret *)
Lemma log2_2 : log2 2%:R = 1.
Proof.
  rewrite /log2 divff//; apply: lt0r_neq0.
  by apply: ln_gt0; rewrite -nat1r -{1}[1%R]addr0 ltrD2l.
Qed.
(* log2K_ln *)
(* infra: no tex label — cancellation of the base-2 logarithm scale. *)
Lemma log2K_ln (x : R) :
  log2 x * ln 2%:R = ln x.
Proof.
  by rewrite /log2 divfK ?lt0r_neq0 ?ln2_gt0.
Qed.
(* log2_pow2_nat *)
(* infra: no tex label — fundamental & reusable (mathcomp-style) *)
(* path: utils:log2_pow2_nat -> bb84:bb84_secret *)
Lemma log2_pow2_nat (m : nat) :
  log2 ((2 ^ m)%:R : R) = m%:R.
Proof.
  rewrite natrX.
  have H2_pos : 0 < 2%:R :> R by rewrite ltr0n.
  have Hln2_nz : ln 2%:R != 0 :> R
    by apply: lt0r_neq0; exact: ln2_gt0.
  by rewrite /log2 (lnXn _ H2_pos) mulrnAl (mulfV Hln2_nz).
Qed.
(* path: utils:neg_log2_inv_pow2_nat -> bb84:bb84_numeric_side -> *)
(*   bb84:bb84_secret *)
Lemma neg_log2_inv_pow2_nat (m : nat) :
  - log2 ((2%:R)^- m) = m%:R.
Proof.
  have Hpow_pos : 0 < 2 ^+ m :> R by rewrite exprn_gt0.
  rewrite /log2 (lnV Hpow_pos).
  rewrite mulNr opprK.
  change (log2 (2 ^+ m) = m%:R).
  by rewrite -natrX log2_pow2_nat.
Qed.
(* elog2_gt0 *)
(* infra: no tex label — entropy-facing extended-real log2 *)
(* path: utils:elog2_gt0 -> bb84:stat -> bb84:bb84_secret *)
Lemma elog2_gt0 (x : R) : 0 < x -> elog2 x = EFin (log2 x).
Proof.
  by move=> Hx; rewrite /elog2 Hx.
Qed.
(* elog2_le0 *)
(* infra: no tex label — entropy-facing extended-real log2 *)
(* path: utils:elog2_le0 -> bb84:stat -> bb84:bb84_secret *)
Lemma elog2_le0 (x : R) : x <= 0 -> elog2 x = @ENInf R.
Proof.
  by move=> Hx; rewrite /elog2 ltNge Hx.
Qed.
(* elog2_0 *)
(* infra: no tex label — entropy-facing extended-real log2 *)
(* path: utils:elog2_0 -> entropy:entropy_data_proc -> *)
(*   bb84:bb84_secret *)
Lemma elog2_0 : elog2 0 = @ENInf R.
Proof.
  by rewrite elog2_le0.
Qed.
(* elog2_fin *)
(* infra: no tex label — entropy-facing extended-real log2 *)
(* path: utils:elog2_fin -> utils:elog2_gt0 -> bb84:stat -> *)
(*   bb84:bb84_secret *)
Lemma elog2_fin (x : R) : 0 < x -> elog2 x \is a fin_num.
Proof.
  by move=> Hx; rewrite elog2_gt0.
Qed.
(* elog2_ninfty *)
(* infra: no tex label — entropy-facing extended-real log2 *)
(* path: utils:elog2_ninfty -> utils:elog2_gt0 -> bb84:stat -> *)
(*   bb84:bb84_secret *)
Lemma elog2_ninfty (x : R) : elog2 x = @ENInf R -> x <= 0.
Proof.
  rewrite /elog2.
  case: ifP => // Hx _.
  by rewrite ltNge in Hx; move/negbFE: Hx.
Qed.
(* log2_pos *)
(* infra: no tex label — fundamental & reusable (mathcomp-style) *)
(* consumer: log2_pos is used downstream by the BB84 secrecy proof. *)
(* path: utils:log2_pos -> bb84:bb84_secret *)
Lemma log2_pos (x : R) : 1 <= x -> 0 <= log2 x.
Proof.
  move=> x_ge1; rewrite /log2.
  apply: divr_ge0; first exact: ln_ge0.
  apply/ltW/ln_gt0.
  by rewrite -nat1r -{1}[1%R]addr0 ltrD2l.
Qed.
(* log2_mul *)
(* infra: no tex label — fundamental & reusable (mathcomp-style) *)
(* consumer: log2_mul is used downstream by the BB84 secrecy proof. *)
(* path: utils:log2_mul -> bb84:bb84_numeric_side -> bb84:bb84_secret *)
Lemma log2_mul (x y : R) : 0 < x -> 0 < y ->
  log2 (x * y) = log2 x + log2 y.
Proof.
  by move=> Hx Hy; rewrite /log2 lnM // mulrDl.
Qed.
(* ================================================================== *)
(* Binary entropy                                                        *)
(* h: x ↦ 0 if x ∉ (0,1); else −x log x − (1−x) log(1−x).             *)
(*                                                                       *)
(* TeX: Nat. Commun. 3:634 (2012), Suppl. Note 1 (binary entropy h).                                       *)
(* ================================================================== *)
(* Binary entropy, standard (Nat. Commun. 3:634 (2012), Suppl. Note 1 (binary entropy h)).
   Returns 0 outside [0,1]; inside, -p log p - (1-p) log (1-p). *)
(* h_bin *)
(* infra: no tex label — fundamental & reusable (mathcomp-style) *)
(* consumer: h_bin is used downstream by the BB84 secrecy proof. *)
Definition h_bin (p : R) : R :=
  if p <= 0 then 0
  else if p >= 1 then 0
  else -(p * log2 p) - ((1 - p) * log2 (1 - p)).
(* ================================================================== *)
(* Van Lint Section 1.4: binomial sum ≤ 2^{n h(t)}                    *)
(* tex: Nat. Commun. 3:634 (2012), Suppl. Lemma 3 (last inequality of lemma:stat)          *)
(* Reference: J.H. van Lint, "Introduction to Coding Theory", §1.4.    *)
(*                                                                      *)
(* For any `t ∈ [0, 1/2]`, the number of binary strings of length `n`   *)
(* whose Hamming weight is at most `floor(n·t)` is bounded by `2^{n·h(t)}`.*)
(* Equivalently, in log2 form: `log2 (\sum_{w ≤ ⌊n·t⌋} C(n,w)) ≤ n · h(t)`. *)
(*                                                                      *)
(* Proof strategy:                                                       *)
(* Jensen-style generating-function argument showing                    *)
(*   (1-t)^{n-w} · t^w ≥ 2^{-n·h(t)}   for `w ≤ ⌊n·t⌋ ≤ n/2`,         *)
(* then summing over `w ∈ [0, ⌊n·t⌋]` yields the bound.                  *)
(* ================================================================== *)
(* --- log2 and floor helpers for van Lint --- *)
(* path: utils:log2_le_pos -> bb84:stat -> bb84:bb84_secret *)
Lemma log2_le_pos (x y : R) : 0 < x -> x <= y -> log2 x <= log2 y.
Proof.
  move=> Hx_pos Hxy.
  have Hy_pos : 0 < y by exact: (lt_le_trans Hx_pos Hxy).
  rewrite /log2 ler_pM2r; last by rewrite invr_gt0 ln2_gt0.
  by rewrite ler_ln.
Qed.
(* elog2_le *)
(* infra: no tex label — entropy-facing extended-real log2 *)
(* path: utils:elog2_le -> entropy:entropy_data_proc -> *)
(*   bb84:bb84_secret *)
Lemma elog2_le (x y : R) : 0 < x -> x <= y -> (elog2 x <= elog2 y)%E.
Proof.
  move=> Hx Hxy.
  have Hy : 0 < y by exact: lt_le_trans Hx Hxy.
  by rewrite !elog2_gt0 // lee_fin; exact: log2_le_pos.
Qed.
(* --- exponent helpers for the binomial generating-function bound --- *)
(* --- prefix-sum positivity helpers --- *)
(* --- Key combinatorial bound: q^m * (prefix binomial sum) ≤ (1 + q)^n --- *)
(* --- van Lint §1.4 entropy bound --- *)
(* tex: Nat. Commun. 3:634 (2012), Suppl. Lemma 3                                            *)
(* math: log2 (Σ_{w ≤ ⌊n·t⌋} C(n,w)) ≤ n · h_bin(t),   for 0 < t < 1/2.  *)
(* Boundary cases (n=0, t=0, t=1/2) are downstream-trivial and can be    *)
(* added via a wrapper when a consumer needs them.                       *)
End FvqkdReal.
Arguments log2 {R} x.
Arguments elog2 {R} x.
Arguments h_bin {R} p.
Arguments ln2_gt0 {R}.
Arguments log2_2 {R}.
Arguments log2K_ln {R} x.
Arguments log2_pow2_nat {R} m.
Arguments neg_log2_inv_pow2_nat {R} m.
Arguments elog2_gt0 {R x} _.
Arguments elog2_le0 {R x} _.
Arguments elog2_0 {R}.
Arguments elog2_fin {R} x.
Arguments elog2_ninfty {R} x.
Arguments log2_pos {R} x.
Arguments log2_mul {R} x y.
Arguments log2_le_pos {R x y} _ _.
Arguments elog2_le {R} x y.
