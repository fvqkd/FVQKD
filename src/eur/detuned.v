(* -------------------------------------------------------------------- *)
(* detuned.v — a genuinely imperfect (q < 1) BB84 source POVM.            *)
(* -------------------------------------------------------------------- *)
(* Module: eur.detuned                                               *)
(*                                                                       *)
(* The library proves the ideal BB84 source (conjugate Hadamard/         *)
(* computational bases) has preparation quality q_of_mx = n, i.e. q = 1  *)
(* per signal (eur/prop.v, q_of_mx_xz_projective_povm).  A non-vacuity   *)
(* witness for the security theorem must instead exhibit a source whose  *)
(* ACTUAL quality is q < 1, exercising the imperfect-source case.        *)
(*                                                                       *)
(* Any 2x2 unitary with uniform entry norms is forced to norm 1/sqrt2    *)
(* (Hadamard, q = 1), so a q < 1 qubit source has NON-uniform entry      *)
(* norms.  We use the rational "3-4-5" rotation V2 = (1/5)[[3,-4],[4,3]], *)
(* whose entry norms are 3/5 and 4/5.  Tensoring n copies and conjugating *)
(* the computational projectors gives an n-qubit X-POVM whose overlap     *)
(* with the computational Z-POVM is at most (16/25)^n, hence             *)
(* q_of_mx >= n * log2(25/16) ~ 0.644 n  (a genuine per-signal quality    *)
(* strictly between 0 and 1).                                            *)
(* -------------------------------------------------------------------- *)
From HB Require Import structures.
From mathcomp Require Import all_boot all_order all_algebra.
From quantum.external Require Import spectral complex.
From mathcomp.reals Require Import reals.
From mathcomp.real_closed Require Import mxtens.
From quantum Require Import mcextra mcaextra notation hermitian quantum
  mxpred extnum mxnorm.
From utils Require Import exports.
From eur Require Import def prop.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory Num.Def.
Local Open Scope ring_scope.
Section DetunedSource.
Variable R : realType.
Notation C := R[i].
(* ================================================================== *)
(* A bounded-entry-norm variant of bigten_entry_norm                    *)
(* ================================================================== *)
(* The library's bigten_entry_norm needs UNIFORM entry norm = c.  For a *)
(* genuinely imperfect (non-Hadamard) qubit unitary the entry norms are *)
(* not uniform, so we only have an upper bound c on each; the n-fold     *)
(* tensor entries are then bounded by c^n.                              *)
Fact bigten_entry_norm_le {m : nat} (A : 'M[C]_m) (k : nat) (c : R) :
  0 <= c ->
  (forall i j, `|A i j| <= c%:C) ->
  forall i j, `|bigten A k i j| <= (c ^+ k)%:C.
Proof.
  move=> Hc HA; elim: k => [|k IH] i j /=.
  - by rewrite (ord1 i) (ord1 j) mxE eqxx normr1 expr0 rmorph1 lexx.
  - rewrite castmxE /= esymK.
  case: (mxtens_indexP (cast_ord (expnSr m k) i)) => i0 i1.
  case: (mxtens_indexP (cast_ord (expnSr m k) j)) => j0 j1.
  rewrite tensmxE normrM exprS rmorphM mulrC.
  apply: ler_pM; [exact: normr_ge0 | exact: normr_ge0 | exact: HA | exact: IH].
Qed.
(* ================================================================== *)
(* The 3-4-5 rotation V2 = (1/5)[[3,-4],[4,3]]                          *)
(* ================================================================== *)
Definition v2_coef (i j : 'I_2) : R :=
  if i == j then 3%:R else if (val i < val j)%N then - (4%:R) else 4%:R.
Definition v2_realmx : 'M[R]_2 := \matrix_(i, j) (5%:R^-1 * v2_coef i j).
Definition v2_mx : 'M[C]_2 := map_mx (real_complex R) v2_realmx.
Lemma v2_realmx_ortho : v2_realmx^T *m v2_realmx = 1%:M.
Proof.
  have H25 : (25%:R : R) != 0 by rewrite pnatr_eq0.
  have HP : forall a b : R, (5%:R^-1 * a) * (5%:R^-1 * b) = (25%:R)^-1 * (a * b)
  by move=> a b; rewrite mulrACA -invfM -natrM.
  apply/matrixP => i j; rewrite !mxE big_ord_recl big_ord1 !mxE /v2_coef.
  case: i => [[|[|i']] Hi]//=; case: j => [[|[|j']] Hj]//=; rewrite ?eqxx/=
  !HP -mulrDr.
  - by rewrite -!natrM -natrD/= mulVf.
  - by rewrite mulrN -!natrM addNr mulr0.
  - by rewrite mulNr -!natrM addNr mulr0.
  - by rewrite mulrNN -!natrM -natrD/= mulVf.
Qed.
Lemma v2_coef_bound (i j : 'I_2) : `|v2_coef i j| <= 4%:R :> R.
Proof.
  rewrite /v2_coef; case: ifP => _.
  - by rewrite ger0_norm ?ler0n // ler_nat.
  case: ifP => _.
  - by rewrite normrN ger0_norm ?ler0n.
  - by rewrite ger0_norm ?ler0n.
Qed.
Lemma v2_entry_norm (i j : 'I_2) : `|v2_mx i j| <= ((5%:R^-1 * 4%:R)%R : R)%:C.
Proof.
  rewrite !mxE normc_real lecR normrM ger0_norm ?invr_ge0 ?ler0n //.
  rewrite ler_pM2l ?invr_gt0 ?ltr0n //; exact: v2_coef_bound.
Qed.
(* Complexification of a real orthogonal matrix is unitary. *)
Lemma real_complexmx_unitary (n : nat) (M : 'M[R]_n) :
  M^T *m M = 1%:M -> map_mx (real_complex R) M \is unitarymx.
Proof.
  move=> HM; have HM' : M *m M^T = 1%:M := mulmx1C HM.
  apply/unitarymxP; apply/matrixP => i j; rewrite !mxE.
  under eq_bigr do rewrite !mxE conjCc conjc_real -rmorphM.
  rewrite -rmorph_sum.
  have ->: (\sum_(k < n) M i k * M j k) = (M *m M^T) i j.
  by rewrite mxE; apply: eq_bigr => k _; rewrite mxE.
  by rewrite HM' !mxE rmorph_nat.
Qed.
Lemma v2_mx_unitary : v2_mx \is unitarymx.
Proof. exact: real_complexmx_unitary v2_realmx_ortho. Qed.
(* ================================================================== *)
(* The detuned X-POVM and its overlap with the computational Z-POVM     *)
(* ================================================================== *)
Definition v2_pow (n : nat) : 'M[C]_(2 ^ n) := bigten v2_mx n.
Lemma v2_pow_unitary (n : nat) : v2_pow n \is unitarymx.
Proof. exact: bigten_unitary v2_mx_unitary. Qed.
Definition x_detuned_povm (n : nat) : 'I_(2 ^ n) -> 'M[C]_(2 ^ n) :=
  fun x => (v2_pow n)^*t *m delta_mx x x *m v2_pow n.
Fact x_detuned_povm_is_povm (n : nat) : is_povm_mx (@x_detuned_povm n).
Proof. exact: unitary_projective_povm_is_povm (v2_pow_unitary n). Qed.
(* Per-entry bound on the n-fold tensor of V2: |(V2^{tensor n}) x z| <= (4/5)^n. *)
Lemma v2_pow_entry_le (n : nat) (x z : 'I_(2 ^ n)) :
  `|v2_pow n x z| <= ((5%:R^-1 * 4%:R) ^+ n : R)%:C.
Proof.
  apply: bigten_entry_norm_le => //; last exact: v2_entry_norm.
  by rewrite mulr_ge0 ?invr_ge0 ?ler0n.
Qed.
(* The overlap is at most ((4/5)^n)^2 = (16/25)^n. *)
Fact overlap_mx_x_detuned_le (n : nat) :
  overlap_mx (@x_detuned_povm n) (@std_projective_povm R (2 ^ n))
    <= ((5%:R^-1 * 4%:R) ^+ n) ^+ 2.
Proof.
  rewrite /overlap_mx.
  have Hbnd : 0 <= (5%:R^-1 * 4%:R : R) ^+ n
  by rewrite exprn_ge0 // mulr_ge0 ?invr_ge0 ?ler0n.
  apply/bigmax_leP; split; first exact: exprn_ge0.
  move=> x _; apply/bigmax_leP; split; first exact: exprn_ge0.
  move=> z _.
  rewrite /x_detuned_povm (unitary_projective_std_i2norm (v2_pow_unitary n) x z).
  have Hre : (@complex.Re R (`|v2_pow n x z|)) <= (5%:R^-1 * 4%:R) ^+ n.
  have H := v2_pow_entry_le x z.
  rewrite lecE in H; move/andP: H => [_ H].
  by rewrite re_realid in H.
  have H0 : 0 <= @complex.Re R (`|v2_pow n x z|).
  by move: (normr_ge0 (v2_pow n x z)); rewrite lecE/= => /andP[_].
  rewrite -exprnP; apply: lerXn2r; rewrite ?nnegrE //.
Qed.
End DetunedSource.
