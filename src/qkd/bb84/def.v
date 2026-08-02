(* def.v — BB84 protocol parameters and security definitions            *)
(* Module: qkd.bb84.def                                       *)
(* Paper: Tomamichel-Lim-Gisin-Renner, Nat. Commun. 3:634 (2012),       *)
(*   "Tight finite-key analysis for quantum cryptography".              *)
(* Covers the protocol definition (Box 1) and the security definitions. *)

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

From utils Require Import exports.
From entropy Require Import def.
From eur Require Import def.
From lhl Require Import def.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Open Scope ring_scope.
Local Open Scope lfun_scope.

Section FvqkdReal.
Variable R : realType.
Notation C := (@hermitian.C R).
Notation chsType := (@chsType R).

Definition bb84_ceil_log_inv_eps (eps_c : R) (m : nat) : Prop :=
  log2 (eps_c^-1) <= m%:R /\
  forall j : nat, log2 (eps_c^-1) <= j%:R -> (m <= j)%N.

Record bb84_protocol := BB84Protocol { bb84_n       : nat; bb84_k       : nat; bb84_round_limit : nat; bb84_l       : nat; bb84_Qtol    : R; bb84_eps_c   : R; bb84_leak_EC : R }.

Definition bb84_mu (n k : nat) (eps : R) : R :=
  Num.sqrt ((((n + k)%:R / (n * k)%:R) * ((k.+1)%:R / k%:R)) *
    ln (eps^-1)).

Definition bb84_h_trunc (x : R) : R :=
  if x <= 0 then 0
  else if 1 / 2 <= x then 1
  else h_bin x.

Definition bb84_key_length_ub (n k : nat)
    (q Qtol eps ebar leak_EC eps_c : R) : R :=
  n%:R * (q - bb84_h_trunc (Qtol + bb84_mu n k eps)) -
  2%:R * log2 ((2%:R * ebar)^-1) -
  leak_EC -
  log2 (2%:R / eps_c).

Section VerificationDefinitions.
Variables (key_count seed_count tag_count : nat).
Variable (hash : 'I_seed_count -> 'I_key_count -> 'I_tag_count).
Variable (corr_prob : 'I_key_count -> 'I_key_count -> R).

Definition verification_collision_prob (x x' : 'I_key_count) : R :=
  #|[set f : 'I_seed_count | hash f x == hash f x']|%:R / seed_count%:R.

Definition p_mismatch : R :=
  \sum_x \sum_(x' | x != x') corr_prob x x' *
    verification_collision_prob x x'.

End VerificationDefinitions.

Section BobZReadout.
Variable (L : finType) (HL : L -> chsType).
Variables (Bq Zp : {set L}).

Definition bob_z_basis_qchannel
    (readout : 'Idx[HL]_Bq -> 'Idx[HL]_Zp) : 'QC[HL]_(Bq, Zp) :=
  QChannel_Build (basis_channel_cptp readout).

Definition bob_z_canonical_readout
    (dim_BqZp : dim ('H[HL]_Bq) = dim ('H[HL]_Zp)) :
    'Idx[HL]_Bq -> 'Idx[HL]_Zp :=
  fun x => @n2i R L HL Zp (cast_ord dim_BqZp (@i2n R L HL Bq x)).

End BobZReadout.

Section WorkRegisters.
Variable (L : finType) (HL : L -> chsType).
Variables (Zkey Bq Zp : {set L}).

Record bb84_aux_regs := BB84AuxRegs { bb84_aux_app : {set L}; bb84_aux_bpp : {set L}; bb84_aux_ciso : {set L}; bb84_aux_cp_src : {set L}; bb84_aux_cpp_src : {set L}; bb84_aux_cp_tgt : {set L}; bb84_aux_cpp_tgt : {set L}; bb84_aux_disZ_app : [disjoint Zkey & bb84_aux_app]; bb84_aux_disZp_bpp : [disjoint Zp & bb84_aux_bpp]; bb84_aux_disZ_bpp : [disjoint Zkey & bb84_aux_bpp]; bb84_aux_disApp_Zp : [disjoint bb84_aux_app & Zp]; bb84_aux_disApp_bpp : [disjoint bb84_aux_app & bb84_aux_bpp]; bb84_aux_dim_app : (dim 'H[HL]_Zkey * dim 'H[HL]_Zkey <= dim 'H[HL]_bb84_aux_app)%N; bb84_aux_dim_bpp : (dim 'H[HL]_Bq * dim 'H[HL]_Zp <= dim 'H[HL]_bb84_aux_bpp)%N; bb84_aux_disZ_ciso : [disjoint Zkey & bb84_aux_ciso]; bb84_aux_disBq_ciso : [disjoint Bq & bb84_aux_ciso]; bb84_aux_disZApp_ciso : [disjoint Zkey :|: bb84_aux_app & bb84_aux_ciso]; bb84_aux_disZpBpp_ciso : [disjoint Zp :|: bb84_aux_bpp & bb84_aux_ciso]; bb84_aux_dim_ZB_ciso : (dim 'H[HL]_(Zkey :|: Bq) <= dim 'H[HL]_bb84_aux_ciso)%N; bb84_aux_dim_ZAppBBpp_ciso : (dim 'H[HL]_((Zkey :|: bb84_aux_app) :|: (Zp :|: bb84_aux_bpp)) <= dim 'H[HL]_bb84_aux_ciso)%N; bb84_aux_disZ_cp_src : [disjoint Zkey & bb84_aux_cp_src]; bb84_aux_disZ_cpp_src : [disjoint Zkey & bb84_aux_cpp_src]; bb84_aux_disBq_cp_src : [disjoint Bq & bb84_aux_cp_src]; bb84_aux_disBq_cpp_src : [disjoint Bq & bb84_aux_cpp_src]; bb84_aux_disCiso_cp_src : [disjoint bb84_aux_ciso & bb84_aux_cp_src]; bb84_aux_disCiso_cpp_src : [disjoint bb84_aux_ciso & bb84_aux_cpp_src]; bb84_aux_disCp_cpp_src : [disjoint bb84_aux_cp_src & bb84_aux_cpp_src]; bb84_aux_dim_Z_cp_src : dim 'H[HL]_Zkey = dim 'H[HL]_bb84_aux_cp_src; bb84_aux_dim_CisoCp_cpp_src : (dim 'H[HL]_bb84_aux_ciso * dim 'H[HL]_bb84_aux_cp_src <= dim 'H[HL]_bb84_aux_cpp_src)%N; bb84_aux_dim_Bq_cpp_src : (dim 'H[HL]_Bq <= dim 'H[HL]_bb84_aux_cpp_src)%N; bb84_aux_disZApp_cp_tgt : [disjoint Zkey :|: bb84_aux_app & bb84_aux_cp_tgt]; bb84_aux_disZApp_cpp_tgt : [disjoint Zkey :|: bb84_aux_app & bb84_aux_cpp_tgt]; bb84_aux_disZpBpp_cp_tgt : [disjoint Zp :|: bb84_aux_bpp & bb84_aux_cp_tgt]; bb84_aux_disZpBpp_cpp_tgt : [disjoint Zp :|: bb84_aux_bpp & bb84_aux_cpp_tgt]; bb84_aux_disCiso_cp_tgt : [disjoint bb84_aux_ciso & bb84_aux_cp_tgt]; bb84_aux_disCiso_cpp_tgt : [disjoint bb84_aux_ciso & bb84_aux_cpp_tgt]; bb84_aux_disCp_cpp_tgt : [disjoint bb84_aux_cp_tgt & bb84_aux_cpp_tgt]; bb84_aux_dim_ZApp_cp_tgt : dim 'H[HL]_(Zkey :|: bb84_aux_app) = dim 'H[HL]_bb84_aux_cp_tgt; bb84_aux_dim_CisoCp_cpp_tgt : (dim 'H[HL]_bb84_aux_ciso * dim 'H[HL]_bb84_aux_cp_tgt <= dim 'H[HL]_bb84_aux_cpp_tgt)%N; bb84_aux_dim_ZpBpp_cpp_tgt : (dim 'H[HL]_(Zp :|: bb84_aux_bpp) <= dim 'H[HL]_bb84_aux_cpp_tgt)%N }.

End WorkRegisters.

Section DelayedMeasurementState.
Variable (L : finType) (HL : L -> chsType).
Variables (Zkey Bq Zp : {set L}).

Record bb84_delayed_measurement_condition (BobZ : 'QC[HL]_(Bq, Zp))
    (rhoZB : 'F[HL]_(Zkey :|: Bq))
    (rhoZZp : 'F[HL]_(Zkey :|: Zp)) := BB84DelayedMeasurementCondition { bb84_dmc_full : 'F[HL]_(Zkey :|: Bq :|: finset.set0); bb84_dmc_full_den1 : bb84_dmc_full \is den1lf; bb84_dmc_source : ptrace_cast3C (disjointX0 Zkey) (disjointX0 Bq) bb84_dmc_full = rhoZB; bb84_dmc_target : ptrace_cast3C (disjointX0 Zkey) (disjointX0 Zp) ((((\:1 : 'SO[HL]_Zkey) :⊗ (BobZ : 'SO[HL]_(Bq, Zp))) :⊗ (\:1 : 'SO[HL]_finset.set0)) bb84_dmc_full) = rhoZZp }.

End DelayedMeasurementState.

Definition eps_correct (p_mismatch eps_c : R) : Prop :=
  p_mismatch <= eps_c.

Section SecurityDefs.
Variable (L : finType) (HL : L -> chsType) (A B : {set L}).
Hypothesis disAB : [disjoint A & B].
Notation S_AB := (A :|: B).

Definition delta_secret (rhoAB : 'F[HL]_S_AB) (Delta : R) : Prop :=
  dist_from_uniform rhoAB <= Delta.

Definition eps_secret (rhoAB : 'F[HL]_S_AB) (eps_s p_abort : R) : Prop :=
  exists Delta : R,
    delta_secret rhoAB Delta /\ (1 - p_abort) * Delta <= eps_s.

Definition eps_secure (p_mismatch eps_c : R) (rhoAB : 'F[HL]_S_AB)
    (eps_s p_abort eps_tot : R) : Prop :=
  eps_correct p_mismatch eps_c /\
  eps_secret rhoAB eps_s p_abort /\
  eps_c + eps_s <= eps_tot.

End SecurityDefs.

Section PublicTranscript.
Variable (L : finType) (HL : L -> chsType).
Variables (S E : {set L}).

Definition bb84_public_assoc (Ppub : {set L}) :
  Ppub :|: (S :|: E) = S :|: (E :|: Ppub).
Proof.
  by apply/setP=> x; rewrite !inE; case: (x \in S); case: (x \in E); case: (x \in Ppub). Defined.

Record bb84_public_leakage
    (Ppub : {set L}) (rhoXE : 'F[HL]_(S :|: E)) (leak : R) :=
  BB84PublicLeakage { bb84_public_disSP : [disjoint S & Ppub]; bb84_public_disEP : [disjoint E & Ppub]; bb84_public_disP_SE : [disjoint Ppub & (S :|: E)]; bb84_public_state : 'F[HL]_(Ppub :|: (S :|: E)); bb84_public_state_psd : bb84_public_state \is psdlf; bb84_public_state_tr : @complex.Re R (\Tr bb84_public_state) <= 1; bb84_public_state_classical : forall x x' : 'Idx[HL]_Ppub, x' != x -> (([> deltav x ; deltav x <] \O (\1 : 'F_(S :|: E))) \o bb84_public_state \o ([> deltav x' ; deltav x' <] \O (\1 : 'F_(S :|: E)))) = 0; bb84_public_state_marginal : ptrace_castl bb84_public_disP_SE bb84_public_state = rhoXE; bb84_public_state_pa_cq : let eq_pub_assoc := bb84_public_assoc Ppub in @is_cq_state R L HL S (E :|: Ppub) (castlf (eq_pub_assoc, eq_pub_assoc) bb84_public_state); bb84_public_leak_bound : log2 (dim 'H[HL]_Ppub)%:R <= leak }.

End PublicTranscript.

End FvqkdReal.

Arguments bb84_protocol {R}.
Arguments bb84_n {R} _.
Arguments bb84_k {R} _.
Arguments bb84_round_limit {R} _.
Arguments bb84_l {R} _.
Arguments bb84_Qtol {R} _.
Arguments bb84_eps_c {R} _.
Arguments bb84_leak_EC {R} _.


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

Fact bb84_mu_ge0 (n k : nat) (eps : R) :
  (0 < n)%N -> (0 < k)%N -> 0 < eps -> 0 <= bb84_mu n k eps.
Proof. by move=> *; rewrite /bb84_mu sqrtr_ge0. Qed.

Lemma bb84_bad_event_prob_le (n k : nat) (z z' : bitstr (k + n)) (eps : R) :
  (0 < n)%N -> (0 < k)%N -> 0 < eps -> Pr_event (fun pi : 'S_(k + n) => @uniform_perm_mu R (k + n) pi)
    (@perm_pair_deviation_event R n k z z' (bb84_mu n k eps)) <= eps ^+ 2.
Proof.
  move=> Hn_pos Hk_pos Heps_pos; have Hmu_nonneg : 0 <= bb84_mu n k eps by exact: bb84_mu_ge0 Hn_pos Hk_pos Heps_pos.
  pose mid := expR (- 2%:R * (((k * n)%:R / (k + n)%:R) * (k%:R / k.+1%:R) * (bb84_mu n k eps) ^+ 2)).
  have Htail : Pr_event (fun pi : 'S_(k + n) => @uniform_perm_mu R (k + n) pi) (@perm_pair_deviation_event R n k z z' (bb84_mu n k eps)) <= mid by exact: (@serfling_uniform_perm_pair_deviation_tail R n k z z' (bb84_mu n k eps) Hn_pos Hk_pos Hmu_nonneg).
  have Hexp : mid <= eps ^+ 2.
  { rewrite /mid addnC.
    have Hcoeff_nonneg : 0 <= ((k * n)%:R / (n + k)%:R) * (k%:R / k.+1%:R) :> R by apply: mulr_ge0; rewrite divr_ge0.
    have Hmu_sq_nonneg : 0 <= (bb84_mu n k eps) ^+ 2 by rewrite expr2; exact: sqr_ge0.
    have [Heps_le1|Heps_gt1] := lerP eps 1.
    - have Hkn_pos : 0 < (n * k)%:R :> R by rewrite natrM; apply: mulr_gt0; rewrite ltr0n.
      have HkR_pos : 0 < k%:R :> R by rewrite ltr0n.
      have HN_pos : 0 < (n + k)%:R :> R by rewrite ltr0n addn_gt0 Hn_pos.
      have Heps_inv_ge1 : 1 <= eps^-1 by rewrite invf_ge1.
      have Hln_nonneg : 0 <= ln (eps^-1) by exact: ln_ge0 Heps_inv_ge1.
      have Hmu_arg_nonneg : 0 <= (((n + k)%:R / (n * k)%:R) * ((k.+1)%:R / k%:R)) * ln (eps^-1) :> R.
      { by apply: mulr_ge0; [apply: mulr_ge0; rewrite divr_ge0 ?ler0n | exact: Hln_nonneg]. } have Hmu_sqE : (bb84_mu n k eps) ^+ 2 = (((n + k)%:R / (n * k)%:R) * ((k.+1)%:R / k%:R)) * ln (eps^-1) by rewrite /bb84_mu sqr_sqrtr.
      have Hcancel : (((k * n)%:R / (n + k)%:R) * (k%:R / k.+1%:R) * (bb84_mu n k eps) ^+ 2) = ln (eps^-1).
      { rewrite Hmu_sqE.
        have /lt0r_neq0 Hkn_neq0 : 0 < (n * k)%:R :> R by exact: Hkn_pos.
        have /lt0r_neq0 Hk_neq0 : 0 < k%:R :> R by exact: HkR_pos.
        have /lt0r_neq0 HN_neq0 : 0 < (n + k)%:R :> R by exact: HN_pos.
        have /lt0r_neq0 Hk1_neq0 : 0 < k.+1%:R :> R by rewrite ltr0Sn.
        pose A : R := (k * n)%:R / (n + k)%:R.
        pose B : R := k%:R / k.+1%:R.
        pose C : R := (n + k)%:R / (n * k)%:R.
        pose D : R := k.+1%:R / k%:R.
        pose L := ln (eps^-1).
        change ((A * B) * ((C * D) * L) = L).
        have HAC : A * C = 1.
        { rewrite /A /C -mulrA [((n + k)%:R^-1 * ((n + k)%:R / (n * k)%:R))]mulrA.
          rewrite [((n + k)%:R^-1 * (n + k)%:R)]mulrC mulfV // mul1r.
          have -> : (k * n)%:R = (n * k)%:R by rewrite mulnC. by rewrite divff. } have HBD : B * D = 1.
        { rewrite /B /D -mulrA [(k.+1%:R^-1 * (k.+1%:R / k%:R))]mulrA.
          by rewrite [(k.+1%:R^-1 * k.+1%:R)]mulrC mulfV // mul1r divff. } have Hrearr : (A * B) * ((C * D) * L) = ((A * C) * (B * D)) * L.
        { by rewrite -[((C * D) * L)]mulrA -mulrA [B * (C * (D * L))]mulrCA -!mulrA. } by rewrite Hrearr HAC HBD !mul1r. } have HlnV : ln (eps^-1) = - ln eps by exact: lnV Heps_pos.
      rewrite Hcancel HlnV. have -> : - 2%:R * - ln eps = 2%:R * ln eps by rewrite mulNr mulrN opprK.
      by rewrite expRM_natl (lnK Heps_pos).
    - have Hexp_le1 : expR (- 2%:R * (((k * n)%:R / (n + k)%:R) * (k%:R / k.+1%:R) * (bb84_mu n k eps) ^+ 2)) <= 1.
      { have -> : 1 = expR 0 :> R by rewrite expR0.
        rewrite ler_expR expR0 mulNr oppr_le0.
        have H2_nonneg : 0 <= 2%:R :> R by apply: ltW; change (0 < (1.+1)%:R :> R); rewrite ltr0Sn.
        have Hinner_nonneg : 0 <= (((k * n)%:R / (n + k)%:R * (k%:R / k.+1%:R)) * bb84_mu n k eps ^+ 2) :> R.
        { exact: mulr_ge0 Hcoeff_nonneg Hmu_sq_nonneg. } change (0 <= 2%:R * (((k * n)%:R / (n + k)%:R * (k%:R / k.+1%:R)) * bb84_mu n k eps ^+ 2) :> R).
        exact: mulr_ge0 H2_nonneg Hinner_nonneg. } apply: (le_trans Hexp_le1); rewrite expr2 -[X in X <= _]mul1r.
      by apply: (ler_pM ler01 ler01); exact: ltW Heps_gt1. }
exact: le_trans Htail Hexp. Qed.

Lemma bb84_bbkey (n k : nat) (z z' : bitstr (k + n)) (Qtol eps : R) :
  (0 < n)%N -> (0 < k)%N -> 0 < eps -> let mu := bb84_mu n k eps in
  let pass_event : {set 'S_(k + n)} :=
    [set pi : 'S_(k + n) | @perm_pair_sample_err R n k z z' pi <= Qtol] in
  let p_pass :=
    Pr_event (fun pi : 'S_(k + n) => @uniform_perm_mu R (k + n) pi) pass_event in
  0 < p_pass -> Pr_cond
    (fun pi : 'S_(k + n) => @uniform_perm_mu R (k + n) pi)
    (@perm_pair_deviation_event R n k z z' mu) pass_event <=
      eps ^+ 2 / p_pass.
Proof.
  move=> Hn_pos Hk_pos Heps_pos /= Hppass_pos.
  set pass_event : {set 'S_(k + n)} := [set pi : 'S_(k + n) | @perm_pair_sample_err R n k z z' pi <= Qtol] in Hppass_pos *.
  set p_pass := Pr_event (fun pi : 'S_(k + n) => @uniform_perm_mu R (k + n) pi) pass_event in Hppass_pos *.
  have Hbad_prob : Pr_event (fun pi : 'S_(k + n) => @uniform_perm_mu R (k + n) pi) (@perm_pair_deviation_event R n k z z' (bb84_mu n k eps)) <= eps ^+ 2 by exact: (bb84_bad_event_prob_le z z' Hn_pos Hk_pos Heps_pos).
  exact: (@Pr_cond_le_event_div R 'S_(k + n) (fun pi : 'S_(k + n) => @uniform_perm_mu R (k + n) pi) (@perm_pair_deviation_event R n k z z' (bb84_mu n k eps)) pass_event (eps ^+ 2) (fun pi => @uniform_perm_mu_nonneg R (k + n) pi) Hppass_pos Hbad_prob). Qed.

Fact bb84_bbkey_mix (n k : nat)
    (W : 'I_(2 ^ (k + n)) -> 'I_(2 ^ (k + n)) -> R)
    (Qtol eps : R) :
  (0 < n)%N -> (0 < k)%N -> 0 < eps -> (forall z z', 0 <= W z z') -> \sum_z \sum_z' W z z' = 1 ->
  \sum_(z : 'I_(2 ^ (k + n)))
    \sum_(z' : 'I_(2 ^ (k + n)))
      W z z' *
        Pr_event (fun pi : 'S_(k + n) => @uniform_perm_mu R (k + n) pi)
          ((@perm_pair_deviation_event R n k
              (ord_to_bitstring z) (ord_to_bitstring z')
              (bb84_mu n k eps)) :&:
           (@perm_pair_sample_le_event R n k
              (ord_to_bitstring z) (ord_to_bitstring z') Qtol)) <= eps ^+ 2.
Proof.
  move=> Hn_pos Hk_pos Heps_pos HW_ge0 HW_sum1.
  have Heps_sum : \sum_(z : 'I_(2 ^ (k + n))) \sum_(z' : 'I_(2 ^ (k + n))) W z z' * eps ^+ 2 = eps ^+ 2.
  { under eq_bigr do rewrite -mulr_suml. by rewrite -mulr_suml HW_sum1 mul1r. } rewrite -Heps_sum; apply: ler_sum => z _; apply: ler_sum => z' _.
  apply: ler_pM.
  1,2,3: by [exact: HW_ge0 | rewrite /Pr_event; apply: sumr_ge0 => pi _; exact: uniform_perm_mu_nonneg | exact: lexx].
  - apply: le_trans.
    + apply: (@Pr_event_cap_le R 'S_(k + n) (fun pi : 'S_(k + n) => @uniform_perm_mu R (k + n) pi) (@perm_pair_deviation_event R n k (ord_to_bitstring z) (ord_to_bitstring z') (bb84_mu n k eps)) (@perm_pair_sample_le_event R n k (ord_to_bitstring z) (ord_to_bitstring z') Qtol)).
      exact: uniform_perm_mu_nonneg.
    + exact: (bb84_bad_event_prob_le (ord_to_bitstring z) (ord_to_bitstring z') Hn_pos Hk_pos Heps_pos). Qed.

End FvqkdReal.
