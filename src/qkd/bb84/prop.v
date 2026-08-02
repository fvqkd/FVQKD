(* prop.v — BB84 statistical and chain-rule lemmas                      *)
(* Module: qkd.bb84.prop                                      *)
(* Paper: Tomamichel-Lim-Gisin-Renner, Nat. Commun. 3:634 (2012),       *)
(*   "Tight finite-key analysis for quantum cryptography".              *)
(* Covers Suppl. Lem 3 and the Suppl. Thm 2 chain-rule footnote.        *)

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
From Stdlib Require Import Psatz.
From quantum Require Import mcextra mcaextra notation hermitian quantum
  cpo mxpred extnum ctopology svd mxnorm hspace qtype.
From quantum.dirac Require Import hstensor.

Import Order.TTheory GRing.Theory Num.Theory Num.Def MxLownerOrder.
Import VectorInternalTheory.

From utils Require Import exports.
From entropy Require Import def prop.
From entropy.smooth Require Import class prop dpi.
From qkd.bb84 Require Import def model.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Open Scope ring_scope.
Local Open Scope lfun_scope.

Section FvqkdReal.
Variable R : realType.
Notation C := (@hermitian.C R).
Notation chsType := (@chsType R).

Local Lemma sqrtr_inv_div1 (x : R) : 0 < x -> Num.sqrt x^-1 = 1 / Num.sqrt x.
Proof. move=> Hx; have Hrhs_ge0 : 0 <= 1 / Num.sqrt x. { apply: divr_ge0. - by rewrite ler01. - exact: sqrtr_ge0 x. } have Hsq_rhs : (1 / Num.sqrt x) ^+ 2 = 1 / x. { rewrite !div1r exprVn. by rewrite (sqr_sqrtr (ltW Hx)). } rewrite -div1r -Hsq_rhs. by rewrite sqrtr_sqr ger0_norm. Qed.

Local Lemma sqrtr_sq_div (e x : R) :
  0 <= e -> 0 < x -> Num.sqrt (e ^+ 2 / x) = e / Num.sqrt x.
Proof. move=> He Hx; rewrite sqrtrM ?sqr_ge0 ?invr_ge0 ?ltW //. rewrite sqrtr_sqr ger0_norm // (sqrtr_inv_div1 Hx). by rewrite div1r. Qed.

Local Lemma ltr1_of_sqrt_lt1 (x : R) : Num.sqrt x < 1 -> x < 1.
Proof. move=> Hs; case: (ltP x 1) => // Hge1. have Hsqrt_ge1 : 1 <= Num.sqrt x. { rewrite -sqrtr1. exact: ler_wsqrtr Hge1. } have := lt_le_trans Hs Hsqrt_ge1. by rewrite ltxx. Qed.

Lemma bb84_h_trunc_nonneg (x : R) : 0 <= bb84_h_trunc x.
Proof.
  rewrite /bb84_h_trunc; case: (lerP x 0) => Hx_nonpos //.
  case: (lerP (1 / 2) x) => Hx_half; first exact: ler01.
  rewrite /h_bin; case: (lerP x 0) => Hgt0 //; case: (lerP 1 x) => Hlt1 //.
  have Hop_pos : 0 < 1 - x by rewrite subr_gt0.
  have Hop_le1 : 1 - x <= 1 by rewrite lerBlDr lerDl ltW.
  have Hlogp_le0 : log2 x <= 0 by rewrite /log2; apply: mulr_le0_ge0; [apply: ln_le0; exact: ltW Hlt1 | rewrite invr_ge0 ltW// ln2_gt0].
  have Hlogop_le0 : log2 (1 - x) <= 0 by rewrite /log2; apply: mulr_le0_ge0; [exact: ln_le0 Hop_le1 | rewrite invr_ge0 ltW// ln2_gt0].
  have Hterm1_ge0 : 0 <= - (x * log2 x) by rewrite oppr_ge0; exact: mulr_ge0_le0 (ltW Hgt0) Hlogp_le0.
  have Hterm2_ge0 : 0 <= - ((1 - x) * log2 (1 - x)) by rewrite oppr_ge0; exact: mulr_ge0_le0 (ltW Hop_pos) Hlogop_le0.
  exact: addr_ge0 Hterm1_ge0 Hterm2_ge0. Qed.

Local Lemma bb84_mu_coeff_ge0 (n k : nat) :
  0 <= (((n + k)%:R / (n * k)%:R) * ((k.+1)%:R / k%:R) : R).
Proof. apply: mulr_ge0; by rewrite divr_ge0 ?ler0n. Qed.

Local Lemma bb84_mu_coeffE (n k : nat) :
  (0 < n)%N -> (0 < k)%N -> (((n + k)%:R / (n * k)%:R) * ((k.+1)%:R / k%:R) : R) =
  (n%:R^-1 + k%:R^-1) * (1 + k%:R^-1).
Proof.
  move=> Hn Hk; have Hn_pos : 0 < n%:R :> R by rewrite ltr0n.
  have Hk_pos : 0 < k%:R :> R by rewrite ltr0n.
  have Hn_neq0 : n%:R != 0 :> R := lt0r_neq0 Hn_pos.
  have Hk_neq0 : k%:R != 0 :> R := lt0r_neq0 Hk_pos.
  have Hsum : (n + k)%:R / (n * k)%:R = n%:R^-1 + k%:R^-1 :> R.
  { have Hden_pos : 0 < (n * k)%:R :> R by rewrite natrM mulr_gt0.
    have Hden_neq0 : (n * k)%:R != 0 :> R := lt0r_neq0 Hden_pos.
    apply: (mulIf Hden_neq0); rewrite divfK // natrD natrM.
    have Hleft : n%:R^-1 * (n%:R * k%:R) = k%:R :> R by rewrite mulrA mulVf ?mul1r.
    have Hright : k%:R^-1 * (n%:R * k%:R) = n%:R :> R by rewrite mulrCA mulVf ?mulr1.
    by rewrite mulrDl Hleft Hright addrC. } have Hstep : k.+1%:R / k%:R = 1 + k%:R^-1 :> R.
  { apply: (mulIf Hk_neq0). rewrite divfK // mulrDl mul1r mulVf ?mul1r //. by rewrite -addn1 natrD. } by rewrite Hsum Hstep. Qed.

Local Lemma bb84_mu_coeff_anti_k (n k z : nat) :
  (0 < n)%N -> (0 < k <= z)%N -> (((n + z)%:R / (n * z)%:R) * ((z.+1)%:R / z%:R) : R) <=
  (((n + k)%:R / (n * k)%:R) * ((k.+1)%:R / k%:R) : R).
Proof.
  move=> Hn /andP[Hk Hkz]; have Hz : (0 < z)%N := leq_trans Hk Hkz.
  rewrite !(bb84_mu_coeffE Hn) //.
  apply: ler_pM.
  1,2,3,4: by [apply: addr_ge0; rewrite invr_ge0 ler0n | apply: addr_ge0; [exact: ler01 | rewrite invr_ge0 ler0n] | apply: lerD; [exact: lexx | rewrite lef_pV2 ?posrE ?ltr0n ?ler_nat]]. Qed.

Fact bb84_mu_anti_k (n k z : nat) (eps : R) :
  (0 < k <= z)%N -> 0 < eps -> bb84_mu n z eps <= bb84_mu n k eps.
Proof.
  move=> Hkz Heps; have [->|Hn] := posnP n.
  - rewrite /bb84_mu.
    have Hcoeff_z0 : (((0 + z)%:R / (0 * z)%:R) * ((z.+1)%:R / z%:R) = 0 :> R) by rewrite add0n mul0n /= invr0 mulr0 mul0r.
    have Hcoeff_k0 : (((0 + k)%:R / (0 * k)%:R) * ((k.+1)%:R / k%:R) = 0 :> R) by rewrite add0n mul0n /= invr0 mulr0 mul0r.
    by rewrite Hcoeff_z0 Hcoeff_k0 !mul0r !sqrtr0.
  - rewrite /bb84_mu.
    have Hcoeff_le := bb84_mu_coeff_anti_k Hn Hkz.
    have [Heps_le1|Heps_gt1] := lerP eps 1.
    + apply: ler_wsqrtr.
      have Hln_nonneg : 0 <= ln ((eps^-1)%R) by apply: ln_ge0; rewrite -[1]invr1 lef_pV2 ?posrE ?ltr01.
      exact: ler_pM (bb84_mu_coeff_ge0 n z) Hln_nonneg Hcoeff_le (lexx _).
    + have Heps_inv_le1 : (eps^-1)%R <= 1 by rewrite -[1]invr1 lef_pV2 ?posrE ?ltr01 ?ltW.
      have Hln_nonpos : ln ((eps^-1)%R) <= 0 := ln_le0 Heps_inv_le1.
      have Harg_z : ((((n + z)%:R / (n * z)%:R) * ((z.+1)%:R / z%:R)) * ln ((eps^-1)%R) <= 0 :> R).
      { exact: mulr_ge0_le0 (bb84_mu_coeff_ge0 n z) Hln_nonpos. } have Harg_k : ((((n + k)%:R / (n * k)%:R) * ((k.+1)%:R / k%:R)) * ln ((eps^-1)%R) <= 0 :> R).
      { exact: mulr_ge0_le0 (bb84_mu_coeff_ge0 n k) Hln_nonpos. } have -> : Num.sqrt ((((n + z)%:R / (n * z)%:R) * ((z.+1)%:R / z%:R)) * ln ((eps^-1)%R)) = 0 :> R by apply/eqP; rewrite sqrtr_eq0 Harg_z.
      have -> : Num.sqrt ((((n + k)%:R / (n * k)%:R) * ((k.+1)%:R / k%:R)) * ln ((eps^-1)%R)) = 0 :> R by apply/eqP; rewrite sqrtr_eq0 Harg_k.
      exact: lexx. Qed.

Fact bb84_key_length_has_sup (P : @bb84_protocol R)
    (q eps_s : R) :
  0 < eps_s -> eps_s <= 1 -> has_sup (fun M : R =>
    exists eps ebar : R,
      0 < eps /\ eps < 1 /\ 0 < ebar /\ eps + ebar <= eps_s /\
      M = ((floor (bb84_key_length_ub (bb84_n P) (bb84_k P) q
        (bb84_Qtol P) eps ebar (bb84_leak_EC P)
        (bb84_eps_c P)))%:~R : R)).
Proof.
  move=> eps_s_pos eps_s_le1; split.
  - exists ((floor (bb84_key_length_ub (bb84_n P) (bb84_k P) q (bb84_Qtol P) (eps_s / 2%:R) (eps_s / 2%:R) (bb84_leak_EC P) (bb84_eps_c P)))%:~R : R).
    exists (eps_s / 2%:R), (eps_s / 2%:R).
    split; first by rewrite divr_gt0 ?ltr0n.
    split.
    { rewrite ltr_pdivrMr; last by rewrite ltr0n.
      have H2 : (1 : R) < 1 * 2%:R by rewrite mul1r ltr1n.
      exact: (le_lt_trans eps_s_le1 H2). } split; first by rewrite divr_gt0 ?ltr0n.
    by split; first by rewrite -(splitr eps_s) lexx.
  - exists ((bb84_n P)%:R * q + 2%:R * log2 (2%:R * eps_s) - bb84_leak_EC P - log2 (2%:R / bb84_eps_c P)).
    move=> M [eps [ebar [eps_pos [_ [ebar_pos [Hbudget ->]]]]]].
    have Hub : bb84_key_length_ub (bb84_n P) (bb84_k P) q (bb84_Qtol P) eps ebar (bb84_leak_EC P) (bb84_eps_c P) <= (bb84_n P)%:R * q + 2%:R * log2 (2%:R * eps_s) - bb84_leak_EC P - log2 (2%:R / bb84_eps_c P).
    { have Hebar_le_eps_s : ebar <= eps_s. { apply: le_trans Hbudget. by rewrite lerDr ltW. } have Harg_ebar_pos : 0 < 2%:R * ebar by rewrite mulr_gt0 ?ltr0n. have Hlog2_inv_ebar : log2 ((2%:R * ebar)^-1) = - log2 (2%:R * ebar) by rewrite /log2 (lnV Harg_ebar_pos) mulNr. have Hbase : (bb84_n P)%:R * (q - bb84_h_trunc (bb84_Qtol P + bb84_mu (bb84_n P) (bb84_k P) eps)) <= (bb84_n P)%:R * q. { rewrite mulrBr lerBlDr lerDl. apply: mulr_ge0; first by rewrite ler0n. exact: bb84_h_trunc_nonneg. } have Harg_le : 2%:R * ebar <= 2%:R * eps_s by rewrite ler_pM2l ?ltr0n. have Hlog : log2 (2%:R * ebar) <= log2 (2%:R * eps_s) by exact: log2_le_pos Harg_ebar_pos Harg_le. have H2log : 2%:R * log2 (2%:R * ebar) <= 2%:R * log2 (2%:R * eps_s) by rewrite ler_pM2l ?ltr0n. rewrite /bb84_key_length_ub Hlog2_inv_ebar mulrN opprK. by rewrite !lerD2r; exact: lerD Hbase H2log. } by apply: (le_trans (@Rfloor_le R _)); exact: Hub. Qed.

Lemma bb84_key_length_sup_witness (P : @bb84_protocol R)
    (q eps_s target : R) :
  0 < eps_s -> eps_s <= 1 -> target \is a int_num -> target <= sup (fun M : R =>
    exists eps ebar : R,
      0 < eps /\ eps < 1 /\ 0 < ebar /\ eps + ebar <= eps_s /\
      M = ((floor (bb84_key_length_ub (bb84_n P) (bb84_k P) q
        (bb84_Qtol P) eps ebar (bb84_leak_EC P)
        (bb84_eps_c P)))%:~R : R)) -> exists eps ebar : R,
    0 < eps /\ eps < 1 /\ 0 < ebar /\ eps + ebar <= eps_s /\
    target <= ((floor (bb84_key_length_ub (bb84_n P) (bb84_k P) q
      (bb84_Qtol P) eps ebar (bb84_leak_EC P)
      (bb84_eps_c P)))%:~R : R).
Proof.
  move=> eps_s_pos eps_s_le1 Htarget_int Htarget_sup.
  have Hsup := bb84_key_length_has_sup P q eps_s_pos eps_s_le1.
  have [M HM Hnear] := sup_adherent ltr01 Hsup.
  case: HM => eps [ebar [eps_pos [eps_lt1 [ebar_pos [Hbudget HM]]]]].
  exists eps, ebar; repeat split=> //.
  have Htarget_lt_M1 : target < M + 1 by apply: (le_lt_trans Htarget_sup); move: Hnear; rewrite ltrBlDr.
  have HM_int : M \is a int_num by rewrite HM intr_int.
  rewrite -HM; move: Htarget_lt_M1; move: Htarget_int HM_int => /intrP[ti ->] /intrP[mi ->].
  rewrite -{3}[1]mulr1z.
  by rewrite -intrD !(ltr_int, ler_int) ltzD1. Qed.

Fact verification_collision_prob_le1 key_count seed_count tag_count
    (hash : 'I_seed_count -> 'I_key_count -> 'I_tag_count)
    (x x' : 'I_key_count) :
  @verification_collision_prob R key_count seed_count tag_count hash x x' <= 1.
Proof.
  case: seed_count hash => [|seed_count] hash.
  - rewrite /verification_collision_prob.
    have Hcard0 : #|[set f : 'I_0 | hash f x == hash f x']| = 0%N.
    { apply/eqP; rewrite cards_eq0; apply/eqP; apply/setP => f. by case: f. } by rewrite Hcard0 mul0r ler01.
  - rewrite /verification_collision_prob.
    set good := [set f : 'I_seed_count.+1 | hash f x == hash f x'].
    have Hprob : ((#|good|%:R : R) * (seed_count.+1%:R)^-1 <= 1).
    { have Hle : Pr_event (@uniform_fin_mu R 'I_seed_count.+1) good <= 1.
      { apply: Pr_event_le1; first exact: uniform_fin_mu_nonneg.
        by apply: uniform_fin_mu_sum1; rewrite card_ord. } by move: Hle; rewrite (@Pr_event_uniform_fin R 'I_seed_count.+1 good) card_ord. } change ((#|good|%:R : R) * (seed_count.+1%:R)^-1 <= 1); exact: Hprob. Qed.

Fact projected_mx_normalized_witness {na nb : nat}
    (P rho : 'M[C]_(na * nb)) :
  P \is projmx -> rho \is psdmx -> @complex.Re R (\tr rho) = 1 -> let raw := P *m rho *m P in
  let mass := @complex.Re R (\tr raw) in
  0 < mass -> let tau := (mass^-1)%:C *: raw in
  [/\ tau \is psdmx,
      @complex.Re R (\tr tau) = 1,
      tau *m P = tau &
      pur_dist_mx tau rho = Num.sqrt (1 - mass)].
Proof.
  move=> HPproj Hrho_psd Hrho_tr1 /= Hmass_pos; pose raw := P *m rho *m P.
  pose mass := @complex.Re R (\tr raw).
  pose tau := (mass^-1)%:C *: raw.
  have Hmass_nz : mass != 0 := lt0r_neq0 Hmass_pos.
  have Hmass_unit : mass \is a GRing.unit by rewrite unitfE.
  have /projmxP_id [/hermmxP HPherm HPid] := HPproj.
  have Hraw_psd : raw \is psdmx.
  { rewrite /raw; have -> : P *m rho *m P = P *m rho *m P^*t by rewrite [P in _ *m _ *m P]HPherm.
    exact: psdmx_bimap_closed_gen Hrho_psd. } have Hraw_trace_real : \tr raw \is Num.real := ger0_real (psdmx_trace Hraw_psd).
  have Hraw_traceE : \tr raw = mass%:C by rewrite /mass -(RRe_real Hraw_trace_real).
  have Htau_psd : tau \is psdmx.
  { rewrite /tau. apply: psdmxZ; last exact: Hraw_psd. by rewrite lecR invr_ge0 ltW. } have Htau_tr1 : @complex.Re R (\tr tau) = 1.
  { rewrite /tau mxtraceZ Hraw_traceE /= (mulVr Hmass_unit). by rewrite mul0r subr0. } have Hraw_mulP : raw *m P = raw. { by rewrite /raw -mulmxA HPid. } have Htau_mulP : tau *m P = tau. { by rewrite /tau -scalemxAl Hraw_mulP. } have Hfid_raw : @complex.Re R (trnorm (sqrtmx raw *m sqrtmx rho)) = mass.
  { have [Hfid _] := fid_iv_proj_mx HPproj Hrho_psd Hrho_psd.
    by move: Hfid; rewrite /raw => Hfid; rewrite Hfid (sqrtmxK Hraw_psd) (psdmx_trnorm Hraw_psd) Hraw_traceE. } have Hfid_tau : @complex.Re R (trnorm (sqrtmx tau *m sqrtmx rho)) = Num.sqrt mass.
  { rewrite /tau.
    have Hmass_inv_ge0 : 0 <= (mass^-1)%R by rewrite invr_ge0; exact: ltW Hmass_pos.
    rewrite (sqrtmxZ_nn Hmass_inv_ge0 Hraw_psd) -scalemxAl trnormZ.
    rewrite (ger0_norm (x := (Num.sqrt (mass^-1))%:C)); last by rewrite lecR sqrtr_ge0.
    have Hnorm_real : \tr| sqrtmx raw *m sqrtmx rho | \is Num.real := schnorm_real 1 (sqrtmx raw *m sqrtmx rho).
    rewrite -(RRe_real Hnorm_real) -rmorphM /= Hfid_raw.
    have Hsqrt_inv := sqrtr_inv_div1 Hmass_pos.
    have HmassE : mass = (Num.sqrt mass) ^+ 2 by rewrite sqr_sqrtr // ltW.
    have Hsqrt_nz : Num.sqrt mass != 0. { rewrite sqrtr_eq0. move: Hmass_pos; by rewrite ltNge. } have Hsqrt_unit : Num.sqrt mass \is a GRing.unit by rewrite unitfE.
    rewrite Hsqrt_inv [X in _ * X]HmassE expr2.
    by rewrite div1r mulrA (mulVr Hsqrt_unit) mul1r. } have Hgf : gfidelity tau rho = Num.sqrt mass.
  { rewrite (alt_gfid_gen Htau_psd Hrho_psd).
    have Htau_corr0 : Num.sqrt (@complex.Re R (1 - \tr tau)) = 0 by rewrite raddfB /= Htau_tr1 subrr sqrtr0.
    have Hrho_corr0 : Num.sqrt (@complex.Re R (1 - \tr rho)) = 0 by rewrite raddfB /= Hrho_tr1 subrr sqrtr0.
    by rewrite Hfid_tau Htau_corr0 Hrho_corr0 mul0r addr0. } have Hsqrt_sq : Num.sqrt mass ^ 2 = mass. { change (Num.sqrt mass ^+ 2 = mass). by rewrite sqr_sqrtr // ltW. } by split=> //; rewrite /pur_dist_mx Hgf Hsqrt_sq. Qed.

Fact bb84_hmax_good_projector_bound (n_key : nat) (delta : R)
    (rho : 'M[C]_((2 ^ n_key) * (2 ^ n_key))) :
  (0 < n_key)%N -> 0 < delta -> rho \is psdmx -> @complex.Re R (\tr rho) = 1 ->
  rho *m @bb84_good_projector R n_key delta = rho -> hmax_mx rho <= n_key%:R * bb84_h_trunc delta.
Proof.
  move=> Hn_key_pos Hdelta_pos Hrho_psd Hrho_tr1 HrhoP; pose key_dim := (2 ^ n_key)%N.
  pose P_good : 'M[C]_(key_dim * key_dim) := @bb84_good_projector R n_key delta.
  pose good_pair (x x' : 'I_key_dim) := @relative_hamming_ball R n_key delta x x'.
  pose good_cond_count (x' : 'I_key_dim) := @relative_hamming_ball_count R n_key delta x'.
  pose good_cond_count_max := @relative_hamming_ball_count_max R n_key delta.
  have HP_good_psd : P_good \is psdmx. { rewrite /P_good. exact: bb84_good_projector_psdmx. } have HP_good_herm : P_good \is hermmx := psdmx_herm HP_good_psd.
  have HP_good_proj : P_good \is projmx. { rewrite /P_good. exact: bb84_good_projector_proj. } have /projmxP_id [_ HP_good_id] := HP_good_proj.
  have Hptrace1_P_good_le_max : ptrace1 P_good <= (good_cond_count_max)%:R%:C *: (1%:M : 'M[C]_key_dim).
  { rewrite /P_good /good_cond_count_max. exact: bb84_good_projector_ptrace1_le_max. } have Hcount_max_ge1_nat : (1 <= good_cond_count_max)%N.
  { pose x0 : 'I_key_dim := @Ordinal key_dim 0 (expn_gt0 2 n_key). have Hself : good_pair x0 x0. { rewrite /good_pair /relative_hamming_ball. have Hdhxx : d_ham (ord_to_bitstring x0) (ord_to_bitstring x0) = 0%N. { rewrite /d_ham /wt_ham /xor_str. apply/eqP. rewrite cards_eq0. apply/eqP. apply/setP => i. by rewrite !inE addbb. } rewrite Hdhxx /= mul0r. exact: Hdelta_pos. } have Hsub : [set x0] \subset [set x : 'I_key_dim | good_pair x x0]. { apply/mathcomp.boot.fintype.subsetP => x. rewrite !inE. move/eqP=> ->; exact: Hself. } have Hcount1 : (1 <= good_cond_count x0)%N. { have Hcount_card : good_cond_count x0 = #|[set x : 'I_key_dim | good_pair x x0]|. { by rewrite /good_cond_count /relative_hamming_ball_count sum_nat_cond_const muln1. } rewrite Hcount_card. apply: (leq_trans _ (subset_leq_card Hsub)). by rewrite cards1. } apply: (leq_trans Hcount1). rewrite /good_cond_count_max. exact: leq_bigmax x0. } have Hcount_max_ge1 : 1 <= good_cond_count_max%:R :> R. { change (((1%N)%:R : R) <= good_cond_count_max%:R). by rewrite ler_nat. } have /hermmxP HP_good_eq := HP_good_herm.
  have Hsupport_bound : hmax_mx rho <= log2 (good_cond_count_max%:R : R).
  { rewrite /hmax_mx.
    have Hkey_dim_pos_A : (0 < key_dim)%N := expn_gt0 2 n_key.
    have Hkey_dim_pos_B : (0 < key_dim)%N := Hkey_dim_pos_A.
    have Hrho_tr_le1 : @complex.Re R (\tr rho) <= 1 by rewrite Hrho_tr1.
    have Hrho_tr_pos : 0 < @complex.Re R (\tr rho) by rewrite Hrho_tr1.
    have Hsupport_has_sup : has_sup [set v : R | exists sigma : 'M[C]_key_dim, sigma \is den1mx /\ elog2 (key_dim%:R * (gfidelity rho (mmix_mx key_dim *t sigma)) ^+ 2) = v%:E]%classic.
    { exact: hmax_mx_has_sup Hkey_dim_pos_A Hkey_dim_pos_B (denmx_psd_re_tr_le Hrho_psd Hrho_tr_le1) Hrho_tr_pos. } apply: ge_sup; last first.
    + move=> v [sigma [Hsigma_den Helog]].
      have /den1mxP [Psig /eqP Hsig_tr1] := Hsigma_den.
      pose tau := mmix_mx key_dim *t sigma.
      pose tauP := P_good *m tau *m P_good.
      have Htau_psd : tau \is psdmx. { apply: psdmx_tens. - exact: mmix_mx_psd. - exact: Psig. } have HtauP_psd : tauP \is psdmx.
      { rewrite /tauP. have -> : P_good *m tau *m P_good = P_good *m tau *m P_good^*t. { by rewrite -HP_good_eq. } exact: psdmx_bimap_closed_gen Htau_psd. } have HP_left_rho : P_good *m rho = rho.
      { have Hrho_herm : rho \is hermmx := psdmx_herm Hrho_psd. have /hermmxP Hrho_eq := Hrho_herm. apply: adjmx_inj. by rewrite adjmxM -Hrho_eq -HP_good_eq HrhoP. } have HrhoP_eq : P_good *m rho *m P_good = rho. { by rewrite HP_left_rho HrhoP. } have [Hfid _] := fid_iv_proj_mx (P := P_good) (rho := rho) (tau := tau) HP_good_proj Hrho_psd Htau_psd.
      move: Hfid; rewrite HrhoP_eq.
      move=> Hfid; have Hgf_eq : gfidelity rho tau = gfidelity rho tauP.
      { rewrite (alt_gfid_gen Hrho_psd Htau_psd) (alt_gfid_gen Hrho_psd HtauP_psd) Hfid. have Hcorr0 : Num.sqrt (@complex.Re R (1 - \tr rho)) = 0. { by rewrite raddfB /= Hrho_tr1 subrr sqrtr0. } by rewrite Hcorr0 !mul0r !addr0. } have HtensmxZl_local : forall m n (k : C) (A : 'M[C]_m) (Bm : 'M[C]_n), (k *: A) *t Bm = k *: (A *t Bm).
      { move=> m n k A Bm; by rewrite -[k *: A]addr0 (linear_tensmxr Bm) linear0l addr0. } have HRe_realM : forall (x : R) (yc : C), @complex.Re R (x%:C * yc) = x * @complex.Re R yc.
      { move=> x yc; case: yc => a b /=. by rewrite mul0r subr0. } have Hkey_R_pos : 0 < key_dim%:R :> R by rewrite ltr0n.
      have Hkey_R_ne0 : (key_dim%:R : R) != 0 := lt0r_neq0 Hkey_R_pos.
      have HtauP_traceE : \tr tauP = ((key_dim%:R)^-1)%:C * \tr (sigma *m ptrace1 P_good).
      { rewrite /tauP /tau /mmix_mx HtensmxZl_local -scalemxAr -scalemxAl linearZ /=. rewrite -mulmxA mxtrace_mulC -mulmxA HP_good_id. by rewrite tr_ptrace1 ptrace1_mulImx. } have HtauP_trace_le : key_dim%:R * @complex.Re R (\tr tauP) <= good_cond_count_max%:R.
      { pose M := ptrace1 P_good. have HM_psd : M \is psdmx. { rewrite /M. exact: ptrace1_psd HP_good_psd. } have Htr_le : \tr (sigma *m M) <= \tr (sigma *m ((good_cond_count_max)%:R%:C *: (1%:M : 'M[C]_key_dim))). { move/le_lownerE_psdtr: Hptrace1_P_good_le_max => Hmon; have Htr_le' := Hmon sigma Psig. have HMtrace : \tr (M *m sigma) = \tr (sigma *m M). { exact: mxtrace_mulC. } have HBtrace : \tr (((good_cond_count_max)%:R%:C *: (1%:M : 'M[C]_key_dim)) *m sigma) = \tr (sigma *m ((good_cond_count_max)%:R%:C *: (1%:M : 'M[C]_key_dim))). { exact: mxtrace_mulC. } rewrite -HMtrace -HBtrace. exact: Htr_le'. } have Htr_real : \tr (sigma *m M) \is Num.real. { have Hsigma_eq : sigma = sigma^*t. { apply/hermmxP. exact: psdmx_herm Psig. } have HM_eq : M = M^*t. { apply/hermmxP. exact: psdmx_herm HM_psd. } apply/CrealP. by rewrite -mxtrace_adj adjmxM -HM_eq -Hsigma_eq mxtrace_mulC. } have Htr_sigma_real : \tr sigma \is Num.real. { exact: ger0_real (psdmx_trace Psig). } have Hrhs : @complex.Re R (\tr sigma) * good_cond_count_max%:R <= good_cond_count_max%:R. { by rewrite Hsig_tr1 /= mul1r. } have Htr_le_R : @complex.Re R (\tr (sigma *m M)) <= good_cond_count_max%:R. { have HBmul : sigma *m ((good_cond_count_max)%:R%:C *: (1%:M : 'M[C]_key_dim)) = (good_cond_count_max)%:R%:C *: sigma. { by rewrite -scalemxAr mulmx1. } move: Htr_le; rewrite HBmul mxtraceZ. rewrite -(RRe_real Htr_real) -(RRe_real Htr_sigma_real) -realcM lecR. move=> Htr_le; rewrite mulrC in Hrhs. exact: (le_trans Htr_le Hrhs). } rewrite HtauP_traceE HRe_realM. rewrite mulrA mulfV ?mul1r //. } have Hgfid_sq_le : key_dim%:R * (gfidelity rho tau) ^+ 2 <= good_cond_count_max%:R.
      { rewrite Hgf_eq.
        have Hcorr0 : Num.sqrt (@complex.Re R (1 - \tr rho)) = 0. { by rewrite raddfB /= Hrho_tr1 subrr sqrtr0. } have Hgf_tauP_eq : gfidelity rho tauP = @complex.Re R (trnorm (sqrtmx rho *m sqrtmx tauP)).
        { by rewrite (alt_gfid_gen Hrho_psd HtauP_psd) Hcorr0 mul0r addr0. } have Hfid_cs := trnorm_sqrt_cs Hrho_psd HtauP_psd.
        rewrite Hrho_tr1 sqrtr1 mul1r in Hfid_cs.
        have HtauP_tr_ge0 : 0 <= @complex.Re R (\tr tauP). { have /= := psdmx_trace HtauP_psd. by rewrite lecE /= => /andP [_]. } have Hgf_sq_trace : (gfidelity rho tauP) ^+ 2 <= @complex.Re R (\tr tauP).
        { rewrite Hgf_tauP_eq.
          pose f := @complex.Re R (trnorm (sqrtmx rho *m sqrtmx tauP)).
          pose t := @complex.Re R (\tr tauP).
          have Hf_ge0 : 0 <= f. { rewrite /f -Hgf_tauP_eq. exact: gfid_ge0_mx Hrho_psd HtauP_psd. } have Hs_ge0 : 0 <= Num.sqrt t := sqrtr_ge0 t.
          have Hf_le_s : f <= Num.sqrt t by exact: Hfid_cs.
          rewrite -/f -/t expr2.
          apply: (le_trans (y := Num.sqrt t * Num.sqrt t)).
          - apply: (le_trans (y := Num.sqrt t * f)).
            + apply: ler_wpM2r; first exact: Hf_ge0.
              exact: Hf_le_s.
            + apply: ler_wpM2l; first exact: Hs_ge0.
              exact: Hf_le_s.
          - by rewrite -expr2 sqr_sqrtr. }
apply: (le_trans (y := key_dim%:R * @complex.Re R (\tr tauP))).
        - apply: ler_wpM2l; first exact: ltW Hkey_R_pos.
          exact: Hgf_sq_trace.
        - exact: HtauP_trace_le. }
have Harg_pos : 0 < key_dim%:R * (gfidelity rho tau) ^+ 2.
      { case: (ltP 0 (key_dim%:R * (gfidelity rho tau) ^+ 2)) => [Harg_gt0|Harg_le0].
        - by [].
        move: Helog; rewrite /tau (elog2_le0 Harg_le0).
        by discriminate. }
have Hv_eq : v = log2 (key_dim%:R * (gfidelity rho tau) ^+ 2). { move: Helog; rewrite /tau (elog2_gt0 Harg_pos). by case. } rewrite Hv_eq.
      exact: log2_le_pos Harg_pos Hgfid_sq_le.
    + by case: Hsupport_has_sup. }
case: (lerP (1 / 2) delta) => Hdelta_half.
  - have Hcount_le_keydim_nat : (good_cond_count_max <= key_dim)%N.
    { apply/bigmax_leqP => x' _. rewrite /good_cond_count /relative_hamming_ball_count sum_nat_cond_const muln1. have Hsub : [set x : 'I_key_dim | good_pair x x'] \subset [set: 'I_key_dim]. { exact: finset.subsetT. } move: (subset_leq_card Hsub); by rewrite cardsT card_ord. } have Hcount_pos : 0 < good_cond_count_max%:R :> R. { exact: (lt_le_trans ltr01 Hcount_max_ge1). } have Hcount_le_keydim : good_cond_count_max%:R <= key_dim%:R :> R.
    { change (good_cond_count_max%:R <= key_dim%:R :> R). by rewrite ler_nat. } have Hbound_keydim : hmax_mx rho <= n_key%:R.
    { apply: (le_trans Hsupport_bound). apply: (le_trans (log2_le_pos Hcount_pos Hcount_le_keydim)). by rewrite /key_dim log2_pow2_nat lexx. } have Hhtrunc1 : bb84_h_trunc delta = 1.
    { rewrite /bb84_h_trunc.
      case: (lerP delta 0) => Hdelta_nonpos.
      - move: Hdelta_pos.
        by rewrite ltNge Hdelta_nonpos.
      - by rewrite Hdelta_half. }
by rewrite Hhtrunc1 mulr1.
  - have HhtruncE : bb84_h_trunc delta = h_bin delta.
    { rewrite /bb84_h_trunc.
      case: (lerP delta 0) => Hdelta_nonpos.
      - move: Hdelta_pos.
        by rewrite ltNge Hdelta_nonpos.
      - case: (lerP (1 / 2) delta) => Hdelta_half'.
        + move: Hdelta_half.
          by rewrite ltNge Hdelta_half'.
        + by []. }
rewrite HhtruncE.
    apply: (le_trans Hsupport_bound).
    exact: hamming_ball_count_max_entropy_bound Hn_key_pos Hdelta_pos Hdelta_half. Qed.

Section Secrecy.
Variable (L : finType) (HL : L -> chsType) (S E : {set L}).
Hypothesis disSE : [disjoint S & E].
Variable (n_pe : nat).

Lemma stat (Zkey B : {set L})
    (disZB : [disjoint Zkey & B])
    (n_key : nat) (z z' : bitstr (n_pe + n_key)) (Qtol eps : R)
    (rhoZZp : 'F[HL]_(Zkey :|: B))
    (dim_Zk : (2 ^ n_key)%N = dim ('H[HL]_Zkey))
    (dim_B : (2 ^ n_key)%N = dim ('H[HL]_B)) :
  (0 < n_key)%N -> (0 < n_pe)%N -> 0 < eps -> rhoZZp \is psdlf -> let mu := bb84_mu n_key n_pe eps in
  let pass_event : {set 'S_(n_pe + n_key)} :=
    [set pi : 'S_(n_pe + n_key) | @perm_pair_sample_err R n_key n_pe z z' pi <= Qtol] in
    let p_pass :=
      Pr_event (fun pi : 'S_(n_pe + n_key) => @uniform_perm_mu R (n_pe + n_key) pi)
        pass_event in
    0 < p_pass -> let eps' := eps / Num.sqrt p_pass in
    eps' < 1 -> let h_trunc := bb84_h_trunc (Qtol + mu) in
  let key_dim := (2 ^ n_key)%N in
  let pair_basis_projector :=
    fun x x' : 'I_key_dim =>
      (delta_mx x x : 'M[C]_key_dim) *t
      (delta_mx x' x' : 'M[C]_key_dim) in
  let rhoZZ' : 'M[C]_(key_dim * key_dim) :=
    \sum_(pi : 'S_(n_pe + n_key) | pi \in pass_event)
      (((@uniform_perm_mu R (n_pe + n_key) pi / p_pass)%:C) *:
        pair_basis_projector
          (bitstring_to_ord (@perm_pair_holdout n_key n_pe z pi))
          (bitstring_to_ord (@perm_pair_holdout n_key n_pe z' pi))) in
  biprod_mx disZB rhoZZp =
    castmx (f_equal2 muln dim_Zk dim_B, f_equal2 muln dim_Zk dim_B) rhoZZ' ->
  smooth_hmax B eps' rhoZZp <= n_key%:R * h_trunc.
Proof.
  move=> Hn_key_pos Hn_pe_pos Heps_pos HrhoZZp_psd /= Hppass_pos Heps'_lt1 Hmx.
  rewrite (smooth_hmax_labelled_mx disZB _ HrhoZZp_psd) Hmx smooth_hmax_mx_cast_bipartite.
  set mu := bb84_mu n_key n_pe eps.
  set pass_event : {set 'S_(n_pe + n_key)} := [set pi : 'S_(n_pe + n_key) | @perm_pair_sample_err R n_key n_pe z z' pi <= Qtol].
  set p_pass := Pr_event (fun pi : 'S_(n_pe + n_key) => @uniform_perm_mu R (n_pe + n_key) pi) pass_event in Hppass_pos *.
  set eps' := eps / Num.sqrt p_pass.
  pose h_trunc := bb84_h_trunc (Qtol + mu).
  pose key_dim := (2 ^ n_key)%N.
  pose pair_basis_projector (x x' : 'I_key_dim) := (delta_mx x x : 'M[C]_key_dim) *t (delta_mx x' x' : 'M[C]_key_dim).
  pose rhoZZ' : 'M[C]_(key_dim * key_dim) := \sum_(pi : 'S_(n_pe + n_key) | pi \in pass_event) (((@uniform_perm_mu R (n_pe + n_key) pi / p_pass)%:C) *: pair_basis_projector (bitstring_to_ord (@perm_pair_holdout n_key n_pe z pi)) (bitstring_to_ord (@perm_pair_holdout n_key n_pe z' pi))).
  pose good_event : {set 'S_(n_pe + n_key)} := [set pi : 'S_(n_pe + n_key) | @perm_pair_holdout_err R n_key n_pe z z' pi < @perm_pair_sample_err R n_key n_pe z z' pi + mu].
  pose good_cond := Pr_cond (fun pi : 'S_(n_pe + n_key) => @uniform_perm_mu R (n_pe + n_key) pi) good_event pass_event.
  pose rhoZZ'_good : 'M[C]_(key_dim * key_dim) := if good_cond == 0 then 0 else \sum_(pi : 'S_(n_pe + n_key) | (pi \in pass_event) && (pi \in good_event)) (((@uniform_perm_mu R (n_pe + n_key) pi / (p_pass * good_cond))%:C) *: pair_basis_projector (bitstring_to_ord (@perm_pair_holdout n_key n_pe z pi)) (bitstring_to_ord (@perm_pair_holdout n_key n_pe z' pi))).
  pose delta := Qtol + mu.
  pose bad_event : {set 'S_(n_pe + n_key)} := @perm_pair_deviation_event R n_key n_pe z z' mu.
  pose good_pair (x x' : 'I_key_dim) := @relative_hamming_ball R n_key delta x x'.
  pose P_good : 'M[C]_(key_dim * key_dim) := \sum_(x : 'I_key_dim) \sum_(x' : 'I_key_dim | good_pair x x') pair_basis_projector x x'.
  have Hhtrunc_nonneg : 0 <= h_trunc. by rewrite /h_trunc; exact: bb84_h_trunc_nonneg.
  have Hrhs_nonneg : 0 <= n_key%:R * h_trunc. { apply: mulr_ge0. - by rewrite ler0n. - exact: Hhtrunc_nonneg. } have Hpair_psd (x x' : 'I_key_dim) : pair_basis_projector x x' \is psdmx.
  { rewrite /pair_basis_projector. exact: bb84_pair_projector_psdmx. } have Hpair_trace (x x' : 'I_key_dim) : \tr (pair_basis_projector x x') = 1.
  { rewrite /pair_basis_projector. exact: bb84_pair_projector_trace. } have Hbitstring_ord_bitstringK : forall s : bitstr n_key, ord_to_bitstring (bitstring_to_ord s) = s.
  { move=> s; rewrite /ord_to_bitstring /bitstring_to_ord. have -> : ord2bseq (bseq2ord (utils.bitstr.bitstring_to_tuple s)) = utils.bitstr.bitstring_to_tuple s. exact: bseq2ordK. apply/funext => i. by rewrite /utils.bitstr.tuple_to_bitstring /utils.bitstr.bitstring_to_tuple tnth_mktuple. } have Hpair_mul (x x' y y' : 'I_key_dim) : pair_basis_projector x x' *m pair_basis_projector y y' = if (x == y) && (x' == y') then pair_basis_projector x x' else 0.
  { rewrite /pair_basis_projector. exact: bb84_pair_projector_mul. } have Hgood_pair_of_event (pi : 'S_(n_pe + n_key)) : (pi \in pass_event) && (pi \in good_event) -> good_pair (bitstring_to_ord (@perm_pair_holdout n_key n_pe z pi)) (bitstring_to_ord (@perm_pair_holdout n_key n_pe z' pi)).
  { move=> /andP [Hpass Hgood]. have Hgood_err : @perm_pair_holdout_err R n_key n_pe z z' pi < @perm_pair_sample_err R n_key n_pe z z' pi + mu. { move: Hgood; by rewrite /good_event !inE. } have Hpass_err : @perm_pair_sample_err R n_key n_pe z z' pi <= Qtol. { move: Hpass; by rewrite /pass_event !inE. } have Hgood_pairR : @perm_pair_holdout_err R n_key n_pe z z' pi < Qtol + mu. { apply: (lt_le_trans Hgood_err). by rewrite lerD2r. } rewrite /good_pair /delta /relative_hamming_ball /perm_pair_holdout_err. by rewrite !Hbitstring_ord_bitstringK. } have Hpair_fix_P_good (x x' : 'I_key_dim) : good_pair x x' -> pair_basis_projector x x' *m P_good = pair_basis_projector x x'.
  { move=> Hgood; rewrite /P_good mulmx_sumr. rewrite (bigD1 x) //=. have Hrest_x : \sum_(y : 'I_key_dim | y != x) pair_basis_projector x x' *m (\sum_(y' : 'I_key_dim | good_pair y y') pair_basis_projector y y') = 0. { apply: big1 => y /negPf Hyx. rewrite mulmx_sumr. apply: big1 => y' _. by rewrite Hpair_mul eq_sym Hyx. } rewrite [X in _ + X]Hrest_x addr0. rewrite mulmx_sumr (bigD1 x') //=. have Hrest_x' : \sum_(y' : 'I_key_dim | good_pair x y' && (y' != x')) pair_basis_projector x x' *m pair_basis_projector x y' = 0. { apply: big1 => y' /andP [_ Hy'x]. by rewrite Hpair_mul eqxx eq_sym (negPf Hy'x). } rewrite [X in _ + X]Hrest_x' addr0. by rewrite Hpair_mul !eqxx. } have HrhoZZ'_good_mul_P_good : rhoZZ'_good *m P_good = rhoZZ'_good.
  { rewrite /rhoZZ'_good.
    case Hgood0 : (good_cond == 0).
    - by rewrite !mul0mx.
    - rewrite mulmx_suml.
      apply: eq_bigr => pi.
      move=> Hcond; rewrite -scalemxAl.
      rewrite (Hpair_fix_P_good (bitstring_to_ord (@perm_pair_holdout n_key n_pe z pi)) (bitstring_to_ord (@perm_pair_holdout n_key n_pe z' pi)) (Hgood_pair_of_event pi Hcond)).
      by []. }
have Hppass_nz : p_pass != 0 := lt0r_neq0 Hppass_pos.
  have Hppass_unit : p_pass \is a GRing.unit by rewrite unitfE.
  have Hgood_cond_nonneg : 0 <= good_cond.
  { rewrite /good_cond /Pr_cond (negbTE Hppass_nz).
    apply: divr_ge0.
    - by apply: sumr_ge0 => pi _; exact: uniform_perm_mu_nonneg.
    - exact: ltW Hppass_pos. }
have Hsum_good : \sum_(pi in pass_event | pi \in good_event) @uniform_perm_mu R (n_pe + n_key) pi = good_cond * p_pass.
  { have Hbayes : Pr_event (fun pi : 'S_(n_pe + n_key) => @uniform_perm_mu R (n_pe + n_key) pi) (good_event :&: pass_event) = good_cond * p_pass. { exact: (@bayes_theorem R 'S_(n_pe + n_key) (fun pi : 'S_(n_pe + n_key) => @uniform_perm_mu R (n_pe + n_key) pi) good_event pass_event Hppass_nz). } rewrite -Hbayes /Pr_event. apply: eq_bigl => pi. by rewrite !inE andbC. }

  have Hgood_tr1_of_nz : good_cond != 0 -> @complex.Re R (\tr rhoZZ'_good) = 1.
  { move=> Hgood_nz. have HtraceE : \tr (\sum_(pi : 'S_(n_pe + n_key) | (pi \in pass_event) && (pi \in good_event)) (((@uniform_perm_mu R (n_pe + n_key) pi / (p_pass * good_cond))%:C) *: pair_basis_projector (bitstring_to_ord (@perm_pair_holdout n_key n_pe z pi)) (bitstring_to_ord (@perm_pair_holdout n_key n_pe z' pi)))) = (\sum_(pi : 'S_(n_pe + n_key) | (pi \in pass_event) && (pi \in good_event)) (@uniform_perm_mu R (n_pe + n_key) pi / (p_pass * good_cond)))%:C. { rewrite linear_sum. rewrite (eq_bigr (fun pi => ((@uniform_perm_mu R (n_pe + n_key) pi / (p_pass * good_cond))%:C) * \tr (pair_basis_projector (bitstring_to_ord (@perm_pair_holdout n_key n_pe z pi)) (bitstring_to_ord (@perm_pair_holdout n_key n_pe z' pi))))); last first. { move=> pi _; by rewrite linearZ. } rewrite (eq_bigr (fun pi => ((@uniform_perm_mu R (n_pe + n_key) pi / (p_pass * good_cond))%:C))); last first. { move=> pi _; by rewrite Hpair_trace mulr1. } by rewrite rmorph_sum. } have Hden_nz : p_pass * good_cond != 0. { apply/negP. rewrite mulf_eq0. by rewrite (negPf Hppass_nz) (negPf Hgood_nz). } have Hden_unit : p_pass * good_cond \is a GRing.unit by rewrite unitfE. have Hsum_div1 : \sum_(pi in pass_event | pi \in good_event) @uniform_perm_mu R (n_pe + n_key) pi / (p_pass * good_cond) = 1. { apply: (mulIf Hden_nz). rewrite mulr_suml mul1r. rewrite (eq_bigr (fun pi => @uniform_perm_mu R (n_pe + n_key) pi)); last first. { move=> pi _; exact: (divrK Hden_unit (@uniform_perm_mu R (n_pe + n_key) pi)). } by rewrite Hsum_good mulrC. } by rewrite /rhoZZ'_good (negbTE Hgood_nz) HtraceE re_realid Hsum_div1. } have Hgood_psd : rhoZZ'_good \is psdmx.
  { rewrite /rhoZZ'_good.
    case Hgood0 : (good_cond == 0).
    - exact: psdmx0.
    - apply: psdmx_sum => pi.
      rewrite !inE => _.
      apply: psdmxZ.
      + rewrite lecR.
        apply: divr_ge0.
        * exact: uniform_perm_mu_nonneg.
        * apply: mulr_ge0. -- exact: ltW Hppass_pos. -- have Hgood_cond_pos : 0 < good_cond. by rewrite lt_def Hgood_cond_nonneg Hgood0. exact: ltW Hgood_cond_pos.
      + exact: Hpair_psd _ _. }
pose err_dim := n_pe.+1.
  have Hperm_pair_sample_count_le (pi : 'S_(n_pe + n_key)) : (@perm_pair_sample_count n_key n_pe z z' pi <= n_pe)%N.
  { rewrite /perm_pair_sample_count /d_ham /wt_ham. have Hsub : [set i : 'I_n_pe | xor_str (@perm_pair_sample n_key n_pe z pi) (@perm_pair_sample n_key n_pe z' pi) i] \subset [set: 'I_n_pe]. { exact: finset.subsetT. } move: (subset_leq_card Hsub); by rewrite cardsT card_ord. } have Hperm_pair_sample_count_lt (pi : 'S_(n_pe + n_key)) : (@perm_pair_sample_count n_key n_pe z z' pi < err_dim)%N.
  { rewrite /err_dim ltnS. exact: Hperm_pair_sample_count_le. } pose err_ord (pi : 'S_(n_pe + n_key)) : 'I_err_dim := @Ordinal err_dim (@perm_pair_sample_count n_key n_pe z z' pi) (Hperm_pair_sample_count_lt pi).
  pose triple_basis_projector (x x' : 'I_key_dim) (e : 'I_err_dim) := pair_basis_projector x x' *t (delta_mx e e : 'M[C]_err_dim).
  pose rhoZZE : 'M[C]_((key_dim * key_dim) * err_dim) := \sum_(pi : 'S_(n_pe + n_key) | pi \in pass_event) (((@uniform_perm_mu R (n_pe + n_key) pi / p_pass)%:C) *: triple_basis_projector (bitstring_to_ord (@perm_pair_holdout n_key n_pe z pi)) (bitstring_to_ord (@perm_pair_holdout n_key n_pe z' pi)) (err_ord pi)).
  pose rhoZZE_good : 'M[C]_((key_dim * key_dim) * err_dim) := if good_cond == 0 then 0 else \sum_(pi : 'S_(n_pe + n_key) | (pi \in pass_event) && (pi \in good_event)) (((@uniform_perm_mu R (n_pe + n_key) pi / (p_pass * good_cond))%:C) *: triple_basis_projector (bitstring_to_ord (@perm_pair_holdout n_key n_pe z pi)) (bitstring_to_ord (@perm_pair_holdout n_key n_pe z' pi)) (err_ord pi)).
  have Htriple_psd (x x' : 'I_key_dim) (e : 'I_err_dim) : triple_basis_projector x x' e \is psdmx.
  { rewrite /triple_basis_projector. apply: psdmx_tens. - exact: Hpair_psd. - exact: delta_mx_ii_psdmx. } have Htriple_trace (x x' : 'I_key_dim) (e : 'I_err_dim) : \tr (triple_basis_projector x x' e) = 1.
  { rewrite /triple_basis_projector mxtrace_tens Hpair_trace mxtrace_delta eqxx. by rewrite mul1r. } have HrhoZZE_psd : rhoZZE \is psdmx.
  { rewrite /rhoZZE.
    apply: psdmx_sum => pi _.
    apply: psdmxZ.
    - rewrite lecR.
      apply: divr_ge0.
      + exact: (@uniform_perm_mu_nonneg R (n_pe + n_key) pi).
      + exact: ltW Hppass_pos.
    - exact: Htriple_psd _ _ _. }
have HrhoZZE_good_psd : rhoZZE_good \is psdmx.
  { rewrite /rhoZZE_good.
    case Hgood0 : (good_cond == 0).
    - exact: psdmx0.
    - apply: psdmx_sum => pi.
      rewrite !inE => _.
      apply: psdmxZ.
      + rewrite lecR.
        apply: divr_ge0.
        * exact: (@uniform_perm_mu_nonneg R (n_pe + n_key) pi).
        * apply: mulr_ge0. -- exact: ltW Hppass_pos. -- have Hgood_cond_pos : 0 < good_cond. by rewrite lt_def Hgood_cond_nonneg Hgood0. exact: ltW Hgood_cond_pos.
      + exact: Htriple_psd _ _ _. }
have Hptrace_triple_basis_projector (x x' : 'I_key_dim) (e : 'I_err_dim) : ptrace2 (triple_basis_projector x x' e) = pair_basis_projector x x'.
  { rewrite /triple_basis_projector ptrace_tensmx mxtrace_delta eqxx. by rewrite scale1r. } have Hptrace_rhoZZE : ptrace2 rhoZZE = rhoZZ'.
  { rewrite /rhoZZE /rhoZZ' linear_sum. apply: eq_bigr => pi _. rewrite linearZ. congr (_ *: _). exact: (Hptrace_triple_basis_projector (bitstring_to_ord (@perm_pair_holdout n_key n_pe z pi)) (bitstring_to_ord (@perm_pair_holdout n_key n_pe z' pi)) (err_ord pi)). } have Hptrace_rhoZZE_good : ptrace2 rhoZZE_good = rhoZZ'_good.
  { rewrite /rhoZZE_good /rhoZZ'_good.
    case Hgood0 : (good_cond == 0).
    - by rewrite linear0.
    - rewrite linear_sum.
      apply: eq_bigr => pi _.
      rewrite linearZ.
      congr (_ *: _).
      exact: (Hptrace_triple_basis_projector (bitstring_to_ord (@perm_pair_holdout n_key n_pe z pi)) (bitstring_to_ord (@perm_pair_holdout n_key n_pe z' pi)) (err_ord pi)). }
have Hgood_tr : @complex.Re R (\tr rhoZZ'_good) <= 1.
  { case Hgood0 : (good_cond == 0).
    - by rewrite /rhoZZ'_good Hgood0 mxtrace0 raddf0.
    - by rewrite (Hgood_tr1_of_nz (negbT Hgood0)). }
have Hgood0_of_delta_nonpos : delta <= 0 -> good_cond == 0.
  { move=> Hdelta_nonpos. have Hnum0 : \sum_(pi in pass_event | pi \in good_event) @uniform_perm_mu R (n_pe + n_key) pi = 0. { apply: big1 => pi /andP [Hpass Hgood]. have Hgood_err : @perm_pair_holdout_err R n_key n_pe z z' pi < @perm_pair_sample_err R n_key n_pe z z' pi + mu. { move: Hgood; by rewrite /good_event !inE. } have Hpass_err : @perm_pair_sample_err R n_key n_pe z z' pi <= Qtol. { move: Hpass; by rewrite /pass_event !inE. } have Hlt0 : @perm_pair_holdout_err R n_key n_pe z z' pi < 0. { apply: (lt_le_trans Hgood_err). apply: (le_trans _ Hdelta_nonpos). by rewrite lerD2r. } have Hge0 : 0 <= @perm_pair_holdout_err R n_key n_pe z z' pi. { rewrite /perm_pair_holdout_err. apply: divr_ge0. - by rewrite ler0n. - by rewrite ler0n. } move: Hlt0; by rewrite ltNge Hge0. } have Hinter0 : Pr_event (fun pi : 'S_(n_pe + n_key) => @uniform_perm_mu R (n_pe + n_key) pi) (good_event :&: pass_event) = 0. { rewrite /Pr_event. rewrite (eq_bigl (fun pi : 'S_(n_pe + n_key) => (pi \in pass_event) && (pi \in good_event))); last first. { move=> pi; by rewrite !inE andbC. } exact: Hnum0. } apply/eqP. rewrite /good_cond /Pr_cond (negbTE Hppass_nz) Hinter0 mul0r. by []. } have Hgood_pd_pos : pur_dist_mx rhoZZ'_good rhoZZ' <= eps' /\ 0 < @complex.Re R (\tr rhoZZ'_good).
    { have Heps_ge0 : 0 <= eps by exact: ltW Heps_pos.
    have Heps'_ge0 : 0 <= eps'. { rewrite /eps'. apply: divr_ge0. - exact: Heps_ge0. - exact: sqrtr_ge0 p_pass. } have Heps'_E : Num.sqrt (eps ^+ 2 / p_pass) = eps' := sqrtr_sq_div Heps_ge0 Hppass_pos.
    have Htrace_rhoZZE : \tr rhoZZE = (\sum_(pi : 'S_(n_pe + n_key) | pi \in pass_event) (@uniform_perm_mu R (n_pe + n_key) pi / p_pass))%:C.
    { rewrite /rhoZZE linear_sum. rewrite (eq_bigr (fun pi => ((@uniform_perm_mu R (n_pe + n_key) pi / p_pass)%:C) * \tr (triple_basis_projector (bitstring_to_ord (@perm_pair_holdout n_key n_pe z pi)) (bitstring_to_ord (@perm_pair_holdout n_key n_pe z' pi)) (err_ord pi)))); last first. { move=> pi _; by rewrite linearZ. } rewrite (eq_bigr (fun pi => ((@uniform_perm_mu R (n_pe + n_key) pi / p_pass)%:C))); last first. { move=> pi _; by rewrite Htriple_trace mulr1. } by rewrite rmorph_sum. } have HrhoZZE_tr1 : @complex.Re R (\tr rhoZZE) = 1.
    { rewrite Htrace_rhoZZE re_realid. apply: (mulIf Hppass_nz). rewrite mulr_suml mul1r. rewrite (eq_bigr (fun pi : 'S_(n_pe + n_key) => @uniform_perm_mu R (n_pe + n_key) pi)); last first. { move=> pi _; exact: (divrK Hppass_unit (@uniform_perm_mu R (n_pe + n_key) pi)). } by rewrite /p_pass /Pr_event. } have HgoodZZE_tr : @complex.Re R (\tr rhoZZE_good) <= 1. { by rewrite tr_ptrace2 Hptrace_rhoZZE_good. } pose bad_cond := Pr_cond (fun pi : 'S_(n_pe + n_key) => @uniform_perm_mu R (n_pe + n_key) pi) bad_event pass_event.
    have Hbad_cond_nonneg : 0 <= bad_cond.
    { rewrite /bad_cond /Pr_cond (negbTE Hppass_nz).
      apply: divr_ge0.
      - apply: sumr_ge0 => pi _.
        exact: uniform_perm_mu_nonneg.
      - exact: ltW Hppass_pos. }
have Hbad_cond_le : bad_cond <= eps ^+ 2 / p_pass. { exact: (bb84_bbkey Hn_key_pos Hn_pe_pos Heps_pos Hppass_pos). } have Hsum_bad : \sum_(pi in pass_event | pi \in bad_event) @uniform_perm_mu R (n_pe + n_key) pi = bad_cond * p_pass.
    { have Hbayes : Pr_event (fun pi : 'S_(n_pe + n_key) => @uniform_perm_mu R (n_pe + n_key) pi) (bad_event :&: pass_event) = bad_cond * p_pass. { exact: (@bayes_theorem R 'S_(n_pe + n_key) (fun pi : 'S_(n_pe + n_key) => @uniform_perm_mu R (n_pe + n_key) pi) bad_event pass_event Hppass_nz). } rewrite -Hbayes /Pr_event. apply: eq_bigl => pi. by rewrite !inE andbC. } have Hbad_eventC : forall pi : 'S_(n_pe + n_key), (pi \in bad_event) = ~~ (pi \in good_event).
    { move=> pi; by rewrite /bad_event /good_event /perm_pair_deviation_event !inE ltNge negbK. } have Hsum_partition : \sum_(pi in pass_event) @uniform_perm_mu R (n_pe + n_key) pi = \sum_(pi in pass_event | pi \in good_event) @uniform_perm_mu R (n_pe + n_key) pi + \sum_(pi in pass_event | pi \in bad_event) @uniform_perm_mu R (n_pe + n_key) pi.
    { rewrite [LHS](bigID (mem good_event)) /=. congr (_ + _). apply: eq_bigl => pi. by rewrite Hbad_eventC. } have Hcond_sum : good_cond + bad_cond = 1.
    { have Hcond_sum_rhs : good_cond * p_pass + bad_cond * p_pass = p_pass. { rewrite -Hsum_good -Hsum_bad /p_pass /Pr_event. exact (esym Hsum_partition). } apply: (mulIf Hppass_nz). rewrite [(good_cond + bad_cond) * p_pass]mulrDl [1 * p_pass]mul1r. exact Hcond_sum_rhs. } have Hbad_condE : bad_cond = 1 - good_cond.
    { have Hcond_sum' : bad_cond + good_cond = 1. { by rewrite addrC Hcond_sum. } have Htmp := congr1 (fun x : R => x - good_cond) Hcond_sum'. rewrite addrK in Htmp. exact: Htmp. } have Hgood_cond_le1 : good_cond <= 1. { rewrite -subr_ge0. by rewrite -Hbad_condE. } have H1mgood_le : 1 - good_cond <= eps ^+ 2 / p_pass. { by rewrite -Hbad_condE. } have Hpdmx_ptrace2 : pur_dist_mx rhoZZ'_good rhoZZ' <= pur_dist_mx rhoZZE_good rhoZZE.
    { have Hmono := gfid_ptr_mono_mx (m := key_dim * key_dim) (n := err_dim) (rho := rhoZZE_good) (sigma := rhoZZE) (ltn0Sn n_pe) HrhoZZE_good_psd HrhoZZE_psd. have Hgf_ge0 := gfid_ge0_mx HrhoZZE_good_psd HrhoZZE_psd. have Hgf_ptr_ge0 := gfid_ge0_mx (ptrace2_psd HrhoZZE_good_psd) (ptrace2_psd HrhoZZE_psd). have Hgf_le1 : gfidelity rhoZZE_good rhoZZE <= 1. { have Hsq_le : (gfidelity rhoZZE_good rhoZZE) ^+ 2 <= 1. { have Hsq_le' : (gfidelity rhoZZE_good rhoZZE) ^+ 2 <= maxr 1 (@complex.Re R (\tr rhoZZE)). { have HrhoZZE_good_den : rhoZZE_good \is denmx := denmx_psd_re_tr_le HrhoZZE_good_psd HgoodZZE_tr. exact: gfid_sq_le_max_mx HrhoZZE_good_den HrhoZZE_psd. } rewrite HrhoZZE_tr1 maxxx in Hsq_le'. exact: Hsq_le'. } have Hsqrt_mono := ler_wsqrtr Hsq_le. rewrite sqrtr1 in Hsqrt_mono. rewrite sqrtr_sqr (ger0_norm Hgf_ge0) in Hsqrt_mono. exact: Hsqrt_mono. } rewrite /pur_dist_mx -Hptrace_rhoZZE_good -Hptrace_rhoZZE. exact: (sqrt_1msq_antimono_gen Hgf_ge0 Hgf_le1 Hgf_ptr_ge0 Hmono). } have Hbig_pd : pur_dist_mx rhoZZE_good rhoZZE <= eps'.
    { case Hgood0 : (good_cond == 0).
      - have Hrho0 : rhoZZE_good = 0.
        { by rewrite /rhoZZE_good Hgood0. } have Hbad1 : bad_cond = 1. { move/eqP: Hgood0 => Hgood0_eq; by rewrite Hbad_condE Hgood0_eq subr0. } have Hone_le : 1 <= eps ^+ 2 / p_pass. { by rewrite -Hbad1. } rewrite Hrho0 /pur_dist_mx.
        have Hgf0_ge : 0 <= gfidelity (0 : 'M[C]_((key_dim * key_dim) * err_dim)) rhoZZE.
        { exact: gfid_ge0_mx (psdmx0 C ((key_dim * key_dim) * err_dim)) HrhoZZE_psd. } have Htmp : Num.sqrt (1 - (gfidelity (0 : 'M[C]_((key_dim * key_dim) * err_dim)) rhoZZE)^2) <= Num.sqrt (1 - (0 : R)^2).
        { apply: sqrt_1msq_antimono_gen.
          - by rewrite lexx.
          - by rewrite ler01.
          1,2: exact: Hgf0_ge. }
apply: (le_trans Htmp).
        rewrite -Heps'_E.
        apply: ler_wsqrtr.
        have Hzero_sq_le1 : 1 - (0 : R)^2 <= 1. { rewrite lerBlDr lerDl. exact: sqr_ge0. } exact: (le_trans Hzero_sq_le1 Hone_le).
      - have Hgood_cond_pos : 0 < good_cond.
        { by rewrite lt_def Hgood_cond_nonneg Hgood0. } have Hgood_cond_nz : good_cond != 0. { exact: lt0r_neq0 Hgood_cond_pos. } have Hgood_cond_unit : good_cond \is a GRing.unit. { by rewrite unitfE. } pose good_triple (x x' : 'I_key_dim) (e : 'I_err_dim) := (d_ham (ord_to_bitstring x) (ord_to_bitstring x'))%:R / n_key%:R < e%:R / n_pe%:R + mu.
        pose P_evt : 'M[C]_((key_dim * key_dim) * err_dim) := \sum_(x : 'I_key_dim) \sum_(x' : 'I_key_dim) \sum_(e : 'I_err_dim | good_triple x x' e) triple_basis_projector x x' e.
        pose rhoZZE_raw : 'M[C]_((key_dim * key_dim) * err_dim) := \sum_(pi : 'S_(n_pe + n_key) | (pi \in pass_event) && (pi \in good_event)) (((@uniform_perm_mu R (n_pe + n_key) pi / p_pass)%:C) *: triple_basis_projector (bitstring_to_ord (@perm_pair_holdout n_key n_pe z pi)) (bitstring_to_ord (@perm_pair_holdout n_key n_pe z' pi)) (err_ord pi)).
        have Hgood_tripleE (pi : 'S_(n_pe + n_key)) : good_triple (bitstring_to_ord (@perm_pair_holdout n_key n_pe z pi)) (bitstring_to_ord (@perm_pair_holdout n_key n_pe z' pi)) (err_ord pi) = (pi \in good_event).
        { rewrite /good_triple /good_event !inE /perm_pair_holdout_err /perm_pair_sample_err. rewrite !Hbitstring_ord_bitstringK /err_ord /=. by []. } have Htriple_mul (x x' y y' : 'I_key_dim) (e f : 'I_err_dim) : triple_basis_projector x x' e *m triple_basis_projector y y' f = if [&& x == y, x' == y' & e == f] then triple_basis_projector x x' e else 0.
        { rewrite /triple_basis_projector tensmx_mul.
          case Hxy : ((x == y) && (x' == y')).
          - move/andP: Hxy => [/eqP -> /eqP ->].
            case Hef : (e == f).
            + move/eqP: Hef => ->.
              rewrite Hpair_mul mul_delta_mx.
              by rewrite !eqxx.
            + have Hdelta0 : (delta_mx e e *m delta_mx f f : 'M[C]_err_dim) = 0.
              { rewrite mul_delta_mx_cond Hef. by rewrite mulr0n. } rewrite Hpair_mul Hdelta0 linear0r.
              by rewrite !eqxx /=.
          - have Hrhs0 : (if [&& x == y, x' == y' & e == f] then triple_basis_projector x x' e else 0) = 0.
            { case Hxeq : (x == y); case Hx'eq : (x' == y'); rewrite /= ?Hxeq ?Hx'eq //. move: Hxy; by rewrite Hxeq Hx'eq. } have Hpair0 : pair_basis_projector x x' *m pair_basis_projector y y' = 0. { by rewrite Hpair_mul Hxy. } by rewrite Hpair0 linear0l Hrhs0. }
have HP_evt_psd : P_evt \is psdmx.
        { rewrite /P_evt. apply: psdmx_sum => x _. apply: psdmx_sum => x' _. apply: psdmx_sum => e _. exact: Htriple_psd. } have Htriple_fix_P_evt (x x' : 'I_key_dim) (e : 'I_err_dim) : good_triple x x' e -> triple_basis_projector x x' e *m P_evt = triple_basis_projector x x' e.
        { move=> Hgood; rewrite /P_evt mulmx_sumr. rewrite (bigD1 x) //=. have Hrest_x : \sum_(y : 'I_key_dim | y != x) triple_basis_projector x x' e *m (\sum_(y' : 'I_key_dim) \sum_(f : 'I_err_dim | good_triple y y' f) triple_basis_projector y y' f) = 0. { apply: big1 => y /negPf Hyx. rewrite mulmx_sumr. apply: big1 => y' _. rewrite mulmx_sumr. apply: big1 => f _. by rewrite Htriple_mul eq_sym Hyx. } rewrite [X in _ + X]Hrest_x addr0. rewrite mulmx_sumr (bigD1 x') //=. have Hrest_x' : \sum_(y' : 'I_key_dim | y' != x') triple_basis_projector x x' e *m (\sum_(f : 'I_err_dim | good_triple x y' f) triple_basis_projector x y' f) = 0. { apply: big1 => y' /negPf Hy'x. rewrite mulmx_sumr. apply: big1 => f _. by rewrite Htriple_mul eqxx eq_sym Hy'x. } rewrite [X in _ + X]Hrest_x' addr0. rewrite mulmx_sumr (bigD1 e) //=. have Hrest_e : \sum_(f : 'I_err_dim | good_triple x x' f && (f != e)) triple_basis_projector x x' e *m triple_basis_projector x x' f = 0. { apply: big1 => f /andP [_ /negPf Hfe]. by rewrite Htriple_mul !eqxx eq_sym Hfe. } rewrite [X in _ + X]Hrest_e addr0. by rewrite Htriple_mul !eqxx /=. } have Htriple_mul_P_evt (x x' : 'I_key_dim) (e : 'I_err_dim) : triple_basis_projector x x' e *m P_evt = if good_triple x x' e then triple_basis_projector x x' e else 0.
        { case Hgood : (good_triple x x' e).
          - exact: Htriple_fix_P_evt Hgood.
          - rewrite /P_evt mulmx_sumr.
            rewrite (bigD1 x) //=.
            have Hrest_x : \sum_(y : 'I_key_dim | y != x) triple_basis_projector x x' e *m (\sum_(y' : 'I_key_dim) \sum_(f : 'I_err_dim | good_triple y y' f) triple_basis_projector y y' f) = 0.
            { apply: big1 => y /negPf Hyx. rewrite mulmx_sumr. apply: big1 => y' _. rewrite mulmx_sumr. apply: big1 => f _. by rewrite Htriple_mul eq_sym Hyx. } rewrite [X in _ + X]Hrest_x addr0.
            rewrite mulmx_sumr (bigD1 x') //=.
            have Hrest_x' : \sum_(y' : 'I_key_dim | y' != x') triple_basis_projector x x' e *m (\sum_(f : 'I_err_dim | good_triple x y' f) triple_basis_projector x y' f) = 0.
            { apply: big1 => y' /negPf Hy'x. rewrite mulmx_sumr. apply: big1 => f _. by rewrite Htriple_mul eqxx eq_sym Hy'x. } rewrite [X in _ + X]Hrest_x' addr0.
            rewrite mulmx_sumr.
            apply: big1 => f Hgoodf.
            rewrite Htriple_mul !eqxx.
            case Hef : (e == f).
            + move/eqP: Hef => Hfe.
              move/negP: Hgood => Hcontra; have Hgoode : good_triple x x' e.
              { move: Hgoodf; by rewrite Hfe. } by case: (Hcontra Hgoode).
            + by []. }
have Htriple_left_mul_P_evt (x x' : 'I_key_dim) (e : 'I_err_dim) : P_evt *m triple_basis_projector x x' e = if good_triple x x' e then triple_basis_projector x x' e else 0.
        { have /hermmxP HPherm := psdmx_herm HP_evt_psd.
          have /hermmxP Htherm := psdmx_herm (Htriple_psd x x' e).
          apply: adjmx_inj.
          rewrite adjmxM -Htherm -HPherm Htriple_mul_P_evt.
          case Hgood : (good_triple x x' e).
          - exact: Htherm.
          - by rewrite /= adjmxE trmx0 map_mx0. }
have HP_evt_id : P_evt *m P_evt = P_evt.
        { rewrite /P_evt mulmx_suml. apply: eq_bigr => x _. rewrite mulmx_suml. apply: eq_bigr => x' _. rewrite mulmx_suml. apply: eq_bigr => e Hgood. exact: Htriple_fix_P_evt Hgood. } have HP_evt_proj : P_evt \is projmx. { apply/projmxP_id; split. - exact: psdmx_herm HP_evt_psd. - exact: HP_evt_id. } have HrhoZZE_raw_psd : rhoZZE_raw \is psdmx.
        { rewrite /rhoZZE_raw.
          apply: psdmx_sum => pi _.
          apply: psdmxZ.
          - rewrite lecR.
            apply: divr_ge0.
            + exact: uniform_perm_mu_nonneg.
            + exact: ltW Hppass_pos.
          - exact: Htriple_psd _ _ _. }
have HrhoZZE_raw_mul_Pevt : rhoZZE_raw *m P_evt = rhoZZE_raw.
        { rewrite /rhoZZE_raw mulmx_suml. apply: eq_bigr => pi. move=> /andP [_ Hgood]; rewrite -scalemxAl. apply: congr1. have Hgood_triple_pi : good_triple (bitstring_to_ord (@perm_pair_holdout n_key n_pe z pi)) (bitstring_to_ord (@perm_pair_holdout n_key n_pe z' pi)) (err_ord pi). { move: Hgood; by rewrite -(Hgood_tripleE pi). } exact: Htriple_fix_P_evt Hgood_triple_pi. } have HrhoZZE_mul_Pevt : rhoZZE *m P_evt = rhoZZE_raw.
        { rewrite /rhoZZE /rhoZZE_raw mulmx_suml [LHS](bigID (mem good_event)) /=. have Hbad_part : \sum_(pi in pass_event | pi \notin good_event) (((@uniform_perm_mu R (n_pe + n_key) pi / p_pass)%:C) *: triple_basis_projector (bitstring_to_ord (@perm_pair_holdout n_key n_pe z pi)) (bitstring_to_ord (@perm_pair_holdout n_key n_pe z' pi)) (err_ord pi) *m P_evt) = 0. { apply: big1 => pi. move=> /andP [_ /negPf Hbad]. rewrite -scalemxAl Htriple_mul_P_evt (Hgood_tripleE pi) Hbad /=. by rewrite scaler0. } rewrite Hbad_part addr0. apply: eq_bigr => pi. move=> /andP [Hpass Hgood]; rewrite -scalemxAl. apply: congr1. have Hgood_triple_pi : good_triple (bitstring_to_ord (@perm_pair_holdout n_key n_pe z pi)) (bitstring_to_ord (@perm_pair_holdout n_key n_pe z' pi)) (err_ord pi). { move: Hgood; by rewrite -(Hgood_tripleE pi). } exact: (Htriple_fix_P_evt (bitstring_to_ord (@perm_pair_holdout n_key n_pe z pi)) (bitstring_to_ord (@perm_pair_holdout n_key n_pe z' pi)) (err_ord pi) Hgood_triple_pi). } have HPevt_mul_rhoZZE_raw : P_evt *m rhoZZE_raw = rhoZZE_raw.
        { rewrite /rhoZZE_raw mulmx_sumr. apply: eq_bigr => pi. move=> /andP [_ Hgood]; rewrite -scalemxAr. apply: congr1. have Hgood_triple_pi : good_triple (bitstring_to_ord (@perm_pair_holdout n_key n_pe z pi)) (bitstring_to_ord (@perm_pair_holdout n_key n_pe z' pi)) (err_ord pi). { move: Hgood; by rewrite -(Hgood_tripleE pi). } rewrite (Htriple_left_mul_P_evt (bitstring_to_ord (@perm_pair_holdout n_key n_pe z pi)) (bitstring_to_ord (@perm_pair_holdout n_key n_pe z' pi)) (err_ord pi)). by rewrite Hgood_triple_pi. } have HrhoP_eq : P_evt *m rhoZZE *m P_evt = rhoZZE_raw. { by rewrite -mulmxA HrhoZZE_mul_Pevt HPevt_mul_rhoZZE_raw. } have Htrace_rhoZZE_raw : \tr rhoZZE_raw = (\sum_(pi in pass_event | pi \in good_event) (@uniform_perm_mu R (n_pe + n_key) pi / p_pass))%:C.
        { rewrite /rhoZZE_raw linear_sum. rewrite (eq_bigr (fun pi => ((@uniform_perm_mu R (n_pe + n_key) pi / p_pass)%:C) * \tr (triple_basis_projector (bitstring_to_ord (@perm_pair_holdout n_key n_pe z pi)) (bitstring_to_ord (@perm_pair_holdout n_key n_pe z' pi)) (err_ord pi)))); last first. { move=> pi _; by rewrite linearZ. } rewrite (eq_bigr (fun pi => ((@uniform_perm_mu R (n_pe + n_key) pi / p_pass)%:C))); last first. { move=> pi _; by rewrite Htriple_trace mulr1. } by rewrite rmorph_sum. } have HrhoZZE_raw_tr : @complex.Re R (\tr rhoZZE_raw) = good_cond.
        { rewrite Htrace_rhoZZE_raw re_realid. apply: (mulIf Hppass_nz). rewrite mulr_suml. rewrite (eq_bigr (fun pi => @uniform_perm_mu R (n_pe + n_key) pi)); last first. { move=> pi _; by rewrite divrK. } exact: Hsum_good. } have HrhoZZE_good_scale : rhoZZE_good = ((good_cond^-1)%:C) *: rhoZZE_raw.
        { rewrite /rhoZZE_good Hgood0 /rhoZZE_raw scaler_sumr. apply: eq_bigr => pi _. rewrite scalerA -rmorphM /=. congr (_ *: _). have -> : @uniform_perm_mu R (n_pe + n_key) pi / (p_pass * good_cond) = (good_cond^-1) * (@uniform_perm_mu R (n_pe + n_key) pi / p_pass). { rewrite invrM ?Hppass_unit ?Hgood_cond_unit //. rewrite mulrA [@uniform_perm_mu R (n_pe + n_key) pi * good_cond^-1]mulrC. by rewrite -mulrA. } by []. } have Hfid_raw : @complex.Re R (trnorm (sqrtmx rhoZZE_raw *m sqrtmx rhoZZE)) = good_cond.
        { have [Hfid _] := fid_iv_proj_mx (P := P_evt) (rho := rhoZZE) (tau := rhoZZE) HP_evt_proj HrhoZZE_psd HrhoZZE_psd. move: Hfid; rewrite HrhoP_eq. move=> Hfid. have Hrhs : @complex.Re R (trnorm (sqrtmx rhoZZE_raw *m sqrtmx rhoZZE_raw)) = good_cond. { by rewrite (sqrtmxK HrhoZZE_raw_psd) psdmx_trnorm // HrhoZZE_raw_tr. } by rewrite Hrhs in Hfid. } have Hfid_scale_left : @complex.Re R (trnorm (sqrtmx rhoZZE_good *m sqrtmx rhoZZE)) = Num.sqrt (good_cond^-1) * @complex.Re R (trnorm (sqrtmx rhoZZE_raw *m sqrtmx rhoZZE)).
        { rewrite HrhoZZE_good_scale. have Hgood_inv_ge0 : (0 <= good_cond^-1)%R. { by rewrite invr_ge0 ltW. } rewrite (sqrtmxZ_nn (c := good_cond^-1) (M := rhoZZE_raw) Hgood_inv_ge0 HrhoZZE_raw_psd). rewrite -scalemxAl trnormZ. rewrite (ger0_norm (x := (Num.sqrt (good_cond^-1))%:C)); last first. { by rewrite lecR sqrtr_ge0. } have Hreal : \tr| sqrtmx rhoZZE_raw *m sqrtmx rhoZZE | \is Num.real. { exact: schnorm_real. } by rewrite -(RRe_real Hreal) -rmorphM /=. } have Hgf_big : gfidelity rhoZZE_good rhoZZE = Num.sqrt good_cond.
        { rewrite (alt_gfid_gen HrhoZZE_good_psd HrhoZZE_psd). have Hsqrt_tau0 : Num.sqrt (@complex.Re R (1 - \tr rhoZZE)) = 0. { by rewrite raddfB /= HrhoZZE_tr1 subrr sqrtr0. } rewrite Hsqrt_tau0 mulr0 addr0 Hfid_scale_left Hfid_raw. have Hsqrt_inv := sqrtr_inv_div1 Hgood_cond_pos. rewrite Hsqrt_inv mul1r. have HgoodE : good_cond = (Num.sqrt good_cond) ^+ 2. { by rewrite sqr_sqrtr // ltW. } rewrite [X in _ * X = _]HgoodE. have Hsqrtg_nz : Num.sqrt good_cond != 0. { rewrite sqrtr_eq0. move: Hgood_cond_pos; by rewrite ltNge. } have Hcancel : (Num.sqrt good_cond)^-1 * (Num.sqrt good_cond * Num.sqrt good_cond) = Num.sqrt good_cond. { have -> : (Num.sqrt good_cond)^-1 * (Num.sqrt good_cond * Num.sqrt good_cond) = ((Num.sqrt good_cond)^-1 * Num.sqrt good_cond) * Num.sqrt good_cond. { by rewrite mulrA. } by rewrite mulVf ?mul1r. } by rewrite expr2 Hcancel. } rewrite /pur_dist_mx Hgf_big.
        have Hsq_good : Num.sqrt good_cond ^ 2 = good_cond. { change (Num.sqrt good_cond ^+ 2 = good_cond). by rewrite sqr_sqrtr //. } rewrite Hsq_good -Heps'_E.
        exact: ler_wsqrtr H1mgood_le. }
have Hpd_good : pur_dist_mx rhoZZ'_good rhoZZ' <= eps' := le_trans Hpdmx_ptrace2 Hbig_pd.
      have Heps2div_lt1 : eps ^+ 2 / p_pass < 1.
      { apply: ltr1_of_sqrt_lt1. by rewrite Heps'_E. } have Hgood_cond_pos : 0 < good_cond.
      { case Hgood0 : (good_cond == 0).
        - have Hone_le : 1 <= eps ^+ 2 / p_pass.
          { move: H1mgood_le. move/eqP: Hgood0 => ->. by rewrite subr0. } have := lt_le_trans Heps2div_lt1 Hone_le.
          by rewrite ltxx.
        - by rewrite lt_def Hgood_cond_nonneg Hgood0. }
have Hgood_cond_nz : good_cond != 0 := lt0r_neq0 Hgood_cond_pos.
      have Hgood_pos : 0 < @complex.Re R (\tr rhoZZ'_good).
      { by rewrite (Hgood_tr1_of_nz Hgood_cond_nz) ltr01. } split; [exact: Hpd_good | exact: Hgood_pos]. }
have Hgood_pd := Hgood_pd_pos.1.
    have Hgood_pos := Hgood_pd_pos.2.
    have Hball : ((rhoZZ'_good \is denmx) && (0 < @complex.Re R (\tr rhoZZ'_good))) && (pur_dist_mx rhoZZ'_good rhoZZ' <= eps').
    { have Hgood_den : rhoZZ'_good \is denmx. { apply/denmxP; split=> //. have Hreal : \tr rhoZZ'_good \is Num.real := ger0_real (psdmx_trace Hgood_psd). by rewrite -(RRe_real Hreal) lecR1. } by rewrite Hgood_den Hgood_pos Hgood_pd. } have Hhmax : hmax_mx rhoZZ'_good <= n_key%:R * h_trunc.
  { case Hgood0 : (good_cond == 0).
    - have Hrho0 : rhoZZ'_good = 0.
      { by rewrite /rhoZZ'_good Hgood0. } rewrite Hrho0.
        apply: le_trans Hrhs_nonneg.
        rewrite /hmax_mx.
        have Hset0 : [set v : R | exists sigma : 'M[C]_key_dim, sigma \is den1mx /\ elog2 (key_dim%:R * (gfidelity (0 : 'M[C]_(key_dim * key_dim)) (mmix_mx key_dim *t sigma)) ^+ 2) = v%:E]%classic = set0.
        { apply/seteqP; split=> [v [sigma [Hsigma_den Helog]] | v []]. have Hkey_pos : (0 < key_dim)%N := expn_gt0 2 n_key. have /den1mxP [Hsigma_psd /eqP Hsigma_tr1] := Hsigma_den. have Htau_psd : (mmix_mx key_dim *t sigma) \is psdmx. { apply: psdmx_tens. - exact: mmix_mx_psd. - exact: Hsigma_psd. } have Htau_tr1 : \tr (mmix_mx key_dim *t sigma) = 1. { by rewrite mxtrace_tens (@tr_mmix_mx R _ Hkey_pos) Hsigma_tr1 mulr1. } have Hgf0 : gfidelity (0 : 'M[C]_(key_dim * key_dim)) (mmix_mx key_dim *t sigma) = 0. { rewrite (alt_gfid_gen (psdmx0 C (key_dim * key_dim)) Htau_psd). by rewrite sqrtmx0 mul0mx trnorm0 raddf0 mxtrace0 subr0 sqrtr1 Htau_tr1 subrr sqrtr0 mulr0 add0r. } have Harg_le0 : key_dim%:R * (gfidelity (0 : 'M[C]_(key_dim * key_dim)) (mmix_mx key_dim *t sigma)) ^+ 2 <= 0. { by rewrite Hgf0 expr2 !mulr0. } move: Helog; rewrite (elog2_le0 Harg_le0). by discriminate. } by rewrite Hset0 sup0.
    - have Hrho_good_tr1 : @complex.Re R (\tr rhoZZ'_good) = 1 := Hgood_tr1_of_nz (negbT Hgood0).
      case: (lerP delta 0) => Hdelta_nonpos.
      * have Hzero : good_cond == 0 := Hgood0_of_delta_nonpos Hdelta_nonpos. by rewrite Hgood0 in Hzero.
      * exact: bb84_hmax_good_projector_bound Hn_key_pos Hdelta_nonpos Hgood_psd Hrho_good_tr1 HrhoZZ'_good_mul_P_good. }
rewrite /smooth_hmax_mx.
    pose witness_set : set R := fun v : R => exists tau : 'M[C]_(key_dim * key_dim), ((tau \is denmx) && (0 < @complex.Re R (\tr tau))) && (pur_dist_mx tau rhoZZ' <= eps') /\ v = hmax_mx tau.
  have HEgood : witness_set (hmax_mx rhoZZ'_good).
  { exists rhoZZ'_good. rewrite /witness_set /=. move/andP: Hball => [/andP[Hgood_den' Hgood_pos'] Hgood_pd']. by rewrite Hgood_den' Hgood_pos' Hgood_pd'. } have [HinfE|HinfE] := pselect (has_inf witness_set).
  - have HlbE : has_lbound witness_set by case: HinfE.
    have Hinf_lb : lbound witness_set (inf witness_set) := ge_inf HlbE.
    apply: le_trans Hhmax.
    exact: Hinf_lb _ HEgood.
  - rewrite (inf_out HinfE).
    exact: Hrhs_nonneg. Qed.

Lemma stat_mix (Zkey B : {set L})
    (disZB : [disjoint Zkey & B])
    (P : @bb84_protocol R) (G : bb84_zsource P) (eps : R)
    (rhoZZp : 'F[HL]_(Zkey :|: B))
    (dim_Zk : (2 ^ bb84_n P)%N = dim ('H[HL]_Zkey))
    (dim_B : (2 ^ bb84_n P)%N = dim ('H[HL]_B)) :
  (0 < bb84_n P)%N -> (0 < bb84_k P)%N -> 0 < eps -> rhoZZp \is psdlf -> 0 < bb84_p_pass_tot G ->
  let eps' := eps / Num.sqrt (bb84_p_pass_tot G) in
  eps' < 1 -> let h_trunc :=
    bb84_h_trunc (bb84_Qtol P +
      bb84_mu (bb84_n P) (bb84_k P) eps) in
  biprod_mx disZB rhoZZp =
    castmx (f_equal2 muln dim_Zk dim_B, f_equal2 muln dim_Zk dim_B)
      (bb84_rhoZZ_pass_mix G) -> smooth_hmax B eps' rhoZZp <= (bb84_n P)%:R * h_trunc.
Proof.
  move=> Hn_pos Hk_pos Heps_pos HrhoZZp_psd Hpass_pos /= Heps'_lt1 Hmx.
  rewrite (smooth_hmax_labelled_mx disZB _ HrhoZZp_psd) Hmx smooth_hmax_mx_cast_bipartite.
  pose n_key := bb84_n P.
  pose key_dim := (2 ^ n_key)%N.
  pose pass := bb84_p_pass_tot G.
  pose delta := bb84_Qtol P + bb84_mu (bb84_n P) (bb84_k P) eps.
  pose eps' := eps / Num.sqrt pass.
  pose rho : 'M[C]_(key_dim * key_dim) := bb84_rhoZZ_pass_mix G.
  pose Pgood : 'M[C]_(key_dim * key_dim) := @bb84_good_projector R n_key delta.
  pose raw : 'M[C]_(key_dim * key_dim) := Pgood *m rho *m Pgood.
  pose mass := @complex.Re R (\tr raw).
  pose tau : 'M[C]_(key_dim * key_dim) := (mass^-1)%:C *: raw.
  have Hpass_nz : pass != 0 := lt0r_neq0 Hpass_pos.
  have Hpass_unit : pass \is a GRing.unit by rewrite unitfE.
  have Hrho_psd : rho \is psdmx. { rewrite /rho. exact: bb84_rhoZZ_pass_mix_psdmx. } have Hrho_tr1 : @complex.Re R (\tr rho) = 1. { rewrite /rho. exact: bb84_rhoZZ_pass_mix_tr1. } have HPgood_proj : Pgood \is projmx. { rewrite /Pgood /n_key. exact: bb84_good_projector_proj. } have Hmass_lb : 1 - bb84_pass_bad_weight G eps / pass <= mass.
  { rewrite /mass /raw /Pgood /rho /delta /pass /n_key. exact: bb84_good_projector_pass_mass. } have H1mass_le_bad : 1 - mass <= bb84_pass_bad_weight G eps / pass.
  { rewrite lerBlDr. move: Hmass_lb; by rewrite lerBlDr addrC. } have Hbad_le : bb84_pass_bad_weight G eps <= eps ^+ 2. { exact: bb84_pass_bad_weight_le. } have Hbad_div_le : bb84_pass_bad_weight G eps / pass <= eps ^+ 2 / pass.
  { rewrite ler_pdivrMr //. by rewrite divfK. } have H1mass_le_eps : 1 - mass <= eps ^+ 2 / pass := le_trans H1mass_le_bad Hbad_div_le.
  have Heps'_E : Num.sqrt (eps ^+ 2 / pass) = eps' := sqrtr_sq_div (ltW Heps_pos) Hpass_pos.
  have Heps2div_lt1 : eps ^+ 2 / pass < 1.
  { apply: ltr1_of_sqrt_lt1. by rewrite Heps'_E. } have Hmass_pos : 0 < mass.
  { have H1mass_lt1 : 1 - mass < 1 := le_lt_trans H1mass_le_eps Heps2div_lt1. move: H1mass_lt1; by rewrite ltrBlDr ltrDl. } have Hdelta_pos : 0 < delta.
  { case: (lerP delta 0) => [Hdelta_nonpos|Hdelta_pos].
    - have HPgood0 : Pgood = 0.
      { rewrite /Pgood /bb84_good_projector. apply: big1 => x _. apply: big1 => x' Hrel. move: Hrel; rewrite /relative_hamming_ball. set v := (d_ham _ _)%:R / n_key%:R. have Hv_ge0 : 0 <= v. { rewrite /v. apply: divr_ge0. - by rewrite ler0n. - by rewrite ler0n. } move=> Hv_lt_delta; have Hv_lt0 : v < 0 := lt_le_trans Hv_lt_delta Hdelta_nonpos. move: Hv_lt0; by rewrite ltNge Hv_ge0. } move: Hmass_pos; rewrite /mass /raw HPgood0 mul0mx mul0mx mxtrace0 raddf0.
      by rewrite ltxx.
    - by []. }
have [Htau_psd Htau_tr1 HtauP Hpd_eq] : [/\ tau \is psdmx, @complex.Re R (\tr tau) = 1, tau *m Pgood = tau & pur_dist_mx tau rho = Num.sqrt (1 - mass)].
  { exact: (@projected_mx_normalized_witness key_dim key_dim Pgood rho HPgood_proj Hrho_psd Hrho_tr1 Hmass_pos). } have Hpd : pur_dist_mx tau rho <= eps'. { rewrite Hpd_eq -Heps'_E. exact: ler_wsqrtr H1mass_le_eps. } have Hhmax : hmax_mx tau <= (bb84_n P)%:R * bb84_h_trunc delta.
  { rewrite /tau /raw in Htau_psd Htau_tr1 HtauP *. exact: bb84_hmax_good_projector_bound Hn_pos Hdelta_pos Htau_psd Htau_tr1 HtauP. } have Hrhs_nonneg : 0 <= (bb84_n P)%:R * bb84_h_trunc delta.
  { apply: mulr_ge0. - by rewrite ler0n. - exact: bb84_h_trunc_nonneg. } rewrite /smooth_hmax_mx.
  pose witness_set : set R := fun v : R => exists tau0 : 'M[C]_(key_dim * key_dim), ((tau0 \is denmx) && (0 < @complex.Re R (\tr tau0))) && (pur_dist_mx tau0 rho <= eps') /\ v = hmax_mx tau0.
  have Htau_den : tau \is denmx. { apply: denmx_psd_re_tr_le; first exact: Htau_psd. by rewrite Htau_tr1. } have Htau_pos : 0 < @complex.Re R (\tr tau) by rewrite Htau_tr1.
  have HEtau : witness_set (hmax_mx tau).
  { exists tau. rewrite /witness_set /=. by rewrite Htau_den Htau_pos Hpd. } have [HinfE|HinfE] := pselect (has_inf witness_set).
  - have HlbE : has_lbound witness_set by case: HinfE.
    have Hinf_lb : lbound witness_set (inf witness_set) := ge_inf HlbE.
    apply: le_trans Hhmax.
    exact: Hinf_lb _ HEtau.
  - rewrite (inf_out HinfE).
    exact: Hrhs_nonneg. Qed.

Lemma chain_rule_class
    (C : {set L})
    (disSC : [disjoint S & C])
    (disEC : [disjoint E & C])
    (disC_SE : [disjoint C & (S :|: E)])
    (eps' : R)
    (rho : 'F[HL]_(C :|: (S :|: E))) :
  rho \is psdlf -> @complex.Re R (\Tr rho) <= 1 -> (forall x x' : 'Idx[HL]_C, x' != x ->
    (([> deltav x ; deltav x <] \O (\1 : 'F_(S :|: E))) \o rho \o
     ([> deltav x' ; deltav x' <] \O (\1 : 'F_(S :|: E)))) = 0) ->
  0 <= eps' < Num.sqrt (@complex.Re R (\Tr rho)) -> (smooth_hminE E eps' (ptrace_castl disC_SE rho) -
      (log2 (dim 'H[HL]_C)%:R)%:E <=
    smooth_hminE (E :|: C) eps' rho)%E.
Proof.
  move=> Hrho Hrho_tr Hclass /andP [Heps0 Hrange].
  have disCS : [disjoint C & S] by rewrite disjoint_sym.
  have disCE : [disjoint C & E] by rewrite disjoint_sym.
  have Hrho_den : rho \is denlf.
  { apply/denlfP; split=> //.
    have Hreal : \Tr rho \is Num.real := ger0_real (psdlf_trlf Hrho).
    by rewrite -(RRe_real Hreal) lecR. } apply: (@class_bounds_2_min_lower R L HL C S E disCS disCE disSE disC_SE eps' rho Hrho_den Hclass).
  by rewrite Heps0 Hrange. Qed.

Fact chain_rule_class_leak_bound
    (C : {set L})
    (disSC : [disjoint S & C])
    (disEC : [disjoint E & C])
    (disC_SE : [disjoint C & (S :|: E)])
    (eps' leak : R)
    (rho : 'F[HL]_(C :|: (S :|: E))) :
  rho \is psdlf -> @complex.Re R (\Tr rho) <= 1 -> (forall x x' : 'Idx[HL]_C, x' != x ->
    (([> deltav x ; deltav x <] \O (\1 : 'F_(S :|: E))) \o rho \o
     ([> deltav x' ; deltav x' <] \O (\1 : 'F_(S :|: E)))) = 0) ->
  0 <= eps' < Num.sqrt (@complex.Re R (\Tr rho)) -> log2 (dim 'H[HL]_C)%:R <= leak ->
  (smooth_hminE E eps' (ptrace_castl disC_SE rho) - leak%:E <=
    smooth_hminE (E :|: C) eps' rho)%E.
Proof. move=> Hrho Hrho_tr Hclass Heps Hleak. have Hchain := @chain_rule_class C disSC disEC disC_SE eps' rho Hrho Hrho_tr Hclass Heps. apply: le_trans Hchain. apply: leeD; first exact: lexx. by rewrite leeN2 lee_fin. Qed.

End Secrecy.

End FvqkdReal.
