(* bb84.v -- BB84 main security theorems (correctness, secrecy, combined) *)
(* Module: qkd.bb84.bb84                                                *)
(* Paper: Tomamichel-Lim-Gisin-Renner, Nat. Commun. 3:634 (2012),       *)
(*   "Tight finite-key analysis for quantum cryptography".              *)
(* Covers Suppl. Thm 1 (correctness) and Suppl. Thm 2 (secrecy).        *)
(* The root goals of the BB84 formalization:                            *)
(*   bb84_correct -- eps_c-correctness                                  *)
(*   bb84_secret  -- eps_s-secrecy                                      *)
(*   bb84_secure            -- combined eps-security                    *)
(* Protocol-level security corollaries built on this layer live in     *)
(* qkd/example.                                                          *)

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
From entropy Require Import def prop.
From entropy.conv Require Import prop.
From entropy.smooth Require Import prop dpi.
From lhl Require Import def util post_hash prop.
From eur Require Import def prop eur.
From qkd.bb84 Require Import def model prop.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Open Scope ring_scope.
Local Open Scope lfun_scope.

Section FvqkdReal.
Variable R : realType.
Notation C := (@hermitian.C R).
Notation chsType := (@chsType R).
Notation bb84_protocol := (@bb84_protocol R).
Notation bb84_source_model := (@bb84_source_model R).

Section Correctness.
Variables (key_count seed_count tag_count : nat).
Variable (verify_hash : 'I_seed_count -> 'I_key_count -> 'I_tag_count).
Variable (corr_prob : 'I_key_count -> 'I_key_count -> R).

Local Notation verification_collision_prob :=
  (@verification_collision_prob R key_count seed_count tag_count verify_hash).
Local Notation p_mismatch :=
  (@p_mismatch R key_count seed_count tag_count verify_hash corr_prob).

Theorem bb84_correct (eps_c : R) :
  (0 < tag_count)%N -> @two_univ R _ _ _ verify_hash -> (forall x x', (0 <= corr_prob x x')%R) ->
  (\sum_x \sum_(x' | x != x') corr_prob x x' <= 1)%R -> ((((tag_count%:R : R)^-1)%R) <= eps_c)%R ->
  eps_correct p_mismatch eps_c.
Proof.
  move=> tag_count_pos H2u Hcorr Hmass Heps; rewrite /eps_correct /p_mismatch; apply: (le_trans _ Heps).
  have Hstep : \sum_x \sum_(x' | x != x') corr_prob x x' * verification_collision_prob x x' <= \sum_x \sum_(x' | x != x') corr_prob x x' * ((tag_count%:R : R)^-1)%R.
  { apply: ler_sum => x _; apply: ler_sum => x' Hneq; apply: ler_pM.
    1,2,3,4: by [exact: Hcorr | rewrite /verification_collision_prob divr_ge0 ?ler0n | exact: lexx | move: (H2u _ _ Hneq); rewrite /collision_probability !card_ord]. } apply: (le_trans Hstep).
  have -> : \sum_x \sum_(x' | x != x') corr_prob x x' * ((tag_count%:R : R)^-1)%R = (\sum_x \sum_(x' | x != x') corr_prob x x') * ((tag_count%:R : R)^-1)%R.
  { transitivity (\sum_x ((\sum_(x' | x != x') corr_prob x x') * ((tag_count%:R : R)^-1)%R)).
    - by apply: eq_bigr => x _; rewrite -mulr_suml.
    - by rewrite -mulr_suml. } set mismatch_mass := \sum_x \sum_(x' | x != x') corr_prob x x'.
  have Hmass_nonneg : 0 <= mismatch_mass by rewrite /mismatch_mass; apply: sumr_ge0 => x _; apply: sumr_ge0 => x' Hneq; exact: Hcorr.
  have Hinv_nonneg : 0 <= ((tag_count%:R : R)^-1)%R. { by rewrite invr_ge0 ler0n. } have Hscaled := ler_pM Hmass_nonneg Hinv_nonneg Hmass (lexx (((tag_count%:R : R)^-1)%R)).
  by rewrite mul1r in Hscaled. Qed.

End Correctness.

Section Secrecy.

Variable (L : finType) (HL : L -> chsType).
Variable (S E Zkey Bq Zp Fl Zl : {set L}).
Hypotheses (disSE : [disjoint S & E]) (disSZ : [disjoint S & Zkey]) (disSBq : [disjoint S & Bq]) (disSZp : [disjoint S & Zp]).
Hypotheses (disSF : [disjoint S & Fl]) (disSZl : [disjoint S & Zl]) (disEZ : [disjoint E & Zkey]) (disEBq : [disjoint E & Bq]).
Hypotheses (disEZp : [disjoint E & Zp]) (disEF : [disjoint E & Fl]) (disEZl : [disjoint E & Zl]) (disZBq : [disjoint Zkey & Bq]).
Hypotheses (disZZp : [disjoint Zkey & Zp]) (disFZl : [disjoint Fl & Zl]).
Variable Aux : @bb84_aux_regs R L HL Zkey Bq Zp.
Let AuxApp : {set L} := @bb84_aux_app R L HL Zkey Bq Zp Aux.
Let AuxBpp : {set L} := @bb84_aux_bpp R L HL Zkey Bq Zp Aux.
Let AuxCiso : {set L} := @bb84_aux_ciso R L HL Zkey Bq Zp Aux.
Let AuxCp_src : {set L} := @bb84_aux_cp_src R L HL Zkey Bq Zp Aux.
Let AuxCpp_src : {set L} := @bb84_aux_cpp_src R L HL Zkey Bq Zp Aux.
Let AuxCp_tgt : {set L} := @bb84_aux_cp_tgt R L HL Zkey Bq Zp Aux.
Let AuxCpp_tgt : {set L} := @bb84_aux_cpp_tgt R L HL Zkey Bq Zp Aux.
Let disZ_AuxApp := @bb84_aux_disZ_app R L HL Zkey Bq Zp Aux.
Let disZp_AuxBpp := @bb84_aux_disZp_bpp R L HL Zkey Bq Zp Aux.
Let disZ_AuxBpp := @bb84_aux_disZ_bpp R L HL Zkey Bq Zp Aux.
Let disAuxApp_Zp := @bb84_aux_disApp_Zp R L HL Zkey Bq Zp Aux.
Let disAuxApp_AuxBpp := @bb84_aux_disApp_bpp R L HL Zkey Bq Zp Aux.
Let dimAuxApp_enough := @bb84_aux_dim_app R L HL Zkey Bq Zp Aux.
Let dimAuxBpp_enough := @bb84_aux_dim_bpp R L HL Zkey Bq Zp Aux.
Let disZ_AuxCiso := @bb84_aux_disZ_ciso R L HL Zkey Bq Zp Aux.
Let disBq_AuxCiso := @bb84_aux_disBq_ciso R L HL Zkey Bq Zp Aux.
Let disZApp_AuxCiso := @bb84_aux_disZApp_ciso R L HL Zkey Bq Zp Aux.
Let disZpBpp_AuxCiso := @bb84_aux_disZpBpp_ciso R L HL Zkey Bq Zp Aux.
Let dimZBq_AuxCiso := @bb84_aux_dim_ZB_ciso R L HL Zkey Bq Zp Aux.
Let dimZAppBBpp_AuxCiso :=
  @bb84_aux_dim_ZAppBBpp_ciso R L HL Zkey Bq Zp Aux.
Let disZ_AuxCp_src := @bb84_aux_disZ_cp_src R L HL Zkey Bq Zp Aux.
Let disZ_AuxCpp_src := @bb84_aux_disZ_cpp_src R L HL Zkey Bq Zp Aux.
Let disBq_AuxCp_src := @bb84_aux_disBq_cp_src R L HL Zkey Bq Zp Aux.
Let disBq_AuxCpp_src := @bb84_aux_disBq_cpp_src R L HL Zkey Bq Zp Aux.
Let disAuxCiso_AuxCp_src :=
  @bb84_aux_disCiso_cp_src R L HL Zkey Bq Zp Aux.
Let disAuxCiso_AuxCpp_src :=
  @bb84_aux_disCiso_cpp_src R L HL Zkey Bq Zp Aux.
Let disAuxCp_AuxCpp_src := @bb84_aux_disCp_cpp_src R L HL Zkey Bq Zp Aux.
Let dimZ_AuxCp_src := @bb84_aux_dim_Z_cp_src R L HL Zkey Bq Zp Aux.
Let dimAuxCisoCp_AuxCpp_src :=
  @bb84_aux_dim_CisoCp_cpp_src R L HL Zkey Bq Zp Aux.
Let dimBq_AuxCpp_src := @bb84_aux_dim_Bq_cpp_src R L HL Zkey Bq Zp Aux.
Let disZApp_AuxCp_tgt := @bb84_aux_disZApp_cp_tgt R L HL Zkey Bq Zp Aux.
Let disZApp_AuxCpp_tgt := @bb84_aux_disZApp_cpp_tgt R L HL Zkey Bq Zp Aux.
Let disZpBpp_AuxCp_tgt := @bb84_aux_disZpBpp_cp_tgt R L HL Zkey Bq Zp Aux.
Let disZpBpp_AuxCpp_tgt := @bb84_aux_disZpBpp_cpp_tgt R L HL Zkey Bq Zp Aux.
Let disAuxCiso_AuxCp_tgt :=
  @bb84_aux_disCiso_cp_tgt R L HL Zkey Bq Zp Aux.
Let disAuxCiso_AuxCpp_tgt :=
  @bb84_aux_disCiso_cpp_tgt R L HL Zkey Bq Zp Aux.
Let disAuxCp_AuxCpp_tgt := @bb84_aux_disCp_cpp_tgt R L HL Zkey Bq Zp Aux.
Let dimZApp_AuxCp_tgt := @bb84_aux_dim_ZApp_cp_tgt R L HL Zkey Bq Zp Aux.
Let dimAuxCisoCp_AuxCpp_tgt :=
  @bb84_aux_dim_CisoCp_cpp_tgt R L HL Zkey Bq Zp Aux.
Let dimZpBpp_AuxCpp_tgt := @bb84_aux_dim_ZpBpp_cpp_tgt R L HL Zkey Bq Zp Aux.

Definition bb84_register_pair_dim (A B : {set L})
    (disAB : [disjoint A & B]) (na nb : nat)
    (dim_A : na = dim ('H[HL]_A))
    (dim_B : nb = dim ('H[HL]_B)) :
  na * nb = dim ('H[HL]_(A :|: B)).
Proof. by rewrite tenv_dim // -dim_A -dim_B. Defined.

Definition bb84_source_zkey_dim (P : bb84_protocol) (q : R)
    (src : bb84_source_model P q) (Z : {set L})
    (dim_Z : @bb84_src_nz R P q src = dim ('H[HL]_Z)) :
  (2 ^ bb84_n P)%N = dim ('H[HL]_Z).
Proof. by rewrite -dim_Z (@bb84_src_dim_Z R P q src). Defined.

Definition bb84_source_bob_key_dim (P : bb84_protocol) (q : R)
    (src : bb84_source_model P q) (B : {set L})
    (dim_B : @bb84_src_nc R P q src = dim ('H[HL]_B)) :
  (2 ^ bb84_n P)%N = dim ('H[HL]_B).
Proof. by rewrite -dim_B (@bb84_src_dim_B R P q src). Defined.

Let disZl_FE : [disjoint Zl & (Fl :|: E)].
Proof. by rewrite disjointXU disjoint_sym disFZl disjoint_sym disEZl. Defined.

Fact bb84_dmc_source_den1 (BobZ : 'QC[HL]_(Bq, Zp))
    (rhoZB : 'F[HL]_(Zkey :|: Bq))
    (rhoZZp : 'F[HL]_(Zkey :|: Zp)) :
  bb84_delayed_measurement_condition BobZ rhoZB rhoZZp -> rhoZB \is den1lf.
Proof. by case=> rhoFull Hfull_den1 Hsrc _; rewrite -Hsrc; exact: ptrace_cast3C_den1lf Hfull_den1. Qed.

Fact bb84_delayed_measurement_map_cptp (BobZ : 'QC[HL]_(Bq, Zp)) :
  ((((\:1 : 'SO[HL]_Zkey) :⊗ BobZ) :⊗
    (\:1 : 'SO[HL]_finset.set0)) \is cptp).
Proof.
  have Hleft : (((\:1 : 'SO[HL]_Zkey) :⊗ BobZ) \is cptp).
  { exact: (@tenso_qc R L HL Zkey Zkey Bq Zp disZBq disZZp (QChannel_Build (idso_qc 'H[HL]_Zkey)) BobZ). } exact: (@tenso_qc R L HL (Zkey :|: Bq) (Zkey :|: Zp) finset.set0 finset.set0 (disjointX0 (Zkey :|: Bq)) (disjointX0 (Zkey :|: Zp)) (QChannel_Build Hleft) (QChannel_Build (idso_qc 'H[HL]_finset.set0))). Qed.

Fact bb84_dmc_target_den1 (BobZ : 'QC[HL]_(Bq, Zp))
    (rhoZB : 'F[HL]_(Zkey :|: Bq))
    (rhoZZp : 'F[HL]_(Zkey :|: Zp)) :
  bb84_delayed_measurement_condition BobZ rhoZB rhoZZp -> rhoZZp \is den1lf.
Proof.
  case=> rhoFull Hfull_den1 _ Htgt; rewrite -Htgt; apply: ptrace_cast3C_den1lf.
  have Hmap_cptp := bb84_delayed_measurement_map_cptp BobZ.
  apply/den1lfP; split.
  - by rewrite (CPMap_BuildE (cptp_cpmap Hmap_cptp)); exact: cp_psdP (den1lf_psd Hfull_den1).
  - by have /cptpP [_ /tpmapP Htp] := Hmap_cptp; rewrite Htp (den1lf_trlf Hfull_den1). Qed.

Fact bb84_bob_z_basis_readout_unit
    (P : bb84_protocol)
    (dim_Zk_key : (2 ^ bb84_n P)%N = dim ('H[HL]_Zkey))
    (dim_Bq_key : (2 ^ bb84_n P)%N = dim ('H[HL]_Bq))
    (dim_Zp_key : (2 ^ bb84_n P)%N = dim ('H[HL]_Zp))
    (c : C) (a a' b b' : 'I_(2 ^ bb84_n P)) :
  let dim_BqZp := etrans (esym dim_Bq_key) dim_Zp_key in
  biprod_mx disZZp
    (((\:1 : 'SO[HL]_Zkey) :⊗
      (bob_z_basis_qchannel (bob_z_canonical_readout dim_BqZp)
        : 'SO[HL]_(Bq, Zp)))
      (biprod_of_mx disZBq
        (castmx (f_equal2 muln dim_Zk_key dim_Bq_key,
                 f_equal2 muln dim_Zk_key dim_Bq_key)
          (c *: ((delta_mx a a' : 'M[C]_(2 ^ bb84_n P)) *t
                 (delta_mx b b' : 'M[C]_(2 ^ bb84_n P))))))) =
  if b == b' then
    castmx (f_equal2 muln dim_Zk_key dim_Zp_key,
            f_equal2 muln dim_Zk_key dim_Zp_key)
      (c *: ((delta_mx a a' : 'M[C]_(2 ^ bb84_n P)) *t
             (delta_mx b b : 'M[C]_(2 ^ bb84_n P))))
  else 0.
Proof.
  rewrite /=; set dim_BqZp := etrans (esym dim_Bq_key) dim_Zp_key.
  set BobZ := bob_z_basis_qchannel (bob_z_canonical_readout dim_BqZp).
  have Hcast_scaleZ (m n : nat) (e : m = n) (c0 : C) (M0 : 'M[C]_(m, m)) : castmx (e, e) (c0 *: M0) = c0 *: castmx (e, e) M0 by case: n / e; rewrite !castmx_id.
  rewrite Hcast_scaleZ biprod_of_mxZ.
  set rho_ab := biprod_of_mx disZBq (castmx (f_equal2 muln dim_Zk_key dim_Bq_key, f_equal2 muln dim_Zk_key dim_Bq_key) ((delta_mx a a' : 'M[C]_(2 ^ bb84_n P)) *t (delta_mx b b' : 'M[C]_(2 ^ bb84_n P)))).
  change (biprod_mx disZZp (((\:1 : 'SO[HL]_Zkey) :⊗ BobZ) (c *: rho_ab)) = if b == b' then castmx (f_equal2 muln dim_Zk_key dim_Zp_key, f_equal2 muln dim_Zk_key dim_Zp_key) (c *: ((delta_mx a a' : 'M[C]_(2 ^ bb84_n P)) *t (delta_mx b b : 'M[C]_(2 ^ bb84_n P)))) else 0).
  have HsoZ : (((\:1 : 'SO[HL]_Zkey) :⊗ BobZ) (c *: rho_ab)) = c *: (((\:1 : 'SO[HL]_Zkey) :⊗ BobZ) rho_ab) by exact: linearZ.
  rewrite HsoZ (@biprod_mxZ R L HL Zkey Zp disZZp) /rho_ab.
  have Hcast_tensmx : forall (m1 m2 n1 n2 : nat) (em : m1 = m2) (en : n1 = n2) (A : 'M[C]_(m1)) (B : 'M[C]_(n1)), castmx (f_equal2 muln em en, f_equal2 muln em en) (A *t B) = castmx (em, em) A *t castmx (en, en) B by move=> m1 m2 n1 n2 em en A B; case: m2 / em; case: n2 / en; rewrite !castmx_id.
  have Hdelta_cast_h2mx : forall (S0 : {set L}) (e : (2 ^ bb84_n P)%N = dim 'H[HL]_S0) (a1 a2 : 'I_(2 ^ bb84_n P)), castmx (e, e) (@delta_mx C _ _ a1 a2) = h2mx [> deltav (@n2i R L HL S0 (cast_ord e a1)) ; deltav (@n2i R L HL S0 (cast_ord e a2)) <] by move=> S0 e a1 a2; rewrite mcextra.delta_mx_cast h2mx_deltav_outp n2iK n2iK.
  case Hbb' : (b == b').
  - rewrite [in RHS]Hcast_scaleZ; apply/f_equal.
    move/eqP: Hbb' => Hb_eq; subst b'; rewrite (Hcast_tensmx _ _ _ _ dim_Zk_key dim_Bq_key).
    rewrite !(Hdelta_cast_h2mx _ dim_Zk_key) !(Hdelta_cast_h2mx _ dim_Bq_key) (biprod_of_mx_sdot disZBq).
    change (biprod_mx disZZp (((\:1 : 'SO[HL]_Zkey) :⊗ basis_channel (bob_z_canonical_readout dim_BqZp)) ([> deltav (@n2i R L HL Zkey (cast_ord dim_Zk_key a)) ; deltav (@n2i R L HL Zkey (cast_ord dim_Zk_key a')) <] \O [> deltav (@n2i R L HL Bq (cast_ord dim_Bq_key b)) ; deltav (@n2i R L HL Bq (cast_ord dim_Bq_key b)) <])) = castmx (f_equal2 muln dim_Zk_key dim_Zp_key, f_equal2 muln dim_Zk_key dim_Zp_key) (delta_mx a a' *t delta_mx b b)).
    rewrite (tenso_sdot_correct disZBq disZZp (\:1 : 'SO[HL]_Zkey) (basis_channel (bob_z_canonical_readout dim_BqZp))) id_soE /BobZ /bob_z_basis_qchannel /basis_channel kraussoE.
    under eq_bigr do rewrite adj_outp -comp_lfunA outp_comp.
    rewrite (bigD1 (@n2i R L HL Bq (cast_ord dim_Bq_key b))) //=.
    rewrite dv_dot eqxx scale1r outp_comp dv_dot eqxx scale1r big1 ?addr0.
    2:{ by move=> x Hxneq; rewrite -comp_lfunZr dv_dot eq_sym (negbTE Hxneq) scale0r. } have Hreadout : bob_z_canonical_readout dim_BqZp (@n2i R L HL Bq (cast_ord dim_Bq_key b)) = @n2i R L HL Zp (cast_ord dim_Zp_key b) by rewrite /bob_z_canonical_readout n2iK; congr n2i; apply: val_inj.
    rewrite Hreadout (Hcast_tensmx _ _ _ _ dim_Zk_key dim_Zp_key).
    by rewrite !(Hdelta_cast_h2mx _ dim_Zk_key) !(Hdelta_cast_h2mx _ dim_Zp_key) biprod_mx_sdot.
  - suff Hzero : biprod_mx disZZp (((\:1 : 'SO[HL]_Zkey) :⊗ basis_channel (bob_z_canonical_readout dim_BqZp)) (biprod_of_mx disZBq (castmx (f_equal2 muln dim_Zk_key dim_Bq_key, f_equal2 muln dim_Zk_key dim_Bq_key) ((delta_mx a a' : 'M[C]_(2 ^ bb84_n P)) *t (delta_mx b b' : 'M[C]_(2 ^ bb84_n P)))))) = 0.
    { by rewrite Hzero scaler0. } rewrite (Hcast_tensmx _ _ _ _ dim_Zk_key dim_Bq_key).
    rewrite !(Hdelta_cast_h2mx _ dim_Zk_key) !(Hdelta_cast_h2mx _ dim_Bq_key) (biprod_of_mx_sdot disZBq).
    change (biprod_mx disZZp (((\:1 : 'SO[HL]_Zkey) :⊗ basis_channel (bob_z_canonical_readout dim_BqZp)) ([> deltav (@n2i R L HL Zkey (cast_ord dim_Zk_key a)) ; deltav (@n2i R L HL Zkey (cast_ord dim_Zk_key a')) <] \O [> deltav (@n2i R L HL Bq (cast_ord dim_Bq_key b)) ; deltav (@n2i R L HL Bq (cast_ord dim_Bq_key b')) <])) = 0).
    rewrite (tenso_sdot_correct disZBq disZZp (\:1 : 'SO[HL]_Zkey) (basis_channel (bob_z_canonical_readout dim_BqZp))) id_soE.
    have Hbasis0 : basis_channel (bob_z_canonical_readout dim_BqZp) [> deltav (@n2i R L HL Bq (cast_ord dim_Bq_key b)) ; deltav (@n2i R L HL Bq (cast_ord dim_Bq_key b')) <] = 0.
    { rewrite /basis_channel kraussoE.
      under eq_bigr do rewrite adj_outp -comp_lfunA outp_comp.
      rewrite (bigD1 (@n2i R L HL Bq (cast_ord dim_Bq_key b))) //=.
      have Hbidx_ne : @n2i R L HL Bq (cast_ord dim_Bq_key b') != @n2i R L HL Bq (cast_ord dim_Bq_key b).
      { apply/eqP => Hidx; move: Hbb'; move: (f_equal (@i2n R L HL Bq) Hidx).
        by rewrite !n2iK => Hcast; rewrite (cast_ord_inj Hcast) eqxx. } rewrite dv_dot (negbTE Hbidx_ne) scale0r comp_lfun0r big1 ?addr0 // => x Hxneq.
      by rewrite -comp_lfunZr dv_dot outp_comp dv_dot eq_sym (negbTE Hxneq) scale0r scaler0. } by rewrite Hbasis0 sdotf0 /biprod_mx h2mx0 linear0 mulmx0 mul0mx. Qed.

Fact bb84_bob_z_basis_readout_block
    (P : bb84_protocol)
    (dim_Zk_key : (2 ^ bb84_n P)%N = dim ('H[HL]_Zkey))
    (dim_Bq_key : (2 ^ bb84_n P)%N = dim ('H[HL]_Bq))
    (dim_Zp_key : (2 ^ bb84_n P)%N = dim ('H[HL]_Zp))
    (a : 'I_(2 ^ bb84_n P))
    (B : 'M[C]_(2 ^ bb84_n P)) :
  let dim_BqZp := etrans (esym dim_Bq_key) dim_Zp_key in
  biprod_mx disZZp
    (((\:1 : 'SO[HL]_Zkey) :⊗
      (bob_z_basis_qchannel (bob_z_canonical_readout dim_BqZp)
        : 'SO[HL]_(Bq, Zp)))
      (biprod_of_mx disZBq
        (castmx (f_equal2 muln dim_Zk_key dim_Bq_key,
                 f_equal2 muln dim_Zk_key dim_Bq_key)
          ((delta_mx a a : 'M[C]_(2 ^ bb84_n P)) *t B)))) =
  castmx (f_equal2 muln dim_Zk_key dim_Zp_key,
          f_equal2 muln dim_Zk_key dim_Zp_key)
    (\sum_(b : 'I_(2 ^ bb84_n P))
      B b b *: ((delta_mx a a : 'M[C]_(2 ^ bb84_n P)) *t
                (delta_mx b b : 'M[C]_(2 ^ bb84_n P)))).
Proof.
  rewrite /=; set dim_BqZp := etrans (esym dim_Bq_key) dim_Zp_key.
  set BobZ := bob_z_basis_qchannel (bob_z_canonical_readout dim_BqZp).
  set e_src := f_equal2 muln dim_Zk_key dim_Bq_key; set e_tgt := f_equal2 muln dim_Zk_key dim_Zp_key.
  have Hcast_addD : forall (m n : nat) (e : m = n) (A0 B0 : 'M[C]_m), castmx (e, e) (A0 + B0) = castmx (e, e) A0 + castmx (e, e) B0 by move=> m n e A0 B0; case: n / e; rewrite !castmx_id.
  have Hcast_0 : forall (m n : nat) (e : m = n), castmx (e, e) (0 : 'M[C]_m) = 0 by move=> m n e; case: n / e; rewrite castmx_id.
  set F := fun M : 'M[C]_((2 ^ bb84_n P) * (2 ^ bb84_n P)) => biprod_mx disZZp (((\:1 : 'SO[HL]_Zkey) :⊗ (BobZ : 'SO[HL]_(Bq, Zp))) (biprod_of_mx disZBq (castmx (e_src, e_src) M))).
  set G := fun M : 'M[C]_((2 ^ bb84_n P) * (2 ^ bb84_n P)) => castmx (e_tgt, e_tgt) M.
  have Hbiprod_of_mx_addD_src (A0 B0 : 'M[C]_(dim 'H[HL]_Zkey * dim 'H[HL]_Bq)) : @biprod_of_mx R L HL Zkey Bq disZBq (A0 + B0) = @biprod_of_mx R L HL Zkey Bq disZBq A0 + @biprod_of_mx R L HL Zkey Bq disZBq B0 by rewrite /biprod_of_mx mulmxDr mulmxDl !linearD.
  have Hbiprod_of_mx_0_src : @biprod_of_mx R L HL Zkey Bq disZBq 0 = 0 by rewrite /biprod_of_mx mulmx0 mul0mx !linear0.
  have Hso_addD (x y : 'F[HL]_(Zkey :|: Bq)) : ((\:1 : 'SO[HL]_Zkey) :⊗ (BobZ : 'SO[HL]_(Bq, Zp))) (x + y) = ((\:1 : 'SO[HL]_Zkey) :⊗ (BobZ : 'SO[HL]_(Bq, Zp))) x + ((\:1 : 'SO[HL]_Zkey) :⊗ (BobZ : 'SO[HL]_(Bq, Zp))) y by exact: linearD.
  have Hso_0 : ((\:1 : 'SO[HL]_Zkey) :⊗ (BobZ : 'SO[HL]_(Bq, Zp))) (0 : 'F[HL]_(Zkey :|: Bq)) = 0 by exact: linear0.
  have Hbiprod_mx_D (x y : 'F[HL]_(Zkey :|: Zp)) : @biprod_mx R L HL Zkey Zp disZZp (x + y) = @biprod_mx R L HL Zkey Zp disZZp x + @biprod_mx R L HL Zkey Zp disZZp y by rewrite /biprod_mx raddfD /= raddfD mulmxDr mulmxDl.
  have Hbiprod_mx_0 : @biprod_mx R L HL Zkey Zp disZZp 0 = 0 by rewrite /biprod_mx h2mx0 linear0 mulmx0 mul0mx.
  have HF_add (A0 B0 : 'M[C]_((2 ^ bb84_n P) * (2 ^ bb84_n P))) : F (A0 + B0) = F A0 + F B0.
  { by rewrite /F Hcast_addD Hbiprod_of_mx_addD_src Hso_addD Hbiprod_mx_D. } have HF_0 : F (0 : 'M[C]_((2 ^ bb84_n P) * (2 ^ bb84_n P))) = 0 by rewrite /F Hcast_0 Hbiprod_of_mx_0_src Hso_0 Hbiprod_mx_0.
  have HG_add (A0 B0 : 'M[C]_((2 ^ bb84_n P) * (2 ^ bb84_n P))) : G (A0 + B0) = G A0 + G B0 by rewrite /G Hcast_addD.
  have HG_0 : G (0 : 'M[C]_((2 ^ bb84_n P) * (2 ^ bb84_n P))) = 0 by rewrite /G Hcast_0.
  have HtensmxZr (c : C) (A0 B0 : 'M[C]_(2 ^ bb84_n P)) : A0 *t (c *: B0) = c *: (A0 *t B0).
  { by rewrite -[c *: B0]addr0 (linear_tensmx A0) linear0r addr0. } change (F ((delta_mx a a : 'M[C]_(2 ^ bb84_n P)) *t B) = G (\sum_(b : 'I_(2 ^ bb84_n P)) B b b *: ((delta_mx a a : 'M[C]_(2 ^ bb84_n P)) *t (delta_mx b b : 'M[C]_(2 ^ bb84_n P))))).
  rewrite {1}(mx_delta_basis B) tensmx_sumr.
  under eq_bigr => b _ do rewrite tensmx_sumr.
  under eq_bigr => b _ do under eq_bigr => b' _ do rewrite HtensmxZr.
  rewrite (big_morph F HF_add HF_0).
  under eq_bigr => b _ do rewrite (big_morph F HF_add HF_0).
  rewrite [RHS](big_morph G HG_add HG_0); apply: eq_bigr => b _; rewrite (bigD1 b) //=.
  have Hdiag : F (B b b *: ((delta_mx a a : 'M[C]_(2 ^ bb84_n P)) *t (delta_mx b b : 'M[C]_(2 ^ bb84_n P)))) = G (B b b *: ((delta_mx a a : 'M[C]_(2 ^ bb84_n P)) *t (delta_mx b b : 'M[C]_(2 ^ bb84_n P)))).
  { rewrite /F /G /BobZ /dim_BqZp /e_src /e_tgt.
    by rewrite (@bb84_bob_z_basis_readout_unit P dim_Zk_key dim_Bq_key dim_Zp_key (B b b) a a b b) eqxx. } rewrite Hdiag [X in _ + X = _]big1; last first.
  { move=> b' Hb'b; have Hbb' : (b == b') = false.
    { have Hb_ne : b != b' by rewrite eq_sym. exact: negbTE Hb_ne. } rewrite /F /BobZ /dim_BqZp /e_src.
    by rewrite (@bb84_bob_z_basis_readout_unit P dim_Zk_key dim_Bq_key dim_Zp_key (B b b') a a b b') Hbb'. } by rewrite addr0. Qed.

Fact bb84_bob_z_basis_readout_rho_ZC
    (P : bb84_protocol) (Gsrc : bb84_zsource P)
    (dim_Zk_key : (2 ^ bb84_n P)%N = dim ('H[HL]_Zkey))
    (dim_Bq_key : (2 ^ bb84_n P)%N = dim ('H[HL]_Bq))
    (dim_Zp_key : (2 ^ bb84_n P)%N = dim ('H[HL]_Zp))
    (rho : 'M[C]_((2 ^ bb84_n P) * bb84_zsrc_nb Gsrc *
                  (2 ^ bb84_n P))) :
  let dimZBq := bb84_register_pair_dim disZBq dim_Zk_key dim_Bq_key in
  let dim_BqZp := etrans (esym dim_Bq_key) dim_Zp_key in
  biprod_mx disZZp
    (((\:1 : 'SO[HL]_Zkey) :⊗
      (bob_z_basis_qchannel (bob_z_canonical_readout dim_BqZp)
        : 'SO[HL]_(Bq, Zp)))
      (eur_rho_ZC disZBq rho
        (@std_projective_povm R (2 ^ bb84_n P)) dimZBq)) =
  castmx (f_equal2 muln dim_Zk_key dim_Zp_key,
          f_equal2 muln dim_Zk_key dim_Zp_key)
    (@bb84_holdout_measure_ZZ R P Gsrc rho).
Proof.
  rewrite /=; set dimZBq := bb84_register_pair_dim disZBq dim_Zk_key dim_Bq_key.
  set dim_BqZp := etrans (esym dim_Bq_key) dim_Zp_key.
  set BobZ := bob_z_basis_qchannel (bob_z_canonical_readout dim_BqZp).
  set e_src := f_equal2 muln dim_Zk_key dim_Bq_key; set e_tgt := f_equal2 muln dim_Zk_key dim_Zp_key.
  set F := fun M : 'M[C]_((2 ^ bb84_n P) * (2 ^ bb84_n P)) => biprod_mx disZZp (((\:1 : 'SO[HL]_Zkey) :⊗ (BobZ : 'SO[HL]_(Bq, Zp))) (biprod_of_mx disZBq (castmx (e_src, e_src) M))).
  set G := fun M : 'M[C]_((2 ^ bb84_n P) * (2 ^ bb84_n P)) => castmx (e_tgt, e_tgt) M.
  have Hcast_addD : forall (m n : nat) (e : m = n) (A0 B0 : 'M[C]_m), castmx (e, e) (A0 + B0) = castmx (e, e) A0 + castmx (e, e) B0 by move=> m n e A0 B0; case: n / e; rewrite !castmx_id.
  have Hcast_0 : forall (m n : nat) (e : m = n), castmx (e, e) (0 : 'M[C]_m) = 0 by move=> m n e; case: n / e; rewrite castmx_id.
  have Hbiprod_of_mx_sum_src (I : finType) (p : pred I) (A0 : I -> 'M[C]_(dim 'H[HL]_Zkey * dim 'H[HL]_Bq)) : @biprod_of_mx R L HL Zkey Bq disZBq (\sum_(i | p i) A0 i) = \sum_(i | p i) @biprod_of_mx R L HL Zkey Bq disZBq (A0 i) by exact: biprod_of_mx_sum.
  have Hso_sum (I : finType) (p : pred I) (x : I -> 'F[HL]_(Zkey :|: Bq)) : ((\:1 : 'SO[HL]_Zkey) :⊗ (BobZ : 'SO[HL]_(Bq, Zp))) (\sum_(i | p i) x i) = \sum_(i | p i) ((\:1 : 'SO[HL]_Zkey) :⊗ (BobZ : 'SO[HL]_(Bq, Zp))) (x i) by exact: linear_sum.
  have Hbiprod_mx_D (x y : 'F[HL]_(Zkey :|: Zp)) : @biprod_mx R L HL Zkey Zp disZZp (x + y) = @biprod_mx R L HL Zkey Zp disZZp x + @biprod_mx R L HL Zkey Zp disZZp y by rewrite /biprod_mx raddfD /= raddfD mulmxDr mulmxDl.
  have Hbiprod_mx_0 : @biprod_mx R L HL Zkey Zp disZZp 0 = 0 by rewrite /biprod_mx h2mx0 linear0 mulmx0 mul0mx.
  have Hbiprod_mx_sum (I : finType) (p : pred I) (x : I -> 'F[HL]_(Zkey :|: Zp)) : @biprod_mx R L HL Zkey Zp disZZp (\sum_(i | p i) x i) = \sum_(i | p i) @biprod_mx R L HL Zkey Zp disZZp (x i) by exact: (big_morph _ Hbiprod_mx_D Hbiprod_mx_0).
  have HF_sum (I : finType) (p : pred I) (A0 : I -> 'M[C]_((2 ^ bb84_n P) * (2 ^ bb84_n P))) : F (\sum_(i | p i) A0 i) = \sum_(i | p i) F (A0 i).
  { rewrite /F (big_morph (fun M => castmx (e_src, e_src) M) (fun A1 B1 => Hcast_addD _ _ e_src A1 B1) (Hcast_0 _ _ e_src)).
    by rewrite Hbiprod_of_mx_sum_src Hso_sum Hbiprod_mx_sum. } have HG_sum (I : finType) (p : pred I) (A0 : I -> 'M[C]_((2 ^ bb84_n P) * (2 ^ bb84_n P))) : G (\sum_(i | p i) A0 i) = \sum_(i | p i) G (A0 i).
  { rewrite /G; exact: (big_morph (fun M => castmx (e_tgt, e_tgt) M) (fun A1 B1 => Hcast_addD _ _ e_tgt A1 B1) (Hcast_0 _ _ e_tgt)). } have HrhoZB : eur_rho_ZC disZBq rho (@std_projective_povm R (2 ^ bb84_n P)) dimZBq = biprod_of_mx disZBq (castmx (e_src, e_src) (rho_ZC (@std_projective_povm R (2 ^ bb84_n P)) rho)).
  { apply: (@biprod_mx_inj R L HL Zkey Bq disZBq); rewrite biprod_mxK.
    exact: (eur_rho_ZC_biprod_mx disZBq rho (@std_projective_povm R (2 ^ bb84_n P)) dimZBq dim_Zk_key dim_Bq_key). } rewrite HrhoZB.
  change (F (rho_ZC (@std_projective_povm R (2 ^ bb84_n P)) rho) = G (@bb84_holdout_measure_ZZ R P Gsrc rho)).
  rewrite /rho_ZC /std_projective_povm HF_sum [X in G X](@bb84_holdout_measure_ZZ_rho_ZC R P Gsrc rho) [RHS]HG_sum.
  apply: eq_bigr => z _; rewrite sqrtmx_delta_mx_ii; set Bz := ptrace1 _.
  have Hblock : F ((delta_mx z z : 'M[C]_(2 ^ bb84_n P)) *t Bz) = G (\sum_(b : 'I_(2 ^ bb84_n P)) Bz b b *: ((delta_mx z z : 'M[C]_(2 ^ bb84_n P)) *t (delta_mx b b : 'M[C]_(2 ^ bb84_n P)))).
  { rewrite /F /G /BobZ /dim_BqZp /e_src /e_tgt; exact: (@bb84_bob_z_basis_readout_block P dim_Zk_key dim_Bq_key dim_Zp_key z Bz). } rewrite Hblock; congr G; apply: eq_bigr => b _; congr (_ *: _).
  by rewrite bb84_pair_projector_diag_trace (@rho_ZC_std_projective_diag_mx R (2 ^ bb84_n P) (bb84_zsrc_nb Gsrc) z b rho). Qed.

Fact bb84_delayed_measurement_of_zsource
    (P : bb84_protocol) (Gsrc : bb84_zsource P)
    (Hpass_pos : 0 < bb84_p_pass_tot Gsrc)
    (dim_Zk_key : (2 ^ bb84_n P)%N = dim ('H[HL]_Zkey))
    (dim_Bq_key : (2 ^ bb84_n P)%N = dim ('H[HL]_Bq))
    (dim_Zp_key : (2 ^ bb84_n P)%N = dim ('H[HL]_Zp)) :
  let dimZBq := bb84_register_pair_dim disZBq dim_Zk_key dim_Bq_key in
  let dim_BqZp := etrans (esym dim_Bq_key) dim_Zp_key in
  bb84_delayed_measurement_condition
    (bob_z_basis_qchannel (bob_z_canonical_readout dim_BqZp))
    (eur_rho_ZC disZBq (bb84_cond_rho Gsrc)
      (@std_projective_povm R (2 ^ bb84_n P)) dimZBq)
    (@bb84_rhoZZ_pass_mixH R L HL Zkey Zp disZZp
      P Gsrc dim_Zk_key dim_Zp_key).
Proof.
  rewrite /=; set dimZBq := bb84_register_pair_dim disZBq dim_Zk_key dim_Bq_key.
  set dim_BqZp := etrans (esym dim_Bq_key) dim_Zp_key.
  set BobZ := bob_z_basis_qchannel (bob_z_canonical_readout dim_BqZp).
  set rhoZB := eur_rho_ZC disZBq (bb84_cond_rho Gsrc) (@std_projective_povm R (2 ^ bb84_n P)) dimZBq.
  set rhoZZp := @bb84_rhoZZ_pass_mixH R L HL Zkey Zp disZZp P Gsrc dim_Zk_key dim_Zp_key.
  set full := rhoZB \O (\1 : 'F[HL]_finset.set0).
  have Hfull_den1 : full \is den1lf.
  { apply: sdot_unit0_den1lf.
    exact: (eur_rho_ZC_den1 disZBq dimZBq (@std_projective_povm_is_povm R (2 ^ bb84_n P)) (bb84_cond_rho_den1 Hpass_pos)). } have Hsource : ptrace_cast3C (disjointX0 Zkey) (disjointX0 Bq) full = rhoZB by exact: ptrace_cast3C_sdot_unit0.
  have Htarget : ptrace_cast3C (disjointX0 Zkey) (disjointX0 Zp) ((((\:1 : 'SO[HL]_Zkey) :⊗ (BobZ : 'SO[HL]_(Bq, Zp))) :⊗ (\:1 : 'SO[HL]_finset.set0)) full) = rhoZZp.
  { rewrite /full (tenso_sdot_correct (disjointX0 (Zkey :|: Bq)) (disjointX0 (Zkey :|: Zp)) ((\:1 : 'SO[HL]_Zkey) :⊗ (BobZ : 'SO[HL]_(Bq, Zp))) (\:1 : 'SO[HL]_finset.set0) rhoZB (\1 : 'F[HL]_finset.set0)).
    rewrite id_soE ptrace_cast3C_sdot_unit0.
    apply: (@biprod_mx_inj R L HL Zkey Zp disZZp); rewrite biprod_mxK /rhoZZp /rhoZB /BobZ /dim_BqZp.
    rewrite (@bb84_bob_z_basis_readout_rho_ZC P Gsrc dim_Zk_key dim_Bq_key dim_Zp_key (bb84_cond_rho Gsrc)).
    by rewrite bb84_cond_rho_born_consistency. } exact: (BB84DelayedMeasurementCondition Hfull_den1 Hsource Htarget). Qed.

Fact bb84_delayed_measurement_hmax (eps0 : R)
    (BobZ : 'QC[HL]_(Bq, Zp))
    (rhoZB : 'F[HL]_(Zkey :|: Bq))
    (rhoZZp : 'F[HL]_(Zkey :|: Zp)) :
  0 <= eps0 -> eps0 < Num.sqrt (@complex.Re R (\Tr rhoZB)) ->
  bb84_delayed_measurement_condition BobZ rhoZB rhoZZp ->
  smooth_hmax Bq eps0 rhoZB <= smooth_hmax Zp eps0 rhoZZp.
Proof.
  move=> Heps0 Heps0_lt Hdelay.
  set rhoFull := bb84_dmc_full Hdelay.
  have HrhoFull_den1 := bb84_dmc_full_den1 Hdelay.
  have HrhoZB_den1 := bb84_dmc_source_den1 Hdelay; have HrhoZZp_den1 := bb84_dmc_target_den1 Hdelay.
  have Hsource := bb84_dmc_source Hdelay; have Htarget := bb84_dmc_target Hdelay.
  have HrhoFull_den : rhoFull \is denlf := den1lf_den HrhoFull_den1.

  have [_ Hmax] := @entropy_data_proc R L HL Zkey Bq finset.set0 Zkey Zp finset.set0 disZBq (disjointX0 Zkey) (disjointX0 Bq) disZZp (disjointX0 Zkey) (disjointX0 Zp) disZBq AuxApp AuxBpp disZ_AuxApp disZp_AuxBpp disZ_AuxBpp disAuxApp_Zp disAuxApp_AuxBpp dimAuxApp_enough dimAuxBpp_enough AuxCiso AuxCp_src AuxCpp_src AuxCp_tgt AuxCpp_tgt disZ_AuxCiso disBq_AuxCiso disZApp_AuxCiso disZpBpp_AuxCiso dimZBq_AuxCiso dimZAppBBpp_AuxCiso disZ_AuxCp_src disZ_AuxCpp_src disBq_AuxCp_src disBq_AuxCpp_src disAuxCp_AuxCpp_src dimZ_AuxCp_src dimAuxCisoCp_AuxCpp_src dimBq_AuxCpp_src disZApp_AuxCp_tgt disZApp_AuxCpp_tgt disZpBpp_AuxCp_tgt disZpBpp_AuxCpp_tgt disAuxCp_AuxCpp_tgt dimZApp_AuxCp_tgt dimAuxCisoCp_AuxCpp_tgt dimZpBpp_AuxCpp_tgt eps0 rhoFull (\:1 : 'SO[HL]_(Zkey, Zkey)) (BobZ : 'SO[HL]_(Bq, Zp)) (\:1 : 'SO[HL]_(finset.set0, finset.set0)) HrhoFull_den Heps0.
  have Hmax_step := Hmax (idso_qc 'H[HL]_Zkey) (ltac:(by rewrite dualso1 is_tnmap)) (is_cptp (BobZ : 'QC[HL]_(Bq, Zp))) (idso_qc 'H[HL]_finset.set0).
  rewrite Hsource in Hmax_step; have Hmax_ineq := Hmax_step Heps0_lt.

  rewrite /dpi.entropy_data_proc_tau /dpi.entropy_data_proc_map Htarget in Hmax_ineq.

  have HrhoZB_psd : rhoZB \is psdlf := den1lf_psd HrhoZB_den1.
  have HrhoZZp_psd : rhoZZp \is psdlf := den1lf_psd HrhoZZp_den1.
  have HrhoZB_trC : \Tr rhoZB = 1 := den1lf_trlf HrhoZB_den1.
  have HrhoZZp_trC : \Tr rhoZZp = 1 := den1lf_trlf HrhoZZp_den1.
  have HrhoZB_tr1 : @complex.Re R (\Tr rhoZB) = 1 by rewrite HrhoZB_trC /=.
  have HrhoZZp_tr1 : @complex.Re R (\Tr rhoZZp) = 1 by rewrite HrhoZZp_trC /=.
  have HrhoZB_tr : @complex.Re R (\Tr rhoZB) <= 1 by rewrite HrhoZB_tr1.
  have HrhoZZp_tr : @complex.Re R (\Tr rhoZZp) <= 1 by rewrite HrhoZZp_tr1.
  have Heps_pair_src : 0 <= eps0 < Num.sqrt (@complex.Re R (\Tr rhoZB)) by rewrite Heps0 Heps0_lt.
  have HsrcE := @smooth_hmaxE_EFin R L HL (Zkey :|: Bq) Bq eps0 rhoZB HrhoZB_psd HrhoZB_tr Heps_pair_src.
  have Heps0_lt_tgt : eps0 < Num.sqrt (@complex.Re R (\Tr rhoZZp)) by rewrite HrhoZZp_tr1 sqrtr1 HrhoZB_tr1 sqrtr1 in Heps0_lt *.
  have Heps_pair_tgt : 0 <= eps0 < Num.sqrt (@complex.Re R (\Tr rhoZZp)) by rewrite Heps0 Heps0_lt_tgt.
  have HtgtE := @smooth_hmaxE_EFin R L HL (Zkey :|: Zp) Zp eps0 rhoZZp HrhoZZp_psd HrhoZZp_tr Heps_pair_tgt.
  rewrite HsrcE HtgtE lee_fin in Hmax_ineq; exact: Hmax_ineq. Qed.

Fact bb84_public_deterministic_state_right
    (Ppub : {set L})
    (disPSE : [disjoint Ppub & (S :|: E)])
    (p : 'Idx[HL]_Ppub)
    (rhoXE : 'F[HL]_(S :|: E)) :
  let eq_pub_assoc := bb84_public_assoc S E Ppub in
  castlf (eq_pub_assoc, eq_pub_assoc)
    ([> deltav p ; deltav p <] \O rhoXE) =
  castlf (esym (finset.setUA S E Ppub),
          esym (finset.setUA S E Ppub))
    (rhoXE \O [> deltav p ; deltav p <]).
Proof. move=> /=; apply: to_Fnd_inj; rewrite !Fnd_cast !to_Fnd_sdotE. by rewrite (@dotFC R L HL (to_Fnd [> deltav p; deltav p <]) (to_Fnd rhoXE)) ?disPSE ?disjoint_sym. Qed.

Fact bb84_public_right_append_cq
    (Ppub : {set L})
    (disSP : [disjoint S & Ppub])
    (disEP : [disjoint E & Ppub])
    (p : 'Idx[HL]_Ppub)
    (rhoXE : 'F[HL]_(S :|: E)) :
  @is_cq_state R L HL S E rhoXE -> @is_cq_state R L HL S (E :|: Ppub)
    (castlf (esym (finset.setUA S E Ppub),
             esym (finset.setUA S E Ppub))
      (rhoXE \O [> deltav p ; deltav p <])).
Proof.
  move=> Hcq; rewrite /is_cq_state; apply/forallP => x; apply/forallP => x'.
  apply/implyP => Hx'x; apply/eqP; move: Hcq; rewrite /is_cq_state => /forallP Hcq.
  have Hold : (([> deltav x ; deltav x <] \O (\1 : 'F[HL]_E)) \o rhoXE \o ([> deltav x' ; deltav x' <] \O (\1 : 'F[HL]_E))) = 0.
  { move: (Hcq x) => /forallP /(_ x') /implyP Hblock; by move/eqP: (Hblock Hx'x). } set eqSEP := esym (finset.setUA S E Ppub); set KP := [> deltav p ; deltav p <].
  set KxE := ([> deltav x ; deltav x <] \O (\1 : 'F[HL]_E) : 'F[HL]_(S :|: E)).
  set Kx'E := ([> deltav x' ; deltav x' <] \O (\1 : 'F[HL]_E) : 'F[HL]_(S :|: E)).
  have disSE_P : [disjoint S :|: E & Ppub]. { by rewrite disjointUX disSP disEP. } have HIEP : (\1 : 'F[HL]_(E :|: Ppub)) = (\1 : 'F[HL]_E) \O (\1 : 'F[HL]_Ppub) by rewrite sdotf11.
  have Hleft : ([> deltav x ; deltav x <] \O (\1 : 'F[HL]_(E :|: Ppub)) : 'F[HL]_(S :|: (E :|: Ppub))) = castlf (eqSEP, eqSEP) (KxE \O (\1 : 'F[HL]_Ppub)) by apply: to_Fnd_inj; rewrite /KxE HIEP Fnd_cast !to_Fnd_sdotE -dotFsA.
  have Hright : ([> deltav x' ; deltav x' <] \O (\1 : 'F[HL]_(E :|: Ppub)) : 'F[HL]_(S :|: (E :|: Ppub))) = castlf (eqSEP, eqSEP) (Kx'E \O (\1 : 'F[HL]_Ppub)) by apply: to_Fnd_inj; rewrite /Kx'E HIEP Fnd_cast !to_Fnd_sdotE -dotFsA.
  rewrite Hleft Hright -!(castlf_complf eqSEP eqSEP eqSEP); apply/eqP; rewrite castlf_eq0; apply/eqP.
  have Hten_l : (KxE \O (\1 : 'F[HL]_Ppub) : 'F[HL]_(S :|: E :|: Ppub)) = KxE \⊗ (\1 : 'F[HL]_Ppub).
  { by apply: to_Fnd_inj; rewrite (sdotFT _ _ disSE_P) to_Fnd_tenE. } have Hten_m : (rhoXE \O KP : 'F[HL]_(S :|: E :|: Ppub)) = rhoXE \⊗ KP.
  { by apply: to_Fnd_inj; rewrite (sdotFT _ _ disSE_P) to_Fnd_tenE. } have Hten_r : (Kx'E \O (\1 : 'F[HL]_Ppub) : 'F[HL]_(S :|: E :|: Ppub)) = Kx'E \⊗ (\1 : 'F[HL]_Ppub).
  { by apply: to_Fnd_inj; rewrite (sdotFT _ _ disSE_P) to_Fnd_tenE. } rewrite Hten_l Hten_m Hten_r -tenf_comp // comp_lfun1l -tenf_comp // comp_lfun1r.
  by rewrite /KxE /Kx'E in Hold; rewrite Hold ten0f. Qed.

Fact bb84_public_leakage_deterministic
    (Ppub : {set L})
    (disSP : [disjoint S & Ppub])
    (disEP : [disjoint E & Ppub])
    (disPSE : [disjoint Ppub & (S :|: E)])
    (p : 'Idx[HL]_Ppub)
    (rhoXE : 'F[HL]_(S :|: E)) (leak : R) :
  rhoXE \is psdlf -> @complex.Re R (\Tr rhoXE) <= 1 -> @is_cq_state R L HL S E rhoXE ->
  log2 (dim 'H[HL]_Ppub)%:R <= leak -> bb84_public_leakage Ppub rhoXE leak.
Proof.
  move=> Hrho Htr Hcq Hleak.
  pose rhoPSE : 'F[HL]_(Ppub :|: (S :|: E)) := [> deltav p ; deltav p <] \O rhoXE.
  refine ({| bb84_public_disSP := disSP; bb84_public_disEP := disEP; bb84_public_disP_SE := disPSE; bb84_public_state := rhoPSE; bb84_public_leak_bound := Hleak |}).
  - rewrite /rhoPSE.
    have Hproj_psd : [> deltav p ; deltav p <] \is psdlf := outp_psd _.
    have Hten : ([> deltav p ; deltav p <] \O rhoXE : 'F[HL]_(Ppub :|: (S :|: E))) = [> deltav p ; deltav p <] \⊗ rhoXE by apply: to_Fnd_inj; rewrite (sdotFT _ _ disPSE) to_Fnd_tenE.
    rewrite Hten psdlfE; apply: tenf_ge0; first exact: disPSE.
    1,2: by rewrite -psdlfE.
  - rewrite /rhoPSE (lftrace_sdot_disj _ _ disPSE) outp_trlf dv_dot eqxx mul1r; exact: Htr.
  - move=> x x' Hneq; rewrite /rhoPSE.
    have Hleft : (([> deltav x ; deltav x <] \O (\1 : 'F_(S :|: E))) : 'F[HL]_(Ppub :|: (S :|: E))) = [> deltav x ; deltav x <] \⊗ (\1 : 'F_(S :|: E)) by apply: to_Fnd_inj; rewrite (sdotFT _ _ disPSE) to_Fnd_tenE.
    have Hmid : ([> deltav p ; deltav p <] \O rhoXE : 'F[HL]_(Ppub :|: (S :|: E))) = [> deltav p ; deltav p <] \⊗ rhoXE by apply: to_Fnd_inj; rewrite (sdotFT _ _ disPSE) to_Fnd_tenE.
    have Hright : (([> deltav x' ; deltav x' <] \O (\1 : 'F_(S :|: E))) : 'F[HL]_(Ppub :|: (S :|: E))) = [> deltav x' ; deltav x' <] \⊗ (\1 : 'F_(S :|: E)) by apply: to_Fnd_inj; rewrite (sdotFT _ _ disPSE) to_Fnd_tenE.
    rewrite Hleft Hmid Hright.
    case: (eqVneq x p) => [Hxp | Hxp].
    + rewrite Hxp; move: Hneq; rewrite Hxp => Hneqp.
      have Hpx' : p != x'. { by rewrite eq_sym. } rewrite -tenf_comp // comp_lfun1l outp_comp dv_dot eqxx scale1r.
      rewrite -tenf_comp // comp_lfun1r outp_comp dv_dot.
      by rewrite ?(negbTE Hneqp) ?(negbTE Hpx') /= scale0r ten0f.
    + have Hpx : p != x by rewrite eq_sym.
      rewrite -tenf_comp // comp_lfun1l outp_comp dv_dot.
      by rewrite ?(negbTE Hxp) ?(negbTE Hpx) /= scale0r ten0f comp_lfun0l.
  - by rewrite /rhoPSE ptrace_castl_sdot_trace_l outp_trlf dv_dot eqxx scale1r.
  - rewrite /rhoPSE (@bb84_public_deterministic_state_right Ppub disPSE p rhoXE).
    exact: (@bb84_public_right_append_cq Ppub disSP disEP p rhoXE Hcq). Defined.

Fact bb84_public_leakage_hminE
    (Ppub : {set L}) (rhoXE : 'F[HL]_(S :|: E)) (leak eps' : R)
    (pub : bb84_public_leakage Ppub rhoXE leak) :
  0 <= eps' < Num.sqrt (@complex.Re R (\Tr (bb84_public_state pub))) ->
  (smooth_hminE E eps' rhoXE - leak%:E <=
    smooth_hminE (E :|: Ppub) eps' (bb84_public_state pub))%E.
Proof. case: pub => disSP disEP disPSE rhoPSE Hrho Htr Hclass Hmarg Hpa_cq Hleak /= Heps. rewrite -Hmarg. exact: (@chain_rule_class_leak_bound R L HL S E disSE Ppub disSP disEP disPSE eps' leak rhoPSE Hrho Htr Hclass Heps Hleak). Qed.

Fact bb84_public_leakage_pa_hminE
    (Ppub : {set L}) (rhoXE : 'F[HL]_(S :|: E)) (leak eps' : R)
    (pub : bb84_public_leakage Ppub rhoXE leak) :
  0 <= eps' < Num.sqrt (@complex.Re R (\Tr (bb84_public_state pub))) ->
  let eq_pub_assoc := bb84_public_assoc S E Ppub in
  (smooth_hminE E eps' rhoXE - leak%:E <=
    smooth_hminE (E :|: Ppub) eps'
      (castlf (eq_pub_assoc, eq_pub_assoc) (bb84_public_state pub)))%E.
Proof.
  move=> Heps /=; set eq_pub_assoc := bb84_public_assoc S E Ppub.
  have Hcast : smooth_hminE (E :|: Ppub) eps' (castlf (eq_pub_assoc, eq_pub_assoc) (bb84_public_state pub)) = smooth_hminE (E :|: Ppub) eps' (bb84_public_state pub).
  { move: (bb84_public_state pub); case: _ / eq_pub_assoc. by move=> rho; rewrite castlf_id. } rewrite Hcast; exact: bb84_public_leakage_hminE. Qed.

Fact bb84_public_leakage_pa_hmin
    (Ppub : {set L}) (rhoXE : 'F[HL]_(S :|: E)) (leak eps' : R)
    (pub : bb84_public_leakage Ppub rhoXE leak) :
  0 <= eps' < Num.sqrt (@complex.Re R (\Tr (bb84_public_state pub))) ->
  let eq_pub_assoc := bb84_public_assoc S E Ppub in
  (smooth_hmin E eps' rhoXE - leak <=
    smooth_hmin (E :|: Ppub) eps'
      (castlf (eq_pub_assoc, eq_pub_assoc) (bb84_public_state pub)))%R.
Proof.
  move=> Heps /=; set eq_pub_assoc := bb84_public_assoc S E Ppub.
  pose disPSE := bb84_public_disP_SE pub; pose rhoPSE := bb84_public_state pub.
  have Hmarg : ptrace_castl disPSE rhoPSE = rhoXE := bb84_public_state_marginal pub.
  pose rhoSEP : 'F[HL]_(S :|: (E :|: Ppub)) := castlf (eq_pub_assoc, eq_pub_assoc) rhoPSE.
  have HrhoXE_psd : rhoXE \is psdlf by rewrite -Hmarg; exact: (ptrace_castl_psdlf disPSE (bb84_public_state_psd pub)).
  have HrhoXE_tr : @complex.Re R (\Tr rhoXE) <= 1 by rewrite -Hmarg trlf_ptrace_castl; exact: bb84_public_state_tr.
  have HtrXE : \Tr rhoXE = \Tr rhoPSE by rewrite -Hmarg; exact: trlf_ptrace_castl.
  have HepsXE : 0 <= eps' < Num.sqrt (@complex.Re R (\Tr rhoXE)) by rewrite HtrXE.
  have disS_Epub : [disjoint S & E :|: Ppub]. { by rewrite disjointXU disSE (bb84_public_disSP pub). } have HrhoSEP_psd : rhoSEP \is psdlf. { rewrite /rhoSEP castlf_psdlfE. exact: bb84_public_state_psd. } have HrhoSEP_tr : @complex.Re R (\Tr rhoSEP) <= 1 by rewrite /rhoSEP castlf_trlfE; exact: bb84_public_state_tr.
  have HepsSEP : 0 <= eps' < Num.sqrt (@complex.Re R (\Tr rhoSEP)) by rewrite /rhoSEP castlf_trlfE.
  have Hsrc_fin : smooth_hminE E eps' rhoXE = (smooth_hmin E eps' rhoXE)%:E := @smooth_hminE_EFin R L HL S E disSE eps' rhoXE HrhoXE_psd HrhoXE_tr HepsXE.
  have Htgt_fin : smooth_hminE (E :|: Ppub) eps' rhoSEP = (smooth_hmin (E :|: Ppub) eps' rhoSEP)%:E := @smooth_hminE_EFin R L HL S (E :|: Ppub) disS_Epub eps' rhoSEP HrhoSEP_psd HrhoSEP_tr HepsSEP.
  have HchainE := @bb84_public_leakage_pa_hminE Ppub rhoXE leak eps' pub Heps.
  have Hchain : (smooth_hminE E eps' rhoXE - leak%:E <= smooth_hminE (E :|: Ppub) eps' rhoSEP)%E by rewrite /rhoSEP /rhoPSE; exact: HchainE.
  by move: Hchain; rewrite Hsrc_fin Htgt_fin -EFinD lee_fin. Qed.

Fact bb84_public_leakage_pa_hmin_diff
    (Ppub : {set L}) (rhoXE : 'F[HL]_(S :|: E))
    (leak eps' base tail logZ : R)
    (pub : bb84_public_leakage Ppub rhoXE leak) :
  0 <= eps' < Num.sqrt (@complex.Re R (\Tr (bb84_public_state pub))) -> base <= smooth_hmin E eps' rhoXE ->
  logZ <= base + tail - leak -> let eq_pub_assoc := bb84_public_assoc S E Ppub in
  logZ - smooth_hmin (E :|: Ppub) eps'
      (castlf (eq_pub_assoc, eq_pub_assoc) (bb84_public_state pub)) <= tail.
Proof.
  move=> Heps Hbase Hlen /=; set eq_pub_assoc := bb84_public_assoc S E Ppub.
  pose rhoSEP : 'F[HL]_(S :|: (E :|: Ppub)) := castlf (eq_pub_assoc, eq_pub_assoc) (bb84_public_state pub).
  have Hpub := @bb84_public_leakage_pa_hmin Ppub rhoXE leak eps' pub Heps.
  change (logZ - smooth_hmin (E :|: Ppub) eps' rhoSEP <= tail).
  have Hbase_le_pub : base - leak <= smooth_hmin (E :|: Ppub) eps' rhoSEP by apply: le_trans Hpub; rewrite lerD2r.
  have Hlog_le_pub_tail : logZ <= smooth_hmin (E :|: Ppub) eps' rhoSEP + tail.
  { apply: (le_trans Hlen).
    have Hrearr : base + tail - leak = base - leak + tail. { by rewrite -addrA [tail + - leak]addrC addrA. } by rewrite Hrearr lerD2r. } set pubH := smooth_hmin (E :|: Ppub) eps' rhoSEP in Hlog_le_pub_tail *.
  by move: Hlog_le_pub_tail; rewrite addrC -lerBlDr. Qed.

Local Lemma bb84_eps_secret_contract (A B : {set L})
    (rhoAB : 'F[HL]_(A :|: B)) (eps eps' ebar eps_s p_abort : R) :
  delta_secret rhoAB (eps' + ebar) -> 0 < ebar -> 0 <= 1 - p_abort -> 1 - p_abort <= 1 ->
  (1 - p_abort) * eps' <= eps -> eps + ebar <= eps_s -> eps_secret rhoAB eps_s p_abort.
Proof. move=> Hsafe ebar_pos Hscale_nonneg Hscale_le1 Heps_contract Hbudget. exists (eps' + ebar); split=> //. have Htmp := ler_pM Hscale_nonneg (ltW ebar_pos) Hscale_le1 (lexx ebar). rewrite mul1r in Htmp. by apply: (le_trans _ Hbudget); rewrite mulrDr; exact: lerD Heps_contract Htmp. Qed.

Fact bb84_delta_from_hmin_diff
    (Epub : {set L})
    (disSEpub : [disjoint S & Epub])
    (disEpubF : [disjoint Epub & Fl])
    (disEpubZl : [disjoint Epub & Zl])
    (disZl_FEpub : [disjoint Zl & (Fl :|: Epub)])
    (Fh : 'Idx[HL]_Fl -> 'Idx[HL]_S -> 'Idx[HL]_Zl)
    (eps' ebar : R)
    (rhoXEpub : 'F[HL]_(S :|: Epub)) :
  rhoXEpub \is psdlf -> @complex.Re R (\Tr rhoXEpub) <= 1 -> @is_cq_state R L HL S Epub rhoXEpub ->
  @two_univ R _ _ _ Fh -> 0 <= eps' -> 0 < ebar -> log2 (dim 'H[HL]_Zl)%:R - smooth_hmin Epub eps' rhoXEpub <=
    2%:R * log2 (2%:R * ebar) -> delta_secret (post_hash_state disSEpub Fh rhoXEpub) (eps' + ebar).
Proof.
  move=> Hrho Htr Hcq HFh Heps'_nn ebar_pos Hhmin_diff.
  have H2ebar_pos : 0 < 2%:R * ebar :> R by rewrite mulr_gt0 // ltr0n.
  have Hlog2_ln : log2 (2%:R * ebar) * ln 2%:R = ln (2%:R * ebar) by rewrite /log2 -mulrA mulVf ?mulr1 //; exact: lt0r_neq0 ln2_gt0.
  have Hexp_log2_2ebar_sq : expR ((2%:R * log2 (2%:R * ebar)) * ln 2%:R) = (2%:R * ebar) ^+ 2.
  { rewrite -mulrA Hlog2_ln.
    have -> : 2%:R * ln (2%:R * ebar) = ln ((2%:R * ebar) ^+ 2) by rewrite lnXn // mulr_natl.
    by apply: lnK; rewrite posrE exprn_gt0. } have Hexp_bound : expR ((log2 (dim 'H[HL]_Zl)%:R - smooth_hmin Epub eps' rhoXEpub) * ln 2%:R) <= (2%:R * ebar) ^+ 2.
  { rewrite -Hexp_log2_2ebar_sq ler_expR. by rewrite ler_pM2r // ln2_gt0. } have Hsqrt_ebar : (2%:R)^-1 * Num.sqrt (expR ((log2 (dim 'H[HL]_Zl)%:R - smooth_hmin Epub eps' rhoXEpub) * ln 2%:R)) <= ebar.
  { have H2ebar_nn : 0 <= 2%:R * ebar by apply: ltW.
    apply: le_trans.
    - by apply: ler_wpM2l; [rewrite invr_ge0 ler0n | apply: ler_wsqrtr Hexp_bound].
    - rewrite sqrtr_sqr ger0_norm // mulrA mulVf; last by rewrite pnatr_eq0.
      by rewrite mul1r. } have Hpa : delta_secret (post_hash_state disSEpub Fh rhoXEpub) (eps' + (2%:R)^-1 * Num.sqrt (expR ((log2 (dim 'H[HL]_Zl)%:R - smooth_hmin Epub eps' rhoXEpub) * ln 2%:R))).
  { rewrite /delta_secret.
    exact: (@privacy_amplification R L HL S Epub disSEpub Fl Zl disSF disSZl disEpubF disEpubZl disFZl Fh eps' rhoXEpub Hrho Htr Hcq HFh Heps'_nn). } rewrite /delta_secret in Hpa *; apply: le_trans Hpa _; by rewrite lerD2l. Qed.

Fact bb84_secret_from_hmin_diff
    (Epub : {set L})
    (disSEpub : [disjoint S & Epub])
    (disEpubF : [disjoint Epub & Fl])
    (disEpubZl : [disjoint Epub & Zl])
    (disZl_FEpub : [disjoint Zl & (Fl :|: Epub)])
    (Fh : 'Idx[HL]_Fl -> 'Idx[HL]_S -> 'Idx[HL]_Zl)
    (eps eps' ebar eps_s p_abort : R)
    (rhoXEpub : 'F[HL]_(S :|: Epub)) :
  rhoXEpub \is psdlf -> @complex.Re R (\Tr rhoXEpub) <= 1 -> @is_cq_state R L HL S Epub rhoXEpub ->
  @two_univ R _ _ _ Fh -> 0 <= eps' -> 0 < ebar -> log2 (dim 'H[HL]_Zl)%:R - smooth_hmin Epub eps' rhoXEpub <=
    2%:R * log2 (2%:R * ebar) -> 0 <= 1 - p_abort -> 1 - p_abort <= 1 -> (1 - p_abort) * eps' <= eps ->
  eps + ebar <= eps_s -> eps_secret (post_hash_state disSEpub Fh rhoXEpub) eps_s p_abort.
Proof.
  move=> Hrho Htr Hcq HFh Heps'_nn ebar_pos Hhmin_diff Hscale_nonneg Hscale_le1 Heps_contract Hbudget.
  exact: (bb84_eps_secret_contract (@bb84_delta_from_hmin_diff Epub disSEpub disEpubF disEpubZl disZl_FEpub Fh eps' ebar rhoXEpub Hrho Htr Hcq HFh Heps'_nn ebar_pos Hhmin_diff) ebar_pos Hscale_nonneg Hscale_le1 Heps_contract Hbudget). Qed.

Lemma bb84_delta_from_public_leakage
    (Ppub : {set L}) (rhoXE : 'F[HL]_(S :|: E))
    (leak eps' ebar base : R)
    (pub : bb84_public_leakage Ppub rhoXE leak)
    (disSEpub : [disjoint S & E :|: Ppub])
    (disEpubF : [disjoint E :|: Ppub & Fl])
    (disEpubZl : [disjoint E :|: Ppub & Zl])
    (disZl_FEpub : [disjoint Zl & (Fl :|: (E :|: Ppub))])
    (Fh : 'Idx[HL]_Fl -> 'Idx[HL]_S -> 'Idx[HL]_Zl) :
  0 <= eps' < Num.sqrt (@complex.Re R (\Tr (bb84_public_state pub))) -> base <= smooth_hmin E eps' rhoXE ->
  log2 (dim 'H[HL]_Zl)%:R <=
    base + 2%:R * log2 (2%:R * ebar) - leak -> @two_univ R _ _ _ Fh -> 0 < ebar ->
  let eq_pub_assoc := bb84_public_assoc S E Ppub in
  delta_secret
    (post_hash_state
      disSEpub Fh
      (castlf (eq_pub_assoc, eq_pub_assoc) (bb84_public_state pub)))
    (eps' + ebar).
Proof.
  move=> Heps Hbase Hlen HFh ebar_pos /=; set eq_pub_assoc := bb84_public_assoc S E Ppub.
  pose rhoSEP : 'F[HL]_(S :|: (E :|: Ppub)) := castlf (eq_pub_assoc, eq_pub_assoc) (bb84_public_state pub).
  have HrhoSEP_psd : rhoSEP \is psdlf by rewrite /rhoSEP castlf_psdlfE; exact: bb84_public_state_psd.
  have HrhoSEP_tr : @complex.Re R (\Tr rhoSEP) <= 1 by rewrite /rhoSEP castlf_trlfE; exact: bb84_public_state_tr.
  have HcqSEP : @is_cq_state R L HL S (E :|: Ppub) rhoSEP by rewrite /rhoSEP; exact: bb84_public_state_pa_cq.
  have Heps'_nn : 0 <= eps' by move/andP: Heps => [Heps'_nn _].
  have Hhmin_diff : log2 (dim 'H[HL]_Zl)%:R - smooth_hmin (E :|: Ppub) eps' rhoSEP <= 2%:R * log2 (2%:R * ebar).
  { rewrite /rhoSEP.
    exact: (@bb84_public_leakage_pa_hmin_diff Ppub rhoXE leak eps' base (2%:R * log2 (2%:R * ebar)) (log2 (dim 'H[HL]_Zl)%:R) pub Heps Hbase Hlen). } exact: (@bb84_delta_from_hmin_diff (E :|: Ppub) disSEpub disEpubF disEpubZl disZl_FEpub Fh eps' ebar rhoSEP HrhoSEP_psd HrhoSEP_tr HcqSEP HFh Heps'_nn ebar_pos Hhmin_diff). Qed.

Fact bb84_secret_from_public_leakage
    (Ppub : {set L}) (rhoXE : 'F[HL]_(S :|: E))
    (leak eps eps' ebar eps_s p_abort base : R)
    (pub : bb84_public_leakage Ppub rhoXE leak)
    (disSEpub : [disjoint S & E :|: Ppub])
    (disEpubF : [disjoint E :|: Ppub & Fl])
    (disEpubZl : [disjoint E :|: Ppub & Zl])
    (disZl_FEpub : [disjoint Zl & (Fl :|: (E :|: Ppub))])
    (Fh : 'Idx[HL]_Fl -> 'Idx[HL]_S -> 'Idx[HL]_Zl) :
  0 <= eps' < Num.sqrt (@complex.Re R (\Tr (bb84_public_state pub))) -> base <= smooth_hmin E eps' rhoXE ->
  log2 (dim 'H[HL]_Zl)%:R <=
    base + 2%:R * log2 (2%:R * ebar) - leak -> @two_univ R _ _ _ Fh -> 0 < ebar -> 0 <= 1 - p_abort ->
  1 - p_abort <= 1 -> (1 - p_abort) * eps' <= eps -> eps + ebar <= eps_s ->
  let eq_pub_assoc := bb84_public_assoc S E Ppub in
  eps_secret
    (post_hash_state
      disSEpub Fh
      (castlf (eq_pub_assoc, eq_pub_assoc) (bb84_public_state pub)))
    eps_s p_abort.
Proof.
  move=> Heps Hbase Hlen HFh ebar_pos Hscale_nonneg Hscale_le1 Heps_contract Hbudget /=.
  exact: (bb84_eps_secret_contract (@bb84_delta_from_public_leakage Ppub rhoXE leak eps' ebar base pub disSEpub disEpubF disEpubZl disZl_FEpub Fh Heps Hbase Hlen HFh ebar_pos) ebar_pos Hscale_nonneg Hscale_le1 Heps_contract Hbudget). Qed.

Theorem bb84_secret (P : bb84_protocol) (q eps_s : R)
    (Gsrc : bb84_zsource P)
    (nx : nat)
    (M : 'I_nx -> 'M[C]_(2 ^ bb84_n P))
    (dim_S : nx = dim ('H[HL]_S))
    (dim_E : bb84_zsrc_nb Gsrc = dim ('H[HL]_E))
    (dim_Zk_key : (2 ^ bb84_n P)%N = dim ('H[HL]_Zkey))
    (dim_Bq_key : (2 ^ bb84_n P)%N = dim ('H[HL]_Bq))
    (dim_Zp_key : (2 ^ bb84_n P)%N = dim ('H[HL]_Zp))
    (p_abort : R)
    (Fh : 'Idx[HL]_Fl -> 'Idx[HL]_S -> 'Idx[HL]_Zl)
    (Fh_2univ : @two_univ R _ _ _ Fh)
    (dim_Zl_ell : dim ('H[HL]_Zl) = (2 ^ bb84_l P)%N)
    (Epub : {set L})
    (pub : bb84_public_leakage Epub
      (eur_rho_XB disSE (bb84_cond_rho Gsrc) M
        (bb84_register_pair_dim disSE dim_S dim_E))
      (bb84_leak_EC P + log2 (2%:R / bb84_eps_c P)))
    (disSEpub : [disjoint S & E :|: Epub])
    (disEpubF : [disjoint E :|: Epub & Fl])
    (disEpubZl : [disjoint E :|: Epub & Zl])
    (disZl_FEpub : [disjoint Zl & (Fl :|: (E :|: Epub))])
    (Hnum : forall eps0 : R, bb84_numeric_side P eps0) :
  (bb84_n P)%:R * q <=
    q_of_mx M (@std_projective_povm R (2 ^ bb84_n P)) -> bb84_pass_prob_le p_abort (bb84_p_pass_tot Gsrc) ->
  is_povm_mx M -> (0 < bb84_n P)%N -> (0 < bb84_k P)%N -> (0 < eps_s) && (eps_s <= 1) -> (bb84_l P)%:R <=
    sup (fun M : R =>
      exists eps ebar : R,
        0 < eps /\ eps < 1 /\ 0 < ebar /\ eps + ebar <= eps_s /\
        M = ((floor (
          (bb84_n P)%:R *
            (q - bb84_h_trunc (bb84_Qtol P +
              bb84_mu (bb84_n P) (bb84_k P) eps)) -
          2%:R * log2 ((2%:R * ebar)^-1) -
          bb84_leak_EC P -
          log2 (2%:R / bb84_eps_c P)))%:~R : R)) -> let eq_pub_assoc := bb84_public_assoc S E Epub in
  eps_secret
    (post_hash_state disSEpub Fh
      (castlf (eq_pub_assoc, eq_pub_assoc) (bb84_public_state pub)))
    eps_s p_abort.
Proof.
  move=> overlap_q Hpass_run M_povm n_pos k_pos /andP [eps_s_pos eps_s_le1] Hlen_sup.
  pose dimSE := bb84_register_pair_dim disSE dim_S dim_E.
  pose dimZBq := bb84_register_pair_dim disZBq dim_Zk_key dim_Bq_key.
  pose rhoSrc := bb84_cond_rho Gsrc.
  pose N := @std_projective_povm R (2 ^ bb84_n P).
  have N_povm : is_povm_mx N := @std_projective_povm_is_povm R _.
  have Hlen_int : (bb84_l P)%:R \is a int_num := @intr_nat R ((bb84_l P)%:R) (@natr_nat R (bb84_l P)).
  have [eps [ebar [eps_pos [_ [ebar_pos [Hbudget Hlen]]]]]] := @bb84_key_length_sup_witness R P q eps_s (bb84_l P)%:R eps_s_pos eps_s_le1 Hlen_int Hlen_sup.
  set p_pass := bb84_p_pass_tot Gsrc.
  case: (ltrP (eps ^+ 2) p_pass) => Hpass_case.
  - have Hdomain : bb84_entropy_domain eps p_pass.
    { split=> //.
      have Heps_sqrt : Num.sqrt (eps ^+ 2) = eps by rewrite sqrtr_sqr ger0_norm // ltW.
      rewrite -Heps_sqrt ltr_sqrt; first exact: Hpass_case.
      exact: lt_trans (exprn_gt0 2 eps_pos) Hpass_case. } pose Hpass_prob := Hpass_run; pose rhoXE := eur_rho_XB disSE rhoSrc M dimSE.
    have p_pass_nn := bb84_p_pass_tot_ge0 Gsrc.
    have p_pass_pos : 0 < p_pass by have [_ Hlt] := Hdomain; rewrite -sqrtr_gt0; exact: lt_trans eps_pos Hlt.
    have rho_den1 : rhoSrc \is den1mx := bb84_cond_rho_den1 p_pass_pos.
    have p_pass_le1 : p_pass <= 1 by rewrite /p_pass; exact: bb84_p_pass_tot_le1.
    have p_abort_ge0 := bb84_pass_prob_le_abort_ge0 Hpass_prob.
    have p_abort_le1 := bb84_pass_prob_le_abort_le1 Hpass_prob.
    have Hpass_abort := bb84_pass_prob_le_bound Hpass_prob.
    have Heps_lt_sqrt_pass := bb84_eps_lt_sqrt_pass Hdomain.
    pose Hnum_eps := Hnum eps.
    have Hleak_nn := bb84_leak_nonneg Hnum_eps.
    have Heps_c_pos := bb84_epsc_pos Hnum_eps.
    have Heps_c_le1 := bb84_epsc_le1 Hnum_eps.
    have Hlen_real : (bb84_l P)%:R <= bb84_key_length_ub (bb84_n P) (bb84_k P) q (bb84_Qtol P) eps ebar (bb84_leak_EC P) (bb84_eps_c P) by exact: (le_trans Hlen (@Rfloor_le R _)).
    set eps' := eps / Num.sqrt p_pass.
    pose rhoZB := eur_rho_ZC disZBq rhoSrc N dimZBq.
    have Hsqrt_p_pass_pos : 0 < Num.sqrt p_pass by rewrite sqrtr_gt0.
    have Heps'_nn : 0 <= eps' by rewrite divr_ge0 // ltW.
    have Heps'_lt1 : eps' < 1. { rewrite /eps' ltr_pdivrMr // mul1r. exact: Heps_lt_sqrt_pass. } have Heps'_range : 0 <= eps' < 1 by rewrite Heps'_nn Heps'_lt1.
    have HtrZB_eq1 : \Tr rhoZB = 1 by rewrite /rhoZB; exact: (eur_rho_ZC_tr1 disZBq dimZBq N_povm rho_den1).
    have HrhoZB_tr1R : @complex.Re R (\Tr rhoZB) = 1 by rewrite HtrZB_eq1 re_realid.
    have Heps'_lt_TrZB : eps' < Num.sqrt (@complex.Re R (\Tr rhoZB)) by rewrite HrhoZB_tr1R sqrtr1.
    have Heps'_lt_sqrt_rhoSrc : eps' < Num.sqrt (@complex.Re R (\tr rhoSrc)).
    { have /den1mxP[_ /eqP Htr1] := rho_den1. by rewrite Htr1 re_realid sqrtr1. } have Hucr : smooth_hmin E eps' rhoXE + smooth_hmax Bq eps' rhoZB >= (bb84_n P)%:R * q.
    { rewrite /rhoXE /rhoZB.
      exact: (@entropic_uncertainty_relation_bb84 R L HL S E Zkey Bq disSE disSZ disSBq disEZ disEBq disZBq (bb84_n P) eps' q (2 ^ bb84_n P) (bb84_zsrc_nb Gsrc) (2 ^ bb84_n P) nx (2 ^ bb84_n P) rhoSrc M N dimSE dimZBq dim_S dim_E dim_Zk_key dim_Bq_key n_pos (den1mx_den rho_den1) Heps'_nn Heps'_lt_sqrt_rhoSrc M_povm N_povm overlap_q). } have HpsiZB : rhoZB \is psdlf by apply: (eur_rho_ZC_psd disZBq dimZBq N_povm rho_den1).
    have HtrZB : @complex.Re R (\Tr rhoZB) <= 1 by rewrite HtrZB_eq1 re_realid lexx.
    pose rhoZZp := @bb84_rhoZZ_pass_mixH R L HL Zkey Zp disZZp P Gsrc dim_Zk_key dim_Zp_key.
    have HrhoZZp_psd : rhoZZp \is psdlf by rewrite /rhoZZp; exact: bb84_rhoZZ_pass_mixH_psd.
    have HstatB : smooth_hmax Bq eps' rhoZB <= (bb84_n P)%:R * bb84_h_trunc (bb84_Qtol P + bb84_mu (bb84_n P) (bb84_k P) eps).
    { have Htransport : smooth_hmax Bq eps' rhoZB <= smooth_hmax Zp eps' rhoZZp.
      { rewrite /rhoZB /rhoZZp; set dim_BqZp := etrans (esym dim_Bq_key) dim_Zp_key.
        pose BobZ := bob_z_basis_qchannel (bob_z_canonical_readout dim_BqZp).
        have Hreadout := @bb84_delayed_measurement_of_zsource P Gsrc p_pass_pos dim_Zk_key dim_Bq_key dim_Zp_key.
        exact: (@bb84_delayed_measurement_hmax eps' BobZ _ _ Heps'_nn Heps'_lt_TrZB Hreadout). } apply: le_trans Htransport _.
      have Hstruct_mix : biprod_mx disZZp rhoZZp = castmx (f_equal2 muln dim_Zk_key dim_Zp_key, f_equal2 muln dim_Zk_key dim_Zp_key) (bb84_rhoZZ_pass_mix Gsrc).
      { by rewrite /rhoZZp; exact: (@bb84_rhoZZ_pass_mixH_biprod R L HL Zkey Zp disZZp P Gsrc dim_Zk_key dim_Zp_key). } exact: (@stat_mix R L HL Zkey Zp disZZp P Gsrc eps rhoZZp dim_Zk_key dim_Zp_key n_pos k_pos eps_pos HrhoZZp_psd p_pass_pos Heps'_lt1 Hstruct_mix). } set h_trunc := bb84_h_trunc (bb84_Qtol P + bb84_mu (bb84_n P) (bb84_k P) eps).
    have Hmin_rhoXE : (bb84_n P)%:R * (q - h_trunc) <= smooth_hmin E eps' rhoXE.
    { have Hcomb : (bb84_n P)%:R * q <= smooth_hmin E eps' rhoXE + (bb84_n P)%:R * h_trunc.
      { by apply: le_trans Hucr _; rewrite lerD2l; exact: HstatB. } by rewrite mulrBr lerBlDr. } have Hlog2_dim : @log2 R ((dim 'H[HL]_Zl)%:R : R) = ((bb84_l P)%:R : R) by rewrite dim_Zl_ell; exact: (@log2_pow2_nat R (bb84_l P)).
    have H2ebar_pos : 0 < 2%:R * ebar :> R by rewrite mulr_gt0 // ltr0n.
    have H2ebar_pos_in : (2%:R * ebar : R) \in Num.pos by rewrite posrE.
    have Hlog2_inv_ebar : log2 ((2%:R * ebar)^-1) = - log2 (2%:R * ebar) by rewrite /log2 lnV // mulNr.
    have Hec_le2 : bb84_eps_c P <= 2%:R :> R by apply: le_trans Heps_c_le1 _; by rewrite ler1n.
    have H2_over_ec_ge1 : 1 <= 2%:R / bb84_eps_c P :> R.
    { rewrite ler_pdivlMr. - by rewrite mul1r. - exact: Heps_c_pos. } have Hlog2_ec_nn : 0 <= log2 (2%:R / bb84_eps_c P) by exact: log2_pos H2_over_ec_ge1.
    have Hlen_rewr : (bb84_l P)%:R <= (bb84_n P)%:R * (q - bb84_h_trunc (bb84_Qtol P + bb84_mu (bb84_n P) (bb84_k P) eps))
      + 2%:R * log2 (2%:R * ebar) - bb84_leak_EC P - log2 (2%:R / bb84_eps_c P) by move: Hlen_real; rewrite /bb84_key_length_ub Hlog2_inv_ebar mulrN opprK.
    set base_h := (bb84_n P)%:R * (q - bb84_h_trunc (bb84_Qtol P + bb84_mu (bb84_n P) (bb84_k P) eps)).
    set public_leak := bb84_leak_EC P + log2 (2%:R / bb84_eps_c P).
    have Hlen_public : log2 (dim 'H[HL]_Zl)%:R <= base_h + 2%:R * log2 (2%:R * ebar) - public_leak.
    { by rewrite Hlog2_dim /base_h /public_leak; apply: le_trans Hlen_rewr _; rewrite opprD addrA. } have HrhoXE_psd : rhoXE \is psdlf by apply: (eur_rho_XB_psd disSE dimSE M_povm rho_den1).
    have HtrXE_eq1 : \Tr rhoXE = 1 by rewrite /rhoXE; exact: (eur_rho_XB_tr1 disSE dimSE M_povm rho_den1).
    have Hmarg_pub : ptrace_castl (bb84_public_disP_SE pub) (bb84_public_state pub) = rhoXE.
    { rewrite /rhoXE. exact: bb84_public_state_marginal. } have Htr_pub_eq : \Tr (bb84_public_state pub) = \Tr rhoXE. { by rewrite -Hmarg_pub trlf_ptrace_castl. } have Heps_pub : 0 <= eps' < Num.sqrt (@complex.Re R (\Tr (bb84_public_state pub))) by rewrite Htr_pub_eq HtrXE_eq1 re_realid sqrtr1 Heps'_nn Heps'_lt1.
    have Hscale_nonneg : 0 <= 1 - p_abort by rewrite subr_ge0.
    have Hscale_le1 : 1 - p_abort <= 1 by rewrite lerBlDr lerDl.
    have Hpass_nonneg : 0 <= p_pass by exact: ltW p_pass_pos.
    have Hsqrt_pass_pos : 0 < Num.sqrt p_pass by rewrite sqrtr_gt0.
    have Hppass_le_sqrt : p_pass <= Num.sqrt p_pass.
    { have Hsq : p_pass ^+ 2 <= p_pass.
      { rewrite -{2}(mul1r p_pass). exact: (ler_pM Hpass_nonneg Hpass_nonneg p_pass_le1 (lexx p_pass)). } have Hsqrt_mono := ler_wsqrtr Hsq.
      have Hsqrt_sq : Num.sqrt (p_pass ^+ 2) = p_pass by rewrite sqrtr_sqr ger0_norm.
      by rewrite Hsqrt_sq in Hsqrt_mono. } have Hsqrt_pass_ge_abort : 1 - p_abort <= Num.sqrt p_pass by exact: le_trans Hpass_abort Hppass_le_sqrt.
    have Heps_nonneg : 0 <= eps by exact: ltW eps_pos.
    have Hebar_nonneg : 0 <= ebar by exact: ltW ebar_pos.
    have Heps_over_nonneg : 0 <= eps / Num.sqrt p_pass by rewrite divr_ge0 ?ltW.
    have Hscale_over_nonneg : 0 <= (1 - p_abort) / Num.sqrt p_pass.
    { apply: mulr_ge0. - exact: Hscale_nonneg. - by rewrite invr_ge0; exact: ltW Hsqrt_pass_pos. } have Hscale_over_le1 : (1 - p_abort) / Num.sqrt p_pass <= 1 by rewrite ler_pdivrMr // mul1r; exact: Hsqrt_pass_ge_abort.
    have Heps_contract : (1 - p_abort) * (eps / Num.sqrt p_pass) <= eps.
    { change ((1 - p_abort) * (eps * (Num.sqrt p_pass)^-1) <= eps); rewrite mulrCA.
      have Htmp : eps * ((1 - p_abort) * (Num.sqrt p_pass)^-1) <= eps * 1.
        exact: (ler_pM Heps_nonneg Hscale_over_nonneg (lexx eps) Hscale_over_le1).
      by rewrite mulr1 in Htmp. } exact: (@bb84_secret_from_public_leakage Epub rhoXE public_leak eps eps' ebar eps_s p_abort base_h pub disSEpub disEpubF disEpubZl disZl_FEpub Fh Heps_pub Hmin_rhoXE Hlen_public Fh_2univ ebar_pos Hscale_nonneg Hscale_le1 Heps_contract Hbudget).
  - have Hnonabort_le_pass : 1 - p_abort <= p_pass := bb84_pass_prob_le_bound Hpass_run.
    have Hpass_le1 : p_pass <= 1 by rewrite /p_pass; exact: bb84_p_pass_tot_le1.
    have Hnonabort_le1 : 1 - p_abort <= 1 := le_trans Hnonabort_le_pass Hpass_le1.
    have Hnonabort_le_eps_s : 1 - p_abort <= eps_s.
    { case: (lerP eps 1) => [Heps_le1 | Hone_lt_eps].
      - have Heps2_le_eps : eps ^+ 2 <= eps.
        { rewrite expr2.
          have Htmp : eps * eps <= eps * 1 by exact: (ler_pM (ltW eps_pos) (ltW eps_pos) (lexx eps) Heps_le1).
          by rewrite mulr1 in Htmp. } have Heps_le_sum : eps <= eps + ebar by rewrite lerDl; exact: ltW ebar_pos.
        have Hpass_le_eps_s : p_pass <= eps_s.
        { exact: le_trans Hpass_case (le_trans Heps2_le_eps (le_trans Heps_le_sum Hbudget)). } exact: le_trans Hnonabort_le_pass Hpass_le_eps_s.
      - have Hone_le_eps_s : 1 <= eps_s.
        { have Heps_lt_sum : eps < eps + ebar by rewrite ltrDl; exact: ebar_pos.
          exact: ltW (lt_le_trans (lt_trans Hone_lt_eps Heps_lt_sum) Hbudget). } exact: le_trans Hnonabort_le1 Hone_le_eps_s. } set eq_pub_assoc := bb84_public_assoc S E Epub.
    set rhoAB := post_hash_state disSEpub Fh (castlf (eq_pub_assoc, eq_pub_assoc) (bb84_public_state pub)).
    have Hpub_cast_psd : castlf (eq_pub_assoc, eq_pub_assoc) (bb84_public_state pub) \is psdlf.
    { exact: castlf_psdlf (bb84_public_state_psd pub). } have HrhoAB_psd : rhoAB \is psdlf.
    { rewrite /rhoAB.
      exact: (@post_hash_psdlf R L HL S (E :|: Epub) Fl Zl disSEpub disSF disSZl disEpubF disEpubZl disFZl Fh _ Hpub_cast_psd). } have HrhoAB_tr : @complex.Re R (\Tr rhoAB) <= 1.
    { rewrite /rhoAB (@post_hash_trace_preserve R L HL S (E :|: Epub) Fl Zl disSEpub disSF disSZl disEpubF disEpubZl disFZl Fh _ Hpub_cast_psd).
      by rewrite castlf_trlfE; exact: bb84_public_state_tr. } have Hdist_le1 : dist_from_uniform rhoAB <= 1.
    { have Htr_ptrace_rho : \Tr (\Tr_(Zl) rhoAB) = \Tr rhoAB.
        by case/cptpP: (@ptraceso_qc R L HL Zl (Zl :|: (Fl :|: (E :|: Epub)))) => _ /tpmapP ->.
      pose sigmaB : 'F[HL]_(Fl :|: (E :|: Epub)) := ptrace_castl disZl_FEpub rhoAB.
      have Hsigma_psd : sigmaB \is psdlf := ptrace_castl_psdlf disZl_FEpub HrhoAB_psd.
      have Hsigma_Tr : \Tr sigmaB = \Tr (\Tr_(Zl) rhoAB).
        by rewrite /sigmaB /ptrace_castl /ptrace_cast_gen -castlf_trlf.
      have Hwb : 2%:R * dist_from_uniform rhoAB <= trnormH (rhoAB - (dim 'H[HL]_Zl)%:R^-1 *: ((\1 : 'F[HL]_Zl) \O sigmaB)).
        by apply: dist_uniform_witness_bound.
      have Htwo_inv_ge0 : (0 : R) <= @GRing.inv R 2%:R by rewrite invr_ge0 ler0n.
      have Hd_u : dist_from_uniform rhoAB <= @GRing.inv R 2%:R * trnormH (rhoAB - (dim 'H[HL]_Zl)%:R^-1 *: ((\1 : 'F[HL]_Zl) \O sigmaB)).
      { have /(ler_wpM2l Htwo_inv_ge0) := Hwb. rewrite mulrA mulVf ?pnatr_eq0// mul1r. by []. } apply: le_trans Hd_u _.
      have Hbound : trnormH (rhoAB - (dim 'H[HL]_Zl)%:R^-1 *: ((\1 : 'F[HL]_Zl) \O sigmaB)) <= trnormH rhoAB + trnormH ((dim 'H[HL]_Zl)%:R^-1 *: ((\1 : 'F[HL]_Zl) \O sigmaB)).
        exact: trnormH_triangleB.
      have Htrn_rho : trnormH rhoAB = @complex.Re R (\Tr rhoAB) := trnormH_psd HrhoAB_psd.
      have Hdim_Zl_ne0_R : ((dim 'H[HL]_Zl)%:R : R) != 0 by rewrite pnatr_eq0 -lt0n dim_proper.
      pose invd : R := @GRing.inv R ((dim 'H[HL]_Zl)%:R).
      have Hinv_eq : @GRing.inv C ((dim 'H[HL]_Zl)%:R) = invd%:C by rewrite /invd -natrC -fmorphV.
      have Hinv_ge0 : 0 <= invd by rewrite /invd invr_ge0 ler0n.
      have Htrn_lift : trnormH ((dim 'H[HL]_Zl)%:R^-1 *: ((\1 : 'F[HL]_Zl) \O sigmaB)) = @complex.Re R (\Tr rhoAB).
      { rewrite Hinv_eq trnormH_scaleZ.
        rewrite (trnormH_lift_I_psd disZl_FEpub Hsigma_psd) trnormH_psd//.
        rewrite (ger0_norm Hinv_ge0) /invd mulrA (mulVf Hdim_Zl_ne0_R) ?mul1r Hsigma_Tr Htr_ptrace_rho.
        by rewrite ?mul1r. } rewrite Htrn_rho Htrn_lift in Hbound.
      have Hhalf_bound : @GRing.inv R 2%:R * trnormH (rhoAB - (dim 'H[HL]_Zl)%:R^-1 *: ((\1 : 'F[HL]_Zl) \O sigmaB)) <= @complex.Re R (\Tr rhoAB).
      { have Hinq := ler_wpM2l Htwo_inv_ge0 Hbound.
        apply: le_trans Hinq _.
        rewrite mulrDr [@GRing.inv R 2%:R * _]mulrC -splitr; exact: lexx. } exact: le_trans Hhalf_bound HrhoAB_tr. } exists 1; split.
    + by rewrite /delta_secret; exact: Hdist_le1.
    + by rewrite mulr1; exact: Hnonabort_le_eps_s. Qed.

End Secrecy.

Section BB84Security.

Variable (L : finType) (HL : L -> chsType).
Variable (S E Zkey Bq Zp Fl Zl : {set L}).
Hypotheses (disSE : [disjoint S & E]) (disSZ : [disjoint S & Zkey]) (disSBq : [disjoint S & Bq]) (disSZp : [disjoint S & Zp]).
Hypotheses (disSF : [disjoint S & Fl]) (disSZl : [disjoint S & Zl]) (disEZ : [disjoint E & Zkey]) (disEBq : [disjoint E & Bq]).
Hypotheses (disEZp : [disjoint E & Zp]) (disEF : [disjoint E & Fl]) (disEZl : [disjoint E & Zl]) (disZBq : [disjoint Zkey & Bq]).
Hypotheses (disZZp : [disjoint Zkey & Zp]) (disFZl : [disjoint Fl & Zl]).
Variable Aux : @bb84_aux_regs R L HL Zkey Bq Zp.

Let disZl_FE : [disjoint Zl & (Fl :|: E)].
Proof. by rewrite disjointXU disjoint_sym disFZl disjoint_sym disEZl. Defined.

Theorem bb84_secure
    (P : bb84_protocol) (q eps_s eps_tot : R)
    (Gsrc : bb84_zsource P)
    (nx : nat)
    (M : 'I_nx -> 'M[C]_(2 ^ bb84_n P))
    (dim_S : nx = dim ('H[HL]_S))
    (dim_E : bb84_zsrc_nb Gsrc = dim ('H[HL]_E))
    (dim_Zk_key : (2 ^ bb84_n P)%N = dim ('H[HL]_Zkey))
    (dim_Bq_key : (2 ^ bb84_n P)%N = dim ('H[HL]_Bq))
    (dim_Zp_key : (2 ^ bb84_n P)%N = dim ('H[HL]_Zp))
    (p_abort : R)
    (mismatch_prob : R)
    (seed_count tag_count : nat)
    (verify_hash : 'I_seed_count -> 'I_(2 ^ bb84_n P) -> 'I_tag_count)
    (corr_prob : 'I_(2 ^ bb84_n P) -> 'I_(2 ^ bb84_n P) -> R)
    (p_mismatchE :
      mismatch_prob =
        @p_mismatch R (2 ^ bb84_n P) seed_count tag_count verify_hash
          corr_prob)
    (verify_tag_count_pos : (0 < tag_count)%N)
    (verify_two_univ : @two_univ R _ _ _ verify_hash)
    (corr_nonneg : forall x x', 0 <= corr_prob x x')
    (corr_mass : \sum_x \sum_(x' | x != x') corr_prob x x' <= 1)
    (verify_tag_inv_le_epsc : ((tag_count%:R : R)^-1 <= bb84_eps_c P)%R)
    (Fh : 'Idx[HL]_Fl -> 'Idx[HL]_S -> 'Idx[HL]_Zl)
    (Fh_two_univ : @two_univ R _ _ _ Fh)
    (Fh_key_dim : dim ('H[HL]_Zl) = (2 ^ bb84_l P)%N)

    (Epub : {set L})
    (pub : bb84_public_leakage Epub
      (eur_rho_XB disSE (bb84_cond_rho Gsrc) M
        (bb84_register_pair_dim disSE dim_S dim_E))
      (bb84_leak_EC P + log2 (2%:R / bb84_eps_c P)))
    (disSEpub : [disjoint S & E :|: Epub])
    (disEpubF : [disjoint E :|: Epub & Fl])
    (disEpubZl : [disjoint E :|: Epub & Zl])
    (disZl_FEpub : [disjoint Zl & (Fl :|: (E :|: Epub))])
    (Hnum : forall eps0 : R, bb84_numeric_side P eps0) :
  (bb84_n P)%:R * q <=
    q_of_mx M (@std_projective_povm R (2 ^ bb84_n P)) -> is_povm_mx M ->
  bb84_pass_prob_le p_abort (bb84_p_pass_tot Gsrc) -> (0 < bb84_n P)%N -> (0 < bb84_k P)%N ->
  bb84_eps_c P + eps_s <= eps_tot -> (0 < eps_s) && (eps_s <= 1) -> (bb84_l P)%:R <=
    sup (fun M : R =>
      exists eps ebar : R,
        0 < eps /\ eps < 1 /\ 0 < ebar /\ eps + ebar <= eps_s /\
        M = ((floor (
          (bb84_n P)%:R *
            (q - bb84_h_trunc (bb84_Qtol P +
              bb84_mu (bb84_n P) (bb84_k P) eps)) -
          2%:R * log2 ((2%:R * ebar)^-1) -
          bb84_leak_EC P -
          log2 (2%:R / bb84_eps_c P)))%:~R : R)) -> let eq_pub_assoc := @bb84_public_assoc L S E Epub in
    eps_secure
      mismatch_prob
      (bb84_eps_c P)
      (post_hash_state disSEpub Fh
        (castlf (eq_pub_assoc, eq_pub_assoc)
          (bb84_public_state pub))) eps_s
      p_abort
      eps_tot.
Proof.
  move=> overlap_q M_povm Hpass_prob n_pos k_pos Htot_budget eps_s_range Hlen_sup.
  split; [|split].
  { rewrite p_mismatchE.
    apply: (@bb84_correct (2 ^ bb84_n P) seed_count tag_count verify_hash corr_prob).
    1,2,3,4,5: by [exact: verify_tag_count_pos | exact: verify_two_univ | exact: corr_nonneg | exact: corr_mass | exact: verify_tag_inv_le_epsc]. }
  { exact: (@bb84_secret L HL S E Zkey Bq Zp Fl Zl disSE disSZ disSBq disSF disSZl disEZ disEBq disZBq disZZp disFZl Aux P q eps_s Gsrc nx M dim_S dim_E dim_Zk_key dim_Bq_key dim_Zp_key p_abort Fh Fh_two_univ Fh_key_dim Epub pub disSEpub disEpubF disEpubZl disZl_FEpub Hnum overlap_q Hpass_prob M_povm n_pos k_pos eps_s_range Hlen_sup). }
  { exact: Htot_budget. } Qed.

End BB84Security.

End FvqkdReal.
