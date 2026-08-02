(* instantiation.v -- Concrete BB84 operating point                     *)
(* Module: qkd.example.instantiation                                    *)
(* The operating point ex_device for bb84_secure_protocol, yielding     *)
(* the concrete instance bb84_secure_example.                           *)

From mathcomp Require Import all_boot all_order all_algebra finmap.
From mathcomp.reals Require Import reals.
From mathcomp.analysis Require Import exp.
From quantum.external Require Import spectral complex.
From quantum Require Import mcextra mcaextra notation hermitian quantum mxpred.
From quantum.dirac Require Import hstensor.

Import Order.TTheory GRing.Theory Num.Theory Num.Def.

From utils Require Import exports.
From entropy Require Import def.
From lhl Require Import def construction.
From eur Require Import def prop.
From qkd.bb84 Require Import def model prop.
From qkd.protocol Require Import syntax semantics qkd_cmd.
From qkd.example Require Import device program run stat example.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Open Scope ring_scope.

Local Lemma ffun_card_gt0 (X Z : finType) : (0 < #|Z|)%N -> (0 < #|[the finType of {ffun X -> Z}]|)%N.
Proof. by move=> HZ; rewrite card_ffun expn_gt0 HZ. Qed.

Local Lemma log2_pow2_le_succ (R0 : realType) (m : nat) : log2 (((2 ^ m)%:R : R0)) <= log2 (((2 ^ m.+1)%:R : R0)).
Proof. by rewrite !log2_pow2_nat ler_nat. Qed.

Local Lemma half_add (R0 : realType) : (2%:R : R0)^-1 + (2%:R)^-1 = 1.
Proof. have H2 : (2%:R : R0) != 0 by rewrite pnatr_eq0. by apply: (mulIf H2); rewrite mulrDl !mulVf // mul1r -mulr2n. Qed.

Local Lemma x_projective_povm2_den1 (R0 : realType) (x : 'I_2) : @x_projective_povm2 R0 x \is den1mx.
Proof.
  apply/den1mxP; split; first exact: x_projective_povm2_psd.
  apply/eqP; case: x => [[|[|x]] Hx]; try by [].
  all: rewrite /mxtrace /x_projective_povm2 /xbasis_vec2 /xbasis_sign2 !big_ord_recl !big_ord0 /=.
  all: by rewrite !mxE ?big_ord_recl ?big_ord0 !mxE /= ?eqxx ?conjC1 ?conjCN1; simpc; rewrite complexr0 half_add. Qed.

Local Lemma adjmx0 (R0 : realType) (m n : nat) : (0 : 'M[@hermitian.C R0]_(m, n))^*t = 0.
Proof. by rewrite adjmxE trmx0 map_mx0. Qed.

Section InstanceScaffold.
Variable R : realType.
Notation C := (@hermitian.C R).
Notation chsType := (@chsType R).

Definition nn : nat := 10 ^ 4.

Definition ex_nn_gt0 : (0 < nn)%N.
Proof. by rewrite /nn expn_gt0. Defined.
Opaque nn.

Definition exlen : nat := 2000.
Definition ex_round_limit : nat := 100 * (nn + nn).
Definition ex_tag_bits : nat := 34.
Definition ex_ec_bits : nat := 1024.

Definition ex_eps_c : R := ((2 ^ ex_tag_bits)%:R)^-1.
Definition ex_eps : R := ex_eps_c.
Definition ex_ebar : R := ex_eps_c.
Definition ex_eps_s : R := ex_eps_c *+ 2.
Definition ex_eps_tot : R := ex_eps_c *+ 3.
Definition ex_leak_EC : R := ex_ec_bits%:R.

Definition Pex : @bb84_protocol R := @BB84Protocol R nn nn ex_round_limit exlen (100%:R)^-1 ex_eps_c ex_leak_EC.

Lemma Pex_n : bb84_n Pex = nn.
Proof. by []. Qed.

Fact Pex_k : bb84_k Pex = nn.
Proof. by []. Qed.

Lemma Pex_eps_c : bb84_eps_c Pex = ex_eps_c.
Proof. by []. Qed.

Lemma ex_eps_c_pos : (0 : R) < ex_eps_c.
Proof. by rewrite /ex_eps_c invr_gt0 ltr0n expn_gt0. Qed.

Fact ex_eps_pos : (0 : R) < ex_eps.
Proof. exact: ex_eps_c_pos. Qed.

Fact ex_eps_lt1 : ex_eps < 1.
Proof. rewrite /ex_eps /ex_eps_c invf_lt1 ?ltr0n //. by rewrite ltr1n. Qed.

Lemma ex_ebar_pos : (0 : R) < ex_ebar.
Proof. exact: ex_eps_c_pos. Qed.

Lemma ex_eps_s_pos : (0 : R) < ex_eps_s.
Proof. rewrite /ex_eps_s mulr2n. exact: addr_gt0 ex_eps_c_pos ex_eps_c_pos. Qed.

Lemma ex_eps_s_le1 : ex_eps_s <= 1.
Proof. have Hden_pos : (0 : R) < (2 ^ ex_tag_bits)%:R by rewrite ltr0n expn_gt0. have Hden_unit : ((2 ^ ex_tag_bits)%:R : R) != 0 := lt0r_neq0 Hden_pos. rewrite -(ler_pM2r Hden_pos) mul1r /ex_eps_s /ex_eps_c mulr2n mulrDl (mulVf Hden_unit). by rewrite -mulr2n ler_nat /ex_tag_bits. Qed.

Fact ex_eps_s_range : (0 < ex_eps_s) && (ex_eps_s <= 1).
Proof. by rewrite ex_eps_s_pos ex_eps_s_le1. Qed.

Fact ex_eps_budget : ex_eps + ex_ebar <= ex_eps_s.
Proof. by rewrite /ex_eps /ex_ebar /ex_eps_s -mulr2n. Qed.

Fact ex_eps_total_budget : bb84_eps_c Pex + ex_eps_s <= ex_eps_tot.
Proof. by rewrite Pex_eps_c /ex_eps_s /ex_eps_tot mulrS. Qed.

Lemma ex_ln_ge_1subInv (u : R) : 0 < u -> 1 - u^-1 <= ln u.
Proof. move=> Hu; have Hlt : (-1 : R) < u^-1 - 1 by rewrite ltrBrDr addNr invr_gt0. have Hle := le_ln1Dx Hlt. by rewrite addrCA subrr addr0 (lnV Hu) lerNl opprB in Hle. Qed.

Lemma ex_xlnx_tangent (x b : R) : 0 < x -> 0 < b -> - (x * ln x) <= - (x * ln b) - (x - b).
Proof.
  move=> Hx Hb; have Hxn0 : x != 0 by rewrite gt_eqF.
  have Hxb : 0 < x / b by rewrite divr_gt0.
  have Hlndiv : ln (x / b) = ln x - ln b by rewrite lnM ?posrE ?invr_gt0 // (lnV Hb).
  have H := ex_ln_ge_1subInv Hxb; rewrite Hlndiv invf_div in H.
  have Hbx : x * (b / x) = b by rewrite mulrC -mulrA (mulVf Hxn0) mulr1.
  have Hmul : x * (1 - b / x) <= x * (ln x - ln b) by rewrite (ler_pM2l Hx).
  by rewrite !mulrBr Hbx mulr1 in Hmul; rewrite -opprD lerN2 addrC -lerBrDr. Qed.

Fact ex_ln2_ge_half : (2%:R : R)^-1 <= ln 2%:R.
Proof. have H2 : (0 : R) < 2%:R by rewrite ltr0n. have H2n0 : (2%:R : R) != 0 by rewrite pnatr_eq0. have key : (2%:R : R)^-1 + (2%:R)^-1 = 1 by apply: (mulIf H2n0); rewrite mulrDl !mulVf // mul1r -mulr2n. by apply: le_trans (ex_ln_ge_1subInv H2); rewrite lerBrDr key. Qed.

Fact ex_h_bin_le58 (x : R) : 0 < x -> x <= (8%:R)^-1 -> h_bin x <= 5%:R / 8%:R.
Proof.
  move=> Hx Hx8; set L := ln (2%:R : R).
  have HLh : (2%:R : R)^-1 <= L := ex_ln2_ge_half.
  have HLpos : (0 : R) < L by apply: lt_le_trans HLh; rewrite invr_gt0 ltr0n.
  have H8pos : (0 : R) < 8%:R by rewrite ltr0n.
  have H18 : (0 : R) < (8%:R)^-1 by rewrite invr_gt0.
  have H81 : ((8%:R : R)^-1) < 1 by rewrite invf_lt1 ?ltr0n // ltr1n.
  have H1x : (0 : R) < 1 - x by rewrite subr_gt0 (le_lt_trans Hx8 H81).
  have Hln18 : ln ((8%:R : R)^-1) = - (3%:R * L).
  { rewrite (lnV H8pos) -log2K_ln; congr (- _). by rewrite (_ : (8%:R : R) = (2 ^ 3)%:R) ?log2_pow2_nat. } have Ex0 : (x <= 0) = false by apply/negbTE; rewrite -ltNge.
  have Ex1 : (1 <= x) = false by apply/negbTE; rewrite -ltNge (le_lt_trans Hx8 H81).
  rewrite -(ler_pM2r HLpos).
  have HhL : h_bin x * L = - (x * ln x) - ((1 - x) * ln (1 - x)).
  { rewrite /h_bin Ex0 Ex1 mulrBl !mulNr. by congr (- _ - _); rewrite -mulrA log2K_ln. } rewrite HhL.
  apply: le_trans (lerD (ex_xlnx_tangent Hx H18) (ex_xlnx_tangent H1x ltr01)) _.
  have c1 : ((1 - x) - 1 : R) = - x by rewrite addrAC subrr add0r.
  rewrite Hln18 ln1 mulr0 oppr0 sub0r mulrN opprK opprB c1 opprK -addrA subrK.
  have H3L : (0 : R) <= 3%:R * L by rewrite mulr_ge0 ?ler0n ?ltW.
  have H2n0 : (2%:R : R) != 0 by rewrite pnatr_eq0.
  have key2 : (1 : R) <= 2%:R * L.
  { rewrite -[X in X <= _](mulVf H2n0) [(2%:R)^-1 * 2%:R]mulrC. apply: ler_wpM2l; first by rewrite ler0n. exact: HLh. } apply: le_trans (lerD (ler_wpM2r H3L Hx8) (lexx ((8%:R : R)^-1))) _.
  rewrite -[X in _ + X <= _]mulr1 -mulrDr [5%:R / 8%:R]mulrC -mulrA.
  apply: ler_wpM2l; first by rewrite invr_ge0 ler0n.
  have E5L : (5%:R : R) * L = 3%:R * L + 2%:R * L by rewrite -mulrDl -natrD.
  rewrite E5L; exact: (lerD (lexx (3%:R * L)) key2). Qed.

Fact ex_h_trunc_le58 (x : R) : 0 < x -> x <= (8%:R)^-1 -> bb84_h_trunc x <= 5%:R / 8%:R.
Proof. move=> Hx Hx8. have H182 : (8%:R : R)^-1 < 1 / 2 by rewrite div1r ltf_pV2 ?posrE ?ltr0n // ltr_nat. rewrite /bb84_h_trunc. have -> : (x <= 0) = false by apply/negbTE; rewrite -ltNge. have -> : (1 / 2 <= x) = false by apply/negbTE; rewrite -ltNge (le_lt_trans Hx8 H182). exact: ex_h_bin_le58. Qed.

Transparent nn.

Fact nn_ge10 : (10 <= nn)%N.
Proof. by rewrite /nn. Qed.

Fact nn_ge7480 : (748 * 10 <= nn)%N.
Proof. by rewrite /nn. Qed.

Opaque nn.

Fact ex_mu_le : bb84_mu (bb84_n Pex) (bb84_k Pex) ex_eps <= (10%:R : R)^-1.
Proof.
  have HnnR : (0 : R) < nn%:R by rewrite ltr0n ex_nn_gt0.
  have HnnRn0 : nn%:R != 0 :> R by rewrite gt_eqF.
  have ex_ln2_le1 : ln (2%:R : R) <= 1.
  { have Hn1 : (-1 : R) < 1 by rewrite -subr_gt0 opprK -mulr2n ltr0n.
    have H := le_ln1Dx Hn1.
    by rewrite mulr2n. } have Hf3 : ln (ex_eps^-1) <= 34%:R.
  { rewrite /ex_eps /ex_eps_c /ex_tag_bits invrK -log2K_ln log2_pow2_nat -[34%:R in X in _ <= X]mulr1.
    apply: ler_wpM2l; first by rewrite ler0n.
    exact: ex_ln2_le1. } have Hnnnn0 : (nn * nn)%:R != 0 :> R. { apply: lt0r_neq0. by rewrite ltr0n muln_gt0 ex_nn_gt0. } have Hf1 : ((nn + nn)%:R / (nn * nn)%:R : R) = 2%:R / nn%:R.
  { apply/eqP.
    rewrite eqr_div; [ | exact: Hnnnn0 | exact: HnnRn0].
    rewrite -!natrM eqr_nat.
    have E2 : (2 = 1 + 1)%N by [].
    rewrite mulnDl E2 mulnDl !mul1n; exact: eqxx. } have Hf2 : ((nn.+1)%:R / nn%:R : R) <= 11%:R / 10%:R.
  { rewrite ler_pdivrMr; last by rewrite ltr0n ex_nn_gt0.
    rewrite mulrAC ler_pdivlMr; last by rewrite ltr0n.
    rewrite -!natrM ler_nat mulSn.
    have E11 : (11 = 10 + 1)%N by [].
    rewrite E11 mulnDl mul1n mulnC addnC leq_add2l.
    exact: nn_ge10. } have Hbk_ge : (0 : R) <= 2%:R / nn%:R by rewrite divr_ge0 ?ler0n ?ltW.
  rewrite /bb84_mu Pex_n Pex_k.
  rewrite [X in (X * _) * _]Hf1.
  rewrite -[X in _ <= X]ger0_norm; last by rewrite invr_ge0 ler0n.
  rewrite -sqrtr_sqr.
  apply: ler_wsqrtr.
  apply: le_trans (ler_wpM2l (mulr_ge0 Hbk_ge (divr_ge0 (ler0n _ _) (ler0n _ _))) Hf3) _.
  apply: le_trans (ler_wpM2r (ler0n _ 34) (ler_wpM2l Hbk_ge Hf2)) _.
  rewrite mulf_div mulrAC -!natrM exprVn -natrX.
  rewrite ler_pdivrMr; last by rewrite ltr0n muln_gt0 ex_nn_gt0.
  rewrite mulrC ler_pdivlMr; last by rewrite ltr0n expn_gt0.
  rewrite -!natrM ler_nat.
  have Elhs : (2 * 11 * 34 * 10 ^ 2 = 10 * (748 * 10))%N by [].
  have Erhs : (nn * 10 = 10 * nn)%N by rewrite mulnC.
  rewrite Elhs Erhs leq_mul2l.
  by apply/orP; right; exact: nn_ge7480. Qed.

Fact ex_x0_le18 : bb84_Qtol Pex + bb84_mu (bb84_n Pex) (bb84_k Pex) ex_eps <= (8%:R)^-1.
Proof.
  have HqtolE : bb84_Qtol Pex = (100%:R)^-1 by [].
  apply: le_trans (lerD (lexx (bb84_Qtol Pex)) ex_mu_le) _.
  rewrite HqtolE.
  have H200 : (0 : R) < 200%:R by rewrite ltr0n.
  rewrite -(ler_pM2r H200) mulrDl.
  have E200_100 : (200%:R : R) = 100%:R * 2%:R by rewrite -natrM.
  have E200_10 : (200%:R : R) = 10%:R * 20%:R by rewrite -natrM.
  have E200_8 : (200%:R : R) = 8%:R * 25%:R by rewrite -natrM.
  have E1 : (100%:R : R)^-1 * 200%:R = 2%:R by rewrite E200_100 mulrA mulVf ?pnatr_eq0 // mul1r.
  have E2 : (10%:R : R)^-1 * 200%:R = 20%:R by rewrite E200_10 mulrA mulVf ?pnatr_eq0 // mul1r.
  have E3 : (8%:R : R)^-1 * 200%:R = 25%:R by rewrite E200_8 mulrA mulVf ?pnatr_eq0 // mul1r.
  by rewrite E1 E2 E3 -natrD ler_nat. Qed.

Lemma ex_log2V (x : R) : 0 < x -> log2 (x^-1) = - log2 x.
Proof. by move=> Hx; rewrite /log2 (lnV Hx) mulNr. Qed.

Fact ex_overhead_ebar : 2%:R * log2 ((2%:R * ex_ebar)^-1) = 66%:R.
Proof. have Hebpos : (0 : R) < ex_ebar := ex_ebar_pos. have H2eb : (0 : R) < 2%:R * ex_ebar by rewrite mulr_gt0 ?ltr0n. rewrite ex_log2V // log2_mul ?ltr0n //. rewrite log2_2 /ex_ebar /ex_eps_c /ex_tag_bits ex_log2V ?ltr0n ?expn_gt0 // log2_pow2_nat. by rewrite opprD opprK mulrDr mulrN1 -natrM addrC -natrB. Qed.

Transparent nn.

Fact nn_ge10000 : (10 ^ 4 <= nn)%N.
Proof. by rewrite /nn. Qed.

Opaque nn.

Fact ex_key_length_ub_ge2625 : (2625%:R : R) <= bb84_key_length_ub (bb84_n Pex) (bb84_k Pex) (1 : R) (bb84_Qtol Pex)
    ex_eps ex_ebar (bb84_leak_EC Pex) (bb84_eps_c Pex).
Proof.
  have Pex_leak_EC : bb84_leak_EC Pex = ex_ec_bits%:R by rewrite /Pex /= /ex_leak_EC /ex_ec_bits.
  have Hleak : bb84_leak_EC Pex = 1024%:R by rewrite Pex_leak_EC /ex_ec_bits.
  have Hmu_ge : (0 : R) <= bb84_mu (bb84_n Pex) (bb84_k Pex) ex_eps by rewrite /bb84_mu sqrtr_ge0.
  have HQtol_gt : (0 : R) < bb84_Qtol Pex by rewrite (_ : bb84_Qtol Pex = (100%:R)^-1) // invr_gt0 ltr0n.
  have Hx0pos : (0 : R) < bb84_Qtol Pex + bb84_mu (bb84_n Pex) (bb84_k Pex) ex_eps by apply: (lt_le_trans HQtol_gt); rewrite lerDl.
  have Hht : bb84_h_trunc (bb84_Qtol Pex + bb84_mu (bb84_n Pex) (bb84_k Pex) ex_eps) <= 5%:R / 8%:R := ex_h_trunc_le58 Hx0pos ex_x0_le18.
  have E38 : (3%:R / 8%:R : R) = 1 - 5%:R / 8%:R.
  { have H8n0 : (8%:R : R) != 0 by rewrite pnatr_eq0.
    apply: (mulIf H8n0).
    by rewrite mulrBl mul1r -!mulrA !(mulVf H8n0) !mulr1 -natrB. } have Hqh : 3%:R / 8%:R <= (1 : R) - bb84_h_trunc (bb84_Qtol Pex + bb84_mu (bb84_n Pex) (bb84_k Pex) ex_eps).
  { rewrite E38; exact: lerB (lexx 1) Hht. } have HA3750 : (3750%:R : R) <= (bb84_n Pex)%:R * (3%:R / 8%:R).
  { rewrite Pex_n mulrA ler_pdivlMr; last by rewrite ltr0n.
    rewrite -!natrM ler_nat.
    have E30000 : (3750 * 8 = 3 * 10 ^ 4)%N by [].
    rewrite E30000 mulnC leq_mul2l.
    by apply/orP; right; exact: nn_ge10000. } have HT : (3750%:R : R) <= (bb84_n Pex)%:R * ((1 : R) - bb84_h_trunc (bb84_Qtol Pex + bb84_mu (bb84_n Pex) (bb84_k Pex) ex_eps)).
  { apply: le_trans HA3750 _. apply: ler_wpM2l; first exact: ler0n. exact: Hqh. } have ex_overhead_epsc : log2 (2%:R / bb84_eps_c Pex) = 35%:R.
  { rewrite Pex_eps_c /ex_eps_c /ex_tag_bits invrK -natrM.
    rewrite (_ : (2 * 2 ^ 34 = 2 ^ 35)%N); last by rewrite -expnS.
    by rewrite log2_pow2_nat. } rewrite /bb84_key_length_ub ex_overhead_ebar Hleak ex_overhead_epsc !lerBrDr -!natrD.
  exact: HT. Qed.

Fact ex_key_length_floor_ge2000 : (bb84_l Pex)%:R <= ((floor (bb84_key_length_ub (bb84_n Pex) (bb84_k Pex) (1 : R) (bb84_Qtol Pex)
    ex_eps ex_ebar (bb84_leak_EC Pex) (bb84_eps_c Pex)))%:~R : R).
Proof.
  have Pex_l : bb84_l Pex = exlen by [].
  rewrite Pex_l /exlen.
  have H2000 : (2000%:R : R) <= bb84_key_length_ub (bb84_n Pex) (bb84_k Pex) (1 : R) (bb84_Qtol Pex) ex_eps ex_ebar (bb84_leak_EC Pex) (bb84_eps_c Pex) by apply: le_trans ex_key_length_ub_ge2625; rewrite ler_nat.
  have E2000 : (2000%:R : R) = (Posz 2000)%:~R by rewrite pmulrn.
  rewrite E2000 ler_int floor_ge_int -E2000.
  exact: H2000. Qed.

Definition ex_bit_ord (bit : bool) : 'I_2 := if bit then Ordinal (isT : (1 < 2)%N) else ord0.

Definition ex_source_dim : nat := ((2 ^ nn) * 1 * (2 ^ nn))%N.

Definition ex_source_zero : 'I_ex_source_dim.
Proof.
  refine (@Ordinal ex_source_dim 0 _).
  have Hpow : (0 < 2 ^ nn)%N by rewrite expn_gt0.
  have Hone : (0 < 1)%N by [].
  exact: ltn_mul (ltn_mul Hpow Hone) Hpow. Defined.

Definition ex_source_rho : 'M[C]_ex_source_dim := delta_mx ex_source_zero ex_source_zero.

Definition ex_source_M : 'I_(2 ^ nn) -> 'M[C]_(2 ^ nn) := @x_projective_povm R nn.

Definition ex_source_N : 'I_(2 ^ nn) -> 'M[C]_(2 ^ nn) := @std_projective_povm R (2 ^ nn).

Definition ex_source_quality : (bb84_n Pex)%:R * (1 : R) <= q_of_mx ex_source_M ex_source_N.
Proof.
  by rewrite /Pex /= /ex_source_M /ex_source_N q_of_mx_xz_projective_povm mulr1. Defined.

Definition ex_source_model : bb84_source_model Pex (1 : R).
Proof.
  refine (@BB84SourceModel R Pex 1 (2 ^ nn)%N 1%N (2 ^ nn)%N (2 ^ nn)%N (2 ^ nn)%N ex_source_rho ex_source_M ex_source_N _ _ _ _ _ _).
  - by apply/den1mxP; split; [exact: delta_mx_ii_psdmx | rewrite tr_delta_mx_ii].
  - exact: x_projective_povm_is_povm.
  - exact: std_projective_povm_is_povm.
  - exact: ex_source_quality.
  1,2: by []. Defined.

Definition ex_prepare_state (basis : bb84_basis) (bit : bool) : 'M[C]_2 := match basis with
  | BasisX => @x_projective_povm2 R (ex_bit_ord bit) | BasisZ => @std_projective_povm R 2 (ex_bit_ord bit) end.

Definition ex_prepare_state_den1 basis bit : ex_prepare_state basis bit \is den1mx.
Proof.
  case: basis; rewrite /ex_prepare_state.
  - exact: x_projective_povm2_den1.
  - by apply/den1mxP; split; [exact: delta_mx_ii_psdmx | rewrite tr_delta_mx_ii]. Defined.

Definition ex_measurement_operator (basis : bb84_basis) (outcome : option bool) : 'M[C]_2 := match outcome with | None => 0
  | Some bit => ex_prepare_state basis bit end.

Definition ex_measurement_complete basis : (ex_measurement_operator basis None)^*t *m ex_measurement_operator basis None +
  (ex_measurement_operator basis (Some false))^*t *m ex_measurement_operator basis (Some false) +
  (ex_measurement_operator basis (Some true))^*t *m ex_measurement_operator basis (Some true) = 1%:M.
Proof.
  case: basis; rewrite /ex_measurement_operator /ex_prepare_state adjmx0 mul0mx add0r.
  - have Hh x : (@x_projective_povm2 R x)^*t = @x_projective_povm2 R x by have /hermmxP := psdmx_herm (@x_projective_povm2_psd R x).
    by rewrite !Hh !x_projective_povm2_idem -x_projective_povm2_sum !big_ord_recl !big_ord0 /= addr0.
  - by rewrite !adjmx_delta !mul_delta_mx (@mx1_sum_delta C 2) !big_ord_recl !big_ord0 /= addr0. Defined.

Definition ex_ir_bits : nat := 0.

Definition ex_ir_pub (_ _ : 'I_(2 ^ nn)) : 'I_(2 ^ ex_ir_bits) := ord0.

Definition ex_ir_dec (_ : 'I_(2 ^ ex_ir_bits)) (xb : 'I_(2 ^ nn)) := xb.

Definition ex_ir_leak : (ex_ir_bits)%:R <= bb84_leak_EC Pex.
Proof. by rewrite /Pex /= /ex_ir_bits. Defined.

Definition ex_verify_seed_count : nat := #|[the finType of {ffun 'I_(2 ^ nn) -> 'I_(2 ^ ex_tag_bits)}]|.

Definition ex_tag_count : nat := 2 ^ ex_tag_bits.

Definition ex_verify_seed (i : 'I_ex_verify_seed_count) : {ffun 'I_(2 ^ nn) -> 'I_(2 ^ ex_tag_bits)} := enum_val i.

Definition ex_verify_hash (i : 'I_ex_verify_seed_count) (x : 'I_(2 ^ nn)) : 'I_(2 ^ ex_tag_bits) := ex_verify_seed i x.

Definition ex_verify_seed_pos : (0 < ex_verify_seed_count)%N.
Proof.
  by rewrite /ex_verify_seed_count; apply: ffun_card_gt0; rewrite card_ord expn_gt0. Defined.

Definition ex_tag_pos : (0 < ex_tag_count)%N.
Proof. by rewrite /ex_tag_count expn_gt0. Defined.

Definition ex_tag_le : ((ex_tag_count%:R : R)^-1 <= bb84_eps_c Pex)%R.
Proof. by rewrite /Pex /= /ex_tag_count /ex_eps_c. Defined.

Definition ex_tag_bits_bound : log2 (ex_tag_count%:R : R) <= log2 (2%:R / bb84_eps_c Pex).
Proof.
  rewrite /Pex /= /ex_tag_count (_ : 2%:R / ex_eps_c = ((2 ^ ex_tag_bits.+1)%:R : R)); first exact: log2_pow2_le_succ.
  by rewrite /ex_eps_c invrK -natrM -expnS. Defined.

Definition ex_verify_hash_two_univ : @two_univ R _ _ _ ex_verify_hash.
Proof.
  pose F := (@allfun_hash 'I_(2 ^ nn) 'I_(2 ^ ex_tag_bits)).
  change (@two_univ R _ _ _ (fun i : 'I_ex_verify_seed_count => F (enum_val i))).
  have Hall : @two_univ R _ _ _ F := @allfun_two_univ R _ _.
  rewrite /two_univ.
  apply: (@reindex_delta_almost_two_univ R [the finType of {ffun 'I_(2 ^ nn) -> 'I_(2 ^ ex_tag_bits)}] 'I_ex_verify_seed_count 'I_(2 ^ nn) 'I_(2 ^ ex_tag_bits) enum_val F); [exact: enum_val_bij | exact: Hall]. Defined.

Definition ex_pa_seed_count : nat := #|[the finType of {ffun 'I_(2 ^ nn) -> 'I_(2 ^ exlen)}]|.

Definition ex_pa_seed (i : 'I_ex_pa_seed_count) : {ffun 'I_(2 ^ nn) -> 'I_(2 ^ exlen)} := enum_val i.

Definition ex_pa_hash (i : 'I_ex_pa_seed_count) (x : 'I_(2 ^ nn)) : 'I_(2 ^ exlen) := ex_pa_seed i x.

Definition ex_detect_basis_indep : ex_measurement_operator BasisX None = ex_measurement_operator BasisZ None.
Proof. by []. Defined.

Definition ex_pa_seed_pos : (0 < ex_pa_seed_count)%N.
Proof.
  by rewrite /ex_pa_seed_count; apply: ffun_card_gt0; rewrite card_ord expn_gt0. Defined.

Definition ex_pa_hash_two_univ : @two_univ R _ _ _ ex_pa_hash.
Proof.
  pose F := (@allfun_hash 'I_(2 ^ nn) 'I_(2 ^ exlen)).
  change (@two_univ R _ _ _ (fun i : 'I_ex_pa_seed_count => F (enum_val i))).
  have Hall : @two_univ R _ _ _ F := @allfun_two_univ R _ _.
  rewrite /two_univ.
  apply: (@reindex_delta_almost_two_univ R [the finType of {ffun 'I_(2 ^ nn) -> 'I_(2 ^ exlen)}] 'I_ex_pa_seed_count 'I_(2 ^ nn) 'I_(2 ^ exlen) enum_val F); [exact: enum_val_bij | exact: Hall]. Defined.

Definition ex_source_dim_A : bb84_src_na ex_source_model = (2 ^ bb84_n Pex)%N.
Proof. by []. Defined.

Definition ex_source_dim_X : bb84_src_nx ex_source_model = (2 ^ bb84_n Pex)%N.
Proof. by []. Defined.

Definition ex_source_nb_pos : (0 < bb84_src_nb ex_source_model)%N.
Proof. by []. Defined.

Definition ex_source_overlap_standard_z : (bb84_n Pex)%:R * (1 : R) <= q_of_mx (bb84_source_x_povm ex_source_dim_A ex_source_dim_X)
    (@std_projective_povm R (2 ^ bb84_n Pex)).
Proof.
  by change ((bb84_n Pex)%:R * (1 : R) <= q_of_mx ex_source_M ex_source_N); exact: ex_source_quality. Defined.

Definition ex_device : bb84_certified_device Pex (1 : R).
Proof.
  refine (@BB84CertifiedDevice R Pex 1 ex_source_model ex_source_dim_A ex_source_dim_X ex_source_nb_pos ex_source_overlap_standard_z ex_prepare_state ex_prepare_state_den1 ex_measurement_operator ex_measurement_complete ex_detect_basis_indep ex_ir_bits ex_ir_pub ex_ir_dec ex_ir_leak ex_verify_seed_count ex_verify_seed_pos ex_tag_count ex_verify_hash ex_verify_hash_two_univ ex_tag_pos ex_tag_le ex_tag_bits_bound ex_pa_seed_count ex_pa_seed_pos ex_pa_hash ex_pa_hash_two_univ). Defined.

Lemma ex_key_length_sup : (bb84_l Pex)%:R <= sup (fun m : R => exists eps ebar : R,
        0 < eps /\ eps < 1 /\ 0 < ebar /\ eps + ebar <= ex_eps_s /\ m = ((floor (bb84_key_length_ub (bb84_n Pex) (bb84_k Pex)
          (1 : R) (bb84_Qtol Pex) eps ebar (bb84_leak_EC Pex) (bb84_eps_c Pex)))%:~R : R)).
Proof.
  apply: le_trans ex_key_length_floor_ge2000 _.
  have [_ Hsup_ub] := bb84_key_length_has_sup Pex (1 : R) ex_eps_s_pos ex_eps_s_le1.
  apply: (ub_le_sup Hsup_ub).
  exists ex_eps, ex_ebar.
  split; first exact: ex_eps_pos; split; first exact: ex_eps_lt1.
  by split; first exact: ex_ebar_pos; split; first exact: ex_eps_budget. Qed.

Section SecureExample.

Variables (LE : finType) (HE : LE -> chsType).

Notation M := (bb84_round_limit Pex).
Notation HB := (@bb84_register_space R Pex 1 ex_device).
Notation L := (bb84_label M LE bb84_register_index).
Notation HL := (bb84_label_space HE HB).

Notation ecP := (cd_ir_bits ex_device).
Notation vsP := (cd_vseed_count ex_device).
Notation tgP := (cd_tag_count ex_device).
Notation psP := (cd_paseed_count ex_device).
Notation V := (bb84_val M (bb84_n Pex) (bb84_l Pex) ecP vsP tgP psP).
Notation state := (@cq_state R L HL (bb84_cvar M) V).
Notation Eve := (@bb84_Eve R Pex LE).
Notation Bq := (@bb84_Bq R Pex LE).
Notation Ereg := (@bb84_E R Pex LE).
Notation Fl := (@bb84_Fl R Pex LE).
Notation Zl := (@bb84_Zl R Pex LE).
Notation Ppub := (@bb84_Ppub R Pex LE).
Notation cstore := (@store (bb84_cvar M) V).
Notation pbvX := (@bb84_program_basis_value R Pex 1 ex_device BasisX).
Notation pbvZ := (@bb84_program_basis_value R Pex 1 ex_device BasisZ).

Definition ex_identity_adversary : @adversary R L HL V Eve := fun Q _ => let QE := Q :|: Eve in
    QChannel_Build (@idso_qc R (@hstensor.Hs R L HL QE)).

Definition ex_initial_store : cstore := [ffun _ => @bb84_bot_val M (bb84_n Pex) (bb84_l Pex) ecP vsP tgP psP].

Definition ex_initial_lf : 'F[HL]_(setT : {set L}) := (((dim 'H[HL]_(setT : {set L}))%:R)^-1)%:C *: (\1%VF : 'F[HL]_(setT : {set L})).

Lemma ex_initial_lf_den1lf : ex_initial_lf \is den1lf.
Proof. apply/den1lfP; split. - by rewrite /ex_initial_lf; apply: psdlfZ; [rewrite lecR invr_ge0 ler0n | rewrite qualifE h2mx1; exact: psdmx1]. - by rewrite /ex_initial_lf linearZ /= /lftrace h2mx1 mxtrace1 -natrC -rmorphM /= mulVf ?rmorph1 // pnatr_eq0 -lt0n dim_proper. Qed.

Definition ex_initial_state : state := @cq_single R L HL (bb84_cvar M) V ex_initial_store ex_initial_lf.

Definition ex_key_sample_set : {set 'I_M} := [set i : 'I_M | (nat_of_ord i < nn)%N].

Definition ex_test_set : {set 'I_M} := [set i : 'I_M | (nn <= nat_of_ord i < nn + nn)%N].

Definition ex_pass_choice (i : 'I_M) : @round_choice V := if i \in ex_test_set then ((bb84_basis_bool_val true, bb84_bit_val false),
      (bb84_basis_bool_val true, bb84_outcome_val (Some false))) else if i \in ex_key_sample_set then
    ((bb84_basis_bool_val false, bb84_bit_val false), (bb84_basis_bool_val false, bb84_outcome_val (Some false))) else
    ((bb84_basis_bool_val false, bb84_bit_val false), (bb84_basis_bool_val true, bb84_outcome_val (Some false))).

Definition ex_pass_trace : @round_trace V M := [ffun i => ex_pass_choice i].

Definition ex_vseed0 : 'I_(cd_vseed_count ex_device) := Ordinal (cd_vseed_pos ex_device).

Definition ex_paseed0 : 'I_(cd_paseed_count ex_device) := Ordinal (cd_paseed_pos ex_device).

Definition ex_key_sample_value : V := @bb84_set_val M (bb84_n Pex) (bb84_l Pex) ecP vsP tgP psP ex_key_sample_set.

Definition ex_vseed_value : V := @bb84_vseed_val M (bb84_n Pex) (bb84_l Pex) ecP vsP tgP psP (Some ex_vseed0).

Definition ex_paseed_value : V := @bb84_paseed_val M (bb84_n Pex) (bb84_l Pex) ecP vsP tgP psP (Some ex_paseed0).

Lemma ex_pass_choice_alice_bit i : choice_y (ex_pass_choice i) = bb84_bit_val false.
Proof. by rewrite /ex_pass_choice; case: ifP; [|case: ifP]. Qed.

Fact ex_pass_choice_alice_basis i : choice_a (ex_pass_choice i) = if i \in ex_test_set then bb84_basis_bool_val true
    else bb84_basis_bool_val false.
Proof. by rewrite /ex_pass_choice; case: ifP; [|case: ifP]. Qed.

Fact ex_pass_choice_bob_basis i : choice_b (ex_pass_choice i) = if i \in ex_test_set then bb84_basis_bool_val true
    else if i \in ex_key_sample_set then bb84_basis_bool_val false else bb84_basis_bool_val true.
Proof. by rewrite /ex_pass_choice; case: ifP; [|case: ifP]. Qed.

Lemma ex_pass_choice_bob_outcome i : choice_y' (ex_pass_choice i) = bb84_outcome_val (Some false).
Proof. by rewrite /ex_pass_choice; case: ifP; [|case: ifP]. Qed.

Lemma ex_round_limit_ge_2nn : (nn + nn <= M)%N.
Proof. rewrite /M /Pex /= /ex_round_limit mulnC. exact: leq_pmulr. Qed.

Fact ex_round_limit_ge_nn : (nn <= M)%N.
Proof. exact: leq_trans (leq_addr nn nn) ex_round_limit_ge_2nn. Qed.

Lemma ex_key_sample_set_card : #|ex_key_sample_set| = nn.
Proof.
  have Hkey_lt (j : 'I_nn) : (nat_of_ord j < M)%N := leq_trans (ltn_ord j) ex_round_limit_ge_nn.
  pose f (j : 'I_nn) : 'I_M := Ordinal (Hkey_lt j).
  have Hset : ex_key_sample_set = [set f j | j in setT].
  { apply/setP=> i; rewrite /ex_key_sample_set inE; apply/idP/imsetP.
    - by move=> Hi; exists (Ordinal Hi) => //; apply/val_inj.
    - by move=> [j _ ->]; rewrite /f /=; exact: ltn_ord. } have Hf_inj : injective f. { move=> i j Hij; apply/val_inj. exact: (congr1 val Hij). } by rewrite Hset (card_imset _ Hf_inj) cardsT card_ord. Qed.

Fact ex_test_set_ge : (nn <= #|ex_test_set|)%N.
Proof.
  have Hshift_lt (j : 'I_nn) : (nn + nat_of_ord j < M)%N by apply: leq_trans ex_round_limit_ge_2nn; rewrite ltn_add2l.
  pose f (j : 'I_nn) : 'I_M := Ordinal (Hshift_lt j).
  have Hsub : [set f j | j in setT] \subset ex_test_set.
  { apply/subsetP=> i /imsetP [j _ ->]. by rewrite /ex_test_set inE leq_addr ltn_add2l ltn_ord. } have Hf_inj : injective f by move=> i j Hij; apply/val_inj; move: (congr1 val Hij) => /= Hijv; exact: (addnI Hijv).
  have Hcard : #|[set f j | j in setT]| = nn by rewrite (card_imset _ Hf_inj) cardsT card_ord.
  by rewrite -Hcard; exact: subset_leq_card Hsub. Qed.

Fact ex_key_sample_mass_pos : 0 < @bb84_unif_nsubset_mass R M (bb84_n Pex) (bb84_l Pex) ecP vsP tgP psP (bb84_n Pex) ex_key_sample_set
  ex_key_sample_value.
Proof. rewrite /ex_key_sample_value (bb84_unif_nsubset_mass_set_val ex_key_sample_set_card (subxx ex_key_sample_set)) invr_gt0 ltr0n. by apply: bb84_nsubset_count_pos; rewrite ex_key_sample_set_card. Qed.

Fact ex_vseed_mass_pos s : 0 < @bb84_unif_vseed_mass R M (bb84_n Pex) (bb84_l Pex) ecP vsP tgP psP s ex_vseed_value.
Proof. rewrite /ex_vseed_value /bb84_unif_vseed_mass (bigD1 ex_vseed0) //=. apply: ltr_wpDr. - by apply: sumr_ge0 => g _; case: ifP => _; rewrite ?invr_ge0 ?ler0n ?lexx. - by rewrite invr_gt0 ltr0n ex_verify_seed_pos. Qed.

Fact ex_paseed_mass_pos s : 0 < @bb84_unif_pseed_mass R M (bb84_n Pex) (bb84_l Pex) ecP vsP tgP psP s ex_paseed_value.
Proof. rewrite /ex_paseed_value /bb84_unif_pseed_mass (bigD1 ex_paseed0) //=. apply: ltr_wpDr. - by apply: sumr_ge0 => f _; case: ifP => _; rewrite ?invr_ge0 ?ler0n ?lexx. - by rewrite invr_gt0 ltr0n ex_pa_seed_pos. Qed.

Fact ex_replay_pX_pos : 0 < @replay_pX R (bb84_n Pex) (bb84_k Pex).
Proof. rewrite /replay_pX invr_gt0. apply: ltr_wpDr; first exact: sqrtr_ge0. exact: ltr01. Qed.

Fact ex_pass_choice_weight_pos s i : 0 < @round_choice_weight R (bb84_cvar M) V (bb84_n Pex) (bb84_k Pex) pbvX pbvZ bb84_bit_val
    (ex_pass_choice i) s.
Proof.
  have HX : 0 < @basis_mass R (bb84_cvar M) V (bb84_n Pex) (bb84_k Pex) pbvX pbvZ s pbvX.
  { rewrite /basis_mass /bb84_program_basis_value /=. exact: ex_replay_pX_pos. } have HZ : 0 < @basis_mass R (bb84_cvar M) V (bb84_n Pex) (bb84_k Pex) pbvX pbvZ s pbvZ.
  { have ex_replay_pZ_pos : 0 < 1 - @replay_pX R (bb84_n Pex) (bb84_k Pex).
    { rewrite /replay_pX /Pex /= subr_gt0 invf_lt1; last by apply: ltr_wpDr; [exact: sqrtr_ge0 | exact: ltr01].
      by rewrite ltrDl sqrtr_gt0 divr_gt0 ?ltr0n ?ex_nn_gt0. } rewrite /basis_mass /bb84_program_basis_value /=. exact: ex_replay_pZ_pos. } have Hbit : 0 < @bit_mass R (bb84_cvar M) V bb84_bit_val s (bb84_bit_val false).
  { by rewrite /bit_mass eqxx invr_gt0 ltr0n. } rewrite /round_choice_weight /ex_pass_choice.
  case: ifP => _.
  - by apply: mulr_gt0; last exact: HZ; apply: mulr_gt0; [exact: HZ | exact: Hbit].
  case: ifP => _.
  - by apply: mulr_gt0; last exact: HX; apply: mulr_gt0; [exact: HX | exact: Hbit].
  by apply: mulr_gt0; last exact: HZ; apply: mulr_gt0; [exact: HX | exact: Hbit]. Qed.

Lemma ex_pass_trace_key_set : @trace_key_set V M pbvX (bb84_outcome_val None) ex_pass_trace = ex_key_sample_set.
Proof.
  apply/setP=> i; rewrite /trace_key_set /ex_key_sample_set !inE /trace_key_round /trace_detected /ex_pass_trace ffunE /ex_pass_choice.
  case Htest: (i \in ex_test_set).
  - by move: Htest; rewrite /ex_test_set inE => /andP [Hge _]; rewrite /bb84_program_basis_value /= ltnNge Hge.
  by case Hkey: (i \in ex_key_sample_set); move: Hkey; rewrite /ex_key_sample_set inE => Hkey; rewrite /bb84_program_basis_value /= Hkey. Qed.

Fact ex_pass_trace_test_set : @trace_test_set V M pbvZ (bb84_outcome_val None) ex_pass_trace = ex_test_set.
Proof.
  apply/setP=> i; rewrite /trace_test_set /ex_test_set !inE /trace_test_round /trace_detected /ex_pass_trace ffunE /ex_pass_choice.
  case Htest: (i \in ex_test_set).
  - by move: Htest; rewrite /ex_test_set inE => ->; rewrite /bb84_program_basis_value /=.
  case Hkey: (i \in ex_key_sample_set).
  - move: Hkey; rewrite /ex_key_sample_set inE => Hlt.
    have Hnot_ge : ~~ (nn <= nat_of_ord i)%N by rewrite -ltnNge.
    by rewrite /bb84_program_basis_value /= (negbTE Hnot_ge).
  by move: Htest; rewrite /ex_test_set inE => Htest; rewrite /bb84_program_basis_value /= Htest. Qed.

Definition ex_M_pos : (0 < bb84_round_limit Pex)%N.
Proof.
  by rewrite /Pex /bb84_round_limit /= /ex_round_limit muln_gt0 addn_gt0 ex_nn_gt0. Defined.

Corollary bb84_secure_example (rhofull : forall (EA : @adversary R L HL V Eve) (xi : @cq_state R L HL (bb84_cvar M) V),
       'M[@hermitian.C R]_(bb84_full_string_count Pex * dim ('H[HL]_Ereg)
          * bb84_full_string_count Pex)) (Hden1 : forall (EA : @adversary R L HL V Eve) (xi : @cq_state R L HL (bb84_cvar M) V),
       rhofull EA xi \is den1mx) (Hcorr : @sigdet_correspondence R Pex 1 ex_device LE HE rhofull Hden1)
    (Hdm : @delayed_measurement_hmin_sigdet R Pex 1 ex_device LE HE) : forall (EA : @adversary R L HL V Eve) (xi_init : state),
  cq_wf xi_init -> let xi_out := @bb84_eval R Pex 1 LE HE bb84_register_index HB ex_device Eve EA xi_init in let p_abort :=
    @run_abort_prob R L HL (bb84_cvar M) V (@BVabort M) bb84_bool_val xi_out in let p_pass :=
    @run_pass_prob R L HL (bb84_cvar M) V (@BVabort M) bb84_bool_val xi_out in let p_mismatch :=
    @run_output_mismatch_prob R L HL (bb84_cvar M) V (@BVS M) (@BVSh M) (@BVabort M) bb84_bool_val xi_out in
  forall (acc rej : 'Idx[HL]_(bb84_signal_reg (Ordinal ex_M_pos))), acc != rej ->

  [/\ (forall (h : @run_history V M) (s : cstore), @bb84_branch_shape R Pex 1 ex_device h s), p_abort + p_pass = 1 & @eps_secure R L HL Zl
        (bb84_signal_reg (Ordinal ex_M_pos) :|: (Fl :|: (Ereg :|: Ppub))) p_mismatch (bb84_eps_c Pex)
        (@bb84_rhoZFbEpub_readout_prog R Pex 1 ex_device LE HE EA xi_init (bb84_signal_reg (Ordinal ex_M_pos)) acc rej)
        ex_eps_s p_abort ex_eps_tot].
Proof.
  have Heps_c34 : bb84_eps_c Pex = (((2 ^ 34)%:R : R)^-1)%R by rewrite Pex_eps_c /ex_eps_c /ex_tag_bits.
  have Htag34 : cd_tag_count ex_device = (2 ^ 34)%N by rewrite /ex_device /= /ex_tag_count /ex_tag_bits.
  exact: (@bb84_secure_protocol_pow2 R Pex 1 ex_device LE HE rhofull Hden1 Hcorr Hdm ex_nn_gt0 ex_nn_gt0 (Ordinal ex_M_pos) 34 Heps_c34 Htag34 ex_eps_s ex_eps_tot ex_eps_total_budget ex_eps_s_range ex_key_length_sup). Qed.

Corollary bb84_branch_shape_example : forall (h : @run_history V M) (s : cstore), @bb84_branch_shape R Pex 1 ex_device h s.
Proof. move=> h s; exact: bb84_final_store_branch_shape. Qed.

Corollary bb84_partition_example : forall (EA : @adversary R L HL V Eve) (xi_init : state), cq_wf xi_init -> let xi_out := @bb84_eval R Pex
    1 LE HE bb84_register_index HB ex_device Eve EA xi_init in let p_abort := @run_abort_prob R L HL (bb84_cvar M) V (@BVabort M)
    bb84_bool_val xi_out in let p_pass := @run_pass_prob R L HL (bb84_cvar M) V (@BVabort M) bb84_bool_val xi_out in p_abort + p_pass = 1.
Proof. exact: (@bb84_partition_protocol R Pex 1 ex_device LE HE). Qed.

Corollary bb84_correct_example : forall (EA : @adversary R L HL V Eve) (xi_init : state), cq_wf xi_init -> let xi_out := @bb84_eval R Pex 1
    LE HE bb84_register_index HB ex_device Eve EA xi_init in let p_mismatch := @run_output_mismatch_prob R L HL (bb84_cvar M) V (@BVS M)
    (@BVSh M) (@BVabort M) bb84_bool_val xi_out in @eps_correct R p_mismatch (bb84_eps_c Pex).
Proof. exact: (@bb84_correct_protocol R Pex 1 ex_device LE HE). Qed.

End SecureExample.

End InstanceScaffold.

Section Reachability.

Import MxLownerOrder.
Import VectorInternalTheory.
Local Open Scope qkd_scope.
Local Open Scope lfun_scope.
Variable R : realType.
Notation C := (@hermitian.C R).
Notation chsType := (@chsType R).
Variables (LE : finType) (HE : LE -> chsType).

Opaque nn ex_round_limit exlen Pex.

Notation M := (bb84_round_limit (Pex R)).
Notation HB := (@bb84_register_space R (Pex R) 1 (ex_device R)).
Notation L := (bb84_label M LE bb84_register_index).
Notation HL := (bb84_label_space HE HB).
Notation V := (bb84_val M (bb84_n (Pex R)) (bb84_l (Pex R)) (cd_ir_bits (ex_device R)) (cd_vseed_count (ex_device R))
  (cd_tag_count (ex_device R)) (cd_paseed_count (ex_device R))).
Notation state := (@cq_state R L HL (bb84_cvar M) V).
Notation Eve := (bb84_Eve (Pex R) LE).

Notation nP := (bb84_n (Pex R)).
Notation QtolP := (bb84_Qtol (Pex R)).
Notation kP := (bb84_k (Pex R)).
Notation lP := (bb84_l (Pex R)).
Notation ecP := (cd_ir_bits (ex_device R)).
Notation vsP := (cd_vseed_count (ex_device R)).
Notation tgP := (cd_tag_count (ex_device R)).
Notation psP := (cd_paseed_count (ex_device R)).

Notation basisX := (@bb84_basis_bool_val M nP lP ecP vsP tgP psP false).
Notation basisZ := (@bb84_basis_bool_val M nP lP ecP vsP tgP psP true).
Notation outEmpty := (@bb84_outcome_val M nP lP ecP vsP tgP psP None).
Notation vbit := (@bb84_bit_val M nP lP ecP vsP tgP psP).
Notation vread := (@bb84_read_bit M nP lP ecP vsP tgP psP).
Notation unif_nsubset_mass := (@bb84_unif_nsubset_mass R M nP lP ecP vsP tgP psP).
Notation unif_vseed := (@bb84_unif_vseed_mass R M nP lP ecP vsP tgP psP).
Notation unif_pseed := (@bb84_unif_pseed_mass R M nP lP ecP vsP tgP psP).
Notation Qsig := (@bb84_signal_reg M LE (fintype_ordinal__canonical__fintype_Finite 8)).

Notation Cv := (bb84_cvar M).
Notation store := (@store Cv V).

Notation a_ := (@BVa M).
Notation y_ := (@BVy M).
Notation b_ := (@BVb M).
Notation y'_ := (@BVy' M).
Notation d_ := (@BVd M).
Notation Xv := (@BVX M).
Notation Zv := (@BVZ M).
Notation Kv := (@BVK M).
Notation XA := (@BVXA M).
Notation XB := (@BVXB M).
Notation ZA := (@BVZA M).
Notation ZB := (@BVZB M).
Notation lamv := (@BVlam M).
Notation pECv := (@BVpec M).
Notation Xhatv := (@BVXhat M).
Notation gv := (@BVg M).
Notation tAv := (@BVtA M).
Notation tBv := (@BVtB M).
Notation fv := (@BVf M).
Notation Sv := (@BVS M).
Notation Shv := (@BVSh M).
Notation abortv := (@BVabort M).
Notation Pvar := (@BVP M).

Notation bot := (@bb84_bot_val M nP lP ecP vsP tgP psP).
Notation empty_transcript := (@bb84_empty_transcript_val M nP lP ecP vsP tgP psP).
Notation vbool := (@bb84_bool_val M nP lP ecP vsP tgP psP).
Notation vset := (@bb84_set_val M nP lP ecP vsP tgP psP).
Notation vset_of := (@bb84_set_of M nP lP ecP vsP tgP psP).
Notation vrat := (@bb84_error_val M nP lP ecP vsP tgP psP).
Notation tr_app_rounds := (@bb84_tr_app_rounds M nP lP ecP vsP tgP psP).
Notation tr_app_pe := (@bb84_tr_app_pe M nP lP ecP vsP tgP psP).
Notation tr_app_ec := (@bb84_tr_app_ec M nP lP ecP vsP tgP psP).
Notation tr_app_pa := (@bb84_tr_app_pa M nP lP ecP vsP tgP psP).
Notation bits_on := (@bb84_bits_on_val M nP lP ecP vsP tgP psP).
Notation test_bits_on := (@bb84_partial_bits_on_val M nP lP ecP vsP tgP psP).
Notation err_count := (@bb84_err_count_val M nP lP ecP vsP tgP psP).
Notation err_of := (@bb84_error_of M nP lP ecP vsP tgP psP).
Notation ir_pub := (bb84_ir_pub_val (cd_ir_pub (ex_device R))).
Notation ir_dec := (bb84_ir_dec_val (@cd_ir_dec R (Pex R) 1 (ex_device R))).
Notation verify_hash := (bb84_verify_hash_val (@cd_vh R (Pex R) 1 (ex_device R))).
Notation privacy_hash := (bb84_privacy_hash_val (@cd_pa R (Pex R) 1 (ex_device R))).

Notation Vfin := ((bb84_val M nP lP ecP vsP tgP psP)%type : finType).

Definition ex_reach_trace : @round_trace V M := ex_pass_trace R.
Definition ex_reach_key : Finite.sort Vfin := ex_key_sample_value R.
Definition ex_reach_vseed : Finite.sort Vfin := ex_vseed_value R.
Definition ex_reach_paseed : Finite.sort Vfin := ex_paseed_value R.
Definition ex_reach_history : @run_history V M := (ex_reach_trace, ((ex_reach_key, ex_reach_vseed), ex_reach_paseed)).

Lemma ex_cd_rho_X_false : cd_rho (ex_device R) BasisX false = @x_projective_povm2 R ord0.
Proof. by []. Qed.

Fact ex_cd_rho_Z_false : cd_rho (ex_device R) BasisZ false = delta_mx (ord0 : 'I_2) ord0.
Proof. by []. Qed.

Fact ex_cd_meas_X_false : cd_meas (ex_device R) BasisX (Some false) = @x_projective_povm2 R ord0.
Proof. by []. Qed.

Lemma ex_cd_meas_Z_false : cd_meas (ex_device R) BasisZ (Some false) = delta_mx (ord0 : 'I_2) ord0.
Proof. by []. Qed.

Fact ex_cd_ir_decE (p : 'I_(2 ^ cd_ir_bits (ex_device R))) (y : 'I_(2 ^ bb84_n (Pex R))) : @cd_ir_dec R (Pex R) 1 (ex_device R) p y = y.
Proof. by []. Qed.

Transparent Pex ex_round_limit.

Fact ex_M_gt0 : (0 < bb84_round_limit (Pex R))%N.
Proof. by rewrite /Pex /bb84_round_limit /= /ex_round_limit muln_gt0 addn_gt0 ex_nn_gt0. Qed.

Fact ex_Qtol_ge0 : 0 <= bb84_Qtol (Pex R).
Proof. by rewrite /Pex /bb84_Qtol /= invr_ge0 ler0n. Qed.

Opaque Pex ex_round_limit.

Opaque ex_device.

Lemma bb84_signal_lfun_formlf_trE (i : 'I_M) (Mx A : 'M[C]_2) : \Tr (formlf (bb84_signal_lfun HE HB i Mx) (bb84_signal_lfun HE HB i A)) =
  \tr (Mx *m A *m Mx^*t).
Proof. rewrite formlfE /lftrace !h2mx_comp h2mx_adj /bb84_signal_lfun !mx2hK. by case: (dim 'H[HL]_(bb84_signal_reg i)) / (esym (bb84_signal_reg_dim HE HB i)); rewrite !castmx_id. Qed.

Fact ex_round_factor_gt0 (i : 'I_M) : (0 : C) < \Tr (formlf (bb84_device_dev_meas HE HB i (choice_b (ex_pass_choice (R:=R) i)) (choice_y'
    (ex_pass_choice (R:=R) i))) (bb84_device_dev_rho HE HB i (choice_a (ex_pass_choice (R:=R) i)) (choice_y (ex_pass_choice (R:=R) i)))).
Proof.
have ex_tr_delta0_mul : forall (A : 'M[C]_2), \tr (delta_mx (ord0 : 'I_2) ord0 *m A) = A ord0 ord0.
{ move=> A. rewrite /mxtrace big_ord_recl big_ord_recl big_ord0 addr0 ![((delta_mx _ _) *m A) _ _]mxE.
  by rewrite !big_ord_recl !big_ord0 !addr0 !mxE /= mul1r !mul0r !addr0. } rewrite ex_pass_choice_alice_bit ex_pass_choice_bob_outcome ex_pass_choice_alice_basis ex_pass_choice_bob_basis.
  have HPxadj : (@x_projective_povm2 R ord0)^*t = @x_projective_povm2 R ord0 by have /hermmxP := psdmx_herm (@x_projective_povm2_psd R ord0).
  have HPxtr : \tr (@x_projective_povm2 R ord0) = 1 by have /den1mxP [_ /eqP ->] := @x_projective_povm2_den1 R ord0.
  have ex_px00 : (@x_projective_povm2 R ord0) ord0 ord0 = ((2%:R)^-1)%:C.
  { rewrite /x_projective_povm2 mxE /xbasis_vec2.
    by rewrite !mxE !big_ord_recl !big_ord0 !mxE /xbasis_sign2 /= addr0 conjC1 !mulr1. } case Htest: (i \in ex_test_set R).
  - rewrite (bb84_device_dev_measE (ex_device R) HE HB i BasisZ (Some false)) (bb84_device_dev_rhoE (ex_device R) HE HB i BasisZ false) bb84_signal_lfun_formlf_trE ex_cd_meas_Z_false ex_cd_rho_Z_false.
    by rewrite adjmx_delta !mul_delta_mx tr_delta_mx_ii ltr01.
  - case Hkey: (i \in ex_key_sample_set R).
    + rewrite (bb84_device_dev_measE (ex_device R) HE HB i BasisX (Some false)) (bb84_device_dev_rhoE (ex_device R) HE HB i BasisX false) bb84_signal_lfun_formlf_trE ex_cd_meas_X_false ex_cd_rho_X_false.
      by rewrite HPxadj !x_projective_povm2_idem HPxtr ltr01.
    + rewrite (bb84_device_dev_measE (ex_device R) HE HB i BasisZ (Some false)) (bb84_device_dev_rhoE (ex_device R) HE HB i BasisX false) bb84_signal_lfun_formlf_trE ex_cd_meas_Z_false ex_cd_rho_X_false.
      by rewrite adjmx_delta mxtrace_mulC mulmxA mul_delta_mx ex_tr_delta0_mul ex_px00 ltc0R invr_gt0 ltr0n. Qed.

Fact ex_identity_adversary_liftfso (Qs : {set L}) (p : V) : liftfso (ex_identity_adversary HE Qs p) = idso.
Proof. exact: liftfso1. Qed.

Fact ex_reach_h1 : forall s, (ex_initial_state HE) s \is psdlf.
Proof. move=> s; rewrite /ex_initial_state /cq_single ffunE. by case: (s == ex_initial_store R); [exact: den1lf_psd (ex_initial_lf_den1lf HE) | exact: is_psdlf]. Qed.

Fact ex_reach_h2 : forall (i : 'I_M) (a y : V), (bb84_device_dev_rho HE HB) i a y \is psdlf.
Proof. move=> i a y; exact: den1lf_psd (bb84_device_dev_rho_den1 (dev:=ex_device R) HE HB i a y). Qed.

Fact ex_reach_h3 : (0 < M)%N.
Proof. exact: ex_M_gt0. Qed.

Fact ex_reach_h4 : 0 <= QtolP.
Proof. exact: ex_Qtol_ge0. Qed.

Fact ex_reach_h5 : forall p y, (@cd_ir_dec R (Pex R) 1 (ex_device R)) p y = y.
Proof. move=> p y; exact: ex_cd_ir_decE. Qed.

Fact ex_reach_h6 : forall i : 'I_M, liftfso ((ex_identity_adversary HE) (Qsig i) empty_transcript) = idso.
Proof. move=> i; exact: ex_identity_adversary_liftfso. Qed.

Fact ex_reach_h7 : \Tr ((ex_initial_state HE) (ex_initial_store R)) = 1.
Proof. rewrite /ex_initial_state cq_single_same. exact: den1lf_trlf (ex_initial_lf_den1lf HE). Qed.

Fact ex_reach_h8 : forall i : 'I_M, (0 : C) < \Tr (formlf ((bb84_device_dev_meas HE HB) i (choice_b (ex_reach_history.1 i)) (choice_y'
    (ex_reach_history.1 i))) ((bb84_device_dev_rho HE HB) i (choice_a (ex_reach_history.1 i)) (choice_y (ex_reach_history.1 i)))).
Proof. by move=> i; rewrite -[ex_reach_history.1]/(ex_pass_trace R) /ex_pass_trace !ffunE; exact: ex_round_factor_gt0. Qed.

Fact ex_reach_h9 : forall i : 'I_M, choice_y' (ex_reach_history.1 i) != outEmpty.
Proof. by move=> i; rewrite -[ex_reach_history.1]/(ex_pass_trace R) /ex_pass_trace !ffunE ex_pass_choice_bob_outcome. Qed.

Fact ex_reach_h10 : (nP <= #|@trace_key_set V M basisX outEmpty ex_reach_history.1|)%N.
Proof. by rewrite -[ex_reach_history.1]/(ex_pass_trace R) ex_pass_trace_key_set ex_key_sample_set_card Pex_n leqnn. Qed.

Fact ex_reach_h11 : (kP <= #|@trace_test_set V M basisZ outEmpty ex_reach_history.1|)%N.
Proof. by rewrite -[ex_reach_history.1]/(ex_pass_trace R) ex_pass_trace_test_set Pex_k; exact: ex_test_set_ge. Qed.

Fact ex_reach_h12 : forall i : 'I_M, vread (choice_y (ex_reach_history.1 i)) = Some false.
Proof. by move=> i; rewrite -[ex_reach_history.1]/(ex_pass_trace R) /ex_pass_trace !ffunE ex_pass_choice_alice_bit. Qed.

Fact ex_reach_h13 : forall i : 'I_M, vread (choice_y' (ex_reach_history.1 i)) = Some false.
Proof. by move=> i; rewrite -[ex_reach_history.1]/(ex_pass_trace R) /ex_pass_trace !ffunE ex_pass_choice_bob_outcome. Qed.

Fact ex_reach_h14 : forall (i : 'I_M) (s : store), 0 < round_choice_weight R nP kP basisX basisZ vbit (ex_reach_history.1 i) s.
Proof. by move=> i s; rewrite -[ex_reach_history.1]/(ex_pass_trace R) /ex_pass_trace ffunE; exact: ex_pass_choice_weight_pos. Qed.

Fact ex_reach_h15 : 0 < unif_nsubset_mass nP (@trace_key_set V M basisX outEmpty ex_reach_history.1) ex_reach_history.2.1.1.
Proof. rewrite -[ex_reach_history.1]/(ex_pass_trace R) ex_pass_trace_key_set. by rewrite -[ex_reach_history.2.1.1]/(ex_key_sample_value R); exact: ex_key_sample_mass_pos. Qed.

Fact ex_reach_h16 : forall s : store, 0 < unif_vseed s ex_reach_history.2.1.2.
Proof. by move=> s; rewrite -[ex_reach_history.2.1.2]/(ex_vseed_value R); exact: ex_vseed_mass_pos. Qed.

Fact ex_reach_h17 : forall s : store, 0 < unif_pseed s ex_reach_history.2.2.
Proof. by move=> s; rewrite -[ex_reach_history.2.2]/(ex_paseed_value R); exact: ex_paseed_mass_pos. Qed.

Lemma bb84_secure_example_reachable_scheme : 0 < run_pass_prob abortv vbool (@bb84_eval_scheme R _ HL Cv V nP kP lP ecP M QtolP
      a_ y_ b_ y'_ d_ Qsig Xv Zv Kv XA XB ZA ZB lamv pECv Xhatv gv tAv tBv fv Sv Shv abortv Pvar basisX basisZ outEmpty bot empty_transcript
      vbool vbit vset vset_of vrat (bb84_device_dev_rho HE HB) (bb84_device_dev_meas HE HB) tr_app_rounds tr_app_pe tr_app_ec tr_app_pa
      bits_on test_bits_on err_count err_of unif_nsubset_mass ir_pub ir_dec unif_vseed verify_hash unif_pseed privacy_hash
      Eve (ex_identity_adversary HE) (ex_initial_state HE)).
Proof.
  apply: (run_pass_prob_reachable ex_reach_history (ex_initial_store R)); [ exact: ex_reach_h1 | exact: ex_reach_h2 | exact: ex_reach_h3 | exact: ex_reach_h4 | exact: ex_reach_h5 | exact: ex_reach_h6 | exact: ex_reach_h7 | exact: ex_reach_h8 | exact: ex_reach_h9 | exact: ex_reach_h10 | exact: ex_reach_h11 | exact: ex_reach_h12 | exact: ex_reach_h13 | exact: ex_reach_h14 | exact: ex_reach_h15 | exact: ex_reach_h16 | exact: ex_reach_h17 ]. Qed.

Lemma bb84_secure_example_reachable : 0 < @run_pass_prob R L HL (bb84_cvar M) V (@BVabort M) bb84_bool_val
    (@bb84_eval R (Pex R) 1 LE HE bb84_register_index HB (ex_device R) Eve (ex_identity_adversary HE) (ex_initial_state HE)).
Proof.
  have evalE : @bb84_eval R (Pex R) 1 LE HE bb84_register_index HB (ex_device R) Eve (ex_identity_adversary HE) (ex_initial_state HE) = bb84_eval_scheme_state (ex_identity_adversary HE) (ex_initial_state HE).
  { by rewrite /bb84_eval /bb84_program /bb84_eval_scheme_state /bb84_eval_scheme /bb84_program_scheme /bb84_program_device_rho /bb84_device_dev_rho /bb84_program_device_meas /bb84_device_dev_meas /bb84_program_basis_value /bb84_basis_value /bb84_program_basis_of_value /bb84_basis_of_value. } by rewrite evalE /bb84_eval_scheme_state; exact: bb84_secure_example_reachable_scheme. Qed.

End Reachability.
