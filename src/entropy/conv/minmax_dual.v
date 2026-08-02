(* -------------------------------------------------------------------- *)
(* minmax_dual.v — Non-smooth min/max duality for pure states           *)
(* -------------------------------------------------------------------- *)
(* Module: entropy.conv.minmax_dual                           *)
(* Source: Tomamichel, 'A Framework for Non-Asymptotic Quantum          *)
(*   Information Theory' (PhD thesis, arXiv:1203.2142), Lemma 4.1        *)
(*   — tex lm:min-max/dual — math: pure ρ_ABC ⇒ H_max(A|B)_ρ = -H_min(A|C)_ρ. *)
(* -------------------------------------------------------------------- *)
(* Statement.                                            *)
(*                                                                      *)
(* Publicly the lemma is stated over ambient set-labelled systems.      *)
(* Matrix/product-coordinate reasoning belongs only in proof-core       *)
(* bridges, not in the canonical Tomamichel theorem surface.                 *)
(*                                                                      *)
(* This file is the canonical Coq surface for Tomamichel's min/max duality.   *)
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
  cpo mxpred extnum ctopology svd mxnorm hspace hspace_extra prodvect tensor.
From quantum.dirac Require Import hstensor.

Import Order.TTheory GRing.Theory Num.Theory Num.Def MxLownerOrder.
Import VectorInternalTheory.

(* --- FVQKD imports --- *)
From utils Require Import exports.
From entropy Require Import def prop pre util.
From entropy.conv Require Import minmax.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Open Scope ring_scope.
Local Open Scope lfun_scope.

Section FvqkdReal.
Variable R : realType.
Notation C := (@hermitian.C R).
Notation chsType := (@chsType R).

(* ================================================================== *)
(* Non-smooth min/max duality for pure states                           *)
(* Tomamichel thesis (arXiv:1203.2142), Lemma 4.1 — tex lm:min-max/dual. *)
(* math: For pure ρ_{ABC} ∈ S_≤(H_{ABC}),                               *)
(*   H_max(A|B)_ρ = - H_min(A|C)_ρ.                                     *)
(* Formalized on the AB and AC marginals of ρ_{ABC}.                    *)
(* ================================================================== *)

Section MinMaxDual.
Variables (L : finType) (H : L -> chsType).
Variables (A B C0 : {set L}).
Hypotheses (disAB : [disjoint A & B])
           (disAC : [disjoint A & C0])
           (disBC : [disjoint B & C0]).
Variables (Cp Cpp : {set L}).
Hypotheses (disA_Cp : [disjoint A & Cp])
           (disA_Cpp : [disjoint A & Cpp])
           (disB_Cp : [disjoint B & Cp])
           (disB_Cpp : [disjoint B & Cpp])
           (disC_Cp : [disjoint C0 & Cp])
           (disC_Cpp : [disjoint C0 & Cpp])
           (disCp_Cpp : [disjoint Cp & Cpp]).
Hypothesis dimA_Cp : dim 'H[H]_A = dim 'H[H]_Cp.
Hypothesis dimC_Cp_Cpp :
  (dim 'H[H]_C0 * dim 'H[H]_Cp <= dim 'H[H]_Cpp)%N.
Hypothesis dimB_Cpp : (dim 'H[H]_B <= dim 'H[H]_Cpp)%N.

Notation S_ABC := (A :|: B :|: C0).

(* path: entropy:minmax_dual -> entropy:smooth_iso_hmax -> *)
(*   entropy:entropy_data_proc -> *)
(*   bb84:bb84_secret *)
Lemma minmax_dual (rhoABC : 'F[H]_S_ABC) :
  rhoABC \is denlf ->
  \Rank rhoABC = 1%N ->
  hmaxE B
    (@ptrace_cast3C R L H A B C0 disAC disBC rhoABC) =
  oppe (hminE C0
    (@ptrace_cast3B R L H A B C0 disAB disBC rhoABC)).
Proof.
  (* Tomamichel proof route:
     expand Hmax by df:max-entropy and Hmin through min_omni; use
     Uhlmann's theorem to identify purifications across C -> C'C'';
     use partial-trace fidelity monotonicity for the two inequalities. *)
  move=> Hrho_den Hrho_rank.
  pose rhoAB : 'F[H]_(A :|: B) :=
    @ptrace_cast3C R L H A B C0 disAC disBC rhoABC.
  pose rhoAC : 'F[H]_(A :|: C0) :=
    @ptrace_cast3B R L H A B C0 disAB disBC rhoABC.
  have Hrho_psd : rhoABC \is psdlf := denlf_psd Hrho_den.
  have Hrho_tr_le : @complex.Re R (\Tr rhoABC) <= 1.
  { have Hreal : \Tr rhoABC \is Num.real := ger0_real (psdlf_trlf Hrho_psd).
    by move: (denlf_trlf Hrho_den); rewrite -(RRe_real Hreal) lecR. }
  have HrhoAB_psd : rhoAB \is psdlf.
  { rewrite /rhoAB.
    exact: ptrace_cast_gen_psdlf. }
  have HrhoAC_psd : rhoAC \is psdlf.
  { rewrite /rhoAC.
    exact: ptrace_cast_gen_psdlf. }
  have Htr_ptrace3C :
      \Tr (@ptrace_cast3C R L H A B C0 disAC disBC rhoABC) =
      \Tr rhoABC.
  { rewrite /ptrace_cast3C /ptrace_cast_gen castlf_trlfE.
    have /cptpP [_ /tpmapP Htp] := @ptraceso_qc R L H C0 S_ABC.
    exact: Htp. }
  have Htr_ptrace3B :
      \Tr (@ptrace_cast3B R L H A B C0 disAB disBC rhoABC) =
      \Tr rhoABC.
  { rewrite /ptrace_cast3B /ptrace_cast_gen castlf_trlfE.
    have /cptpP [_ /tpmapP Htp] := @ptraceso_qc R L H B S_ABC.
    exact: Htp. }
  have HrhoAB_tr_le : @complex.Re R (\Tr rhoAB) <= 1
    by rewrite /rhoAB Htr_ptrace3C.
  have HrhoAC_tr_le : @complex.Re R (\Tr rhoAC) <= 1
    by rewrite /rhoAC Htr_ptrace3B.
  have Hrho_ne0 : rhoABC != 0.
  { apply/eqP=> Heq0.
    move: Hrho_rank.
    by rewrite Heq0 ranklf0. }
  have Hrho_tr_pos_C : (0 : C) < \Tr rhoABC.
  { rewrite lt_def psdlf_trlf // andbT.
    apply/negP=> /eqP Htr0.
    apply/negP: Hrho_ne0; rewrite negbK.
    have Hrho_ge0 : 0 ⊑ rhoABC by move: Hrho_psd; rewrite psdlfE.
    apply/trlf0_eq0.
    exact: (conj Hrho_ge0 Htr0). }
  have Hrho_tr_pos_R : 0 < @complex.Re R (\Tr rhoABC).
  { have Hreal : \Tr rhoABC \is Num.real := ger0_real (psdlf_trlf Hrho_psd).
    by move: Hrho_tr_pos_C; rewrite -{1}(RRe_real Hreal) ltcR. }
  have HrhoAB_den : rhoAB \is denlf.
  { apply/denlfP; split=> //.
    have Hreal : \Tr rhoAB \is Num.real := ger0_real (psdlf_trlf HrhoAB_psd).
    by rewrite -(RRe_real Hreal) lecR. }
  have HrhoAB_tr_pos_R : 0 < @complex.Re R (\Tr rhoAB)
    by rewrite /rhoAB Htr_ptrace3C.
  have HrhoAC_den : rhoAC \is denlf.
  { apply/denlfP; split=> //.
    have Hreal : \Tr rhoAC \is Num.real := ger0_real (psdlf_trlf HrhoAC_psd).
    by rewrite -(RRe_real Hreal) lecR. }
  have HrhoAB_hmaxE_fin :
      hmaxE B rhoAB = (hmax B rhoAB)%:E
    := @hmaxE_EFin R L H (A :|: B) B rhoAB
        HrhoAB_psd HrhoAB_tr_le HrhoAB_tr_pos_R.
  have Hmin_omni :=
    @min_omni R L H A C0 Cp Cpp
      disAC disA_Cp disA_Cpp disCp_Cpp
      dimA_Cp dimC_Cp_Cpp rhoAC HrhoAC_den.
  have disACp_Cpp : [disjoint A :|: Cp & Cpp]
    by rewrite disjointUX disA_Cpp disCp_Cpp.
  have disA_CpCpp : [disjoint A & Cp :|: Cpp]
    by rewrite disjointXU disA_Cp disA_Cpp.
  pose gamma_ACp : 'F[H]_(A :|: Cp) :=
    @gamma_state R L H A Cp dimA_Cp.
  have Hgamma_ACp_den1 : gamma_ACp \is den1lf :=
    @gamma_state_den1 R L H A Cp disA_Cp dimA_Cp.
  have Hgamma_ACp_rank1 : \Rank gamma_ACp = 1%N :=
    @gamma_state_rank1 R L H A Cp disA_Cp dimA_Cp.
  have Hgamma_ACp_den : gamma_ACp \is denlf :=
    den1lf_den Hgamma_ACp_den1.
  pose pi_A : 'F[H]_A := ((dim 'H[H]_A)%:R^-1)%:C *: (\1 : 'F[H]_A).
  have Hpi_A_psd : pi_A \is psdlf.
  { rewrite /pi_A.
    apply: psdlfZ; first by rewrite lecR invr_ge0.
    by rewrite qualifE h2mx1; exact: psdmx1. }
  have Hpi_A_tr1 : \Tr pi_A = 1.
  { have Hdim_neq0 : ((dim 'H[H]_A)%:R : R) != 0.
    { apply: lt0r_neq0.
      by rewrite ltr0n dim_proper. }
    rewrite /pi_A linearZ /= /lftrace h2mx1 mxtrace1.
    rewrite -natrC -rmorphM /= mulrC (mulfV Hdim_neq0).
    exact: rmorph1. }
  have Hpi_A_den1 : pi_A \is den1lf
    by apply/den1lfP; split.
  have HsigmaB_pur :
      forall sigma_B : 'F[H]_B,
        sigma_B \is den1lf ->
        exists phi_BCpp : 'F[H]_(B :|: Cpp),
          phi_BCpp \is den1lf /\
          \Rank phi_BCpp = 1%N /\
          ptrace_cast disB_Cpp phi_BCpp = sigma_B.
  { move=> sigma_B Hsigma_B_den1.
    exact: (@pur_exists_den1 R L H B Cpp disB_Cpp sigma_B
      dimB_Cpp Hsigma_B_den1). }
  have Hmax_target_pur :
      forall sigma_B : 'F[H]_B,
        sigma_B \is den1lf ->
        exists (phi_BCpp : 'F[H]_(B :|: Cpp))
               (tau_star : 'F[H]_Cpp)
               (target_star : 'F[H]_(A :|: Cp :|: Cpp)),
          phi_BCpp \is den1lf /\
          \Rank phi_BCpp = 1%N /\
          ptrace_cast disB_Cpp phi_BCpp = sigma_B /\
          tau_star \is den1lf /\
          tau_star = ptrace_castl disB_Cpp phi_BCpp /\
          target_star \is den1lf /\
          target_star =
            ((gamma_ACp \O tau_star) : 'F[H]_(A :|: Cp :|: Cpp)) /\
          ptrace_cast disACp_Cpp target_star = gamma_ACp.
  { move=> sigma_B Hsigma_B_den1.
    have [phi_BCpp [Hphi_den1 [Hphi_rank Hphi_ptr]]] :=
      HsigmaB_pur sigma_B Hsigma_B_den1.
    pose tau_star : 'F[H]_Cpp := ptrace_castl disB_Cpp phi_BCpp.
    have Htau_star_den1 : tau_star \is den1lf.
    { apply/den1lfP; split.
      - rewrite /tau_star.
        apply: ptrace_castl_psdlf.
        exact: den1lf_psd Hphi_den1.
      - rewrite /tau_star /ptrace_castl /ptrace_cast_gen castlf_trlfE.
        have /cptpP [_ /tpmapP Htp] :=
          @ptraceso_qc R L H B (B :|: Cpp).
        by rewrite Htp (den1lf_trlf Hphi_den1). }
    pose target_star : 'F[H]_(A :|: Cp :|: Cpp) :=
      gamma_ACp \O tau_star.
    have Htau_star_psd : tau_star \is psdlf :=
      den1lf_psd Htau_star_den1.
    have Hgamma_ACp_le : (0 : 'F[H]_(A :|: Cp)) ⊑ gamma_ACp.
    { move: (den1lf_psd Hgamma_ACp_den1).
      by rewrite psdlfE. }
    have Htau_star_le : (0 : 'F[H]_Cpp) ⊑ tau_star.
    { by move: Htau_star_psd; rewrite psdlfE. }
    have Htarget_star_psd : target_star \is psdlf.
    { have -> :
          target_star =
          ((gamma_ACp \⊗ tau_star) : 'F[H]_(A :|: Cp :|: Cpp)).
      { apply: to_Fnd_inj.
        by rewrite /target_star (sdotFT _ _ disACp_Cpp) to_Fnd_tenE. }
      rewrite psdlfE.
      exact: tenf_ge0 disACp_Cpp Hgamma_ACp_le Htau_star_le. }
    have Htarget_star_tr1 : \Tr target_star = 1.
    { rewrite /target_star (lftrace_sdot_disj _ _ disACp_Cpp).
      by rewrite (den1lf_trlf Hgamma_ACp_den1)
        (den1lf_trlf Htau_star_den1) mul1r. }
    have Htarget_star_den1 : target_star \is den1lf.
    { by apply/den1lfP; split. }
    have Htarget_star_ptr :
        ptrace_cast disACp_Cpp target_star = gamma_ACp.
    { apply: h2mx_inj.
      rewrite /target_star (h2mx_ptrace_cast_ptrace2 disACp_Cpp).
      have -> :
          h2mx ((gamma_ACp \O tau_star) :
            'F[H]_(A :|: Cp :|: Cpp)) =
          h2mx ((gamma_ACp \⊗ tau_star) :
            'F[H]_(A :|: Cp :|: Cpp)).
      { congr h2mx.
        apply: to_Fnd_inj.
        by rewrite (sdotFT _ _ disACp_Cpp) to_Fnd_tenE. }
      rewrite h2mx_tenf.
      pose UU := @tenv_mxU R L H (A :|: Cp) Cpp.
      have HUadj : UU^*t \is unitarymx :=
        tenv_mxU_adj_unitarymx disACp_Cpp.
      have Uadj_mul_U : UU^*t *m UU = 1%:M
        by have := unitarymxK HUadj; rewrite adjmxK.
      have Htau_tr1_mx : \tr (h2mx tau_star) = 1
        by move: (den1lf_trlf Htau_star_den1); rewrite /lftrace.
      rewrite !mulmxA Uadj_mul_U mul1mx -mulmxA Uadj_mul_U mulmx1.
      rewrite ptrace_tensmx h2mxZ_lf /lftrace.
      by rewrite Htau_tr1_mx scale1r. }
    exists phi_BCpp, tau_star, target_star.
    by do 7 split=> //. }
  have HdimC_CpCpp : (dim 'H[H]_C0 <= dim 'H[H]_(Cp :|: Cpp))%N.
  { rewrite (tenv_dim disCp_Cpp).
    have HdimCp_ge1 : (1 <= dim 'H[H]_Cp)%N := dim_proper.
    have Hleft : (dim 'H[H]_C0 <= dim 'H[H]_C0 * dim 'H[H]_Cp)%N.
    { rewrite -{1}(muln1 (dim 'H[H]_C0)).
      exact: leq_mul (leqnn _) HdimCp_ge1. }
    have Hright :
        (dim 'H[H]_C0 * dim 'H[H]_Cp <=
         dim 'H[H]_Cp * dim 'H[H]_Cpp)%N.
    { have Hcpp_le :
          (dim 'H[H]_Cpp <= dim 'H[H]_Cp * dim 'H[H]_Cpp)%N.
      { rewrite -{1}(mul1n (dim 'H[H]_Cpp)).
        exact: leq_mul HdimCp_ge1 (leqnn _). }
      exact: leq_trans dimC_Cp_Cpp Hcpp_le. }
    exact: leq_trans Hleft Hright. }
  have disB_CpCpp : [disjoint B & Cp :|: Cpp]
    by rewrite disjointXU disB_Cp disB_Cpp.
  have disAB_CpCpp_g : [disjoint A :|: B & Cp :|: Cpp]
    by rewrite disjointUX disA_CpCpp disB_CpCpp.
  have disCp_B_g : [disjoint Cp & B] by rewrite disjoint_sym.
  have disACp_B_g : [disjoint A :|: Cp & B]
    by rewrite disjointUX disAB disCp_B_g.
  have disACp_BCpp_g : [disjoint A :|: Cp & B :|: Cpp]
    by rewrite disjointXU disACp_B_g disACp_Cpp.
  have disACpB_Cpp_g : [disjoint A :|: Cp :|: B & Cpp]
    by rewrite disjointUX disACp_Cpp disB_Cpp.
  have disCpp_B_g : [disjoint Cpp & B] by rewrite disjoint_sym.
  have disACpCpp_B_g : [disjoint A :|: Cp :|: Cpp & B]
    by rewrite disjointUX disACp_B_g disCpp_B_g.
  have eqACp_BCpp_AB_CpCpp :
      A :|: Cp :|: (B :|: Cpp) = A :|: B :|: (Cp :|: Cpp).
  { apply/setP=> x.
    rewrite !inE.
    by case: (x \in A); case: (x \in B);
      case: (x \in Cp); case: (x \in Cpp). }
  have eqACpB_Cpp_AB_CpCpp_g :
      A :|: Cp :|: B :|: Cpp = A :|: B :|: (Cp :|: Cpp).
  { apply/setP=> x.
    rewrite !inE.
    by case: (x \in A); case: (x \in B);
      case: (x \in Cp); case: (x \in Cpp). }
  have eqACpCpp_B_AB_CpCpp_g :
      A :|: Cp :|: Cpp :|: B = A :|: B :|: (Cp :|: Cpp).
  { apply/setP=> x.
    rewrite !inE.
    by case: (x \in A); case: (x \in B);
      case: (x \in Cp); case: (x \in Cpp). }
  have Hmax_target_full :
      forall sigma_B : 'F[H]_B,
        sigma_B \is den1lf ->
        exists (phi_BCpp : 'F[H]_(B :|: Cpp))
               (tau_star : 'F[H]_Cpp)
               (target_star : 'F[H]_(A :|: Cp :|: Cpp))
               (target_full : 'F[H]_(A :|: B :|: (Cp :|: Cpp))),
          phi_BCpp \is den1lf /\
          \Rank phi_BCpp = 1%N /\
          ptrace_cast disB_Cpp phi_BCpp = sigma_B /\
          tau_star \is den1lf /\
          target_star \is den1lf /\
          target_star =
            ((gamma_ACp \O tau_star) : 'F[H]_(A :|: Cp :|: Cpp)) /\
          target_full \is den1lf /\
          \Rank target_full = 1%N /\
          ptrace_cast disAB_CpCpp_g target_full =
            (pi_A \O sigma_B : 'F[H]_(A :|: B)) /\
          ptrace_cast disACpCpp_B_g
            (castlf (esym eqACpCpp_B_AB_CpCpp_g,
                     esym eqACpCpp_B_AB_CpCpp_g) target_full) =
            target_star.
  { move=> sigma_B Hsigma_B_den1.
    have [phi_BCpp [tau_star [target_star Htarget]]]
      := Hmax_target_pur sigma_B Hsigma_B_den1.
    case: Htarget => Hphi_den1 [Hphi_rank [Hphi_ptr
      [Htau_den1 [Htau_eq [Htarget_den1 [Htarget_eq Htarget_ptr]]]]]].
    pose target0 : 'F[H]_(A :|: Cp :|: (B :|: Cpp)) :=
      gamma_ACp \O phi_BCpp.
    pose eqACp_BCpp_assoc := finset.setUA (A :|: Cp) B Cpp.
    pose target1 : 'F[H]_(A :|: Cp :|: B :|: Cpp) :=
      castlf (eqACp_BCpp_assoc, eqACp_BCpp_assoc) target0.
    pose target_full : 'F[H]_(A :|: B :|: (Cp :|: Cpp)) :=
      castlf (eqACpB_Cpp_AB_CpCpp_g, eqACpB_Cpp_AB_CpCpp_g) target1.
    have Hphi_psd : phi_BCpp \is psdlf := den1lf_psd Hphi_den1.
    have Hgamma_ACp_le : (0 : 'F[H]_(A :|: Cp)) ⊑ gamma_ACp.
    { move: (den1lf_psd Hgamma_ACp_den1).
      by rewrite psdlfE. }
    have Hphi_le : (0 : 'F[H]_(B :|: Cpp)) ⊑ phi_BCpp.
    { by move: Hphi_psd; rewrite psdlfE. }
    have Htarget0_psd : target0 \is psdlf.
    { have -> :
          target0 =
          ((gamma_ACp \⊗ phi_BCpp) :
            'F[H]_(A :|: Cp :|: (B :|: Cpp))).
      { apply: to_Fnd_inj.
        by rewrite /target0 (sdotFT _ _ disACp_BCpp_g) to_Fnd_tenE. }
      rewrite psdlfE.
      exact: tenf_ge0 disACp_BCpp_g Hgamma_ACp_le Hphi_le. }
    have Htarget0_tr1 : \Tr target0 = 1.
    { rewrite /target0 (lftrace_sdot_disj _ _ disACp_BCpp_g).
      by rewrite (den1lf_trlf Hgamma_ACp_den1)
        (den1lf_trlf Hphi_den1) mul1r. }
    have Htarget1_psd : target1 \is psdlf.
    { rewrite /target1.
      exact: castlf_psdlf Htarget0_psd. }
    have Htarget_full_psd : target_full \is psdlf.
    { rewrite /target_full.
      exact: castlf_psdlf Htarget1_psd. }
    have Htarget_full_den1 : target_full \is den1lf.
    { apply/den1lfP; split.
      - exact: Htarget_full_psd.
      - by rewrite /target_full /target1 !castlf_trlfE Htarget0_tr1. }
    have Htarget0_rank : \Rank target0 = 1%N.
    { rewrite /target0.
      rewrite (sdotF_to_tenF disACp_BCpp_g gamma_ACp phi_BCpp).
      rewrite /lfrank h2mx_tenf.
      pose U := @tenv_mxU R L H (A :|: Cp) (B :|: Cpp).
      have HUadj : U^*t \is unitarymx :=
        tenv_mxU_adj_unitarymx disACp_BCpp_g.
      rewrite -/U (mxrank_mulmxU _ HUadj).
      rewrite -[U]adjmxK (mxrank_mulUCmx _ HUadj).
      by rewrite rank_tens -/(lfrank gamma_ACp) -/(lfrank phi_BCpp)
        Hgamma_ACp_rank1 Hphi_rank. }
    have Htarget_full_rank : \Rank target_full = 1%N.
    { rewrite /target_full /target1 /lfrank !h2mx_castlf !mxrank_cast.
      exact: Htarget0_rank. }
    pose target_ACpB : 'F[H]_(A :|: Cp :|: B) :=
      ptrace_cast3C disACp_Cpp disB_Cpp target1.
    have Htarget_ACpB :
        target_ACpB =
        (gamma_ACp \O sigma_B : 'F[H]_(A :|: Cp :|: B)).
    { rewrite /target_ACpB /target1 /target0.
      rewrite (@ptrace_cast3C_sdot_right R L H (A :|: Cp) B Cpp
        disACp_B_g disACp_Cpp disB_Cpp gamma_ACp phi_BCpp).
      by rewrite Hphi_ptr. }
    have Htarget_AB :
        ptrace_cast3B disA_Cp disCp_B_g target_ACpB =
        (pi_A \O sigma_B : 'F[H]_(A :|: B)).
    { rewrite Htarget_ACpB.
      rewrite (ptrace_cast3B_sdot_mid disA_Cp disCp_B_g disAB).
      by rewrite /pi_A gamma_state_ptrace. }
    pose target_ACpCpp : 'F[H]_(A :|: Cp :|: Cpp) :=
      ptrace_cast3B disACp_B_g disB_Cpp target1.
    have Htarget_ACpCpp : target_ACpCpp = target_star.
    { rewrite /target_ACpCpp /target1 /target0.
      rewrite (@ptrace_cast3B_sdot_right R L H (A :|: Cp) B Cpp
        disACp_B_g disB_Cpp disACp_Cpp gamma_ACp phi_BCpp).
      by rewrite -Htau_eq -Htarget_eq. }
    have Htarget_full_ptr :
        ptrace_cast disAB_CpCpp_g target_full =
        (pi_A \O sigma_B : 'F[H]_(A :|: B)).
    { rewrite -Htarget_AB.
      rewrite /target_full /target_ACpB.
      rewrite /ptrace_cast3B /ptrace_cast3C /ptrace_cast /ptrace_cast_gen.
      have Hcomp_trace :=
        congr1
          (fun F : 'SO[H]_(A :|: Cp :|: B :|: Cpp,
             (((A :|: Cp :|: B :|: Cpp) :\: Cpp) :\: Cp)) =>
             F target1)
          (@ptraceso_comp R L H Cp Cpp (A :|: Cp :|: B :|: Cpp)).
      move: Hcomp_trace.
      rewrite comp_soE castsoE /= castlf_id.
      move=> Hcomp_trace.
      have eq_res_after_Cpp :
          ((A :|: Cp :|: B :|: Cpp) :\: Cpp) :\: Cp =
          (A :|: Cp :|: B) :\: Cp
        by rewrite (setDU_r disACpB_Cpp_g).
      have eq_res_full :
          (A :|: Cp :|: B :|: Cpp) :\: (Cp :|: Cpp) =
          (A :|: B :|: (Cp :|: Cpp)) :\: (Cp :|: Cpp)
        by rewrite eqACpB_Cpp_AB_CpCpp_g.
      have eq_trace_full :
          (A :|: Cp :|: B :|: Cpp) :\: (Cp :|: Cpp) =
          (A :|: Cp :|: B :|: Cpp) :\: (Cpp :|: Cp).
      { by rewrite (finset.setUC Cp Cpp). }
      have Htrace_full_cast :
          \Tr_(Cp :|: Cpp) target1 =
          castlf (esym eq_trace_full, esym eq_trace_full)
            (\Tr_(Cpp :|: Cp) target1).
      { case: _ / (finset.setUC Cp Cpp) in eq_trace_full *.
        by rewrite (eq_irrelevance eq_trace_full erefl) castlf_id. }
      rewrite (ptracelf_castlf_eq eqACpB_Cpp_AB_CpCpp_g eq_res_full).
      rewrite Htrace_full_cast.
      rewrite (eq_irrelevance (setDU3_C disACp_Cpp disB_Cpp)
        (setDU_r disACpB_Cpp_g)).
      rewrite (ptracelf_castlf_eq (setDU_r disACpB_Cpp_g) eq_res_after_Cpp).
      rewrite Hcomp_trace.
      rewrite !castlf_comp.
      by congr (castlf (_, _) _); exact: eq_irrelevance. }
    have Htarget_full_ptr_star :
        ptrace_cast disACpCpp_B_g
          (castlf (esym eqACpCpp_B_AB_CpCpp_g,
                   esym eqACpCpp_B_AB_CpCpp_g) target_full) =
        target_star.
    { rewrite -Htarget_ACpCpp.
      rewrite /target_full /target_ACpCpp.
      rewrite /ptrace_cast3B /ptrace_cast /ptrace_cast_gen.
      have eqS :
          A :|: Cp :|: B :|: Cpp = A :|: Cp :|: Cpp :|: B.
      { apply/setP=> x.
        rewrite !inE.
        by case: (x \in A); case: (x \in Cp);
          case: (x \in B); case: (x \in Cpp). }
      have Hcast :
          castlf (esym eqACpCpp_B_AB_CpCpp_g,
                  esym eqACpCpp_B_AB_CpCpp_g)
            (castlf (eqACpB_Cpp_AB_CpCpp_g,
                     eqACpB_Cpp_AB_CpCpp_g) target1) =
          castlf (eqS, eqS) target1.
      { rewrite castlf_comp.
        by congr (castlf (_, _) _); exact: eq_irrelevance. }
      rewrite Hcast.
      have eq_res :
          (A :|: Cp :|: B :|: Cpp) :\: B =
          (A :|: Cp :|: Cpp :|: B) :\: B
        by rewrite eqS.
      rewrite (ptracelf_castlf_eq eqS eq_res).
      rewrite castlf_comp.
      by congr (castlf (_, _) _); exact: eq_irrelevance. }
    exists phi_BCpp, tau_star, target_star, target_full.
    split; first exact: Hphi_den1.
    split; first exact: Hphi_rank.
    split; first exact: Hphi_ptr.
    split; first exact: Htau_den1.
    split; first exact: Htarget_den1.
    split; first exact: Htarget_eq.
    split; first exact: Htarget_full_den1.
    split; first exact: Htarget_full_rank.
    split; first exact: Htarget_full_ptr.
    exact: Htarget_full_ptr_star. }
  have disAC_B : [disjoint A :|: C0 & B].
  { have disCB : [disjoint C0 & B] by rewrite disjoint_sym.
    by rewrite disjointUX disAB disCB. }
  have eqABC_ACB : A :|: B :|: C0 = A :|: C0 :|: B :=
    setUC_swap3 A B C0.
  pose rhoABC_acb : 'F[H]_(A :|: C0 :|: B) :=
    castlf (eqABC_ACB, eqABC_ACB) rhoABC.
  have HrhoAC_recast : rhoAC = ptrace_cast disAC_B rhoABC_acb.
  { rewrite /rhoAC /rhoABC_acb /ptrace_cast3B /ptrace_cast_gen.
    have eq_res :
        (A :|: B :|: C0) :\: B = (A :|: C0 :|: B) :\: B
      by rewrite eqABC_ACB.
    rewrite /ptrace_cast /ptrace_cast_gen.
    rewrite (ptracelf_castlf_eq eqABC_ACB eq_res).
    rewrite castlf_comp.
    by congr (castlf (_, _) _); exact: eq_irrelevance. }
  have eqA_CpCpp : A :|: (Cp :|: Cpp) = A :|: Cp :|: Cpp.
  { apply/setP=> x.
    by rewrite !inE orbA. }
  have Hobjective_bridge_M13c :
      forall (V_star : 'FI[H]_(C0, Cp :|: Cpp))
             (tau_star : 'F[H]_Cpp),
        tau_star \is den1lf ->
        exists (Rext : 'F[H]_((A :|: Cp) :|: Cpp))
               (taubar : 'F[H]_(A :|: Cp :|: Cpp))
               (target_star : 'F[H]_(A :|: Cp :|: Cpp))
               (phi_Cpp : 'F[H]_Cpp)
               (sigma_Bmax : 'F[H]_B),
          Rext =
          (castlf (eqA_CpCpp, eqA_CpCpp)
            ((((\1 : 'F[H]_A) \⊗ V_star) \o rhoAC \o
              (((\1 : 'F[H]_A) \⊗ V_star)^A)) :
              'F[H]_(A :|: (Cp :|: Cpp)))) /\
          target_star =
          ((gamma_ACp \O tau_star) : 'F[H]_(A :|: Cp :|: Cpp)) /\
          Rext \is denlf /\
          taubar \is den1lf /\
          target_star \is den1lf /\
          phi_Cpp \is den1lf /\
          sigma_Bmax \is den1lf /\
          ptrace_cast disACp_Cpp target_star = gamma_ACp /\
          ptrace_cast disACp_Cpp taubar = gamma_ACp /\
          taubar = ((gamma_ACp \O phi_Cpp) : 'F[H]_(A :|: Cp :|: Cpp)) /\
          pur_dist rhoAB (pi_A \O sigma_Bmax) <= pur_dist Rext target_star /\
          pur_dist Rext taubar <= pur_dist Rext target_star /\
          pur_dist Rext taubar =
          pur_dist (ptrace_cast disACp_Cpp Rext) gamma_ACp.
  { move=> V_star tau_star Htau_star_den1.
    pose W_iso : 'F[H]_(A :|: C0, A :|: (Cp :|: Cpp)) :=
      (\1 : 'F[H]_A) \⊗ V_star.
    pose rho_ext_raw : 'F[H]_(A :|: (Cp :|: Cpp)) :=
      W_iso \o rhoAC \o W_iso^A.
    pose Rext : 'F[H]_((A :|: Cp) :|: Cpp) :=
      castlf (eqA_CpCpp, eqA_CpCpp) rho_ext_raw.
    have HVstar_cptp : formso V_star \is cptp by apply: is_cptp.
    have HVstar_cp : formso V_star \is cpmap :=
      cptp_cpmap HVstar_cptp.
    have Hidcp : ((\:1 : 'SO[H]_A) \is cpmap) :=
      cptp_cpmap (idso_qc 'H[H]_A).
    have Hraw_psd : rho_ext_raw \is psdlf.
    { have Hraw_E :
          rho_ext_raw =
          (((\:1 : 'SO[H]_A) :⊗ formso V_star) rhoAC).
      { have -> :
            ((\:1 : 'SO[H]_A) :⊗ formso V_star) =
            formso ((\1 : 'F[H]_A) \⊗ V_star)
          by rewrite -formso1 tenso_formso.
        by rewrite /rho_ext_raw /W_iso formsoE. }
      rewrite Hraw_E (CPMap_BuildE Hidcp) (CPMap_BuildE HVstar_cp).
      exact: cp_psdP HrhoAC_psd. }
    have HR_psd : Rext \is psdlf.
    { rewrite /Rext.
      exact: castlf_psdlf. }
    have HR_tr_eq : \Tr Rext = \Tr rhoAC.
    { rewrite /Rext castlf_trlfE /rho_ext_raw /W_iso.
      rewrite lftraceC !comp_lfunA.
      have HW_isolf : (((\1 : 'F[H]_A) \⊗ V_star) \is isolf).
      { apply/isolfP.
        by rewrite tenf_adj -tenf_comp ?disAC ?disA_CpCpp //
          isofE isofE tenf11. }
      have HWi : (((\1 : 'F[H]_A) \⊗ V_star)^A) \o
                 ((\1 : 'F[H]_A) \⊗ V_star) = \1
        by move: HW_isolf => /isolfP.
      by rewrite HWi comp_lfun1l. }
    have HR_den : Rext \is denlf.
    { apply/denlfP; split; first exact: HR_psd.
      have HR_real : \Tr Rext \is Num.real := ger0_real (psdlf_trlf HR_psd).
      by rewrite -(RRe_real HR_real) lecR HR_tr_eq. }
    pose W_iso_B : 'F[H]_(A :|: C0 :|: B, A :|: (Cp :|: Cpp) :|: B) :=
      W_iso \⊗ (\1 : 'F[H]_B).
    pose rho_full_acb : 'F[H]_(A :|: (Cp :|: Cpp) :|: B) :=
      W_iso_B \o rhoABC_acb \o W_iso_B^A.
    have disACpCpp_B : [disjoint A :|: (Cp :|: Cpp) & B].
    { have disCp_B : [disjoint Cp & B] by rewrite disjoint_sym.
      have disCpp_B : [disjoint Cpp & B] by rewrite disjoint_sym.
      have disCpCpp_B : [disjoint Cp :|: Cpp & B]
        by rewrite disjointUX disCp_B disCpp_B.
      by rewrite disjointUX disAB disCpCpp_B. }
    have Hfull_marg_raw :
        ptrace_cast disACpCpp_B rho_full_acb = rho_ext_raw.
    { apply/h2mx_inj.
      rewrite /rho_full_acb /rho_ext_raw.
      rewrite (h2mx_ptrace_cast_ptrace2 disACpCpp_B).
      rewrite !h2mx_comp h2mx_adj.
      rewrite (h2mx_tenf W_iso (\1 : 'F[H]_B)) h2mx1.
      rewrite adjmxM.
      set Tout := @tenv_mxU R L H (A :|: (Cp :|: Cpp)) B.
      set Tin := @tenv_mxU R L H (A :|: C0) B.
      set Wmx := h2mx W_iso.
      have HToutK : Tout^*t *m Tout = 1%:M.
      { have /unitarymxK : Tout^*t \is unitarymx :=
          tenv_mxU_adj_unitarymx disACpCpp_B.
        by rewrite adjmxK. }
      rewrite -/Tout -/Wmx -/Tin adjmxK adjmxM.
      rewrite !mulmxA HToutK !mul1mx.
      rewrite -!mulmxA HToutK ?mulmx1 //.
      rewrite adjmx_tens adjmx1.
      have HrhoAC_mx :
          h2mx rhoAC = ptrace2 (Tin^*t *m h2mx rhoABC_acb *m Tin).
      { by rewrite HrhoAC_recast (h2mx_ptrace_cast_ptrace2 disAC_B). }
      transitivity
        (ptrace2
          ((Wmx *t (1%:M : 'M[C]_(dim 'H[H]_B))) *m
           (Tin^*t *m h2mx rhoABC_acb *m Tin) *m
           (Wmx^*t *t (1%:M : 'M[C]_(dim 'H[H]_B))))).
      { congr ptrace2.
        by rewrite !mulmxA. }
      rewrite ptrace2_tens_id_sandwich.
      by rewrite -HrhoAC_mx h2mx_adj -/Wmx !mulmxA. }
    pose eqACpCpp_B := f_equal (fun S : {set L} => S :|: B) eqA_CpCpp.
    pose rho_full_RB : 'F[H]_((A :|: Cp :|: Cpp) :|: B) :=
      castlf (eqACpCpp_B, eqACpCpp_B) rho_full_acb.
    have disR_B : [disjoint A :|: Cp :|: Cpp & B].
    { by rewrite -eqA_CpCpp. }
    have Hfull_marg_R : ptrace_cast disR_B rho_full_RB = Rext.
    { rewrite /rho_full_RB /Rext -Hfull_marg_raw.
      rewrite /ptrace_cast /ptrace_cast_gen.
      have eq_res :
          (A :|: (Cp :|: Cpp) :|: B) :\: B =
          ((A :|: Cp :|: Cpp) :|: B) :\: B
        by rewrite eqACpCpp_B.
      rewrite (ptracelf_castlf_eq eqACpCpp_B eq_res).
      rewrite !castlf_comp.
      by congr (castlf (_, _) _); exact: eq_irrelevance. }
    have disAB_C0 : [disjoint A :|: B & C0]
      by rewrite disjointUX disAC disBC.
    have disAB_CpCpp : [disjoint A :|: B & Cp :|: Cpp].
    { have disAB_Cp : [disjoint A :|: B & Cp]
        by rewrite disjointUX disA_Cp disB_Cp.
      have disAB_Cpp : [disjoint A :|: B & Cpp]
        by rewrite disjointUX disA_Cpp disB_Cpp.
      by rewrite disjointXU disAB_Cp disAB_Cpp. }
    have eqFullAB_CpCpp :
        A :|: (Cp :|: Cpp) :|: B = A :|: B :|: (Cp :|: Cpp).
    { apply/setP=> x.
      rewrite !inE.
      by case: (x \in A); case: (x \in B);
        case: (x \in Cp); case: (x \in Cpp). }
    have Hfull_marg_AB :
        ptrace_cast disAB_CpCpp
          (castlf (eqFullAB_CpCpp, eqFullAB_CpCpp) rho_full_acb) = rhoAB.
    { pose W_AB_CpCpp :
          'F[H]_(A :|: B :|: C0, A :|: B :|: (Cp :|: Cpp)) :=
        (\1 : 'F[H]_(A :|: B)) \⊗ V_star.
      have HrhoAB_ptr :
          h2mx rhoAB =
          ptrace2 ((@tenv_mxU R L H (A :|: B) C0)^*t *m
            h2mx rhoABC *m (@tenv_mxU R L H (A :|: B) C0)).
      { rewrite /rhoAB /ptrace_cast3C /ptrace_cast /ptrace_cast_gen.
        rewrite (eq_irrelevance (setDU3_C disAC disBC)
          (setDU_r disAB_C0)).
        by rewrite (h2mx_ptrace_cast_ptrace2 disAB_C0). }
      have Hfull_cast_form :
          castlf (eqFullAB_CpCpp, eqFullAB_CpCpp) rho_full_acb =
          W_AB_CpCpp \o rhoABC \o W_AB_CpCpp^A.
      { rewrite /rho_full_acb /rhoABC_acb /W_iso_B /W_iso /W_AB_CpCpp.
        to_Fnd.
        rewrite -tenF11.
        by rewrite -!tenFA
          (tenFC (to_Fnd V_star) (to_Fnd (\1 : 'F[H]_B))) !tenFA. }
      apply/h2mx_inj.
      rewrite Hfull_cast_form.
      rewrite (h2mx_ptrace_cast_ptrace2 disAB_CpCpp).
      rewrite !h2mx_comp h2mx_adj.
      rewrite /W_AB_CpCpp !h2mx_tenf !h2mx1.
      set Uout := @tenv_mxU R L H (A :|: B) (Cp :|: Cpp).
      set Uin := @tenv_mxU R L H (A :|: B) C0.
      set Vmx := h2mx V_star.
      set Tmx := (1%:M : 'M[C]_(dim 'H[H]_(A :|: B))) *t Vmx.
      have HUoutK0 :
          (@tenv_mxU R L H (A :|: B) (Cp :|: Cpp))^*t *m
          (@tenv_mxU R L H (A :|: B) (Cp :|: Cpp)) = 1%:M.
      { have /unitarymxK :
            (@tenv_mxU R L H (A :|: B) (Cp :|: Cpp))^*t \is unitarymx :=
          tenv_mxU_adj_unitarymx disAB_CpCpp.
        by rewrite adjmxK. }
      have HUoutK : Uout^*t *m Uout = 1%:M.
      { exact: HUoutK0. }
      have HVK : Vmx^*t *m Vmx = 1%:M.
      { have := f_equal h2mx (isofE V_star).
        by rewrite h2mx_comp h2mx_adj h2mx1. }
      rewrite -/Uout -/Uin -/Vmx -/Tmx adjmxM.
      rewrite !mulmxA -mulmxA HUoutK mul1mx.
      rewrite adjmxK adjmxM.
      rewrite -/Tmx.
      rewrite -!mulmxA [Uout^*t *m Uout]HUoutK !mulmx1.
      rewrite !mulmxA.
      transitivity
        (ptrace2 ((((1%:M : 'M[C]_(dim 'H[H]_(A :|: B))) *t Vmx) *m
          (Uin^*t *m h2mx rhoABC *m Uin)) *m
          (((1%:M : 'M[C]_(dim 'H[H]_(A :|: B))) *t Vmx)^*t))).
      { congr ptrace2.
        by rewrite !mulmxA. }
      rewrite (@ptrace2_conj_tens_right_iso R (dim 'H[H]_(A :|: B))
        (dim 'H[H]_C0) (dim 'H[H]_(Cp :|: Cpp)) Vmx
        (Uin^*t *m h2mx rhoABC *m Uin) HVK).
      by rewrite -HrhoAB_ptr. }
    have eqFullRB_AB_CpCpp :
        (A :|: Cp :|: Cpp) :|: B = A :|: B :|: (Cp :|: Cpp).
    { apply/setP=> x.
      rewrite !inE.
      by case: (x \in A); case: (x \in B);
        case: (x \in Cp); case: (x \in Cpp). }
    have Hfull_RB_marg_AB :
        ptrace_cast disAB_CpCpp
          (castlf (eqFullRB_AB_CpCpp, eqFullRB_AB_CpCpp) rho_full_RB) =
        rhoAB.
    { rewrite /rho_full_RB.
      have Hcast :
          castlf (eqFullRB_AB_CpCpp, eqFullRB_AB_CpCpp)
            (castlf (eqACpCpp_B, eqACpCpp_B) rho_full_acb) =
          castlf (eqFullAB_CpCpp, eqFullAB_CpCpp) rho_full_acb.
      { rewrite castlf_comp.
        by congr (castlf (_, _) _); exact: eq_irrelevance. }
      by rewrite Hcast Hfull_marg_AB. }
    have HrhoABC_acb_psd : rhoABC_acb \is psdlf.
    { rewrite /rhoABC_acb.
      exact: castlf_psdlf. }
    have HW_iso_B_isolf : W_iso_B \is isolf.
    { have HW_iso_isolf : W_iso \is isolf.
      { apply/isolfP.
        by rewrite /W_iso tenf_adj -tenf_comp ?disAC ?disA_CpCpp //
          isofE isofE tenf11. }
      have HWi : W_iso^A \o W_iso = \1 by move: HW_iso_isolf => /isolfP.
      apply/isolfP.
      by rewrite /W_iso_B tenf_adj -tenf_comp ?disAC_B ?disACpCpp_B //
        HWi adjf1 comp_lfun1l tenf11. }
    have Hfull_acb_psd : rho_full_acb \is psdlf.
    { have Hfull_E :
          rho_full_acb = formso W_iso_B rhoABC_acb
        by rewrite /rho_full_acb formsoE.
      have HW_cp : formso W_iso_B \is cpmap := @formso_cp R _ _ W_iso_B.
      rewrite Hfull_E (CPMap_BuildE HW_cp).
      exact: cp_psdP HrhoABC_acb_psd. }
    have Hfull_acb_tr_eq : \Tr rho_full_acb = \Tr rhoABC.
    { rewrite /rho_full_acb lftraceC !comp_lfunA.
      have HWi : W_iso_B^A \o W_iso_B = \1
        by move: HW_iso_B_isolf => /isolfP.
      by rewrite HWi comp_lfun1l /rhoABC_acb castlf_trlfE. }
    have Hfull_RB_den : rho_full_RB \is denlf.
    { apply/denlfP; split.
      - rewrite /rho_full_RB.
        exact: castlf_psdlf.
      - have Hfull_real : \Tr rho_full_RB \is Num.real.
        { rewrite /rho_full_RB castlf_trlfE.
          exact: ger0_real (psdlf_trlf Hfull_acb_psd). }
        rewrite -(RRe_real Hfull_real) lecR /rho_full_RB castlf_trlfE.
        by rewrite Hfull_acb_tr_eq. }
    pose target_star : 'F[H]_(A :|: Cp :|: Cpp) :=
      gamma_ACp \O tau_star.
    have Htau_star_psd : tau_star \is psdlf :=
      den1lf_psd Htau_star_den1.
    have Hgamma_ACp_le : (0 : 'F[H]_(A :|: Cp)) ⊑ gamma_ACp.
    { move: (den1lf_psd Hgamma_ACp_den1).
      by rewrite psdlfE. }
    have Htau_star_le : (0 : 'F[H]_Cpp) ⊑ tau_star.
    { by move: Htau_star_psd; rewrite psdlfE. }
    have Htarget_star_psd : target_star \is psdlf.
    { have -> :
          target_star =
          ((gamma_ACp \⊗ tau_star) : 'F[H]_(A :|: Cp :|: Cpp)).
      { apply: to_Fnd_inj.
        by rewrite /target_star (sdotFT _ _ disACp_Cpp) to_Fnd_tenE. }
      rewrite psdlfE.
      exact: tenf_ge0 disACp_Cpp Hgamma_ACp_le Htau_star_le. }
    have Htarget_star_tr1 : \Tr target_star = 1.
    { rewrite /target_star (lftrace_sdot_disj _ _ disACp_Cpp).
      by rewrite (den1lf_trlf Hgamma_ACp_den1)
        (den1lf_trlf Htau_star_den1) mul1r. }
    have Htarget_star_den1 : target_star \is den1lf.
    { by apply/den1lfP; split. }
    have Htarget_star_ptr :
        ptrace_cast disACp_Cpp target_star = gamma_ACp.
    { apply: h2mx_inj.
      rewrite /target_star (h2mx_ptrace_cast_ptrace2 disACp_Cpp).
      have -> :
          h2mx ((gamma_ACp \O tau_star) :
            'F[H]_(A :|: Cp :|: Cpp)) =
          h2mx ((gamma_ACp \⊗ tau_star) :
            'F[H]_(A :|: Cp :|: Cpp)).
      { congr h2mx.
        apply: to_Fnd_inj.
        by rewrite (sdotFT _ _ disACp_Cpp) to_Fnd_tenE. }
      rewrite h2mx_tenf.
      pose UU := @tenv_mxU R L H (A :|: Cp) Cpp.
      have HUadj : UU^*t \is unitarymx :=
        tenv_mxU_adj_unitarymx disACp_Cpp.
      have Uadj_mul_U : UU^*t *m UU = 1%:M
        by have := unitarymxK HUadj; rewrite adjmxK.
      have Htau_tr1_mx : \tr (h2mx tau_star) = 1
        by move: (den1lf_trlf Htau_star_den1); rewrite /lftrace.
      rewrite !mulmxA Uadj_mul_U mul1mx -mulmxA Uadj_mul_U mulmx1.
      rewrite ptrace_tensmx h2mxZ_lf /= /lftrace.
      by rewrite Htau_tr1_mx scale1r. }
    pose rho_ptr : 'F[H]_(A :|: Cp) := ptrace_cast disACp_Cpp Rext.
    have [taubar [Htaubar_den [Htaubar_ptr Htaubar_pd]]] :=
      @pd_ext R L H (A :|: Cp) Cpp disACp_Cpp
        rho_ptr gamma_ACp Rext HR_den (erefl _) Hgamma_ACp_den.
    have Htr_ptrace_taubar : \Tr taubar = \Tr gamma_ACp.
    { rewrite -Htaubar_ptr /ptrace_cast /ptrace_cast_gen castlf_trlfE.
      have /cptpP [_ /tpmapP Htp] :=
        @ptraceso_qc R L H Cpp ((A :|: Cp) :|: Cpp).
      by rewrite Htp. }
    have Htaubar_den1 : taubar \is den1lf.
    { apply/den1lfP; split.
      - by move/denlfP: Htaubar_den => [].
      - by rewrite Htr_ptrace_taubar (den1lf_trlf Hgamma_ACp_den1). }
    have [theta_full [Htheta_full_den [Htheta_full_ptr Htheta_full_pd]]] :=
      @pd_ext R L H (A :|: Cp :|: Cpp) B disR_B
        Rext taubar rho_full_RB Hfull_RB_den Hfull_marg_R Htaubar_den.
    have Htr_ptrace_theta : \Tr theta_full = \Tr taubar.
    { rewrite -Htheta_full_ptr /ptrace_cast /ptrace_cast_gen castlf_trlfE.
      have /cptpP [_ /tpmapP Htp] :=
        @ptraceso_qc R L H B ((A :|: Cp :|: Cpp) :|: B).
      by rewrite Htp. }
    have Htheta_full_den1 : theta_full \is den1lf.
    { apply/den1lfP; split.
      - by move/denlfP: Htheta_full_den => [].
      - by rewrite Htr_ptrace_theta (den1lf_trlf Htaubar_den1). }
    pose sigma_B : 'F[H]_B := ptrace_castl disR_B theta_full.
    have Hsigma_B_den1 : sigma_B \is den1lf.
    { apply/den1lfP; split.
      - rewrite /sigma_B.
        apply: ptrace_castl_psdlf.
        exact: den1lf_psd Htheta_full_den1.
      - rewrite /sigma_B /ptrace_castl /ptrace_cast_gen castlf_trlfE.
        have /cptpP [_ /tpmapP Htp] :=
          @ptraceso_qc R L H (A :|: Cp :|: Cpp) ((A :|: Cp :|: Cpp) :|: B).
        by rewrite Htp (den1lf_trlf Htheta_full_den1). }
    have disACp_B : [disjoint A :|: Cp & B].
    { have disCp_B : [disjoint Cp & B] by rewrite disjoint_sym.
      by rewrite disjointUX disAB disCp_B. }
    have disACp_CppB : [disjoint A :|: Cp & Cpp :|: B].
    { by rewrite disjointXU disACp_Cpp disACp_B. }
    have eqThetaAssoc :
        (A :|: Cp :|: Cpp) :|: B = A :|: Cp :|: (Cpp :|: B).
    { apply/setP=> x.
      by rewrite !inE orbA. }
    pose theta_ACp_CppB : 'F[H]_(A :|: Cp :|: (Cpp :|: B)) :=
      castlf (eqThetaAssoc, eqThetaAssoc) theta_full.
    have Htheta_ACp_CppB_den1 : theta_ACp_CppB \is den1lf.
    { apply/den1lfP; split.
      - rewrite /theta_ACp_CppB.
        exact: castlf_psdlf (den1lf_psd Htheta_full_den1).
      - by rewrite /theta_ACp_CppB castlf_trlfE
          (den1lf_trlf Htheta_full_den1). }
    have Htheta_ACp_CppB_ptr :
        ptrace_cast disACp_CppB theta_ACp_CppB = gamma_ACp.
    { rewrite -Htaubar_ptr -Htheta_full_ptr.
      rewrite /theta_ACp_CppB /ptrace_cast /ptrace_cast_gen.
      have Hcomp_trace :=
        congr1
          (fun F : 'SO[H]_(((A :|: Cp :|: Cpp) :|: B),
             ((((A :|: Cp :|: Cpp) :|: B) :\: B) :\: Cpp)) =>
             F theta_full)
          (@ptraceso_comp R L H Cpp B ((A :|: Cp :|: Cpp) :|: B)).
      move: Hcomp_trace.
      rewrite comp_soE castsoE /= castlf_id.
      move=> Hcomp_trace.
      have eq_res_assoc :
          ((A :|: Cp :|: Cpp) :|: B) :\: (Cpp :|: B) =
          (A :|: Cp :|: (Cpp :|: B)) :\: (Cpp :|: B)
        by rewrite eqThetaAssoc.
      have eq_res_B_then_Cpp :
          (((A :|: Cp :|: Cpp) :|: B) :\: B) :\: Cpp =
          (A :|: Cp :|: Cpp) :\: Cpp
        by rewrite (setDU_r disR_B).
      have eq_trace_CppB :
          ((A :|: Cp :|: Cpp) :|: B) :\: (Cpp :|: B) =
          ((A :|: Cp :|: Cpp) :|: B) :\: (B :|: Cpp).
      { by rewrite (finset.setUC Cpp B). }
      have Htrace_union_cast :
          \Tr_(Cpp :|: B) theta_full =
          castlf (esym eq_trace_CppB, esym eq_trace_CppB)
            (\Tr_(B :|: Cpp) theta_full).
      { case: _ / (finset.setUC Cpp B) in eq_trace_CppB *.
        by rewrite (eq_irrelevance eq_trace_CppB erefl) castlf_id. }
      rewrite (ptracelf_castlf_eq eqThetaAssoc eq_res_assoc).
      rewrite (ptracelf_castlf_eq (setDU_r disR_B) eq_res_B_then_Cpp).
      rewrite Hcomp_trace.
      rewrite Htrace_union_cast.
      rewrite !castlf_comp.
      by congr (castlf (_, _) _); exact: eq_irrelevance. }
    have [phi_CppB [Hphi_CppB_den1 Htheta_full_split]] :=
      @pure_extension_split R L H A Cp (Cpp :|: B) disACp_CppB
        gamma_ACp theta_ACp_CppB Hgamma_ACp_den1 Hgamma_ACp_rank1
        Htheta_ACp_CppB_den1 Htheta_ACp_CppB_ptr.
    have Htheta_full_target :
        theta_ACp_CppB =
        ((gamma_ACp \O phi_CppB) : 'F[H]_(A :|: Cp :|: (Cpp :|: B))).
    { rewrite Htheta_full_split.
      by rewrite (eq_irrelevance (esym _) (erefl (A :|: Cp :|: (Cpp :|: B))))
        castlf_id. }
    have disCpp_B : [disjoint Cpp & B] by rewrite disjoint_sym.
    pose sigma_B_split : 'F[H]_B := ptrace_castl disCpp_B phi_CppB.
    have Hsigma_B_split_den1 : sigma_B_split \is den1lf.
    { apply/den1lfP; split.
      - rewrite /sigma_B_split.
        apply: ptrace_castl_psdlf.
        exact: den1lf_psd Hphi_CppB_den1.
      - rewrite /sigma_B_split /ptrace_castl /ptrace_cast_gen castlf_trlfE.
        have /cptpP [_ /tpmapP Htp] :=
          @ptraceso_qc R L H Cpp (Cpp :|: B).
        by rewrite Htp (den1lf_trlf Hphi_CppB_den1). }
    have eqThetaAB_CpCpp :
        A :|: Cp :|: (Cpp :|: B) = A :|: B :|: (Cp :|: Cpp).
    { apply/setP=> x.
      rewrite !inE.
      by case: (x \in A); case: (x \in B);
        case: (x \in Cp); case: (x \in Cpp). }
    pose theta_AB_CpCpp : 'F[H]_(A :|: B :|: (Cp :|: Cpp)) :=
      castlf (eqThetaAB_CpCpp, eqThetaAB_CpCpp) theta_ACp_CppB.
    pose max_target_AB : 'F[H]_(A :|: B) := pi_A \O sigma_B_split.
    have disACpB_Cpp : [disjoint A :|: Cp :|: B & Cpp].
    { have disACp_Cpp' : [disjoint A :|: Cp & Cpp] := disACp_Cpp.
      by rewrite disjointUX disACp_Cpp' disB_Cpp. }
    have eqTheta_ACpB_Cpp :
        A :|: Cp :|: (Cpp :|: B) = A :|: Cp :|: B :|: Cpp.
    { apply/setP=> x.
      rewrite !inE.
      by case: (x \in A); case: (x \in Cp);
        case: (x \in B); case: (x \in Cpp). }
    pose theta_ACpB : 'F[H]_(A :|: Cp :|: B) :=
      ptrace_cast disACpB_Cpp
        (castlf (eqTheta_ACpB_Cpp, eqTheta_ACpB_Cpp) theta_ACp_CppB).
    have Htheta_ACpB_den1 : theta_ACpB \is den1lf.
    { apply/den1lfP; split.
      - rewrite /theta_ACpB.
        apply: ptrace_cast_psdlf.
        rewrite castlf_psdlfE.
        exact: den1lf_psd Htheta_ACp_CppB_den1.
      - rewrite /theta_ACpB /ptrace_cast /ptrace_cast_gen castlf_trlfE.
        have /cptpP [_ /tpmapP Htp] :=
          @ptraceso_qc R L H Cpp (A :|: Cp :|: B :|: Cpp).
        by rewrite Htp castlf_trlfE
          (den1lf_trlf Htheta_ACp_CppB_den1). }
    have Htheta_ACpB_ptr :
        ptrace_cast disACp_B theta_ACpB = gamma_ACp.
    { rewrite -Htheta_ACp_CppB_ptr.
      rewrite /theta_ACpB /ptrace_cast /ptrace_cast_gen.
      have Hcomp_trace :=
        congr1
          (fun F : 'SO[H]_(A :|: Cp :|: B :|: Cpp,
             (((A :|: Cp :|: B :|: Cpp) :\: Cpp) :\: B)) =>
             F (castlf (eqTheta_ACpB_Cpp, eqTheta_ACpB_Cpp)
                  theta_ACp_CppB))
          (@ptraceso_comp R L H B Cpp (A :|: Cp :|: B :|: Cpp)).
      move: Hcomp_trace.
      rewrite comp_soE castsoE /= castlf_id.
      move=> Hcomp_trace.
      have eq_res_after_Cpp :
          ((A :|: Cp :|: B :|: Cpp) :\: Cpp) :\: B =
          (A :|: Cp :|: B) :\: B
        by rewrite (setDU_r disACpB_Cpp).
      have eq_res_union :
          (A :|: Cp :|: (Cpp :|: B)) :\: (Cpp :|: B) =
          (A :|: Cp :|: B :|: Cpp) :\: (Cpp :|: B)
        by rewrite eqTheta_ACpB_Cpp.
      rewrite (ptracelf_castlf_eq (setDU_r disACpB_Cpp) eq_res_after_Cpp).
      rewrite Hcomp_trace.
      rewrite (ptracelf_castlf_eq eqTheta_ACpB_Cpp eq_res_union).
      rewrite !castlf_comp.
      by congr (castlf (_, _) _); exact: eq_irrelevance. }
    have [sigma_B2 [Hsigma_B2_den1 Htheta_ACpB_split]] :=
      @pure_extension_split R L H A Cp B disACp_B
        gamma_ACp theta_ACpB Hgamma_ACp_den1 Hgamma_ACp_rank1
        Htheta_ACpB_den1 Htheta_ACpB_ptr.
    have Htheta_ACpB_target :
        theta_ACpB = ((gamma_ACp \O sigma_B2) : 'F[H]_(A :|: Cp :|: B)).
    { rewrite Htheta_ACpB_split.
      by rewrite (eq_irrelevance (esym _) (erefl (A :|: Cp :|: B)))
        castlf_id. }
    have disCp_B : [disjoint Cp & B] by rewrite disjoint_sym.
    have Htheta_AB_target :
        ptrace_cast3B disA_Cp disCp_B theta_ACpB =
        (pi_A \O sigma_B2 : 'F[H]_(A :|: B)).
    { rewrite Htheta_ACpB_target.
      rewrite (ptrace_cast3B_sdot_mid disA_Cp disCp_B disAB).
      by rewrite /pi_A gamma_state_ptrace. }
    have Htheta_full_AB_target :
        ptrace_cast disAB_CpCpp
          (castlf (eqFullRB_AB_CpCpp, eqFullRB_AB_CpCpp) theta_full) =
        (pi_A \O sigma_B2 : 'F[H]_(A :|: B)).
    { rewrite -Htheta_AB_target.
      rewrite /theta_ACpB /theta_ACp_CppB.
      rewrite /ptrace_cast3B /ptrace_cast /ptrace_cast_gen.
      have Hcomp_trace :=
        congr1
          (fun F : 'SO[H]_(A :|: Cp :|: B :|: Cpp,
             (((A :|: Cp :|: B :|: Cpp) :\: Cpp) :\: Cp)) =>
             F (castlf (eqTheta_ACpB_Cpp, eqTheta_ACpB_Cpp)
                  theta_ACp_CppB))
          (@ptraceso_comp R L H Cp Cpp (A :|: Cp :|: B :|: Cpp)).
      move: Hcomp_trace.
      rewrite comp_soE castsoE /= castlf_id.
      move=> Hcomp_trace.
      have eq_res_after_Cpp :
          ((A :|: Cp :|: B :|: Cpp) :\: Cpp) :\: Cp =
          (A :|: Cp :|: B) :\: Cp
        by rewrite (setDU_r disACpB_Cpp).
      have eq_res_union :
          (A :|: Cp :|: (Cpp :|: B)) :\: (Cpp :|: Cp) =
          (A :|: Cp :|: B :|: Cpp) :\: (Cpp :|: Cp)
        by rewrite eqTheta_ACpB_Cpp.
      have eq_res_assoc :
          ((A :|: Cp :|: Cpp) :|: B) :\: (Cpp :|: Cp) =
          (A :|: Cp :|: (Cpp :|: B)) :\: (Cpp :|: Cp)
        by rewrite eqThetaAssoc.
      have eq_res_full :
          ((A :|: Cp :|: Cpp) :|: B) :\: (Cp :|: Cpp) =
          (A :|: B :|: (Cp :|: Cpp)) :\: (Cp :|: Cpp)
        by rewrite eqFullRB_AB_CpCpp.
      have eq_trace_full :
          ((A :|: Cp :|: Cpp) :|: B) :\: (Cp :|: Cpp) =
          ((A :|: Cp :|: Cpp) :|: B) :\: (Cpp :|: Cp).
      { by rewrite (finset.setUC Cp Cpp). }
      have Htrace_full_cast :
          \Tr_(Cp :|: Cpp) theta_full =
          castlf (esym eq_trace_full, esym eq_trace_full)
            (\Tr_(Cpp :|: Cp) theta_full).
      { case: _ / (finset.setUC Cp Cpp) in eq_trace_full *.
        by rewrite (eq_irrelevance eq_trace_full erefl) castlf_id. }
      rewrite (ptracelf_castlf_eq eqFullRB_AB_CpCpp eq_res_full).
      rewrite Htrace_full_cast.
      rewrite (ptracelf_castlf_eq (setDU_r disACpB_Cpp) eq_res_after_Cpp).
      rewrite Hcomp_trace.
      rewrite (ptracelf_castlf_eq eqTheta_ACpB_Cpp eq_res_union).
      rewrite (ptracelf_castlf_eq eqThetaAssoc eq_res_assoc).
      rewrite !castlf_comp.
      by congr (castlf (_, _) _); exact: eq_irrelevance. }
    have [phi_Cpp [Hphi_Cpp_den1 Htaubar_split]] :=
      @pure_extension_split R L H A Cp Cpp disACp_Cpp
        gamma_ACp taubar Hgamma_ACp_den1 Hgamma_ACp_rank1
        Htaubar_den1 Htaubar_ptr.
    have Htaubar_target :
        taubar = ((gamma_ACp \O phi_Cpp) : 'F[H]_(A :|: Cp :|: Cpp)).
    { rewrite Htaubar_split.
      by rewrite (eq_irrelevance (esym _) (erefl (A :|: Cp :|: Cpp)))
        castlf_id. }
    have Hpd_target :
        pur_dist Rext taubar <= pur_dist Rext target_star.
    { have Hmono :=
        @pd_mono_ptrace_cast R L H (A :|: Cp) Cpp disACp_Cpp
          target_star Rext HR_psd Htarget_star_psd.
      by rewrite Htarget_star_ptr -Htaubar_pd in Hmono. }
    have Hpd_full_cast :
        pur_dist
          (castlf (eqFullRB_AB_CpCpp, eqFullRB_AB_CpCpp) rho_full_RB)
          (castlf (eqFullRB_AB_CpCpp, eqFullRB_AB_CpCpp) theta_full) =
        pur_dist rho_full_RB theta_full.
    { by rewrite /pur_dist /gfid !h2mx_castlf gfid_cast_mx. }
    have Hpd_AB_theta :
        pur_dist rhoAB (pi_A \O sigma_B2) <=
        pur_dist rho_full_RB theta_full.
    { have Hrho_full_cast_psd :
          castlf (eqFullRB_AB_CpCpp, eqFullRB_AB_CpCpp) rho_full_RB \is psdlf.
      { exact: castlf_psdlf (denlf_psd Hfull_RB_den). }
      have Htheta_full_cast_psd :
          castlf (eqFullRB_AB_CpCpp, eqFullRB_AB_CpCpp) theta_full \is psdlf.
      { exact: castlf_psdlf (den1lf_psd Htheta_full_den1). }
      have Hmono := @pd_mono_ptrace_cast R L H (A :|: B) (Cp :|: Cpp)
        disAB_CpCpp
        (castlf (eqFullRB_AB_CpCpp, eqFullRB_AB_CpCpp) theta_full)
        (castlf (eqFullRB_AB_CpCpp, eqFullRB_AB_CpCpp) rho_full_RB)
        Hrho_full_cast_psd Htheta_full_cast_psd.
      by rewrite Hfull_RB_marg_AB Htheta_full_AB_target Hpd_full_cast in Hmono. }
    have Hpd_AB_target :
        pur_dist rhoAB (pi_A \O sigma_B2) <= pur_dist Rext target_star.
    { rewrite Htheta_full_pd in Hpd_AB_theta.
      exact: le_trans Hpd_AB_theta Hpd_target. }
    exists Rext, taubar, target_star, phi_Cpp, sigma_B2.
    split.
    { by rewrite /Rext /rho_ext_raw /W_iso. }
    split; first by rewrite /target_star.
    do 10 split=> //. }
  have Hmax_uhlmann_witness :
      forall sigma_B : 'F[H]_B,
        sigma_B \is den1lf ->
        exists (V_star : 'FI[H]_(C0, Cp :|: Cpp))
               (tau_star : 'F[H]_Cpp)
               (target_star : 'F[H]_(A :|: Cp :|: Cpp))
               (target_full : 'F[H]_(A :|: B :|: (Cp :|: Cpp))),
          tau_star \is den1lf /\
          target_star \is den1lf /\
          target_star =
            ((gamma_ACp \O tau_star) : 'F[H]_(A :|: Cp :|: Cpp)) /\
          target_full \is den1lf /\
          \Rank target_full = 1%N /\
          ptrace_cast disAB_CpCpp_g target_full =
            (pi_A \O sigma_B : 'F[H]_(A :|: B)) /\
          ptrace_cast disACpCpp_B_g
            (castlf (esym eqACpCpp_B_AB_CpCpp_g,
                     esym eqACpCpp_B_AB_CpCpp_g) target_full) =
            target_star /\
          @complex.Re R
            (trnorm
              (sqrtmx
                ((((1%:M : 'M[C]_(dim 'H[H]_(A :|: B))) *t h2mx V_star) *m
                  ((@tenv_mxU R L H (A :|: B) C0)^*t *m h2mx rhoABC *m
                    (@tenv_mxU R L H (A :|: B) C0))) *m
                 (((1%:M : 'M[C]_(dim 'H[H]_(A :|: B))) *t h2mx V_star)^*t)) *m
               sqrtmx
                 ((@tenv_mxU R L H (A :|: B) (Cp :|: Cpp))^*t *m
                   h2mx target_full *m
                   (@tenv_mxU R L H (A :|: B) (Cp :|: Cpp))))) =
          @complex.Re R
            (trnorm
              (sqrtmx (h2mx rhoAB) *m
               sqrtmx (h2mx (pi_A \O sigma_B : 'F[H]_(A :|: B))))).
  { move=> sigma_B Hsigma_B_den1.
    have [phi_BCpp [tau_star [target_star [target_full Htarget]]]] :=
      Hmax_target_full sigma_B Hsigma_B_den1.
    case: Htarget => Hphi_den1 [Hphi_rank [Hphi_ptr
      [Htau_den1 [Htarget_den1 [Htarget_eq
      [Htarget_full_den1 [Htarget_full_rank
      [Htarget_full_ptr Htarget_full_ptr_star]]]]]]]].
    have disAB_C0 : [disjoint A :|: B & C0]
      by rewrite disjointUX disAC disBC.
    pose Uin := @tenv_mxU R L H (A :|: B) C0.
    pose Uout := @tenv_mxU R L H (A :|: B) (Cp :|: Cpp).
    pose rho_src := Uin^*t *m h2mx rhoABC *m Uin.
    pose theta_tgt := Uout^*t *m h2mx target_full *m Uout.
    have HUin : Uin \is unitarymx :=
      @tenv_mxU_unitarymx R L H (A :|: B) C0.
    have HUin_adj : Uin^*t \is unitarymx :=
      tenv_mxU_adj_unitarymx disAB_C0.
    have HUinK : Uin^*t *m Uin = 1%:M
      by have := unitarymxK HUin_adj; rewrite adjmxK.
    have HUinKt : Uin *m Uin^*t = 1%:M :=
      unitarymxK (@tenv_mxU_unitarymx R L H (A :|: B) C0).
    have HUout : Uout \is unitarymx :=
      @tenv_mxU_unitarymx R L H (A :|: B) (Cp :|: Cpp).
    have HUout_adj : Uout^*t \is unitarymx :=
      tenv_mxU_adj_unitarymx disAB_CpCpp_g.
    have HUoutK : Uout^*t *m Uout = 1%:M
      by have := unitarymxK HUout_adj; rewrite adjmxK.
    have HUoutKt : Uout *m Uout^*t = 1%:M :=
      unitarymxK (@tenv_mxU_unitarymx R L H (A :|: B) (Cp :|: Cpp)).
    have Hrho_mx_psd : h2mx rhoABC \is psdmx
      by move: Hrho_psd; rewrite qualifE.
    have Hrho_src_psd : rho_src \is psdmx.
    { rewrite /rho_src.
      have Hpsd :=
        @psdmx_bimap_closed_gen C _ (h2mx rhoABC) _ Uin^*t
          Hrho_mx_psd.
      by move: Hpsd; rewrite adjmxK. }
    have Hrho_src_tr : \tr rho_src = \tr (h2mx rhoABC).
    { rewrite /rho_src mxtrace_mulC.
      by rewrite mulmxA HUinKt mul1mx. }
    have Hrho_src_den : rho_src \is denmx.
    { apply/denmxP; split; first exact: Hrho_src_psd.
      move/denlfP: Hrho_den => [_ Htr].
      by rewrite Hrho_src_tr. }
    have Hrho_src_rank : \rank rho_src = 1%N.
    { rewrite /rho_src.
      rewrite (mxrank_mulmxU _ HUin).
      rewrite (mxrank_mulUCmx _ HUin).
      by move: Hrho_rank; rewrite /lfrank. }
    have Hrho_src_ptr : ptrace2 rho_src = h2mx rhoAB.
    { rewrite /rho_src /rhoAB /ptrace_cast3C /ptrace_cast /ptrace_cast_gen.
      rewrite (eq_irrelevance (setDU3_C disAC disBC)
        (setDU_r disAB_C0)).
      by rewrite (h2mx_ptrace_cast_ptrace2 disAB_C0). }
    have Htarget_full_psd : target_full \is psdlf :=
      den1lf_psd Htarget_full_den1.
    have Htheta_mx_psd : h2mx target_full \is psdmx
      by move: Htarget_full_psd; rewrite qualifE.
    have Htheta_tgt_psd : theta_tgt \is psdmx.
    { rewrite /theta_tgt.
      have Hpsd :=
        @psdmx_bimap_closed_gen C _ (h2mx target_full) _ Uout^*t
          Htheta_mx_psd.
      by move: Hpsd; rewrite adjmxK. }
    have Htheta_tgt_tr : \tr theta_tgt = \tr (h2mx target_full).
    { by rewrite /theta_tgt mxtrace_mulC mulmxA HUoutKt mul1mx. }
    have Htheta_tgt_den : theta_tgt \is denmx.
    { apply/denmxP; split; first exact: Htheta_tgt_psd.
      move/den1lfP: Htarget_full_den1 => [_ Htr1].
      rewrite Htheta_tgt_tr /lftrace -Htr1.
      exact: lexx. }
    have Htheta_tgt_rank : \rank theta_tgt = 1%N.
    { rewrite /theta_tgt.
      rewrite (mxrank_mulmxU _ HUout).
      rewrite (mxrank_mulUCmx _ HUout).
      by move: Htarget_full_rank; rewrite /lfrank. }
    have Htheta_tgt_ptr :
        ptrace2 theta_tgt =
        h2mx (pi_A \O sigma_B : 'F[H]_(A :|: B)).
    { by rewrite /theta_tgt -Htarget_full_ptr
        (h2mx_ptrace_cast_ptrace2 disAB_CpCpp_g). }
    have [Vmx [HVmx Hfid_mx]] :=
      @fid_iii_uhl_iso_mx R
        (dim 'H[H]_(A :|: B)) (dim 'H[H]_C0)
        (dim 'H[H]_(Cp :|: Cpp))
        rho_src theta_tgt (h2mx rhoAB)
        (h2mx (pi_A \O sigma_B : 'F[H]_(A :|: B)))
        HdimC_CpCpp Hrho_src_den Hrho_src_rank Hrho_src_ptr
        Htheta_tgt_den Htheta_tgt_rank Htheta_tgt_ptr.
    pose Vraw : 'F[H]_(C0, Cp :|: Cpp) := mx2h Vmx.
    have HVraw_iso : Vraw \is isolf.
    { apply/isolfP; apply/h2mx_inj.
      by rewrite h2mx_comp h2mx_adj /Vraw mx2hK h2mx1 HVmx. }
    pose V_star : 'FI[H]_(C0, Cp :|: Cpp) := IsoLf_Build HVraw_iso.
    exists V_star, tau_star, target_star, target_full.
    split; first exact: Htau_den1.
    split; first exact: Htarget_den1.
    split; first exact: Htarget_eq.
    split; first exact: Htarget_full_den1.
    split; first exact: Htarget_full_rank.
    split; first exact: Htarget_full_ptr.
    split; first exact: Htarget_full_ptr_star.
    rewrite /V_star /Vraw mx2hK.
    exact: Hfid_mx. }
  have Hobjective_bridge_M13d :
      forall sigma_B : 'F[H]_B,
        sigma_B \is den1lf ->
        exists (V_star : 'FI[H]_(C0, Cp :|: Cpp))
               (tau_star : 'F[H]_Cpp)
               (Rext target_star : 'F[H]_(A :|: Cp :|: Cpp)),
          Rext =
          (castlf (eqA_CpCpp, eqA_CpCpp)
            ((((\1 : 'F[H]_A) \⊗ V_star) \o rhoAC \o
              (((\1 : 'F[H]_A) \⊗ V_star)^A)) :
              'F[H]_(A :|: (Cp :|: Cpp)))) /\
          tau_star \is den1lf /\
          target_star \is den1lf /\
          target_star =
            ((gamma_ACp \O tau_star) : 'F[H]_(A :|: Cp :|: Cpp)) /\
          (gfid rhoAB
             (pi_A \O sigma_B : 'F[H]_(A :|: B))) ^+ 2 <=
          (gfid Rext target_star) ^+ 2.
  { move=> sigma_B Hsigma_B_den1.
    have [V_star [tau_star [target_star [target_full Hpack]]]] :=
      Hmax_uhlmann_witness sigma_B Hsigma_B_den1.
    case: Hpack => Htau_den1 [Htarget_den1 [Htarget_eq
      [Htarget_full_den1 [Htarget_full_rank [Htarget_full_ptr
      [Htarget_full_ptr_star Hfid_mx]]]]]].
    pose W_iso : 'F[H]_(A :|: C0, A :|: (Cp :|: Cpp)) :=
      (\1 : 'F[H]_A) \⊗ V_star.
    pose rho_ext_raw : 'F[H]_(A :|: (Cp :|: Cpp)) :=
      W_iso \o rhoAC \o W_iso^A.
    pose Rext : 'F[H]_(A :|: Cp :|: Cpp) :=
      castlf (eqA_CpCpp, eqA_CpCpp) rho_ext_raw.
    pose W_AB : 'F[H]_(A :|: B :|: C0,
                       A :|: B :|: (Cp :|: Cpp)) :=
      (\1 : 'F[H]_(A :|: B)) \⊗ V_star.
    pose rho_full_AB : 'F[H]_(A :|: B :|: (Cp :|: Cpp)) :=
      W_AB \o rhoABC \o W_AB^A.
    pose rho_full_RB : 'F[H]_((A :|: Cp :|: Cpp) :|: B) :=
      castlf (esym eqACpCpp_B_AB_CpCpp_g,
              esym eqACpCpp_B_AB_CpCpp_g) rho_full_AB.
    pose target_full_RB : 'F[H]_((A :|: Cp :|: Cpp) :|: B) :=
      castlf (esym eqACpCpp_B_AB_CpCpp_g,
              esym eqACpCpp_B_AB_CpCpp_g) target_full.
    have Hrho_full_RB_psd : rho_full_RB \is psdlf.
    { rewrite /rho_full_RB.
      apply: castlf_psdlf.
      rewrite /rho_full_AB qualifE !h2mx_comp h2mx_adj.
      have Hrho_mx_psd : h2mx rhoABC \is psdmx
        by move: Hrho_psd; rewrite qualifE.
      exact: psdmx_bimap_closed_gen Hrho_mx_psd. }
    have Htarget_full_RB_psd : target_full_RB \is psdlf.
    { rewrite /target_full_RB.
      exact: castlf_psdlf (den1lf_psd Htarget_full_den1). }
    have Hsource_ptr :
        ptrace_cast disACpCpp_B_g rho_full_RB = Rext.
    { pose W_iso_B :
          'F[H]_(A :|: C0 :|: B, A :|: (Cp :|: Cpp) :|: B) :=
        W_iso \⊗ (\1 : 'F[H]_B).
      pose rho_full_acb : 'F[H]_(A :|: (Cp :|: Cpp) :|: B) :=
        W_iso_B \o rhoABC_acb \o W_iso_B^A.
      have disACpCpp_B : [disjoint A :|: (Cp :|: Cpp) & B].
      { have disCp_B : [disjoint Cp & B] by rewrite disjoint_sym.
        have disCpp_B : [disjoint Cpp & B] by rewrite disjoint_sym.
        have disCpCpp_B : [disjoint Cp :|: Cpp & B]
          by rewrite disjointUX disCp_B disCpp_B.
        by rewrite disjointUX disAB disCpCpp_B. }
      have Hfull_marg_raw :
          ptrace_cast disACpCpp_B rho_full_acb = rho_ext_raw.
      { apply/h2mx_inj.
        rewrite /rho_full_acb /rho_ext_raw.
        rewrite (h2mx_ptrace_cast_ptrace2 disACpCpp_B).
        rewrite !h2mx_comp h2mx_adj.
        rewrite (h2mx_tenf W_iso (\1 : 'F[H]_B)) h2mx1.
        rewrite adjmxM.
        set Tout := @tenv_mxU R L H (A :|: (Cp :|: Cpp)) B.
        set Tin := @tenv_mxU R L H (A :|: C0) B.
        set Wmx := h2mx W_iso.
        have HToutK : Tout^*t *m Tout = 1%:M.
        { have /unitarymxK : Tout^*t \is unitarymx :=
            tenv_mxU_adj_unitarymx disACpCpp_B.
          by rewrite adjmxK. }
        rewrite -/Tout -/Wmx -/Tin adjmxK adjmxM.
        rewrite !mulmxA HToutK !mul1mx.
        rewrite -!mulmxA HToutK ?mulmx1 //.
        rewrite adjmx_tens adjmx1.
        have HrhoAC_mx :
            h2mx rhoAC = ptrace2 (Tin^*t *m h2mx rhoABC_acb *m Tin).
        { by rewrite HrhoAC_recast (h2mx_ptrace_cast_ptrace2 disAC_B). }
        transitivity
          (ptrace2
            ((Wmx *t (1%:M : 'M[C]_(dim 'H[H]_B))) *m
             (Tin^*t *m h2mx rhoABC_acb *m Tin) *m
             (Wmx^*t *t (1%:M : 'M[C]_(dim 'H[H]_B))))).
        { congr ptrace2.
          by rewrite !mulmxA. }
        rewrite ptrace2_tens_id_sandwich.
        by rewrite -HrhoAC_mx h2mx_adj -/Wmx !mulmxA. }
      have eqFullAB_CpCpp :
          A :|: (Cp :|: Cpp) :|: B = A :|: B :|: (Cp :|: Cpp).
      { apply/setP=> x.
        rewrite !inE.
        by case: (x \in A); case: (x \in B);
          case: (x \in Cp); case: (x \in Cpp). }
      have Hfull_cast_form :
          castlf (eqFullAB_CpCpp, eqFullAB_CpCpp) rho_full_acb =
          rho_full_AB.
      { rewrite /rho_full_acb /rhoABC_acb /W_iso_B /W_iso
          /rho_full_AB /W_AB.
        to_Fnd.
        rewrite -tenF11.
        by rewrite -!tenFA
          (tenFC (to_Fnd V_star) (to_Fnd (\1 : 'F[H]_B))) !tenFA. }
      pose eqACpCpp_B := f_equal (fun S : {set L} => S :|: B) eqA_CpCpp.
      have Hrho_RB_cast :
          rho_full_RB =
          castlf (eqACpCpp_B, eqACpCpp_B) rho_full_acb.
      { rewrite /rho_full_RB -Hfull_cast_form castlf_comp.
        by congr (castlf (_, _) _); exact: eq_irrelevance. }
      rewrite Hrho_RB_cast /Rext -Hfull_marg_raw.
      rewrite /ptrace_cast /ptrace_cast_gen.
      have eq_res :
          (A :|: (Cp :|: Cpp) :|: B) :\: B =
          ((A :|: Cp :|: Cpp) :|: B) :\: B
        by rewrite eqACpCpp_B.
      rewrite (ptracelf_castlf_eq eqACpCpp_B eq_res).
      rewrite !castlf_comp.
      by congr (castlf (_, _) _); exact: eq_irrelevance. }
    have Htarget_ptr :
        ptrace_cast disACpCpp_B_g target_full_RB = target_star.
    { exact: Htarget_full_ptr_star. }
    have Hgfid_full_eq :
        gfid rho_full_RB target_full_RB =
        gfid rhoAB (pi_A \O sigma_B : 'F[H]_(A :|: B)).
    { have Hgfid_cast :
          gfid rho_full_RB target_full_RB =
          gfid rho_full_AB target_full.
      { rewrite /rho_full_RB /target_full_RB /gfid !h2mx_castlf.
        by rewrite gfid_cast_mx. }
      have Hrho_full_AB_psd : rho_full_AB \is psdlf.
      { rewrite /rho_full_AB qualifE !h2mx_comp h2mx_adj.
        have Hrho_mx_psd : h2mx rhoABC \is psdmx
          by move: Hrho_psd; rewrite qualifE.
        exact: psdmx_bimap_closed_gen Hrho_mx_psd. }
      have Hrho_full_AB_den : rho_full_AB \is denlf.
      { apply/denlfP; split; first exact: Hrho_full_AB_psd.
        have disAB_C0 : [disjoint A :|: B & C0]
          by rewrite disjointUX disAC disBC.
        have HW_AB_iso : W_AB \is isolf.
        { apply/isolfP.
          by rewrite /W_AB tenf_adj -tenf_comp ?disAB_C0
            ?disAB_CpCpp_g // isofE isofE tenf11. }
        have HWi : W_AB^A \o W_AB = \1 by move: HW_AB_iso => /isolfP.
        by rewrite /rho_full_AB lftraceC !comp_lfunA HWi
          comp_lfun1l; exact: denlf_trlf Hrho_den. }
      have Htarget_AB_den1 :
          (pi_A \O sigma_B : 'F[H]_(A :|: B)) \is den1lf.
      { apply/den1lfP; split.
        - rewrite -Htarget_full_ptr.
          exact: ptrace_cast_gen_psdlf (den1lf_psd Htarget_full_den1).
        - rewrite -Htarget_full_ptr /ptrace_cast /ptrace_cast_gen.
          rewrite castlf_trlfE.
          have /cptpP [_ /tpmapP Htp] :=
            @ptraceso_qc R L H (Cp :|: Cpp) (A :|: B :|: (Cp :|: Cpp)).
          by rewrite Htp (den1lf_trlf Htarget_full_den1). }
      have Hgfid_eq_fid : forall (S : {set L}) (x y : 'F[H]_S),
          x \is denlf -> y \is den1lf -> gfid x y = fidelity x y.
      { move=> S x y Hxd Hyd.
        have Hx : x \is psdlf := denlf_psd Hxd.
        have Hy : y \is psdlf := den1lf_psd Hyd.
        have Hxm : h2mx x \is psdmx by move: Hx; rewrite qualifE.
        have Hym : h2mx y \is psdmx by move: Hy; rewrite qualifE.
        have Hytr1 : \tr (h2mx y) = 1
          by move: (den1lf_trlf Hyd); rewrite /lftrace.
        have Hxtr_real : \tr (h2mx x) \is Num.real :=
          ger0_real (psdlf_trlf Hx).
        have Hxtr : @complex.Re R (\tr (h2mx x)) <= 1.
        { move: (denlf_trlf Hxd).
          by rewrite /lftrace -(RRe_real Hxtr_real) lecR. }
        rewrite /gfid (gfid_sym_mx Hxm Hym).
        rewrite (gfid_eq_fid_tr1_mx Hym Hxm Hytr1 Hxtr).
        rewrite /fidelity !h2mx_comp !sqrtH_h2mx.
          exact: (fid_i_sym_mx Hym Hxm). }
      rewrite Hgfid_cast.
      rewrite (Hgfid_eq_fid _ rho_full_AB target_full
        Hrho_full_AB_den Htarget_full_den1).
      rewrite (Hgfid_eq_fid _ rhoAB
        (pi_A \O sigma_B : 'F[H]_(A :|: B))
        HrhoAB_den Htarget_AB_den1).
      rewrite /fidelity !h2mx_comp !sqrtH_h2mx.
      pose Uin := @tenv_mxU R L H (A :|: B) C0.
      pose Uout := @tenv_mxU R L H (A :|: B) (Cp :|: Cpp).
      pose Vmx := h2mx V_star.
      pose Tmx := (1%:M : 'M[C]_(dim 'H[H]_(A :|: B))) *t Vmx.
      have HUout_adj : Uout^*t \is unitarymx :=
        tenv_mxU_adj_unitarymx disAB_CpCpp_g.
      have Hrho_full_AB_mx_psd : h2mx rho_full_AB \is psdmx
        by move: Hrho_full_AB_psd; rewrite qualifE.
      have Htarget_full_mx_psd : h2mx target_full \is psdmx
        by move: (den1lf_psd Htarget_full_den1); rewrite qualifE.
      have Hfid_unit :
          @complex.Re R
            (trnorm (sqrtmx (Uout^*t *m h2mx rho_full_AB *m Uout) *m
              sqrtmx (Uout^*t *m h2mx target_full *m Uout))) =
          @complex.Re R
            (trnorm (sqrtmx (h2mx rho_full_AB) *m
              sqrtmx (h2mx target_full))).
      { clearbody Uout.
        move: Uout HUout_adj Hrho_full_AB_mx_psd Htarget_full_mx_psd.
        case: _ / (tenv_dim disAB_CpCpp_g) =>
          Uout HUout_adj Hrho_full_AB_mx_psd Htarget_full_mx_psd.
        have := fid_unitary_conj_mx HUout_adj Hrho_full_AB_mx_psd
          Htarget_full_mx_psd.
        by rewrite !adjmxK. }
      rewrite -Hfid_unit.
      have HUoutK : Uout^*t *m Uout = 1%:M
        by have := unitarymxK HUout_adj; rewrite adjmxK.
      have Hrho_full_AB_prod :
          Uout^*t *m h2mx rho_full_AB *m Uout =
          Tmx *m (Uin^*t *m h2mx rhoABC *m Uin) *m Tmx^*t.
      { rewrite /rho_full_AB /W_AB !h2mx_comp h2mx_adj
          !h2mx_tenf !h2mx1.
        rewrite -/Uout -/Uin -/Vmx -/Tmx adjmxM.
        rewrite !mulmxA -mulmxA HUoutK mul1mx.
        rewrite adjmxK adjmxM -/Tmx.
        by rewrite -!mulmxA [Uout^*t *m Uout]HUoutK !mulmx1 !mulmxA. }
      rewrite Hrho_full_AB_prod.
      exact: Hfid_mx. }
    have Hmono := @gfid_ptr_mono R L H (A :|: Cp :|: Cpp) B
      disACpCpp_B_g rho_full_RB target_full_RB
      Hrho_full_RB_psd Htarget_full_RB_psd dim_proper.
    rewrite Hsource_ptr Htarget_ptr Hgfid_full_eq in Hmono.
    have Hleft_ge0 :
        0 <= gfid rhoAB (pi_A \O sigma_B : 'F[H]_(A :|: B)).
    { rewrite /gfid.
      have Htarget_psd : (pi_A \O sigma_B : 'F[H]_(A :|: B)) \is psdlf.
      { rewrite -Htarget_full_ptr.
        exact: ptrace_cast_gen_psdlf (den1lf_psd Htarget_full_den1). }
      exact: gfid_ge0_mx (psdlf_h2mx HrhoAB_psd)
        (psdlf_h2mx Htarget_psd). }
    have Hright_ge0 : 0 <= gfid Rext target_star.
    { rewrite /gfid.
      have HR_psd : Rext \is psdlf.
      { rewrite -Hsource_ptr.
        exact: ptrace_cast_psdlf Hrho_full_RB_psd. }
      exact: gfid_ge0_mx (psdlf_h2mx HR_psd)
        (psdlf_h2mx (den1lf_psd Htarget_den1)). }
    have Hsq_le :=
      lerXn2r 2 Hleft_ge0 Hright_ge0 Hmono.
    exists V_star, tau_star, Rext, target_star.
    split.
    { by rewrite /Rext /rho_ext_raw /W_iso. }
    split; first exact: Htau_den1.
    split; first exact: Htarget_den1.
    split; first exact: Htarget_eq.
    exact: Hsq_le. }
  pose Eomni_sq : set R := fun v : R =>
    exists (V : 'FI[H]_(C0, Cp :|: Cpp))
           (tau : 'F[H]_Cpp),
      tau \is den1lf /\
      v =
      (gfid
        (((\1 : 'F[H]_A) \⊗ V) \o rhoAC \o
          (((\1 : 'F[H]_A) \⊗ V)^A))
        (castlf
          (esym (minmax.eqABpBpp A Cp Cpp),
           esym (minmax.eqABpBpp A Cp Cpp))
          (minmax.gamma_ABp dimA_Cp \O tau))) ^+ 2.
  pose Emax_sq : set R := fun v =>
    exists sigma_B : 'F[H]_B,
      sigma_B \is den1lf /\
      v =
      (gfid rhoAB
        (pi_A \O sigma_B : 'F[H]_(A :|: B))) ^+ 2.
  pose Emin_sq : set R := fun v =>
    exists (V_star : 'FI[H]_(C0, Cp :|: Cpp))
           (tau_star : 'F[H]_Cpp),
      tau_star \is den1lf /\
      v =
      (gfid
        (castlf (eqA_CpCpp, eqA_CpCpp)
          ((((\1 : 'F[H]_A) \⊗ V_star) \o rhoAC \o
            (((\1 : 'F[H]_A) \⊗ V_star)^A)) :
            'F[H]_(A :|: (Cp :|: Cpp))))
        ((gamma_ACp \O tau_star) : 'F[H]_(A :|: Cp :|: Cpp))) ^+ 2.
  have HEmax_has_sup : has_sup Emax_sq.
  { have Htarget_den :
        forall sigma_B : 'F[H]_B,
          sigma_B \is den1lf ->
          (pi_A \O sigma_B : 'F[H]_(A :|: B)) \is denlf.
    { move=> sigma_B Hsigma_den1.
      have Htarget_psd :
          (pi_A \O sigma_B : 'F[H]_(A :|: B)) \is psdlf.
      { have Hten :
            (pi_A \O sigma_B : 'F[H]_(A :|: B)) =
            (pi_A \⊗ sigma_B).
        { by apply: to_Fnd_inj; rewrite (sdotFT _ _ disAB) to_Fnd_tenE. }
        rewrite Hten psdlfE.
        apply: tenf_ge0; first exact: disAB.
        - by move: Hpi_A_psd; rewrite psdlfE.
        - by move: (den1lf_psd Hsigma_den1); rewrite psdlfE. }
      have Htarget_tr1 :
          \Tr (pi_A \O sigma_B : 'F[H]_(A :|: B)) = 1.
      { rewrite (lftrace_sdot_disj _ _ disAB).
        by rewrite Hpi_A_tr1 (den1lf_trlf Hsigma_den1) mul1r. }
      apply/denlfP; split=> //.
      by rewrite Htarget_tr1. }
    split.
    - pose sigmaI_B : 'F[H]_B :=
        ((dim 'H[H]_B)%:R^-1)%:C *: (\1 : 'F[H]_B).
      have HsigmaI_B_psd : sigmaI_B \is psdlf.
      { rewrite /sigmaI_B.
        apply: psdlfZ; first by rewrite lecR invr_ge0.
        by rewrite qualifE h2mx1; exact: psdmx1. }
      have HsigmaI_B_tr1 : \Tr sigmaI_B = 1.
      { have Hdim_neq0 : ((dim 'H[H]_B)%:R : R) != 0.
        { apply: lt0r_neq0.
          by rewrite ltr0n dim_proper. }
        rewrite /sigmaI_B linearZ /= /lftrace h2mx1 mxtrace1.
        rewrite -natrC -rmorphM /= mulrC (mulfV Hdim_neq0).
        exact: rmorph1. }
      have HsigmaI_B_den1 : sigmaI_B \is den1lf
        by apply/den1lfP; split.
      exists ((gfid rhoAB
        (pi_A \O sigmaI_B : 'F[H]_(A :|: B))) ^+ 2).
      exists sigmaI_B; split=> //.
    - exists 1 => v [sigma_B [Hsigma_den1 ->]].
      have Htarget_mx_den :
          h2mx (pi_A \O sigma_B : 'F[H]_(A :|: B)) \is denmx.
      { by move: (Htarget_den sigma_B Hsigma_den1); rewrite qualifE. }
      have HrhoAB_mx_den : h2mx rhoAB \is denmx
        by move: HrhoAB_den; rewrite qualifE.
      have Hg_ge0 :
          0 <= gfid rhoAB
            (pi_A \O sigma_B : 'F[H]_(A :|: B)).
      { rewrite /gfid.
        exact: gfid_ge0_mx (denmx_psd HrhoAB_mx_den)
          (denmx_psd Htarget_mx_den). }
      have Hg_le1 :
          gfid rhoAB
            (pi_A \O sigma_B : 'F[H]_(A :|: B)) <= 1.
      { rewrite /gfid.
        exact: gfid_le1_mx HrhoAB_mx_den Htarget_mx_den. }
      have := @lerXn2r R 2
        (gfid rhoAB
          (pi_A \O sigma_B : 'F[H]_(A :|: B))) 1 Hg_ge0 ler01 Hg_le1.
      by rewrite expr1n. }
  have HEmin_has_sup : has_sup Emin_sq.
  { split.
    - have [V0 _] :=
        @labelled_isolf_via_dim_le R L H C0 (Cp :|: Cpp) HdimC_CpCpp.
      pose psiCpp := (deltav (@idx_default R L H Cpp) : 'H[H]_Cpp).
      pose tau0 : 'F[H]_Cpp := [> psiCpp ; psiCpp <].
      have Htau0_den1 : tau0 \is den1lf
        by exact: proj1lf_den1 (outp_proj1 psiCpp).
      exists ((gfid
        (castlf (eqA_CpCpp, eqA_CpCpp)
          ((((\1 : 'F[H]_A) \⊗ V0) \o rhoAC \o
            (((\1 : 'F[H]_A) \⊗ V0)^A)) :
            'F[H]_(A :|: (Cp :|: Cpp))))
        ((gamma_ACp \O tau0) : 'F[H]_(A :|: Cp :|: Cpp))) ^+ 2).
      exists V0, tau0; by split.
    - exists 1 => v [V [tau [Htau_den1 ->]]].
      pose W : 'F[H]_(A :|: C0, A :|: (Cp :|: Cpp)) :=
        (\1 : 'F[H]_A) \⊗ V.
      pose rho_ext_raw : 'F[H]_(A :|: (Cp :|: Cpp)) :=
        W \o rhoAC \o W^A.
      pose R0 : 'F[H]_(A :|: Cp :|: Cpp) :=
        castlf (eqA_CpCpp, eqA_CpCpp) rho_ext_raw.
      pose target0 : 'F[H]_(A :|: Cp :|: Cpp) :=
        gamma_ACp \O tau.
      have HW_iso : W \is isolf.
      { apply/isolfP.
        by rewrite /W tenf_adj -tenf_comp ?disAC ?disA_CpCpp //
          isofE isofE tenf11. }
      have HWi : W^A \o W = \1 by move: HW_iso => /isolfP.
      have HR0_psd : R0 \is psdlf.
      { rewrite /R0.
        apply: castlf_psdlf.
        rewrite /rho_ext_raw qualifE !h2mx_comp h2mx_adj.
        have HrhoAC_mx_psd : h2mx rhoAC \is psdmx
          by move: HrhoAC_psd; rewrite qualifE.
        exact: psdmx_bimap_closed_gen HrhoAC_mx_psd. }
      have HR0_den : R0 \is denlf.
      { apply/denlfP; split; first exact: HR0_psd.
        rewrite /R0 castlf_trlfE /rho_ext_raw lftraceC !comp_lfunA.
        by rewrite HWi comp_lfun1l; exact: denlf_trlf HrhoAC_den. }
      have Htarget0_den1 : target0 \is den1lf.
      { have Htau_psd : tau \is psdlf := den1lf_psd Htau_den1.
        have Hgamma_le : (0 : 'F[H]_(A :|: Cp)) ⊑ gamma_ACp
          by move: (den1lf_psd Hgamma_ACp_den1); rewrite psdlfE.
        have Htau_le : (0 : 'F[H]_Cpp) ⊑ tau
          by move: Htau_psd; rewrite psdlfE.
        have Htarget0_psd : target0 \is psdlf.
        { have -> :
              target0 =
              ((gamma_ACp \⊗ tau) : 'F[H]_(A :|: Cp :|: Cpp)).
          { apply: to_Fnd_inj.
            by rewrite /target0 (sdotFT _ _ disACp_Cpp) to_Fnd_tenE. }
          rewrite psdlfE.
          exact: tenf_ge0 disACp_Cpp Hgamma_le Htau_le. }
        apply/den1lfP; split; first exact: Htarget0_psd.
        rewrite /target0 (lftrace_sdot_disj _ _ disACp_Cpp).
        by rewrite (den1lf_trlf Hgamma_ACp_den1)
          (den1lf_trlf Htau_den1) mul1r. }
      have HR0_mx_den : h2mx R0 \is denmx
        by move: HR0_den; rewrite qualifE.
      have Htarget0_mx_den : h2mx target0 \is denmx
        by move: (den1lf_den Htarget0_den1); rewrite qualifE.
      have Hg_ge0 : 0 <= gfid R0 target0.
      { rewrite /gfid.
        exact: gfid_ge0_mx (denmx_psd HR0_mx_den)
          (denmx_psd Htarget0_mx_den). }
      have Hg_le1 : gfid R0 target0 <= 1.
      { rewrite /gfid.
        exact: gfid_le1_mx HR0_mx_den Htarget0_mx_den. }
      have := @lerXn2r R 2 (gfid R0 target0) 1
        Hg_ge0 ler01 Hg_le1.
      by rewrite expr1n. }
  have Hsup_sq_eq : sup Emax_sq = sup Emin_sq.
  { apply/eqP; rewrite eq_le; apply/andP; split.
    - apply: ExtNumTopology.sup_least_ubound; first exact: HEmax_has_sup.
      move=> v [sigma_B [Hsigma_B_den1 ->]].
      have [V_star [tau_star [Rext [target_star
        [HR_eq [Htau_den1 [Htarget_den1 [Htarget_eq Hle]]]]]]]] :=
        Hobjective_bridge_M13d sigma_B Hsigma_B_den1.
      have HEmin_R : Emin_sq ((gfid Rext target_star) ^+ 2).
      { exists V_star; exists tau_star.
        split; first exact: Htau_den1.
        by rewrite HR_eq Htarget_eq. }
      have /ubP Hub := sup_upper_bound HEmin_has_sup.
      exact: le_trans Hle (Hub _ HEmin_R).
    - apply: ExtNumTopology.sup_least_ubound; first exact: HEmin_has_sup.
      move=> v [V_star [tau_star [Htau_den1 ->]]].
      have [Rext [taubar [target_star [phi_Cpp [sigma_Bmax Hbridge]]]]] :=
        Hobjective_bridge_M13c V_star tau_star Htau_den1.
      case: Hbridge => HR_eq [Htarget_eq [HR_den [Htaubar_den1 [Htarget_den1
        [Hphi_Cpp_den1 [Hsigma_Bmax_den1 [Htarget_ptr
        [Htaubar_ptr [Htaubar_eq [Hpd_AB [Hpd_R Hpd_ptr]]]]]]]]]]].
      have HEmax_sigma :
          Emax_sq
            ((gfid rhoAB
              (pi_A \O sigma_Bmax : 'F[H]_(A :|: B))) ^+ 2).
      { exists sigma_Bmax; split=> //. }
      have Hsq_le :
          (gfid
            (castlf (eqA_CpCpp, eqA_CpCpp)
              ((((\1 : 'F[H]_A) \⊗ V_star) \o rhoAC \o
                (((\1 : 'F[H]_A) \⊗ V_star)^A)) :
                'F[H]_(A :|: (Cp :|: Cpp))))
            ((gamma_ACp \O tau_star) : 'F[H]_(A :|: Cp :|: Cpp))) ^+ 2
          <=
          (gfid rhoAB
            (pi_A \O sigma_Bmax : 'F[H]_(A :|: B))) ^+ 2.
      { rewrite -HR_eq -Htarget_eq.
        set a := gfid Rext target_star.
        set b := gfid rhoAB
          (pi_A \O sigma_Bmax : 'F[H]_(A :|: B)).
        have HR_mx_den : h2mx Rext \is denmx
          by move: HR_den; rewrite qualifE.
        have Htarget_mx_den1 : h2mx target_star \is den1mx
          by move: Htarget_den1; rewrite qualifE.
        have Htarget_mx_den : h2mx target_star \is denmx :=
          den1mx_den Htarget_mx_den1.
        have HrhoAB_mx_den : h2mx rhoAB \is denmx
          by move: HrhoAB_den; rewrite qualifE.
        have Hpi_psd : pi_A \is psdlf.
        { rewrite /pi_A.
          apply: psdlfZ; first by rewrite lecR invr_ge0.
          by rewrite qualifE h2mx1; exact: psdmx1. }
        have Hpi_tr1 : \Tr pi_A = 1.
        { have Hdim_neq0 : ((dim 'H[H]_A)%:R : R) != 0.
          { apply: lt0r_neq0.
            by rewrite ltr0n dim_proper. }
          rewrite /pi_A linearZ /= /lftrace h2mx1 mxtrace1.
          rewrite -natrC -rmorphM /= mulrC (mulfV Hdim_neq0).
          exact: rmorph1. }
        have Hmax_target_psd :
            (pi_A \O sigma_Bmax : 'F[H]_(A :|: B)) \is psdlf.
        { have Hten :
              (pi_A \O sigma_Bmax : 'F[H]_(A :|: B)) =
              (pi_A \⊗ sigma_Bmax).
          { by apply: to_Fnd_inj; rewrite (sdotFT _ _ disAB) to_Fnd_tenE. }
          rewrite Hten psdlfE.
          apply: tenf_ge0; first exact: disAB.
          - by move: Hpi_psd; rewrite psdlfE.
          - by move: (den1lf_psd Hsigma_Bmax_den1); rewrite psdlfE. }
        have Hmax_target_tr1 :
            \Tr (pi_A \O sigma_Bmax : 'F[H]_(A :|: B)) = 1.
        { rewrite (lftrace_sdot_disj _ _ disAB).
          by rewrite Hpi_tr1 (den1lf_trlf Hsigma_Bmax_den1) mul1r. }
        have Hmax_target_den :
            (pi_A \O sigma_Bmax : 'F[H]_(A :|: B)) \is denlf.
        { apply/denlfP; split=> //.
          by rewrite Hmax_target_tr1. }
        have Hmax_target_mx_den :
            h2mx (pi_A \O sigma_Bmax : 'F[H]_(A :|: B)) \is denmx.
        { by move: Hmax_target_den; rewrite qualifE. }
        have Ha0 : 0 <= a.
        { rewrite /a /gfid.
          exact: gfid_ge0_mx (denmx_psd HR_mx_den)
            (denmx_psd Htarget_mx_den). }
        have Ha1 : a <= 1.
        { rewrite /a /gfid.
          exact: gfid_le1_mx HR_mx_den Htarget_mx_den. }
        have Hb0 : 0 <= b.
        { rewrite /b /gfid.
          exact: gfid_ge0_mx (denmx_psd HrhoAB_mx_den)
            (denmx_psd Hmax_target_mx_den). }
        have Hb1 : b <= 1.
        { rewrite /b /gfid.
          exact: gfid_le1_mx HrhoAB_mx_den Hmax_target_mx_den. }
        have Hpd : Num.sqrt (1 - b ^+ 2) <= Num.sqrt (1 - a ^+ 2).
        { by move: Hpd_AB; rewrite /pur_dist -/a -/b. }
        have Hpd_sq := lerXn2r 2 (sqrtr_ge0 (1 - b ^+ 2))
          (sqrtr_ge0 (1 - a ^+ 2)) Hpd.
        move: Hpd_sq.
        rewrite !sqr_sqrtr ?subr_ge0.
        - by rewrite lerD2l lerN2.
        - have := @lerXn2r R 2 a 1 Ha0 ler01 Ha1.
          by rewrite expr1n.
        - have := @lerXn2r R 2 b 1 Hb0 ler01 Hb1.
          by rewrite expr1n. }
      have /ubP Hub := sup_upper_bound HEmax_has_sup.
      exact: le_trans Hsq_le (Hub _ HEmax_sigma). }
  have Hmin_sup_eq : sup Eomni_sq = sup Emin_sq.
  { have Hsq_cast_gen :
        forall (raw : 'F[H]_(A :|: (Cp :|: Cpp)))
               (sig : 'F[H]_(A :|: Cp :|: Cpp)),
          (gfid raw
             (castlf
               (esym (minmax.eqABpBpp A Cp Cpp),
                esym (minmax.eqABpBpp A Cp Cpp)) sig)) ^+ 2 =
          (gfid (castlf (eqA_CpCpp, eqA_CpCpp) raw) sig) ^+ 2.
    { move=> raw sig.
      rewrite /gfid !h2mx_castlf.
      set e := f_equal (fun T : {set L} => dim 'H[H]_T) eqA_CpCpp.
      have He : f_equal (fun T : {set L} => dim 'H[H]_T)
                  (esym (minmax.eqABpBpp A Cp Cpp)) = esym e
        by apply: eq_irrelevance.
      rewrite He.
      move: (h2mx raw) (h2mx sig) => X Y.
      rewrite -[in RHS](gfid_cast_mx (esym e) (castmx (e, e) X) Y).
      by rewrite !castmx_comp /= !etrans_esym !castmx_id. }
    have Hset_eq : Eomni_sq = Emin_sq.
    { apply/funext=> v; apply/propext; split.
      - move=> [V [tau [Htau_den1 ->]]].
        exists V, tau; split; first exact: Htau_den1.
        exact: (Hsq_cast_gen _ _).
      - move=> [V [tau [Htau_den1 ->]]].
        exists V, tau; split; first exact: Htau_den1.
        by symmetry; exact: (Hsq_cast_gen _ _). }
    by rewrite Hset_eq. }
  pose S_AB := A :|: B.
  have eqB_set : S_AB :&: B = B.
  { apply/setP=> x.
    by rewrite /S_AB !inE; case: (x \in A); case: (x \in B). }
  have eqA_set : S_AB :\: B = A.
  { rewrite /S_AB; exact: setDU_r disAB. }
  have eqST_set : (S_AB :\: B) :|: (S_AB :&: B) = S_AB.
  { by rewrite finset.setUC finset.setID. }
  have Hhmax_target_eq :
      forall sigma : 'F[H]_(S_AB :&: B),
        castlf (eqST_set, eqST_set)
          (((dim 'H[H]_(S_AB :\: B))%:R^-1)%:C *:
            ((\1 : 'F[H]_(S_AB :\: B)) \O sigma)) =
        (pi_A \O castlf (eqB_set, eqB_set) sigma : 'F[H]_(A :|: B)).
  { move=> sigma.
    rewrite /pi_A.
    have HdimA : dim 'H[H]_(S_AB :\: B) = dim 'H[H]_A
      by rewrite eqA_set.
    rewrite HdimA linearZ /= sdotfZl.
    congr (_ *: _).
    to_Fnd.
    f_equal.
    apply Fnd_eq1.
    exact: eqA_set. }
  pose dA : R := (dim 'H[H]_A)%:R.
  have HdA_pos : 0 < dA by rewrite /dA ltr0n dim_proper.
  have Hhmax_sup : has_sup [set v : R | hmax_feasible B rhoAB v] :=
    @hmax_has_sup R L H S_AB B rhoAB
      HrhoAB_psd HrhoAB_tr_le HrhoAB_tr_pos_R.
  have Hfeas_unpack :
      forall v : R,
        hmax_feasible B rhoAB v ->
        exists (w : R) (sigma_B : 'F[H]_B),
          [/\ Emax_sq w,
              0 < dA * w &
              v = log2 (dA * w)].
  { move=> v [sigma [Hsigma_den Hve]].
    pose sigma_B : 'F[H]_B := castlf (eqB_set, eqB_set) sigma.
    pose w := (gfid rhoAB
      (pi_A \O sigma_B : 'F[H]_(A :|: B))) ^+ 2.
    have Hsigma_B_den : sigma_B \is den1lf.
    { apply/den1lfP; split.
      - exact: castlf_psdlf (den1lf_psd Hsigma_den).
      - by rewrite /sigma_B castlf_trlfE (den1lf_trlf Hsigma_den). }
    exists w, sigma_B.
    have HEw : Emax_sq w.
    { exists sigma_B; by split. }
    split; first exact: HEw.
    - case: (ltP 0 (dA * w)) => // Harg_le0.
      move: Hve.
      rewrite /hmax_feasible /S_AB.
      set e := (X in castlf (X, X) _).
      rewrite (eq_irrelevance e eqST_set).
      rewrite Hhmax_target_eq -/sigma_B /w /dA eqA_set.
      rewrite (elog2_le0 Harg_le0).
      by discriminate.
    - move: Hve.
      rewrite /hmax_feasible /S_AB.
      set e := (X in castlf (X, X) _).
      rewrite (eq_irrelevance e eqST_set).
      rewrite Hhmax_target_eq -/sigma_B /w /dA eqA_set.
      move=> Hve'.
      have Harg_pos : 0 < dA * w.
      { case: (ltP 0 (dA * w)) => // Harg_le0.
        move: Hve'.
        rewrite (elog2_le0 Harg_le0).
        by discriminate. }
      move: Hve'.
      rewrite (elog2_gt0 Harg_pos).
      by case. }
  have HsupEmax_pos : 0 < sup Emax_sq.
  { case: Hhmax_sup => [[v Hv] _].
    have [w [sigma_B [HEw Harg_pos _]]] := Hfeas_unpack v Hv.
    have Hw_pos : 0 < w.
    { by rewrite -(ltr_pM2l HdA_pos) mulr0. }
    have /ubP Hub := sup_upper_bound HEmax_has_sup.
    exact: lt_le_trans Hw_pos (Hub _ HEw). }
  have Hhmax_log :
      hmax B rhoAB = log2 ((dim 'H[H]_A)%:R * sup Emax_sq).
  { apply/eqP; rewrite eq_le; apply/andP; split.
    - apply: hmax_lub; first exact: Hhmax_sup.
      move=> v Hv.
      have [w [sigma_B [HEw Harg_pos Hv_eq]]] := Hfeas_unpack v Hv.
      rewrite Hv_eq /dA.
      apply: log2_le_pos; first exact: Harg_pos.
      apply: ler_wpM2l; first exact: ltW HdA_pos.
      have /ubP Hub := sup_upper_bound HEmax_has_sup.
      exact: Hub.
    - pose h := hmax B rhoAB.
      have Harg_sup_pos : 0 < dA * sup Emax_sq :=
        mulr_gt0 HdA_pos HsupEmax_pos.
      case: (leP (log2 (dA * sup Emax_sq)) h) => // Hh_lt.
      have Htwo_pow_pos : 0 < 2 `^ h by rewrite powR_gt0.
      have Hpow_lt_prod : 2 `^ h < dA * sup Emax_sq.
      { have Hlog_gt : ln (2 `^ h) < ln (dA * sup Emax_sq).
        { have Hln2_unit : ln 2 \is a GRing.unit := unitf_gt0 (@ln2_gt0 R).
          have Htmp : h * ln 2 < ln (dA * sup Emax_sq).
          { have Htmp1 := Hh_lt.
            rewrite -(ltr_pM2r ln2_gt0) in Htmp1.
            rewrite /log2 (divrK Hln2_unit) in Htmp1.
            exact: Htmp1. }
          by rewrite ln_powR. }
        by rewrite -ltr_ln ?powR_gt0. }
      have Hx_lt_sup : (2 `^ h) / dA < sup Emax_sq.
      { by rewrite ltr_pdivrMr // mulrC. }
      have Heps_pos : 0 < sup Emax_sq - (2 `^ h) / dA
        by rewrite subr_gt0.
      have [w HEw Hw_gt] := sup_adherent Heps_pos HEmax_has_sup.
      rewrite subKr in Hw_gt.
      have Hw_pos : 0 < w :=
        lt_trans (divr_gt0 Htwo_pow_pos HdA_pos) Hw_gt.
      have Harg_w_pos : 0 < dA * w := mulr_gt0 HdA_pos Hw_pos.
      case: HEw => sigma_B [Hsigma_B_den Hw_eq].
      pose sigma : 'F[H]_(S_AB :&: B) :=
        castlf (esym eqB_set, esym eqB_set) sigma_B.
      have Hsigma_den : sigma \is den1lf.
      { apply/den1lfP; split.
        - exact: castlf_psdlf (den1lf_psd Hsigma_B_den).
        - by rewrite /sigma castlf_trlfE (den1lf_trlf Hsigma_B_den). }
      have Hsigma_back : castlf (eqB_set, eqB_set) sigma = sigma_B.
      { rewrite /sigma castlf_comp.
        rewrite (eq_irrelevance (etrans (esym eqB_set) eqB_set) (erefl _)).
        by rewrite castlf_id. }
      have Hfeas_w : hmax_feasible B rhoAB (log2 (dA * w)).
      { exists sigma; split; first exact: Hsigma_den.
        rewrite /hmax_feasible /S_AB.
        set e := (X in castlf (X, X) _).
        rewrite (eq_irrelevance e eqST_set).
        rewrite Hhmax_target_eq Hsigma_back -Hw_eq /dA eqA_set.
        by rewrite (elog2_gt0 Harg_w_pos). }
      have Hlog_w_le : log2 (dA * w) <= h.
      { rewrite /h.
        exact: hmax_ub Hhmax_sup Hfeas_w. }
      have Hpow_lt_w : 2 `^ h < dA * w.
      { move: Hw_gt.
        by rewrite ltr_pdivrMr // mulrC. }
      have Hh_lt_logw : h < log2 (dA * w).
      { have Hlog_gt : ln (2 `^ h) < ln (dA * w).
        { have Htmp := Hpow_lt_w.
          by rewrite -ltr_ln ?powR_gt0 // in Htmp. }
        have Hln2_unit : ln 2 \is a GRing.unit := unitf_gt0 (@ln2_gt0 R).
        have Htmp : h * ln 2 < ln (dA * w).
        { move: Hlog_gt.
          by rewrite ln_powR. }
        rewrite -(ltr_pM2r ln2_gt0).
        rewrite /log2 (divrK Hln2_unit).
        exact: Htmp. }
      have := lt_le_trans Hh_lt_logw Hlog_w_le.
      by rewrite ltxx. }
  have Hsup_arg_pos : 0 < (dim 'H[H]_A)%:R * sup Emin_sq.
  { rewrite -Hsup_sq_eq -/dA.
    exact: mulr_gt0 HdA_pos HsupEmax_pos. }
  rewrite -/rhoAB -/rhoAC HrhoAB_hmaxE_fin Hmin_omni Hhmax_log Hsup_sq_eq.
  change (sup [set v | (exists (V : 'FI[H]_(C0, Cp :|: Cpp))
      (tau : 'F[H]_Cpp),
      tau \is den1lf /\
      v =
      (gfid
        (((\1 : 'F[H]_A) \⊗ V) \o rhoAC \o
          (((\1 : 'F[H]_A) \⊗ V)^A))
        (castlf
          (esym (minmax.eqABpBpp A Cp Cpp),
           esym (minmax.eqABpBpp A Cp Cpp))
          (minmax.gamma_ABp dimA_Cp \O tau))) ^+ 2)%R])
    with (sup Eomni_sq).
  rewrite Hmin_sup_eq.
  rewrite (elog2_gt0 Hsup_arg_pos).
  by rewrite oppeK.
Qed.

End MinMaxDual.

End FvqkdReal.
