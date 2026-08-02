(* -------------------------------------------------------------------- *)
(* prop.v — Core LHL lemmas: uniform-to-collision, privacy-amp          *)
(* -------------------------------------------------------------------- *)
(* Module: lhl.prop                                       *)
(* Source: Tomamichel-Schaffner-Smith-Renner, 'Leftover Hashing       *)
(*   Against Quantum Side Information' (IEEE Trans. IT 57:5524 (2011);  *)
(*   arXiv:1002.2436): lemma:uniform-to-collision (Lem. 4) and         *)
(*   lemma:privacy-amp (Lem. 5).                                        *)
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
  cpo mxpred extnum ctopology svd mxnorm hspace hspace_extra.
From quantum.dirac Require Import hstensor setdec.
Import Order.TTheory GRing.Theory Num.Theory Num.Def MxLownerOrder.
Import VectorInternalTheory.
(* --- FVQKD imports --- *)
From utils Require Import exports.
From entropy Require Import def.
From entropy.conv Require Import prop.
From lhl Require Import def dephase util post_hash.
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
(* Definition-level facts moved out of lhl/def.v                       *)
(* ================================================================== *)
Section DistFromUniform.
Variable (L : finType) (H : L -> chsType) (A B : {set L}).
Hypothesis disAB : [disjoint A & B].
(* path: lhl:dist_uniform_lb -> lhl:two_universal_hashing -> *)
(*   bb84:privacy_amplification -> bb84:bb84_secret *)
Lemma dist_uniform_lb (rhoAB : 'F[H]_(A :|: B)) v :
  dist_uniform_feasible rhoAB v -> dist_from_uniform rhoAB <= v.
Proof.
  move=> Hv; apply: ge_inf => //.
  exists 0 => x [sigma [_ [_ ->]]].
  apply: mulr_ge0; first by rewrite invr_ge0 ler0n.
  rewrite /trnormH.
  set M := h2mx _.
  by move: (trnorm_ge0 M); rewrite lecE/= => /andP[_].
Qed.
(* Foundational witness-bound form of def:dist-from-uniform.               *)
(* math: any feasible witness σ_B gives 2·d_u(ρ) ≤ ‖ρ - ω_A ⊗ σ_B‖_1.    *)
(* Reusable by lemma:uniform-to-collision (Lem. 4) and by the             *)
(* specialization σ_B := ρ_B (eqn:uniform-bound-2, Eq. 13).               *)
(* path: lhl:dist_uniform_witness_bound -> lhl:two_universal_hashing -> *)
(*   bb84:privacy_amplification -> bb84:bb84_secret *)
Lemma dist_uniform_witness_bound (rhoAB : 'F[H]_(A :|: B)) (sigmaB : 'F[H]_B) :
  sigmaB \is psdlf ->
  \Tr sigmaB = \Tr (\Tr_(A) rhoAB) ->
  2%:R * dist_from_uniform rhoAB <=
    trnormH (rhoAB - (dim 'H[H]_A)%:R^-1 *: ((\1 : 'F_A) \O sigmaB)).
Proof.
  move=> Psig Htr.
  have Hfeas : dist_uniform_feasible rhoAB
      ((2%:R)^-1 * trnormH
        (rhoAB - (dim 'H[H]_A)%:R^-1 *: ((\1 : 'F_A) \O sigmaB))).
    by exists sigmaB; do ?split.
  have /(ler_wpM2l (ler0n _ 2%N)) := dist_uniform_lb Hfeas.
  by rewrite mulrA mulfV ?mul1r // pnatr_eq0.
Qed.
Lemma dist_uniform_le_trace (rhoAB : 'F[H]_(A :|: B)) :
  rhoAB \is psdlf ->
  dist_from_uniform rhoAB <= @complex.Re R (\Tr rhoAB).
Proof.
  move=> Hrho; have Htr_ptrace_rho : \Tr (\Tr_(A) rhoAB) = \Tr rhoAB.
    by case/cptpP: (@ptraceso_qc R L H A (A :|: B)) => _ /tpmapP ->.
  pose sigmaB : 'F[H]_B := ptrace_castl disAB rhoAB.
  have Hsigma_psd : sigmaB \is psdlf := ptrace_castl_psdlf disAB Hrho.
  have Hsigma_Tr : \Tr sigmaB = \Tr (\Tr_(A) rhoAB).
    by rewrite /sigmaB /ptrace_castl /ptrace_cast_gen -castlf_trlf.
  have Hwb : 2%:R * dist_from_uniform rhoAB <=
    trnormH (rhoAB - (dim 'H[H]_A)%:R^-1 *: ((\1 : 'F_A) \O sigmaB)).
    by apply: dist_uniform_witness_bound.
  have Htwo_inv_ge0 : (0 : R) <= @GRing.inv R 2%:R
    by rewrite invr_ge0 ler0n.
  have Hd_u : dist_from_uniform rhoAB <=
    @GRing.inv R 2%:R *
      trnormH (rhoAB -
        (dim 'H[H]_A)%:R^-1 *: ((\1 : 'F_A) \O sigmaB)).
  {
    have /(ler_wpM2l Htwo_inv_ge0) := Hwb.
    by rewrite mulrA mulVf ?mul1r // pnatr_eq0.
  }
  apply: le_trans Hd_u _.
  have Hbound :
      trnormH (rhoAB -
        (dim 'H[H]_A)%:R^-1 *: ((\1 : 'F_A) \O sigmaB)) <=
      trnormH rhoAB +
        trnormH ((dim 'H[H]_A)%:R^-1 *:
          ((\1 : 'F_A) \O sigmaB)).
    exact: trnormH_triangleB.
  have Htrn_rho : trnormH rhoAB = @complex.Re R (\Tr rhoAB) :=
    trnormH_psd Hrho.
  have Hdim_A_ne0_R : ((dim 'H[H]_A)%:R : R) != 0
    by rewrite pnatr_eq0 -lt0n dim_proper.
  pose invd : R := @GRing.inv R ((dim 'H[H]_A)%:R).
  have Hinv_eq : @GRing.inv C ((dim 'H[H]_A)%:R) = invd%:C.
    by rewrite /invd -natrC -fmorphV.
  have Hinv_ge0 : 0 <= invd by rewrite /invd invr_ge0 ler0n.
  have Htrn_lift :
      trnormH ((dim 'H[H]_A)%:R^-1 *:
        ((\1 : 'F_A) \O sigmaB)) =
      @complex.Re R (\Tr rhoAB).
  {
    rewrite Hinv_eq trnormH_scaleZ.
    rewrite (trnormH_lift_I_psd disAB Hsigma_psd) trnormH_psd//.
    rewrite (ger0_norm Hinv_ge0) /invd mulrA (mulVf Hdim_A_ne0_R) ?mul1r.
    by rewrite Hsigma_Tr Htr_ptrace_rho.
  }
  rewrite Htrn_rho Htrn_lift in Hbound.
  have Hhalf_bound :
      @GRing.inv R 2%:R *
        trnormH (rhoAB -
          (dim 'H[H]_A)%:R^-1 *: ((\1 : 'F_A) \O sigmaB)) <=
      @complex.Re R (\Tr rhoAB).
  {
    have Hinq := ler_wpM2l Htwo_inv_ge0 Hbound.
    apply: le_trans Hinq _.
    rewrite mulrDr [@GRing.inv R 2%:R * _]mulrC.
    by rewrite -splitr.
  }
  exact: Hhalf_bound.
Qed.
(* path: lhl:dist_uniform_glb -> lhl:two_universal_hashing -> *)
(*   bb84:privacy_amplification -> bb84:bb84_secret *)
Lemma dist_uniform_glb (rhoAB : 'F[H]_(A :|: B)) lb :
  rhoAB \is psdlf ->
  (forall v, dist_uniform_feasible rhoAB v -> lb <= v) ->
  lb <= dist_from_uniform rhoAB.
Proof.
  move=> Hrho Hlb; rewrite /dist_from_uniform.
  apply: lb_le_inf; last exact: Hlb.
  exists ((2%:R)^-1 * trnormH
    (rhoAB - (dim 'H[H]_A)%:R^-1 *: ((\1 : 'F_A) \O ptrace_castl disAB rhoAB))).
  exists (ptrace_castl disAB rhoAB); split.
    exact: (@ptrace_castl_psdlf R L H A B disAB rhoAB Hrho).
  split=> //.
  by rewrite /ptrace_castl /ptrace_cast_gen -castlf_trlf.
Qed.
Lemma dist_uniform_has_inf (rhoAB : 'F[H]_(A :|: B)) :
  rhoAB \is psdlf ->
  has_inf [set v : R | dist_uniform_feasible rhoAB v].
Proof.
  move=> Hrho; split.
  - exists ((2%:R)^-1 * trnormH
      (rhoAB - (dim 'H[H]_A)%:R^-1 *:
        ((\1 : 'F_A) \O ptrace_castl disAB rhoAB))).
    exists (ptrace_castl disAB rhoAB); split.
      exact: (@ptrace_castl_psdlf R L H A B disAB rhoAB Hrho).
    split=> //.
    by rewrite /ptrace_castl /ptrace_cast_gen -castlf_trlf.
  - exists 0 => v [sigma [_ [_ ->]]].
    apply: mulr_ge0; first by rewrite invr_ge0 ler0n.
    rewrite /trnormH.
    set M := h2mx _.
    by move: (trnorm_ge0 M); rewrite lecE/= => /andP[_].
Qed.
Lemma dist_uniform_adherent (rhoAB : 'F[H]_(A :|: B)) eta :
  rhoAB \is psdlf ->
  0 < eta ->
  exists2 v, dist_uniform_feasible rhoAB v &
    v < dist_from_uniform rhoAB + eta.
Proof.
  move=> Hrho Heta; exact: inf_adherent Heta (dist_uniform_has_inf Hrho).
Qed.
(* Scaling form needed when a protocol proof works with a conditional
   non-abort state but the denotational semantics gives the corresponding
   subnormalized branch. *)
Lemma dist_uniform_scale_le (rhoAB : 'F[H]_(A :|: B)) (c : R) :
  rhoAB \is psdlf -> 0 <= c ->
  c * dist_from_uniform rhoAB <= dist_from_uniform (c%:C *: rhoAB).
Proof.
  move=> Hrho Hc; case: (eqVneq c 0) => [-> | Hc0].
  - rewrite mul0r.
    apply: dist_uniform_glb.
    + by rewrite scale0r psdlfE lexx.
    + move=> v [sigma [_ [_ ->]]].
      apply: mulr_ge0; first by rewrite invr_ge0 ler0n.
      rewrite /trnormH.
      set M := h2mx _.
      by move: (trnorm_ge0 M); rewrite lecE /= => /andP[_].
  - have Hc_pos : 0 < c by rewrite lt_def Hc Hc0.
    have Hscaled_psd : c%:C *: rhoAB \is psdlf.
      by apply: psdlfZ; [rewrite lecR Hc | exact: Hrho].
    apply: (dist_uniform_glb (rhoAB := c%:C *: rhoAB) Hscaled_psd) =>
      v [sigma [Hsigma_psd [Hsigma_tr ->]]].
    pose sigma_p : 'F[H]_B := (c^-1)%:C *: sigma.
    have Hsigma_p_psd : sigma_p \is psdlf.
    {
      rewrite /sigma_p.
      by apply: psdlfZ; [rewrite lecR invr_ge0 Hc | exact: Hsigma_psd].
    }
    have Hsigma_p_tr : \Tr sigma_p = \Tr (\Tr_(A) rhoAB).
    {
      rewrite /sigma_p linearZ /= Hsigma_tr [\Tr_(A) (c%:C *: rhoAB)]linearZ /=.
      rewrite linearZ /= mulrA.
      have HcC0 : c%:C != 0 :> C by rewrite realc_eq0.
      by rewrite fmorphV // mulVf // mul1r.
    }
    have Hdist := dist_uniform_lb
      (rhoAB := rhoAB)
      (v := (2%:R)^-1 * trnormH
        (rhoAB - (dim 'H[H]_A)%:R^-1 *: ((\1 : 'F_A) \O sigma_p)))
      (ex_intro _ sigma_p (conj Hsigma_p_psd (conj Hsigma_p_tr erefl))).
    have Hmul := ler_wpM2l Hc Hdist.
    apply: le_trans Hmul _.
    rewrite mulrA [c * (2%:R)^-1]mulrC -mulrA.
    have Hsigma_scale : c%:C *: sigma_p = sigma.
    {
      rewrite /sigma_p scalerA.
      have HcC0 : c%:C != 0 :> C by rewrite realc_eq0.
      by rewrite fmorphV // mulfV // scale1r.
    }
    have Hdiff :
        c%:C *:
          (rhoAB - (dim 'H[H]_A)%:R^-1 *:
            ((\1 : 'F_A) \O sigma_p)) =
        c%:C *: rhoAB -
          (dim 'H[H]_A)%:R^-1 *: ((\1 : 'F_A) \O sigma).
    {
      rewrite scalerBr scalerA mulrC -scalerA -sdotfZr Hsigma_scale.
      by [].
    }
    by rewrite -Hdiff trnormH_scaleZ ger0_norm.
Qed.
(* Protocol-side recombination uses explicit public-branch witnesses before
   taking the infimum hidden in dist_from_uniform. *)
Lemma dist_uniform_sum_witness_le (I : finType)
    (w : I -> R)
    (rho : I -> 'F[H]_(A :|: B)) (sigma : I -> 'F[H]_B) :
  (forall i, 0 <= w i) ->
  (forall i, sigma i \is psdlf) ->
  (forall i, \Tr (sigma i) = \Tr (\Tr_(A) (rho i))) ->
  dist_from_uniform (\sum_i (w i)%:C *: rho i) <=
    \sum_i w i * ((2%:R)^-1 * trnormH
      (rho i - (dim 'H[H]_A)%:R^-1 *: ((\1 : 'F_A) \O sigma i))).
Proof.
  move=> Hw Hsigma Htr; pose rho_mix : 'F[H]_(A :|: B) := \sum_i (w i)%:C *: rho i.
  pose sigma_mix : 'F[H]_B := \sum_i (w i)%:C *: sigma i.
  have Hsigma_mix_psd : sigma_mix \is psdlf.
  {
    rewrite /sigma_mix.
    apply: psdlf_sum => i _.
    by apply: psdlfZ; [rewrite lecR Hw | exact: Hsigma].
  }
  have Hsigma_mix_tr : \Tr sigma_mix = \Tr (\Tr_(A) rho_mix).
  {
    have Hptr (x : 'F[H]_(A :|: B)) : \Tr (\Tr_(A) x) = \Tr x.
      by case/cptpP: (@ptraceso_qc R L H A (A :|: B)) => _ /tpmapP ->.
    rewrite /sigma_mix linear_sum /= (Hptr rho_mix) /rho_mix linear_sum /=.
    apply: eq_bigr => i _.
    by rewrite !linearZ /= Htr Hptr.
  }
  pose witness_value : R := (2%:R)^-1 * trnormH
    (rho_mix - (dim 'H[H]_A)%:R^-1 *:
      ((\1 : 'F_A) \O sigma_mix)).
  have Hfeasible : dist_uniform_feasible rho_mix witness_value.
  {
    exists sigma_mix; split; first exact: Hsigma_mix_psd.
    by split; [exact: Hsigma_mix_tr | rewrite /witness_value].
  }
  apply: le_trans (dist_uniform_lb Hfeasible) _.
  have Hdiff :
      rho_mix - (dim 'H[H]_A)%:R^-1 *:
        ((\1 : 'F_A) \O sigma_mix) =
      \sum_i (w i)%:C *:
        (rho i - (dim 'H[H]_A)%:R^-1 *:
          ((\1 : 'F_A) \O sigma i)).
  {
    rewrite /rho_mix /sigma_mix sdotf_sumr scaler_sumr.
    rewrite -sumrB.
    apply: eq_bigr => i _.
    rewrite scalerBr sdotfZr !scalerA.
    by rewrite mulrC.
  }
  have Hsum_trnorm :
      trnormH (\sum_i (w i)%:C *:
        (rho i - (dim 'H[H]_A)%:R^-1 *:
          ((\1 : 'F_A) \O sigma i))) <=
      \sum_i trnormH ((w i)%:C *:
        (rho i - (dim 'H[H]_A)%:R^-1 *:
          ((\1 : 'F_A) \O sigma i))).
  {
    apply: (big_ind2 (fun x y => trnormH x <= y)).
    - rewrite /trnormH h2mx0 /= trnorm0.
      exact: lexx.
    - move=> x1 r1 x2 r2 Hx Hy.
      have Htri := trnormH_triangle x1 x2.
      exact: le_trans Htri (lerD Hx Hy).
    - by move=> i _.
  }
  rewrite /witness_value Hdiff.
  have Hhalf_ge0 : 0 <= @GRing.inv R 2%:R by rewrite invr_ge0 ler0n.
  have Hscaled := ler_wpM2l Hhalf_ge0 Hsum_trnorm.
  apply: le_trans Hscaled _.
  rewrite mulr_sumr.
  apply: ler_sum => i _.
  rewrite trnormH_scaleZ ger0_norm; last exact: Hw.
  set half := @GRing.inv R 2%:R.
  by rewrite !mulrA [half * w i]mulrC.
Qed.
Fact dist_uniform_sum_le (I : finType)
    (w : I -> R) (rho : I -> 'F[H]_(A :|: B)) :
  (forall i, 0 <= w i) ->
  (forall i, rho i \is psdlf) ->
  \sum_i w i <= 1 ->
  dist_from_uniform (\sum_i (w i)%:C *: rho i) <=
    \sum_i w i * dist_from_uniform (rho i).
Proof.
  move=> Hw Hrho Hw_sum; apply/ler_addgt0Pr => eta Heta.
  have Hchoose i :
      exists sigma : 'F[H]_B,
        sigma \is psdlf /\
        \Tr sigma = \Tr (\Tr_(A) (rho i)) /\
        (2%:R)^-1 * trnormH
          (rho i - (dim 'H[H]_A)%:R^-1 *:
            ((\1 : 'F_A) \O sigma)) <
        dist_from_uniform (rho i) + eta.
  {
    have [v [sigma [Hsigma [Htr ->]]] Hv] :=
      dist_uniform_adherent (Hrho i) Heta.
    by exists sigma.
  }
  have [sigma Hsigma] := choice Hchoose.
  set branch := fun i => (2%:R)^-1 * trnormH
    (rho i - (dim 'H[H]_A)%:R^-1 *:
      ((\1 : 'F_A) \O sigma i)).
  apply: (le_trans
    (@dist_uniform_sum_witness_le I w rho sigma Hw
      (fun i => let: conj H _ := Hsigma i in H)
      (fun i => let: conj _ (conj H _) := Hsigma i in H))).
  have Hbranch :
      \sum_i w i * branch i <=
      \sum_i w i * (dist_from_uniform (rho i) + eta).
  {
    apply: ler_sum => i _.
    case: (Hsigma i) => _ [_ Hlt].
    rewrite /branch.
    apply: ler_wpM2l; first exact: Hw.
    exact: ltW Hlt.
  }
  apply: le_trans Hbranch _.
  have Hexpand :
      \sum_i w i * (dist_from_uniform (rho i) + eta) =
      \sum_i (w i * dist_from_uniform (rho i) + w i * eta).
  {
    apply: eq_bigr => i _.
    by rewrite mulrDr.
  }
  rewrite Hexpand big_split /=.
  apply: lerD; first exact: lexx.
  have Heta_comm : \sum_i w i * eta = eta * \sum_i w i.
  {
    rewrite [eta * _]mulr_sumr.
    apply: eq_bigr => i _.
    by rewrite mulrC.
  }
  rewrite Heta_comm.
  apply: le_trans (ler_wpM2l (ltW Heta) Hw_sum) _.
  by rewrite mulr1.
Qed.
(* Tomamichel-Schaffner-Smith-Renner, 'Leftover Hashing Against Quantum      *)
(* Side Information' (IEEE Trans. IT 57:5524 (2011); arXiv:1002.2436); proof  *)
(* step (smoothing) of thm:two-universal-hashing (Thm. 6), adapted from       *)
(* ρ̃ = τ to arbitrary τ via σ_rho := c·σ_tau scaling.                        *)
(* math: d_u(ρ) ≤ P(ρ,τ) + d_u(τ) (triangle inequality via purified          *)
(* distance, for sub-normalized states).                                      *)
(* Standalone justification: textbook metric-triangle inequality for the      *)
(* sub-normalized distance d_u, derived from the generalized trace distance   *)
(* D̄ = ½‖ρ-τ‖₁ + ½|ΔTr|. Main branch: srho := c·stau with c := Re(Tr ρ) /    *)
(* Re(Tr τ); trnormH_triangle twice; (1-c) lift term bounded via             *)
(* trnormH_scaleZ + trnormH_lift_I_psd + trnormH_psd; closes with       *)
(* pd_gtd_bar_lb.  Zero-tau branch: srho := Tr_A(ρ), τ=0 witness.              *)
(* Consumers: thm:two-universal-hashing (Thm. 6) smoothing step.             *)
(* path: lhl:dist_uniform_pd_triangle -> lhl:two_universal_hashing -> *)
(*   bb84:privacy_amplification -> bb84:bb84_secret *)
Lemma dist_uniform_pd_triangle (rhoAB tauAB : 'F[H]_(A :|: B)) :
  rhoAB \is psdlf -> tauAB \is psdlf ->
  @complex.Re R (\Tr rhoAB) <= 1 ->
  @complex.Re R (\Tr tauAB) <= 1 ->
  dist_from_uniform rhoAB <=
    pur_dist rhoAB tauAB + dist_from_uniform tauAB.
Proof.
  move=> Hrho Htau Hrho_tr Htau_tr; have Hrho_Re_ge0 : 0 <= @complex.Re R (\Tr rhoAB).
    by move: (psdlf_trlf Hrho); rewrite lecE/= => /andP[_].
  have Htau_Re_ge0 : 0 <= @complex.Re R (\Tr tauAB).
    by move: (psdlf_trlf Htau); rewrite lecE/= => /andP[_].
  have Hrho_Tr_real : \Tr rhoAB \is Num.real := ger0_real (psdlf_trlf Hrho).
  have Htau_Tr_real : \Tr tauAB \is Num.real := ger0_real (psdlf_trlf Htau).
  have Hdim_A_pos : (0 < dim 'H[H]_A)%N := dim_proper.
  have Hdim_A_ne0_R : ((dim 'H[H]_A)%:R : R) != 0 by rewrite pnatr_eq0 -lt0n.
  have Hdim_A_ne0_C : ((dim 'H[H]_A)%:R : C) != 0 by rewrite pnatr_eq0 -lt0n.
  have Htr_ptrace_tau : \Tr (\Tr_(A) tauAB) = \Tr tauAB.
    by case/cptpP: (@ptraceso_qc R L H A (A :|: B)) => _ /tpmapP ->.
  have Htr_ptrace_rho : \Tr (\Tr_(A) rhoAB) = \Tr rhoAB.
    by case/cptpP: (@ptraceso_qc R L H A (A :|: B)) => _ /tpmapP ->.
  rewrite -lerBlDl.
  apply: (dist_uniform_glb Htau) => // v_τ [stau [Hstau_psd [Hstau_tr ->]]].
  have Hstau_Tr : \Tr stau = \Tr tauAB by rewrite Hstau_tr Htr_ptrace_tau.
  have Hstau_Re_Tr : @complex.Re R (\Tr stau) = @complex.Re R (\Tr tauAB).
    by rewrite Hstau_Tr.
  rewrite lerBlDl.
  have Hsplit_eq : forall (srho : 'F[H]_B),
    rhoAB - (dim 'H[H]_A)%:R^-1 *: ((\1 : 'F_A) \O srho) =
    (rhoAB - tauAB) +
    (tauAB - (dim 'H[H]_A)%:R^-1 *: ((\1 : 'F_A) \O stau)) +
    ((dim 'H[H]_A)%:R^-1 *: ((\1 : 'F_A) \O stau) -
     (dim 'H[H]_A)%:R^-1 *: ((\1 : 'F_A) \O srho)).
    move=> srho.
    by rewrite !addrA [_ - tauAB + tauAB]addrNK
               [_ - _ *: (_ \O stau) + _ *: (_ \O stau)]addrNK.
  case: (ltrgt0P (@complex.Re R (\Tr tauAB))) => [Htau_pos|Htau_neg|Htau_zero].
  - set cR := @complex.Re R (\Tr rhoAB) / @complex.Re R (\Tr tauAB).
    have HcR_ge0 : 0 <= cR := divr_ge0 Hrho_Re_ge0 (ltW Htau_pos).
    have HcR_R_ne0 : @complex.Re R (\Tr tauAB) != 0 by rewrite gt_eqF.
    set srho := cR%:C *: stau.
    have Hsrh_psd : srho \is psdlf.
      by apply: psdlfZ => //; rewrite lecE/= eqxx/=.
    have Hsrh_Tr : \Tr srho = \Tr (\Tr_(A) rhoAB).
      rewrite /srho linearZ/= Hstau_Tr Htr_ptrace_rho.
      rewrite -[\Tr rhoAB]RRe_real// -[\Tr tauAB]RRe_real//.
      by rewrite -realcM /cR -mulrA mulVf// mulr1.
    have Hwb : 2%:R * dist_from_uniform rhoAB <=
      trnormH (rhoAB - (dim 'H[H]_A)%:R^-1 *: ((\1 : 'F_A) \O srho)).
      by apply: dist_uniform_witness_bound.
    pose invd : R := @GRing.inv R ((dim 'H[H]_A)%:R).
    have Hinv_eq : @GRing.inv C ((dim 'H[H]_A)%:R) = invd%:C.
      by rewrite /invd -natrC -fmorphV.
    have Hinv_ge0 : 0 <= invd by rewrite /invd invr_ge0 ler0n.
    have Hthird :
      trnormH ((dim 'H[H]_A)%:R^-1 *: ((\1 : 'F_A) \O stau) -
                 (dim 'H[H]_A)%:R^-1 *: ((\1 : 'F_A) \O srho)) =
      `|@complex.Re R (\Tr tauAB) - @complex.Re R (\Tr rhoAB)|.
      rewrite -scalerBr -sdotfBr.
      have Hdiff : stau - srho = (1 - cR%:C) *: stau.
        by rewrite /srho scalerBl scale1r.
      rewrite Hdiff sdotfZr.
      rewrite scalerA mulrC -scalerA.
      have Hone_sub : (1 - cR%:C : C) = (1 - cR)%:C by rewrite raddfB.
      rewrite Hone_sub trnormH_scaleZ.
      rewrite Hinv_eq trnormH_scaleZ.
      rewrite (ger0_norm Hinv_ge0) (trnormH_lift_I_psd disAB Hstau_psd).
      rewrite trnormH_psd//.
      rewrite Hstau_Re_Tr.
      rewrite /invd mulrA mulrA divfK//.
      have Halg : (1 - cR) * @complex.Re R (\Tr tauAB) =
                  @complex.Re R (\Tr tauAB) - @complex.Re R (\Tr rhoAB).
        rewrite mulrBl mul1r /cR.
        by rewrite (divfK HcR_R_ne0).
      rewrite -Halg normrM.
      by rewrite (ger0_norm (ltW Htau_pos)).
    have Htri :
      trnormH (rhoAB - (dim 'H[H]_A)%:R^-1 *: ((\1 : 'F_A) \O srho)) <=
      trnormH (rhoAB - tauAB) +
      trnormH (tauAB - (dim 'H[H]_A)%:R^-1 *: ((\1 : 'F_A) \O stau)) +
      trnormH ((dim 'H[H]_A)%:R^-1 *: ((\1 : 'F_A) \O stau) -
                 (dim 'H[H]_A)%:R^-1 *: ((\1 : 'F_A) \O srho)).
      rewrite Hsplit_eq.
      apply: le_trans (trnormH_triangle _ _) _.
      apply: lerD; last exact: lexx.
      exact: trnormH_triangle.
    rewrite Hthird in Htri.
    have Htwo_gt0 : (0 : R) < 2%:R by rewrite ltr0n.
    have Htwo_inv_ge0 : (0 : R) <= @GRing.inv R 2%:R by rewrite invr_ge0 ler0n.
    have Hd_u : dist_from_uniform rhoAB <=
                  (2%:R)^-1 * trnormH
                    (rhoAB - (dim 'H[H]_A)%:R^-1 *: ((\1 : 'F_A) \O srho)).
      have /(ler_wpM2l Htwo_inv_ge0) := Hwb.
      rewrite mulrA mulVf ?pnatr_eq0// mul1r.
      by [].
    apply: le_trans Hd_u _.
    have Htri' := ler_wpM2l Htwo_inv_ge0 Htri.
    apply: le_trans Htri' _.
    rewrite !mulrDr.
    rewrite -!addrA [X in _ + X]addrC !addrA.
    have Hpd := pd_gtd_bar_lb Hrho Htau Hrho_tr Htau_tr.
    apply: lerD; last exact: lexx.
    apply: le_trans _ Hpd.
    rewrite [@GRing.inv R 2%:R * _]mulrC [@GRing.inv R 2%:R * _]mulrC.
    by rewrite distrC.
  - by move: Htau_Re_ge0; rewrite leNgt Htau_neg.
  - have Htau_Tr_zero : \Tr tauAB = 0.
      rewrite -(RRe_real Htau_Tr_real).
      by rewrite Htau_zero.
    have Htau_eq0 : tauAB = 0.
      apply/eqP/trlf0_eq0.
      split; last exact: Htau_Tr_zero.
      by move: Htau; rewrite psdlfE.
    have Hstau_Tr_zero : \Tr stau = 0 by rewrite Hstau_Tr.
    have Hstau_eq0 : stau = 0.
      apply/eqP/trlf0_eq0.
      split; last exact: Hstau_Tr_zero.
      by move: Hstau_psd; rewrite psdlfE.
    rewrite Htau_eq0 Hstau_eq0 sdotf0 scaler0 subrr.
    rewrite /trnormH h2mx0/= trnorm0 linear0 mulr0 addr0.
    pose srho : 'F[H]_B := ptrace_castl disAB rhoAB.
    have Hsrh_psd : srho \is psdlf := ptrace_castl_psdlf disAB Hrho.
    have Hsrh_Tr : \Tr srho = \Tr (\Tr_(A) rhoAB).
      by rewrite /srho /ptrace_castl /ptrace_cast_gen -castlf_trlf.
    have Hwb : 2%:R * dist_from_uniform rhoAB <=
      trnormH (rhoAB - (dim 'H[H]_A)%:R^-1 *: ((\1 : 'F_A) \O srho)).
      by apply: dist_uniform_witness_bound.
    have Htwo_inv_ge0 : (0 : R) <= @GRing.inv R 2%:R by rewrite invr_ge0 ler0n.
    have Hd_u : dist_from_uniform rhoAB <=
                  @GRing.inv R 2%:R * trnormH
                    (rhoAB - (dim 'H[H]_A)%:R^-1 *: ((\1 : 'F_A) \O srho)).
      have /(ler_wpM2l Htwo_inv_ge0) := Hwb.
      rewrite mulrA mulVf ?pnatr_eq0// mul1r.
      by [].
    apply: le_trans Hd_u _.
    have Hbound : trnormH (rhoAB - (dim 'H[H]_A)%:R^-1 *: ((\1 : 'F_A) \O srho))
                  <= trnormH rhoAB +
                     trnormH ((dim 'H[H]_A)%:R^-1 *: ((\1 : 'F_A) \O srho)).
      exact: trnormH_triangleB.
    have Htrn_rho : trnormH rhoAB = @complex.Re R (\Tr rhoAB) := trnormH_psd Hrho.
    pose invd : R := @GRing.inv R ((dim 'H[H]_A)%:R).
    have Hinv_eq : @GRing.inv C ((dim 'H[H]_A)%:R) = invd%:C.
      by rewrite /invd -natrC -fmorphV.
    have Hinv_ge0 : 0 <= invd by rewrite /invd invr_ge0 ler0n.
    have Htrn_lift : trnormH ((dim 'H[H]_A)%:R^-1 *: ((\1 : 'F_A) \O srho))
                     = @complex.Re R (\Tr rhoAB).
      rewrite Hinv_eq trnormH_scaleZ.
      rewrite (trnormH_lift_I_psd disAB Hsrh_psd) trnormH_psd//.
      rewrite (ger0_norm Hinv_ge0) /invd mulrA mulVf// mul1r.
      rewrite Hsrh_Tr Htr_ptrace_rho.
      by [].
    rewrite Htrn_rho Htrn_lift in Hbound.
    have Hhalf_bound : @GRing.inv R 2%:R *
                       trnormH (rhoAB - (dim 'H[H]_A)%:R^-1 *: ((\1 : 'F_A) \O srho))
                       <= @complex.Re R (\Tr rhoAB).
      have Hinq := ler_wpM2l Htwo_inv_ge0 Hbound.
      apply: le_trans Hinq _.
      rewrite mulrDr [@GRing.inv R 2%:R * _]mulrC.
      rewrite -splitr.
      exact: lexx.
    apply: le_trans Hhalf_bound _.
    have Hzero_psd : (0 : 'F[H]_(A :|: B)) \is psdlf by rewrite psdlfE lexx.
    have Hzero_tr : @complex.Re R (\Tr (0 : 'F[H]_(A :|: B))) <= 1.
      by rewrite linear0/= ler01.
    have Hpd := pd_gtd_bar_lb Hrho Hzero_psd Hrho_tr Hzero_tr.
    apply: le_trans _ Hpd.
    rewrite subr0 linear0 subr0 trnormH_psd// (ger0_norm Hrho_Re_ge0).
    by rewrite -splitr lexx.
Qed.
End DistFromUniform.
(* Monotonicity of the collision-probability bound.                     *)
(* Tomamichel-Schaffner-Smith-Renner, 'Leftover Hashing Against Quantum *)
(* Side Information' (IEEE Trans. IT 57:5524 (2011); arXiv:1002.2436);   *)
(* explicit-constructions section (Lem. 8 / Thm. 9-10), used by the      *)
(* explicit construction bounds.                                        *)
(* path: lhl:delta_almost_two_univ_mono -> lhl:two_universal_hashing -> *)
(*   bb84:privacy_amplification -> bb84:bb84_secret *)
Fact delta_almost_two_univ_mono
    {Fidx X Z : finType} (F : Fidx -> X -> Z) (d1 d2 : R) :
  d1 <= d2 ->
  delta_almost_two_univ F d1 ->
  delta_almost_two_univ F d2.
Proof. by move=> Hd HF x x' Hxx; exact: le_trans (HF x x' Hxx) Hd. Qed.
(* Collision probability is the probability of the collision event under
   the uniform seed distribution.                                      *)
(* Tomamichel-Schaffner-Smith-Renner, 'Leftover Hashing Against Quantum *)
(* Side Information' (IEEE Trans. IT 57:5524 (2011); arXiv:1002.2436),   *)
(* Eq. 7 — tex eqn:almost-two-universal.                                 *)
(* path: lhl:collision_probability_uniform -> lhl:two_universal_hashing -> *)
(*   bb84:privacy_amplification -> bb84:bb84_secret *)
Lemma collision_probability_uniform
    {Fidx X Z : finType} (F : Fidx -> X -> Z) (x x' : X) :
  collision_probability F x x' =
  Pr_event (@uniform_fin_mu R Fidx) [set f : Fidx | F f x == F f x'].
Proof. by rewrite /collision_probability (@Pr_event_uniform_fin R Fidx) mulrC. Qed.
(* Stinson concatenation for finite hash families.                       *)
(* Tomamichel-Schaffner-Smith-Renner, 'Leftover Hashing Against Quantum  *)
(* Side Information' (IEEE Trans. IT 57:5524 (2011); arXiv:1002.2436),    *)
(* Lem. 8 — tex lemma:concatenation.                                      *)
(* path: lhl:hash_comp_delta_almost_two_univ -> lhl:two_universal_hashing -> *)
(*   bb84:privacy_amplification -> bb84:bb84_secret *)
Lemma hash_comp_delta_almost_two_univ
    {F1idx F2idx X Y Z : finType}
    (F1 : F1idx -> X -> Y) (F2 : F2idx -> Y -> Z)
    (delta1 delta2 : R) :
  (0 < #|{: F1idx}|)%N ->
  (0 < #|{: F2idx}|)%N ->
  0 <= delta1 ->
  0 <= delta2 ->
  delta_almost_two_univ F1 delta1 ->
  delta_almost_two_univ F2 delta2 ->
  delta_almost_two_univ (hash_comp F1 F2) (delta1 + delta2).
Proof.
  move=> Hcard1 Hcard2 Hdelta1 Hdelta2 HF1 HF2 x x' Hxx; pose mu1 := @uniform_fin_mu R F1idx.
  pose mu2 := @uniform_fin_mu R F2idx.
  pose prod_mu (fg : (F1idx * F2idx)%type) := mu1 fg.1 * mu2 fg.2.
  pose Coll : {set (F1idx * F2idx)%type} :=
    [set fg | hash_comp F1 F2 fg x == hash_comp F1 F2 fg x'].
  pose Bad : {set (F1idx * F2idx)%type} :=
    [set fg | F1 fg.1 x == F1 fg.1 x'].
  pose GoodE (f1 : F1idx) : {set F2idx} :=
    if F1 f1 x != F1 f1 x' then
      [set f2 | F2 f2 (F1 f1 x) == F2 f2 (F1 f1 x')]
    else [set f2 : F2idx | false].
  pose Good : {set (F1idx * F2idx)%type} :=
    [set fg | fg.2 \in GoodE fg.1].
  rewrite /collision_probability.
  rewrite -[X in X <= _](@Pr_event_uniform_fin R (F1idx * F2idx)%type Coll).
  have Hpair_mu : forall fg : (F1idx * F2idx)%type,
    @uniform_fin_mu R (F1idx * F2idx)%type fg = prod_mu fg.
  {
    move=> fg; rewrite /prod_mu /mu1 /mu2 /uniform_fin_mu card_prod natrM.
    by rewrite invfM //.
  }
  have Hcoll_mu :
    Pr_event (@uniform_fin_mu R (F1idx * F2idx)%type) Coll =
    Pr_event prod_mu Coll.
  { by apply: eq_bigr => fg _; rewrite Hpair_mu. }
  rewrite Hcoll_mu.
  have Hsplit : Pr_event prod_mu Coll <=
      Pr_event prod_mu Bad + Pr_event prod_mu Good.
  {
    rewrite /Pr_event /Coll /Bad /Good /GoodE /hash_comp.
    rewrite (bigID (fun fg : (F1idx * F2idx)%type =>
      F1 fg.1 x == F1 fg.1 x')) /=.
    apply: lerD.
    - rewrite [leLHS](eq_bigl (fun fg : (F1idx * F2idx)%type =>
        F1 fg.1 x == F1 fg.1 x')); last first.
      {
        move=> fg; rewrite !inE.
        case Hb : (F1 fg.1 x == F1 fg.1 x'); last by rewrite !andbF.
        by move/eqP: Hb => ->; rewrite eqxx.
      }
      rewrite [leRHS](eq_bigl (fun fg : (F1idx * F2idx)%type =>
        F1 fg.1 x == F1 fg.1 x')); last by move=> fg; rewrite inE.
      exact: lexx.
    - rewrite [leLHS](eq_bigl (fun fg : (F1idx * F2idx)%type =>
        fg.2 \in (if F1 fg.1 x != F1 fg.1 x' then
          [set f2 | F2 f2 (F1 fg.1 x) == F2 f2 (F1 fg.1 x')]
        else [set f2 : F2idx | false]))); last first.
      {
      move=> fg; rewrite !inE.
      by case: (F1 fg.1 x == F1 fg.1 x'); rewrite ?andbF ?andbT ?inE.
      }
      rewrite [leRHS](eq_bigl (fun fg : (F1idx * F2idx)%type =>
        fg.2 \in (if F1 fg.1 x != F1 fg.1 x' then
          [set f2 | F2 f2 (F1 fg.1 x) == F2 f2 (F1 fg.1 x')]
        else [set f2 : F2idx | false]))); first exact: lexx.
      by move=> fg; rewrite inE.
  }
  apply: (le_trans Hsplit).
  apply: lerD.
  - pose Bad1 : {set F1idx} := [set f1 | F1 f1 x == F1 f1 x'].
    have HbadE :
      Pr_event prod_mu Bad = Pr_event mu1 Bad1.
    {
      rewrite /prod_mu (_ : Bad = [set ab : (F1idx * F2idx)%type | ab.1 \in Bad1]).
      - exact: product_prob_fst_event (@uniform_fin_mu_sum1 R F2idx Hcard2).
      apply/setP => ab.
      by rewrite /Bad /Bad1 !inE.
    }
    rewrite HbadE -collision_probability_uniform.
    exact: HF1.
  - have Hgood_le :
      Pr_event prod_mu Good <= delta2.
    {
      rewrite /Pr_event /Good /prod_mu.
      rewrite (eq_bigl (fun ab : (F1idx * F2idx)%type =>
        ab.2 \in GoodE ab.1)); last by move=> ab; rewrite inE.
      apply: (@product_prob_fiber_le R F1idx F2idx mu1 mu2 GoodE delta2).
      - exact: (@uniform_fin_mu_nonneg R F1idx).
      - exact: (@uniform_fin_mu_nonneg R F2idx).
      - exact: (@uniform_fin_mu_sum1 R F1idx Hcard1).
      - move=> f1.
        rewrite /GoodE.
        case Hneq1 : (F1 f1 x != F1 f1 x').
        + rewrite -collision_probability_uniform.
          exact: HF2.
        + rewrite /Pr_event.
          rewrite big_pred0; first exact: Hdelta2.
          by move=> f2; rewrite inE.
    }
    exact: Hgood_le.
Qed.
(* ================================================================== *)
(* Bound d_u via collision entropy                                     *)
(* Tomamichel-Schaffner-Smith-Renner, 'Leftover Hashing Against Quantum *)
(* Side Information' (IEEE Trans. IT 57:5524 (2011); arXiv:1002.2436),   *)
(* Lem. 4 — tex lemma:uniform-to-collision — math: for supp τ_B ⊇ supp   *)
(* ρ_B, d_u(A|B)_ρ ≤ ½√(d_A·Γ_C(ρ_AB|τ_B) − Tr(ρ_B τ_B^{-½} ρ_B τ_B^{-½})). *)
(* ================================================================== *)
Section UnifToColl.
Variable (L : finType) (HL : L -> chsType) (A B : {set L}).
Hypothesis disAB : [disjoint A & B].
Notation S_AB := (A :|: B).
(* Fixed-marginal core behind lemma:uniform-to-collision.                  *)
(* math: ½‖ρ_AB − ω_A⊗ρ_B‖₁ ≤ ½√(d_A · Γ_C(ρ_AB | τ_B) − Tr(ρ_B τ_B^{-½} ρ_B τ_B^{-½})) *)
(* tex hypothesis of lemma:uniform-to-collision (Lem. 4): supp τ_B ⊇       *)
(* supp ρ_B. Without this the                                              *)
(* Hölder factorization (I_A ⊗ τ^{1/4})·(I_A ⊗ τ^{-1/4}) = I_A ⊗ Π_τ       *)
(* does not act as identity on ρ_AB, and the stated inequality is false    *)
(* (e.g. τ_B = 0 with ρ_B ≠ 0 forces a negative RHS under pinv).           *)
(* path: lhl:uniform_collision_bound -> *)
(*   bb84:privacy_amplification -> bb84:bb84_secret *)
Lemma uniform_collision_bound (rhoAB : 'F[HL]_S_AB) (tauB : 'F[HL]_B) :
  rhoAB \is psdlf -> tauB \is psdlf ->
  @complex.Re R (\Tr tauB) <= 1 ->
  (supph (ptrace_castl disAB rhoAB) `<=` supph tauB)%HS ->
  let rhoB := ptrace_castl disAB rhoAB in
  let tau_inv_half := pinvlf (sqrtH tauB) in
  (2%:R)^-1 * trnormH
    (rhoAB - (dim 'H[HL]_A)%:R^-1 *: ((\1 : 'F_A) \O rhoB)) <=
  (2%:R)^-1 * Num.sqrt (
    (dim 'H[HL]_A)%:R * collision_ent rhoAB tauB
    - @complex.Re R (\Tr (rhoB \o tau_inv_half \o rhoB \o tau_inv_half))).
Proof.
  move=> Prho Ptau Htr Hsupp /=.
  pose wdiff := rhoAB - (dim 'H[HL]_A)%:R^-1 *:
                  ((\1 : 'F_A) \O ptrace_castl disAB rhoAB).
  pose Minv := (\1 : 'F_A) \O pinvlf (sqrtH tauB).
  pose Sval := @complex.Re R (\Tr (wdiff \o Minv \o wdiff \o Minv)).
  (* proof step of lemma:uniform-to-collision (Lem. 4) applying          *)
  (* lemma:hoelder (Lem. 18): Hölder (r,s,t)=(4,2,4) with factoring   *)
  (* A = C = I_A ⊗ τ^{1/4}, B = (I_A ⊗ τ^{-1/4})·wdiff·(I_A ⊗ τ^{-1/4}).    *)
  (* Uses Hsupp (I⊗τ^{1/4})·(I⊗τ^{-1/4}) acts as id on wdiff, and Htr       *)
  (* (Tr τ ≤ 1 absorbs the √(d_A · Tr τ · …) factor into √(d_A · …)).       *)
  have Hhoelder : (trnormH wdiff <=
      Num.sqrt ((dim 'H[HL]_A)%:R * Sval))%R.
    (* Quarter-root factorization *)
    pose T14 := sqrtH (sqrtH tauB).
    pose T14i := pinvlf T14.
    pose AA : 'F[HL]_S_AB := (\1 : 'F_A) \O T14.
    pose AAi : 'F[HL]_S_AB := (\1 : 'F_A) \O T14i.
    pose Bmid : 'F[HL]_S_AB := AAi \o wdiff \o AAi.
    (* (1) supph rhoAB ≤ supph(\1 \O tauB) via ptrace lift + Hsupp *)
    have HsrhoAB : (supph rhoAB `<=` supph ((\1 : 'F_A) \O tauB))%HS.
      apply: (@Order.le_trans _ _
        (supph ((\1 : 'F_A) \O ptrace_castl disAB rhoAB))).
        exact: (ptrace_supph_lift disAB Prho).
      exact: (@supph_lift_mono R L HL A B _ _ Hsupp).
    (* (2) supph(\1 \O ρ_B) ≤ supph(\1 \O tauB) via lift monotonicity *)
    have HsWlift : (supph ((\1 : 'F_A) \O ptrace_castl disAB rhoAB
                    : 'F[HL]_S_AB)
                    `<=` supph ((\1 : 'F_A) \O tauB))%HS.
      exact: (@supph_lift_mono R L HL A B _ _ Hsupp).
    (* Herm hypotheses required by lift_supph_sandwich_quarter. *)
    have rhoAB_herm : rhoAB \is hermlf by exact: psdlf_herm.
    have PrhoB : ptrace_castl disAB rhoAB \is psdlf
      by apply: (@ptrace_castl_psdlf R L HL _ _ disAB _ Prho).
    have rhoB_herm : ptrace_castl disAB rhoAB \is hermlf := psdlf_herm PrhoB.
    have Wlift_herm : (\1 : 'F_A) \O ptrace_castl disAB rhoAB \is hermlf.
      by apply/hermlfP; rewrite sdot_I_adj; move/hermlfP: rhoB_herm=>->.
    have wdiff_herm : wdiff \is hermlf.
      apply/hermlfP; rewrite /wdiff adjfB adjfZ.
      move/hermlfP: rhoAB_herm=>->; move/hermlfP: Wlift_herm=>->.
      by rewrite conj_Creal // realV realn.
    (* (3) sandwich identities from lift_supph_sandwich_quarter *)
    have Erho : AA \o AAi \o rhoAB \o AAi \o AA = rhoAB.
      exact: (lift_supph_sandwich_quarter disAB Ptau HsrhoAB rhoAB_herm).
    have Ewlift : AA \o AAi \o ((\1 : 'F_A) \O ptrace_castl disAB rhoAB)
                  \o AAi \o AA =
                  (\1 : 'F_A) \O ptrace_castl disAB rhoAB.
      exact: (lift_supph_sandwich_quarter disAB Ptau HsWlift Wlift_herm).
    (* (4) Derive supph wdiff ≤ supph(\1 \O tauB), then factor via sandwich *)
    pose Wlift : 'F[HL]_S_AB := (\1 : 'F_A) \O ptrace_castl disAB rhoAB.
    have HsuppWdiff : (supph wdiff `<=` supph ((\1 : 'F_A) \O tauB))%HS.
      rewrite /wdiff.
      apply: (le_trans (supphD_le _ _)).
      rewrite cuphP; apply/andP; split; first exact: HsrhoAB.
      rewrite -scaleNr supphZ.
        exact: HsWlift.
      by rewrite oppr_eq0 invr_eq0 pnatr_eq0 -lt0n dim_proper.
    have HsandwichW : AA \o AAi \o wdiff \o AAi \o AA = wdiff.
      exact: (lift_supph_sandwich_quarter disAB Ptau HsuppWdiff wdiff_herm).
    have Ewdiff : wdiff = AA \o Bmid \o AA.
      rewrite -{1}HsandwichW /Bmid.
      by rewrite !comp_lfunA.
    (* (5) Apply matrix Hölder with (r,s,t) = (4,2,4) *)
    have Hq4 : ((2%:R : R)^-1 / 2%:R = (4%:R : R)^-1)%R.
      by rewrite -invrM ?unitfE ?pnatr_eq0 // -natrM.
    have Hq : ((4%:R : R)^-1 + (4%:R : R)^-1 = (2%:R : R)^-1)%R.
      by rewrite -Hq4 -splitr.
    have Hhalf : ((2%:R : R)^-1 + (2%:R : R)^-1 = 1)%R.
      have Hs := @splitr R (1 : R).
      rewrite !mul1r in Hs.
      by symmetry; exact: Hs.
    have Hsum : ((4%:R : R)^-1 + (2%:R : R)^-1 + (4%:R : R)^-1 = 1)%R.
      by rewrite -addrA [(4%:R : R)^-1 + _]addrC -addrA Hq Hhalf.
    have Hhol : trnormH (AA \o Bmid \o AA) <=
      @complex.Re R (schnorm 4%:R (h2mx AA) * schnorm 2%:R (h2mx Bmid)
        * schnorm 4%:R (h2mx AA)).
    {
      rewrite /trnormH h2mx_comp h2mx_comp.
      set X := h2mx AA *m h2mx Bmid *m h2mx AA.
      set P := schnorm 4%:R (h2mx AA) * schnorm 2%:R (h2mx Bmid)
        * schnorm 4%:R (h2mx AA).
      have H0 : (0 : C) <= trnorm X by apply: trnorm_ge0.
      have HP0 : (0 : C) <= P.
        by rewrite /P; apply: mulr_ge0; [apply: mulr_ge0|]; apply: schnorm_ge0.
      have Hh : trnorm X <= P.
      {
        rewrite /X /P.
        apply: hoelder; [by [] | by [] | by [] | exact: Hsum].
      }
      move: Hh; rewrite -(RRe_real (ger0_real H0)) -(RRe_real (ger0_real HP0)).
      by rewrite lecR.
    }
    rewrite Ewdiff.
    apply: (le_trans Hhol).
    (* (6) Bound schnorm product ≤ √(d_A · Sval).                          *)
    (* Abbreviations *)
    set s4 := schnorm 4%:R (h2mx AA).
    set s2 := schnorm 2%:R (h2mx Bmid).
    have Hs4_ge0 : (0 : C) <= s4 by apply: schnorm_ge0.
    have Hs2_ge0 : (0 : C) <= s2 by apply: schnorm_ge0.
    (* (6a) s4 * s2 * s4 is nonneg, so Re passes through multiplication *)
    have HRe_prod : @complex.Re R (s4 * s2 * s4) =
                    @complex.Re R s4 * @complex.Re R s2 * @complex.Re R s4.
      by rewrite -(RRe_real (ger0_real Hs4_ge0))
                 -(RRe_real (ger0_real Hs2_ge0))
                 -!realcM !re_realid.
    rewrite HRe_prod.
    set Rs4 := @complex.Re R s4.
    set Rs2 := @complex.Re R s2.
    have HRs4_ge0 : (0 <= Rs4)%R by move: Hs4_ge0; rewrite lecE /= => /andP[].
    have HRs2_ge0 : (0 <= Rs2)%R by move: Hs2_ge0; rewrite lecE /= => /andP[].
    (* (6b) Rs4^4 ≤ d_A via H4 and Htr *)
    have Hs4_pow4 : s4 ^+ 4 = (dim 'H[HL]_A)%:R%:C * \Tr tauB.
      exact: (schnorm4_lift_quarter_pow4 disAB Ptau).
    have Tr_tauB_real : \Tr tauB \is Num.real.
      apply: ger0_real.
      by move: (psdlf_trlf Ptau).
    have Hs4_real : s4 \is Num.real by exact: ger0_real.
    have HRs4_pow4_eq : Rs4 ^+ 4 = (dim 'H[HL]_A)%:R * @complex.Re R (\Tr tauB).
      have E : Rs4 ^+ 4 = @complex.Re R (s4 ^+ 4).
        by rewrite /Rs4 -(RRe_real Hs4_real) -rmorphXn re_realid.
      rewrite E Hs4_pow4.
      by case: (\Tr tauB) => [a b]; rewrite /= mul0r subr0.
    have HRs4_pow4 : (Rs4 ^+ 4 <= (dim 'H[HL]_A)%:R)%R.
      rewrite HRs4_pow4_eq.
      rewrite -[X in (_ <= X)%R](mulr1 (dim 'H[HL]_A)%:R).
      apply: ler_wpM2l; first by rewrite ler0n.
      exact: Htr.
    (* (6c) Rs2^2 = Sval via HS-norm + Bmid hermlf + cyclicity + H5. *)
    have T14_psd : T14 \is psdlf by apply/sqrtH_psd/sqrtH_psd.
    have T14_herm : T14 \is hermlf by exact: psdlf_herm.
    have T14i_psd : T14i \is psdlf by rewrite /T14i; apply: pinvlf_psdlf.
    have T14i_herm : T14i \is hermlf by exact: psdlf_herm.
    have AAi_herm : AAi \is hermlf.
      by apply/hermlfP; rewrite sdot_I_adj; move/hermlfP: T14i_herm=>->.
    have Bmid_herm : Bmid \is hermlf.
      apply/hermlfP; rewrite /Bmid -comp_lfunA.
      rewrite !adjf_comp.
      by move/hermlfP: AAi_herm=>->; move/hermlfP: wdiff_herm=>->;
         rewrite comp_lfunA.
    (* HS-norm squared = Tr(Bmid^A \o Bmid) = Tr(Bmid \o Bmid) via Bmid_herm *)
    have Hs2_sq_tr : s2 ^+ 2 = \Tr (Bmid \o Bmid).
      rewrite /s2 -[schnorm _ _]/(fbnorm _) fbnorm_dotV sqrtCK /lftrace h2mx_comp -h2mx_adj.
      by move/hermlfP: Bmid_herm=>->.
    (* Reduce Tr(Bmid \o Bmid) to Tr(wdiff \o Minv \o wdiff \o Minv) via
       cyclicity + sdotI_comp + H5. *)
    have AAi_sq : AAi \o AAi = Minv.
      rewrite /AAi /Minv sdotI_comp.
      congr ((\1 : 'F_A) \O _).
      exact: (pinvlf_sqrtH_pow2 (sqrtH_psd Ptau)).
    have Hbmid_sq_tr : \Tr (Bmid \o Bmid) = \Tr (wdiff \o Minv \o wdiff \o Minv).
      rewrite /Bmid.
      have Hcollapse :
        \Tr ((AAi \o wdiff \o AAi) \o (AAi \o wdiff \o AAi)) =
        \Tr ((AAi \o AAi) \o wdiff \o (AAi \o AAi) \o wdiff).
      {
        have E :
          (AAi \o wdiff \o AAi) \o (AAi \o wdiff \o AAi) =
          AAi \o wdiff \o AAi \o AAi \o wdiff \o AAi.
          by rewrite !comp_lfunA.
        rewrite E /lftrace !h2mx_comp.
        exact: mxtrace_abaaba_collapse.
      }
      rewrite Hcollapse.
      (* Collapse both adjacent `AAi` factors before cyclically rotating the trace. *)
      rewrite AAi_sq.
      (* Goal: \Tr (Minv \o wdiff \o Minv \o wdiff) = \Tr (wdiff \o Minv \o wdiff \o Minv) *)
      rewrite lftraceC.
      by rewrite !comp_lfunA.
    have HRs2_sq : (Rs2 ^+ 2 = Sval)%R.
      have HReXn : (@complex.Re R s2) ^+ 2 = @complex.Re R (s2 ^+ 2).
        by rewrite -(RRe_real (ger0_real Hs2_ge0)) -rmorphXn re_realid.
      by rewrite /Rs2 /Sval HReXn Hs2_sq_tr Hbmid_sq_tr.
    (* (6d) Combine via sqrt monotonicity.
       Rs4 * Rs2 * Rs4 ≤ √(d_A · Sval) iff (Rs4 * Rs2 * Rs4)^2 ≤ d_A · Sval. *)
    have HSval_ge0 : (0 <= Sval)%R.
      rewrite -HRs2_sq; exact: exprn_ge0.
    have Hprod_ge0 : (0 <= Rs4 * Rs2 * Rs4)%R.
      by apply: mulr_ge0 => //; apply: mulr_ge0.
    rewrite -[X in (X <= _)%R](ger0_norm Hprod_ge0) -sqrtr_sqr.
    apply: ler_wsqrtr.
    (* Goal: (Rs4 * Rs2 * Rs4)^+2 ≤ d_A · Sval *)
    rewrite !exprMn HRs2_sq.
    (* Rs4^+2 * Sval * Rs4^+2 ≤ d_A * Sval *)
    rewrite -mulrA [Sval * _]mulrC mulrA -exprD /=.
    by apply: ler_wpM2r.
  (* proof step of lemma:uniform-to-collision (Lem. 4): 4-term            *)
  (* expansion of Tr((wdiff · Minv)²).                                    *)
  (* Cross terms collapse via partial trace Tr(ρ·(I_A⊗X)) = Tr(ρ_B · X);    *)
  (* diagonal term with ω_A ⊗ ρ_B picks up a (1/d_A) from Tr(I_A ⊗ M) =     *)
  (* d_A · Tr M cancellation.                                                *)
  have Htrexpand : ((dim 'H[HL]_A)%:R * Sval =
      (dim 'H[HL]_A)%:R * collision_ent rhoAB tauB -
      @complex.Re R (\Tr (ptrace_castl disAB rhoAB \o pinvlf (sqrtH tauB)
        \o ptrace_castl disAB rhoAB \o pinvlf (sqrtH tauB))))%R.
    set dA := (dim 'H[HL]_A)%:R : R.
    set rhoB_ := ptrace_castl disAB rhoAB.
    set M_ := pinvlf (sqrtH tauB).
    set Wlift : 'F[HL]_S_AB := (\1 : 'F_A) \O rhoB_.
    pose RBMR : C := \Tr (rhoB_ \o M_ \o rhoB_ \o M_).
    have dA_pos : (0 < dA)%R by rewrite /dA ltr0n dim_proper.
    have dA_neq0 : dA != 0 :> R by rewrite gt_eqF.
    have dAc_neq0 : dA%:C != 0.
      rewrite realc_eq0; exact: dA_neq0.
    (* Sdot composition regroupings. *)
    have E_MWM :
      Minv \o Wlift \o Minv = (\1 : 'F_A) \O (M_ \o rhoB_ \o M_).
      by rewrite /Minv /Wlift !sdotI_comp.
    have E_WMWM :
      Wlift \o Minv \o Wlift \o Minv =
      (\1 : 'F_A) \O (rhoB_ \o M_ \o rhoB_ \o M_).
      by rewrite /Minv /Wlift !sdotI_comp.
    (* Four trace identities for the 2×2 bilinear expansion. *)
    have TrT1 : \Tr (rhoAB \o Minv \o rhoAB \o Minv) =
                \Tr (Minv \o rhoAB \o Minv \o rhoAB).
      rewrite -!comp_lfunA lftraceC.
      by rewrite !comp_lfunA.
    have TrT2 : \Tr (rhoAB \o Minv \o Wlift \o Minv) = RBMR.
      rewrite -!comp_lfunA [Minv \o (Wlift \o Minv)]comp_lfunA E_MWM.
      rewrite (trlf_lift_partial disAB rhoAB (M_ \o rhoB_ \o M_)).
      by rewrite /RBMR !comp_lfunA.
    have TrT3 : \Tr (Wlift \o Minv \o rhoAB \o Minv) = RBMR.
      rewrite -TrT2 -[Wlift \o Minv \o rhoAB \o Minv]comp_lfunA.
      rewrite lftraceC.
      by rewrite !comp_lfunA.
    have TrT4 : \Tr (Wlift \o Minv \o Wlift \o Minv) = dA%:C * RBMR.
      rewrite E_WMWM (trlf_lift_I disAB).
      by rewrite /dA /RBMR natrC.
    (* Bilinear expansion of Tr(wdiff \o Minv \o wdiff \o Minv). *)
      have E_wdiff : wdiff = rhoAB + (- dA%:C^-1) *: Wlift.
        by rewrite /wdiff /dA /Wlift natrC scaleNr.
    have Hexp :
      \Tr (wdiff \o Minv \o wdiff \o Minv) =
      \Tr (rhoAB \o Minv \o rhoAB \o Minv)
      - (dA%:C^-1) * \Tr (rhoAB \o Minv \o Wlift \o Minv)
      - (dA%:C^-1) * \Tr (Wlift \o Minv \o rhoAB \o Minv)
        + (dA%:C^-1 * dA%:C^-1) *
          \Tr (Wlift \o Minv \o Wlift \o Minv).
        rewrite {1 2}E_wdiff !(comp_lfunDl, comp_lfunDr).
        rewrite -!(comp_lfunZl, comp_lfunZr) !linearD /=.
        rewrite linearZ /=.
        rewrite linearZ /=.
        rewrite linearZ /=.
        rewrite linearZ /= !mulNr !mulrN !opprK.
        rewrite !mulrA.
      rewrite -!addrA.
      rewrite [X in _ + X]addrCA.
      by reflexivity.
    (* Assemble at C level: the trace equals `CE_chainC - Nc^-1 * RBMR`. *)
    have Hreduce :
      \Tr (wdiff \o Minv \o wdiff \o Minv) =
      \Tr (Minv \o rhoAB \o Minv \o rhoAB) - (dA%:C^-1) * RBMR.
      rewrite Hexp TrT1 TrT2 TrT3 TrT4 [(dA%:C^-1 * dA%:C^-1) * (dA%:C * RBMR)]mulrA.
      rewrite -[(dA%:C^-1 * dA%:C^-1) * dA%:C]mulrA mulVf // mulr1.
      by rewrite -addrA addNr addr0.
    (* Convert to R and scale by dA. *)
    rewrite /Sval Hreduce.
    have ReCmul : forall (c : R) (z : C),
        @complex.Re R (c%:C * z) = c * @complex.Re R z.
      by move=> c [x y] /=; rewrite mul0r subr0.
    rewrite raddfB /= -realcI ReCmul /collision_ent -/Minv mulrBr.
    congr (_ - _).
    by rewrite mulrA mulfV // mul1r.
  rewrite Htrexpand in Hhoelder.
  have H01 : (0 <= (2%:R : R)^-1)%R by rewrite invr_ge0 ler0n.
  have Hhalf := ler_wpM2l H01 Hhoelder.
  rewrite /wdiff in Hhalf.
  exact: Hhalf.
Qed.
(* Tomamichel-Schaffner-Smith-Renner, 'Leftover Hashing Against Quantum     *)
(* Side Information' (IEEE Trans. IT 57:5524 (2011); arXiv:1002.2436),       *)
(* Lem. 4 — tex lemma:uniform-to-collision                                   *)
(* math: d_u(ρ_AB) ≤ ½√(d_A · Γ_C(ρ_AB | τ_B) − Tr(ρ_B τ_B^{-½} ρ_B τ_B^{-½})) *)
(* path: lhl:uniform_to_collision -> lhl:two_universal_hashing -> *)
(*   bb84:privacy_amplification -> bb84:bb84_secret *)
Lemma uniform_to_collision (rhoAB : 'F[HL]_S_AB) (tauB : 'F[HL]_B) :
  rhoAB \is psdlf -> tauB \is psdlf ->
  @complex.Re R (\Tr tauB) <= 1 ->
  (supph (ptrace_castl disAB rhoAB) `<=` supph tauB)%HS ->
  let rhoB := ptrace_castl disAB rhoAB in
  let tau_inv_half := pinvlf (sqrtH tauB) in
  dist_from_uniform rhoAB <=
  (2%:R)^-1 * Num.sqrt (
    (dim 'H[HL]_A)%:R * collision_ent rhoAB tauB
    - @complex.Re R (\Tr (rhoB \o tau_inv_half \o rhoB \o tau_inv_half))).
Proof.
  move=> Prho Ptau Htr Hsupp /=.
  pose wdiff := rhoAB - (dim 'H[HL]_A)%:R^-1 *:
                  ((\1 : 'F_A) \O ptrace_castl disAB rhoAB).
  have PrhoB : ptrace_castl disAB rhoAB \is psdlf
    by apply: (@ptrace_castl_psdlf R L HL _ _ disAB _ Prho).
  have Htrsig : \Tr (ptrace_castl disAB rhoAB) = \Tr (\Tr_(A) rhoAB).
    by rewrite /ptrace_castl /ptrace_cast_gen castlf_trlfE.
  have Hwit : (2%:R * dist_from_uniform rhoAB <= trnormH wdiff)%R.
    rewrite /wdiff.
    apply: dist_uniform_witness_bound.
    - exact: PrhoB.
    - exact: Htrsig.
  have H01 : (0 <= (2%:R : R)^-1)%R by rewrite invr_ge0 ler0n.
  have Hhalf := ler_wpM2l H01 Hwit.
  rewrite mulrA mulVf ?pnatr_eq0 // mul1r in Hhalf.
  have Hcore := @uniform_collision_bound rhoAB tauB Prho Ptau Htr Hsupp.
  rewrite /= -/wdiff in Hcore.
  rewrite /wdiff in Hhalf.
  exact: le_trans Hhalf Hcore.
Qed.
End UnifToColl.
(* ================================================================== *)
(* Privacy amplification                                                *)
(* Tomamichel-Schaffner-Smith-Renner, 'Leftover Hashing Against Quantum *)
(* Side Information' (IEEE Trans. IT 57:5524 (2011); arXiv:1002.2436),   *)
(* Lem. 5 — tex lemma:privacy-amp — math: for δ-almost-two-universal F,  *)
(* Γ_C(ρ_FZE | ρ_F ⊗ τ_E) ≤ Γ_C(ρ_XE|τ_E) + δ·Tr(ρ_E τ_E^{-½} ρ_E τ_E^{-½}). *)
(* ================================================================== *)
Section PrivacyAmp.
Variable (L : finType) (HL : L -> chsType) (X E Fl Zl : {set L}).
Hypothesis disXE : [disjoint X & E].
Hypothesis disXF : [disjoint X & Fl].
Hypothesis disXZ : [disjoint X & Zl].
Hypothesis disEF : [disjoint E & Fl].
Hypothesis disEZ : [disjoint E & Zl].
Hypothesis disFZ : [disjoint Fl & Zl].
Notation S_XE := (X :|: E).
Let disZl_FE : [disjoint Zl & (Fl :|: E)].
Proof. by rewrite disjointXU disjoint_sym disFZ disjoint_sym disEZ. Defined.
(* ================================================================== *)
(* Infrastructure for privacy_amp:                                      *)
(*   - Gamma_C_post_hash_split : expand Γ_C(ρ_ZFE | ρ_F ⊗ τ) into       *)
(*     Γ_C(ρ_XE | τ) + cross-terms from the hash function Fh.           *)
(*   - Gamma_C_post_hash_offdiag_bound : bound cross-terms by           *)
(*     (1/|Z|)·Tr(ρ_E τ^{-½} ρ_E τ^{-½}) using 2-universality of Fh.    *)
(* ================================================================== *)
(* proof step 1 of lemma:privacy-amp (Lem. 5; Tomamichel-Schaffner-      *)
(* Smith-Renner, "Leftover Hashing Against Quantum Side Information",     *)
(* IEEE Trans. IT 57:5524 (2011); arXiv:1002.2436) Γ_C expansion         *)
(* math: Γ_C(ρ_ZFE | ρ_F ⊗ τ) = (1/|F|)·Σ_{x,x'} |{f: Fh f x=Fh f x'}|·  *)
(*       Re Tr(cq_x·τ^{-½}·cq_{x'}·τ^{-½}).                              *)
(* Standalone justification: textbook tensor-product + projector-trace   *)
(* expansion of the collision-entropy quadratic form on the post-hash    *)
(* CQ state, using orthogonality of |z⟩⟨z| and |f⟩⟨f|.                 *)
(* Gamma_C_post_hash_expand *)
(* infra: no tex label — fundamental & reusable (mathcomp-style) *)
(* consumer: Gamma_C_post_hash_expand is used downstream by the BB84 secrecy proof. *)
(* path: lhl:Gamma_C_post_hash_expand -> lhl:Gamma_C_post_hash_split -> *)
(*   lhl:privacy_amp -> bb84:privacy_amplification -> *)
(*   bb84:bb84_secret *)
Lemma Gamma_C_post_hash_expand
    (rhoXE : 'F[HL]_S_XE) (tauE : 'F[HL]_E)
    (Fh : 'Idx[HL]_Fl -> 'Idx[HL]_X -> 'Idx[HL]_Zl) :
  rhoXE \is psdlf ->
  tauE \is psdlf ->
  is_cq_state rhoXE ->
  collision_ent (post_hash_state disXE Fh rhoXE)
    (((dim 'H[HL]_Fl)%:R^-1)%:C *: ((\1 : 'F_Fl) \O tauE)) =
  ((dim 'H[HL]_Fl)%:R^-1)%R *
  \sum_(x : 'Idx[HL]_X) \sum_(x' : 'Idx[HL]_X)
    (#|[set f : 'Idx[HL]_Fl | Fh f x == Fh f x']|%:R : R) *
    @complex.Re R (\Tr (
      cq_block disXE x rhoXE \o pinvlf (sqrtH tauE) \o
      cq_block disXE x' rhoXE \o pinvlf (sqrtH tauE))).
Proof.
  move=> Prho Ptau Hcq.
  rewrite (Gamma_C_post_hash_block_form
            disXE disXF disXZ disEF disEZ disFZ Fh Prho Ptau Hcq).
  congr (_ * _).
  pose P := pinvlf (sqrtH tauE).
  pose T (x x' : 'Idx[HL]_X) : R :=
    @complex.Re R (\Tr (cq_block disXE x rhoXE \o P \o
                         cq_block disXE x' rhoXE \o P)).
  transitivity
    (\sum_(f : 'Idx[HL]_Fl) \sum_(z : 'Idx[HL]_Zl)
      \sum_(x : 'Idx[HL]_X | Fh f x == z)
        \sum_(x' : 'Idx[HL]_X | Fh f x' == z) T x x').
  { apply: eq_bigr => f _; apply: eq_bigr => z _.
    rewrite /T -/P.
    have Hexp :
      (\sum_(x : 'Idx[HL]_X | Fh f x == z) cq_block disXE x rhoXE) \o P \o
      (\sum_(x' : 'Idx[HL]_X | Fh f x' == z) cq_block disXE x' rhoXE) \o P =
      \sum_(x : 'Idx[HL]_X | Fh f x == z)
        \sum_(x' : 'Idx[HL]_X | Fh f x' == z)
          (cq_block disXE x rhoXE \o P \o cq_block disXE x' rhoXE \o P).
    { rewrite linear_sumlz /= linear_sumlz /= linear_sumlz /=.
      apply: eq_bigr => x _.
      rewrite linear_sumr /= linear_sumlz /=.
      by apply: eq_bigr => x' _. }
    rewrite Hexp.
    have HTr_inner :
      \Tr (\sum_(x : 'Idx[HL]_X | Fh f x == z)
            \sum_(x' : 'Idx[HL]_X | Fh f x' == z)
              (cq_block disXE x rhoXE \o P \o
               cq_block disXE x' rhoXE \o P)) =
      \sum_(x : 'Idx[HL]_X | Fh f x == z)
        \sum_(x' : 'Idx[HL]_X | Fh f x' == z)
          \Tr (cq_block disXE x rhoXE \o P \o
               cq_block disXE x' rhoXE \o P).
    { rewrite linear_sum /=; apply: eq_bigr => x _.
      by rewrite linear_sum /=. }
    rewrite HTr_inner.
    rewrite raddf_sum /=; apply: eq_bigr => x _.
    by rewrite raddf_sum /=. }
  exact: (partition_count_double_sum Fh T).
Qed.
(* proof step 1 of lemma:privacy-amp (Lem. 5; Tomamichel-Schaffner-      *)
(* Smith-Renner, "Leftover Hashing Against Quantum Side Information",     *)
(* IEEE Trans. IT 57:5524 (2011); arXiv:1002.2436) Γ_C expansion         *)
(* (combined form).                                                       *)
(* math: Γ_C(ρ_ZFE | ρ_F ⊗ τ) ≤ Γ_C(ρ_XE | τ) plus off-diagonal         *)
(* contributions parameterized by pairs (x, x') with x ≠ x'.             *)
(* Structural note: proof uses two Γ_C decomposition identities:         *)
(*   Hexpand  (via Gamma_C_post_hash_expand) :                           *)
(*     Γ_C(ρ_ZFE | ρ_F ⊗ τ) = (1/|F|)·Σ_{x,x'} count·T(x,x')            *)
(*   Hcqdiag : Γ_C(ρ_XE  | τ)       = Σ_x T(x,x)                         *)
(* (where T(x,x') := Re Tr(cq_x · τ^{-½} · cq_{x'} · τ^{-½})).          *)
(* Gamma_C_post_hash_split *)
(* infra: no tex label — fundamental & reusable (mathcomp-style) *)
(* consumer: Gamma_C_post_hash_split is used downstream by the BB84 secrecy proof. *)
(* path: lhl:Gamma_C_post_hash_split -> lhl:privacy_amp -> *)
(*   bb84:privacy_amplification -> bb84:bb84_secret *)
Lemma Gamma_C_post_hash_split
    (rhoXE : 'F[HL]_S_XE) (tauE : 'F[HL]_E)
    (Fh : 'Idx[HL]_Fl -> 'Idx[HL]_X -> 'Idx[HL]_Zl) :
  rhoXE \is psdlf ->
  tauE \is psdlf ->
  is_cq_state rhoXE ->
  let rhoZFE := post_hash_state disXE Fh rhoXE in
  let rhoF_tauE := ((dim 'H[HL]_Fl)%:R^-1)%:C *: ((\1 : 'F_Fl) \O tauE) in
  let tau_inv_half := pinvlf (sqrtH tauE) in
  let inv_Fl : R := ((dim 'H[HL]_Fl)%:R^-1)%R in
  (collision_ent rhoZFE rhoF_tauE <=
  collision_ent rhoXE tauE +
  inv_Fl *
  \sum_(x : 'Idx[HL]_X) \sum_(x' : 'Idx[HL]_X | x' != x)
    (#|[set f : 'Idx[HL]_Fl | Fh f x == Fh f x']|%:R : R) *
    @complex.Re R (\Tr (
      cq_block disXE x rhoXE \o tau_inv_half \o
      cq_block disXE x' rhoXE \o tau_inv_half))).
Proof.
  move=> Hrho Htau Hcq /=; set P := pinvlf (sqrtH tauE).
  set inv_Fl : R := ((dim 'H[HL]_Fl)%:R^-1)%R.
  (* ----------------------------------------------------------------- *)
  (* Inline identity Hcqdiag: Γ_C CQ-diagonal form.                     *)
  (*                                                                    *)
  (* Proof route with six numbered CQ-diagonal identities:              *)
  (*   HQ-1: self-adjointness of K_x                                    *)
  (*   HQ-2: block-extraction identity K_x·ρ·K_x = [>x<]\O cq_x         *)
  (*   HQ-3: CQ decomposition rhoXE = Σ_x ([>x<]\O cq_x)   (provable   *)
  (*          inline given HQ-1 + HQ-2)                                 *)
  (*   HQ-4: per-pair quadruple product split on `x == y`              *)
  (*   HQ-5: distribute double sum through quadruple product           *)
  (*   HQ-6: trace-of-tensor + Re-linearity + cyclicity finish         *)
  (* ----------------------------------------------------------------- *)
  have Hcqdiag :
    collision_ent rhoXE tauE =
    \sum_(x : 'Idx[HL]_X)
      @complex.Re R (\Tr (
        cq_block disXE x rhoXE \o P \o
        cq_block disXE x rhoXE \o P)).
  { rewrite /collision_ent /=.
    rewrite -/P.
    (* [HQ-1] Self-adjointness K_x^A = K_x for K_x := [>dv x<] \O \1_E.  *)
    (* Provable inline: copy pattern from util.v:838 (HKadj in           *)
    (* cq_sum_cq_block_eq_ptrace_castl).                                 *)
    have HKadj : forall x : 'Idx[HL]_X,
      (([> deltav x; deltav x <] \O (\1 : 'F[HL]_E)
         : 'F[HL]_S_XE))^A =
      [> deltav x; deltav x <] \O (\1 : 'F[HL]_E).
    { move=> x.
      have Htensor : ([> deltav x; deltav x <] \O (\1 : 'F[HL]_E)
                      : 'F[HL]_S_XE) =
                     [> deltav x; deltav x <] \⊗ (\1 : 'F[HL]_E).
        by apply: to_Fnd_inj; rewrite (sdotFT _ _ disXE) to_Fnd_tenE.
      by rewrite Htensor tenf_adj adj_outp adjf1 -Htensor. }
    (* [HQ-2] Block-extraction identity K_x·ρ·K_x = [>dv x<] \O cq_x.    *)
    (* Holds for any ρ_XE, not only CQ states. Proof: apply               *)
    (* `trlf_intror` +                                                    *)
    (* `trlf_lift_partial` + convert \O to \⊗ via sdotFT + tenf_comp,   *)
    (* then use dv_dot for [>x<] evaluation.                              *)
    have Kbox_eq : forall x : 'Idx[HL]_X,
      (([> deltav x; deltav x <] \O (\1 : 'F[HL]_E)
        : 'F[HL]_S_XE) \o rhoXE \o
       ([> deltav x; deltav x <] \O (\1 : 'F[HL]_E)
        : 'F[HL]_S_XE)) =
      [> deltav x; deltav x <] \O cq_block disXE x rhoXE.
    { move=> x.
      set K := ([> deltav x; deltav x <] \O (\1 : 'F[HL]_E)
                : 'F[HL]_S_XE).
      have HK_ten : K = [> deltav x; deltav x <] \⊗
                        (\1 : 'F[HL]_E).
        by apply: to_Fnd_inj; rewrite (sdotFT _ _ disXE) to_Fnd_tenE.
      have HRHS_ten :
        ([> deltav x; deltav x <] \O cq_block disXE x rhoXE
          : 'F[HL]_S_XE) =
        [> deltav x; deltav x <] \⊗ cq_block disXE x rhoXE.
        by apply: to_Fnd_inj; rewrite (sdotFT _ _ disXE) to_Fnd_tenE.
      have H1O : forall (Y : 'F[HL]_E),
        ((\1 : 'F[HL]_X) \O Y : 'F[HL]_S_XE) =
        (\1 : 'F[HL]_X) \⊗ Y.
        by move=> Y; apply: to_Fnd_inj;
           rewrite (sdotFT _ _ disXE) to_Fnd_tenE.
      rewrite HRHS_ten.
      (* Matrix element identity for cq_block_x:
         <dv e_v; cq_block_x rho (dv e_u)>
           = <dv (idxU x e_v); rhoXE (dv (idxU x e_u))>.  *)
      have Hmx_cq : forall (e_u e_v : 'Idx[HL]_E),
        [< deltav e_v;
           cq_block disXE x rhoXE (deltav e_u) >] =
        [< deltav (idxU x e_v);
           rhoXE (deltav (idxU x e_u)) >].
      { move=> e_u e_v.
        (* Trace form: <dv e_v; Y(dv e_u)> = \Tr(Y \o [>dv e_u; dv e_v<]). *)
        rewrite -!outp_trlf -!outp_compr.
        (* Both sides now are traces.  Unfold cq_block on LHS and apply
           trlf_lift_partial in reverse to express as K-sandwich trace. *)
        rewrite /cq_block.
        rewrite -(trlf_lift_partial disXE _ [>deltav e_u; deltav e_v<]).
        (* LHS: \Tr((K rho K) \o (\1 \O [>dv e_u; dv e_v<])). *)
        rewrite -/K HK_ten H1O.
        (* Simplify K \o (\1 \⊗ [>..<]) \o K to [>x;x<] \⊗ [>..<]. *)
        have HKmid :
          ([> deltav x; deltav x <] \⊗ (\1 : 'F[HL]_E)
            : 'F[HL]_S_XE) \o
          ((\1 : 'F[HL]_X) \⊗
            [> deltav e_u; deltav e_v <]) \o
          ([> deltav x; deltav x <] \⊗ (\1 : 'F[HL]_E)
            : 'F[HL]_S_XE) =
          ([> deltav x; deltav x <] \⊗
            [> deltav e_u; deltav e_v <] : 'F[HL]_S_XE).
        { rewrite -tenf_comp; last exact: disXE.
          rewrite !comp_lfun1l !comp_lfun1r.
          rewrite -tenf_comp; last exact: disXE.
          rewrite !comp_lfun1r.
          by rewrite outp_comp dv_dot eqxx scale1r. }
        (* Cyclically reorder LHS to apply HKmid. *)
        rewrite -!comp_lfunA lftraceC -comp_lfunA HKmid.
        (* Goal: \Tr (rhoXE \o ([>x;x<] \⊗ [>e_u; e_v<])) =
                \Tr (rhoXE \o [>idxU x e_u; idxU x e_v<]).  *)
        congr (\Tr (_ \o _)).
        rewrite tenf_outp.
        by rewrite !(dv_tensor _ _ disXE). }
      have HK_adj : K^A = K.
        by rewrite HK_ten tenf_adj adj_outp adjf1 -HK_ten.
      (* Generic identity: K (dv w) = (x == idxSl w)%:R *: dv (idxU x (idxSr w)). *)
      have HKdv : forall w : 'Idx[HL]_S_XE,
        K (deltav w) =
        (x == idxSl w)%:R *: deltav (idxU x (idxSr w)).
      { move=> w.
        rewrite HK_ten -tenf_dv outpE lfunE /= tenvZl dv_dot.
        by rewrite (dv_tensor _ _ disXE). }
      (* Reduce main goal to matrix elements. *)
      apply/lfunPD => u.
      apply/intro_cdvl => v.
      rewrite !comp_lfunE.
      (* simplify inner K (dv u). *)
      rewrite {1}HKdv.
      (* pull scalar through rhoXE (linear) and K (linear); cdv is
         a scalar functional, so the scalar comes out multiplicatively. *)
      rewrite !linearZ /=.
      (* outer K via adjoint: cdv v (K z) = <K^A dv v; z> = <K dv v; z>. *)
      rewrite cdvE -adj_dotEl HK_adj.
      rewrite HKdv dotpZl conjC_nat.
      (* LHS: (x==idxSl u)%:R * ((x==idxSl v)%:R *
             <dv (idxU x (idxSr v)); rhoXE (dv (idxU x (idxSr u)))>). *)
      (* RHS: simplify ([>x;x<] \⊗ cq_block_x rho) (dv u). *)
      rewrite -tenf_dv outpE tenvZl dv_dot linearZ /=.
      rewrite cdvE {1}(dv_split v) tenv_dot; last exact: disXE.
      rewrite dv_dot.
      (* Now both sides: (x == idxSl u)%:R * (<stuff> * <inner product>). *)
      rewrite [in X in _ = _ * (X * _)]eq_sym.
      (* Align factors and apply Hmx_cq on the inner-product factor. *)
      congr (_ * (_ * _)).
      by rewrite Hmx_cq. }
    (* [HQ-3] CQ decomposition rhoXE = Σ_x ([>dv x<] \O cq_x).           *)
    (* Fully provable inline once HQ-2 is closed:                        *)
    (*   rhoXE = dephase_X_so rhoXE  [dephase_X_cq_id Hcq]               *)
    (*         = Σ_x K_x · rhoXE · (K_x)^A  [kraussoE]                  *)
    (*         = Σ_x K_x · rhoXE · K_x     [HKadj]                      *)
    (*         = Σ_x [>dv x<] \O cq_x       [Kbox_eq]                    *)
    have HrhoCQ : rhoXE =
      \sum_(x : 'Idx[HL]_X)
        ([> deltav x; deltav x <] \O cq_block disXE x rhoXE
          : 'F[HL]_S_XE).
    { rewrite -{1}(dephase_X_cq_id disXE Hcq).
      rewrite /dephase_X_so kraussoE.
      apply: eq_bigr => x _.
      by rewrite HKadj Kbox_eq. }
    (* [HQ-4] Per-pair quadruple product evaluates to diagonal term.     *)
    (*   (\1\O P) \o ([>x<]\O cq_x) \o (\1\O P) \o ([>y<]\O cq_y)        *)
    (*     = if x == y then [>x<] \⊗ (cq_x · P · cq_x · P) else 0.      *)
    (* Proof: convert all \O to \⊗ via `sdotFT disXE`; use `tenf_comp`   *)
    (* to merge compositions factor-wise; on X-factor use                *)
    (*   [>dv x;dv x<] \o [>dv y;dv y<] = <dv x | dv y> [>dv x;dv y<]   *)
    (*   = [x=y] [>dv x; dv x<]                                          *)
    (* (via outp_compl or direct computation + dv_dot); on E-factor      *)
    (* collect `P \o cq_x \o P \o cq_y`.  Case split on `x == y` + zero. *)
    have HQpair : forall x y : 'Idx[HL]_X,
      (((\1 : 'F[HL]_X) \O P : 'F[HL]_S_XE) \o
       ([> deltav x; deltav x <] \O cq_block disXE x rhoXE
         : 'F[HL]_S_XE) \o
       ((\1 : 'F[HL]_X) \O P : 'F[HL]_S_XE) \o
       ([> deltav y; deltav y <] \O cq_block disXE y rhoXE
         : 'F[HL]_S_XE)) =
      (if x == y then
         ([> deltav x; deltav x <] \⊗
          (P \o cq_block disXE x rhoXE \o P \o cq_block disXE x rhoXE)
           : 'F[HL]_S_XE)
       else 0).
    { move=> x y.
      have HtensorA : ((\1 : 'F[HL]_X) \O P : 'F[HL]_S_XE) =
                      (\1 : 'F[HL]_X) \⊗ P.
        by apply: to_Fnd_inj; rewrite (sdotFT _ _ disXE) to_Fnd_tenE.
      have HtensorU : forall a : 'Idx[HL]_X,
        ([> deltav a; deltav a <] \O cq_block disXE a rhoXE
          : 'F[HL]_S_XE) =
        [> deltav a; deltav a <] \⊗ cq_block disXE a rhoXE.
        by move=> a; apply: to_Fnd_inj;
           rewrite (sdotFT _ _ disXE) to_Fnd_tenE.
      rewrite HtensorA !HtensorU.
      do ! (rewrite -tenf_comp; last exact: disXE).
      rewrite !comp_lfun1l !comp_lfun1r outp_comp dv_dot.
      case Hxy: (x == y).
      - move/eqP: Hxy => Hxy.
        subst y.
        by rewrite /= scale1r.
      - by rewrite /= scale0r ten0f.
      }
    (* [HQ-5] Distribute double sum through quadruple product.            *)
    (*   (\1\O P) \o rhoXE \o (\1\O P) \o rhoXE                           *)
    (*     = Σ_x Σ_y  (per-pair term)                                     *)
    (*     = Σ_x [>x<] \⊗ (cq_x·P·cq_x·P)    [after HQpair collapses].   *)
    (* Proof: rewrite rhoXE via HrhoCQ (positions 2 and 4); use           *)
    (*   `linear_sumlz` / `linear_sumr` to push Σ past compositions;       *)
    (*   apply HQpair per term; collapse `if x == y` via                  *)
    (*   `bigID (fun y => y == x)` + `big_pred1_eq` + `big1` for the 0's. *)
    have Hdist :
      (((\1 : 'F[HL]_X) \O P : 'F[HL]_S_XE) \o rhoXE \o
       ((\1 : 'F[HL]_X) \O P : 'F[HL]_S_XE) \o rhoXE) =
      \sum_(x : 'Idx[HL]_X)
        ([> deltav x; deltav x <] \⊗
         (P \o cq_block disXE x rhoXE \o P \o cq_block disXE x rhoXE)
          : 'F[HL]_S_XE).
    { rewrite {1 2}HrhoCQ.
      rewrite linear_sumr /=.
      under eq_bigr => y _ do
        rewrite linear_sumr /= linear_sumlz /= linear_sumlz /=.
      rewrite exchange_big /=.
      apply: eq_bigr => x _.
      under eq_bigr => y _ do rewrite HQpair.
      rewrite (bigD1 x) //= eqxx big1 ?addr0 //.
      by move=> y /negbTE Hyx; rewrite eq_sym Hyx. }
    (* [HQ-6] Trace + Re finalization.                                    *)
    (*   rewrite Hdist, push Tr through Σ_x via `linear_sum`, push Re    *)
    (*   through Σ_x via `raddf_sum`, factor each                          *)
    (*     Tr([>x<] \⊗ Y) = Tr[>x<] · Tr Y     [lftrace_tenf disXE]      *)
    (*   with Tr([>dv x; dv x<]) = ⟨dv x | dv x⟩ = 1  [outp_trlf+dv_dot].*)
    rewrite Hdist.
    have HTr_sum :
      \Tr (\sum_(x : 'Idx[HL]_X)
        ([> deltav x; deltav x <] \⊗
         (P \o cq_block disXE x rhoXE \o P \o cq_block disXE x rhoXE)
          : 'F[HL]_S_XE)) =
      \sum_(x : 'Idx[HL]_X)
        \Tr ([> deltav x; deltav x <] \⊗
         (P \o cq_block disXE x rhoXE \o P \o cq_block disXE x rhoXE)
          : 'F[HL]_S_XE).
      by rewrite linear_sum.
    rewrite HTr_sum.
    have HRe_sum :
      @complex.Re R (\sum_(x : 'Idx[HL]_X)
        \Tr ([> deltav x; deltav x <] \⊗
         (P \o cq_block disXE x rhoXE \o P \o cq_block disXE x rhoXE)
          : 'F[HL]_S_XE)) =
      \sum_(x : 'Idx[HL]_X) @complex.Re R
        (\Tr ([> deltav x; deltav x <] \⊗
         (P \o cq_block disXE x rhoXE \o P \o cq_block disXE x rhoXE)
          : 'F[HL]_S_XE)).
      by rewrite raddf_sum.
    rewrite HRe_sum.
    apply: eq_bigr => x _.
    rewrite lftrace_tenf; last exact: disXE.
    rewrite outp_trlf dv_dot eqxx mul1r.
    (* Cyclic: Tr(P · cq_x · P · cq_x) = Tr(cq_x · P · cq_x · P). *)
    rewrite -[\Tr (_ \o _ \o _ \o _)]lftraceC.
    by rewrite !comp_lfunA. }
  (* Γ_C expansion on post-hash CQ state via standalone lemma.           *)
  have Hexpand := @Gamma_C_post_hash_expand rhoXE tauE Fh Hrho Htau Hcq.
  rewrite -/P -/inv_Fl in Hexpand.
  rewrite Hexpand Hcqdiag.
  have HdimFl_ne0 : ((dim 'H[HL]_Fl)%:R : R) != 0.
    by rewrite pnatr_eq0 -lt0n dim_proper.
  (* Goal (after rewrites):
       inv_Fl * Σ_x Σ_{x'} count * T x x' ≤
       Σ_x T x x + inv_Fl * Σ_x Σ_{x'≠x} count * T x x'
     where T x x' = Re Tr(cq_x · P · cq_{x'} · P). *)
  have Heq :
    (inv_Fl *
      \sum_(x : 'Idx[HL]_X) \sum_(x' : 'Idx[HL]_X)
        (#|[set f : 'Idx[HL]_Fl | Fh f x == Fh f x']|%:R : R) *
        @complex.Re R (\Tr (cq_block disXE x rhoXE \o P \o
                            cq_block disXE x' rhoXE \o P)))%R =
    (\sum_(x : 'Idx[HL]_X)
      @complex.Re R (\Tr (cq_block disXE x rhoXE \o P \o
                          cq_block disXE x rhoXE \o P)) +
    inv_Fl *
      \sum_(x : 'Idx[HL]_X) \sum_(x' : 'Idx[HL]_X | x' != x)
        (#|[set f : 'Idx[HL]_Fl | Fh f x == Fh f x']|%:R : R) *
        @complex.Re R (\Tr (cq_block disXE x rhoXE \o P \o
                            cq_block disXE x' rhoXE \o P)))%R.
    rewrite mulr_sumr [X in _ = _ + X]mulr_sumr.
    rewrite -big_split /=.
    apply: eq_bigr => x _.
    rewrite (bigID (fun x' => x' != x)) /=.
    rewrite mulrDr [X in _ = X]addrC.
    congr (_ + _).
    rewrite (eq_bigl (pred1 x)); last first.
      by move=> x' /=; rewrite negbK.
    rewrite big_pred1_eq.
    have Hcount_diag :
      (#|[set f : 'Idx[HL]_Fl | Fh f x == Fh f x]|%:R : R) =
      (dim 'H[HL]_Fl)%:R.
      congr (_%:R).
      rewrite -idx_card.
      apply: eq_card => f.
      by rewrite !inE eqxx.
    rewrite Hcount_diag mulrA /inv_Fl mulVf// mul1r.
    by [].
  rewrite Heq; exact: lexx.
Qed.
(* proof step 2 of lemma:privacy-amp (Lem. 5; Tomamichel-Schaffner-      *)
(* Smith-Renner, "Leftover Hashing Against Quantum Side Information",     *)
(* IEEE Trans. IT 57:5524 (2011); arXiv:1002.2436) — 2-universality bound *)
(* math: Using |{f : Fh f x = Fh f x'}| ≤ |F|/|Z| for x ≠ x', the         *)
(* off-diagonal sum is bounded by (1/|Z|)·Tr(ρ_E τ^{-½} ρ_E τ^{-½})       *)
(* where ρ_E = Σ_x cq_block x.                                            *)
(* Standalone justification: textbook reduction using 2-universality +   *)
(* Σ_{x,x'} cq_block = ρ_E tensor-product structure.                      *)
(* Gamma_C_post_hash_offdiag_bound *)
(* infra: no tex label — fundamental & reusable (mathcomp-style) *)
(* consumer: Gamma_C_post_hash_offdiag_bound is used downstream by the BB84 secrecy proof. *)
(* path: lhl:Gamma_C_post_hash_offdiag_bound -> lhl:privacy_amp -> *)
(*   bb84:privacy_amplification -> bb84:bb84_secret *)
Lemma Gamma_C_post_hash_offdiag_bound
    (rhoXE : 'F[HL]_S_XE) (tauE : 'F[HL]_E)
    (Fh : 'Idx[HL]_Fl -> 'Idx[HL]_X -> 'Idx[HL]_Zl)
    (delta : R) :
  rhoXE \is psdlf ->
  tauE \is psdlf ->
  is_cq_state rhoXE ->
  0 <= delta ->
  (forall x x' : 'Idx[HL]_X, x != x' ->
    (#|[set f : 'Idx[HL]_Fl | Fh f x == Fh f x']|%:R /
    (dim 'H[HL]_Fl)%:R : R) <= delta) ->
  let tau_inv_half := pinvlf (sqrtH tauE) in
  let rhoE := ptrace_castl disXE rhoXE in
  let inv_Fl : R := ((dim 'H[HL]_Fl)%:R^-1)%R in
  ((inv_Fl *
  \sum_(x : 'Idx[HL]_X) \sum_(x' : 'Idx[HL]_X | x' != x)
    (#|[set f : 'Idx[HL]_Fl | Fh f x == Fh f x']|%:R : R) *
    @complex.Re R (\Tr (
      cq_block disXE x rhoXE \o tau_inv_half \o
      cq_block disXE x' rhoXE \o tau_inv_half)))%R <=
  (delta * @complex.Re R (\Tr (
    rhoE \o tau_inv_half \o rhoE \o tau_inv_half)))%R).
Proof.
  move=> Hrho Htau Hcq Hdelta HFh /=; set P := pinvlf (sqrtH tauE).
  set rE := ptrace_castl disXE rhoXE.
  set dinv : R := delta.
  set finv : R := ((dim 'H[HL]_Fl)%:R^-1)%R.
  pose T (x x' : 'Idx[HL]_X) : R :=
    @complex.Re R (\Tr (cq_block disXE x rhoXE \o P \o
                        cq_block disXE x' rhoXE \o P)).
  (* Setup: psd and non-negativity facts. *)
  have Htau_psd : tauE \is psdlf := Htau.
  have HP_psd : P \is psdlf := pinvlf_psdlf (sqrtH_psd Htau_psd).
  have HP_adj : P^A = P := hermlf_adjE (psdlf_herm HP_psd).
  have Hcq_psd : forall x, cq_block disXE x rhoXE \is psdlf.
    move=> x; rewrite /cq_block; apply: ptrace_castl_psdlf.
    rewrite psdlfE.
    have HP_eq : ([> deltav x; deltav x <] \O (\1 : 'F_E)
                  : 'F[HL]_S_XE) =
                 [> deltav x; deltav x <] \⊗ (\1 : 'F_E).
      by apply: to_Fnd_inj; rewrite (sdotFT _ _ disXE) to_Fnd_tenE.
    have Hadj : ([> deltav x; deltav x <] \O (\1 : 'F_E)
                 : 'F[HL]_S_XE)^A =
                [> deltav x; deltav x <] \O (\1 : 'F_E).
      by rewrite HP_eq tenf_adj adj_outp adjf1 -HP_eq.
    rewrite -{2}Hadj; apply: gef0_formfV; by rewrite -psdlfE.
  have HT_ge0 : forall x x' : 'Idx[HL]_X, 0 <= T x x'.
    move=> x x'; rewrite /T.
    have HPBP : P \o cq_block disXE x' rhoXE \o P \is psdlf.
      rewrite psdlfE -{2}HP_adj.
      apply: gef0_formfV.
      by move: (Hcq_psd x'); rewrite psdlfE.
    have Hre : cq_block disXE x rhoXE \o P \o cq_block disXE x' rhoXE \o P =
               cq_block disXE x rhoXE \o (P \o cq_block disXE x' rhoXE \o P).
      by rewrite !comp_lfunA.
    rewrite Hre.
    have Htr := psdlf_TrM (Hcq_psd x) HPBP.
    by move: Htr; rewrite lecE /= => /andP [_].
  have Hdinv_ge0 : 0 <= dinv by rewrite /dinv.
  have Hfinv_ge0 : 0 <= finv by rewrite /finv invr_ge0 ler0n.
  have HdimFl_ne0 : ((dim 'H[HL]_Fl)%:R : R) != 0.
    by rewrite pnatr_eq0 -lt0n dim_proper.
  (* term-wise 2-universality bound
       finv * count_{x,x'} * T x x' ≤ dinv * T x x' for x' ≠ x. *)
  have Hcoeff_le :
    (finv *
    \sum_(x : 'Idx[HL]_X) \sum_(x' : 'Idx[HL]_X | x' != x)
      (#|[set f : 'Idx[HL]_Fl | Fh f x == Fh f x']|%:R : R) * T x x') <=
    (\sum_(x : 'Idx[HL]_X) \sum_(x' : 'Idx[HL]_X | x' != x)
      dinv * T x x').
    rewrite mulr_sumr.
    apply: ler_sum => x _.
    rewrite mulr_sumr.
    apply: ler_sum => x' Hxx'.
    have HxNE : x != x' by rewrite eq_sym.
    have HFh_xx' := HFh x x' HxNE.
    (* goal: finv * (count * T) ≤ dinv * T *)
    rewrite [_ * (_ * _)]mulrA [finv * _]mulrC -[finv]/((dim 'H[HL]_Fl)%:R^-1)%R.
    apply: ler_pM.
    - by rewrite divr_ge0 ?ler0n.
    - exact: HT_ge0.
    - exact: HFh_xx'.
    - exact: lexx.
  (* Σ_{x'≠x} dinv * T ≤ Σ_{x'} dinv * T (via non-negative x'=x tail). *)
  have Hoffdiag_full :
    \sum_(x : 'Idx[HL]_X) \sum_(x' : 'Idx[HL]_X | x' != x)
      dinv * T x x' <=
    \sum_(x : 'Idx[HL]_X) \sum_(x' : 'Idx[HL]_X) dinv * T x x'.
    apply: ler_sum => x _.
    rewrite [X in _ <= X](bigID (fun x' => x' != x)) /=.
    rewrite lerDl.
    apply: sumr_ge0 => x' _.
    by apply: mulr_ge0.
  (* Σ_x Σ_{x'} dinv * T x x' = dinv * Re Tr(ρ_E · P · ρ_E · P). *)
  have HrhoE_eq : rE = \sum_(x : 'Idx[HL]_X) cq_block disXE x rhoXE.
    rewrite /rE.
    by rewrite (@cq_sum_cq_block_eq_ptrace_castl R L HL X E
                disXE rhoXE Hrho Hcq).
  have Hfull_trace :
    \sum_(x : 'Idx[HL]_X) \sum_(x' : 'Idx[HL]_X) dinv * T x x' =
    dinv * @complex.Re R (\Tr (rE \o P \o rE \o P)).
    transitivity (dinv *
      \sum_(x : 'Idx[HL]_X) \sum_(x' : 'Idx[HL]_X) T x x').
      rewrite mulr_sumr; apply: eq_bigr => x _.
      by rewrite mulr_sumr.
    congr (dinv * _).
    rewrite /T.
    have Hcomposite :
      (\sum_(a : 'Idx[HL]_X) cq_block disXE a rhoXE) \o P \o
      (\sum_(b : 'Idx[HL]_X) cq_block disXE b rhoXE) \o P =
      \sum_(a : 'Idx[HL]_X)
        (\sum_(b : 'Idx[HL]_X)
          (cq_block disXE a rhoXE \o P \o cq_block disXE b rhoXE \o P)).
      rewrite linear_sumlz /=.
      rewrite linear_sumlz /=.
      rewrite linear_sumlz /=.
      apply: eq_bigr => a _.
      rewrite linear_sumr /=.
      rewrite linear_sumlz /=.
      apply: eq_bigr => b _.
      by [].
    (* Tr-level equality: \sum \sum Tr = Tr(\sum \sum) *)
    have HTr_eq :
      \sum_(x : 'Idx[HL]_X) \sum_(x' : 'Idx[HL]_X)
        \Tr (cq_block disXE x rhoXE \o P \o
             cq_block disXE x' rhoXE \o P) =
      \Tr ((\sum_(a : 'Idx[HL]_X) cq_block disXE a rhoXE) \o P \o
           (\sum_(b : 'Idx[HL]_X) cq_block disXE b rhoXE) \o P).
      rewrite Hcomposite.
      rewrite linear_sum /=.
      apply: eq_bigr => x _.
      by rewrite linear_sum.
    (* Now combine with Re via raddf_sum *)
    have HRe_eq :
      \sum_(x : 'Idx[HL]_X) \sum_(x' : 'Idx[HL]_X)
        @complex.Re R (\Tr (cq_block disXE x rhoXE \o P \o
                             cq_block disXE x' rhoXE \o P)) =
      @complex.Re R
        (\sum_(x : 'Idx[HL]_X) \sum_(x' : 'Idx[HL]_X)
          \Tr (cq_block disXE x rhoXE \o P \o
               cq_block disXE x' rhoXE \o P)).
      rewrite raddf_sum /=.
      apply: eq_bigr => x _.
      by rewrite raddf_sum.
    rewrite HRe_eq HTr_eq HrhoE_eq.
    by [].
  (* Combine: LHS ≤ Hcoeff_le's RHS ≤ Hoffdiag_full's RHS = Hfull_trace's RHS. *)
  apply: (le_trans Hcoeff_le).
  apply: (le_trans Hoffdiag_full).
  by rewrite Hfull_trace.
Qed.
(* Tomamichel-Schaffner-Smith-Renner, 'Leftover Hashing Against Quantum   *)
(* Side Information' (IEEE Trans. IT 57:5524 (2011); arXiv:1002.2436),     *)
(* Lem. 5 — tex lemma:privacy-amp                                          *)
(* math: Γ_C(ρ_ZFE | ρ_F ⊗ τ_E) ≤ Γ_C(ρ_XE | τ_E)                       *)
(*        + δ·Tr(ρ_E τ_E^{-½} ρ_E τ_E^{-½}).                            *)
(* path: lhl:privacy_amp -> bb84:privacy_amplification -> *)
(*   bb84:bb84_secret *)
Lemma privacy_amp (rhoXE : 'F[HL]_S_XE) (tauE : 'F[HL]_E)
    (Fh : 'Idx[HL]_Fl -> 'Idx[HL]_X -> 'Idx[HL]_Zl)
    (delta : R) :
  rhoXE \is psdlf ->
  @complex.Re R (\Tr rhoXE) <= 1 ->
  tauE \is psdlf ->
  is_cq_state rhoXE ->
  0 <= delta ->
  delta_almost_two_univ Fh delta ->
  let rhoZFE := post_hash_state disXE Fh rhoXE in
  let rhoF_tauE := ((dim 'H[HL]_Fl)%:R^-1)%:C *: ((\1 : 'F_Fl) \O tauE) in
  let tau_inv_half := pinvlf (sqrtH tauE) in
  let rhoE := ptrace_castl disXE rhoXE in
  collision_ent rhoZFE rhoF_tauE <=
  collision_ent rhoXE tauE +
  delta * @complex.Re R (\Tr (
    rhoE \o tau_inv_half \o rhoE \o tau_inv_half)).
Proof.
  move=> Hrho Hrho_tr Htau Hcq Hdelta HFh.
  have HFh_dim : forall x x' : 'Idx[HL]_X, x != x' ->
    (#|[set f : 'Idx[HL]_Fl | Fh f x == Fh f x']|%:R /
    (dim 'H[HL]_Fl)%:R : R) <= delta.
  {
    move=> x x' Hxx.
    move: (HFh x x' Hxx).
    by rewrite /collision_probability idx_card.
  }
  have Hsplit := @Gamma_C_post_hash_split rhoXE tauE Fh Hrho Htau Hcq.
  have Hoffdiag := @Gamma_C_post_hash_offdiag_bound rhoXE tauE Fh delta
                     Hrho Htau Hcq Hdelta HFh_dim.
  apply: (le_trans Hsplit).
  by rewrite lerD2l.
Qed.
End PrivacyAmp.
(* thm:two-universal-hashing is in lhl/lhl.v (the single main result) *)
End FvqkdReal.
