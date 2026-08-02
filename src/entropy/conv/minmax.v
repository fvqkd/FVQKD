(* -------------------------------------------------------------------- *)
(* minmax.v — Alternate min/max expressions (Tomamichel thesis Sec. 4.2) *)
(* -------------------------------------------------------------------- *)
(* Module: entropy.conv.minmax                                *)
(* Source: Tomamichel, 'A Framework for Non-Asymptotic Quantum          *)
(*   Information Theory' (PhD thesis, arXiv:1203.2142), Sec. 4.2         *)
(*   (Min- and Max-Entropies); equations Eq. (4.6)–(4.7).               *)
(* -------------------------------------------------------------------- *)
(* Restate:                                               *)
(*   The TeX writes F = generalized fidelity (\fidb / gfid).    *)
(*   The thesis' clarifying remark (Sec. 4.2.1):                        *)
(*     We write F for the generalized fidelity, which corresponds to    *)
(*     the fidelity in this case as gamma is normalized.                *)
(*   So `F` numerically reduces to plain `fidelity` whenever the right  *)
(*   argument has trace 1 (gamma_ABp is den1 by gamma_state_den1, and  *)
(*   gamma_ABp \O tau is den1 by tenfXX-of-den1 since tau is den1lf).    *)
(*   The bridge lemma is `gfid_eq_fid_tr1_mx`           *)
(*   (utils/dist/fid.v:832).                                             *)
(*                                                                       *)
(* The checked statements below are the single Coq surfaces for Tomamichel's  *)
(* `min/koenig` and `min-omni` TeX lines. They are stated over ambient   *)
(* set-labelled systems; the proof uses product-coordinate matrix        *)
(* algebra only internally.                                              *)
(* -------------------------------------------------------------------- *)
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
From quantum.dirac Require Import hstensor setdec.
Import Order.TTheory GRing.Theory Num.Theory Num.Def MxLownerOrder.
Import VectorInternalTheory.
From utils Require Import exports.
From entropy Require Import def pre util.

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
(* Min-entropy omni expression                                        *)
(* Tomamichel thesis (arXiv:1203.2142), Eq. (4.7) — tex min-omni.     *)
(* math: H_min(A|B)[ρ] = -log d_A max_{B→B'B''} max_τ                  *)
(*   F^2(ρ_{AB'B''}, γ_{AB'} ⊗ τ_{B''})                                *)
(* where the maximization is over isometries B -> B'B'' and            *)
(* normalized states τ on B''.                                         *)
(* ================================================================== *)

Section MinOmni.
Variable (L : finType) (H : L -> chsType).
Variables (A B Bp Bpp : {set L}).
Hypothesis disAB : [disjoint A & B].
Hypothesis disABp : [disjoint A & Bp].
Hypothesis disABpp : [disjoint A & Bpp].
Hypothesis disBpBpp : [disjoint Bp & Bpp].
Hypothesis dimABp : dim 'H[H]_A = dim 'H[H]_Bp.
Hypothesis dimBpp_enough :
  (dim 'H[H]_B * dim 'H[H]_Bp <= dim 'H[H]_Bpp)%N.

Notation S_AB := (A :|: B).
Notation S_BpBpp := (Bp :|: Bpp).
Notation S_ABp := (A :|: Bp).
Notation S_ABpBpp := (A :|: Bp :|: Bpp).

Local Definition dimABp_set : dim 'H[H]_A = dim 'H[H]_Bp := dimABp.

Local Definition gamma_ABp : 'F[H]_S_ABp :=
  @gamma_state R L H A Bp dimABp_set.

Local Definition eqABpBpp : A :|: S_BpBpp = S_ABpBpp.
Proof.
  apply/setP=> x.
  by rewrite /S_BpBpp /S_ABpBpp !inE orbA.
Defined.

(* ================================================================== *)
(* Koenig bridge                                                        *)
(* Tomamichel thesis (arXiv:1203.2142), Eq. (4.6) — tex min/koenig.    *)
(* math: H_min(A|B)_rho = -log d_A max_E F^2(E[rho_AB], gamma_AB')      *)
(*   where F = generalized fidelity (gfid), reducing to        *)
(*   plain fidelity since gamma_AB' is normalized (gamma_state_den1).  *)
(* ================================================================== *)

(* path: entropy:min_koenig -> entropy:min_omni -> entropy:minmax_dual -> *)
(*   entropy:smooth_iso_hmax -> entropy:entropy_data_proc -> *)
(*   bb84:bb84_secret *)
Lemma min_koenig (rhoAB : 'F[H]_S_AB) :
  rhoAB \is denlf ->
  hminE B rhoAB =
  oppe (elog2
      ((dim 'H[H]_A)%:R *
       sup [set v : R |
         exists E : 'SO[H]_(B, Bp),
           [/\ E \is cptp &
               v =
               (gfid (((\:1 : 'SO[H]_A) :⊗ E) rhoAB)
                  gamma_ABp) ^+ 2]])).
Proof.
  move=> Hrho_den.
  have Prho : rhoAB \is psdlf := denlf_psd Hrho_den.
  have Hrho : @complex.Re R (\Tr rhoAB) <= 1.
  { have Hreal : \Tr rhoAB \is Num.real := ger0_real (psdlf_trlf Prho).
    by move: (denlf_trlf Hrho_den); rewrite -(RRe_real Hreal) lecR. }
  (* Bridge facts: gamma_ABp is den1 (trace 1, psdlf). When the proof
     produces equality with a `fidelity`-based set, the FV's
     `gfid` form is reached pointwise via
     `gfid_eq_fid_tr1_mx` (gamma_ABp on the right is den1).
     The terminal set-bridging step reduces to `Ecoh_g = Ecoh` via
     gfidelity_lf_sym + the matrix bridge + fid_i_sym_mx, applied
     pointwise per `E \is cptp`. *)
  have Hgamma_den1 : gamma_ABp \is den1lf :=
    @gamma_state_den1 R L H A Bp disABp dimABp_set.
  have Hgamma_psdlf : gamma_ABp \is psdlf := den1lf_psd Hgamma_den1.
  have Hgamma_tr1 : \Tr gamma_ABp = 1.
  { by move/den1lfP: Hgamma_den1 => [_ ->]. }
  have Hgamma_mx_psd : h2mx gamma_ABp \is psdmx by move: Hgamma_psdlf; rewrite qualifE.
  have Hgamma_mx_tr1 : \tr (h2mx gamma_ABp) = 1.
  { by move: Hgamma_tr1; rewrite /lftrace. }
  (* The `Ecoh` set — proof body operates on this; we use
     fidelity here and bridge to gfid at the closing step. *)
  pose Ecoh : set R := fun v : R =>
    exists E : 'SO[H]_(B, Bp),
      [/\ E \is cptp &
          v =
          (fidelity (((\:1 : 'SO[H]_A) :⊗ E) rhoAB)
             gamma_ABp) ^+ 2].
  have Hbridge :
      phi_min B rhoAB =
      (dim 'H[H]_A)%:R * sup Ecoh.
  {
    pose PhiSet : set R :=
      [set v : R | phi_min_feasible B rhoAB v]%classic.
    have Halpha_phi :
        phi_min B rhoAB = ExtNumTopology.etinf PhiSet.
    { by rewrite /phi_min /PhiSet /ExtNumTopology.etinf. }
    pose Psi_fun (sigmaB : 'F[H]_B) : 'F[H]_S_AB :=
      (\1 : 'F[H]_A) \O sigmaB.
    have HPsi_fun_linear : linear Psi_fun.
    { by move=> c sigma tau; rewrite /Psi_fun sdotfDr sdotfZr. }
    pose Psi_lfun : {linear 'F[H]_B -> 'F[H]_S_AB} :=
      HB.pack Psi_fun
        (GRing.isLinear.Build C _ _ *:%R _ HPsi_fun_linear).
    pose Psi : 'SO('H[H]_B, 'H[H]_S_AB) :=
      SOType (linfun Psi_lfun).
    pose SdpP : set R :=
      @sdp_primal_set R 'H[H]_B 'H[H]_S_AB
        (h2mx (\1 : 'F[H]_B)) (h2mx rhoAB) Psi.
    pose SdpD : set R :=
      @sdp_dual_set R 'H[H]_B 'H[H]_S_AB
        (h2mx (\1 : 'F[H]_B)) (h2mx rhoAB) Psi.
    have eqAB_diff : S_AB :\: B = A by exact: setDU_r.
    have eqAB_cond : S_AB :&: B = B by setdec.
    have eqAB_lift : (S_AB :\: B) :|: B = S_AB by rewrite eqAB_diff.
    have eqAB_lift_sig :
        (S_AB :\: B) :|: (S_AB :&: B) =
        (S_AB :\: B) :|: B by rewrite eqAB_cond.
    have eqAB_phi :
        (S_AB :\: B) :|: (S_AB :&: B) = S_AB
      by rewrite finset.setUC finset.setID.
    have eqBA : S_AB = (B :|: A) by setdec.
    have phi_lift_term (sigmaB : 'F[H]_B) :
        castlf (eqAB_phi, eqAB_phi)
          ((\1 : 'F[H]_(S_AB :\: B)) \O
            castlf (esym eqAB_cond, esym eqAB_cond) sigmaB) =
        (\1 : 'F[H]_A) \O sigmaB.
    { have -> : eqAB_phi = etrans eqAB_lift_sig eqAB_lift by apply: eq_irrelevance.
      rewrite -castlf_comp.
      rewrite (@sdotIf_cast_r R _ _ (S_AB :\: B)
        (S_AB :&: B) B
        eqAB_cond eqAB_lift_sig
        (castlf (esym eqAB_cond, esym eqAB_cond) sigmaB)).
      have -> :
          castlf (eqAB_cond, eqAB_cond)
            (castlf (esym eqAB_cond, esym eqAB_cond) sigmaB) = sigmaB
        by exact: castlfKV.
      rewrite (@sdotIf_cast_l R _ _ (S_AB :\: B) A B
        eqAB_diff eqAB_lift
        (\1 : 'F[H]_(S_AB :\: B)) sigmaB).
      have -> :
          castlf (eqAB_diff, eqAB_diff)
            (\1 : 'F[H]_(S_AB :\: B)) =
          (\1 : 'F[H]_A) by exact: castlf1.
      done. }
    have phi_lift_term_any
        (eqp : (S_AB :\: B) :|: (S_AB :&: B) = S_AB)
        (sigmaB : 'F[H]_B) :
        castlf (eqp, eqp)
          ((\1 : 'F[H]_(S_AB :\: B)) \O
            castlf (esym eqAB_cond, esym eqAB_cond) sigmaB) =
        (\1 : 'F[H]_A) \O sigmaB.
    { have -> : eqp = eqAB_phi by apply: eq_irrelevance.
      exact: phi_lift_term. }
    have phi_swap_term (sigmaB : 'F[H]_B) :
        castlf (esym eqBA, esym eqBA)
          (sigmaB \⊗ (\1 : 'F[H]_A)) =
        (\1 : 'F[H]_A) \O sigmaB.
    { apply: to_Fnd_inj.
      rewrite Fnd_cast (sdotFT _ _ disAB) !to_Fnd_tenE.
      by rewrite tenFC. }
    have Hphi_primal : PhiSet = SdpP.
    { (* Block 1: identify phi_min's feasible sigma_B with the primal SDP
         variable for Psi(sigma_B) = I_A tensor sigma_B. *)
      apply/funext=> v /=.
      apply/propext; split.
      - rewrite /PhiSet /SdpP /sdp_primal_set /=.
        move=> [sigma [Psigma [Hgap ->]]].
        pose sigmaB : 'F[H]_B :=
          castlf (eqAB_cond, eqAB_cond) sigma.
        exists (h2mx sigmaB).
        split.
        + have PsigmaB : sigmaB \is psdlf by rewrite /sigmaB castlf_psdlfE.
          by move: PsigmaB; rewrite qualifE.
        + have Hpsi_sigma :
              Psi (mx2h (h2mx sigmaB)) =
              (\1 : 'F[H]_A) \O sigmaB.
          { rewrite /Psi superopE lfunE /= /Psi_lfun /Psi_fun.
            by rewrite h2mxK. }
          rewrite Hpsi_sigma -lef_h2mx.
          have Hsigma_cast :
              sigma =
              castlf (esym eqAB_cond, esym eqAB_cond) sigmaB
            by rewrite /sigmaB castlfK.
          move: Hgap.
          rewrite Hsigma_cast (phi_lift_term_any _ sigmaB).
          move=> Hgap_psd.
          rewrite {1}/Order.le /= /lef_def.
          exact: Hgap_psd.
        + rewrite h2mx1 mul1mx.
          change (@complex.Re R (\Tr sigma) =
                  @complex.Re R (\Tr sigmaB)).
          by rewrite /sigmaB castlf_trlfE.
      - rewrite /PhiSet /SdpP /sdp_primal_set /=.
        move=> [X [PX HXfeas ->]].
        pose sigmaB : 'F[H]_B := mx2h X.
        pose sigma : 'F[H]_(S_AB :&: B) :=
          castlf (esym eqAB_cond, esym eqAB_cond) sigmaB.
        exists sigma.
        split.
        + by rewrite /sigma /sigmaB castlf_psdlfE qualifE mx2hK.
        + split.
          * rewrite /sigma (phi_lift_term_any _ sigmaB).
            have Hpsi_X : Psi (mx2h X) =
                (\1 : 'F[H]_A) \O sigmaB
              by rewrite /Psi superopE lfunE /= /Psi_lfun /Psi_fun /sigmaB.
            have Hmx :
                h2mx (((\1 : 'F[H]_A) \O sigmaB) - rhoAB) \is psdmx.
            { move: HXfeas.
              rewrite Hpsi_X le_lownerE.
              by rewrite raddfB. }
            rewrite qualifE.
            exact: Hmx.
          * rewrite h2mx1 mul1mx /sigma castlf_trlfE /sigmaB /lftrace mx2hK.
            done. }
    have Halpha_sdp :
        phi_min B rhoAB = ExtNumTopology.etinf SdpP
      by rewrite Halpha_phi Hphi_primal.
    have Hstrong_dual :
        ExtNumTopology.etinf SdpP = ExtNumTopology.etsup SdpD.
    { (* Block 2: apply strong primal SDP duality.  The strict dual
         witness is a small multiple of I_AB, using Psi^*(I_AB)=d_A I_B. *)
      have HA : h2mx (\1 : 'F[H]_B) \is hermmx.
      { apply: psdmx_herm.
        by rewrite h2mx1; exact: psdmx1. }
      have HB : h2mx rhoAB \is hermmx.
      { apply: psdmx_herm.
        by move: Prho; rewrite qualifE. }
      have HPsi_herm :
          forall X : 'M[C]_(dim 'H[H]_B),
            X \is hermmx -> h2mx (Psi (mx2h X)) \is hermmx.
      { move=> X HX.
        rewrite /Psi superopE lfunE /= /Psi_lfun /Psi_fun.
        have HX_lf : mx2h X \is hermlf.
        { apply/hermlfP.
          apply/h2mx_inj.
          rewrite h2mx_adj !mx2hK.
          by move/hermmxP: HX. }
        have Hten_lf :
            ((\1 : 'F[H]_A) \O mx2h X : 'F[H]_S_AB) \is hermlf.
        { apply/hermlfP.
          move/hermlfP: HX_lf => HX_adj.
          by rewrite sdot_I_adj HX_adj. }
        by move: Hten_lf; rewrite qualifE. }
      have Hhas_inf : has_inf SdpP.
      { split.
        - have disBA : [disjoint B & A] by rewrite disjoint_sym.
          pose rhoBA : 'F[H]_(B :|: A) :=
            castlf (eqBA, eqBA) rhoAB.
          have PrhoBA : rhoBA \is psdlf by rewrite /rhoBA castlf_psdlfE.
          pose sigmaB : 'F[H]_B :=
            (dim 'H[H]_A)%:R%:C *: ptrace_cast disBA rhoBA.
          pose domBA : 'F[H]_(B :|: A) :=
            sigmaB \⊗ (\1 : 'F[H]_A).
          exists (@complex.Re R (\tr (h2mx (\1 : 'F[H]_B) *m
                                      h2mx sigmaB))).
          rewrite /SdpP /sdp_primal_set /=.
          exists (h2mx sigmaB).
          split.
          + rewrite qualifE.
            rewrite /sigmaB h2mxZ_lf.
            apply: psdmxZ.
            * by rewrite lecR.
            * by move: (ptrace_cast_psdlf disBA PrhoBA); rewrite qualifE.
          + have Hop := @op_bound R L H B A disBA rhoBA PrhoBA.
            have Hop_psd :
                (domBA - rhoBA) \is psdlf.
            { have -> :
                  domBA =
                  (dim 'H[H]_A)%:R *:
                    (ptrace_cast disBA rhoBA \⊗ (\1 : 'F[H]_A)).
              { by rewrite /domBA /sigmaB -natrC tenfZl. }
              rewrite {1}/Order.le /= /lef_def in Hop.
              exact: Hop. }
            have Hop_psd' :
                (castlf (esym eqBA, esym eqBA)
                  (domBA - rhoBA)) \is psdlf.
            { exact: castlf_psdlf Hop_psd. }
            have Hdom :
                castlf (esym eqBA, esym eqBA) domBA =
                (\1 : 'F[H]_A) \O sigmaB.
            { by rewrite /domBA phi_swap_term. }
            have Hrho_cast :
                castlf (esym eqBA, esym eqBA) rhoBA = rhoAB.
            { by rewrite /rhoBA castlfK. }
            rewrite /Psi superopE lfunE /= /Psi_lfun /Psi_fun h2mxK.
            rewrite -lef_h2mx.
            move: Hop_psd'.
            rewrite castlf_sub Hdom Hrho_cast.
            move=> Hgap.
            rewrite lefE.
            exact: Hgap.
          + by rewrite h2mx1 mul1mx.
        - rewrite /has_lbound.
          exists 0.
          rewrite /lbound /SdpP /sdp_primal_set /=.
          move=> v [X [PX _ ->]].
          rewrite h2mx1 mul1mx.
          have Htr := psdmx_trace PX.
          move: Htr; rewrite lecE /= => /andP[_ Hre].
          exact: Hre. }
      have Halpha_refl :
          ExtNumTopology.etinf SdpP =
          ExtNumTopology.etinf (@sdp_primal_set R 'H[H]_B 'H[H]_S_AB
            (h2mx (\1 : 'F[H]_B)) (h2mx rhoAB) Psi)
        by [].
      have Hbeta_refl :
          ExtNumTopology.etsup SdpD =
          ExtNumTopology.etsup (@sdp_dual_set R 'H[H]_B 'H[H]_S_AB
            (h2mx (\1 : 'F[H]_B)) (h2mx rhoAB) Psi)
        by [].
      have Hslater :
          exists Y : 'M[C]_(dim 'H[H]_S_AB),
            Y \is pdmx /\
            (h2mx (\1 : 'F[H]_B) - h2mx (Psi^*o (mx2h Y))) \is pdmx.
      { have Hscalar_pdmx :
            forall n (a : R), 0 < a ->
              (a%:C *: 1%:M : 'M[C]_n) \is pdmx.
        { move=> n a Ha.
          apply/pdmxP; split.
          - apply/hermmxP/matrixP=> i j.
            rewrite !mxE.
            case Eij: (i == j).
            + move/eqP: Eij=> ->.
              rewrite eqxx !mulr1.
              change (a%:C = (a%:C)^*%C).
              by rewrite conjc_real.
            + have Eji : (j == i) = false by rewrite eq_sym Eij.
              rewrite Eji !mulr0.
              change ((0 : C) = (0 : C)^*%C).
              by rewrite conjc0.
          - apply/posmxP=> i j.
            by rewrite scalemx1 spectral_diag_scale mxE posrE ltc0R. }
        have HPsi_dual_ptrace :
            forall Y : 'F[H]_S_AB,
              Psi^*o Y = ptrace_castl disAB Y.
        { move=> Y.
          apply/eqP/trlf_intror=> X.
          rewrite -dualso_trlfEV.
          rewrite /Psi superopE lfunE /= /Psi_lfun /Psi_fun.
          by rewrite trlf_lift_partial. }
        pose dA_R : R := (dim 'H[H]_A)%:R.
        pose half_R : R := GRing.inv (2%:R : R).
        pose c_R : R := half_R * GRing.inv dA_R.
        have HdA_pos : 0 < dA_R by rewrite /dA_R ltr0n dim_proper.
        have HdA_neq0 : dA_R != 0 by rewrite gt_eqF.
        have Hhalf_pos : 0 < half_R by rewrite /half_R invr_gt0 ltr0n.
        have Hc_pos : 0 < c_R.
        { rewrite /c_R.
          apply: mulr_gt0 => //.
          by rewrite invr_gt0. }
        have Hc_d : c_R * dA_R = half_R
          by rewrite /c_R -mulrA mulVf ?mulr1.
        have Hhalf_sub : 1 - half_R = half_R.
        { have Hsplit : 1 = half_R + half_R
            by rewrite /half_R split21.
          by rewrite {1}Hsplit addrK. }
        pose Ylf : 'F[H]_S_AB := c_R%:C *: \1.
        exists (h2mx Ylf).
        split.
        - rewrite /Ylf h2mxZ_lf h2mx1.
          exact: Hscalar_pdmx Hc_pos.
        - have HPsiY :
              Psi^*o (mx2h (h2mx Ylf)) =
              half_R%:C *: (\1 : 'F[H]_B).
          { have HptrI :
                ptrace_castl disAB (\1 : 'F[H]_S_AB) =
                dA_R%:C *: (\1 : 'F[H]_B)
              by rewrite -sdotf11 ptrace_castl_sdot_I /dA_R.
            have HptrZ :
                ptrace_castl disAB Ylf =
                c_R%:C *: ptrace_castl disAB (\1 : 'F[H]_S_AB).
            { rewrite /Ylf /ptrace_castl /ptrace_cast_gen.
              rewrite [\Tr_(A) _]linearZ /=.
              by rewrite linearZ. }
            rewrite h2mxK HPsi_dual_ptrace HptrZ HptrI scalerA.
            by rewrite -realcM Hc_d. }
          rewrite HPsiY h2mxZ_lf h2mx1.
          have Hhalf_subC : 1 - half_R%:C = half_R%:C
            by rewrite -realcB Hhalf_sub.
          have Hdiff_eq :
              (1%:M : 'M[C]_(dim 'H[H]_B)) -
                half_R%:C *: 1%:M =
              half_R%:C *: 1%:M.
          { have Hright :
                half_R%:C *: (1%:M : 'M[C]_(dim 'H[H]_B)) =
                ((1 : C) - half_R%:C) *: 1%:M
              by rewrite Hhalf_subC.
            rewrite [X in _ = X]Hright.
            by rewrite scalerBl scale1r. }
          rewrite Hdiff_eq.
          exact: Hscalar_pdmx Hhalf_pos. }
      have [Hdual_eq _] :=
        @sdp_strong_primal R 'H[H]_B 'H[H]_S_AB
          (h2mx (\1 : 'F[H]_B)) (h2mx rhoAB) Psi
          (ExtNumTopology.etinf SdpP) (ExtNumTopology.etsup SdpD)
          HA HB HPsi_herm Hhas_inf Halpha_refl Hbeta_refl Hslater.
      exact: Hdual_eq. }
    have Hchoi_fidelity :
        ExtNumTopology.etsup SdpD =
        (dim 'H[H]_A)%:R * sup Ecoh.
    { (* Block 3: saturate the dual constraint X_B <= I_B to X_B = I_B,
         then read saturated dual points as Choi states of CP unital
         adjoints, equivalently TP-CPMs B -> B'. *)
      have Hgamma_rank1 : \Rank gamma_ABp = 1%N
        by exact: gamma_state_rank1.
      have Hgamma_proj1 : gamma_ABp \is proj1lf.
      { apply/proj1lf_rankP.
        split.
        - rewrite qualifE.
          apply/projmxP_id; split.
          + apply: psdmx_herm.
            by move: Hgamma_psdlf; rewrite qualifE.
          + have Hgamma_mx_den1 : h2mx gamma_ABp \is den1mx
              by move: Hgamma_den1; rewrite qualifE.
            have Hgamma_mx_rank : \rank (h2mx gamma_ABp) = 1%N
              by move: Hgamma_rank1; rewrite /lfrank.
            have [v Hv] := rank1_form Hgamma_mx_den1 Hgamma_mx_rank.
            rewrite Hv.
            have Hvv : v^*t *m v = 1%:M.
            { have /den1mxP [_ /eqP Htr1] := Hgamma_mx_den1.
              apply/matrixP=> i j.
              rewrite !ord1 !mxE.
              move: Htr1.
              by rewrite Hv mxtrace_mulC /mxtrace big_ord1 !mxE. }
            rewrite -[X in X = _](mulmxA v v^*t (v *m v^*t)).
            rewrite [v^*t *m (v *m v^*t)](mulmxA v^*t v v^*t).
            by rewrite Hvv mul1mx.
        - exact: Hgamma_rank1. }
      have Hsqrt_gamma : sqrtH gamma_ABp = gamma_ABp.
      { apply/h2mx_inj.
        rewrite sqrtH_h2mx.
        have Hgamma_mx_proj : h2mx gamma_ABp \is projmx
          by move: (proj1lf_proj Hgamma_proj1); rewrite qualifE.
        have /projmxP_id [_ Hgamma_idem] := Hgamma_mx_proj.
        have Hsqrt_square := sqrtmx_psd_square Hgamma_mx_psd.
        rewrite Hgamma_idem in Hsqrt_square.
        exact: Hsqrt_square. }
      have HPsi_dual_ptrace :
          forall Y : 'F[H]_S_AB,
            Psi^*o Y = ptrace_castl disAB Y.
      { move=> Y.
        apply/eqP/trlf_intror=> X.
        rewrite -dualso_trlfEV.
        rewrite /Psi superopE lfunE /= /Psi_lfun /Psi_fun.
        by rewrite trlf_lift_partial. }
      pose Dineq : set R := fun v : R =>
        exists Y : 'F[H]_S_AB,
          [/\ Y \is psdlf,
              ptrace_castl disAB Y <= (\1 : 'F[H]_B) &
              v = @complex.Re R (\Tr (rhoAB \o Y))].
      have Hdual_ineq : SdpD = Dineq.
      { apply/funext=> v /=.
        apply/propext; split.
        - rewrite /SdpD /Dineq /sdp_dual_set /=.
          move=> [Y [PY HY ->]].
          exists (mx2h Y).
          split.
          + by rewrite qualifE mx2hK.
          + rewrite lef_h2mx h2mx1.
            move: HY.
            rewrite h2mx1.
            move=> HYmx.
            have HptrY := congr1 h2mx (HPsi_dual_ptrace (mx2h Y)).
            move: HptrY.
            move=> <-.
            exact: HYmx.
          + by rewrite /lftrace h2mx_comp mx2hK.
        - rewrite /SdpD /Dineq /sdp_dual_set /=.
          move=> [Y [PY HY ->]].
          exists (h2mx Y).
          split.
          + by move: PY; rewrite qualifE.
          + move: HY.
            rewrite lef_h2mx h2mx1.
            have HptrY := congr1 h2mx (HPsi_dual_ptrace Y).
            rewrite h2mxK.
            move=> HYmx.
            move: HptrY.
            move=> ->.
            exact: HYmx.
          + by rewrite /lftrace h2mx_comp. }
      pose Dsat : set R := fun v : R =>
        exists Y : 'F[H]_S_AB,
          [/\ Y \is psdlf,
              ptrace_castl disAB Y = (\1 : 'F[H]_B) &
              v = @complex.Re R (\Tr (rhoAB \o Y))].
      have Hsat_dominates :
          forall v, Dineq v -> exists w, Dsat w /\ v <= w.
      { move=> v [Y [PY HY ->]].
        pose dA_R : R := (dim 'H[H]_A)%:R.
        pose gapB : 'F[H]_B :=
          (\1 : 'F[H]_B) - ptrace_castl disAB Y.
        pose padY : 'F[H]_S_AB :=
          (dA_R^-1)%:C *: ((\1 : 'F[H]_A) \O gapB).
        pose Ysat : 'F[H]_S_AB := Y + padY.
        have Hgap_psd : gapB \is psdlf.
        { rewrite /gapB.
          by move: HY; rewrite lefE. }
        have Hlift_gap_psd :
            ((\1 : 'F[H]_A) \O gapB : 'F[H]_S_AB) \is psdlf.
        { have -> :
              ((\1 : 'F[H]_A) \O gapB : 'F[H]_S_AB) =
              (\1 : 'F[H]_A) \⊗ gapB.
          { apply: to_Fnd_inj.
            by rewrite (sdotFT _ _ disAB) to_Fnd_tenE. }
          rewrite psdlfE.
          apply: tenf_ge0; first exact: disAB.
          - exact: lef01.
          - by rewrite -psdlfE. }
        have Hpad_psd : padY \is psdlf.
        { rewrite /padY.
          apply: psdlfZ.
          - by rewrite lecR invr_ge0.
          - exact: Hlift_gap_psd. }
        exists (@complex.Re R (\Tr (rhoAB \o Ysat))).
        split.
        - exists Ysat.
          split.
          + by apply: psdlfD.
          + have Hptr_pad : ptrace_castl disAB padY = gapB.
            { rewrite /padY.
              have -> :
                  ptrace_castl disAB
                    ((dA_R^-1)%:C *:
                      ((\1 : 'F[H]_A) \O gapB : 'F[H]_S_AB)) =
                  (dA_R^-1)%:C *:
                    ptrace_castl disAB
                      ((\1 : 'F[H]_A) \O gapB : 'F[H]_S_AB).
              { rewrite /ptrace_castl /ptrace_cast_gen.
                rewrite [\Tr_(A) _]linearZ /=.
                by rewrite linearZ. }
              rewrite ptrace_castl_sdot_I /dA_R.
              rewrite scalerA -realcM.
              have HdA_neq0 : dA_R != 0
                by rewrite /dA_R pnatr_eq0 -lt0n dim_proper.
              by rewrite mulVf ?scale1r. }
            have -> :
                ptrace_castl disAB Ysat =
                ptrace_castl disAB Y + ptrace_castl disAB padY.
            { rewrite /Ysat /ptrace_castl /ptrace_cast_gen.
              rewrite [\Tr_(A) _]raddfD /=.
              by rewrite raddfD. }
            rewrite Hptr_pad /gapB.
            by rewrite addrC subrK.
          + done.
        - have Htr_pad := psdlf_TrM Prho Hpad_psd.
          have Hre_pad :
              0 <= @complex.Re R (\Tr (rhoAB \o padY))
            by move: Htr_pad; rewrite lecE /= => /andP[_].
          have -> : rhoAB \o Ysat = (rhoAB \o Y) + (rhoAB \o padY).
          { rewrite /Ysat.
            apply/h2mx_inj.
            rewrite !h2mx_comp.
            rewrite [h2mx (Y + padY)]raddfD /=.
            rewrite [h2mx ((rhoAB \o Y) + (rhoAB \o padY))]raddfD /=.
            by rewrite !h2mx_comp mulmxDr. }
          rewrite linearD /= raddfD /=.
          by rewrite lerDl. }
      have Hsat_subset : forall v, Dsat v -> Dineq v.
      { move=> v [Y [PY HY ->]].
        exists Y.
        split=> //.
        by rewrite HY. }
      have psdlf_le_tr_id_local :
          forall (S0 : {set L}) (f : 'F[H]_S0),
            f \is psdlf ->
            f <= (@complex.Re R (\Tr f))%:C *: (\1 : 'F[H]_S0).
      { move=> S0 f Pf.
        have Htr_real : \Tr f \is Num.real := ger0_real (psdlf_trlf Pf).
        rewrite lef_h2mx.
        have -> :
            h2mx ((@complex.Re R (\Tr f))%:C *: (\1 : 'F[H]_S0)) =
            (\tr (h2mx f))%:M.
        { rewrite h2mxZ_lf h2mx1 /lftrace (RRe_real Htr_real) scalemx1.
          done. }
        apply: lemx_psd_ub.
        by rewrite qualifE. }
      have Hrho_le_I : rhoAB <= (\1 : 'F[H]_S_AB).
      { have Hrho_le_trI := psdlf_le_tr_id_local S_AB rhoAB Prho.
        have HtrI_le_I :
            (@complex.Re R (\Tr rhoAB))%:C *: (\1 : 'F[H]_S_AB) <=
            (\1 : 'F[H]_S_AB).
        { rewrite lefE.
          have -> :
              (\1 : 'F[H]_S_AB) -
                (@complex.Re R (\Tr rhoAB))%:C *: (\1 : 'F[H]_S_AB) =
              (1 - @complex.Re R (\Tr rhoAB))%:C *:
                (\1 : 'F[H]_S_AB)
            by rewrite realcB scalerBl scale1r.
          apply: psdlfZ.
          - by rewrite lecR subr_ge0.
          - by rewrite qualifE h2mx1; exact: psdmx1. }
        exact: (le_trans Hrho_le_trI HtrI_le_I). }
      have HDineq_upper :
          forall v, Dineq v -> v <= (dim 'H[H]_B)%:R.
      { move=> v [Y [PY HY ->]].
        have HrhoY_le : \Tr (rhoAB \o Y) <= \Tr ((\1 : 'F[H]_S_AB) \o Y).
        { move/lef_psdtr: Hrho_le_I => /(_ Y PY).
          exact. }
        have HtrY_le_dimB :
            @complex.Re R (\Tr Y) <= (dim 'H[H]_B)%:R.
        { have Hptr_tr_le := lef_trlf HY.
          move: Hptr_tr_le.
          rewrite (trlf_ptrace_castl disAB Y).
          rewrite /lftrace h2mx1 mxtrace1.
          rewrite lecE /= => /andP[_ Hre].
          by move: Hre; rewrite -natrC re_realid. }
        move: HrhoY_le.
        rewrite comp_lfun1l.
        rewrite lecE /= => /andP[_ Hre].
        exact: le_trans Hre HtrY_le_dimB. }
      have HDineq_nonempty : nonempty Dineq.
      { exists 0.
        exists (0 : 'F[H]_S_AB).
        split.
        - by rewrite qualifE h2mx0; exact: psdmx0.
        - have Hptr0 :
              ptrace_castl disAB (0 : 'F[H]_S_AB) = (0 : 'F[H]_B).
          { rewrite /ptrace_castl /ptrace_cast_gen linear0 /=.
            by apply/eqP; rewrite castlf_eq0 eqxx. }
          by rewrite Hptr0; exact: lef01.
        - by rewrite comp_lfun0r linear0 raddf0. }
      have HDineq_has_sup : has_sup Dineq.
      { split.
        - exact: HDineq_nonempty.
        - exists (dim 'H[H]_B)%:R.
          exact: HDineq_upper. }
      have HDsat_has_sup : has_sup Dsat.
      { split.
        - case: HDineq_nonempty => v Hv.
          have [w [Hw _]] := Hsat_dominates v Hv.
          by exists w.
        - exists (dim 'H[H]_B)%:R => v Hv.
          exact: HDineq_upper (Hsat_subset v Hv). }
      have Hsup_Dineq_Dsat :
          ExtNumTopology.etsup Dineq = ExtNumTopology.etsup Dsat.
      { apply/eqP.
        rewrite eq_le.
        apply/andP; split.
        - apply: ExtNumTopology.etsup_least_ubound.
          + exact: HDineq_has_sup.
          + move=> v Hv.
            have [w [Hw Hvw]] := Hsat_dominates v Hv.
            exact (le_trans Hvw
              (ExtNumTopology.etsup_upper_bound HDsat_has_sup Hw)).
        - apply: ExtNumTopology.etsup_least_ubound.
          + exact: HDsat_has_sup.
          + move=> v Hv.
            exact (ExtNumTopology.etsup_upper_bound
              HDineq_has_sup (Hsat_subset v Hv)). }
      (* Block 4: gamma_AB' is pure and normalized, so the dual pairing is
         d_A times F^2((id_A tensor E)(rho_AB), gamma_AB'). *)
      have Hsat_choi_fidelity :
          ExtNumTopology.etsup Dsat =
          (dim 'H[H]_A)%:R * sup Ecoh.
      { pose dA_R : R := (dim 'H[H]_A)%:R.
        pose Escaled : set R := fun v : R =>
          exists w : R, Ecoh w /\ v = dA_R * w.
        have Hgamma_fidelity :
            forall sigmaABp : 'F[H]_S_ABp,
              sigmaABp \is psdlf ->
              (fidelity sigmaABp gamma_ABp) ^+ 2 =
              @complex.Re R (\Tr (sigmaABp \o gamma_ABp)).
        { (* Pure-state block: gamma_AB' is normalized rank one, so
             F(sigma,gamma)^2 is the gamma expectation of sigma. *)
          move=> sigmaABp Psigma.
          pose r : R :=
            @complex.Re R (\Tr (sigmaABp \o gamma_ABp)).
          have Hr_ge0 : 0 <= r.
          { have Htr_ge0 : 0 <= \Tr (sigmaABp \o gamma_ABp)
              by exact: psdlf_TrM.
            by move: Htr_ge0; rewrite lecE /= => /andP[_]. }
          have Hgamma_sandwich :
              gamma_ABp \o sigmaABp \o gamma_ABp =
              r%:C *: gamma_ABp.
          { (* Rank-one sandwich: |gamma><gamma| sigma |gamma><gamma|
               equals the gamma expectation of sigma times gamma. *)
            apply/h2mx_inj.
            rewrite !h2mx_comp h2mxZ_lf.
            have Htr_ge0 : 0 <= \Tr (sigmaABp \o gamma_ABp)
              by exact: psdlf_TrM.
            have Htr_real :
                \Tr (sigmaABp \o gamma_ABp) \is Num.real :=
              ger0_real Htr_ge0.
            have HrC : r%:C = \Tr (sigmaABp \o gamma_ABp)
              by rewrite /r RRe_real.
            rewrite HrC /lftrace h2mx_comp.
            pose P := h2mx gamma_ABp.
            pose X := h2mx sigmaABp.
            have Hgamma_mx_den1 : P \is den1mx
              by rewrite /P; move: Hgamma_den1; rewrite qualifE.
            have Hgamma_mx_rank : \rank P = 1%N
              by rewrite /P; move: Hgamma_rank1; rewrite /lfrank.
            have [v Hv] := rank1_form Hgamma_mx_den1 Hgamma_mx_rank.
            have Hvv : v^*t *m v = 1%:M.
            { have /den1mxP [_ /eqP Htr1] := Hgamma_mx_den1.
              apply/matrixP=> i j.
              rewrite !ord1 !mxE.
              move: Htr1.
              by rewrite Hv mxtrace_mulC /mxtrace big_ord1 !mxE. }
            have Hmx1 (M : 'M[C]_1) : M = (\tr M)%:M.
            { apply/matrixP=> i j.
              by rewrite !ord1 /mxtrace big_ord1 mxE. }
            have Htr_cyc :
                \tr (v^*t *m X *m v) = \tr (X *m v *m v^*t)
              by rewrite -mulmxA mxtrace_mulC.
            have HP_unfold :
                ((dim 'H[H]_A)%:R^-1)%:C *:
                  h2mx (@max_entangled R L H A Bp dimABp_set) = P
              by rewrite /P /gamma_ABp /gamma_state h2mxZ_lf.
            rewrite h2mxZ_lf HP_unfold -/P -/X Hv.
            transitivity (v *m ((v^*t *m X *m v) *m v^*t)).
            { by rewrite !mulmxA. }
            rewrite (Hmx1 (v^*t *m X *m v)).
            rewrite mul_scalar_mx -scalemxAr Htr_cyc -mulmxA.
            by []. }
          have Hfid_project :
              fidelity sigmaABp gamma_ABp =
              fidelity (gamma_ABp \o sigmaABp \o gamma_ABp) gamma_ABp.
          { (* Project both arguments onto the one-dimensional support of
               gamma_AB' using tb:fid item (iv). *)
            have Hgamma_mx_proj : h2mx gamma_ABp \is projmx
              by move: (proj1lf_proj Hgamma_proj1); rewrite qualifE.
            have Hsigma_mx_psd : h2mx sigmaABp \is psdmx
              by move: Psigma; rewrite qualifE.
            have Hgamma_mx_psd2 : h2mx gamma_ABp \is psdmx
              by move: Hgamma_psdlf; rewrite qualifE.
            have /projmxP_id [_ Hgamma_idem] := Hgamma_mx_proj.
            have [Hleft Hright] :=
              fid_iv_proj_mx
                (P := h2mx gamma_ABp)
                (rho := h2mx sigmaABp)
                (tau := h2mx gamma_ABp)
                Hgamma_mx_proj Hsigma_mx_psd Hgamma_mx_psd2.
            have HrhoP :
                h2mx (gamma_ABp \o sigmaABp \o gamma_ABp) =
                h2mx gamma_ABp *m h2mx sigmaABp *m h2mx gamma_ABp
              by rewrite !h2mx_comp.
            have HtauP :
                h2mx gamma_ABp *m h2mx gamma_ABp *m h2mx gamma_ABp =
                h2mx gamma_ABp
              by rewrite Hgamma_idem.
            rewrite /fidelity !h2mx_comp !sqrtH_h2mx.
            symmetry.
            move: Hright.
            by rewrite HtauP -HrhoP. }
          have Hfid_scaled :
              fidelity (r%:C *: gamma_ABp) gamma_ABp = Num.sqrt r.
          { (* The only surviving operator is sqrt(r) * gamma_AB'. *)
            rewrite /fidelity !h2mx_comp !sqrtH_h2mx h2mxZ_lf.
            have Hgamma_mx_psd2 : h2mx gamma_ABp \is psdmx
              by move: Hgamma_psdlf; rewrite qualifE.
            have Hsqrt_gamma_mx :
                sqrtmx (h2mx gamma_ABp) = h2mx gamma_ABp
              by rewrite -sqrtH_h2mx Hsqrt_gamma.
            rewrite (sqrtmxZ_nn Hr_ge0 Hgamma_mx_psd2) Hsqrt_gamma_mx.
            have Hgamma_mx_proj : h2mx gamma_ABp \is projmx
              by move: (proj1lf_proj Hgamma_proj1); rewrite qualifE.
            have /projmxP_id [_ Hgamma_idem] := Hgamma_mx_proj.
            rewrite -scalemxAl Hgamma_idem.
            rewrite trnormZ.
            have Htrnorm_gamma : trnorm (h2mx gamma_ABp) = 1
              by rewrite (psdmx_trnorm Hgamma_mx_psd2)
                -/(\Tr gamma_ABp) (proj1lf_trlf Hgamma_proj1).
            rewrite Htrnorm_gamma mulr1.
            have Habs :
                `|((Num.sqrt r)%:C : C)| = (Num.sqrt r)%:C
              by rewrite normc_def /= expr0n /= addr0 sqrtr_sqr
                ger0_norm ?sqrtr_ge0.
            by rewrite Habs. }
          rewrite Hfid_project Hgamma_sandwich Hfid_scaled.
          by rewrite sqr_sqrtr. }
        (* Hgamma_left — partial trace over A of gamma_AB' = (1/d_A) I_B'.
           Shared infrastructure used by both directions of the Choi
           block (Hsat_to_scaled / Hscaled_to_sat). *)
        have Hgamma_left :
            ptrace_castl disABp gamma_ABp =
            (dA_R^-1)%:C *: (\1 : 'F[H]_Bp).
        { have disBpA : [disjoint Bp & A]
            by rewrite disjoint_sym.
          pose eqBpA_to_ABp : Bp :|: A = S_ABp :=
            finset.setUC Bp A.
          pose gamma_BpA : 'F[H]_(Bp :|: A) :=
            @gamma_state R L H Bp A (esym dimABp_set).
          have Hptr_swap :
              ptrace_castl disABp
                (castlf (eqBpA_to_ABp, eqBpA_to_ABp) gamma_BpA) =
              ptrace_cast disBpA gamma_BpA.
          { rewrite /ptrace_castl /ptrace_cast /ptrace_cast_gen.
            pose eqDU :
                (Bp :|: A) :\: A =
                S_ABp :\: A :=
              congr1 (fun S : {set L} => S :\: A)
                eqBpA_to_ABp.
            have Hptr_cast :
                \Tr_(A)
                  (castlf (eqBpA_to_ABp, eqBpA_to_ABp) gamma_BpA) =
                castlf (eqDU, eqDU) (\Tr_(A) gamma_BpA).
            { case: S_ABp / eqBpA_to_ABp eqDU.
              move=> eqDU0.
              rewrite (eq_irrelevance eqDU0 (erefl _)).
              by rewrite castlf_id. }
            rewrite Hptr_cast castlf_comp.
            have -> :
                etrans eqDU (setDU_l disABp) = setDU_r disBpA
              by apply: eq_irrelevance.
            done. }
          have Hgamma_swap :
              castlf (eqBpA_to_ABp, eqBpA_to_ABp) gamma_BpA = gamma_ABp.
          { rewrite /gamma_BpA /gamma_ABp /gamma_state.
            rewrite linearZ /=.
            have Hdim_BpA :
                dim 'H[H]_Bp = dim 'H[H]_A.
            { exact: esym dimABp_set. }
            have Hscale_BpA :
                (((dim 'H[H]_Bp)%:R^-1)%:C : C) =
                (((dim 'H[H]_A)%:R^-1)%:C : C)
              by rewrite Hdim_BpA.
            rewrite Hscale_BpA.
            congr (_ *: _).
            rewrite /max_entangled /purification castlf_outp.
            have Hvec :
                casths eqBpA_to_ABp (pur.pur_vec (esym dimABp_set) \1) =
                pur.pur_vec dimABp_set \1.
            { rewrite /pur.pur_vec !sqrtH1.
              rewrite linear_sum /=.
              have hcast_bij :
                  {on [pred x | true],
                    bijective (cast_ord (pur.dim_HA_HB dimABp_set))}.
              { exists (cast_ord (pur.dim_HA_HB (esym dimABp_set))).
                - move=> k _.
                  by apply/val_inj.
                - move=> k _.
                  by apply/val_inj. }
              rewrite (reindex (cast_ord (pur.dim_HA_HB dimABp_set))
                hcast_bij) /=.
              apply: eq_bigr=> i _.
              have HcastK :
                  cast_ord (pur.dim_HA_HB (esym dimABp_set))
                    (cast_ord (pur.dim_HA_HB dimABp_set) i) = i
                by apply/val_inj.
              by rewrite !lfunE tenv_castC HcastK. }
            by rewrite Hvec. }
          rewrite -Hgamma_swap Hptr_swap.
          rewrite /gamma_BpA gamma_state_ptrace.
          congr (_ *: _).
          have Hdim_BpA :
              dim 'H[H]_Bp = dim 'H[H]_A.
          { exact: esym dimABp_set. }
          by rewrite /dA_R Hdim_BpA. }
        have Hsat_to_scaled : forall v, Dsat v -> Escaled v.
        { (* Choi block, forward direction: read a saturated dual variable
             as the Choi state of a CP-unital adjoint. *)
          move=> v [Y [PY HptrY ->]].
          have Hdim_ABp_set :
              dim 'H[H]_A = dim 'H[H]_Bp.
          { exact: dimABp_set. }
          pose Hdim_choi :
              dim 'H[H]_A * dim 'H[H]_B =
              dim 'H[H]_Bp * dim 'H[H]_B :=
            congr1 (fun n => n * dim 'H[H]_B) Hdim_ABp_set.
          pose UAB := @tenv_mxU R L H A B.
          pose MAB : 'M[C]_(dim 'H[H]_A * dim 'H[H]_B) :=
            UAB^*t *m h2mx Y *m UAB.
          pose M : 'M[C]_(dim 'H[H]_Bp * dim 'H[H]_B) :=
            castmx (Hdim_choi, Hdim_choi) MAB.
          pose D : 'SO[H]_(Bp, B) := choi2so M.
          have HDcp : D \is cpmap.
          { (* Positivity of Y is positivity of its Choi matrix after
               tensor-coordinate conjugation and the A=B' dimension cast. *)
            apply/cpmapP.
            rewrite /D choi2soK /M.
            apply: castmx_sq_psdmx.
            rewrite /MAB.
            have PYmx : h2mx Y \is psdmx
              by move: PY; rewrite qualifE.
            have HpsdMAB :=
              @psdmx_bimap_closed_gen C (dim 'H[H]_S_AB) (h2mx Y)
                (dim 'H[H]_A * dim 'H[H]_B) UAB^*t PYmx.
            by move: HpsdMAB; rewrite adjmxK. }
          have Hrealize :
              Y =
              dA_R%:C *:
                (((\:1 : 'SO[H]_A) :⊗ D) gamma_ABp).
          { (* Choi realization: the inverse map built from Y has Y as
               its unnormalized Choi state. *)
            apply/h2mx_inj.
            rewrite h2mxZ_lf /gamma_ABp /gamma_state.
            have HsoZ :
                (((\:1 : 'SO[H]_A) :⊗ D)
                  (((dim 'H[H]_A)%:R^-1)%:C *:
                    @max_entangled R L H A Bp dimABp_set)) =
                ((dim 'H[H]_A)%:R^-1)%:C *:
                  (((\:1 : 'SO[H]_A) :⊗ D)
                    (@max_entangled R L H A Bp dimABp_set)).
            { exact: linearZ. }
            rewrite HsoZ h2mxZ_lf scalerA -realcM.
            have HdA_neq0 : dA_R != 0
              by rewrite /dA_R pnatr_eq0 -lt0n dim_proper.
            rewrite mulfV ?scale1r //.
            have HUAB : UAB \is unitarymx
              by exact: tenv_mxU_unitarymx.
            have HYMAB :
                h2mx Y = UAB *m MAB *m UAB^*t.
            { rewrite -[h2mx Y]mul1mx -(unitarymxK HUAB).
              rewrite -[(UAB *m UAB^*t *m h2mx Y)]mulmx1.
              rewrite -(unitarymxK HUAB).
              by rewrite /MAB !mulmxA. }
            rewrite HYMAB.
            have HmaxMAB :
                h2mx
                  (((\:1 : 'SO[H]_A) :⊗ D)
                    (@max_entangled R L H A Bp dimABp_set)) =
                UAB *m MAB *m UAB^*t.
            { (* Matrix Choi identity in tensor coordinates. *)
              have Hmax_so2choi :
                  h2mx
                    (((\:1 : 'SO[H]_A) :⊗ D)
                      (@max_entangled R L H A Bp dimABp_set)) =
                  UAB *m
                    castmx (esym Hdim_choi, esym Hdim_choi)
                      (so2choi D) *m UAB^*t.
              { have Hmax_expand :
                    @max_entangled R L H A Bp dimABp_set =
                    \sum_i \sum_j
                      ((delta_lf i j : 'F[H]_A) \⊗
                       (delta_lf (cast_ord Hdim_ABp_set i)
                          (cast_ord Hdim_ABp_set j) : 'F[H]_Bp)).
                { (* Expand |gamma><gamma| as the double sum of tensor
                     matrix units in the A,B' tensor coordinates. *)
                  apply/h2mx_inj.
                  rewrite /max_entangled /purification outp.unlock mx2hK.
                  pose UABp := @tenv_mxU R L H A Bp.
                  pose V : 'cV[C]_(dim 'H[H]_A *
                                    dim 'H[H]_Bp) :=
                    \sum_i
                      ((h2mx (sqrtH (\1 : 'F[H]_A)) *m
                          delta_mx i (0 : 'I_1)) *t
                       (delta_mx (cast_ord Hdim_ABp_set i) (0 : 'I_1)
                          : 'cV_(dim 'H[H]_Bp))).
                  have tens_cv_entry (dA dB : nat) (X : 'M[C]_(dA, 1))
                      (Yv : 'cV[C]_dB) (r : 'I_dA) (s : 'I_dB) :
                      (X *t Yv) (mxtens_index (r, s)) 0 =
                      X r 0 * Yv s 0.
                  { rewrite mxE mxtens_indexK /=.
                    by apply: f_equal2; congr (_ _ _); apply/val_inj. }
                  have Hpv :
                      h2c (pur.pur_vec dimABp_set \1) = UABp *m V.
                  { rewrite /pur.pur_vec raddf_sum /= /V mulmx_sumr.
                    apply: eq_bigr=> i _.
                    rewrite tenv_h2cE.
                    have Hleft :
                        h2c ((sqrtH (\1 : 'F[H]_A)) (eb i)) =
                        h2mx (sqrtH (\1 : 'F[H]_A)) *m
                          delta_mx i (0 : 'I_1).
                    { rewrite applyfh c2hK.
                      by rewrite h2c_eb. }
                    rewrite Hleft.
                    by rewrite h2c_eb. }
                  have Ventry :
                      forall (a : 'I_(dim 'H[H]_A))
                             (b : 'I_(dim 'H[H]_Bp)),
                        V (mxtens_index (a, b)) 0 =
                        (b == cast_ord Hdim_ABp_set a)%:R.
                  { move=> a b.
                    rewrite /V summxE.
                    rewrite (bigD1 a)//= [X in _ + X]big1.
                    - rewrite addr0 sqrtH1 h2mx1 mul1mx tens_cv_entry.
                      rewrite !mxE !eqxx /= mul1r.
                      by rewrite andbT.
                    - move=> i /negPf nia.
                      rewrite sqrtH1 h2mx1 mul1mx tens_cv_entry !mxE.
                      rewrite eq_sym nia.
                      by rewrite mul0r. }
                  have Houter :
                      V *m V^*t =
                      \sum_i \sum_j
                        (delta_mx i j *t
                         delta_mx (cast_ord Hdim_ABp_set i)
                           (cast_ord Hdim_ABp_set j)).
                  { apply/matrix_tenP=> a b c d.
                    rewrite mxE big_ord1 mxE_adj Ventry Ventry.
                    rewrite summxE.
                    rewrite (bigD1 a)//= [X in _ + X]big1.
                    2: { move=> i /negPf nia.
                      rewrite summxE big1 // => j _.
                      by rewrite tensmxE !mxE eq_sym nia mul0r. }
                    rewrite addr0 summxE.
                    rewrite (bigD1 c)//= [X in _ + X]big1.
                    2: { move=> j /negPf njc.
                      by rewrite tensmxE !mxE eq_sym njc andbF mul0r. }
                    rewrite addr0 !tensmxE !mxE !eqxx /= !mul1r.
                    rewrite conjC_nat.
                    by case: (b == cast_ord Hdim_ABp_set a);
                      case: (d == cast_ord Hdim_ABp_set c);
                      rewrite ?mul0r ?mul1r. }
                  rewrite Hpv adjmxM -mulmxA.
                  rewrite [V *m (V^*t *m UABp^*t)]mulmxA Houter.
                  rewrite !raddf_sum /=.
                  under [RHS]eq_bigr => i _ do rewrite raddf_sum /=.
                  under [RHS]eq_bigr => i _ do under eq_bigr => j _ do
                    rewrite h2mx_tenf !delta_lfE !mx2hK.
                  rewrite -/UABp.
                  rewrite mulmx_suml mulmx_sumr.
                  under [LHS]eq_bigr => i _ do
                    rewrite mulmx_suml mulmx_sumr.
                  apply: eq_bigr=> i _.
                  apply: eq_bigr=> j _.
                  by rewrite mulmxA. }
                have Hcast_prod :
                    forall (a : 'I_(dim 'H[H]_A))
                           (b : 'I_(dim 'H[H]_B)),
                      cast_ord Hdim_choi (mxtens_index (a, b)) =
                      mxtens_index (cast_ord Hdim_ABp_set a, b)
                  by move=> a b; apply/val_inj.
                have Hmiddle :
                    \sum_i \sum_j
                      (delta_mx i j *t
                        h2mx (D (delta_lf (cast_ord Hdim_ABp_set i)
                          (cast_ord Hdim_ABp_set j)))) =
                    castmx (esym Hdim_choi, esym Hdim_choi) (so2choi D).
                { apply/matrix_tenP=> a b c d.
                  rewrite castmxE /= !esymK Hcast_prod Hcast_prod.
                  rewrite so2choi.unlock !summxE.
                  rewrite (bigD1 a)//= [X in _ + X]big1.
                  2: { move=> i /negPf nia.
                    rewrite summxE big1 // => j _.
                    by rewrite tensmxE !mxE eq_sym nia mul0r. }
                  rewrite addr0 summxE (bigD1 c)//= [X in _ + X]big1.
                  2: { move=> j /negPf njc.
                    by rewrite tensmxE !mxE eq_sym njc andbF mul0r. }
                  rewrite addr0 !tensmxE !mxE !eqxx /= !mul1r.
                  rewrite (bigD1 (cast_ord Hdim_ABp_set a))//=.
                  rewrite [X in _ + X]big1.
                  2: { move=> p /negPf npa.
                    rewrite summxE big1 // => q _.
                    by rewrite tensmxE !mxE eq_sym npa mul0r. }
                  rewrite addr0 summxE.
                  rewrite (bigD1 (cast_ord Hdim_ABp_set c))//=.
                  rewrite [X in _ + X]big1.
                  2: { move=> q /negPf nqc.
                    by rewrite tensmxE !mxE eq_sym nqc andbF mul0r. }
                  by rewrite addr0 !tensmxE !mxE !eqxx /= !mul1r. }
                rewrite Hmax_expand raddf_sum /= raddf_sum /=.
                under eq_bigr => i _ do rewrite raddf_sum /= raddf_sum /=.
                under eq_bigr => i _ do under eq_bigr => j _ do
                  rewrite -(@tenso_correct R L H
                    A A Bp B
                    (\:1 : 'SO[H]_A) D disABp
                    (delta_lf i j : 'F[H]_A)
                    (delta_lf (cast_ord Hdim_ABp_set i)
                       (cast_ord Hdim_ABp_set j) : 'F[H]_Bp))
                    soE.
                under eq_bigr => i _ do under eq_bigr => j _ do
                  rewrite h2mx_tenf !delta_lfE !mx2hK.
                rewrite -Hmiddle.
                rewrite mulmx_sumr mulmx_suml.
                under [RHS]eq_bigr => i _ do
                  rewrite mulmx_sumr mulmx_suml.
                apply: eq_bigr=> i _.
                apply: eq_bigr=> j _.
                by rewrite /UAB -delta_lfE. }
              rewrite Hmax_so2choi /D choi2soK /M.
              by rewrite castmxK. }
            by rewrite HmaxMAB. }
          have Hptr_tenso_D :
              ptrace_castl disAB
                (((\:1 : 'SO[H]_A) :⊗ D) gamma_ABp) =
              D (ptrace_castl disABp gamma_ABp).
          { apply/eqP/trlf_intror=> g.
            rewrite -trlf_lift_partial.
            rewrite (@dualso_trlfE R 'H[H]_S_ABp 'H[H]_S_AB
              (((\:1 : 'SO[H]_A) :⊗ D)) gamma_ABp
              ((\1 : 'F[H]_A) \O g)).
            rewrite (@tenso_dual R L H A A Bp B
              (\:1 : 'SO[H]_A) D) dualso1.
            have Htenso_adj :
                (((\:1 : 'SO[H]_A) :⊗ D^*o)
                  ((\1 : 'F[H]_A) \O g : 'F[H]_S_AB)) =
                ((\1 : 'F[H]_A) \O (D^*o g) : 'F[H]_S_ABp).
            { have Hg_ten :
                  ((\1 : 'F[H]_A) \O g : 'F[H]_S_AB) =
                  (\1 : 'F[H]_A) \⊗ g.
              { apply: to_Fnd_inj.
                by rewrite (sdotFT _ _ disAB) to_Fnd_tenE. }
              rewrite Hg_ten -(@tenso_correct R L H
                A A B Bp
                (\:1 : 'SO[H]_A) D^*o disAB
                (\1 : 'F[H]_A) g) soE.
              symmetry.
              apply: to_Fnd_inj.
              by rewrite (sdotFT _ _ disABp) to_Fnd_tenE. }
            rewrite Htenso_adj (trlf_lift_partial disABp).
            by rewrite -(@dualso_trlfE R 'H[H]_Bp 'H[H]_B
              D (ptrace_castl disABp gamma_ABp) g). }
          have HD1 : D (\1 : 'F[H]_Bp) = (\1 : 'F[H]_B).
          { (* The saturated partial trace condition is the unital
               condition for the Choi inverse. *)
            have Hptr_scale :
                ptrace_castl disAB Y =
                dA_R%:C *:
                  ptrace_castl disAB
                    (((\:1 : 'SO[H]_A) :⊗ D) gamma_ABp).
            { rewrite Hrealize /ptrace_castl /ptrace_cast_gen.
              set W := (((\:1 : 'SO[H]_A) :⊗ D) gamma_ABp).
              change (castlf (setDU_l disAB, setDU_l disAB)
                (\Tr_(A) (dA_R%:C *: W)) =
                dA_R%:C *:
                  castlf (setDU_l disAB, setDU_l disAB) (\Tr_(A) W)).
              have HtrW :
                  \Tr_(A) (dA_R%:C *: W) =
                  dA_R%:C *: \Tr_(A) W.
              {
                have HlinTr := superop_is_linear (@ptraceso R L H A S_AB).
                have Htr := HlinTr dA_R%:C W 0.
                have Htr0 : \Tr_(A) (0 : 'F[H]_S_AB) = 0.
                { exact: linear0. }
                by move: Htr; rewrite addr0 Htr0 addr0.
              }
              rewrite HtrW.
              have HcastZ (x : 'F[H]_(S_AB :\: A)) :
                  castlf (setDU_l disAB, setDU_l disAB) (dA_R%:C *: x) =
                  dA_R%:C *:
                    castlf (setDU_l disAB, setDU_l disAB) x.
              { exact: linearZ. }
              by rewrite HcastZ. }
            move: HptrY.
            rewrite Hptr_scale Hptr_tenso_D Hgamma_left /=.
            have HDZ (c : C) (x : 'F[H]_Bp) :
                D (c *: x) = c *: D x.
            {
              have Hlin := superop_is_linear D.
              have HD0 : D (0 : 'F[H]_Bp) = 0.
              { exact: linear0. }
              move: (Hlin c x 0).
              rewrite addr0 HD0 addr0.
              by move=> ->.
            }
            rewrite (HDZ (dA_R^-1)%:C (\1 : 'F[H]_Bp)).
            rewrite scalerA -rmorphM /=.
            have HdA_neq0 : dA_R != 0
              by rewrite /dA_R pnatr_eq0 -lt0n dim_proper.
            by rewrite mulfV ?scale1r. }
          pose E : 'SO[H]_(B, Bp) := D^*o.
          have HEcptp : E \is cptp.
          { rewrite /E.
            pose Dcp : 'CP[H]_(Bp, B) := CPMap_Build HDcp.
            have HDcp_eq : D = Dcp := CPMap_BuildE HDcp.
            rewrite HDcp_eq.
            apply/cp_isquP.
            by rewrite -HDcp_eq. }
          exists ((fidelity (((\:1 : 'SO[H]_A) :⊗ E) rhoAB)
            gamma_ABp) ^+ 2).
          split.
          - by exists E.
          - have Psigma :
                (((\:1 : 'SO[H]_A) :⊗ E) rhoAB) \is psdlf.
            { have Hidcp : ((\:1 : 'SO[H]_A) \is cpmap)
                by exact: cptp_cpmap (idso_qc 'H[H]_A).
              have HEcp : E \is cpmap := cptp_cpmap HEcptp.
              rewrite (CPMap_BuildE Hidcp) (CPMap_BuildE HEcp).
              exact: cp_psdP Prho. }
            have Htrace_complex :
                \Tr (rhoAB \o
                  (((\:1 : 'SO[H]_A) :⊗ D) gamma_ABp)) =
                \Tr ((((\:1 : 'SO[H]_A) :⊗ E) rhoAB)
                  \o gamma_ABp).
            { rewrite lftraceC.
              rewrite (@dualso_trlfE R 'H[H]_S_ABp 'H[H]_S_AB
                (((\:1 : 'SO[H]_A) :⊗ D)) gamma_ABp rhoAB).
              rewrite (@tenso_dual R L H A A Bp B
                (\:1 : 'SO[H]_A) D).
              by rewrite dualso1 /E lftraceC. }
            have Htrace_choi :
                @complex.Re R (\Tr (rhoAB \o Y)) =
                dA_R *
                @complex.Re R
                  (\Tr ((((\:1 : 'SO[H]_A) :⊗ E) rhoAB)
                    \o gamma_ABp)).
            { rewrite Hrealize -comp_lfunZr linearZ /= Htrace_complex.
              have HRe_realM : forall (c : R) (z : C),
                  @complex.Re R (c%:C * z) = c * @complex.Re R z.
              { move=> c z.
                case: z => a b /=.
                by rewrite mul0r subr0. }
              by rewrite HRe_realM. }
            by rewrite Htrace_choi -Hgamma_fidelity. }
        have Hscaled_to_sat : forall v, Escaled v -> Dsat v.
        { (* Choi block, reverse direction: dA times the Choi state of the
             adjoint of any TP-CPM is saturated dual-feasible. *)
          move=> v [w [[E [HEcptp ->]] ->]].
          pose Eqc : 'QC[H]_(B, Bp) := QChannel_Build HEcptp.
          pose Dqu : 'QU[H]_(Bp, B) := (Eqc^*o).
          pose D : 'SO[H]_(Bp, B) := Dqu.
          pose Y : 'F[H]_S_AB :=
            dA_R%:C *:
              (((\:1 : 'SO[H]_A) :⊗ D) gamma_ABp).
          exists Y.
          split.
          - rewrite /Y.
            apply: psdlfZ.
            + by rewrite lecR /dA_R ler0n.
            + have Hidcp : ((\:1 : 'SO[H]_A) \is cpmap)
                by exact: cptp_cpmap (idso_qc 'H[H]_A).
              have HDcp : (D \is cpmap)
                by rewrite /D; apply: is_cpmap.
              rewrite (CPMap_BuildE Hidcp) (CPMap_BuildE HDcp).
              exact: cp_psdP Hgamma_psdlf.
          - have Hptr_tenso_D :
                ptrace_castl disAB
                  (((\:1 : 'SO[H]_A) :⊗ D) gamma_ABp) =
                D (ptrace_castl disABp gamma_ABp).
            { apply/eqP/trlf_intror=> g.
              rewrite -trlf_lift_partial.
              rewrite (@dualso_trlfE R 'H[H]_S_ABp 'H[H]_S_AB
                (((\:1 : 'SO[H]_A) :⊗ D)) gamma_ABp
                ((\1 : 'F[H]_A) \O g)).
              rewrite (@tenso_dual R L H A A Bp B
                (\:1 : 'SO[H]_A) D) dualso1.
              have Htenso_adj :
                  (((\:1 : 'SO[H]_A) :⊗ D^*o)
                    ((\1 : 'F[H]_A) \O g : 'F[H]_S_AB)) =
                  ((\1 : 'F[H]_A) \O (D^*o g) : 'F[H]_S_ABp).
              { have Hg_ten :
                    ((\1 : 'F[H]_A) \O g : 'F[H]_S_AB) =
                    (\1 : 'F[H]_A) \⊗ g.
                { apply: to_Fnd_inj.
                  by rewrite (sdotFT _ _ disAB) to_Fnd_tenE. }
                rewrite Hg_ten -(@tenso_correct R L H
                  A A B Bp
                  (\:1 : 'SO[H]_A) D^*o disAB
                  (\1 : 'F[H]_A) g) soE.
                symmetry.
                apply: to_Fnd_inj.
                by rewrite (sdotFT _ _ disABp) to_Fnd_tenE. }
              rewrite Htenso_adj (trlf_lift_partial disABp).
              by rewrite -(@dualso_trlfE R 'H[H]_Bp 'H[H]_B
                D (ptrace_castl disABp gamma_ABp) g). }
            have HD1 : D (\1 : 'F[H]_Bp) = (\1 : 'F[H]_B)
              by rewrite /D; exact: qu1_eq1.
            have Hptr_scale :
                ptrace_castl disAB Y =
                dA_R%:C *:
                  ptrace_castl disAB
                    (((\:1 : 'SO[H]_A) :⊗ D) gamma_ABp).
            { rewrite /Y /ptrace_castl /ptrace_cast_gen.
              set W := (((\:1 : 'SO[H]_A) :⊗ D) gamma_ABp).
              change (castlf (setDU_l disAB, setDU_l disAB)
                (\Tr_(A) (dA_R%:C *: W)) =
                dA_R%:C *:
                  castlf (setDU_l disAB, setDU_l disAB) (\Tr_(A) W)).
              have HtrW :
                  \Tr_(A) (dA_R%:C *: W) =
                  dA_R%:C *: \Tr_(A) W.
              {
                have HlinTr := superop_is_linear (@ptraceso R L H A S_AB).
                have Htr := HlinTr dA_R%:C W 0.
                have Htr0 : \Tr_(A) (0 : 'F[H]_S_AB) = 0.
                { exact: linear0. }
                by move: Htr; rewrite addr0 Htr0 addr0.
              }
              rewrite HtrW.
              have HcastZ (x : 'F[H]_(S_AB :\: A)) :
                  castlf (setDU_l disAB, setDU_l disAB) (dA_R%:C *: x) =
                  dA_R%:C *:
                    castlf (setDU_l disAB, setDU_l disAB) x.
              { exact: linearZ. }
              by rewrite HcastZ. }
            rewrite Hptr_scale Hptr_tenso_D Hgamma_left /=.
            have HDZ (c : C) (x : 'F[H]_Bp) :
                D (c *: x) = c *: D x.
            {
              have Hlin := superop_is_linear D.
              have HD0 : D (0 : 'F[H]_Bp) = 0.
              { exact: linear0. }
              move: (Hlin c x 0).
              rewrite addr0 HD0 addr0.
              by move=> ->.
            }
            rewrite (HDZ (dA_R^-1)%:C (\1 : 'F[H]_Bp)) HD1.
            rewrite scalerA -rmorphM /= mulfV ?scale1r //.
            by rewrite /dA_R pnatr_eq0 -lt0n dim_proper.
          - have Psigma :
                (((\:1 : 'SO[H]_A) :⊗ E) rhoAB) \is psdlf.
            { have Hidcp : ((\:1 : 'SO[H]_A) \is cpmap)
                by exact: cptp_cpmap (idso_qc 'H[H]_A).
              have HEcp : E \is cpmap := cptp_cpmap HEcptp.
              rewrite (CPMap_BuildE Hidcp) (CPMap_BuildE HEcp).
              exact: cp_psdP Prho. }
            have HDqudual :
                ((Dqu : 'SO[H]_(Bp, B))^*o) = E
              by rewrite /Dqu dualsoK -(QChannel_BuildE HEcptp).
            have Htrace_complex :
                \Tr (rhoAB \o
                  (((\:1 : 'SO[H]_A) :⊗ D) gamma_ABp)) =
                \Tr ((((\:1 : 'SO[H]_A) :⊗ E) rhoAB)
                  \o gamma_ABp).
            { rewrite lftraceC.
              rewrite (@dualso_trlfE R 'H[H]_S_ABp 'H[H]_S_AB
                (((\:1 : 'SO[H]_A) :⊗ D)) gamma_ABp rhoAB).
              rewrite (@tenso_dual R L H A A Bp B
                (\:1 : 'SO[H]_A) D).
              by rewrite dualso1 /D HDqudual lftraceC. }
            have Htrace_choi :
                @complex.Re R (\Tr (rhoAB \o Y)) =
                dA_R *
                @complex.Re R
                  (\Tr ((((\:1 : 'SO[H]_A) :⊗ E) rhoAB)
                    \o gamma_ABp)).
            { rewrite /Y -comp_lfunZr linearZ /= Htrace_complex.
              have HRe_realM : forall (c : R) (z : C),
                  @complex.Re R (c%:C * z) = c * @complex.Re R z.
              { move=> c z.
                case: z => a b /=.
                by rewrite mul0r subr0. }
              by rewrite HRe_realM. }
            by rewrite Htrace_choi -Hgamma_fidelity. }
        have Hsat_scaled : Dsat = Escaled.
        { apply/funext=> v /=.
          apply/propext; split.
          - exact: Hsat_to_scaled.
          - exact: Hscaled_to_sat. }
        have Hsup_scaled :
            ExtNumTopology.etsup Escaled = dA_R * sup Ecoh.
        { (* Supremum bridge: scale the TP-CPM fidelity value set by dA. *)
          have HdA_pos : 0 < dA_R
            by rewrite /dA_R ltr0n dim_proper.
          have HdA_ge0 : 0 <= dA_R := ltW HdA_pos.
          have HEscaled_has_sup : has_sup Escaled
            by rewrite -Hsat_scaled.
          have HEcoh_has_sup : has_sup Ecoh.
          { split.
            - case: HEscaled_has_sup => Hne _.
              case: Hne => v [w [Hw _]].
              by exists w.
            - case: HEscaled_has_sup => _ [M HM].
              exists (dA_R^-1 * M) => w Hw.
              have Hv : Escaled (dA_R * w) by exists w; split.
              have Hdw := HM _ Hv.
              rewrite -(ler_pM2l HdA_pos).
              rewrite mulrA (mulfV (lt0r_neq0 HdA_pos)) mul1r.
              exact: Hdw. }
          change (sup Escaled = dA_R * sup Ecoh).
          apply/eqP.
          rewrite eq_le.
          apply/andP; split.
          - apply: ExtNumTopology.sup_least_ubound.
            + exact: HEscaled_has_sup.
            + move=> v [w [Hw ->]].
              apply: ler_wpM2l.
              * exact: HdA_ge0.
              * have /ubP HEcoh_ub := sup_upper_bound HEcoh_has_sup.
                exact: HEcoh_ub _ Hw.
          - have Heco_le :
                sup Ecoh <= dA_R^-1 * sup Escaled.
            { apply: ExtNumTopology.sup_least_ubound.
              - exact: HEcoh_has_sup.
              - move=> w Hw.
                have Hv : Escaled (dA_R * w) by exists w; split.
                have /ubP HEscaled_ub := sup_upper_bound HEscaled_has_sup.
                have Hdw := HEscaled_ub _ Hv.
                rewrite -(ler_pM2l HdA_pos).
                rewrite mulrA (mulfV (lt0r_neq0 HdA_pos)) mul1r.
                exact: Hdw. }
            have Hmul := ler_wpM2l HdA_ge0 Heco_le.
            move: Hmul.
            by rewrite mulrA (mulfV (lt0r_neq0 HdA_pos)) mul1r. }
        by rewrite Hsat_scaled Hsup_scaled. }
      by rewrite Hdual_ineq Hsup_Dineq_Dsat Hsat_choi_fidelity. }
    by rewrite Halpha_sdp Hstrong_dual Hchoi_fidelity. }
  (* Final step: bridge `Ecoh` (fidelity-based, used in Hbridge) to the
     gfid-based set in the lemma statement.  Pointwise via
     gfid_eq_fid_tr1_mx + symmetry on both sides. *)
  pose Ecoh_g : set R := fun v : R =>
    exists E : 'SO[H]_(B, Bp),
      [/\ E \is cptp &
          v =
          (gfid (((\:1 : 'SO[H]_A) :⊗ E) rhoAB)
             gamma_ABp) ^+ 2].
  have Hpt :
      forall (E : 'SO[H]_(B, Bp)),
        E \is cptp ->
        gfid (((\:1 : 'SO[H]_A) :⊗ E) rhoAB) gamma_ABp =
        fidelity (((\:1 : 'SO[H]_A) :⊗ E) rhoAB) gamma_ABp.
  { move=> E HEcptp.
    pose X : 'F[H]_S_ABp := ((\:1 : 'SO[H]_A) :⊗ E) rhoAB.
    have HXpsd : X \is psdlf.
    { rewrite /X.
      have Hidcp : ((\:1 : 'SO[H]_A) \is cpmap)
        by exact: cptp_cpmap (idso_qc 'H[H]_A).
      have HEcp : E \is cpmap := cptp_cpmap HEcptp.
      rewrite (CPMap_BuildE Hidcp) (CPMap_BuildE HEcp).
      exact: cp_psdP Prho. }
    have HXmx_psd : h2mx X \is psdmx
      by move: HXpsd; rewrite qualifE.
    have HtensTP : ((\:1 : 'SO[H]_A) :⊗ E) \is cptp.
    { pose Eqc : 'QC[H]_(B, Bp) := QChannel_Build HEcptp.
      pose Idqc : 'QC[H]_(A, A) :=
        QChannel_Build (idso_qc 'H[H]_A).
      exact: (@tenso_qc R L H A A B Bp
                disAB disABp Idqc Eqc). }
    have /cptpP [_ /tpmapP HtensTr] := HtensTP.
    have HX_tr_eq : \Tr X = \Tr rhoAB by rewrite /X HtensTr.
    have HX_tr_le : @complex.Re R (\Tr X) <= 1 by rewrite HX_tr_eq.
    have HX_mx_tr_le : @complex.Re R (\tr (h2mx X)) <= 1
      by move: HX_tr_le; rewrite /lftrace.
    rewrite /gfid.
    rewrite (gfid_sym_mx HXmx_psd Hgamma_mx_psd).
    rewrite (gfid_eq_fid_tr1_mx Hgamma_mx_psd HXmx_psd
               Hgamma_mx_tr1 HX_mx_tr_le).
    rewrite /fidelity h2mx_comp !sqrtH_h2mx.
      exact: (fid_i_sym_mx Hgamma_mx_psd HXmx_psd). }
  have Hset_eq : Ecoh = Ecoh_g.
  { apply/funext=> v.
    apply/propext; split.
    - move=> [E [HEcptp Hv]].
      exists E; split=> //.
      by rewrite Hv (Hpt E HEcptp).
    - move=> [E [HEcptp Hv]].
      exists E; split=> //.
      by rewrite Hv -(Hpt E HEcptp). }
  by rewrite /hminE Hbridge Hset_eq.
Qed.

(* path: entropy:min_omni -> entropy:minmax_dual -> entropy:smooth_iso_hmax -> *)
(*   entropy:entropy_data_proc -> *)
(*   bb84:bb84_secret *)
Lemma min_omni (rhoAB : 'F[H]_S_AB) :
  rhoAB \is denlf ->
  hminE B rhoAB =
  oppe (elog2
      ((dim 'H[H]_A)%:R *
       sup [set v : R |
           exists (V : 'FI[H]_(B, S_BpBpp)),
             exists tau : 'F[H]_Bpp,
             [/\ tau \is den1lf &
                 v =
                 (gfid
                    (((\1 : 'F[H]_A) \⊗ V) \o rhoAB \o
                    (((\1 : 'F[H]_A) \⊗ V)^A))
                    (castlf (esym eqABpBpp, esym eqABpBpp)
                      ((gamma_ABp \O tau) : 'F[H]_S_ABpBpp))) ^+ 2]])).
Proof.
  move=> Hrho_den.
  have Prho : rhoAB \is psdlf := denlf_psd Hrho_den.
  have Hrho : @complex.Re R (\Tr rhoAB) <= 1.
  { have Hreal : \Tr rhoAB \is Num.real := ger0_real (psdlf_trlf Prho).
    by move: (denlf_trlf Hrho_den); rewrite -(RRe_real Hreal) lecR. }
  (* Re-derive gamma facts (they live inside min_koenig's proof scope).   *)
  have Hgamma_den1 : gamma_ABp \is den1lf :=
    @gamma_state_den1 R L H A Bp disABp dimABp_set.
  have Hgamma_psdlf : gamma_ABp \is psdlf := den1lf_psd Hgamma_den1.
  have Hgamma_tr1 : \Tr gamma_ABp = 1.
  { by move/den1lfP: Hgamma_den1 => [_ ->]. }
  have Hgamma_mx_psd : h2mx gamma_ABp \is psdmx
    by move: Hgamma_psdlf; rewrite qualifE.
  have Hgamma_mx_tr1 : \tr (h2mx gamma_ABp) = 1
    by move: Hgamma_tr1; rewrite /lftrace.
  (* Disjointness facts.                                                   *)
  have disABp_Bpp0 : [disjoint S_ABp & Bpp]
    by rewrite /S_ABp disjointUX disABpp disBpBpp.
  have disA_BpBpp0 : [disjoint A & S_BpBpp]
    by rewrite /S_BpBpp disjointXU disABp disABpp.
  (* Note: disA_BpBpp0 / disABp_Bpp0 are required by `Hproc_eqV` and by
     the Stinespring-bridging pieces `Hsup_le` / `Hsup_ge`.                *)
  (* The `Ecoh` set (fidelity-based; matches the substantive body work). *)
  pose Ecoh : set R := fun v : R =>
    exists E : 'SO[H]_(B, Bp),
      [/\ E \is cptp &
          v =
          (fidelity (((\:1 : 'SO[H]_A) :⊗ E) rhoAB)
             gamma_ABp) ^+ 2].
  (* Pointwise bridge: any CPTP image gives gfid = fidelity
     (gamma_ABp on the right is den1, so the embed-subnorm correction in
     gfidelity vanishes).  Same pattern as `Hpt` inside `min_koenig`.      *)
  have Hpt_coh :
      forall (E : 'SO[H]_(B, Bp)),
        E \is cptp ->
        gfid (((\:1 : 'SO[H]_A) :⊗ E) rhoAB) gamma_ABp =
        fidelity (((\:1 : 'SO[H]_A) :⊗ E) rhoAB) gamma_ABp.
  { move=> E HEcptp.
    pose X : 'F[H]_S_ABp := ((\:1 : 'SO[H]_A) :⊗ E) rhoAB.
    have HXpsd : X \is psdlf.
    { rewrite /X.
      have Hidcp : ((\:1 : 'SO[H]_A) \is cpmap)
        by exact: cptp_cpmap (idso_qc 'H[H]_A).
      have HEcp : E \is cpmap := cptp_cpmap HEcptp.
      rewrite (CPMap_BuildE Hidcp) (CPMap_BuildE HEcp).
      exact: cp_psdP Prho. }
    have HXmx_psd : h2mx X \is psdmx by move: HXpsd; rewrite qualifE.
    have HtensTP : ((\:1 : 'SO[H]_A) :⊗ E) \is cptp.
    { pose Eqc : 'QC[H]_(B, Bp) := QChannel_Build HEcptp.
      pose Idqc : 'QC[H]_(A, A) :=
        QChannel_Build (idso_qc 'H[H]_A).
      exact: (@tenso_qc R L H A A B Bp
                disAB disABp Idqc Eqc). }
    have /cptpP [_ /tpmapP HtensTr] := HtensTP.
    have HX_tr_eq : \Tr X = \Tr rhoAB by rewrite /X HtensTr.
    have HX_mx_tr_le : @complex.Re R (\tr (h2mx X)) <= 1
      by move: Hrho; rewrite -HX_tr_eq /lftrace.
    rewrite /gfid.
    rewrite (gfid_sym_mx HXmx_psd Hgamma_mx_psd).
    rewrite (gfid_eq_fid_tr1_mx Hgamma_mx_psd HXmx_psd
               Hgamma_mx_tr1 HX_mx_tr_le).
    rewrite /fidelity h2mx_comp !sqrtH_h2mx.
      exact: (fid_i_sym_mx Hgamma_mx_psd HXmx_psd). }
  (* Set equality between min_koenig's RHS set and Ecoh, established
     pointwise via Hpt_coh.                                                *)
  pose Ecoh_g : set R := fun v : R =>
    exists E : 'SO[H]_(B, Bp),
      [/\ E \is cptp &
          v =
          (gfid (((\:1 : 'SO[H]_A) :⊗ E) rhoAB)
             gamma_ABp) ^+ 2].
  have Hcoh_eq : Ecoh_g = Ecoh.
  { apply/funext=> v; apply/propext; split.
    - move=> [E [HEcptp Hv]]; exists E; split=> //.
      by rewrite Hv (Hpt_coh E HEcptp).
    - move=> [E [HEcptp Hv]]; exists E; split=> //.
      by rewrite Hv -(Hpt_coh E HEcptp). }
  (* Apply min_koenig: hminE = -elog2 of the dimension-weighted gfid supremum.
     Use Ecoh_g as the bridge.  The min_koenig RHS is definitionally the
     same existential image set as Ecoh_g,
     so the substitution succeeds via change.                              *)
  have Hk_koenig := min_koenig Hrho_den.
  have Hk_alt :
      hminE B rhoAB =
      oppe (elog2 ((dim 'H[H]_A)%:R * sup Ecoh_g))
    by rewrite Hk_koenig.
  rewrite Hk_alt Hcoh_eq.
  (* Remaining: sup Ecoh = sup [goal-set, gfid-based on Eden_g].
     This is the substantive Stinespring + Uhlmann content
     (Hptrace2_conj_tens_right_iso, Hproc_eqV, Hsup_le, Hsup_ge,
     Hsup_eq).  The gfid↔fidelity bridge for the goal set is also
     folded in here (Hpt_den / Hden_eq).                                   *)
  congr (oppe (elog2 ((dim 'H[H]_A)%:R * _))).
  (* Hptrace2_conj_tens_right_iso:
     Pure matrix identity: the right-iso sandwich (1 *t U0) M (1 *t U0)^*t
     has the same partial trace over the second register as M, whenever
     U0 is a left-iso (U0^*t * U0 = 1).                                    *)
  have Hptrace2_conj_tens_right_iso :
      forall a b b' (U0 : 'M[C]_(b', b)) (M : 'M[C]_(a * b)),
        U0^*t *m U0 = 1%:M ->
        ptrace2
          ((((1%:M : 'M[C]_a) *t U0) *m M) *m
             (((1%:M : 'M[C]_a) *t U0)^*t)) =
        ptrace2 M.
  { move=> a0 b0 b1 U0 M0 HU0.
    have ptrace2E' : forall s t (N1 : 'M[C]_(s * t)) r1 r2,
      (ptrace2 N1) r1 r2 =
      \sum_l N1 (mxtens_index (r1, l)) (mxtens_index (r2, l)).
    { move=> s t N1 r1 r2.
      rewrite ptrace2E1 ptrace1E.
      by apply: eq_bigr => l _; rewrite mxE !mxtens_indexK. }
    apply/matrixP => i j.
    rewrite !ptrace2E'.
    pose RR := (((1%:M : 'M[C]_a0) *t U0)^*t).
    have HleftMul :
        forall (N1 : 'M[C]_(a0 * b0, a0 * b1))
               (k : 'I_b1) (t : 'I_(a0 * b1)),
          ((((1%:M : 'M[C]_a0) *t U0) *m N1)
             (mxtens_index (i, k)) t) =
          \sum_(k1 : 'I_b0) U0 k k1 * N1 (mxtens_index (i, k1)) t.
    { move=> N1 k t.
      rewrite (tensmxE_mid (((1%:M : 'M[C]_a0) *t U0)) N1
        (mxtens_index (i, k)) t).
      transitivity
        (\sum_(i1 : 'I_a0) \sum_(k1 : 'I_b0)
          ((i == i1)%:R * U0 k k1) *
          N1 (mxtens_index (i1, k1)) t).
      { apply: eq_bigr => i1 _.
        apply: eq_bigr => k1 _.
        by rewrite tensmxE !mxE -mulrA. }
      transitivity
        (\sum_(i1 : 'I_a0)
          (i == i1)%:R *
          \sum_(k1 : 'I_b0) U0 k k1 * N1 (mxtens_index (i1, k1)) t).
      { apply: eq_bigr => i1 _.
        rewrite mulr_sumr.
        by apply: eq_bigr => k1 _; rewrite -mulrA. }
      rewrite (bigD1 i) //= eqxx mul1r.
      rewrite [X in _ + X]big1 ?addr0 //.
      by move=> i1 Hi1; rewrite eq_sym (negPf Hi1) mul0r. }
    have HrightMul :
        forall (k1 : 'I_b0) (k : 'I_b1),
          (M0 *m RR) (mxtens_index (i, k1)) (mxtens_index (j, k)) =
          \sum_(k2 : 'I_b0)
            M0 (mxtens_index (i, k1)) (mxtens_index (j, k2)) *
            (U0^*t) k2 k.
    { move=> k1 k.
      rewrite /RR.
      rewrite (tensmxE_mid M0 (((1%:M : 'M[C]_a0) *t U0)^*t)
        (mxtens_index (i, k1)) (mxtens_index (j, k))).
      transitivity
        (\sum_(j1 : 'I_a0) \sum_(k2 : 'I_b0)
          ((j == j1)%:R *
            M0 (mxtens_index (i, k1)) (mxtens_index (j1, k2))) *
          (U0^*t) k2 k).
      { apply: eq_bigr => j1 _.
        apply: eq_bigr => k2 _.
        rewrite adjmx_tens adjmx1.
        rewrite tensmxE !mxE eq_sym.
        rewrite -mulrA.
        by rewrite mulrCA. }
      transitivity
        (\sum_(j1 : 'I_a0)
          (j == j1)%:R *
          \sum_(k2 : 'I_b0)
            M0 (mxtens_index (i, k1)) (mxtens_index (j1, k2)) *
            (U0^*t) k2 k).
      { apply: eq_bigr => j1 _.
        rewrite mulr_sumr.
        by apply: eq_bigr => k2 _; rewrite -mulrA. }
      rewrite (bigD1 j) //= eqxx mul1r.
      rewrite [X in _ + X]big1 ?addr0 //.
      by move=> j1 Hj1; rewrite eq_sym (negPf Hj1) mul0r. }
    transitivity
      (\sum_(k : 'I_b1) \sum_(k1 : 'I_b0)
        U0 k k1 * (M0 *m RR) (mxtens_index (i, k1)) (mxtens_index (j, k))).
    { apply: eq_bigr => k _.
      by rewrite -mulmxA HleftMul. }
    rewrite exchange_big /=.
    transitivity
      (\sum_(k1 : 'I_b0) \sum_(k2 : 'I_b0)
        M0 (mxtens_index (i, k1)) (mxtens_index (j, k2)) *
        \sum_(k : 'I_b1) (U0^*t) k2 k * U0 k k1).
    { apply: eq_bigr => k1 _.
      transitivity
        (\sum_(k : 'I_b1) \sum_(k2 : 'I_b0)
          M0 (mxtens_index (i, k1)) (mxtens_index (j, k2)) *
          ((U0^*t) k2 k * U0 k k1)).
      - apply: eq_bigr => k _.
        rewrite HrightMul mulr_sumr.
        apply: eq_bigr => k2 _.
        rewrite mulrA [U0 k k1 * _]mulrC -mulrA.
        by rewrite [(U0 k k1) * _]mulrC.
      - rewrite exchange_big /=.
        apply: eq_bigr => k2 _.
        by rewrite -mulr_sumr. }
    transitivity
      (\sum_(k1 : 'I_b0) \sum_(k2 : 'I_b0)
        M0 (mxtens_index (i, k1)) (mxtens_index (j, k2)) *
        ((U0^*t *m U0) k2 k1)).
    { apply: eq_bigr => k1 _.
      by apply: eq_bigr => k2 _; rewrite mxE. }
    rewrite HU0.
    transitivity
      (\sum_(k1 : 'I_b0)
        M0 (mxtens_index (i, k1)) (mxtens_index (j, k1))).
    { apply: eq_bigr => k1 _.
      rewrite (bigD1 k1) //= mxE !eqxx /= mulr1.
      rewrite big1 ?addr0 //.
      move=> k2 Hk2; rewrite mxE.
      have -> : (k2 == k1) = false by rewrite (negPf Hk2).
      by rewrite /= mulr0. }
    by []. }
  have Hproc_eqV :
      forall V : 'FI[H]_(B, S_BpBpp),
        (((\:1 : 'SO[H]_A) :⊗
           (((castso (erefl _, setDU_r disBpBpp)
                (QChannel_Build (@ptraceso_qc R L H Bpp S_BpBpp)))
               : 'QC[H]_(S_BpBpp, Bp)) :o formso V)) rhoAB) =
        @ptrace_cast R L H S_ABp Bpp disABp_Bpp0
          (castlf (eqABpBpp, eqABpBpp)
            ((((\1 : 'F[H]_A) \⊗ V) \o rhoAB \o
              (((\1 : 'F[H]_A) \⊗ V)^A))
                : 'F[H]_(A :|: S_BpBpp))).
  { move=> V.
    pose PTqc0 : 'QC[H]_(S_BpBpp, S_BpBpp :\: Bpp) :=
      QChannel_Build (@ptraceso_qc R L H Bpp S_BpBpp).
    pose PTqc : 'QC[H]_(S_BpBpp, Bp) :=
      castso (erefl _, setDU_r disBpBpp) PTqc0.
    pose E : 'QC[H]_(B, Bp) := PTqc :o formso V.
    pose rho_ext_raw : 'F[H]_(A :|: S_BpBpp) :=
      (((\1 : 'F[H]_A) \⊗ V) \o rhoAB \o
       (((\1 : 'F[H]_A) \⊗ V)^A)).
    pose rho_ext : 'F[H]_S_ABpBpp :=
      castlf (eqABpBpp, eqABpBpp) rho_ext_raw.
    have Hcomp :
        (((\:1 : 'SO[H]_A) :⊗ (E : 'SO[H]_(B, Bp)))
          rhoAB) =
        (((\:1 : 'SO[H]_A) :⊗
           (PTqc : 'SO[H]_(S_BpBpp, Bp))) rho_ext_raw).
    { have HextE_raw :
          rho_ext_raw =
          (((\:1 : 'SO[H]_A) :⊗ formso V) rhoAB).
      { have -> :
            ((\:1 : 'SO[H]_A) :⊗ formso V) =
            formso ((\1 : 'F[H]_A) \⊗ V).
        { by rewrite -formso1 tenso_formso. }
        by rewrite /rho_ext_raw formsoE. }
      rewrite /E.
      have -> :
          ((\:1 : 'SO[H]_A) :⊗
            ((PTqc : 'SO[H]_(S_BpBpp, Bp)) :o formso V)) =
          ((((\:1 : 'SO[H]_A) :⊗
              (PTqc : 'SO[H]_(S_BpBpp, Bp))) :o
             ((\:1 : 'SO[H]_A) :⊗ formso V))
              : 'SO[H]_(S_AB, S_ABp)).
      { by rewrite -tenso_comp ?comp_so1l //. }
      by rewrite comp_soE HextE_raw. }
    pose PTfull0 : 'QC[H]_(S_ABpBpp, S_ABpBpp :\: Bpp) :=
      QChannel_Build (@ptraceso_qc R L H Bpp S_ABpBpp).
    pose PTfull : 'QC[H]_(S_ABpBpp, S_ABp) :=
      castso (erefl _, setDU_r disABp_Bpp0) PTfull0.
    have HPT_tensor :
        (((\:1 : 'SO[H]_A) :⊗
           (PTqc : 'SO[H]_(S_BpBpp, Bp))) :
           'SO[H]_(A :|: S_BpBpp, S_ABp)) =
        castso (esym eqABpBpp, erefl _)
          (PTfull : 'SO[H]_(S_ABpBpp, S_ABp)).
    { (* Cast bridge: tensoring the small partial trace with I_A is
         the same superoperator as the full partial trace over B''
         on A B' B''. *)
      have HPTqc_basis :
          forall u v : 'Idx[H]_S_BpBpp,
            PTqc [> deltav u ; deltav v <] =
            (idxSr u == idxSr v)%:R *:
              [> deltav (idxSl u) ; deltav (idxSl v)
                 : 'H[H]_Bp <].
      { move=> u0 w0.
        have Huv_ten :
            [> deltav u0 ; deltav w0 <] =
            (([> deltav (idxSl u0) ; deltav (idxSl w0)
                 : 'H[H]_Bp <] \O
              [> deltav (idxSr u0) ; deltav (idxSr w0)
                 : 'H[H]_Bpp <]) : 'F[H]_S_BpBpp).
        { apply: to_Fnd_inj.
          rewrite !dv_split -tenf_outp to_Fnd_tenE.
          by rewrite (sdotFT _ _ disBpBpp). }
        rewrite /PTqc castsoE /= Huv_ten.
        rewrite (QChannel_BuildE (@ptraceso_qc R L H Bpp S_BpBpp)).
        pose rho_uv : 'F[H]_S_BpBpp :=
          (([> deltav (idxSl u0) ; deltav (idxSl w0)
               : 'H[H]_Bp <] \⊗
            [> deltav (idxSr u0) ; deltav (idxSr w0)
               : 'H[H]_Bpp <]) : 'F[H]_S_BpBpp).
        have Huv_tenF :
            (([> deltav (idxSl u0) ; deltav (idxSl w0)
                 : 'H[H]_Bp <] \O
              [> deltav (idxSr u0) ; deltav (idxSr w0)
                 : 'H[H]_Bpp <]) : 'F[H]_S_BpBpp) = rho_uv.
        { apply: to_Fnd_inj.
          by rewrite (sdotFT _ _ disBpBpp) to_Fnd_tenE. }
        rewrite Huv_tenF.
        have -> :
            castlf (setDU_r disBpBpp, setDU_r disBpBpp)
              ((@ptraceso R L H Bpp S_BpBpp) rho_uv) =
            ptrace_cast disBpBpp rho_uv.
        { by rewrite /ptrace_cast /ptrace_cast_gen. }
        apply/h2mx_inj.
        rewrite (h2mx_ptrace_cast_ptrace2 disBpBpp rho_uv).
        rewrite h2mx_tenf.
        pose U := @tenv_mxU R L H Bp Bpp.
        have HUadj : U^*t \is unitarymx := tenv_mxU_adj_unitarymx disBpBpp.
        have Uadj_mul_U : U^*t *m U = 1%:M.
        { by have := unitarymxK HUadj; rewrite adjmxK. }
        rewrite !mulmxA Uadj_mul_U mul1mx -mulmxA Uadj_mul_U mulmx1.
        rewrite ptrace_tensmx.
        have -> :
            \tr
              (h2mx
                 [> deltav (idxSr u0) ; deltav (idxSr w0)
                    : 'H[H]_Bpp <]) =
            (idxSr u0 == idxSr w0)%:R.
        { change
            (\Tr [> deltav (idxSr u0) ; deltav (idxSr w0)
                    : 'H[H]_Bpp <] =
             (idxSr u0 == idxSr w0)%:R).
          by rewrite outp_trlf dv_dot eq_sym. }
        by rewrite h2mxZ_lf. }
      have HPTfull_basis :
          forall u v : 'Idx[H]_(A :|: S_BpBpp),
            castso (esym eqABpBpp, erefl _)
              (PTfull : 'SO[H]_(S_ABpBpp, S_ABp))
              [> deltav u ; deltav v <] =
            (idxSr (idxSr u) == idxSr (idxSr v))%:R *:
              (([> deltav (idxSl u) ; deltav (idxSl v)
                   : 'H[H]_A <] \O
                [> deltav (idxSl (idxSr u)) ;
                   deltav (idxSl (idxSr v))
                   : 'H[H]_Bp <]) : 'F[H]_S_ABp).
      { move=> u0 w0.
        have Huv_right :
            [> deltav (idxSr u0) ; deltav (idxSr w0) <] =
            (([> deltav (idxSl (idxSr u0)) ;
                 deltav (idxSl (idxSr w0))
                 : 'H[H]_Bp <] \O
              [> deltav (idxSr (idxSr u0)) ;
                 deltav (idxSr (idxSr w0))
                 : 'H[H]_Bpp <]) : 'F[H]_S_BpBpp).
        { apply: to_Fnd_inj.
          rewrite !dv_split -tenf_outp to_Fnd_tenE.
          by rewrite (sdotFT _ _ disBpBpp). }
        have Hcast_in :
            castlf (eqABpBpp, eqABpBpp) [> deltav u0 ; deltav w0 <] =
            ((([> deltav (idxSl u0) ; deltav (idxSl w0)
                  : 'H[H]_A <] \O
                 [> deltav (idxSl (idxSr u0)) ;
                    deltav (idxSl (idxSr w0))
                    : 'H[H]_Bp <]) \O
               [> deltav (idxSr (idxSr u0)) ;
                  deltav (idxSr (idxSr w0))
                  : 'H[H]_Bpp <]) : 'F[H]_S_ABpBpp).
        { have Houter_right :
              [> deltav u0 ; deltav w0 <] =
              (([> deltav (idxSl u0) ; deltav (idxSl w0)
                    : 'H[H]_A <] \O
                 [> deltav (idxSr u0) ; deltav (idxSr w0)
                    : 'H[H]_S_BpBpp <]) :
                 'F[H]_(A :|: S_BpBpp)).
          { apply: to_Fnd_inj.
            by rewrite !dv_split -tenf_outp to_Fnd_tenE
              (sdotFT _ _ disA_BpBpp0). }
          rewrite Houter_right Huv_right.
          pose fA : 'F[H]_A :=
            [> deltav (idxSl u0) ; deltav (idxSl w0) <].
          pose gBp : 'F[H]_Bp :=
            [> deltav (idxSl (idxSr u0)) ;
               deltav (idxSl (idxSr w0)) <].
          pose hBpp : 'F[H]_Bpp :=
            [> deltav (idxSr (idxSr u0)) ;
               deltav (idxSr (idxSr w0)) <].
            apply: to_Fnd_inj.
            by rewrite Fnd_cast !to_Fnd_sdotE dotFsA. }
        have Hcast_in_full :
            castlf (esym (esym eqABpBpp), esym (esym eqABpBpp))
              [> deltav u0 ; deltav w0 <] =
            ((([> deltav (idxSl u0) ; deltav (idxSl w0)
                  : 'H[H]_A <] \O
                 [> deltav (idxSl (idxSr u0)) ;
                    deltav (idxSl (idxSr w0))
                    : 'H[H]_Bp <]) \O
               [> deltav (idxSr (idxSr u0)) ;
                  deltav (idxSr (idxSr w0))
                  : 'H[H]_Bpp <]) : 'F[H]_S_ABpBpp).
        { by rewrite !esymK Hcast_in. }
        rewrite castsoE /= /PTfull castsoE /=.
        rewrite [castlf (esym (esym eqABpBpp), esym (esym eqABpBpp))
                    [> deltav u0 ; deltav w0 <]] Hcast_in_full.
        rewrite (QChannel_BuildE (@ptraceso_qc R L H Bpp S_ABpBpp)).
        pose rho_full : 'F[H]_S_ABpBpp :=
          ((([> deltav (idxSl u0) ; deltav (idxSl w0)
                : 'H[H]_A <] \⊗
               [> deltav (idxSl (idxSr u0)) ;
                  deltav (idxSl (idxSr w0))
                  : 'H[H]_Bp <]) \⊗
             [> deltav (idxSr (idxSr u0)) ;
                deltav (idxSr (idxSr w0))
                : 'H[H]_Bpp <]) : 'F[H]_S_ABpBpp).
        have Hfull_tenF :
            ((([> deltav (idxSl u0) ; deltav (idxSl w0)
                  : 'H[H]_A <] \O
                 [> deltav (idxSl (idxSr u0)) ;
                    deltav (idxSl (idxSr w0))
                    : 'H[H]_Bp <]) \O
              [> deltav (idxSr (idxSr u0)) ;
                 deltav (idxSr (idxSr w0))
                 : 'H[H]_Bpp <]) : 'F[H]_S_ABpBpp) = rho_full.
        { apply: to_Fnd_inj.
          by rewrite (sdotFT _ _ disABp_Bpp0) (sdotFT _ _ disABp) !to_Fnd_tenE. }
        rewrite Hfull_tenF.
        have -> :
            castlf (setDU_r disABp_Bpp0, setDU_r disABp_Bpp0)
              ((@ptraceso R L H Bpp S_ABpBpp) rho_full) =
            ptrace_cast disABp_Bpp0 rho_full.
        { by rewrite /ptrace_cast /ptrace_cast_gen. }
        apply/h2mx_inj.
        rewrite (h2mx_ptrace_cast_ptrace2 disABp_Bpp0 rho_full).
        rewrite h2mx_tenf.
        pose U := @tenv_mxU R L H S_ABp Bpp.
        have HUadj : U^*t \is unitarymx :=
          tenv_mxU_adj_unitarymx disABp_Bpp0.
        have Uadj_mul_U : U^*t *m U = 1%:M.
        { by have := unitarymxK HUadj; rewrite adjmxK. }
        rewrite !mulmxA Uadj_mul_U mul1mx -mulmxA Uadj_mul_U mulmx1.
        rewrite ptrace_tensmx.
        have -> :
            \tr
              (h2mx
                 [> deltav (idxSr (idxSr u0)) ;
                    deltav (idxSr (idxSr w0))
                    : 'H[H]_Bpp <]) =
            (idxSr (idxSr u0) == idxSr (idxSr w0))%:R.
        { change
            (\Tr [> deltav (idxSr (idxSr u0)) ;
                    deltav (idxSr (idxSr w0))
                    : 'H[H]_Bpp <] =
             (idxSr (idxSr u0) == idxSr (idxSr w0))%:R).
          by rewrite outp_trlf dv_dot eq_sym. }
        have HABp_tenF :
            (([> deltav (idxSl u0) ; deltav (idxSl w0)
                  : 'H[H]_A <] \O
               [> deltav (idxSl (idxSr u0)) ;
                  deltav (idxSl (idxSr w0))
                  : 'H[H]_Bp <]) : 'F[H]_S_ABp) =
            (([> deltav (idxSl u0) ; deltav (idxSl w0)
                  : 'H[H]_A <] \⊗
               [> deltav (idxSl (idxSr u0)) ;
                  deltav (idxSl (idxSr w0))
                  : 'H[H]_Bp <]) : 'F[H]_S_ABp).
        { apply: to_Fnd_inj.
          by rewrite (sdotFT _ _ disABp) to_Fnd_tenE. }
          by rewrite h2mxZ_lf HABp_tenF. }
      apply/superopPD=> i j.
      have HABp_tenF :
          (([> deltav (idxSl i) ; deltav (idxSl j)
                : 'H[H]_A <] \O
             [> deltav (idxSl (idxSr i)) ;
                deltav (idxSl (idxSr j))
                : 'H[H]_Bp <]) : 'F[H]_S_ABp) =
          (([> deltav (idxSl i) ; deltav (idxSl j)
                : 'H[H]_A <] \⊗
             [> deltav (idxSl (idxSr i)) ;
                deltav (idxSl (idxSr j))
                : 'H[H]_Bp <]) : 'F[H]_S_ABp).
      { apply: to_Fnd_inj.
        by rewrite (sdotFT _ _ disABp) to_Fnd_tenE. }
      rewrite -tensodf !soE.
      by rewrite HPTqc_basis tenfZr HPTfull_basis HABp_tenF. }
    have HPTfull_rho :
        PTfull rho_ext =
        @ptrace_cast R L H S_ABp Bpp disABp_Bpp0 rho_ext.
    { rewrite /PTfull castsoE /=.
      rewrite (QChannel_BuildE (@ptraceso_qc R L H Bpp S_ABpBpp)).
      by rewrite /ptrace_cast /ptrace_cast_gen. }
    rewrite Hcomp HPT_tensor.
    rewrite castsoE /=.
    have -> :
        castlf (esym (esym eqABpBpp), esym (esym eqABpBpp)) rho_ext_raw =
        rho_ext.
    { by rewrite /rho_ext !esymK. }
    exact: HPTfull_rho. }
  (* ---------------------------------------------------------------------- *)
  (* Bridge gfid-goal-set ↔ Eden, then start Hsup_le with HEden_has_sup.    *)
  (* ---------------------------------------------------------------------- *)
  pose Eden : set R := fun v : R =>
    exists (V : 'FI[H]_(B, S_BpBpp)),
      exists tau : 'F[H]_Bpp,
        [/\ tau \is den1lf &
            v =
            (fidelity
               (((\1 : 'F[H]_A) \⊗ V) \o rhoAB \o
                (((\1 : 'F[H]_A) \⊗ V)^A))
               (castlf (esym eqABpBpp, esym eqABpBpp)
                 ((gamma_ABp \O tau) : 'F[H]_S_ABpBpp))) ^+ 2].
  (* Pointwise gfid↔fidelity bridge for Eden witnesses; gamma_ABp\O
     tau is den1 (tenfXX of two den1's), so the trace-1 hypothesis applies. *)
  have Hpt_den :
      forall (V : 'FI[H]_(B, S_BpBpp)) (tau : 'F[H]_Bpp),
        tau \is den1lf ->
        gfid
          (((\1 : 'F[H]_A) \⊗ V) \o rhoAB \o
           (((\1 : 'F[H]_A) \⊗ V)^A))
          (castlf (esym eqABpBpp, esym eqABpBpp)
            ((gamma_ABp \O tau) : 'F[H]_S_ABpBpp)) =
        fidelity
          (((\1 : 'F[H]_A) \⊗ V) \o rhoAB \o
           (((\1 : 'F[H]_A) \⊗ V)^A))
          (castlf (esym eqABpBpp, esym eqABpBpp)
            ((gamma_ABp \O tau) : 'F[H]_S_ABpBpp)).
  { move=> V tau Htau_den.
    pose X : 'F[H]_(A :|: S_BpBpp) :=
      (((\1 : 'F[H]_A) \⊗ V) \o rhoAB \o
       (((\1 : 'F[H]_A) \⊗ V)^A)).
    pose Y : 'F[H]_(A :|: S_BpBpp) :=
      castlf (esym eqABpBpp, esym eqABpBpp)
        ((gamma_ABp \O tau) : 'F[H]_S_ABpBpp).
    have Htau_psd : tau \is psdlf := den1lf_psd Htau_den.
    have HW_iso : (((\1 : 'F[H]_A) \⊗ V) \is isolf).
    { apply/isolfP.
      by rewrite tenf_adj -tenf_comp ?disAB ?disA_BpBpp0 //
        isofE isofE tenf11. }
    have HWi :
        (((\1 : 'F[H]_A) \⊗ V)^A) \o
        ((\1 : 'F[H]_A) \⊗ V) = \1
      by move: HW_iso => /isolfP.
    have HV_cptp : formso V \is cptp by apply: is_cptp.
    have HV_cp : formso V \is cpmap := cptp_cpmap HV_cptp.
    have Hidcp : ((\:1 : 'SO[H]_A) \is cpmap)
      by exact: cptp_cpmap (idso_qc 'H[H]_A).
    have HXE : X = (((\:1 : 'SO[H]_A) :⊗ formso V) rhoAB).
    { have -> :
          ((\:1 : 'SO[H]_A) :⊗ formso V) =
          formso ((\1 : 'F[H]_A) \⊗ V)
        by rewrite -formso1 tenso_formso.
      by rewrite /X formsoE. }
    have HXpsd : X \is psdlf.
    { rewrite HXE (CPMap_BuildE Hidcp) (CPMap_BuildE HV_cp).
      exact: cp_psdP Prho. }
    have HXmx_psd : h2mx X \is psdmx by move: HXpsd; rewrite qualifE.
    have HX_tr_eq : \Tr X = \Tr rhoAB.
    { by rewrite /X lftraceC !comp_lfunA HWi comp_lfun1l. }
    have HX_mx_tr_le : @complex.Re R (\tr (h2mx X)) <= 1
      by move: Hrho; rewrite -HX_tr_eq /lftrace.
    have Hg_le : (0 : 'F[H]_S_ABp) ⊑ gamma_ABp.
    { by move: Hgamma_psdlf; rewrite psdlfE. }
    have Hb_le : (0 : 'F[H]_Bpp) ⊑ tau.
    { by move: Htau_psd; rewrite psdlfE. }
    have Hgt_psd : (gamma_ABp \O tau) \is psdlf.
    { have -> :
          ((gamma_ABp \O tau) : 'F[H]_S_ABpBpp) =
          ((gamma_ABp \⊗ tau) : 'F[H]_S_ABpBpp).
      { apply: to_Fnd_inj.
        by rewrite (sdotFT _ _ disABp_Bpp0) to_Fnd_tenE. }
      rewrite psdlfE.
      exact: tenf_ge0 disABp_Bpp0 Hg_le Hb_le. }
    have HYpsd : Y \is psdlf.
    { rewrite /Y. exact: castlf_psdlf Hgt_psd. }
    have HYmx_psd : h2mx Y \is psdmx by move: HYpsd; rewrite qualifE.
    have HY_tr1 : \Tr Y = 1.
    { rewrite /Y castlf_trlfE.
      have -> :
          ((gamma_ABp \O tau) : 'F[H]_S_ABpBpp) =
          ((gamma_ABp \⊗ tau) : 'F[H]_S_ABpBpp).
      { apply: to_Fnd_inj.
        by rewrite (sdotFT _ _ disABp_Bpp0) to_Fnd_tenE. }
      rewrite (lftrace_tenf gamma_ABp tau disABp_Bpp0).
      by rewrite (den1lf_trlf Hgamma_den1) (den1lf_trlf Htau_den) mul1r. }
    have HY_mx_tr1 : \tr (h2mx Y) = 1 by move: HY_tr1; rewrite /lftrace.
    rewrite /gfid.
    rewrite (gfid_sym_mx HXmx_psd HYmx_psd).
    rewrite (gfid_eq_fid_tr1_mx HYmx_psd HXmx_psd
               HY_mx_tr1 HX_mx_tr_le).
    rewrite /fidelity h2mx_comp !sqrtH_h2mx.
      exact: (fid_i_sym_mx HYmx_psd HXmx_psd). }
  (* Set equality between Eden and the gfid goal-set Eden_g.        *)
  pose Eden_g : set R := fun v : R =>
    exists (V : 'FI[H]_(B, S_BpBpp)),
      exists tau : 'F[H]_Bpp,
        [/\ tau \is den1lf &
            v =
            (gfid
               (((\1 : 'F[H]_A) \⊗ V) \o rhoAB \o
                (((\1 : 'F[H]_A) \⊗ V)^A))
               (castlf (esym eqABpBpp, esym eqABpBpp)
                 ((gamma_ABp \O tau) : 'F[H]_S_ABpBpp))) ^+ 2].
  have Hden_eq : Eden_g = Eden.
  { apply/funext=> v; apply/propext; split.
    - move=> [V [tau [Htau_den Hv]]]; exists V, tau; split=> //.
      by rewrite Hv (Hpt_den V tau Htau_den).
    - move=> [V [tau [Htau_den Hv]]]; exists V, tau; split=> //.
      by rewrite Hv -(Hpt_den V tau Htau_den). }
  (* The goal `sup Ecoh = sup Eden_g` becomes `sup Ecoh = sup Eden`.        *)
  change (sup Ecoh = sup Eden_g); rewrite Hden_eq.
  (* ---------------------------------------------------------------------- *)
  (* Hsup_le : sup Ecoh <= sup Eden.  Begin by establishing has_sup Eden.   *)
  (* The fixed-register isometry V0 + projector tau0 furnish a witness;     *)
  (* fidelity ≤ sqrt(Tr ρ_ext)·sqrt(Tr σ) ≤ 1 gives the uniform upper bound.*)
  (* ---------------------------------------------------------------------- *)
  have HEden_has_sup : has_sup Eden.
  { split.
    - pose nB := dim 'H[H]_B.
      pose nT := dim 'H[H]_S_BpBpp.
      have HleBT : (nB <= nT)%N.
      { rewrite /nB /nT (tenv_dim disBpBpp).
        have HBp_ge1 : (1 <= dim 'H[H]_Bp)%N := dim_proper.
        have Hleft : (dim 'H[H]_B <= dim 'H[H]_B * dim 'H[H]_Bp)%N
          by rewrite -{1}(muln1 (dim 'H[H]_B)); exact: leq_mul (leqnn _) HBp_ge1.
        have Hright : (dim 'H[H]_B * dim 'H[H]_Bp <=
                       dim 'H[H]_Bp * dim 'H[H]_Bpp)%N.
        { have HBpp_le : (dim 'H[H]_Bpp <= dim 'H[H]_Bp * dim 'H[H]_Bpp)%N
            by rewrite -{1}(mul1n (dim 'H[H]_Bpp)); exact: leq_mul HBp_ge1 (leqnn _).
          exact (leq_trans dimBpp_enough HBpp_le). }
        exact (leq_trans Hleft Hright). }
      pose R0 : 'M[C]_(nB, nB + (nT - nB)) :=
        row_mx (1%:M : 'M[C]_nB) (0 : 'M[C]_(nB, nT - nB)).
      pose RR : 'M[C]_(nB, nT) := castmx (erefl nB, subnKC HleBT) R0.
      have HR_unit : RR \is unitarymx.
      { rewrite /RR castmx_funE.
        exact: (row_mx0_unitarymx _ (unitarymx1 _ _)). }
      pose Vraw : 'Hom('H[H]_B, 'H[H]_S_BpBpp) := mx2h RR^*t.
      have Vraw_iso : Vraw \is isolf.
      { apply/isolfP; apply/h2mx_inj.
        rewrite h2mx_comp h2mx_adj mx2hK adjmxK h2mx1.
        exact: unitarymxK HR_unit. }
      pose V0 : 'FI[H]_(B, S_BpBpp) := IsoLf_Build Vraw_iso.
      pose psiBpp := (deltav (@idx_default R L H Bpp) : 'H[H]_Bpp).
      pose tau0 : 'F[H]_Bpp := [> psiBpp ; psiBpp <].
      have Htau0_den : tau0 \is den1lf
        by exact: proj1lf_den1 (outp_proj1 psiBpp).
      exists ((fidelity
        (((\1 : 'F[H]_A) \⊗ V0) \o rhoAB \o
         (((\1 : 'F[H]_A) \⊗ V0)^A))
        (castlf (esym eqABpBpp, esym eqABpBpp)
          ((gamma_ABp \O tau0) : 'F[H]_S_ABpBpp))) ^+ 2).
      exists V0, tau0; by split.
    - exists 1 => w [V [tau [Htau_den ->]]].
      pose rho_ext_raw : 'F[H]_(A :|: S_BpBpp) :=
        (((\1 : 'F[H]_A) \⊗ V) \o rhoAB \o
         (((\1 : 'F[H]_A) \⊗ V)^A)).
      pose sigma_ext : 'F[H]_S_ABpBpp := (gamma_ABp \O tau).
      pose sigma_raw : 'F[H]_(A :|: S_BpBpp) :=
        castlf (esym eqABpBpp, esym eqABpBpp) sigma_ext.
      have HV_cptp : formso V \is cptp by apply: is_cptp.
      have Hidcp : ((\:1 : 'SO[H]_A) \is cpmap)
        by exact: cptp_cpmap (idso_qc 'H[H]_A).
      have HV_cp : formso V \is cpmap := cptp_cpmap HV_cptp.
      have HW_iso : (((\1 : 'F[H]_A) \⊗ V) \is isolf).
      { apply/isolfP.
        by rewrite tenf_adj -tenf_comp ?disAB ?disA_BpBpp0 //
          isofE isofE tenf11. }
      have HWi :
          (((\1 : 'F[H]_A) \⊗ V)^A) \o
          ((\1 : 'F[H]_A) \⊗ V) = \1
        by move: HW_iso => /isolfP.
      have Hrho_extE :
          rho_ext_raw =
          (((\:1 : 'SO[H]_A) :⊗ formso V) rhoAB).
      { have -> :
            ((\:1 : 'SO[H]_A) :⊗ formso V) =
            formso ((\1 : 'F[H]_A) \⊗ V)
          by rewrite -formso1 tenso_formso.
        by rewrite /rho_ext_raw formsoE. }
      have Hrho_ext_psd : rho_ext_raw \is psdlf.
      { rewrite Hrho_extE (CPMap_BuildE Hidcp) (CPMap_BuildE HV_cp).
        exact: cp_psdP Prho. }
      have Htau_psd : tau \is psdlf := den1lf_psd Htau_den.
      have Hg2_le : (0 : 'F[H]_S_ABp) ⊑ gamma_ABp.
      { by move: Hgamma_psdlf; rewrite psdlfE. }
      have Hb2_le : (0 : 'F[H]_Bpp) ⊑ tau.
      { by move: Htau_psd; rewrite psdlfE. }
      have Hsigma_ext_psd : sigma_ext \is psdlf.
      { have -> :
            sigma_ext =
            ((gamma_ABp \⊗ tau) : 'F[H]_S_ABpBpp).
        { apply: to_Fnd_inj.
          by rewrite /sigma_ext (sdotFT _ _ disABp_Bpp0) to_Fnd_tenE. }
        rewrite psdlfE.
        exact: tenf_ge0 disABp_Bpp0 Hg2_le Hb2_le. }
      have Hsigma_raw_psd : sigma_raw \is psdlf.
      { rewrite /sigma_raw. exact: castlf_psdlf Hsigma_ext_psd. }
      have Hrho_ext_tr : @complex.Re R (\Tr rho_ext_raw) <= 1.
      { have Hrho_ext_trE : \Tr rho_ext_raw = \Tr rhoAB
          by rewrite /rho_ext_raw lftraceC !comp_lfunA HWi comp_lfun1l.
        by rewrite Hrho_ext_trE. }
      have Hsigma_raw_tr1 : \Tr sigma_raw = 1.
      { rewrite /sigma_raw castlf_trlfE.
        have -> :
            sigma_ext =
            ((gamma_ABp \⊗ tau) : 'F[H]_S_ABpBpp).
        { apply: to_Fnd_inj.
          by rewrite /sigma_ext (sdotFT _ _ disABp_Bpp0) to_Fnd_tenE. }
        rewrite (lftrace_tenf gamma_ABp tau disABp_Bpp0).
        by rewrite (den1lf_trlf Hgamma_den1) (den1lf_trlf Htau_den) mul1r. }
      have Hfid_ge0 : 0 <= fidelity rho_ext_raw sigma_raw.
      { rewrite /fidelity.
        have /= := trnorm_ge0 (h2mx (sqrtH rho_ext_raw \o sqrtH sigma_raw)).
        by rewrite lecE /= => /andP[]. }
      have Hrho_ext_mx_psd : h2mx rho_ext_raw \is psdmx
        by move: Hrho_ext_psd; rewrite qualifE.
      have Hsigma_raw_mx_psd : h2mx sigma_raw \is psdmx
        by move: Hsigma_raw_psd; rewrite qualifE.
      have Hfid_le_tr :
          fidelity rho_ext_raw sigma_raw <=
          Num.sqrt (@complex.Re R (\Tr rho_ext_raw)) *
          Num.sqrt (@complex.Re R (\Tr sigma_raw)).
      { rewrite /fidelity /lftrace h2mx_comp !sqrtH_h2mx.
        exact: fid_le_tr_mx Hrho_ext_mx_psd Hsigma_raw_mx_psd. }
      have Hfid_le1 : fidelity rho_ext_raw sigma_raw <= 1.
      { have Hsqrt_le1 : Num.sqrt (@complex.Re R (\Tr rho_ext_raw)) <= 1
          by rewrite -sqrtr1; exact: ler_wsqrtr Hrho_ext_tr.
        move: Hfid_le_tr.
        rewrite Hsigma_raw_tr1 /= sqrtr1 mulr1 => Htmp.
        exact: le_trans Htmp Hsqrt_le1. }
      have Hsq_le :
          (fidelity rho_ext_raw sigma_raw) ^+ 2 <= 1 ^+ 2
        by exact: (@lerXn2r R 2 _ 1 Hfid_ge0 ler01 Hfid_le1).
      by rewrite expr1n in Hsq_le. }
  (* ---------------------------------------------------------------------- *)
  (* HEcoh_has_sup : has_sup Ecoh.                                          *)
  (* The TP-CPM witness set Ecoh is nonempty (use the constant-state Kraus  *)
  (* family K_i = |psiB'><i|) and bounded above by 1 (fidelity ≤            *)
  (* sqrt(Tr ρ)·sqrt(Tr γ) ≤ 1 since γ_AB' is den1 and the CPTP image of   *)
  (* a subnormalised ρ has trace ≤ 1).                                     *)
  (* ---------------------------------------------------------------------- *)
  have HEcoh_has_sup : has_sup Ecoh.
  { split.
    - pose psiB' := (deltav (@idx_default R L H Bp) : 'H[H]_Bp).
      pose K (i : 'Idx[H]_B) :
          'Hom('H[H]_B, 'H[H]_Bp) :=
        [> psiB' ; deltav i : 'H[H]_B <].
      have HKtp : trace_presv K.
      { rewrite /trace_presv; apply/eqP.
        under eq_bigr do
          rewrite adj_outp outp_comp ns_dot scale1r.
        by rewrite sumonb_out. }
      have HEcptp : (krausso K : 'SO[H]_(B, Bp)) \is cptp
        by apply/krausso_qcP; exact: HKtp.
      exists ((fidelity
        (((\:1 : 'SO[H]_A) :⊗
            (krausso K : 'SO[H]_(B, Bp))) rhoAB)
        gamma_ABp) ^+ 2).
      by exists (krausso K : 'SO[H]_(B, Bp)); split.
    - exists 1 => w [E [HEcptp ->]].
      pose Eqc : 'QC[H]_(B, Bp) := QChannel_Build HEcptp.
      have HEfull_cptp :
          ((((\:1 : 'SO[H]_A) :⊗
              (Eqc : 'SO[H]_(B, Bp)))
             : 'SO[H]_(S_AB, S_ABp)) \is cptp) by exact: is_cptp.
      have HEfull_cp :
          (((\:1 : 'SO[H]_A) :⊗
            (Eqc : 'SO[H]_(B, Bp))) \is cpmap) :=
        cptp_cpmap HEfull_cptp.
      have HEfull_tp :
          (((\:1 : 'SO[H]_A) :⊗
            (Eqc : 'SO[H]_(B, Bp))) \is tpmap) :=
        cptp_tpmap HEfull_cptp.
      have Hout_psd :
          (((\:1 : 'SO[H]_A) :⊗
            (Eqc : 'SO[H]_(B, Bp))) rhoAB) \is psdlf.
      { rewrite (CPMap_BuildE HEfull_cp); exact: cp_psdP Prho. }
      have Hout_tr :
          @complex.Re R
            (\Tr ((((\:1 : 'SO[H]_A) :⊗
                  (Eqc : 'SO[H]_(B, Bp))) rhoAB))) <= 1.
      { move/tpmapP: HEfull_tp => HEtp.
        by rewrite (HEtp rhoAB). }
      have Hfid_ge0 :
          0 <= fidelity
            ((((\:1 : 'SO[H]_A) :⊗
                (Eqc : 'SO[H]_(B, Bp))) rhoAB))
            gamma_ABp.
      { rewrite /fidelity.
        have /= := trnorm_ge0
          (h2mx (sqrtH
            ((((\:1 : 'SO[H]_A) :⊗
                (Eqc : 'SO[H]_(B, Bp))) rhoAB)) \o
            sqrtH gamma_ABp)).
        by rewrite lecE /= => /andP[]. }
      pose outE :=
        ((((\:1 : 'SO[H]_A) :⊗
            (Eqc : 'SO[H]_(B, Bp))) rhoAB)).
      have Hout_mx_psd : h2mx outE \is psdmx
        by rewrite /outE; move: Hout_psd; rewrite qualifE.
      have Hfid_le_tr :
          fidelity outE gamma_ABp <=
          Num.sqrt (@complex.Re R (\Tr outE)) *
          Num.sqrt (@complex.Re R (\Tr gamma_ABp)).
      { rewrite /fidelity /lftrace h2mx_comp !sqrtH_h2mx.
        exact: fid_le_tr_mx Hout_mx_psd Hgamma_mx_psd. }
      have Hfid_le1 :
          fidelity
            ((((\:1 : 'SO[H]_A) :⊗
                (Eqc : 'SO[H]_(B, Bp))) rhoAB))
            gamma_ABp <= 1.
      { have Hsqrt_le1 :
            Num.sqrt (@complex.Re R
              (\Tr ((((\:1 : 'SO[H]_A) :⊗
                    (Eqc : 'SO[H]_(B, Bp))) rhoAB)))) <= 1
          by rewrite -sqrtr1; exact: ler_wsqrtr Hout_tr.
        move: Hfid_le_tr.
        rewrite (den1lf_trlf Hgamma_den1) /= sqrtr1 mulr1.
        move=> Htmp.
        exact: le_trans Htmp Hsqrt_le1. }
      have Hsq_le :
          (fidelity
             ((((\:1 : 'SO[H]_A) :⊗
                 (Eqc : 'SO[H]_(B, Bp))) rhoAB))
             gamma_ABp) ^+ 2 <= 1 ^+ 2
        by exact: (@lerXn2r R 2 _ 1 Hfid_ge0 ler01 Hfid_le1).
      by rewrite expr1n in Hsq_le. }
  (* Hsup_le : sup Ecoh <= sup Eden.
     Per-CPTP-witness reduction: build Stinespring isometry V via the
     matrix dilation pipeline W -> R0/R -> G -> T -> Wten -> Wlbl -> V,
     then apply Hproc_eqV + pd_ext + pure_extension_split.                  *)
  have Hsup_le : sup Ecoh <= sup Eden.
  { apply: ExtNumTopology.sup_least_ubound; first exact: HEcoh_has_sup.
    move=> v [E [HEcptp ->]].
    pose Eqc : 'QC[H]_(B, Bp) := QChannel_Build HEcptp.
    pose sigma : 'F[H]_S_ABp :=
      (((\:1 : 'SO[H]_A) :⊗
        (Eqc : 'SO[H]_(B, Bp))) rhoAB).
    have Hsigma_cptp : ((((\:1 : 'SO[H]_A) :⊗
        (Eqc : 'SO[H]_(B, Bp)))
        : 'SO[H]_(S_AB, S_ABp)) \is cptp) by exact: is_cptp.
    have Hsigma_psd : sigma \is psdlf
      by rewrite /sigma (CPMap_BuildE (cptp_cpmap Hsigma_cptp));
         exact: cp_psdP Prho.
    have Hsigma_tr_le : @complex.Re R (\Tr sigma) <= 1.
    { by move/tpmapP: (cptp_tpmap Hsigma_cptp) => Htp; rewrite /sigma Htp. }
    (* Stinespring witness on the chosen B'' system. *)
    have [V Hptr] :
        exists V : 'FI[H]_(B, S_BpBpp),
          @ptrace_cast R L H S_ABp Bpp disABp_Bpp0
            (castlf (eqABpBpp, eqABpBpp)
              ((((\1 : 'F[H]_A) \⊗ V) \o rhoAB \o
                (((\1 : 'F[H]_A) \⊗ V)^A))
                 : 'F[H]_(A :|: S_BpBpp))) = sigma.
    { have HEcp : (Eqc : 'SO[H]_(B, Bp)) \is cpmap :=
        cptp_cpmap HEcptp.
      pose nB := dim 'H[H]_B.
      pose nBp := dim 'H[H]_Bp.
      pose nBpp := dim 'H[H]_Bpp.
      pose z := nB * nBp.
      pose Ec := CPMap_Build HEcp.
      pose K (k : 'I_z) := krausop Ec k.
      pose W : 'M[C]_(nBp * z, nB) :=
        \matrix_(r, c) let rc := mxtens_unindex r : 'I_nBp * 'I_z in
          (h2mx (K rc.2)) rc.1 c.
      have HKfun : K = krausop Ec by apply/funext => k; rewrite /K.
      have HWadj : W^*t *m W = \sum_k (h2mx (K k))^*t *m h2mx (K k).
      { apply/matrixP => a b; rewrite mxE.
        transitivity (\sum_(i : 'I_nBp) \sum_(k : 'I_z)
          (W^*t) a (mxtens_index (i, k)) * W (mxtens_index (i, k)) b).
        { rewrite (reindex (@mxtens_index nBp z)) /=.
          2: (exists (@mxtens_unindex nBp z) => l /=;
             by rewrite ?mxtens_indexK ?mxtens_unindexK -?surjective_pairing).
          by rewrite pair_bigV /=. }
        transitivity (\sum_(i : 'I_nBp) \sum_(k : 'I_z)
          ((h2mx (K k))^*t) a i * (h2mx (K k)) i b).
        { apply: eq_bigr => i _; apply: eq_bigr => k _.
          by rewrite !adjmxE /W !mxE !mxtens_indexK. }
        rewrite exchange_big summxE; apply: eq_bigr => k _.
        rewrite mxE; by apply: eq_bigr => i _; rewrite !mxE. }
      have ptrace2E' : forall s t (B0 : 'M[C]_(s * t)) r1 r2,
          (ptrace2 B0) r1 r2 =
          \sum_(l : 'I_t) B0 (mxtens_index (r1, l)) (mxtens_index (r2, l)).
      { move=> s t B0 r1 r2; rewrite ptrace2E1 ptrace1E.
        by apply: eq_bigr => l _; rewrite mxE !mxtens_indexK. }
      have HptrW : forall rho : 'M[C]_nB,
          ptrace2 (W *m rho *m W^*t) =
          \sum_k h2mx (K k) *m rho *m (h2mx (K k))^*t.
      { move=> rho; apply/matrixP => i j.
        rewrite ptrace2E' summxE; apply: eq_bigr => k _.
        rewrite !mxE; apply: eq_bigr => a _.
        have Hadj : (W^*t) a (mxtens_index (j, k)) =
                    ((h2mx (K k))^*t) a j
          by rewrite !adjmxE /W !mxE !mxtens_indexK.
        have HWrho : (W *m rho) (mxtens_index (i, k)) a =
                     (h2mx (K k) *m rho) i a.
        { rewrite !mxE; by apply: eq_bigr => b _;
            rewrite /W !mxE !mxtens_indexK. }
        by rewrite Hadj HWrho. }
      have Hact : forall rho : 'M[C]_nB,
          h2mx (Eqc (mx2h rho)) = ptrace2 (W *m rho *m W^*t).
      { move=> rho.
        have HEval : h2mx (Eqc (mx2h rho)) = h2mx (Ec (mx2h rho)).
        { move: (CPMap_BuildE HEcp).
          by move/(congr1 (fun G : 'SO('H[H]_B, 'H[H]_Bp) =>
            h2mx (G (mx2h rho)))). }
        rewrite HEval HptrW (krausE Ec (mx2h rho)) raddf_sum.
        apply: eq_bigr => k _.
        by rewrite /= !h2mx_comp h2mx_adj mx2hK. }
      have HWiso : W^*t *m W = 1%:M.
      { have HEtpEc : (Ec : 'SO('H[H]_B, 'H[H]_Bp)) \is tpmap
          by rewrite -(CPMap_BuildE HEcp); exact: cptp_tpmap HEcptp.
        have HEc_k : (Ec : 'SO('H[H]_B, 'H[H]_Bp)) = krausso K
          by rewrite HKfun; exact: krausopE.
        move: HEtpEc.
        rewrite HEc_k krausso_tpE /trace_presv => /eqP HKtp.
        rewrite HWadj.
        transitivity (h2mx (\sum_k ((K k)^A \o K k))).
        { rewrite raddf_sum; apply: eq_bigr => k _.
          by rewrite /= h2mx_comp h2mx_adj. }
        by rewrite HKtp h2mx1. }
      have Hle_z : (z <= nBpp)%N.
      { rewrite /z /nB /nBp /nBpp.
        exact: dimBpp_enough. }
      pose R0 : 'M[C]_(z, z + (nBpp - z)) :=
        row_mx (1%:M : 'M[C]_z) (0 : 'M[C]_(z, nBpp - z)).
      pose RR : 'M[C]_(z, nBpp) := castmx (erefl z, subnKC Hle_z) R0.
      have HR_unit : RR \is unitarymx.
      { rewrite /RR castmx_funE.
        exact: (row_mx0_unitarymx _ (unitarymx1 _ _)). }
      pose G : 'M[C]_(nBpp, z) := RR^*t.
      have HGG : G^*t *m G = 1%:M
        by rewrite /G adjmxK; exact: unitarymxK HR_unit.
      pose T : 'M[C]_(nBp * nBpp, nBp * z) := ((1%:M : 'M[C]_nBp) *t G).
      have HTadj_unit : T^*t \is unitarymx.
      { rewrite /T adjmx_tens adjmx1 /G adjmxK.
        apply: unitarymx_tens; [exact: unitarymx1 | exact: HR_unit]. }
      have HTiso : T^*t *m T = 1%:M.
      { by have := unitarymxK HTadj_unit; rewrite adjmxK. }
      pose Wten : 'M[C]_(nBp * nBpp, nB) := T *m W.
      pose UU := @tenv_mxU R L H Bp Bpp.
      have HUadj : UU^*t \is unitarymx :=
        tenv_mxU_adj_unitarymx disBpBpp.
      have Uadj_mul_U : UU^*t *m UU = 1%:M.
      { by have := unitarymxK HUadj; rewrite adjmxK. }
      pose Wlbl : 'M[C]_(dim 'H[H]_S_BpBpp, nB) := UU *m Wten.
      pose Vraw : 'Hom('H[H]_B, 'H[H]_S_BpBpp) := mx2h Wlbl.
      have Vraw_iso : Vraw \is isolf.
      { apply/isolfP; apply/h2mx_inj.
        rewrite h2mx_comp h2mx_adj /Vraw mx2hK h2mx1.
        have -> : Wlbl^*t *m Wlbl = Wten^*t *m (UU^*t *m UU) *m Wten
          by rewrite /Wlbl adjmxM -!mulmxA.
        rewrite Uadj_mul_U mulmx1.
        have -> : Wten^*t *m Wten = W^*t *m (T^*t *m T) *m W
          by rewrite /Wten adjmxM -!mulmxA.
        have -> : W^*t *m (T^*t *m T) *m W = W^*t *m W
          by rewrite HTiso -mulmxA mul1mx.
        exact: HWiso. }
      pose V : 'FI[H]_(B, S_BpBpp) := IsoLf_Build Vraw_iso.
      pose PTqc0 : 'QC[H]_(S_BpBpp, S_BpBpp :\: Bpp) :=
        QChannel_Build (@ptraceso_qc R L H Bpp S_BpBpp).
      pose PTqc : 'QC[H]_(S_BpBpp, Bp) :=
        castso (erefl _, setDU_r disBpBpp) PTqc0.
      have HEqcV :
          ((PTqc : 'SO[H]_(S_BpBpp, Bp)) :o formso V) = Eqc.
      { apply/superopP => X; apply/h2mx_inj.
        pose rho := h2mx X.
        have -> : X = mx2h rho by rewrite /rho h2mxK.
        rewrite comp_soE /PTqc castsoE /=.
        rewrite (QChannel_BuildE (@ptraceso_qc R L H Bpp S_BpBpp)).
        rewrite /ptrace_cast /ptrace_cast_gen.
        rewrite (h2mx_ptrace_cast_ptrace2 disBpBpp (formso V (mx2h rho))).
        have Hform_mx :
            h2mx (formso V (mx2h rho)) = Wlbl *m rho *m Wlbl^*t
          by rewrite formsoE !h2mx_comp h2mx_adj /V /Vraw !mx2hK.
        rewrite Hform_mx.
        have HWlblE : Wlbl *m rho *m Wlbl^*t =
                      UU *m (Wten *m rho *m Wten^*t) *m UU^*t
          by rewrite /Wlbl adjmxM !mulmxA.
        rewrite HWlblE.
        rewrite !mulmxA Uadj_mul_U mul1mx -mulmxA Uadj_mul_U mulmx1.
        have -> : Wten *m rho *m Wten^*t =
                  ((T *m (W *m rho *m W^*t)) *m T^*t)
          by rewrite /Wten adjmxM !mulmxA.
        rewrite /T.
        rewrite (Hptrace2_conj_tens_right_iso
          nBp z nBpp G (W *m rho *m W^*t) HGG).
        by rewrite (Hact rho). }
      exists V; symmetry.
      have Hpe := Hproc_eqV V.
      rewrite -/PTqc0 -/PTqc HEqcV /sigma in Hpe.
      exact: Hpe. }
    (* Build rho_ext (purified extension) and use pd_ext + pure_extension_split. *)
    pose rho_ext_raw : 'F[H]_(A :|: S_BpBpp) :=
      (((\1 : 'F[H]_A) \⊗ V) \o rhoAB \o
       (((\1 : 'F[H]_A) \⊗ V)^A)).
    pose rho_ext : 'F[H]_S_ABpBpp :=
      castlf (eqABpBpp, eqABpBpp) rho_ext_raw.
    have HW_iso : (((\1 : 'F[H]_A) \⊗ V) \is isolf).
    { apply/isolfP.
      by rewrite tenf_adj -tenf_comp ?disAB ?disA_BpBpp0 //
        isofE isofE tenf11. }
    have HWi : (((\1 : 'F[H]_A) \⊗ V)^A) \o
        ((\1 : 'F[H]_A) \⊗ V) = \1
      by move: HW_iso => /isolfP.
    have Hrho_ext_psd : rho_ext \is psdlf.
    { rewrite /rho_ext; apply: castlf_psdlf.
      have HV_cp : formso V \is cpmap := cptp_cpmap (is_cptp _).
      have Hidcp : ((\:1 : 'SO[H]_A) \is cpmap)
        by exact: cptp_cpmap (idso_qc 'H[H]_A).
      have -> : rho_ext_raw =
            (((\:1 : 'SO[H]_A) :⊗ formso V) rhoAB).
      { have -> : ((\:1 : 'SO[H]_A) :⊗ formso V) =
                  formso ((\1 : 'F[H]_A) \⊗ V)
          by rewrite -formso1 tenso_formso.
        by rewrite /rho_ext_raw formsoE. }
      rewrite (CPMap_BuildE Hidcp) (CPMap_BuildE HV_cp).
      exact: cp_psdP Prho. }
    have Hrho_ext_trE : \Tr rho_ext = \Tr rhoAB
      by rewrite /rho_ext castlf_trlfE /rho_ext_raw
                 lftraceC !comp_lfunA HWi comp_lfun1l.
    have Hrho_ext_tr_le : @complex.Re R (\Tr rho_ext) <= 1
      by rewrite Hrho_ext_trE.
    have Hrho_ext_den : rho_ext \is denlf.
    { apply/denlfP; split=> //.
      have Hreal : \Tr rho_ext \is Num.real
        by exact: ger0_real (psdlf_trlf Hrho_ext_psd).
      by rewrite -(RRe_real Hreal) lecR. }
    have Hgamma_rank1 : \Rank gamma_ABp = 1%N
      by exact: gamma_state_rank1.
    have [taubar [Htaubar_den [Htaubar_ptr Htaubar_pd]]] :=
      @pd_ext R L H S_ABp Bpp disABp_Bpp0 sigma gamma_ABp rho_ext
        Hrho_ext_den Hptr (den1lf_den Hgamma_den1).
    have Htaubar_den1 : taubar \is den1lf.
    { apply/den1lfP; split; first by move/denlfP: Htaubar_den => [].
      have /cptpP [_ /tpmapP Htp] := @ptraceso_qc R L H Bpp S_ABpBpp.
      have Htr_eq : \Tr taubar =
                    \Tr (@ptrace_cast R L H S_ABp Bpp disABp_Bpp0 taubar)
        by rewrite /ptrace_cast /ptrace_cast_gen castlf_trlfE Htp.
      by rewrite Htr_eq Htaubar_ptr (den1lf_trlf Hgamma_den1). }
    have [tau [Htau_den Htaubar_split]] :=
      @pure_extension_split R L H A Bp Bpp disABp_Bpp0
        gamma_ABp taubar
        Hgamma_den1 Hgamma_rank1 Htaubar_den1 Htaubar_ptr.
    have Htaubar_target :
        taubar = ((gamma_ABp \O tau) : 'F[H]_S_ABpBpp).
    { rewrite Htaubar_split.
      by rewrite (eq_irrelevance (esym _) (erefl S_ABpBpp)) castlf_id. }
    have Htaubar_psd : taubar \is psdlf := den1lf_psd Htaubar_den1.
    have Hgamma_psd : gamma_ABp \is psdlf := den1lf_psd Hgamma_den1.
    (* gfid = fidelity when the right side is den1 (trace 1).      *)
    have Hgfid_eq_fid : forall (S : {set L}) (x y : 'F[H]_S),
        x \is psdlf -> y \is den1lf -> gfid x y = fidelity x y.
    { move=> S x y Hx Hyd.
      have Hy : y \is psdlf := den1lf_psd Hyd.
      have Hxm : h2mx x \is psdmx by move: Hx; rewrite qualifE.
      have Hym : h2mx y \is psdmx by move: Hy; rewrite qualifE.
      have Hytr1 : \tr (h2mx y) = 1
        by move: (den1lf_trlf Hyd); rewrite /lftrace.
      rewrite /gfid (alt_gfid_gen Hxm Hym).
      have -> : @complex.Re R
          (trnorm (sqrtmx (h2mx x) *m sqrtmx (h2mx y))) = fidelity x y
        by rewrite /fidelity !h2mx_comp !sqrtH_h2mx.
        have -> : @complex.Re R (1 - \tr (h2mx y)) = 0
          by rewrite raddfB /= Hytr1 subrr.
      by rewrite sqrtr0 mulr0 addr0. }
    have Hgfid_ext := Hgfid_eq_fid _ _ taubar Hrho_ext_psd Htaubar_den1.
    have Hgfid_sig := Hgfid_eq_fid _ _ gamma_ABp Hsigma_psd Hgamma_den1.
    have Hfid_eq : fidelity rho_ext taubar = fidelity sigma gamma_ABp.
    { have Hpd_eq : Num.sqrt (1 - (fidelity rho_ext taubar) ^+ 2) =
                    Num.sqrt (1 - (fidelity sigma gamma_ABp) ^+ 2)
        by move: Htaubar_pd; rewrite /pur_dist Hgfid_ext Hgfid_sig.
      have Hfid_ge0 : forall (S0 : {set L}) (x y : 'F[H]_S0),
          0 <= fidelity x y.
      { move=> S0 x y; rewrite /fidelity.
        have /= := trnorm_ge0 (h2mx (sqrtH x \o sqrtH y)).
        by rewrite lecE /= => /andP[]. }
      have Htbar_tr_le : @complex.Re R (\Tr taubar) <= 1
        by rewrite (den1lf_trlf Htaubar_den1).
      have Hgamma_tr_le : @complex.Re R (\Tr gamma_ABp) <= 1
        by rewrite (den1lf_trlf Hgamma_den1).
        have Hf1le : gfid rho_ext taubar <= 1.
        {
          rewrite /gfid.
          have Hrho_ext_mx_den : h2mx rho_ext \is denmx.
          { apply: denmx_psd_re_tr_le; first by move: Hrho_ext_psd; rewrite qualifE.
            exact: Hrho_ext_tr_le. }
          have Htaubar_mx_den : h2mx taubar \is denmx.
          { apply: denmx_psd_re_tr_le; first by move: Htaubar_psd; rewrite qualifE.
            exact: Htbar_tr_le. }
          exact: gfid_le1_mx Hrho_ext_mx_den Htaubar_mx_den.
        }
      rewrite Hgfid_ext in Hf1le.
        have Hf2le : gfid sigma gamma_ABp <= 1.
        {
          rewrite /gfid.
          have Hsigma_mx_den : h2mx sigma \is denmx.
          { apply: denmx_psd_re_tr_le; first by move: Hsigma_psd; rewrite qualifE.
            exact: Hsigma_tr_le. }
          have Hgamma_mx_den : h2mx gamma_ABp \is denmx.
          { apply: denmx_psd_re_tr_le; first by move: Hgamma_psd; rewrite qualifE.
            exact: Hgamma_tr_le. }
          exact: gfid_le1_mx Hsigma_mx_den Hgamma_mx_den.
        }
      rewrite Hgfid_sig in Hf2le.
      have Hsq_eq : 1 - (fidelity rho_ext taubar) ^+ 2 =
                    1 - (fidelity sigma gamma_ABp) ^+ 2.
      { have := congr1 (fun x : R => x ^+ 2) Hpd_eq.
        rewrite !sqr_sqrtr ?subr_ge0 //;
          first by have := @lerXn2r R 2 _ 1 (Hfid_ge0 _ _ _) ler01 Hf2le;
            rewrite expr1n.
        by have := @lerXn2r R 2 _ 1 (Hfid_ge0 _ _ _) ler01 Hf1le;
          rewrite expr1n. }
      have Hinj : injective (fun x : R => 1 - x)
        by apply: (can_inj (g := fun x : R => 1 - x))=> x;
          rewrite opprB addrCA subrr addr0.
      have Hfid_sq := Hinj _ _ Hsq_eq.
      have := congr1 Num.sqrt Hfid_sq.
      by rewrite !sqrtr_sqr !ger0_norm ?Hfid_ge0. }
    have Hsq_cast_gen : forall (raw : 'F[H]_(A :|: S_BpBpp))
                               (sig : 'F[H]_S_ABpBpp),
        (fidelity (castlf (eqABpBpp, eqABpBpp) raw) sig) ^+ 2 =
        (fidelity raw (castlf (esym eqABpBpp, esym eqABpBpp) sig)) ^+ 2
      by move=> raw sig; case: _ / eqABpBpp in raw sig *; rewrite !castlf_id.
    have /ubP HEden_ub := sup_upper_bound HEden_has_sup.
    apply: HEden_ub; exists V, tau; split; first exact: Htau_den.
    by rewrite -Hfid_eq Htaubar_target Hsq_cast_gen. }
  (* ---------------------------------------------------------------------- *)
  (* Hsup_ge : sup Eden <= sup Ecoh.                                        *)
  (* Per-Eden-witness `(V, tau)`: build the TP-CPM channel                  *)
  (* `E := PTqc :o formso V` (post-isometry then partial-trace over B'').   *)
  (* Use `Hproc_eqV V` to identify `(\:1 ⊗ E) rhoAB` with                    *)
  (* `ptrace_cast (cast ((1\⊗V)∘rhoAB∘(1\⊗V)^A))`, then partial-trace        *)
  (* monotonicity of fidelity (`fid_ii_cptp_bounds` with the full PT      *)
  (* over B'' on A B' B'') gives the witness inequality, finally collapsed *)
  (* through `Hsq_cast_gen` (already in D7 scope).                          *)
  (* ---------------------------------------------------------------------- *)
  have Hsup_ge : sup Eden <= sup Ecoh.
  { apply: ExtNumTopology.sup_least_ubound; first exact: HEden_has_sup.
    move=> v [V [tau [Htau_den ->]]].
    pose PTqc0 : 'QC[H]_(S_BpBpp, S_BpBpp :\: Bpp) :=
      QChannel_Build (@ptraceso_qc R L H Bpp S_BpBpp).
    pose PTqc : 'QC[H]_(S_BpBpp, Bp) :=
      castso (erefl _, setDU_r disBpBpp) PTqc0.
    pose E : 'QC[H]_(B, Bp) := PTqc :o formso V.
    pose rho_ext_raw : 'F[H]_(A :|: S_BpBpp) :=
      (((\1 : 'F[H]_A) \⊗ V) \o rhoAB \o
       (((\1 : 'F[H]_A) \⊗ V)^A)).
    pose rho_ext : 'F[H]_S_ABpBpp :=
      castlf (eqABpBpp, eqABpBpp) rho_ext_raw.
    pose sigma_ext : 'F[H]_S_ABpBpp := (gamma_ABp \O tau).
    have Hsq_cast_gen :
        forall (raw : 'F[H]_(A :|: S_BpBpp))
               (sig : 'F[H]_S_ABpBpp),
          (fidelity raw
             (castlf (esym eqABpBpp, esym eqABpBpp) sig)) ^+ 2 =
          (fidelity (castlf (eqABpBpp, eqABpBpp) raw) sig) ^+ 2
      by move=> raw sig; case: _ / eqABpBpp in raw sig *; rewrite !castlf_id.
    have Hsq_cast :
        (fidelity rho_ext_raw
           (castlf (esym eqABpBpp, esym eqABpBpp) sigma_ext)) ^+ 2 =
        (fidelity rho_ext sigma_ext) ^+ 2
      by exact: Hsq_cast_gen rho_ext_raw sigma_ext.
    have HEcptp : (E : 'SO[H]_(B, Bp)) \is cptp by exact: is_cptp.
    have HV_cptp : formso V \is cptp by apply: is_cptp.
    have HV_cp : formso V \is cpmap := cptp_cpmap HV_cptp.
    have Hidcp : ((\:1 : 'SO[H]_A) \is cpmap)
      by exact: cptp_cpmap (idso_qc 'H[H]_A).
    have Hext_psd : rho_ext \is psdlf.
    { rewrite /rho_ext; apply: castlf_psdlf.
      have HextE_raw :
          rho_ext_raw =
          (((\:1 : 'SO[H]_A) :⊗ formso V) rhoAB).
      { have -> :
            ((\:1 : 'SO[H]_A) :⊗ formso V) =
            formso ((\1 : 'F[H]_A) \⊗ V)
          by rewrite -formso1 tenso_formso.
        by rewrite /rho_ext_raw formsoE. }
      rewrite HextE_raw (CPMap_BuildE Hidcp) (CPMap_BuildE HV_cp).
      exact: cp_psdP Prho. }
    have Htau_psd : tau \is psdlf := den1lf_psd Htau_den.
    have Hg3_le : (0 : 'F[H]_S_ABp) ⊑ gamma_ABp.
    { by move: Hgamma_psdlf; rewrite psdlfE. }
    have Hb3_le : (0 : 'F[H]_Bpp) ⊑ tau.
    { by move: Htau_psd; rewrite psdlfE. }
    have Htarget_psd : sigma_ext \is psdlf.
    { have -> :
          sigma_ext =
          ((gamma_ABp \⊗ tau) : 'F[H]_S_ABpBpp).
      { apply: to_Fnd_inj.
        by rewrite /sigma_ext (sdotFT _ _ disABp_Bpp0) to_Fnd_tenE. }
      rewrite psdlfE.
      exact: tenf_ge0 disABp_Bpp0 Hg3_le Hb3_le. }
    have Hproc_eq :
        (((\:1 : 'SO[H]_A) :⊗ (E : 'SO[H]_(B, Bp))) rhoAB) =
        @ptrace_cast R L H S_ABp Bpp disABp_Bpp0 rho_ext.
    { have Hpe := Hproc_eqV V.
      rewrite /E /PTqc /PTqc0 /rho_ext /rho_ext_raw in Hpe.
      exact: Hpe. }
    have Htarget_ptr :
        @ptrace_cast R L H S_ABp Bpp disABp_Bpp0 sigma_ext = gamma_ABp.
    { have Hten :
          sigma_ext = ((gamma_ABp \⊗ tau) : 'F[H]_S_ABpBpp).
      { apply: to_Fnd_inj.
        by rewrite /sigma_ext (sdotFT _ _ disABp_Bpp0) to_Fnd_tenE. }
      apply: h2mx_inj.
      rewrite Hten (h2mx_ptrace_cast_ptrace2 disABp_Bpp0
        ((gamma_ABp \⊗ tau) : 'F[H]_S_ABpBpp)).
      rewrite h2mx_tenf.
      pose UU := @tenv_mxU R L H S_ABp Bpp.
      have HUadj : UU^*t \is unitarymx := tenv_mxU_adj_unitarymx disABp_Bpp0.
      have Uadj_mul_U : UU^*t *m UU = 1%:M
        by have := unitarymxK HUadj; rewrite adjmxK.
      have Htau_tr1_mx : \tr (h2mx tau) = 1
        by move: (den1lf_trlf Htau_den); rewrite /lftrace.
      rewrite !mulmxA Uadj_mul_U mul1mx -mulmxA Uadj_mul_U mulmx1.
      rewrite ptrace_tensmx h2mxZ_lf /lftrace.
      by rewrite Htau_tr1_mx scale1r. }
    have Hmono :
        fidelity rho_ext sigma_ext <=
        fidelity (((\:1 : 'SO[H]_A) :⊗
                   (E : 'SO[H]_(B, Bp))) rhoAB) gamma_ABp.
    { pose PTfull0 : 'QC[H]_(S_ABpBpp, S_ABpBpp :\: Bpp) :=
        QChannel_Build (@ptraceso_qc R L H Bpp S_ABpBpp).
      pose PTfull : 'QC[H]_(S_ABpBpp, S_ABp) :=
        castso (erefl _, setDU_r disABp_Bpp0) PTfull0.
      have Hpt_cptp : (PTfull : 'SO[H]_(S_ABpBpp, S_ABp)) \is cptp
        by exact: is_cptp.
      have Hmono_full :
          fidelity rho_ext sigma_ext <=
          fidelity (PTfull rho_ext) (PTfull sigma_ext)
        by exact: (proj1 (fid_ii_cptp_bounds Hext_psd Htarget_psd Hpt_cptp)).
      have HPTfull_rho :
          PTfull rho_ext =
          @ptrace_cast R L H S_ABp Bpp disABp_Bpp0 rho_ext.
      { rewrite /PTfull castsoE /=.
        rewrite (QChannel_BuildE (@ptraceso_qc R L H Bpp S_ABpBpp)).
        by rewrite /ptrace_cast /ptrace_cast_gen. }
      have HPTfull_sigma :
          PTfull sigma_ext =
          @ptrace_cast R L H S_ABp Bpp disABp_Bpp0 sigma_ext.
      { rewrite /PTfull castsoE /=.
        rewrite (QChannel_BuildE (@ptraceso_qc R L H Bpp S_ABpBpp)).
        by rewrite /ptrace_cast /ptrace_cast_gen. }
      rewrite HPTfull_rho HPTfull_sigma in Hmono_full.
      by rewrite -Hproc_eq Htarget_ptr in Hmono_full. }
    have Hv_mem :
        Ecoh
          ((fidelity (((\:1 : 'SO[H]_A) :⊗
                       (E : 'SO[H]_(B, Bp))) rhoAB)
             gamma_ABp) ^+ 2)
      by exists (E : 'SO[H]_(B, Bp)); split.
    have /ubP HEcoh_ub := sup_upper_bound HEcoh_has_sup.
    have Hfid_ge0_local :
        forall (S0 : {set L}) (x y : 'F[H]_S0), 0 <= fidelity x y.
    { move=> S0 x y; rewrite /fidelity.
      have /= := trnorm_ge0 (h2mx (sqrtH x \o sqrtH y)).
      by rewrite lecE /= => /andP[]. }
    have Hsq_le :
        (fidelity rho_ext sigma_ext) ^+ 2 <=
        (fidelity (((\:1 : 'SO[H]_A) :⊗
                    (E : 'SO[H]_(B, Bp))) rhoAB)
           gamma_ABp) ^+ 2.
    { apply: lerXn2r;
        [exact: Hfid_ge0_local | exact: Hfid_ge0_local | exact: Hmono]. }
    rewrite Hsq_cast.
    exact: le_trans Hsq_le (HEcoh_ub _ Hv_mem). }
  have Hsup_eq : sup Ecoh = sup Eden
    by apply/eqP; rewrite eq_le; apply/andP; split.
  exact: Hsup_eq.
Qed.

End MinOmni.

End FvqkdReal.
