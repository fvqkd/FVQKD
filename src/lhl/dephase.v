(* -------------------------------------------------------------------- *)
(* lhl/dephase.v — LHL dephasing-X operators                            *)
(* -------------------------------------------------------------------- *)
(* Module: lhl.dephase                                              *)
(* Source: Tomamichel-Schaffner-Smith-Renner, 'Leftover Hashing       *)
(*   Against Quantum Side Information' (IEEE Trans. IT 57:5524 (2011);  *)
(*   arXiv:1002.2436): eqn:cq-state (Eq. 14, CQ-state form) and        *)
(*   lemma:cq-smoothing (Lem. 19, smoothing preserves CQ structure).   *)
(*   Data-processing specialization: Tomamichel, 'A Framework for      *)
(*   Non-Asymptotic Quantum Information Theory' (PhD thesis, ETH        *)
(*   Zürich; arXiv:1203.2142), th:pd-mono.                             *)
(* -------------------------------------------------------------------- *)
(* The X-basis dephasing channel dephase_X_so and its key properties    *)
(* (CPTP, identity on CQ states, preserves CQ structure, H_min          *)
(* non-decreasing).  Shared by lhl/util.v (cq_smoothing), lhl/prop.v     *)
(* (Gamma_C analysis), and measurement-based consumers.                  *)
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
From entropy Require Import def prop util.
From entropy.smooth Require Import dpi.
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
(* ================================================================== *)
(* X-basis dephasing channel                                          *)
(* Tomamichel-Schaffner-Smith-Renner, 'Leftover Hashing Against        *)
(* Quantum Side Information' (IEEE Trans. IT 57:5524 (2011);            *)
(* arXiv:1002.2436), Eq. 14 — tex eqn:cq-state (implicit) — math: the   *)
(* canonical X-basis dephasing channel with Kraus operators            *)
(* {|x⟩⟨x|_X ⊗ I_E} maps any state to the CQ form Σ_x |x⟩⟨x| ⊗ ρ_E^[x].*)
(* ================================================================== *)
Section DephasingX.
Variable (L : finType) (HL : L -> chsType) (X E : {set L}).
Hypothesis disXE : [disjoint X & E].
Notation S_XE := (X :|: E).
Let eqXE_diff : S_XE :\: E = X.
Proof. exact: setDU_r disXE. Defined.
Let eqXE_cond : S_XE :&: E = E.
Proof. setdec. Defined.
Let eqXE_lift :
    (S_XE :\: E) :|: E = S_XE.
Proof. by rewrite eqXE_diff. Defined.
Let eqXE_lift_sig :
    (S_XE :\: E) :|: (S_XE :&: E) =
    (S_XE :\: E) :|: E.
Proof. by rewrite eqXE_cond. Defined.
Let eqXE_phi :
    (S_XE :\: E) :|: (S_XE :&: E) = S_XE.
Proof. by rewrite finset.setUC finset.setID. Defined.
Let phi_lift_term (sigmaE : 'F[HL]_E) :
    castlf (eqXE_phi, eqXE_phi)
      ((\1 : 'F[HL]_(S_XE :\: E)) \O
        castlf (esym eqXE_cond, esym eqXE_cond) sigmaE) =
    (\1 : 'F[HL]_X) \O sigmaE.
Proof.
  have -> : eqXE_phi = etrans eqXE_lift_sig eqXE_lift.
  {
    apply: eq_irrelevance.
  }
  rewrite -castlf_comp.
  rewrite (@sdotIf_cast_r R _ _ (S_XE :\: E)
    (S_XE :&: E) E
    eqXE_cond eqXE_lift_sig
    (castlf (esym eqXE_cond, esym eqXE_cond) sigmaE)).
  have -> :
      castlf (eqXE_cond, eqXE_cond)
        (castlf (esym eqXE_cond, esym eqXE_cond) sigmaE) = sigmaE.
  {
    exact: castlfKV.
  }
  rewrite (@sdotIf_cast_l R _ _ (S_XE :\: E) X E
    eqXE_diff eqXE_lift
    (\1 : 'F[HL]_(S_XE :\: E)) sigmaE).
  have -> :
      castlf (eqXE_diff, eqXE_diff)
        (\1 : 'F[HL]_(S_XE :\: E)) =
      (\1 : 'F[HL]_X).
  {
    exact: castlf1.
  }
  done.
Defined.
Local Notation dephase_X_so := (@dephase_X_so R L HL X E).
(* tex: eqn:purified-monotone, Tomamichel09 Lm.7 (cq-preserving CPM).   *)
(* math: dephase_X_so is CPTP.                                          *)
(* Derivation: projective measurement Kraus operators                   *)
(* {|x⟩⟨x|_X ⊗ I_E} satisfy Σ_x K_x^A·K_x = I (idempotent + complete).  *)
(* dephase_X_cptp *)
(* infra: no tex label — fundamental & reusable (mathcomp-style) *)
(* consumer: dephase_X_cptp is used downstream by the BB84 secrecy proof. *)
(* path: lhl:dephase_X_cptp -> lhl:cq_smoothing -> *)
(*   bb84:privacy_amplification -> bb84:bb84_secret *)
Lemma dephase_X_cptp : dephase_X_so \is cptp.
Proof.
  rewrite /dephase_X_so.
  apply/krausso_qcP.
  rewrite /trace_presv.
  apply/eqP.
  under eq_bigr => x _.
    have Htensor : ([> deltav x; deltav x <] \O (\1 : 'F_E)
                    : 'F[HL]_S_XE) =
                   [> deltav x; deltav x <] \⊗ (\1 : 'F_E).
      by apply: to_Fnd_inj; rewrite (sdotFT _ _ disXE) to_Fnd_tenE.
    rewrite {1}Htensor tenf_adj adj_outp adjf1 -Htensor.
    have Hsq : ([> deltav x; deltav x <] \O (\1 : 'F_E)
                : 'F[HL]_S_XE) \o
               ([> deltav x; deltav x <] \O (\1 : 'F_E)) =
               [> deltav x; deltav x <] \O (\1 : 'F_E).
      rewrite {1 2}Htensor -tenf_comp; last exact: disXE.
      rewrite comp_lfun1l outp_comp dv_dot eqxx scale1r.
      by rewrite -Htensor.
    rewrite Hsq.
    over.
  transitivity (\sum_(x : 'Idx[HL]_X)
    ([> deltav x; deltav x <] \⊗ (\1 : 'F_E) : 'F[HL]_S_XE)).
    apply: eq_bigr => x _.
    by apply: to_Fnd_inj; rewrite (sdotFT _ _ disXE) to_Fnd_tenE.
  by rewrite -tenf_suml sumonb_out tenf11.
Qed.
(* dephase_X acts as identity on already-CQ states.                     *)
(* math: is_cq_state ρ ⇒ dephase_X_so ρ = ρ.                            *)
(* dephase_X_cq_id *)
(* infra: no tex label — fundamental & reusable (mathcomp-style) *)
(* consumer: dephase_X_cq_id is used downstream by the BB84 secrecy proof. *)
(* path: lhl:dephase_X_cq_id -> lhl:cq_smoothing -> *)
(*   bb84:privacy_amplification -> bb84:bb84_secret *)
Lemma dephase_X_cq_id (rhoXE : 'F[HL]_S_XE) :
  is_cq_state rhoXE -> dephase_X_so rhoXE = rhoXE.
Proof.
  rewrite /is_cq_state => /forallP Hcq.
  rewrite /dephase_X_so kraussoE.
  have HK_adj : forall x,
    (([> deltav x; deltav x <] \O (\1 : 'F_E) : 'F[HL]_S_XE))^A =
    [> deltav x; deltav x <] \O (\1 : 'F_E).
    move=> x.
    have Htensor : ([> deltav x; deltav x <] \O (\1 : 'F_E)
                    : 'F[HL]_S_XE) =
                   [> deltav x; deltav x <] \⊗ (\1 : 'F_E).
      by apply: to_Fnd_inj; rewrite (sdotFT _ _ disXE) to_Fnd_tenE.
    by rewrite Htensor tenf_adj adj_outp adjf1 -Htensor.
  under eq_bigr => x _ do rewrite HK_adj.
  have Hsum_I : \sum_(x : 'Idx[HL]_X)
    ([> deltav x; deltav x <] \O (\1 : 'F_E) : 'F[HL]_S_XE) =
    (\1 : 'F[HL]_S_XE).
    transitivity (\sum_(x : 'Idx[HL]_X)
      ([> deltav x; deltav x <] \⊗ (\1 : 'F_E) : 'F[HL]_S_XE)).
      apply: eq_bigr => x _.
      by apply: to_Fnd_inj; rewrite (sdotFT _ _ disXE) to_Fnd_tenE.
    by rewrite -tenf_suml sumonb_out tenf11.
  apply: esym.
  rewrite -{1}[rhoXE]comp_lfun1l -{1}Hsum_I linear_sumlz /=.
  apply: eq_bigr => y _.
  rewrite -{1}[_ \o rhoXE]comp_lfun1r -{1}Hsum_I linear_sumr /=.
  rewrite (bigID (fun z : 'Idx[HL]_X => z == y)) /= big_pred1_eq.
  rewrite [X in _ + X]big1; first by rewrite addr0.
  move=> z Hzy; move: (Hcq y) => /forallP /(_ z).
  by rewrite Hzy /= => /eqP ->.
Qed.
(* dephase_X maps psd states to CQ psd states.                          *)
(* math: ρ psd ⇒ is_cq_state (dephase_X_so ρ).                          *)
(* dephase_X_is_cq *)
(* infra: no tex label — fundamental & reusable (mathcomp-style) *)
(* consumer: dephase_X_is_cq is used downstream by the BB84 secrecy proof. *)
(* path: lhl:dephase_X_is_cq -> lhl:cq_smoothing -> *)
(*   bb84:privacy_amplification -> bb84:bb84_secret *)
Lemma dephase_X_is_cq (rhoXE : 'F[HL]_S_XE) :
  rhoXE \is psdlf -> is_cq_state (dephase_X_so rhoXE).
Proof.
  move=> _; rewrite /is_cq_state.
  apply/forallP => x; apply/forallP => x'; apply/implyP => Hxx'.
  rewrite /dephase_X_so kraussoE.
  apply/eqP.
  rewrite linear_sumr /= linear_sumlz /=.
  apply: big1 => y _.
  have Htensor : forall w : 'Idx[HL]_X,
    ([> deltav w; deltav w <] \O (\1 : 'F_E) : 'F[HL]_S_XE) =
    [> deltav w; deltav w <] \⊗ (\1 : 'F_E).
    by move=> w; apply: to_Fnd_inj;
       rewrite (sdotFT _ _ disXE) to_Fnd_tenE.
  have HKadj : forall w,
    (([> deltav w; deltav w <] \O (\1 : 'F_E) : 'F[HL]_S_XE))^A =
    [> deltav w; deltav w <] \O (\1 : 'F_E).
    by move=> w; rewrite Htensor tenf_adj adj_outp adjf1 -Htensor.
  rewrite HKadj.
  have HKprod : forall w1 w2 : 'Idx[HL]_X,
    ([> deltav w1 ; deltav w1 <] \O (\1 : 'F_E) : 'F[HL]_S_XE) \o
    ([> deltav w2 ; deltav w2 <] \O (\1 : 'F_E)) =
    if (w1 == w2) then
      [> deltav w1 ; deltav w1 <] \O (\1 : 'F_E)
    else 0.
    move=> w1 w2.
    rewrite !Htensor -tenf_comp; last exact: disXE.
    rewrite comp_lfun1l outp_comp dv_dot.
    case: (eqVneq w1 w2) => [Hw1w2|Hw1w2].
    - rewrite Hw1w2.
      by rewrite /= scale1r -Htensor.
    - by rewrite /= scale0r ten0f.
  case: (eqVneq y x) => [Hyx|Hyx].
  - case: (eqVneq y x') => [Hyx'|Hyx'].
    + have Hxx : x' = x by rewrite -Hyx' Hyx.
      move: Hxx'; rewrite Hxx => Habs.
      by rewrite eqxx in Habs.
    + rewrite -!comp_lfunA.
      rewrite HKprod (negbTE Hyx') /=.
      by rewrite !comp_lfun0r.
  - rewrite !comp_lfunA.
    rewrite HKprod eq_sym (negbTE Hyx) /=.
    by rewrite !comp_lfun0l.
Qed.
(* Conditional min-entropy is non-decreasing under X-measurement.       *)
(* tex: Tomamichel09 Thm.19 (DPI for H_min on conditioning reg).*)
(* math: ρ psd ⇒ H_min(X|E)_ρ ≤ H_min(X|E)_(dephase_X_so ρ), on the      *)
(*       extended-real min-entropy surface.                     *)
(* Derivation: dephase_X_so is CPTP and acts as id on E-register;       *)
(* hmin_cptp_sys_monotone (smooth/dpi.v) applies.                       *)
(* path: lhl:dephase_X_hmin_preserve -> lhl:cq_smoothing -> *)
(*   bb84:privacy_amplification -> bb84:bb84_secret *)
Lemma dephase_X_hmin_preserve (rhoXE : 'F[HL]_S_XE) :
  rhoXE \is psdlf ->
  (hminE E rhoXE <= hminE E (dephase_X_so rhoXE))%E.
Proof.
  move=> Prho; pose rhoXE' := dephase_X_so rhoXE.
  have psdlf_le_tr_id_local :
      forall (S : {set L}) (f : 'F[HL]_S),
        f \is psdlf ->
        f <= (@complex.Re R (\Tr f))%:C *: (\1 : 'F[HL]_S).
  {
    move=> S f Pf; have Htr_real : \Tr f \is Num.real := ger0_real (psdlf_trlf Pf).
    rewrite lef_h2mx.
    have -> :
        h2mx ((@complex.Re R (\Tr f))%:C *: (\1 : 'F[HL]_S)) =
        (\tr (h2mx f))%:M.
    {
      rewrite h2mxZ_lf /= h2mx1 /lftrace (RRe_real Htr_real) scalemx1.
      done.
    }
    apply: lemx_psd_ub.
    by rewrite qualifE.
  }
  have HrhoXE'_psd : rhoXE' \is psdlf.
  {
    have Hcp : dephase_X_so \is cpmap := cptp_cpmap dephase_X_cptp.
    exact: (cp_psdP (CPMap_Build Hcp) Prho).
  }
  have Htr_rhoXE' : \Tr rhoXE' = \Tr rhoXE.
  {
    have /cptpP [_ /tpmapP Htp] := dephase_X_cptp.
    exact: Htp.
  }
  have Htr_rho_ge0 : 0 <= @complex.Re R (\Tr rhoXE).
  {
    by move: (psdlf_trlf Prho); rewrite lecE /= => /andP[].
  }
  have Htr_rho'_ge0 : 0 <= @complex.Re R (\Tr rhoXE').
  {
    by rewrite Htr_rhoXE' Htr_rho_ge0.
  }
  have Hphi_le :
      phi_min E rhoXE' <= phi_min E rhoXE.
  {
    rewrite /phi_min.
    apply: lb_le_inf.
    - pose c := @complex.Re R (\Tr rhoXE).
      pose sigmaE : 'F[HL]_E := c%:C *: (\1 : 'F[HL]_E).
      pose sigma0 : 'F[HL]_(S_XE :&: E) :=
        castlf (esym eqXE_cond, esym eqXE_cond) sigmaE.
      exists (@complex.Re R (\Tr sigma0)).
      exists sigma0.
      split.
      + rewrite /sigma0 /sigmaE castlf_psdlfE.
        apply: psdlfZ.
        * by rewrite lecE /= eqxx Htr_rho_ge0.
        * by rewrite qualifE h2mx1; exact: psdmx1.
      + split.
        * have Hlift_one :
              ((\1 : 'F[HL]_X) \O (\1 : 'F[HL]_E)
                : 'F[HL]_S_XE) = (\1 : 'F[HL]_S_XE).
          {
            apply: to_Fnd_inj.
            by rewrite (sdotFT _ _ disXE) -!to_FndEV tenf11.
          }
          match goal with
          | |- context[castlf (?p, ?p) _] =>
              have -> : p = eqXE_phi by apply: eq_irrelevance
          end.
          rewrite /sigma0.
          have -> :
              castlf (esym eqXE_cond, esym eqXE_cond) sigmaE =
              sigma0 by [].
          rewrite phi_lift_term /sigmaE sdotfZr Hlift_one.
          exact: psdlf_le_tr_id_local Prho.
        * done.
    - move=> v [sigma [Psigma [Hsigma Hv]]].
      pose sigmaE : 'F[HL]_E := castlf (eqXE_cond, eqXE_cond) sigma.
      have PsigmaE : sigmaE \is psdlf.
      {
        by rewrite /sigmaE castlf_psdlfE.
      }
      have HsigmaE :
          ((\1 : 'F[HL]_X) \O sigmaE - rhoXE) \is psdlf.
      {
        move: Hsigma.
        have -> :
            castlf (eqXE_phi, eqXE_phi)
              ((\1 : 'F[HL]_(S_XE :\: E)) \O sigma) =
            (\1 : 'F[HL]_X) \O sigmaE.
        {
          have -> :
              sigma =
              castlf (esym eqXE_cond, esym eqXE_cond) sigmaE.
          {
            by rewrite /sigmaE castlfK.
          }
          exact: phi_lift_term.
        }
        done.
      }
      have Hsigma_fix :
          dephase_X_so ((\1 : 'F[HL]_X) \O sigmaE) =
          (\1 : 'F[HL]_X) \O sigmaE.
      {
        apply: dephase_X_cq_id.
        rewrite /is_cq_state.
        apply/forallP => x; apply/forallP => x'; apply/implyP => Hxx'.
        apply/eqP.
        have HKprod : forall w1 w2 : 'Idx[HL]_X,
          ([> deltav w1 ; deltav w1 <] \O (\1 : 'F_E) : 'F[HL]_S_XE) \o
          ((\1 : 'F[HL]_X) \O sigmaE) \o
          ([> deltav w2 ; deltav w2 <] \O (\1 : 'F_E)) =
          if (w1 == w2) then
            [> deltav w1 ; deltav w1 <] \O sigmaE else 0.
        {
          move=> w1 w2.
          have HtensorK : forall w,
            ([> deltav w ; deltav w <] \O (\1 : 'F_E) : 'F[HL]_S_XE) =
            [> deltav w ; deltav w <] \⊗ (\1 : 'F_E).
            by move=> w; apply: to_Fnd_inj;
               rewrite (sdotFT _ _ disXE) to_Fnd_tenE.
          have HtensorS :
            ((\1 : 'F[HL]_X) \O sigmaE : 'F[HL]_S_XE) =
            (\1 : 'F[HL]_X) \⊗ sigmaE.
            by apply: to_Fnd_inj; rewrite (sdotFT _ _ disXE) to_Fnd_tenE.
          have HtensorB : forall w,
            ([> deltav w ; deltav w <] \O sigmaE : 'F[HL]_S_XE) =
            [> deltav w ; deltav w <] \⊗ sigmaE.
            by move=> w; apply: to_Fnd_inj;
               rewrite (sdotFT _ _ disXE) to_Fnd_tenE.
          rewrite !HtensorK HtensorS.
          rewrite -tenf_comp; last exact: disXE.
          rewrite comp_lfun1l comp_lfun1r.
          rewrite -tenf_comp; last exact: disXE.
          rewrite comp_lfun1r outp_comp dv_dot.
          case: (eqVneq w1 w2) => [->|Hw].
          - by rewrite scale1r -HtensorB.
          - have Hw12 : ~~ (w1 == w2) by exact: Hw.
            have Hw21 : ~~ (w2 == w1) by rewrite eq_sym.
            by rewrite ?(negbTE Hw12) ?(negbTE Hw21) scale0r ten0f.
        }
        have Hxx2 : ~~ (x' == x) by exact: Hxx'.
        have Hxx1 : ~~ (x == x') by rewrite eq_sym.
        by rewrite HKprod ?(negbTE Hxx1) ?(negbTE Hxx2).
      }
      have Hgap_psd :
          dephase_X_so (((\1 : 'F[HL]_X) \O sigmaE) - rhoXE) \is psdlf.
      {
        have Hcp : dephase_X_so \is cpmap := cptp_cpmap dephase_X_cptp.
        exact: (cp_psdP (CPMap_Build Hcp) HsigmaE).
      }
      have Hfeas' :
          phi_min_feasible E rhoXE' v.
      {
        exists sigma.
        split.
        - exact: Psigma.
        split.
        - have Hlin :
              dephase_X_so (((\1 : 'F[HL]_X) \O sigmaE) - rhoXE) =
              dephase_X_so ((\1 : 'F[HL]_X) \O sigmaE) -
              dephase_X_so rhoXE.
          {
            have Hlin := superop_is_linear dephase_X_so.
            have H0 : dephase_X_so (0 : 'F[HL]_S_XE) = 0.
            { exact: linear0. }
            have Hopp (x : 'F[HL]_S_XE) :
                dephase_X_so (- x) = - dephase_X_so x.
            {
              have Hx0 : (-1 : C) *: x + 0 = - x.
              { by rewrite addr0 scaleN1r. }
              have Hr0 : (-1 : C) *: dephase_X_so x + dephase_X_so 0 =
                          - dephase_X_so x.
              { by rewrite H0 addr0 scaleN1r. }
              by move: (Hlin (-1 : C) x 0); rewrite Hx0 Hr0.
            }
            have HA :
                (1 : C) *: ((\1 : 'F[HL]_X) \O sigmaE) + - rhoXE =
                ((\1 : 'F[HL]_X) \O sigmaE) - rhoXE.
            { by rewrite scale1r. }
            have HR :
                (1 : C) *: dephase_X_so ((\1 : 'F[HL]_X) \O sigmaE) +
                dephase_X_so (- rhoXE) =
                dephase_X_so ((\1 : 'F[HL]_X) \O sigmaE) -
                dephase_X_so rhoXE.
            { by rewrite scale1r Hopp. }
            by move: (Hlin (1 : C) ((\1 : 'F[HL]_X) \O sigmaE) (- rhoXE));
              rewrite HA HR.
          }
          match goal with
          | |- context[castlf (?p, ?p) _] =>
              have -> : p = eqXE_phi by apply: eq_irrelevance
          end.
          rewrite /rhoXE'.
          move: Hgap_psd; rewrite Hlin Hsigma_fix.
          have -> :
              dephase_X_so rhoXE = rhoXE' by [].
          have -> :
              (\1 : 'F[HL]_X) \O sigmaE =
              castlf (eqXE_phi, eqXE_phi)
                ((\1 : 'F[HL]_(S_XE :\: E)) \O sigma).
          {
            have -> :
                sigma =
                castlf (esym eqXE_cond, esym eqXE_cond) sigmaE.
            {
              by rewrite /sigmaE castlfK.
            }
            exact: (esym (phi_lift_term sigmaE)).
          }
          done.
        - exact: Hv.
      }
      have Hhas_inf' :
          has_inf [set w : R | phi_min_feasible E rhoXE' w].
      {
        split.
        - by exists v.
        - exists 0 => w [tau [Ptau [_ ->]]].
          by have := psdlf_trlf Ptau; rewrite lecE /= => /andP[_].
      }
      exact: (ge_inf Hhas_inf'.2 Hfeas').
  }
  have Htr_rho_real : \Tr rhoXE \is Num.real.
  {
    exact: ger0_real (psdlf_trlf Prho).
  }
  have Htr_rho'_real : \Tr rhoXE' \is Num.real.
  {
    exact: ger0_real (psdlf_trlf HrhoXE'_psd).
  }
  have Htr_eqR :
      @complex.Re R (\Tr rhoXE') = @complex.Re R (\Tr rhoXE).
  {
    by rewrite Htr_rhoXE'.
  }
  case Htr0 : (@complex.Re R (\Tr rhoXE) == 0).
  - have Htr0R : @complex.Re R (\Tr rhoXE) = 0 by move/eqP: Htr0.
    have Hrho0 : rhoXE = 0.
    {
      have Hrho_ge0 : 0 ⊑ rhoXE by move: Prho; rewrite psdlfE.
      have Htr0C : \Tr rhoXE = 0 by rewrite -(RRe_real Htr_rho_real) Htr0R.
      have Hrho_eq0 : rhoXE == 0 by apply/trlf0_eq0; exact: conj Hrho_ge0 Htr0C.
      by move/eqP: Hrho_eq0.
    }
    subst rhoXE.
    have Hdeph0 : dephase_X_so 0 = 0.
    {
      rewrite /dephase_X_so kraussoE.
      apply: big1 => x _.
      by rewrite comp_lfun0r comp_lfun0l.
    }
    rewrite /hminE Hdeph0.
    by rewrite lexx.
  - have Htr_pos : 0 < @complex.Re R (\Tr rhoXE).
    {
      have Htr_ge0 : 0 <= @complex.Re R (\Tr rhoXE).
      {
        by move: (psdlf_trlf Prho); rewrite lecE /= => /andP[].
      }
      by rewrite lt_neqAle Htr_ge0 andbT eq_sym Htr0.
    }
    have Hphi_lb :
        @complex.Re R (\Tr rhoXE') / (dim 'H[HL]_X)%:R <=
        phi_min E rhoXE'.
    {
      apply: lb_le_inf.
      - pose sigmaE := (@complex.Re R (\Tr rhoXE'))%:C *:
                       (\1 : 'F[HL]_E).
        pose sigma0 : 'F[HL]_(S_XE :&: E) :=
          castlf (esym eqXE_cond, esym eqXE_cond) sigmaE.
        exists (@complex.Re R (\Tr sigma0)).
        exists sigma0.
        split.
        + rewrite /sigma0 /sigmaE castlf_psdlfE.
          apply: psdlfZ.
          * by rewrite lecE /= eqxx Htr_rho'_ge0.
          * by apply/gef0_psd; exact: lef01.
        + split.
          * have Hlift_one :
                ((\1 : 'F[HL]_X) \O (\1 : 'F[HL]_E)
                  : 'F[HL]_S_XE) = (\1 : 'F[HL]_S_XE).
            {
              apply: to_Fnd_inj.
              by rewrite (sdotFT _ _ disXE) -!to_FndEV tenf11.
            }
            match goal with
            | |- context[castlf (?p, ?p) _] =>
                have -> : p = eqXE_phi by apply: eq_irrelevance
            end.
            rewrite /sigma0 phi_lift_term /sigmaE sdotfZr Hlift_one.
            apply: psdlf_le_tr_id_local.
            exact: HrhoXE'_psd.
          * done.
      - move=> v [sigma [Psigma [Hfeas ->]]].
        have Htr_sigma_real : (\Tr sigma : C) = (@complex.Re R (\Tr sigma))%:C.
          by rewrite RRe_real // ger0_real // psdlf_trlf.
        have Htau_leR :
            @complex.Re R (\Tr rhoXE') <=
            (dim 'H[HL]_X)%:R * @complex.Re R (\Tr sigma).
        {
          have Hgap_nonneg0 := psdlf_trlf Hfeas.
          have Htau_leC :
              \Tr rhoXE' <=
              \Tr (castlf (eqXE_phi, eqXE_phi)
                ((\1 : 'F[HL]_(S_XE :\: E)) \O sigma)).
          {
            have Hle :
                rhoXE' ⊑
                castlf (eqXE_phi, eqXE_phi)
                  ((\1 : 'F[HL]_(S_XE :\: E)) \O sigma).
            {
              by move: Hfeas; rewrite lefE.
            }
            exact: lef_trlf Hle.
          }
          rewrite -(RRe_real Htr_rho'_real) in Htau_leC.
          match type of Htau_leC with
          | context[castlf (?p, ?p) _] =>
              have Hp : p = eqXE_phi by apply: eq_irrelevance;
              rewrite Hp in Htau_leC
          end.
          have Hcast :
              \Tr (castlf (eqXE_phi, eqXE_phi)
                ((\1 : 'F[HL]_(S_XE :\: E)) \O sigma)) =
              ((dim 'H[HL]_X)%:R * @complex.Re R (\Tr sigma))%:C.
          {
            rewrite castlf_trlfE.
            have disSplit : [disjoint (S_XE :\: E) & (S_XE :&: E)].
            { setdec. }
            rewrite (trlf_lift_I disSplit) Htr_sigma_real -natrC -realcM.
            by rewrite eqXE_diff re_realid.
          }
          rewrite Hcast in Htau_leC.
          by move: Htau_leC; rewrite lecR.
        }
        rewrite ler_pdivrMr; last by rewrite ltr0n dim_proper.
        by rewrite mulrC.
    }
    have Hphi_pos :
        0 < phi_min E rhoXE'.
    {
      have Htr_pos' :
          0 < @complex.Re R (\Tr rhoXE') / (dim 'H[HL]_X)%:R.
      {
        rewrite Htr_eqR.
        apply: divr_gt0.
        - exact: Htr_pos.
        - by rewrite ltr0n dim_proper.
      }
      exact: lt_le_trans Htr_pos' Hphi_lb.
    }
    have Helog_le :
        (elog2 (phi_min E rhoXE') <=
         elog2 (phi_min E rhoXE))%E.
    {
      exact: elog2_le _ _ Hphi_pos Hphi_le.
    }
    by rewrite /hminE leeNr oppeK; exact: Helog_le.
Qed.
End DephasingX.
End FvqkdReal.
