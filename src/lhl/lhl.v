(* -------------------------------------------------------------------- *)
(* lhl.v — Main result: Quantum Leftover Hash Lemma                     *)
(* -------------------------------------------------------------------- *)
(* Module: lhl.lhl                                        *)
(* Source: Tomamichel-Schaffner-Smith-Renner, 'Leftover Hashing       *)
(*   Against Quantum Side Information' (IEEE Trans. IT 57:5524 (2011);  *)
(*   arXiv:1002.2436): thm:two-universal-hashing (Thm. 6).              *)
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
  cpo mxpred extnum ctopology svd mxnorm hspace.
From quantum.dirac Require Import hstensor setdec.
Import Order.TTheory GRing.Theory Num.Theory Num.Def MxLownerOrder.
Import VectorInternalTheory.
(* --- FVQKD imports --- *)
From utils Require Import exports.
From entropy Require Import def prop.
From entropy.smooth Require Import sm prop.
From lhl Require Import def dephase util post_hash prop.
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
(* Quantum Leftover Hash Lemma                                          *)
(* Tomamichel-Schaffner-Smith-Renner, 'Leftover Hashing Against Quantum *)
(* Side Information' (IEEE Trans. IT 57:5524 (2011); arXiv:1002.2436),   *)
(* Thm. 6 — tex thm:two-universal-hashing                                *)
(* math: d_u(Z|FE)_ρ ≤ ε + ½ √(2^{ℓ - H^ε_min(X|E)_ρ})               *)
(*       where ℓ = log₂|Z|, ρ_{Z(FE)} = post-hash state                *)
(* ================================================================== *)
Section LHL.
Variable (L : finType) (HL : L -> chsType) (X E Fl Zl : {set L}).
Hypothesis disXE : [disjoint X & E].
Hypothesis disXF : [disjoint X & Fl].
Hypothesis disXZ : [disjoint X & Zl].
Hypothesis disEF : [disjoint E & Fl].
Hypothesis disEZ : [disjoint E & Zl].
Hypothesis disFZ : [disjoint Fl & Zl].
Let disZl_FE : [disjoint Zl & (Fl :|: E)].
Proof. by rewrite disjointXU disjoint_sym disFZ disjoint_sym disEZ. Defined.
(* Quantum Leftover Hash Lemma (two-universal hashing)                    *)
(* Tomamichel-Schaffner-Smith-Renner, 'Leftover Hashing Against Quantum     *)
(* Side Information' (IEEE Trans. IT 57:5524 (2011); arXiv:1002.2436),       *)
(* Thm. 6 — tex thm:two-universal-hashing                                    *)
(* math: For a two-universal hash family F: X × F → Z, a subnormalized CQ *)
(*   state ρ_XE with quantum side-info E, and smoothing parameter ε ≥ 0,  *)
(*     d_u(Z | FE)_{ρ_ZFE} ≤ ε + ½ · √(2^{ℓ - H^ε_min(X|E)_ρ}),            *)
(*   where ℓ := log₂|Z| and ρ_ZFE is the post-hash state.                 *)
(* Note: the tex phrase “let ρ_XE be defined as in           *)
(*   eqn:cq-state” is represented here by the explicit hypotheses         *)
(*   `rhoXE \is psdlf`, `Re (Tr rhoXE) <= 1`, and `is_cq_state rhoXE`.    *)
(* Specialization detail: F two-universal is used in the δ = 1/|Z|          *)
(*   specialization of eqn:almost-two-universal (Eq. 7).                   *)
(* path: lhl:two_universal_hashing -> *)
(*   bb84:privacy_amplification -> bb84:bb84_secret *)
Theorem two_universal_hashing
    (Fh : 'Idx[HL]_Fl -> 'Idx[HL]_X -> 'Idx[HL]_Zl)
    (eps : R) (rhoXE : 'F[HL]_(X :|: E)) :
  rhoXE \is psdlf ->
  @complex.Re R (\Tr rhoXE) <= 1 ->
  is_cq_state rhoXE ->
  @two_univ R _ _ _ Fh ->
  0 <= eps ->
  let rhoZFE := post_hash_state disXE Fh rhoXE in
  dist_from_uniform rhoZFE <=
  eps + (2%:R)^-1 * Num.sqrt (expR ((log2 (dim 'H[HL]_Zl)%:R -
    smooth_hmin E eps rhoXE) * ln 2%:R)).
Proof.
  move=> Hrho Hrho_tr Hcq HFh Heps /=; pose rhoZFE := post_hash_state disXE Fh rhoXE.
  have HrhoZFE_psd : rhoZFE \is psdlf.
    exact: (@post_hash_psdlf R L HL X E Fl Zl disXE disXF disXZ disEF disEZ disFZ
      Fh rhoXE Hrho).
  have HrhoZFE_tr : @complex.Re R (\Tr rhoZFE) <= 1.
  {
    rewrite /rhoZFE (@post_hash_trace_preserve R L HL X E Fl Zl
      disXE disXF disXZ disEF disEZ disFZ Fh rhoXE Hrho).
    exact: Hrho_tr.
  }
  have [Hepslt | Hlarge] :=
      ltP eps (Num.sqrt (@complex.Re R (\Tr rhoXE))).
    - have Heps_small :
          0 <= eps < Num.sqrt (@complex.Re R (\Tr rhoXE)).
      {
        by apply/andP; split.
      }
      have Hrho_pos : 0 < @complex.Re R (\Tr rhoXE).
      {
        have Hsqrt_gt0 : 0 < Num.sqrt (@complex.Re R (\Tr rhoXE)) :=
          le_lt_trans Heps Hepslt.
        have Hrho_ge0 : 0 <= @complex.Re R (\Tr rhoXE).
        { have := psdlf_trlf Hrho.
          by rewrite lecE /= => /andP []. }
        have Hsqrt_sq_pos :
            0 < (Num.sqrt (@complex.Re R (\Tr rhoXE))) ^+ 2
          by rewrite expr2; apply: mulr_gt0.
        by rewrite (sqr_sqrtr Hrho_ge0) in Hsqrt_sq_pos.
      }
    have Hrho_den : rhoXE \is denlf.
    { apply/denlfP; split=> //.
      have Hreal : \Tr rhoXE \is Num.real := ger0_real (psdlf_trlf Hrho).
      by rewrite -(RRe_real Hreal) lecR. }
    case: (@smoothing_support_hmin R L HL X E disXE eps rhoXE
              Hrho_den Heps_small)
      => tau0 [Htau0_ball [Htau0_opt [_ _]]].
    pose tauXE := @dephase_X_so R L HL X E tau0.
    have Htau0_psd : tau0 \is psdlf.
    {
      exact: eps_ball_psdlf Htau0_ball.
    }
    have Htau0_tr : @complex.Re R (\Tr tau0) <= 1.
    {
      exact: eps_ball_trlf Htau0_ball.
    }
    have Htau_psd : tauXE \is psdlf.
    {
      have Hcp : @dephase_X_so R L HL X E \is cpmap :=
        cptp_cpmap (@dephase_X_cptp R L HL X E disXE).
      exact: (cp_psdP (CPMap_Build Hcp) Htau0_psd).
    }
      have Htau_tr : @complex.Re R (\Tr tauXE) <= 1.
      {
        have /cptpP [_ /tpmapP Htp] := @dephase_X_cptp R L HL X E disXE.
        rewrite /tauXE Htp.
        exact: Htau0_tr.
      }
      have HtauXE_pos : 0 < @complex.Re R (\Tr tauXE).
      {
        have /cptpP [_ /tpmapP Htp] := @dephase_X_cptp R L HL X E disXE.
        rewrite /tauXE Htp.
        exact: eps_ball_trlf_gt0 Htau0_ball.
      }
      have Hpd_tau_rho : pur_dist tauXE rhoXE <= eps.
      {
      have Hdpi := @pd_mono_cptp R L HL (X :|: E) (X :|: E)
        (@dephase_X_so R L HL X E) tau0 rhoXE
        (@dephase_X_cptp R L HL X E disXE) Htau0_psd Hrho Htau0_tr Hrho_tr.
      rewrite /tauXE.
      rewrite (@dephase_X_cq_id R L HL X E disXE rhoXE Hcq) in Hdpi.
        have Htau0_pd := eps_ball_pur_dist Htau0_ball.
        exact: le_trans Hdpi Htau0_pd.
      }
    have Hpd_rho_tau : pur_dist rhoXE tauXE <= eps.
    {
      have Hrho_mx_psd : h2mx rhoXE \is psdmx by move: Hrho; rewrite qualifE.
      have Htau_mx_psd : h2mx tauXE \is psdmx
        by move: Htau_psd; rewrite qualifE.
      rewrite /pur_dist /gfid (gfid_sym_mx Hrho_mx_psd Htau_mx_psd).
      exact: Hpd_tau_rho.
    }
    have Hcq_tau : is_cq_state tauXE.
    {
      exact: (@dephase_X_is_cq R L HL X E disXE tau0 Htau0_psd).
    }
    pose S_XE := (X :|: E).
    have Hzero_psd_XE : (0 : 'F[HL]_S_XE) \is psdlf.
      by rewrite qualifE h2mx0 psdmx0.
    have Hzero_tr_XE : @complex.Re R (\Tr (0 : 'F[HL]_S_XE)) <= 1.
      by rewrite linear0 raddf0 ler01.
    have Hpd_zero_eq_XE :
        forall tau : 'F[HL]_S_XE,
          tau \is psdlf ->
          @complex.Re R (\Tr tau) <= 1 ->
          pur_dist (0 : 'F[HL]_S_XE) tau =
            Num.sqrt (@complex.Re R (\Tr tau)).
    {
      move=> tau Ptau Htau_tr0; have Hzero_mx_psd : h2mx (0 : 'F[HL]_S_XE) \is psdmx.
      {
        by move: Hzero_psd_XE; rewrite qualifE.
      }
      have Htau_mx_psd : h2mx tau \is psdmx.
      {
        by move: Ptau; rewrite qualifE.
      }
      have Hgfid0 :
          gfid (0 : 'F[HL]_S_XE) tau =
          Num.sqrt (1 - @complex.Re R (\Tr tau)).
      {
        rewrite /gfid (alt_gfid_gen Hzero_mx_psd Htau_mx_psd).
        have -> :
            @complex.Re R
              (trnorm (sqrtmx (h2mx (0 : 'F[HL]_S_XE)) *m sqrtmx (h2mx tau))) = 0.
        {
          by rewrite h2mx0 sqrtmx0 mul0mx trnorm0 raddf0.
        }
        have -> :
            @complex.Re R (1 - \tr (h2mx (0 : 'F[HL]_S_XE))) = 1.
        {
          by rewrite h2mx0 mxtrace0 subr0.
        }
        have -> :
            @complex.Re R (1 - \tr (h2mx tau)) =
            1 - @complex.Re R (\Tr tau).
        {
          by rewrite raddfB /= /lftrace.
        }
        by rewrite sqrtr1 mul1r add0r.
      }
      rewrite /pur_dist.
      pose a := 1 - @complex.Re R (\Tr tau).
      have Ha_ge0 : 0 <= a.
      {
        rewrite /a.
        by rewrite subr_ge0.
      }
      have -> :
          (gfid (0 : 'F[HL]_S_XE) tau)^2 = a.
      {
        rewrite Hgfid0.
        exact: sqr_sqrtr Ha_ge0.
      }
      by rewrite /a opprB addrCA subrr addr0.
    }
    have Hball_trace_pos :
        forall tau : 'F[HL]_S_XE, eps_ball eps rhoXE tau ->
          0 < @complex.Re R (\Tr tau).
    {
      move=> tau Hb; have Ptau : tau \is psdlf := eps_ball_psdlf Hb.
      have Htau_tr_ball : @complex.Re R (\Tr tau) <= 1 := eps_ball_trlf Hb.
      have Htau_pd : pur_dist tau rhoXE <= eps.
      {
        move: Hb; by rewrite /eps_ball => /andP [/andP [_ _] Hpd].
      }
      have Hrho_zero := Hpd_zero_eq_XE rhoXE Hrho Hrho_tr.
      have Htau_zero := Hpd_zero_eq_XE tau Ptau Htau_tr_ball.
      have Hgap_pos : 0 < Num.sqrt (@complex.Re R (\Tr rhoXE)) - eps.
      {
        by rewrite subr_gt0.
      }
      have Hsqrt_le :
          Num.sqrt (@complex.Re R (\Tr rhoXE)) <=
          Num.sqrt (@complex.Re R (\Tr tau)) + eps.
      {
        rewrite -Hrho_zero -Htau_zero.
        have Htri := @pd_metric_triangle R L HL S_XE
          (0 : 'F[HL]_S_XE) rhoXE tau
          Hzero_psd_XE Hrho Ptau Hzero_tr_XE Hrho_tr Htau_tr_ball.
        have Hstep :
            pur_dist (0 : 'F[HL]_S_XE) tau + pur_dist tau rhoXE <=
            pur_dist (0 : 'F[HL]_S_XE) tau + eps.
        {
          apply: lerD.
          - exact: lexx.
          - exact: Htau_pd.
        }
        exact: le_trans Htri Hstep.
      }
      have Hgap_le :
          Num.sqrt (@complex.Re R (\Tr rhoXE)) - eps <=
          Num.sqrt (@complex.Re R (\Tr tau)).
      {
        move: Hsqrt_le; by rewrite lerBlDr addrC.
      }
      have Htau_sqrt_pos : 0 < Num.sqrt (@complex.Re R (\Tr tau)).
      {
        exact: lt_le_trans Hgap_pos Hgap_le.
      }
      by rewrite -sqrtr_gt0.
    }
    have eqXE_diff : S_XE :\: E = X.
    {
      exact: setDU_r disXE.
    }
    have eqXE_cond : S_XE :&: E = E.
    {
      rewrite /S_XE.
      by setdec.
    }
    have eqXE_lift :
        (S_XE :\: E) :|: E = S_XE.
    {
      by rewrite eqXE_diff.
    }
    have eqXE_lift_sig :
        (S_XE :\: E) :|: (S_XE :&: E) =
        (S_XE :\: E) :|: E.
    {
      by rewrite eqXE_cond.
    }
    have eqXE_phi :
        (S_XE :\: E) :|: (S_XE :&: E) = S_XE.
    {
      by rewrite finset.setUC finset.setID.
    }
    have phi_lift_term (sigmaE : 'F[HL]_E) :
        castlf (eqXE_phi, eqXE_phi)
          ((\1 : 'F[HL]_(S_XE :\: E)) \O
            castlf (esym eqXE_cond, esym eqXE_cond) sigmaE) =
        (\1 : 'F[HL]_X) \O sigmaE.
    {
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
    }
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
    have Hphi_trace_lb :
        forall tau : 'F[HL]_S_XE,
          tau \is psdlf ->
          @complex.Re R (\Tr tau) <= 1 ->
          @complex.Re R (\Tr tau) / (dim 'H[HL]_X)%:R <=
            phi_min E tau.
    {
      move=> tau Ptau Htau_tr0; have Htr_tau_real : \Tr tau \is Num.real.
      {
        exact: ger0_real (psdlf_trlf Ptau).
      }
      apply: lb_le_inf.
      - pose sigmaE := (@complex.Re R (\Tr tau))%:C *:
                       (\1 : 'F[HL]_E).
        pose sigma0 : 'F[HL]_(S_XE :&: E) :=
          castlf (esym eqXE_cond, esym eqXE_cond) sigmaE.
        exists (@complex.Re R (\Tr sigma0)).
        exists sigma0.
        split.
        + rewrite /sigma0 /sigmaE castlf_psdlfE.
          apply: psdlfZ.
          * by rewrite lecE /= eqxx; move: (psdlf_trlf Ptau); rewrite lecE /= => /andP[].
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
            exact: Ptau.
          * done.
      - move=> v [sigma [Psigma [Hfeas ->]]].
        have Htr_sigma_real : (\Tr sigma : C) =
            (@complex.Re R (\Tr sigma))%:C.
        {
          by rewrite RRe_real // ger0_real // psdlf_trlf.
        }
        have Htau_leR :
            @complex.Re R (\Tr tau) <=
            (dim 'H[HL]_X)%:R * @complex.Re R (\Tr sigma).
        {
          have [p0 Hfeas0] :
              exists p0 :
                (S_XE :\: E) :|: (S_XE :&: E) = S_XE,
                (castlf (p0, p0)
                  ((\1 : 'F[HL]_(S_XE :\: E)) \O sigma) - tau)
                \is psdlf.
          {
            match type of Hfeas with
            | context[castlf (?p, ?p) _] => exists p
            end.
            exact: Hfeas.
          }
          pose gap :=
            castlf (p0, p0)
              ((\1 : 'F[HL]_(S_XE :\: E)) \O sigma).
          have Hp0_eq : p0 = eqXE_phi by apply: eq_irrelevance.
          have Htau_leC :
              \Tr tau <= \Tr gap.
          {
            have Hle : tau ⊑ gap.
            {
              rewrite /gap lefE.
              exact: Hfeas0.
            }
            exact: lef_trlf Hle.
          }
          rewrite -(RRe_real Htr_tau_real) in Htau_leC.
          have Hcast :
              \Tr gap =
              ((dim 'H[HL]_X)%:R * @complex.Re R (\Tr sigma))%:C.
          {
            rewrite /gap Hp0_eq castlf_trlfE.
            have disSplit :
                [disjoint (S_XE :\: E) & (S_XE :&: E)].
            {
              rewrite /S_XE.
              setdec.
            }
            rewrite (trlf_lift_I disSplit) Htr_sigma_real -natrC -realcM.
            by rewrite eqXE_diff re_realid.
          }
          rewrite Hcast in Htau_leC.
          by move: Htau_leC; rewrite lecR.
        }
        rewrite ler_pdivrMr; last by rewrite ltr0n dim_proper.
        by rewrite mulrC.
    }
    have HhminE_fin_on_ball :
        forall tau : 'F[HL]_S_XE, eps_ball eps rhoXE tau ->
          hminE E tau = (hmin E tau)%:E.
    {
      move=> tau Htau_ball; have Ptau : tau \is psdlf := eps_ball_psdlf Htau_ball.
      have Htau_tr_ball : @complex.Re R (\Tr tau) <= 1 := eps_ball_trlf Htau_ball.
      have Htau_pos : 0 < @complex.Re R (\Tr tau).
      {
        exact: Hball_trace_pos Htau_ball.
      }
      have Hphi_lb :
          @complex.Re R (\Tr tau) / (dim 'H[HL]_X)%:R <=
          phi_min E tau.
      {
        exact: Hphi_trace_lb Ptau Htau_tr_ball.
      }
      have Hphi_pos : 0 < phi_min E tau.
      {
        have Htau_dim_pos :
            0 < @complex.Re R (\Tr tau) / (dim 'H[HL]_X)%:R.
        {
          apply: divr_gt0.
          - exact: Htau_pos.
          - by rewrite ltr0n dim_proper.
        }
        exact: lt_le_trans Htau_dim_pos Hphi_lb.
      }
      rewrite /hminE /hmin (elog2_gt0 Hphi_pos).
      by rewrite EFinN.
    }
    have Hsmooth_le_tau :
        smooth_hmin E eps rhoXE <= hmin E tauXE.
    {
        have Htau_ball : eps_ball eps rhoXE tauXE.
        {
          by rewrite /eps_ball Htau_psd HtauXE_pos Htau_tr Hpd_tau_rho.
        }
      have Htau0_le_tau :
          (hminE E tau0 <= hminE E tauXE)%E.
      {
        rewrite /tauXE.
        exact: (@dephase_X_hmin_preserve R L HL X E disXE tau0 Htau0_psd).
      }
      have Htau0_ubE :
          forall tau : 'F[HL]_S_XE, eps_ball eps rhoXE tau ->
            (hminE E tau <= hminE E tau0)%E.
      {
        move=> tau Htau_ball0; rewrite -Htau0_opt /smooth_hminE.
        apply: ereal_sup_ubound.
        exists tau.
        split.
        - exact: Htau_ball0.
        - reflexivity.
      }
      rewrite /smooth_hmin.
      apply: ge_sup.
      - exists (hmin E rhoXE).
        exists rhoXE.
        split; last reflexivity.
          by rewrite /eps_ball Hrho Hrho_pos Hrho_tr
            (pur_dist_refl Hrho Hrho_tr) Heps.
      - move=> v [tau [Htau_ball0 ->]].
        have Htau_le_tauXE :
            (hminE E tau <= hminE E tauXE)%E.
        {
          exact: le_trans (Htau0_ubE tau Htau_ball0) Htau0_le_tau.
        }
        move: Htau_le_tauXE.
        rewrite (HhminE_fin_on_ball tau Htau_ball0)
          (HhminE_fin_on_ball tauXE Htau_ball).
        by rewrite lee_fin.
    }
    pose tauZFE := post_hash_state disXE Fh tauXE.
    have HtauZFE_psd : tauZFE \is psdlf.
      exact: (@post_hash_psdlf R L HL X E Fl Zl disXE disXF disXZ disEF disEZ disFZ
        Fh tauXE Htau_psd).
    have HtauZFE_tr : @complex.Re R (\Tr tauZFE) <= 1.
    {
      rewrite /tauZFE (@post_hash_trace_preserve R L HL X E Fl Zl
        disXE disXF disXZ disEF disEZ disFZ Fh tauXE Htau_psd).
      exact: Htau_tr.
    }
    have Hpd_post : pur_dist rhoZFE tauZFE <= eps.
    {
      apply: (le_trans (@pd_mono_post_hash R L HL X E Fl Zl
        disXE disXF disXZ disEF disEZ disFZ Fh rhoXE tauXE Hrho Htau_psd
        Hrho_tr Htau_tr)).
      exact: Hpd_rho_tau.
    }
    have [sigmaE [Hsigma_den [Hsupp_sigma Hcoll]]] :=
      @min_coll_bound R L HL X E disXE tauXE Htau_psd Htau_tr.
    have Hsigma_psd : sigmaE \is psdlf := denlf_psd Hsigma_den.
    have disFE : [disjoint Fl & E] by rewrite disjoint_sym.
    pose rhoF_sigmaE :=
      ((dim 'H[HL]_Fl)%:R^-1)%:C *: ((\1 : 'F_Fl) \O sigmaE).
    have Hlift_sigma_psd :
        ((\1 : 'F_Fl) \O sigmaE : 'F[HL]_(Fl :|: E)) \is psdlf.
    {
      have -> : ((\1 : 'F_Fl) \O sigmaE : 'F[HL]_(Fl :|: E)) =
                (\1 : 'F_Fl) \⊗ sigmaE.
        by apply: to_Fnd_inj; rewrite (sdotFT _ _ disFE) to_Fnd_tenE.
      rewrite psdlfE.
      apply: tenf_ge0; first exact: disFE.
      - exact: lef01.
      - by rewrite -psdlfE.
    }
    have HrhoF_sigma_psd : rhoF_sigmaE \is psdlf.
    {
      rewrite /rhoF_sigmaE.
      apply: psdlfZ.
      - by rewrite lecR invr_ge0.
      - exact: Hlift_sigma_psd.
    }
    have HrhoF_sigma_tr_eq : \Tr rhoF_sigmaE = \Tr sigmaE.
    {
      rewrite /rhoF_sigmaE linearZ/= (trlf_lift_I disFE sigmaE) mulrA.
      have HdimF_neq0 : ((dim 'H[HL]_Fl)%:R : C) != 0.
        by rewrite pnatr_eq0 -lt0n dim_proper.
      have Hscalar_eq :
          ((dim 'H[HL]_Fl)%:R^-1)%:C =
          @GRing.inv C ((dim 'H[HL]_Fl)%:R).
        by rewrite -natrC -fmorphV.
      have Hscale1 :
          (((dim 'H[HL]_Fl)%:R^-1)%:C * (dim 'H[HL]_Fl)%:R = 1 :> C).
      {
        rewrite Hscalar_eq.
        by rewrite mulVf.
      }
      by rewrite Hscale1 mul1r.
    }
    have HrhoF_sigma_tr : @complex.Re R (\Tr rhoF_sigmaE) <= 1.
    {
      rewrite HrhoF_sigma_tr_eq.
      have Hsigma_trC :
          (\Tr sigmaE : C) = (@complex.Re R (\Tr sigmaE))%:C.
      { by rewrite RRe_real // ger0_real // psdlf_trlf. }
      move: (denlf_trlf Hsigma_den); by rewrite Hsigma_trC lecR.
    }
    have Hsupp_post :
        (supph (ptrace_castl disZl_FE tauZFE) `<=` supph rhoF_sigmaE)%HS.
    {
      rewrite /tauZFE (@post_hash_ptrace_Z_CQ R L HL X E Fl Zl
        disXE disXF disXZ disEF disEZ disFZ Fh tauXE Htau_psd Hcq_tau).
      rewrite /rhoF_sigmaE !supphZ.
      - exact: (@supph_lift_mono R L HL Fl E
          (ptrace_castl disXE tauXE) sigmaE Hsupp_sigma).
      - by rewrite fmorph_eq0 invr_eq0 pnatr_eq0 -lt0n dim_proper.
      - by rewrite fmorph_eq0 invr_eq0 pnatr_eq0 -lt0n dim_proper.
    }
    have Hnonsmooth_tau :
        dist_from_uniform tauZFE <=
        (2%:R)^-1 * Num.sqrt (expR ((log2 (dim 'H[HL]_Zl)%:R -
          hmin E tauXE) * ln 2%:R)).
    {
      have Hucoll := @uniform_to_collision R L HL Zl (Fl :|: E)
        disZl_FE tauZFE rhoF_sigmaE
        HtauZFE_psd HrhoF_sigma_psd HrhoF_sigma_tr Hsupp_post.
      rewrite /tauZFE (@post_hash_ptrace_Z_CQ R L HL X E Fl Zl
        disXE disXF disXZ disEF disEZ disFZ Fh tauXE Htau_psd Hcq_tau) in Hucoll.
      rewrite /rhoF_sigmaE.
      rewrite (@trlf_cross_system_4pt_identity R L HL Fl E
        disFE sigmaE (ptrace_castl disXE tauXE) Hsigma_psd) in Hucoll.
      set T := @complex.Re R (\Tr (
        ptrace_castl disXE tauXE \o pinvlf (sqrtH sigmaE) \o
        ptrace_castl disXE tauXE \o pinvlf (sqrtH sigmaE))) in Hucoll.
      have Hdelta_ge0 : 0 <= @GRing.inv R ((dim 'H[HL]_Zl)%:R)
        by rewrite invr_ge0 ler0n.
      have HFh_delta :
        delta_almost_two_univ Fh (@GRing.inv R ((dim 'H[HL]_Zl)%:R)).
      {
        move=> x x' Hxx; move: (HFh x x' Hxx).
        by rewrite /collision_probability !idx_card.
      }
      have Hpa := @privacy_amp R L HL X E Fl Zl
        disXE disXF disXZ disEF disEZ disFZ tauXE sigmaE Fh
        (@GRing.inv R ((dim 'H[HL]_Zl)%:R))
        Htau_psd Htau_tr (denlf_psd Hsigma_den) Hcq_tau
        Hdelta_ge0 HFh_delta.
      have dZ_ge0 : 0 <= (dim 'H[HL]_Zl)%:R :> R by rewrite ler0n.
      have dZ_neq0 : ((dim 'H[HL]_Zl)%:R != 0 :> R).
        by rewrite pnatr_eq0 -lt0n dim_proper.
      have Hinside1 :
          (dim 'H[HL]_Zl)%:R * collision_ent tauZFE
            (((dim 'H[HL]_Fl)%:R^-1)%:C *:
              ((\1 : 'F_Fl) \O sigmaE)) - T
        <= (dim 'H[HL]_Zl)%:R * collision_ent tauXE sigmaE.
      {
        have Hscaled :
            (dim 'H[HL]_Zl)%:R * collision_ent tauZFE
              (((dim 'H[HL]_Fl)%:R^-1)%:C *:
                ((\1 : 'F_Fl) \O sigmaE)) - T
          <= (dim 'H[HL]_Zl)%:R *
              (collision_ent tauXE sigmaE +
               (dim 'H[HL]_Zl)%:R^-1 * T) - T.
        {
          have Hmul := ler_wpM2l dZ_ge0 Hpa.
          set lhsT :=
            (dim 'H[HL]_Zl)%:R * collision_ent tauZFE
              (((dim 'H[HL]_Fl)%:R^-1)%:C *:
                ((\1 : 'F_Fl) \O sigmaE)).
          set rhsT :=
            (dim 'H[HL]_Zl)%:R *
              (collision_ent tauXE sigmaE +
               (dim 'H[HL]_Zl)%:R^-1 * T).
          change (lhsT + (- T) <= rhsT + (- T)).
          by rewrite lerD2r.
        }
        apply: (le_trans Hscaled).
        rewrite mulrDr.
        have -> :
            (dim 'H[HL]_Zl)%:R *
              ((dim 'H[HL]_Zl)%:R^-1 * T) = T.
        {
          by rewrite mulrA mulfV // mul1r.
        }
        by rewrite addrK.
      }
      have Hinside2 :
          (dim 'H[HL]_Zl)%:R * collision_ent tauXE sigmaE
        <= (dim 'H[HL]_Zl)%:R *
            expR (- hmin E tauXE * ln 2%:R).
        exact: (ler_wpM2l dZ_ge0 Hcoll).
      have HZlog_exp :
          @expR R (log2 (dim 'H[HL]_Zl)%:R * ln 2%:R) =
          (dim 'H[HL]_Zl)%:R.
      {
        have HdimZ_pos : (0 < (dim 'H[HL]_Zl)%:R :> R)%R
          by rewrite ltr0n dim_proper.
        rewrite /log2 /=.
        change (expR ((ln ((dim 'H[HL]_Zl)%:R : R) *
          (ln (2%:R : R))^-1) * ln (2%:R : R)) =
          ((dim 'H[HL]_Zl)%:R : R)).
        rewrite mulfVK ?(lnK HdimZ_pos) //.
        exact: lt0r_neq0 ln2_gt0.
      }
      apply: (le_trans Hucoll).
      apply: ler_pM.
      - by rewrite invr_ge0 ler0n.
      - exact: sqrtr_ge0 _.
      - exact: lexx.
      - rewrite ler_sqrt; last first.
          by apply: (ltW (expR_gt0 _)).
        apply: (le_trans Hinside1).
        apply: (le_trans Hinside2).
        rewrite -[X in X * _ <= _]HZlog_exp -expRD.
        rewrite ler_expR.
        by rewrite mulrBl mulNr.
    }
    have Hnonsmooth :
        dist_from_uniform tauZFE <=
        (2%:R)^-1 * Num.sqrt (expR ((log2 (dim 'H[HL]_Zl)%:R -
          smooth_hmin E eps rhoXE) * ln 2%:R)).
    {
      apply: (le_trans Hnonsmooth_tau).
      apply: ler_pM.
      - by rewrite invr_ge0 ler0n.
      - exact: sqrtr_ge0 _.
      - exact: lexx.
      - rewrite ler_sqrt; last first.
          by apply: (ltW (expR_gt0 _)).
        rewrite ler_expR (ler_pM2r ln2_gt0).
        have Hneg_le :
            - hmin E tauXE <= - smooth_hmin E eps rhoXE.
        {
          by rewrite lerN2 Hsmooth_le_tau.
        }
        rewrite [log2 (dim 'H[HL]_Zl)%:R - hmin E tauXE]addrC.
        rewrite [log2 (dim 'H[HL]_Zl)%:R - smooth_hmin E eps rhoXE]addrC lerD2r.
        exact: Hneg_le.
    }
    have Htri := @dist_uniform_pd_triangle R L HL Zl (Fl :|: E)
      disZl_FE rhoZFE tauZFE HrhoZFE_psd HtauZFE_psd HrhoZFE_tr HtauZFE_tr.
    apply: (le_trans Htri).
    exact: lerD Hpd_post Hnonsmooth.
  - have Hzero_psd :
        (0 : 'F[HL]_(Zl :|: (Fl :|: E))) \is psdlf.
      by rewrite qualifE h2mx0 psdmx0.
    have Hpd_zero_eq :
        forall tau : 'F[HL]_(Zl :|: (Fl :|: E)),
          tau \is psdlf ->
          @complex.Re R (\Tr tau) <= 1 ->
          pur_dist (0 : 'F[HL]_(Zl :|: (Fl :|: E))) tau =
            Num.sqrt (@complex.Re R (\Tr tau)).
    {
      move=> tau Ptau Htau_tr0.
      have Hzero_mx_psd :
          h2mx (0 : 'F[HL]_(Zl :|: (Fl :|: E))) \is psdmx.
      {
        by move: Hzero_psd; rewrite qualifE.
      }
      have Htau_mx_psd : h2mx tau \is psdmx.
      {
        by move: Ptau; rewrite qualifE.
      }
      have Hgfid0 :
          gfid (0 : 'F[HL]_(Zl :|: (Fl :|: E))) tau =
          Num.sqrt (1 - @complex.Re R (\Tr tau)).
      {
        rewrite /gfid.
        rewrite (alt_gfid_gen Hzero_mx_psd Htau_mx_psd).
        have -> :
            @complex.Re R
              (trnorm
                (sqrtmx
                  (h2mx (0 : 'F[HL]_(Zl :|: (Fl :|: E)))) *m
                 sqrtmx (h2mx tau))) = 0.
        {
          by rewrite h2mx0 sqrtmx0 mul0mx trnorm0 raddf0.
        }
        have -> :
            @complex.Re R
              (1 - \tr
                (h2mx (0 : 'F[HL]_(Zl :|: (Fl :|: E))))) = 1.
        {
          by rewrite h2mx0 mxtrace0 subr0.
        }
        have -> :
            @complex.Re R (1 - \tr (h2mx tau)) =
            1 - @complex.Re R (\Tr tau).
        {
          by rewrite raddfB /= /lftrace.
        }
        by rewrite sqrtr1 mul1r add0r.
      }
      rewrite /pur_dist.
      pose a := 1 - @complex.Re R (\Tr tau).
      have Ha_ge0 : 0 <= a.
      {
        rewrite /a.
        by rewrite subr_ge0.
      }
      have -> :
          (gfid
             (0 : 'F[HL]_(Zl :|: (Fl :|: E))) tau)^2 = a.
      {
        rewrite Hgfid0.
        exact: sqr_sqrtr Ha_ge0.
      }
      by rewrite /a opprB addrCA subrr addr0.
    }
    have Hpd_post0 :
        pur_dist rhoZFE (0 : 'F[HL]_(Zl :|: (Fl :|: E))) <= eps.
    {
      have Hsym :
          pur_dist rhoZFE
            (0 : 'F[HL]_(Zl :|: (Fl :|: E)) ) =
          pur_dist
            (0 : 'F[HL]_(Zl :|: (Fl :|: E)) ) rhoZFE.
      {
        have HrhoZFE_mx_psd : h2mx rhoZFE \is psdmx
          by move: HrhoZFE_psd; rewrite qualifE.
        have Hzero_mx_psd :
            h2mx (0 : 'F[HL]_(Zl :|: (Fl :|: E))) \is psdmx
          by move: Hzero_psd; rewrite qualifE.
        by rewrite /pur_dist /gfid
          (gfid_sym_mx HrhoZFE_mx_psd Hzero_mx_psd).
      }
      rewrite Hsym.
      rewrite (Hpd_zero_eq rhoZFE HrhoZFE_psd HrhoZFE_tr) /rhoZFE.
      rewrite (@post_hash_trace_preserve R L HL X E Fl Zl
        disXE disXF disXZ disEF disEZ disFZ Fh rhoXE Hrho).
      exact: Hlarge.
    }
    have Hdfu0 :
        dist_from_uniform
          (0 : 'F[HL]_(Zl :|: (Fl :|: E))) = 0.
    {
      apply/eqP; rewrite eq_le.
      apply/andP; split.
      - have Hfeas0 :
            @dist_uniform_feasible R L HL Zl (Fl :|: E)
              (0 : 'F[HL]_(Zl :|: (Fl :|: E))) 0.
        {
          exists (0 : 'F[HL]_(Fl :|: E)); split.
          - by rewrite psdlfE lexx.
          - split.
            + by rewrite !linear0.
            + by rewrite sdotf0 scaler0 subr0 /trnormH h2mx0 trnorm0 mulr0.
        }
        exact: dist_uniform_lb Hfeas0.
      - apply: (@dist_uniform_glb R L HL Zl (Fl :|: E) disZl_FE
          (0 : 'F[HL]_(Zl :|: (Fl :|: E))) 0).
        + exact: Hzero_psd.
        + move=> v [sigma [Hsigma_psd [_ ->]]].
          apply: mulr_ge0.
          * by rewrite invr_ge0 ler0n.
          * rewrite /trnormH.
            have := trnorm_ge0 (h2mx
              ((0 : 'F[HL]_(Zl :|: (Fl :|: E))) -
               (dim 'H[HL]_Zl)%:R^-1 *:
                 ((\1 : 'F_Zl) \O sigma))).
            by rewrite lecE /= => /andP[].
    }
    have Hterm_ge0 :
        0 <= (2%:R)^-1 * Num.sqrt
          (expR ((log2 (dim 'H[HL]_Zl)%:R -
            smooth_hmin E eps rhoXE) * ln 2%:R)).
    {
      apply: mulr_ge0.
      - by rewrite invr_ge0 ler0n.
      - exact: sqrtr_ge0 _.
    }
    have Hzero_tr : @complex.Re R (\Tr
      (0 : 'F[HL]_(Zl :|: (Fl :|: E)))) <= 1.
    {
      by rewrite linear0 ler01.
    }
    have Htri := @dist_uniform_pd_triangle R L HL Zl (Fl :|: E)
      disZl_FE rhoZFE
      (0 : 'F[HL]_(Zl :|: (Fl :|: E)))
      HrhoZFE_psd Hzero_psd HrhoZFE_tr Hzero_tr.
    rewrite Hdfu0 in Htri.
    apply: (le_trans Htri).
    have Hsum :
        pur_dist rhoZFE
          (0 : 'F[HL]_(Zl :|: (Fl :|: E))) + 0 <=
        eps + (2%:R)^-1 * Num.sqrt
          (expR ((log2 (dim 'H[HL]_Zl)%:R -
            smooth_hmin E eps rhoXE) * ln 2%:R)).
    {
      exact: lerD Hpd_post0 Hterm_ge0.
    }
    exact Hsum.
Qed.
(* ================================================================== *)
(* Quantum Leftover Hash Lemma (δ-almost-two-universal hashing)         *)
(* Tomamichel-Schaffner-Smith-Renner, 'Leftover Hashing Against Quantum *)
(* Side Information' (IEEE Trans. IT 57:5524 (2011); arXiv:1002.2436),   *)
(* Thm. 7 — tex thm:almost-two-universal-hashing                         *)
(* math: For a δ-almost-two-universal hash family F: X × F → Z, a        *)
(*   NORMALIZED CQ state ρ_XE, smoothing parameters ε ≥ 0 and ε̄ > 0,    *)
(*     d_u(Z | FE)_{ρ_ZFE} ≤ ε + ε̄ +                                    *)
(*       ½·√((2^ℓ·δ − 1) + 2^{ℓ − H^ε_min(X|E)_ρ}·(2/ε̄² + 1/(1−ε²))),   *)
(*   where ℓ := log₂|Z|, ρ_ZFE is the post-hash state.                  *)
(* Note: the paper prints the last factor as the constant   *)
(*   2^{log(2/ε̄²+1)} = (2/ε̄²+1).  The honest consequence of             *)
(*   lemma:min-bound-1 (which we prove, via `coll_bound`) carries the     *)
(*   input trace 1/Tr ρ̂ of the smoothing witness ρ̂; bounding             *)
(*   Tr ρ̂ ≥ 1−ε² (ρ normalized) yields the closed form 1/(1−ε²), which   *)
(*   coincides with the printed (2/ε̄²+1) at ε = 0.                       *)
(* path: lhl:almost_two_universal_hashing *)
Theorem almost_two_universal_hashing
    (Fh : 'Idx[HL]_Fl -> 'Idx[HL]_X -> 'Idx[HL]_Zl)
    (delta eps eps_bar : R) (rhoXE : 'F[HL]_(X :|: E)) :
  rhoXE \is psdlf ->
  @complex.Re R (\Tr rhoXE) = 1 ->
  is_cq_state rhoXE ->
  0 <= delta ->
  delta_almost_two_univ Fh delta ->
  0 <= eps ->
  0 < eps_bar ->
  let rhoZFE := post_hash_state disXE Fh rhoXE in
  dist_from_uniform rhoZFE <=
  eps + eps_bar + (2%:R)^-1 * Num.sqrt (
    (dim 'H[HL]_Zl)%:R * delta - 1 + eps ^+ 2 +
    expR ((log2 (dim 'H[HL]_Zl)%:R - smooth_hmin E eps rhoXE) * ln 2%:R)
      * (2%:R * eps_bar^-2 + (1 - eps ^+ 2)^-1)).
Proof.
  move=> Hrho Hrho_tr1 Hcq Hdelta_ge0 HFh Heps Hepsbar /=.
  set rhoZFE := post_hash_state disXE Fh rhoXE.
  have Hrho_tr : @complex.Re R (\Tr rhoXE) <= 1 by rewrite Hrho_tr1.
  have HrhoZFE_psd : rhoZFE \is psdlf
    by exact: (@post_hash_psdlf R L HL X E Fl Zl
      disXE disXF disXZ disEF disEZ disFZ Fh rhoXE Hrho).
  have HrhoZFE_tr : @complex.Re R (\Tr rhoZFE) <= 1.
  {
    rewrite /rhoZFE (@post_hash_trace_preserve R L HL X E Fl Zl
      disXE disXF disXZ disEF disEZ disFZ Fh rhoXE Hrho).
    exact: Hrho_tr.
  }
  pose dZ := (dim 'H[HL]_Zl)%:R : R.
  have HdZ_pos : 0 < dZ by rewrite /dZ ltr0n dim_proper.
  have Hexp_log2 : forall y : R, 0 < y -> expR (log2 y * ln 2%:R) = y.
  {
    move=> y Hy.
    have Hln2 : ln 2%:R != 0 :> R by exact: lt0r_neq0 ln2_gt0.
    by rewrite /log2 -mulrA mulVf // mulr1 lnK.
  }
  have [Hepslt | Hlarge] :=
      ltP eps (Num.sqrt (@complex.Re R (\Tr rhoXE))).
  - (* ---------- small case: eps < √(Tr ρ) = 1 ---------- *)
    have Heps_small : 0 <= eps < Num.sqrt (@complex.Re R (\Tr rhoXE))
      by apply/andP.
    have [tauXE [Htau_ball [Htau_cq Htau_hminE]]] :=
      @cq_smoothing R L HL X E disXE eps rhoXE Hrho Hrho_tr Heps Hepslt Hcq.
    have Htau_psd : tauXE \is psdlf := eps_ball_psdlf Htau_ball.
    have Htau_tr : @complex.Re R (\Tr tauXE) <= 1 := eps_ball_trlf Htau_ball.
    have Htau_tr_pos : 0 < @complex.Re R (\Tr tauXE)
      := eps_ball_trlf_gt0 Htau_ball.
    have [rhobar [Hrhobar_psd Hrhobar_tr1 Hrhobar_cq Hrhobar_ball Hrhobar_coll]]
      := @coll_bound R L HL X E disXE eps_bar tauXE
           Htau_psd Htau_tr_pos Htau_tr Htau_cq Hepsbar.
    have Hrhobar_tr : @complex.Re R (\Tr rhobar) <= 1
      by rewrite Hrhobar_tr1; exact: Htau_tr.
    pose rhobarZFE := post_hash_state disXE Fh rhobar.
    have HrhobarZFE_psd : rhobarZFE \is psdlf
      by exact: (@post_hash_psdlf R L HL X E Fl Zl
        disXE disXF disXZ disEF disEZ disFZ Fh rhobar Hrhobar_psd).
    have HrhobarZFE_tr : @complex.Re R (\Tr rhobarZFE) <= 1.
    {
      rewrite /rhobarZFE (@post_hash_trace_preserve R L HL X E Fl Zl
        disXE disXF disXZ disEF disEZ disFZ Fh rhobar Hrhobar_psd).
      exact: Hrhobar_tr.
    }
    (* (P1) smoothing witness keeps trace ≥ 1 − ε²                          *)
    (* via 1−ε² ≤ F̄(τ,ρ)² ≤ Tr τ (Cauchy–Schwarz on √ρ√τ, with Tr ρ = 1).  *)
    have Htau_tr_lb : 1 - eps ^+ 2 <= @complex.Re R (\Tr tauXE).
    {
      have Hrho_mx : h2mx rhoXE \is psdmx by move: Hrho; rewrite qualifE.
      have Htau_mx : h2mx tauXE \is psdmx by move: Htau_psd; rewrite qualifE.
      have HRe_tau_ge0 : 0 <= @complex.Re R (\Tr tauXE) by apply: ltW.
      have Htr_rho_mx : \tr (h2mx rhoXE) = 1.
      {
        have Hreal : \Tr rhoXE \is Num.real := ger0_real (psdlf_trlf Hrho).
        by rewrite -[\tr (h2mx rhoXE)]/(\Tr rhoXE) -(RRe_real Hreal) Hrho_tr1 rmorph1.
      }
      have Htr_rho_Re : @complex.Re R (\tr (h2mx rhoXE)) = 1
        by rewrite Htr_rho_mx -(re_realid 1).
      have Hrho_den : h2mx rhoXE \is denmx.
      {
        apply/denmxP; split; first exact: Hrho_mx.
        by rewrite Htr_rho_mx.
      }
      have Htau_den : h2mx tauXE \is denmx.
      {
        apply/denmxP; split; first exact: Htau_mx.
        have Hreal : \Tr tauXE \is Num.real := ger0_real (psdlf_trlf Htau_psd).
        by rewrite -[\tr (h2mx tauXE)]/(\Tr tauXE) -(RRe_real Hreal) lecR.
      }
      have Hgfid_ge0 : 0 <= gfid tauXE rhoXE
        by rewrite /gfid; exact: (gfid_ge0_mx Htau_mx Hrho_mx).
      have Hgfid_le1 : gfid tauXE rhoXE <= 1
        by rewrite /gfid; exact: (gfid_le1_mx Htau_den Hrho_den).
      have Hgfid_le : gfid tauXE rhoXE <= Num.sqrt (@complex.Re R (\Tr tauXE)).
      {
        rewrite /gfid (gfid_sym_mx Htau_mx Hrho_mx)
          (gfid_eq_fid_tr1_mx Hrho_mx Htau_mx Htr_rho_mx Htau_tr).
        apply: le_trans (trnorm_sqrt_cs Hrho_mx Htau_mx) _.
        by rewrite Htr_rho_Re sqrtr1 mul1r.
      }
      have Hpd_ge0 : 0 <= pur_dist tauXE rhoXE
        by rewrite /pur_dist; exact: sqrtr_ge0.
      have Hpd : pur_dist tauXE rhoXE <= eps := eps_ball_pur_dist Htau_ball.
      have Hgfid_sq_le : (gfid tauXE rhoXE) ^+ 2 <= @complex.Re R (\Tr tauXE).
      {
        rewrite -(sqr_sqrtr HRe_tau_ge0) !expr2.
        by apply: ler_pM.
      }
      have Hgfid_sq_le1 : (gfid tauXE rhoXE) ^+ 2 <= 1.
      {
        rewrite expr2 -[leRHS]mulr1.
        by apply: ler_pM.
      }
      have Hpd_sq : (pur_dist tauXE rhoXE) ^+ 2 = 1 - (gfid tauXE rhoXE) ^+ 2.
      {
        rewrite /pur_dist sqr_sqrtr.
        - by [].
        - by rewrite subr_ge0.
      }
      have Heps_sq : (pur_dist tauXE rhoXE) ^+ 2 <= eps ^+ 2.
      {
        rewrite !expr2.
        by apply: ler_pM.
      }
      have Hgfid_sq_ge : 1 - eps ^+ 2 <= (gfid tauXE rhoXE) ^+ 2.
      {
        move: Heps_sq; rewrite Hpd_sq => Hle.
        by rewrite lerBlDr addrC -lerBlDr.
      }
      exact: le_trans Hgfid_sq_ge Hgfid_sq_le.
    }
    (* (P2) the smoothing witness attains the smooth min-entropy *)
    have Hhmin_eq : hmin E tauXE = smooth_hmin E eps rhoXE.
    {
      have Hphi_pos : 0 < phi_min E tauXE.
      { apply: phi_min_pos_trace;
          [exact: Htau_psd | exact: Htau_tr | exact: Htau_tr_pos]. }
      have HhminE_tau : hminE E tauXE = (hmin E tauXE)%:E.
      { by rewrite /hminE /hmin (elog2_gt0 Hphi_pos) EFinN. }
      have HsmoothE : smooth_hminE E eps rhoXE = (smooth_hmin E eps rhoXE)%:E.
      { exact: (@smooth_hminE_EFin R L HL X E disXE eps rhoXE
          Hrho Hrho_tr Heps_small). }
      apply: EFin_inj.
      by rewrite -HhminE_tau -Htau_hminE HsmoothE.
    }
    (* (P3) non-smooth bound on ρ̄ via uniform_to_collision + privacy_amp.   *)
    (* Reference τ_FE := (1/|F|) I_F ⊗ ρ̄_E is exactly the post-hash          *)
    (* F-marginal, so both the 4-point term of uniform_to_collision and the   *)
    (* δ-term of privacy_amp collapse to a bare trace via pinvlf_sqrtH_quad_id.*)
    have Hnonsmooth : dist_from_uniform rhobarZFE <=
      (2%:R)^-1 * Num.sqrt (dZ *
        collision_ent rhobar (ptrace_castl disXE rhobar)
        + (dZ * delta * @complex.Re R (\Tr tauXE)
           - @complex.Re R (\Tr tauXE))).
    {
      have HsigmaE_psd : ptrace_castl disXE rhobar \is psdlf
        by exact: (@ptrace_castl_psdlf R L HL X E disXE rhobar Hrhobar_psd).
      have HsigmaE_tr : @complex.Re R (\Tr (ptrace_castl disXE rhobar))
                        = @complex.Re R (\Tr tauXE)
        by rewrite trlf_ptrace_castl Hrhobar_tr1.
      have disFE : [disjoint Fl & E] by rewrite disjoint_sym.
      pose rhoF_sigmaE :=
        ((dim 'H[HL]_Fl)%:R^-1)%:C *: ((\1 : 'F_Fl) \O ptrace_castl disXE rhobar).
      have Hlift_psd :
          ((\1 : 'F_Fl) \O ptrace_castl disXE rhobar : 'F[HL]_(Fl :|: E))
            \is psdlf.
      {
        have -> : ((\1 : 'F_Fl) \O ptrace_castl disXE rhobar
                    : 'F[HL]_(Fl :|: E)) =
                  (\1 : 'F_Fl) \⊗ ptrace_castl disXE rhobar
          by apply: to_Fnd_inj; rewrite (sdotFT _ _ disFE) to_Fnd_tenE.
        rewrite psdlfE; apply: tenf_ge0;
          [exact: disFE | exact: lef01 | by rewrite -psdlfE].
      }
      have HrhoF_sigma_psd : rhoF_sigmaE \is psdlf
        by rewrite /rhoF_sigmaE; apply: psdlfZ;
          [by rewrite lecR invr_ge0 | exact: Hlift_psd].
      have HrhoF_sigma_tr_eq : \Tr rhoF_sigmaE = \Tr (ptrace_castl disXE rhobar).
      {
        rewrite /rhoF_sigmaE linearZ/=
          (trlf_lift_I disFE (ptrace_castl disXE rhobar)) mulrA.
        have HdimF_neq0 : ((dim 'H[HL]_Fl)%:R : C) != 0
          by rewrite pnatr_eq0 -lt0n dim_proper.
        have Hscalar_eq :
            ((dim 'H[HL]_Fl)%:R^-1)%:C = @GRing.inv C ((dim 'H[HL]_Fl)%:R)
          by rewrite -natrC -fmorphV.
        have Hscale1 :
            ((dim 'H[HL]_Fl)%:R^-1)%:C * (dim 'H[HL]_Fl)%:R = 1 :> C.
        { rewrite Hscalar_eq. by rewrite mulVf. }
        by rewrite Hscale1 mul1r.
      }
      have HrhoF_sigma_tr_t : @complex.Re R (\Tr rhoF_sigmaE)
                              = @complex.Re R (\Tr tauXE)
        by rewrite HrhoF_sigma_tr_eq HsigmaE_tr.
      have HrhoF_sigma_tr : @complex.Re R (\Tr rhoF_sigmaE) <= 1
        by rewrite HrhoF_sigma_tr_t.
      have Hmarg : ptrace_castl disZl_FE rhobarZFE = rhoF_sigmaE.
      { by rewrite /rhobarZFE (@post_hash_ptrace_Z_CQ R L HL X E Fl Zl
          disXE disXF disXZ disEF disEZ disFZ Fh rhobar Hrhobar_psd Hrhobar_cq). }
      have Hsupp_post :
          (supph (ptrace_castl disZl_FE rhobarZFE) `<=` supph rhoF_sigmaE)%HS.
      { rewrite Hmarg; exact: lexx. }
      have Hucoll := @uniform_to_collision R L HL Zl (Fl :|: E)
        disZl_FE rhobarZFE rhoF_sigmaE
        HrhobarZFE_psd HrhoF_sigma_psd HrhoF_sigma_tr Hsupp_post.
      have Hsub :
          @complex.Re R (\Tr (ptrace_castl disZl_FE rhobarZFE \o
            pinvlf (sqrtH rhoF_sigmaE) \o ptrace_castl disZl_FE rhobarZFE \o
            pinvlf (sqrtH rhoF_sigmaE))) = @complex.Re R (\Tr tauXE)
        by rewrite Hmarg (pinvlf_sqrtH_quad_id HrhoF_sigma_psd) HrhoF_sigma_tr_t.
      rewrite /= Hsub in Hucoll.
      apply: (le_trans Hucoll).
      apply: ler_wpM2l; first by rewrite invr_ge0 ler0n.
      apply: ler_wsqrtr.
      have Hpa := @privacy_amp R L HL X E Fl Zl
        disXE disXF disXZ disEF disEZ disFZ rhobar (ptrace_castl disXE rhobar)
        Fh delta Hrhobar_psd Hrhobar_tr HsigmaE_psd Hrhobar_cq Hdelta_ge0 HFh.
      have Hqterm :
          @complex.Re R (\Tr (ptrace_castl disXE rhobar \o
            pinvlf (sqrtH (ptrace_castl disXE rhobar)) \o
            ptrace_castl disXE rhobar \o
            pinvlf (sqrtH (ptrace_castl disXE rhobar)))) = @complex.Re R (\Tr tauXE)
        by rewrite (pinvlf_sqrtH_quad_id HsigmaE_psd) HsigmaE_tr.
      rewrite /= Hqterm -/rhobarZFE -/rhoF_sigmaE in Hpa.
      have HdZ_ge0 : 0 <= dZ by apply: ltW.
      have Hstep := ler_wpM2l HdZ_ge0 Hpa.
      rewrite mulrDr mulrA in Hstep.
      rewrite /dZ addrA lerD2r.
      exact: Hstep.
    }
    (* (P4) feed the collision bound + (P1),(P2) into the target form *)
    have Hdu_rhobar : dist_from_uniform rhobarZFE <=
      (2%:R)^-1 * Num.sqrt (dZ * delta - 1 + eps ^+ 2 +
        expR ((log2 dZ - smooth_hmin E eps rhoXE) * ln 2%:R)
          * (2%:R * eps_bar^-2 + (1 - eps ^+ 2)^-1)).
    {
      have Heps_lt1 : eps < 1 by move: Hepslt; rewrite Hrho_tr1 sqrtr1.
      have Heps2_lt1 : eps ^+ 2 < 1.
      { rewrite expr2 -[ltRHS]mulr1; apply: ltr_pM => //; exact: Heps. }
      have H1meps2_pos : 0 < 1 - eps ^+ 2 by rewrite subr_gt0.
      have Heb2_pos : 0 < eps_bar ^+ 2 by exact: exprn_gt0.
      have HKt_pos : 0 < 2%:R * eps_bar^-2 + (@complex.Re R (\Tr tauXE))^-1.
      {
        apply: addr_gt0; last by rewrite invr_gt0.
        by apply: mulr_gt0; [exact: ltr0n | rewrite invr_gt0].
      }
      apply: (le_trans Hnonsmooth).
      apply: ler_wpM2l; first by rewrite invr_ge0 ler0n.
      apply: ler_wsqrtr.
      rewrite [leLHS]addrC.
      apply: lerD.
      - (* sub-normalisation term: dZ·δ·t − t ≤ dZ·δ − 1 + ε²,            *)
        (* t := Re Tr τ ∈ [1−ε²,1].  Split: dZ·δ·t ≤ dZ·δ and −t ≤ ε²−1.  *)
        have HA : dZ * delta * @complex.Re R (\Tr tauXE) <= dZ * delta.
        { rewrite -[X in _ <= X]mulr1; apply: ler_wpM2l.
          - by apply: mulr_ge0; [exact: ltW HdZ_pos | exact: Hdelta_ge0].
          - exact: Htau_tr. }
        have HB : - @complex.Re R (\Tr tauXE) <= eps ^+ 2 - 1
          by rewrite -(opprB 1 (eps ^+ 2)) lerN2; exact: Htau_tr_lb.
        apply: (le_trans (lerD HA HB)).
        by rewrite addrA addrAC.
      - (* main term: dZ·Γ_C(ρ̄|ρ̄_E) ≤ expR(…)·(2/ε̄²+(1−ε²)⁻¹). *)
        apply: (@le_trans _ _
          (dZ * (expR (- hmin E tauXE * ln 2%:R)
            * (2%:R * eps_bar^-2 + (@complex.Re R (\Tr tauXE))^-1)))).
        + apply: ler_wpM2l; first exact: ltW.
          apply: (le_trans Hrhobar_coll).
          by rewrite mulrDl expRD (Hexp_log2 _ HKt_pos).
        + rewrite mulrA.
          have HdZexp : dZ * expR (- hmin E tauXE * ln 2%:R)
            = expR ((log2 dZ - smooth_hmin E eps rhoXE) * ln 2%:R).
          { rewrite -{1}(Hexp_log2 _ HdZ_pos) -expRD; congr expR.
            by rewrite Hhmin_eq mulrBl mulNr. }
          rewrite HdZexp.
          apply: ler_wpM2l; first by apply: ltW; exact: expR_gt0.
          rewrite lerD2l lef_pV2 ?inE ?posrE //.
    }
    have Hpd_sym : forall a b : 'F[HL]_(X :|: E),
        a \is psdlf -> b \is psdlf -> pur_dist a b = pur_dist b a.
    {
      move=> a b Pa Pb.
      have Pa_mx : h2mx a \is psdmx by move: Pa; rewrite qualifE.
      have Pb_mx : h2mx b \is psdmx by move: Pb; rewrite qualifE.
      by rewrite /pur_dist /gfid (gfid_sym_mx Pa_mx Pb_mx).
    }
    have Hpd_post : pur_dist rhoZFE rhobarZFE <= eps + eps_bar.
    {
      have Hpd_mono := @pd_mono_post_hash R L HL X E Fl Zl
        disXE disXF disXZ disEF disEZ disFZ Fh rhoXE rhobar
        Hrho Hrhobar_psd Hrho_tr Hrhobar_tr.
      apply: (le_trans Hpd_mono).
      have Htri := @pd_metric_triangle R L HL (X :|: E) rhoXE rhobar tauXE
        Hrho Hrhobar_psd Htau_psd Hrho_tr Hrhobar_tr Htau_tr.
      apply: (le_trans Htri).
      have H1 : pur_dist rhoXE tauXE <= eps.
      {
        rewrite (Hpd_sym _ _ Hrho Htau_psd).
        exact: eps_ball_pur_dist Htau_ball.
      }
      have H2 : pur_dist tauXE rhobar <= eps_bar.
      {
        rewrite (Hpd_sym _ _ Htau_psd Hrhobar_psd).
        exact: eps_ball_pur_dist Hrhobar_ball.
      }
      exact: lerD H1 H2.
    }
    have Htri := @dist_uniform_pd_triangle R L HL Zl (Fl :|: E)
      disZl_FE rhoZFE rhobarZFE
      HrhoZFE_psd HrhobarZFE_psd HrhoZFE_tr HrhobarZFE_tr.
    apply: (le_trans Htri).
    exact: lerD Hpd_post Hdu_rhobar.
  - (* ---------- large case: eps ≥ √(Tr ρ) = 1 ---------- *)
    (* d_u(ρ_ZFE) ≤ P(ρ_ZFE, 0) = √(Tr ρ_ZFE) = √(Tr ρ) ≤ ε ≤ the bound. *)
    have Hzero_psd : (0 : 'F[HL]_(Zl :|: (Fl :|: E))) \is psdlf
      by rewrite qualifE h2mx0 psdmx0.
    have Hpd_zero_eq :
        forall tau : 'F[HL]_(Zl :|: (Fl :|: E)),
          tau \is psdlf ->
          @complex.Re R (\Tr tau) <= 1 ->
          pur_dist (0 : 'F[HL]_(Zl :|: (Fl :|: E))) tau =
            Num.sqrt (@complex.Re R (\Tr tau)).
    {
      move=> tau Ptau Htau_tr0.
      have Hzero_mx_psd : h2mx (0 : 'F[HL]_(Zl :|: (Fl :|: E))) \is psdmx
        by move: Hzero_psd; rewrite qualifE.
      have Htau_mx_psd : h2mx tau \is psdmx by move: Ptau; rewrite qualifE.
      have Hgfid0 :
          gfid (0 : 'F[HL]_(Zl :|: (Fl :|: E))) tau =
          Num.sqrt (1 - @complex.Re R (\Tr tau)).
      {
        rewrite /gfid (alt_gfid_gen Hzero_mx_psd Htau_mx_psd).
        have -> :
            @complex.Re R
              (trnorm (sqrtmx (h2mx (0 : 'F[HL]_(Zl :|: (Fl :|: E)))) *m
                 sqrtmx (h2mx tau))) = 0
          by rewrite h2mx0 sqrtmx0 mul0mx trnorm0 raddf0.
        have -> :
            @complex.Re R (1 - \tr (h2mx (0 : 'F[HL]_(Zl :|: (Fl :|: E))))) = 1
          by rewrite h2mx0 mxtrace0 subr0.
        have -> :
            @complex.Re R (1 - \tr (h2mx tau)) = 1 - @complex.Re R (\Tr tau)
          by rewrite raddfB /= /lftrace.
        by rewrite sqrtr1 mul1r add0r.
      }
      rewrite /pur_dist.
      pose a := 1 - @complex.Re R (\Tr tau).
      have Ha_ge0 : 0 <= a by rewrite /a subr_ge0.
      have -> : (gfid (0 : 'F[HL]_(Zl :|: (Fl :|: E))) tau) ^ 2 = a
        by rewrite Hgfid0; exact: sqr_sqrtr Ha_ge0.
      by rewrite /a opprB addrCA subrr addr0.
    }
    have Hpd_post0 :
        pur_dist rhoZFE (0 : 'F[HL]_(Zl :|: (Fl :|: E))) <= eps.
    {
      have Hsym :
          pur_dist rhoZFE (0 : 'F[HL]_(Zl :|: (Fl :|: E))) =
          pur_dist (0 : 'F[HL]_(Zl :|: (Fl :|: E))) rhoZFE.
      {
        have HrhoZFE_mx_psd : h2mx rhoZFE \is psdmx
          by move: HrhoZFE_psd; rewrite qualifE.
        have Hzero_mx_psd : h2mx (0 : 'F[HL]_(Zl :|: (Fl :|: E))) \is psdmx
          by move: Hzero_psd; rewrite qualifE.
        by rewrite /pur_dist /gfid (gfid_sym_mx HrhoZFE_mx_psd Hzero_mx_psd).
      }
      rewrite Hsym (Hpd_zero_eq rhoZFE HrhoZFE_psd HrhoZFE_tr) /rhoZFE.
      rewrite (@post_hash_trace_preserve R L HL X E Fl Zl
        disXE disXF disXZ disEF disEZ disFZ Fh rhoXE Hrho).
      exact: Hlarge.
    }
    have Hdfu0 :
        dist_from_uniform (0 : 'F[HL]_(Zl :|: (Fl :|: E))) = 0.
    {
      apply/eqP; rewrite eq_le; apply/andP; split.
      - have Hfeas0 :
            @dist_uniform_feasible R L HL Zl (Fl :|: E)
              (0 : 'F[HL]_(Zl :|: (Fl :|: E))) 0.
        {
          exists (0 : 'F[HL]_(Fl :|: E)); split; first by rewrite psdlfE lexx.
          split; first by rewrite !linear0.
          by rewrite sdotf0 scaler0 subr0 /trnormH h2mx0 trnorm0 mulr0.
        }
        exact: dist_uniform_lb Hfeas0.
      - apply: (@dist_uniform_glb R L HL Zl (Fl :|: E) disZl_FE
          (0 : 'F[HL]_(Zl :|: (Fl :|: E))) 0); first exact: Hzero_psd.
        move=> v [sigma [Hsigma_psd [_ ->]]].
        apply: mulr_ge0; first by rewrite invr_ge0 ler0n.
        rewrite /trnormH.
        have := trnorm_ge0 (h2mx ((0 : 'F[HL]_(Zl :|: (Fl :|: E))) -
          (dim 'H[HL]_Zl)%:R^-1 *: ((\1 : 'F_Zl) \O sigma))).
        by rewrite lecE /= => /andP[].
    }
    have Hzero_tr : @complex.Re R (\Tr (0 : 'F[HL]_(Zl :|: (Fl :|: E)))) <= 1
      by rewrite linear0 ler01.
    have Hterm_ge0 :
        0 <= (2%:R)^-1 * Num.sqrt ((dim 'H[HL]_Zl)%:R * delta - 1 + eps ^+ 2 +
          expR ((log2 (dim 'H[HL]_Zl)%:R - smooth_hmin E eps rhoXE) * ln 2%:R)
            * (2%:R * eps_bar^-2 + (1 - eps ^+ 2)^-1)).
    { apply: mulr_ge0; [by rewrite invr_ge0 ler0n | exact: sqrtr_ge0]. }
    have Htri := @dist_uniform_pd_triangle R L HL Zl (Fl :|: E)
      disZl_FE rhoZFE (0 : 'F[HL]_(Zl :|: (Fl :|: E)))
      HrhoZFE_psd Hzero_psd HrhoZFE_tr Hzero_tr.
    apply: (le_trans Htri).
    rewrite Hdfu0 addr0.
    apply: (le_trans Hpd_post0).
    rewrite -addrA lerDl.
    by apply: addr_ge0; [exact: ltW | exact: Hterm_ge0].
Qed.
End LHL.
End FvqkdReal.
