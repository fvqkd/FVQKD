(* -------------------------------------------------------------------- *)
(* sm.v — Smoothing support property                                    *)
(* -------------------------------------------------------------------- *)
(* Module: entropy.smooth.sm                        *)
(* Source: Tomamichel, 'A Framework for Non-Asymptotic Quantum          *)
(*   Information Theory' (PhD thesis, arXiv:1203.2142), Proposition 5.1  *)
(*   — tex pr:smoothing/support.                                        *)
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
From entropy.conv Require Import prop minmax_dual.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Open Scope ring_scope.
Local Open Scope lfun_scope.
Local Open Scope hspace_scope.

Section FvqkdReal.
Variable R : realType.
Notation C := (@hermitian.C R).
Notation chsType := (@chsType R).

(* ================================================================== *)
(* Support property for smoothing (min half)                            *)
(* Tomamichel thesis (arXiv:1203.2142), Proposition 5.1 — tex pr:smoothing/support, min half. *)
(* math: Under Tomamichel's standing assumption ε < √tr(ρ), for               *)
(*   ρ ∈ S_≤(ℋ_{AB}), there exists τ̃ ∈ B^ε(ρ_{AB}) with                 *)
(*   τ̃ supported on supp(ρ_A) ⊗ supp(ρ_B) and                           *)
(*   H^ε_min(A|B)_ρ = H_min(A|B)_τ̃.                                     *)
(* consumer: pr_ss is used downstream by the BB84 secrecy proof. *)
(* ================================================================== *)

Section SmoothingSupport.
Variable (L : finType) (H : L -> chsType) (A B : {set L}).
Hypothesis disAB : [disjoint A & B].
Notation S_AB := (A :|: B).

(* path: entropy:smoothing_support_hmin -> lhl:cq_smoothing -> *)
(*   bb84:privacy_amplification -> bb84:bb84_secret *)
Lemma smoothing_support_hmin (eps : R) (rhoAB : 'F[H]_S_AB) :
  rhoAB \is denlf ->
  0 <= eps < Num.sqrt (@complex.Re R (\Tr rhoAB)) ->
  exists (tauAB : 'F[H]_S_AB),
    eps_ball eps rhoAB tauAB /\
    smooth_hminE B eps rhoAB = hminE B tauAB /\
    (supplf (ptrace_cast disAB rhoAB) \O supplf (ptrace_castl disAB rhoAB))
      \o tauAB = tauAB /\
    tauAB \o (supplf (ptrace_cast disAB rhoAB) \O supplf (ptrace_castl disAB rhoAB))
      = tauAB.
Proof.
  move=> Hrho_den /andP [Heps0 Hepslt].
  have Prho : rhoAB \is psdlf := denlf_psd Hrho_den.
  have Htr : @complex.Re R (\Tr rhoAB) <= 1.
  { have Hreal : \Tr rhoAB \is Num.real := ger0_real (psdlf_trlf Prho).
    by move: (denlf_trlf Hrho_den); rewrite -(RRe_real Hreal) lecR. }
  pose rhoA := ptrace_cast disAB rhoAB.
  pose rhoB := ptrace_castl disAB rhoAB.
  pose PA := (supplf rhoA : 'F[H]_A).
  pose PB := (supplf rhoB : 'F[H]_B).
  pose P :=
    (PA \O PB
      : 'F[H]_S_AB).
  have PrhoA : rhoA \is psdlf.
    exact: ptrace_cast_psdlf.
  have PrhoB : rhoB \is psdlf.
    exact: ptrace_castl_psdlf.
  have HrhoA_right : rhoA \o PA = rhoA.
  {
    rewrite /PA.
    exact: suppvlf.
  }
  have HrhoB_right : rhoB \o PB = rhoB.
  {
    rewrite /PB.
    exact: suppvlf.
  }
  have HrhoA_left : PA \o rhoA = rhoA.
  {
    have -> : PA = cosupplf rhoA.
    {
      rewrite /PA.
      have HrhoAh : rhoA^A = rhoA.
        exact: hermlf_adjE (psdlf_herm PrhoA).
      have HsupA : supplf rhoA^A = cosupplf rhoA.
        exact: supplf_adj rhoA.
      by rewrite HrhoAh in HsupA.
    }
    exact: cosupplfv.
  }
  have HrhoB_left : PB \o rhoB = rhoB.
  {
    have -> : PB = cosupplf rhoB.
    {
      rewrite /PB.
      have HrhoBh : rhoB^A = rhoB.
        exact: hermlf_adjE (psdlf_herm PrhoB).
      have HsupB : supplf rhoB^A = cosupplf rhoB.
        exact: supplf_adj rhoB.
      by rewrite HrhoBh in HsupB.
    }
    exact: cosupplfv.
  }
  have Hopt :
      exists tau0 : 'F[H]_S_AB, exists sigma0 : 'F[H]_B,
        eps_ball eps rhoAB tau0 /\
        sigma0 \is psdlf /\
        ((\1 : 'F[H]_A) \O sigma0 - tau0) \is psdlf /\
        phi_min B tau0 = @complex.Re R (\Tr sigma0) /\
        smooth_hmin B eps rhoAB = hmin B tau0 /\
        (forall tau : 'F[H]_S_AB,
          eps_ball eps rhoAB tau -> hmin B tau <= hmin B tau0).
  {
    pose n := dim 'H[H]_S_AB.
    pose b := dim 'H[H]_B.
    pose rhoM : 'M[C]_n := h2mx rhoAB.
    pose dB : R := b%:R.
    have Hn_pos : (0 < n)%N.
    {
      rewrite /n.
      exact: dim_proper.
    }
    pose pdistM (tau : 'M[C]_n) : R :=
      pur_dist (mx2h tau : 'F[H]_S_AB) rhoAB.
      pose BallM :=
        [set tau : 'M[C]_n |
          tau \is denmx /\
          pdistM tau <= eps]%classic.
    pose SigmaCubeM :=
      [set sigma : 'M[C]_b |
        sigma \is psdmx /\ \tr sigma <= dB%:C]%classic.
    pose lift_sigmaM (sigma : 'M[C]_b) : 'M[C]_n :=
      h2mx ((((\1 : 'F[H]_A) \O (mx2h sigma : 'F[H]_B))
              : 'F[H]_S_AB)).
    pose PairCubeM :=
      [set p : 'M[C]_n * 'M[C]_b | BallM p.1 /\ SigmaCubeM p.2]%classic.
    pose gapM (p : 'M[C]_n * 'M[C]_b) := lift_sigmaM p.2 - p.1.
    pose FeasM :=
      [set p : 'M[C]_n * 'M[C]_b |
        BallM p.1 /\ SigmaCubeM p.2 /\ gapM p \is psdmx]%classic.
      have HballM_compact : compact BallM.
      {
        pose DenM :=
          [set tau : 'M[C]_n | tau \is denmx]%classic.
        have HDenM_closed : closed DenM.
        {
          have HDen_denE :
              [set tau : 'M[C]_n | tau \is denmx]%classic =
              [set tau : 'M[C]_n | tau \is psdmx /\ @complex.Re R (\tr tau) <= 1]%classic.
          {
            apply/funext=> tau /=.
            apply/propext; split.
            - move=> Htau_den.
              have /denmxP[Htau_psd Htau_trC] := Htau_den.
              split; first exact: Htau_psd.
              by move: Htau_trC; rewrite lecE /= => /andP [_].
            - move=> [Htau_psd Htau_tr].
              exact: denmx_psd_re_tr_le Htau_psd Htau_tr.
          }
          have HDenE :
              [set tau : 'M[C]_n | tau \is psdmx /\ @complex.Re R (\tr tau) <= 1]%classic =
            setI [set tau : 'M[C]_n | (0 : 'M[C]_n) <= tau]%classic
                 [set tau : 'M[C]_n | \tr tau <= 1]%classic.
        {
          apply/funext=> tau /=.
          apply/propext; split.
          - move=> [Htau_psd Htau_tr].
            have Htau_tr_real : \tr tau \is Num.real.
            {
              exact: ger0_real (psdmx_trace Htau_psd).
            }
            split.
            + by rewrite le_lownerE subr0.
            + have -> : \tr tau = (@complex.Re R (\tr tau))%:C.
              {
                exact: esym (RRe_real Htau_tr_real).
              }
              by rewrite lecR.
          - move=> [Htau_ge0 Htau_tr].
            have Htau_psd : tau \is psdmx.
            {
              by rewrite le_lownerE subr0 in Htau_ge0.
            }
            have Htau_tr_real : \tr tau \is Num.real.
            {
              exact: ger0_real (psdmx_trace Htau_psd).
            }
            split.
            + exact: Htau_psd.
            + move: Htau_tr.
              have -> : \tr tau = (@complex.Re R (\tr tau))%:C.
              {
                exact: esym (RRe_real Htau_tr_real).
              }
              by rewrite lecR.
        }
          rewrite /DenM HDen_denE HDenE.
          apply: closedI.
          - exact: psdmx_closed n.
          - exact: closed_letr _.
      }
      have HballM_closed : closed BallM.
      {
          rewrite /BallM closedE => tauM Htau_near.
          have Htau_den :
              tauM \is denmx.
          {
            have Htau_den_near :
                ~ (\forall X \near tauM, ~ DenM X).
          {
            move=> Hnear_not_den.
              apply: Htau_near.
              near=> X.
              move=> HXball.
              have HXden : DenM X.
              {
                exact: HXball.1.
              }
            have HXnotden : ~ DenM X.
            {
              near: X.
              exact: Hnear_not_den.
            }
            exact: HXnotden HXden.
            Unshelve. end_near.
          }
          move: HDenM_closed.
          rewrite closedE.
          move=> /(_ tauM) Hclosed_tau.
            exact: Hclosed_tau Htau_den_near.
          }
          have /denmxP[Htau_psd Htau_trC] := Htau_den.
          have Htau_tr : @complex.Re R (\tr tauM) <= 1
            by move: Htau_trC; rewrite lecE /= => /andP [_].
        have Htau_psdlf : (mx2h tauM : 'F[H]_S_AB) \is psdlf.
        {
          by rewrite qualifE /= mx2hK.
        }
        have Hrho_psdlf : (mx2h rhoM : 'F[H]_S_AB) \is psdlf.
        {
          have -> : (mx2h rhoM : 'F[H]_S_AB) = rhoAB.
          {
            apply/h2mx_inj.
            by rewrite /rhoM mx2hK.
          }
          exact: Prho.
        }
        pose dtau := pdistM tauM.
          pose close_tau := (dtau <= eps).
          have [Htau_dist|Htau_far] := boolP close_tau.
          - exact: conj Htau_den Htau_dist.
        - move: Htau_far.
          rewrite /close_tau -ltNge => Htau_far.
          pose gap := dtau - eps.
          pose eta := gap / 2%:R.
          have Htwo_pos : 0 < (2%:R : R).
          {
            exact: ltr0Sn.
          }
          have Hgap_pos : 0 < gap.
          {
            rewrite /gap subr_gt0.
            exact: Htau_far.
          }
          have Heta_pos : 0 < eta.
          {
            rewrite /eta.
            exact: divr_gt0 Hgap_pos Htwo_pos.
          }
          have Heta_ge0 : 0 <= eta.
          {
            exact: ltW Heta_pos.
          }
          have Heta_lt_gap : eta < gap.
          {
            rewrite /eta ltr_pdivrMr.
            - rewrite mulr_natr mulr2n ltrDl.
              exact: Hgap_pos.
            - exact: Htwo_pos.
          }
          have [c Hc_pos Hc_bound] :
              exists2 c : C, 0 < c &
                forall X : 'M[C]_n, trnorm X <= c * mx_norm X.
          {
            exact: cmnorm_bounded.
          }
          apply: False_ind.
          apply: Htau_near.
          apply/nbhs_ballP.
          (* Ball radius halved so trnorm + |Tr diff| <= eta^2 (   *)
          (* `pd_gtd_ub'` returns `\sqrt(2D̄)` with `D̄ = D + ½|Tr ρ - Tr τ|`.    *)
          (* Since `|Tr ρ - Tr τ| <= ||ρ-τ||₁` (`trnorm_ge_tr`), shrinking the    *)
          (* ball to `eta^2 / 2` keeps the contradiction tight.)                  *)
          exists ((eta ^+ 2 / 2%:R)%:C / c).
          + have Heta2_pos : 0 < (eta ^+ 2 / 2%:R)%:C :> C.
            {
              rewrite ltcR.
              apply: divr_gt0; last by apply: ltr0Sn.
              by rewrite expr2; apply: mulr_gt0.
            }
            exact: divr_gt0 Heta2_pos Hc_pos.
            + move=> sigma Hsigma_close.
              move=> [Hsigma_den Hsigma_dist].
              have /denmxP[Hsigma_psd Hsigma_trC] := Hsigma_den.
              have Hsigma_tr : @complex.Re R (\tr sigma) <= 1
                by move: Hsigma_trC; rewrite lecE /= => /andP [_].
            have Hsigma_psdlf : (mx2h sigma : 'F[H]_S_AB) \is psdlf.
            {
              by rewrite qualifE /= mx2hK.
            }
            have Htrnorm_le : trnorm (tauM - sigma) <= (eta ^+ 2 / 2%:R)%:C.
            {
              have Hn0F : (n == 0)%N = false.
              {
                apply/negbTE.
                by rewrite -lt0n.
              }
              have H0nF : (0 == n)%N = false.
              {
                by rewrite eq_sym Hn0F.
              }
              have Hrad_pos : 0 < (eta ^+ 2 / 2%:R)%:C / c.
              {
                have Heta2_pos : 0 < (eta ^+ 2 / 2%:R)%:C :> C.
                {
                  rewrite ltcR.
                  apply: divr_gt0; last by apply: ltr0Sn.
                  by rewrite expr2; apply: mulr_gt0.
                }
                exact: divr_gt0 Heta2_pos Hc_pos.
              }
              have Hmx_lt :
                  mx_norm (tauM - sigma) < (eta ^+ 2 / 2%:R)%:C / c.
              {
                move: Hsigma_close.
                move/(@mxball_normE C n n tauM
                  ((eta ^+ 2 / 2%:R)%:C / c) sigma Hrad_pos).
                by rewrite /= ?Hn0F ?H0nF.
              }
              have Hmx_le :
                  mx_norm (tauM - sigma) <= (eta ^+ 2 / 2%:R)%:C / c.
              {
                move: (ltW Hmx_lt).
                by rewrite ?opprB ?mx_normN.
              }
              have Hscaled :
                  c * mx_norm (tauM - sigma) <= (eta ^+ 2 / 2%:R)%:C.
              {
                rewrite mulrC -ler_pdivlMr; last exact: Hc_pos.
                exact: Hmx_le.
              }
              exact: (le_trans (Hc_bound (tauM - sigma)) Hscaled).
            }
            have Htrnorm_real : trnorm (tauM - sigma) \is Num.real.
            {
              exact: ger0_real (trnorm_ge0 _).
            }
            have Htrnorm_leR :
                trnormH ((mx2h tauM : 'F[H]_S_AB) - mx2h sigma)
                  <= eta ^+ 2 / 2%:R.
            {
              rewrite /trnormH raddfB /= !mx2hK.
              move: Htrnorm_le.
              by rewrite -(RRe_real Htrnorm_real) lecR.
            }
            (* `|Re(Tr(tauM-sigma))|_R ≤ trnorm` via `trnorm_ge_tr`. *)
            have Htr_diff_real :
                \tr tauM - \tr sigma \is Num.real.
            {
              apply: rpredB; apply: ger0_real;
                [exact: psdmx_trace Htau_psd | exact: psdmx_trace Hsigma_psd].
            }
            have Hre_tr_diff_le :
                `|@complex.Re R (\Tr (mx2h tauM : 'F[H]_S_AB)) -
                  @complex.Re R (\Tr (mx2h sigma : 'F[H]_S_AB))|
                <= eta ^+ 2 / 2%:R.
            {
              rewrite /lftrace /= !mx2hK -raddfB/=.
              have Habs_C : `|\tr tauM - \tr sigma| <= trnorm (tauM - sigma).
              {
                rewrite -raddfB/=.
                exact: trnorm_ge_tr.
              }
              rewrite -(RRe_real Htr_diff_real) normc_real in Habs_C.
              have Hchain :
                  (`|@complex.Re R (\tr tauM - \tr sigma)|)%:C
                    <= (eta ^+ 2 / 2%:R)%:C
                := le_trans Habs_C Htrnorm_le.
              by rewrite -lecR.
            }
            have Hsum_le :
                trnormH ((mx2h tauM : 'F[H]_S_AB) - mx2h sigma) +
                `|@complex.Re R (\Tr (mx2h tauM : 'F[H]_S_AB)) -
                  @complex.Re R (\Tr (mx2h sigma : 'F[H]_S_AB))|
                <= eta ^+ 2.
            {
              have Hsum : eta ^+ 2 / 2%:R + eta ^+ 2 / 2%:R = eta ^+ 2.
              { have H2 : (2%:R : R) != 0 by rewrite pnatr_eq0.
                rewrite [in RHS](_ : eta ^+ 2 = (eta ^+ 2 / 2%:R) * 2%:R);
                  last by rewrite -mulrA mulVf// mulr1.
                by rewrite mulr_natr mulr2n. }
              by rewrite -Hsum; apply: lerD.
            }
            pose dtau_sigma :=
              pur_dist (mx2h tauM : 'F[H]_S_AB) (mx2h sigma : 'F[H]_S_AB).
            have Hpd_tau_sigma :
                dtau_sigma <= eta.
            {
              have Hpd_lf :
                  pur_dist (mx2h tauM : 'F[H]_S_AB) (mx2h sigma) <=
                  Num.sqrt (trnormH
                    ((mx2h tauM : 'F[H]_S_AB) - mx2h sigma) +
                    `|@complex.Re R (\Tr (mx2h tauM : 'F[H]_S_AB)) -
                      @complex.Re R (\Tr (mx2h sigma : 'F[H]_S_AB))|).
              {
                have Htau_trlf :
                    @complex.Re R (\Tr (mx2h tauM : 'F[H]_S_AB)) <= 1
                  by rewrite /lftrace mx2hK.
                have Hsigma_trlf :
                    @complex.Re R (\Tr (mx2h sigma : 'F[H]_S_AB)) <= 1
                  by rewrite /lftrace mx2hK.
                exact: pd_gtd_ub' Htau_psdlf Hsigma_psdlf
                  Htau_trlf Hsigma_trlf.
              }
              rewrite /dtau_sigma.
              apply: (le_trans Hpd_lf).
              have Heta_sqrt : Num.sqrt (eta ^+ 2) = eta.
              {
                rewrite sqrtr_sqr ger0_norm //.
              }
              rewrite -Heta_sqrt.
              exact: ler_wsqrtr Hsum_le.
            }
            have Htau_rho_le : dtau <= eps + eta.
            {
              have Htri :
                  dtau <= dtau_sigma + pdistM sigma.
              {
                rewrite /dtau /dtau_sigma /pdistM.
                have Htau_tr_lf :
                    @complex.Re R (\Tr (mx2h tauM : 'F[H]_S_AB)) <= 1
                  by rewrite /lftrace /= mx2hK.
                have Hsigma_tr_lf :
                    @complex.Re R (\Tr (mx2h sigma : 'F[H]_S_AB)) <= 1
                  by rewrite /lftrace /= mx2hK.
                exact: pd_metric_triangle Htau_psdlf Prho Hsigma_psdlf
                  Htau_tr_lf Htr Hsigma_tr_lf.
              }
              have Hrhs : dtau_sigma + pdistM sigma <= eps + eta.
              {
                have -> : eps + eta = eta + eps.
                {
                  exact: addrC eps eta.
                }
                exact: lerD Hpd_tau_sigma Hsigma_dist.
              }
              exact: le_trans Htri Hrhs.
            }
            have Heps_eta_lt : eps + eta < dtau.
            {
              move: Heta_lt_gap.
              by rewrite /gap ltrBrDl addrC.
            }
            have Hcontra := le_lt_trans Htau_rho_le Heps_eta_lt.
            by rewrite ltxx in Hcontra.
      }
        have HballM_sub :
            (BallM `<=` [set tau : 'M[C]_n | mx_norm tau <= 1])%classic.
        {
          move=> tauM [Htau_den _].
          have /denmxP[Htau_psd Htau_trC] := Htau_den.
        have Hmx_i2 : `|tauM| <= i2norm tauM.
        {
          have Hi2_ge0 : 0 <= i2norm tauM.
          {
            exact: i2norm_ge0.
          }
          have -> : i2norm tauM = (NngNum Hi2_ge0)%:num.
          {
            reflexivity.
          }
          rewrite -mx_normEV /mx_norm num_le.
          apply/bigmax_leP => /=.
          split.
          - rewrite -num_le /=.
            exact: Hi2_ge0.
          - move=> ij _.
            move: (i2norm_elem tauM ij.1 ij.2).
            rewrite -num_le /= => Hij_le.
            exact: Hij_le.
        }
        apply: (le_trans Hmx_i2).
        apply: (le_trans (i2norm_trnorm tauM)).
        have Htau_tr_real : \tr tauM \is Num.real.
        {
          exact: ger0_real (psdmx_trace Htau_psd).
          }
          rewrite (psdmx_trnorm Htau_psd).
          exact: Htau_trC.
        }
      have Hcube_compact :
          compact [set tau : 'M[C]_n | mx_norm tau <= 1].
      {
        exact: compact_cmnorm_le.
      }
      apply: (subclosed_compact HballM_closed Hcube_compact _).
      exact: HballM_sub.
    }
    have HSigmaCubeM_compact : compact SigmaCubeM.
    {
      have HSigmaCubeM_closed : closed SigmaCubeM.
      {
        rewrite /SigmaCubeM.
        have HSigmaE :
            [set sigma : 'M[C]_b | sigma \is psdmx /\ \tr sigma <= dB%:C]%classic =
            setI [set sigma : 'M[C]_b | (0 : 'M[C]_b) <= sigma]%classic
                 [set sigma : 'M[C]_b | \tr sigma <= dB%:C]%classic.
        {
          apply/funext=> sigma /=.
          apply/propext; split.
          - move=> [Hsigma_psd Hsigma_tr].
            split.
            + by rewrite le_lownerE subr0.
            + exact: Hsigma_tr.
          - move=> [Hsigma_ge0 Hsigma_tr].
            split.
            + by rewrite le_lownerE subr0 in Hsigma_ge0.
            + exact: Hsigma_tr.
        }
        rewrite HSigmaE.
        apply: closedI.
        - exact: psdmx_closed b.
        - exact: closed_letr _.
      }
      have HSigmaCubeM_sub :
          (SigmaCubeM `<=` [set sigma : 'M[C]_b | mx_norm sigma <= dB%:C])%classic.
      {
        move=> sigma [Hsigma_psd Hsigma_tr].
        have Hmx_i2 : `|sigma| <= i2norm sigma.
        {
          have Hi2_ge0 : 0 <= i2norm sigma.
          {
            exact: i2norm_ge0.
          }
          have -> : i2norm sigma = (NngNum Hi2_ge0)%:num.
          {
            reflexivity.
          }
          rewrite -mx_normEV /mx_norm num_le.
          apply/bigmax_leP => /=.
          split.
          - rewrite -num_le /=.
            exact: Hi2_ge0.
          - move=> ij _.
            move: (i2norm_elem sigma ij.1 ij.2).
            rewrite -num_le /= => Hij_le.
            exact: Hij_le.
        }
        apply: (le_trans Hmx_i2).
        apply: (le_trans (i2norm_trnorm sigma)).
        rewrite (psdmx_trnorm Hsigma_psd).
        exact: Hsigma_tr.
      }
      have Hcm_ball_compact :
          compact [set sigma : 'M[C]_b | mx_norm sigma <= dB%:C].
      {
        exact: compact_cmnorm_le.
      }
      apply: (subclosed_compact HSigmaCubeM_closed Hcm_ball_compact _).
      exact: HSigmaCubeM_sub.
    }
    have HPairCubeM_compact : compact PairCubeM.
    {
      change (compact (BallM `*` SigmaCubeM)).
      exact: compact_setX HballM_compact HSigmaCubeM_compact.
    }
    have lift_sigmaM_linear : linear lift_sigmaM.
    {
      move=> a x y.
      rewrite /lift_sigmaM (mx2hP a x y) /=.
      rewrite sdotfDr sdotfZr.
      by rewrite (h2mxP a _ _) /=.
    }
    have gapM_linear :
        linear gapM.
    {
      move=> a [x1 y1] [x2 y2] /=.
      rewrite /gapM /= lift_sigmaM_linear scalerBr opprD -!addrA.
      rewrite [lift_sigmaM y2 + (- (a *: x1) + - x2)]addrA.
      rewrite [lift_sigmaM y2 + - (a *: x1)]addrC.
      by rewrite !addrA.
    }
    have HFeasM_nonempty : (FeasM !=set0)%classic.
    {
      have HrhoM_psd : rhoM \is psdmx.
      {
        by move: Prho; rewrite qualifE.
      }
      have HrhoM_ball : BallM rhoM.
        {
          have HrhoM_tr : @complex.Re R (\tr rhoM) <= 1.
          {
            exact: Htr.
          }
          split.
          - exact: denmx_psd_re_tr_le HrhoM_psd HrhoM_tr.
          rewrite /pdistM.
        have -> : (mx2h rhoM : 'F[H]_S_AB) = rhoAB.
        {
          apply/h2mx_inj.
          by rewrite /rhoM mx2hK.
        }
        rewrite (pur_dist_refl Prho Htr).
        exact: Heps0.
      }
      have H1_sigma : SigmaCubeM (1%:M : 'M[C]_b).
      {
        split.
        - exact: psdmx1.
        - rewrite mxtrace1 /dB natrC.
          exact: lexx.
      }
      have Hlift1 :
          lift_sigmaM (1%:M : 'M[C]_b) = (1%:M : 'M[C]_n).
      {
        rewrite /lift_sigmaM.
        have Hmx2h1 : (mx2h (1%:M : 'M[C]_b) : 'F[H]_B) = \1.
        {
          apply/h2mx_inj.
          by rewrite mx2hK h2mx1.
        }
        rewrite Hmx2h1.
        have Hten1 :
            (((\1 : 'F[H]_A) \O (\1 : 'F[H]_B)) : 'F[H]_S_AB) = \1.
        {
          apply: to_Fnd_inj.
          rewrite -tenf11.
          by rewrite (sdotFT _ _ disAB) to_Fnd_tenE.
        }
        by rewrite Hten1 h2mx1.
      }
      have HrhoAB_den : rhoAB \is denlf.
      {
        apply/denlfP; split=> //.
        have Hrho_tr_real : (\Tr rhoAB : C) = (@complex.Re R (\Tr rhoAB))%:C.
          by rewrite RRe_real // ger0_real // psdlf_trlf.
        by rewrite Hrho_tr_real lecR.
      }
      have Hrho_le1 : rhoAB ⊑ (\1 : 'F[H]_S_AB).
      {
        move: (denlf_obs HrhoAB_den).
        by rewrite obslfE => /andP [_].
      }
      have Hgap1_psd :
          (((\1 : 'F[H]_S_AB) - rhoAB) : 'F[H]_S_AB) \is psdlf.
      {
        rewrite psdlfE.
        by rewrite subv_ge0.
      }
      have Hgap1 :
          gapM (rhoM, (1%:M : 'M[C]_b)) \is psdmx.
      {
        rewrite /gapM Hlift1 /rhoM.
        rewrite -h2mx1 -raddfB /=.
        by move: Hgap1_psd; rewrite qualifE.
      }
      exists (rhoM, (1%:M : 'M[C]_b)).
      rewrite /FeasM.
      by split.
    }
      have HballM_sub :
          (BallM `<=` [set tau : 'M[C]_n | mx_norm tau <= 1])%classic.
      {
        move=> tauM [Htau_den _].
        have /denmxP[Htau_psd Htau_trC] := Htau_den.
      have Hmx_i2 : `|tauM| <= i2norm tauM.
      {
        have Hi2_ge0 : 0 <= i2norm tauM.
        {
          exact: i2norm_ge0.
        }
        have -> : i2norm tauM = (NngNum Hi2_ge0)%:num.
        {
          reflexivity.
        }
        rewrite -mx_normEV /mx_norm num_le.
        apply/bigmax_leP => /=.
        split.
        - rewrite -num_le /=.
          exact: Hi2_ge0.
        - move=> ij _.
          move: (i2norm_elem tauM ij.1 ij.2).
          rewrite -num_le /= => Hij_le.
          exact: Hij_le.
      }
      apply: (le_trans Hmx_i2).
      apply: (le_trans (i2norm_trnorm tauM)).
      have Htau_tr_real : \tr tauM \is Num.real.
      {
        exact: ger0_real (psdmx_trace Htau_psd).
        }
        rewrite (psdmx_trnorm Htau_psd).
        exact: Htau_trC.
      }
    have HSigmaCubeM_sub :
        (SigmaCubeM `<=` [set sigma : 'M[C]_b | mx_norm sigma <= dB%:C])%classic.
    {
      move=> sigma [Hsigma_psd Hsigma_tr].
      have Hmx_i2 : `|sigma| <= i2norm sigma.
      {
        have Hi2_ge0 : 0 <= i2norm sigma.
        {
          exact: i2norm_ge0.
        }
        have -> : i2norm sigma = (NngNum Hi2_ge0)%:num.
        {
          reflexivity.
        }
        rewrite -mx_normEV /mx_norm num_le.
        apply/bigmax_leP => /=.
        split.
        - rewrite -num_le /=.
          exact: Hi2_ge0.
        - move=> ij _.
          move: (i2norm_elem sigma ij.1 ij.2).
          rewrite -num_le /= => Hij_le.
          exact: Hij_le.
      }
      apply: (le_trans Hmx_i2).
      apply: (le_trans (i2norm_trnorm sigma)).
      rewrite (psdmx_trnorm Hsigma_psd).
      exact: Hsigma_tr.
    }
    pose TraceSetM : set R :=
      [set v : R | exists p : 'M[C]_n * 'M[C]_b,
        FeasM p /\ v = @complex.Re R (\tr p.2)]%classic.
    have HTraceSetM_nonempty : (TraceSetM !=set0)%classic.
    {
      move: HFeasM_nonempty => [p Hp].
      exists (@complex.Re R (\tr p.2)).
      by exists p.
    }
    have HTraceSetM_has_inf : has_inf TraceSetM.
    {
      split.
      - exact: HTraceSetM_nonempty.
      - exists 0 => v [p [Hp ->]].
        case: Hp => _.
        case=> Hsigma _.
        case: Hsigma => Hsigma_psd _.
        have Htr_real : \tr p.2 \is Num.real.
        {
          exact: ger0_real (psdmx_trace Hsigma_psd).
        }
        move: (psdmx_trace Hsigma_psd).
        by rewrite -(RRe_real Htr_real) lecR.
    }
    pose epsn (k : nat) : R := 1 / (k.+1)%:R.
    have Hepsn_pos k : 0 < epsn k.
    {
      rewrite /epsn div1r invr_gt0.
      exact: ltr0Sn.
    }
    have Hex_pair :
        forall k,
          exists p : 'M[C]_n * 'M[C]_b,
            FeasM p /\ @complex.Re R (\tr p.2) < inf TraceSetM + epsn k.
    {
      move=> k.
      have [v Hv Hvlt] := inf_adherent (Hepsn_pos k) HTraceSetM_has_inf.
      case: Hv => p [Hp Hv].
      exists p.
      split=> //.
      by rewrite -Hv.
    }
    have [f Hf] := choice Hex_pair.
    pose pseq (k : nat) := f k.
    pose tauseq (k : nat) := (pseq k).1.
    pose sigseq (k : nat) := (pseq k).2.
    have Hbound_sigma : forall k, mx_norm (sigseq k) <= dB%:C.
    {
      move=> k.
      exact: HSigmaCubeM_sub ((Hf k).1.2.1).
    }
    have [g [Hg Hcvg_sigma]] := ExtNumTopology.Bolzano_Weierstrass Hbound_sigma.
    pose sigmaM0 := limn (sigseq \o g).
    have Hbound_tau : forall k, mx_norm (tauseq (g k)) <= 1.
    {
      move=> k.
      exact: HballM_sub ((Hf (g k)).1.1).
    }
    have [s [Hs Hcvg_tau]] := ExtNumTopology.Bolzano_Weierstrass Hbound_tau.
    pose sigseq0 (k : nat) := sigseq (g (s k)).
    pose tauseq0 (k : nat) := tauseq (g (s k)).
    pose tauM0 := limn tauseq0.
    have Hcvg_sigma_to :=
      (proj2 (cmxcvgn_limnE (sigseq \o g) sigmaM0)
         (conj erefl Hcvg_sigma)).
    have Hcvg_sigseq0_to :=
      (proj1 (cmxcvgn_subseqP (sigseq \o g) sigmaM0) Hcvg_sigma_to
         s Hs).
    have Hcvg_tauseq0_to :=
      (proj2 (cmxcvgn_limnE tauseq0 tauM0)
         (conj erefl Hcvg_tau)).
    have Hsigseq0_lim : limn sigseq0 = sigmaM0.
    {
      have Hcvg_sigseq0_to' := Hcvg_sigseq0_to.
      rewrite /sigseq0 in Hcvg_sigseq0_to'.
      exact: (proj1 (proj1 (cmxcvgn_limnE (fun k => sigseq (g (s k))) sigmaM0)
        Hcvg_sigseq0_to')).
    }
    have Hsigseq0_cvgn : cvgn sigseq0.
    {
      have Hcvg_sigseq0_to' := Hcvg_sigseq0_to.
      rewrite /sigseq0 in Hcvg_sigseq0_to'.
      exact: (proj2 (proj1 (cmxcvgn_limnE (fun k => sigseq (g (s k))) sigmaM0)
        Hcvg_sigseq0_to')).
    }
    have Htau0_cvgn : cvgn tauseq0.
    {
      by rewrite /tauseq0.
    }
    have HsigmaM0_cube : SigmaCubeM sigmaM0.
    {
      have Hsigma_ge0 :
          lbounded_by (0 : 'M[C]_b) (fun k => sigseq (g k)).
      {
        move=> k.
        move: (Hf (g k)).1.2.1.1.
        by rewrite le_lownerE subr0.
      }
      have HsigmaM0_ge0 : (0 : 'M[C]_b) ⊑ sigmaM0.
      {
        exact: cmxlimn_ge Hcvg_sigma Hsigma_ge0.
      }
      have HsigmaM0_psd : sigmaM0 \is psdmx.
      {
        by rewrite le_lownerE subr0 in HsigmaM0_ge0.
      }
      have Htrace_cvgn : cvgn (fun k => \tr (sigseq (g k))).
      {
        exact: is_cmxcvgn_trace Hcvg_sigma.
      }
      have Htrace_le : forall k, \tr (sigseq (g k)) <= dB%:C.
      {
        move=> k.
        exact: (Hf (g k)).1.2.1.2.
      }
      have HsigmaM0_tr : \tr sigmaM0 <= dB%:C.
      {
        move: (@climn_le R dB%:C (fun k => \tr (sigseq (g k))) Htrace_cvgn Htrace_le).
        rewrite (_ : (fun k => \tr (sigseq (g k))) = ((@mxtrace _ b) \o (sigseq \o g))%FUN).
        - rewrite (cmxlimn_trace Hcvg_sigma).
          exact.
        - by apply/funext=> k.
      }
      exact: conj HsigmaM0_psd HsigmaM0_tr.
    }
    have HtauM0_ball : BallM tauM0.
    {
      have HballM_closed : closed BallM.
      {
        apply: compact_closed.
        - exact: ExtNumTopology.mxhausdorff.
        - exact: HballM_compact.
      }
      have Hnear_ball : \forall k \near \oo%classic, BallM (tauseq0 k).
      {
        near=> k.
        exact: (Hf (g (s k))).1.1.
        Unshelve. end_near.
      }
      exact: (@closed_cvg _ _ _ _ tauseq0 BallM
                HballM_closed Hnear_ball tauM0 Hcvg_tauseq0_to).
    }
    have Hcvg_sigseq0_to' : (sigseq0 @ \oo --> sigmaM0)%classic.
    {
      have Htmp := Hcvg_sigseq0_to.
      by rewrite /sigseq0 in Htmp.
    }
    have Hcvg_lift :
        ((fun k => lift_sigmaM (sigseq0 k)) @ \oo --> lift_sigmaM sigmaM0)%classic.
    {
      apply: cmxcvgn_lfun.
      - exact: lift_sigmaM_linear.
      - exact: Hcvg_sigseq0_to'.
    }
    have Hcvg_gap :
        ((fun k => lift_sigmaM (sigseq0 k) - tauseq0 k) @ \oo -->
        lift_sigmaM sigmaM0 - tauM0)%classic.
    {
      apply: cmxcvgnB.
      - exact: Hcvg_lift.
      - exact: Hcvg_tauseq0_to.
    }
    have Hclosed_psd : closed [set X : 'M[C]_n | X \is psdmx]%classic.
    {
      have -> :
          [set X : 'M[C]_n | X \is psdmx]%classic =
          [set X : 'M[C]_n | (0 : 'M[C]_n) <= X]%classic.
      {
        apply/funext=> X /=.
        apply/propext; split.
        - move=> HX.
          by rewrite le_lownerE subr0.
        - move=> HX.
          by rewrite le_lownerE subr0 in HX.
      }
      exact: psdmx_closed n.
    }
    have Hgap0_psd : lift_sigmaM sigmaM0 - tauM0 \is psdmx.
    {
      have Hnear_gap :
          \forall k \near eventually,
            [set X : 'M[C]_n | X \is psdmx]%classic
              (lift_sigmaM (sigseq0 k) - tauseq0 k).
      {
        by apply: nearW => k /=; exact: (Hf (g (s k))).1.2.2.
      }
      have Hclosed_gap :=
        @closed_cvg _ _ _ eventually_filter
          (fun k => lift_sigmaM (sigseq0 k) - tauseq0 k)
          [set X : 'M[C]_n | X \is psdmx]%classic
          Hclosed_psd Hnear_gap.
      exact: Hclosed_gap _ Hcvg_gap.
    }
    pose p0 := (tauM0, sigmaM0).
    have Hp0 : BallM p0.1.
    {
      exact: HtauM0_ball.
    }
    have Htr0 : SigmaCubeM p0.2 /\ gapM p0 \is psdmx.
    {
      split.
      - exact: HsigmaM0_cube.
      - rewrite /p0 /gapM /=.
        exact: Hgap0_psd.
    }
    have Htrace0_eq_inf :
        @complex.Re R (\tr sigmaM0) = inf TraceSetM.
    {
      have Hp0_feas : FeasM p0.
      {
        rewrite /FeasM /p0 /=.
        by split.
      }
      have Htrace0_mem :
          TraceSetM (@complex.Re R (\tr sigmaM0)).
      {
        rewrite /TraceSetM.
        exists p0.
        by split.
      }
      have Htrace0_ge_inf : inf TraceSetM <= @complex.Re R (\tr sigmaM0).
      {
        have Hlb : lbound TraceSetM (inf TraceSetM).
        {
          exact: ge_inf HTraceSetM_has_inf.2.
        }
        exact: Hlb _ Htrace0_mem.
      }
      have Hcvg_trace0 :
          ((fun k => \tr (sigseq0 k)) @ \oo --> \tr sigmaM0)%classic.
      {
        have Htrace_cvgn : cvgn ((@mxtrace C b) \o sigseq0).
        {
          exact: is_cmxcvgn_trace Hsigseq0_cvgn.
        }
        rewrite ccvgn_limnE; split.
        - rewrite (cmxlimn_trace Hsigseq0_cvgn) Hsigseq0_lim.
          reflexivity.
        - rewrite (_ : (fun k => \tr (sigseq0 k)) = ((@mxtrace C b) \o sigseq0)%FUN).
          + exact: Htrace_cvgn.
          + by apply/funext=> k.
      }
      have Htrace_lt :
          forall k,
            @complex.Re R (\tr (sigseq0 k)) < inf TraceSetM + epsn (g (s k)).
      {
        move=> k.
        exact: (Hf (g (s k))).2.
      }
      have Hupper_near :
          forall e : R, 0 < e ->
          \forall k \near \oo%classic,
            @complex.Re R (\tr sigmaM0) < inf TraceSetM + e.
      {
        move=> e He.
        have He2 : 0 < e / 2 by rewrite divr_gt0.
        have Hnear_trace :
            \forall t \near \oo%classic, `|@complex.Re R (\tr (sigseq0 t)) -
              @complex.Re R (\tr sigmaM0)| < e / 2.
        {
          pose trace_fun := fun k : nat => @complex.Re R (\tr (sigseq0 k)).
          pose trace_lim := @complex.Re R (\tr sigmaM0).
          have Hdist_trace :
              forall e0 : R, 0 < e0 ->
              \forall t \near \oo%classic,
                `|trace_lim - trace_fun t| < e0.
          {
            move=> e0 He0.
            have Hcvg_trace_fun := Re_cvgn_realV Hcvg_trace0.
            have Hdist_trace0 :=
              @cvgr_dist_lt R [the normedModType R of R^o]
                nat \oo%classic _ trace_fun trace_lim Hcvg_trace_fun.
            exact: Hdist_trace0 _ He0.
          }
          move: (Hdist_trace _ He2).
          under eq_near do rewrite distrC.
          exact.
        }
        near=> k.
        have Htr_close :
            `|@complex.Re R (\tr (sigseq0 k)) - @complex.Re R (\tr sigmaM0)| < e / 2.
        {
          near: k.
          exact: Hnear_trace.
        }
        have Heps_small : epsn (g (s k)) < e / 2.
        {
          have Hk_small : epsn k < e / 2.
          {
            rewrite /epsn div1r.
            near: k.
            exact: near_infty_natSinv_lt (PosNum He2).
          }
          have Hsk_ge_k : (s k >= k)%N.
          {
            exact: nchain_ge Hs k.
          }
          have Hgsk_ge_sk : (g (s k) >= s k)%N.
          {
            exact: nchain_ge Hg (s k).
          }
          have Hinv_le :
              epsn (g (s k)) <= epsn k.
          {
            rewrite /epsn !div1r.
            rewrite lef_pV2.
            - rewrite ler_nat.
              rewrite -(leq_add2r 1%N) !addn1.
              exact: leq_trans Hsk_ge_k Hgsk_ge_sk.
            - by rewrite posrE ltr0Sn.
            - by rewrite posrE ltr0Sn.
          }
          exact: (le_lt_trans Hinv_le Hk_small).
        }
        have Htr_lt :
            @complex.Re R (\tr (sigseq0 k)) < inf TraceSetM + epsn (g (s k)).
        {
          exact: Htrace_lt k.
        }
        have Hsig_lt :
            @complex.Re R (\tr sigmaM0) <
            @complex.Re R (\tr (sigseq0 k)) + e / 2.
        {
          exact: ltr_distlCDr Htr_close.
        }
        apply: (lt_trans Hsig_lt).
        have Hmid1 :
            @complex.Re R (\tr (sigseq0 k)) + e / 2 <
            inf TraceSetM + epsn (g (s k)) + e / 2.
        {
          by rewrite (ltrD2r (e / 2)).
        }
        have Hmid2 :
            inf TraceSetM + epsn (g (s k)) + e / 2 <
            inf TraceSetM + e.
        {
          rewrite -addrA.
          have Hinner :
              epsn (g (s k)) + e / 2 < e.
          {
            have He_half : e - e / 2 = e / 2.
            {
              move: (congr1 (fun x => x - e / 2) (splitr e)).
              by rewrite -addrA subrr addr0.
            }
            rewrite -ltrBrDr He_half.
            exact: Heps_small.
          }
          rewrite (ltrD2l (inf TraceSetM)).
          exact: Hinner.
        }
        exact: (lt_trans Hmid1 Hmid2).
        Unshelve. end_near.
      }
      have Htrace0_le_inf : @complex.Re R (\tr sigmaM0) <= inf TraceSetM.
      {
        rewrite leNgt.
        apply/negP=> Hlt.
        pose e := (@complex.Re R (\tr sigmaM0) - inf TraceSetM) / 2.
        have He_pos : 0 < e.
        {
          rewrite /e.
          rewrite divr_gt0.
          split.
          - by rewrite subr_gt0.
          - by rewrite ltr0Sn.
        }
        have Hnear := Hupper_near e He_pos.
        have Hineq : @complex.Re R (\tr sigmaM0) < inf TraceSetM + e.
        {
          move: Hnear.
          rewrite /prop_near1 nbhs_filterE => -[N _ HN].
          exact: (HN N (leqnn N)).
        }
        pose d := @complex.Re R (\tr sigmaM0) - inf TraceSetM.
        have Hd_pos : 0 < d.
        {
          by rewrite /d subr_gt0.
        }
        have Hd_half_pos : 0 < d / 2.
        {
          have Htwo_pos : 0 < (2%:R : R).
          {
            by rewrite ltr0n.
          }
          exact: divr_gt0 Hd_pos Htwo_pos.
        }
        have Hd_half_lt : d / 2 < d.
        {
          have Htwo_pos : 0 < (2%:R : R).
          {
            by rewrite ltr0n.
          }
          have H2_unit : (2%:R : R) \is a GRing.unit.
          {
            exact: unitf_gt0 Htwo_pos.
          }
          rewrite -(ltr_pM2r Htwo_pos).
          rewrite (divrK H2_unit d) mulr_natr mulr2n.
          rewrite ltrDl.
          exact: Hd_pos.
        }
        have Hupper_lt : inf TraceSetM + e < @complex.Re R (\tr sigmaM0).
        {
          have Hbase : e < d.
          {
            rewrite /e /d.
            exact: Hd_half_lt.
          }
          have Hrhs : inf TraceSetM + e < inf TraceSetM + d.
          {
            exact: (ler_ltD (lexx (inf TraceSetM)) Hbase).
          }
          have -> : @complex.Re R (\tr sigmaM0) = inf TraceSetM + d.
          {
            by rewrite /d addrC subrK.
          }
          exact: Hrhs.
        }
        have : @complex.Re R (\tr sigmaM0) < @complex.Re R (\tr sigmaM0).
        {
          exact: (lt_trans Hineq Hupper_lt).
        }
        by rewrite ltxx.
      }
      apply/eqP; rewrite eq_le; apply/andP; split.
      - exact: Htrace0_le_inf.
      - exact: Htrace0_ge_inf.
    }
    pose tau0 := (mx2h tauM0 : 'F[H]_S_AB).
    pose sigma0 := (mx2h sigmaM0 : 'F[H]_B).
    have Htau0_ball : eps_ball eps rhoAB tau0.
      {
        have HtauM0_ball0 : BallM tauM0 := Hp0.
        have /denmxP[HtauM0_psd HtauM0_trC] := proj1 HtauM0_ball0.
        have HtauM0_tr : @complex.Re R (\tr tauM0) <= 1
          by move: HtauM0_trC; rewrite lecE /= => /andP [_].
        have HtauM0_dist : pdistM tauM0 <= eps := proj2 HtauM0_ball0.
        have Htau0_psd : tau0 \is psdlf
          by rewrite /tau0 qualifE /= mx2hK.
        have Htau0_tr : @complex.Re R (\Tr tau0) <= 1
          by rewrite /tau0 /lftrace /= mx2hK.
        have Htau0_pos : 0 < @complex.Re R (\Tr tau0).
        {
          have Hsmall : 0 <= eps < Num.sqrt (@complex.Re R (\Tr rhoAB))
            by apply/andP; split.
          have Holdball :
              ((tau0 \is psdlf) &&
                (@complex.Re R (\Tr tau0) <= 1)) &&
              (pur_dist tau0 rhoAB <= eps).
          {
            apply/andP; split.
            - by rewrite Htau0_psd Htau0_tr.
            - by rewrite /tau0 /pdistM.
          }
          exact: (eps_ball_trace_pos_from_small Prho Htr Hsmall Holdball).
        }
      rewrite /eps_ball.
      apply/andP; split.
      - apply/andP; split.
        + by apply/andP; split.
        + exact: Htau0_tr.
      - rewrite /pdistM /pur_dist /gfid /tau0 /rhoM.
        by rewrite /tau0.
    }
    have Hsigma0_psd : sigma0 \is psdlf.
    {
      have HsigmaM0_cube0 : SigmaCubeM sigmaM0 := proj1 Htr0.
      have HsigmaM0_psd : sigmaM0 \is psdmx := proj1 HsigmaM0_cube0.
      have Hsigma0_psd' : sigma0 \is psdlf.
        by rewrite /sigma0 qualifE /= mx2hK.
      exact: Hsigma0_psd'.
    }
    have Hsigma0_tr_le : \Tr sigma0 <= dB%:C.
    {
      have HsigmaM0_cube0 : SigmaCubeM sigmaM0 := proj1 Htr0.
      have HsigmaM0_tr : \tr sigmaM0 <= dB%:C := proj2 HsigmaM0_cube0.
      rewrite /sigma0 /lftrace /= mx2hK.
      exact: HsigmaM0_tr.
    }
    have Hsigma0_gap :
        (((\1 : 'F[H]_A) \O sigma0) - tau0 : 'F[H]_S_AB) \is psdlf.
    {
      have Hgap0 : gapM p0 \is psdmx := proj2 Htr0.
      have Hsigma0_gap' :
          (((\1 : 'F[H]_A) \O sigma0) - tau0 : 'F[H]_S_AB) \is psdlf.
      {
        rewrite qualifE.
        have -> :
            h2mx ((((\1 : 'F[H]_A) \O sigma0) - tau0 : 'F[H]_S_AB)) =
            h2mx (((\1 : 'F[H]_A) \O sigma0)) - h2mx tau0.
          by rewrite raddfB.
        rewrite /sigma0 /tau0 /= mx2hK.
        rewrite /gapM /lift_sigmaM in Hgap0.
        exact: Hgap0.
      }
      exact: Hsigma0_gap'.
    }
    have Hsigma0_feas :
        phi_min_feasible B tau0 (@complex.Re R (\Tr sigma0)).
    {
      have eqSA_support : S_AB :\: B = A.
      {
        exact: setDU_r disAB.
      }
      have eqSB_support : S_AB :&: B = B.
      {
        by setdec.
      }
      have eqST_support :
          (S_AB :\: B) :|: (S_AB :&: B) = S_AB.
      {
        by rewrite finset.setUC finset.setID.
      }
      rewrite /phi_min_feasible.
      pose sigma0I := castlf (esym eqSB_support, esym eqSB_support) sigma0.
      have Hsigma0I_psd : sigma0I \is psdlf.
      {
        exact: castlf_psdlf Hsigma0_psd.
      }
      have Hsigma0I_tr : @complex.Re R (\Tr sigma0I) = @complex.Re R (\Tr sigma0).
      {
        rewrite /sigma0I castlf_trlfE.
        reflexivity.
      }
      have Hsigma0I_back : castlf (eqSB_support, eqSB_support) sigma0I = sigma0.
      {
        by rewrite /sigma0I castlf_comp castlf_id.
      }
      have eqU1 :
          (S_AB :\: B) :|: (S_AB :&: B) =
          (S_AB :\: B) :|: B.
      {
        by rewrite eqSB_support.
      }
      have eqU2 :
          (S_AB :\: B) :|: B = S_AB.
      {
        by rewrite eqSA_support.
      }
      have Hcast_step1 :
          castlf (eqU1, eqU1)
            ((\1 : 'F[H]_(S_AB :\: B)) \O sigma0I) =
          ((\1 : 'F[H]_(S_AB :\: B)) \O sigma0 :
            'F[H]_((S_AB :\: B) :|: B)).
      {
        rewrite (sdotIf_cast_r eqSB_support eqU1).
        by rewrite Hsigma0I_back.
      }
      have Hcast_step2 :
          castlf (eqU2, eqU2)
            ((\1 : 'F[H]_(S_AB :\: B)) \O sigma0 :
              'F[H]_((S_AB :\: B) :|: B)) =
          (((\1 : 'F[H]_A) \O sigma0) : 'F[H]_S_AB).
      {
        rewrite (sdotIf_cast_l eqSA_support eqU2).
        have -> :
            castlf (eqSA_support, eqSA_support)
              (\1 : 'F[H]_(S_AB :\: B)) = (\1 : 'F[H]_A).
        {
          exact: castlf1.
        }
        reflexivity.
      }
      have Hcast_comp :
          castlf (eqST_support, eqST_support)
            ((\1 : 'F[H]_(S_AB :\: B)) \O sigma0I) =
          castlf (eqU2, eqU2)
            (castlf (eqU1, eqU1)
              ((\1 : 'F[H]_(S_AB :\: B)) \O sigma0I)).
      {
        rewrite castlf_comp.
        have -> : etrans eqU1 eqU2 = eqST_support by apply: eq_irrelevance.
        reflexivity.
      }
      exists sigma0I.
      split.
      - exact: Hsigma0I_psd.
      split.
      - lazymatch goal with
        | |- context [castlf (?eqHidden, ?eqHidden) _] =>
            pose eqHidden0 := eqHidden
        end.
        have Hcast_hidden :
            castlf (eqHidden0, eqHidden0)
              ((\1 : 'F[H]_(S_AB :\: B)) \O sigma0I) =
            castlf (eqST_support, eqST_support)
              ((\1 : 'F[H]_(S_AB :\: B)) \O sigma0I).
        {
          have -> : eqHidden0 = eqST_support by apply: eq_irrelevance.
          reflexivity.
        }
        rewrite Hcast_hidden Hcast_comp Hcast_step1 Hcast_step2.
        exact: Hsigma0_gap.
      - by rewrite Hsigma0I_tr.
    }
    have Hphi_tau0_eq : phi_min B tau0 = @complex.Re R (\Tr sigma0).
    {
      have Hsigma0_tr_real : (\Tr sigma0 : C) = (@complex.Re R (\Tr sigma0))%:C.
      {
        rewrite RRe_real //.
        exact: ger0_real (psdlf_trlf Hsigma0_psd).
      }
      have Hsigma0_tr_leR : @complex.Re R (\Tr sigma0) <= dB.
      {
        move: Hsigma0_tr_le.
        by rewrite Hsigma0_tr_real lecR.
      }
      apply/eqP.
      rewrite eq_le.
      apply/andP; split.
      - apply: ge_inf.
        + exists 0 => x [sigma [Psigma [_ ->]]].
          have Htr_sigma : 0 <= @complex.Re R (\Tr sigma).
          {
            have Htr_real : (\Tr sigma : C) = (@complex.Re R (\Tr sigma))%:C.
            {
              rewrite RRe_real //.
              exact: ger0_real (psdlf_trlf Psigma).
            }
            move: (psdlf_trlf Psigma).
            by rewrite Htr_real lecR.
          }
          exact: Htr_sigma.
        + exact: Hsigma0_feas.
      - apply: lb_le_inf.
        + by exists (@complex.Re R (\Tr sigma0)); exact: Hsigma0_feas.
        + move=> v [sigma [Psigma [Hgap_hidden ->]]].
          have eqSA_support : S_AB :\: B = A.
          {
            exact: setDU_r disAB.
          }
          have eqSB_support : S_AB :&: B = B.
          {
            by setdec.
          }
          have eqST_support :
              (S_AB :\: B) :|: (S_AB :&: B) = S_AB.
          {
            by rewrite finset.setUC finset.setID.
          }
          pose sigmaB := castlf (eqSB_support, eqSB_support) sigma.
          have HsigmaB_psd : sigmaB \is psdlf.
          {
            exact: castlf_psdlf Psigma.
          }
          have Hsigma_tr_real : (\Tr sigma : C) = (@complex.Re R (\Tr sigma))%:C.
          {
            rewrite RRe_real //.
            exact: ger0_real (psdlf_trlf Psigma).
          }
          have HsigmaB_tr_real : (\Tr sigmaB : C) = (@complex.Re R (\Tr sigmaB))%:C.
          {
            rewrite RRe_real //.
            exact: ger0_real (psdlf_trlf HsigmaB_psd).
          }
          have HsigmaB_tr_eq : @complex.Re R (\Tr sigmaB) = @complex.Re R (\Tr sigma).
          {
            rewrite /sigmaB castlf_trlfE.
            reflexivity.
          }
          have Hsigma_back :
              castlf (esym eqSB_support, esym eqSB_support) sigmaB = sigma.
          {
            by rewrite /sigmaB castlf_comp castlf_id.
          }
          have eqU1 :
              (S_AB :\: B) :|: (S_AB :&: B) =
              (S_AB :\: B) :|: B.
          {
            by rewrite eqSB_support.
          }
          have eqU2 :
              (S_AB :\: B) :|: B = S_AB.
          {
            by rewrite eqSA_support.
          }
          have Hcast_step1 :
              castlf (eqU1, eqU1)
                ((\1 : 'F[H]_(S_AB :\: B)) \O sigma) =
              ((\1 : 'F[H]_(S_AB :\: B)) \O sigmaB :
                'F[H]_((S_AB :\: B) :|: B)).
          {
            rewrite (sdotIf_cast_r eqSB_support eqU1).
            by rewrite /sigmaB.
          }
          have Hcast_step2 :
              castlf (eqU2, eqU2)
                ((\1 : 'F[H]_(S_AB :\: B)) \O sigmaB :
                  'F[H]_((S_AB :\: B) :|: B)) =
              (((\1 : 'F[H]_A) \O sigmaB) : 'F[H]_S_AB).
          {
            rewrite (sdotIf_cast_l eqSA_support eqU2).
            have -> :
                castlf (eqSA_support, eqSA_support)
                  (\1 : 'F[H]_(S_AB :\: B)) = (\1 : 'F[H]_A).
            {
              exact: castlf1.
            }
            reflexivity.
          }
          have Hcast_comp :
              castlf (eqST_support, eqST_support)
                ((\1 : 'F[H]_(S_AB :\: B)) \O sigma) =
              castlf (eqU2, eqU2)
                (castlf (eqU1, eqU1)
                  ((\1 : 'F[H]_(S_AB :\: B)) \O sigma)).
          {
            rewrite castlf_comp.
            have -> : etrans eqU1 eqU2 = eqST_support by apply: eq_irrelevance.
            reflexivity.
          }
          lazymatch type of Hgap_hidden with
          | is_true (?gapExpr \is psdlf) =>
              pose gapExpr0 := gapExpr
          end.
          have Hgap_hiddenE :
              gapExpr0 = (((\1 : 'F[H]_A) \O sigmaB) - tau0 : 'F[H]_S_AB).
          {
            rewrite /gapExpr0.
            lazymatch goal with
            | |- context [castlf (?eqHidden, ?eqHidden) _] =>
                pose eqHidden0 := eqHidden
            end.
            have Hcast_hidden :
                castlf (eqHidden0, eqHidden0)
                  ((\1 : 'F[H]_(S_AB :\: B)) \O sigma) =
                castlf (eqST_support, eqST_support)
                  ((\1 : 'F[H]_(S_AB :\: B)) \O sigma).
            {
              have -> : eqHidden0 = eqST_support by apply: eq_irrelevance.
              reflexivity.
            }
            rewrite Hcast_hidden Hcast_comp Hcast_step1 Hcast_step2.
            reflexivity.
          }
          have Hgap_raw :
              (((\1 : 'F[H]_A) \O sigmaB) - tau0 : 'F[H]_S_AB) \is psdlf.
          {
            change (is_true (gapExpr0 \is psdlf)) in Hgap_hidden.
            rewrite Hgap_hiddenE in Hgap_hidden.
            exact: Hgap_hidden.
          }
          have [Hsigma_tr_le_dB|Hsigma_tr_gt_dB] :=
            lerP (@complex.Re R (\Tr sigma)) dB.
          * have HsigmaB_tr_leC : \Tr sigmaB <= dB%:C.
            {
              rewrite HsigmaB_tr_real lecR HsigmaB_tr_eq.
              exact: Hsigma_tr_le_dB.
            }
            have HgapB : gapM (tauM0, h2mx sigmaB) \is psdmx.
            {
              move: Hgap_raw.
              rewrite qualifE.
              have -> :
                  h2mx ((((\1 : 'F[H]_A) \O sigmaB) - tau0 : 'F[H]_S_AB)) =
                  gapM (tauM0, h2mx sigmaB).
              {
                rewrite raddfB /gapM.
                have -> :
                    lift_sigmaM (h2mx sigmaB) =
                    h2mx ((((\1 : 'F[H]_A) \O sigmaB) : 'F[H]_S_AB)).
                {
                  rewrite /lift_sigmaM /=.
                  by rewrite h2mxK.
                }
                rewrite /tau0 /=.
                by rewrite mx2hK.
              }
              exact.
            }
            have Hpair_feas : FeasM (tauM0, h2mx sigmaB).
            {
              rewrite /FeasM /=.
              split.
              - exact: Hp0.
              split.
              - split.
                + by move: HsigmaB_psd; rewrite qualifE.
                + move: HsigmaB_tr_leC.
                  by rewrite /lftrace.
              - exact: HgapB.
            }
            have Htrace_mem :
                TraceSetM (@complex.Re R (\tr (h2mx sigmaB))).
            {
              rewrite /TraceSetM.
              exists (tauM0, h2mx sigmaB).
              split.
              - exact: Hpair_feas.
              - reflexivity.
            }
            have Hsigma0_trmx :
                @complex.Re R (\Tr sigma0) = @complex.Re R (\tr sigmaM0).
            {
              by rewrite /sigma0 /lftrace /= mx2hK.
            }
            have HsigmaB_trmx :
                @complex.Re R (\tr (h2mx sigmaB)) = @complex.Re R (\Tr sigmaB).
            {
              by rewrite /lftrace.
            }
            have Hinf_sigma :
                @complex.Re R (\Tr sigma0) <= @complex.Re R (\Tr sigma).
            {
              have Hlb := ge_inf HTraceSetM_has_inf.2.
              have Hlb_sigma := Hlb _ Htrace_mem.
              rewrite -Htrace0_eq_inf -Hsigma0_trmx in Hlb_sigma.
              rewrite HsigmaB_trmx HsigmaB_tr_eq in Hlb_sigma.
              exact: Hlb_sigma.
            }
            exact: Hinf_sigma.
          * exact: (le_trans Hsigma0_tr_leR (ltW Hsigma_tr_gt_dB)).
    }
    have Htau0_ub :
        forall tau : 'F[H]_S_AB,
          eps_ball eps rhoAB tau -> hmin B tau <= hmin B tau0.
    {
      move=> tau Htau_ball.
      have Hphi_le : phi_min B tau0 <= phi_min B tau.
      {
        apply: lb_le_inf.
        - move: Htau_ball.
          rewrite /eps_ball =>
            /andP [/andP [/andP [Htau_psd _] Htau_tr] _].
          pose sigma_w := (\1 : 'F[H]_B).
          have Psigma_w : sigma_w \is psdlf.
          {
            rewrite /sigma_w psdlfE.
            exact: lef01.
          }
          have Hgap_w :
              ((((\1 : 'F[H]_A) \O sigma_w) : 'F[H]_S_AB) - tau)
                \is psdlf.
          {
            have Htau_mx_psd : h2mx tau \is psdmx.
            {
              by move: Htau_psd; rewrite qualifE.
            }
            have Htau_le1_mx : h2mx tau <= (1%:M : 'M[C]_(dim 'H[H]_S_AB)).
            {
              have Htau_le_tr := lemx_psd_ub Htau_mx_psd.
              have Htau_tr_real :
                  (\tr (h2mx tau) : C) =
                  (@complex.Re R (\tr (h2mx tau)))%:C.
              {
                rewrite RRe_real //.
                exact: ger0_real (psdmx_trace Htau_mx_psd).
              }
              have Htau_tr_mx : @complex.Re R (\tr (h2mx tau)) <= 1.
              {
                move: Htau_tr.
                by rewrite /lftrace.
              }
              have Htr_le1_mx :
                  ((@complex.Re R (\tr (h2mx tau)))%:C)%:M <=
                  (1%:M : 'M[C]_(dim 'H[H]_S_AB)).
              {
                apply: scalemx_le.
                by rewrite lecR.
              }
              rewrite Htau_tr_real in Htau_le_tr.
              exact: le_trans Htau_le_tr Htr_le1_mx.
            }
            have Hten1 :
                (((\1 : 'F[H]_A) \O sigma_w) : 'F[H]_S_AB) = \1.
            {
              rewrite /sigma_w.
              apply: to_Fnd_inj.
              rewrite -tenf11.
              by rewrite (sdotFT _ _ disAB) to_Fnd_tenE.
            }
            rewrite Hten1 qualifE raddfB /= h2mx1.
            by move: Htau_le1_mx; rewrite le_lownerE.
          }
          have Hop :
              tau <= ((\1 : 'F[H]_A) \O sigma_w : 'F[H]_S_AB).
          {
            by rewrite lefE.
          }
          exists (@complex.Re R (\Tr sigma_w)).
          have eqSA_support : S_AB :\: B = A.
          {
            exact: setDU_r disAB.
          }
          have eqSB_support : S_AB :&: B = B.
          {
            by setdec.
          }
          have eqST_support :
              (S_AB :\: B) :|: (S_AB :&: B) = S_AB.
          {
            by rewrite finset.setUC finset.setID.
          }
          rewrite /phi_min_feasible.
          pose sigma_wI := castlf (esym eqSB_support, esym eqSB_support) sigma_w.
          have Hsigma_wI_psd : sigma_wI \is psdlf.
          {
            exact: castlf_psdlf Psigma_w.
          }
          have Hsigma_wI_tr :
              @complex.Re R (\Tr sigma_wI) = @complex.Re R (\Tr sigma_w).
          {
            rewrite /sigma_wI castlf_trlfE.
            reflexivity.
          }
          have Hsigma_wI_back :
              castlf (eqSB_support, eqSB_support) sigma_wI = sigma_w.
          {
            by rewrite /sigma_wI castlf_comp castlf_id.
          }
          have eqU1 :
              (S_AB :\: B) :|: (S_AB :&: B) =
              (S_AB :\: B) :|: B.
          {
            by rewrite eqSB_support.
          }
          have eqU2 :
              (S_AB :\: B) :|: B = S_AB.
          {
            by rewrite eqSA_support.
          }
          have Hcast_step1 :
              castlf (eqU1, eqU1)
                ((\1 : 'F[H]_(S_AB :\: B)) \O sigma_wI) =
              ((\1 : 'F[H]_(S_AB :\: B)) \O sigma_w :
                'F[H]_((S_AB :\: B) :|: B)).
          {
            rewrite (sdotIf_cast_r eqSB_support eqU1).
            by rewrite Hsigma_wI_back.
          }
          have Hcast_step2 :
              castlf (eqU2, eqU2)
                ((\1 : 'F[H]_(S_AB :\: B)) \O sigma_w :
                  'F[H]_((S_AB :\: B) :|: B)) =
              (((\1 : 'F[H]_A) \O sigma_w) : 'F[H]_S_AB).
          {
            rewrite (sdotIf_cast_l eqSA_support eqU2).
            have -> :
                castlf (eqSA_support, eqSA_support)
                  (\1 : 'F[H]_(S_AB :\: B)) = (\1 : 'F[H]_A).
            {
              exact: castlf1.
            }
            reflexivity.
          }
          have Hcast_comp :
              castlf (eqST_support, eqST_support)
                ((\1 : 'F[H]_(S_AB :\: B)) \O sigma_wI) =
              castlf (eqU2, eqU2)
                (castlf (eqU1, eqU1)
                  ((\1 : 'F[H]_(S_AB :\: B)) \O sigma_wI)).
          {
            rewrite castlf_comp.
            have -> : etrans eqU1 eqU2 = eqST_support by apply: eq_irrelevance.
            reflexivity.
          }
          exists sigma_wI.
          split.
          - exact: Hsigma_wI_psd.
          split.
          - lazymatch goal with
            | |- context [castlf (?eqHidden, ?eqHidden) _] =>
                pose eqHidden0 := eqHidden
            end.
            have Hcast_hidden :
                castlf (eqHidden0, eqHidden0)
                  ((\1 : 'F[H]_(S_AB :\: B)) \O sigma_wI) =
                castlf (eqST_support, eqST_support)
                  ((\1 : 'F[H]_(S_AB :\: B)) \O sigma_wI).
            {
              have -> : eqHidden0 = eqST_support by apply: eq_irrelevance.
              reflexivity.
            }
            rewrite Hcast_hidden Hcast_comp Hcast_step1 Hcast_step2.
            exact: Hgap_w.
          - by rewrite Hsigma_wI_tr.
        - move=> v [sigma [Psigma [Hgap_hidden ->]]].
          have eqSA_support : S_AB :\: B = A.
          {
            exact: setDU_r disAB.
          }
          have eqSB_support : S_AB :&: B = B.
          {
            by setdec.
          }
          have eqST_support :
              (S_AB :\: B) :|: (S_AB :&: B) = S_AB.
          {
            by rewrite finset.setUC finset.setID.
          }
          pose sigmaB := castlf (eqSB_support, eqSB_support) sigma.
          have HsigmaB_psd : sigmaB \is psdlf.
          {
            exact: castlf_psdlf Psigma.
          }
          have Hsigma_tr_real : (\Tr sigma : C) = (@complex.Re R (\Tr sigma))%:C.
          {
            rewrite RRe_real //.
            exact: ger0_real (psdlf_trlf Psigma).
          }
          have HsigmaB_tr_real : (\Tr sigmaB : C) = (@complex.Re R (\Tr sigmaB))%:C.
          {
            rewrite RRe_real //.
            exact: ger0_real (psdlf_trlf HsigmaB_psd).
          }
          have HsigmaB_tr_eq : @complex.Re R (\Tr sigmaB) = @complex.Re R (\Tr sigma).
          {
            rewrite /sigmaB castlf_trlfE.
            reflexivity.
          }
          have eqU1 :
              (S_AB :\: B) :|: (S_AB :&: B) =
              (S_AB :\: B) :|: B.
          {
            by rewrite eqSB_support.
          }
          have eqU2 :
              (S_AB :\: B) :|: B = S_AB.
          {
            by rewrite eqSA_support.
          }
          have Hcast_step1 :
              castlf (eqU1, eqU1)
                ((\1 : 'F[H]_(S_AB :\: B)) \O sigma) =
              ((\1 : 'F[H]_(S_AB :\: B)) \O sigmaB :
                'F[H]_((S_AB :\: B) :|: B)).
          {
            rewrite (sdotIf_cast_r eqSB_support eqU1).
            by rewrite /sigmaB.
          }
          have Hcast_step2 :
              castlf (eqU2, eqU2)
                ((\1 : 'F[H]_(S_AB :\: B)) \O sigmaB :
                  'F[H]_((S_AB :\: B) :|: B)) =
              (((\1 : 'F[H]_A) \O sigmaB) : 'F[H]_S_AB).
          {
            rewrite (sdotIf_cast_l eqSA_support eqU2).
            have -> :
                castlf (eqSA_support, eqSA_support)
                  (\1 : 'F[H]_(S_AB :\: B)) = (\1 : 'F[H]_A).
            {
              exact: castlf1.
            }
            reflexivity.
          }
          have Hcast_comp :
              castlf (eqST_support, eqST_support)
                ((\1 : 'F[H]_(S_AB :\: B)) \O sigma) =
              castlf (eqU2, eqU2)
                (castlf (eqU1, eqU1)
                  ((\1 : 'F[H]_(S_AB :\: B)) \O sigma)).
          {
            rewrite castlf_comp.
            have -> : etrans eqU1 eqU2 = eqST_support by apply: eq_irrelevance.
            reflexivity.
          }
          lazymatch type of Hgap_hidden with
          | is_true (?gapExpr \is psdlf) =>
              pose gapExpr0 := gapExpr
          end.
          have Hgap_hiddenE :
              gapExpr0 = (((\1 : 'F[H]_A) \O sigmaB) - tau : 'F[H]_S_AB).
          {
            rewrite /gapExpr0.
            lazymatch goal with
            | |- context [castlf (?eqHidden, ?eqHidden) _] =>
                pose eqHidden0 := eqHidden
            end.
            have Hcast_hidden :
                castlf (eqHidden0, eqHidden0)
                  ((\1 : 'F[H]_(S_AB :\: B)) \O sigma) =
                castlf (eqST_support, eqST_support)
                  ((\1 : 'F[H]_(S_AB :\: B)) \O sigma).
            {
              have -> : eqHidden0 = eqST_support by apply: eq_irrelevance.
              reflexivity.
            }
            rewrite Hcast_hidden Hcast_comp Hcast_step1 Hcast_step2.
            reflexivity.
          }
          have Hfeas_raw :
              (((\1 : 'F[H]_A) \O sigmaB) - tau : 'F[H]_S_AB) \is psdlf.
          {
            change (is_true (gapExpr0 \is psdlf)) in Hgap_hidden.
            rewrite Hgap_hiddenE in Hgap_hidden.
            exact: Hgap_hidden.
          }
          have Hsigma0_tr_real : (\Tr sigma0 : C) = (@complex.Re R (\Tr sigma0))%:C.
          {
            rewrite RRe_real //.
            exact: ger0_real (psdlf_trlf Hsigma0_psd).
          }
          have Hsigma0_tr_leR : @complex.Re R (\Tr sigma0) <= dB.
          {
            move: Hsigma0_tr_le.
            by rewrite Hsigma0_tr_real lecR.
          }
          have [Hsigma_tr_le_dB|Hsigma_tr_gt_dB] :=
            lerP (@complex.Re R (\Tr sigma)) dB.
          * have HsigmaB_tr_leC : \Tr sigmaB <= dB%:C.
            {
              rewrite HsigmaB_tr_real lecR HsigmaB_tr_eq.
              exact: Hsigma_tr_le_dB.
            }
            pose tauM := h2mx tau.
            have HtauM_ball : BallM tauM.
            {
                have Htau_psd : tau \is psdlf := eps_ball_psdlf Htau_ball.
                have Htau_tr : @complex.Re R (\Tr tau) <= 1 :=
                  eps_ball_trlf Htau_ball.
                have Htau_dist : pur_dist tau rhoAB <= eps :=
                  eps_ball_pur_dist Htau_ball.
                rewrite /BallM /pdistM.
                split.
                - apply: denmx_psd_re_tr_le.
                  + by move: Htau_psd; rewrite qualifE.
                  + by rewrite /tauM /lftrace.
                - by rewrite /tauM h2mxK.
              }
            have HgapB : gapM (tauM, h2mx sigmaB) \is psdmx.
            {
              move: Hfeas_raw.
              rewrite qualifE.
              have -> :
                  h2mx ((((\1 : 'F[H]_A) \O sigmaB) - tau : 'F[H]_S_AB)) =
                  gapM (tauM, h2mx sigmaB).
              {
                rewrite raddfB /gapM.
                have -> :
                    lift_sigmaM (h2mx sigmaB) =
                    h2mx ((((\1 : 'F[H]_A) \O sigmaB) : 'F[H]_S_AB)).
                {
                  rewrite /lift_sigmaM /=.
                  by rewrite h2mxK.
                }
                by rewrite /tauM.
              }
              exact.
            }
            have Hpair_feas : FeasM (tauM, h2mx sigmaB).
            {
              rewrite /FeasM /=.
              split.
              - exact: HtauM_ball.
              split.
              - split.
                + by move: HsigmaB_psd; rewrite qualifE.
                + by move: HsigmaB_tr_leC; rewrite /lftrace.
              - exact: HgapB.
            }
            have Htrace_mem :
                TraceSetM (@complex.Re R (\tr (h2mx sigmaB))).
            {
              rewrite /TraceSetM.
              exists (tauM, h2mx sigmaB).
              split.
              - exact: Hpair_feas.
              - reflexivity.
            }
            have Hsigma0_trmx :
                @complex.Re R (\Tr sigma0) = @complex.Re R (\tr sigmaM0).
            {
              by rewrite /sigma0 /lftrace /= mx2hK.
            }
            have HsigmaB_trmx :
                @complex.Re R (\tr (h2mx sigmaB)) = @complex.Re R (\Tr sigmaB).
            {
              by rewrite /lftrace.
            }
            have Hlb := ge_inf HTraceSetM_has_inf.2.
            have Hlb_sigma := Hlb _ Htrace_mem.
            rewrite -Htrace0_eq_inf -Hsigma0_trmx in Hlb_sigma.
            rewrite HsigmaB_trmx HsigmaB_tr_eq in Hlb_sigma.
            rewrite Hphi_tau0_eq.
            exact: Hlb_sigma.
          * rewrite Hphi_tau0_eq.
            exact: (le_trans Hsigma0_tr_leR (ltW Hsigma_tr_gt_dB)).
      }
      have Hphi_tau0_pos :
          0 < phi_min B tau0.
      {
          have Htau0_psd : tau0 \is psdlf.
          {
            move: Htau0_ball.
            by move/eps_ball_psdlf.
          }
        have Hrho_tr_real : (\Tr rhoAB : C) = (@complex.Re R (\Tr rhoAB))%:C.
          by rewrite RRe_real // ger0_real // psdlf_trlf.
        have Htau0_nz : tau0 != 0.
        {
          apply/eqP=> Htau00.
          have Hzero_psd : (0 : 'F[H]_S_AB) \is psdlf.
            by rewrite psdlfE lexx.
          have Hpd0 : pur_dist (0 : 'F[H]_S_AB) rhoAB =
                      Num.sqrt (@complex.Re R (\Tr rhoAB)).
          {
            have Hzero_mx_psd : h2mx (0 : 'F[H]_S_AB) \is psdmx.
              by move: Hzero_psd; rewrite qualifE.
            have Hrho_mx_psd : h2mx rhoAB \is psdmx.
              by move: Prho; rewrite qualifE.
            have Hgfid0 :
                gfid (0 : 'F[H]_S_AB) rhoAB =
                Num.sqrt (1 - @complex.Re R (\Tr rhoAB)).
            {
              rewrite /gfid.
              rewrite (alt_gfid_gen Hzero_mx_psd Hrho_mx_psd).
              have -> :
                  @complex.Re R
                    (trnorm (sqrtmx (h2mx (0 : 'F[H]_S_AB)) *m sqrtmx (h2mx rhoAB))) = 0.
              {
                by rewrite h2mx0 sqrtmx0 mul0mx trnorm0 raddf0.
              }
              have -> :
                  @complex.Re R (1 - \tr (h2mx (0 : 'F[H]_S_AB))) = 1.
              {
                by rewrite h2mx0 mxtrace0 subr0.
              }
              have -> :
                  @complex.Re R (1 - \tr (h2mx rhoAB)) =
                  1 - @complex.Re R (\Tr rhoAB).
              {
                by rewrite raddfB /= Hrho_tr_real.
              }
              by rewrite sqrtr1 mul1r add0r.
            }
            rewrite /pur_dist.
            pose a := 1 - @complex.Re R (\Tr rhoAB).
            have Ha_ge0 : 0 <= a.
            {
              rewrite /a.
              by rewrite subr_ge0.
            }
            have -> :
                (gfid (0 : 'F[H]_S_AB) rhoAB)^2 =
                a.
            {
              rewrite Hgfid0.
              exact: sqr_sqrtr Ha_ge0.
            }
            by rewrite /a opprB addrCA subrr addr0.
          }
            have Hball := eps_ball_pur_dist Htau0_ball.
            rewrite Htau00 in Hball.
          have Hsqrt_le : Num.sqrt (@complex.Re R (\Tr rhoAB)) <= eps.
            by rewrite -Hpd0.
          have := lt_le_trans Hepslt Hsqrt_le.
          by rewrite ltxx.
        }
        have Htau0_real : (\Tr tau0) \is Num.real.
          exact: ger0_real (psdlf_trlf Htau0_psd).
        have Htau0_tr_real : (\Tr tau0 : C) = (@complex.Re R (\Tr tau0))%:C.
          by rewrite RRe_real.
        have Htau0_tr_ge0 : 0 <= @complex.Re R (\Tr tau0).
        {
          move: (psdlf_trlf Htau0_psd).
          by rewrite Htau0_tr_real lecR.
        }
        have Htau0_tr_ne0 : @complex.Re R (\Tr tau0) != 0.
        {
          apply/eqP=> Htau0_tr0.
          have Htau0_ge0 : 0 ⊑ tau0.
            by move: Htau0_psd; rewrite psdlfE.
          have Htau00 : tau0 == 0.
          {
            apply/trlf0_eq0.
            split=> //.
            by rewrite Htau0_tr_real Htau0_tr0.
          }
          by move/negP: Htau0_nz; rewrite Htau00.
        }
        have Htau0_tr_pos : 0 < @complex.Re R (\Tr tau0).
          by rewrite lt0r Htau0_tr_ge0 Htau0_tr_ne0.
        have eqSA : S_AB :\: B = A.
        {
          exact: setDU_r disAB.
        }
        have disSplit : [disjoint (S_AB :\: B) & (S_AB :&: B)].
        {
          setdec.
        }
        have Hphi_lb :
            @complex.Re R (\Tr tau0) / (dim 'H[H]_A)%:R <=
            phi_min B tau0.
        {
          apply: lb_le_inf.
          - by exists (@complex.Re R (\Tr sigma0)).
          - move=> v [sigma [Psigma [Hfeas ->]]].
            have Htr_sigma_real : (\Tr sigma : C) = (@complex.Re R (\Tr sigma))%:C.
              by rewrite RRe_real // ger0_real // psdlf_trlf.
            have Htau_leR :
                @complex.Re R (\Tr tau0) <=
                (dim 'H[H]_((S_AB :\: B)))%:R * @complex.Re R (\Tr sigma).
            {
              pose Hgap_nonneg0 := psdlf_trlf Hfeas.
              have Htau_leC :
                  \Tr tau0 <=
                  (dim 'H[H]_((S_AB :\: B)))%:R * \Tr sigma.
              {
                move: Hgap_nonneg0.
                rewrite raddfB /= castlf_trlfE (trlf_lift_I disSplit).
                by rewrite subr_ge0.
              }
              move: Htau_leC.
              rewrite Htau0_tr_real Htr_sigma_real.
              by rewrite -natrC -rmorphM /= lecR.
            }
            rewrite eqSA in Htau_leR.
            rewrite ler_pdivrMr; last by rewrite ltr0n dim_proper.
            by rewrite mulrC in Htau_leR.
        }
        have Htau0_dim_pos :
            0 < @complex.Re R (\Tr tau0) / (dim 'H[H]_A)%:R.
        {
          apply: divr_gt0.
          - exact: Htau0_tr_pos.
          - by rewrite ltr0n dim_proper.
        }
        exact: lt_le_trans Htau0_dim_pos Hphi_lb.
      }
      rewrite /hmin.
      have Hlog_le :
          log2 (phi_min B tau0) <= log2 (phi_min B tau).
      {
        exact: log2_le_pos Hphi_tau0_pos Hphi_le.
      }
      move: Hlog_le.
      by rewrite lerNl opprK.
    }
    have Htau0_opt : smooth_hmin B eps rhoAB = hmin B tau0.
    {
      apply/eqP; rewrite eq_le.
      apply/andP; split.
      - apply: ge_sup.
        + exists (hmin B tau0).
          exists tau0.
          split.
          * exact: Htau0_ball.
          * reflexivity.
        + apply/ubP=> v [tau [Htau_ball ->]].
          exact: Htau0_ub Htau_ball.
      - have Hsmooth_ub :
            has_ubound [set v : R | exists tauS : 'F[H]_S_AB,
              eps_ball eps rhoAB tauS /\ v = hmin B tauS].
        {
          exists (hmin B tau0).
          apply/ubP=> v [tau [Htau_ball ->]].
          exact: Htau0_ub Htau_ball.
        }
        have Htau0_mem :
            exists tauS : 'F[H]_S_AB,
              eps_ball eps rhoAB tauS /\ hmin B tau0 = hmin B tauS.
        {
          by exists tau0.
        }
        exact: (ub_le_sup Hsmooth_ub Htau0_mem).
    }
    exists tau0; exists sigma0.
    repeat split=> //.
  }
  case: Hopt => tau0 [sigma0 [Htau0_ball [Psigma0 [Hsigma0_feas [Hsigma0_opt [Htau0_opt Htau0_ub]]]]]].
    have Htau0_psd : tau0 \is psdlf.
    {
      move: Htau0_ball.
      by move/eps_ball_psdlf.
    }
    have Htau0_tr : @complex.Re R (\Tr tau0) <= 1.
    {
      move: Htau0_ball.
      by move/eps_ball_trlf.
    }
  pose tauAB := (P \o tau0 \o P : 'F[H]_S_AB).
  have PAproj : PA \is projlf.
    exact: supplf_proj.
  have PBproj : PB \is projlf.
    exact: supplf_proj.
  have HP_eq : P = (PA \⊗ PB : 'F[H]_S_AB).
  {
    apply: to_Fnd_inj.
    by rewrite /P (sdotFT _ _ disAB) to_Fnd_tenE.
  }
  have HPherm : P^A = P.
  {
    move: PAproj PBproj => /projlfP [HPAh _] /projlfP [HPBh _].
    by rewrite HP_eq tenf_adj HPAh HPBh -HP_eq.
  }
  have HtauAB_ball : eps_ball eps rhoAB tauAB.
  {
    have HPid : P \o P = P.
    {
      move: PAproj PBproj => /projlfP [_ HAid] /projlfP [_ HBid].
      apply: to_Fnd_inj.
      rewrite !to_Fnd_compE !(sdotFT _ _ disAB) -!to_Fnd_tenE -dotF_comp.
      by rewrite -tenf_comp ?HAid ?HBid.
    }
    have HPproj : P \is projlf.
    {
      apply/projlfP; split.
      - exact: HPherm.
      - exact: HPid.
    }
    have HPbound : P \is bound1lf.
      exact: projlf_bound1 HPproj.
    have HXB_psd :
        (((\1 : 'F[H]_A) \O rhoB : 'F[H]_S_AB) \is psdlf).
    {
      have -> :
          (((\1 : 'F[H]_A) \O rhoB : 'F[H]_S_AB)) =
          ((\1 : 'F[H]_A) \⊗ rhoB : 'F[H]_S_AB).
      {
        apply: to_Fnd_inj.
        by rewrite (sdotFT _ _ disAB) to_Fnd_tenE.
      }
      rewrite psdlfE.
      apply: tenf_ge0.
      - exact: disAB.
      - exact: lef01.
      - by move: PrhoB; rewrite psdlfE.
    }
    have HQAproj : (((PA \O (\1 : 'F[H]_B)) : 'F[H]_S_AB) \is projlf).
    {
      have HPA1_eq :
          (((PA \O (\1 : 'F[H]_B)) : 'F[H]_S_AB)) =
          (PA \⊗ (\1 : 'F[H]_B) : 'F[H]_S_AB).
      {
        apply: to_Fnd_inj.
        by rewrite (sdotFT _ _ disAB) to_Fnd_tenE.
      }
      move: PAproj => /projlfP [HPAh HAid].
      apply/projlfP.
      split.
      - by rewrite HPA1_eq tenf_adj HPAh adjf1 -HPA1_eq.
      - by rewrite HPA1_eq -tenf_comp ?HAid ?comp_lfun1l ?comp_lfun1r -?HPA1_eq.
    }
    have HQBproj : ((((\1 : 'F[H]_A) \O PB) : 'F[H]_S_AB) \is projlf).
    {
      have H1PB_eq :
          ((((\1 : 'F[H]_A) \O PB) : 'F[H]_S_AB)) =
          ((\1 : 'F[H]_A) \⊗ PB : 'F[H]_S_AB).
      {
        apply: to_Fnd_inj.
        by rewrite (sdotFT _ _ disAB) to_Fnd_tenE.
      }
      move: PBproj => /projlfP [HPBh HBid].
      apply/projlfP.
      split.
      - by rewrite H1PB_eq tenf_adj adjf1 HPBh -H1PB_eq.
      - by rewrite H1PB_eq -tenf_comp ?HBid ?comp_lfun1l ?comp_lfun1r -?H1PB_eq.
    }
    have proj_absorbL : forall (X Q : 'F[H]_S_AB),
        X \is hermlf -> Q \is projlf ->
        (supph X `<=` supph Q)%HS -> Q \o X = X.
    {
      move=> X Q HXh HQ /lehP HS.
      apply/lfunP=> u; rewrite lfunE /=.
      have HXmem : X u \in supph X.
      {
        have HXeq : X^A = X.
          exact: hermlf_adjE HXh.
        apply/memh_suppP.
        exists u.
        by rewrite HXeq.
      }
      have HXQ : X u \in supph Q.
        exact: HS _ HXmem.
      move/memhP: HXQ => HXQ.
      move: (supph_Pid (ProjLf_Build HQ)) => HQid.
      rewrite HQid in HXQ.
      exact: HXQ.
    }
    have proj_absorbR : forall (X Q : 'F[H]_S_AB),
        X \is hermlf -> Q \is projlf ->
        (supph X `<=` supph Q)%HS -> X \o Q = X.
    {
      move=> X Q HXh HQ HS.
      have HQeq : Q^A = Q.
        exact: hermlf_adjE (projlf_herm HQ).
      have HXeq : X^A = X.
        exact: hermlf_adjE HXh.
      have Hleft : Q \o X = X.
        exact: proj_absorbL HXh HQ HS.
      have HleftA : (Q \o X)^A = X^A.
        by rewrite Hleft.
      rewrite adjf_comp HQeq HXeq in HleftA.
      exact: HleftA.
    }
    have supph_le_projR : forall (X Q : 'F[H]_S_AB),
        X \is psdlf -> Q \is projlf -> X \o Q = X ->
        (supph X `<=` supph Q)%HS.
    {
      move=> X Q PX HQ HXQ.
      have HQid : (supph Q)%:VF = Q.
        exact: supph_Pid (ProjLf_Build HQ).
      have Htr0 : \Tr ((PsdLf_Build PX : 'F[H]_S_AB)
                       \o (~` supph Q)%:VF) = 0.
      {
        rewrite hsE /= /cplmt HQid linearBr /= comp_lfun1r HXQ.
        by rewrite subrr linear0.
      }
      exact: supph_trlf0_le Htr0.
    }
    have Hsupp_B :
        (supph rhoAB `<=` supph (((\1 : 'F[H]_A) \O PB) : 'F[H]_S_AB))%HS.
    {
      have Hsupp_lift :
          (supph rhoAB `<=` supph (((\1 : 'F[H]_A) \O rhoB) : 'F[H]_S_AB))%HS.
        exact: ptrace_supph_lift.
      have HXB_right :
          (((\1 : 'F[H]_A) \O rhoB : 'F[H]_S_AB) \o
             (((\1 : 'F[H]_A) \O PB) : 'F[H]_S_AB)) =
          ((\1 : 'F[H]_A) \O rhoB : 'F[H]_S_AB).
      {
        rewrite sdotI_comp.
        by rewrite HrhoB_right.
      }
      have Hsupp_XB :
          (supph (((\1 : 'F[H]_A) \O rhoB : 'F[H]_S_AB))
             `<=` supph (((\1 : 'F[H]_A) \O PB) : 'F[H]_S_AB))%HS.
      {
        exact: supph_le_projR HXB_psd HQBproj HXB_right.
      }
      exact: le_trans Hsupp_lift Hsupp_XB.
    }
    have HXA_psd :
        ((rhoA \⊗ (\1 : 'F[H]_B) : 'F[H]_S_AB) \is psdlf).
    {
      rewrite psdlfE.
      apply: tenf_ge0.
      - exact: disAB.
      - by move: PrhoA; rewrite psdlfE.
      - exact: lef01.
    }
    have Hsupp_A :
        (supph rhoAB `<=` supph ((PA \O (\1 : 'F[H]_B)) : 'F[H]_S_AB))%HS.
    {
      have Hrho_le :
          rhoAB <= (dim 'H[H]_B)%:R *: (rhoA \⊗ (\1 : 'F[H]_B) : 'F[H]_S_AB).
      { exact: (@op_bound R L H A B disAB rhoAB Prho). }
      have Hsupp_tensor :
          (supph rhoAB `<=` supph ((dim 'H[H]_B)%:R *:
            (rhoA \⊗ (\1 : 'F[H]_B) : 'F[H]_S_AB)))%HS.
      {
        exact: (@supph_lef R _ (PsdLf_Build Prho) _ Hrho_le).
      }
      have HXA_right :
          ((rhoA \⊗ (\1 : 'F[H]_B) : 'F[H]_S_AB) \o
             ((PA \O (\1 : 'F[H]_B)) : 'F[H]_S_AB)) =
          (rhoA \⊗ (\1 : 'F[H]_B) : 'F[H]_S_AB).
      {
        apply: to_Fnd_inj.
        rewrite !to_Fnd_compE !(sdotFT _ _ disAB) -!to_Fnd_tenE -dotF_comp.
        rewrite -tenf_comp ?comp_lfun1r ?comp_lfun1l //.
        by rewrite HrhoA_right.
      }
      have Hsupp_XA :
          (supph ((rhoA \⊗ (\1 : 'F[H]_B) : 'F[H]_S_AB))
             `<=` supph ((PA \O (\1 : 'F[H]_B)) : 'F[H]_S_AB))%HS.
      {
        exact: supph_le_projR HXA_psd HQAproj HXA_right.
      }
      have Hsupp_tensor' :
          (supph ((dim 'H[H]_B)%:R *:
            (rhoA \⊗ (\1 : 'F[H]_B) : 'F[H]_S_AB))
             `<=` supph ((rhoA \⊗ (\1 : 'F[H]_B) : 'F[H]_S_AB)))%HS.
      {
        exact: supphZ_le.
      }
      exact: le_trans Hsupp_tensor (le_trans Hsupp_tensor' Hsupp_XA).
    }
    have HrhoA_lift_left :
        ((PA \O (\1 : 'F[H]_B)) : 'F[H]_S_AB) \o rhoAB = rhoAB.
    {
      exact: proj_absorbL (psdlf_herm Prho) HQAproj Hsupp_A.
    }
    have HrhoB_lift_left :
        ((((\1 : 'F[H]_A) \O PB) : 'F[H]_S_AB) \o rhoAB) = rhoAB.
    {
      exact: proj_absorbL (psdlf_herm Prho) HQBproj Hsupp_B.
    }
    have HrhoA_lift_right :
        rhoAB \o ((PA \O (\1 : 'F[H]_B)) : 'F[H]_S_AB) = rhoAB.
    {
      exact: proj_absorbR (psdlf_herm Prho) HQAproj Hsupp_A.
    }
    have HrhoB_lift_right :
        rhoAB \o ((((\1 : 'F[H]_A) \O PB) : 'F[H]_S_AB)) = rhoAB.
    {
      exact: proj_absorbR (psdlf_herm Prho) HQBproj Hsupp_B.
    }
    have HPsplit :
        P =
        ((PA \O (\1 : 'F[H]_B)) : 'F[H]_S_AB) \o
        ((((\1 : 'F[H]_A) \O PB) : 'F[H]_S_AB)).
    {
      apply: to_Fnd_inj.
      rewrite /P !to_Fnd_compE !(sdotFT _ _ disAB) -!to_Fnd_tenE -dotF_comp.
      by rewrite -tenf_comp ?comp_lfun1l ?comp_lfun1r.
    }
    have Hrho_left : P \o rhoAB = rhoAB.
    {
      rewrite HPsplit -comp_lfunA HrhoB_lift_left.
      exact: HrhoA_lift_left.
    }
    have Hrho_right : rhoAB \o P = rhoAB.
    {
      rewrite HPsplit comp_lfunA HrhoA_lift_right.
      exact: HrhoB_lift_right.
    }
    have Hform_tau0 : (formso P) tau0 = tauAB.
      by rewrite formsoE HPherm /tauAB.
    have Hform_rho : (formso P) rhoAB = rhoAB.
    {
      by rewrite formsoE HPherm -comp_lfunA Hrho_right Hrho_left.
    }
    have HtauAB_psd : tauAB \is psdlf.
    {
      have Hform_psd : ((formso P) tau0) \is psdlf.
        exact: cp_psdP Htau0_psd.
      by rewrite Hform_tau0 in Hform_psd.
    }
    have HtauAB_tr : @complex.Re R (\Tr tauAB) <= 1.
    {
      have Htr_form : \Tr tauAB <= \Tr tau0.
      {
        have := qo_trlfE (formso (Bound1Lf_Build HPbound)) Htau0_psd.
        by rewrite formsoE HPherm /tauAB.
      }
      have HtauAB_real : \Tr tauAB \is Num.real.
        exact: ger0_real (psdlf_trlf HtauAB_psd).
      have Htau0_real : \Tr tau0 \is Num.real.
        exact: ger0_real (psdlf_trlf Htau0_psd).
      move: Htr_form.
      rewrite -(RRe_real HtauAB_real) -(RRe_real Htau0_real) lecR.
      move=> Htr_form.
      exact: le_trans Htr_form Htau0_tr.
    }
      have HtauAB_pd : pur_dist tauAB rhoAB <= eps.
      { have Hform_cptn :
            (formso (Bound1Lf_Build HPbound) : 'SO('H_S_AB, 'H_S_AB)) \is cptn.
        {
          exact: is_cptn.
        }
        have [_ Hpd] :=
            pd_mono Hform_cptn Htau0_psd Prho Htau0_tr Htr.
        rewrite Hform_tau0 Hform_rho in Hpd.
        exact: le_trans Hpd (eps_ball_pur_dist Htau0_ball). }
      have HtauAB_pos : 0 < @complex.Re R (\Tr tauAB).
      {
        have Hsmall : 0 <= eps < Num.sqrt (@complex.Re R (\Tr rhoAB))
          by apply/andP; split.
        have Holdball :
            ((tauAB \is psdlf) &&
              (@complex.Re R (\Tr tauAB) <= 1)) &&
            (pur_dist tauAB rhoAB <= eps)
          by rewrite HtauAB_psd HtauAB_tr HtauAB_pd.
        exact: (eps_ball_trace_pos_from_small Prho Htr Hsmall Holdball).
      }
      apply/andP; split.
      - apply/andP; split.
        + by apply/andP; split.
        + exact: HtauAB_tr.
      - exact: HtauAB_pd.
    }
  have HtauAB_ge : hmin B tau0 <= hmin B tauAB.
  {
    pose QB := ((\1 : 'F[H]_B) - PB).
    pose sigmaPB := (PB \o sigma0 \o PB : 'F[H]_B).
    pose sigmaQB := (QB \o sigma0 \o QB : 'F[H]_B).
    pose sigma1 := (sigmaPB + sigmaQB : 'F[H]_B).
    have HQBproj : QB \is projlf.
    {
      move: PBproj => /projlfP [HPBh HBid].
      apply/projlfP; split.
      - by rewrite /QB adjfB adjf1 HPBh.
      - rewrite /QB linearBl/= !linearBr/= !comp_lfun1l !comp_lfun1r.
        by rewrite HBid opprB addrA addrNK.
    }
    have HsigmaPB_psd : sigmaPB \is psdlf.
    {
      have Htmp : ((formso PB) sigma0) \is psdlf.
        exact: cp_psdP Psigma0.
      have HPBh : PB^A = PB.
        exact: hermlf_adjE (projlf_herm PBproj).
      by rewrite formsoE HPBh /sigmaPB in Htmp.
    }
    have HsigmaQB_psd : sigmaQB \is psdlf.
    {
      have Htmp : ((formso QB) sigma0) \is psdlf.
        exact: cp_psdP Psigma0.
      have HQBh : QB^A = QB.
        exact: hermlf_adjE (projlf_herm HQBproj).
      by rewrite formsoE HQBh /sigmaQB in Htmp.
    }
    have Hsigma1_psd : sigma1 \is psdlf.
    {
      rewrite /sigma1.
      exact: psdlfD HsigmaPB_psd HsigmaQB_psd.
    }
    have Hsigma1_tr : @complex.Re R (\Tr sigma1) = @complex.Re R (\Tr sigma0).
    {
      have HtrPB : \Tr sigmaPB = \Tr (PB \o sigma0).
      {
        rewrite /sigmaPB lftraceC comp_lfunA.
        by rewrite (projlf_idem PBproj).
      }
      have HtrQB : \Tr sigmaQB = \Tr (QB \o sigma0).
      {
        rewrite /sigmaQB lftraceC comp_lfunA.
        by rewrite (projlf_idem HQBproj).
      }
      rewrite /sigma1 linearD/= HtrPB HtrQB -linearD/=.
      rewrite /QB linearBl/= !comp_lfun1l addrC subrK.
      reflexivity.
    }
    have HEsigma :
        (P \o (((\1 : 'F[H]_A) \O sigma0) : 'F[H]_S_AB) \o P) =
        ((PA \O sigmaPB) : 'F[H]_S_AB).
    {
      rewrite HP_eq.
      apply: to_Fnd_inj.
      rewrite !to_Fnd_compE !(sdotFT _ _ disAB) -!to_Fnd_tenE -!dotF_comp.
      rewrite -tenf_comp ?comp_lfun1l //.
      rewrite -tenf_comp ?comp_lfun1r //.
      by rewrite (projlf_idem PAproj) /sigmaPB comp_lfunA.
    }
    have Hnonneg :
        ((((\1 : 'F[H]_A) \O sigma1) : 'F[H]_S_AB) -
         (P \o (((\1 : 'F[H]_A) \O sigma0) : 'F[H]_S_AB) \o P)) \is psdlf.
    {
      have HcplmtPA_proj :
          ((((\1 : 'F[H]_A) - PA) : 'F[H]_A) \is projlf).
      {
        change ((((\1 : 'F[H]_A) - ((ProjLf_Build PAproj) : 'F[H]_A))
          : 'F[H]_A) \is projlf).
        rewrite cplmtE.
        exact: cplmt_proj (ProjLf_Build PAproj).
      }
      have HcplmtPA_psd :
          ((((\1 : 'F[H]_A) - PA) : 'F[H]_A) \is psdlf).
      {
        exact: projlf_psd HcplmtPA_proj.
      }
      have HblkPB_psd :
          (((((\1 : 'F[H]_A) - PA) \O sigmaPB) : 'F[H]_S_AB) \is psdlf).
      {
        have -> :
            (((((\1 : 'F[H]_A) - PA) \O sigmaPB) : 'F[H]_S_AB)) =
            ((((\1 : 'F[H]_A) - PA) \⊗ sigmaPB) : 'F[H]_S_AB).
        {
          apply: to_Fnd_inj.
          by rewrite (sdotFT _ _ disAB) to_Fnd_tenE.
        }
        rewrite psdlfE.
        apply: tenf_ge0.
        - exact: disAB.
        - by move: HcplmtPA_psd; rewrite psdlfE.
        - by move: HsigmaPB_psd; rewrite psdlfE.
      }
      have HblkQB_psd :
          ((((\1 : 'F[H]_A) \O sigmaQB) : 'F[H]_S_AB) \is psdlf).
      {
        have -> :
            ((((\1 : 'F[H]_A) \O sigmaQB) : 'F[H]_S_AB)) =
            (((\1 : 'F[H]_A) \⊗ sigmaQB) : 'F[H]_S_AB).
        {
          apply: to_Fnd_inj.
          by rewrite (sdotFT _ _ disAB) to_Fnd_tenE.
        }
        rewrite psdlfE.
        apply: tenf_ge0.
        - exact: disAB.
        - exact: lef01.
        - by move: HsigmaQB_psd; rewrite psdlfE.
      }
      rewrite HEsigma /sigma1 sdotfDr.
      have -> :
          ((((\1 : 'F[H]_A) \O sigmaPB) : 'F[H]_S_AB) +
           (((\1 : 'F[H]_A) \O sigmaQB) : 'F[H]_S_AB) -
           ((PA \O sigmaPB) : 'F[H]_S_AB)) =
          (((((\1 : 'F[H]_A) - PA) \O sigmaPB) : 'F[H]_S_AB) +
           (((\1 : 'F[H]_A) \O sigmaQB) : 'F[H]_S_AB)).
      {
        rewrite -addrA.
        rewrite [(((\1 : 'F[H]_A) \O sigmaQB) : 'F[H]_S_AB) +
                 - ((PA \O sigmaPB) : 'F[H]_S_AB)]addrC.
        rewrite addrA.
        by rewrite sdotfBl.
      }
      exact: psdlfD HblkPB_psd HblkQB_psd.
    }
    have Hfeas_raw :
        ((((\1 : 'F[H]_A) \O sigma1) : 'F[H]_S_AB) - tauAB) \is psdlf.
    {
      have Hproj_feas :
          ((P \o (((\1 : 'F[H]_A) \O sigma0) : 'F[H]_S_AB) \o P) - tauAB)
            \is psdlf.
      {
        have Htmp : ((formso P)
            ((((\1 : 'F[H]_A) \O sigma0) : 'F[H]_S_AB) - tau0)) \is psdlf.
          exact: cp_psdP Hsigma0_feas.
        rewrite formsoE HPherm in Htmp.
        have Htmp' :
            ((P \o ((((\1 : 'F[H]_A) \O sigma0) : 'F[H]_S_AB) - tau0) \o P)
              \is psdlf).
          exact: Htmp.
        rewrite linearBr/= linearBl/= /tauAB in Htmp'.
        exact: Htmp'.
      }
      have -> :
          ((((\1 : 'F[H]_A) \O sigma1) : 'F[H]_S_AB) - tauAB) =
          (((((\1 : 'F[H]_A) \O sigma1) : 'F[H]_S_AB) -
             (P \o (((\1 : 'F[H]_A) \O sigma0) : 'F[H]_S_AB) \o P)) +
           ((P \o (((\1 : 'F[H]_A) \O sigma0) : 'F[H]_S_AB) \o P) - tauAB)).
      {
        pose A0 := ((((\1 : 'F[H]_A) \O sigma1) : 'F[H]_S_AB)).
        pose B0 := (P \o (((\1 : 'F[H]_A) \O sigma0) : 'F[H]_S_AB) \o P).
        pose C0 := tauAB.
        change (A0 - C0 = (A0 - B0) + (B0 - C0)).
        change (A0 + - C0 = (A0 + - B0) + (B0 + - C0)).
        have -> :
            (A0 + - B0) + (B0 + - C0) = ((A0 + - B0) + B0) + - C0.
          by rewrite addrA.
        congr (_ + - C0).
        have -> : (A0 + - B0) + B0 = A0.
          by rewrite -addrA addNr addr0.
        reflexivity.
      }
      exact: psdlfD Hnonneg Hproj_feas.
    }
    have eqSA_support : S_AB :\: B = A.
    {
      exact: setDU_r disAB.
    }
    have eqSB_support : S_AB :&: B = B.
    {
      by setdec.
    }
    have eqST_support :
        (S_AB :\: B) :|: (S_AB :&: B) = S_AB.
    {
      by rewrite finset.setUC finset.setID.
    }
    have Hsigma1_feas :
        phi_min_feasible B tauAB (@complex.Re R (\Tr sigma1)).
    {
      rewrite /phi_min_feasible.
      pose sigma1I := castlf (esym eqSB_support, esym eqSB_support) sigma1.
      have Hsigma1I_psd : sigma1I \is psdlf.
      {
        exact: castlf_psdlf Hsigma1_psd.
      }
      have Hsigma1I_tr : @complex.Re R (\Tr sigma1I) = @complex.Re R (\Tr sigma1).
      {
        rewrite /sigma1I castlf_trlfE.
        reflexivity.
      }
      have Hsigma1I_back : castlf (eqSB_support, eqSB_support) sigma1I = sigma1.
      {
        by rewrite /sigma1I castlf_comp castlf_id.
      }
      have eqU1 :
          (S_AB :\: B) :|: (S_AB :&: B) =
          (S_AB :\: B) :|: B.
      {
        by rewrite eqSB_support.
      }
      have eqU2 :
          (S_AB :\: B) :|: B = S_AB.
      {
        by rewrite eqSA_support.
      }
      have Hcast_step1 :
          castlf (eqU1, eqU1)
            ((\1 : 'F[H]_(S_AB :\: B)) \O sigma1I) =
          ((\1 : 'F[H]_(S_AB :\: B)) \O sigma1 :
            'F[H]_((S_AB :\: B) :|: B)).
      {
        rewrite (sdotIf_cast_r eqSB_support eqU1).
        by rewrite Hsigma1I_back.
      }
      have Hcast_step2 :
          castlf (eqU2, eqU2)
            ((\1 : 'F[H]_(S_AB :\: B)) \O sigma1 :
              'F[H]_((S_AB :\: B) :|: B)) =
          (((\1 : 'F[H]_A) \O sigma1) : 'F[H]_S_AB).
      {
        rewrite (sdotIf_cast_l eqSA_support eqU2).
        have -> :
            castlf (eqSA_support, eqSA_support)
              (\1 : 'F[H]_(S_AB :\: B)) = (\1 : 'F[H]_A).
        {
          exact: castlf1.
        }
        reflexivity.
      }
      have Hcast_comp :
          castlf (eqST_support, eqST_support)
            ((\1 : 'F[H]_(S_AB :\: B)) \O sigma1I) =
          castlf (eqU2, eqU2)
            (castlf (eqU1, eqU1)
              ((\1 : 'F[H]_(S_AB :\: B)) \O sigma1I)).
      {
        rewrite castlf_comp.
        have -> : etrans eqU1 eqU2 = eqST_support by apply: eq_irrelevance.
        reflexivity.
      }
      exists sigma1I.
      split.
      - exact: Hsigma1I_psd.
      split.
      - lazymatch goal with
        | |- context [castlf (?eqHidden, ?eqHidden) _] =>
            pose eqHidden0 := eqHidden
        end.
        have Hcast_hidden :
            castlf (eqHidden0, eqHidden0)
              ((\1 : 'F[H]_(S_AB :\: B)) \O sigma1I) =
            castlf (eqST_support, eqST_support)
              ((\1 : 'F[H]_(S_AB :\: B)) \O sigma1I).
        {
          have -> : eqHidden0 = eqST_support by apply: eq_irrelevance.
          reflexivity.
        }
        rewrite Hcast_hidden Hcast_comp Hcast_step1 Hcast_step2.
        exact: Hfeas_raw.
      - by rewrite Hsigma1I_tr.
    }
    (* Tomamichel Φ-vi (data processing): tauAB = formso (PA ⊗ PB) tau0 is the
       projector sandwich, which factors as the A-channel formso PA followed
       by the B-channel formso PB. Both are trace-nonincreasing CP maps, so
       phi_min only increases under them — exactly phi_min_data_proc_A and
       phi_min_data_proc_B. *)
    have Hphi_le : phi_min B tauAB <= phi_min B tau0.
    {
      have HPA_b1 : PA \is bound1lf := projlf_bound1 PAproj.
      have HPB_b1 : PB \is bound1lf := projlf_bound1 PBproj.
      have HformPA_cp : (formso PA : 'SO[H]_A) \is cpmap := formso_cp PA.
      have HPA_herm : PA^A = PA := hermlf_adjE (projlf_herm PAproj).
      have HformPA_dualtn : (formso PA : 'SO[H]_A)^*o \is tnmap.
      { rewrite dualso_formso HPA_herm (Bound1Lf_BuildE HPA_b1).
        exact: formso_tn _. }
      have HformPB_cptn : (formso PB : 'SO[H]_B) \is cptn.
      { by rewrite (Bound1Lf_BuildE HPB_b1) qualifE formso_cp formso_tn. }
      pose EPB : 'QO[H]_B := QOperation_Build HformPB_cptn.
      have HtensoPB_cp :
          ((\:1 : 'SO[H]_A) :⊗ (formso PB : 'SO[H]_B)) \is cpmap.
      { exact: (@tenso_cp R L H A A B B disAB
          (\:1 : 'CP[H]_A) (CPMap_Build (formso_cp PB))). }
      have HY_psd :
          (((\:1 : 'SO[H]_A) :⊗ (formso PB : 'SO[H]_B)) tau0) \is psdlf.
      { rewrite (CPMap_BuildE HtensoPB_cp). exact: cp_psdP Htau0_psd. }
      have HtauAB_eq :
          tauAB =
          ((formso PA : 'SO[H]_A) :⊗ (\:1 : 'SO[H]_B))
            (((\:1 : 'SO[H]_A) :⊗ (formso PB : 'SO[H]_B)) tau0).
      { rewrite -comp_soE -tenso_comp ?disAB // comp_so1r comp_so1l.
        rewrite tenso_formso ?disAB // -HP_eq.
        by rewrite formsoE HPherm /tauAB. }
      rewrite HtauAB_eq.
      apply: le_trans.
      - exact: (@phi_min_data_proc_A R L H A A B disAB disAB
          (((\:1 : 'SO[H]_A) :⊗ (formso PB : 'SO[H]_B)) tau0)
          (formso PA) HY_psd HformPA_cp HformPA_dualtn).
      - have HEPB :
            ((\:1 : 'SO[H]_A) :⊗ EPB) tau0 =
            ((\:1 : 'SO[H]_A) :⊗ (formso PB : 'SO[H]_B)) tau0 by [].
        rewrite -HEPB.
        exact: (@phi_min_data_proc_B R L H A B B disAB disAB tau0 EPB
          Htau0_psd).
    }
    have Hphi_pos :
        0 < phi_min B tauAB.
    {
        have HtauAB_psd : tauAB \is psdlf.
        {
          move: HtauAB_ball.
          by move/eps_ball_psdlf.
        }
      have Hrho_tr_real : (\Tr rhoAB : C) = (@complex.Re R (\Tr rhoAB))%:C.
        by rewrite RRe_real // ger0_real // psdlf_trlf.
      have Hrho_tr_ge0 : 0 <= @complex.Re R (\Tr rhoAB).
      {
        move: (psdlf_trlf Prho).
        by rewrite Hrho_tr_real lecR.
      }
      have HtauAB_nz : tauAB != 0.
      {
        apply/eqP=> HtauAB0.
        have Hzero_psd : (0 : 'F[H]_S_AB) \is psdlf.
          by rewrite psdlfE lexx.
        have Hpd0 : pur_dist (0 : 'F[H]_S_AB) rhoAB =
                    Num.sqrt (@complex.Re R (\Tr rhoAB)).
        {
          have Hzero_mx_psd : h2mx (0 : 'F[H]_S_AB) \is psdmx.
            by move: Hzero_psd; rewrite qualifE.
          have Hrho_mx_psd : h2mx rhoAB \is psdmx.
            by move: Prho; rewrite qualifE.
          have Hgfid0 :
              gfid (0 : 'F[H]_S_AB) rhoAB =
              Num.sqrt (1 - @complex.Re R (\Tr rhoAB)).
          {
            rewrite /gfid.
            rewrite (alt_gfid_gen Hzero_mx_psd Hrho_mx_psd).
            have -> :
                @complex.Re R
                  (trnorm (sqrtmx (h2mx (0 : 'F[H]_S_AB)) *m sqrtmx (h2mx rhoAB))) = 0.
            {
              by rewrite h2mx0 sqrtmx0 mul0mx trnorm0 raddf0.
            }
            have -> :
                @complex.Re R (1 - \tr (h2mx (0 : 'F[H]_S_AB))) = 1.
            {
              by rewrite h2mx0 mxtrace0 subr0.
            }
            have -> :
                @complex.Re R (1 - \tr (h2mx rhoAB)) =
                1 - @complex.Re R (\Tr rhoAB).
            {
              by rewrite raddfB /= Hrho_tr_real.
            }
            by rewrite sqrtr1 mul1r add0r.
          }
          rewrite /pur_dist.
          pose a := 1 - @complex.Re R (\Tr rhoAB).
          have Ha_ge0 : 0 <= a.
          {
            rewrite /a.
            by rewrite subr_ge0.
          }
          have -> :
              (gfid (0 : 'F[H]_S_AB) rhoAB)^2 =
              a.
          {
            rewrite Hgfid0.
            exact: sqr_sqrtr Ha_ge0.
          }
          by rewrite /a opprB addrCA subrr addr0.
        }
          have Hball := eps_ball_pur_dist HtauAB_ball.
          rewrite HtauAB0 in Hball.
        have Hsqrt_le : Num.sqrt (@complex.Re R (\Tr rhoAB)) <= eps.
          by rewrite -Hpd0.
        have := lt_le_trans Hepslt Hsqrt_le.
        by rewrite ltxx.
      }
      have HtauAB_real : (\Tr tauAB) \is Num.real.
        exact: ger0_real (psdlf_trlf HtauAB_psd).
      have HtauAB_tr_real : (\Tr tauAB : C) = (@complex.Re R (\Tr tauAB))%:C.
        by rewrite RRe_real.
      have HtauAB_tr_ge0 : 0 <= @complex.Re R (\Tr tauAB).
      {
        move: (psdlf_trlf HtauAB_psd).
        by rewrite HtauAB_tr_real lecR.
      }
      have HtauAB_tr_ne0 : @complex.Re R (\Tr tauAB) != 0.
      {
        apply/eqP=> Htr0.
        have HtauAB_ge0 : 0 ⊑ tauAB.
          by move: HtauAB_psd; rewrite psdlfE.
        have HtauAB0 : tauAB == 0.
        {
          apply/trlf0_eq0.
          split=> //.
          by rewrite HtauAB_tr_real Htr0.
        }
        by move/negP: HtauAB_nz; rewrite HtauAB0.
      }
      have HtauAB_tr_pos : 0 < @complex.Re R (\Tr tauAB).
        by rewrite lt0r HtauAB_tr_ge0 HtauAB_tr_ne0.
      have eqSA : S_AB :\: B = A.
      {
        exact: setDU_r disAB.
      }
      have disSplit : [disjoint (S_AB :\: B) & (S_AB :&: B)].
      {
        setdec.
      }
      have Hphi_lb :
          @complex.Re R (\Tr tauAB) / (dim 'H[H]_A)%:R <=
          phi_min B tauAB.
      {
        apply: lb_le_inf.
        - by exists (@complex.Re R (\Tr sigma1)).
        - move=> v [sigma [Psigma [Hfeas ->]]].
          have Htr_sigma_real : (\Tr sigma : C) = (@complex.Re R (\Tr sigma))%:C.
            by rewrite RRe_real // ger0_real // psdlf_trlf.
          have Htau_leR :
              @complex.Re R (\Tr tauAB) <=
              (dim 'H[H]_((S_AB :\: B)))%:R * @complex.Re R (\Tr sigma).
          {
            pose Hgap_real :=
              ger0_real (psdlf_trlf Hfeas).
            pose Hgap_nonneg0 :=
              psdlf_trlf Hfeas.
            have Htau_leC :
                \Tr tauAB <=
                (dim 'H[H]_((S_AB :\: B)))%:R * \Tr sigma.
            {
              move: Hgap_nonneg0.
              rewrite raddfB /= castlf_trlfE (trlf_lift_I disSplit).
              by rewrite subr_ge0.
            }
            move: Htau_leC.
            rewrite HtauAB_tr_real Htr_sigma_real.
            by rewrite -natrC -rmorphM /= lecR.
          }
          rewrite eqSA in Htau_leR.
          rewrite ler_pdivrMr; last by rewrite ltr0n dim_proper.
          by rewrite mulrC in Htau_leR.
      }
      have HtauAB_dim_pos :
          0 < @complex.Re R (\Tr tauAB) / (dim 'H[H]_A)%:R.
      {
        apply: divr_gt0.
        - exact: HtauAB_tr_pos.
        - by rewrite ltr0n dim_proper.
      }
      exact: lt_le_trans HtauAB_dim_pos Hphi_lb.
    }
    rewrite /hmin.
    have Hlog_le :
        log2 (phi_min B tauAB) <= log2 (phi_min B tau0).
      exact: log2_le_pos Hphi_pos Hphi_le.
    move: Hlog_le.
    by rewrite lerNl opprK.
  }
  have HtauAB_le : hmin B tauAB <= smooth_hmin B eps rhoAB.
  {
    rewrite Htau0_opt.
    exact: Htau0_ub HtauAB_ball.
  }
  have HtauAB_opt : smooth_hmin B eps rhoAB = hmin B tauAB.
  {
    apply/eqP; rewrite eq_le.
    apply/andP; split.
    - rewrite Htau0_opt.
      exact: HtauAB_ge.
    - exact: HtauAB_le.
  }
  have HtauAB_ub :
      forall tau : 'F[H]_S_AB,
        eps_ball eps rhoAB tau -> hmin B tau <= hmin B tauAB.
  {
    move=> tau Htau.
    exact: le_trans (Htau0_ub tau Htau) HtauAB_ge.
  }
  have HtauAB_optE : smooth_hminE B eps rhoAB = hminE B tauAB.
  {
    have Heps_pair : 0 <= eps < Num.sqrt (@complex.Re R (\Tr rhoAB)).
    { by rewrite Heps0 Hepslt. }
    apply/eqP; rewrite eq_le; apply/andP; split.
    - rewrite /smooth_hminE.
      apply: ge_ereal_sup => v [tau [Htau ->]].
      have Htau_psd : tau \is psdlf := eps_ball_psdlf Htau.
      have Htau_tr : @complex.Re R (\Tr tau) <= 1 := eps_ball_trlf Htau.
      have Htau_pos : 0 < @complex.Re R (\Tr tau).
      { exact: eps_ball_trace_pos Prho Htr Heps_pair Htau. }
      have HtauAB_psd : tauAB \is psdlf := eps_ball_psdlf HtauAB_ball.
      have HtauAB_tr : @complex.Re R (\Tr tauAB) <= 1 :=
        eps_ball_trlf HtauAB_ball.
      have HtauAB_pos : 0 < @complex.Re R (\Tr tauAB).
      { exact: eps_ball_trace_pos Prho Htr Heps_pair HtauAB_ball. }
      rewrite (@hminE_EFin R L H S_AB B tau
        (@phi_min_pos_trace R L H S_AB B tau
          Htau_psd Htau_tr Htau_pos)).
      rewrite (@hminE_EFin R L H S_AB B tauAB
        (@phi_min_pos_trace R L H S_AB B tauAB
          HtauAB_psd HtauAB_tr HtauAB_pos)).
      by rewrite lee_fin; exact: HtauAB_ub.
    - rewrite /smooth_hminE.
      apply: ereal_sup_ubound.
      by exists tauAB.
  }
  have HPid : P \o P = P.
  {
    move: PAproj PBproj => /projlfP [_ HAid] /projlfP [_ HBid].
    apply: to_Fnd_inj.
    rewrite !to_Fnd_compE !(sdotFT _ _ disAB) -!to_Fnd_tenE -dotF_comp.
    by rewrite -tenf_comp ?HAid ?HBid.
  }
  have HPtau_left : P \o tauAB = tauAB.
  by rewrite /tauAB !comp_lfunA HPid.
  have HPtau_right : tauAB \o P = tauAB.
  by rewrite /tauAB -!comp_lfunA HPid.
  exists tauAB.
  split.
  - exact: HtauAB_ball.
  - split.
    + exact: HtauAB_optE.
    + split.
      * exact: HPtau_left.
      * exact: HPtau_right.
Qed.

End SmoothingSupport.

(* ================================================================== *)
(* Support property for smoothing (max half)                            *)
(* Tomamichel thesis (arXiv:1203.2142), Proposition 5.1 — tex pr:smoothing/support, max half. *)
(* math: Under Tomamichel's standing assumption ε < √tr(ρ), for               *)
(*   ρ ∈ S_≤(ℋ_{AB}), there exists τ̃ ∈ B^ε(ρ_{AB}) with                 *)
(*   τ̃ supported on supp(ρ_A) ⊗ supp(ρ_B) and                           *)
(*   H^ε_max(A|B)_ρ = H_max(A|B)_τ̃.                                     *)
(* consumer: pr_ss is used downstream by the BB84 secrecy proof. *)
(* ================================================================== *)

(* Statement (Proposition 5.1, max-half).                      *)
(* The max-half route follows the dual chain:                                  *)
(*   hmax(A|B)[tau0] = -hmin(A|C0)[ptrace_B θ0_ABC]   [minmax_dual]            *)
(* where θ0_ABC is a pure rank-1 purification of tau0 on a fresh purifier C0. *)
(* The DPI on phi_min proves the (Π_A ⊗ Π_B)·ρ·(Π_A ⊗ Π_B) projection step    *)
(* directly, avoiding an unnecessary fidelity detour.                         *)
(* The fresh purifier C0 + dim_C0_enough are introduced as section variables   *)
(* (Coq-shape-specific implicit-framework fillings; "let H_C ≅ H_AB" in tex).      *)

Section SmoothingSupportMaxHalf.
Variable (L : finType) (H : L -> chsType) (A B C0 : {set L}).
Hypothesis disAB : [disjoint A & B].
Hypothesis disAC : [disjoint A & C0].
Hypothesis disBC : [disjoint B & C0].
Hypothesis dim_C0_enough :
  (dim 'H[H]_A * dim 'H[H]_B <= dim 'H[H]_C0)%N.
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
Notation S_AB := (A :|: B).
Notation S_ABC := (A :|: B :|: C0).

(* path: entropy:smoothing_support_hmax -> entropy:smooth_iso_hmax -> *)
(*   entropy:entropy_data_proc -> *)
(*   bb84:bb84_secret *)
Lemma smoothing_support_hmax (eps : R) (rhoAB : 'F[H]_S_AB) :
  rhoAB \is denlf ->
  0 <= eps < Num.sqrt (@complex.Re R (\Tr rhoAB)) ->
  exists (tauAB : 'F[H]_S_AB),
    eps_ball eps rhoAB tauAB /\
    smooth_hmaxE B eps rhoAB = hmaxE B tauAB /\
    (supplf (ptrace_cast disAB rhoAB) \O supplf (ptrace_castl disAB rhoAB))
      \o tauAB = tauAB /\
    tauAB \o (supplf (ptrace_cast disAB rhoAB) \O supplf (ptrace_castl disAB rhoAB))
      = tauAB.
Proof.
  move=> Hrho_den Heps.
  have Prho : rhoAB \is psdlf := denlf_psd Hrho_den.
  have Htr : @complex.Re R (\Tr rhoAB) <= 1.
  { have Hreal : \Tr rhoAB \is Num.real := ger0_real (psdlf_trlf Prho).
    by move: (denlf_trlf Hrho_den); rewrite -(RRe_real Hreal) lecR. }
  pose rhoA := ptrace_cast disAB rhoAB.
  pose rhoB := ptrace_castl disAB rhoAB.
  pose PA := (supplf rhoA : 'F[H]_A).
  pose PB := (supplf rhoB : 'F[H]_B).
  pose P := (PA \O PB : 'F[H]_S_AB).
  have PrhoA : rhoA \is psdlf by exact: ptrace_cast_psdlf.
  have PrhoB : rhoB \is psdlf by exact: ptrace_castl_psdlf.
  have HrhoA_right : rhoA \o PA = rhoA by rewrite /PA; exact: suppvlf.
  have HrhoB_right : rhoB \o PB = rhoB by rewrite /PB; exact: suppvlf.
  have HrhoA_left : PA \o rhoA = rhoA.
  { have -> : PA = cosupplf rhoA.
    { rewrite /PA.
      have HrhoAh : rhoA^A = rhoA by exact: hermlf_adjE (psdlf_herm PrhoA).
      have HsupA : supplf rhoA^A = cosupplf rhoA by exact: supplf_adj rhoA.
      by rewrite HrhoAh in HsupA. }
    exact: cosupplfv. }
  have HrhoB_left : PB \o rhoB = rhoB.
  { have -> : PB = cosupplf rhoB.
    { rewrite /PB.
      have HrhoBh : rhoB^A = rhoB by exact: hermlf_adjE (psdlf_herm PrhoB).
      have HsupB : supplf rhoB^A = cosupplf rhoB by exact: supplf_adj rhoB.
      by rewrite HrhoBh in HsupB. }
    exact: cosupplfv. }
  (* extract optimal tau0 attaining smooth_hmax (prop:1129). *)
  have [tau0 [Htau0_ball Htau0_opt]] :=
    @smooth_hmax_attained R L H S_AB B eps rhoAB Prho Htr Heps.
    have Htau0_psd : tau0 \is psdlf.
      by move: Htau0_ball; move/eps_ball_psdlf.
    have Htau0_tr : @complex.Re R (\Tr tau0) <= 1.
      by move: Htau0_ball; move/eps_ball_trlf.
  (* define tauAB := P · tau0 · P (Tomamichel's projection step). *)
  pose tauAB := (P \o tau0 \o P : 'F[H]_S_AB).
  have PAproj : PA \is projlf by exact: supplf_proj.
  have PBproj : PB \is projlf by exact: supplf_proj.
  have HP_eq : P = (PA \⊗ PB : 'F[H]_S_AB).
  { apply: to_Fnd_inj.
    by rewrite /P (sdotFT _ _ disAB) to_Fnd_tenE. }
  have HPherm : P^A = P.
  { move: PAproj PBproj => /projlfP [HPAh _] /projlfP [HPBh _].
    by rewrite HP_eq tenf_adj HPAh HPBh -HP_eq. }
  have HPid : P \o P = P.
  { move: PAproj PBproj => /projlfP [_ HAid] /projlfP [_ HBid].
    apply: to_Fnd_inj.
    rewrite !to_Fnd_compE !(sdotFT _ _ disAB) -!to_Fnd_tenE -dotF_comp.
    by rewrite -tenf_comp ?HAid ?HBid. }
  have HPproj : P \is projlf by apply/projlfP; split.
  have HPbound : P \is bound1lf by exact: projlf_bound1 HPproj.
  (* support absorption — rhoAB sits inside supp(rhoA) ⊗ supp(rhoB). *)
  have HQAproj : (((PA \O (\1 : 'F[H]_B)) : 'F[H]_S_AB) \is projlf).
  { have HPA1_eq : (((PA \O (\1 : 'F[H]_B)) : 'F[H]_S_AB)) =
        (PA \⊗ (\1 : 'F[H]_B) : 'F[H]_S_AB).
    { apply: to_Fnd_inj.
      by rewrite (sdotFT _ _ disAB) to_Fnd_tenE. }
    move: PAproj => /projlfP [HPAh HAid].
    apply/projlfP; split.
    - by rewrite HPA1_eq tenf_adj HPAh adjf1 -HPA1_eq.
    - by rewrite HPA1_eq -tenf_comp ?HAid ?comp_lfun1l ?comp_lfun1r -?HPA1_eq. }
  have HQBproj : ((((\1 : 'F[H]_A) \O PB) : 'F[H]_S_AB) \is projlf).
  { have H1PB_eq : ((((\1 : 'F[H]_A) \O PB) : 'F[H]_S_AB)) =
        ((\1 : 'F[H]_A) \⊗ PB : 'F[H]_S_AB).
    { apply: to_Fnd_inj.
      by rewrite (sdotFT _ _ disAB) to_Fnd_tenE. }
    move: PBproj => /projlfP [HPBh HBid].
    apply/projlfP; split.
    - by rewrite H1PB_eq tenf_adj adjf1 HPBh -H1PB_eq.
    - by rewrite H1PB_eq -tenf_comp ?HBid ?comp_lfun1l ?comp_lfun1r -?H1PB_eq. }
  have HXB_psd : (((\1 : 'F[H]_A) \O rhoB : 'F[H]_S_AB) \is psdlf).
  { have -> : (((\1 : 'F[H]_A) \O rhoB : 'F[H]_S_AB)) =
        ((\1 : 'F[H]_A) \⊗ rhoB : 'F[H]_S_AB).
    { apply: to_Fnd_inj.
      by rewrite (sdotFT _ _ disAB) to_Fnd_tenE. }
    rewrite psdlfE.
    apply: tenf_ge0.
    - exact: disAB.
    - exact: lef01.
    - by move: PrhoB; rewrite psdlfE. }
  have HXA_psd : ((rhoA \⊗ (\1 : 'F[H]_B) : 'F[H]_S_AB) \is psdlf).
  { rewrite psdlfE.
    apply: tenf_ge0.
    - exact: disAB.
    - by move: PrhoA; rewrite psdlfE.
    - exact: lef01. }
  have proj_absorbL : forall (X Q : 'F[H]_S_AB),
      X \is hermlf -> Q \is projlf ->
      (supph X `<=` supph Q)%HS -> Q \o X = X.
  { move=> X Q HXh HQ /lehP HS.
    apply/lfunP=> u; rewrite lfunE /=.
    have HXmem : X u \in supph X.
    { have HXeq : X^A = X by exact: hermlf_adjE HXh.
      apply/memh_suppP.
      exists u.
      by rewrite HXeq. }
    have HXQ : X u \in supph Q by exact: HS _ HXmem.
    move/memhP: HXQ => HXQ.
    move: (supph_Pid (ProjLf_Build HQ)) => HQid.
    rewrite HQid in HXQ.
    exact: HXQ. }
  have proj_absorbR : forall (X Q : 'F[H]_S_AB),
      X \is hermlf -> Q \is projlf ->
      (supph X `<=` supph Q)%HS -> X \o Q = X.
  { move=> X Q HXh HQ HS.
    have HQeq : Q^A = Q by exact: hermlf_adjE (projlf_herm HQ).
    have HXeq : X^A = X by exact: hermlf_adjE HXh.
    have Hleft : Q \o X = X by exact: proj_absorbL HXh HQ HS.
    have HleftA : (Q \o X)^A = X^A by rewrite Hleft.
    rewrite adjf_comp HQeq HXeq in HleftA.
    exact: HleftA. }
  have supph_le_projR : forall (X Q : 'F[H]_S_AB),
      X \is psdlf -> Q \is projlf -> X \o Q = X ->
      (supph X `<=` supph Q)%HS.
  { move=> X Q PX HQ HXQ.
    have HQid : (supph Q)%:VF = Q by exact: supph_Pid (ProjLf_Build HQ).
    have Htr0 : \Tr ((PsdLf_Build PX : 'F[H]_S_AB)
                     \o (~` supph Q)%:VF) = 0.
    { rewrite hsE /= /cplmt HQid linearBr /= comp_lfun1r HXQ.
      by rewrite subrr linear0. }
    exact: supph_trlf0_le Htr0. }
  have Hsupp_B :
      (supph rhoAB `<=` supph (((\1 : 'F[H]_A) \O PB) : 'F[H]_S_AB))%HS.
  { have Hsupp_lift :
        (supph rhoAB `<=` supph (((\1 : 'F[H]_A) \O rhoB) : 'F[H]_S_AB))%HS.
      exact: ptrace_supph_lift.
    have HXB_right :
        (((\1 : 'F[H]_A) \O rhoB : 'F[H]_S_AB) \o
           (((\1 : 'F[H]_A) \O PB) : 'F[H]_S_AB)) =
        ((\1 : 'F[H]_A) \O rhoB : 'F[H]_S_AB).
    { rewrite sdotI_comp.
      by rewrite HrhoB_right. }
    have Hsupp_XB :
        (supph (((\1 : 'F[H]_A) \O rhoB : 'F[H]_S_AB))
           `<=` supph (((\1 : 'F[H]_A) \O PB) : 'F[H]_S_AB))%HS
      by exact: supph_le_projR HXB_psd HQBproj HXB_right.
    exact: le_trans Hsupp_lift Hsupp_XB. }
    have Hsupp_A :
        (supph rhoAB `<=` supph ((PA \O (\1 : 'F[H]_B)) : 'F[H]_S_AB))%HS.
  { have Hrho_le :
        rhoAB <= (dim 'H[H]_B)%:R *: (rhoA \⊗ (\1 : 'F[H]_B) : 'F[H]_S_AB)
      by exact: (@op_bound R L H A B disAB rhoAB Prho).
    have Hsupp_tensor :
        (supph rhoAB `<=` supph ((dim 'H[H]_B)%:R *:
          (rhoA \⊗ (\1 : 'F[H]_B) : 'F[H]_S_AB)))%HS
      by exact: (@supph_lef R _ (PsdLf_Build Prho) _ Hrho_le).
    have HXA_right :
        ((rhoA \⊗ (\1 : 'F[H]_B) : 'F[H]_S_AB) \o
           ((PA \O (\1 : 'F[H]_B)) : 'F[H]_S_AB)) =
        (rhoA \⊗ (\1 : 'F[H]_B) : 'F[H]_S_AB).
    { apply: to_Fnd_inj.
      rewrite !to_Fnd_compE !(sdotFT _ _ disAB) -!to_Fnd_tenE -dotF_comp.
      rewrite -tenf_comp ?comp_lfun1r ?comp_lfun1l //.
      by rewrite HrhoA_right. }
    have Hsupp_XA :
        (supph ((rhoA \⊗ (\1 : 'F[H]_B) : 'F[H]_S_AB))
           `<=` supph ((PA \O (\1 : 'F[H]_B)) : 'F[H]_S_AB))%HS
      by exact: supph_le_projR HXA_psd HQAproj HXA_right.
    have Hsupp_tensor' :
        (supph ((dim 'H[H]_B)%:R *:
          (rhoA \⊗ (\1 : 'F[H]_B) : 'F[H]_S_AB))
           `<=` supph ((rhoA \⊗ (\1 : 'F[H]_B) : 'F[H]_S_AB)))%HS
      by exact: supphZ_le.
    exact: le_trans Hsupp_tensor (le_trans Hsupp_tensor' Hsupp_XA). }
  have HrhoA_lift_left :
      ((PA \O (\1 : 'F[H]_B)) : 'F[H]_S_AB) \o rhoAB = rhoAB
    by exact: proj_absorbL (psdlf_herm Prho) HQAproj Hsupp_A.
  have HrhoB_lift_left :
      ((((\1 : 'F[H]_A) \O PB) : 'F[H]_S_AB) \o rhoAB) = rhoAB
    by exact: proj_absorbL (psdlf_herm Prho) HQBproj Hsupp_B.
  have HrhoA_lift_right :
      rhoAB \o ((PA \O (\1 : 'F[H]_B)) : 'F[H]_S_AB) = rhoAB
    by exact: proj_absorbR (psdlf_herm Prho) HQAproj Hsupp_A.
  have HrhoB_lift_right :
      rhoAB \o ((((\1 : 'F[H]_A) \O PB) : 'F[H]_S_AB)) = rhoAB
    by exact: proj_absorbR (psdlf_herm Prho) HQBproj Hsupp_B.
  have HPsplit :
      P =
      ((PA \O (\1 : 'F[H]_B)) : 'F[H]_S_AB) \o
      ((((\1 : 'F[H]_A) \O PB) : 'F[H]_S_AB)).
  { apply: to_Fnd_inj.
    rewrite /P !to_Fnd_compE !(sdotFT _ _ disAB) -!to_Fnd_tenE -dotF_comp.
    by rewrite -tenf_comp ?comp_lfun1l ?comp_lfun1r. }
  have Hrho_left : P \o rhoAB = rhoAB.
  { rewrite HPsplit -comp_lfunA HrhoB_lift_left.
    exact: HrhoA_lift_left. }
  have Hrho_right : rhoAB \o P = rhoAB.
  { rewrite HPsplit comp_lfunA HrhoA_lift_right.
    exact: HrhoB_lift_right. }
  have Hform_tau0 : (formso P) tau0 = tauAB.
    by rewrite formsoE HPherm /tauAB.
  have Hform_rho : (formso P) rhoAB = rhoAB.
    by rewrite formsoE HPherm -comp_lfunA Hrho_right Hrho_left.
  have HtauAB_psd : tauAB \is psdlf.
  { have Hform_psd : ((formso P) tau0) \is psdlf
      by exact: cp_psdP Htau0_psd.
    by rewrite Hform_tau0 in Hform_psd. }
  have HtauAB_tr : @complex.Re R (\Tr tauAB) <= 1.
  { have Htr_form : \Tr tauAB <= \Tr tau0.
    { have := qo_trlfE (formso (Bound1Lf_Build HPbound)) Htau0_psd.
      by rewrite formsoE HPherm /tauAB. }
    have HtauAB_real : \Tr tauAB \is Num.real
      by exact: ger0_real (psdlf_trlf HtauAB_psd).
    have Htau0_real : \Tr tau0 \is Num.real
      by exact: ger0_real (psdlf_trlf Htau0_psd).
    move: Htr_form.
    rewrite -(RRe_real HtauAB_real) -(RRe_real Htau0_real) lecR.
    move=> Htr_form.
    exact: le_trans Htr_form Htau0_tr. }
  (* tauAB satisfies eps_ball via pd_mono on (formso P). *)
  have HtauAB_ball : eps_ball eps rhoAB tauAB.
    { have HtauAB_pd : pur_dist tauAB rhoAB <= eps.
      { have Hform_cptn :
          (formso (Bound1Lf_Build HPbound) : 'SO('H_S_AB, 'H_S_AB)) \is cptn
          by exact: is_cptn.
        have [_ Hpd] :=
          pd_mono Hform_cptn Htau0_psd Prho Htau0_tr Htr.
        rewrite Hform_tau0 Hform_rho in Hpd.
        exact: le_trans Hpd (eps_ball_pur_dist Htau0_ball). }
      have HtauAB_pos : 0 < @complex.Re R (\Tr tauAB).
      {
        have Holdball :
            ((tauAB \is psdlf) &&
              (@complex.Re R (\Tr tauAB) <= 1)) &&
            (pur_dist tauAB rhoAB <= eps)
          by rewrite HtauAB_psd HtauAB_tr HtauAB_pd.
        exact: (eps_ball_trace_pos_from_small Prho Htr Heps Holdball).
      }
      apply/andP; split.
      - apply/andP; split.
        + by apply/andP; split.
        + exact: HtauAB_tr.
      - exact: HtauAB_pd. }
  (* support conjuncts (3, 4) — trivial from idempotency of P. *)
  have HPtau_left : P \o tauAB = tauAB
    by rewrite /tauAB !comp_lfunA HPid.
  have HPtau_right : tauAB \o P = tauAB
    by rewrite /tauAB -!comp_lfunA HPid.
  (* smooth_hmax = hmax tauAB.
     - LE direction (smooth_hmax <= hmax tauAB): tauAB ∈ ε-ball, infimum lb.
     - GE direction (hmax tauAB <= smooth_hmax = hmax tau0): Tomamichel's dual
       argument via fresh purifier C0 (section variables) + minmax_dual.
       Chain: hmax_B(tau0) = -hmin_C0(Tr_B tau0_ABC) where tau0_ABC is a
       rank<=1 purification on ABC0; tauABC := (PA⊗PB⊗1_C0) tau0_ABC sandwich
       has Tr_C0 tauABC = tauAB (via H2 ptrace_cast3B_formso_commute) and
       rank<=1, so hmax_B(tauAB) = -hmin_C0(Tr_B tauABC) by minmax_dual.
       Reduce to phi_min [C0] (Tr_B tauABC) <= phi_min [C0] (Tr_B tau0_ABC):
       (i) marginal Property vi via phi_min_data_proc_A with E=formso PA;
       (ii) marginal Property ii via phi_min_ii_mono + lm:pt-norm-bound for
       (1_A⊗PB⊗1_C0)·_·(1_A⊗PB⊗1_C0) sandwich. Edge cases handle tau0=0
       and tauABC=0. *)
  have HtauAB_hmax_le : hmax B tauAB <= hmax B tau0.
  { (* Tomamichel's dual route (Proposition 5.1, tex pr:smoothing/support):
       purify tau0 on ABC0, sandwich with P⊗1_C0, apply minmax_dual on both
       sides, reduce to phi_min monotonicity + data processing.
       Edge case tauAB=0 eliminated by pur_dist analysis. *)
    (* --- tauAB != 0 via pur_dist analysis. --- *)
    (* From pd_mono: pur_dist tauAB rhoAB <= eps.  If tauAB = 0 then
       pur_dist 0 rhoAB = sqrt(Tr rhoAB) > eps, contradiction. *)
    have HtauAB_ne0 : tauAB != 0.
    { apply/eqP=> HtauAB_eq0.
      have HtauAB_ball_pd : pur_dist tauAB rhoAB <= eps.
      { move: HtauAB_ball; rewrite /eps_ball => /andP [_ Hpd].
        exact: Hpd. }
      have Hpd0 : pur_dist (0 : 'F[H]_S_AB) rhoAB = Num.sqrt (@complex.Re R (\Tr rhoAB)).
      { have H0psd : h2mx (0 : 'F[H]_S_AB) \is psdmx
          by rewrite h2mx0; exact: psdmx0.
        have Hrho_psd : h2mx rhoAB \is psdmx
          by move: Prho; rewrite qualifE.
        have Hgfid0 :
            gfid (0 : 'F[H]_S_AB) rhoAB =
            Num.sqrt (1 - @complex.Re R (\Tr rhoAB)).
        { rewrite /gfid (alt_gfid_gen H0psd Hrho_psd).
          have -> :
              @complex.Re R
                (trnorm (sqrtmx (h2mx (0 : 'F[H]_S_AB)) *m sqrtmx (h2mx rhoAB))) = 0
            by rewrite h2mx0 sqrtmx0 mul0mx trnorm0 raddf0.
          have -> :
              @complex.Re R (1 - \tr (h2mx (0 : 'F[H]_S_AB))) = 1.
          { by rewrite h2mx0 mxtrace0 subr0. }
          have -> :
              @complex.Re R (1 - \tr (h2mx rhoAB)) =
              1 - @complex.Re R (\Tr rhoAB)
            by rewrite raddfB /=.
          by rewrite sqrtr1 mul1r add0r. }
        rewrite /pur_dist.
        pose a := 1 - @complex.Re R (\Tr rhoAB).
        have Ha_ge0 : 0 <= a
          by rewrite /a subr_ge0.
        have -> : (gfid (0 : 'F[H]_S_AB) rhoAB)^2 = a.
        { rewrite Hgfid0. exact: sqr_sqrtr Ha_ge0. }
        by rewrite /a opprB addrCA subrr addr0. }
      have : Num.sqrt (@complex.Re R (\Tr rhoAB)) <= eps.
      { by rewrite -Hpd0 -HtauAB_eq0 HtauAB_ball_pd. }
      have : eps < Num.sqrt (@complex.Re R (\Tr rhoAB)).
      { by case/andP: Heps. }
      by move=> Hlt Hle; have := le_lt_trans Hle Hlt; rewrite ltxx. }
    (* --- tau0 is denlf and nonzero. --- *)
    have Htau0_ne0 : tau0 != 0.
    { apply/eqP=> Htau0_eq0.
      move: HtauAB_ne0; rewrite /tauAB Htau0_eq0.
      by rewrite comp_lfun0r comp_lfun0l eqxx. }
    have Htau0_den : tau0 \is denlf.
    { apply/denlfP; split=> //.
      have Hreal : \Tr tau0 \is Num.real
        := ger0_real (psdlf_trlf Htau0_psd).
      by rewrite -(RRe_real Hreal) lecR. }
    (* --- purify tau0 to tau0_ABC. --- *)
    have disAB_C : [disjoint S_AB & C0]
      by rewrite disjointUX disAC disBC.
    have Hdim_AB_le :
        (dim 'H[H]_S_AB <= dim 'H[H]_C0)%N.
    { by rewrite (tenv_dim disAB). }
    have [tau0_ABC [Htau0ABC_den [Htau0ABC_rank1 Htau0ABC_marg_raw]]] :=
      @purification_exists_with_ancilla R L H A B C0 disAC disBC tau0
        Hdim_AB_le Htau0_den Htau0_ne0.
    (* Bridge proof-irrelevance: purification_exists_with_ancilla uses its own
       disAB_C, but minmax_dual/ptrace_cast3C use section disAC/disBC.
       Both prove [disjoint S_AB & C0]; bridge via eq_irrelevance. *)
    have ptrace_cast_irr : forall (d1 d2 : [disjoint S_AB & C0])
        (f : 'F[H]_S_ABC),
        ptrace_cast d1 f = ptrace_cast d2 f.
    { by move=> d1 d2 f; rewrite /ptrace_cast /ptrace_cast_gen
        (eq_irrelevance (setDU_r d1) (setDU_r d2)). }
    have Htau0ABC_marg : ptrace_cast disAB_C tau0_ABC = tau0.
    { rewrite (ptrace_cast_irr disAB_C (pur.disAB_C disAC disBC) tau0_ABC).
      exact: Htau0ABC_marg_raw. }
    (* ptrace_cast3C ↔ ptrace_cast bridge. *)
    have HptC_eq : forall (X : 'F[H]_S_ABC),
        @ptrace_cast3C R L H A B C0 disAC disBC X =
        ptrace_cast disAB_C X.
    { move=> X.
      rewrite /ptrace_cast3C /ptrace_cast /ptrace_cast_gen.
      have Hdu : setDU3_C disAC disBC = setDU_r disAB_C := eq_irrelevance _ _.
      by rewrite Hdu. }
    have Htau0ABC_marg_3C :
        ptrace_cast3C disAC disBC tau0_ABC = tau0
      by rewrite HptC_eq.
    have Htau0ABC_psd : tau0_ABC \is psdlf := denlf_psd Htau0ABC_den.
    have Htau0ABC_tr : @complex.Re R (\Tr tau0_ABC) <= 1.
    { have := denlf_trlf Htau0ABC_den.
      have Hreal : \Tr tau0_ABC \is Num.real
        := ger0_real (psdlf_trlf Htau0ABC_psd).
      by rewrite -(RRe_real Hreal) lecR. }
    (* tau0_ABC has rank exactly 1 (from rank <= 1 + nonzero). *)
    have Htau0ABC_ne0 : tau0_ABC != 0.
    { apply/eqP=> Heq0.
      have : ptrace_cast disAB_C tau0_ABC = 0
        by rewrite Heq0 /ptrace_cast /ptrace_cast_gen raddf0 /= raddf0.
      by rewrite Htau0ABC_marg => /eqP; rewrite (negPf Htau0_ne0). }
    have Htau0ABC_rank_eq1 : \Rank tau0_ABC = 1%N.
    { have Hgt0 : (0 < \Rank tau0_ABC)%N.
      { rewrite lt0n /lfrank mxrank_eq0.
        apply/eqP=> H0.
        have : tau0_ABC = 0 by apply/h2mx_inj; rewrite H0 h2mx0.
        by move/eqP; rewrite (negPf Htau0ABC_ne0). }
      by apply/anti_leq/andP; split. }
    have Hphi_pos_trace :
        forall (S T : {set L}) (x : 'F[H]_S),
        x \is psdlf -> @complex.Re R (\Tr x) <= 1 ->
        0 < @complex.Re R (\Tr x) -> 0 < phi_min T x.
    {
      move=> S T x Px Hx_tr Hx_tr_pos.
      have eqST : (S :\: T) :|: (S :&: T) = S
        by rewrite finset.setUC finset.setID.
      have disSplit : [disjoint (S :\: T) & (S :&: T)].
      { apply/disjointP=> z; rewrite !inE.
        by case: (z \in T); rewrite ?andbF ?andbT. }
      pose dT : R := (dim 'H[H]_(S :\: T))%:R.
      have HdT_pos : 0 < dT by rewrite /dT ltr0n dim_proper.
      rewrite /phi_min.
      apply: (@lt_le_trans _ _ ((@complex.Re R (\Tr x)) / dT)).
      - by apply: divr_gt0.
      - apply: lb_le_inf.
        + pose sigma1 : 'F[H]_(S :&: T) := \1.
          exists (@complex.Re R (\Tr sigma1)).
          rewrite /phi_min_feasible.
          exists sigma1; split.
          { by rewrite qualifE h2mx1; apply: psdmx1. }
          split; last by [].
          rewrite sdotf11 castlf1.
          have Hx_den : x \is denlf.
          { apply/denlfP; split=> //.
            have Hreal : \Tr x \is Num.real := ger0_real (psdlf_trlf Px).
            by rewrite -(RRe_real Hreal) lecR. }
          have Hx_le1 : x ⊑ (\1 : 'F[H]_S)
            := denf_le1 (DenLf_Build Hx_den).
          by move: Hx_le1; rewrite lefE.
        + move=> v [sigma [Psigma [Hfeas ->]]].
          have Htr_sigma_real :
              (\Tr sigma : C) = (@complex.Re R (\Tr sigma))%:C
            by rewrite RRe_real // ger0_real // psdlf_trlf.
          have Hx_tr_real : (\Tr x : C) = (@complex.Re R (\Tr x))%:C
            by rewrite RRe_real // ger0_real // psdlf_trlf.
          have Hx_leC :
              \Tr x <= (dim 'H[H]_(S :\: T))%:R * \Tr sigma.
          { have Hgap_nonneg := psdlf_trlf Hfeas.
            move: Hgap_nonneg.
            rewrite raddfB /= castlf_trlfE (trlf_lift_I disSplit).
            by rewrite subr_ge0. }
          move: Hx_leC; rewrite Hx_tr_real Htr_sigma_real.
          rewrite /dT -natrC -rmorphM /= lecR => Hx_leR.
          rewrite ler_pdivrMr //.
          by rewrite mulrC.
    }
    have Htau0_tr_pos_C : (0 : C) < \Tr tau0.
    { rewrite lt_def psdlf_trlf // andbT.
      apply/negP=> /eqP Htr0.
      apply/negP: Htau0_ne0; rewrite negbK.
      have Htau0_ge0 : 0 ⊑ tau0.
        by move: Htau0_psd; rewrite psdlfE.
      apply/trlf0_eq0.
      exact: (conj Htau0_ge0 Htr0). }
    have Htau0_tr_pos_R : 0 < @complex.Re R (\Tr tau0).
    { have Hreal : \Tr tau0 \is Num.real := ger0_real (psdlf_trlf Htau0_psd).
      by move: Htau0_tr_pos_C; rewrite -{1}(RRe_real Hreal) ltcR. }
    have Htau0AC_psd_dual :
        ptrace_cast3B disAB disBC tau0_ABC \is psdlf
      by exact: ptrace_cast_gen_psdlf.
    have Htau0AC_tr_eq_dual :
        \Tr (ptrace_cast3B disAB disBC tau0_ABC) = \Tr tau0_ABC.
    { rewrite /ptrace_cast3B /ptrace_cast_gen castlf_trlfE.
      have /cptpP [_ /tpmapP Htp] := @ptraceso_qc R L H B S_ABC.
      exact: Htp. }
    have Htau0ABC_tr_pos_C : (0 : C) < \Tr tau0_ABC.
    { rewrite lt_def psdlf_trlf // andbT.
      apply/negP=> /eqP Htr0.
      apply/negP: Htau0ABC_ne0; rewrite negbK.
      have Htau0ABC_ge0 : 0 ⊑ tau0_ABC.
        by move: Htau0ABC_psd; rewrite psdlfE.
      apply/trlf0_eq0.
      exact: (conj Htau0ABC_ge0 Htr0). }
    have Htau0AC_tr_pos_R :
        0 < @complex.Re R (\Tr (ptrace_cast3B disAB disBC tau0_ABC)).
    { rewrite Htau0AC_tr_eq_dual.
      have Hreal : \Tr tau0_ABC \is Num.real
        := ger0_real (psdlf_trlf Htau0ABC_psd).
      by move: Htau0ABC_tr_pos_C; rewrite -{1}(RRe_real Hreal) ltcR. }
    have Htau0AC_tr_le_R :
        @complex.Re R (\Tr (ptrace_cast3B disAB disBC tau0_ABC)) <= 1
      by rewrite Htau0AC_tr_eq_dual.
    have Hphi_tau0AC_pos_dual :
        0 < phi_min C0 (ptrace_cast3B disAB disBC tau0_ABC)
      := Hphi_pos_trace _ _ _ Htau0AC_psd_dual
           Htau0AC_tr_le_R Htau0AC_tr_pos_R.
    have Htau0_ptC_psd_dual :
        ptrace_cast3C disAC disBC tau0_ABC \is psdlf
      by exact: ptrace_cast_gen_psdlf.
    have Htau0_ptC_tr_le_dual :
        @complex.Re R (\Tr (ptrace_cast3C disAC disBC tau0_ABC)) <= 1
      by rewrite Htau0ABC_marg_3C.
    have Htau0_ptC_tr_pos_dual :
        0 < @complex.Re R (\Tr (ptrace_cast3C disAC disBC tau0_ABC))
      by rewrite Htau0ABC_marg_3C.
    have Htau0_hmaxE_fin :
        hmaxE B (ptrace_cast3C disAC disBC tau0_ABC) =
        (hmax B (ptrace_cast3C disAC disBC tau0_ABC))%:E
      := @hmaxE_EFin R L H (A :|: B) B
           (ptrace_cast3C disAC disBC tau0_ABC)
           Htau0_ptC_psd_dual Htau0_ptC_tr_le_dual
           Htau0_ptC_tr_pos_dual.
    have Htau0_hminE_fin :
        hminE C0 (ptrace_cast3B disAB disBC tau0_ABC) =
        (hmin C0 (ptrace_cast3B disAB disBC tau0_ABC))%:E
      := @hminE_EFin R L H (A :|: C0) C0
           (ptrace_cast3B disAB disBC tau0_ABC)
           Hphi_tau0AC_pos_dual.
    (* --- apply minmax_dual on tau0_ABC. --- *)
    (* hmax [B] tau0 = - hmin [C0] (ptrace_cast3B disAB disBC tau0_ABC) *)
    have Hdual_tau0 :
        hmax B (ptrace_cast3C disAC disBC tau0_ABC) =
        - hmin C0 (ptrace_cast3B disAB disBC tau0_ABC).
    { have HdualE := @minmax_dual R L H A B C0 disAB disAC disBC Cp Cpp
           disA_Cp disA_Cpp disB_Cp disB_Cpp disCp_Cpp
           dimA_Cp dimC_Cp_Cpp dimB_Cpp tau0_ABC Htau0ABC_den
           Htau0ABC_rank_eq1.
      move: HdualE.
      rewrite Htau0_hmaxE_fin Htau0_hminE_fin EFinN.
      by case. }
    rewrite Htau0ABC_marg_3C in Hdual_tau0.
    (* Now Hdual_tau0 : hmax [B] tau0 = - hmin [C0] (Tr_B tau0_ABC) *)
    rewrite Hdual_tau0.
    (* Goal: hmax [B] tauAB <= - hmin [C0] (ptrace_cast3B disAB disBC tau0_ABC) *)
    (* Suffices: hmax [B] tauAB = - hmin [C0] (Tr_B tauABC) for some tauABC
       with ptrace_cast3C tauABC = tauAB and rank 1, PLUS
       hmin [C0] (Tr_B tau0_ABC) <= hmin [C0] (Tr_B tauABC). *)
    (* --- define tauABC = Pi · tau0_ABC · Pi, Pi = P ⊗ 1_C0. --- *)
    pose Pi : 'F[H]_S_ABC := (P \O (\1 : 'F[H]_C0) : 'F[H]_S_ABC).
    pose tauABC := (Pi \o tau0_ABC \o Pi : 'F[H]_S_ABC).
    (* Pi is projlf and bound1lf. *)
    have HPi_eq : Pi = (P \⊗ (\1 : 'F[H]_C0) : 'F[H]_S_ABC).
    { apply: to_Fnd_inj.
      by rewrite /Pi (sdotFT _ _ disAB_C) to_Fnd_tenE. }
    have HPi_proj : Pi \is projlf.
    { move: HPproj => /projlfP [HPh HPidem].
      apply/projlfP; split.
      - by rewrite HPi_eq tenf_adj HPh adjf1 -HPi_eq.
      - by rewrite HPi_eq -tenf_comp ?HPidem ?comp_lfun1l -?HPi_eq. }
    have HPi_herm : Pi^A = Pi
      by exact: hermlf_adjE (projlf_herm HPi_proj).
    have HPi_idem : Pi \o Pi = Pi.
    { by move/projlfP: HPi_proj => []. }
    have HPi_bound1 : Pi \is bound1lf := projlf_bound1 HPi_proj.
    (* tauABC is psd, denlf, rank <= 1. *)
    have HtauABC_psd : tauABC \is psdlf.
    { have : (formso Pi) tau0_ABC \is psdlf
        by exact: cp_psdP Htau0ABC_psd.
      by rewrite formsoE HPi_herm /tauABC. }
    have HtauABC_tr : @complex.Re R (\Tr tauABC) <= 1.
    { have Htr_le : \Tr tauABC <= \Tr tau0_ABC.
      { have := qo_trlfE (formso (Bound1Lf_Build HPi_bound1)) Htau0ABC_psd.
        by rewrite formsoE HPi_herm /tauABC. }
      have Hreal_tauABC : \Tr tauABC \is Num.real
        := ger0_real (psdlf_trlf HtauABC_psd).
      have Hreal_tau0ABC : \Tr tau0_ABC \is Num.real
        := ger0_real (psdlf_trlf Htau0ABC_psd).
      move: Htr_le.
      rewrite -(RRe_real Hreal_tauABC) -(RRe_real Hreal_tau0ABC) lecR.
      move=> Hle; exact: (le_trans Hle Htau0ABC_tr). }
    have HtauABC_den : tauABC \is denlf.
    { apply/denlfP; split=> //.
      have Hreal : \Tr tauABC \is Num.real
        := ger0_real (psdlf_trlf HtauABC_psd).
      by rewrite -(RRe_real Hreal) lecR. }
    have HtauABC_rank_le1 : (\Rank tauABC <= 1)%N.
    { rewrite /tauABC /lfrank.
      have -> : h2mx (Pi \o tau0_ABC \o Pi) =
                h2mx Pi *m h2mx tau0_ABC *m h2mx Pi
        by rewrite !h2mx_comp.
      exact: leq_trans (mxrankM_maxl _ _)
               (leq_trans (mxrankM_maxr _ _)
                 Htau0ABC_rank1). }
    (* tauABC != 0 follows from tauAB != 0 via ptrace. *)
    have HtauABC_ne0 : tauABC != 0.
    { apply/eqP=> Heq0.
      have : ptrace_cast disAB_C tauABC = 0
        by rewrite Heq0 /ptrace_cast /ptrace_cast_gen raddf0 /= raddf0.
      rewrite /ptrace_cast /ptrace_cast_gen => Htr0.
      have HtauAB_eq0 : tauAB = 0.
      { (* tauAB = ptrace_cast3C tauABC = ptrace_cast disAB_C tauABC = 0.
           Need to show ptrace_cast3C tauABC = tauAB first. *)
        have HptC_tauABC :
            ptrace_cast disAB_C tauABC = tauAB.
        { rewrite /tauABC /ptrace_cast /ptrace_cast_gen.
          (* Pi = P ⊗ 1_C0, ptrace_C0 commutes with P-sandwich. *)
          have HPC_commute :
              castlf (setDU_r disAB_C, setDU_r disAB_C)
                (\Tr_(C0) (Pi \o tau0_ABC \o Pi)) =
              P \o (castlf (setDU_r disAB_C, setDU_r disAB_C)
                (\Tr_(C0) tau0_ABC)) \o P.
          { have Hcomm := @ptrace_cast3B_formso_commute R L H
              S_AB C0 disAB_C tau0_ABC P.
            rewrite /ptrace_cast /ptrace_cast_gen in Hcomm.
            rewrite -HPi_eq in Hcomm.
            rewrite Hcomm.
            done. }
          rewrite HPC_commute.
          have Hmarg :
              castlf (setDU_r disAB_C, setDU_r disAB_C)
                (\Tr_(C0) tau0_ABC) = tau0.
          { exact: Htau0ABC_marg. }
          by rewrite Hmarg. }
        by rewrite -HptC_tauABC /ptrace_cast /ptrace_cast_gen Htr0. }
      by move: HtauAB_ne0; rewrite HtauAB_eq0 eqxx. }
    have HtauABC_rank_eq1 : \Rank tauABC = 1%N.
    { have Hgt0 : (0 < \Rank tauABC)%N.
      { rewrite lt0n /lfrank mxrank_eq0.
        apply/eqP=> H0.
        have : tauABC = 0 by apply/h2mx_inj; rewrite H0 h2mx0.
        by move/eqP; rewrite (negPf HtauABC_ne0). }
      by apply/anti_leq/andP; split. }
    (* --- ptrace_cast3C tauABC = tauAB. --- *)
    have HtauABC_marg : ptrace_cast3C disAC disBC tauABC = tauAB.
    { rewrite HptC_eq.
      rewrite /tauABC /ptrace_cast /ptrace_cast_gen.
      have Hcomm := @ptrace_cast3B_formso_commute R L H
        S_AB C0 disAB_C tau0_ABC P.
      rewrite -HPi_eq /ptrace_cast /ptrace_cast_gen in Hcomm.
      rewrite Hcomm -/(ptrace_cast_gen _ tau0_ABC) -/(ptrace_cast disAB_C tau0_ABC).
      by rewrite Htau0ABC_marg. }
    have HtauABC_tr_pos_C : (0 : C) < \Tr tauABC.
    { rewrite lt_def psdlf_trlf // andbT.
      apply/negP=> /eqP Htr0.
      apply/negP: HtauABC_ne0; rewrite negbK.
      have HtauABC_ge0 : 0 ⊑ tauABC.
        by move: HtauABC_psd; rewrite psdlfE.
      apply/trlf0_eq0.
      exact: (conj HtauABC_ge0 Htr0). }
    have HtauABC_tr_pos_R : 0 < @complex.Re R (\Tr tauABC).
    { have Hreal : \Tr tauABC \is Num.real
        := ger0_real (psdlf_trlf HtauABC_psd).
      by move: HtauABC_tr_pos_C; rewrite -{1}(RRe_real Hreal) ltcR. }
    have HtauAC_psd_dual :
        ptrace_cast3B disAB disBC tauABC \is psdlf
      by exact: ptrace_cast_gen_psdlf.
    have HtauAC_tr_eq_dual :
        \Tr (ptrace_cast3B disAB disBC tauABC) = \Tr tauABC.
    { rewrite /ptrace_cast3B /ptrace_cast_gen castlf_trlfE.
      have /cptpP [_ /tpmapP Htp] := @ptraceso_qc R L H B S_ABC.
      exact: Htp. }
    have HtauAC_tr_pos_dual :
        0 < @complex.Re R (\Tr (ptrace_cast3B disAB disBC tauABC))
      by rewrite HtauAC_tr_eq_dual.
    have HtauAC_tr_le_dual :
        @complex.Re R (\Tr (ptrace_cast3B disAB disBC tauABC)) <= 1
      by rewrite HtauAC_tr_eq_dual.
    have Hphi_tauAC_pos_dual :
        0 < phi_min C0 (ptrace_cast3B disAB disBC tauABC)
      := Hphi_pos_trace _ _ _ HtauAC_psd_dual
           HtauAC_tr_le_dual HtauAC_tr_pos_dual.
    have Htau_ptC_psd_dual :
        ptrace_cast3C disAC disBC tauABC \is psdlf
      by exact: ptrace_cast_gen_psdlf.
    have Htau_ptC_tr_eq_dual :
        \Tr (ptrace_cast3C disAC disBC tauABC) = \Tr tauABC.
    { rewrite /ptrace_cast3C /ptrace_cast_gen castlf_trlfE.
      have /cptpP [_ /tpmapP Htp] := @ptraceso_qc R L H C0 S_ABC.
      exact: Htp. }
    have Htau_ptC_tr_le_dual :
        @complex.Re R (\Tr (ptrace_cast3C disAC disBC tauABC)) <= 1
      by rewrite Htau_ptC_tr_eq_dual.
    have Htau_ptC_tr_pos_dual :
        0 < @complex.Re R (\Tr (ptrace_cast3C disAC disBC tauABC))
      by rewrite Htau_ptC_tr_eq_dual.
    have Htau_hmaxE_fin :
        hmaxE B (ptrace_cast3C disAC disBC tauABC) =
        (hmax B (ptrace_cast3C disAC disBC tauABC))%:E
      := @hmaxE_EFin R L H (A :|: B) B
           (ptrace_cast3C disAC disBC tauABC)
           Htau_ptC_psd_dual Htau_ptC_tr_le_dual
           Htau_ptC_tr_pos_dual.
    have Htau_hminE_fin :
        hminE C0 (ptrace_cast3B disAB disBC tauABC) =
        (hmin C0 (ptrace_cast3B disAB disBC tauABC))%:E
      := @hminE_EFin R L H (A :|: C0) C0
           (ptrace_cast3B disAB disBC tauABC)
           Hphi_tauAC_pos_dual.
    (* --- apply minmax_dual on tauABC. --- *)
    have Hdual_tauABC :
        hmax B (ptrace_cast3C disAC disBC tauABC) =
        - hmin C0 (ptrace_cast3B disAB disBC tauABC).
    { have HdualE := @minmax_dual R L H A B C0 disAB disAC disBC Cp Cpp
           disA_Cp disA_Cpp disB_Cp disB_Cpp disCp_Cpp
           dimA_Cp dimC_Cp_Cpp dimB_Cpp tauABC HtauABC_den
           HtauABC_rank_eq1.
      move: HdualE.
      rewrite Htau_hmaxE_fin Htau_hminE_fin EFinN.
      by case. }
    rewrite HtauABC_marg in Hdual_tauABC.
    (* Now Hdual_tauABC : hmax [B] tauAB = - hmin [C0] (Tr_B tauABC). *)
    rewrite Hdual_tauABC.
    (* Goal: - hmin [C0] (Tr_B tauABC) <= - hmin [C0] (Tr_B tau0_ABC)
       i.e.: hmin [C0] (Tr_B tau0_ABC) <= hmin [C0] (Tr_B tauABC)
       i.e.: phi_min [C0] (Tr_B tauABC) <= phi_min [C0] (Tr_B tau0_ABC). *)
    rewrite lerNl opprK.
    (* Goal: hmin [C0] (Tr_B tau0_ABC) <= hmin [C0] (Tr_B tauABC). *)
    rewrite /hmin.
    rewrite lerN2.
    (* Goal: log2 (phi_min [C0] (Tr_B tauABC)) <=
             log2 (phi_min [C0] (Tr_B tau0_ABC)). *)
    (* Positivity for log2 monotonicity. *)
    have HtauAC_psd_local : ptrace_cast3B disAB disBC tauABC \is psdlf
      by exact: ptrace_cast_gen_psdlf.
    have HtauAC_tr_eq : \Tr (ptrace_cast3B disAB disBC tauABC) = \Tr tauABC.
    { rewrite /ptrace_cast3B /ptrace_cast_gen castlf_trlfE.
      have /cptpP [_ /tpmapP Htp] := @ptraceso_qc R L H B S_ABC.
      exact: Htp. }
    have HtauABC_tr_pos : (0 : C) < \Tr tauABC.
    { rewrite lt_def psdlf_trlf // andbT.
      apply/negP => /eqP Htr0.
      apply/negP: HtauABC_ne0; rewrite negbK.
      have HtauABC_ge0 : 0 ⊑ tauABC.
        by move: HtauABC_psd; rewrite psdlfE.
      apply/trlf0_eq0.
      exact: (conj HtauABC_ge0 Htr0). }
    have HtauAC_tr_pos_R :
        0 < @complex.Re R (\Tr (ptrace_cast3B disAB disBC tauABC)).
    { rewrite HtauAC_tr_eq.
      have Hreal2 : \Tr tauABC \is Num.real
        := ger0_real (psdlf_trlf HtauABC_psd).
      by move: HtauABC_tr_pos; rewrite -{1}(RRe_real Hreal2) ltcR. }
    have HtauAC_tr_le1_R :
        @complex.Re R (\Tr (ptrace_cast3B disAB disBC tauABC)) <= 1.
    { by rewrite HtauAC_tr_eq. }
    have Hphi_tauAC_pos : 0 < phi_min C0 (ptrace_cast3B disAB disBC tauABC).
    { (* phi_min T x > 0 for non-zero psd x (class.v pattern). *)
      set tauAC_local := ptrace_cast3B disAB disBC tauABC.
      have HtauAC_den : tauAC_local \is denlf.
      { apply/denlfP; split=> //.
        have Hreal : \Tr tauAC_local \is Num.real
          := ger0_real (psdlf_trlf HtauAC_psd_local).
        by rewrite -(RRe_real Hreal) lecR. }
      have eqST_gen : ((A :|: C0) :\: C0) :|:
                       ((A :|: C0) :&: C0) =
                       (A :|: C0)
        by rewrite finset.setUC finset.setID.
      have disSplit_gen :
          [disjoint (A :|: C0) :\: C0 &
                    (A :|: C0) :&: C0]
        := disjointDI _ _.
      pose dT : R := (dim 'H[H]_((A :|: C0) :\: C0))%:R.
      have HdT_pos : 0 < dT by rewrite /dT ltr0n dim_proper.
      rewrite /phi_min -/tauAC_local.
      apply: (@lt_le_trans _ _ ((@complex.Re R (\Tr tauAC_local)) / dT)).
      - by apply: divr_gt0.
      - apply: lb_le_inf.
        + pose sigma1 : 'F[H]_((A :|: C0) :&: C0) := \1.
          exists (@complex.Re R (\Tr sigma1)).
          rewrite /phi_min_feasible.
          exists sigma1; split.
          { by rewrite qualifE h2mx1; apply: psdmx1. }
          split; last by [].
          rewrite sdotf11 castlf1.
          have Htau_le1 : tauAC_local ⊑ (\1 : 'F[H]_(A :|: C0)).
          { exact: denf_le1 (DenLf_Build HtauAC_den). }
          by move: Htau_le1; rewrite lefE.
        + move=> v [sigma [Psigma [Hfeas ->]]].
          have Htr_sigma_real :
              (\Tr sigma : C) = (@complex.Re R (\Tr sigma))%:C
            by rewrite RRe_real // ger0_real // psdlf_trlf.
          have Htau_leC : \Tr tauAC_local <= dT%:C * \Tr sigma.
          { have Hle : tauAC_local ⊑ castlf (eqST_gen, eqST_gen)
                ((\1 : 'F_((A :|: C0) :\: C0)) \O sigma).
            { move: Hfeas; rewrite lefE => Hle.
              have Hle2 : (castlf (eqST_gen, eqST_gen)
                ((\1 : 'F_((A :|: C0) :\: C0)) \O sigma)
                - tauAC_local) \is psdlf.
              { move: Hle; congr (_ \is psdlf); congr (_ - _).
                by congr (castlf (_, _) _); exact: eq_irrelevance. }
              by rewrite -lefE in Hle2. }
            apply: (le_trans (lef_trlf Hle)).
            have -> : \Tr (castlf (eqST_gen, eqST_gen)
              ((\1 : 'F_((A :|: C0) :\: C0)) \O sigma))
              = dT%:C * \Tr sigma.
            { by rewrite castlf_trlfE (trlf_lift_I disSplit_gen) /dT natrC. }
            by []. }
          have Htau_tr_real : (\Tr tauAC_local : C) = (@complex.Re R (\Tr tauAC_local))%:C.
          { rewrite RRe_real //.
            exact: ger0_real (psdlf_trlf HtauAC_psd_local). }
          move: Htau_leC.
          rewrite Htau_tr_real Htr_sigma_real -rmorphM /= lecR.
          rewrite ler_pdivrMr //.
          by rewrite mulrC. }
    apply: log2_le_pos Hphi_tauAC_pos _.
    (* Goal: phi_min [C0] (Tr_B tauABC) <= phi_min [C0] (Tr_B tau0_ABC). *)
    (* --- phi_min chain. --- *)
    (* Decompose tauABC = (PA⊗1_B⊗1_C0) · ((1_A⊗PB⊗1_C0) · tau0_ABC · (1_A⊗PB⊗1_C0)) · (PA⊗1_B⊗1_C0).
       phi_min_data_proc_A with E = formso PA on the A-register.
       phi_min_ii_mono with Tr_B(PB-sandwich) <= Tr_B. *)
    (* phi_min [C0] tauAC <= phi_min [C0] tau0_AC
       via data processing (formso PA on A) + monotonicity (PB on B). *)
    (* The chain uses two facts:
       (i) the PA-step: the A-component is handled via formso PA through
           the two-step decomposition (Pi = (PA x PB) x 1_C0, and the
           B-component PB does not commute trivially with Tr_B).
       (ii) For the PB-step: Tr_B(PB_full·X·PB_full) <= Tr_B(X) via pt-norm-bound.

       For the PA-step: Tr_B(PA_full·X·PA_full) = PA·(Tr_B X)·PA, then
       phi_min_data_proc_A gives phi_min [C0] (PA·Y·PA) <= phi_min [C0] Y.

       Combined: phi_min [C0] tauAC
         = phi_min [C0] (Tr_B tauABC)
         = phi_min [C0] (PA · Tr_B(PB_full · tau0_ABC · PB_full) · PA)
           [by ptrace_cast3B_formso_commute for the PA part]
         <= phi_min [C0] (Tr_B(PB_full · tau0_ABC · PB_full))
           [by phi_min_data_proc_A with E = formso PA]
         <= phi_min [C0] (Tr_B tau0_ABC) = phi_min [C0] tau0_AC.
           [by phi_min_ii_mono + pt-norm-bound] *)
    (* Establish the key intermediate:
       ptrace_cast3B tauABC = (formso PA :⊗ \:1_C0) applied to
       ptrace_cast3B of the PB-sandwiched tau0_ABC. Then chain. *)
    (* Define the PB-sandwiched intermediate. *)
    pose PB_full : 'F[H]_S_ABC :=
      (((\1 : 'F[H]_A) \O PB) \O (\1 : 'F[H]_C0)
        : 'F[H]_S_ABC).
    pose PA_full : 'F[H]_S_ABC :=
      ((PA \O (\1 : 'F[H]_B)) \O (\1 : 'F[H]_C0)
        : 'F[H]_S_ABC).
    pose midABC := (PB_full \o tau0_ABC \o PB_full : 'F[H]_S_ABC).
    (* tauABC = PA_full · midABC · PA_full. *)
    have HPA_full_eq : PA_full = (PA \⊗ (\1 : 'F[H]_B)) \⊗ (\1 : 'F[H]_C0).
    { apply: to_Fnd_inj.
      rewrite /PA_full !(sdotFT _ _ disAB_C) !(sdotFT _ _ disAB).
      by rewrite !to_Fnd_tenE. }
    have HPB_full_eq0 : PB_full = ((\1 : 'F[H]_A) \⊗ PB) \⊗ (\1 : 'F[H]_C0).
    { apply: to_Fnd_inj.
      rewrite /PB_full !(sdotFT _ _ disAB_C) !(sdotFT _ _ disAB).
      by rewrite !to_Fnd_tenE. }
    have HPi_split : Pi = PA_full \o PB_full.
    { rewrite HPi_eq HPA_full_eq HPB_full_eq0.
      have disBA : [disjoint B & A] by rewrite disjoint_sym.
      rewrite -tenf_comp; last exact: disAB_C.
      rewrite comp_lfun1l.
      congr (_ \⊗ _).
      rewrite -tenf_comp; last exact: disAB.
      by rewrite comp_lfun1r comp_lfun1l. }
    have HPAfull_PBfull_commute : PA_full \o PB_full = PB_full \o PA_full.
    { rewrite HPA_full_eq HPB_full_eq0.
      rewrite -tenf_comp; last exact: disAB_C.
      rewrite comp_lfun1l.
      rewrite -tenf_comp; last exact: disAB.
      rewrite comp_lfun1l comp_lfun1r.
      symmetry.
      rewrite -tenf_comp; last exact: disAB_C.
      rewrite comp_lfun1l.
      rewrite -tenf_comp; last exact: disAB.
      by rewrite comp_lfun1l comp_lfun1r. }
    have HtauABC_split : tauABC = PA_full \o midABC \o PA_full.
    { rewrite /tauABC /midABC HPi_split.
      (* LHS: (PA_full \o PB_full) \o tau0_ABC \o (PA_full \o PB_full)
         RHS: PA_full \o (PB_full \o tau0_ABC \o PB_full) \o PA_full *)
      (* Swap the rightmost (PA_full \o PB_full) to (PB_full \o PA_full) *)
      have -> : (PA_full \o PB_full) \o tau0_ABC \o (PA_full \o PB_full) =
                (PA_full \o PB_full) \o tau0_ABC \o (PB_full \o PA_full)
        by rewrite HPAfull_PBfull_commute.
      by rewrite !comp_lfunA. }
    (* midABC is psd. *)
    have HmidABC_psd : midABC \is psdlf.
    { have HPB_full_eq : PB_full = ((\1 : 'F[H]_A) \⊗ PB) \⊗ (\1 : 'F[H]_C0).
      { apply: to_Fnd_inj.
        rewrite /PB_full !(sdotFT _ _ disAB_C) !(sdotFT _ _ disAB).
        by rewrite !to_Fnd_tenE. }
      have HPBf_proj : PB_full \is projlf.
      { rewrite HPB_full_eq.
        apply/projlfP; split.
        - rewrite !tenf_adj adjf1 (hermlf_adjE (projlf_herm PBproj)) adjf1.
          by rewrite -HPB_full_eq.
        - rewrite -tenf_comp; last exact: disAB_C.
          rewrite comp_lfun1l.
          rewrite -tenf_comp; last exact: disAB.
          rewrite comp_lfun1l.
          by move/projlfP: PBproj => [_ ->]; rewrite -HPB_full_eq. }
      have HPBf_bound1 := projlf_bound1 HPBf_proj.
      have : (formso PB_full) tau0_ABC \is psdlf
        by exact: cp_psdP Htau0ABC_psd.
      by rewrite formsoE (hermlf_adjE (projlf_herm HPBf_proj)) /midABC. }
    (* Tr_B(PA_full · X · PA_full) = PA · (Tr_B X) · PA
       via ptrace_cast3B_formso_commute. *)
    (* We need: ptrace_cast3B disAB disBC (PA_full · X · PA_full) =
                PA · ptrace_cast3B disAB disBC X · PA.
       PA_full = (PA ⊗ 1_B) ⊗ 1_C0. The ptrace_cast3B traces B from ABC.
       Viewing ABC = (A∪C0) ∪ B (after regrouping), this is ptrace_cast
       with PA⊗1_C0 on the A∪C0 factor.
       Direct application of ptrace_cast3B_formso_commute requires
       regrouping the set association, which we handle via eq_irrelevance. *)
    (* For the overall phi_min inequality, use an indirect argument:
       tauABC = formso Pi tau0_ABC, and Pi = P ⊗ 1_C0.
       Then ptrace_cast3B tauABC and ptrace_cast3B tau0_ABC are on A∪C0.
       We show the phi_min inequality via the formso-composition approach. *)
    (* Since phi_min_data_proc_A applies
       to maps E : 'SO_(A, A'), and formso PA : 'SO_(A, A),
       we need Tr_B tauABC = (formso PA :⊗ \:1_C0)(Tr_B midABC).
       Then phi_min [C0] (Tr_B tauABC) <= phi_min [C0] (Tr_B midABC)
       by phi_min_data_proc_A.
       And phi_min [C0] (Tr_B midABC) <= phi_min [C0] (Tr_B tau0_ABC)
       by phi_min_ii_mono + operator-order bound on partial trace. *)
    (* Tr_B tauABC = (formso PA :⊗ \:1_C0)(Tr_B midABC). *)
    (* This requires ptrace_cast3B (PA_full · X · PA_full) =
       PA · ptrace_cast3B X · PA, which is the 3-register commutation. *)
    pose PAC : 'F[H]_(A :|: C0) :=
      (PA \O (\1 : 'F[H]_C0) : 'F[H]_(A :|: C0)).
    have HptB_PA_commute :
        ptrace_cast3B disAB disBC (PA_full \o midABC \o PA_full) =
        PAC \o ptrace_cast3B disAB disBC midABC \o PAC.
    { have HPAC_ten : PAC = PA \⊗ (\1 : 'F[H]_C0).
      { apply: to_Fnd_inj.
        by rewrite /PAC (sdotFT _ _ disAC) to_Fnd_tenE. }
      (* PA_full = (PA ⊗ 1_B) ⊗ 1_C, which matches the lemma's input form. *)
      have HPA_full_ten : PA_full =
          (PA \⊗ (\1 : 'F[H]_B)) \⊗ (\1 : 'F[H]_C0).
      { exact: HPA_full_eq. }
      rewrite HPA_full_ten HPAC_ten.
      exact: (ptrace_cast3B_formso_commute_AC disAB disBC disAC midABC PA). }
    (* ============================================================ *)
    (* Prove the full chain at once. *)
    (* phi_min [C0] tauAC <= phi_min [C0] tau0_AC where
       tauAC = ptrace_cast3B tauABC and tau0_AC = ptrace_cast3B tau0_ABC. *)
    (* Use the two-step chain:
       (1) tauAC = PA · mid_AC · PA (from ptrace commutation)
       (2) phi_min [C0] (PA · mid_AC · PA) <= phi_min [C0] mid_AC (phi_min_data_proc_A)
       (3) mid_AC <= tau0_AC (pt-norm-bound)
       (4) phi_min [C0] mid_AC <= phi_min [C0] tau0_AC (phi_min_ii_mono) *)
    (* For (3), the pt-norm-bound, proved via the decomposition:
       tau0_AC - mid_AC = Tr_B((1-PB_full) · tau0_ABC · (1-PB_full))  [cross terms = 0]
       which is psd. The cross terms vanish because PB_full has product structure. *)
    pose mid_AC := ptrace_cast3B disAB disBC midABC.
    pose tau0_AC := ptrace_cast3B disAB disBC tau0_ABC.
    have Htau0_AC_psd : tau0_AC \is psdlf
      by rewrite /tau0_AC; exact: ptrace_cast_gen_psdlf.
    have Hmid_AC_psd : mid_AC \is psdlf
      by rewrite /mid_AC; exact: ptrace_cast_gen_psdlf.
    (* pt-norm-bound at labelled level. *)
    have HPBf_proj : PB_full \is projlf.
    { have HPB_full_eq : PB_full =
          ((\1 : 'F[H]_A) \⊗ PB \⊗ (\1 : 'F[H]_C0)
            : 'F[H]_S_ABC).
      { apply: to_Fnd_inj.
        rewrite /PB_full !(sdotFT _ _ disAB_C) !(sdotFT _ _ disAB).
        by rewrite !to_Fnd_tenE. }
      rewrite HPB_full_eq; apply/projlfP; split.
      - by rewrite !tenf_adj adjf1 (hermlf_adjE (projlf_herm PBproj)) adjf1 -HPB_full_eq.
      - rewrite -tenf_comp; last exact: disAB_C.
        rewrite comp_lfun1l.
        rewrite -tenf_comp; last exact: disAB.
        rewrite comp_lfun1l.
        by move/projlfP: PBproj => [_ ->]; rewrite -HPB_full_eq. }
    have HPBf_herm : PB_full^A = PB_full
      := hermlf_adjE (projlf_herm HPBf_proj).
    have HPBf_idem : PB_full \o PB_full = PB_full
      by move/projlfP: HPBf_proj => [].
    (* tau0_AC - mid_AC = Tr_B((1-PB_full) · tau0_ABC · (1-PB_full)) *)
    have Hmid_AC_le_tau0_AC : mid_AC <= tau0_AC.
    { rewrite /mid_AC /tau0_AC /midABC HPB_full_eq0.
      exact: (ptrace_cast3B_B_proj_le disAB disBC disAC Htau0ABC_psd PBproj). }
    (* Step A: phi_min [C0] mid_AC <= phi_min [C0] tau0_AC via phi_min_ii_mono. *)
    have Hphi_step_B : phi_min C0 mid_AC <= phi_min C0 tau0_AC
      := @phi_min_ii_mono R L H (A :|: C0) C0 mid_AC tau0_AC
           Hmid_AC_psd Htau0_AC_psd Hmid_AC_le_tau0_AC.
    (* Step B: phi_min [C0] tauAC <= phi_min [C0] mid_AC via phi_min_data_proc_A. *)
    (* Need: tauAC = (formso PA :⊗ :1_C0)(mid_AC). *)
    pose tauAC := ptrace_cast3B disAB disBC tauABC.
    have HtauAC_eq : tauAC = PAC \o mid_AC \o PAC.
    { rewrite /tauAC /mid_AC HtauABC_split HptB_PA_commute. done. }
    (* Show (formso PA :⊗ :1_C0)(mid_AC) = PA · mid_AC · PA. *)
    have Hformso_PA_cp : (formso PA) \is cpmap := @formso_cp R _ _ PA.
    have Hformso_PA_dualtn : (formso PA)^*o \is tnmap.
    { (* (formso PA)^*o = formso (PA^A) = formso PA (since PA hermitian).
         formso PA \is tnmap is formso_tn. *)
      have HPA_herm : PA^A = PA
        := hermlf_adjE (projlf_herm PAproj).
      (* The dual of formso X is formso (X^A). *)
      have Hdual_eq : (formso PA)^*o = formso PA.
      { by rewrite dualso_formso HPA_herm. }
      rewrite Hdual_eq.
      exact: formso_tn. }
    (* Apply phi_min_data_proc_A:
       phi_min [C0] ((formso PA :⊗ :1_C0) mid_AC) <= phi_min [C0] mid_AC. *)
    have Hphi_step_A :
        phi_min C0 ((formso PA :⊗ (\:1 : 'SO[H]_C0)) mid_AC) <=
        phi_min C0 mid_AC.
    { exact: (@phi_min_data_proc_A R L H A A C0
        disAC disAC mid_AC (formso PA) Hmid_AC_psd
        Hformso_PA_cp Hformso_PA_dualtn). }
    (* Bridge: tauAC = (formso PA :⊗ :1_C0)(mid_AC). *)
    have HtauAC_eq2 :
        tauAC = (formso PA :⊗ (\:1 : 'SO[H]_C0)) mid_AC.
    { rewrite HtauAC_eq.
      have HPA_herm2 : PA^A = PA
        := hermlf_adjE (projlf_herm PAproj).
      have HPAC_eq : PAC = PA \⊗ (\1 : 'F[H]_C0).
      { apply: to_Fnd_inj.
        by rewrite /PAC (sdotFT _ _ disAC) to_Fnd_tenE. }
      symmetry.
      have -> : (formso PA :⊗ (\:1 : 'SO[H]_C0)) mid_AC =
                formso PAC mid_AC.
      { by rewrite HPAC_eq -formso1 -tenso_formso. }
      rewrite formsoE.
      have -> : PAC^A = PAC.
      { by rewrite HPAC_eq tenf_adj adjf1 (hermlf_adjE (projlf_herm PAproj)). }
      by []. }
    have Hphi_tauAC_le : phi_min C0 tauAC <= phi_min C0 tau0_AC.
    { rewrite HtauAC_eq2.
      exact: le_trans Hphi_step_A Hphi_step_B. }
    (* Chain: phi_min tauAC <= phi_min tau0_AC. *)
    exact: Hphi_tauAC_le. }
  have Hsmooth_le_tauAB : smooth_hmax B eps rhoAB <= hmax B tauAB
    by exact: smooth_hmax_lb Prho Htr Heps HtauAB_ball.
  have HtauAB_opt : smooth_hmax B eps rhoAB = hmax B tauAB.
  { apply/eqP; rewrite eq_le; apply/andP; split.
    - exact: Hsmooth_le_tauAB.
    - rewrite Htau0_opt; exact: HtauAB_hmax_le. }
  have HtauAB_lb :
      forall tau : 'F[H]_S_AB,
        eps_ball eps rhoAB tau -> hmax B tauAB <= hmax B tau.
  {
    move=> tau Htau.
    have Hsmooth_le_tau : smooth_hmax B eps rhoAB <= hmax B tau
      by exact: smooth_hmax_lb Prho Htr Heps Htau.
    rewrite Htau0_opt in Hsmooth_le_tau.
    exact: le_trans HtauAB_hmax_le Hsmooth_le_tau.
  }
  have HtauAB_optE : smooth_hmaxE B eps rhoAB = hmaxE B tauAB.
  {
    have HtauAB_pos : 0 < @complex.Re R (\Tr tauAB).
    { exact: eps_ball_trace_pos Prho Htr Heps HtauAB_ball. }
    apply/eqP; rewrite eq_le; apply/andP; split.
    - rewrite /smooth_hmaxE leeNl.
      apply: ereal_sup_ubound.
      by exists tauAB.
    - rewrite /smooth_hmaxE leeNr.
      apply: ge_ereal_sup => v [tau [Htau ->]].
      rewrite leeN2.
      have Htau_psd : tau \is psdlf := eps_ball_psdlf Htau.
      have Htau_tr : @complex.Re R (\Tr tau) <= 1 := eps_ball_trlf Htau.
      have Htau_pos : 0 < @complex.Re R (\Tr tau).
      { exact: eps_ball_trace_pos Prho Htr Heps Htau. }
      rewrite (@hmaxE_EFin R L H S_AB B tauAB
        HtauAB_psd HtauAB_tr HtauAB_pos).
      rewrite (@hmaxE_EFin R L H S_AB B tau
        Htau_psd Htau_tr Htau_pos).
      by rewrite lee_fin; exact: HtauAB_lb.
  }
  exists tauAB.
  split; first exact: HtauAB_ball.
  split; first exact: HtauAB_optE.
  by split.
Qed.

End SmoothingSupportMaxHalf.

End FvqkdReal.
