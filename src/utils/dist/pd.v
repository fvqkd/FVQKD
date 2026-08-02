(* -------------------------------------------------------------------- *)
(* pd.v — Purified distance P(ρ,τ) and metric properties                *)
(* -------------------------------------------------------------------- *)
(* Module: utils.dist.pd                                  *)
(* Paper: Tomamichel, 'A Framework for Non-Asymptotic Quantum           *)
(*   Information Theory' (PhD thesis, arXiv:1203.2142), Chapter 3        *)
(*   (The Purified Distance).                                            *)
(* TeX labels (closure members): th:pd-mono (Thm 3.4), th:pd-uhl        *)
(*   (Thm 3.5), co:pd-ext (Cor 3.6)                                     *)
(* Other labels (df:pd = Def 3.3, pr:pd-metric = Prop 3.2,             *)
(*   pr:pd-gtd-bounds = Prop 3.3, lm:pd-proj = Lem 3.8,                 *)
(*   lm:pd-ext-constr = Lem 3.7) are either definitional or            *)
(*   Qed-helpers of the closure members; kept per Qed-helper rule.      *)
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
  cpo mxpred extnum ctopology svd mxnorm hspace inhabited.
From quantum.dirac Require Import hstensor.

Import Order.TTheory GRing.Theory Num.Theory Num.Def MxLownerOrder.
Import VectorInternalTheory.

(* --- FVQKD imports --- *)
From utils Require Import pur.
From utils.mx Require Import def prop.
From utils.labelled Require Import lift op sys.
From utils.dist Require Import fid.

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
(* Purified distance P(ρ,τ) = sqrt(1 - F̄(ρ,τ)²)                       *)
(* tex: df:pd — Tomamichel, 'A Framework for Non-Asymptotic Quantum    *)
(*   Information Theory' (PhD thesis, arXiv:1203.2142), Definition 3.3  *)
(* ================================================================== *)

Section PurDistSetDef.
Variables (L : finType) (HL : L -> chsType) (S : {set L}).

(* tex: df:pd — Tomamichel, 'A Framework for Non-Asymptotic Quantum    *)
(*   Information Theory' (PhD thesis, arXiv:1203.2142), Definition 3.3  *)
(* math: P(ρ,τ) := √(1 - F̄(ρ,τ)²)                                     *)
Definition pur_dist (rho tau : 'F[HL]_S) : R :=
  Num.sqrt (1 - (gfid rho tau)^2).

End PurDistSetDef.

Arguments pur_dist {L HL S} rho tau.

Section PurDistReflSet.
Variable (L : finType) (HL : L -> chsType) (S : {set L}).

(* Reflexivity of purified distance on sub-normalized PSD states. Direct       *)
(* consequence of gfid_refl_mx: gfidelity ρ ρ = 1 ⇒ 1 - 1² = 0.              *)
(* pur_dist_refl *)
(* infra: no tex label — fundamental & reusable (mathcomp-style) *)
(* consumer: pur_dist_refl is used downstream by the BB84 secrecy proof. *)
(* path: utils:pur_dist_refl -> bb84:privacy_amplification -> *)
(*   bb84:bb84_secret *)
Lemma pur_dist_refl (rho : 'F[HL]_S) :
  rho \is psdlf -> @complex.Re R (\Tr rho) <= 1 ->
  pur_dist rho rho = 0.
Proof.
  move=> Prho Htr.
  have Hgf : gfid rho rho = 1.
  {
    have Hrho_mx_den : h2mx rho \is denmx.
    { apply: denmx_psd_re_tr_le; first by move: Prho; rewrite qualifE.
      exact: Htr. }
    rewrite /gfid.
    exact: gfid_refl_mx Hrho_mx_den.
  }
  rewrite /pur_dist Hgf.
  by rewrite exp1rz subrr sqrtr0.
Qed.

End PurDistReflSet.

Section PurDistFacts.
Variables (Ltri : finType) (HLtri : Ltri -> chsType) (Stri : {set Ltri}).

(* tex: pr:pd-metric — Tomamichel, 'A Framework for Non-Asymptotic      *)
(*   Quantum Information Theory' (PhD thesis, arXiv:1203.2142),          *)
(*   Proposition 3.2                                                     *)
(* math: P(ρ,τ) ≤ P(ρ,σ) + P(σ,τ)  (triangle inequality)              *)
(* path: utils:pd_metric_triangle -> lhl:cq_smoothing -> *)
(*   bb84:privacy_amplification -> bb84:bb84_secret *)
Lemma pd_metric_triangle (rho tau sigma : 'F[HLtri]_Stri) :
  rho \is psdlf -> tau \is psdlf -> sigma \is psdlf ->
  @complex.Re R (\Tr rho) <= 1 ->
  @complex.Re R (\Tr tau) <= 1 ->
  @complex.Re R (\Tr sigma) <= 1 ->
  pur_dist rho tau <= pur_dist rho sigma + pur_dist sigma tau.
Proof.
  move=> Prho Ptau Psigma Hrho_tr Htau_tr Hsigma_tr.
  pose pdmx := fun n (X Y : 'M[C]_n) =>
    Num.sqrt (1 - (gfidelity X Y) ^+ 2).
  (* TeX route, pure core: angular-distance triangle on rank-one
     normalized purifications, proved here as the one-consumer local block. *)
  have Hpure_triangle :
      forall (n : nat) (rho0 sigma0 tau0 : 'M[C]_n),
        rho0 \is den1mx ->
        sigma0 \is den1mx ->
        tau0 \is den1mx ->
        \rank rho0 = 1%N ->
        \rank sigma0 = 1%N ->
        \rank tau0 = 1%N ->
        pdmx n rho0 tau0 <= pdmx n rho0 sigma0 + pdmx n sigma0 tau0.
  {
    move=> n rho0 sigma0 tau0 Hrho0 Hsigma0 Htau0
      Hrho0_rank Hsigma0_rank Htau0_rank.
    have [u Hu] := @rank1_form R n rho0 Hrho0 Hrho0_rank.
    have [v Hv] := @rank1_form R n sigma0 Hsigma0 Hsigma0_rank.
    have [w Hw] := @rank1_form R n tau0 Htau0 Htau0_rank.
    have /den1mxP [Hrho0_psd /eqP Hrho0_tr1] := Hrho0.
    have /den1mxP [Hsigma0_psd /eqP Hsigma0_tr1] := Hsigma0.
    have /den1mxP [Htau0_psd /eqP Htau0_tr1] := Htau0.
    pose aC : C := (u^*t *m v) 0 0.
    pose bC : C := (v^*t *m w) 0 0.
    pose gC : C := (u^*t *m w) 0 0.
    pose a : R := @complex.Re R `|aC|.
    pose b : R := @complex.Re R `|bC|.
    pose g : R := @complex.Re R `|gC|.
    pose r : R := Num.sqrt (1 - a ^+ 2).
    pose s : R := Num.sqrt (1 - b ^+ 2).
    pose ru := u - aC^* *: v.
    pose rw := w - bC *: v.
    have HaC_real : `|aC| \is Num.real by exact: normr_real _.
    have HbC_real : `|bC| \is Num.real by exact: normr_real _.
    have HgC_real : `|gC| \is Num.real by exact: normr_real _.
    have HaC_eq : `|aC| = a%:C.
    { rewrite /a. exact: esym (RRe_real HaC_real). }
    have HbC_eq : `|bC| = b%:C.
    { rewrite /b. exact: esym (RRe_real HbC_real). }
    have HgC_eq : `|gC| = g%:C.
    { rewrite /g. exact: esym (RRe_real HgC_real). }
    have Hfid_a :
        @complex.Re R (trnorm (sqrtmx rho0 *m sqrtmx sigma0)) = a.
    { rewrite Hu Hv fid_gram_general_mx (schnorm11 1) /a /aC.
      done. }
    have Hfid_b :
        @complex.Re R (trnorm (sqrtmx sigma0 *m sqrtmx tau0)) = b.
    { rewrite Hv Hw fid_gram_general_mx (schnorm11 1) /b /bC.
      done. }
    have Hfid_g :
        @complex.Re R (trnorm (sqrtmx rho0 *m sqrtmx tau0)) = g.
    { rewrite Hu Hw fid_gram_general_mx (schnorm11 1) /g /gC.
      done. }
    have Hsigma0_tr_le : @complex.Re R (\tr sigma0) <= 1
      by rewrite Hsigma0_tr1 re_realid lexx.
    have Htau0_tr_le : @complex.Re R (\tr tau0) <= 1
      by rewrite Htau0_tr1 re_realid lexx.
    have Hgf_a : gfidelity rho0 sigma0 = a.
    {
      rewrite (gfid_eq_fid_tr1_mx
        Hrho0_psd Hsigma0_psd Hrho0_tr1 Hsigma0_tr_le).
      exact: Hfid_a.
    }
    have Hgf_b : gfidelity sigma0 tau0 = b.
    {
      rewrite (gfid_eq_fid_tr1_mx
        Hsigma0_psd Htau0_psd Hsigma0_tr1 Htau0_tr_le).
      exact: Hfid_b.
    }
    have Hgf_g : gfidelity rho0 tau0 = g.
    {
      rewrite (gfid_eq_fid_tr1_mx
        Hrho0_psd Htau0_psd Hrho0_tr1 Htau0_tr_le).
      exact: Hfid_g.
    }
    have Hpur_a : pdmx n rho0 sigma0 = r by rewrite /pdmx Hgf_a /r.
    have Hpur_b : pdmx n sigma0 tau0 = s by rewrite /pdmx Hgf_b /s.
    have Hpur_g : pdmx n rho0 tau0 = Num.sqrt (1 - g ^+ 2).
    { rewrite /pdmx.
      rewrite Hgf_g.
      reflexivity. }
    have Htr_uu : \tr (u^*t *m u) = 1.
    { by rewrite (mxtrace_mulC (u^*t) u) -Hu Hrho0_tr1. }
    have Htr_vv : \tr (v^*t *m v) = 1.
    { by rewrite (mxtrace_mulC (v^*t) v) -Hv Hsigma0_tr1. }
    have Htr_ww : \tr (w^*t *m w) = 1.
    { by rewrite (mxtrace_mulC (w^*t) w) -Hw Htau0_tr1. }
    have Hu_norm : l2normC u = 1.
    { by rewrite l2normC_dot -Hu Hrho0_tr1 sqrtC1. }
    have Hv_norm : l2normC v = 1.
    { by rewrite l2normC_dot -Hv Hsigma0_tr1 sqrtC1. }
    have Hw_norm : l2normC w = 1.
    { by rewrite l2normC_dot -Hw Htau0_tr1 sqrtC1. }
    have Htr_uv : \tr (u^*t *m v) = aC.
    { by rewrite trace_mx11 /aC. }
    have Htr_vu : \tr (v^*t *m u) = aC^*.
    { rewrite -{1}[v^*t *m u]adjmxK adjmxM !adjmxK mxtrace_adj Htr_uv.
      done. }
    have Htr_vw : \tr (v^*t *m w) = bC.
    { by rewrite trace_mx11 /bC. }
    have Htr_wv : \tr (w^*t *m v) = bC^*.
    { rewrite -{1}[w^*t *m v]adjmxK adjmxM !adjmxK mxtrace_adj Htr_vw.
      done. }
    have Htr_uw : \tr (u^*t *m w) = gC.
    { by rewrite trace_mx11 /gC. }
    have Ha_sqC : aC^* * aC = (a ^+ 2)%:C.
    { by rewrite -normCKC HaC_eq -rmorphXn. }
    have Ha_sqC' : aC * aC^* = (a ^+ 2)%:C.
    { by rewrite mulrC Ha_sqC. }
    have Hb_sqC : bC^* * bC = (b ^+ 2)%:C.
    { by rewrite -normCKC HbC_eq -rmorphXn. }
    have Hb_sqC' : bC * bC^* = (b ^+ 2)%:C.
    { by rewrite mulrC Hb_sqC. }
    have Ha_ge0 : 0 <= a.
    { by move: (normr_ge0 aC); rewrite HaC_eq lecR. }
    have Hb_ge0 : 0 <= b.
    { by move: (normr_ge0 bC); rewrite HbC_eq lecR. }
    have Hg_ge0 : 0 <= g.
    { by move: (normr_ge0 gC); rewrite HgC_eq lecR. }
    have Ha_le1 : a <= 1.
    { move: (@l2normC_cauchy C n (u^*t) v).
      rewrite Htr_uv l2normC_adjmx Hu_norm Hv_norm mul1r HaC_eq.
      by rewrite lecR. }
    have Hb_le1 : b <= 1.
    { move: (@l2normC_cauchy C n (v^*t) w).
      rewrite Htr_vw l2normC_adjmx Hv_norm Hw_norm mul1r HbC_eq.
      by rewrite lecR. }
    have Hg_le1 : g <= 1.
    { move: (@l2normC_cauchy C n (u^*t) w).
      rewrite Htr_uw l2normC_adjmx Hu_norm Hw_norm mul1r HgC_eq.
      by rewrite lecR. }
    have H1ma_ge0 : 0 <= 1 - a ^+ 2.
    { rewrite subr_ge0.
      exact: (exprn_ile1 2 Ha_ge0 Ha_le1). }
    have H1mb_ge0 : 0 <= 1 - b ^+ 2.
    { rewrite subr_ge0.
      exact: (exprn_ile1 2 Hb_ge0 Hb_le1). }
    have Hru_adj : ru^*t = u^*t - aC *: v^*t.
    { apply/matrixP=> i j.
      have -> : i = ord0 by apply: ord1.
      rewrite /ru !mxE rmorphB /= rmorphM /= conjCK.
      done. }
    have Hrw_adj : rw^*t = w^*t - bC^* *: v^*t.
    { apply/matrixP=> i j.
      have -> : i = ord0 by apply: ord1.
      rewrite /rw !mxE rmorphB /= rmorphM /=.
      done. }
    have Htr_u_av : \tr (u^*t *m (aC^* *: v)) = (a ^+ 2)%:C.
    { rewrite -scalemxAr linearZ /= Htr_uv.
      exact: Ha_sqC. }
    have Htr_av_u : \tr ((aC *: v^*t) *m u) = (a ^+ 2)%:C.
    { rewrite -scalemxAl linearZ /= Htr_vu.
      exact: Ha_sqC'. }
    have Htr_av_av : \tr ((aC *: v^*t) *m (aC^* *: v)) = (a ^+ 2)%:C.
    { rewrite -scalemxAl -scalemxAr !linearZ /= Htr_vv.
      rewrite mulrA mulr1.
      exact: Ha_sqC'. }
    have Htr_w_bv : \tr (w^*t *m (bC *: v)) = (b ^+ 2)%:C.
    { rewrite -scalemxAr linearZ /= Htr_wv.
      exact: Hb_sqC'. }
    have Htr_bv_w : \tr ((bC^* *: v^*t) *m w) = (b ^+ 2)%:C.
    { rewrite -scalemxAl linearZ /= Htr_vw.
      exact: Hb_sqC. }
    have Htr_bv_bv : \tr ((bC^* *: v^*t) *m (bC *: v)) = (b ^+ 2)%:C.
    { rewrite -scalemxAl -scalemxAr !linearZ /= Htr_vv.
      rewrite mulrA mulr1.
      exact: Hb_sqC. }
    have Htr_u_bv : \tr (u^*t *m (bC *: v)) = aC * bC.
    { rewrite -scalemxAr linearZ /= Htr_uv.
      by rewrite mulrC. }
    have Htr_av_w : \tr ((aC *: v^*t) *m w) = aC * bC.
    { rewrite -scalemxAl linearZ /= Htr_vw.
      done. }
    have Htr_av_bv : \tr ((aC *: v^*t) *m (bC *: v)) = aC * bC.
    { rewrite -scalemxAl -scalemxAr !linearZ /= Htr_vv.
      by rewrite mulrA mulr1. }
    have Htr_u_ru : \tr (u^*t *m ru) = (1 - a ^+ 2)%:C.
    { rewrite /ru mulmxBr linearB /= Htr_uu Htr_u_av.
      by rewrite rmorphB // rmorph1. }
    have Htr_av_ru : \tr ((aC *: v^*t) *m ru) = 0.
    { rewrite /ru mulmxBr linearB /= Htr_av_u Htr_av_av subrr.
      done. }
    have Htr_w_rw : \tr (w^*t *m rw) = (1 - b ^+ 2)%:C.
    { rewrite /rw mulmxBr linearB /= Htr_ww Htr_w_bv.
      by rewrite rmorphB // rmorph1. }
    have Htr_bv_rw : \tr ((bC^* *: v^*t) *m rw) = 0.
    { rewrite /rw mulmxBr linearB /= Htr_bv_w Htr_bv_bv subrr.
      done. }
    have Htr_ru : \tr (ru^*t *m ru) = (1 - a ^+ 2)%:C.
    { rewrite Hru_adj mulmxBl linearB /= Htr_u_ru Htr_av_ru.
      by rewrite subr0. }
    have Htr_rw : \tr (rw^*t *m rw) = (1 - b ^+ 2)%:C.
    { rewrite Hrw_adj mulmxBl linearB /= Htr_w_rw Htr_bv_rw.
      by rewrite subr0. }
    have Hr_sqC : (r%:C) ^+ 2 = (1 - a ^+ 2)%:C.
    { by rewrite -rmorphXn /= /r sqr_sqrtr. }
    have Hs_sqC : (s%:C) ^+ 2 = (1 - b ^+ 2)%:C.
    { by rewrite -rmorphXn /= /s sqr_sqrtr. }
    have Hru_sq_eq : l2normC ru ^+ 2 = (r%:C) ^+ 2.
    { by rewrite -[l2normC ru ^+ 2]dotV_l2normC Htr_ru Hr_sqC. }
    have Hrw_sq_eq : l2normC rw ^+ 2 = (s%:C) ^+ 2.
    { by rewrite -[l2normC rw ^+ 2]dotV_l2normC Htr_rw Hs_sqC. }
    have Hru_norm : l2normC ru = r%:C.
    { apply/eqP.
      rewrite -(@eqrXn2 _ 2) //.
      - by rewrite Hru_sq_eq eqxx.
      - by rewrite lecR /r sqrtr_ge0. }
    have Hrw_norm : l2normC rw = s%:C.
    { apply/eqP.
      rewrite -(@eqrXn2 _ 2) //.
      - by rewrite Hrw_sq_eq eqxx.
      - by rewrite lecR /s sqrtr_ge0. }
    have Htr_u_rw : \tr (u^*t *m rw) = gC - aC * bC.
    { rewrite /rw mulmxBr linearB /= Htr_uw Htr_u_bv.
      by rewrite mulrC. }
    have Htr_av_rw : \tr ((aC *: v^*t) *m rw) = 0.
    { rewrite /rw mulmxBr linearB /= Htr_av_w Htr_av_bv subrr.
      done. }
    have Hg_decomp : gC = aC * bC + \tr (ru^*t *m rw).
    { rewrite Hru_adj mulmxBl linearB /= Htr_u_rw Htr_av_rw subr0.
      by rewrite addrC subrK. }
    have Hcorr_leC : `| \tr (ru^*t *m rw) | <= l2normC (ru^*t) * l2normC rw.
    { exact: l2normC_cauchy. }
    have Hcorr_real : `| \tr (ru^*t *m rw) | \is Num.real by exact: normr_real _.
    have Hcorr_le : @complex.Re R `| \tr (ru^*t *m rw) | <= r * s.
    { move: Hcorr_leC.
      rewrite l2normC_adjmx Hru_norm Hrw_norm -rmorphM /=.
      by rewrite -(RRe_real Hcorr_real) -lecR. }
    have HabC_eq : `| aC * bC | = (a * b)%:C.
    { by rewrite normrM HaC_eq HbC_eq -rmorphM. }
    have Hab_le_corr : a * b <= g + @complex.Re R `| \tr (ru^*t *m rw) |.
    { have Hnorm_step :
          `| aC * bC | <= `| gC | + `| \tr (ru^*t *m rw) |.
      { have -> : aC * bC = gC + - \tr (ru^*t *m rw).
        { rewrite Hg_decomp.
          by rewrite -addrA addrN addr0. }
        apply: (le_trans (ler_normD gC (- \tr (ru^*t *m rw)))).
        by rewrite normrN. }
      move: Hnorm_step.
      rewrite HabC_eq HgC_eq -(RRe_real Hcorr_real) -rmorphD /=.
      by rewrite -lecR. }
    have Hab_le_grs : a * b <= g + r * s.
    { apply: (le_trans Hab_le_corr).
      by rewrite lerD2l. }
    have Hab_minus_le_g : a * b - r * s <= g.
    { have Htmp := Hab_le_grs.
      rewrite -[a * b](subrK (r * s)) in Htmp.
      move: Htmp.
      by rewrite lerD2r. }
    have Hr_ge0 : 0 <= r by rewrite /r sqrtr_ge0.
    have Hs_ge0 : 0 <= s by rewrite /s sqrtr_ge0.
    have Hrs_ge0 : 0 <= r * s := mulr_ge0 Hr_ge0 Hs_ge0.
    have Hsum_ge0 : 0 <= r + s := addr_ge0 Hr_ge0 Hs_ge0.
    have Hab_ge0 : 0 <= a * b := mulr_ge0 Ha_ge0 Hb_ge0.
    have Hr_sq : r ^+ 2 = 1 - a ^+ 2.
    { by rewrite /r sqr_sqrtr. }
    have Hs_sq : s ^+ 2 = 1 - b ^+ 2.
    { by rewrite /s sqr_sqrtr. }
    have Hab_le1 : a * b <= 1.
    { apply: (le_trans (ler_pM Ha_ge0 Hb_ge0 Ha_le1 Hb_le1)).
      by rewrite mulr1. }
    have Hsq_goal : 1 - g ^+ 2 <= (r + s) ^+ 2.
    { case: (lerP (a * b) (r * s)) => Hab_cmp.
      - have Hab_small : a * b <= r * s := Hab_cmp.
        have Hab_small_sq : (a * b) ^+ 2 <= (r * s) ^+ 2.
        { have Hstep1 : (a * b) ^+ 2 <= (r * s) * (a * b).
          { have -> : (a * b) ^+ 2 = (a * b) * (a * b).
            { rewrite expr2.
              done. }
            apply: ler_wpM2r.
            - exact: Hab_ge0.
            - exact: Hab_small. }
          have Hstep2 : (r * s) * (a * b) <= (r * s) ^+ 2.
          { have -> : (r * s) ^+ 2 = (r * s) * (r * s).
            { rewrite expr2.
              done. }
            apply: ler_wpM2l.
            - exact: Hrs_ge0.
            - exact: Hab_small. }
          exact: le_trans Hstep1 Hstep2. }
        have Hsum_aux : 0 <= 1 - a ^+ 2 - b ^+ 2.
        { move: Hab_small_sq.
          rewrite !exprMn Hr_sq Hs_sq.
          have -> : (1 - a ^+ 2) * (1 - b ^+ 2) =
              1 - a ^+ 2 - b ^+ 2 + a ^+ 2 * b ^+ 2.
          { rewrite -addrA.
            have -> : -(b ^+ 2) + a ^+ 2 * b ^+ 2 =
                - ((1 - a ^+ 2) * b ^+ 2).
            { rewrite addrC -opprB.
              have <- : (1 - a ^+ 2) * b ^+ 2 =
                  b ^+ 2 - a ^+ 2 * b ^+ 2.
              { rewrite mulrBl mul1r.
                done. }
              done. }
            have <- : (1 - a ^+ 2) * (1 - b ^+ 2) =
                (1 - a ^+ 2) - (1 - a ^+ 2) * b ^+ 2.
            { rewrite mulrBr mulr1.
              done. }
            done. }
          move=> Htmp.
          have Hshift := lerB (lexx (1 - a ^+ 2 - b ^+ 2 + a ^+ 2 * b ^+ 2)) Htmp.
          rewrite subrr in Hshift.
          have Hcancel :
              (1 - a ^+ 2 - b ^+ 2 + a ^+ 2 * b ^+ 2) - a ^+ 2 * b ^+ 2 =
              1 - a ^+ 2 - b ^+ 2.
          { apply: (addIr (a ^+ 2 * b ^+ 2)).
            rewrite subrK.
            done. }
          rewrite Hcancel in Hshift.
          exact: Hshift. }
        have Hsum_le1 : a ^+ 2 + b ^+ 2 <= 1.
        { rewrite -subr_ge0.
          have -> : 1 - (a ^+ 2 + b ^+ 2) = 1 - a ^+ 2 - b ^+ 2.
          { rewrite opprD -addrA.
            done. }
          exact: Hsum_aux. }
        have Hrs_sq_ge1 : 1 <= (r + s) ^+ 2.
        { have Hbase : 1 <= r ^+ 2 + s ^+ 2.
          { rewrite -subr_ge0 Hr_sq Hs_sq.
            have -> :
                ((1 - a ^+ 2) + (1 - b ^+ 2)) - 1 =
                1 - (a ^+ 2 + b ^+ 2).
            { apply: (addIr 1).
              rewrite subrK opprD.
              rewrite -!addrA [-(b ^+ 2) + 1]addrC.
              done. }
            by rewrite subr_ge0. }
          have Hlift : r ^+ 2 + s ^+ 2 <= (r + s) ^+ 2.
          { have Hr_part : r ^+ 2 <= (r + s) * r.
            { rewrite expr2.
              apply: ler_wpM2r.
              - exact: Hr_ge0.
              - by rewrite lerDl. }
            have Hs_part : s ^+ 2 <= (r + s) * s.
            { rewrite expr2.
              apply: ler_wpM2r.
              - exact: Hs_ge0.
              - rewrite [r + s]addrC.
                by rewrite lerDl. }
            have -> : (r + s) ^+ 2 = (r + s) * (r + s).
            { rewrite expr2.
              done. }
            rewrite mulrDr.
            exact: (lerD Hr_part Hs_part). }
          exact: le_trans Hbase Hlift. }
        have Hleft : 1 - g ^+ 2 <= 1.
        { have Hgg_ge0 : 0 <= g ^+ 2.
          { exact: exprn_ge0. }
          have Htmp := lerB (lexx 1) Hgg_ge0.
          rewrite subr0 in Htmp.
          exact: Htmp. }
        exact: le_trans Hleft Hrs_sq_ge1.
      - have Hab_big : r * s < a * b := Hab_cmp.
        have Hab_big_ge0 : 0 <= a * b - r * s.
        { rewrite subr_ge0.
          exact: ltW Hab_big. }
        have Hsq_le : (a * b - r * s) ^+ 2 <= g ^+ 2.
        { rewrite (ler_sqr Hab_big_ge0 Hg_ge0).
          exact: Hab_minus_le_g. }
        have Hmid : 1 - g ^+ 2 <= 1 - (a * b - r * s) ^+ 2.
        { exact: (lerB (lexx 1) Hsq_le). }
        have Hpoly : 1 - (a * b - r * s) ^+ 2 <= (r + s) ^+ 2.
        { have Hsq_ab : (a * b) ^+ 2 = a ^+ 2 * b ^+ 2.
          { rewrite exprMn.
            done. }
          have Hsq_rs : (r * s) ^+ 2 = r ^+ 2 * s ^+ 2.
          { rewrite exprMn.
            done. }
          have Hprod_expand : (1 - a ^+ 2) * (1 - b ^+ 2) =
              1 - a ^+ 2 - b ^+ 2 + a ^+ 2 * b ^+ 2.
          { rewrite -addrA.
            have -> : -(b ^+ 2) + a ^+ 2 * b ^+ 2 =
                - ((1 - a ^+ 2) * b ^+ 2).
            { rewrite addrC -opprB.
              have <- : (1 - a ^+ 2) * b ^+ 2 =
                  b ^+ 2 - a ^+ 2 * b ^+ 2.
              { rewrite mulrBl mul1r.
                done. }
              done. }
            have <- : (1 - a ^+ 2) * (1 - b ^+ 2) =
                (1 - a ^+ 2) - (1 - a ^+ 2) * b ^+ 2.
            { rewrite mulrBr mulr1.
              done. }
            done. }
          have Hcore :
              r ^+ 2 + s ^+ 2 + (a * b) ^+ 2 - 1 = (r * s) ^+ 2.
          { rewrite Hsq_ab Hsq_rs Hr_sq Hs_sq Hprod_expand.
            have -> :
                (1 - a ^+ 2) + (1 - b ^+ 2) + a ^+ 2 * b ^+ 2 - 1 =
                1 - a ^+ 2 - b ^+ 2 + a ^+ 2 * b ^+ 2.
            { apply: (addIr 1).
              rewrite subrK -!addrA.
              have -> : a ^+ 2 * b ^+ 2 + 1 =
                  1 + a ^+ 2 * b ^+ 2.
              { rewrite addrC.
                done. }
              have -> : -(b ^+ 2) + (1 + a ^+ 2 * b ^+ 2) =
                  1 + (-(b ^+ 2) + a ^+ 2 * b ^+ 2).
              { rewrite addrA.
                have -> : -(b ^+ 2) + 1 = 1 - b ^+ 2.
                { rewrite addrC.
                  done. }
                rewrite addrA.
                done. }
              done. }
            done. }
          have Habrs_le_rs : (a * b) * (r * s) <= r * s.
          { have Hgap_ge0 : 0 <= (1 - a * b) * (r * s).
            { apply: mulr_ge0.
              - rewrite subr_ge0.
                exact: Hab_le1.
              - exact: Hrs_ge0. }
            rewrite -subr_ge0.
            have -> : r * s - (a * b) * (r * s) = (1 - a * b) * (r * s).
            { rewrite mulrBl mul1r.
              done. }
            exact: Hgap_ge0. }
          have Hlin_le :
              ((a * b) * (r * s) + (a * b) * (r * s)) - (r * s) ^+ 2 <=
              r * s + r * s.
          { have Hrs_sq_ge0 : 0 <= (r * s) ^+ 2.
            { exact: exprn_ge0. }
            have Hdrop :=
                lerB (lexx ((a * b) * (r * s) + (a * b) * (r * s))) Hrs_sq_ge0.
            rewrite subr0 in Hdrop.
            exact: (le_trans Hdrop (lerD Habrs_le_rs Habrs_le_rs)). }
          pose cross := ((a * b) * (r * s) + (a * b) * (r * s)).
          have Hlin_neg : - (r * s + r * s) <= - cross + (r * s) ^+ 2.
          { have Htmp : - (r * s + r * s) <= - (cross - (r * s) ^+ 2).
            { rewrite lerN2.
              exact: Hlin_le. }
            have -> : - cross + (r * s) ^+ 2 = (r * s) ^+ 2 - cross.
            { rewrite addrC.
              done. }
            have -> : (r * s) ^+ 2 - cross = - (cross - (r * s) ^+ 2).
            { rewrite opprB.
              done. }
            exact: Htmp. }
          have Hsq_lower :
              (a * b) ^+ 2 - (r * s + r * s) <= (a * b - r * s) ^+ 2.
          { have Hsq_expand :
                (a * b - r * s) ^+ 2 =
                (a * b) ^+ 2 - cross + (r * s) ^+ 2.
            { rewrite sqrrB /cross.
              rewrite opprD -!addrA.
              done. }
            rewrite Hsq_expand.
            rewrite -!addrA.
            rewrite lerD2l.
            exact: Hlin_neg. }
          have Hmain_le :
              1 - (a * b - r * s) ^+ 2 <=
              1 - (a * b) ^+ 2 + (r * s + r * s).
          { have Htmp := lerB (lexx 1) Hsq_lower.
            have Hrhs :
                1 - ((a * b) ^+ 2 - (r * s + r * s)) =
                1 - (a * b) ^+ 2 + (r * s + r * s).
            { have -> :
                  1 - ((a * b) ^+ 2 - (r * s + r * s)) =
                  1 + ((r * s + r * s) - (a * b) ^+ 2).
              { rewrite opprB.
                done. }
              have -> :
                  1 + ((r * s + r * s) - (a * b) ^+ 2) =
                  1 + (r * s + r * s) - (a * b) ^+ 2.
              { rewrite addrA.
                done. }
              have -> :
                  1 + (r * s + r * s) - (a * b) ^+ 2 =
                  1 + - (a * b) ^+ 2 + (r * s + r * s).
              { rewrite addrAC.
                done. }
              done. }
            rewrite -Hrhs.
            exact: Htmp. }
          have Hone_ab_le :
              1 - (a * b) ^+ 2 <= r ^+ 2 + s ^+ 2.
          { have Hcore_ge0 : 0 <= r ^+ 2 + s ^+ 2 + (a * b) ^+ 2 - 1.
            { rewrite Hcore.
              exact: exprn_ge0. }
            rewrite -subr_ge0.
            have -> :
                (r ^+ 2 + s ^+ 2) - (1 - (a * b) ^+ 2) =
                r ^+ 2 + s ^+ 2 + (a * b) ^+ 2 - 1.
            { have -> :
                  (r ^+ 2 + s ^+ 2) - (1 - (a * b) ^+ 2) =
                  r ^+ 2 + s ^+ 2 + ((a * b) ^+ 2 - 1).
              { rewrite opprB.
                done. }
              rewrite addrA.
              done. }
            exact: Hcore_ge0. }
          apply: (le_trans Hmain_le).
          have -> : (r + s) ^+ 2 = r ^+ 2 + s ^+ 2 + (r * s + r * s).
          { rewrite sqrrD.
            rewrite mulr2n.
            have -> :
                r ^+ 2 + (r * s + r * s) + s ^+ 2 =
                r ^+ 2 + s ^+ 2 + (r * s + r * s).
            { rewrite -addrA.
              have -> : (r * s + r * s) + s ^+ 2 =
                  s ^+ 2 + (r * s + r * s).
              { rewrite addrC.
                done. }
              rewrite addrA.
              done. }
            done. }
          exact: lerD Hone_ab_le (lexx _).
        }
        exact: le_trans Hmid Hpoly. }
    have Hsum_sqrt : Num.sqrt ((r + s) ^+ 2) = r + s.
    { by rewrite sqrtr_sqr ger0_norm. }
    have Hfinal : Num.sqrt (1 - g ^+ 2) <= r + s.
    { rewrite -Hsum_sqrt.
      exact: ler_wsqrtr. }
    by rewrite Hpur_g Hpur_a Hpur_b.
  }
  (* TeX route, Uhlmann lift: normalized states inherit the pure triangle
     by lifting all three endpoints to rank-one purifications. *)
  have Hden1_triangle :
      forall (n : nat) (rho0 sigma0 tau0 : 'M[C]_n),
        rho0 \is den1mx ->
        sigma0 \is den1mx ->
        tau0 \is den1mx ->
        pdmx n rho0 tau0 <= pdmx n rho0 sigma0 + pdmx n sigma0 tau0.
  {
    move=> n rho0 sigma0 tau0 Hrho0 Hsigma0 Htau0.
    have Hden1_tr1 :
        forall (m : nat) (X : 'M[C]_m), X \is den1mx -> \tr X = 1.
    {
      move=> m X /den1mxP [_ /eqP Htr].
      exact: Htr.
    }
    have Hrho0_den : rho0 \is denmx := den1mx_den Hrho0.
    have Hsigma0_den : sigma0 \is denmx := den1mx_den Hsigma0.
    have Htau0_den : tau0 \is denmx := den1mx_den Htau0.
    have Hrho0_psd : rho0 \is psdmx := denmx_psd Hrho0_den.
    have Hsigma0_psd : sigma0 \is psdmx := denmx_psd Hsigma0_den.
    have Htau0_psd : tau0 \is psdmx := denmx_psd Htau0_den.
    have Hrho0_nz : rho0 != 0.
    {
      apply/negP=> /eqP H0.
      have Htr1 : \tr rho0 = 1 by exact: Hden1_tr1 _ _ Hrho0.
      have H01 : (0 : C) = 1 by rewrite -Htr1 H0 mxtrace0.
      have H10 : (1 : C) = 0 by exact: esym H01.
      move: (@oner_neq0 C).
      by rewrite H10 eqxx.
    }
    have Hsigma0_nz : sigma0 != 0.
    {
      apply/negP=> /eqP H0.
      have Htr1 : \tr sigma0 = 1 by exact: Hden1_tr1 _ _ Hsigma0.
      have H01 : (0 : C) = 1 by rewrite -Htr1 H0 mxtrace0.
      have H10 : (1 : C) = 0 by exact: esym H01.
      move: (@oner_neq0 C).
      by rewrite H10 eqxx.
    }
    have Htau0_nz : tau0 != 0.
    {
      apply/negP=> /eqP H0.
      have Htr1 : \tr tau0 = 1 by exact: Hden1_tr1 _ _ Htau0.
      have H01 : (0 : C) = 1 by rewrite -Htr1 H0 mxtrace0.
      have H10 : (1 : C) = 0 by exact: esym H01.
      move: (@oner_neq0 C).
      by rewrite H10 eqxx.
    }
    have Hn_pos : (0 < n)%N.
    {
      have Hrank_pos : (0 < \rank rho0)%N.
        by rewrite lt0n mxrank_eq0.
      exact: (leq_trans Hrank_pos (rank_leq_row rho0)).
    }
    have Hrho0_rank : (\rank rho0 <= n)%N by exact: rank_leq_row.
    have Hsigma0_rank : (\rank sigma0 <= n)%N by exact: rank_leq_row.
    have Htau0_rank : (\rank tau0 <= n)%N by exact: rank_leq_row.
    have [r [Hr_den [Hr_rank Hptr_r]]] :=
      purification_exists_in_dim Hrho0_den Hrho0_nz Hrho0_rank.
    have Hr_den1 : r \is den1mx.
    {
      apply/den1mxP; split.
      - exact: denmx_psd Hr_den.
      - apply/eqP.
        rewrite tr_ptrace2 Hptr_r.
        exact: Hden1_tr1 _ _ Hrho0.
    }
    have [s [Hs_den [Hs_rank [Hptr_s Hrs_fid]]]] :=
      fid_iii_uhl_mx (den1mx_den Hr_den1) Hr_rank Hptr_r
        Hsigma0_den Hsigma0_nz Hsigma0_rank.
    have Hs_den1 : s \is den1mx.
    {
      apply/den1mxP; split.
      - exact: denmx_psd Hs_den.
      - apply/eqP.
        rewrite tr_ptrace2 Hptr_s.
        exact: Hden1_tr1 _ _ Hsigma0.
    }
    have [t [Ht_den [Ht_rank [Hptr_t Hst_fid]]]] :=
      fid_iii_uhl_mx (den1mx_den Hs_den1) Hs_rank Hptr_s
        Htau0_den Htau0_nz Htau0_rank.
    have Ht_den1 : t \is den1mx.
    {
      apply/den1mxP; split.
      - exact: denmx_psd Ht_den.
      - apply/eqP.
        rewrite tr_ptrace2 Hptr_t.
        exact: Hden1_tr1 _ _ Htau0.
    }
    have Hpdmx_ptrace2 :
        forall m k (X Y : 'M[C]_(m * k)),
          (0 < k)%N ->
          X \is psdmx -> Y \is psdmx ->
          pdmx m (ptrace2 X) (ptrace2 Y) <= pdmx (m * k) X Y.
    {
      move=> m k X Y Hk HX HY.
      have Hmono := gfid_ptr_mono_mx Hk HX HY.
      rewrite /pdmx.
      have Hgfid_ge0 := gfid_ge0_mx HX HY.
      have Hpt_X : ptrace2 X \is psdmx := ptrace2_psd HX.
      have Hpt_Y : ptrace2 Y \is psdmx := ptrace2_psd HY.
      have Hgfid_ge0' := gfid_ge0_mx Hpt_X Hpt_Y.
      apply: ler_wsqrtr.
      apply: lerB; first exact: lexx.
      rewrite ler_sqr ?nnegrE//.
    }
    have Hrt_ge : pdmx n rho0 tau0 <= pdmx (n * n) r t.
    {
      rewrite -Hptr_r -Hptr_t.
      exact: Hpdmx_ptrace2 Hn_pos (denmx_psd Hr_den) (denmx_psd Ht_den).
    }
    have Hpure : pdmx (n * n) r t <= pdmx (n * n) r s + pdmx (n * n) s t.
    {
      exact: Hpure_triangle Hr_den1 Hs_den1 Ht_den1 Hr_rank Hs_rank Ht_rank.
    }
    have Hrs_eq : pdmx (n * n) r s = pdmx n rho0 sigma0.
    {
      rewrite /pdmx.
      have Hr_psd : r \is psdmx := denmx_psd (den1mx_den Hr_den1).
      have Hs_psd : s \is psdmx := denmx_psd (den1mx_den Hs_den1).
      have Hr_tr1 : \tr r = 1 by exact: Hden1_tr1 _ _ Hr_den1.
      have Hrho0_tr1 : \tr rho0 = 1 by exact: Hden1_tr1 _ _ Hrho0.
      have Hs_tr_le : @complex.Re R (\tr s) <= 1
        by rewrite (Hden1_tr1 _ _ Hs_den1) re_realid lexx.
      have Hsigma0_tr_le : @complex.Re R (\tr sigma0) <= 1
        by rewrite (Hden1_tr1 _ _ Hsigma0) re_realid lexx.
      rewrite (gfid_eq_fid_tr1_mx
        Hr_psd Hs_psd Hr_tr1 Hs_tr_le).
      rewrite (gfid_eq_fid_tr1_mx
        Hrho0_psd Hsigma0_psd Hrho0_tr1 Hsigma0_tr_le).
      by rewrite Hrs_fid.
    }
    have Hst_eq : pdmx (n * n) s t = pdmx n sigma0 tau0.
    {
      rewrite /pdmx.
      have Hs_psd : s \is psdmx := denmx_psd (den1mx_den Hs_den1).
      have Ht_psd : t \is psdmx := denmx_psd (den1mx_den Ht_den1).
      have Hs_tr1 : \tr s = 1 by exact: Hden1_tr1 _ _ Hs_den1.
      have Hsigma0_tr1 : \tr sigma0 = 1 by exact: Hden1_tr1 _ _ Hsigma0.
      have Ht_tr_le : @complex.Re R (\tr t) <= 1
        by rewrite (Hden1_tr1 _ _ Ht_den1) re_realid lexx.
      have Htau0_tr_le : @complex.Re R (\tr tau0) <= 1
        by rewrite (Hden1_tr1 _ _ Htau0) re_realid lexx.
      rewrite (gfid_eq_fid_tr1_mx
        Hs_psd Ht_psd Hs_tr1 Ht_tr_le).
      rewrite (gfid_eq_fid_tr1_mx
        Hsigma0_psd Htau0_psd Hsigma0_tr1 Htau0_tr_le).
      by rewrite Hst_fid.
    }
    apply: (le_trans Hrt_ge).
    apply: (le_trans Hpure).
    by rewrite Hrs_eq Hst_eq.
  }
  (* TeX route, generalized fidelity extensions: embed subnormalized states
     into trace-one flag states, prove the normalized triangle there, then
     rewrite back through the definition of generalized fidelity. *)
  have Hmatrix_triangle :
      forall (n : nat) (rho0 tau0 sigma0 : 'M[C]_n),
        rho0 \is psdmx -> tau0 \is psdmx -> sigma0 \is psdmx ->
        @complex.Re R (\tr rho0) <= 1 ->
        @complex.Re R (\tr tau0) <= 1 ->
        @complex.Re R (\tr sigma0) <= 1 ->
        pdmx n rho0 tau0 <= pdmx n rho0 sigma0 + pdmx n sigma0 tau0.
  {
    move=> n rho0 tau0 sigma0 Hrho0 Htau0 Hsigma0
      Hrho0_tr Htau0_tr Hsigma0_tr.
    have Hrho0_den : rho0 \is denmx := denmx_psd_re_tr_le Hrho0 Hrho0_tr.
    have Htau0_den : tau0 \is denmx := denmx_psd_re_tr_le Htau0 Htau0_tr.
    have Hsigma0_den : sigma0 \is denmx :=
      denmx_psd_re_tr_le Hsigma0 Hsigma0_tr.
    pose rhoE := embed_subnorm rho0.
    pose tauE := embed_subnorm tau0.
    pose sigmaE := embed_subnorm sigma0.
    have HrhoE_psd : rhoE \is psdmx := embed_subnorm_psdmx Hrho0_den.
    have HtauE_psd : tauE \is psdmx := embed_subnorm_psdmx Htau0_den.
    have HsigmaE_psd : sigmaE \is psdmx := embed_subnorm_psdmx Hsigma0_den.
    have HrhoE_trR : @complex.Re R (\tr rhoE) = 1
      by rewrite /rhoE (embed_subnorm_tr_eq1 Hrho0_den).
    have HtauE_trR : @complex.Re R (\tr tauE) = 1
      by rewrite /tauE (embed_subnorm_tr_eq1 Htau0_den).
    have HsigmaE_trR : @complex.Re R (\tr sigmaE) = 1
      by rewrite /sigmaE (embed_subnorm_tr_eq1 Hsigma0_den).
    have HrhoE_tr1 : \tr rhoE = 1.
    {
      have Hreal : \tr rhoE \is Num.real
        by apply: ger0_real; exact: (psdmx_trace HrhoE_psd).
      by rewrite -(RRe_real Hreal) HrhoE_trR.
    }
    have HtauE_tr1 : \tr tauE = 1.
    {
      have Hreal : \tr tauE \is Num.real
        by apply: ger0_real; exact: (psdmx_trace HtauE_psd).
      by rewrite -(RRe_real Hreal) HtauE_trR.
    }
    have HsigmaE_tr1 : \tr sigmaE = 1.
    {
      have Hreal : \tr sigmaE \is Num.real
        by apply: ger0_real; exact: (psdmx_trace HsigmaE_psd).
      by rewrite -(RRe_real Hreal) HsigmaE_trR.
    }
    have HrhoE_den1 : rhoE \is den1mx.
    {
      apply/den1mxP; split.
      - exact: HrhoE_psd.
      - by apply/eqP; exact: HrhoE_tr1.
    }
    have HtauE_den1 : tauE \is den1mx.
    {
      apply/den1mxP; split.
      - exact: HtauE_psd.
      - by apply/eqP; exact: HtauE_tr1.
    }
    have HsigmaE_den1 : sigmaE \is den1mx.
    {
      apply/den1mxP; split.
      - exact: HsigmaE_psd.
      - by apply/eqP; exact: HsigmaE_tr1.
    }
    have Hembed_pd :
        forall (X Y : 'M[C]_n),
          X \is psdmx -> Y \is psdmx ->
          @complex.Re R (\tr X) <= 1 ->
          @complex.Re R (\tr Y) <= 1 ->
          pdmx n X Y = pdmx (n + 1) (embed_subnorm X) (embed_subnorm Y).
    {
      move=> X Y PX PY HX HY.
      have HX_den : X \is denmx := denmx_psd_re_tr_le PX HX.
      have HY_den : Y \is denmx := denmx_psd_re_tr_le PY HY.
      rewrite /pdmx.
      have PEX : embed_subnorm X \is psdmx := embed_subnorm_psdmx HX_den.
      have PEY : embed_subnorm Y \is psdmx := embed_subnorm_psdmx HY_den.
      have HtrEX_R : @complex.Re R (\tr (embed_subnorm X)) = 1
        by rewrite (embed_subnorm_tr_eq1 HX_den).
      have HtrEX : \tr (embed_subnorm X) = 1.
      {
        have Hreal : \tr (embed_subnorm X) \is Num.real
          by apply: ger0_real; exact: (psdmx_trace PEX).
        by rewrite -(RRe_real Hreal) HtrEX_R.
      }
      have HtrEY_R : @complex.Re R (\tr (embed_subnorm Y)) = 1
        by rewrite (embed_subnorm_tr_eq1 HY_den).
      have HtrEY_le : @complex.Re R (\tr (embed_subnorm Y)) <= 1
        by rewrite HtrEY_R lexx.
      rewrite (gfid_eq_fid_tr1_mx PEX PEY HtrEX HtrEY_le).
      by rewrite /gfidelity.
    }
    rewrite (Hembed_pd rho0 tau0 Hrho0 Htau0 Hrho0_tr Htau0_tr).
    rewrite (Hembed_pd rho0 sigma0 Hrho0 Hsigma0 Hrho0_tr Hsigma0_tr).
    rewrite (Hembed_pd sigma0 tau0 Hsigma0 Htau0 Hsigma0_tr Htau0_tr).
    exact: Hden1_triangle HrhoE_den1 HsigmaE_den1 HtauE_den1.
  }
  rewrite /pur_dist /gfid.
  have Hrho_mx : h2mx rho \is psdmx by move: Prho; rewrite qualifE.
  have Htau_mx : h2mx tau \is psdmx by move: Ptau; rewrite qualifE.
  have Hsigma_mx : h2mx sigma \is psdmx by move: Psigma; rewrite qualifE.
  exact: Hmatrix_triangle Hrho_mx Htau_mx Hsigma_mx Hrho_tr Htau_tr Hsigma_tr.
Qed.

(* Matrix purified distance, used by the pure-state trace-norm bridge.   *)
Definition pur_dist_mx {na nb : nat} (A B : 'M[C]_(na * nb)) : R :=
  Num.sqrt (1 - (gfidelity A B)^2).

(* pure_state_trnorm                                                        *)
(* infra: no tex label — fundamental & reusable (mathcomp-style)            *)
(* math: for unit-trace rank-1 PSD A,B: trnorm(A-B) = 2·pur_dist_mx(A,B).  *)
(* Consumer: pd_gtd_bar_lb and Fuchs-van de Graaf style bounds.             *)
(* path: utils:pure_state_trnorm -> utils:pd_gtd_bar_lb -> *)
(*   bb84:privacy_amplification -> bb84:bb84_secret *)
Lemma pure_state_trnorm {na nb : nat} (A B : 'M[C]_(na * nb)) :
  A \is psdmx -> B \is psdmx ->
  (\rank A <= 1)%N -> (\rank B <= 1)%N ->
  @complex.Re R (\tr A) = 1 -> @complex.Re R (\tr B) = 1 ->
  trnorm (A - B) = ((2%:R : R) * pur_dist_mx A B)%:C.
Proof.
  move=> HApsd HBpsd HArank HBrank HAtr HBtr.
  have HtrA_C : \tr A = 1
    by rewrite -(RRe_real (ger0_real (psdmx_trace HApsd))) HAtr.
  have HtrB_C : \tr B = 1
    by rewrite -(RRe_real (ger0_real (psdmx_trace HBpsd))) HBtr.
  have HA_ne0 : A != 0.
  { apply/eqP=> HA0; move: HtrA_C; rewrite HA0 raddf0.
    by move/eqP; rewrite eq_sym oner_eq0. }
  have HB_ne0 : B != 0.
  { apply/eqP=> HB0; move: HtrB_C; rewrite HB0 raddf0.
    by move/eqP; rewrite eq_sym oner_eq0. }
  have HArank1 : \rank A = 1%N
    by apply/eqP; rewrite eqn_leq HArank lt0n mxrank_eq0.
  have HBrank1 : \rank B = 1%N
    by apply/eqP; rewrite eqn_leq HBrank lt0n mxrank_eq0.
  have HA_den1 : A \is den1mx
    by rewrite qualifE/= HApsd /= HtrA_C eqxx.
  have HB_den1 : B \is den1mx
    by rewrite qualifE/= HBpsd /= HtrB_C eqxx.
  have [u Hu] := rank1_form HA_den1 HArank1.
  have [v Hv] := rank1_form HB_den1 HBrank1.
  have Htr_uu : (u^*t *m u) ord0 ord0 = 1
    by rewrite -trace_mx11 mxtrace_mulC -Hu HtrA_C.
  have Htr_vv : (v^*t *m v) ord0 ord0 = 1
    by rewrite -trace_mx11 mxtrace_mulC -Hv HtrB_C.
  have Hunorm : u^*t *m u = 1%:M
    by rewrite [u^*t *m u]mx11_scalar Htr_uu.
  have Hvnorm : v^*t *m v = 1%:M
    by rewrite [v^*t *m v]mx11_scalar Htr_vv.
  pose c : C := (u^*t *m v) ord0 ord0.
  have Huv : u^*t *m v = c%:M by rewrite [LHS]mx11_scalar.
  have Hvu : v^*t *m u = ( c^* )%:M.
  { rewrite [LHS]mx11_scalar; congr (_ %:M).
    rewrite /c -mxE_adj.
    by rewrite adjmxM !adjmxK. }
  (* gfidelity A B = `|c| (real). *)
  have HA_tr_le : @complex.Re R (\tr A) <= 1 by rewrite HAtr lexx.
  have HB_tr_le : @complex.Re R (\tr B) <= 1 by rewrite HBtr lexx.
  pose ac : R := @complex.Re R `|c|.
  have Hac_real : `|c| \is Num.real by exact: normr_real.
  have HacE : `|c| = ac%:C by rewrite /ac RRe_real.
  have Hac_ge0 : 0 <= ac by move: (normr_ge0 c); rewrite HacE lecR.
  have Hac_le1 : ac <= 1.
  { move: (@l2normC_cauchy C _ (u^*t) v).
    rewrite trace_mx11 l2normC_adjmx.
    have Hu_l2 : l2normC u = 1 by rewrite l2normC_dot -Hu HtrA_C sqrtC1.
    have Hv_l2 : l2normC v = 1 by rewrite l2normC_dot -Hv HtrB_C sqrtC1.
    rewrite Hu_l2 Hv_l2 mul1r -/c HacE lecR.
    done. }
  have Hac_sq_le1 : ac ^+ 2 <= 1.
  { have <- : (1 : R) ^+ 2 = 1 by rewrite expr1n.
    by rewrite lerXn2r ?nnegrE. }
  have HccE : c * c^* = (ac ^+ 2)%:C.
  { by rewrite -normCK HacE -rmorphXn. }
  have HccE' : c^* * c = (ac ^+ 2)%:C.
  { by rewrite mulrC HccE. }
  have Hgf : gfidelity A B = ac.
  { rewrite (gfid_eq_fid_tr1_mx HApsd HBpsd HtrA_C HB_tr_le).
    by rewrite Hu Hv fid_gram_general_mx (schnorm11 1) /ac. }
  have HpurE : pur_dist_mx A B = Num.sqrt (1 - ac ^+ 2).
  { by rewrite /pur_dist_mx Hgf. }
  have H1mac_ge0 : 0 <= 1 - ac ^+ 2 by rewrite subr_ge0.
  (* (A - B)^3 = (1 - |c|^2) * (A - B). *)
  pose M : 'M[C]_(na * nb) := A - B.
  have HAA : A *m A = A.
  { rewrite Hu -mulmxA [u^*t *m _]mulmxA Hunorm mul1mx. done. }
  have HBB : B *m B = B.
  { rewrite Hv -mulmxA [v^*t *m _]mulmxA Hvnorm mul1mx. done. }
  have HAB : A *m B = c *: (u *m v^*t).
  { rewrite Hu Hv -[(u *m u^*t) *m _]mulmxA [u^*t *m _]mulmxA Huv.
    by rewrite mul_scalar_mx scalemxAr. }
  have HBA : B *m A = c^* *: (v *m u^*t).
  { rewrite Hu Hv -[(v *m v^*t) *m _]mulmxA [v^*t *m _]mulmxA Hvu.
    by rewrite mul_scalar_mx scalemxAr. }
  pose Y : 'M[C]_(na * nb) := c *: (u *m v^*t).
  pose Z : 'M[C]_(na * nb) := c^* *: (v *m u^*t).
  have HABsq : M *m M = A + B - Y - Z.
  { have HMM : M *m M = A *m A - A *m B - (B *m A - B *m B).
    { by rewrite /M mulmxBl !mulmxBr. }
    rewrite HMM HAA HBB HAB HBA -/Y -/Z.
    (* Goal: A - Y - (Z - B) = A + B - Y - Z *)
    rewrite opprB addrACA addrA.
    done. }
  (* M is hermitian, M*M is PSD. *)
  have HM_herm : M^*t = M.
  { rewrite /M linearB/= Hu Hv.
    by rewrite !adjmxM !adjmxK. }
  have HMpsd_sq : M *m M \is psdmx.
  { have -> : M *m M = M^*t *m M by rewrite HM_herm.
    exact: formV_psd. }
  (* Polynomial identity M*M*M = (1 - ac^2) *: M. *)
  have HYA : Y *m A = (ac ^+ 2)%:C *: A.
  { rewrite /Y Hu -scalemxAl -[(u *m v^*t) *m _]mulmxA.
    rewrite [v^*t *m _]mulmxA Hvu mul_scalar_mx.
    by rewrite -scalemxAr scalerA -Hu HccE. }
  have HYB : Y *m B = Y.
  { rewrite /Y Hv -scalemxAl -[(u *m v^*t) *m _]mulmxA.
    by rewrite [v^*t *m _]mulmxA Hvnorm mul1mx. }
  have HZA : Z *m A = Z.
  { rewrite /Z Hu -scalemxAl -[(v *m u^*t) *m _]mulmxA.
    by rewrite [u^*t *m _]mulmxA Hunorm mul1mx. }
  have HZB : Z *m B = (ac ^+ 2)%:C *: B.
  { rewrite /Z Hv -scalemxAl -[(v *m u^*t) *m _]mulmxA.
    rewrite [u^*t *m _]mulmxA Huv mul_scalar_mx.
    by rewrite -scalemxAr scalerA -Hv HccE'. }
  (* Step (a): cubic identity M*M*M = (1 - ac^2) *: M. *)
  pose g : C := (1 - ac ^+ 2)%:C.
  have HAM : A *m M = A - Y.
  { rewrite /M.
    rewrite mulmxBr.
    rewrite HAA.
    rewrite HAB.
    reflexivity. }
  have HBM : B *m M = Z - B.
  { rewrite /M.
    rewrite mulmxBr.
    rewrite HBA.
    rewrite HBB.
    reflexivity. }
  have HYM : Y *m M = (ac ^+ 2)%:C *: A - Y.
  { rewrite /M.
    rewrite mulmxBr.
    rewrite HYA.
    rewrite HYB.
    reflexivity. }
  have HZM : Z *m M = Z - (ac ^+ 2)%:C *: B.
  { rewrite /M.
    rewrite mulmxBr.
    rewrite HZA.
    rewrite HZB.
    reflexivity. }
  have HABcube : M *m M *m M = g *: M.
  { rewrite HABsq mulmxBl mulmxBl mulmxDl HAM HBM HYM HZM /g /M.
    rewrite [(1 - ac ^+ 2)%:C](raddfB (real_complex _))/= rmorph1.
    set p : C := (ac ^+ 2)%:C.
    rewrite scalerBr scalerBl scalerBl scale1r scale1r.
    rewrite !opprB.
    (* LHS = ((A - Y) + (Z - B)) + (Y - p*:A) + (p*:B - Z) *)
    rewrite -addrA.
    rewrite addrACA.
    (* Each pair: (A - Y) + (Y - p*:A) = A - p*:A; (Z - B) + (p*:B - Z) = p*:B - B *)
    rewrite -[(A - Y) + (Y - p *: A)]addrA.
    rewrite [- Y + (Y - p *: A)]addrA.
    rewrite addNr add0r.
    rewrite -[(Z - B) + (p *: B - Z)]addrA.
    rewrite addrCA.
    rewrite [Z + (p *: B - Z)]addrCA.
    rewrite subrr addr0.
    rewrite [- B + p *: B]addrC.
    by rewrite -opprB. }
  (* Step (b): spectral analysis. *)
  have HM_normal : M \is normalmx by apply: hermmx_normal; apply/hermmxP.
  pose s := spectral_diag M.
  pose U := eigenmx M.
  have HU_uni : U \is unitarymx by apply: eigen_unitarymx.
  have HU_K : U^*t *m U = 1%:M by apply: unitarymxKV.
  have HU_K' : U *m U^*t = 1%:M by apply: unitarymxK.
  have HM_dec : M = U *m diag_mx s *m U^*t by move/eigen_dec: HM_normal.
  have Hs_real : s \is a realmx
    by apply: hermitian_spectral_diag_real; apply/hermmxP.
  (* Conjugation lemma: U *m D *m U^*t *m (U *m D' *m U^*t) = U *m (D *m D') *m U^*t *)
  have HUD_compose : forall (D1 D2 : 'M[C]_(na*nb)),
      (U *m D1 *m U^*t) *m (U *m D2 *m U^*t) = U *m (D1 *m D2) *m U^*t.
  { move=> D1 D2.
    rewrite -[(U *m D1 *m U^*t) *m _]mulmxA.
    rewrite [U^*t *m (U *m D2 *m U^*t)]mulmxA.
    rewrite [U^*t *m (U *m D2)]mulmxA HU_K mul1mx.
    by rewrite mulmxA mulmxA. }
  have HM2_diag : M *m M = U *m diag_mx (s .* s) *m U^*t.
  { rewrite {1 2}HM_dec HUD_compose.
    by rewrite diag_mx_dmul. }
  have HM3_diag : M *m M *m M = U *m diag_mx (s .* s .* s) *m U^*t.
  { rewrite HM2_diag {1}HM_dec HUD_compose.
    by rewrite diag_mx_dmul. }
  have HsCube : forall i, s 0 i * s 0 i * s 0 i = g * s 0 i.
  { move=> i.
    (* From HM3_diag and HABcube: U *m diag(s³) *m U^*t = g *: U *m diag(s) *m U^*t.
      Multiply on left by U^*t and right by U to extract diag(s³) = g *: diag(s). *)
    have Hkey : diag_mx (s .* s .* s) = g *: diag_mx s.
    { have HE : U *m diag_mx (s .* s .* s) *m U^*t
              = U *m (g *: diag_mx s) *m U^*t.
      { rewrite -HM3_diag HABcube.
        rewrite -[in RHS]scalemxAr -[in RHS]scalemxAl.
        by rewrite -HM_dec. }
      have simpl_UU : forall (X : 'M[C]_(na*nb)),
          U^*t *m (U *m X *m U^*t) *m U = X.
      { move=> X.
        rewrite -mulmxA. rewrite -[(U *m X *m U^*t) *m U]mulmxA.
        rewrite [U^*t *m U]HU_K mulmx1.
        rewrite mulmxA HU_K mul1mx. done. }
      by rewrite -[diag_mx _]simpl_UU HE simpl_UU. }
    by move/matrixP/(_ i i): Hkey; rewrite !mxE eqxx !mulr1n. }
  (* Each eigenvalue s_i satisfies s_i^3 = g · s_i, i.e. s_i (s_i^2 - g) = 0. *)
  have Hsroot : forall i, s 0 i = 0 \/ s 0 i ^+ 2 = g.
  { move=> i.
    have HC := HsCube i.
    have HE : s 0 i * (s 0 i * s 0 i - g) = 0.
    { rewrite mulrBr.
      rewrite [s 0 i * (s 0 i * s 0 i)]mulrA HC.
      by rewrite [s 0 i * g]mulrC subrr. }
    move/eqP: HE; rewrite mulf_eq0.
    case/orP=> [/eqP Hsi | /eqP Hsi2]; first by left.
    by right; rewrite expr2; apply/eqP; rewrite -subr_eq0 Hsi2. }
  have HtrM_sum : \tr M = \sum_i s 0 i.
  { rewrite {1}HM_dec mxtrace_mulC mulmxA HU_K mul1mx mxtrace_diag.
    by apply: eq_bigr=> i _. }
  have HtrM0 : \tr M = 0.
  { by rewrite /M raddfB/= HtrA_C HtrB_C subrr. }
  have HtrM2_sum : \tr (M *m M) = \sum_i s 0 i ^+ 2.
  { rewrite HM2_diag mxtrace_mulC mulmxA HU_K mul1mx mxtrace_diag.
    by apply: eq_bigr=> i _; rewrite !mxE expr2. }
  have HtrY : \tr Y = (ac ^+ 2)%:C.
  { rewrite /Y linearZ/= mxtrace_mulC.
    rewrite trace_mx11 Hvu mxE eqxx mulr1n.
    by rewrite -HccE. }
  have HtrZ : \tr Z = (ac ^+ 2)%:C.
  { rewrite /Z linearZ/= mxtrace_mulC.
    rewrite trace_mx11 Huv mxE eqxx mulr1n.
    by rewrite -/c mulrC -HccE. }
  have HtrM2_val : \tr (M *m M) = (2%:R * (1 - ac ^+ 2))%:C.
  { rewrite HABsq !raddfD/= !raddfN/=.
    rewrite HtrA_C HtrB_C HtrY HtrZ.
    rewrite mulrBr mulr1 (raddfB (real_complex _))/=.
    rewrite -addrA -opprD.
    congr (_ - _).
    - by rewrite rmorph_nat -[2%:R]/(1 *+ 2) mulrSr mulr1n.
    - rewrite -mulr2n -rmorphMn/= mulr_natl. done. }
  have Hg_real : (1 - ac ^+ 2 : R) >= 0 by [].
  have Hg_eq : g = (1 - ac ^+ 2)%:C by [].
  (* Sum of squares = 2(1 - ac^2). *)
  have Hsum_sq : \sum_i s 0 i ^+ 2 = (2%:R * (1 - ac ^+ 2))%:C
    by rewrite -HtrM2_sum HtrM2_val.
  (* Sum |s i| = 2 sqrt(1 - ac^2). Reduce to two cases on whether g = 0. *)
  have Hac_to_sqrt : Num.sqrt (1 - ac ^+ 2) ^+ 2 = 1 - ac ^+ 2
    by rewrite sqr_sqrtr.
  have Hs_abs_val : forall i, `|s 0 i| = 0 \/ `|s 0 i| = (Num.sqrt (1 - ac ^+ 2))%:C.
  { move=> i; case: (Hsroot i)=> Hroot; first by left; rewrite Hroot normr0.
    right.
    have Hsq : `|s 0 i| ^+ 2 = (1 - ac ^+ 2)%:C.
    { rewrite -normrX ger0_norm; first by rewrite Hroot.
      by rewrite Hroot lecR. }
    have Hrhs_sq : ((Num.sqrt (1 - ac ^+ 2))%:C : C) ^+ 2 = (1 - ac ^+ 2)%:C
      by rewrite -rmorphXn/= sqr_sqrtr.
    have HnormGe0 : 0 <= `|s 0 i| by apply: normr_ge0.
    have HsqrtGe0 : 0 <= ((Num.sqrt (1 - ac ^+ 2))%:C : C)
      by rewrite ler0c sqrtr_ge0.
    have <- := sqrCK HnormGe0.
    have <- := sqrCK HsqrtGe0.
    by rewrite Hsq Hrhs_sq. }
  (* trnorm M via spectral *)
  have HUadj_uni : U^*t \is unitarymx by apply/adjmx_unitaryP.
  have Htrnorm_M : trnorm M = \sum_i `|s 0 i|.
  { rewrite {1}HM_dec.
    rewrite (trnormUr _ HUadj_uni).
    rewrite (trnormUl _ HU_uni).
    by rewrite trnorm_diag l1normE big_ord1; apply: eq_bigr=> i _. }
  (* Count nonzero eigenvalues to fix sum |s i|. *)
  case: (eqVneq (1 - ac ^+ 2 : R) 0) => [Hg0 | Hgnz].
  { (* g = 0: every s_i = 0. *)
    have Hall0 : forall i, s 0 i = 0.
    { move=> i; case: (Hsroot i) => // Hsq.
      apply/eqP; rewrite -[_ == _]sqrf_eq0 Hsq /g.
      by rewrite Hg0 eqxx. }
    rewrite Htrnorm_M HpurE Hg0 sqrtr0 mulr0.
    rewrite -[RHS](_ : 0%:C = 0) //.
    rewrite (eq_bigr (fun=> 0)).
    - by rewrite big1.
    - by move=> i _; rewrite Hall0 normr0. }
  (* g != 0 case: count k = #{i: s_i != 0}, get k * (1 - ac²) = 2(1-ac²). *)
  pose T := [pred i : 'I_(na * nb) | s 0 i != 0].
  have HT_sq : \sum_(i in T) s 0 i ^+ 2 = (#|T|)%:R * g.
  { rewrite (eq_bigr (fun=> g)).
    - by rewrite sumr_const mulr_natl.
    - move=> i; rewrite inE => Hi.
      by case: (Hsroot i) => [Hi0|->]; [rewrite Hi0 eqxx in Hi |]. }
  have Hsum_split_sq : \sum_i s 0 i ^+ 2 = \sum_(i in T) s 0 i ^+ 2.
  { rewrite [LHS](bigID (fun i => i \in T))/= addrC big1 ?add0r //.
    by move=> i; rewrite inE negbK => /eqP ->; rewrite expr0n. }
  have Hg_C_neq0 : g != 0
    by rewrite /g -[0]/(0%:C); apply/eqP=> /complexI; apply/eqP.
  have HT_card_C : ((#|T|)%:R : C) = 2%:R.
  { apply/(@mulIf _ g)=> //.
    rewrite -HT_sq -Hsum_split_sq Hsum_sq /g.
    by rewrite (rmorphM (real_complex _))/= rmorph_nat. }
  have HT_abs : \sum_(i in T) `|s 0 i|
              = ((#|T|)%:R : C) * (Num.sqrt (1 - ac ^+ 2))%:C.
  { rewrite (eq_bigr (fun=> ((Num.sqrt (1 - ac ^+ 2))%:C : C))).
    - by rewrite sumr_const mulr_natl.
    - move=> i; rewrite inE => Hi.
      case: (Hs_abs_val i) => Habs //.
      move: Hi => /negP[]. apply/eqP. apply/normr0_eq0.
      by rewrite Habs. }
  have Hsum_abs_split : \sum_i `|s 0 i| = \sum_(i in T) `|s 0 i|.
  { rewrite [LHS](bigID (fun i => i \in T))/= addrC big1 ?add0r //.
    by move=> i; rewrite inE negbK => /eqP ->; rewrite normr0. }
  rewrite Htrnorm_M HpurE Hsum_abs_split HT_abs HT_card_C.
  by rewrite (rmorphM (real_complex _))/= rmorph_nat.
Qed.

(* tex: pr:pd-gtd-bounds — Tomamichel, 'A Framework for Non-Asymptotic       *)
(*   Quantum Information Theory' (PhD thesis, arXiv:1203.2142),              *)
(*   Proposition 3.3, full generalized trace distance                        *)
(* math: D̄(ρ,τ) := ½||ρ-τ||₁ + ½|Tr ρ - Tr τ| ≤ P(ρ,τ).                     *)
(* Consumers (≥1 Coq, compelling standalone textbook fact): used by          *)
(* thm:two-universal-hashing smoothing-step triangle inequality.            *)
(* pr:pd-gtd-bounds gives the FULL D̄ ≤ P identity, of which pd_gtd_lb        *)
(* (D ≤ P) is only the lossless half.                                       *)
(* path: utils:pd_gtd_bar_lb -> bb84:privacy_amplification -> *)
(*   bb84:bb84_secret *)
Lemma pd_gtd_bar_lb (L : finType) (HL : L -> chsType) (S : {set L})
    (rho tau : 'F[HL]_S) :
  rho \is psdlf -> tau \is psdlf ->
  @complex.Re R (\Tr rho) <= 1 -> @complex.Re R (\Tr tau) <= 1 ->
  trnormH (rho - tau) / 2%:R +
    `|@complex.Re R (\Tr rho) - @complex.Re R (\Tr tau)| / 2%:R
  <= pur_dist rho tau.
Proof.
  move=> Prho Ptau Hrho_tr Htau_tr.
  set n := dim 'H[HL]_S.
  pose rhoM : 'M[C]_n := h2mx rho.
  pose tauM : 'M[C]_n := h2mx tau.
  have Hh2mxB (x y : 'F[HL]_S) :
      h2mx (x - y) = h2mx x - h2mx y.
  { have Hlin := @h2mxP R ('H[HL]_S) ('H[HL]_S).
    have Hadd (u v : 'F[HL]_S) : h2mx (u + v) = h2mx u + h2mx v.
    { rewrite -[u in h2mx (u + v)]scale1r.
      rewrite -[h2mx u]scale1r.
      exact: (Hlin 1 u v). }
    have Hneg (z : 'F[HL]_S) : h2mx (- z) = - h2mx z.
    { exact: linearN. }
    change (h2mx (x + - y) = h2mx x + - h2mx y).
    by rewrite Hadd Hneg. }
  have HrhoM_psd : rhoM \is psdmx by move: Prho; rewrite qualifE.
  have HtauM_psd : tauM \is psdmx by move: Ptau; rewrite qualifE.
  have HtrR_rhoM : @complex.Re R (\tr rhoM) <= 1 by [].
  have HtrR_tauM : @complex.Re R (\tr tauM) <= 1 by [].
  have HrhoM_den : rhoM \is denmx := denmx_psd_re_tr_le HrhoM_psd HtrR_rhoM.
  have HtauM_den : tauM \is denmx := denmx_psd_re_tr_le HtauM_psd HtrR_tauM.
  pose rhoE : 'M[C]_(n + 1) := embed_subnorm rhoM.
  pose tauE : 'M[C]_(n + 1) := embed_subnorm tauM.
  have HrhoE_psd : rhoE \is psdmx := embed_subnorm_psdmx HrhoM_den.
  have HtauE_psd : tauE \is psdmx := embed_subnorm_psdmx HtauM_den.
  have HrhoE_trR : @complex.Re R (\tr rhoE) = 1 :=
    embed_subnorm_tr_eq1 HrhoM_den.
  have HtauE_trR : @complex.Re R (\tr tauE) = 1 :=
    embed_subnorm_tr_eq1 HtauM_den.
  have HrhoE_realtr : \tr rhoE \is Num.real
    by apply: ger0_real; exact: psdmx_trace HrhoE_psd.
  have HtauE_realtr : \tr tauE \is Num.real
    by apply: ger0_real; exact: psdmx_trace HtauE_psd.
  have HrhoE_tr1 : \tr rhoE = 1
    by rewrite -(RRe_real HrhoE_realtr) HrhoE_trR.
  have HtauE_tr1 : \tr tauE = 1
    by rewrite -(RRe_real HtauE_realtr) HtauE_trR.
  have HrhoE_den : rhoE \is denmx
    by rewrite qualifE/= HrhoE_psd /= HrhoE_tr1 lexx.
  have HtauE_den : tauE \is denmx
    by rewrite qualifE/= HtauE_psd /= HtauE_tr1 lexx.
  have HrhoE_nz : rhoE != 0.
  { apply/eqP=> Hz; move: HrhoE_tr1; rewrite Hz raddf0=> /esym.
    by apply/eqP; rewrite oner_eq0. }
  have HrhoE_rk_le : (\rank rhoE <= n + 1)%N by exact: rank_leq_row.
  (* Step A: rank-1 purification phi of rhoE on M[C]_((n+1)*(n+1)). *)
  have [phi [Hphi_den [Hphi_rk1 Hphi_pt]]] := purification_exists_in_dim HrhoE_den HrhoE_nz HrhoE_rk_le.
  (* Step B: Apply fid_iii_uhl_mx to lift tauE. *)
  have HtauE_nz : tauE != 0.
  { apply/eqP=> Hz; move: HtauE_tr1; rewrite Hz raddf0=> /esym.
    by apply/eqP; rewrite oner_eq0. }
  have HtauE_rk_le : (\rank tauE <= n + 1)%N by exact: rank_leq_row.
  have [psi [Hpsi_den [Hpsi_rk1 [Hpsi_pt Hfid_pp]]]] :=
    fid_iii_uhl_mx Hphi_den Hphi_rk1 Hphi_pt HtauE_den HtauE_nz HtauE_rk_le.
  have Hphi_psd : phi \is psdmx := denmx_psd Hphi_den.
  have Hpsi_psd : psi \is psdmx := denmx_psd Hpsi_den.
  have Hphi_tr1 : \tr phi = 1
    by rewrite (tr_ptrace2 phi) Hphi_pt HrhoE_tr1.
  have Hpsi_tr1 : \tr psi = 1
    by rewrite (tr_ptrace2 psi) Hpsi_pt HtauE_tr1.
  have Hphi_trR : @complex.Re R (\tr phi) = 1 by rewrite Hphi_tr1.
  have Hpsi_trR : @complex.Re R (\tr psi) = 1 by rewrite Hpsi_tr1.
  (* Step C: gfidelity phi psi = gfidelity rhoE tauE. *)
  have HtauE_tr_le : @complex.Re R (\tr tauE) <= 1 by rewrite HtauE_trR lexx.
  have Hpsi_tr_le : @complex.Re R (\tr psi) <= 1 by rewrite Hpsi_trR lexx.
  have Hgf_pp : gfidelity phi psi = gfidelity rhoE tauE.
  { rewrite (gfid_eq_fid_tr1_mx Hphi_psd Hpsi_psd Hphi_tr1 Hpsi_tr_le).
    by rewrite (gfid_eq_fid_tr1_mx HrhoE_psd HtauE_psd HrhoE_tr1 HtauE_tr_le). }
  (* Step D: gfidelity rhoE tauE = gfid rho tau. *)
  (* gfidelity rhoE tauE (when both have trace 1) =                         *)
  (*   Re(trnorm(sqrtmx rhoE *m sqrtmx tauE)) (gfid_eq_fid_tr1_mx) *)
  (* gfidelity (h2mx rho) (h2mx tau) (defn) =                                *)
  (*   Re(trnorm(sqrtmx (embed_subnorm (h2mx rho)) *m sqrtmx (embed_subnorm (h2mx tau)))) *)
  (*   = Re(trnorm(sqrtmx rhoE *m sqrtmx tauE)).                             *)
  have Hgf_E : gfidelity rhoE tauE = gfid rho tau.
  { rewrite (gfid_eq_fid_tr1_mx HrhoE_psd HtauE_psd HrhoE_tr1 HtauE_tr_le).
    by rewrite /gfid /gfidelity -/rhoM -/tauM /rhoE /tauE. }
  (* Step E: Apply pure_state_trnorm. *)
  have Hphi_rk_le : (\rank phi <= 1)%N by rewrite Hphi_rk1.
  have Hpsi_rk_le : (\rank psi <= 1)%N by rewrite Hpsi_rk1.
  have Htn_pp : trnorm (phi - psi) = ((2%:R : R) * pur_dist_mx phi psi)%:C
    := pure_state_trnorm Hphi_psd Hpsi_psd Hphi_rk_le Hpsi_rk_le Hphi_trR Hpsi_trR.
  have Hpdmx_eq : pur_dist_mx phi psi = pur_dist rho tau
    by rewrite /pur_dist_mx /pur_dist Hgf_pp Hgf_E.
  (* Step F: DPI: trnorm(rhoE - tauE) <= trnorm(phi - psi). *)
  have Hpt_diff : ptrace2 (phi - psi) = rhoE - tauE
    by rewrite linearB /= Hphi_pt Hpsi_pt.
  have HDPI : trnorm (rhoE - tauE) <= trnorm (phi - psi)
    by rewrite -Hpt_diff; exact: trnorm_ptrace2.
  (* Step G: Block-diag decomp of trnorm(rhoE - tauE). *)
  have HrhoE_tr1R : (1 : R) - @complex.Re R (\tr rhoM) = @complex.Re R (1 - \tr rhoM)
    by rewrite raddfB /=.
  have HtauE_tr1R : (1 : R) - @complex.Re R (\tr tauM) = @complex.Re R (1 - \tr tauM)
    by rewrite raddfB /=.
  pose dt : R := @complex.Re R (\tr tauM) - @complex.Re R (\tr rhoM).
  have HrhoM_real : \tr rhoM = (@complex.Re R (\tr rhoM))%:C
    by apply: esym; apply: RRe_real; apply: ger0_real; apply: psdmx_trace HrhoM_psd.
  have HtauM_real : \tr tauM = (@complex.Re R (\tr tauM))%:C
    by apply: esym; apply: RRe_real; apply: ger0_real; apply: psdmx_trace HtauM_psd.
  pose tA : R := @complex.Re R (\tr rhoM).
  pose tB : R := @complex.Re R (\tr tauM).
  have HtA_real : \tr rhoM = tA%:C
    by apply/esym; apply: RRe_real; apply: ger0_real; exact: psdmx_trace HrhoM_psd.
  have HtB_real : \tr tauM = tB%:C
    by apply/esym; apply: RRe_real; apply: ger0_real; exact: psdmx_trace HtauM_psd.
  have HdtR : dt = tB - tA by [].
  have HdiffE : rhoE - tauE = block_mx (rhoM - tauM) (0 : 'M[C]_(n,1)) (0 : 'M[C]_(1,n))
                                      (dt%:C *: (1%:M : 'M[C]_1)).
  { rewrite /rhoE /tauE /embed_subnorm.
    rewrite opp_block_mx !oppr0 add_block_mx !(addr0,add0r).
    congr (block_mx _ _ _ _).
    rewrite -scalerBl; congr (_ *: _).
    rewrite HtA_real HtB_real HdtR.
    have one_C_real : (1 : C) = (1 : R)%:C by apply/esym; exact: rmorph1.
    rewrite [X in X - _ - _]one_C_real.
    rewrite [X in _ - (X - _)]one_C_real.
    rewrite -!rmorphB /=.
    have HR : (((1 : R) - tA) - ((1 : R) - tB) = tB - tA)%R.
    { rewrite GRing.opprB.
      rewrite [(tB - (1 : R))%R]GRing.addrC.
      rewrite GRing.addrACA.
      by rewrite GRing.subrr GRing.add0r GRing.addrC. }
    by rewrite HR. }
  have Htn_E : trnorm (rhoE - tauE) = trnorm (rhoM - tauM) + `|dt|%:C.
  { rewrite HdiffE.
    rewrite (schnorm_mxdiag 1 (rhoM - tauM) (dt%:C *: (1%:M : 'M[C]_1))).
    rewrite l1normE !big_ord1 big_split_ord /=.
    under eq_bigr => j _.
      rewrite row_mxEl ger0_norm; last by apply: svd_d_ge0.
      over.
    rewrite big_ord1 row_mxEr ger0_norm; last by apply: svd_d_ge0.
    rewrite -trnorm_svdE.
    have svdEq : svd_d (dt%:C *: (1%:M : 'M[C]_1)) 0 ord0 = `|dt|%:C.
    { have Htr : trnorm (dt%:C *: (1%:M : 'M[C]_1)) = `|dt|%:C
        by rewrite scalemx1 trnorm_scale mul1r normc_def /=
                  expr0n addr0 sqrtr_sqr.
      by rewrite trnorm_svdE big_ord1 in Htr. }
    by rewrite svdEq. }
  (* Step H: Combine. *)
  have HtnRE : @complex.Re R (trnorm (rhoE - tauE)) =
              @complex.Re R (trnorm (rhoM - tauM)) + `|dt|.
  { by rewrite Htn_E raddfD /=. }
  (* trnormH rho - tau *)
  have Htn_lf : trnormH (rho - tau) = @complex.Re R (trnorm (rhoM - tauM)).
  { by rewrite /trnormH Hh2mxB -/rhoM -/tauM. }
  have Hdt_eq : `|dt| = `|@complex.Re R (\Tr rho) - @complex.Re R (\Tr tau)|.
  { rewrite /dt /lftrace -/rhoM -/tauM distrC. done. }
  (* trnorm(phi - psi) is real *)
  have Hphi_psi_realC : trnorm (phi - psi) = ((2%:R * pur_dist rho tau) : R)%:C
    by rewrite Htn_pp Hpdmx_eq.
  have HRe_phi_psi : @complex.Re R (trnorm (phi - psi)) = 2%:R * pur_dist rho tau
    by rewrite Hphi_psi_realC /=.
  have HtnE_real : @complex.Re R (trnorm (rhoE - tauE)) <= 2%:R * pur_dist rho tau.
  { rewrite -HRe_phi_psi -lecR.
    rewrite (RRe_real (ger0_real (trnorm_ge0 _))).
    rewrite (RRe_real (ger0_real (trnorm_ge0 _))).
    exact: HDPI. }
  move: HtnE_real; rewrite HtnRE Htn_lf Hdt_eq.
  move=> Hkey.
  rewrite -mulrDl ler_pdivrMr ?ltr0n// mulrC.
  exact: Hkey.
Qed.

(* Identity of indiscernibles for purified distance.          *)
(* tex: consequence of pr:pd-gtd-bounds — the Fuchs–van de Graaf lower bound *)
(* ½||ρ-τ||₁ ≤ P(ρ,τ).  At P=0 the trace-norm half is squeezed to 0, and a  *)
(* norm vanishes only on 0, so ρ=τ.  This is the metric axiom missing from   *)
(* pd_metric_triangle; needed for the ε=0 smoothing ball being a singleton.  *)
(* path: utils:pur_dist_eq0 -> entropy:smooth ε=0 bridge.                     *)
Lemma pur_dist_eq0 (L : finType) (HL : L -> chsType) (S : {set L})
    (rho tau : 'F[HL]_S) :
  rho \is psdlf -> tau \is psdlf ->
  @complex.Re R (\Tr rho) <= 1 -> @complex.Re R (\Tr tau) <= 1 ->
  pur_dist rho tau = 0 -> rho = tau.
Proof.
  move=> Prho Ptau Hrho Htau Hpd0.
  have Hbound := pd_gtd_bar_lb Prho Ptau Hrho Htau.
  rewrite Hpd0 in Hbound.
  (* trnormH(ρ-τ)/2 + |Δtr|/2 ≤ 0, with both summands ≥ 0. *)
  have Htn_ge0 : 0 <= trnormH (rho - tau).
  { have Hge := trnorm_ge0 (h2mx (rho - tau)).
    have Hreal : trnorm (h2mx (rho - tau)) \is Num.real := ger0_real Hge.
    rewrite /trnormH -lecR rmorph0 (RRe_real Hreal). exact: Hge. }
  have Hhalf1_ge0 : 0 <= trnormH (rho - tau) / 2%:R
    by apply: divr_ge0; [exact: Htn_ge0 | rewrite ler0n].
  have Hhalf2_ge0 :
      0 <= `|@complex.Re R (\Tr rho) - @complex.Re R (\Tr tau)| / 2%:R
    by apply: divr_ge0; [exact: normr_ge0 | rewrite ler0n].
  have Hhalf1_le0 : trnormH (rho - tau) / 2%:R <= 0.
  { apply: le_trans _ Hbound. by rewrite lerDl. }
  have Htn_le0 : trnormH (rho - tau) <= 0
    by move: Hhalf1_le0; rewrite ler_pdivrMr ?ltr0n // mul0r.
  have Htn0 : trnormH (rho - tau) = 0
    by apply/eqP; rewrite eq_le Htn_le0 Htn_ge0.
  have Htrnorm0 : trnorm (h2mx (rho - tau)) = 0.
  { have Hreal : trnorm (h2mx (rho - tau)) \is Num.real :=
      ger0_real (trnorm_ge0 _).
    by rewrite -(RRe_real Hreal) -/(trnormH (rho - tau)) Htn0 rmorph0. }
  have Hmx0 : h2mx (rho - tau) = 0 := trnorm0_eq0 Htrnorm0.
  have Hsub0 : rho - tau = 0 by apply: h2mx_inj; rewrite Hmx0 h2mx0.
  by apply/eqP; rewrite -subr_eq0 Hsub0.
Qed.

(* tex: pr:pd-gtd-bounds — Tomamichel, 'A Framework for Non-Asymptotic      *)
(*   Quantum Information Theory' (PhD thesis, arXiv:1203.2142),             *)
(*   Proposition 3.3, upper bound half.                                     *)
(* Tomamichel's `D` is the GENERALIZED trace distance for sub-normalized states  *)
(* (df:gtd = Definition 3.1): D(ρ,τ) = ½||ρ-τ||₁ + ½|Tr ρ - Tr τ|.        *)

(* Helper: 1 - (1 - x)² = 2x - x²  for any pzRingType.                         *)
(* The explicit `(R0 : pzRingType)` quantifier locks elaboration to ring scope, *)
(* preventing `\bar R` canonical-structure leak that breaks inline proofs.    *)
(* path: utils:sqr_sub1_expand_ring -> utils:pd_gtd_ub -> utils:pd_gtd_ub' -> *)
(*   entropy:smooth_hmax_attained -> entropy:smooth_hmaxE_EFin -> *)
(*   bb84:bb84_secret *)
Lemma sqr_sub1_expand_ring (R0 : pzRingType) (x : R0) :
  2%:R * x - x ^+ 2 = 1 - (1 - x) ^+ 2.
Proof.
  rewrite -[1 - x]opprB sqrrN sqrrB1.
  rewrite opprD addrA addrAC subrr add0r opprB.
  by rewrite mulr_natl.
Qed.

Local Lemma pd_gtd_ub_aux_PS4f1 {n : nat} : forall XX YY : 'M[C]_(n + 1),
  adjmx XX *m XX <= adjmx YY *m YY ->
  adjmx XX *m YY = adjmx YY *m XX ->
  exists (V B' C' : 'M[C]_(n + 1)) (d : 'rV[C]_(n + 1))
         (U Q : 'M[C]_(n + 1)),
    YY = U *m Q /\
    U \is unitarymx /\
    Q \is psdmx /\
    V \is unitarymx /\
    adjmx V *m V = 1%:M /\ V *m adjmx V = 1%:M /\
    Q = adjmx V *m diag_mx d *m V /\
    (forall i, 0 <= d 0 i) /\
    (forall j, (d 0 j)^* = d 0 j) /\
    B' = V *m (adjmx U *m XX) *m adjmx V /\
    adjmx B' *m B' <= diag_mx d *m diag_mx d /\
    adjmx B' *m diag_mx d = diag_mx d *m B' /\
    (forall i j, d 0 j = 0 -> B' i j = 0) /\
    C' *m diag_mx d = B' /\
    C' = adjmx C' /\
    C' = \matrix_(i, j)
          (if d 0 j != 0 then B' i j / d 0 j
           else if d 0 i != 0 then (B' j i)^* / d 0 i
           else 0).
Proof.
  move=> XX YY Hle Hcomm.
  have [P [Q [U [_ [HQpsd [_ [HQ2 [HU [_ HYQ]]]]]]]]] := polar_PU_UQ YY.
  set B := adjmx U *m XX.
  have HUU : U *m adjmx U = 1%:M := unitarymxK HU.
  have HUtU : adjmx U *m U = 1%:M := unitarymxKV HU.
  have HBle : adjmx B *m B <= Q *m Q.
  { suff HBB : adjmx B *m B = adjmx XX *m XX.
    { suff HQQ : Q *m Q = adjmx YY *m YY by rewrite HBB HQQ.
      have /hermmxP HQh := psdmx_herm HQpsd.
      rewrite HYQ adjmxM -mulmxA (mulmxA (adjmx U)) HUtU mul1mx.
      by rewrite {1}HQh. }
    by rewrite /B adjmxM adjmxK -mulmxA (mulmxA U) HUU mul1mx. }
  have HBcomm : adjmx B *m Q = Q *m B.
  { have /hermmxP HQh := psdmx_herm HQpsd.
    have HBQ : adjmx B *m Q = adjmx XX *m YY.
    { by rewrite /B adjmxM adjmxK -mulmxA -HYQ. }
    have HQB : Q *m B = adjmx YY *m XX.
    { by rewrite /B mulmxA {1}HQh -adjmxM -HYQ. }
    by rewrite HBQ Hcomm -HQB. }
  set V := spectralmx Q.
  set d := spectral_diag Q.
  have HVu : V \is unitarymx := spectral_unitarymx Q.
  have HVtV : adjmx V *m V = 1%:M by exact: unitarymxKV.
  have HVVt : V *m adjmx V = 1%:M by exact: unitarymxK.
  have HQspec : Q = adjmx V *m diag_mx d *m V.
  { by move: (hermitian_normalmx (psdmx_herm HQpsd)) => /eigen_dec;
      rewrite /eigenmx adjmxK -/V -/d. }
  have Hd_nneg : forall i, 0 <= d 0 i.
  { by move=> i; exact: psdmx_eigen_ge0. }
  have Hd_real : forall j, (d 0 j)^* = d 0 j.
  { move=> j. apply/conj_Creal.
    have /realmxP Hreal := hermitian_spectral_diag_real (psdmx_herm HQpsd).
    exact: Hreal. }
  set B' := V *m B *m adjmx V.
  have HVQ : V *m Q = diag_mx d *m V.
  { by rewrite HQspec !mulmxA HVVt mul1mx. }
  have HQV : Q *m adjmx V = adjmx V *m diag_mx d.
  { by rewrite HQspec -(mulmxA _ V (adjmx V)) HVVt mulmx1. }
  have HadjB' : adjmx B' = V *m adjmx B *m adjmx V.
  { by rewrite /B' (adjmxM (V *m B)) adjmxK (adjmxM V B) mulmxA. }
  have HB'comm : adjmx B' *m diag_mx d = diag_mx d *m B'.
  { rewrite HadjB'.
    rewrite -(mulmxA _ (adjmx V) (diag_mx d)) -HQV.
    rewrite -(mulmxA V (adjmx B) _).
    rewrite (mulmxA (adjmx B) Q (adjmx V)) HBcomm.
    rewrite (mulmxA V (Q *m B) (adjmx V)).
    rewrite (mulmxA V Q B) HVQ.
    rewrite -(mulmxA (diag_mx d) V B).
    by rewrite -(mulmxA (diag_mx d) _ (adjmx V)) -/B'. }
  have HB'le : adjmx B' *m B' <= diag_mx d *m diag_mx d.
  { rewrite le_lownerE.
    have Hpsd0 : Q *m Q - adjmx B *m B \is psdmx by rewrite -le_lownerE.
    suff -> : diag_mx d *m diag_mx d - adjmx B' *m B' =
              V *m (Q *m Q - adjmx B *m B) *m adjmx V.
    { exact: psdmx_bimap_closed_gen. }
    rewrite mulmxBr mulmxBl.
    congr (_ - _).
    { symmetry.
      rewrite !mulmxA HVQ -(mulmxA (diag_mx d) V Q) HVQ.
      rewrite (mulmxA (diag_mx d) (diag_mx d) V).
      by rewrite -(mulmxA (diag_mx d *m diag_mx d) V _) HVVt mulmx1. }
    { rewrite HadjB' /B' !mulmxA.
      rewrite -(mulmxA (V *m adjmx B) (adjmx V) V) HVtV mulmx1.
      done. } }
  have HB'col0 : forall i j, d 0 j = 0 -> B' i j = 0.
  { move=> i0 j0 Hdj.
    have Hpsd_diff : (diag_mx d *m diag_mx d - adjmx B' *m B') \is psdmx
      by rewrite -le_lownerE.
    have HBBjj : (adjmx B' *m B') j0 j0 = \sum_i (`|B' i j0| ^+ 2).
    { rewrite !mxE; apply eq_bigr => k _.
      by rewrite !mxE -normCKC. }
    have HD2jj : (diag_mx d *m diag_mx d) j0 j0 = 0.
    { rewrite !mxE (bigD1 j0) //= big1 ?addr0; last first.
        by move=> k kj; rewrite !mxE (negbTE kj) mulr0.
      by rewrite !mxE eqxx Hdj mul0r. }
    have Hge0 : 0 <= (diag_mx d *m diag_mx d - adjmx B' *m B') j0 j0.
    { move/psdmx_dot: Hpsd_diff => Hpd.
      move: (Hpd (delta_mx j0 0 : 'cV_(n + 1))).
      by rewrite nnegrE adjmx_delta trace_mx11 delta_mx_mulEl
        delta_mx_mulEr eqxx !mul1r. }
    have Hle0 : (adjmx B' *m B') j0 j0 <= 0.
    { have : 0 <= (diag_mx d *m diag_mx d) j0 j0 - (adjmx B' *m B') j0 j0.
      { by move: Hge0; rewrite !mxE. }
      by rewrite HD2jj sub0r oppr_ge0. }
    have Hge0' : (adjmx B' *m B') j0 j0 >= 0.
    { rewrite HBBjj. apply sumr_ge0 => k _.
      exact: exprn_ge0 (normr_ge0 _). }
    have HBBjj0 : (adjmx B' *m B') j0 j0 = 0
      by apply/eqP; rewrite eq_le Hle0 Hge0'.
    have Hsum0 : \sum_i (`|B' i j0| ^+ 2) = 0 by rewrite -HBBjj HBBjj0.
    suff: `|B' i0 j0| ^+ 2 = 0.
    { by move/eqP; rewrite expf_eq0 /= normr_eq0 => /eqP. }
    apply/eqP; rewrite eq_le; apply/andP; split.
    2: exact: exprn_ge0 (normr_ge0 _).
    rewrite -Hsum0 (bigD1 i0) //=.
    rewrite -[X in X <= _]addr0; apply lerD; first by [].
    apply sumr_ge0 => k _; exact: exprn_ge0 (normr_ge0 _). }
  pose C' : 'M[C]_(n + 1) := \matrix_(i, j)
    (if d 0 j != 0 then B' i j / d 0 j
     else if d 0 i != 0 then (B' j i)^* / d 0 i
     else 0).
  have HC'def : C' = \matrix_(i, j)
    (if d 0 j != 0 then B' i j / d 0 j
     else if d 0 i != 0 then (B' j i)^* / d 0 i
     else 0) by [].
  have HC'D : C' *m diag_mx d = B'.
  { apply/matrixP=> i j; rewrite [LHS]mxE (bigD1 j) //=.
    rewrite big1 ?addr0; last first.
    { by move=> k kj; rewrite !mxE (negbTE kj) mulr0. }
    rewrite [diag_mx d j j]mxE eqxx /C' mxE.
    case E: (d 0 j != 0); first by rewrite mulfVK.
    move/negbFE: E => /eqP Hdj0.
    by rewrite Hdj0 mulr0 (HB'col0 i j Hdj0). }
  have HC'herm : C' = adjmx C'.
  { apply/matrixP => i j.
    have HCij : C' i j = (if d 0 j != 0 then B' i j / d 0 j
      else if d 0 i != 0 then (B' j i)^* / d 0 i else 0)
      by rewrite /C' mxE.
    have HaCji : (adjmx C') i j = (C' j i)^* by rewrite !mxE.
    have HCji : C' j i = (if d 0 i != 0 then B' j i / d 0 i
      else if d 0 j != 0 then (B' i j)^* / d 0 j else 0)
      by rewrite /C' mxE.
    rewrite HCij HaCji HCji.
    case Edj: (d 0 j != 0); case Edi: (d 0 i != 0).
    - have Hcomm_ij : (B' j i)^* * d 0 j = d 0 i * B' i j.
      { have := congr1 (fun M : 'M__ => M i j) HB'comm.
        by rewrite mul_mx_diag mul_diag_mx !mxE. }
      rewrite fmorph_div.
      have Hdi_real :
        Num.Num_conj__canonical__GRing_RMorphism
          (complex_complex__canonical__Num_ClosedField R) (d 0 i) = d 0 i.
      { change (@Num.conj C (d 0 i) = d 0 i).
        exact: (Hd_real i). }
      rewrite Hdi_real.
      apply/eqP; rewrite eqr_div //; apply/eqP.
      rewrite Hcomm_ij.
      by rewrite mulrC.
    - rewrite fmorph_div.
      have HBij_conjK :
        Num.Num_conj__canonical__GRing_RMorphism
          (complex_complex__canonical__Num_ClosedField R)
          (conjC (B' i j)) = B' i j.
      { change (@Num.conj C (conjC (B' i j)) = B' i j).
        exact: conjCK. }
      have Hdj_real :
        Num.Num_conj__canonical__GRing_RMorphism
          (complex_complex__canonical__Num_ClosedField R) (d 0 j) = d 0 j.
      { change (@Num.conj C (d 0 j) = d 0 j).
        exact: (Hd_real j). }
      by rewrite HBij_conjK Hdj_real.
    - rewrite fmorph_div.
      have Hdi_real :
        Num.Num_conj__canonical__GRing_RMorphism
          (complex_complex__canonical__Num_ClosedField R) (d 0 i) = d 0 i.
      { change (@Num.conj C (d 0 i) = d 0 i).
        exact: (Hd_real i). }
      by rewrite Hdi_real.
    - by rewrite conjC0. }
  exists V, B', C', d, U, Q.
  split; first exact: HYQ.
  split; first exact: HU.
  split; first exact: HQpsd.
  split; first exact: HVu.
  split; first exact: HVtV.
  split; first exact: HVVt.
  split; first exact: HQspec.
  split; first exact: Hd_nneg.
  split; first exact: Hd_real.
  split; first by change (B' = V *m B *m adjmx V); rewrite /B'.
  split; first exact: HB'le.
  split; first exact: HB'comm.
  split; first exact: HB'col0.
  split; first exact: HC'D.
  split; first exact: HC'herm.
  by [].
Qed.

Local Lemma pd_gtd_ub_aux_PS4f2 {n : nat} : forall XX YY : 'M[C]_(n + 1),
  adjmx XX *m XX <= adjmx YY *m YY ->
  adjmx XX *m YY = adjmx YY *m XX ->
  exists (V B' C' Pi invD L A_rr Delta_sq : 'M[C]_(n + 1))
         (d : 'rV[C]_(n + 1))
         (U Q : 'M[C]_(n + 1)),
    YY = U *m Q /\ U \is unitarymx /\ Q \is psdmx /\
    V \is unitarymx /\
    adjmx V *m V = 1%:M /\ V *m adjmx V = 1%:M /\
    Q = adjmx V *m diag_mx d *m V /\
    (forall i, 0 <= d 0 i) /\ (forall j, (d 0 j)^* = d 0 j) /\
    B' = V *m (adjmx U *m XX) *m adjmx V /\
    C' *m diag_mx d = B' /\ C' = adjmx C' /\
    Pi = diag_mx (\row_j ((d 0 j != 0%R)%:R%:C : C) : 'rV_(n + 1)) /\
    invD = diag_mx (\row_j
      ((if d 0 j != 0%R then ((d 0 j)^-1)%R else 0) : C)
      : 'rV_(n + 1)) /\
    L = B' *m invD /\
    A_rr = Pi *m L *m Pi /\
    Delta_sq = Pi - A_rr *m A_rr /\
    Pi *m Pi = Pi /\ Pi = adjmx Pi /\
    (1%:M - Pi) *m (1%:M - Pi) = 1%:M - Pi /\
    1%:M - Pi = adjmx (1%:M - Pi) /\
    Pi *m (1%:M - Pi) = 0 /\ (1%:M - Pi) *m Pi = 0 /\
    invD *m diag_mx d = Pi /\ diag_mx d *m invD = Pi /\
    adjmx invD = invD /\
    L *m diag_mx d = B' /\
    L *m (1%:M - Pi) = 0 /\ (1%:M - Pi) *m adjmx L = 0 /\
    L *m Pi = L /\
    Pi *m L *m Pi = adjmx (Pi *m L *m Pi) /\
    A_rr *m A_rr = adjmx L *m Pi *m L /\
    adjmx L *m L <= Pi /\
    Delta_sq \is psdmx.
Proof.
  move=> XX YY Hle Hcomm.
  have [V [B' [C' [d [U [Q
    [HYQ [HU [HQpsd [HVu [HVtV [HVVt [HQspec [Hd_nneg [Hd_real
    [HB'def [HB'le [HB'comm [HB'col0 [HC'D [HC'herm _]]]]]]]]]]]]]]]]]]]]]
    := @pd_gtd_ub_aux_PS4f1 n XX YY Hle Hcomm.
  pose Pi : 'M[C]_(n + 1) :=
    diag_mx (\row_j (d 0 j != 0)%:R%:C : 'rV_(n + 1)).
  pose invD : 'M[C]_(n + 1) := diag_mx (\row_j
    ((if d 0 j != 0%R then ((d 0 j)^-1)%R else 0) : C)
    : 'rV_(n + 1)).
  pose L : 'M[C]_(n + 1) := B' *m invD.
  pose A_rr : 'M[C]_(n + 1) := Pi *m L *m Pi.
  pose Delta_sq : 'M[C]_(n + 1) := Pi - A_rr *m A_rr.
  have HPi_proj : Pi *m Pi = Pi.
  { apply/matrixP => i j; rewrite !mxE (bigD1 i) //= big1 ?addr0;
      last by move=> k nki; rewrite !mxE (eqtype.eq_sym i k) (negbTE nki)
                      mulr0n mul0r.
    rewrite !mxE eqxx mulr1n.
    case Hij: (i == j); last by rewrite mulr0n mulr0.
    rewrite (eqP Hij) mulr1n.
    by case: (d 0 j != 0) => /=; rewrite ?mulr1 ?mulr0. }
  have HPi_herm : Pi = adjmx Pi.
  { rewrite /Pi diag_mx_adj; congr (diag_mx _).
    apply/matrixP => i j; rewrite !mxE.
    by case: (d 0 j != 0); rewrite ?conjC1 ?conjC0. }
  have HonePi_proj : (1%:M - Pi) *m (1%:M - Pi) = 1%:M - Pi.
  { by rewrite mulmxBl mul1mx mulmxBr mulmx1 HPi_proj opprB addrA subrK. }
  have HonePi_herm : 1%:M - Pi = adjmx (1%:M - Pi).
  { by rewrite linearB /= adjmx1 -HPi_herm. }
  have HPi_onePi : Pi *m (1%:M - Pi) = 0.
  { by rewrite mulmxBr mulmx1 HPi_proj subrr. }
  have HonePi_Pi : (1%:M - Pi) *m Pi = 0.
  { by rewrite mulmxBl mul1mx HPi_proj subrr. }
  have HinvD_D : invD *m diag_mx d = Pi.
  { rewrite /invD diag_mx_dmul /Pi; congr (diag_mx _).
    apply/matrixP => i j; rewrite !mxE (ord1 i).
    case E: (d 0 j != 0); rewrite ?E /=; last by rewrite mul0r.
    by rewrite mulVf ?unitfE. }
  have HD_invD : diag_mx d *m invD = Pi.
  { rewrite /invD diag_mx_dmul /Pi; congr (diag_mx _).
    apply/matrixP => i j; rewrite !mxE (ord1 i).
    case E: (d 0 j != 0); rewrite ?E /=; last by rewrite mulr0.
    by rewrite mulfV ?unitfE. }
  have HinvD_herm : adjmx invD = invD.
  { rewrite /invD diag_mx_adj; congr (diag_mx _).
    apply/matrixP => i j; rewrite !mxE.
    case E: (d 0 j != 0); last by rewrite conjC0.
    by rewrite conjc_inv_ Hd_real. }
  have HLD : L *m diag_mx d = B' *m Pi.
  { by rewrite /L -mulmxA HinvD_D. }
  have HB'Pi : B' *m Pi = B'.
  { rewrite -HC'D -mulmxA; congr (C' *m _).
    rewrite /Pi diag_mx_dmul; congr (diag_mx _).
    apply/matrixP => i j; rewrite mxE (ord1 i) mxE.
    case E: (d 0 j != 0); rewrite /=; first by rewrite mulr1.
    move/negbFE: E => /eqP E; by rewrite E mulr0. }
  have HLD' : L *m diag_mx d = B' by rewrite HLD HB'Pi.
  have HL_onePi : L *m (1%:M - Pi) = 0.
  { rewrite mulmxBr mulmx1.
    suff -> : L *m Pi = L by rewrite subrr.
    rewrite /L -mulmxA.
    suff -> : invD *m Pi = invD by [].
    rewrite /invD /Pi diag_mx_dmul; congr (diag_mx _).
    apply/matrixP => i j; rewrite !mxE.
    by case: (d 0 j != 0) => /=; rewrite ?mulr1 ?mulr0. }
  have HonePi_adjL : (1%:M - Pi) *m adjmx L = 0.
  { have H0 : adjmx (L *m (1%:M - Pi)) = 0
      by rewrite HL_onePi adjmxE trmx0 map_mx0.
    by rewrite (adjmxM L (1%:M - Pi)) -HonePi_herm in H0. }
  have HLPi : L *m Pi = L.
  { have := HL_onePi; rewrite mulmxBr mulmx1; by move/subr0_eq. }
  have HPiLPi_herm : Pi *m L *m Pi = adjmx (Pi *m L *m Pi).
  { have HCPi_eq : C' *m Pi = L.
    { have HC'Pi : C' *m Pi = L *m Pi
        by rewrite -HD_invD !mulmxA HC'D HLD'.
      by rewrite HC'Pi HLPi. }
    suff -> : Pi *m L *m Pi = Pi *m C' *m Pi.
    { rewrite (adjmxM (Pi *m C') Pi) -HPi_herm.
      rewrite (adjmxM Pi C') -HPi_herm -HC'herm.
      by rewrite mulmxA. }
    by rewrite -(mulmxA Pi L Pi) HLPi -HCPi_eq mulmxA. }
  have HPL_eq : Pi *m L = adjmx L *m Pi.
  { have HK := HPiLPi_herm.
    rewrite -mulmxA HLPi (adjmxM Pi L) -HPi_herm in HK.
    done. }
  have HArr_sq_eq : A_rr *m A_rr = adjmx L *m Pi *m L.
  { have H1 : A_rr = adjmx L *m Pi
      by rewrite /A_rr -mulmxA HLPi HPL_eq.
    have H2 : A_rr = Pi *m L by rewrite /A_rr -mulmxA HLPi.
    rewrite {1}H1 {1}H2 -!mulmxA [X in _ *m X]mulmxA HPi_proj.
    by rewrite mulmxA. }
  have HLstL : adjmx L *m L <= Pi.
  { rewrite le_lownerE.
    suff -> : Pi - adjmx L *m L =
      invD *m (diag_mx d *m diag_mx d - adjmx B' *m B') *m invD.
    { rewrite -[X in _ *m X]HinvD_herm.
      apply: psdmx_bimap_closed_gen.
      by rewrite -le_lownerE. }
    rewrite mulmxBr mulmxBl; congr (_ - _).
    { by rewrite (mulmxA invD (diag_mx d) _) HinvD_D
        -(mulmxA Pi _ _) HD_invD HPi_proj. }
    { rewrite /L adjmxM HinvD_herm.
      rewrite (mulmxA (invD *m adjmx B') B' invD).
      by rewrite -(mulmxA invD (adjmx B') B'). } }
  have HDelta_sq_psd : Delta_sq \is psdmx.
  { have HLPiL_le : adjmx L *m Pi *m L <= adjmx L *m L.
    { rewrite le_lownerE.
      suff -> : adjmx L *m L - adjmx L *m Pi *m L =
                adjmx L *m (1%:M - Pi) *m L.
      { rewrite -[L in _ *m L]adjmxK.
        apply: psdmx_bimap_closed_gen.
        have -> : 1%:M - Pi = adjmx (1%:M - Pi) *m (1%:M - Pi)
          by rewrite -HonePi_herm HonePi_proj.
        exact: formV_psd. }
      by rewrite mulmxBr mulmx1 mulmxBl. }
    rewrite /Delta_sq HArr_sq_eq -le_lownerE.
    exact: le_trans HLPiL_le HLstL. }
  exists V, B', C', Pi, invD, L, A_rr, Delta_sq, d, U, Q.
  split; first exact: HYQ.
  split; first exact: HU.
  split; first exact: HQpsd.
  split; first exact: HVu.
  split; first exact: HVtV.
  split; first exact: HVVt.
  split; first exact: HQspec.
  split; first exact: Hd_nneg.
  split; first exact: Hd_real.
  split; first by [].
  split; first exact: HC'D.
  split; first exact: HC'herm.
  split; first by [].
  split; first by [].
  split; first by [].
  split; first by [].
  split; first by [].
  split; first exact: HPi_proj.
  split; first exact: HPi_herm.
  split; first exact: HonePi_proj.
  split; first exact: HonePi_herm.
  split; first exact: HPi_onePi.
  split; first exact: HonePi_Pi.
  split; first exact: HinvD_D.
  split; first exact: HD_invD.
  split; first exact: HinvD_herm.
  split; first exact: HLD'.
  split; first exact: HL_onePi.
  split; first exact: HonePi_adjL.
  split; first exact: HLPi.
  split; first exact: HPiLPi_herm.
  split; first exact: HArr_sq_eq.
  split; first exact: HLstL.
  exact: HDelta_sq_psd.
Qed.

(* path: utils:pd_gtd_ub_aux_PS4f5 -> utils:pd_gtd_ub -> utils:pd_gtd_ub' -> *)
(*   entropy:smooth_hmax_attained -> entropy:smooth_hmaxE_EFin -> *)
(*   bb84:bb84_secret *)
Local Lemma pd_gtd_ub_aux_PS4f5 {n : nat}
  (H_PS4f2 :
    forall XX YY : 'M[C]_(n + 1),
      adjmx XX *m XX <= adjmx YY *m YY ->
      adjmx XX *m YY = adjmx YY *m XX ->
      exists (V B' C' Pi invD L A_rr Delta_sq : 'M[C]_(n + 1))
             (d : 'rV[C]_(n + 1))
             (U Q : 'M[C]_(n + 1)),
        YY = U *m Q /\ U \is unitarymx /\ Q \is psdmx /\
        V \is unitarymx /\
        adjmx V *m V = 1%:M /\ V *m adjmx V = 1%:M /\
        Q = adjmx V *m diag_mx d *m V /\
        (forall i, 0 <= d 0 i) /\ (forall j, (d 0 j)^* = d 0 j) /\
        B' = V *m (adjmx U *m XX) *m adjmx V /\
        C' *m diag_mx d = B' /\ C' = adjmx C' /\
        Pi = diag_mx (\row_j ((d 0 j != 0%R)%:R%:C : C) : 'rV_(n + 1)) /\
        invD = diag_mx (\row_j
          ((if d 0 j != 0%R then ((d 0 j)^-1)%R else 0) : C)
          : 'rV_(n + 1)) /\
        L = B' *m invD /\
        A_rr = Pi *m L *m Pi /\
        Delta_sq = Pi - A_rr *m A_rr /\
        Pi *m Pi = Pi /\ Pi = adjmx Pi /\
        (1%:M - Pi) *m (1%:M - Pi) = 1%:M - Pi /\
        1%:M - Pi = adjmx (1%:M - Pi) /\
        Pi *m (1%:M - Pi) = 0 /\ (1%:M - Pi) *m Pi = 0 /\
        invD *m diag_mx d = Pi /\ diag_mx d *m invD = Pi /\
        adjmx invD = invD /\
        L *m diag_mx d = B' /\
        L *m (1%:M - Pi) = 0 /\ (1%:M - Pi) *m adjmx L = 0 /\
        L *m Pi = L /\
        Pi *m L *m Pi = adjmx (Pi *m L *m Pi) /\
        A_rr *m A_rr = adjmx L *m Pi *m L /\
        adjmx L *m L <= Pi /\
        Delta_sq \is psdmx) :
  forall XX YY : 'M[C]_(n + 1),
    adjmx XX *m XX <= adjmx YY *m YY ->
    adjmx XX *m YY = adjmx YY *m XX ->
    exists (Pi L A_rr Delta F G_op V B' U Q : 'M[C]_(n + 1))
           (d : 'rV[C]_(n + 1)),
      Pi *m Pi = Pi /\ Pi = adjmx Pi /\
      L *m Pi = L /\ A_rr = Pi *m L *m Pi /\
      Delta *m Delta = Pi - A_rr *m A_rr /\
      Delta = adjmx Delta /\
      F = (1%:M - Pi) *m L /\
      G_op = (1%:M - Pi) *m L *m pinvmx_ Delta /\
      adjmx G_op *m G_op <= 1%:M /\
      G_op *m adjmx G_op <= 1%:M /\
      F = G_op *m Delta /\
      (* Algebraic prerequisites: A_rr hermitian, commutation with Delta,   *)
      (* nilpotent links with the orthogonal complement (1 - Pi).            *)
      A_rr = adjmx A_rr /\
      A_rr = adjmx L *m Pi /\ A_rr = Pi *m L /\
      Pi *m A_rr = A_rr /\ A_rr *m Pi = A_rr /\
      (1%:M - Pi) *m Delta = 0 /\ Delta *m (1%:M - Pi) = 0 /\
      Pi *m Delta = Delta /\ Delta *m Pi = Delta /\
      A_rr *m Delta = Delta *m A_rr /\
      L *m (1%:M - Pi) = 0 /\ (1%:M - Pi) *m adjmx L = 0 /\
      (* Spectral linkage: U/V unitary, polar(YY)=U*Q,                       *)
      (* spectral(Q)=V^*t*diag d*V, B'=V*(U^*t*XX)*V^*t, L*diag d=B'.       *)
      U \is unitarymx /\ V \is unitarymx /\
      adjmx U *m U = 1%:M /\ U *m adjmx U = 1%:M /\
      adjmx V *m V = 1%:M /\ V *m adjmx V = 1%:M /\
      YY = U *m Q /\ Q = adjmx V *m diag_mx d *m V /\
      B' = V *m (adjmx U *m XX) *m adjmx V /\
      L *m diag_mx d = B' /\ Pi *m diag_mx d = diag_mx d.
Proof.
  move=> XX YY Hle Hcomm.
  have [V [B' [C' [Pi [invD [L [A_rr [Delta_sq [d [U [Q
    [HYQ_p [HU_p [HQpsd_p [HVu_p [HVtV_p [HVVt_p [HQspec_p [_ [_ [HB'def_p
    [_ [_ [HPi_def_p [_ [_
    [HArr_def [HDsq_def
    [HPi_proj [HPi_herm [_ [HonePi_herm [HPi_onePi [HonePi_Pi
    [_ [_ [_ [HLD'_p [HL_onePi [HonePi_adjL [HLPi [HPiLPi_herm
    [HArr_sq_eq [HLstL HDelta_sq_psd
    ]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]
    := H_PS4f2 XX YY Hle Hcomm.
  pose Delta : 'M[C]_(n + 1) := sqrtmx Delta_sq.
  pose F : 'M[C]_(n + 1) := (1%:M - Pi) *m L.
  pose G_op : 'M[C]_(n + 1) := (1%:M - Pi) *m L *m pinvmx_ Delta.
  have HDelta_sq : Delta *m Delta = Delta_sq.
  { rewrite /Delta. exact: sqrtmxK HDelta_sq_psd. }
  have HDelta_sq_eq : Delta *m Delta = Pi - A_rr *m A_rr.
  { by rewrite HDelta_sq HDsq_def. }
  have HDelta_herm : Delta = adjmx Delta.
  { apply/hermmxP; exact: sqrtmx_herm (psdmx_herm HDelta_sq_psd). }
  (* HadjFF : adjmx F * F = adjmx L * L - A_rr * A_rr *)
  have HadjFF : adjmx F *m F = adjmx L *m L - A_rr *m A_rr.
  { have HadjF_eq : adjmx F = adjmx L *m (1%:M - Pi)
      by rewrite /F adjmxM -HonePi_herm.
    rewrite HadjF_eq /F -mulmxA.
    rewrite (mulmxA (1%:M - Pi) (1%:M - Pi) L).
    have HonePi_proj : (1%:M - Pi) *m (1%:M - Pi) = 1%:M - Pi.
    { by rewrite mulmxBl mul1mx mulmxBr mulmx1 HPi_proj opprB addrA subrK. }
    rewrite HonePi_proj.
    have H1 : (1%:M - Pi) *m L = L - Pi *m L.
    { rewrite mulmxBl.
      congr (_ - _).
      exact: mul1mx. }
    rewrite H1 mulmxBr.
    congr (_ - _).
    by rewrite mulmxA; exact: esym HArr_sq_eq. }
  (* HadjFF_le : adjmx F * F <= Delta * Delta *)
  have HadjFF_le : adjmx F *m F <= Delta *m Delta.
  { rewrite HadjFF HDelta_sq_eq.
    exact: lev_add2rP HLstL. }
  (* --- HadjGG_le : adjmx G_op *m G_op <= 1%:M --- *)
  have HadjGG_le : adjmx G_op *m G_op <= 1%:M.
  { (* Delta * pinvmx_ Delta = suppmx Delta (Hermitian Delta) *)
    have HDpinv_supp : Delta *m pinvmx_ Delta = suppmx Delta.
    { have /hermmxP Hsh := suppmx_herm Delta.
      have Hgen0 : forall n0 (A0 B0 : 'M[C]_n0),
        B0 = B0^*t -> (B0 *m A0) = (A0^*t *m B0)^*t.
      { move=> n0 A0 B0 HB.
        by rewrite adjmxM adjmxK -HB. }
      rewrite (Hgen0 _ (pinvmx_ Delta) _ HDelta_herm).
      by rewrite -/suppmx Hsh. }
    (* adjG*G = adj(pinvmx) * (adjF*F) * pinvmx *)
    have HadjGG_form : adjmx G_op *m G_op =
      adjmx (pinvmx_ Delta) *m (adjmx F *m F) *m pinvmx_ Delta.
    { have Hgen : forall n0 (A0 D0 : 'M[C]_n0),
        adjmx (A0 *m D0) *m (A0 *m D0) =
        adjmx D0 *m (adjmx A0 *m A0) *m D0.
      { move=> n0 A0 D0.
        by rewrite adjmxM !mulmxA. }
      rewrite /G_op /F. exact: Hgen. }
    (* adj(pinv) * (Delta*Delta) * pinv = suppmx Delta *)
    have Hsupp_eq : adjmx (pinvmx_ Delta) *m (Delta *m Delta) *m
      pinvmx_ Delta = suppmx Delta.
    { have Hsd : (pinvmx_ Delta)^*t *m Delta = suppmx Delta
        by rewrite /suppmx.
      have Hgen_a : forall n0 (A0 B0 C0 D0 : 'M[C]_n0),
        A0 *m (B0 *m C0) *m D0 = (A0 *m B0) *m (C0 *m D0).
      { move=> n0 A0 B0 C0 D0. by rewrite !mulmxA. }
      rewrite (Hgen_a _ _ Delta Delta _) Hsd HDpinv_supp.
      have /projmxP_id [_ Hid] := suppmx_proj Delta.
      exact: Hid. }
    (* suppmx Delta <= 1 (projector is observable, hence <= 1) *)
    have Hsupp_le : suppmx Delta <= 1%:M.
    { have Hobs := projmx_obs (suppmx_proj Delta).
      rewrite obsmx_psd_eq in Hobs.
      by have /andP [_ Hub] := Hobs; rewrite le_lownerE. }
    apply: (le_trans _ Hsupp_le).
    rewrite HadjGG_form le_lownerE -Hsupp_eq.
    (* adj(pinv) * (Delta*Delta - adjF*F) * pinv is psdmx *)
    have Hgen : forall n0 (A0 B0 M0 N0 : 'M[C]_n0),
      A0 *m M0 *m B0 - A0 *m N0 *m B0 =
      A0 *m (M0 - N0) *m B0.
    { move=> n0 A0 B0 M0 N0.
      by rewrite -mulmxBl -mulmxBr. }
    rewrite (Hgen _ (adjmx (pinvmx_ Delta)) (pinvmx_ Delta)).
    have HadjmxK0 : forall n0 (A0 : 'M[C]_n0), A0 = adjmx (adjmx A0).
    { move=> n0 A0. by rewrite adjmxK. }
    rewrite [X in _ *m X](HadjmxK0 _ (pinvmx_ Delta)).
    apply: psdmx_bimap_closed_gen.
    by rewrite -le_lownerE. }
  (* --- HF_GD : F = G_op *m Delta --- *)
  have HF_GD : F = G_op *m Delta.
  { (* pinvmx_ Delta *m Delta = cosuppmx Delta *)
    have Hcosup_eq : pinvmx_ Delta *m Delta = cosuppmx Delta.
    { have /hermmxP Hch := cosuppmx_herm Delta.
      have Hgen0 : forall n0 (A0 B0 : 'M[C]_n0),
        B0 = B0^*t -> (A0 *m B0) = (B0 *m A0^*t)^*t.
      { move=> n0 A0 B0 HB.
        by rewrite adjmxM adjmxK -HB. }
      rewrite (Hgen0 _ (pinvmx_ Delta) _ HDelta_herm).
      by rewrite -/cosuppmx Hch. }
    (* (1 - cosuppmx Delta) * Delta = 0 *)
    have HoneCosup_D : (1%:M - cosuppmx Delta) *m Delta = 0.
    { by rewrite mulmxBl mul1mx (cosuppmx_id Delta) subrr. }
    (* (1 - cosuppmx Delta) hermitian *)
    have HoneCosup_herm :
      1%:M - cosuppmx Delta = adjmx (1%:M - cosuppmx Delta).
    { have /hermmxP Hch := cosuppmx_herm Delta.
      by rewrite linearB /= adjmx1 -Hch. }
    set Q0 := 1%:M - cosuppmx Delta.
    (* Q0 * (adjF*F) * Q0 = 0 via psd-eq0 squeeze *)
    have HQ_adjFF_0 : Q0 *m (adjmx F *m F) *m Q0 = 0.
    { have QaFFQ_psd : Q0 *m (adjmx F *m F) *m Q0 \is psdmx.
      { have Hp := formV_psd F.
        rewrite [X in _ *m X]HoneCosup_herm.
        exact: psdmx_bimap_closed_gen Hp. }
      have QD2Q_0 : Q0 *m (Delta *m Delta) *m Q0 = 0.
      { have Hgen_assoc : forall n0 (A0 B0 C0 D0 : 'M[C]_n0),
          A0 *m (B0 *m C0) *m D0 = (A0 *m B0) *m (C0 *m D0).
        { move=> n0 A0 B0 C0 D0. by rewrite !mulmxA. }
        by rewrite (Hgen_assoc _ Q0 Delta Delta Q0) HoneCosup_D mul0mx. }
      have QD2Q_le :
        Q0 *m (Delta *m Delta) *m Q0 - Q0 *m (adjmx F *m F) *m Q0 \is psdmx.
      { have Hgen : forall n0 (A0 B0 M0 N0 : 'M[C]_n0),
          A0 *m M0 *m B0 - A0 *m N0 *m B0 =
          A0 *m (M0 - N0) *m B0.
        { move=> n0 A0 B0 M0 N0.
          by rewrite -mulmxBl -mulmxBr. }
        rewrite (Hgen _ Q0 Q0).
        rewrite [X in _ *m X]HoneCosup_herm.
        apply: psdmx_bimap_closed_gen.
        by rewrite -le_lownerE. }
      apply: psdmx_eq0 QaFFQ_psd _.
      by rewrite -[X in X \is psdmx]sub0r -QD2Q_0. }
    (* F * Q0 = 0 via formV_tr_eq0 *)
    have HF_oncosup0 : F *m Q0 = 0.
    { apply: formV_tr_eq0.
      have Hgen_formV : forall n0 (A0 B0 : 'M[C]_n0),
        B0 = B0^*t -> B0 *m B0 = B0 ->
        \tr ((A0 *m B0)^*t *m (A0 *m B0)) =
        \tr (B0 *m (A0^*t *m A0) *m B0).
      { move=> n0 A0 B0 HB HBidem.
        by rewrite adjmxM -HB !mulmxA. }
      have /projmxP_id [_ Hid] := cosuppmx_proj Delta.
      have HQ_proj : Q0 *m Q0 = Q0.
      { rewrite /Q0 mulmxBl mul1mx mulmxBr mulmx1 Hid subrr subr0 //. }
      rewrite (Hgen_formV _ _ _ HoneCosup_herm HQ_proj).
      rewrite -/Q0 HQ_adjFF_0. by rewrite linear0. }
    (* F = F * cosuppmx Delta = G_op * Delta *)
    have HF_cosup : F *m cosuppmx Delta = F.
    { move: HF_oncosup0; rewrite /Q0 mulmxBr mulmx1 => /eqP.
      by rewrite subr_eq0 => /eqP. }
    rewrite -HF_cosup -Hcosup_eq /G_op /F.
    by rewrite -(mulmxA ((1%:M - Pi) *m L) (pinvmx_ Delta) Delta). }
  (* --- HGadjG_le : G_op * adjmx G_op <= 1%:M --- *)
  (* Stated as a polymorphic local `have` so the size argument is a fresh   *)
  (* `n`, avoiding the `n + 1` vs `(dim H).+1` cast issue in                 *)
  (* `i2norm_existsr`.                                                       *)
  have HformV_le_of_form_le :
    forall (n : nat) (M : 'M[C]_n),
    adjmx M *m M <= 1%:M -> M *m adjmx M <= 1%:M.
  { move=> nn M HM.
    case: nn M HM => [M _ | nn M HM ].
    { by rewrite !mx_dim0E le_lownerE subr0 psdmx0. }
    (* form_le_i2norm_sq applied to adjmx M:                         *)
    (*   M *m adjmx M = (adjmx M)^*t *m (adjmx M) <= \i2|adjmx M|^+2 *: 1.  *)
    have Hi2_bound : M *m adjmx M <= (\i2| M | ^+ 2) *: (1%:M : 'M[C]_nn.+1).
    { (* inline form_le_i2norm_sq for A := adjmx M *)
      have HMad : M *m adjmx M = (adjmx M)^*t *m adjmx M by rewrite adjmxK.
      rewrite HMad -(i2norm_adjmx M).
      set Aux := adjmx M.
      rewrite le_lownerE.
      set Vsv := svd_v Aux. set dsv := svds_d Aux.
      have HVu : Vsv \is unitarymx := svd_v_unitarymx Aux.
      set Usv := svd_u Aux.
      have HUu : Usv \is unitarymx := svd_u_unitarymx Aux.
      have HAtA : Aux^*t *m Aux =
        Vsv *m diag_mx (map_mx Num.conj dsv .* dsv) *m Vsv^*t.
      { rewrite (svdsE Aux).
        rewrite -/Usv -/Vsv -/dsv.
        rewrite !adjmxM adjmxK.
        rewrite !mulmxA.
        rewrite mulmxKtV ?HUu//.
        rewrite mulmxACA.
        by rewrite diag_mx_adj diag_mx_dmul. }
      have HcI : (\i2| Aux | ^+ 2) *: (1%:M : 'M[C]_nn.+1) =
        Vsv *m ((\i2| Aux | ^+ 2) *: 1%:M) *m Vsv^*t.
      { by rewrite -scalemxAr -scalemxAl mulmx1 (unitarymxP HVu). }
      rewrite HcI HAtA -mulmxBl -mulmxBr.
      set Esv := map_mx Num.conj dsv .* dsv.
      set newD := \row_(j < nn.+1) ((\i2| Aux | ^+ 2) - Esv 0 j).
      suff -> :
        (\i2| Aux | ^+ 2) *: (1%:M : 'M[C]_nn.+1) - diag_mx Esv = diag_mx newD.
      { apply: nneg_form.
        apply/nnegmxP => i j.
        rewrite /newD /Esv !mxE /= nnegrE subr_ge0.
        rewrite (geC0_conj (svds_d_ge0 Aux 0 j)) -/dsv -expr2.
        rewrite i2normsE_Sn /dsv ler_pXn2r ?nnegrE ?svds_d_ge0//.
        by apply/rv_nincrP/leq0n; exact/svd_diag_nincr/svds_d_svd_diag. }
      apply/matrixP => i j; rewrite /newD !mxE.
      by case: eqP => [->|_]; rewrite ?mulr1 ?mulr1n ?mulr0 ?mulr0n ?subr0. }
    (* \i2| M | ^+ 2 <= 1, derived from HM via i2norm_existsr.       *)
    have Hi2_le1 : ((\i2| M | ^+ 2) : C) <= 1.
    { move: (i2norm_existsr M 0) => [v Hv1 Hv2].
      have Hpsd0 : (1%:M - adjmx M *m M) \is psdmx by move: HM; rewrite le_lownerE.
      move/psdmx_dot: Hpsd0 => /(_ v) Hdot.
      move: Hdot. rewrite nnegrE.
      rewrite mulmxBr mulmxBl mulmx1 linearB /=.
      have Htr_eq : \tr (v ^*t *m (adjmx M *m M) *m v) =
                    \tr ((M *m v) ^*t *m (M *m v))
        by rewrite adjmxM -!mulmxA.
      rewrite Htr_eq !dotV_l2norm Hv1 Hv2 expr1n.
      by rewrite subr_ge0. }
    (* combine via le_trans + psdmxZ.                                *)
    apply: (le_trans Hi2_bound).
    rewrite le_lownerE -{1}(scale1r (1%:M : 'M[C]_nn.+1)) -scalerBl.
    apply: psdmxZ; last exact: psdmx1.
    by rewrite subr_ge0. }
  have HGadjG_le : G_op *m adjmx G_op <= 1%:M
    := HformV_le_of_form_le _ _ HadjGG_le.
  (* === Algebraic prerequisites for the contraction bound. === *)
  have HArr_herm : A_rr = adjmx A_rr.
  { rewrite {1}HArr_def HPiLPi_herm.
    by congr (adjmx _); rewrite -HArr_def. }
  have HPL_eq : Pi *m L = adjmx L *m Pi.
  { have HK := HPiLPi_herm.
    rewrite -mulmxA HLPi (adjmxM Pi L) -HPi_herm in HK.
    done. }
  have HArrE2 : A_rr = Pi *m L by rewrite HArr_def -mulmxA HLPi.
  have HArrE1 : A_rr = adjmx L *m Pi.
  { by rewrite HArr_def -mulmxA HLPi HPL_eq. }
  have HPi_Arr : Pi *m A_rr = A_rr by rewrite HArrE2 mulmxA HPi_proj.
  have HArr_Pi : A_rr *m Pi = A_rr by rewrite HArrE1 -mulmxA HPi_proj.
  have HArr_comm_Dsq :
    A_rr *m (Pi - A_rr *m A_rr) = (Pi - A_rr *m A_rr) *m A_rr.
  { by rewrite mulmxBr mulmxBl HPi_Arr HArr_Pi !mulmxA. }
  have HonePi_Delta : (1%:M - Pi) *m Delta = 0.
  { have HPi_Dsq : Pi *m Delta_sq = Delta_sq.
    { rewrite HDsq_def mulmxBr HPi_proj mulmxA HPi_Arr //. }
    have HDsq_Pi : Delta_sq *m Pi = Delta_sq.
    { have /hermmxP HDsq_h := psdmx_herm HDelta_sq_psd.
      by rewrite {1}HDsq_h {1}HPi_herm -adjmxM HPi_Dsq -HDsq_h. }
    apply: form_tr_eq0.
    have HsqK := sqrtmxK HDelta_sq_psd. rewrite -/Delta in HsqK.
    have HonePi_Dsq : (1%:M - Pi) *m Delta_sq = 0.
    { by rewrite mulmxBl mul1mx HPi_Dsq subrr. }
    have Hgen : forall n0 (P0 D0 : 'M[C]_n0),
      P0 = adjmx P0 -> D0 = adjmx D0 ->
      (P0 *m D0) *m (P0 *m D0) ^*t = P0 *m (D0 *m D0) *m P0.
    { move=> n0 P0 D0 HP HD.
      by rewrite adjmxM -HD -HP -!mulmxA [X in _ *m X]mulmxA. }
    rewrite (Hgen _ _ _ HonePi_herm HDelta_herm) HsqK HonePi_Dsq.
    by rewrite mul0mx linear0. }
  have HDelta_onePi : Delta *m (1%:M - Pi) = 0.
  { by rewrite {1}HDelta_herm {1}HonePi_herm -adjmxM HonePi_Delta
      linear0. }
  have HPi_compl : Pi + (1%:M - Pi) = 1%:M :> 'M[C]_(n + 1).
  { by apply/matrixP => i j; rewrite !mxE addrC subrK. }
  have HPi_Delta : Pi *m Delta = Delta.
  { rewrite -[RHS]mul1mx -HPi_compl mulmxDl.
    by rewrite HonePi_Delta addr0. }
  have HDelta_Pi : Delta *m Pi = Delta.
  { by rewrite {1}HDelta_herm {1}HPi_herm -adjmxM HPi_Delta
      -HDelta_herm. }
  (* Spectral commutativity: A_rr *m Delta = Delta *m A_rr (port of f4).   *)
  have HArr_comm_D : A_rr *m Delta = Delta *m A_rr.
  { have HDsq_herm0 : Delta_sq \is hermmx := psdmx_herm HDelta_sq_psd.
    set Ed := eigenmx Delta_sq. set dd := spectral_diag Delta_sq.
    have HEdu : Ed \is unitarymx := eigen_unitarymx Delta_sq.
    have HEdEdt : Ed *m Ed^*t = 1%:M := unitarymxK HEdu.
    have HEdtu : Ed^*t \is unitarymx by rewrite trmxC_unitary.
    have /eigen_dec := hermitian_normalmx HDsq_herm0.
    rewrite -/Ed -/dd => Hspec.
    have HArr_Dsq_concrete : A_rr *m Delta_sq = Delta_sq *m A_rr.
    { by rewrite HDsq_def; exact: HArr_comm_Dsq. }
    have HArr_conj_comm :
      (Ed^*t *m A_rr *m Ed) *m diag_mx dd =
      diag_mx dd *m (Ed^*t *m A_rr *m Ed).
    { have HEig : Ed^*t *m Delta_sq *m Ed = diag_mx dd.
      { rewrite Hspec !mulmxA unitarymxKV// mul1mx -mulmxA.
        by rewrite unitarymxKV// mulmx1. }
      rewrite -HEig.
      have Hgen : forall n0 (E0 A0 D0 : 'M[C]_n0),
        E0 *m E0^*t = 1%:M ->
        A0 *m D0 = D0 *m A0 ->
        (E0^*t *m A0 *m E0) *m (E0^*t *m D0 *m E0) =
        (E0^*t *m D0 *m E0) *m (E0^*t *m A0 *m E0).
      { move=> n0 E0 A0 D0 HEEt Hcomm0.
        rewrite !mulmxA -(mulmxA (E0^*t *m A0) E0 (E0^*t)) HEEt mulmx1.
        rewrite -(mulmxA (E0^*t *m D0) E0 (E0^*t)) HEEt mulmx1.
        by rewrite -(mulmxA (E0^*t) A0 D0) Hcomm0
          (mulmxA (E0^*t) D0 A0). }
      exact: Hgen _ _ _ _ HEdEdt HArr_Dsq_concrete. }
    set f := fun x : C => (Num.sqrt (@complex.Re R x))%:C.
    have HDelta_mapf : Delta = mapf_mx f Delta_sq.
    { rewrite /Delta /sqrtmx mapf_mx.unlock.
      have Hrow : \row_i (Num.sqrt (@complex.Re R
        (spectral_diag Delta_sq 0 i)))%:C =
          map_mx f (spectral_diag Delta_sq).
      { by apply/matrixP => i j; rewrite !mxE /f;
          have -> : i = 0 by exact: ord1. }
      by rewrite Hrow. }
    have HEig_sqrt : Ed *m diag_mx (map_mx f dd) *m Ed^*t = Delta.
    { rewrite HDelta_mapf.
      have Hspec2 : (Ed^*t)^*t *m diag_mx dd *m Ed^*t = Delta_sq
        by rewrite adjmxK -Hspec.
      have := mapf_mx_unique f HEdtu Hspec2.
      by rewrite adjmxK => ->. }
    have HArr_conj_comm_f :
      (Ed^*t *m A_rr *m Ed) *m diag_mx (map_mx f dd) =
      diag_mx (map_mx f dd) *m (Ed^*t *m A_rr *m Ed).
    { set U0 := Ed^*t *m A_rr *m Ed.
      apply/matrixP => a b; apply/eqP.
      have := HArr_conj_comm; rewrite -/U0 => Hcd.
      move: Hcd => /matrixP/(_ a b)/eqP.
      rewrite !mul_mx_diag !mul_diag_mx !mxE mulrC -subr_eq0 -mulrBl
              mulf_eq0.
      move=>/orP[|/eqP->]; last by rewrite mulr0 mul0r.
      by rewrite subr_eq0 => /eqP Hdij; rewrite Hdij mulrC. }
    have Hgen : forall n0 (E0 B0 D0 : 'M[C]_n0),
      E0 *m E0^*t = 1%:M ->
      (E0^*t *m B0 *m E0) *m D0 = D0 *m (E0^*t *m B0 *m E0) ->
      B0 *m (E0 *m D0 *m E0^*t) = (E0 *m D0 *m E0^*t) *m B0.
    { move=> n0 E0 B0 D0 HEEt0 Hcomm0.
      have HLHS : B0 *m (E0 *m D0 *m E0^*t) =
                  E0 *m ((E0^*t *m B0 *m E0) *m D0) *m E0^*t.
      { symmetry; rewrite !mulmxA HEEt0 mul1mx //. }
      have HRHS : (E0 *m D0 *m E0^*t) *m B0 =
                  E0 *m (D0 *m (E0^*t *m B0 *m E0)) *m E0^*t.
      { symmetry; rewrite !mulmxA -mulmxA HEEt0 mulmx1 //. }
      by rewrite HLHS HRHS Hcomm0. }
    rewrite -HEig_sqrt.
    exact: Hgen _ _ _ _ HEdEdt HArr_conj_comm_f. }
  have HPi_diagd : Pi *m diag_mx d = diag_mx d.
  { rewrite HPi_def_p diag_mx_dmul; congr (diag_mx _).
    apply/matrixP => i j; rewrite !mxE (ord1 i).
    by case: (d 0 j =P 0) => [->|_]; rewrite ?mulr0 ?mul1r. }
  exists Pi, L, A_rr, Delta, F, G_op, V, B', U, Q, d.
  split; first exact: HPi_proj.
  split; first exact: HPi_herm.
  split; first exact: HLPi.
  split; first exact: HArr_def.
  split; first exact: HDelta_sq_eq.
  split; first exact: HDelta_herm.
  split; first by [].
  split; first by [].
  split; first exact: HadjGG_le.
  split; first exact: HGadjG_le.
  split; first exact: HF_GD.
  split; first exact: HArr_herm.
  split; first exact: HArrE1.
  split; first exact: HArrE2.
  split; first exact: HPi_Arr.
  split; first exact: HArr_Pi.
  split; first exact: HonePi_Delta.
  split; first exact: HDelta_onePi.
  split; first exact: HPi_Delta.
  split; first exact: HDelta_Pi.
  split; first exact: HArr_comm_D.
  split; first exact: HL_onePi.
  split; first exact: HonePi_adjL.
  split; first exact: HU_p.
  split; first exact: HVu_p.
  split; first exact: (unitarymxKV HU_p).
  split; first exact: (unitarymxK HU_p).
  split; first exact: HVtV_p.
  split; first exact: HVVt_p.
  split; first exact: HYQ_p.
  split; first exact: HQspec_p.
  split; first exact: HB'def_p.
  split; first exact: HLD'_p.
  exact: HPi_diagd.
Qed.

(* path: utils:pd_gtd_ub_aux_PS4f6 -> utils:pd_gtd_ub -> utils:pd_gtd_ub' -> *)
(*   entropy:smooth_hmax_attained -> entropy:smooth_hmaxE_EFin -> *)
(*   bb84:bb84_secret *)
Local Lemma pd_gtd_ub_aux_PS4f6 {n : nat}
  (H_PS4f5 :
    forall XX YY : 'M[C]_(n + 1),
      adjmx XX *m XX <= adjmx YY *m YY ->
      adjmx XX *m YY = adjmx YY *m XX ->
      exists (Pi L A_rr Delta F G_op V B' U Q : 'M[C]_(n + 1))
             (d : 'rV[C]_(n + 1)),
        Pi *m Pi = Pi /\ Pi = adjmx Pi /\
        L *m Pi = L /\ A_rr = Pi *m L *m Pi /\
        Delta *m Delta = Pi - A_rr *m A_rr /\
        Delta = adjmx Delta /\
        F = (1%:M - Pi) *m L /\
        G_op = (1%:M - Pi) *m L *m pinvmx_ Delta /\
        adjmx G_op *m G_op <= 1%:M /\
        G_op *m adjmx G_op <= 1%:M /\
        F = G_op *m Delta /\
        (* Algebraic prerequisites: A_rr hermitian, commutation with Delta.   *)
        A_rr = adjmx A_rr /\
        A_rr = adjmx L *m Pi /\ A_rr = Pi *m L /\
        Pi *m A_rr = A_rr /\ A_rr *m Pi = A_rr /\
        (1%:M - Pi) *m Delta = 0 /\ Delta *m (1%:M - Pi) = 0 /\
        Pi *m Delta = Delta /\ Delta *m Pi = Delta /\
        A_rr *m Delta = Delta *m A_rr /\
        L *m (1%:M - Pi) = 0 /\ (1%:M - Pi) *m adjmx L = 0 /\
        (* Spectral linkage: U/V unitary, polar(YY)=U*Q,                       *)
        (* spectral(Q)=V^*t*diag d*V, B'=V*(U^*t*XX)*V^*t, L*diag d=B'.       *)
        U \is unitarymx /\ V \is unitarymx /\
        adjmx U *m U = 1%:M /\ U *m adjmx U = 1%:M /\
        adjmx V *m V = 1%:M /\ V *m adjmx V = 1%:M /\
        YY = U *m Q /\ Q = adjmx V *m diag_mx d *m V /\
        B' = V *m (adjmx U *m XX) *m adjmx V /\
        L *m diag_mx d = B' /\ Pi *m diag_mx d = diag_mx d) :
  forall XX YY : 'M[C]_(n + 1),
    adjmx XX *m XX <= adjmx YY *m YY ->
    adjmx XX *m YY = adjmx YY *m XX ->
    exists (Pi L A_rr Delta F G_op T_kernel C'f V B' U Q
            : 'M[C]_(n + 1)) (d : 'rV[C]_(n + 1)),
      Pi *m Pi = Pi /\ Pi = adjmx Pi /\
      L *m Pi = L /\ A_rr = Pi *m L *m Pi /\
      Delta *m Delta = Pi - A_rr *m A_rr /\
      Delta = adjmx Delta /\
      F = (1%:M - Pi) *m L /\
      G_op = (1%:M - Pi) *m L *m pinvmx_ Delta /\
      adjmx G_op *m G_op <= 1%:M /\
      G_op *m adjmx G_op <= 1%:M /\
      F = G_op *m Delta /\
      T_kernel = - ((1%:M - Pi) *m G_op *m A_rr *m adjmx G_op
                    *m (1%:M - Pi)) /\
      C'f = adjmx C'f /\
      adjmx C'f *m C'f <= 1%:M /\
      (* Spectral linkage. *)
      U \is unitarymx /\ V \is unitarymx /\
      adjmx U *m U = 1%:M /\ U *m adjmx U = 1%:M /\
      adjmx V *m V = 1%:M /\ V *m adjmx V = 1%:M /\
      YY = U *m Q /\ Q = adjmx V *m diag_mx d *m V /\
      B' = V *m (adjmx U *m XX) *m adjmx V /\
      C'f *m diag_mx d = B'.
Proof.
  move=> XX YY Hle Hcomm.
  (* Re-derive the witness (Pi, L, A_rr, Delta, F, G_op and algebraic facts  *)
  (* HArr_D_sum, HArr_comm_D, HPi_Delta, etc.).  Construct T_kernel and C'f  *)
  (* from these, prove the PSD bound, and re-package.                        *)
  have [Pi [L [A_rr [Delta [F [G_op [V [B' [U [Q [d
    [HPi_proj [HPi_herm [HLPi [HArr_def [HDelta_sq_eq
    [HDelta_herm [HFdef [HG_def [HadjGG_le [HGadjG_le
    [HF_GD [HArr_herm [HArrE1 [HArrE2 [HPi_Arr [HArr_Pi
    [HonePi_Delta [HDelta_onePi [HPi_Delta [HDelta_Pi
    [HArr_comm_D [HL_onePi0 [HonePi_L0
    [HU [HVu [HUtU [HUU [HVtV [HVVt [HYQ [HQspec [HB'def [HLD' HPi_diagd
    ]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]
    := H_PS4f5 XX YY Hle Hcomm.
  pose T_kernel : 'M[C]_(n + 1) :=
    - ((1%:M - Pi) *m G_op *m A_rr *m adjmx G_op *m (1%:M - Pi)).
  (* C'f := L + adjF + T_kernel.  Equivalently L + (1-Pi)*adjL + T_kernel. *)
  pose C'f : 'M[C]_(n + 1) := L + adjmx F + T_kernel.
  have HT_def :
    T_kernel = - ((1%:M - Pi) *m G_op *m A_rr *m adjmx G_op
                  *m (1%:M - Pi)) by [].
  have HonePi_proj : (1%:M - Pi) *m (1%:M - Pi) = 1%:M - Pi.
  { by rewrite mulmxBl mul1mx mulmxBr mulmx1 HPi_proj opprB addrA subrK. }
  have HonePi_herm : 1%:M - Pi = adjmx (1%:M - Pi).
  { by rewrite linearB /= adjmx1 -HPi_herm. }
  have HPi_onePi : Pi *m (1%:M - Pi) = 0.
  { by rewrite mulmxBr mulmx1 HPi_proj subrr. }
  have HonePi_Pi : (1%:M - Pi) *m Pi = 0.
  { by rewrite mulmxBl mul1mx HPi_proj subrr. }
  have HPi_compl : Pi + (1%:M - Pi) = 1%:M :> 'M[C]_(n + 1).
  { by apply/matrixP => i j; rewrite !mxE addrC subrK. }
  have HArr_D_sum : A_rr *m A_rr + Delta *m Delta = Pi.
  { by rewrite HDelta_sq_eq addrC subrK. }
  have HT_herm : T_kernel = adjmx T_kernel.
  { rewrite /T_kernel linearN /=; congr (- _).
    rewrite (adjmxM _ (1%:M - Pi)) -HonePi_herm.
    rewrite (adjmxM _ (adjmx G_op)) adjmxK.
    rewrite (adjmxM _ A_rr) -HArr_herm.
    rewrite (adjmxM _ G_op) -HonePi_herm.
    by rewrite !mulmxA. }
  (* G is a contraction (key tool for the main bound)                        *)
  have HG_contr : forall (v : 'cV[C]_(n + 1)),
    \tr ((G_op *m v)^*t *m (G_op *m v)) <= \tr (v^*t *m v).
  { move=> v.
    have Hpsd1 : (1%:M - adjmx G_op *m G_op) \is psdmx
      by move: HadjGG_le; rewrite le_lownerE.
    have Hdot1 := psdmx_dot _ Hpsd1 v.
    move: Hdot1; rewrite nnegrE.
    have Heq : \tr (v ^*t *m (1%:M - adjmx G_op *m G_op) *m v) =
               \tr (v ^*t *m v) - \tr ((G_op *m v)^*t *m (G_op *m v)).
    { rewrite mulmxBr mulmxBl mulmx1 linearB /=.
      congr (_ - _).
      by rewrite adjmxM -!mulmxA [X in \tr X]mulmxA. }
    by rewrite Heq subr_ge0. }
  have HC'f_herm : C'f = adjmx C'f.
  { rewrite /C'f !linearD /= adjmxK -HT_herm.
    (* Goal: L + adjF + T = adjL + F + T, i.e. L + adjF = adjL + F.          *)
    congr (_ + _).
    rewrite HFdef adjmxM -HonePi_herm.
    rewrite mulmxBl mulmxBr mul1mx mulmx1.
    rewrite -HArrE1 -HArrE2.
    (* Goal: L + (adjL - A_rr) = adjL + (L - A_rr) *)
    by rewrite addrA [L + adjmx L]addrC -addrA. }
  (* Structural prerequisites for the main bound (HC'f_sq + block facts).   *)
  have HC'fPi : C'f *m Pi = L.
  { rewrite /C'f !mulmxDl HLPi.
    suff -> : adjmx F *m Pi = 0.
    { suff -> : T_kernel *m Pi = 0 by rewrite !addr0.
      rewrite /T_kernel.
      pose Ktd := (1%:M - Pi) *m G_op *m A_rr *m adjmx G_op.
      change (- (Ktd *m (1%:M - Pi)) *m Pi = 0).
      by rewrite mulNmx -mulmxA HonePi_Pi mulmx0 oppr0. }
    rewrite HFdef adjmxM -HonePi_herm.
    by rewrite -mulmxA HonePi_Pi mulmx0. }
  have HPiC'f : Pi *m C'f = adjmx L
    by rewrite HC'f_herm {1}HPi_herm -adjmxM HC'fPi.
  have HT_onePi : T_kernel *m (1%:M - Pi) = T_kernel.
  { rewrite /T_kernel.
    pose Ktd := (1%:M - Pi) *m G_op *m A_rr *m adjmx G_op.
    change (- (Ktd *m (1%:M - Pi)) *m (1%:M - Pi) =
      - (Ktd *m (1%:M - Pi))).
    rewrite mulNmx; congr (- _).
    by rewrite -mulmxA HonePi_proj. }
  have HC'f_onePi : C'f *m (1%:M - Pi) = adjmx F + T_kernel.
  { rewrite /C'f !mulmxDl HL_onePi0 add0r HT_onePi.
    congr (_ + _).
    rewrite HFdef adjmxM -HonePi_herm.
    by rewrite -mulmxA HonePi_proj. }
  have HonePi_C'f : (1%:M - Pi) *m C'f = F + T_kernel.
  { rewrite -{1}[_ *m C'f]adjmxK adjmxM -HC'f_herm -HonePi_herm.
    rewrite HC'f_onePi linearD /= adjmxK.
    by rewrite -HT_herm. }
  have HLFT : L *m (F + T_kernel) = 0
    by rewrite -HonePi_C'f mulmxA HL_onePi0 mul0mx.
  have HadjFTadjL : (adjmx F + T_kernel) *m adjmx L = 0
    by rewrite -HC'f_onePi -mulmxA HonePi_L0 mulmx0.
  have HC'f_sq : C'f *m C'f = L *m adjmx L
                            + (adjmx F + T_kernel) *m (F + T_kernel).
  { transitivity ((C'f *m Pi) *m C'f + (C'f *m (1%:M - Pi)) *m C'f).
    { by rewrite -mulmxDl -mulmxDr HPi_compl mulmx1. }
    rewrite HC'fPi HC'f_onePi.
    have HLC'f : L *m C'f = L *m adjmx L.
    { transitivity (L *m (Pi *m C'f) + L *m ((1%:M - Pi) *m C'f)).
      { by rewrite -mulmxDr -mulmxDl HPi_compl mul1mx. }
      by rewrite HPiC'f HonePi_C'f HLFT addr0. }
    have HadjFTC'f : (adjmx F + T_kernel) *m C'f =
      (adjmx F + T_kernel) *m (F + T_kernel).
    { transitivity ((adjmx F + T_kernel) *m (Pi *m C'f) +
                    (adjmx F + T_kernel) *m ((1%:M - Pi) *m C'f)).
      { by rewrite -mulmxDr -mulmxDl HPi_compl mul1mx. }
      by rewrite HPiC'f HonePi_C'f HadjFTadjL add0r. }
    by rewrite HLC'f HadjFTC'f. }
  (* === Main bound: 1 - C'f^2 is PSD via psdmx_dot ===                       *)
  (* Strategy:                                                                  *)
  (*  1. set p := Pi*u, q := (1-Pi)*u, w := adjG*q.                             *)
  (*  2. Decompose: u = p + q (HPi_compl); ||u||^2 = ||p||^2 + ||q||^2 (Horth). *)
  (*  3. Block-rewrite C'f-actions:                                              *)
  (*       adjL*u = A_rr*p + Delta*w (HadjLu_eq, via HadjF_DadjG: adjF=Delta*adjG)*)
  (*       (F+T)*u = G*(Delta*p - A_rr*w) (HFTu_eq, via HF_GD + HT_ker).         *)
  (*  4. Reduce trace identity:                                                  *)
  (*       \tr(u^*t (1 - C'f^2) u)                                               *)
  (*       = ||p||^2 + ||q||^2 - ||A_rr*p + Delta*w||^2                          *)
  (*                            - ||G*(Delta*p - A_rr*w)||^2.                    *)
  (*  5. HG_contr drops G: replace ||G*v||^2 with the upper bound ||v||^2.      *)
  (*  6. Cross-cancellation (commutativity of A_rr/Delta):                       *)
  (*       ||A_rr*p+Delta*w||^2 + ||Delta*p-A_rr*w||^2 = ||p||^2 + ||Pi*w||^2.  *)
  (*  7. HPi_w (Pi*w = w, since suppmx Delta * adjG = adjG via HadjF_DadjG) +  *)
  (*     Hw_le_q (||w||^2 <= ||q||^2 from HG_contr applied to adjG) close it.   *)
  have HC'f_contr : adjmx C'f *m C'f <= 1%:M.
  { rewrite -HC'f_herm le_lownerE.
    suff Hpsd : (1%:M - C'f *m C'f) \is psdmx by exact: Hpsd.
    apply/psdmx_dot => u; rewrite nnegrE.
    rewrite HC'f_sq.
    have HadjF_eq : adjmx F = adjmx L *m (1%:M - Pi).
    { by rewrite HFdef adjmxM -HonePi_herm. }
    have HadjF_DadjG : adjmx F = Delta *m adjmx G_op.
    { by rewrite HF_GD adjmxM -HDelta_herm. }
    have HT_ker : forall (q : 'cV[C]_(n + 1)),
      (1%:M - Pi) *m q = q ->
      T_kernel *m q = - (G_op *m A_rr *m adjmx G_op *m q).
    { move=> q Hq. rewrite HT_def mulNmx; congr (- _).
      have HonePi_G : (1%:M - Pi) *m G_op = G_op.
      { by rewrite HG_def !mulmxA HonePi_proj. }
      have Hgen : forall n0 (P0 G0 A0 Ga : 'M[C]_n0) (q0 : 'cV_n0),
        P0 *m G0 = G0 -> P0 *m q0 = q0 ->
        P0 *m G0 *m A0 *m Ga *m P0 *m q0 = G0 *m A0 *m Ga *m q0.
      { move=> n0 P0 G0 A0 Ga q0 HPG HPq0.
        by rewrite HPG -mulmxA HPq0. }
      exact: Hgen _ _ _ _ _ _ HonePi_G Hq. }
    set p := Pi *m u. set q := (1%:M - Pi) *m u.
    have Hu_pq : u = p + q.
    { by rewrite /p /q -mulmxDl HPi_compl mul1mx. }
    have Horth : \tr (u ^*t *m u) = \tr (p ^*t *m p) + \tr (q ^*t *m q).
    { have Hgen : forall n0 (P : 'M[C]_n0) (v : 'cV_n0),
        P *m P = P -> P = adjmx P ->
        \tr ((P *m v) ^*t *m ((1%:M - P) *m v)) = 0.
      { move=> n0 P0 v0 Hproj Hherm.
        rewrite adjmxM -Hherm -(mulmxA (v0 ^*t)) (mulmxA P0).
        by rewrite mulmxBr mulmx1 Hproj subrr mul0mx mulmx0 linear0. }
      rewrite {1}Hu_pq adjmxD mulmxDl !Hu_pq !mulmxDr !linearD /=.
      rewrite (Hgen _ _ _ HPi_proj HPi_herm).
      have Hgen2 : \tr (q ^*t *m p) = 0.
      { suff -> : \tr (q ^*t *m p) = (\tr (p ^*t *m q))^* by
          rewrite (Hgen _ _ _ HPi_proj HPi_herm) conjC0.
        have Hgen3 : forall m0 (A0 B0 : 'cV[C]_m0),
          \tr (A0 ^*t *m B0) = (\tr (B0 ^*t *m A0))^*.
        { move=> m0 A0 B0.
          by rewrite -mxtrace_adj adjmxM adjmxK. }
        exact: Hgen3. }
      by rewrite Hgen2 !addr0 add0r. }
    have HadjL_u : adjmx L *m u = A_rr *m p + adjmx F *m q.
    { rewrite Hu_pq mulmxDr.
      congr (_ + _).
      - by rewrite /p !mulmxA -HArrE1 HArr_Pi.
      - by rewrite HadjF_eq /q -(mulmxA (adjmx L))
             (mulmxA (1%:M - Pi) (1%:M - Pi)) HonePi_proj. }
    have HFT_u : (F + T_kernel) *m u = F *m p + T_kernel *m q.
    { rewrite Hu_pq mulmxDr mulmxDl mulmxDl.
      have HFq : F *m q = 0.
      { rewrite /q mulmxA HFdef.
        rewrite -(mulmxA (1%:M - Pi) L (1%:M - Pi)) HL_onePi0.
        by rewrite mulmx0 mul0mx. }
      have HTp : T_kernel *m p = 0.
      { rewrite HT_def mulNmx; apply/eqP; rewrite oppr_eq0; apply/eqP.
        have HonePi_p : (1%:M - Pi) *m p = 0
          by rewrite /p mulmxA HonePi_Pi mul0mx.
        have Hgen : forall n0 (P0 G0 A0 Ga : 'M[C]_n0) (v : 'cV_n0),
          P0 *m v = 0 ->
          P0 *m G0 *m A0 *m Ga *m P0 *m v = 0.
        { move=> n0 P0 G0 A0 Ga v Hpv.
          by rewrite -!mulmxA Hpv !mulmx0. }
        exact: Hgen _ _ _ _ _ _ HonePi_p. }
      rewrite HFq HTp.
      rewrite addr0 add0r.
      reflexivity. }
    set w := adjmx G_op *m q.
    have HadjFq : adjmx F *m q = Delta *m w.
    { by rewrite /w HadjF_DadjG !mulmxA. }
    have HTq_eq : T_kernel *m q = - (G_op *m A_rr *m w).
    { have Hq_ker : (1%:M - Pi) *m q = q
        by rewrite /q mulmxA HonePi_proj.
      rewrite (HT_ker q Hq_ker) /w !mulmxA //. }
    have HFp : F *m p = G_op *m (Delta *m p).
    { by rewrite HF_GD !mulmxA. }
    have HFTu_eq : (F + T_kernel) *m u
      = G_op *m (Delta *m p - A_rr *m w).
    { have Hgen : forall n0 (G0 A0 : 'M[C]_n0) (a b : 'cV_n0),
        G0 *m a + - (G0 *m A0 *m b) = G0 *m (a - A0 *m b).
      { move=> n0 G0 A0 a b. by rewrite mulmxBr mulmxA. }
      by rewrite HFT_u HFp HTq_eq (Hgen _ G_op A_rr). }
    have HadjLu_eq : adjmx L *m u = A_rr *m p + Delta *m w.
    { by rewrite HadjL_u HadjFq. }
    have Hstep : \tr (u ^*t *m (1%:M - (L *m adjmx L +
      (adjmx F + T_kernel) *m (F + T_kernel))) *m u) =
      \tr (p ^*t *m p) + \tr (q ^*t *m q) -
      \tr ((adjmx L *m u) ^*t *m (adjmx L *m u)) -
      \tr (((F + T_kernel) *m u) ^*t *m ((F + T_kernel) *m u)).
    { have HadjFT : adjmx (F + T_kernel) = adjmx F + T_kernel.
      { by rewrite linearD /= -HT_herm. }
      rewrite -HadjFT.
      have Hgen : forall n0 (M1 M2 : 'M[C]_n0) (v : 'cV_n0),
        \tr (v ^*t *m (1%:M - (M1 *m adjmx M1 + adjmx M2 *m M2)) *m v) =
        \tr (v ^*t *m v) - \tr ((adjmx M1 *m v) ^*t *m (adjmx M1 *m v)) -
        \tr ((M2 *m v) ^*t *m (M2 *m v)).
      { move=> n0 M1 M2 v.
        rewrite mulmxBr mulmxBl mulmx1 mulmxDr mulmxDl.
        rewrite !linearB linearD /=.
        rewrite opprD addrA.
        congr (_ - _ - _).
        - by rewrite adjmxM adjmxK -!mulmxA [X in \tr X]mulmxA.
        - by rewrite adjmxM -!mulmxA [X in \tr X]mulmxA. }
      rewrite (Hgen _ L (F + T_kernel) u).
      congr (_ - _ - _); first exact: Horth.
      all: by []. }
    rewrite Hstep. clear Hstep.
    rewrite HadjLu_eq HFTu_eq.
    have Hcross_cancel :
      \tr ((A_rr *m p + Delta *m w) ^*t *m (A_rr *m p + Delta *m w)) +
      \tr ((Delta *m p - A_rr *m w) ^*t *m (Delta *m p - A_rr *m w)) =
      \tr (p ^*t *m p) + \tr (w ^*t *m (Pi *m w)).
    { have Hgen_expand : forall n0 (H1 H2 P0 : 'M[C]_n0) (a b : 'cV_n0),
        H1 = adjmx H1 -> H2 = adjmx H2 -> H1 *m H2 = H2 *m H1 ->
        H1 *m H1 + H2 *m H2 = P0 ->
        \tr ((H1 *m a + H2 *m b) ^*t *m (H1 *m a + H2 *m b)) +
        \tr ((H2 *m a - H1 *m b) ^*t *m (H2 *m a - H1 *m b)) =
        \tr (a ^*t *m (P0 *m a)) + \tr (b ^*t *m (P0 *m b)).
      { move=> n0 H1 H2 P0 a b HH1 HH2 Hcomm0 Hsum.
        have Hgen_adj_add : forall (M1 M2 : 'M[C]_n0) (v0 w0 : 'cV_n0),
          M1 = adjmx M1 -> M2 = adjmx M2 ->
          adjmx (M1 *m v0 + M2 *m w0) = v0 ^*t *m M1 + w0 ^*t *m M2.
        { move=> M1 M2 v0 w0 HM1 HM2.
          by rewrite adjmxD !adjmxM -HM1 -HM2. }
        have Hgen_adj_neg : forall m1 m2 (A0 : 'M[C]_(m1,m2)),
          (- A0) ^*t = - A0 ^*t.
        { move=> m1 m2 A0. apply/matrixP => i j.
          by rewrite !mxE rmorphN. }
        have Hgen_mulmxN : forall m1 m2 m3 (A0 : 'M[C]_(m1,m2))
          (B0 : 'M[C]_(m2,m3)),
          A0 *m (- B0) = - (A0 *m B0).
        { move=> m1 m2 m3 A0 B0. apply/matrixP => i j.
          rewrite !mxE -sumrN. apply: eq_bigr => k _.
          by rewrite !mxE mulrN. }
        have Hgen_adj_sub : forall (M1 M2 : 'M[C]_n0) (v0 w0 : 'cV_n0),
          M1 = adjmx M1 -> M2 = adjmx M2 ->
          adjmx (M1 *m v0 - M2 *m w0) = v0 ^*t *m M1 - w0 ^*t *m M2.
        { move=> M1 M2 v0 w0 HM1 HM2.
          have -> : M1 *m v0 - M2 *m w0 = M1 *m v0 + M2 *m (- w0).
          { by rewrite Hgen_mulmxN. }
          rewrite (Hgen_adj_add M1 M2 v0 (- w0) HM1 HM2).
          by rewrite Hgen_adj_neg mulNmx. }
        have Hmat_id :
          (a ^*t *m H1 + b ^*t *m H2) *m (H1 *m a + H2 *m b) +
          (a ^*t *m H2 - b ^*t *m H1) *m (H2 *m a - H1 *m b) =
          a ^*t *m (P0 *m a) + b ^*t *m (P0 *m b).
        { have Hprod1 : (a ^*t *m H1 + b ^*t *m H2)
                          *m (H1 *m a + H2 *m b) =
            a ^*t *m H1 *m (H1 *m a) + a ^*t *m H1 *m (H2 *m b) +
            (b ^*t *m H2 *m (H1 *m a) + b ^*t *m H2 *m (H2 *m b)).
          { by rewrite mulmxDl !mulmxDr. }
          have Hprod2 : (a ^*t *m H2 - b ^*t *m H1)
                          *m (H2 *m a - H1 *m b) =
            a ^*t *m H2 *m (H2 *m a) - a ^*t *m H2 *m (H1 *m b) -
            (b ^*t *m H1 *m (H2 *m a) - b ^*t *m H1 *m (H1 *m b)).
          { by rewrite mulmxBl !mulmxBr. }
          rewrite Hprod1 Hprod2.
          have Hgen_rassoc : forall (r : 'rV[C]_n0) (M1 M2 : 'M[C]_n0)
            (v0 : 'cV_n0),
            r *m M1 *m (M2 *m v0) = r *m (M1 *m M2) *m v0.
          { move=> r M1 M2 v0. by rewrite !mulmxA. }
          rewrite !(Hgen_rassoc (a ^*t)) !(Hgen_rassoc (b ^*t)).
          rewrite Hcomm0 -Hsum.
          have Hgen_dist2 : forall (r : 'rV[C]_n0) (M1 M2 : 'M[C]_n0)
            (v0 : 'cV_n0),
            r *m ((M1 + M2) *m v0) = r *m (M1 *m v0) + r *m (M2 *m v0).
          { move=> r M1 M2 v0. by rewrite mulmxDl mulmxDr. }
          rewrite !(Hgen_dist2 (a ^*t)) !(Hgen_dist2 (b ^*t)).
          rewrite !mulmxA opprB.
          have gen_cancel :
            forall (T : zmodType) (a1 b1 c1 d1 a2 b2 : T),
            (a1 + b1 + (c1 + d1)) + (a2 + - b1 + (b2 + - c1)) =
              (a1 + a2) + (b2 + d1).
          { move=> T x1 x2 x3 x4 x5 x6.
            rewrite addrACA [x1 + x2 + _]addrACA subrr addr0.
            congr (_ + _).
            by rewrite [x3 + _]addrC addrACA subrr addr0 addrC. }
          by rewrite gen_cancel. }
        rewrite (Hgen_adj_add _ _ _ _ HH1 HH2).
        rewrite (Hgen_adj_sub _ _ _ _ HH2 HH1).
        by rewrite -linearD Hmat_id linearD. }
      rewrite (Hgen_expand _ A_rr Delta Pi p w
                 HArr_herm HDelta_herm HArr_comm_D HArr_D_sum).
      congr (_ + _).
      have HPi_p : Pi *m p = p
        by rewrite /p mulmxA HPi_proj.
      by rewrite HPi_p. }
    have Hw_le_q : \tr (w ^*t *m w) <= \tr (q ^*t *m q).
    { have /psdmx_dot Hdot : (1%:M - G_op *m adjmx G_op) \is psdmx
        by rewrite -le_lownerE.
      move: (Hdot q); rewrite nnegrE.
      have Hgen : forall n0 (M0 : 'M[C]_n0) (v : 'cV_n0),
        \tr (v ^*t *m (1%:M - M0 *m adjmx M0) *m v) =
        \tr (v ^*t *m v) - \tr ((adjmx M0 *m v) ^*t *m (adjmx M0 *m v)).
      { move=> n0 M0 v.
        rewrite mulmxBr mulmxBl mulmx1 linearB /=.
        congr (_ - _).
        by rewrite mulmxA adjmxM adjmxK -!mulmxA [X in \tr X]mulmxA. }
      rewrite (Hgen _ G_op q) -/w.
      by rewrite subr_ge0. }
    have HPi_w : Pi *m w = w.
    { have Hsupp_Pi : suppmx Delta *m Pi = suppmx Delta
        by rewrite /suppmx -mulmxA HDelta_Pi.
      have HPi_supp : Pi *m suppmx Delta = suppmx Delta.
      { have Hsupp_herm : suppmx Delta = adjmx (suppmx Delta)
          by exact/hermmxP/suppmx_herm.
        have H0 : adjmx (suppmx Delta *m Pi) = adjmx (suppmx Delta)
          by rewrite Hsupp_Pi.
        rewrite adjmxM -HPi_herm -Hsupp_herm in H0; exact: H0. }
      have Hsupp_adjG : suppmx Delta *m adjmx G_op = adjmx G_op.
      { have HadjG_eq : adjmx G_op =
          adjmx (pinvmx_ Delta) *m adjmx L *m (1%:M - Pi)
          by rewrite HG_def !adjmxM -HonePi_herm !mulmxA.
        rewrite /suppmx.
        have Hgen_assoc3 : forall (A0 B0 C0 : 'M[C]_(n + 1)),
          A0 *m B0 *m C0 = A0 *m (B0 *m C0)
          by move=> *; rewrite mulmxA.
        rewrite (Hgen_assoc3 _ _ (adjmx G_op)).
        rewrite -HadjF_DadjG HadjF_eq mulmxA.
        by rewrite -HadjG_eq. }
      have HPi_adjG : Pi *m adjmx G_op = adjmx G_op
        by rewrite -Hsupp_adjG mulmxA HPi_supp.
      by rewrite /w mulmxA HPi_adjG. }
    set s1 := \tr ((A_rr *m p + Delta *m w) ^*t
                     *m (A_rr *m p + Delta *m w)).
    set s2_raw := Delta *m p - A_rr *m w.
    have Hle_s2 :
      \tr ((G_op *m s2_raw) ^*t *m (G_op *m s2_raw))
        <= \tr (s2_raw ^*t *m s2_raw)
      by exact: HG_contr s2_raw.
    have Hgoal :
      \tr (p ^*t *m p) + \tr (q ^*t *m q) - s1 -
      \tr ((G_op *m s2_raw) ^*t *m (G_op *m s2_raw)) >=
      \tr (p ^*t *m p) + \tr (q ^*t *m q) - s1 -
      \tr (s2_raw ^*t *m s2_raw)
      by rewrite lerD2l lerN2.
    apply: (le_trans _ Hgoal).
    have -> : \tr (p ^*t *m p) + \tr (q ^*t *m q) - s1 -
                \tr (s2_raw ^*t *m s2_raw) =
              \tr (q ^*t *m q) - \tr (w ^*t *m w).
    { have Hcc := Hcross_cancel.
      rewrite /s1 /s2_raw in Hcc *.
      rewrite HPi_w in Hcc.
      have Hgen : forall (a b c s10 s20 : C),
        s10 + s20 = a + c -> a + b - s10 - s20 = b - c.
      { move=> a0 b0 c0 s10 s20 Hsum.
        by rewrite -addrA -opprD Hsum opprD addrACA subrr add0r. }
      exact: Hgen _ _ _ _ _ Hcc. }
    by rewrite subr_ge0. }
  (* HC'fD : C'f *m diag_mx d = B'.  The L*diag d term gives B' (HLD');       *)
  (* the adjmx F * diag d and T_kernel * diag d pieces vanish via             *)
  (* (1-Pi)*diag d = 0 (= HPi_diagd) and HonePi_L0.                           *)
  have HonePi_diagd : (1%:M - Pi) *m diag_mx d = 0.
  { by rewrite mulmxBl mul1mx HPi_diagd subrr. }
  have HC'fD : C'f *m diag_mx d = B'.
  { rewrite /C'f !mulmxDl HLD'.
    suff -> : adjmx F *m diag_mx d = 0.
    { suff -> : T_kernel *m diag_mx d = 0 by rewrite !addr0.
      rewrite /T_kernel.
      pose Ktd := (1%:M - Pi) *m G_op *m A_rr *m adjmx G_op.
      change (- (Ktd *m (1%:M - Pi)) *m diag_mx d = 0).
      rewrite mulNmx -mulmxA HonePi_diagd.
      by rewrite mulmx0 oppr0. }
    rewrite HFdef adjmxM -HonePi_herm -mulmxA HonePi_diagd.
    by rewrite mulmx0. }
  exists Pi, L, A_rr, Delta, F, G_op, T_kernel, C'f, V, B', U, Q, d.
  split; first exact: HPi_proj.
  split; first exact: HPi_herm.
  split; first exact: HLPi.
  split; first exact: HArr_def.
  split; first exact: HDelta_sq_eq.
  split; first exact: HDelta_herm.
  split; first exact: HFdef.
  split; first exact: HG_def.
  split; first exact: HadjGG_le.
  split; first exact: HGadjG_le.
  split; first exact: HF_GD.
  split; first exact: HT_def.
  split; first exact: HC'f_herm.
  split; first exact: HC'f_contr.
  split; first exact: HU.
  split; first exact: HVu.
  split; first exact: HUtU.
  split; first exact: HUU.
  split; first exact: HVtV.
  split; first exact: HVVt.
  split; first exact: HYQ.
  split; first exact: HQspec.
  split; first exact: HB'def.
  exact: HC'fD.
Qed.

Local Lemma pd_gtd_ub_aux_PS4f7 {n : nat} : forall XX YY : 'M[C]_(n + 1),
  adjmx XX *m XX <= adjmx YY *m YY ->
  adjmx XX *m YY = adjmx YY *m XX ->
  exists K : 'M[C]_(n + 1),
    XX = K *m YY /\ K = adjmx K /\ adjmx K *m K <= 1%:M.
Proof.
  have H_PS4f5 := pd_gtd_ub_aux_PS4f5 (@pd_gtd_ub_aux_PS4f2 n).
  have H_PS4f6 := pd_gtd_ub_aux_PS4f6 H_PS4f5.
  move=> XX YY Hle Hcomm.
  have [Pi [L [A_rr [Delta [F [G_op [T_kernel [C'f [V [B' [U [Q [d
    [_ [_ [_ [_ [_ [_ [_ [_ [_ [_ [_ [_ [HC'f_herm [HC'f_contr
    [HU [_ [HUtU [HUU [HVtV [HVVt [HYQ [HQspec [HB'def HC'fD
    ]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]
    := H_PS4f6 XX YY Hle Hcomm.
  pose Cfull : 'M[C]_(n + 1) := adjmx V *m C'f *m V.
  pose K : 'M[C]_(n + 1) := U *m Cfull *m adjmx U.
  have HCfullQ : Cfull *m Q = adjmx U *m XX.
  { (* Use Cfull = adjmx V *m C'f *m V and Q = adjmx V *m diag_mx d *m V.   *)
    (* Cfull *m Q = adjmx V *m C'f *m (V *m adjmx V) *m diag_mx d *m V       *)
    (*           = adjmx V *m (C'f *m diag_mx d) *m V                        *)
    (*           = adjmx V *m B' *m V                                         *)
    (*           = (adjmx V *m V) *m (adjmx U *m XX) *m (adjmx V *m V)       *)
    (*           = adjmx U *m XX.                                             *)
    have HCQ_eq : Cfull *m Q =
      adjmx V *m (C'f *m diag_mx d) *m V.
    { rewrite /Cfull HQspec.
      have -> : adjmx V *m C'f *m V *m (adjmx V *m diag_mx d *m V) =
                adjmx V *m C'f *m (V *m adjmx V) *m (diag_mx d *m V)
        by rewrite !mulmxA.
      by rewrite HVVt mulmx1 !mulmxA. }
    rewrite HCQ_eq HC'fD HB'def.
    have -> : adjmx V *m (V *m (adjmx U *m XX) *m adjmx V) *m V =
              (adjmx V *m V) *m (adjmx U *m XX) *m (adjmx V *m V)
      by rewrite !mulmxA.
    by rewrite HVtV mul1mx mulmx1. }
  have HXeq : XX = K *m YY.
  { rewrite /K HYQ.
    have -> : U *m Cfull *m adjmx U *m (U *m Q) =
              U *m Cfull *m (adjmx U *m U) *m Q by rewrite !mulmxA.
    rewrite HUtU mulmx1 -mulmxA HCfullQ.
    by rewrite mulmxA HUU mul1mx. }
  have HCfull_herm : Cfull = adjmx Cfull.
  { rewrite /Cfull (adjmxM (adjmx V *m C'f) V).
    rewrite (adjmxM (adjmx V) C'f) adjmxK.
    by rewrite -mulmxA -HC'f_herm mulmxA. }
  have HK_herm : K = adjmx K.
  { rewrite /K (adjmxM (U *m Cfull) (adjmx U)) adjmxK.
    rewrite (adjmxM U Cfull) -HCfull_herm.
    by rewrite mulmxA. }
  have HK_contr : adjmx K *m K <= 1%:M.
  { rewrite le_lownerE.
    have Hadj_UCU : adjmx K = U *m adjmx Cfull *m adjmx U.
    { rewrite /K (adjmxM (U *m Cfull) (adjmx U)) adjmxK.
      by rewrite (adjmxM U Cfull) mulmxA. }
    have Hadj_Cf_sq : adjmx Cfull *m Cfull =
      adjmx V *m (adjmx C'f *m C'f) *m V.
    { rewrite /Cfull (adjmxM (adjmx V *m C'f) V) (adjmxM (adjmx V) C'f).
      rewrite adjmxK.
      transitivity (adjmx V *m (adjmx C'f *m (V *m adjmx V) *m C'f) *m V).
      { by rewrite !mulmxA. }
      by rewrite HVVt mulmx1. }
    have Hadj_K_K : adjmx K *m K =
      U *m (adjmx V *m (adjmx C'f *m C'f) *m V) *m adjmx U.
    { rewrite Hadj_UCU /K.
      transitivity (U *m (adjmx Cfull *m ((adjmx U *m U) *m Cfull)) *m
                      adjmx U).
      { set A0 := adjmx Cfull.
        set B0 := Cfull.
        set W := adjmx U.
        by rewrite ![in LHS]mulmxA ![in RHS]mulmxA. }
      by rewrite HUtU mul1mx Hadj_Cf_sq. }
    have HUVVtU : U *m (adjmx V *m V) *m adjmx U = 1%:M.
    { by rewrite HVtV mulmx1 HUU. }
    have Hexp : 1%:M - adjmx K *m K =
      U *m (adjmx V *m (1%:M - adjmx C'f *m C'f) *m V) *m adjmx U.
    { rewrite Hadj_K_K.
      have Hin : adjmx V *m (1%:M - adjmx C'f *m C'f) *m V =
        adjmx V *m V - adjmx V *m (adjmx C'f *m C'f) *m V
        by rewrite mulmxBr mulmx1 mulmxBl.
      rewrite Hin.
      have HBL : U *m (adjmx V *m V - adjmx V *m (adjmx C'f *m C'f) *m V)
                   *m adjmx U =
        U *m (adjmx V *m V) *m adjmx U
          - U *m (adjmx V *m (adjmx C'f *m C'f) *m V) *m adjmx U
        by rewrite mulmxBr mulmxBl.
      by rewrite HBL HUVVtU. }
    rewrite Hexp.
    have HMpsd : (adjmx V *m (1%:M - adjmx C'f *m C'f) *m V) \is psdmx.
    { rewrite -[V in _ *m V]adjmxK.
      apply: psdmx_bimap_closed_gen.
      by rewrite -le_lownerE. }
    exact: psdmx_bimap_closed_gen HMpsd. }
  exists K. split; first exact: HXeq.
  split; first exact: HK_herm.
  exact: HK_contr.
Qed.

(* Matrix Powers-Stormer/Fuchs-van-de-Graaf bound for normalized PSD states.      *)
(* This is the substantive proof-engineering split used by pd_gtd_ub: the large  *)
(* contraction-witness construction is sealed here, so the public purified-      *)
(* distance theorem does not carry the full Powers-Stormer proof term.           *)
(* path: utils:pd_gtd_ub_powers_stormer_mx -> utils:pd_gtd_ub -> *)
(*   utils:pd_gtd_ub' -> entropy:smooth_hmax_attained -> *)
(*   entropy:smooth_hmaxE_EFin -> *)
(*   bb84:bb84_secret *)
Local Lemma pd_gtd_ub_powers_stormer_mx {n : nat}
    (rho tau : 'M[C]_(n + 1)) :
  rho \is psdmx -> tau \is psdmx ->
  @complex.Re R (\tr rho) = 1 -> @complex.Re R (\tr tau) = 1 ->
  1 - @complex.Re R (trnorm (rho - tau)) / 2%:R <=
  @complex.Re R (trnorm (sqrtmx rho *m sqrtmx tau)).
Proof.
  move=> Hrho_psd Htau_psd Hrho_tr_eq1 Htau_tr_eq1.
  pose Srho := sqrtmx rho.
  pose Stau := sqrtmx tau.
  pose Mdiff := rho - tau.
  pose Dbar : R := @complex.Re R (trnorm Mdiff) / 2%:R.
  change (1 - Dbar <= @complex.Re R (trnorm (Srho *m Stau))).
  have Hrho_realtr : \tr rho \is Num.real
    by apply: ger0_real; exact: psdmx_trace Hrho_psd.
  have Htau_realtr : \tr tau \is Num.real
    by apply: ger0_real; exact: psdmx_trace Htau_psd.
  have Hrho_eq1 : \tr rho = 1
    by rewrite -(RRe_real Hrho_realtr) Hrho_tr_eq1.
  have Htau_eq1 : \tr tau = 1
    by rewrite -(RRe_real Htau_realtr) Htau_tr_eq1.
  have HSrho_psd : Srho \is psdmx := sqrtmx_psd Hrho_psd.
  have HStau_psd : Stau \is psdmx := sqrtmx_psd Htau_psd.
  have HSrho_herm : Srho \is hermmx := psdmx_herm HSrho_psd.
  have HStau_herm : Stau \is hermmx := psdmx_herm HStau_psd.
  have HSrho_adj : Srho ^*t = Srho := esym (hermmxP _ HSrho_herm).
  have HStau_adj : Stau ^*t = Stau := esym (hermmxP _ HStau_herm).
  have H_polar :
    exists (U : 'M[C]_(n + 1)) (P0 : 'M[C]_(n + 1)),
      Srho *m Stau = U *m P0 /\
      U \is unitarymx /\
      P0 \is psdmx /\
      P0 = sqrtmx ((Srho *m Stau)^*t *m (Srho *m Stau)).
  { have [P0 [U0 [HP0_psd [HP0_sq [HU0_adj_uni HM_eq]]]]]
      := polar_UP (Srho *m Stau) (leqnn (n + 1)).
    have HU0_uni : U0 \is unitarymx
      by move: HU0_adj_uni; rewrite adjmx_unitary.
    exists U0, P0; do ! split.
    - exact: HM_eq.
    - exact: HU0_uni.
    - exact: HP0_psd.
    - by rewrite -HP0_sq sqrtmx_psd_square. }
  have H_PS4c : forall A B : 'M[C]_(n + 1),
    (adjmx A *m B) \is psdmx ->
    adjmx (A - B) *m (A - B) <= adjmx (A + B) *m (A + B) /\
    adjmx (A - B) *m (A + B) = adjmx (A + B) *m (A - B).
  { move=> A B HAB_psd.
    have HAB_herm : (adjmx A *m B) \is hermmx
      := psdmx_herm HAB_psd.
    have /hermmxP HBA_eq := HAB_herm.
    rewrite adjmxM !adjmxK in HBA_eq.
    have Hsub_add : forall XX YY ZZ : 'M[C]_(n + 1),
      (XX - YY) + (YY - ZZ) = XX - ZZ.
    { move=> XX YY ZZ; apply/matrixP=> i j.
      by rewrite !mxE subrKA. }
    have Hadd_sub : forall XX YY ZZ : 'M[C]_(n + 1),
      (XX + YY) - (YY + ZZ) = XX - ZZ.
    { move=> XX YY ZZ; apply/matrixP=> i j.
      by rewrite !mxE addrKA. }
    have Hdiff2 : forall XX YY : 'M[C]_(n + 1),
      (XX + YY) - (XX - YY) = YY + YY.
    { move=> XX YY; apply/matrixP=> i j.
      by rewrite !mxE opprB addrC subrKA. }
    have Hplus_pack : forall XX YY WW : 'M[C]_(n + 1),
      (XX + YY) + (YY + WW) = (XX + WW) + (YY + YY).
    { move=> XX YY WW; apply/matrixP=> i j.
      by rewrite !mxE [YY i j + WW i j]addrC addrACA. }
    have Hminus_pack : forall XX YY WW : 'M[C]_(n + 1),
      (XX - YY) - (YY - WW) = (XX + WW) - (YY + YY).
    { move=> XX YY WW; apply/matrixP=> i j.
      by rewrite !mxE opprB addrACA -opprD. }
    pose X0 := adjmx A *m A.
    pose Y0 := adjmx A *m B.
    pose W0 := adjmx B *m B.
    split.
    - rewrite le_lownerE.
      have Hplus :
        adjmx (A + B) *m (A + B) = (X0 + W0) + (Y0 + Y0).
      { rewrite adjmxD mulmxDl !mulmxDr -HBA_eq.
        exact: Hplus_pack. }
      have Hminus :
        adjmx (A - B) *m (A - B) = (X0 + W0) - (Y0 + Y0).
      { rewrite adjmxD linearN mulmxBl !mulmxBr -HBA_eq.
        exact: Hminus_pack. }
      rewrite Hplus Hminus Hdiff2.
      apply: psdmxD; apply: psdmxD; exact: HAB_psd.
    - have Hlhs :
        adjmx (A - B) *m (A + B) = X0 - W0.
      { rewrite adjmxD linearN mulmxBl !mulmxDr -HBA_eq.
        exact: Hadd_sub. }
      have Hrhs :
        adjmx (A + B) *m (A - B) = X0 - W0.
      { rewrite adjmxD mulmxDl !mulmxBr -HBA_eq.
        exact: Hsub_add. }
      by rewrite Hlhs Hrhs. }
  have H_PS4d : forall A B : 'M[C]_(n + 1),
    (((2%:R)^-1)%:C : C) *:
      ((A - B) *m (A + B)^*t + (A + B) *m (A - B)^*t) =
    A *m A^*t - B *m B^*t.
  { move=> A B.
    pose X0 := A *m A^*t.
    pose Y0 := A *m B^*t.
    pose Z0 := B *m A^*t.
    pose W0 := B *m B^*t.
    have Hpack : forall P Q RR SS : 'M[C]_(n + 1),
      (P - RR) + (Q - SS) = (P + Q) - (RR + SS).
    { move=> P Q RR SS; apply/matrixP=> i j.
      by rewrite !mxE addrACA -opprD. }
    have Hinner :
      (A - B) *m (A + B)^*t + (A + B) *m (A - B)^*t =
      (X0 - W0) + (X0 - W0).
    { have Hleft : (A - B) *m (A + B)^*t = (X0 - Z0) + (Y0 - W0).
      { by rewrite [(A + B)^*t]adjmxD !mulmxDr !mulmxBl. }
      have Hright : (A + B) *m (A - B)^*t = (X0 + Z0) - (Y0 + W0).
      { by rewrite [(A - B)^*t]adjmxD linearN/= !mulmxBr !mulmxDl. }
      rewrite Hleft Hright.
      rewrite (Hpack X0 Y0 Z0 W0).
      rewrite (Hpack (X0 + Y0) (X0 + Z0) (Z0 + W0) (Y0 + W0)).
      have Hnum : (X0 + Y0) + (X0 + Z0) = (X0 + X0) + (Y0 + Z0).
      { by rewrite addrACA. }
      have Hden : (Z0 + W0) + (Y0 + W0) = (Y0 + Z0) + (W0 + W0).
      { by rewrite addrACA [Z0 + Y0]addrC. }
      rewrite Hnum Hden.
      rewrite addrKA.
      by rewrite -(Hpack X0 X0 W0 W0). }
    rewrite Hinner.
    rewrite scalerDr.
    rewrite -scalerDl.
    have Hhalf : (((2%:R)^-1)%:C : C) + (((2%:R)^-1)%:C : C) = 1.
    { by rewrite -rmorphD/= split21 rmorph1. }
    by rewrite Hhalf scale1r. }
  have H_PS4e : forall (A K : 'M[C]_(n + 1)),
    A \is psdmx ->
    K = adjmx K ->
    adjmx K *m K <= 1%:M ->
    @complex.Re R (\tr (K *m A *m K)) <=
    @complex.Re R (\tr| (2%:R^-1)%:C *: (K *m A + A *m K) |).
  { move=> A K HApsd HKself HKcontract.
    pose M := (2%:R^-1)%:C *: (K *m A + A *m K).
    have HdimE : n + 1 = n.+1 := addn1 _.
    have CT : n.+1 = dim (@ihb_chsType R 'I_(n.+1)).
    { by rewrite -(@ihb_dim_cast R 'I_(n.+1)) /= card_ord. }
    pose Klf : 'End['I_(n.+1)] :=
      mx2h (castmx (CT, CT) (castmx (HdimE, HdimE) K)).
    have HK_bound : Klf \is bound1lf.
    { rewrite bound1lf_form_le1.
      rewrite lef_h2mx.
      rewrite h2mx1.
      rewrite h2mx_comp.
      rewrite h2mx_adj.
      rewrite /Klf.
      rewrite mx2hK.
      rewrite -[X in X *m _](adjmx_castV (CT, CT)).
      rewrite (castmx_mul CT CT CT).
      rewrite castmx_le1.
      rewrite -[X in X *m _](adjmx_castV (HdimE, HdimE)).
      rewrite (castmx_mul HdimE HdimE HdimE).
      rewrite castmx_le1.
      apply: HKcontract. }
    have Hi2K : \i2| K | <= 1.
    { move: HK_bound.
      rewrite bound1lf_i2normE.
      rewrite /Klf.
      rewrite mx2hK.
      rewrite i2norm_castmx.
      rewrite i2norm_castmx.
      by []. }
    have HKAK_psd : (K *m A *m K) \is psdmx.
    { have HKAK_psd' : (K *m A *m K^*t) \is psdmx :=
          @psdmx_bimap_closed_gen _ _ A _ K HApsd.
      have -> : K *m A *m K = K *m A *m K^*t.
      { rewrite [X in K *m A *m X]HKself; reflexivity. }
      apply: HKAK_psd'. }
    have HKAK_tr_ge0 : 0 <= \tr (K *m A *m K)
      := psdmx_trace HKAK_psd.
    have HKAK_tr_real : (\tr (K *m A *m K)) \is Num.real
      := ger0_real HKAK_tr_ge0.
    have HM_tr_ge0 : 0 <= \tr| M | := trnorm_ge0 _.
    have HM_tr_real : (\tr| M |) \is Num.real := ger0_real HM_tr_ge0.
    have Hhalf :
      ((((2%:R)^-1)%:C : C) + (((2%:R)^-1)%:C : C)) = 1%:C.
    { by rewrite -rmorphD split21 rmorph1. }
    have HtrKM : \tr (K *m M) = \tr (K *m A *m K).
    { rewrite /M.
      rewrite -scalemxAr.
      rewrite mulmxDr.
      rewrite linearZ /=.
      rewrite linearD /=.
      rewrite !mulmxA.
      have HcycKKA : \tr (K *m K *m A) = \tr (K *m A *m K).
      { rewrite -mulmxA.
        rewrite (mxtrace_mulC K (K *m A)).
        reflexivity. }
      rewrite HcycKKA.
      set t := \tr (K *m A *m K).
      change (((2%:R^-1)%:C : C) * (t + t) = t).
      rewrite mulrDr.
      rewrite -mulrDl.
      rewrite Hhalf.
      by rewrite mul1r. }
    have Habs_le : `| \tr (K *m M) | <= \tr| M |.
    { apply: (le_trans (trnormM_ge K M)).
      have Hmul : \i2| K | * \tr| M | <= 1 * \tr| M |.
      { apply: ler_pM.
        - exact: i2norm_ge0.
        - exact: trnorm_ge0.
        - exact: Hi2K.
        - exact: lexx. }
      by rewrite mul1r in Hmul. }
    have HgoalC : \tr (K *m A *m K) <= \tr| M |.
    { have HtrKM_sym : \tr (K *m A *m K) = \tr (K *m M) := esym HtrKM.
      rewrite HtrKM_sym.
      rewrite HtrKM_sym in HKAK_tr_ge0.
      have HnormKM : \tr (K *m M) = `| \tr (K *m M) |
        := esym (ger0_norm HKAK_tr_ge0).
      rewrite HnormKM.
      exact: Habs_le. }
    move: HgoalC.
    rewrite -(RRe_real HKAK_tr_real).
    rewrite -(RRe_real HM_tr_real).
    by rewrite lecR. }
  have HReTrn_eq_2Dbar : @complex.Re R (trnorm Mdiff) = 2%:R * Dbar.
  { by rewrite /Dbar mulrC mulfVK// pnatr_eq0. }
  have [U_pol [P0 [HM_polar [HU_uni [HP0_psd _]]]]] := H_polar.
  have HUpolUUt : U_pol *m adjmx U_pol = 1%:M
    := unitarymxK HU_uni.
  have HUpolUtU : adjmx U_pol *m U_pol = 1%:M
    := unitarymxKV HU_uni.
  have HP0_herm : adjmx P0 = P0 := esym (hermmxP _ (psdmx_herm HP0_psd)).
  pose Apol : 'M[C]_(n + 1) := Srho *m U_pol.
  pose Bpol : 'M[C]_(n + 1) := Stau.
  have HApol_adjB : adjmx Apol *m Bpol = P0.
  { rewrite /Apol /Bpol adjmxM HSrho_adj.
    rewrite -mulmxA HM_polar mulmxA HUpolUtU mul1mx; reflexivity. }
  have HApolB_psd : (adjmx Apol *m Bpol) \is psdmx
    by rewrite HApol_adjB.
  have [HleAB HsymAB] := H_PS4c Apol Bpol HApolB_psd.
  have [K_w [HKeq [HKherm HKcontr]]] := pd_gtd_ub_aux_PS4f7 HleAB HsymAB.
  pose Ypad : 'M[C]_(n + 1) := (Apol + Bpol) *m adjmx (Apol + Bpol).
  have HYpad_psd : Ypad \is psdmx := form_psd _.
  have HE := H_PS4e Ypad K_w HYpad_psd HKherm HKcontr.
  have HKAK_eq :
    K_w *m Ypad *m K_w = (Apol - Bpol) *m adjmx (Apol - Bpol).
  { rewrite /Ypad.
    have HadjK : adjmx (Apol - Bpol) = adjmx (Apol + Bpol) *m K_w.
    { by rewrite HKeq adjmxM -HKherm. }
    rewrite HadjK.
    rewrite !mulmxA -HKeq.
    reflexivity. }
  have HMpad_eq :
    ((2%:R)^-1)%:C *: (K_w *m Ypad + Ypad *m K_w)
    = Apol *m adjmx Apol - Bpol *m adjmx Bpol.
  { have HKL : K_w *m Ypad = (Apol - Bpol) *m adjmx (Apol + Bpol).
    { by rewrite /Ypad mulmxA -HKeq. }
    have HKR : Ypad *m K_w = (Apol + Bpol) *m adjmx (Apol - Bpol).
    { rewrite /Ypad -mulmxA.
      have -> : adjmx (Apol + Bpol) *m K_w
              = adjmx (K_w *m (Apol + Bpol)) by rewrite adjmxM -HKherm.
      by rewrite -HKeq. }
    by rewrite HKL HKR; exact: H_PS4d Apol Bpol. }
  have HAA : Apol *m adjmx Apol = rho.
  { rewrite /Apol adjmxM HSrho_adj.
    rewrite -mulmxA [U_pol *m _]mulmxA HUpolUUt mul1mx.
    exact: sqrtmxK Hrho_psd. }
  have HBB : Bpol *m adjmx Bpol = tau.
  { rewrite /Bpol HStau_adj. exact: sqrtmxK Htau_psd. }
  have HMdiff_pad : Apol *m adjmx Apol - Bpol *m adjmx Bpol = Mdiff.
  { by rewrite HAA HBB. }
  rewrite HKAK_eq in HE.
  rewrite HMpad_eq HMdiff_pad in HE.
  have HTr_AmB :
    \tr ((Apol - Bpol) *m adjmx (Apol - Bpol)) =
    \tr rho + \tr tau - 2%:R * \tr P0.
  { have Hexpand :
      (Apol - Bpol) *m adjmx (Apol - Bpol) =
      (Apol *m adjmx Apol + Bpol *m adjmx Bpol) -
      (Apol *m adjmx Bpol + Bpol *m adjmx Apol).
    { rewrite [adjmx (Apol - Bpol)]linearB/=.
      rewrite mulmxBl !mulmxBr.
      set a := Apol *m adjmx Apol.
      set b := Apol *m adjmx Bpol.
      set c := Bpol *m adjmx Apol.
      set d := Bpol *m adjmx Bpol.
      by rewrite opprB addrACA -opprD. }
    rewrite Hexpand HAA HBB.
    rewrite raddfB/= raddfD/= raddfD/=.
    have HSStauSrho : Stau *m Srho = adjmx (Srho *m Stau).
    { rewrite adjmxM.
      rewrite HSrho_adj HStau_adj.
      reflexivity. }
    have HTrAB : \tr (Apol *m adjmx Bpol) = \tr P0.
    { rewrite /Apol /Bpol HStau_adj.
      rewrite mxtrace_mulC.
      rewrite mulmxA.
      rewrite HSStauSrho HM_polar adjmxM HP0_herm.
      rewrite -mulmxA HUpolUtU mulmx1.
      reflexivity. }
    have HTrBA : \tr (Bpol *m adjmx Apol) = \tr P0.
    { rewrite /Apol /Bpol.
      rewrite adjmxM HSrho_adj.
      rewrite mxtrace_mulC.
      rewrite -mulmxA HM_polar.
      rewrite mulmxA HUpolUtU mul1mx.
      reflexivity. }
    rewrite HTrAB HTrBA.
    by rewrite -mulr2n mulr_natl. }
  have HRe_TrAmB :
    @complex.Re R (\tr ((Apol - Bpol) *m adjmx (Apol - Bpol))) =
    2%:R - 2%:R * @complex.Re R (\tr P0).
  { rewrite HTr_AmB raddfB/= raddfD/=.
    rewrite Hrho_tr_eq1 Htau_tr_eq1 raddfMnat.
    by []. }
  have HE2 :
    2%:R - 2%:R * @complex.Re R (\tr P0) <=
    @complex.Re R (trnorm Mdiff).
  { by rewrite -HRe_TrAmB; exact: HE. }
  have HTrP0_eq_trnX :
    @complex.Re R (\tr P0) = @complex.Re R (trnorm (Srho *m Stau)).
  { have HtrnX : trnorm (Srho *m Stau) = \tr P0.
    { rewrite HM_polar.
      rewrite schnormUl//.
      exact: psdmx_trnorm HP0_psd. }
    by rewrite HtrnX. }
  rewrite HTrP0_eq_trnX in HE2.
  rewrite HReTrn_eq_2Dbar in HE2.
  have H2pos : (0 : R) < 2%:R by rewrite ltr0n.
  rewrite -(ler_pM2l H2pos) mulrBr mulr1.
  rewrite lerBlDr addrC -lerBlDr in HE2.
  exact: HE2.
Qed.

(* path: utils:pd_gtd_ub -> utils:pd_gtd_ub' -> *)
(*   entropy:smooth_hmax_attained -> entropy:smooth_hmaxE_EFin -> *)
(*   bb84:bb84_secret *)
Lemma pd_gtd_ub (Lsys : finType) (Hsys : Lsys -> chsType) (S : {set Lsys})
    (rho tau : 'F[Hsys]_S) :
  rho \is psdlf -> tau \is psdlf ->
  @complex.Re R (\Tr rho) <= 1 -> @complex.Re R (\Tr tau) <= 1 ->
  pur_dist rho tau <=
  Num.sqrt (2%:R *
              ((trnormH (rho - tau) +
                `|@complex.Re R (\Tr rho) - @complex.Re R (\Tr tau)|) / 2%:R) -
            ((trnormH (rho - tau) +
              `|@complex.Re R (\Tr rho) - @complex.Re R (\Tr tau)|) / 2%:R) ^ 2).
Proof.
  move=> Prho Ptau Hrho_tr Htau_tr.
  pose H : chsType := 'H[Hsys]_S.
  set Tbar := trnormH (rho - tau) +
              `|@complex.Re R (\Tr rho) - @complex.Re R (\Tr tau)|.
  set Dbar := Tbar / 2%:R.
  have Hrho_mx : h2mx rho \is psdmx by move: Prho; rewrite qualifE.
  have Htau_mx : h2mx tau \is psdmx by move: Ptau; rewrite qualifE.
  have Hh2mxB_gtd (x y : 'F[Hsys]_S) :
      h2mx (x - y) = h2mx x - h2mx y.
  { have Hlin := @h2mxP R ('H[Hsys]_S) ('H[Hsys]_S).
    have Hadd (u v : 'F[Hsys]_S) : h2mx (u + v) = h2mx u + h2mx v.
    { rewrite -[u in h2mx (u + v)]scale1r.
      rewrite -[h2mx u]scale1r.
      exact: (Hlin 1 u v). }
    have Hneg (z : 'F[Hsys]_S) : h2mx (- z) = - h2mx z.
    { exact: linearN. }
    change (h2mx (x + - y) = h2mx x + - h2mx y).
    by rewrite Hadd Hneg. }
  have Hrho_mx_tr : @complex.Re R (\tr (h2mx rho)) <= 1.
  { move: Hrho_tr; by rewrite /lftrace. }
  have Htau_mx_tr : @complex.Re R (\tr (h2mx tau)) <= 1.
  { move: Htau_tr; by rewrite /lftrace. }
  have Hrho_mx_den : h2mx rho \is denmx :=
    denmx_psd_re_tr_le Hrho_mx Hrho_mx_tr.
  have Htau_mx_den : h2mx tau \is denmx :=
    denmx_psd_re_tr_le Htau_mx Htau_mx_tr.
  have HrhoE_psd : embed_subnorm (h2mx rho) \is psdmx :=
    embed_subnorm_psdmx Hrho_mx_den.
  have HtauE_psd : embed_subnorm (h2mx tau) \is psdmx :=
    embed_subnorm_psdmx Htau_mx_den.
  have HrhoE_tr_eq1 : @complex.Re R (\tr (embed_subnorm (h2mx rho))) = 1 :=
    embed_subnorm_tr_eq1 Hrho_mx_den.
  have HtauE_tr_eq1 : @complex.Re R (\tr (embed_subnorm (h2mx tau))) = 1 :=
    embed_subnorm_tr_eq1 Htau_mx_den.
  have HrhoE_realtr : \tr (embed_subnorm (h2mx rho)) \is Num.real
    by apply: ger0_real; exact: psdmx_trace HrhoE_psd.
  have HtauE_realtr : \tr (embed_subnorm (h2mx tau)) \is Num.real
    by apply: ger0_real; exact: psdmx_trace HtauE_psd.
  have HrhoE_eq1 : \tr (embed_subnorm (h2mx rho)) = 1
    by rewrite -(RRe_real HrhoE_realtr) HrhoE_tr_eq1.
  have HtauE_eq1 : \tr (embed_subnorm (h2mx tau)) = 1
    by rewrite -(RRe_real HtauE_realtr) HtauE_tr_eq1.
  pose Mdiff := embed_subnorm (h2mx rho) - embed_subnorm (h2mx tau).
  have Hembed_diff_block :
      embed_subnorm (h2mx rho) - embed_subnorm (h2mx tau) =
      block_mx (h2mx rho - h2mx tau)
              (0 : 'M[C]_(dim H, 1))
              (0 : 'M[C]_(1, dim H))
              ((\tr (h2mx tau) - \tr (h2mx rho)) *: 1%:M : 'M[C]_1).
  { rewrite /embed_subnorm opp_block_mx oppr0 add_block_mx !addr0.
    congr (block_mx _ _ _ _); first by rewrite subrr.
    rewrite -scalerBl.
    congr (_ *: _).
    by rewrite opprD opprK addrACA subrr add0r addrC. }
  have H_embed_trnorm_eq :
      trnorm (embed_subnorm (h2mx rho) - embed_subnorm (h2mx tau)) =
      trnorm (h2mx rho - h2mx tau) +
      Num.norm (\tr (h2mx tau) - \tr (h2mx rho)).
  { rewrite Hembed_diff_block schnorm_mxdiag.
    rewrite l1normE big_ord1 big_split_ord/=.
    rewrite (eq_bigr (fun j => svd_d (h2mx rho - h2mx tau) 0 j)); last first.
    { by move=> j _; rewrite row_mxEl ger0_norm// svd_d_ge0. }
    rewrite [X in _ + X = _]
      (eq_bigr (fun j => svd_d ((\tr (h2mx tau) - \tr (h2mx rho))
                                *: 1%:M : 'M[C]_1) 0 j)); last first.
    { by move=> j _; rewrite row_mxEr ger0_norm// svd_d_ge0. }
    rewrite -trnorm_svdE -trnorm_svdE.
    congr (_ + _).
    by rewrite scalemx1 trnorm_scale mul1r. }
  have Hrho_tr_real : \tr (h2mx rho) \is Num.real
    by apply: ger0_real; exact: psdmx_trace Hrho_mx.
  have Htau_tr_real : \tr (h2mx tau) \is Num.real
    by apply: ger0_real; exact: psdmx_trace Htau_mx.
  have HReTrn_eq_2Dbar : @complex.Re R (trnorm Mdiff) = 2%:R * Dbar.
  { have H1 : @complex.Re R (trnorm Mdiff) =
              @complex.Re R (trnorm (h2mx rho - h2mx tau)) +
              @complex.Re R (Num.norm (\tr (h2mx tau) - \tr (h2mx rho))).
    { by rewrite /Mdiff H_embed_trnorm_eq raddfD/=. }
    have H2 : @complex.Re R (trnorm (h2mx rho - h2mx tau)) =
              trnormH (rho - tau).
    { by rewrite /trnormH Hh2mxB_gtd. }
    have H3 : @complex.Re R (Num.norm (\tr (h2mx tau) - \tr (h2mx rho))) =
              `|@complex.Re R (\Tr rho) - @complex.Re R (\Tr tau)|.
    { have Heq_diff : \tr (h2mx tau) - \tr (h2mx rho) =
        (@complex.Re R (\tr (h2mx tau)) -
         @complex.Re R (\tr (h2mx rho)))%:C.
      { by rewrite -(RRe_real Htau_tr_real) -(RRe_real Hrho_tr_real) -realcB. }
      rewrite Heq_diff /=.
      rewrite expr0n addr0 Num.Theory.sqrtr_sqr.
      by rewrite /lftrace distrC. }
    rewrite H1 H2 H3 -/Tbar.
    by rewrite /Dbar mulrC mulfVK// pnatr_eq0. }
  have HDbar_le1 : Dbar <= 1.
  { have Htrnorm_embed_rho : trnorm (embed_subnorm (h2mx rho)) = 1.
    { rewrite (psdmx_trnorm HrhoE_psd); exact: HrhoE_eq1. }
    have Htrnorm_embed_tau : trnorm (embed_subnorm (h2mx tau)) = 1.
    { rewrite (psdmx_trnorm HtauE_psd); exact: HtauE_eq1. }
    have Htn_Mdiff_le2_C : trnorm Mdiff <= 2%:C.
    { rewrite /Mdiff.
      have := trnorm_triangle (embed_subnorm (h2mx rho))
                              (- embed_subnorm (h2mx tau)).
      rewrite schnormN Htrnorm_embed_rho Htrnorm_embed_tau.
      by rewrite -rmorphD. }
    have Htn_Mdiff_Re_le2 : @complex.Re R (trnorm Mdiff) <= 2%:R.
    { by move: Htn_Mdiff_le2_C; rewrite lecE /= => /andP []. }
    have H2Dbar_le2 : 2%:R * Dbar <= 2%:R.
    { by rewrite -HReTrn_eq_2Dbar. }
    have H2pos : (0 : R) < 2%:R by rewrite ltr0n.
    rewrite -(ler_pM2l H2pos) ?mulr1.
    exact: H2Dbar_le2. }
  have Hmatrix_PS :=
    pd_gtd_ub_powers_stormer_mx HrhoE_psd HtauE_psd
      HrhoE_tr_eq1 HtauE_tr_eq1.
  have H_powers_stormer : 1 - Dbar <= gfid rho tau.
  { rewrite /gfid /gfidelity.
    move: Hmatrix_PS.
    rewrite -/Mdiff HReTrn_eq_2Dbar.
    have Hhalf : (2%:R * Dbar) / 2%:R = Dbar.
    { by rewrite [2%:R * Dbar]mulrC -mulrA mulfV ?mulr1// pnatr_eq0. }
    by rewrite Hhalf. }
  have Hgfid_ge0 : 0 <= gfid rho tau.
  { rewrite /gfid.
    apply: gfid_ge0_mx.
    - by move: Prho; rewrite qualifE.
    - by move: Ptau; rewrite qualifE. }
  have H1mDbar_ge0 : 0 <= 1 - Dbar by rewrite subr_ge0; exact: HDbar_le1.
  have Hsq : (1 - Dbar) ^ 2 <= (gfid rho tau) ^ 2.
    exact: lerXn2r.
  rewrite /pur_dist.
  apply: ler_wsqrtr.
  have -> : 2%:R * Dbar - Dbar ^ 2 = 1 - (1 - Dbar) ^ 2
    by exact: sqr_sub1_expand_ring.
  exact: lerB (lexx 1) Hsq.
Qed.

(* tex: pr:pd-gtd-bounds — Tomamichel, 'A Framework for Non-Asymptotic      *)
(*   Quantum Information Theory' (PhD thesis, arXiv:1203.2142),             *)
(*   Proposition 3.3, weaker corollary `P ≤ √(2D̄)`.                        *)
(* Direct corollary of `pd_gtd_ub`: since 2D̄ - D̄² ≤ 2D̄ (D̄² ≥ 0),           *)
(* `√(2D̄ - D̄²) ≤ √(2D̄)` by `ler_wsqrtr`. Upper bound        *)
(* exposed to consumers (prop.v, sm.v).                                 *)
(* pd_gtd_ub' *)
(* infra: corresponds to `pr:pd-gtd-bounds` (Proposition 3.3) weak-form RHS *)
(* consumer: pd_gtd_ub' is used downstream by the BB84 secrecy proof. *)
(* path: utils:pd_gtd_ub' -> entropy:smooth_hmax_attained -> *)
(*   entropy:smooth_hmaxE_EFin -> *)
(*   bb84:bb84_secret *)
Lemma pd_gtd_ub' (Lsys : finType) (Hsys : Lsys -> chsType) (S : {set Lsys})
    (rho tau : 'F[Hsys]_S) :
  rho \is psdlf -> tau \is psdlf ->
  @complex.Re R (\Tr rho) <= 1 -> @complex.Re R (\Tr tau) <= 1 ->
  pur_dist rho tau <=
    Num.sqrt (trnormH (rho - tau) +
              `|@complex.Re R (\Tr rho) - @complex.Re R (\Tr tau)|).
Proof.
  move=> Prho Ptau Hrho_tr Htau_tr.
  apply: (le_trans (pd_gtd_ub Prho Ptau Hrho_tr Htau_tr)).
  apply: ler_wsqrtr.
  set Tbar := trnormH (rho - tau) +
              `|@complex.Re R (\Tr rho) - @complex.Re R (\Tr tau)|.
  have H2 : (2%:R : R) != 0 by rewrite pnatr_eq0.
  have HT_eq : 2%:R * (Tbar / 2%:R) = Tbar.
    by rewrite mulrA mulrAC mulfV// mul1r.
  rewrite HT_eq.
  rewrite lerBlDr lerDl.
  exact: sqr_ge0.
Qed.

End PurDistFacts.

(* Matrix-level pur_dist reflexivity. Derived from gfid_refl_mx.         *)
(* pur_dist_mx_refl *)
(* infra: no tex label — fundamental & reusable (mathcomp-style) *)
(* consumer: pur_dist_mx_refl is used downstream by the BB84 secrecy proof. *)
(* path: utils:pur_dist_mx_refl -> eur:smooth_hmax_mx_rho_ZC_purif_dpi -> *)
(*   eur:entropic_uncertainty_relation -> *)
(*   eur:entropic_uncertainty_relation -> *)
(*   bb84:entropic_uncertainty_relation_bb84 -> bb84:bb84_secret *)
Lemma pur_dist_mx_refl {na nb : nat} (rho : 'M[C]_(na * nb)) :
  rho \is denmx ->
  pur_dist_mx rho rho = 0.
Proof.
  move=> Hrho; have /denmxP [Prho HtrC] := Hrho.
  have Htr : @complex.Re R (\tr rho) <= 1
    by move: HtrC; rewrite lecE /= => /andP [_].
  rewrite /pur_dist_mx.
  by rewrite (gfid_refl_mx Hrho) exp1rz subrr sqrtr0.
Qed.

(* Matrix form of `pr:pd-metric`, used by matrix smooth-max optimizers. *)
(* pur_dist_mx_triangle *)
(* infra: no tex label — reusable matrix counterpart of `pd_metric_triangle`. *)
(* path: utils:pur_dist_mx_triangle -> utils:pur_dist_mx_trace_sqrt_bound -> *)
(*   eur:smooth_hmax_mx_rho_ZC_purif_dpi -> *)
(*   eur:entropic_uncertainty_relation -> *)
(*   eur:entropic_uncertainty_relation -> *)
(*   bb84:entropic_uncertainty_relation_bb84 -> bb84:bb84_secret *)
Lemma pur_dist_mx_triangle {n : nat} (rho tau sigma : 'M[C]_n) :
  (0 < n)%N ->
  rho \is denmx -> tau \is denmx -> sigma \is denmx ->
  Num.sqrt (1 - (gfidelity rho tau) ^+ 2) <=
    Num.sqrt (1 - (gfidelity rho sigma) ^+ 2) +
    Num.sqrt (1 - (gfidelity sigma tau) ^+ 2).
Proof.
  case: n rho tau sigma => [|m] rho tau sigma Hn_pos Hrho_den Htau_den
    Hsigma_den.
  { by move: Hn_pos; rewrite ltnn. }
  have /denmxP [Hrho Hrho_trC] := Hrho_den.
  have /denmxP [Htau Htau_trC] := Htau_den.
  have /denmxP [Hsigma Hsigma_trC] := Hsigma_den.
  have Hrho_tr : @complex.Re R (\tr rho) <= 1
    by move: Hrho_trC; rewrite lecE /= => /andP [_].
  have Htau_tr : @complex.Re R (\tr tau) <= 1
    by move: Htau_trC; rewrite lecE /= => /andP [_].
  have Hsigma_tr : @complex.Re R (\tr sigma) <= 1
    by move: Hsigma_trC; rewrite lecE /= => /andP [_].
  pose T : ihbFinType := [the ihbFinType of 'I_(m.+1)].
  have Hdim : dim (@ihb_chsType R T) = m.+1.
  { by rewrite -(@ihb_dim_cast R T) /T card_ord. }
  pose L0 := 'I_1.
  pose HL0 (_ : L0) : chsType := @ihb_chsType R T.
  pose S0 : {set L0} := [set ord0].
  have Hdim0 : dim 'H[HL0]_S0 = m.+1.
  { rewrite /S0 dim_setten big_set1 /HL0.
    exact: Hdim. }
  pose rhoL : 'F[HL0]_S0 := mx2h (castmx (esym Hdim0, esym Hdim0) rho).
  pose tauL : 'F[HL0]_S0 := mx2h (castmx (esym Hdim0, esym Hdim0) tau).
  pose sigmaL : 'F[HL0]_S0 := mx2h (castmx (esym Hdim0, esym Hdim0) sigma).
  have HrhoL : rhoL \is psdlf.
  { rewrite /rhoL qualifE /= mx2hK -/(castmx_sq (esym Hdim) rho).
    exact: castmx_sq_psdmx Hrho. }
  have HtauL : tauL \is psdlf.
  { rewrite /tauL qualifE /= mx2hK -/(castmx_sq (esym Hdim) tau).
    exact: castmx_sq_psdmx Htau. }
  have HsigmaL : sigmaL \is psdlf.
  { rewrite /sigmaL qualifE /= mx2hK -/(castmx_sq (esym Hdim) sigma).
    exact: castmx_sq_psdmx Hsigma. }
  have HrhoL_tr : @complex.Re R (\Tr rhoL) <= 1.
  { rewrite /rhoL /lftrace /= mx2hK mxtrace_castmx_sq. exact: Hrho_tr. }
  have HtauL_tr : @complex.Re R (\Tr tauL) <= 1.
  { rewrite /tauL /lftrace /= mx2hK mxtrace_castmx_sq. exact: Htau_tr. }
  have HsigmaL_tr : @complex.Re R (\Tr sigmaL) <= 1.
  { rewrite /sigmaL /lftrace /= mx2hK mxtrace_castmx_sq. exact: Hsigma_tr. }
  have Htri := @pd_metric_triangle L0 HL0 S0 rhoL tauL sigmaL
    HrhoL HtauL HsigmaL HrhoL_tr HtauL_tr HsigmaL_tr.
  move: Htri.
  rewrite /pur_dist /gfid /rhoL /tauL /sigmaL !mx2hK.
  by rewrite !gfid_cast_mx.
Qed.

(* Matrix trace estimate from the purified-distance triangle with 0. *)
(* pur_dist_mx_trace_sqrt_bound *)
(* infra: no tex label — reusable matrix epsilon-ball trace estimate. *)
(* path: utils:pur_dist_mx_trace_sqrt_bound -> *)
(*   eur:smooth_hmax_mx_rho_ZC_purif_dpi -> *)
(*   eur:entropic_uncertainty_relation -> *)
(*   eur:entropic_uncertainty_relation -> *)
(*   bb84:entropic_uncertainty_relation_bb84 -> bb84:bb84_secret *)
Lemma pur_dist_mx_trace_sqrt_bound {n : nat} (rho tau : 'M[C]_n) :
  (0 < n)%N ->
  rho \is denmx -> tau \is denmx ->
  Num.sqrt (@complex.Re R (\tr rho)) <=
    Num.sqrt (@complex.Re R (\tr tau)) +
    Num.sqrt (1 - (gfidelity tau rho) ^+ 2).
Proof.
  move=> Hn_pos Hrho_den Htau_den.
  have /denmxP [Hrho Hrho_trC] := Hrho_den.
  have /denmxP [Htau Htau_trC] := Htau_den.
  have Hrho_tr : @complex.Re R (\tr rho) <= 1
    by move: Hrho_trC; rewrite lecE /= => /andP [_].
  have Htau_tr : @complex.Re R (\tr tau) <= 1
    by move: Htau_trC; rewrite lecE /= => /andP [_].
  have Hzero_psd : (0 : 'M[C]_n) \is psdmx := psdmx0 C n.
  have Hzero_tr : @complex.Re R (\tr (0 : 'M[C]_n)) <= 1
    by rewrite mxtrace0 raddf0 ler01.
  have Hzero_den : (0 : 'M[C]_n) \is denmx.
  { exact: denmx0. }
  have Hpd_zero : forall x : 'M[C]_n,
      x \is denmx ->
      Num.sqrt (1 - (gfidelity (0 : 'M[C]_n) x) ^+ 2) =
      Num.sqrt (@complex.Re R (\tr x)).
  { move=> x Hx_den.
    have /denmxP [Hx Hx_trC] := Hx_den.
    have Hx_tr : @complex.Re R (\tr x) <= 1
      by move: Hx_trC; rewrite lecE /= => /andP [_].
    have Hx_tr_ge0 : 0 <= @complex.Re R (\tr x).
    { have /= := psdmx_trace Hx.
      by rewrite lecE /= => /andP [_]. }
    have Hgf0 :
        gfidelity (0 : 'M[C]_n) x =
        Num.sqrt (1 - @complex.Re R (\tr x)).
    { rewrite (alt_gfid_gen Hzero_psd Hx).
      rewrite sqrtmx0 mul0mx trnorm0 raddf0 add0r.
      rewrite mxtrace0 subr0.
      have Hone : @complex.Re R 1 = 1 by rewrite -(re_realid 1).
      have Hx_tr_real : (\tr x : C) = (@complex.Re R (\tr x))%:C
        by rewrite RRe_real // ger0_real // psdmx_trace.
      have Hone_minus :
          @complex.Re R (1 - \tr x) = 1 - @complex.Re R (\tr x).
      { rewrite Hx_tr_real.
        have -> : (1 : C) - (@complex.Re R (\tr x))%:C =
                  (1 - @complex.Re R (\tr x))%:C
          by rewrite -realcB.
        by rewrite re_realid. }
      by rewrite Hone Hone_minus sqrtr1 mul1r. }
    rewrite Hgf0.
    have Hone_minus_ge0 : 0 <= 1 - @complex.Re R (\tr x)
      by rewrite subr_ge0.
    rewrite sqr_sqrtr //.
    have -> : 1 - (1 - @complex.Re R (\tr x)) = @complex.Re R (\tr x)
      by rewrite opprB addrCA subrr addr0.
    by []. }
  have Htri := pur_dist_mx_triangle Hn_pos Hzero_den Hrho_den Htau_den.
  have Hpd0rho := Hpd_zero rho Hrho_den.
  have Hpd0tau := Hpd_zero tau Htau_den.
  rewrite -Hpd0rho.
  rewrite -Hpd0tau.
  exact: Htri.
Qed.

(* ================================================================== *)
(* Monotonicity under quantum operations                                *)

(* Set-level ptrace_cast DPI via matrix gfidelity monotonicity.          *)
Section PurDistMonoPTraceCastSet.
Variable (L : finType) (HL : L -> chsType) (A B : {set L}).
Hypothesis disAB : [disjoint A & B].

(* pd_mono_ptrace_cast *)
(* infra: no tex label — fundamental & reusable (mathcomp-style) *)
(* path: utils:pd_mono_ptrace_cast -> entropy:entropy_data_proc -> *)
(*   bb84:bb84_secret *)
Lemma pd_mono_ptrace_cast (rho tau : 'F[HL]_(A :|: B)) :
  tau \is psdlf -> rho \is psdlf ->
  pur_dist (ptrace_cast disAB tau) (ptrace_cast disAB rho) <=
  pur_dist tau rho.
Proof.
  move=> Ptau Prho.
  have Hgfid := gfid_ptr_mono disAB Ptau Prho dim_proper.
  rewrite /pur_dist.
  have Hpt_rho : ptrace_cast disAB rho \is psdlf
    := ptrace_cast_psdlf disAB Prho.
  have Hpt_tau : ptrace_cast disAB tau \is psdlf
    := ptrace_cast_psdlf disAB Ptau.
  have Hgfid_ge0 : 0 <= gfid tau rho.
  {
    rewrite /gfid.
    apply: gfid_ge0_mx.
    - by move: Ptau; rewrite qualifE.
    - by move: Prho; rewrite qualifE.
  }
  have Hgfid_ge0' : 0 <= gfid
      (ptrace_cast disAB tau) (ptrace_cast disAB rho).
  {
    rewrite /gfid.
    apply: gfid_ge0_mx.
    - by move: Hpt_tau; rewrite qualifE.
    - by move: Hpt_rho; rewrite qualifE.
  }
  apply: ler_wsqrtr.
  apply: lerB; first exact: lexx.
  rewrite ler_sqr ?nnegrE//.
Qed.

End PurDistMonoPTraceCastSet.

(* ================================================================== *)
(* Uhlmann's theorem for purified distance                              *)
(* tex: th:pd-uhl — Tomamichel, 'A Framework for Non-Asymptotic Quantum *)
(*   Information Theory' (PhD thesis, arXiv:1203.2142), Theorem 3.5     *)
(* ================================================================== *)

Section PurDistUhlmann.
Variable (L : finType) (HL : L -> chsType) (A B : {set L}).
Hypothesis disAB : [disjoint A & B].
Hypothesis dimAB : dim 'H[HL]_A = dim 'H[HL]_B.
Notation S_AB := (A :|: B).

(* tex: th:pd-uhl — Tomamichel, 'A Framework for Non-Asymptotic Quantum *)
(*   Information Theory' (PhD thesis, arXiv:1203.2142), Theorem 3.5     *)
(* math: For purification φ of ρ, ∃ purification θ of τ s.t.           *)
(*       P(ρ,τ) = P(φ,θ)                                                *)
(* Labelled-level form of Uhlmann's theorem for purified distance. The    *)
(* proof may rely on matrix-level Uhlmann facts internally, but the        *)
(* exported statement is phrased over set-labelled systems.               *)
Lemma pd_uhl (rho tau : 'F[HL]_A) (phi : 'F[HL]_S_AB) :
  phi \is denlf ->
  (\Rank phi <= 1%N)%N ->
  ptrace_cast disAB phi = rho ->
  tau \is denlf ->
  exists (vartheta : 'F[HL]_S_AB),
    vartheta \is denlf /\
    (\Rank vartheta <= 1%N)%N /\
    ptrace_cast disAB vartheta = tau /\
    pur_dist phi vartheta = pur_dist rho tau.
Proof.
  move=> Hphi_den Hphi_rank Hptr Htau_den.
  have HdimAB_set : dim 'H[HL]_A = dim 'H[HL]_B := dimAB.
  have Hphi_psd : phi \is psdlf by move/denlfP: Hphi_den => [].
  have Htau_psd : tau \is psdlf by move/denlfP: Htau_den => [].
  have Hrho_psd : rho \is psdlf.
  { rewrite -Hptr. exact: ptrace_cast_psdlf Hphi_psd. }
  have Hphi_mx_psd : h2mx phi \is psdmx by move: Hphi_psd; rewrite qualifE.
  have Htau_mx_psd : h2mx tau \is psdmx by move: Htau_psd; rewrite qualifE.
  have Hrho_mx_psd : h2mx rho \is psdmx by move: Hrho_psd; rewrite qualifE.
  have trlf_ptrace_cast (f : 'F[HL]_S_AB) : \Tr (ptrace_cast disAB f) = \Tr f.
  {
    rewrite /ptrace_cast /ptrace_cast_gen castlf_trlfE.
    have /cptpP [_ /tpmapP Htp] := @ptraceso_qc R L HL B S_AB.
    exact: Htp.
  }
  have Htr_rho : \Tr rho = \Tr phi by rewrite -Hptr trlf_ptrace_cast.
  have HF_right0 :
      forall (L0 : finType) (H0 : L0 -> chsType) (S0 : {set L0})
        (x : 'F[H0]_S0), fidelity x 0 = 0.
  {
    move=> L0 H0 S0 x.
    have Hsqrt0 : sqrtH (0 : 'F[H0]_S0) = 0.
    { by apply/h2mx_inj; rewrite sqrtH_h2mx h2mx0 sqrtmx0. }
    by rewrite /fidelity Hsqrt0 comp_lfun0r h2mx0 trnorm0 raddf0.
  }
  have HF_left0 :
      forall (L0 : finType) (H0 : L0 -> chsType) (S0 : {set L0})
        (x : 'F[H0]_S0), fidelity 0 x = 0.
  {
    move=> L0 H0 S0 x.
    have Hsqrt0 : sqrtH (0 : 'F[H0]_S0) = 0.
    { by apply/h2mx_inj; rewrite sqrtH_h2mx h2mx0 sqrtmx0. }
    by rewrite /fidelity Hsqrt0 comp_lfun0l h2mx0 trnorm0 raddf0.
  }
  have Hfid_scale :
      forall (L0 : finType) (H0 : L0 -> chsType) (S0 : {set L0})
        (x y : 'F[H0]_S0) (c d : R),
        0 <= c -> 0 <= d ->
        x \is psdlf -> y \is psdlf ->
        fidelity (c%:C *: x) (d%:C *: y) =
          Num.sqrt c * Num.sqrt d * fidelity x y.
  {
    move=> L0 H0 S0 x y c d Hc_ge0 Hd_ge0 Hx_psd Hy_psd.
    rewrite /fidelity.
    rewrite (sqrtHZ_nn Hc_ge0 Hx_psd) (sqrtHZ_nn Hd_ge0 Hy_psd).
    rewrite -!comp_lfunZl -!comp_lfunZr scalerA.
    have -> :
        ((Num.sqrt c)%:C * (Num.sqrt d)%:C : C) =
        ((Num.sqrt c * Num.sqrt d)%:C : C).
      by rewrite rmorphM.
    change (trnormH (((Num.sqrt c * Num.sqrt d)%:C) *: (sqrtH x \o sqrtH y)) =
            Num.sqrt c * Num.sqrt d * fidelity x y).
    rewrite trnormH_scaleZ.
    rewrite ger0_norm; last first.
    { apply: mulr_ge0; exact: sqrtr_ge0. }
    by rewrite /fidelity /trnormH.
  }
  have Hfid_to_pur :
      forall vartheta : 'F[HL]_S_AB,
        vartheta \is psdlf ->
        ptrace_cast disAB vartheta = tau ->
        fidelity phi vartheta = fidelity rho tau ->
        pur_dist phi vartheta = pur_dist rho tau.
  {
    move=> vartheta Hvartheta_psd Hvartheta_ptr Hfid.
    have Hvartheta_mx_psd : h2mx vartheta \is psdmx
      by move: Hvartheta_psd; rewrite qualifE.
    have Htr_vartheta : \Tr vartheta = \Tr tau
      by rewrite -Hvartheta_ptr trlf_ptrace_cast.
    rewrite /lftrace in Htr_rho Htr_vartheta *.
    rewrite /pur_dist /gfid.
    rewrite (alt_gfid_gen Hphi_mx_psd Hvartheta_mx_psd).
    rewrite (alt_gfid_gen Hrho_mx_psd Htau_mx_psd).
    rewrite /fidelity !h2mx_comp !sqrtH_h2mx in Hfid.
    by rewrite Hfid -Htr_rho Htr_vartheta.
  }
  case Htau0 : (tau == 0).
  - exists (0 : 'F[HL]_S_AB); split; first exact: denlf0.
    split; first by rewrite ranklf0.
    split.
    + move/eqP: Htau0 => ->.
      apply/h2mx_inj.
      rewrite (h2mx_ptrace_cast_ptrace2 disAB (0 : 'F[HL]_S_AB)).
      have -> :
          ((@tenv_mxU R L HL A B)^*t *m h2mx (0 : 'F[HL]_S_AB) *m
           (@tenv_mxU R L HL A B)) = 0.
      { by rewrite h2mx0 mulmx0 mul0mx. }
      by rewrite h2mx0 linear0.
    + apply: Hfid_to_pur.
      * exact: is_psdlf.
      * move/eqP: Htau0 => ->.
        apply/h2mx_inj.
        rewrite (h2mx_ptrace_cast_ptrace2 disAB (0 : 'F[HL]_S_AB)).
        have -> :
            ((@tenv_mxU R L HL A B)^*t *m h2mx (0 : 'F[HL]_S_AB) *m
             (@tenv_mxU R L HL A B)) = 0.
        { by rewrite h2mx0 mulmx0 mul0mx. }
        by rewrite h2mx0 linear0.
      * move/eqP: Htau0 => ->.
        by rewrite HF_right0.
  - have Htau_nz : tau != 0 by rewrite Htau0.
    case Hphi0 : (phi == 0).
    + have Htau_rankB : (\Rank tau <= dim 'H[HL]_B)%N.
      {
        rewrite -HdimAB_set /lfrank.
        exact: rank_leq_row.
      }
      have Htau_mx_nz : h2mx tau != 0.
      {
        apply/negP => /eqP Htau_mx0.
        move/negP: Htau_nz.
        apply.
        apply/eqP.
        have Htau_eq0 := f_equal mx2h Htau_mx0.
        by rewrite h2mxK mx2h0 in Htau_eq0.
      }
      have Htau_mx_den : h2mx tau \is denmx
        by move: Htau_den; rewrite qualifE.
      have [theta0 [Htheta0_den [Htheta0_rank Htheta0_ptrace]]] :=
        purification_exists_in_dim Htau_mx_den Htau_mx_nz Htau_rankB.
      pose U := @tenv_mxU R _ HL A B.
      have HU : U \is unitarymx := tenv_mxU_unitarymx _ _.
      have HUadj : U^*t \is unitarymx := tenv_mxU_adj_unitarymx disAB.
      have Uadj_mul_U : U^*t *m U = 1%:M.
      { by have := unitarymxK HUadj; rewrite adjmxK. }
      pose vartheta : 'F[HL]_S_AB := mx2h (U *m theta0 *m U^*t).
      have Htheta0_psd : theta0 \is psdmx by move/denmxP: Htheta0_den => [].
      have Hvartheta_h2mx : h2mx vartheta = U *m theta0 *m U^*t
        by rewrite /vartheta mx2hK.
      have Hvartheta_den : vartheta \is denlf.
      {
        have Hvartheta_psd : h2mx vartheta \is psdmx.
        { by rewrite Hvartheta_h2mx; exact: psdmx_bimap_closed_gen. }
        have Htr_theta0 : \tr theta0 <= 1 by move/denmxP: Htheta0_den => [].
        have Htr_vartheta : \tr (h2mx vartheta) = \tr theta0.
        {
          rewrite Hvartheta_h2mx mxtrace_mulC mulmxA.
          by rewrite Uadj_mul_U mul1mx.
        }
        rewrite qualifE.
        by apply/denmxP; split=> //; rewrite Htr_vartheta.
      }
      have Hvartheta_rank : \Rank vartheta = 1%N.
      {
        rewrite /lfrank Hvartheta_h2mx mxrank_mulmxU// -[U]adjmxK.
        by rewrite mxrank_mulUCmx//.
      }
      have HMvartheta_theta0 : U^*t *m h2mx vartheta *m U = theta0.
      {
        rewrite Hvartheta_h2mx !mulmxA Uadj_mul_U mul1mx -mulmxA Uadj_mul_U.
        by rewrite mulmx1.
      }
      have Hvartheta_ptr : ptrace_cast disAB vartheta = tau.
      {
        apply/h2mx_inj.
        rewrite (h2mx_ptrace_cast_ptrace2 disAB vartheta).
        by rewrite HMvartheta_theta0.
      }
      have Hrho0 : rho = 0.
      {
        move/eqP: Hphi0 => Hphi0.
        apply/h2mx_inj.
        rewrite -Hptr Hphi0 (h2mx_ptrace_cast_ptrace2 disAB (0 : 'F[HL]_S_AB)).
        have -> :
            ((@tenv_mxU R L HL A B)^*t *m h2mx (0 : 'F[HL]_S_AB) *m
             (@tenv_mxU R L HL A B)) = 0.
        { by rewrite h2mx0 mulmx0 mul0mx. }
        by rewrite h2mx0 linear0.
      }
      exists vartheta; split=> //.
      split; first by rewrite Hvartheta_rank.
      split; first exact: Hvartheta_ptr.
      apply: Hfid_to_pur.
      * by move/denlfP: Hvartheta_den => [].
      * exact: Hvartheta_ptr.
      * move/eqP: Hphi0 => ->.
        by rewrite Hrho0 HF_left0.
    + have Hphi_nz : phi != 0 by rewrite Hphi0.
      have Hphi_rank1 : \Rank phi = 1%N.
      {
        apply/eqP; rewrite eqn_leq; apply/andP; split=> //.
        rewrite lt0n /lfrank mxrank_eq0.
        apply/negP => /eqP Hphi_mx0.
        move/negP: Hphi_nz.
        apply.
        apply/eqP.
        have Hphi_eq0 := f_equal mx2h Hphi_mx0.
        by rewrite h2mxK mx2h0 in Hphi_eq0.
      }
      pose a := @complex.Re R (\Tr phi).
      pose b := @complex.Re R (\Tr tau).
      have Hphi_tr_real : (\Tr phi : C) = a%:C.
      { by rewrite /a RRe_real // ger0_real // psdlf_trlf. }
      have Htau_tr_real : (\Tr tau : C) = b%:C.
      { by rewrite /b RRe_real // ger0_real // psdlf_trlf. }
      have Ha_ge0 : 0 <= a.
      { by move: (psdlf_trlf Hphi_psd); rewrite Hphi_tr_real lecR. }
      have Hb_ge0 : 0 <= b.
      { by move: (psdlf_trlf Htau_psd); rewrite Htau_tr_real lecR. }
      have Ha_le1 : a <= 1.
      { by move: (denlf_trlf Hphi_den); rewrite Hphi_tr_real lecR. }
      have Hb_le1 : b <= 1.
      { by move: (denlf_trlf Htau_den); rewrite Htau_tr_real lecR. }
      have Ha_ne0 : a != 0.
      {
        apply/eqP=> Ha0.
        have Hphi_ge0 : 0 ⊑ phi by move: Hphi_psd; rewrite psdlfE.
        have Hphi_tr0 : \Tr phi = 0 by rewrite Hphi_tr_real Ha0.
        have Hphi_eq0 : phi == 0.
        { apply/trlf0_eq0. exact: (conj Hphi_ge0 Hphi_tr0). }
        by move/negP: Hphi_nz; rewrite Hphi_eq0.
      }
      have Hb_ne0 : b != 0.
      {
        apply/eqP=> Hb0.
        have Htau_ge0 : 0 ⊑ tau by move: Htau_psd; rewrite psdlfE.
        have Htau_tr0 : \Tr tau = 0 by rewrite Htau_tr_real Hb0.
        have Htau_eq0 : tau == 0.
        { apply/trlf0_eq0. exact: (conj Htau_ge0 Htau_tr0). }
        by move/negP: Htau_nz; rewrite Htau_eq0.
      }
      pose phi1 := ((a^-1)%:C) *: phi.
      pose rho1 := ((a^-1)%:C) *: rho.
      pose tau1 := ((b^-1)%:C) *: tau.
      have Hphi1_psd : phi1 \is psdlf.
      {
        apply: psdlfZ.
        - by rewrite lecR invr_ge0.
        - exact: Hphi_psd.
      }
      have Hrho1_psd : rho1 \is psdlf.
      {
        apply: psdlfZ.
        - by rewrite lecR invr_ge0.
        - exact: Hrho_psd.
      }
      have Htau1_psd : tau1 \is psdlf.
      {
        apply: psdlfZ.
        - by rewrite lecR invr_ge0.
        - exact: Htau_psd.
      }
      have Hphi1_tr1 : \Tr phi1 = 1.
      {
        rewrite /phi1 linearZ/= Hphi_tr_real.
        by rewrite -rmorphM/= mulVf ?rmorph1.
      }
      have Htau1_tr1 : \Tr tau1 = 1.
      {
        rewrite /tau1 linearZ/= Htau_tr_real.
        by rewrite -rmorphM/= mulVf ?rmorph1.
      }
      have Hphi1_den1 : phi1 \is den1lf.
      { by apply/den1lfP; split. }
      have Htau1_den : tau1 \is denlf.
      {
        apply/denlfP; split=> //.
        by rewrite Htau1_tr1.
      }
      have Hphi1_ptr : ptrace_cast disAB phi1 = rho1.
      {
        apply/h2mx_inj.
        have Hh2mxZ_AB (c : C) (x : 'F[HL]_S_AB) :
            h2mx (c *: x) = c *: h2mx x.
        { have Hlin := @h2mxP R ('H[HL]_S_AB) ('H[HL]_S_AB).
          move: (Hlin c x 0).
          rewrite addr0 h2mx0 addr0.
          by move=> ->. }
        have Hh2mxZ_A (c : C) (x : 'F[HL]_A) :
            h2mx (c *: x) = c *: h2mx x.
        { have Hlin := @h2mxP R ('H[HL]_A) ('H[HL]_A).
          move: (Hlin c x 0).
          rewrite addr0 h2mx0 addr0.
          by move=> ->. }
        rewrite (h2mx_ptrace_cast_ptrace2 disAB phi1) /phi1 /rho1
          Hh2mxZ_AB Hh2mxZ_A /=.
        set U := @tenv_mxU R L HL A B.
        rewrite -scalemxAr -scalemxAl.
        set M := U^*t *m h2mx phi *m U.
        have -> : ptrace2 (((a^-1)%:C) *: M) = ((a^-1)%:C) *: ptrace2 M.
        { by rewrite linearZ. }
        have Hptr_mx : ptrace2 M = h2mx rho.
        {
          rewrite /M /U -(h2mx_ptrace_cast_ptrace2 disAB phi).
          exact (f_equal h2mx Hptr).
        }
        exact (congr1 (fun x => ((a^-1)%:C) *: x) Hptr_mx).
      }
      have HainvC_neq0 : ((a^-1)%:C : C) != 0 by rewrite fmorph_eq0 invr_eq0.
      have HbinvC_neq0 : ((b^-1)%:C : C) != 0 by rewrite fmorph_eq0 invr_eq0.
      have /eqmxP Hphi1_eqmx := eqmx_scale (h2mx phi) HainvC_neq0.
      have /eqmxP Htau1_eqmx := eqmx_scale (h2mx tau) HbinvC_neq0.
      have Hh2mxZ_AB_rank (c : C) (x : 'F[HL]_S_AB) :
          h2mx (c *: x) = c *: h2mx x.
      { have Hlin := @h2mxP R ('H[HL]_S_AB) ('H[HL]_S_AB).
        move: (Hlin c x 0).
        rewrite addr0 h2mx0 addr0.
        by move=> ->. }
      have Hh2mxZ_A_rank (c : C) (x : 'F[HL]_A) :
          h2mx (c *: x) = c *: h2mx x.
      { have Hlin := @h2mxP R ('H[HL]_A) ('H[HL]_A).
        move: (Hlin c x 0).
        rewrite addr0 h2mx0 addr0.
        by move=> ->. }
      have Hphi1_rank : \Rank phi1 = 1%N.
      {
        rewrite /lfrank /phi1 Hh2mxZ_AB_rank /= (eqmx_rank Hphi1_eqmx).
        exact: Hphi_rank1.
      }
      have Htau1_rankB : (\Rank tau1 <= dim 'H[HL]_B)%N.
      {
        rewrite /lfrank /tau1 Hh2mxZ_A_rank /= (eqmx_rank Htau1_eqmx).
        rewrite -HdimAB_set.
        exact: rank_leq_row.
      }
      have Htau_mx_nz : h2mx tau != 0.
      {
        apply/negP=> /eqP Htau_mx0.
        have Htau_eq0 : tau = 0.
        {
          have := f_equal mx2h Htau_mx0.
          by rewrite h2mxK mx2h0.
        }
        by move/negP: Htau_nz; rewrite Htau_eq0.
      }
      have Htau1_nz : h2mx tau1 != 0.
      {
        apply/negP=> /eqP Htau1_0.
        have Htau_eq0 : tau = 0.
        {
          apply/h2mx_inj.
          have Hscaled := congr1 (fun x => (b%:C) *: x) Htau1_0.
          rewrite /tau1 Hh2mxZ_A_rank /= scalerA -rmorphM/= mulfV ?rmorph1 // in Hscaled.
          rewrite scale1r scaler0 in Hscaled.
          rewrite h2mx0.
          exact: Hscaled.
        }
        by move/negP: Htau_nz; rewrite Htau_eq0.
      }
      have [psi1 [Hpsi1_den [Hpsi1_rank [Hpsi1_ptr Hpsi1_fid]]]] :=
        @fid_iii_uhl R L HL A B disAB HdimAB_set phi1 tau1
          Hphi1_den1 Hphi1_rank Htau1_den Htau1_nz Htau1_rankB.
      pose vartheta := (b%:C) *: psi1.
      have Hpsi1_psd : psi1 \is psdlf by move/denlfP: Hpsi1_den => [].
      have Hpsi1_tr1 : \Tr psi1 = 1.
      {
        rewrite -(trlf_ptrace_cast psi1) Hpsi1_ptr.
        exact: Htau1_tr1.
      }
      have Hvartheta_den : vartheta \is denlf.
      {
        apply/denlfP; split.
        - apply: psdlfZ.
          + by rewrite lecR.
          + exact: Hpsi1_psd.
        - rewrite /vartheta linearZ/= Hpsi1_tr1 mulr1.
          by rewrite lecR.
      }
      have HbC_neq0 : (b%:C : C) != 0 by rewrite fmorph_eq0.
      have /eqmxP Hvartheta_eqmx := eqmx_scale (h2mx psi1) HbC_neq0.
      have Hvartheta_rank : \Rank vartheta = 1%N.
      {
        rewrite /lfrank /vartheta Hh2mxZ_AB_rank /=.
        rewrite (eqmx_rank Hvartheta_eqmx).
        exact: Hpsi1_rank.
      }
      have Htau_scale : tau = (b%:C) *: tau1.
      {
        rewrite /tau1 scalerA -rmorphM/= mulfV ?rmorph1 //.
        by rewrite scale1r.
      }
      have Hvartheta_ptr : ptrace_cast disAB vartheta = tau.
      {
        rewrite Htau_scale.
        apply/h2mx_inj.
        rewrite (h2mx_ptrace_cast_ptrace2 disAB vartheta) /vartheta
          Hh2mxZ_AB_rank Hh2mxZ_A_rank /=.
        set U := @tenv_mxU R L HL A B.
        rewrite -scalemxAr -scalemxAl.
        set M := U^*t *m h2mx psi1 *m U.
        have -> : ptrace2 ((b%:C) *: M) = (b%:C) *: ptrace2 M.
        { by rewrite linearZ. }
        have Hpsi1_ptr_mx : ptrace2 M = h2mx tau1.
        {
          rewrite /M /U -(h2mx_ptrace_cast_ptrace2 disAB psi1).
          exact (f_equal h2mx Hpsi1_ptr).
        }
        exact (congr1 (fun x => (b%:C) *: x) Hpsi1_ptr_mx).
      }
      have Hphi_scale : phi = (a%:C) *: phi1.
      {
        rewrite /phi1 scalerA -rmorphM/= mulfV ?rmorph1 //.
        by rewrite scale1r.
      }
      have Hrho_scale : rho = (a%:C) *: rho1.
      {
        rewrite /rho1 scalerA -rmorphM/= mulfV ?rmorph1 //.
        by rewrite scale1r.
      }
      exists vartheta; split=> //.
      split; first by rewrite Hvartheta_rank.
      split; first exact: Hvartheta_ptr.
      apply: Hfid_to_pur.
      * by move/denlfP: Hvartheta_den => [].
      * exact: Hvartheta_ptr.
      * rewrite Hphi_scale /vartheta.
        rewrite (@Hfid_scale L HL S_AB phi1 psi1 a b
                   Ha_ge0 Hb_ge0 Hphi1_psd Hpsi1_psd).
        rewrite Hrho_scale Htau_scale.
        rewrite (@Hfid_scale L HL A rho1 tau1 a b
                   Ha_ge0 Hb_ge0 Hrho1_psd Htau1_psd).
        rewrite Hphi1_ptr in Hpsi1_fid.
        by rewrite Hpsi1_fid.
Qed.

End PurDistUhlmann.

(* ================================================================== *)
(* Extension corollary for purified distance                            *)
(* tex: co:pd-ext — Tomamichel, 'A Framework for Non-Asymptotic Quantum *)
(*   Information Theory' (PhD thesis, arXiv:1203.2142), Corollary 3.6   *)
(* ================================================================== *)

Section PurDistExtension.
Variable (L : finType) (HL : L -> chsType) (A B : {set L}).
Hypothesis disAB : [disjoint A & B].
Notation S_AB := (A :|: B).

(* tex: co:pd-ext — Tomamichel, 'A Framework for Non-Asymptotic Quantum *)
(*   Information Theory' (PhD thesis, arXiv:1203.2142), Corollary 3.6   *)
(* math: every extension rhobar of rho can be matched by an extension   *)
(*       taubar of tau with the same purified distance                  *)
(* Stated over set-labelled systems. The construction depends only on    *)
(* the matrix representation (`h2mx`) and the tensor-coordinate unitary   *)
(* `tenv_mxU`, so it applies uniformly to singleton and compound labels. *)
(* path: utils:pd_ext -> utils:ptrace_cast_psdlf -> lhl:min_coll_bound -> *)
(*   bb84:privacy_amplification -> bb84:bb84_secret *)
Lemma pd_ext (rho tau : 'F[HL]_A) (rhobar : 'F[HL]_S_AB) :
  rhobar \is denlf ->
  ptrace_cast disAB rhobar = rho ->
  tau \is denlf ->
  exists taubar : 'F[HL]_S_AB,
    taubar \is denlf /\
    ptrace_cast disAB taubar = tau /\
    pur_dist rhobar taubar = pur_dist rho tau.
Proof.
  move=> Hrhobar_den Hptr Htau_den.
  pose a := dim 'H[HL]_A.
  pose b := dim 'H[HL]_B.
  pose U := @tenv_mxU R L HL A B.
  pose fidmx := fun n (X Y : 'M[C]_n) => @complex.Re R (trnorm (sqrtmx X *m sqrtmx Y)).
  pose pdmx := fun n (X Y : 'M[C]_n) => Num.sqrt (1 - (gfidelity X Y)^2).
  have HU : U \is unitarymx := tenv_mxU_unitarymx _ _.
  have HUadj : U^*t \is unitarymx := tenv_mxU_adj_unitarymx disAB.
  have U_mul_Uadj : U *m U^*t = 1%:M := unitarymxK HU.
  have Uadj_mul_U : U^*t *m U = 1%:M.
  { by have := unitarymxK HUadj; rewrite adjmxK. }
  have Hrhobar_mx_den : h2mx rhobar \is denmx by move: Hrhobar_den; rewrite qualifE.
  have Htau_mx_den : h2mx tau \is denmx by move: Htau_den; rewrite qualifE.
  have Hrhobar_mx_psd : h2mx rhobar \is psdmx := denmx_psd Hrhobar_mx_den.
  pose rho_AB := U^*t *m h2mx rhobar *m U.
  have HrhoAB_den : rho_AB \is denmx.
  {
    have HrhoAB_psd : rho_AB \is psdmx.
    { rewrite /rho_AB -[U in _ *m _ *m U]adjmxK.
      exact: psdmx_bimap_closed_gen Hrhobar_mx_psd. }
    move/denmxP: Hrhobar_mx_den => [_ Htr_rhobar].
    apply/denmxP; split=> //.
    rewrite /rho_AB mxtrace_mulC mulmxA.
    by rewrite U_mul_Uadj mul1mx.
  }
  have Hptr_mx : ptrace2 rho_AB = h2mx rho.
  {
    rewrite /rho_AB -(h2mx_ptrace_cast_ptrace2 disAB rhobar).
    exact (f_equal h2mx Hptr).
  }
  have Hmatrix_pd_ext :
      forall (rho_AB0 : 'M[C]_(a * b)) (rho_A0 tau_A0 : 'M[C]_a),
        (0 < b)%N ->
        rho_AB0 \is denmx ->
        ptrace2 rho_AB0 = rho_A0 ->
        tau_A0 \is denmx ->
        exists taub_AB : 'M[C]_(a * b),
          taub_AB \is denmx /\
          ptrace2 taub_AB = tau_A0 /\
          pdmx _ rho_AB0 taub_AB = pdmx _ rho_A0 tau_A0.
  {
    move=> rho_AB0 rho_A0 tau_A0 Hb_pos0 Hrho Hptr0 Htau.
    have Hden_cast : forall (n n' : nat) (eq_n : n = n') (M : 'M[C]_n),
        M \is denmx -> castmx_sq eq_n M \is denmx.
    {
      move=> n n' eq_n M HM.
      move/denmxP: HM => [Hpsd Htr].
      apply/denmxP; split.
      - exact: castmx_sq_psdmx Hpsd.
      - by rewrite mxtrace_castmx_sq.
    }
    have Hrank_castmx_sq : forall (n n' : nat) (eq_n : n = n') (M : 'M[C]_n),
        \rank (castmx_sq eq_n M) = \rank M.
    {
      move=> n n' eq_n M.
      by subst n'; rewrite /castmx_sq castmx_id.
    }
    have Hptrace2_regroup : forall m n k (A0 : 'M[C]_((m * n) * k)),
        ptrace2 (castmx_sq (esym (mulnA m n k)) A0) = ptrace2 (ptrace2 A0).
    {
      move=> m n k A0.
      have ptrace2E' : forall s t (B0 : 'M[C]_(s * t)) r1 r2,
          (ptrace2 B0) r1 r2 =
          \sum_(k0 : 'I_t) B0 (mxtens_index (r1, k0)) (mxtens_index (r2, k0)).
      {
        move=> s t B0 r1 r2.
        rewrite ptrace2E1 ptrace1E.
        by apply: eq_bigr => k0 _; rewrite mxE !mxtens_indexK.
      }
      have mxtens_assoc : forall (i : 'I_m) (j : 'I_n) (k0 : 'I_k),
          cast_ord (mulnA m n k) (mxtens_index (i, mxtens_index (j, k0))) =
          mxtens_index (mxtens_index (i, j), k0).
      {
        move=> i j k0.
        apply/val_inj => /=.
        by rewrite mulnDl mulnA addnA.
      }
      apply/matrixP => i j.
      rewrite ptrace2E'.
      transitivity
        (\sum_(j0 : 'I_n) \sum_(k0 : 'I_k)
          A0 (mxtens_index (mxtens_index (i, j0), k0))
             (mxtens_index (mxtens_index (j, j0), k0))).
      {
        rewrite (reindex (@mxtens_index n k))/=.
        2:{
          exists (@mxtens_unindex n k) => k0 /=.
          - by rewrite ?mxtens_indexK ?mxtens_unindexK -?surjective_pairing.
          - by rewrite ?mxtens_indexK ?mxtens_unindexK -?surjective_pairing.
        }
        rewrite pair_bigV /=.
        apply: eq_bigr => j0 _; apply: eq_bigr => k0 _.
        by rewrite castmxE /= esymK !mxtens_assoc.
      }
      rewrite ptrace2E'.
      by apply: eq_bigr => j0 _; rewrite ptrace2E'.
    }
    have HF_right0 :
        forall k : nat, forall X : 'M[C]_k, fidmx _ X 0 = 0.
    {
      move=> k X.
      by rewrite /fidmx sqrtmx0 mulmx0 trnorm0 raddf0.
    }
    have HF_left0 :
        forall k : nat, forall X : 'M[C]_k, fidmx _ 0 X = 0.
    {
      move=> k X.
      by rewrite /fidmx sqrtmx0 mul0mx trnorm0 raddf0.
    }
    have Hfid_to_pdmx :
        forall taub_AB : 'M[C]_(a * b),
          taub_AB \is psdmx ->
          ptrace2 taub_AB = tau_A0 ->
          fidmx _ rho_AB0 taub_AB = fidmx _ rho_A0 tau_A0 ->
          pdmx _ rho_AB0 taub_AB = pdmx _ rho_A0 tau_A0.
    {
      move=> taub_AB Htaub_psd Htaub_ptr Hfid.
      rewrite /fidmx in Hfid.
      have Hrho_psd : rho_AB0 \is psdmx := denmx_psd Hrho.
      have HrhoA_psd : rho_A0 \is psdmx.
      { rewrite -Hptr0. exact: ptrace2_psd Hrho_psd. }
      have Htau_psd : tau_A0 \is psdmx := denmx_psd Htau.
      have Hrho_tr : \tr rho_AB0 = \tr rho_A0 by rewrite tr_ptrace2 Hptr0.
      have Htaub_tr : \tr taub_AB = \tr tau_A0 by rewrite tr_ptrace2 Htaub_ptr.
      rewrite /pdmx.
      rewrite (alt_gfid_gen Hrho_psd Htaub_psd).
      rewrite (alt_gfid_gen HrhoA_psd Htau_psd).
      by rewrite Hfid Hrho_tr Htaub_tr.
    }
    have Hpdmx_cast : forall (n n' : nat) (eq_n : n = n') (X Y : 'M[C]_n),
        pdmx _ (castmx_sq eq_n X) (castmx_sq eq_n Y) = pdmx _ X Y.
    {
      move=> n n' eq_n X Y.
      rewrite /pdmx /castmx_sq.
      by rewrite gfid_cast_mx.
    }
    have Hpdmx_ptrace2 :
        forall m n (X Y : 'M[C]_(m * n)),
          (0 < n)%N ->
          X \is psdmx -> Y \is psdmx ->
          pdmx _ (ptrace2 X) (ptrace2 Y) <= pdmx _ X Y.
    {
      move=> m n X Y Hn0 HX HY.
      have Hmono := gfid_ptr_mono_mx Hn0 HX HY.
      have HXY_ge0 := gfid_ge0_mx HX HY.
      have Hpt_ge0 := gfid_ge0_mx (ptrace2_psd HX) (ptrace2_psd HY).
      rewrite /pdmx.
      apply: ler_wsqrtr.
      apply: lerB; first exact: lexx.
      by rewrite ler_sqr ?nnegrE.
    }
    have HrhoA_den : rho_A0 \is denmx.
    {
      rewrite -Hptr0.
      exact: ptrace2_denmx Hrho.
    }
    have Hrho_rank_sys : (\rank rho_AB0 <= a * b)%N.
    {
      exact: rank_leq_row rho_AB0.
    }
    have Htau_rank : (\rank tau_A0 <= a)%N.
    {
      exact: rank_leq_row tau_A0.
    }
    pose i0 : 'I_b := Ordinal Hb_pos0.
    pose eta : 'M[C]_b := (delta_mx i0 i0 : 'M[C]_b).
    have Heta_den1 : eta \is den1mx.
    {
      apply/den1mxP; split.
      - rewrite /eta.
        exact: delta_mx_ii_psdmx.
      - by rewrite /eta tr_delta_mx_ii.
    }
    have /den1mxP [_ /eqP Heta_tr1] := Heta_den1.
    have Hlegacy_pure_extension :
        forall c : nat, forall rho_AC : 'M[C]_(a * c),
          rho_AC \is denmx ->
          \rank rho_AC = 1%N ->
          ptrace2 rho_AC = rho_A0 ->
          tau_A0 != 0 ->
          (\rank tau_A0 <= c)%N ->
          exists theta : 'M[C]_(a * c),
            theta \is denmx /\
            ptrace2 theta = tau_A0 /\
            pdmx _ rho_AC theta = pdmx _ rho_A0 tau_A0.
    {
      move=> c rho_AC HrhoAC_den HrhoAC_rank HptrAC Htau_nz Htau_rank_c.
      have HrhoAC_psd : rho_AC \is psdmx := denmx_psd HrhoAC_den.
      have [theta [Htheta_den [Htheta_rank [Htheta_ptr Htheta_fid_raw]]]] :=
        fid_iii_uhl_mx HrhoAC_den HrhoAC_rank HptrAC Htau Htau_nz Htau_rank_c.
      have Htheta_fid : fidmx _ rho_AC theta = fidmx _ rho_A0 tau_A0 :=
        Htheta_fid_raw.
      have Htheta_psd : theta \is psdmx := denmx_psd Htheta_den.
      have HrhoA_psd : rho_A0 \is psdmx.
      { rewrite -HptrAC. exact: ptrace2_psd HrhoAC_psd. }
      have Htau_psd : tau_A0 \is psdmx := denmx_psd Htau.
      exists theta; split=> //.
      split; first exact: Htheta_ptr.
      rewrite /pdmx.
      rewrite (alt_gfid_gen HrhoAC_psd Htheta_psd).
      rewrite (alt_gfid_gen HrhoA_psd Htau_psd).
      rewrite /fidmx in Htheta_fid.
      have HrhoAC_tr : \tr rho_AC = \tr rho_A0 by rewrite tr_ptrace2 HptrAC.
      have Htheta_tr : \tr theta = \tr tau_A0 by rewrite tr_ptrace2 Htheta_ptr.
      by rewrite Htheta_fid HrhoAC_tr Htheta_tr.
    }
    case Htau0 : (tau_A0 == 0).
    - move/eqP: Htau0 => Htau_eq0.
      exists (0 : 'M[C]_(a * b)); split.
      + exact: denmx0.
      + split.
        * by rewrite Htau_eq0 linear0.
        * apply: Hfid_to_pdmx.
          -- exact: psdmx0.
          -- by rewrite Htau_eq0 linear0.
          -- rewrite Htau_eq0.
             by rewrite HF_right0 HF_right0.
    - have Htau_nz : tau_A0 != 0 by rewrite Htau0.
      case Hrho0 : (rho_AB0 == 0).
      + pose taub_AB := tau_A0 *t eta.
        have Htaub_den : taub_AB \is denmx.
        {
          rewrite /taub_AB.
          exact: denmx_tens Htau (den1mx_den Heta_den1).
        }
        have Htaub_ptrace : ptrace2 taub_AB = tau_A0.
        {
          rewrite /taub_AB ptrace_tensmx Heta_tr1.
          by rewrite scale1r.
        }
        have HrhoA0 : rho_A0 = 0.
        {
          move/eqP: Hrho0 => Hrho_eq0.
          by rewrite -Hptr0 Hrho_eq0 linear0.
        }
        exists taub_AB; split=> //.
        split; first exact: Htaub_ptrace.
        apply: Hfid_to_pdmx.
        * exact: denmx_psd Htaub_den.
        * exact: Htaub_ptrace.
        * move/eqP: Hrho0 => Hrho_eq0.
          rewrite Hrho_eq0 HrhoA0 /taub_AB.
          by rewrite HF_left0 HF_left0.
      + have Hrho_nz : rho_AB0 != 0 by rewrite Hrho0.
        pose c := a * b.
        have Ha_pos : (0 < a)%N by rewrite /a; exact: dim_proper.
        have Hc_pos : (0 < c)%N.
        {
          rewrite /c muln_gt0.
          by apply/andP; split.
        }
        have [rho_ABC0 [HrhoABC0_den [HrhoABC0_rank1 HptraceABC0]]] :=
          purification_exists_in_dim Hrho Hrho_nz Hrho_rank_sys.
        pose rho_ABC : 'M[C]_(a * (b * c)) :=
          castmx_sq (esym (mulnA a b c)) rho_ABC0.
        have HrhoABC_den : rho_ABC \is denmx.
        {
          exact (Hden_cast (a * b * c) (a * (b * c))
            (esym (mulnA a b c)) rho_ABC0 HrhoABC0_den).
        }
        have HrhoABC_rank1 : \rank rho_ABC = 1%N.
        {
          rewrite /rho_ABC
            (Hrank_castmx_sq (a * b * c) (a * (b * c))
              (esym (mulnA a b c)) rho_ABC0).
          exact: HrhoABC0_rank1.
        }
        have HrhoABC_ptrace : ptrace2 rho_ABC = rho_A0.
        {
          rewrite /rho_ABC Hptrace2_regroup HptraceABC0.
          exact: Hptr0.
        }
        pose rho_big0 : 'M[C]_((a * (b * c)) * b) := rho_ABC *t eta.
        pose rho_big : 'M[C]_(a * ((b * c) * b)) :=
          castmx_sq (esym (mulnA a (b * c) b)) rho_big0.
        have HrhoBig_den : rho_big \is denmx.
        {
          exact (Hden_cast ((a * (b * c)) * b) (a * ((b * c) * b))
            (esym (mulnA a (b * c) b)) rho_big0
            (denmx_tens HrhoABC_den (den1mx_den Heta_den1))).
        }
        have HrhoBig_rank1 : \rank rho_big = 1%N.
        {
          have Heta_rank1 : \rank eta = 1%N.
          {
            have Houter :
                eta =
                (delta_mx i0 (0 : 'I_1) : 'M[C]_(b, 1)) *m
                  (delta_mx i0 (0 : 'I_1))^*t.
            {
              apply/matrixP => p q.
              rewrite !mxE big_ord1 !mxE conjC_nat.
              by case: (p == i0); case: (q == i0) => //=;
                 rewrite ?mul1r ?mul0r ?mulr0.
            }
            apply/eqP; rewrite eqn_leq; apply/andP; split.
            - rewrite Houter.
              apply: (leq_trans (mxrankM_maxl _ _)).
              exact: rank_leq_col.
            - rewrite lt0n mxrank_eq0.
              apply/eqP => Heta0.
              have Htr_ne0 : \tr eta != 0 by rewrite Heta_tr1 oner_eq0.
              by rewrite Heta0 mxtrace0 eqxx in Htr_ne0.
          }
          rewrite /rho_big
            (Hrank_castmx_sq ((a * (b * c)) * b) (a * ((b * c) * b))
              (esym (mulnA a (b * c) b)) rho_big0).
          rewrite /rho_big0 rank_tens HrhoABC_rank1 Heta_rank1 /=.
          reflexivity.
        }
        have HrhoBig_ptrace : ptrace2 rho_big = rho_A0.
        {
          rewrite /rho_big /rho_big0 Hptrace2_regroup.
          rewrite ptrace_tensmx Heta_tr1 scale1r.
          exact: HrhoABC_ptrace.
        }
        have Htau_rank_big : (\rank tau_A0 <= ((b * c) * b))%N.
        {
          rewrite /c.
          apply: (leq_trans Htau_rank).
          have Hcube_pos : (0 < b * (b * b))%N.
          {
            rewrite muln_gt0.
            apply/andP; split=> //.
            rewrite muln_gt0.
            by apply/andP; split.
          }
          have Hone_le : (1 <= b * (b * b))%N := Hcube_pos.
          have Hrhs_eq : ((b * c) * b)%N = a * (b * (b * b)).
          {
            rewrite /c.
            transitivity ((a * (b * b)) * b)%N.
            - apply: (congr1 (fun x => x * b)).
              exact: mulnCA.
            - rewrite -mulnA.
              apply: (congr1 (fun x => a * x)).
              exact: esym (mulnA b b b).
          }
          rewrite Hrhs_eq.
          exact: leq_pmulr Hone_le.
        }
        have [theta_big [HthetaBig_den [HthetaBig_ptrace HthetaBig_dist]]] :=
          Hlegacy_pure_extension ((b * c) * b) rho_big
            HrhoBig_den HrhoBig_rank1 HrhoBig_ptrace Htau_nz Htau_rank_big.
        pose theta_big0 : 'M[C]_((a * (b * c)) * b) :=
          castmx_sq (mulnA a (b * c) b) theta_big.
        pose theta_mid : 'M[C]_(a * (b * c)) := ptrace2 theta_big0.
        pose taub_view : 'M[C]_((a * b) * c) :=
          castmx_sq (mulnA a b c) theta_mid.
        pose taub_AB : 'M[C]_(a * b) := ptrace2 taub_view.
        have HthetaBig0_den : theta_big0 \is denmx.
        {
          exact (Hden_cast (a * ((b * c) * b)) ((a * (b * c)) * b)
            (mulnA a (b * c) b) theta_big HthetaBig_den).
        }
        have HthetaMid_den : theta_mid \is denmx := ptrace2_denmx HthetaBig0_den.
        have HtaubView_den : taub_view \is denmx.
        {
          exact (Hden_cast (a * (b * c)) ((a * b) * c)
            (mulnA a b c) theta_mid HthetaMid_den).
        }
        have Htaub_den : taub_AB \is denmx := ptrace2_denmx HtaubView_den.
        have HthetaMid_ptrace : ptrace2 theta_mid = tau_A0.
        {
          rewrite /theta_mid /theta_big0.
          rewrite -[ptrace2 (ptrace2 (castmx_sq (mulnA a (b * c) b) theta_big))]
                  (Hptrace2_regroup _ _ _ (castmx_sq (mulnA a (b * c) b) theta_big)).
          have -> :
              castmx_sq (esym (mulnA a (b * c) b))
                (castmx_sq (mulnA a (b * c) b) theta_big) = theta_big.
          {
            by rewrite /castmx_sq castmxK.
          }
          exact: HthetaBig_ptrace.
        }
        have Htaub_ptrace : ptrace2 taub_AB = tau_A0.
        {
          rewrite /taub_AB /taub_view.
          rewrite -[ptrace2 (ptrace2 (castmx_sq (mulnA a b c) theta_mid))]
                  (Hptrace2_regroup _ _ _ (castmx_sq (mulnA a b c) theta_mid)).
          have -> :
              castmx_sq (esym (mulnA a b c))
                (castmx_sq (mulnA a b c) theta_mid) = theta_mid.
          {
            by rewrite /castmx_sq castmxK.
          }
          exact: HthetaMid_ptrace.
        }
        have Hcast_big : pdmx _ rho_big0 theta_big0 = pdmx _ rho_big theta_big.
        {
          have Hrho_bigK :
              castmx_sq (esym (mulnA a (b * c) b)) rho_big0 = rho_big.
          {
            by rewrite /rho_big.
          }
          have Htheta_bigK :
              castmx_sq (esym (mulnA a (b * c) b)) theta_big0 = theta_big.
          {
            by rewrite /theta_big0 /castmx_sq castmxK.
          }
          rewrite -Hrho_bigK -Htheta_bigK.
          apply: esym.
          exact (Hpdmx_cast ((a * (b * c)) * b) (a * ((b * c) * b))
            (esym (mulnA a (b * c) b)) rho_big0 theta_big0).
        }
        have Hcast_mid : pdmx _ rho_ABC0 taub_view = pdmx _ rho_ABC theta_mid.
        {
          have Hrho_ABCK :
              castmx_sq (esym (mulnA a b c)) rho_ABC0 = rho_ABC.
          {
            by rewrite /rho_ABC.
          }
          have Htaub_viewK :
              castmx_sq (esym (mulnA a b c)) taub_view = theta_mid.
          {
            by rewrite /taub_view /castmx_sq castmxK.
          }
          rewrite -Hrho_ABCK -Htaub_viewK.
          apply: esym.
          exact (Hpdmx_cast ((a * b) * c) (a * (b * c))
            (esym (mulnA a b c)) rho_ABC0 taub_view).
        }
        have Hupper_mid : pdmx _ rho_ABC theta_mid <= pdmx _ rho_A0 tau_A0.
        {
          have Hrho_big0_psd : rho_big0 \is psdmx.
          {
            rewrite /rho_big0.
            apply: psdmx_tens.
            - exact: denmx_psd HrhoABC_den.
            - exact: denmx_psd (den1mx_den Heta_den1).
          }
          have Htheta_big0_psd : theta_big0 \is psdmx.
          {
            exact: castmx_sq_psdmx (denmx_psd HthetaBig_den).
          }
          have Hmono := Hpdmx_ptrace2 (a * (b * c)) b rho_big0 theta_big0
            Hb_pos0 Hrho_big0_psd Htheta_big0_psd.
          rewrite /rho_big0 /theta_big0 in Hmono.
          rewrite ptrace_tensmx Heta_tr1 scale1r in Hmono.
          rewrite Hcast_big HthetaBig_dist in Hmono.
          exact: Hmono.
        }
        have Hupper : pdmx _ rho_AB0 taub_AB <= pdmx _ rho_A0 tau_A0.
        {
          have Hmono := Hpdmx_ptrace2 (a * b) c rho_ABC0 taub_view
            Hc_pos (denmx_psd HrhoABC0_den) (denmx_psd HtaubView_den).
          rewrite HptraceABC0 Hcast_mid in Hmono.
          exact: le_trans Hmono Hupper_mid.
        }
        have Hlower : pdmx _ rho_A0 tau_A0 <= pdmx _ rho_AB0 taub_AB.
        {
          have Hmono := Hpdmx_ptrace2 a b rho_AB0 taub_AB
            Hb_pos0 (denmx_psd Hrho) (denmx_psd Htaub_den).
          by rewrite Hptr0 Htaub_ptrace in Hmono.
        }
        exists taub_AB; split=> //.
        split; first exact: Htaub_ptrace.
        apply/eqP; rewrite eq_le; apply/andP; split=> //.
    }
  have Hb_pos : (0 < b)%N by rewrite /b; exact: dim_proper.
  have [taub_AB [Htaub_den [Htaub_ptr Htaub_pd]]] :=
    Hmatrix_pd_ext rho_AB (h2mx rho) (h2mx tau) Hb_pos HrhoAB_den Hptr_mx Htau_mx_den.
  pose taubar := mx2h (U *m taub_AB *m U^*t).
  have Htaubar_h2mx : h2mx taubar = U *m taub_AB *m U^*t
    by rewrite /taubar mx2hK.
  have Htaub_mx_psd : taub_AB \is psdmx := denmx_psd Htaub_den.
  have Htaubar_mx_psd : h2mx taubar \is psdmx.
  { rewrite Htaubar_h2mx.
    exact: psdmx_bimap_closed_gen Htaub_mx_psd. }
  have Htaubar_den : taubar \is denlf.
  {
    move/denmxP: Htaub_den => [_ Htr_taub].
    rewrite qualifE.
    apply/denmxP; split=> //.
    rewrite Htaubar_h2mx mxtrace_mulC mulmxA.
    by rewrite Uadj_mul_U mul1mx.
  }
  have Htaubar_conj : U^*t *m h2mx taubar *m U = taub_AB.
  {
    rewrite Htaubar_h2mx !mulmxA.
    rewrite Uadj_mul_U mul1mx -mulmxA.
    by rewrite Uadj_mul_U mulmx1.
  }
  have Htaubar_ptr : ptrace_cast disAB taubar = tau.
  {
    apply/h2mx_inj.
    rewrite (h2mx_ptrace_cast_ptrace2 disAB taubar) Htaubar_conj.
    exact: Htaub_ptr.
  }
  exists taubar; split=> //.
  split; first exact: Htaubar_ptr.
  rewrite /pur_dist /gfid /pdmx in Htaub_pd *.
  have -> : gfidelity (h2mx rhobar) (h2mx taubar) = gfidelity rho_AB taub_AB.
  {
    rewrite (gfid_tenv_mxU_conj_eq_mx disAB Hrhobar_mx_psd Htaubar_mx_psd).
    by rewrite /rho_AB Htaubar_conj.
  }
  exact: Htaub_pd.
Qed.

(* tex: co:pd-ext — Tomamichel, 'A Framework for Non-Asymptotic Quantum *)
(*   Information Theory' (PhD thesis, arXiv:1203.2142), Corollary 3.6;  *)
(*   subnormalized form required by th:data-proc (Theorem 5.7) where    *)
(*   states live in S_<= rather than S_=1.                              *)
(* path: utils:pd_ext_subnorm -> entropy:entropy_data_proc -> *)
(*   bb84:bb84_secret *)
Lemma pd_ext_subnorm (rho tau : 'F[HL]_A) (rhobar : 'F[HL]_S_AB) :
  rhobar \is psdlf ->
  @complex.Re R (\Tr rhobar) <= 1 ->
  ptrace_cast disAB rhobar = rho ->
  tau \is psdlf ->
  @complex.Re R (\Tr tau) <= 1 ->
  exists taubar : 'F[HL]_S_AB,
    taubar \is psdlf /\
    @complex.Re R (\Tr taubar) <= 1 /\
    ptrace_cast disAB taubar = tau /\
    pur_dist rhobar taubar = pur_dist rho tau.
Proof.
  move=> Hrhobar_psd Hrhobar_tr Hptr Htau_psd Htau_tr.
  pose a := dim 'H[HL]_A.
  pose b := dim 'H[HL]_B.
  pose k := a.
  pose U := @tenv_mxU R L HL A B.
  pose pdmx := fun n (X Y : 'M[C]_n) => Num.sqrt (1 - (gfidelity X Y)^2).
  have HU : U \is unitarymx := tenv_mxU_unitarymx _ _.
  have HUadj : U^*t \is unitarymx := tenv_mxU_adj_unitarymx disAB.
  have U_mul_Uadj : U *m U^*t = 1%:M := unitarymxK HU.
  have Uadj_mul_U : U^*t *m U = 1%:M.
  {
    by have := unitarymxK HUadj; rewrite adjmxK.
  }
  have Hrhobar_mx_psd : h2mx rhobar \is psdmx
    by move: Hrhobar_psd; rewrite qualifE.
  have Htau_mx_psd : h2mx tau \is psdmx
    by move: Htau_psd; rewrite qualifE.
  pose rho_AB := U^*t *m h2mx rhobar *m U.
  have HrhoAB_psd : rho_AB \is psdmx.
  {
    rewrite /rho_AB -[U in _ *m _ *m U]adjmxK.
    exact: psdmx_bimap_closed_gen Hrhobar_mx_psd.
  }
  have Htr_rhoAB_eq : \tr rho_AB = \Tr rhobar.
  {
    rewrite /rho_AB mxtrace_mulC mulmxA.
    by rewrite U_mul_Uadj mul1mx.
  }
  have HrhoAB_tr : @complex.Re R (\tr rho_AB) <= 1.
  {
    by rewrite Htr_rhoAB_eq.
  }
  have Hptr_mx : ptrace2 rho_AB = h2mx rho.
  {
    rewrite /rho_AB -(h2mx_ptrace_cast_ptrace2 disAB rhobar).
    exact (f_equal h2mx Hptr).
  }
  have Hb_pos : (0 < b)%N by rewrite /b; exact: dim_proper.
  have Ha_pos : (0 < a)%N by rewrite /a; exact: dim_proper.
  have Hk_pos : (0 < k)%N by rewrite /k.
  pose i0 : 'I_k := Ordinal Hk_pos.
  pose eta : 'M[C]_k := (delta_mx i0 i0 : 'M[C]_k).
  have Heta_den1 : eta \is den1mx.
  {
    apply/den1mxP; split.
    - rewrite /eta.
      exact: delta_mx_ii_psdmx.
    - by rewrite /eta tr_delta_mx_ii.
  }
  have /den1mxP [Heta_psd /eqP Heta_tr1] := Heta_den1.
  have Hptrace2_regroup : forall m n l (A0 : 'M[C]_((m * n) * l)),
      ptrace2 (castmx_sq (esym (mulnA m n l)) A0) = ptrace2 (ptrace2 A0).
  {
    move=> m n l A0.
    have ptrace2E' : forall s t (B0 : 'M[C]_(s * t)) r1 r2,
        ptrace2 B0 r1 r2 =
        \sum_(k0 : 'I_t) B0 (mxtens_index (r1, k0)) (mxtens_index (r2, k0)).
    {
      move=> s t B0 r1 r2.
      rewrite ptrace2E1 ptrace1E.
      by apply: eq_bigr => k0 _; rewrite mxE !mxtens_indexK.
    }
    have mxtens_assoc : forall (i : 'I_m) (j : 'I_n) (l0 : 'I_l),
        cast_ord (mulnA m n l) (mxtens_index (i, mxtens_index (j, l0))) =
        mxtens_index (mxtens_index (i, j), l0).
    {
      move=> i j l0.
      apply/val_inj => /=.
      by rewrite mulnDl mulnA addnA.
    }
    apply/matrixP => i j.
    rewrite ptrace2E'.
    transitivity
      (\sum_(j0 : 'I_n) \sum_(l0 : 'I_l)
        A0 (mxtens_index (mxtens_index (i, j0), l0))
           (mxtens_index (mxtens_index (j, j0), l0))).
    {
      rewrite (reindex (@mxtens_index n l))/=.
      2:{
        exists (@mxtens_unindex n l) => l0 /=.
        - by rewrite ?mxtens_indexK ?mxtens_unindexK -?surjective_pairing.
        - by rewrite ?mxtens_indexK ?mxtens_unindexK -?surjective_pairing.
      }
      rewrite pair_bigV /=.
      apply: eq_bigr => j0 _; apply: eq_bigr => l0 _.
      by rewrite castmxE /= esymK !mxtens_assoc.
    }
    rewrite ptrace2E'.
    by apply: eq_bigr => j0 _; rewrite ptrace2E'.
  }
  have Hpdmx_cast : forall (n n' : nat) (eq_n : n = n') (X Y : 'M[C]_n),
      pdmx _ (castmx_sq eq_n X) (castmx_sq eq_n Y) = pdmx _ X Y.
  {
    move=> n n' eq_n X Y.
    rewrite /pdmx /castmx_sq.
    by rewrite gfid_cast_mx.
  }
  have Hpdmx_ptrace2 :
      forall m n (X Y : 'M[C]_(m * n)),
        (0 < n)%N ->
        X \is psdmx -> Y \is psdmx ->
        pdmx _ (ptrace2 X) (ptrace2 Y) <= pdmx _ X Y.
  {
    move=> m n X Y Hn0 HX HY.
    have Hmono := gfid_ptr_mono_mx Hn0 HX HY.
    have HXY_ge0 := gfid_ge0_mx HX HY.
    have Hpt_ge0 := gfid_ge0_mx (ptrace2_psd HX) (ptrace2_psd HY).
    rewrite /pdmx.
    apply: ler_wsqrtr.
    apply: lerB; first exact: lexx.
    by rewrite ler_sqr ?nnegrE.
  }
  pose psi_big0 : 'M[C]_((a * b) * k) := rho_AB *t eta.
  pose psi_big : 'M[C]_(a * (b * k)) :=
    castmx_sq (esym (mulnA a b k)) psi_big0.
  have Hpsi_big0_psd : psi_big0 \is psdmx.
  {
    rewrite /psi_big0.
    exact: psdmx_tens HrhoAB_psd Heta_psd.
  }
  have Hpsi_big_psd : psi_big \is psdmx.
  {
    exact: castmx_sq_psdmx Hpsi_big0_psd.
  }
  have Hpsi_big_tr : @complex.Re R (\tr psi_big) <= 1.
  {
    rewrite /psi_big mxtrace_castmx_sq /psi_big0 mxtrace_tens Heta_tr1.
    by rewrite mulr1.
  }
  have Hpsi_big_ptr : ptrace2 psi_big = h2mx rho.
  {
    rewrite /psi_big Hptrace2_regroup /psi_big0 ptrace_tensmx Heta_tr1.
    by rewrite scale1r Hptr_mx.
  }
  have Htau_rank : (\rank (h2mx tau) <= b * k)%N.
  {
    have Hrank_a : (\rank (h2mx tau) <= a)%N := rank_leq_row (h2mx tau).
    apply: (leq_trans Hrank_a).
    rewrite /k.
    rewrite -{1}(mul1n a).
    apply: leq_mul; last exact: leqnn.
    exact: Hb_pos.
  }
  have [theta_big [Htheta_big_psd Htheta_big_tr Htheta_big_ptr Htheta_gfid]] :=
    @subnorm_matrix_uhlmann_arbitrary_rank R a (b * k) psi_big
      (h2mx rho) (h2mx tau)
      Hpsi_big_psd Hpsi_big_tr Hpsi_big_ptr
      Htau_mx_psd Htau_tr Htau_rank.
  pose theta_big0 : 'M[C]_((a * b) * k) :=
    castmx_sq (mulnA a b k) theta_big.
  pose theta_AB : 'M[C]_(a * b) := ptrace2 theta_big0.
  have Htheta_big0_psd : theta_big0 \is psdmx.
  {
    exact: castmx_sq_psdmx Htheta_big_psd.
  }
  have HthetaAB_psd : theta_AB \is psdmx.
  {
    exact: ptrace2_psd Htheta_big0_psd.
  }
  have HthetaAB_tr : @complex.Re R (\tr theta_AB) <= 1.
  {
    have Htr_eq : \tr theta_AB = \tr theta_big.
    {
      rewrite /theta_AB -tr_ptrace2 /theta_big0.
      exact: (@mxtrace_castmx_sq R (a * (b * k)) ((a * b) * k)
        (mulnA a b k) theta_big).
    }
    by rewrite Htr_eq.
  }
  have HthetaAB_ptr : ptrace2 theta_AB = h2mx tau.
  {
    rewrite /theta_AB /theta_big0.
    rewrite -[ptrace2 (ptrace2 (castmx_sq (mulnA a b k) theta_big))]
            (Hptrace2_regroup _ _ _ (castmx_sq (mulnA a b k) theta_big)).
    have -> :
        castmx_sq (esym (mulnA a b k))
          (castmx_sq (mulnA a b k) theta_big) = theta_big.
    {
      by rewrite /castmx_sq castmxK.
    }
    exact: Htheta_big_ptr.
  }
  have Hcast_big : pdmx _ psi_big0 theta_big0 = pdmx _ psi_big theta_big.
  {
    have Hpsi_bigK :
        castmx_sq (esym (mulnA a b k)) psi_big0 = psi_big.
    {
      by rewrite /psi_big.
    }
    have Htheta_bigK :
        castmx_sq (esym (mulnA a b k)) theta_big0 = theta_big.
    {
      by rewrite /theta_big0 /castmx_sq castmxK.
    }
    rewrite -Hpsi_bigK -Htheta_bigK.
    apply: esym.
    exact (Hpdmx_cast ((a * b) * k) (a * (b * k))
      (esym (mulnA a b k)) psi_big0 theta_big0).
  }
  have Hpdmx_big_eq : pdmx _ psi_big theta_big = pdmx _ (h2mx rho) (h2mx tau).
  {
    by rewrite /pdmx Htheta_gfid.
  }
  have Hupper : pdmx _ rho_AB theta_AB <= pdmx _ (h2mx rho) (h2mx tau).
  {
    have Hmono := Hpdmx_ptrace2 (a * b) k psi_big0 theta_big0
      Hk_pos Hpsi_big0_psd Htheta_big0_psd.
    rewrite /psi_big0 ptrace_tensmx Heta_tr1 scale1r in Hmono.
    rewrite Hcast_big Hpdmx_big_eq in Hmono.
    exact: Hmono.
  }
  have Hlower : pdmx _ (h2mx rho) (h2mx tau) <= pdmx _ rho_AB theta_AB.
  {
    have Hmono := Hpdmx_ptrace2 a b rho_AB theta_AB
      Hb_pos HrhoAB_psd HthetaAB_psd.
    by rewrite Hptr_mx HthetaAB_ptr in Hmono.
  }
  have Hpdmx_eq : pdmx _ rho_AB theta_AB = pdmx _ (h2mx rho) (h2mx tau).
  {
    apply/eqP; rewrite eq_le; apply/andP; split=> //.
  }
  pose taubar := mx2h (U *m theta_AB *m U^*t).
  have Htaubar_h2mx : h2mx taubar = U *m theta_AB *m U^*t
    by rewrite /taubar mx2hK.
  have Htaubar_mx_psd : h2mx taubar \is psdmx.
  {
    rewrite Htaubar_h2mx.
    exact: psdmx_bimap_closed_gen HthetaAB_psd.
  }
  have Htaubar_psd : taubar \is psdlf by rewrite qualifE.
  have Htaubar_tr : @complex.Re R (\Tr taubar) <= 1.
  {
    rewrite /lftrace Htaubar_h2mx mxtrace_mulC mulmxA.
    by rewrite Uadj_mul_U mul1mx.
  }
  have Htaubar_conj : U^*t *m h2mx taubar *m U = theta_AB.
  {
    rewrite Htaubar_h2mx !mulmxA.
    rewrite Uadj_mul_U mul1mx -mulmxA.
    by rewrite Uadj_mul_U mulmx1.
  }
  have Htaubar_ptr : ptrace_cast disAB taubar = tau.
  {
    apply/h2mx_inj.
    rewrite (h2mx_ptrace_cast_ptrace2 disAB taubar) Htaubar_conj.
    exact: HthetaAB_ptr.
  }
  exists taubar; split; first exact: Htaubar_psd.
  split; first exact: Htaubar_tr.
  split; first exact: Htaubar_ptr.
  rewrite /pur_dist /gfid /pdmx in Hpdmx_eq *.
  have -> : gfidelity (h2mx rhobar) (h2mx taubar) = gfidelity rho_AB theta_AB.
  {
    rewrite (gfid_tenv_mxU_conj_eq_mx disAB Hrhobar_mx_psd Htaubar_mx_psd).
    by rewrite /rho_AB Htaubar_conj.
  }
  exact: Hpdmx_eq.
Qed.

End PurDistExtension.

(* Tensor with normalized identity: closed PSD/trace support facts. *)

Section PurDistTensorMmix.
Variable (L : finType) (HL : L -> chsType) (A B : {set L}).
Hypothesis disAB : [disjoint A & B].
Notation S_AB := (A :|: B).

(* psdlf_scale_tensor_id_mmix *)(* psdlf_scale_tensor_id_mmix *)
(* infra: no tex label — fundamental & reusable (mathcomp-style) *)
(* consumer: psdlf_scale_tensor_id_mmix is used downstream by the BB84 secrecy proof. *)
(* path: utils:psdlf_scale_tensor_id_mmix -> utils:pd_mono -> *)
(*   entropy:entropy_data_proc -> *)
(*   bb84:bb84_secret *)
Lemma psdlf_scale_tensor_id_mmix (sigma : 'F[HL]_B) :
  sigma \is psdlf ->
  ((dim 'H[HL]_A)%:R^-1 *: ((\1 : 'F[HL]_A) \⊗ sigma)) \is psdlf.
Proof.
  move=> Hsigma.
  apply: psdlfZ; first by rewrite invr_ge0 ler0n.
  rewrite qualifE h2mx_tenf.
  apply: psdmx_bimap_closed_gen.
  rewrite h2mx1; apply: psdmx_tens; first exact: psdmx1.
  by move: Hsigma; rewrite qualifE.
Qed.

(* trlf_scale_tensor_id_mmix *)
(* infra: no tex label — fundamental & reusable (mathcomp-style) *)
(* consumer: trlf_scale_tensor_id_mmix is used downstream by the BB84 secrecy proof. *)
(* path: utils:trlf_scale_tensor_id_mmix -> utils:pd_mono -> *)
(*   entropy:entropy_data_proc -> *)
(*   bb84:bb84_secret *)
Lemma trlf_scale_tensor_id_mmix (sigma : 'F[HL]_B) :
  (0 < dim 'H[HL]_A)%N ->
  \Tr ((dim 'H[HL]_A)%:R^-1 *: ((\1 : 'F[HL]_A) \⊗ sigma)) = \Tr sigma.
Proof.
  move=> Hd.
  rewrite linearZ/= lftrace_tenf ?disAB//.
  have Htr1 : \Tr (\1 : 'F[HL]_A) = (dim 'H[HL]_A)%:R.
  { rewrite lftrace_baseE.
    under eq_bigr do rewrite lfunE/= ns_dot.
    by rewrite sumr_const card_ord. }
  rewrite Htr1 mulrA mulVf ?mul1r//.
  by rewrite pnatr_eq0 -lt0n.
Qed.

(* Trace preservation of ptrace_castl (TP property of the partial trace). *)
(* trlf_ptrace_castl *)
(* infra: no tex label — fundamental & reusable (mathcomp-style) *)
(* consumer: trlf_ptrace_castl is used downstream by the BB84 secrecy proof. *)
(* path: utils:trlf_ptrace_castl -> lhl:min_coll_bound -> *)
(*   bb84:privacy_amplification -> bb84:bb84_secret *)
Lemma trlf_ptrace_castl (f : 'F[HL]_S_AB) :
  \Tr (ptrace_castl disAB f) = \Tr f.
Proof.
  rewrite /ptrace_castl /ptrace_cast_gen castlf_trlfE.
  have /cptpP [_ /tpmapP Htp] := @ptraceso_qc R L HL A S_AB.
  exact: Htp.
Qed.

End PurDistTensorMmix.

(* ================================================================== *)
(* pd invariance under bipartite unitary conjugation (U ⊗ V)          *)
(* tex: implicit in pr:pd-metric + th:pd-mono with isometry both ways   *)
(* math: pd((U⊗V) τ (U⊗V)†, (U⊗V) σ (U⊗V)†) = pd(τ, σ)                 *)
(* ================================================================== *)

Section PurDistUnitaryConj.
Variable (L : finType) (HL : L -> chsType) (A B : {set L}).
Hypothesis disAB : [disjoint A & B].
Notation S_AB := (A :|: B).

(* path: utils:psdlf_unitary_conj_OV -> utils:pd_mono -> *)
(*   entropy:entropy_data_proc -> *)
(*   bb84:bb84_secret *)
Lemma psdlf_unitary_conj_OV (U : 'F[HL]_A) (V : 'F[HL]_B)
    (rho : 'F[HL]_S_AB) :
  U \is unitarylf -> V \is unitarylf ->
  rho \is psdlf ->
  ((U \O V) \o rho \o (U \O V)^A) \is psdlf.
Proof.
  move=> _ _ Hrho; apply/psdlfP => v.
  rewrite comp_lfunE comp_lfunE -adj_dotEl.
  by move/psdlfP : Hrho.
Qed.

(* Adjoint distributes over sdot when supports are disjoint.             *)
(* path: utils:sdot_adj_OV -> utils:pd_mono -> entropy:entropy_data_proc -> *)
(*   bb84:bb84_secret *)
Lemma sdot_adj_OV (U : 'F[HL]_A) (V : 'F[HL]_B) :
  (U \O V)^A = U^A \O V^A.
Proof.
  apply/to_Fnd_inj.
  rewrite to_Fnd_adjE !(sdotFT _ _ disAB).
  by rewrite -[LHS]/(to_Fnd ((U \⊗ V)^A)) tenf_adj.
Qed.

(* pd_unitary_conj_OV *)
(* infra: no tex label — fundamental & reusable (mathcomp-style) *)
(* consumer: pd_unitary_conj_OV is used downstream by the BB84 secrecy proof. *)
(* path: utils:pd_unitary_conj_OV -> utils:pd_mono -> *)
(*   entropy:entropy_data_proc -> *)
(*   bb84:bb84_secret *)
Lemma pd_unitary_conj_OV (U : 'F[HL]_A) (V : 'F[HL]_B)
    (rho tau : 'F[HL]_S_AB) :
  U \is unitarylf -> V \is unitarylf ->
  rho \is psdlf -> tau \is psdlf ->
  @complex.Re R (\Tr rho) <= 1 -> @complex.Re R (\Tr tau) <= 1 ->
  pur_dist ((U \O V) \o tau \o (U \O V)^A)
           ((U \O V) \o rho \o (U \O V)^A) =
  pur_dist tau rho.
Proof.
  move=> HU HV Prho Ptau Htr_rho Htr_tau.
  have HUV_unitlf : (U \O V) \is unitarylf.
  { apply/unitarylfP.
    move: HU HV => /unitarylfP HU /unitarylfP HV.
    rewrite sdot_adj_OV.
    have H1 : (U^A \⊗ V^A) \o (U \⊗ V) = (\1 : 'F[HL]_S_AB).
    { by rewrite -tenf_comp ?disAB// HU HV tenf11. }
    apply/to_Fnd_inj.
    rewrite to_Fnd_compE !(sdotFT _ _ disAB) -!to_Fnd_tenE -dotF_comp.
    by rewrite H1. }
  have HUV_mx_unit : h2mx (U \O V) \is unitarymx.
  { apply/unitarymxPV.
    rewrite -h2mx_adj -h2mx_comp.
    by move: HUV_unitlf => /unitarylfP ->; rewrite h2mx1. }
  rewrite /pur_dist /gfid !h2mx_comp !h2mx_adj.
    have Hrho_mx : h2mx rho \is psdmx by move: Prho; rewrite qualifE.
    have Htau_mx : h2mx tau \is psdmx by move: Ptau; rewrite qualifE.
    have Htr_rho_mx : @complex.Re R (\tr (h2mx rho)) <= 1 by move: Htr_rho.
    have Htr_tau_mx : @complex.Re R (\tr (h2mx tau)) <= 1 by move: Htr_tau.
    have Hrho_mx_den : h2mx rho \is denmx :=
      denmx_psd_re_tr_le Hrho_mx Htr_rho_mx.
    have Htau_mx_den : h2mx tau \is denmx :=
      denmx_psd_re_tr_le Htau_mx Htr_tau_mx.
    by rewrite (gfid_unitary_conj_mx HUV_mx_unit Htau_mx_den Hrho_mx_den).
Qed.

(* trlf_unitary_conj_OV *)
(* infra: no tex label — fundamental & reusable (mathcomp-style) *)
(* consumer: trlf_unitary_conj_OV is used downstream by the BB84 secrecy proof. *)
(* path: utils:trlf_unitary_conj_OV -> utils:pd_mono -> *)
(*   entropy:entropy_data_proc -> *)
(*   bb84:bb84_secret *)
Lemma trlf_unitary_conj_OV (U : 'F[HL]_A) (V : 'F[HL]_B)
    (rho : 'F[HL]_S_AB) :
  U \is unitarylf -> V \is unitarylf ->
  \Tr ((U \O V) \o rho \o (U \O V)^A) = \Tr rho.
Proof.
  move=> /unitarylfP HU /unitarylfP HV.
  have Hinv : (U \O V)^A \o (U \O V) = (\1 : 'F[HL]_S_AB).
  { rewrite sdot_adj_OV.
    have H1 : (U^A \⊗ V^A) \o (U \⊗ V) = (\1 : 'F[HL]_S_AB).
    { by rewrite -tenf_comp ?disAB// HU HV tenf11. }
    apply/to_Fnd_inj.
    rewrite to_Fnd_compE !(sdotFT _ _ disAB) -!to_Fnd_tenE -dotF_comp.
    by rewrite H1. }
  rewrite lftraceC comp_lfunA Hinv.
  by rewrite comp_lfun1l.
Qed.

(* Unitary conjugation sandwich: inverting by adjoint returns original.  *)
(* sdot_conj_inv_OV *)
(* infra: no tex label — fundamental & reusable (mathcomp-style) *)
(* consumer: sdot_conj_inv_OV is used downstream by the BB84 secrecy proof. *)
(* path: utils:sdot_conj_inv_OV -> utils:pd_mono -> entropy:entropy_data_proc -> *)
(*   bb84:bb84_secret *)
Lemma sdot_conj_inv_OV (U : 'F[HL]_A) (V : 'F[HL]_B)
    (rho : 'F[HL]_S_AB) :
  U \is unitarylf -> V \is unitarylf ->
  (U^A \O V^A) \o ((U \O V) \o rho \o (U \O V)^A) \o (U \O V) = rho.
Proof.
  move=> /unitarylfP HU /unitarylfP HV.
  have Hinv : (U \O V)^A \o (U \O V) = (\1 : 'F[HL]_S_AB).
  { rewrite sdot_adj_OV.
    have H1 : (U^A \⊗ V^A) \o (U \⊗ V) = (\1 : 'F[HL]_S_AB).
    { by rewrite -tenf_comp ?disAB// HU HV tenf11. }
    apply/to_Fnd_inj.
    rewrite to_Fnd_compE !(sdotFT _ _ disAB) -!to_Fnd_tenE -dotF_comp.
    by rewrite H1. }
  rewrite -sdot_adj_OV -!comp_lfunA Hinv comp_lfun1r.
  by rewrite comp_lfunA Hinv comp_lfun1l.
Qed.

End PurDistUnitaryConj.

(* ================================================================== *)
(* CPTN contraction of purified distance (th:pd-mono).   *)
(* tex: th:pd-mono — Tomamichel, 'A Framework for Non-Asymptotic        *)
(*   Quantum Information Theory' (PhD thesis, arXiv:1203.2142),         *)
(*   Theorem 3.4 — trace non-increasing maps do                        *)
(* not increase purified distance. CPTN is the tex form; CPTP is a     *)
(* specialization.                                                      *)
(* Consumers: pd_mono_cptp (corollary below), pd_mono_post_hash        *)
(* (lhl/util.v), cq_smoothing (lhl/util.v), smooth_hmin/hmax_dpi      *)
(* (smooth/dpi.v).                                                     *)
(* ================================================================== *)

Section PurDistCPTN.
Variables (L : finType) (HL : L -> chsType).
Variables (U V : {set L}).

(* ================================================================== *)
(* pd_mono: monotonicity of purified distance             *)
(* tex: th:pd-mono — Tomamichel, 'A Framework for Non-Asymptotic        *)
(*   Quantum Information Theory' (PhD thesis, arXiv:1203.2142),         *)
(*   Theorem 3.4                                                        *)
(* Statement from CoqQ-2 (utils/dist/pd.v:1572): for sub-normalized     *)
(* states rho, tau and a trace non-increasing CPM E,                    *)
(*   F(rho, tau) <= F(E rho, E tau)   and                               *)
(*   P(E rho, E tau) <= P(rho, tau).                                     *)
(* ================================================================== *)
(* path: utils:pd_mono_core -> utils:pd_mono -> entropy:entropy_data_proc -> *)
(*   bb84:bb84_secret *)
(* stinespring_mx (matrix Stinespring dilation, completed/embedded form):    *)
(* a trace-non-increasing CPM `E` lifts to an isometry `Wc` on the +1-leak    *)
(* embedded space whose ancilla partial trace recovers `E` on every           *)
(* sub-normalized input.  Matrix twin of `stinespring` (utils/dist/dilation.v); *)
(* `pd_mono_core` calls it instead of inlining the block-matrix construction.  *)
(* path: utils:stinespring_embed_mx -> utils:pd_mono -> *)
(*   entropy:entropy_data_proc -> bb84:bb84_secret *)
Local Lemma stinespring_embed_mx (E : 'SO[HL]_(U, V)) :
  E \is cptn ->
  exists Wc : 'M[C]_((dim 'H[HL]_V + 1) *
                     (dim 'H[HL]_U * dim 'H[HL]_V + (dim 'H[HL]_U + 1)),
                     dim 'H[HL]_U + 1),
    Wc^*t *m Wc = 1%:M /\
    (forall sigma : 'F[HL]_U,
       ptrace2 (Wc *m embed_subnorm (h2mx sigma) *m Wc^*t) =
       embed_subnorm (h2mx (E sigma))).
Proof.
  move=> HE.
  have HEcp : E \is cpmap := cptn_cpmap HE.
  pose Eq := QOperation_Build HE.
  pose du := dim 'H[HL]_U.
  pose dv := dim 'H[HL]_V.
  pose z := du * dv.
  pose K (k : 'I_z) := h2mx (krausop Eq k).
  pose M := \sum_(k : 'I_z) (K k)^*t *m K k.
  have HMle : M <= 1%:M.
  {
    have HEtnK_mx : h2mx (\sum_(k : 'I_z) ((krausop Eq k)^A \o krausop Eq k)) <= 1%:M.
    {
      rewrite -h2mx1 -lef_h2mx /trace_nincr.
      exact: krausop_tn Eq.
    }
    rewrite /M.
    have -> : \sum_(k : 'I_z) (K k)^*t *m K k =
              h2mx (\sum_(k : 'I_z) ((krausop Eq k)^A \o krausop Eq k)).
    {
      symmetry.
      rewrite raddf_sum.
      apply: eq_bigr => k _.
      by rewrite /K /= h2mx_comp h2mx_adj.
    }
    exact: HEtnK_mx.
  }
  have HMpsd : (1%:M - M) \is psdmx by move: HMle; rewrite le_lownerE.
  pose Rm := sqrtmx (1%:M - M).
  have HRm_herm : Rm^*t = Rm.
    by apply/esym/hermmxP; exact: sqrtmx_herm (psdmx_herm HMpsd).
  have HRm_sq : Rm^*t *m Rm = 1%:M - M.
    by rewrite HRm_herm (sqrtmxK HMpsd).
  pose Khat_mx (i : 'I_(z + (du + 1))) : 'M[C]_(dv + 1, du + 1) :=
    match split i with
    | inl k => block_mx (K k) (0 : 'M[C]_(dv, 1))
                        (0 : 'M[C]_(1, du)) (0 : 'M[C]_1)
    | inr j =>
        match split j with
        | inl u => block_mx (0 : 'M[C]_(dv, du)) (0 : 'M[C]_(dv, 1))
                            (delta_mx ord0 u *m Rm) (0 : 'M[C]_1)
        | inr _ => block_mx (0 : 'M[C]_(dv, du)) (0 : 'M[C]_(dv, 1))
                            (0 : 'M[C]_(1, du)) (1%:M : 'M[C]_1)
        end
    end.
  pose Wc : 'M[C]_((dv + 1) * (z + (du + 1)), du + 1) :=
    \matrix_(r, c)
      let rc := mxtens_unindex r : 'I_(dv + 1) * 'I_(z + (du + 1)) in
      (Khat_mx rc.2) rc.1 c.
  have HWc_adj :
      Wc^*t *m Wc = \sum_(i : 'I_(z + (du + 1))) (Khat_mx i)^*t *m Khat_mx i.
  {
    apply/matrixP => a b.
    rewrite mxE.
    transitivity
      (\sum_(i : 'I_(dv + 1)) \sum_(k : 'I_(z + (du + 1)))
        (Wc^*t) a (mxtens_index (i, k)) * Wc (mxtens_index (i, k)) b).
    {
      rewrite (reindex (@mxtens_index (dv + 1) (z + (du + 1)))) /=.
      2:{
        exists (@mxtens_unindex (dv + 1) (z + (du + 1))) => l /=;
          by rewrite ?mxtens_indexK ?mxtens_unindexK -?surjective_pairing.
      }
      by rewrite pair_bigV /=.
    }
    transitivity
      (\sum_(i : 'I_(dv + 1)) \sum_(k : 'I_(z + (du + 1)))
        ((Khat_mx k)^*t) a i * (Khat_mx k) i b).
    {
      apply: eq_bigr => i _.
      apply: eq_bigr => k _.
      by rewrite !adjmxE /Wc !mxE !mxtens_indexK.
    }
    rewrite exchange_big summxE.
    apply: eq_bigr => k _.
    rewrite mxE.
    by apply: eq_bigr => i _; rewrite !mxE.
  }
  have ptrace2E' : forall s t (B : 'M[C]_(s * t)) r1 r2,
      (ptrace2 B) r1 r2 =
      \sum_(l : 'I_t) B (mxtens_index (r1, l)) (mxtens_index (r2, l)).
  {
    move=> s t B r1 r2.
    rewrite ptrace2E1 ptrace1E.
    by apply: eq_bigr => l _; rewrite mxE !mxtens_indexK.
  }
  have Hptrc : forall A : 'M[C]_(du + 1),
      ptrace2 (Wc *m A *m Wc^*t) =
      \sum_(i : 'I_(z + (du + 1))) Khat_mx i *m A *m (Khat_mx i)^*t.
  {
    move=> A.
    apply/matrixP => i j.
    rewrite ptrace2E' summxE.
    apply: eq_bigr => k _.
    rewrite !mxE.
    apply: eq_bigr => a _.
    have Hadj :
        (Wc^*t) a (mxtens_index (j, k)) = ((Khat_mx k)^*t) a j.
    {
      by rewrite !adjmxE /Wc !mxE !mxtens_indexK.
    }
    have HWA :
        (Wc *m A) (mxtens_index (i, k)) a = (Khat_mx k *m A) i a.
    {
      rewrite !mxE.
      by apply: eq_bigr => b _; rewrite /Wc !mxE !mxtens_indexK.
    }
    by rewrite Hadj HWA.
  }
  have HWc_iso : Wc^*t *m Wc = 1%:M.
  {
    have Hlast :
        Khat_mx (rshift z (rshift (du) ord0)) =
        block_mx (0 : 'M[C]_(dv, du)) (0 : 'M[C]_(dv, 1))
                 (0 : 'M[C]_(1, du)) (1%:M : 'M[C]_1).
    {
      by rewrite /Khat_mx splitEr splitEr.
    }
    have Hblock_ul : forall (F : 'I_(du) -> 'M[C]_(du)),
        \sum_(i : 'I_(du))
          block_mx (F i) (0 : 'M[C]_(du, 1))
                   (0 : 'M[C]_(1, du)) (0 : 'M[C]_1) =
        block_mx (\sum_(i : 'I_(du)) F i) (0 : 'M[C]_(du, 1))
                 (0 : 'M[C]_(1, du)) (0 : 'M[C]_1).
    {
      move=> F.
      apply/matrixP => i j.
      case: (split_ordP i) => [i' ->|i' ->];
      case: (split_ordP j) => [j' ->|j' ->].
      - rewrite summxE block_mxEul // summxE.
        by apply: eq_bigr => x _; rewrite block_mxEul.
      - rewrite summxE block_mxEur // mxE.
        rewrite big1 ?addr0 // => x _.
        by rewrite block_mxEur mxE.
      - rewrite summxE block_mxEdl // mxE.
        rewrite big1 ?addr0 // => x _.
        by rewrite block_mxEdl mxE.
      - rewrite summxE block_mxEdr // mxE.
        rewrite big1 ?addr0 // => x _.
        by rewrite block_mxEdr mxE.
    }
    have Hdelta_sum :
        \sum_(u < du)
          (delta_mx u ord0 *m delta_mx ord0 u : 'M[C]_(du)) = 1%:M.
    {
      transitivity (\sum_(u < du) (delta_mx u u : 'M[C]_(du))).
      - apply: congr_big => // u _.
        by rewrite mul_delta_mx.
      - by rewrite mx1_sum_delta.
    }
    have Hsum_row_gram :
        \sum_(u : 'I_(du))
          ((delta_mx ord0 u : 'M[C]_(1, du)) *m Rm)^*t *m
          ((delta_mx ord0 u : 'M[C]_(1, du)) *m Rm) =
        Rm^*t *m Rm.
    {
      apply/matrixP => p q.
      rewrite summxE !mxE.
      apply: eq_bigr => u _.
      rewrite !mxE big_ord1.
      have Hu_p :
          ((delta_mx ord0 u : 'M[C]_(1, du)) *m Rm) ord0 p = Rm u p.
      {
        by rewrite delta_mx_mulEr eqxx mul1r.
      }
      have Hu_q :
          ((delta_mx ord0 u : 'M[C]_(1, du)) *m Rm) ord0 q = Rm u q.
      {
        by rewrite delta_mx_mulEr eqxx mul1r.
      }
      have Hu_p_adj :
          (((delta_mx ord0 u : 'M[C]_(1, du)) *m Rm)^*t) p ord0 =
          (Rm u p)^*.
      {
        have -> :
            (((delta_mx ord0 u : 'M[C]_(1, du)) *m Rm)^*t) p ord0 =
            (((delta_mx ord0 u : 'M[C]_(1, du)) *m Rm) ord0 p)^*.
        {
          by rewrite adjmxE !mxE.
        }
        by rewrite Hu_p.
      }
      by rewrite Hu_p_adj Hu_q adjmxE !mxE.
    }
    have Hmain :
        \sum_(k : 'I_z)
          (block_mx (K k) (0 : 'M[C]_(dv, 1))
                    (0 : 'M[C]_(1, du)) (0 : 'M[C]_1))^*t *m
          block_mx (K k) (0 : 'M[C]_(dv, 1))
                    (0 : 'M[C]_(1, du)) (0 : 'M[C]_1) =
        block_mx M (0 : 'M[C]_(du, 1))
                 (0 : 'M[C]_(1, du)) (0 : 'M[C]_1).
    {
      under eq_bigr do
        rewrite adj_block_mx !linear0.
      under eq_bigr do
        rewrite mulmx_block ?mulmx0 ?mul0mx ?addr0 ?add0r.
      apply/matrixP => i j.
      case: (split_ordP i) => [i' ->|i' ->];
      case: (split_ordP j) => [j' ->|j' ->].
      - rewrite summxE block_mxEul // /M summxE.
        by apply: eq_bigr => x _; rewrite block_mxEul.
      - rewrite summxE block_mxEur // mxE.
        rewrite big1 ?addr0 // => x _.
        by rewrite block_mxEur mxE.
      - rewrite summxE block_mxEdl // mxE.
        rewrite big1 ?addr0 // => x _.
        by rewrite block_mxEdl mxE.
      - rewrite summxE block_mxEdr // mxE.
        rewrite big1 ?addr0 // => x _.
        by rewrite block_mxEdr mxE.
    }
    have Hfail :
        \sum_(u : 'I_(du))
          (block_mx (0 : 'M[C]_(dv, du)) (0 : 'M[C]_(dv, 1))
                    ((delta_mx ord0 u : 'M[C]_(1, du)) *m Rm) (0 : 'M[C]_1))^*t *m
          block_mx (0 : 'M[C]_(dv, du)) (0 : 'M[C]_(dv, 1))
                   ((delta_mx ord0 u : 'M[C]_(1, du)) *m Rm) (0 : 'M[C]_1) =
        block_mx (1%:M - M) (0 : 'M[C]_(du, 1))
                 (0 : 'M[C]_(1, du)) (0 : 'M[C]_1).
    {
      under eq_bigr do
        rewrite adj_block_mx !linear0.
      under eq_bigr do
        rewrite mulmx_block !mulmx0 !mul0mx !addr0 !add0r.
      rewrite Hblock_ul Hsum_row_gram.
      by rewrite HRm_sq.
    }
    have Hflag :
        (Khat_mx (rshift z (rshift (du) ord0)))^*t *m
        Khat_mx (rshift z (rshift (du) ord0)) =
        block_mx (0 : 'M[C]_(du)) (0 : 'M[C]_(du, 1))
                 (0 : 'M[C]_(1, du)) (1%:M : 'M[C]_1).
    {
      have Hzvu :
          (0 : 'M[C]_(dv, du))^*t = (0 : 'M[C]_(du, dv)).
      {
        by apply/matrixP => i j; rewrite !mxE conjC0.
      }
      have Hzv1 :
          (0 : 'M[C]_(dv, 1))^*t = (0 : 'M[C]_(1, dv)).
      {
        by apply/matrixP => i j; rewrite !mxE conjC0.
      }
      have Hzu1 :
          (0 : 'M[C]_(1, du))^*t = (0 : 'M[C]_(du, 1)).
      {
        by apply/matrixP => i j; rewrite !mxE conjC0.
      }
      rewrite Hlast adj_block_mx Hzvu Hzu1 Hzv1 adjmx1.
      rewrite mulmx_block !mulmx0 !mul0mx !add0r.
      by rewrite mulmx1.
    }
    have Hblock1 :
        block_mx (1%:M : 'M[C]_(du)) (0 : 'M[C]_(du, 1))
                 (0 : 'M[C]_(1, du)) (1%:M : 'M[C]_1) =
        (1%:M : 'M[C]_(du + 1)).
    {
      apply/matrixP => i j.
      case: (split_ordP i) => [i' ->|i' ->];
      case: (split_ordP j) => [j' ->|j' ->].
      - by rewrite block_mxEul !mxE eq_lshift.
      - by rewrite block_mxEur !mxE eq_lrshift.
      - by rewrite block_mxEdl !mxE eq_rlshift.
      - by rewrite block_mxEdr !mxE eq_rshift.
    }
    rewrite HWc_adj big_split_ord /=.
    rewrite [X in _ + X]big_split_ord /= big_ord1 /=.
    under [\sum_(k : 'I_z) _]eq_bigr do rewrite /Khat_mx /K splitEl.
    under [\sum_(u : 'I_(du)) _]eq_bigr do rewrite /Khat_mx splitEr splitEl.
    rewrite Hmain Hfail Hflag.
    have -> :
        block_mx (1%:M - M) (0 : 'M[C]_(du, 1))
                 (0 : 'M[C]_(1, du)) (0 : 'M[C]_1) +
        block_mx (0 : 'M[C]_(du)) (0 : 'M[C]_(du, 1))
                 (0 : 'M[C]_(1, du)) (1%:M : 'M[C]_1) =
        block_mx (1%:M - M) (0 : 'M[C]_(du, 1))
                 (0 : 'M[C]_(1, du)) (1%:M : 'M[C]_1).
    {
      by rewrite add_block_mx !add0r addr0.
    }
    have -> :
        block_mx M (0 : 'M[C]_(du, 1))
                 (0 : 'M[C]_(1, du)) (0 : 'M[C]_1) +
        block_mx (1%:M - M) (0 : 'M[C]_(du, 1))
                 (0 : 'M[C]_(1, du)) (1%:M : 'M[C]_1) =
        block_mx (M + (1%:M - M)) (0 : 'M[C]_(du, 1))
                 (0 : 'M[C]_(1, du)) (1%:M : 'M[C]_1).
    {
      by rewrite add_block_mx !add0r.
    }
    have -> : M + (1%:M - M) = 1%:M.
    {
      by rewrite addrC subrK.
    }
    exact: Hblock1.
  }
  have Hembed_act (sigma : 'F[HL]_U) :
      ptrace2 (Wc *m embed_subnorm (h2mx sigma) *m Wc^*t) =
      embed_subnorm (h2mx (E sigma)).
  {
    have HE_sigma :
        \sum_(k : 'I_z) K k *m h2mx sigma *m (K k)^*t = h2mx (E sigma).
    {
      have HEval : h2mx (E sigma) = h2mx (Eq sigma).
      {
        move: (QOperation_BuildE HE).
        move/(congr1 (fun F : 'SO[HL]_(U, V) => h2mx (F sigma))).
        by [].
      }
      rewrite HEval (krausE Eq sigma).
      symmetry.
      rewrite raddf_sum.
      apply: eq_bigr => k _.
      by rewrite /K /= !h2mx_comp h2mx_adj.
    }
    have HM_sigma_tr : \tr (M *m h2mx sigma) = \tr (h2mx (E sigma)).
    {
      rewrite /M mulmx_suml raddf_sum.
      transitivity (\sum_(k : 'I_z) \tr (K k *m h2mx sigma *m (K k)^*t)).
      - apply: eq_bigr => k _.
        by rewrite mxtrace_mulC -mulmxA.
      by rewrite -linear_sum HE_sigma.
    }
    have Hfail_diag :
        \sum_(u : 'I_(du))
          (delta_mx ord0 u *m Rm *m h2mx sigma *m Rm^*t *m delta_mx u ord0)
        = (\tr (Rm *m h2mx sigma *m Rm^*t)) *: (1%:M : 'M[C]_1).
    {
      pose A := Rm *m h2mx sigma *m Rm^*t.
      apply/matrixP => i j.
      have -> : i = ord0 by exact: ord1.
      have -> : j = ord0 by exact: ord1.
      rewrite summxE [((\tr A) *: (1%:M : 'M[C]_1)) ord0 ord0]mxE /mxtrace.
      transitivity (\sum_(u : 'I_(du)) A u u).
      - apply: eq_bigr => u _.
        rewrite delta_mx_mulEl ?eqxx ?mul1r //.
        rewrite -!mulmxA delta_mx_mulEr ?eqxx ?mul1r //.
        by rewrite /A !mulmxA.
      - have -> : (1%:M : 'M[C]_1) ord0 ord0 = 1.
        {
          by rewrite mxE.
        }
        by rewrite mulr1.
    }
    have Hzvu :
        (0 : 'M[C]_(dv, du))^*t = (0 : 'M[C]_(du, dv)).
    {
      by apply/matrixP => i j; rewrite !mxE conjC0.
    }
    have Hzv1 :
        (0 : 'M[C]_(dv, 1))^*t = (0 : 'M[C]_(1, dv)).
    {
      by apply/matrixP => i j; rewrite !mxE conjC0.
    }
    have Hzu1 :
        (0 : 'M[C]_(1, du))^*t = (0 : 'M[C]_(du, 1)).
    {
      by apply/matrixP => i j; rewrite !mxE conjC0.
    }
    have Hz11 : (0 : 'M[C]_1)^*t = (0 : 'M[C]_1).
    {
      by apply/matrixP => i j; rewrite !mxE conjC0.
    }
    have Hbig_block_ul :
        forall (F : 'I_z -> 'M[C]_(dv)),
          \sum_(k : 'I_z)
            block_mx (F k) (0 : 'M[C]_(dv, 1))
                     (0 : 'M[C]_(1, dv)) (0 : 'M[C]_1) =
          block_mx (\sum_(k : 'I_z) F k) (0 : 'M[C]_(dv, 1))
                   (0 : 'M[C]_(1, dv)) (0 : 'M[C]_1).
    {
      move=> F.
      apply/matrixP => i j.
      case: (split_ordP i) => [i' ->|i' ->];
      case: (split_ordP j) => [j' ->|j' ->].
      - rewrite summxE block_mxEul // summxE.
        by apply: eq_bigr => x _; rewrite block_mxEul.
      - rewrite summxE block_mxEur // mxE.
        rewrite big1 ?addr0 // => x _.
        by rewrite block_mxEur mxE.
      - rewrite summxE block_mxEdl // mxE.
        rewrite big1 ?addr0 // => x _.
        by rewrite block_mxEdl mxE.
      - rewrite summxE block_mxEdr // mxE.
        rewrite big1 ?addr0 // => x _.
        by rewrite block_mxEdr mxE.
    }
    have Hbig_block_lr :
        forall (F : 'I_(du) -> 'M[C]_1),
          \sum_(u : 'I_(du))
            block_mx (0 : 'M[C]_(dv)) (0 : 'M[C]_(dv, 1))
                     (0 : 'M[C]_(1, dv)) (F u) =
          block_mx (0 : 'M[C]_(dv)) (0 : 'M[C]_(dv, 1))
                   (0 : 'M[C]_(1, dv)) (\sum_(u : 'I_(du)) F u).
    {
      move=> F.
      apply/matrixP => i j.
      case: (split_ordP i) => [i' ->|i' ->];
      case: (split_ordP j) => [j' ->|j' ->].
      - rewrite summxE block_mxEul // mxE.
        rewrite big1 ?addr0 // => x _.
        by rewrite block_mxEul mxE.
      - rewrite summxE block_mxEur // mxE.
        rewrite big1 ?addr0 // => x _.
        by rewrite block_mxEur mxE.
      - rewrite summxE block_mxEdl // mxE.
        rewrite big1 ?addr0 // => x _.
        by rewrite block_mxEdl mxE.
      - rewrite summxE block_mxEdr // summxE.
        by apply: eq_bigr => x _; rewrite block_mxEdr.
    }
    have Hmain_embed :
        \sum_(k : 'I_z)
          block_mx (K k) (0 : 'M[C]_(dv, 1))
                   (0 : 'M[C]_(1, du)) (0 : 'M[C]_1) *m
          embed_subnorm (h2mx sigma) *m
          (block_mx (K k) (0 : 'M[C]_(dv, 1))
                    (0 : 'M[C]_(1, du)) (0 : 'M[C]_1))^*t =
        block_mx (\sum_(k : 'I_z) K k *m h2mx sigma *m (K k)^*t)
                 (0 : 'M[C]_(dv, 1))
                 (0 : 'M[C]_(1, dv)) (0 : 'M[C]_1).
    {
      under eq_bigr do
        rewrite /embed_subnorm adj_block_mx Hzu1 Hzv1 Hz11.
      under eq_bigr do
        rewrite mulmx_block !mulmx0 !mul0mx !addr0.
      under eq_bigr do
        rewrite mulmx_block !mulmx0 !mul0mx !addr0.
      exact: Hbig_block_ul.
    }
    have Hfail_embed :
        \sum_(u : 'I_(du))
          block_mx (0 : 'M[C]_(dv, du)) (0 : 'M[C]_(dv, 1))
                   ((delta_mx ord0 u : 'M[C]_(1, du)) *m Rm) (0 : 'M[C]_1) *m
          embed_subnorm (h2mx sigma) *m
          (block_mx (0 : 'M[C]_(dv, du)) (0 : 'M[C]_(dv, 1))
                    ((delta_mx ord0 u : 'M[C]_(1, du)) *m Rm) (0 : 'M[C]_1))^*t =
        block_mx (0 : 'M[C]_(dv)) (0 : 'M[C]_(dv, 1))
                 (0 : 'M[C]_(1, dv))
                 (\sum_(u : 'I_(du))
                    (delta_mx ord0 u *m Rm *m h2mx sigma *m Rm^*t *m delta_mx u ord0)).
    {
      have HL_adj (u : 'I_(du)) :
          ((delta_mx ord0 u : 'M[C]_(1, du)) *m Rm)^*t =
          Rm^*t *m (delta_mx u ord0 : 'M[C]_(du, 1)).
      {
        by rewrite adjmxM adjmx_delta.
      }
      under eq_bigr do
        rewrite /embed_subnorm adj_block_mx Hzvu (HL_adj _) Hzv1 Hz11.
      under eq_bigr do
        rewrite mulmx_block !mulmx0 !mul0mx !addr0.
      under eq_bigr do
        rewrite mulmx_block !mulmx0 !mul0mx !addr0.
      under eq_bigr do rewrite mulmxA.
      exact: Hbig_block_lr.
    }
    have Hflag_embed :
        block_mx (0 : 'M[C]_(dv, du)) (0 : 'M[C]_(dv, 1))
                 (0 : 'M[C]_(1, du)) (1%:M : 'M[C]_1) *m
        embed_subnorm (h2mx sigma) *m
        (block_mx (0 : 'M[C]_(dv, du)) (0 : 'M[C]_(dv, 1))
                  (0 : 'M[C]_(1, du)) (1%:M : 'M[C]_1))^*t =
        block_mx (0 : 'M[C]_(dv)) (0 : 'M[C]_(dv, 1))
                 (0 : 'M[C]_(1, dv))
                 ((1 - \tr (h2mx sigma)) *: (1%:M : 'M[C]_1)).
    {
      rewrite /embed_subnorm adj_block_mx Hzvu Hzu1 Hzv1 adjmx1.
      rewrite mulmx_block !mulmx0 !mul0mx !add0r.
      rewrite mulmx_block !mulmx0 !mul0mx !add0r !mulmx1 !mul1mx.
      by [].
    }
    rewrite Hptrc big_split_ord /=.
    rewrite [X in _ + X]big_split_ord /=.
    set Tflag := (X in _ + (_ + X)).
    under [\sum_(k : 'I_z) _]eq_bigr do rewrite /Khat_mx /K splitEl.
    under [\sum_(u : 'I_(du)) _]eq_bigr do rewrite /Khat_mx splitEr splitEl.
    have HTflag :
        Tflag =
        block_mx (0 : 'M[C]_(dv)) (0 : 'M[C]_(dv, 1))
                 (0 : 'M[C]_(1, dv))
                 ((1 - \tr (h2mx sigma)) *: (1%:M : 'M[C]_1)).
    {
      rewrite /Tflag big_ord1 /= /Khat_mx splitEr splitEr.
      exact: Hflag_embed.
    }
    rewrite Hmain_embed Hfail_embed HTflag.
    have Htrace_fail : \tr (Rm *m h2mx sigma *m Rm^*t) =
              \tr (h2mx sigma) - \tr (h2mx (E sigma)).
    {
      rewrite mxtrace_mulC mulmxA.
      rewrite [Rm^*t *m Rm]HRm_sq.
      rewrite mulmxBl linearB /= mul1mx HM_sigma_tr.
      by [].
    }
    rewrite /embed_subnorm HE_sigma Hfail_diag Htrace_fail.
    rewrite add_block_mx ?add0r ?addr0.
    rewrite add_block_mx ?add0r ?addr0.
    rewrite -scalerDl.
    congr (block_mx _ _ _ (_ *: _)).
    pose x := \tr (h2mx sigma).
    pose y := \tr (h2mx (E sigma)).
    change ((x - y) + (1 - x) = 1 - y).
    rewrite addrC.
    rewrite -addrA [(- x) + (x - y)]addrA addNr sub0r.
    by [].
  }
  exists Wc; split; [exact: HWc_iso | exact: Hembed_act].
Qed.

(* path: utils:pd_mono_core -> utils:pd_mono -> entropy:entropy_data_proc -> *)
(*   bb84:bb84_secret *)
Local Lemma pd_mono_core (E : 'SO[HL]_(U, V)) (rho tau : 'F[HL]_U) :
  E \is cptn ->
  rho \is psdlf -> tau \is psdlf ->
  @complex.Re R (\Tr rho) <= 1 -> @complex.Re R (\Tr tau) <= 1 ->
  [/\ gfidelity (h2mx rho) (h2mx tau) <=
      gfidelity (h2mx (E rho)) (h2mx (E tau)) &
      Num.sqrt (1 - (gfidelity (h2mx (E rho)) (h2mx (E tau))) ^ 2) <=
      Num.sqrt (1 - (gfidelity (h2mx rho) (h2mx tau)) ^ 2)].
Proof.
  move=> HE Prho Ptau Hrho_tr Htau_tr.
  have HEcp : E \is cpmap := cptn_cpmap HE.
  have [Wc [HWc_iso Hembed_act]] := stinespring_embed_mx HE.
    have Hrho_mx : h2mx rho \is psdmx by move: Prho; rewrite qualifE.
    have Htau_mx : h2mx tau \is psdmx by move: Ptau; rewrite qualifE.
    have Hrho_mx_den : h2mx rho \is denmx.
    { apply: denmx_psd_re_tr_le; first exact: Hrho_mx.
      exact: Hrho_tr. }
    have Htau_mx_den : h2mx tau \is denmx.
    { apply: denmx_psd_re_tr_le; first exact: Htau_mx.
      exact: Htau_tr. }
    have Hemb_rho_psd : embed_subnorm (h2mx rho) \is psdmx.
    {
      exact: embed_subnorm_psdmx Hrho_mx_den.
    }
    have Hemb_tau_psd : embed_subnorm (h2mx tau) \is psdmx.
    {
      exact: embed_subnorm_psdmx Htau_mx_den.
    }
  have Hgfid :
      gfidelity (h2mx rho) (h2mx tau) <=
      gfidelity (h2mx (E rho)) (h2mx (E tau)).
  {
    (* tb:fid item (ii): the generalized fidelity does not decrease under the   *)
    (* Stinespring channel realized by the isometry `Wc` (conjugate by `Wc`,    *)
    (* then trace out the ancilla), now via the canonical matrix twin           *)
    (* `fid_ii_cptp_bounds_mx`.  The dilation identity `Hembed_act` rewrites     *)
    (* each output `embed(E ·)` as `ptrace2 (Wc · Wc^*t)`.                       *)
    have Hanc_pos :
        (0 < dim 'H[HL]_U * dim 'H[HL]_V + (dim 'H[HL]_U + 1))%N.
    { rewrite addn_gt0; apply/orP; right. rewrite addn1. exact: ltn0Sn. }
    rewrite /gfidelity -(Hembed_act rho) -(Hembed_act tau).
    exact: (fid_ii_cptp_bounds_mx Hanc_pos HWc_iso Hemb_rho_psd Hemb_tau_psd).
  }
  have HErho_psd : E rho \is psdlf.
  {
    rewrite (CPMap_BuildE HEcp).
    exact: cp_psdP.
  }
  have HEtau_psd : E tau \is psdlf.
  {
    rewrite (CPMap_BuildE HEcp).
    exact: cp_psdP.
  }
  split; first exact: Hgfid.
  apply: sqrt_1msq_antimono_gen.
  - apply: gfid_ge0_mx.
    + by move: Prho; rewrite qualifE.
    + by move: Ptau; rewrite qualifE.
    - exact: (gfid_le1_mx Hrho_mx_den Htau_mx_den).
  - apply: gfid_ge0_mx.
    + by move: HErho_psd; rewrite qualifE.
    + by move: HEtau_psd; rewrite qualifE.
  - exact: Hgfid.
Qed.

End PurDistCPTN.

Section PurDistCPTNSet.
Variables (L : finType) (HL : L -> chsType).
Variables (U V : {set L}).

(* pd_mono *)
(* tex: th:pd-mono — Tomamichel, "A Framework for Non-Asymptotic Quantum Information Theory" (PhD thesis, arXiv:1203.2142), Theorem 3.4 *)
(* consumer: pd_mono is used downstream by the BB84 secrecy proof. *)
(* path: utils:pd_mono -> entropy:entropy_data_proc -> *)
(*   bb84:bb84_secret *)
Lemma pd_mono (E : 'SO[HL]_(U, V)) (rho tau : 'F[HL]_U) :
  E \is cptn ->
  rho \is psdlf -> tau \is psdlf ->
  @complex.Re R (\Tr rho) <= 1 -> @complex.Re R (\Tr tau) <= 1 ->
  [/\ gfid rho tau <= gfid (E rho) (E tau) &
      pur_dist (E rho) (E tau) <= pur_dist rho tau].
Proof.
  move=> HE Prho Ptau Hrho_tr Htau_tr.
  have [Hg Hp] := pd_mono_core HE Prho Ptau Hrho_tr Htau_tr.
  split; by rewrite /gfid /pur_dist.
Qed.

End PurDistCPTNSet.

Section PurDistCPTNCorollariesSet.
Variables (L : finType) (HL : L -> chsType).
Variables (U V : {set L}).

(* pd_mono_cptn *)
(* infra: no tex label — set-labelled corollary of `pd_mono`. *)
(* consumer: pd_mono_cptn is used downstream by the BB84 secrecy proof. *)
(* path: utils:pd_mono_cptn -> utils:pd_mono_cptp -> lhl:cq_smoothing -> *)
(*   bb84:privacy_amplification -> bb84:bb84_secret *)
Lemma pd_mono_cptn (E : 'SO[HL]_(U, V)) (rho tau : 'F[HL]_U) :
  E \is cptn ->
  rho \is psdlf -> tau \is psdlf ->
  @complex.Re R (\Tr rho) <= 1 -> @complex.Re R (\Tr tau) <= 1 ->
  pur_dist (E rho) (E tau) <= pur_dist rho tau.
Proof.
  move=> HE Prho Ptau Hrho_tr Htau_tr.
  by have [_ ?] := pd_mono HE Prho Ptau Hrho_tr Htau_tr.
Qed.

(* CPTP specialization: cptp ⊂ cptn via cptp_cptn. *)
(* pd_mono_cptp *)
(* infra: no tex label — set-labelled corollary of `pd_mono_cptn`. *)
(* consumer: pd_mono_cptp is used downstream by the BB84 secrecy proof. *)
(* path: utils:pd_mono_cptp -> lhl:cq_smoothing -> *)
(*   bb84:privacy_amplification -> bb84:bb84_secret *)
Lemma pd_mono_cptp (E : 'SO[HL]_(U, V)) (rho tau : 'F[HL]_U) :
  E \is cptp ->
  rho \is psdlf -> tau \is psdlf ->
  @complex.Re R (\Tr rho) <= 1 -> @complex.Re R (\Tr tau) <= 1 ->
  pur_dist (E rho) (E tau) <= pur_dist rho tau.
Proof.
  by move=> /cptp_cptn HE Prho Ptau Hrho_tr Htau_tr;
    exact: pd_mono_cptn.
Qed.

End PurDistCPTNCorollariesSet.

(* ================================================================== *)
(* Matrix-level purified-distance contraction under a CPTN Kraus      *)
(* Deferred here because proofs use `pd_mono` (defined above).         *)
(* ================================================================== *)

Section PurDistMxKraus.

(* path: utils:pur_dist_mx_cptn_kraus_contract -> eur:ucr_pure_smooth -> *)
(*   eur:entropic_uncertainty_relation -> *)
(*   eur:entropic_uncertainty_relation -> *)
(*   bb84:entropic_uncertainty_relation_bb84 -> bb84:bb84_secret *)
Lemma pur_dist_mx_cptn_kraus_contract
    {J : finType} {nin nout : nat}
    (E : J -> 'M[C]_(nout, nin))
    (rho1 rho2 : 'M[C]_nin) :
  (0 < nin)%N -> (0 < nout)%N ->
  rho1 \is denmx -> rho2 \is denmx ->
  \sum_(j : J) (E j)^*t *m (E j) = 1%:M ->
  Num.sqrt (1 - (gfidelity
    (\sum_(j : J) (E j) *m rho1 *m (E j)^*t)
    (\sum_(j : J) (E j) *m rho2 *m (E j)^*t)) ^+ 2)
  <= Num.sqrt (1 - (gfidelity rho1 rho2) ^+ 2).
Proof.
  move=> Hnin Hnout Hrho1_den Hrho2_den HTP.
  have /denmxP [Hp1 Htr1C] := Hrho1_den.
  have /denmxP [Hp2 Htr2C] := Hrho2_den.
  have Htr1 : @complex.Re R (\tr rho1) <= 1
    by move: Htr1C; rewrite lecE /= => /andP [_].
  have Htr2 : @complex.Re R (\tr rho2) <= 1
    by move: Htr2C; rewrite lecE /= => /andP [_].
  clear Hrho1_den Hrho2_den Htr1C Htr2C.
  pose Tin : ihbFinType := [the ihbFinType of 'I_(nin.-1).+1].
  pose Tout : ihbFinType := [the ihbFinType of 'I_(nout.-1).+1].
  have Hdin : dim (@ihb_chsType R Tin) = nin.
  { by rewrite -(@ihb_dim_cast R Tin) /Tin card_ord prednK. }
  have Hdout : dim (@ihb_chsType R Tout) = nout.
  { by rewrite -(@ihb_dim_cast R Tout) /Tout card_ord prednK. }
  case: _ / Hdin in rho1 rho2 E Hp1 Htr1 Hp2 Htr2 HTP *.
  case: _ / Hdout in E HTP *.
  pose L0 := bool.
  pose HL0 (b : L0) : chsType :=
    if b then @ihb_chsType R Tout else @ihb_chsType R Tin.
  pose U0 : {set L0} := [set false].
  pose V0 : {set L0} := [set true].
  have HdimU0 : dim 'H[HL0]_U0 = dim (@ihb_chsType R Tin).
  { by rewrite /U0 dim_setten big_set1 /HL0. }
  have HdimV0 : dim 'H[HL0]_V0 = dim (@ihb_chsType R Tout).
  { by rewrite /V0 dim_setten big_set1 /HL0. }
  pose rho1L : 'F[HL0]_U0 :=
    mx2h (castmx (esym HdimU0, esym HdimU0) rho1).
  pose rho2L : 'F[HL0]_U0 :=
    mx2h (castmx (esym HdimU0, esym HdimU0) rho2).
  pose K (j : J) : 'F[HL0]_(U0, V0) :=
    mx2h (castmx (esym HdimV0, esym HdimU0) (E j)).
  pose Ec : 'SO[HL0]_(U0, V0) := krausso K.
  have Hrho1L_mx :
      h2mx rho1L = castmx (esym HdimU0, esym HdimU0) rho1
    by rewrite /rho1L mx2hK.
  have Hrho2L_mx :
      h2mx rho2L = castmx (esym HdimU0, esym HdimU0) rho2
    by rewrite /rho2L mx2hK.
  have Hrho1L_psd : rho1L \is psdlf.
  { rewrite qualifE Hrho1L_mx -/(castmx_sq (esym HdimU0) rho1).
    exact: castmx_sq_psdmx Hp1. }
  have Hrho2L_psd : rho2L \is psdlf.
  { rewrite qualifE Hrho2L_mx -/(castmx_sq (esym HdimU0) rho2).
    exact: castmx_sq_psdmx Hp2. }
  have Hrho1L_tr : @complex.Re R (\Tr rho1L) <= 1.
  { by rewrite /lftrace Hrho1L_mx mxtrace_castmx_sq. }
  have Hrho2L_tr : @complex.Re R (\Tr rho2L) <= 1.
  { by rewrite /lftrace Hrho2L_mx mxtrace_castmx_sq. }
  have HEc_cptp : Ec \is cptp.
  {
    apply/cptpP; split; first exact: krausso_cp.
    rewrite /Ec krausso_tpE /trace_presv.
    apply/eqP; apply/h2mx_inj.
    rewrite raddf_sum /=.
    transitivity
      (castmx (esym HdimU0, esym HdimU0)
        (\sum_(j : J) (E j)^*t *m E j)).
    { rewrite raddf_sum.
      apply: eq_bigr => j _.
      rewrite /K h2mx_comp h2mx_adj !mx2hK.
      rewrite -[X in X *m _]
        (adjmx_castV (esym HdimU0, esym HdimV0)).
      by rewrite (castmx_mul (esym HdimV0)
        (esym HdimU0) (esym HdimU0)). }
    rewrite HTP h2mx1.
    apply/eqP.
    by rewrite castmx_eq1 eqxx.
  }
  have Hout_mx : forall rho : 'M[C]_(dim (@ihb_chsType R Tin)),
      h2mx (Ec (mx2h (castmx (esym HdimU0, esym HdimU0) rho))) =
      castmx (esym HdimV0, esym HdimV0)
        (\sum_(j : J) (E j) *m rho *m (E j)^*t).
  {
    move=> rho.
    rewrite /Ec kraussoE raddf_sum /=.
    transitivity
      (\sum_(j : J)
        h2mx (K j \o mx2h (castmx (esym HdimU0, esym HdimU0) rho)
          \o (K j)^A)).
    { by []. }
    rewrite raddf_sum.
    apply: eq_bigr => j _.
    rewrite /K !h2mx_comp h2mx_adj !mx2hK.
    rewrite -[X in _ *m _ *m X]
      (adjmx_castV (esym HdimU0, esym HdimV0)).
    rewrite (castmx_mul (esym HdimU0) (esym HdimV0) (esym HdimU0)).
    by rewrite (castmx_mul (esym HdimU0) (esym HdimV0) (esym HdimV0)).
  }
  have Hpd := (pd_mono_core (cptp_cptn HEc_cptp)
    Hrho1L_psd Hrho2L_psd Hrho1L_tr Hrho2L_tr).2.
  move: Hpd.
  by rewrite /pur_dist /gfid /rho1L /rho2L !Hout_mx !mx2hK
    !gfid_cast_mx.
Qed.

(* path: utils:pur_dist_mx_cptn_kraus_contract_le -> eur:ucr_pure_smooth -> *)
(*   eur:entropic_uncertainty_relation -> *)
(*   eur:entropic_uncertainty_relation -> *)
(*   bb84:entropic_uncertainty_relation_bb84 -> bb84:bb84_secret *)
Lemma pur_dist_mx_cptn_kraus_contract_le
    {J : finType} {nin nout : nat}
    (E : J -> 'M[C]_(nout, nin))
    (rho1 rho2 : 'M[C]_nin) :
  (0 < nin)%N -> (0 < nout)%N ->
  rho1 \is denmx -> rho2 \is denmx ->
  \sum_(j : J) (E j)^*t *m (E j) <= 1%:M ->
  Num.sqrt (1 - (gfidelity
    (\sum_(j : J) (E j) *m rho1 *m (E j)^*t)
    (\sum_(j : J) (E j) *m rho2 *m (E j)^*t)) ^+ 2)
  <= Num.sqrt (1 - (gfidelity rho1 rho2) ^+ 2).
Proof.
  move=> Hnin Hnout Hrho1_den Hrho2_den HTN.
  have /denmxP [Hp1 Htr1C] := Hrho1_den.
  have /denmxP [Hp2 Htr2C] := Hrho2_den.
  have Htr1 : @complex.Re R (\tr rho1) <= 1
    by move: Htr1C; rewrite lecE /= => /andP [_].
  have Htr2 : @complex.Re R (\tr rho2) <= 1
    by move: Htr2C; rewrite lecE /= => /andP [_].
  clear Hrho1_den Hrho2_den Htr1C Htr2C.
  pose Tin : ihbFinType := [the ihbFinType of 'I_(nin.-1).+1].
  pose Tout : ihbFinType := [the ihbFinType of 'I_(nout.-1).+1].
  have Hdin : dim (@ihb_chsType R Tin) = nin.
  { by rewrite -(@ihb_dim_cast R Tin) /Tin card_ord prednK. }
  have Hdout : dim (@ihb_chsType R Tout) = nout.
  { by rewrite -(@ihb_dim_cast R Tout) /Tout card_ord prednK. }
  case: _ / Hdin in rho1 rho2 E Hp1 Htr1 Hp2 Htr2 HTN *.
  case: _ / Hdout in E HTN *.
  pose L0 := bool.
  pose HL0 (b : L0) : chsType :=
    if b then @ihb_chsType R Tout else @ihb_chsType R Tin.
  pose U0 : {set L0} := [set false].
  pose V0 : {set L0} := [set true].
  have HdimU0 : dim 'H[HL0]_U0 = dim (@ihb_chsType R Tin).
  { by rewrite /U0 dim_setten big_set1 /HL0. }
  have HdimV0 : dim 'H[HL0]_V0 = dim (@ihb_chsType R Tout).
  { by rewrite /V0 dim_setten big_set1 /HL0. }
  pose rho1L : 'F[HL0]_U0 :=
    mx2h (castmx (esym HdimU0, esym HdimU0) rho1).
  pose rho2L : 'F[HL0]_U0 :=
    mx2h (castmx (esym HdimU0, esym HdimU0) rho2).
  pose K (j : J) : 'F[HL0]_(U0, V0) :=
    mx2h (castmx (esym HdimV0, esym HdimU0) (E j)).
  pose Ec : 'SO[HL0]_(U0, V0) := krausso K.
  have Hrho1L_mx :
      h2mx rho1L = castmx (esym HdimU0, esym HdimU0) rho1
    by rewrite /rho1L mx2hK.
  have Hrho2L_mx :
      h2mx rho2L = castmx (esym HdimU0, esym HdimU0) rho2
    by rewrite /rho2L mx2hK.
  have Hrho1L_psd : rho1L \is psdlf.
  { rewrite qualifE Hrho1L_mx -/(castmx_sq (esym HdimU0) rho1).
    exact: castmx_sq_psdmx Hp1. }
  have Hrho2L_psd : rho2L \is psdlf.
  { rewrite qualifE Hrho2L_mx -/(castmx_sq (esym HdimU0) rho2).
    exact: castmx_sq_psdmx Hp2. }
  have Hrho1L_tr : @complex.Re R (\Tr rho1L) <= 1.
  { by rewrite /lftrace Hrho1L_mx mxtrace_castmx_sq. }
  have Hrho2L_tr : @complex.Re R (\Tr rho2L) <= 1.
  { by rewrite /lftrace Hrho2L_mx mxtrace_castmx_sq. }
  have HEc_cptn : Ec \is cptn.
  {
    apply/cptnP; split; first exact: krausso_cp.
    rewrite /Ec krausso_tnE /trace_nincr.
    rewrite lef_h2mx h2mx1 raddf_sum /=.
    have -> :
        \sum_i h2mx ((K i)^A \o K i) =
        castmx (esym HdimU0, esym HdimU0)
          (\sum_(j : J) (E j)^*t *m E j).
    {
      rewrite raddf_sum.
      apply: eq_bigr => j _.
      rewrite /K h2mx_comp h2mx_adj !mx2hK.
      rewrite -[X in X *m _]
        (adjmx_castV (esym HdimU0, esym HdimV0)).
      by rewrite (castmx_mul (esym HdimV0)
        (esym HdimU0) (esym HdimU0)).
    }
    rewrite castmx_le1.
    exact: HTN.
  }
  have Hout_mx : forall rho : 'M[C]_(dim (@ihb_chsType R Tin)),
      h2mx (Ec (mx2h (castmx (esym HdimU0, esym HdimU0) rho))) =
      castmx (esym HdimV0, esym HdimV0)
        (\sum_(j : J) (E j) *m rho *m (E j)^*t).
  {
    move=> rho.
    rewrite /Ec kraussoE raddf_sum /=.
    transitivity (\sum_(j : J)
        h2mx (K j \o mx2h (castmx (esym HdimU0, esym HdimU0) rho)
          \o (K j)^A)).
    { by []. }
    rewrite raddf_sum.
    apply: eq_bigr => j _.
    rewrite /K !h2mx_comp h2mx_adj !mx2hK.
    rewrite -[X in _ *m _ *m X]
      (adjmx_castV (esym HdimU0, esym HdimV0)).
    rewrite (castmx_mul (esym HdimU0) (esym HdimV0) (esym HdimU0)).
    by rewrite (castmx_mul (esym HdimU0) (esym HdimV0) (esym HdimV0)).
  }
  have Hpd := (pd_mono_core HEc_cptn
    Hrho1L_psd Hrho2L_psd Hrho1L_tr Hrho2L_tr).2.
  move: Hpd.
  by rewrite /pur_dist /gfid /rho1L /rho2L !Hout_mx !mx2hK
    !gfid_cast_mx.
Qed.

End PurDistMxKraus.

(* ================================================================== *)
(* Table tb:fid properties are stated and Qed in utils/dist/fid.v       *)
(* (items i, iii, iv, v, vi) and in entropy/pre.v (item ii,       *)
(* which needs the Stinespring dilation). See statements   *)
(* at those sites; this file only hosts pd-level lemmas.                *)
(* ================================================================== *)

End FvqkdReal.

Arguments pur_dist {R L HL S} rho tau.
