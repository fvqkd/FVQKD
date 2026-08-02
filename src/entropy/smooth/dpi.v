(* -------------------------------------------------------------------- *)
(* dpi.v — Data processing inequality for smooth entropies              *)
(* -------------------------------------------------------------------- *)
(* Module: entropy.smooth.dpi                       *)
(* Source: Tomamichel, 'A Framework for Non-Asymptotic Quantum          *)
(*   Information Theory' (PhD thesis, arXiv:1203.2142), Theorem 5.7      *)
(*   (Generalized Data Processing) — tex th:data-proc.                  *)
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
From entropy Require Import def prop util pre.
From entropy.conv Require Import prop.
From entropy.smooth Require Import prop.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Open Scope ring_scope.
Local Open Scope lfun_scope.

Section FvqkdReal.
Variable R : realType.
Notation C := (@hermitian.C R).
Notation chsType := (@chsType R).

(* Local reduction target for the regular max-branch `Hlift_output` below.
   This is the projected A-side comparison needed in the lifted cascade:
   after an Aout*App projection whose App marginal is bounded by I_Aout,
   tracing App from the unprojected lift should only increase the max-entropy
   comparison target. *)
(* path: entropy:hmax_mx_projected_A_app_le -> entropy:entropy_data_proc -> *)
(*   bb84:bb84_secret *)
Local Lemma hmax_mx_projected_A_app_le {nA nApp nB : nat}
    (P : 'M[C]_(nA * nApp))
    (tau tau_hat : 'M[C]_((nA * nApp) * nB))
    (tau0 : 'M[C]_(nA * nB)) :
  (0 < nA)%N ->
  (0 < nApp)%N ->
  (0 < nB)%N ->
  P^*t = P ->
  P *m P = P ->
  ptrace2 P <= (1%:M : 'M[C]_nA) ->
  tau \is psdmx ->
  @complex.Re R (\tr tau) <= 1 ->
  tau_hat =
    (P *t (1%:M : 'M[C]_nB)) *m tau *m
    (P *t (1%:M : 'M[C]_nB)) ->
  tau_hat \is psdmx ->
  @complex.Re R (\tr tau_hat) <= 1 ->
  0 < @complex.Re R (\tr tau_hat) ->
  tau0 \is psdmx ->
  @complex.Re R (\tr tau0) <= 1 ->
  0 < @complex.Re R (\tr tau0) ->
  ptrace2 (mxswap23 tau) = tau0 ->
  hmax_mx tau_hat <= hmax_mx tau0.
Proof.
  move=> HnA_pos HnApp_pos HnB_pos HPherm HPid HPptr_le
    Htau_psd Htau_tr Htau_hat_def Htau_hat_psd Htau_hat_tr
    Htau_hat_pos Htau0_psd Htau0_tr Htau0_pos Htau_marg.
  have HnAApp_pos : (0 < nA * nApp)%N
    by rewrite muln_gt0 HnA_pos HnApp_pos.
  have Htau_hat_den : tau_hat \is denmx :=
    denmx_psd_re_tr_le Htau_hat_psd Htau_hat_tr.
  have Htau0_den : tau0 \is denmx :=
    denmx_psd_re_tr_le Htau0_psd Htau0_tr.
  have Hsmall_has_sup :=
    hmax_mx_has_sup HnA_pos HnB_pos Htau0_den Htau0_pos.
  have Hbig_nonempty :
      nonempty [set v : R | exists sigma : 'M[C]_nB,
        sigma \is den1mx /\
        elog2 ((nA * nApp)%:R * (gfidelity tau_hat
                  (mmix_mx (nA * nApp) *t sigma)) ^+ 2) = v%:E].
  {
    have Hbig_has_sup :=
      hmax_mx_has_sup HnAApp_pos HnB_pos Htau_hat_den Htau_hat_pos.
    by case: Hbig_has_sup.
  }
  pose Pfull : 'M[C]_((nA * nApp) * nB) :=
    P *t (1%:M : 'M[C]_nB).
  have HPproj : Pfull \is projmx.
  {
    apply/projmxP_id; split.
    - apply/hermmxP.
      by rewrite /Pfull adjmx_tens adjmx1 HPherm.
    - by rewrite /Pfull tensmx_mul mulmx1 HPid.
  }
  rewrite /hmax_mx.
  apply: sup_le; last exact: Hsmall_has_sup; first last.
  { exact: Hbig_nonempty. }
  move=> v [sigma [Hsigma_den Hv]].
  have Hsigma_psd : sigma \is psdmx
    by move/den1mxP: Hsigma_den => [].
  have /den1mxP [_ /eqP Hsigma_tr1] := Hsigma_den.
  pose Xbig : 'M[C]_((nA * nApp) * nB) :=
    mmix_mx (nA * nApp) *t sigma.
  pose Xsmall : 'M[C]_(nA * nB) := mmix_mx nA *t sigma.
  have HXbig_psd : Xbig \is psdmx.
  { rewrite /Xbig.
    apply: psdmx_tens; first exact: mmix_mx_psd.
    exact: Hsigma_psd. }
  have HXsmall_psd : Xsmall \is psdmx.
  { rewrite /Xsmall.
    apply: psdmx_tens; first exact: mmix_mx_psd.
    exact: Hsigma_psd. }
  have HXbig_tr1 : \tr Xbig = 1.
  { by rewrite /Xbig mxtrace_tens (@tr_mmix_mx R (nA * nApp) HnAApp_pos)
      Hsigma_tr1 mulr1. }
  have HXsmall_tr1 : \tr Xsmall = 1.
  { by rewrite /Xsmall mxtrace_tens (@tr_mmix_mx R nA HnA_pos)
      Hsigma_tr1 mulr1. }
  pose Xproj : 'M[C]_((nA * nApp) * nB) :=
    Pfull *m Xbig *m Pfull.
  have HXproj_eq :
      Xproj = ((((nA * nApp)%:R : R)^-1)%:C *: P) *t sigma.
  {
    have HXbig_scale :
        Xbig =
        ((((nA * nApp)%:R : R)^-1)%:C *:
          ((1%:M : 'M[C]_(nA * nApp)) *t sigma)).
    { by rewrite /Xbig /mmix_mx tensmxZl. }
    rewrite /Xproj HXbig_scale /Pfull.
    rewrite -scalemxAr -scalemxAl !tensmx_mul.
    rewrite mulmx1 mul1mx HPid mulmx1.
    by rewrite -tensmxZl.
  }
  have HXproj_psd : Xproj \is psdmx.
  { rewrite /Xproj.
    have HPfull_herm : Pfull^*t = Pfull
      by rewrite /Pfull adjmx_tens adjmx1 HPherm.
    rewrite -[Pfull in _ *m _ *m Pfull]HPfull_herm.
    exact: psdmx_bimap_closed_gen HXbig_psd.
  }
  have Hfid_big_eq :
      gfidelity tau_hat Xbig =
      @complex.Re R (trnorm (sqrtmx tau *m sqrtmx Xproj)).
  {
    rewrite (gfid_sym_mx Htau_hat_psd HXbig_psd).
    rewrite (gfid_eq_fid_tr1_mx HXbig_psd Htau_hat_psd HXbig_tr1
      Htau_hat_tr).
    rewrite (fid_i_sym_mx HXbig_psd Htau_hat_psd).
    have [Hproj_l Hproj_r] :=
      fid_iv_proj_mx HPproj Htau_psd HXbig_psd.
    rewrite Htau_hat_def /Xproj -/Pfull.
    exact: (eq_trans Hproj_l Hproj_r).
  }
  pose Ymid : 'M[C]_(nA * nB) := ptrace2 (mxswap23 Xproj).
  have HYmid_eq :
      Ymid = (((((nA * nApp)%:R : R)^-1)%:C *: ptrace2 P) *t sigma).
  {
    rewrite /Ymid HXproj_eq ptr2_mxswap23_tens_mx.
    by rewrite linearZ.
  }
  have HYmid_psd : Ymid \is psdmx.
  { rewrite /Ymid; exact: ptrace2_psd (mxswap23_psdmx HXproj_psd). }
  have Hfid_middle :
      @complex.Re R (trnorm (sqrtmx tau *m sqrtmx Xproj)) <=
      @complex.Re R (trnorm (sqrtmx tau0 *m sqrtmx Ymid)).
  {
    have Hmono := fid_ptr_mono_mxswap23 HnApp_pos Htau_psd HXproj_psd.
    by rewrite Htau_marg -/Ymid in Hmono.
  }
  pose cApp : R := ((nApp%:R : R)^-1)%R.
  pose Yscaled : 'M[C]_(nA * nB) := cApp%:C *: Xsmall.
  have HcApp_ge0 : 0 <= cApp by rewrite /cApp invr_ge0 ler0n.
  have HcApp_pos : 0 < cApp by rewrite /cApp invr_gt0 ltr0n.
  have HY_le_scaled : Ymid <= Yscaled.
  {
    rewrite HYmid_eq /Yscaled /Xsmall /mmix_mx /cApp.
    rewrite le_lownerE.
    have Hcoef_ge0 : (0 : C) <= ((((nA * nApp)%:R : R)^-1)%:C)
      by rewrite lecE /= eqxx invr_ge0 ler0n.
    have Hdiff_psd :
        ((1%:M : 'M[C]_nA) - ptrace2 P) \is psdmx
      by move: HPptr_le; rewrite le_lownerE.
    have Hten_psd :
        (((((nA * nApp)%:R : R)^-1)%:C *:
            ((1%:M : 'M[C]_nA) - ptrace2 P)) *t sigma) \is psdmx.
    {
      apply: psdmx_tens; last exact: Hsigma_psd.
      exact: psdmxZ Hcoef_ge0 Hdiff_psd.
    }
    have -> :
        cApp%:C *: (((nA%:R : R)^-1)%:C *: 1%:M *t sigma) -
        (((((nA * nApp)%:R : R)^-1)%:C *: ptrace2 P) *t sigma) =
        (((((nA * nApp)%:R : R)^-1)%:C *:
            ((1%:M : 'M[C]_nA) - ptrace2 P)) *t sigma).
    {
      have Hcoef :
          cApp * (((nA%:R : R)^-1)%R) =
          ((((nA%:R : R) * (nApp%:R : R))^-1)%R).
      { rewrite /cApp.
        rewrite -invrM.
        - by rewrite mulrC.
        - rewrite unitfE.
          apply/eqP=> Hzero.
          move/eqP: Hzero; rewrite pnatr_eq0 => /eqP HnA0.
          by move: HnA_pos; rewrite HnA0.
        - rewrite unitfE.
          apply/eqP=> Hzero.
          move/eqP: Hzero; rewrite pnatr_eq0 => /eqP HnApp0.
          by move: HnApp_pos; rewrite HnApp0. }
      have HcoefC :
          cApp%:C * (((nA%:R : R)^-1)%:C) =
          ((((nA * nApp)%:R : R)^-1)%:C)
        by rewrite -rmorphM Hcoef -natrM.
      rewrite !tensmxZl scalerA HcoefC.
      by rewrite linearBl /= scalerBr.
    }
    exact: Hten_psd.
  }
  have HcAppC_ge0 : (0 : C) <= cApp%:C
    by rewrite lecE /= eqxx HcApp_ge0.
  have HYscaled_psd : Yscaled \is psdmx.
  { rewrite /Yscaled.
    exact: psdmxZ HcAppC_ge0 HXsmall_psd. }
  have Hfid_order :
      @complex.Re R (trnorm (sqrtmx tau0 *m sqrtmx Ymid)) <=
      @complex.Re R (trnorm (sqrtmx tau0 *m sqrtmx Yscaled)).
  { exact: fid_v_mono_r_psd_mx Htau0_psd HYmid_psd HYscaled_psd HY_le_scaled. }
  have Hfid_scaled :
      @complex.Re R (trnorm (sqrtmx tau0 *m sqrtmx Yscaled)) =
      Num.sqrt cApp *
      @complex.Re R (trnorm (sqrtmx tau0 *m sqrtmx Xsmall)).
  {
    rewrite /Yscaled (sqrtmxZ_nn HcApp_ge0 HXsmall_psd).
    rewrite -scalemxAr trnormZ.
    have Hsqrt_ge0 : (0 : C) <= (Num.sqrt cApp)%:C
      by rewrite lecE /= eqxx sqrtr_ge0.
    rewrite (ger0_norm Hsqrt_ge0).
    have HReM : forall z : C,
        @complex.Re R ((Num.sqrt cApp)%:C * z) =
        Num.sqrt cApp * @complex.Re R z.
    { move=> [a b] /=. by rewrite mul0r subr0. }
    by rewrite HReM.
  }
  have Hgf_small_eq :
      gfidelity tau0 Xsmall =
      @complex.Re R (trnorm (sqrtmx tau0 *m sqrtmx Xsmall)).
  {
    rewrite (gfid_sym_mx Htau0_psd HXsmall_psd).
    rewrite (gfid_eq_fid_tr1_mx HXsmall_psd Htau0_psd HXsmall_tr1
      Htau0_tr).
    by rewrite fid_i_sym_mx.
  }
  have Hsqrt_ge0 : 0 <= Num.sqrt cApp := sqrtr_ge0 cApp.
  have Hgf_big_ge0 : 0 <= gfidelity tau_hat Xbig :=
    gfid_ge0_mx Htau_hat_psd HXbig_psd.
  have Hgf_small_ge0 : 0 <= gfidelity tau0 Xsmall :=
    gfid_ge0_mx Htau0_psd HXsmall_psd.
  have Hgf_scaled_le :
      gfidelity tau_hat Xbig <= Num.sqrt cApp * gfidelity tau0 Xsmall.
  {
    rewrite Hfid_big_eq Hgf_small_eq.
    apply: (le_trans Hfid_middle).
    apply: (le_trans Hfid_order).
    by rewrite Hfid_scaled.
  }
  have Hsq_scaled_le :
      (gfidelity tau_hat Xbig) ^+ 2 <=
      cApp * (gfidelity tau0 Xsmall) ^+ 2.
  {
    have Hrhs_ge0 : 0 <= Num.sqrt cApp * gfidelity tau0 Xsmall
      by apply: mulr_ge0.
    have Hsq := lerXn2r 2 Hgf_big_ge0 Hrhs_ge0 Hgf_scaled_le.
    move: Hsq.
    by rewrite exprMn sqr_sqrtr ?HcApp_ge0.
  }
  have Harg_le :
      (nA * nApp)%:R * (gfidelity tau_hat Xbig) ^+ 2 <=
      nA%:R * (gfidelity tau0 Xsmall) ^+ 2.
  {
    apply: (@le_trans _ _ ((nA * nApp)%:R *
        (cApp * (gfidelity tau0 Xsmall) ^+ 2))).
    - apply: ler_wpM2l; first by rewrite ler0n.
      exact: Hsq_scaled_le.
    - have Hcancel :
          (nA * nApp)%:R *
            (cApp * (gfidelity tau0 Xsmall) ^+ 2) =
          nA%:R * (gfidelity tau0 Xsmall) ^+ 2.
      {
        rewrite /cApp natrM.
        rewrite [LHS]mulrA.
        have Hdiv :
            (nA%:R : R) * (nApp%:R : R) / (nApp%:R : R) =
            (nA%:R : R).
        {
          rewrite mulfK.
          - by [].
          apply/eqP=> Hzero.
          move/eqP: Hzero; rewrite pnatr_eq0 => /eqP HnApp0.
          by move: HnApp_pos; rewrite HnApp0.
        }
        by rewrite Hdiv.
      }
      by rewrite Hcancel.
  }
  have Hbig_arg_pos :
      0 < (nA * nApp)%:R * (gfidelity tau_hat Xbig) ^+ 2.
  { move: Hv; rewrite /Xbig.
    case: (ltP 0 ((nA * nApp)%:R *
        (gfidelity tau_hat (mmix_mx (nA * nApp) *t sigma)) ^+ 2))
      => // Hle0.
    by rewrite (elog2_le0 Hle0); discriminate. }
  have Hsmall_arg_pos :
      0 < nA%:R * (gfidelity tau0 Xsmall) ^+ 2 :=
    lt_le_trans Hbig_arg_pos Harg_le.
  have Hv_eq :
      v = log2 ((nA * nApp)%:R * (gfidelity tau_hat Xbig) ^+ 2).
  { move: Hv; rewrite /Xbig (elog2_gt0 Hbig_arg_pos). by case. }
  pose w := log2 (nA%:R * (gfidelity tau0 Xsmall) ^+ 2).
  exists w; split.
  - exists sigma; split; first exact: Hsigma_den.
    rewrite /w /Xsmall. by rewrite (elog2_gt0 Hsmall_arg_pos).
  - rewrite Hv_eq /w.
    exact: log2_le_pos Hbig_arg_pos Harg_le.
Qed.

(* ================================================================== *)
(* Tomamichel thesis (arXiv:1203.2142), Theorem 5.7 (Generalized Data   *)
(*   Processing) — tex th:data-proc.                                    *)
(* math: Let ε ≥ 0 and ρ_ABC ∈ S_≤(ℋ_ABC).                              *)
(*   E : A -> A' is sub-unital and trace non-increasing CP,              *)
(*   F : B -> B' and G : C -> C' are trace non-increasing CP.            *)
(*   τ_A'B'C' = (G ∘ F ∘ E)[ρ_ABC].                                      *)
(*   H^ε_min(A|B)_ρ ≤ H^ε_min(A'|B')_τ.                                  *)
(*   If E,F,G are trace preserving,                                      *)
(*   H^ε_max(A|B)_ρ ≤ H^ε_max(A'|B')_τ.                                  *)
(* ================================================================== *)

Section TomamichelDataProcTex.
Variable (L : finType) (H : L -> chsType).
Variables (A B C0 A' B' C0' : {set L}).

Hypothesis disAB : [disjoint A & B].
Hypothesis disAC : [disjoint A & C0].
Hypothesis disBC : [disjoint B & C0].
Hypothesis disA'B' : [disjoint A' & B'].
Hypothesis disA'C' : [disjoint A' & C0'].
Hypothesis disB'C' : [disjoint B' & C0'].
(* Upstream-ambient intermediate labels: the min-half proof factors the
   channel as A -> A' and then B,C -> B',C' inside the same label universe. *)
Hypothesis disA'B : [disjoint A' & B].
Hypothesis disA'C0 : [disjoint A' & C0].
Hypothesis disB'C0 : [disjoint B' & C0].
(* Upstream-ambient Stinespring environments for the max-half proof:
   App and Bpp implement Tomamichel's A'' and B''. *)
Variables (App Bpp : {set L}).
Notation S_ApApp := (A' :|: App).
Notation S_BpBpp := (B' :|: Bpp).
Hypothesis disA'App : [disjoint A' & App].
Hypothesis disB'Bpp : [disjoint B' & Bpp].
Hypothesis disA'Bpp : [disjoint A' & Bpp].
Hypothesis disAppB' : [disjoint App & B'].
Hypothesis disAppBpp : [disjoint App & Bpp].
Hypothesis dimApp_enough :
  (dim 'H[H]_A * dim 'H[H]_A' <= dim 'H[H]_App)%N.
Hypothesis dimBpp_enough :
  (dim 'H[H]_B * dim 'H[H]_B' <= dim 'H[H]_Bpp)%N.
(* Upstream-ambient purifier/copy rooms used only by smooth_iso_hmax in the
   max-half proof.  They are proof artifacts, not downstream subsystems. *)
Variables (Ciso Cp_src Cpp_src Cp_tgt Cpp_tgt : {set L}).
Hypothesis disA_Ciso : [disjoint A & Ciso].
Hypothesis disB_Ciso : [disjoint B & Ciso].
Hypothesis disApApp_Ciso : [disjoint S_ApApp & Ciso].
Hypothesis disBpBpp_Ciso : [disjoint S_BpBpp & Ciso].
Hypothesis dimAB_Ciso :
  (dim 'H[H]_(A :|: B) <= dim 'H[H]_Ciso)%N.
Hypothesis dimApAppBpBpp_Ciso :
  (dim 'H[H]_(S_ApApp :|: S_BpBpp) <= dim 'H[H]_Ciso)%N.
Hypothesis disA_Cp_src : [disjoint A & Cp_src].
Hypothesis disA_Cpp_src : [disjoint A & Cpp_src].
Hypothesis disB_Cp_src : [disjoint B & Cp_src].
Hypothesis disB_Cpp_src : [disjoint B & Cpp_src].
Hypothesis disCiso_Cp_src : [disjoint Ciso & Cp_src].
Hypothesis disCiso_Cpp_src : [disjoint Ciso & Cpp_src].
Hypothesis disCp_Cpp_src : [disjoint Cp_src & Cpp_src].
Hypothesis dimA_Cp_src :
  (dim 'H[H]_A = dim 'H[H]_Cp_src).
Hypothesis dimCisoCp_Cpp_src :
  (dim 'H[H]_Ciso * dim 'H[H]_Cp_src <= dim 'H[H]_Cpp_src)%N.
Hypothesis dimB_Cpp_src :
  (dim 'H[H]_B <= dim 'H[H]_Cpp_src)%N.
Hypothesis disApApp_Cp_tgt : [disjoint S_ApApp & Cp_tgt].
Hypothesis disApApp_Cpp_tgt : [disjoint S_ApApp & Cpp_tgt].
Hypothesis disBpBpp_Cp_tgt : [disjoint S_BpBpp & Cp_tgt].
Hypothesis disBpBpp_Cpp_tgt : [disjoint S_BpBpp & Cpp_tgt].
Hypothesis disCiso_Cp_tgt : [disjoint Ciso & Cp_tgt].
Hypothesis disCiso_Cpp_tgt : [disjoint Ciso & Cpp_tgt].
Hypothesis disCp_Cpp_tgt : [disjoint Cp_tgt & Cpp_tgt].
Hypothesis dimApApp_Cp_tgt :
  (dim 'H[H]_S_ApApp = dim 'H[H]_Cp_tgt).
Hypothesis dimCisoCp_Cpp_tgt :
  (dim 'H[H]_Ciso * dim 'H[H]_Cp_tgt <= dim 'H[H]_Cpp_tgt)%N.
Hypothesis dimBpBpp_Cpp_tgt :
  (dim 'H[H]_S_BpBpp <= dim 'H[H]_Cpp_tgt)%N.

Notation S_ABC := (A :|: B :|: C0).
Notation S_A'B'C' := (A' :|: B' :|: C0').

Local Definition entropy_data_proc_map
    (E : 'SO[H]_(A, A')) (F : 'SO[H]_(B, B'))
    (G : 'SO[H]_(C0, C0')) : 'SO[H]_(S_ABC, S_A'B'C') :=
  (E :⊗ F) :⊗ G.

Local Definition entropy_data_proc_tau (rhoABC : 'F[H]_S_ABC)
    (E : 'SO[H]_(A, A')) (F : 'SO[H]_(B, B'))
    (G : 'SO[H]_(C0, C0')) : 'F[H]_S_A'B'C' :=
  entropy_data_proc_map E F G rhoABC.

(* path: entropy:entropy_data_proc -> *)
(*   bb84:bb84_secret *)
Theorem entropy_data_proc (eps : R) (rhoABC : 'F[H]_S_ABC)
    (E : 'SO[H]_(A, A')) (F : 'SO[H]_(B, B'))
    (G : 'SO[H]_(C0, C0')) :
  rhoABC \is denlf ->
  0 <= eps ->
    let tauA'B'C' := entropy_data_proc_tau rhoABC E F G in
    (E \is cptn -> E^*o \is tnmap -> F \is cptn -> G \is cptn ->
      (eps < Num.sqrt (@complex.Re R
        (\Tr (ptrace_cast3C disA'C' disB'C' tauA'B'C'))))%R ->
      smooth_hminE B eps (ptrace_cast3C disAC disBC rhoABC) <=
      smooth_hminE B' eps (ptrace_cast3C disA'C' disB'C' tauA'B'C'))%E /\
    (E \is cptp -> E^*o \is tnmap -> F \is cptp -> G \is cptp ->
      (eps < Num.sqrt (@complex.Re R
        (\Tr (ptrace_cast3C disAC disBC rhoABC))))%R ->
      smooth_hmaxE B eps (ptrace_cast3C disAC disBC rhoABC) <=
      smooth_hmaxE B' eps (ptrace_cast3C disA'C' disB'C' tauA'B'C'))%E.
Proof.
  move=> Hrho_den Heps.
  set rhoAB := ptrace_cast3C disAC disBC rhoABC.
  set tauABC := entropy_data_proc_tau rhoABC E F G.
  set tauA'B' := ptrace_cast3C disA'C' disB'C' tauABC.
  split.
    - move=> HE_cptn HE_dualtn HF_cptn HG_cptn Heps_tgt_lt.
    have Hmin_transport :
        forall tauAB : 'F[H]_(A :|: B),
          eps_ball eps rhoAB tauAB ->
          exists tauA'B'0 : 'F[H]_(A' :|: B'),
            eps_ball eps tauA'B' tauA'B'0 /\
            (hminE B tauAB <= hminE B' tauA'B'0)%E.
    {
      move=> tauAB HtauAB_ball.
      have PtauAB : tauAB \is psdlf := eps_ball_psdlf HtauAB_ball.
      have HtauAB_tr : @complex.Re R (\Tr tauAB) <= 1 :=
        eps_ball_trlf HtauAB_ball.
      have PrhoABC : rhoABC \is psdlf := denlf_psd Hrho_den.
      have PrhoAB : rhoAB \is psdlf.
      { rewrite /rhoAB /ptrace_cast3C.
        exact: ptrace_cast_gen_psdlf PrhoABC. }
      have HrhoABC_tr : @complex.Re R (\Tr rhoABC) <= 1.
      { have Hreal : \Tr rhoABC \is Num.real :=
          ger0_real (psdlf_trlf PrhoABC).
        by move: (denlf_trlf Hrho_den); rewrite -(RRe_real Hreal) lecR. }
      have disAB_C0 : [disjoint A :|: B & C0]
        by rewrite disjointUX disAC disBC.
      have HrhoABC_marg : ptrace_cast disAB_C0 rhoABC = rhoAB.
      { rewrite /rhoAB /ptrace_cast3C /ptrace_cast /ptrace_cast_gen.
        congr (castlf (_, _) _); exact: eq_irrelevance. }
      have [tauABC0 [PtauABC0 [HtauABC0_tr [HtauABC0_marg Hpd_ext]]]] :=
        @pd_ext_subnorm R L H (A :|: B) C0 disAB_C0
          rhoAB tauAB rhoABC PrhoABC HrhoABC_tr HrhoABC_marg
          PtauAB HtauAB_tr.
      pose tauABC0' : 'F[H]_S_A'B'C' :=
        entropy_data_proc_tau tauABC0 E F G.
      pose tauA'B'0 : 'F[H]_(A' :|: B') :=
        ptrace_cast3C disA'C' disB'C' tauABC0'.
      exists tauA'B'0; split.
      - have Pmap : entropy_data_proc_map E F G \is cptn.
        {
          rewrite /entropy_data_proc_map.
          have HEF_cptn : (E :⊗ F) \is cptn.
          { exact: (@tenso_qo R L H A A' B B'
              disAB disA'B' (QOperation_Build HE_cptn)
              (QOperation_Build HF_cptn)). }
          have disAB_C : [disjoint A :|: B & C0]
            by rewrite disjointUX disAC disBC.
          have disA'B'_C' : [disjoint A' :|: B' & C0']
            by rewrite disjointUX disA'C' disB'C'.
          exact: (@tenso_qo R L H (A :|: B) (A' :|: B') C0 C0'
            disAB_C disA'B'_C' (QOperation_Build HEF_cptn)
            (QOperation_Build HG_cptn)).
        }
        have PtauABC0' : tauABC0' \is psdlf.
        { rewrite /tauABC0' /entropy_data_proc_tau.
          rewrite (CPMap_BuildE (cptn_cpmap Pmap)).
          exact: cp_psdP PtauABC0. }
          have PtauABC_img : tauABC \is psdlf.
          { rewrite /tauABC /entropy_data_proc_tau.
            rewrite (CPMap_BuildE (cptn_cpmap Pmap)).
            exact: cp_psdP PrhoABC. }
          have PtauA'B' : tauA'B' \is psdlf.
          { rewrite /tauA'B' /ptrace_cast3C.
            exact: ptrace_cast_gen_psdlf PtauABC_img. }
          have HtauA'B'_tr : @complex.Re R (\Tr tauA'B') <= 1.
          {
            have HtauABC_tr : @complex.Re R (\Tr tauABC) <= 1.
            {
              have HleC : \Tr tauABC <= \Tr rhoABC.
              { rewrite /tauABC /entropy_data_proc_tau
                  (QOperation_BuildE Pmap).
                exact: qo_trlfE PrhoABC. }
              have HrhoABC_real : (\Tr rhoABC : C) =
                  (@complex.Re R (\Tr rhoABC))%:C
                by rewrite RRe_real // ger0_real // psdlf_trlf.
              have HtauABC_real : (\Tr tauABC : C) =
                  (@complex.Re R (\Tr tauABC))%:C
                by rewrite RRe_real // ger0_real // psdlf_trlf.
              have Hre_le : @complex.Re R (\Tr tauABC) <=
                  @complex.Re R (\Tr rhoABC)
                by move: HleC; rewrite HrhoABC_real HtauABC_real lecR.
              exact: le_trans Hre_le HrhoABC_tr.
            }
            rewrite /tauA'B' /ptrace_cast3C /ptrace_cast_gen castlf_trlfE.
            have /cptpP [_ /tpmapP Htp] := @ptraceso_qc R L H C0' S_A'B'C'.
            by rewrite Htp.
          }
          have PtauA'B'0 : tauA'B'0 \is psdlf.
          { rewrite /tauA'B'0 /ptrace_cast3C.
            exact: ptrace_cast_gen_psdlf PtauABC0'. }
        have HtauABC0'_tr : @complex.Re R (\Tr tauABC0') <= 1.
        {
          have HleC : \Tr tauABC0' <= \Tr tauABC0.
          { rewrite /tauABC0' /entropy_data_proc_tau
              (QOperation_BuildE Pmap).
            exact: qo_trlfE PtauABC0. }
          have HtauABC0_real : (\Tr tauABC0 : C) =
              (@complex.Re R (\Tr tauABC0))%:C
            by rewrite RRe_real // ger0_real // psdlf_trlf.
          have HtauABC0'_real : (\Tr tauABC0' : C) =
              (@complex.Re R (\Tr tauABC0'))%:C
            by rewrite RRe_real // ger0_real // psdlf_trlf.
          have Hre_le : @complex.Re R (\Tr tauABC0') <=
              @complex.Re R (\Tr tauABC0)
            by move: HleC; rewrite HtauABC0_real HtauABC0'_real lecR.
          exact: le_trans Hre_le HtauABC0_tr.
        }
        have HtauA'B'0_tr : @complex.Re R (\Tr tauA'B'0) <= 1.
        {
          rewrite /tauA'B'0 /ptrace_cast3C /ptrace_cast_gen castlf_trlfE.
          have /cptpP [_ /tpmapP Htp] := @ptraceso_qc R L H C0' S_A'B'C'.
          by rewrite Htp.
        }
        have HtauA'B'0_pd : pur_dist tauA'B'0 tauA'B' <= eps.
        {
          move: HtauAB_ball => /andP [/andP [_ _] HpdAB].
          have Hpd_ext_sym : pur_dist tauABC0 rhoABC =
              pur_dist rhoABC tauABC0.
          {
            have Ptau_mx : h2mx tauABC0 \is psdmx
              by move: PtauABC0; rewrite qualifE.
            have Prho_mx : h2mx rhoABC \is psdmx
              by move: PrhoABC; rewrite qualifE.
            rewrite /pur_dist /gfid.
            exact: (f_equal (fun x => Num.sqrt (1 - x^2))
              (gfid_sym_mx Ptau_mx Prho_mx)).
          }
          have HpdAB_sym : pur_dist rhoAB tauAB =
              pur_dist tauAB rhoAB.
          {
            have Prho_mx : h2mx rhoAB \is psdmx
              by move: PrhoAB; rewrite qualifE.
            have Ptau_mx : h2mx tauAB \is psdmx
              by move: PtauAB; rewrite qualifE.
            rewrite /pur_dist /gfid.
            exact: (f_equal (fun x => Num.sqrt (1 - x^2))
              (gfid_sym_mx Prho_mx Ptau_mx)).
          }
          have Hpd_tauABC0_r : pur_dist rhoABC tauABC0 <= eps.
          { rewrite Hpd_ext HpdAB_sym. exact: HpdAB. }
          have Hpd_tauABC0 : pur_dist tauABC0 rhoABC <= eps.
          { rewrite Hpd_ext_sym. exact: Hpd_tauABC0_r. }
          have Hpd_map :
              pur_dist tauABC0' tauABC <= eps.
          {
            have [_ Hmono] :=
              pd_mono Pmap PtauABC0 PrhoABC HtauABC0_tr HrhoABC_tr.
            exact: le_trans Hmono Hpd_tauABC0.
          }
          have disA'B'_C' : [disjoint A' :|: B' & C0']
            by rewrite disjointUX disA'C' disB'C'.
          have Hpt_tau :
              ptrace_cast disA'B'_C' tauABC0' = tauA'B'0.
          { rewrite /tauA'B'0 /ptrace_cast3C /ptrace_cast /ptrace_cast_gen.
            congr (castlf (_, _) _); exact: eq_irrelevance. }
          have Hpt_rho :
              ptrace_cast disA'B'_C' tauABC = tauA'B'.
          { rewrite /tauA'B' /ptrace_cast3C /ptrace_cast /ptrace_cast_gen.
            congr (castlf (_, _) _); exact: eq_irrelevance. }
          have Hpd_ptr :=
            @pd_mono_ptrace_cast R L H (A' :|: B') C0' disA'B'_C'
              tauABC tauABC0' PtauABC0' PtauABC_img.
            rewrite Hpt_tau Hpt_rho in Hpd_ptr.
            exact: le_trans Hpd_ptr Hpd_map.
          }
          have HtauA'B'0_pos : 0 < @complex.Re R (\Tr tauA'B'0).
          {
            have Htarget_range :
                0 <= eps < Num.sqrt (@complex.Re R (\Tr tauA'B'))
              by rewrite Heps Heps_tgt_lt.
            have Holdball :
                ((tauA'B'0 \is psdlf) &&
                 (@complex.Re R (\Tr tauA'B'0) <= 1)) &&
                (pur_dist tauA'B'0 tauA'B' <= eps).
            { by rewrite PtauA'B'0 HtauA'B'0_tr HtauA'B'0_pd. }
            exact: (eps_ball_trace_pos_from_small PtauA'B'
              HtauA'B'_tr Htarget_range Holdball).
          }
          by rewrite /eps_ball PtauA'B'0 HtauA'B'0_pos
            HtauA'B'0_tr HtauA'B'0_pd.
      - (* Tomamichel, Theorem 5.7 proof (min half).  The remaining unsmoothed
           step is the Φ chain: extend tauAB to tauABC, process by
           E⊗F⊗G, use Properties vi/vii plus the marginal order from
           tracing the TNI C-channel, then apply monotonicity of elog2. *)
        pose tauA'B0 : 'F[H]_(A' :|: B) :=
          ((E :⊗ (\:1 : 'SO[H]_B)) tauAB).
        pose tauA'B'1 : 'F[H]_(A' :|: B') :=
          (((\:1 : 'SO[H]_A') :⊗ F) tauA'B0).
        have HE_cp : E \is cpmap := cptn_cpmap HE_cptn.
        have HF_cp : F \is cpmap := cptn_cpmap HF_cptn.
        have HEid_cp : (E :⊗ (\:1 : 'SO[H]_B)) \is cpmap.
        { exact: (@tenso_cp R L H A A' B B disAB
            (CPMap_Build HE_cp) (\:1 : 'CP[H]_B)). }
        have HidF_cp : ((\:1 : 'SO[H]_A') :⊗ F) \is cpmap.
        { exact: (@tenso_cp R L H A' A' B B' disA'B
            (\:1 : 'CP[H]_A') (CPMap_Build HF_cp)). }
        have PtauA'B0 : tauA'B0 \is psdlf.
        { rewrite /tauA'B0 (CPMap_BuildE HEid_cp).
          exact: cp_psdP PtauAB. }
        have PtauA'B'1 : tauA'B'1 \is psdlf.
        { rewrite /tauA'B'1 (CPMap_BuildE HidF_cp).
          exact: cp_psdP PtauA'B0. }
        have Pmap : entropy_data_proc_map E F G \is cptn.
        {
          rewrite /entropy_data_proc_map.
          have HEF_cptn : (E :⊗ F) \is cptn.
          { exact: (@tenso_qo R L H A A' B B'
              disAB disA'B' (QOperation_Build HE_cptn)
              (QOperation_Build HF_cptn)). }
          have disAB_C : [disjoint A :|: B & C0]
            by rewrite disjointUX disAC disBC.
          have disA'B'_C' : [disjoint A' :|: B' & C0']
            by rewrite disjointUX disA'C' disB'C'.
          exact: (@tenso_qo R L H (A :|: B) (A' :|: B') C0 C0'
            disAB_C disA'B'_C' (QOperation_Build HEF_cptn)
            (QOperation_Build HG_cptn)).
        }
        have PtauABC0' : tauABC0' \is psdlf.
        { rewrite /tauABC0' /entropy_data_proc_tau.
          rewrite (CPMap_BuildE (cptn_cpmap Pmap)).
          exact: cp_psdP PtauABC0. }
        have PtauA'B'0 : tauA'B'0 \is psdlf.
        { rewrite /tauA'B'0 /ptrace_cast3C.
          exact: ptrace_cast_gen_psdlf PtauABC0'. }
        have Hmarg_order : tauA'B'0 <= tauA'B'1.
        {
          (* Tomamichel implicit bridge: tracing out the output of the TNI
             extension channel G is order-bounded by not applying G. *)
          have disA'B'_C' : [disjoint A' :|: B' & C0']
            by rewrite disjointUX disA'C' disB'C'.
          have disAB_C : [disjoint A :|: B & C0]
            by rewrite disjointUX disAC disBC.
          have HEF_cp : (E :⊗ F) \is cpmap.
          { exact: (@tenso_cp R L H A A' B B' disAB
              (CPMap_Build HE_cp) (CPMap_Build HF_cp)). }
          have Hseq_EF : tauA'B'1 = (E :⊗ F) tauAB.
          {
            rewrite /tauA'B'1 /tauA'B0.
            have Hcomp := @tenso_comp R L H A' A' B B' A B
              (\:1 : 'SO[H]_A') E F (\:1 : 'SO[H]_B) disA'B.
            move: Hcomp.
            rewrite comp_so1l comp_so1r => Hcomp.
            by rewrite -comp_soE -Hcomp.
          }
          apply/lef_psdtr=> X PX.
          pose Y : 'F[H]_(A :|: B) := ((E :⊗ F)^*o) X.
          have PY : Y \is psdlf.
          {
            have HEF_dual_cp : (E :⊗ F)^*o \is cpmap
              by rewrite dualso_cpE.
            rewrite /Y (CPMap_BuildE HEF_dual_cp).
            exact: cp_psdP PX.
          }
          have HGdual_sub :
              G^*o (\1 : 'F[H]_C0') <= (\1 : 'F[H]_C0).
          {
            have HG_cp : G \is cpmap := cptn_cpmap HG_cptn.
            have HGdual_cp : G^*o \is cpmap by rewrite dualso_cpE.
            move: (cptn_tnmap HG_cptn).
            rewrite -[G in G \is tnmap]dualsoK.
            rewrite (@cp_isdualtnE R _ _ (CPMap_Build HGdual_cp)).
            exact.
          }
          have HK :
              Y \O (G^*o (\1 : 'F[H]_C0')) <=
              Y \O (\1 : 'F[H]_C0).
          {
            rewrite (sdotF_to_tenF disAB_C0 Y (G^*o (\1 : 'F[H]_C0'))).
            rewrite (sdotF_to_tenF disAB_C0 Y (\1 : 'F[H]_C0)).
            exact: (lef_tenfr disAB_C0 (psdlf_ge0 PY) HGdual_sub).
          }
          have Htrace_le :
              \Tr (tauABC0 \o (Y \O (G^*o (\1 : 'F[H]_C0')))) <=
              \Tr (tauABC0 \o (Y \O (\1 : 'F[H]_C0))).
          {
            have /lef_psdtr Hle := HK.
            have Hle0 := Hle tauABC0 PtauABC0.
            rewrite [\Tr (tauABC0 \o (Y \O (G^*o (\1 : 'F[H]_C0'))))]lftraceC.
            rewrite [\Tr (tauABC0 \o (Y \O (\1 : 'F[H]_C0)))]lftraceC.
            exact: Hle0.
          }
          have Hpt_tau0 :
              ptrace_cast disA'B'_C' tauABC0' = tauA'B'0.
          { rewrite /tauA'B'0 /ptrace_cast3C /ptrace_cast /ptrace_cast_gen.
            congr (castlf (_, _) _); exact: eq_irrelevance. }
          rewrite -Hpt_tau0.
          rewrite -(trlf_lift_partial_r disA'B'_C' tauABC0' X).
          rewrite /tauABC0' /entropy_data_proc_tau /entropy_data_proc_map.
          rewrite dualso_trlfE.
          have Hdual_tensor :
              ((E :⊗ F) :⊗ G)^*o (X \O (\1 : 'F[H]_C0')) =
              Y \O (G^*o (\1 : 'F[H]_C0')).
          {
            rewrite tenso_dual (sdotF_to_tenF disA'B'_C' X (\1 : 'F[H]_C0')).
            rewrite -(tenso_correct ((E :⊗ F)^*o) G^*o disA'B'_C' X
              (\1 : 'F[H]_C0')).
            by rewrite /Y -(sdotF_to_tenF disAB_C0 Y (G^*o (\1 : 'F[H]_C0'))).
          }
          rewrite Hdual_tensor.
          rewrite Hseq_EF dualso_trlfE -HtauABC0_marg.
          rewrite -(trlf_lift_partial_r disAB_C0 tauABC0 Y).
          exact: Htrace_le.
        }
        have Hphi_marg :
            phi_min B' tauA'B'0 <= phi_min B' tauA'B'1.
        { exact: (@phi_min_ii_mono R L H (A' :|: B') B'
            tauA'B'0 tauA'B'1 PtauA'B'0 PtauA'B'1 Hmarg_order). }
        have Hphi_B :
            phi_min B' tauA'B'1 <= phi_min B tauA'B0.
        { exact: (@phi_min_data_proc_B R L H A' B B'
            disA'B disA'B' tauA'B0 (QOperation_Build HF_cptn)
            PtauA'B0). }
        have Hphi_A :
            phi_min B tauA'B0 <= phi_min B tauAB.
        { exact: (@phi_min_data_proc_A R L H A A' B
            disAB disA'B tauAB E PtauAB HE_cp HE_dualtn). }
        have Hphi_le : phi_min B' tauA'B'0 <= phi_min B tauAB
          := le_trans Hphi_marg (le_trans Hphi_B Hphi_A).
        case: (ltP 0 (phi_min B' tauA'B'0)) => Hphi_pos.
        + rewrite /hminE leeN2.
          exact: elog2_le _ _ Hphi_pos Hphi_le.
        + by rewrite /hminE (elog2_le0 Hphi_pos) leey.
    }
    rewrite /smooth_hminE.
    apply: ge_ereal_sup => v [tauAB [HtauAB_ball ->]].
    have [tauA'B'0 [HtauA'B'_ball Hhmin_le]] :=
      Hmin_transport tauAB HtauAB_ball.
    have Hsmooth_ge :
        (hminE B' tauA'B'0 <=
         ereal_sup [set v : extended R | exists tauS : 'F[H]_(A' :|: B'),
           eps_ball eps tauA'B' tauS /\ v = hminE B' tauS])%E.
    { apply: ereal_sup_ubound. by exists tauA'B'0. }
    exact: le_trans Hhmin_le Hsmooth_ge.
    - move=> HE_cptp HE_dualtn HF_cptp HG_cptp Heps_src_lt.
    have Hmax_bound :
        forall tauA'B'0 : 'F[H]_(A' :|: B'),
          eps_ball eps tauA'B' tauA'B'0 ->
          (smooth_hmaxE B eps rhoAB <= hmaxE B' tauA'B'0)%E.
    {
      move=> tauA'B'0 HtauA'B'_ball.
      (* Tomamichel, Theorem 5.7 proof (max half).
         The max half is not a source-witness transport.  For each output
         smooth witness, lift it to the Stinespring dilation, project onto the
         A-side image, compare hmax by fidelity monotonicity, then use
         smooth_iso_hmax to return to the source smooth entropy. *)
      have PrhoABC : rhoABC \is psdlf := denlf_psd Hrho_den.
      have PrhoAB : rhoAB \is psdlf.
      { rewrite /rhoAB /ptrace_cast3C.
        exact: ptrace_cast_gen_psdlf PrhoABC. }
      have HrhoAB_tr : @complex.Re R (\Tr rhoAB) <= 1.
      { rewrite /rhoAB /ptrace_cast3C /ptrace_cast_gen castlf_trlfE.
        have /cptpP [_ /tpmapP Htp] := @ptraceso_qc R L H C0 S_ABC.
        have Hreal : \Tr rhoABC \is Num.real :=
          ger0_real (psdlf_trlf PrhoABC).
        move: (denlf_trlf Hrho_den); rewrite -(RRe_real Hreal) lecR => Htr.
        by rewrite Htp. }
      have HrhoAB_trC : \Tr rhoAB <= 1.
      { rewrite /rhoAB /ptrace_cast3C /ptrace_cast_gen castlf_trlfE.
        have /cptpP [_ /tpmapP Htp] := @ptraceso_qc R L H C0 S_ABC.
        by rewrite Htp; exact: denlf_trlf Hrho_den. }
      have HrhoAB_den : rhoAB \is denlf.
      { apply/denlfP; split; first exact: PrhoAB.
        exact: HrhoAB_trC. }
      case: (ltP eps (Num.sqrt (@complex.Re R (\Tr rhoAB)))) => Heps_lt.
      - have Heps_pair : 0 <= eps <
            Num.sqrt (@complex.Re R (\Tr rhoAB))
          by rewrite Heps Heps_lt.
        have stinespring_to_env :
            forall (X Y Env : {set L}) (disYEnv : [disjoint Y & Env])
              (dimEnv_enough :
                (dim 'H[H]_X * dim 'H[H]_Y <= dim 'H[H]_Env)%N)
              (Q : 'SO[H]_(X, Y)),
            Q \is cptp ->
            exists V : 'FI[H]_(X, Y :|: Env),
              ((castso (erefl _, setDU_r disYEnv)
                  (QChannel_Build (@ptraceso_qc R L H Env (Y :|: Env)))
                : 'SO[H]_(Y :|: Env, Y)) :o formso V) = Q.
        {
          move=> X Y Env disYEnv dimEnv_enough Q HQ_cptp.
          have HQ_cp : Q \is cpmap := cptp_cpmap HQ_cptp.
          have [z [W [Hz Hact HWtp _]]] :=
            (proj1 (stinespring Q) HQ_cp).
          have HWiso : W^*t *m W = 1%:M :=
            HWtp (cptp_tpmap HQ_cptp).
          pose nX := dim 'H[H]_X.
          pose nY := dim 'H[H]_Y.
          pose nEnv := dim 'H[H]_Env.
          have Hle_z : (z <= nEnv)%N.
          { rewrite /nX /nY /nEnv Hz.
            exact: dimEnv_enough. }
          pose R0 : 'M[C]_(z, z + (nEnv - z)) :=
            row_mx (1%:M : 'M[C]_z) (0 : 'M[C]_(z, nEnv - z)).
          pose RR : 'M[C]_(z, nEnv) :=
            castmx (erefl z, subnKC Hle_z) R0.
          have HR_unit : RR \is unitarymx.
          { rewrite /RR castmx_funE.
            exact: (row_mx0_unitarymx _ (unitarymx1 _ _)). }
          pose Genv : 'M[C]_(nEnv, z) := RR^*t.
          have HGG : Genv^*t *m Genv = 1%:M
            by rewrite /Genv adjmxK; exact: unitarymxK HR_unit.
          pose Tenv : 'M[C]_(nY * nEnv, nY * z) :=
            ((1%:M : 'M[C]_nY) *t Genv).
          have HTadj_unit : Tenv^*t \is unitarymx.
          { rewrite /Tenv adjmx_tens adjmx1 /Genv adjmxK.
            apply: unitarymx_tens; [exact: unitarymx1 | exact: HR_unit]. }
          have HTiso : Tenv^*t *m Tenv = 1%:M.
          { by have := unitarymxK HTadj_unit; rewrite adjmxK. }
          pose Wten : 'M[C]_(nY * nEnv, nX) := Tenv *m W.
          pose UU := @tenv_mxU R L H Y Env.
          have HUadj : UU^*t \is unitarymx :=
            tenv_mxU_adj_unitarymx disYEnv.
          have Uadj_mul_U : UU^*t *m UU = 1%:M.
          { by have := unitarymxK HUadj; rewrite adjmxK. }
          pose Wlbl : 'M[C]_(dim 'H[H]_(Y :|: Env), nX) := UU *m Wten.
          pose Vraw : 'Hom('H[H]_X, 'H[H]_(Y :|: Env)) := mx2h Wlbl.
          have Vraw_iso : Vraw \is isolf.
          { apply/isolfP; apply/h2mx_inj.
            rewrite h2mx_comp h2mx_adj /Vraw mx2hK h2mx1.
            have -> : Wlbl^*t *m Wlbl =
                Wten^*t *m (UU^*t *m UU) *m Wten
              by rewrite /Wlbl adjmxM -!mulmxA.
            rewrite Uadj_mul_U mulmx1.
            have -> : Wten^*t *m Wten =
                W^*t *m (Tenv^*t *m Tenv) *m W
              by rewrite /Wten adjmxM -!mulmxA.
            have -> : W^*t *m (Tenv^*t *m Tenv) *m W =
                W^*t *m W
              by rewrite HTiso -mulmxA mul1mx.
            exact: HWiso. }
          pose V : 'FI[H]_(X, Y :|: Env) := IsoLf_Build Vraw_iso.
          exists V.
          apply/superopP=> X0; apply/h2mx_inj.
          pose rho := h2mx X0.
          have -> : X0 = mx2h rho by rewrite /rho h2mxK.
          rewrite comp_soE castsoE /=.
          rewrite (QChannel_BuildE (@ptraceso_qc R L H Env (Y :|: Env))).
          rewrite /ptrace_cast /ptrace_cast_gen.
          rewrite (h2mx_ptrace_cast_ptrace2 disYEnv (formso V (mx2h rho))).
          have Hform_mx :
              h2mx (formso V (mx2h rho)) =
              Wlbl *m rho *m Wlbl^*t
            by rewrite formsoE !h2mx_comp h2mx_adj /V /Vraw !mx2hK.
          rewrite Hform_mx.
          have HWlblE :
              Wlbl *m rho *m Wlbl^*t =
              UU *m (Wten *m rho *m Wten^*t) *m UU^*t
            by rewrite /Wlbl adjmxM !mulmxA.
          rewrite HWlblE.
          rewrite !mulmxA Uadj_mul_U mul1mx -mulmxA Uadj_mul_U mulmx1.
          have -> : Wten *m rho *m Wten^*t =
              ((Tenv *m (W *m rho *m W^*t)) *m Tenv^*t)
            by rewrite /Wten adjmxM !mulmxA.
          rewrite /Tenv.
          rewrite (@ptrace2_conj_tens_right_iso R nY z nEnv Genv
            (W *m rho *m W^*t) HGG).
          by rewrite -Hact.
        }
        have [UA HE_after_UA] :=
          stinespring_to_env A A' App disA'App dimApp_enough E HE_cptp.
        have [VB HF_after_VB] :=
          stinespring_to_env B B' Bpp disB'Bpp dimBpp_enough F HF_cptp.
        have disApApp_BpBpp : [disjoint S_ApApp & S_BpBpp].
        { by rewrite /S_ApApp /S_BpBpp disjointUX !disjointXU
            disA'B' disA'Bpp disAppB' disAppBpp. }
        have Hiso :=
          @smooth_iso_hmax R L H A B S_ApApp S_BpBpp
            disAB disApApp_BpBpp
            Ciso Cp_src Cpp_src Cp_tgt Cpp_tgt
            disA_Ciso disB_Ciso disApApp_Ciso disBpBpp_Ciso
            dimAB_Ciso dimApAppBpBpp_Ciso
            disA_Cp_src disA_Cpp_src disB_Cp_src disB_Cpp_src
            disCp_Cpp_src dimA_Cp_src dimCisoCp_Cpp_src dimB_Cpp_src
            disApApp_Cp_tgt disApApp_Cpp_tgt
            disBpBpp_Cp_tgt disBpBpp_Cpp_tgt
            disCp_Cpp_tgt dimApApp_Cp_tgt dimCisoCp_Cpp_tgt dimBpBpp_Cpp_tgt
            eps rhoAB UA VB HrhoAB_den Heps_pair.
        pose rho_dil : 'F[H]_(S_ApApp :|: S_BpBpp) :=
          (UA \⊗ VB) \o rhoAB \o (UA \⊗ VB)^A.
        have Hlift_output :
            exists tau_dil : 'F[H]_(S_ApApp :|: S_BpBpp),
              eps_ball eps rho_dil tau_dil /\
              (hmaxE S_BpBpp tau_dil <= hmaxE B' tauA'B'0)%E.
        {
          (* Regular-branch reduction: lift the arbitrary output witness
             tauA'B'0 from the processed marginal to the Stinespring
             dilation and compare hmax after tracing out App and Bpp.
             The projected A-side hmax part is isolated above as the local
             matrix reduction `hmax_mx_projected_A_app_le`; this block
             connects the labelled Uhlmann lift and Stinespring marginal
             equalities to that matrix statement. *)
            have PtauA'B'0 : tauA'B'0 \is psdlf :=
              eps_ball_psdlf HtauA'B'_ball.
            have HtauA'B'0_tr :
                @complex.Re R (\Tr tauA'B'0) <= 1 :=
              eps_ball_trlf HtauA'B'_ball.
            have HtauA'B'0_pd : pur_dist tauA'B'0 tauA'B' <= eps :=
              eps_ball_pur_dist HtauA'B'_ball.
          pose UV_dil := UA \⊗ VB.
          have HUV_dil_iso : UV_dil \is isolf.
          { apply/isolfP.
            rewrite /UV_dil tenf_adj -tenf_comp ?disAB ?disApApp_BpBpp //.
            by rewrite isofE isofE tenf11. }
          pose UV_dil_iso := IsoLf_Build HUV_dil_iso.
          have HUV_dilE : UV_dil = UV_dil_iso
            by exact: IsoLf_BuildE HUV_dil_iso.
          have HUV_dil_cptp : formso UV_dil_iso \is cptp
            by apply: is_cptp.
          have Hrho_dilE : rho_dil = formso UV_dil_iso rhoAB.
          { by rewrite /rho_dil -/UV_dil HUV_dilE formsoE. }
          have Prho_dil : rho_dil \is psdlf.
          { rewrite Hrho_dilE (CPMap_BuildE (cptp_cpmap HUV_dil_cptp)).
            exact: cp_psdP PrhoAB. }
          have Hrho_dil_tr_eq : \Tr rho_dil = \Tr rhoAB.
          { rewrite /rho_dil -/UV_dil HUV_dilE /formlf lftraceC comp_lfunA.
            by rewrite isofE comp_lfun1l. }
            have Hrho_dil_tr : @complex.Re R (\Tr rho_dil) <= 1
              by rewrite Hrho_dil_tr_eq.
          have disA'B'_AppBpp : [disjoint A' :|: B' & App :|: Bpp].
          { have disB'App : [disjoint B' & App]
              by rewrite disjoint_sym.
            by rewrite disjointXU !disjointUX disA'App
              disB'App disA'Bpp disB'Bpp. }
          have disA'B'_C' : [disjoint A' :|: B' & C0']
            by rewrite disjointUX disA'C' disB'C'.
          have disAB_C0 : [disjoint A :|: B & C0]
            by rewrite disjointUX disAC disBC.
          have HtauA'B'_EF : tauA'B' = (E :⊗ F) rhoAB.
          {
            apply/trlf_introdvl=> i j.
            set X : 'F[H]_(A' :|: B') := [> deltav i ; deltav j <].
            pose Y : 'F[H]_(A :|: B) := ((E :⊗ F)^*o) X.
            have HGdual1 :
                G^*o (\1 : 'F[H]_C0') = (\1 : 'F[H]_C0).
            {
              pose Gqc : 'QC[H]_(C0, C0') := QChannel_Build HG_cptp.
              pose Gdual : 'QU[H]_(C0', C0) := (Gqc^*o).
              change (Gdual (\1 : 'F[H]_C0') = (\1 : 'F[H]_C0)).
              exact: qu1_eq1 Gdual.
            }
            have Hpt_tau :
                ptrace_cast disA'B'_C' tauABC = tauA'B'.
            { rewrite /tauA'B' /ptrace_cast3C /ptrace_cast /ptrace_cast_gen.
              congr (castlf (_, _) _); exact: eq_irrelevance. }
            have Hpt_rho :
                ptrace_cast disAB_C0 rhoABC = rhoAB.
            { rewrite /rhoAB /ptrace_cast3C /ptrace_cast /ptrace_cast_gen.
              congr (castlf (_, _) _); exact: eq_irrelevance. }
            rewrite -Hpt_tau [\Tr (X \o ptrace_cast disA'B'_C' tauABC)]lftraceC.
            rewrite -(trlf_lift_partial_r disA'B'_C' tauABC X).
            rewrite /tauABC /entropy_data_proc_tau /entropy_data_proc_map.
            rewrite dualso_trlfE.
            have Hdual_tensor :
                ((E :⊗ F) :⊗ G)^*o (X \O (\1 : 'F[H]_C0')) =
                Y \O (G^*o (\1 : 'F[H]_C0')).
            {
              rewrite tenso_dual
                (sdotF_to_tenF disA'B'_C' X (\1 : 'F[H]_C0')).
              rewrite -(tenso_correct ((E :⊗ F)^*o) G^*o
                disA'B'_C' X (\1 : 'F[H]_C0')).
              by rewrite /Y
                -(sdotF_to_tenF disAB_C0 Y (G^*o (\1 : 'F[H]_C0'))).
            }
            rewrite Hdual_tensor HGdual1.
            rewrite [\Tr (X \o ((E :⊗ F) rhoAB))]lftraceC.
            rewrite dualso_trlfE -Hpt_rho -/Y.
            by rewrite -(trlf_lift_partial_r disAB_C0 rhoABC Y).
          }
          have eq_dil :
              S_ApApp :|: S_BpBpp = (A' :|: B') :|: (App :|: Bpp).
          { by setdec. }
          pose rho_dil_reg : 'F[H]_((A' :|: B') :|: (App :|: Bpp)) :=
            castlf (eq_dil, eq_dil) rho_dil.
          have Prho_dil_reg : rho_dil_reg \is psdlf.
          { rewrite /rho_dil_reg. exact: castlf_psdlf Prho_dil. }
          have Hrho_dil_reg_tr :
              @complex.Re R (\Tr rho_dil_reg) <= 1.
          { by rewrite /rho_dil_reg castlf_trlfE. }
          have Hrho_dil_marg :
              ptrace_cast disA'B'_AppBpp rho_dil_reg = tauA'B'.
          {
            have Hrho_dil_marg_EF :
                ptrace_cast disA'B'_AppBpp rho_dil_reg =
                (E :⊗ F) rhoAB.
            {
              apply/trlf_introdvl=> i j.
              pose XA : 'F[H]_A' :=
                [> deltav (idxSl i) ; deltav (idxSl j) <].
              pose XB : 'F[H]_B' :=
                [> deltav (idxSr i) ; deltav (idxSr j) <].
              pose XAB : 'F[H]_(A' :|: B') :=
                [> deltav i ; deltav j <].
              have HXAB_split :
                  XAB = (XA \O XB : 'F[H]_(A' :|: B')).
              {
                apply: to_Fnd_inj.
                by rewrite /XAB /XA /XB !dv_split -tenf_outp
                  to_Fnd_tenE (sdotFT _ _ disA'B').
              }
              have HE_dual_XA :
                  E^*o XA =
                  UA^A \o (XA \O (\1 : 'F[H]_App)) \o UA.
              {
                apply/trlf_introdvl=> p q.
                pose ZA : 'F[H]_A := [> deltav p ; deltav q <].
                rewrite -/ZA.
                rewrite [\Tr (ZA \o (E^*o XA))]lftraceC.
                rewrite -dualso_trlfEV -HE_after_UA comp_soE.
                rewrite castsoE /=.
                rewrite (QChannel_BuildE (@ptraceso_qc R L H App S_ApApp)).
                rewrite [\Tr (XA \o castlf _ _)]lftraceC.
                rewrite /ptrace_cast /ptrace_cast_gen.
                rewrite -(trlf_lift_partial_r disA'App (formso UA ZA) XA).
                rewrite formsoE.
                rewrite -!comp_lfunA.
                rewrite [\Tr (UA \o _)]lftraceC.
                by rewrite !comp_lfunA.
              }
              have HF_dual_XB :
                  F^*o XB =
                  VB^A \o (XB \O (\1 : 'F[H]_Bpp)) \o VB.
              {
                apply/trlf_introdvl=> p q.
                pose ZB : 'F[H]_B := [> deltav p ; deltav q <].
                rewrite -/ZB.
                rewrite [\Tr (ZB \o (F^*o XB))]lftraceC.
                rewrite -dualso_trlfEV -HF_after_VB comp_soE.
                rewrite castsoE /=.
                rewrite (QChannel_BuildE (@ptraceso_qc R L H Bpp S_BpBpp)).
                rewrite [\Tr (XB \o castlf _ _)]lftraceC.
                rewrite /ptrace_cast /ptrace_cast_gen.
                rewrite -(trlf_lift_partial_r disB'Bpp (formso VB ZB) XB).
                rewrite formsoE.
                rewrite -!comp_lfunA.
                rewrite [\Tr (VB \o _)]lftraceC.
                by rewrite !comp_lfunA.
              }
              pose KA : 'F[H]_S_ApApp :=
                XA \O (\1 : 'F[H]_App).
              pose KB : 'F[H]_S_BpBpp :=
                XB \O (\1 : 'F[H]_Bpp).
              have Htest_cast :
                  let Zreg : 'F[H]_((A' :|: B') :|: (App :|: Bpp)) :=
                    XAB \O (\1 : 'F[H]_(App :|: Bpp)) in
                  castlf (esym eq_dil, esym eq_dil) Zreg =
                  (KA \O KB : 'F[H]_(S_ApApp :|: S_BpBpp)).
              {
                simpl.
                rewrite /KA /KB HXAB_split -sdotf11.
                apply: to_Fnd_inj.
                rewrite Fnd_cast !to_Fnd_sdotE.
                rewrite !dotFsA //.
                rewrite -[X in (_ = (X \· to_Fnd (\1 : 'F[H]_Bpp))%FND)]dotFsA //.
                have disB'App : [disjoint B' & App]
                  by rewrite disjoint_sym.
                rewrite (@dotFC R L H (to_Fnd (\1 : 'F[H]_App))
                  (to_Fnd XB)) ?disB'App //.
                by rewrite dotFsA.
              }
              pose Zreg : 'F[H]_((A' :|: B') :|: (App :|: Bpp)) :=
                XAB \O (\1 : 'F[H]_(App :|: Bpp)).
              have Htrace_reg :
                  \Tr (rho_dil_reg \o
                    Zreg) =
                  \Tr (rho_dil \o
                    (KA \O KB : 'F[H]_(S_ApApp :|: S_BpBpp))).
              {
                rewrite /rho_dil_reg.
                have Hcast_trace :
                    \Tr (castlf (eq_dil, eq_dil) rho_dil \o Zreg) =
                    \Tr (rho_dil \o
                      castlf (esym eq_dil, esym eq_dil) Zreg).
                { clearbody Zreg.
                  clear -eq_dil rho_dil Zreg.
                  case: _ / eq_dil in rho_dil Zreg *.
                  by rewrite !castlf_id. }
                by rewrite Hcast_trace Htest_cast.
              }
              have HK_dual :
                  (UA \⊗ VB)^A \o (KA \O KB) \o (UA \⊗ VB) =
                  ((E^*o XA) \O (F^*o XB) : 'F[H]_(A :|: B)).
              {
                rewrite (sdotF_to_tenF disApApp_BpBpp KA KB).
                rewrite tenf_adj -!tenf_comp ?disAB ?disApApp_BpBpp //.
                rewrite -/KA -/KB -HE_dual_XA -HF_dual_XB.
                by rewrite -(sdotF_to_tenF disAB (E^*o XA) (F^*o XB)).
              }
              have Htrace_dil :
                  \Tr (rho_dil \o
                    (KA \O KB : 'F[H]_(S_ApApp :|: S_BpBpp))) =
                  \Tr (rhoAB \o
                    ((E^*o XA) \O (F^*o XB) : 'F[H]_(A :|: B))).
              {
                rewrite /rho_dil.
                rewrite ?comp_lfunA.
                rewrite lftraceC.
                rewrite !comp_lfunA.
                rewrite lftraceC.
                rewrite !comp_lfunA.
                rewrite HK_dual.
                by rewrite lftraceC.
              }
              have Hdual_EF_X :
                  (E :⊗ F)^*o XAB =
                  ((E^*o XA) \O (F^*o XB) : 'F[H]_(A :|: B)).
              {
                rewrite HXAB_split tenso_dual
                  (sdotF_to_tenF disA'B' XA XB).
                rewrite -(tenso_correct (E^*o) (F^*o) disA'B' XA XB).
                by rewrite -(sdotF_to_tenF disAB (E^*o XA) (F^*o XB)).
              }
              rewrite -/XAB [\Tr (XAB \o ptrace_cast _ _)]lftraceC.
              rewrite -(trlf_lift_partial_r disA'B'_AppBpp rho_dil_reg XAB).
              rewrite Htrace_reg Htrace_dil.
              rewrite [\Tr (XAB \o (E :⊗ F) rhoAB)]lftraceC.
              by rewrite dualso_trlfE Hdual_EF_X.
            }
            by rewrite Hrho_dil_marg_EF HtauA'B'_EF.
          }
          have [tau_ext [Ptau_ext [Htau_ext_tr
              [Htau_ext_marg Htau_ext_pd]]]] :=
            @pd_ext_subnorm R L H (A' :|: B') (App :|: Bpp)
              disA'B'_AppBpp tauA'B' tauA'B'0 rho_dil_reg
              Prho_dil_reg Hrho_dil_reg_tr Hrho_dil_marg
              PtauA'B'0 HtauA'B'0_tr.
          pose tau_raw : 'F[H]_(S_ApApp :|: S_BpBpp) :=
            castlf (esym eq_dil, esym eq_dil) tau_ext.
          pose PA : 'F[H]_S_ApApp := UA \o UA^A.
          pose Pfull : 'F[H]_(S_ApApp :|: S_BpBpp) :=
            PA \O (\1 : 'F[H]_S_BpBpp).
          pose tau_dil : 'F[H]_(S_ApApp :|: S_BpBpp) :=
            Pfull \o tau_raw \o Pfull.
          have Htau_dil_ball : eps_ball eps rho_dil tau_dil.
          {
            have Ptau_raw : tau_raw \is psdlf.
            { rewrite /tau_raw. exact: castlf_psdlf Ptau_ext. }
            have Htau_raw_tr : @complex.Re R (\Tr tau_raw) <= 1.
            { by rewrite /tau_raw castlf_trlfE. }
            have Htau_raw_pd : pur_dist tau_raw rho_dil <= eps.
            {
              have Hpd_cast :
                  pur_dist tau_raw rho_dil =
                  pur_dist tau_ext rho_dil_reg.
              {
                clear Ptau_raw Htau_raw_tr Ptau_ext Htau_ext_tr
                  Htau_ext_marg Htau_ext_pd Prho_dil_reg
                  Hrho_dil_reg_tr Hrho_dil_marg Hrho_dilE Prho_dil
                  Hrho_dil_tr_eq Hrho_dil_tr.
                rewrite /tau_raw /rho_dil_reg.
                case: _ / eq_dil in rho_dil rho_dil_reg tau_ext tau_raw tau_dil *.
                by rewrite !castlf_id.
              }
              have Hpd_ext_sym :
                  pur_dist tau_ext rho_dil_reg =
                  pur_dist rho_dil_reg tau_ext.
              {
                have Htau_mx : h2mx tau_ext \is psdmx
                  by move: Ptau_ext; rewrite qualifE.
                have Hrho_mx : h2mx rho_dil_reg \is psdmx
                  by move: Prho_dil_reg; rewrite qualifE.
                rewrite /pur_dist /gfid.
                exact: (f_equal (fun x => Num.sqrt (1 - x^2))
                  (gfid_sym_mx Htau_mx Hrho_mx)).
              }
              have Hpd_base_sym :
                  pur_dist tauA'B' tauA'B'0 =
                  pur_dist tauA'B'0 tauA'B'.
              {
                have PtauA'B' : tauA'B' \is psdlf.
                { rewrite /tauA'B' /ptrace_cast3C.
                  apply: ptrace_cast_gen_psdlf.
                  rewrite /tauABC /entropy_data_proc_tau.
                  have Pmap_cptp : entropy_data_proc_map E F G \is cptp.
                  { rewrite /entropy_data_proc_map.
                    have HEF_cptp : (E :⊗ F) \is cptp.
                    { exact: (@tenso_qc R L H A A' B B'
                        disAB disA'B' (QChannel_Build HE_cptp)
                        (QChannel_Build HF_cptp)). }
                    exact: (@tenso_qc R L H (A :|: B) (A' :|: B') C0 C0'
                      disAB_C0 disA'B'_C' (QChannel_Build HEF_cptp)
                      (QChannel_Build HG_cptp)). }
                  rewrite (CPMap_BuildE (cptp_cpmap Pmap_cptp)).
                  exact: cp_psdP PrhoABC. }
                have Htau_mx : h2mx tauA'B' \is psdmx
                  by move: PtauA'B'; rewrite qualifE.
                have Htau0_mx : h2mx tauA'B'0 \is psdmx
                  by move: PtauA'B'0; rewrite qualifE.
                rewrite /pur_dist /gfid.
                exact: (f_equal (fun x => Num.sqrt (1 - x^2))
                  (gfid_sym_mx Htau_mx Htau0_mx)).
              }
              by rewrite Hpd_cast Hpd_ext_sym Htau_ext_pd
                Hpd_base_sym.
            }
            have HPA_proj : PA \is projlf.
            {
              apply/projlfP; split.
              - by rewrite /PA adjf_comp adjfK.
              - apply/lfunP=> x; rewrite /PA !comp_lfunE /=.
                have -> : UA^A (UA (UA^A x)) = UA^A x.
                { rewrite -comp_lfunE [UA^A \o UA]isofE. by rewrite lfunE. }
                reflexivity.
            }
            have HPfull_eq :
                Pfull =
                (PA \⊗ (\1 : 'F[H]_S_BpBpp)
                  : 'F[H]_(S_ApApp :|: S_BpBpp)).
            { apply: to_Fnd_inj.
              by rewrite /Pfull (sdotFT _ _ disApApp_BpBpp) to_Fnd_tenE. }
            have HPfull_proj : Pfull \is projlf.
            {
              move: HPA_proj => /projlfP [HPAh HPAid].
              apply/projlfP; split.
              - by rewrite HPfull_eq tenf_adj HPAh adjf1 -HPfull_eq.
              - by rewrite HPfull_eq -tenf_comp ?HPAid ?comp_lfun1l
                  ?comp_lfun1r -?HPfull_eq.
            }
            have HPfull_herm : Pfull^A = Pfull
              := hermlf_adjE (projlf_herm HPfull_proj).
            have HPfull_bound : Pfull \is bound1lf
              := projlf_bound1 HPfull_proj.
            have HPfullB :
                (Bound1Lf_Build HPfull_bound
                  : 'F[H]_(S_ApApp :|: S_BpBpp)) = Pfull.
            { by rewrite -(Bound1Lf_BuildE HPfull_bound). }
            have Hform_tau_raw :
                formso (Bound1Lf_Build HPfull_bound) tau_raw = tau_dil.
            {
              rewrite formsoE.
              rewrite HPfullB.
              by rewrite HPfull_herm /tau_dil.
            }
            have HPfull_rho : Pfull \o rho_dil \o Pfull = rho_dil.
            {
              have HPA_UA : PA \o UA = UA.
              {
                apply/lfunP=> x; rewrite /PA !comp_lfunE /=.
                have -> : UA^A (UA x) = x.
                { rewrite -comp_lfunE [UA^A \o UA]isofE. by rewrite lfunE. }
                reflexivity.
              }
              have HUA_PA : UA^A \o PA = UA^A.
              {
                apply/lfunP=> x; rewrite /PA !comp_lfunE /=.
                have -> : UA^A (UA (UA^A x)) = UA^A x.
                { rewrite -comp_lfunE [UA^A \o UA]isofE. by rewrite lfunE. }
                reflexivity.
              }
              have HPfull_UV : Pfull \o UV_dil = UV_dil.
              {
                rewrite /UV_dil.
                rewrite HPfull_eq.
                rewrite -tenf_comp ?disAB ?disApApp_BpBpp //.
                by rewrite HPA_UA comp_lfun1l.
              }
              have HUV_Pfull : UV_dil^A \o Pfull = UV_dil^A.
              {
                rewrite /UV_dil.
                rewrite tenf_adj HPfull_eq.
                rewrite -tenf_comp ?disAB ?disApApp_BpBpp //.
                by rewrite HUA_PA comp_lfun1r -tenf_adj.
              }
              apply/lfunP=> x.
              rewrite /rho_dil -/UV_dil !comp_lfunE /=.
              have Hpre : UV_dil^A (Pfull x) = UV_dil^A x
                by rewrite -comp_lfunE HUV_Pfull.
              have Hpost y : Pfull (UV_dil y) = UV_dil y
                by rewrite -comp_lfunE HPfull_UV.
              by rewrite Hpre Hpost.
            }
            have Hform_rho :
                formso (Bound1Lf_Build HPfull_bound) rho_dil = rho_dil.
            {
              rewrite formsoE.
              rewrite HPfullB.
              by rewrite HPfull_herm HPfull_rho.
            }
            have Ptau_dil : tau_dil \is psdlf.
            {
              have Hform_psd :
                  formso (Bound1Lf_Build HPfull_bound) tau_raw \is psdlf
                by exact: cp_psdP Ptau_raw.
              by rewrite Hform_tau_raw in Hform_psd.
            }
            have Htau_dil_tr : @complex.Re R (\Tr tau_dil) <= 1.
            {
              have Htr_form : \Tr tau_dil <= \Tr tau_raw.
              {
                have := qo_trlfE
                  (formso (Bound1Lf_Build HPfull_bound)) Ptau_raw.
                by rewrite Hform_tau_raw.
              }
              have Htau_dil_real : \Tr tau_dil \is Num.real
                := ger0_real (psdlf_trlf Ptau_dil).
              have Htau_raw_real : \Tr tau_raw \is Num.real
                := ger0_real (psdlf_trlf Ptau_raw).
              move: Htr_form.
              rewrite -(RRe_real Htau_dil_real)
                -(RRe_real Htau_raw_real) lecR => Htr_form.
              exact: le_trans Htr_form Htau_raw_tr.
            }
              have Htau_dil_pd : pur_dist tau_dil rho_dil <= eps.
              {
              have Hform_cptn :
                  (formso (Bound1Lf_Build HPfull_bound)
                    : 'SO('H[H]_(S_ApApp :|: S_BpBpp),
                          'H[H]_(S_ApApp :|: S_BpBpp))) \is cptn
                by exact: is_cptn.
              have [_ Hpd] :=
                pd_mono Hform_cptn Ptau_raw Prho_dil
                  Htau_raw_tr Hrho_dil_tr.
                rewrite Hform_tau_raw Hform_rho in Hpd.
                exact: le_trans Hpd Htau_raw_pd.
              }
              have Htau_dil_pos : 0 < @complex.Re R (\Tr tau_dil).
              {
                have Heps_pair_dil :
                    0 <= eps < Num.sqrt (@complex.Re R (\Tr rho_dil)).
                { by rewrite Hrho_dil_tr_eq. }
                have Holdball :
                    ((tau_dil \is psdlf) &&
                     (@complex.Re R (\Tr tau_dil) <= 1)) &&
                    (pur_dist tau_dil rho_dil <= eps).
                { by rewrite Ptau_dil Htau_dil_tr Htau_dil_pd. }
                exact: (eps_ball_trace_pos_from_small Prho_dil
                  Hrho_dil_tr Heps_pair_dil Holdball).
              }
              by rewrite /eps_ball Ptau_dil Htau_dil_pos
                Htau_dil_tr Htau_dil_pd.
            }
            exists tau_dil; split; first exact: Htau_dil_ball.
            - have Ptau_dil : tau_dil \is psdlf :=
                eps_ball_psdlf Htau_dil_ball.
              have Htau_dil_tr : @complex.Re R (\Tr tau_dil) <= 1 :=
                eps_ball_trlf Htau_dil_ball.
              have Htau_dil_pos : 0 < @complex.Re R (\Tr tau_dil).
              { exact: eps_ball_trlf_gt0 Htau_dil_ball. }
            have HtauA'B'_tr_eq : \Tr tauA'B' = \Tr rhoAB.
            {
              rewrite HtauA'B'_EF.
              have HEF_cptp : (E :⊗ F) \is cptp.
              { exact: (@tenso_qc R L H A A' B B' disAB disA'B'
                  (QChannel_Build HE_cptp) (QChannel_Build HF_cptp)). }
              move/cptpP: HEF_cptp => [_ /tpmapP Htp].
              exact: Htp.
            }
            have PtauA'B' : tauA'B' \is psdlf.
            {
              rewrite HtauA'B'_EF.
              have HEF_cptp : (E :⊗ F) \is cptp.
              { exact: (@tenso_qc R L H A A' B B' disAB disA'B'
                  (QChannel_Build HE_cptp) (QChannel_Build HF_cptp)). }
              rewrite (CPMap_BuildE (cptp_cpmap HEF_cptp)).
              exact: cp_psdP PrhoAB.
            }
            have HtauA'B'_tr : @complex.Re R (\Tr tauA'B') <= 1.
            { by rewrite HtauA'B'_tr_eq. }
              have Heps_pair_tau :
                  0 <= eps < Num.sqrt (@complex.Re R (\Tr tauA'B')).
              { by rewrite HtauA'B'_tr_eq. }
              have HtauA'B'0_pos : 0 < @complex.Re R (\Tr tauA'B'0).
              {
                have Holdball :
                    ((tauA'B'0 \is psdlf) &&
                     (@complex.Re R (\Tr tauA'B'0) <= 1)) &&
                    (pur_dist tauA'B'0 tauA'B' <= eps).
                { by rewrite PtauA'B'0 HtauA'B'0_tr HtauA'B'0_pd. }
                exact: (eps_ball_trace_pos_from_small PtauA'B'
                  HtauA'B'_tr Heps_pair_tau Holdball).
              }
            rewrite (hmaxE_labelled_product_mx disApApp_BpBpp
              Ptau_dil Htau_dil_tr Htau_dil_pos).
            rewrite (hmaxE_labelled_product_mx disA'B'
              PtauA'B'0 HtauA'B'0_tr HtauA'B'0_pos).
            rewrite lee_fin.
            have Hhmax_mx_le :
                hmax_mx
                  (biprod_mx disApApp_BpBpp tau_dil) <=
                hmax_mx
                  (biprod_mx disA'B' tauA'B'0).
            {
              have disA'_BpBpp : [disjoint A' & S_BpBpp].
              { by rewrite /S_BpBpp disjointXU disA'Bpp disA'B'. }
              have disA'BpBpp_App : [disjoint A' :|: S_BpBpp & App].
              {
                have disB'App : [disjoint B' & App]
                  by rewrite disjoint_sym.
                have disBppApp : [disjoint Bpp & App]
                  by rewrite disjoint_sym.
                by rewrite disjointUX disA'App /S_BpBpp disjointUX
                  disB'App disBppApp.
              }
              have eq_ext_App :
                  (A' :|: B') :|: (App :|: Bpp) =
                  (A' :|: S_BpBpp) :|: App.
              { by setdec. }
              pose tau_mid : 'F[H]_(A' :|: S_BpBpp) :=
                ptrace_cast disA'BpBpp_App
                  (castlf (eq_ext_App, eq_ext_App) tau_ext).
              have Ptau_mid : tau_mid \is psdlf.
              { rewrite /tau_mid. apply: ptrace_cast_gen_psdlf.
                exact: castlf_psdlf Ptau_ext. }
              have Htau_mid_tr : @complex.Re R (\Tr tau_mid) <= 1.
              {
                rewrite /tau_mid /ptrace_cast_gen castlf_trlfE.
                have /cptpP [_ /tpmapP Htp] :=
                  @ptraceso_qc R L H App ((A' :|: S_BpBpp) :|: App).
                rewrite Htp castlf_trlfE.
                exact: Htau_ext_tr.
              }
              have eq_mid_assoc : A' :|: S_BpBpp = A' :|: B' :|: Bpp.
              { by setdec. }
              pose tau_mid_assoc : 'F[H]_(A' :|: B' :|: Bpp) :=
                castlf (eq_mid_assoc, eq_mid_assoc) tau_mid.
              have Hmid_to_tau0 :
                  ptrace_cast3C disA'Bpp disB'Bpp tau_mid_assoc =
                  tauA'B'0.
              {
                rewrite -Htau_ext_marg.
                rewrite /tau_mid_assoc /tau_mid /ptrace_cast3C
                  /ptrace_cast /ptrace_cast_gen.
                have Hcomp_trace :=
                  congr1
                    (fun F : 'SO[H]_((A' :|: S_BpBpp) :|: App,
                       ((((A' :|: S_BpBpp) :|: App) :\: App) :\: Bpp)) =>
                       F (castlf (eq_ext_App, eq_ext_App) tau_ext))
                    (@ptraceso_comp R L H Bpp App
                      ((A' :|: S_BpBpp) :|: App)).
                move: Hcomp_trace.
                rewrite comp_soE castsoE /= castlf_id.
                move=> Hcomp_trace.
                have eq_res_mid :
                    (A' :|: S_BpBpp) :\: Bpp =
                    (A' :|: B' :|: Bpp) :\: Bpp
                  by rewrite eq_mid_assoc.
                have eq_res_after_App :
                    (((A' :|: S_BpBpp) :|: App) :\: App) :\: Bpp =
                    (A' :|: S_BpBpp) :\: Bpp
                  by rewrite (setDU_r disA'BpBpp_App).
                have eq_res_union :
                    ((A' :|: B') :|: (App :|: Bpp)) :\: (App :|: Bpp) =
                    ((A' :|: S_BpBpp) :|: App) :\: (App :|: Bpp)
                  by rewrite eq_ext_App.
                rewrite (ptracelf_castlf_eq eq_mid_assoc eq_res_mid).
                rewrite (ptracelf_castlf_eq (setDU_r disA'BpBpp_App)
                  eq_res_after_App).
                rewrite Hcomp_trace.
                rewrite (ptracelf_castlf_eq eq_ext_App eq_res_union).
                rewrite !castlf_comp.
                by congr (castlf (_, _) _); exact: eq_irrelevance.
              }
              have Htau_mid_pos : 0 < @complex.Re R (\Tr tau_mid).
              {
                move: HtauA'B'0_pos.
                rewrite -Hmid_to_tau0 /tau_mid_assoc /ptrace_cast3C.
                rewrite /ptrace_cast_gen !castlf_trlfE.
                have /cptpP [_ /tpmapP Htp] :=
                  @ptraceso_qc R L H Bpp (A' :|: B' :|: Bpp).
                rewrite Htp.
                move=> Hpos.
                move: Hpos.
                rewrite /tau_mid /ptrace_cast_gen !castlf_trlfE.
                have /cptpP [_ /tpmapP Htp2] :=
                  @ptraceso_qc R L H App ((A' :|: S_BpBpp) :|: App).
                by rewrite Htp2 castlf_trlfE.
              }
              have Hmid_mx_le :
                  hmax_mx
                    (biprod_mx disA'_BpBpp tau_mid) <=
                  hmax_mx
                    (biprod_mx disA'B' tauA'B'0).
              {
                rewrite -(@hmax_labelled_product_mx R L H A' S_BpBpp
                  disA'_BpBpp tau_mid Ptau_mid).
                rewrite -(@hmax_labelled_product_mx R L H A' B'
                  disA'B' tauA'B'0 PtauA'B'0).
                have Hmid_sup :
                    has_sup [set v : R | hmax_feasible S_BpBpp tau_mid v].
                { exact: (@hmax_has_sup R L H (A' :|: S_BpBpp)
                    S_BpBpp tau_mid Ptau_mid Htau_mid_tr Htau_mid_pos). }
                have Htau0_sup :
                    has_sup [set v : R | hmax_feasible B' tauA'B'0 v].
                { exact: (@hmax_has_sup R L H (A' :|: B') B'
                    tauA'B'0 PtauA'B'0 HtauA'B'0_tr HtauA'B'0_pos). }
                apply: (@hmax_lub R L H (A' :|: S_BpBpp) S_BpBpp
                  tau_mid (hmax B' tauA'B'0) Hmid_sup).
                move=> v [sigma [Psigma_den Hv]].
                have eqSig_mid :
                    ((A' :|: S_BpBpp) :&: S_BpBpp) = S_BpBpp
                  by setdec.
                pose sigmaBBpp : 'F[H]_S_BpBpp :=
                  castlf (eqSig_mid, eqSig_mid) sigma.
                have PsigmaBBpp_den : sigmaBBpp \is den1lf.
                { apply/den1lfP; split.
                  - exact: castlf_psdlf (den1lf_psd Psigma_den).
                  - by rewrite /sigmaBBpp castlf_trlfE
                      (den1lf_trlf Psigma_den). }
                pose sigmaB' : 'F[H]_B' :=
                  ptrace_cast disB'Bpp sigmaBBpp.
                have PsigmaB'_den : sigmaB' \is den1lf.
                { apply/den1lfP; split.
                  - rewrite /sigmaB'.
                    exact: ptrace_cast_gen_psdlf
                      (den1lf_psd PsigmaBBpp_den).
                  - rewrite /sigmaB' /ptrace_cast /ptrace_cast_gen
                      castlf_trlfE.
                    have /cptpP [_ /tpmapP Htp] :=
                      @ptraceso_qc R L H Bpp S_BpBpp.
                    by rewrite Htp (den1lf_trlf PsigmaBBpp_den). }
                have eqSig_small : ((A' :|: B') :&: B') = B'
                  by setdec.
                pose sigma0 : 'F[H]_((A' :|: B') :&: B') :=
                  castlf (esym eqSig_small, esym eqSig_small) sigmaB'.
                have Psigma0_den : sigma0 \is den1lf.
                { apply/den1lfP; split.
                  - exact: castlf_psdlf (den1lf_psd PsigmaB'_den).
                  - by rewrite /sigma0 castlf_trlfE
                      (den1lf_trlf PsigmaB'_den). }
                have eqST_mid :
                    ((A' :|: S_BpBpp) :\: S_BpBpp) :|:
                    ((A' :|: S_BpBpp) :&: S_BpBpp) =
                    A' :|: S_BpBpp
                  by rewrite finset.setUC finset.setID.
                pose target_mid : 'F[H]_(A' :|: S_BpBpp) :=
                  castlf (eqST_mid, eqST_mid)
                    ((((dim 'H[H]_((A' :|: S_BpBpp) :\: S_BpBpp))%:R^-1)%:C *:
                      ((\1 : 'F[H]_((A' :|: S_BpBpp) :\: S_BpBpp))
                        \O sigma))).
                have Hv_mid :
                    elog2
                      ((dim 'H[H]_((A' :|: S_BpBpp) :\: S_BpBpp))%:R *
                        (gfid tau_mid target_mid) ^+ 2) = v%:E.
                { move: Hv.
                  rewrite /target_mid.
                  set e := (X in castlf (X, X) _).
                  by rewrite (eq_irrelevance e eqST_mid). }
                have eqST_small :
                    ((A' :|: B') :\: B') :|: ((A' :|: B') :&: B') =
                    A' :|: B'
                  by rewrite finset.setUC finset.setID.
                pose target_small : 'F[H]_(A' :|: B') :=
                  castlf (eqST_small, eqST_small)
                    ((((dim 'H[H]_((A' :|: B') :\: B'))%:R^-1)%:C *:
                      ((\1 : 'F[H]_((A' :|: B') :\: B')) \O sigma0))).
                have Ptarget_mid : target_mid \is psdlf.
                {
                  rewrite /target_mid; apply: castlf_psdlf.
                  apply: psdlfZ; first by rewrite lecR invr_ge0 ler0n.
                  have disMid :
                      [disjoint (A' :|: S_BpBpp) :\: S_BpBpp
                         & (A' :|: S_BpBpp) :&: S_BpBpp]
                    by setdec.
                  have -> :
                      ((\1 : 'F[H]_((A' :|: S_BpBpp) :\: S_BpBpp))
                        \O sigma
                       : 'F[H]_(((A' :|: S_BpBpp) :\: S_BpBpp) :|:
                         ((A' :|: S_BpBpp) :&: S_BpBpp))) =
                      ((\1 : 'F[H]_((A' :|: S_BpBpp) :\: S_BpBpp))
                        \⊗ sigma).
                  { by apply: to_Fnd_inj; rewrite (sdotFT _ _ disMid)
                      to_Fnd_tenE. }
                  rewrite psdlfE.
                  apply: tenf_ge0; first exact: disMid.
                  - by rewrite -psdlfE qualifE h2mx1; exact: psdmx1.
                  - by rewrite -psdlfE; exact: den1lf_psd Psigma_den.
                }
                have Ptarget_small : target_small \is psdlf.
                {
                  rewrite /target_small; apply: castlf_psdlf.
                  apply: psdlfZ; first by rewrite lecR invr_ge0 ler0n.
                  have disSmall :
                      [disjoint (A' :|: B') :\: B'
                         & (A' :|: B') :&: B']
                    by setdec.
                  have -> :
                      ((\1 : 'F[H]_((A' :|: B') :\: B')) \O sigma0
                       : 'F[H]_(((A' :|: B') :\: B') :|:
                         ((A' :|: B') :&: B'))) =
                      ((\1 : 'F[H]_((A' :|: B') :\: B')) \⊗ sigma0).
                  { by apply: to_Fnd_inj; rewrite (sdotFT _ _ disSmall)
                      to_Fnd_tenE. }
                  rewrite psdlfE.
                  apply: tenf_ge0; first exact: disSmall.
                  - by rewrite -psdlfE qualifE h2mx1; exact: psdmx1.
                  - by rewrite -psdlfE; exact: den1lf_psd Psigma0_den.
                }
                have disA'B'_Bpp : [disjoint A' :|: B' & Bpp]
                  by rewrite disjointUX disA'Bpp disB'Bpp.
                have Htau_ptr :
                    ptrace_cast disA'B'_Bpp tau_mid_assoc = tauA'B'0.
                { rewrite -Hmid_to_tau0 /ptrace_cast3C /ptrace_cast
                    /ptrace_cast_gen.
                  by congr (castlf (_, _) _); exact: eq_irrelevance. }
                pose target_mid_assoc : 'F[H]_(A' :|: B' :|: Bpp) :=
                  castlf (eq_mid_assoc, eq_mid_assoc) target_mid.
                have Htarget_ptr :
                    ptrace_cast disA'B'_Bpp target_mid_assoc = target_small.
                {
                  have Htarget_mid_assoc_simpl :
                      target_mid_assoc =
                      castlf (finset.setUA A' B' Bpp,
                        finset.setUA A' B' Bpp)
                        ((((dim 'H[H]_A')%:R^-1)%:C *:
                          ((\1 : 'F[H]_A') \O sigmaBBpp))).
                  {
                    have eqA_mid :
                        (A' :|: S_BpBpp) :\: S_BpBpp = A'
                      by exact: setDU_r disA'_BpBpp.
                    have eqU1 :
                        (A' :|: S_BpBpp) :\: S_BpBpp :|:
                          (A' :|: S_BpBpp) :&: S_BpBpp =
                        A' :|: (A' :|: S_BpBpp) :&: S_BpBpp
                      by rewrite eqA_mid.
                    have eqU2 :
                        A' :|: (A' :|: S_BpBpp) :&: S_BpBpp =
                        A' :|: S_BpBpp
                      by rewrite eqSig_mid.
                    have Hmid_lift :
                        castlf (eqST_mid, eqST_mid)
                          ((\1 : 'F[H]_((A' :|: S_BpBpp) :\: S_BpBpp))
                            \O sigma) =
                        ((\1 : 'F[H]_A') \O sigmaBBpp
                          : 'F[H]_(A' :|: S_BpBpp)).
                    {
                      transitivity
                        (castlf (etrans eqU1 eqU2, etrans eqU1 eqU2)
                          ((\1 : 'F[H]_((A' :|: S_BpBpp) :\: S_BpBpp))
                            \O sigma)).
                      { by rewrite (eq_irrelevance (etrans eqU1 eqU2)
                          eqST_mid). }
                      rewrite -(castlf_comp eqU1 eqU1 eqU2 eqU2).
                      rewrite (sdotIf_cast_l eqA_mid eqU1) castlf1.
                      rewrite (sdotIf_cast_r eqSig_mid eqU2).
                      by rewrite /sigmaBBpp.
                    }
                    rewrite /target_mid_assoc /target_mid linearZ /=
                      Hmid_lift eqA_mid.
                    by rewrite (eq_irrelevance eq_mid_assoc
                      (finset.setUA A' B' Bpp)).
                  }
                  have Htarget_small_simpl :
                      target_small =
                      ((((dim 'H[H]_A')%:R^-1)%:C *:
                        ((\1 : 'F[H]_A') \O sigmaB'))).
                  {
                    have eqA_small :
                        (A' :|: B') :\: B' = A'
                      by exact: setDU_r disA'B'.
                    have eqU1 :
                        (A' :|: B') :\: B' :|:
                          (A' :|: B') :&: B' =
                        A' :|: (A' :|: B') :&: B'
                      by rewrite eqA_small.
                    have eqU2 :
                        A' :|: (A' :|: B') :&: B' = A' :|: B'
                      by rewrite eqSig_small.
                    have Hsmall_lift :
                        castlf (eqST_small, eqST_small)
                          ((\1 : 'F[H]_((A' :|: B') :\: B')) \O sigma0) =
                        ((\1 : 'F[H]_A') \O sigmaB'
                          : 'F[H]_(A' :|: B')).
                    {
                      transitivity
                        (castlf (etrans eqU1 eqU2, etrans eqU1 eqU2)
                          ((\1 : 'F[H]_((A' :|: B') :\: B')) \O sigma0)).
                      { by rewrite (eq_irrelevance (etrans eqU1 eqU2)
                          eqST_small). }
                      rewrite -(castlf_comp eqU1 eqU1 eqU2 eqU2).
                      rewrite (sdotIf_cast_l eqA_small eqU1) castlf1.
                      rewrite (sdotIf_cast_r eqSig_small eqU2).
                      rewrite /sigma0 castlf_comp.
                      rewrite (eq_irrelevance
                        (etrans (esym eqSig_small) eqSig_small) (erefl _)).
                      by rewrite castlf_id.
                    }
                    by rewrite /target_small linearZ /= Hsmall_lift eqA_small.
                  }
                  have Hptrace3 :
                      forall z : 'F[H]_(A' :|: B' :|: Bpp),
                      ptrace_cast disA'B'_Bpp z =
                      ptrace_cast3C disA'Bpp disB'Bpp z.
                  { move=> z.
                    rewrite /ptrace_cast3C /ptrace_cast /ptrace_cast_gen.
                    by congr (castlf (_, _) _); exact: eq_irrelevance. }
                  rewrite Htarget_mid_assoc_simpl Htarget_small_simpl
                    Hptrace3.
                  rewrite linearZ /=.
                  have Hptr3C_Z (c : C)
                      (z : 'F[H]_(A' :|: B' :|: Bpp)) :
                      ptrace_cast3C disA'Bpp disB'Bpp (c *: z) =
                      c *: ptrace_cast3C disA'Bpp disB'Bpp z.
                  { rewrite /ptrace_cast3C /ptrace_cast_gen.
                    have HtrZ : \Tr_(Bpp) (c *: z) = c *: \Tr_(Bpp) z
                      by exact: linearZ.
                    rewrite HtrZ.
                    exact: linearZ. }
                  rewrite Hptr3C_Z.
                  rewrite (@ptrace_cast3C_sdot_right R L H A' B' Bpp
                    disA'B' disA'Bpp disB'Bpp
                    (\1 : 'F[H]_A') sigmaBBpp).
                  by rewrite /sigmaB'.
                }
                have Hgfid_cast :
                    gfid tau_mid target_mid =
                    gfid tau_mid_assoc target_mid_assoc.
                { by rewrite /tau_mid_assoc /target_mid_assoc /gfid
                    !h2mx_castlf gfid_cast_mx. }
                have Hgfid_le :
                    gfid tau_mid target_mid <=
                    gfid tauA'B'0 target_small.
                {
                  rewrite Hgfid_cast.
                  have Ptau_mid_assoc : tau_mid_assoc \is psdlf.
                  { rewrite /tau_mid_assoc; exact: castlf_psdlf Ptau_mid. }
                  have Ptarget_mid_assoc : target_mid_assoc \is psdlf.
                  { rewrite /target_mid_assoc; exact: castlf_psdlf Ptarget_mid. }
                  have Hmono :=
                    @gfid_ptr_mono R L H (A' :|: B') Bpp disA'B'_Bpp
                      tau_mid_assoc target_mid_assoc
                      Ptau_mid_assoc Ptarget_mid_assoc dim_proper.
                  by rewrite Htau_ptr Htarget_ptr in Hmono.
                }
                pose arg_mid :=
                  (dim 'H[H]_((A' :|: S_BpBpp) :\: S_BpBpp))%:R *
                  (gfid tau_mid target_mid) ^+ 2.
                pose arg_small :=
                  (dim 'H[H]_((A' :|: B') :\: B'))%:R *
                  (gfid tauA'B'0 target_small) ^+ 2.
                have Harg_mid_pos : 0 < arg_mid.
                { case: (ltP 0 arg_mid) => // Harg_le0.
                  move: Hv_mid; rewrite /arg_mid (elog2_le0 Harg_le0).
                  by discriminate. }
                have Hv_eq : v = log2 arg_mid.
                { move: Hv_mid; rewrite /arg_mid (elog2_gt0 Harg_mid_pos).
                  by case. }
                have Hmid_gfid_ge0 : 0 <= gfid tau_mid target_mid.
                { rewrite /gfid.
                  exact: gfid_ge0_mx (psdlf_h2mx Ptau_mid)
                    (psdlf_h2mx Ptarget_mid). }
                have Hsmall_gfid_ge0 : 0 <= gfid tauA'B'0 target_small.
                { rewrite /gfid.
                  exact: gfid_ge0_mx (psdlf_h2mx PtauA'B'0)
                    (psdlf_h2mx Ptarget_small). }
                have Harg_le : arg_mid <= arg_small.
                {
                  rewrite /arg_mid /arg_small.
                  have Hdim_eq :
                      dim 'H[H]_((A' :|: S_BpBpp) :\: S_BpBpp) =
                      dim 'H[H]_((A' :|: B') :\: B').
                  { by rewrite (setDU_r disA'_BpBpp)
                      (setDU_r disA'B'). }
                  rewrite Hdim_eq.
                  apply: ler_wpM2l; first by rewrite ler0n.
                  have Hsq_le :=
                    lerXn2r 2 Hmid_gfid_ge0 Hsmall_gfid_ge0 Hgfid_le.
                  exact: Hsq_le.
                }
                have Harg_small_pos : 0 < arg_small :=
                  lt_le_trans Harg_mid_pos Harg_le.
                pose w := log2 arg_small.
                have Hw_feas : hmax_feasible B' tauA'B'0 w.
                {
                  exists sigma0; split; first exact: Psigma0_den.
                  rewrite /w /arg_small /target_small.
                  set e := (X in castlf (X, X) _).
                  rewrite (eq_irrelevance e eqST_small).
                  by rewrite (elog2_gt0 Harg_small_pos).
                }
                rewrite Hv_eq /w.
                exact: le_trans (log2_le_pos Harg_mid_pos Harg_le)
                  (@hmax_ub R L H (A' :|: B') B' tauA'B'0 w
                    Htau0_sup Hw_feas).
              }
              have HPA_proj_local : PA \is projlf.
              {
                apply/projlfP; split.
                - by rewrite /PA adjf_comp adjfK.
                - apply/lfunP=> x; rewrite /PA !comp_lfunE /=.
                  have -> : UA^A (UA (UA^A x)) = UA^A x.
                  { rewrite -comp_lfunE [UA^A \o UA]isofE. by rewrite lfunE. }
                  reflexivity.
              }
              have HE_cp : E \is cpmap := cptp_cpmap HE_cptp.
              have HEsub : E (\1 : 'F[H]_A) <= (\1 : 'F[H]_A').
              {
                rewrite (CPMap_BuildE HE_cp).
                rewrite -(@cp_isdualtnE R _ _ (CPMap_Build HE_cp)).
                by rewrite -(CPMap_BuildE HE_cp).
              }
              have HPA_marg : ptrace_cast disA'App PA = E (\1 : 'F[H]_A).
              {
                have HUA1 := congr1
                  (fun K : 'SO[H]_(A, A') => K (\1 : 'F[H]_A))
                  HE_after_UA.
                move: HUA1.
                rewrite comp_soE castsoE /=.
                rewrite (QChannel_BuildE (@ptraceso_qc R L H App S_ApApp)).
                rewrite /ptrace_cast /ptrace_cast_gen formsoE comp_lfun1r /PA.
                exact.
              }
              have HPA_ptr_le : ptrace_cast disA'App PA <= (\1 : 'F[H]_A')
                by rewrite HPA_marg.
              have Hproj_hmax_le :
                  hmax S_BpBpp tau_dil <= hmax S_BpBpp tau_mid.
              {
                have Htau_dil_sup :
                    has_sup [set v : R | hmax_feasible S_BpBpp tau_dil v].
                { exact: (@hmax_has_sup R L H (S_ApApp :|: S_BpBpp)
                    S_BpBpp tau_dil Ptau_dil Htau_dil_tr Htau_dil_pos). }
                have Htau_mid_sup :
                    has_sup [set v : R | hmax_feasible S_BpBpp tau_mid v].
                { exact: (@hmax_has_sup R L H (A' :|: S_BpBpp)
                    S_BpBpp tau_mid Ptau_mid Htau_mid_tr Htau_mid_pos). }
                apply: (@hmax_lub R L H (S_ApApp :|: S_BpBpp)
                  S_BpBpp tau_dil (hmax S_BpBpp tau_mid) Htau_dil_sup).
                move=> v [sigma [Psigma_den Hv]].
                have eqSig_big :
                    ((S_ApApp :|: S_BpBpp) :&: S_BpBpp) = S_BpBpp
                  by setdec.
                pose sigmaT : 'F[H]_S_BpBpp :=
                  castlf (eqSig_big, eqSig_big) sigma.
                have PsigmaT_den : sigmaT \is den1lf.
                { apply/den1lfP; split.
                  - exact: castlf_psdlf (den1lf_psd Psigma_den).
                  - by rewrite /sigmaT castlf_trlfE
                      (den1lf_trlf Psigma_den). }
                have eqSig_mid2 :
                    ((A' :|: S_BpBpp) :&: S_BpBpp) = S_BpBpp
                  by setdec.
                pose sigma_mid : 'F[H]_((A' :|: S_BpBpp) :&: S_BpBpp) :=
                  castlf (esym eqSig_mid2, esym eqSig_mid2) sigmaT.
                have Psigma_mid_den : sigma_mid \is den1lf.
                { apply/den1lfP; split.
                  - exact: castlf_psdlf (den1lf_psd PsigmaT_den).
                  - by rewrite /sigma_mid castlf_trlfE
                      (den1lf_trlf PsigmaT_den). }
                have eqST_big :
                    ((S_ApApp :|: S_BpBpp) :\: S_BpBpp) :|:
                    ((S_ApApp :|: S_BpBpp) :&: S_BpBpp) =
                    S_ApApp :|: S_BpBpp
                  by rewrite finset.setUC finset.setID.
                pose target_big : 'F[H]_(S_ApApp :|: S_BpBpp) :=
                  castlf (eqST_big, eqST_big)
                    ((((dim 'H[H]_((S_ApApp :|: S_BpBpp) :\: S_BpBpp))%:R^-1)%:C *:
                      ((\1 : 'F[H]_((S_ApApp :|: S_BpBpp) :\: S_BpBpp))
                        \O sigma))).
                have Hv_big :
                    elog2
                      ((dim 'H[H]_((S_ApApp :|: S_BpBpp) :\: S_BpBpp))%:R *
                        (gfid tau_dil target_big) ^+ 2) = v%:E.
                { move: Hv.
                  rewrite /target_big.
                  set e := (X in castlf (X, X) _).
                  by rewrite (eq_irrelevance e eqST_big). }
                have eqST_mid2 :
                    ((A' :|: S_BpBpp) :\: S_BpBpp) :|:
                    ((A' :|: S_BpBpp) :&: S_BpBpp) =
                    A' :|: S_BpBpp
                  by rewrite finset.setUC finset.setID.
                pose target_mid2 : 'F[H]_(A' :|: S_BpBpp) :=
                  castlf (eqST_mid2, eqST_mid2)
                    ((((dim 'H[H]_((A' :|: S_BpBpp) :\: S_BpBpp))%:R^-1)%:C *:
                      ((\1 : 'F[H]_((A' :|: S_BpBpp) :\: S_BpBpp))
                        \O sigma_mid))).
                have Ptarget_big : target_big \is psdlf.
                {
                  rewrite /target_big; apply: castlf_psdlf.
                  apply: psdlfZ; first by rewrite lecR invr_ge0 ler0n.
                  have disBig :
                      [disjoint (S_ApApp :|: S_BpBpp) :\: S_BpBpp
                         & (S_ApApp :|: S_BpBpp) :&: S_BpBpp]
                    by setdec.
                  have -> :
                      ((\1 : 'F[H]_((S_ApApp :|: S_BpBpp) :\: S_BpBpp))
                        \O sigma
                       : 'F[H]_(((S_ApApp :|: S_BpBpp) :\: S_BpBpp) :|:
                         ((S_ApApp :|: S_BpBpp) :&: S_BpBpp))) =
                      ((\1 : 'F[H]_((S_ApApp :|: S_BpBpp) :\: S_BpBpp))
                        \⊗ sigma).
                  { by apply: to_Fnd_inj; rewrite (sdotFT _ _ disBig)
                      to_Fnd_tenE. }
                  rewrite psdlfE.
                  apply: tenf_ge0; first exact: disBig.
                  - by rewrite -psdlfE qualifE h2mx1; exact: psdmx1.
                  - by rewrite -psdlfE; exact: den1lf_psd Psigma_den.
                }
                have Ptarget_mid2 : target_mid2 \is psdlf.
                {
                  rewrite /target_mid2; apply: castlf_psdlf.
                  apply: psdlfZ; first by rewrite lecR invr_ge0 ler0n.
                  have disMid2 :
                      [disjoint (A' :|: S_BpBpp) :\: S_BpBpp
                         & (A' :|: S_BpBpp) :&: S_BpBpp]
                    by setdec.
                  have -> :
                      ((\1 : 'F[H]_((A' :|: S_BpBpp) :\: S_BpBpp))
                        \O sigma_mid
                       : 'F[H]_(((A' :|: S_BpBpp) :\: S_BpBpp) :|:
                         ((A' :|: S_BpBpp) :&: S_BpBpp))) =
                      ((\1 : 'F[H]_((A' :|: S_BpBpp) :\: S_BpBpp))
                        \⊗ sigma_mid).
                  { by apply: to_Fnd_inj; rewrite (sdotFT _ _ disMid2)
                      to_Fnd_tenE. }
                  rewrite psdlfE.
                  apply: tenf_ge0; first exact: disMid2.
                  - by rewrite -psdlfE qualifE h2mx1; exact: psdmx1.
                  - by rewrite -psdlfE; exact: den1lf_psd Psigma_mid_den.
                }
                have Htarget_big_simpl :
                    target_big =
                    ((((dim 'H[H]_S_ApApp)%:R^-1)%:C *:
                      ((\1 : 'F[H]_S_ApApp) \O sigmaT))).
                {
                  have eqA_big :
                      (S_ApApp :|: S_BpBpp) :\: S_BpBpp = S_ApApp
                    by exact: setDU_r disApApp_BpBpp.
                  have eqU1 :
                      (S_ApApp :|: S_BpBpp) :\: S_BpBpp :|:
                        (S_ApApp :|: S_BpBpp) :&: S_BpBpp =
                      S_ApApp :|:
                        (S_ApApp :|: S_BpBpp) :&: S_BpBpp
                    by rewrite eqA_big.
                  have eqU2 :
                      S_ApApp :|:
                        (S_ApApp :|: S_BpBpp) :&: S_BpBpp =
                      S_ApApp :|: S_BpBpp
                    by rewrite eqSig_big.
                  have Hbig_lift :
                      castlf (eqST_big, eqST_big)
                        ((\1 : 'F[H]_((S_ApApp :|: S_BpBpp) :\: S_BpBpp))
                          \O sigma) =
                      ((\1 : 'F[H]_S_ApApp) \O sigmaT
                        : 'F[H]_(S_ApApp :|: S_BpBpp)).
                  {
                    transitivity
                      (castlf (etrans eqU1 eqU2, etrans eqU1 eqU2)
                        ((\1 : 'F[H]_((S_ApApp :|: S_BpBpp) :\: S_BpBpp))
                          \O sigma)).
                    { by rewrite (eq_irrelevance (etrans eqU1 eqU2)
                        eqST_big). }
                    rewrite -(castlf_comp eqU1 eqU1 eqU2 eqU2).
                    rewrite (sdotIf_cast_l eqA_big eqU1) castlf1.
                    rewrite (sdotIf_cast_r eqSig_big eqU2).
                    by rewrite /sigmaT.
                  }
                  by rewrite /target_big linearZ /= Hbig_lift eqA_big.
                }
                have Htarget_mid2_simpl :
                    target_mid2 =
                    ((((dim 'H[H]_A')%:R^-1)%:C *:
                      ((\1 : 'F[H]_A') \O sigmaT))).
                {
                  have eqA_mid2 :
                      (A' :|: S_BpBpp) :\: S_BpBpp = A'
                    by exact: setDU_r disA'_BpBpp.
                  have eqU1 :
                      (A' :|: S_BpBpp) :\: S_BpBpp :|:
                        (A' :|: S_BpBpp) :&: S_BpBpp =
                      A' :|: (A' :|: S_BpBpp) :&: S_BpBpp
                    by rewrite eqA_mid2.
                  have eqU2 :
                      A' :|: (A' :|: S_BpBpp) :&: S_BpBpp =
                      A' :|: S_BpBpp
                    by rewrite eqSig_mid2.
                  have Hmid2_lift :
                      castlf (eqST_mid2, eqST_mid2)
                        ((\1 : 'F[H]_((A' :|: S_BpBpp) :\: S_BpBpp))
                          \O sigma_mid) =
                      ((\1 : 'F[H]_A') \O sigmaT
                        : 'F[H]_(A' :|: S_BpBpp)).
                  {
                    transitivity
                      (castlf (etrans eqU1 eqU2, etrans eqU1 eqU2)
                        ((\1 : 'F[H]_((A' :|: S_BpBpp) :\: S_BpBpp))
                          \O sigma_mid)).
                    { by rewrite (eq_irrelevance (etrans eqU1 eqU2)
                        eqST_mid2). }
                    rewrite -(castlf_comp eqU1 eqU1 eqU2 eqU2).
                    rewrite (sdotIf_cast_l eqA_mid2 eqU1) castlf1.
                    rewrite (sdotIf_cast_r eqSig_mid2 eqU2).
                    rewrite /sigma_mid castlf_comp.
                    rewrite (eq_irrelevance
                      (etrans (esym eqSig_mid2) eqSig_mid2) (erefl _)).
                    by rewrite castlf_id.
                  }
                  by rewrite /target_mid2 linearZ /= Hmid2_lift eqA_mid2.
                }
                pose arg_big :=
                  (dim 'H[H]_((S_ApApp :|: S_BpBpp) :\: S_BpBpp))%:R *
                  (gfid tau_dil target_big) ^+ 2.
                pose arg_mid2 :=
                  (dim 'H[H]_((A' :|: S_BpBpp) :\: S_BpBpp))%:R *
                  (gfid tau_mid target_mid2) ^+ 2.
                have Harg_big_pos : 0 < arg_big.
                { case: (ltP 0 arg_big) => // Harg_le0.
                  move: Hv_big; rewrite /arg_big (elog2_le0 Harg_le0).
                  by discriminate. }
                have Hv_eq : v = log2 arg_big.
                { move: Hv_big; rewrite /arg_big (elog2_gt0 Harg_big_pos).
                  by case. }
                have Harg_project_le : arg_big <= arg_mid2.
                {
                  rewrite /arg_big /arg_mid2.
                  rewrite (setDU_r disApApp_BpBpp)
                    (setDU_r disA'_BpBpp).
                  rewrite Htarget_big_simpl Htarget_mid2_simpl.
                  pose cApp : R := ((dim 'H[H]_App)%:R)^-1%R.
                  have Hgf_big_ge0 :
                      0 <= gfid tau_dil
                        (((dim 'H[H]_S_ApApp)%:R^-1)%:C *:
                          ((\1 : 'F[H]_S_ApApp) \O sigmaT)).
                  { rewrite /gfid.
                    have Psimp : (((dim 'H[H]_S_ApApp)%:R^-1)%:C *:
                        ((\1 : 'F[H]_S_ApApp) \O sigmaT)) \is psdlf
                      by rewrite -Htarget_big_simpl.
                    exact: gfid_ge0_mx (psdlf_h2mx Ptau_dil)
                      (psdlf_h2mx Psimp). }
                  have Hgf_mid_ge0 :
                      0 <= gfid tau_mid
                        (((dim 'H[H]_A')%:R^-1)%:C *:
                          ((\1 : 'F[H]_A') \O sigmaT)).
                  { rewrite /gfid.
                    have Psimp : (((dim 'H[H]_A')%:R^-1)%:C *:
                        ((\1 : 'F[H]_A') \O sigmaT)) \is psdlf
                      by rewrite -Htarget_mid2_simpl.
                    exact: gfid_ge0_mx (psdlf_h2mx Ptau_mid)
                      (psdlf_h2mx Psimp). }
                  have HcApp_ge0 : 0 <= cApp
                    by rewrite /cApp invr_ge0 ler0n.
                  have Hgf_le_scaled :
                      gfid tau_dil
                        (((dim 'H[H]_S_ApApp)%:R^-1)%:C *:
                          ((\1 : 'F[H]_S_ApApp) \O sigmaT)) <=
                      Num.sqrt cApp *
                      gfid tau_mid
                        (((dim 'H[H]_A')%:R^-1)%:C *:
                          ((\1 : 'F[H]_A') \O sigmaT)).
                  {
                    pose Xbig_lf : 'F[H]_(S_ApApp :|: S_BpBpp) :=
                      (((dim 'H[H]_S_ApApp)%:R^-1)%:C *:
                        ((\1 : 'F[H]_S_ApApp) \O sigmaT)).
                    pose Xmid_lf : 'F[H]_(A' :|: S_BpBpp) :=
                      (((dim 'H[H]_A')%:R^-1)%:C *:
                        ((\1 : 'F[H]_A') \O sigmaT)).
                    pose Xproj_lf : 'F[H]_(S_ApApp :|: S_BpBpp) :=
                      Pfull \o Xbig_lf \o Pfull.
                    have Ptau_raw : tau_raw \is psdlf.
                    { rewrite /tau_raw. exact: castlf_psdlf Ptau_ext. }
                    have PXbig : Xbig_lf \is psdlf.
                    { by rewrite /Xbig_lf -Htarget_big_simpl. }
                    have PXmid : Xmid_lf \is psdlf.
                    { by rewrite /Xmid_lf -Htarget_mid2_simpl. }
                    have HPfull_proj_local : Pfull \is projlf.
                    {
                      move: HPA_proj_local => /projlfP [HPAh HPAid].
                      have HPfull_eq_local :
                          Pfull =
                          (PA \⊗ (\1 : 'F[H]_S_BpBpp)
                            : 'F[H]_(S_ApApp :|: S_BpBpp)).
                      { apply: to_Fnd_inj.
                        by rewrite /Pfull (sdotFT _ _ disApApp_BpBpp)
                          to_Fnd_tenE. }
                      apply/projlfP; split.
                      - by rewrite HPfull_eq_local tenf_adj HPAh adjf1
                          -HPfull_eq_local.
                      - by rewrite HPfull_eq_local -tenf_comp ?HPAid
                          ?comp_lfun1l ?comp_lfun1r -?HPfull_eq_local.
                    }
                    have HPfull_herm_local : Pfull^A = Pfull
                      := hermlf_adjE (projlf_herm HPfull_proj_local).
                    have PXproj : Xproj_lf \is psdlf.
                    {
                      rewrite /Xproj_lf -[Pfull in _ \o _ \o Pfull]HPfull_herm_local.
                      apply/psdlfP=> x.
                      rewrite !comp_lfunE /= -adj_dotEl.
                      by move/psdlfP: PXbig.
                    }
                    have HXbig_tr1 : \Tr Xbig_lf = 1.
                    {
                      rewrite /Xbig_lf linearZ /= (trlf_lift_I disApApp_BpBpp).
                      rewrite (den1lf_trlf PsigmaT_den).
                      rewrite -natrC -rmorphM /=.
                      rewrite mulr1 -rmorphM /=.
                      have Hdim_neq0 :
                          ((dim 'H[H]_S_ApApp)%:R : R) != 0
                        by rewrite lt0r_neq0 ?ltr0n ?dim_proper.
                      by rewrite (mulVf Hdim_neq0) rmorph1.
                    }
                    have HXmid_tr1 : \Tr Xmid_lf = 1.
                    {
                      rewrite /Xmid_lf linearZ /= (trlf_lift_I disA'_BpBpp).
                      rewrite (den1lf_trlf PsigmaT_den).
                      rewrite -natrC -rmorphM /=.
                      rewrite mulr1 -rmorphM /=.
                      have Hdim_neq0 :
                          ((dim 'H[H]_A')%:R : R) != 0
                        by rewrite lt0r_neq0 ?ltr0n ?dim_proper.
                      by rewrite (mulVf Hdim_neq0) rmorph1.
                    }
                    have HPfull_mx_proj : h2mx Pfull \is projmx.
                    {
                      apply/projmxP_id; split.
                      - apply/hermmxP.
                        by rewrite -h2mx_adj HPfull_herm_local.
                      - move: HPfull_proj_local => /projlfP [_ HPid].
                        move/(congr1 h2mx): HPid.
                        by rewrite h2mx_comp.
                    }
                    have Htau_dil_mx_def :
                        h2mx tau_dil =
                        h2mx Pfull *m h2mx tau_raw *m h2mx Pfull.
                    { by rewrite /tau_dil !h2mx_comp. }
                    have HXproj_mx_def :
                        h2mx Xproj_lf =
                        h2mx Pfull *m h2mx Xbig_lf *m h2mx Pfull.
                    {
                      rewrite /Xproj_lf.
                      rewrite h2mx_comp.
                      congr (_ *m h2mx Pfull).
                      by rewrite h2mx_comp.
                    }
                    have Hgf_big_eq :
                        gfid tau_dil Xbig_lf =
                        @complex.Re R
                          (trnorm (sqrtmx (h2mx tau_raw) *m
                            sqrtmx (h2mx Xproj_lf))).
                    {
                      rewrite /gfid.
                      have Ptau_dil_mx := psdlf_h2mx Ptau_dil.
                      have PXbig_mx := psdlf_h2mx PXbig.
                      have Ptau_raw_mx := psdlf_h2mx Ptau_raw.
                      rewrite (gfid_sym_mx Ptau_dil_mx PXbig_mx).
                      rewrite (gfid_eq_fid_tr1_mx PXbig_mx Ptau_dil_mx
                        HXbig_tr1 Htau_dil_tr).
                      rewrite (fid_i_sym_mx PXbig_mx Ptau_dil_mx).
                      have [Hproj_l Hproj_r] :=
                        fid_iv_proj_mx HPfull_mx_proj Ptau_raw_mx PXbig_mx.
                      rewrite Htau_dil_mx_def.
                      rewrite -HXproj_mx_def in Hproj_l Hproj_r.
                      exact: (eq_trans Hproj_l Hproj_r).
                    }
                    have disApp_BpBpp : [disjoint App & S_BpBpp].
                    { by rewrite /S_BpBpp disjointXU disAppB' disAppBpp. }
                    have Htau_raw_mid :
                        ptrace_cast3B disA'App disApp_BpBpp tau_raw = tau_mid.
                    {
                      rewrite /tau_mid /tau_raw /ptrace_cast3B
                        /ptrace_cast /ptrace_cast_gen.
                      have eq_res_raw :
                          (S_ApApp :|: S_BpBpp) :\: App =
                          ((A' :|: B') :|: (App :|: Bpp)) :\: App
                        by rewrite eq_dil.
                      have eq_res_mid :
                          ((A' :|: B') :|: (App :|: Bpp)) :\: App =
                          ((A' :|: S_BpBpp) :|: App) :\: App
                        by rewrite eq_ext_App.
                      rewrite (ptracelf_castlf_eq (esym eq_dil)
                        (esym eq_res_raw)).
                      rewrite (ptracelf_castlf_eq eq_ext_App eq_res_mid).
                      rewrite !castlf_comp.
                      by congr (castlf (_, _) _); exact: eq_irrelevance.
                    }
                    have HXproj_mid_le :
                        ptrace_cast3B disA'App disApp_BpBpp Xproj_lf <=
                        cApp%:C *: Xmid_lf.
                    {
                      have HPAid : PA \o PA = PA.
                      { by move/projlfP: HPA_proj_local => [_]. }
                      have Hscale_sand (c : C)
                          (x p : 'F[H]_(S_ApApp :|: S_BpBpp)) :
                          p \o (c *: x) \o p =
                          c *: (p \o x \o p).
                      { by rewrite comp_lfunZl comp_lfunZr. }
                      have HXproj_simpl :
                          Xproj_lf =
                          (((dim 'H[H]_S_ApApp)%:R^-1)%:C *:
                            (PA \O sigmaT)).
                      {
                        rewrite /Xproj_lf /Xbig_lf /Pfull.
                        rewrite Hscale_sand.
                        congr (_ *: _).
                        rewrite (sdotF_to_tenF disApApp_BpBpp PA
                          (\1 : 'F[H]_S_BpBpp)).
                        rewrite (sdotF_to_tenF disApApp_BpBpp
                          (\1 : 'F[H]_S_ApApp) sigmaT).
                        rewrite -!tenf_comp ?disApApp_BpBpp //.
                        rewrite !comp_lfun1l !comp_lfun1r.
                        rewrite HPAid.
                        by rewrite -(sdotF_to_tenF disApApp_BpBpp PA
                          sigmaT).
                      }
                      have Hptr3B_Z (c : C)
                          (z : 'F[H]_(S_ApApp :|: S_BpBpp)) :
                          ptrace_cast3B disA'App disApp_BpBpp (c *: z) =
                          c *: ptrace_cast3B disA'App disApp_BpBpp z.
                      { rewrite /ptrace_cast3B /ptrace_cast_gen.
                        have HtrZ : \Tr_(App) (c *: z) = c *: \Tr_(App) z
                          by exact: linearZ.
                        rewrite HtrZ.
                        exact: linearZ. }
                      have Hptr_Xproj :
                          ptrace_cast3B disA'App disApp_BpBpp Xproj_lf =
                          (((dim 'H[H]_S_ApApp)%:R^-1)%:C *:
                            ((ptrace_cast disA'App PA) \O sigmaT)).
                      {
                        rewrite HXproj_simpl Hptr3B_Z.
                        by rewrite (ptrace_cast3B_sdot_mid disA'App
                          disApp_BpBpp disA'_BpBpp).
                      }
                      have Hlift_le :
                          ((ptrace_cast disA'App PA) \O sigmaT
                            : 'F[H]_(A' :|: S_BpBpp)) <=
                          ((\1 : 'F[H]_A') \O sigmaT).
                      {
                        rewrite !(sdotF_to_tenF disA'_BpBpp).
                        apply: (lef_tenfl disA'_BpBpp).
                        - exact: psdlf_ge0 (den1lf_psd PsigmaT_den).
                        - exact: HPA_ptr_le.
                      }
                      have HcoefR :
                          cApp * (((dim 'H[H]_A')%:R : R)^-1)%R =
                          (((dim 'H[H]_S_ApApp)%:R : R)^-1)%R.
                      {
                        rewrite /cApp (tenv_dim disA'App) natrM.
                        have HA_neq0 : ((dim 'H[H]_A')%:R : R) != 0
                          by rewrite lt0r_neq0 ?ltr0n ?dim_proper.
                        have HApp_neq0 : ((dim 'H[H]_App)%:R : R) != 0
                          by rewrite lt0r_neq0 ?ltr0n ?dim_proper.
                        rewrite invrM.
                        - by rewrite mulrC.
                        - by rewrite unitfE HA_neq0.
                        - by rewrite unitfE HApp_neq0.
                      }
                      have Hcoef :
                          cApp%:C *
                            ((((dim 'H[H]_A')%:R : R)^-1)%R)%:C =
                          ((((dim 'H[H]_S_ApApp)%:R : R)^-1)%R)%:C
                        by rewrite -rmorphM HcoefR.
                      have Halpha_posC :
                          0 < (((dim 'H[H]_S_ApApp)%:R^-1)%:C : C)
                        by rewrite ltc0R invr_gt0 ltr0n dim_proper.
                      rewrite Hptr_Xproj /Xmid_lf scalerA Hcoef.
                      exact: lef_pscale2lP Halpha_posC Hlift_le.
                    }
                    have Hfid_mid :
                        @complex.Re R
                          (trnorm (sqrtmx (h2mx tau_raw) *m
                            sqrtmx (h2mx Xproj_lf))) <=
                        @complex.Re R
                          (trnorm (sqrtmx (h2mx tau_mid) *m
                            sqrtmx (h2mx (ptrace_cast3B disA'App
                              disApp_BpBpp Xproj_lf)))).
                    {
                      set eqS := setUC_swap3 A' App S_BpBpp
                        : S_ApApp :|: S_BpBpp =
                          A' :|: S_BpBpp :|: App.
                      pose tau_rawR := castlf (eqS, eqS) tau_raw.
                      pose XprojR := castlf (eqS, eqS) Xproj_lf.
                      have Ptau_rawR : tau_rawR \is psdlf
                        by rewrite /tau_rawR; exact: castlf_psdlf Ptau_raw.
                      have PXprojR : XprojR \is psdlf
                        by rewrite /XprojR; exact: castlf_psdlf PXproj.
                      have Hptr3B_recast
                          (z : 'F[H]_(S_ApApp :|: S_BpBpp)) :
                          ptrace_cast3B disA'App disApp_BpBpp z =
                          ptrace_cast disA'BpBpp_App
                            (castlf (eqS, eqS) z).
                      {
                        rewrite /ptrace_cast3B /ptrace_cast
                          /ptrace_cast_gen.
                        have eq_res :
                            (S_ApApp :|: S_BpBpp) :\: App =
                            (A' :|: S_BpBpp :|: App) :\: App
                          by rewrite eqS.
                        rewrite (ptracelf_castlf_eq eqS eq_res).
                        rewrite castlf_comp.
                        by congr (castlf (_, _) _); exact: eq_irrelevance.
                      }
                      have HtauR_ptr :
                          ptrace_cast disA'BpBpp_App tau_rawR = tau_mid
                        by rewrite /tau_rawR -Hptr3B_recast Htau_raw_mid.
                      have HXprojR_ptr :
                          ptrace_cast disA'BpBpp_App XprojR =
                          ptrace_cast3B disA'App disApp_BpBpp Xproj_lf
                        by rewrite /XprojR -Hptr3B_recast.
                      have Hfid_cast_gen (S T : {set L}) (eqST : S = T)
                          (x y : 'F[H]_S) :
                          fidelity (castlf (eqST, eqST) x)
                            (castlf (eqST, eqST) y) = fidelity x y.
                      { by case: _ / eqST in x y *; rewrite !castlf_id. }
                      have Hfid_cast :
                          fidelity tau_rawR XprojR =
                          fidelity tau_raw Xproj_lf.
                      { exact: Hfid_cast_gen eqS tau_raw Xproj_lf. }
                      have Hmono :=
                        @fid_ptr_mono R L H (A' :|: S_BpBpp) App
                          disA'BpBpp_App tau_rawR XprojR
                          Ptau_rawR PXprojR dim_proper.
                      rewrite Hfid_cast HtauR_ptr HXprojR_ptr in Hmono.
                      have HfidE (S : {set L}) (x y : 'F[H]_S) :
                          fidelity x y =
                          @complex.Re R
                            (trnorm (sqrtmx (h2mx x) *m
                              sqrtmx (h2mx y))).
                      { by rewrite /fidelity h2mx_comp !sqrtH_h2mx. }
                      rewrite -(@HfidE (S_ApApp :|: S_BpBpp) tau_raw
                        Xproj_lf).
                      rewrite -(@HfidE (A' :|: S_BpBpp) tau_mid
                        (ptrace_cast3B disA'App disApp_BpBpp Xproj_lf)).
                      exact: Hmono.
                    }
                    have Hfid_order :
                        @complex.Re R
                          (trnorm (sqrtmx (h2mx tau_mid) *m
                            sqrtmx (h2mx (ptrace_cast3B disA'App
                              disApp_BpBpp Xproj_lf)))) <=
                        @complex.Re R
                          (trnorm (sqrtmx (h2mx tau_mid) *m
                            sqrtmx (h2mx (cApp%:C *: Xmid_lf)))).
                    {
                      have PXproj_mid : ptrace_cast3B disA'App
                          disApp_BpBpp Xproj_lf \is psdlf.
                      { rewrite /ptrace_cast3B.
                        exact: ptrace_cast_gen_psdlf PXproj. }
                      have PcXmid : (cApp%:C *: Xmid_lf) \is psdlf.
                      { apply: psdlfZ; first by rewrite lecE /= eqxx HcApp_ge0.
                        exact: PXmid. }
                      apply: fid_v_mono_r_psd_mx.
                      - exact: psdlf_h2mx Ptau_mid.
                      - exact: psdlf_h2mx PXproj_mid.
                      - exact: psdlf_h2mx PcXmid.
                      - by move: HXproj_mid_le; rewrite lef_h2mx h2mxZ_lf.
                    }
                    have Hfid_scaled :
                        @complex.Re R
                          (trnorm (sqrtmx (h2mx tau_mid) *m
                            sqrtmx (h2mx (cApp%:C *: Xmid_lf)))) =
                        Num.sqrt cApp *
                        @complex.Re R
                          (trnorm (sqrtmx (h2mx tau_mid) *m
                            sqrtmx (h2mx Xmid_lf))).
                    {
                      rewrite h2mxZ_lf /= (sqrtmxZ_nn HcApp_ge0
                        (psdlf_h2mx PXmid)).
                      rewrite -scalemxAr trnormZ.
                      have Hsqrt_ge0 : (0 : C) <= (Num.sqrt cApp)%:C
                        by rewrite lecE /= eqxx sqrtr_ge0.
                      rewrite (ger0_norm Hsqrt_ge0).
                      have HReM : forall z : C,
                          @complex.Re R ((Num.sqrt cApp)%:C * z) =
                          Num.sqrt cApp * @complex.Re R z.
                      { move=> [a b] /=. by rewrite mul0r subr0. }
                      by rewrite HReM.
                    }
                    have Hgf_mid_eq :
                        gfid tau_mid Xmid_lf =
                        @complex.Re R
                          (trnorm (sqrtmx (h2mx tau_mid) *m
                            sqrtmx (h2mx Xmid_lf))).
                    {
                      rewrite /gfid.
                      have Ptau_mid_mx := psdlf_h2mx Ptau_mid.
                      have PXmid_mx := psdlf_h2mx PXmid.
                      rewrite (gfid_sym_mx Ptau_mid_mx PXmid_mx).
                      rewrite (gfid_eq_fid_tr1_mx PXmid_mx Ptau_mid_mx
                        HXmid_tr1 Htau_mid_tr).
                      by rewrite (fid_i_sym_mx PXmid_mx Ptau_mid_mx).
                    }
                    rewrite -/Xbig_lf -/Xmid_lf.
                    rewrite Hgf_big_eq Hgf_mid_eq.
                    apply: (le_trans Hfid_mid).
                    apply: (le_trans Hfid_order).
                    by rewrite Hfid_scaled.
                  }
                  have Hrhs_ge0 :
                      0 <= Num.sqrt cApp *
                        gfid tau_mid
                          (((dim 'H[H]_A')%:R^-1)%:C *:
                            ((\1 : 'F[H]_A') \O sigmaT))
                    by apply: mulr_ge0; [exact: sqrtr_ge0 | exact: Hgf_mid_ge0].
                  have Hsq_le :
                      (gfid tau_dil
                        (((dim 'H[H]_S_ApApp)%:R^-1)%:C *:
                          ((\1 : 'F[H]_S_ApApp) \O sigmaT))) ^+ 2 <=
                      cApp *
                      (gfid tau_mid
                        (((dim 'H[H]_A')%:R^-1)%:C *:
                          ((\1 : 'F[H]_A') \O sigmaT))) ^+ 2.
                  {
                    have Hsq := lerXn2r 2 Hgf_big_ge0 Hrhs_ge0
                      Hgf_le_scaled.
                    move: Hsq.
                    by rewrite exprMn sqr_sqrtr ?HcApp_ge0.
                  }
                  apply: (@le_trans _ _
                    ((dim 'H[H]_S_ApApp)%:R *
                      (cApp *
                      (gfid tau_mid
                        (((dim 'H[H]_A')%:R^-1)%:C *:
                          ((\1 : 'F[H]_A') \O sigmaT))) ^+ 2))).
                  - apply: ler_wpM2l; first by rewrite ler0n.
                    exact: Hsq_le.
                  - rewrite /cApp (tenv_dim disA'App) natrM.
                    rewrite [X in X <= _]mulrA.
                    have Hcancel :
                        (dim 'H[H]_A')%:R * (dim 'H[H]_App)%:R *
                          ((dim 'H[H]_App)%:R)^-1 =
                        (dim 'H[H]_A')%:R :> R.
                    {
                      rewrite -mulrA.
                      rewrite mulfV ?mulr1 //.
                      by rewrite lt0r_neq0 ?ltr0n ?dim_proper.
                    }
                    by rewrite Hcancel.
                }
                have Harg_mid2_pos : 0 < arg_mid2 :=
                  lt_le_trans Harg_big_pos Harg_project_le.
                pose w := log2 arg_mid2.
                have Hw_feas : hmax_feasible S_BpBpp tau_mid w.
                {
                  exists sigma_mid; split; first exact: Psigma_mid_den.
                  rewrite /w /arg_mid2 /target_mid2.
                  set e := (X in castlf (X, X) _).
                  rewrite (eq_irrelevance e eqST_mid2).
                  by rewrite (elog2_gt0 Harg_mid2_pos).
                }
                rewrite Hv_eq /w.
                exact: le_trans (log2_le_pos Harg_big_pos Harg_project_le)
                  (@hmax_ub R L H (A' :|: S_BpBpp) S_BpBpp tau_mid w
                    Htau_mid_sup Hw_feas).
              }
              move: Hproj_hmax_le.
              rewrite (hmax_labelled_product_mx disApApp_BpBpp Ptau_dil).
              rewrite (hmax_labelled_product_mx disA'_BpBpp Ptau_mid).
              move=> Hproj_mx_le.
              exact: le_trans Hproj_mx_le Hmid_mx_le.
            }
            exact: Hhmax_mx_le.
        }
        case: Hlift_output => tau_dil [Htau_dil_ball Htau_dil_hmax].
        have Hsmooth_dil_le :
            (smooth_hmaxE S_BpBpp eps rho_dil <=
             hmaxE S_BpBpp tau_dil)%E.
        {
          rewrite /smooth_hmaxE leeNl.
          apply: ereal_sup_ubound.
          by exists tau_dil.
        }
        rewrite -Hiso.
        change (smooth_hmaxE S_BpBpp eps rho_dil <=
          hmaxE B' tauA'B'0)%E.
        exact: le_trans Hsmooth_dil_le Htau_dil_hmax.
        - have Hbad : eps < eps := lt_le_trans Heps_src_lt Heps_lt.
          by move: Hbad; rewrite ltxx.
    }
    rewrite /smooth_hmaxE leeN2.
    apply: ge_ereal_sup => v [tauA'B'0 [HtauA'B'_ball ->]].
    have Hbound := Hmax_bound tauA'B'0 HtauA'B'_ball.
    move: Hbound.
    rewrite /smooth_hmaxE -[hmaxE B' tauA'B'0]oppeK leeN2 oppeK.
    exact.
Qed.

End TomamichelDataProcTex.

End FvqkdReal.
