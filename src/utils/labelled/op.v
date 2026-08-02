(* -------------------------------------------------------------------- *)
(* op.v — Ambient set-labelled operator utilities and matrix bridges    *)
(* -------------------------------------------------------------------- *)
(* Module: utils.labelled.op                              *)
(* TeX source: none (library utility)                                    *)
(* TeX labels: none                                                      *)
(* -------------------------------------------------------------------- *)
(* Owns lfun utilities whose checked public surface is ambient labelled  *)
(* (`L : finType`, `H : L -> chsType`, `S : {set L}`).                   *)
(* Labeled-system ptrace/cast infrastructure lives in labelled/sys.v.    *)
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
From quantum.dirac Require Import hstensor.

Import Order.TTheory GRing.Theory Num.Theory Num.Def MxLownerOrder.
Import VectorInternalTheory.

(* --- FVQKD imports --- *)
From utils Require Import arith.
From utils.mx Require Import def prop.
From utils.labelled Require Export def prop.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Open Scope ring_scope.
Local Open Scope lfun_scope.

Section FvqkdReal.
Variable R : realType.
Notation C := (@hermitian.C R).
Notation chsType := (@chsType R).

(* krausso_outp_onbE *)
(* infra: no tex label — generalized preparation/discard channel action. *)
(* path: utils:krausso_outp_onbE -> utils:sqrtH_herm -> lhl:min_coll_bound -> *)
(*   bb84:privacy_amplification -> bb84:bb84_secret *)
Lemma krausso_outp_onbE (U V : chsType) (F : finType)
    (onb : 'ONB(F; U)) (v : V) (x : 'End(U)) :
  krausso (fun i => [> v ; onb i <]) x = \Tr x *: [> v ; v <].
Proof.
  rewrite kraussoE (onb_trlf onb x) /= scaler_suml.
  by apply: eq_bigr => i _; rewrite adj_outp -comp_lfunA outp_compr outp_comp.
Qed.

(* psdlf_h2mx *)
(* infra: no tex label — fundamental & reusable psdlf/psdmx bridge *)
(* path: utils:psdlf_h2mx -> entropy:entropy_data_proc -> *)
(*   bb84:bb84_secret *)
Lemma psdlf_h2mx (L : finType) (H : L -> chsType) (S : {set L}) (A : 'F[H]_S) :
  A \is psdlf -> h2mx A \is psdmx.
Proof.
  by rewrite qualifE.
Qed.

(* dephaseH_cptp *)
(* infra: no tex label — projective dephasing is CPTP *)
(* path: utils:dephaseH_cptp -> utils:psdlf_h2mx -> entropy:entropy_data_proc -> *)
(*   bb84:bb84_secret *)
Lemma dephaseH_cptp (L : finType) (H : L -> chsType) (S : {set L}) :
  dephaseH H S \is cptp.
Proof.
  rewrite /dephaseH.
  apply/krausso_qcP.
  rewrite /trace_presv.
  apply/eqP.
  under eq_bigr => x _.
    rewrite adj_outp outp_comp dv_dot eqxx scale1r.
    over.
  exact: sumonb_out.
Qed.

(* basis_channel_cptp *)
(* infra: no tex label — basis channels are CPTP *)
(* path: utils:basis_channel_cptp -> entropy:smooth_hmax_labelled_mx -> *)
(*   bb84:stat -> bb84:bb84_secret *)
Lemma basis_channel_cptp (L : finType) (H : L -> chsType)
    (S T : {set L}) (f : 'Idx[H]_S -> 'Idx[H]_T) :
  @basis_channel R L H S T f \is cptp.
Proof.
  rewrite /basis_channel.
  apply/krausso_qcP.
  rewrite /trace_presv.
  apply/eqP.
  under eq_bigr => x _.
    rewrite adj_outp outp_comp dv_dot eqxx scale1r.
    over.
  exact: sumonb_out.
Qed.

(* ================================================================== *)
(* sqrtH lemmas: spectral bridge + algebra                           *)
(* ================================================================== *)

Section SqrtLfLemmasSet.
Variables (L : finType) (H : L -> chsType) (S : {set L}).

(* sqrtH_h2mx *)
(* infra: no tex label — fundamental & reusable ambient set-labelled utility *)
(* consumer: sqrtH_h2mx is used downstream by the BB84 secrecy proof. *)
(* path: utils:sqrtH_h2mx -> entropy:entropy_data_proc -> *)
(*   bb84:bb84_secret *)
Lemma sqrtH_h2mx (A : 'F[H]_S) :
  h2mx (sqrtH A) = sqrtmx (h2mx A).
Proof.
  rewrite /sqrtH /sqrtmx sumoutpE.
  have Hlin := @h2mxP R ('H[H]_S) ('H[H]_S).
  have Hadd (x y : 'F[H]_S) : h2mx (x + y) = h2mx x + h2mx y.
  { have := Hlin 1 x y.
    by rewrite !scale1r. }
  have Hsum (F : 'I_(dim 'H[H]_S) -> 'F[H]_S) :
      h2mx (\sum_i F i) = \sum_i h2mx (F i).
  { apply: (big_morph h2mx); [exact: Hadd | exact: h2mx0]. }
  have Hscale (c : C) (x : 'F[H]_S) :
      h2mx (c *: x) = c *: h2mx x.
  { have := Hlin c x 0.
    by rewrite addr0 h2mx0 addr0. }
  rewrite Hsum /= mulmx_colrow.
  apply: eq_bigr => i _.
  rewrite col_diag_mul -scalemxAl Hscale /= mxE /eigenval_all /eigenvec_all.
  apply: f_equal.
  rewrite outp.unlock/= mx2hK c2hK.
  by rewrite /eigenmx adj_col adjmxK.
Qed.

End SqrtLfLemmasSet.

Section SqrtLfCoreSet.

(* sqrtH_psd *)
(* infra: no tex label — fundamental & reusable (mathcomp-style) *)
(* consumer: sqrtH_psd is used downstream by the BB84 secrecy proof. *)
(* path: utils:sqrtH_psd -> lhl:min_coll_bound -> *)
(*   bb84:privacy_amplification -> bb84:bb84_secret *)
Lemma sqrtH_psd (L : finType) (HL : L -> chsType) (S : {set L})
    (A : 'F[HL]_S) : A \is psdlf -> sqrtH A \is psdlf.
Proof.
  by rewrite !qualifE sqrtH_h2mx; exact: sqrtmx_psd.
Qed.

(* sqrtHK *)
(* infra: no tex label — fundamental & reusable (mathcomp-style) *)
(* consumer: sqrtHK is used downstream by the BB84 secrecy proof. *)
(* path: utils:sqrtHK -> lhl:min_coll_bound -> *)
(*   bb84:privacy_amplification -> bb84:bb84_secret *)
Lemma sqrtHK (L : finType) (HL : L -> chsType) (S : {set L})
    (A : 'F[HL]_S) : A \is psdlf -> sqrtH A \o sqrtH A = A.
Proof.
  move=> PA; apply/h2mx_inj; rewrite h2mx_comp !sqrtH_h2mx.
  by apply: sqrtmxK; move: PA; rewrite qualifE.
Qed.

(* sqrtH_herm *)
(* infra: no tex label — fundamental & reusable (mathcomp-style) *)
(* consumer: sqrtH_herm is used downstream by the BB84 secrecy proof. *)
(* path: utils:sqrtH_herm -> lhl:min_coll_bound -> *)
(*   bb84:privacy_amplification -> bb84:bb84_secret *)
Lemma sqrtH_herm (L : finType) (HL : L -> chsType) (S : {set L})
    (A : 'F[HL]_S) : A \is hermlf -> sqrtH A \is hermlf.
Proof.
  by rewrite !qualifE sqrtH_h2mx; exact: sqrtmx_herm.
Qed.

End SqrtLfCoreSet.

(* povm_channel_krausE *)
(* infra: no tex label — exact Kraus execution of a labelled POVM
   recording channel.                                                   *)
(* path: utils:povm_channel_krausE -> utils:sqrtH_herm -> *)
(*   lhl:min_coll_bound -> bb84:privacy_amplification -> *)
(*   bb84:bb84_secret *)
Lemma povm_channel_krausE (L : finType) (H : L -> chsType)
    (I : finType) (S T : {set L})
    (out : I -> 'Idx[H]_T) (M : I -> 'F[H]_S)
    (rho : 'F[H]_S) :
  @povm_channel R L H I S T out M rho =
  \sum_(p : I * 'Idx[H]_S)
    (([> deltav (out p.1) ; deltav p.2 <] \o sqrtH (M p.1)) \o
      rho \o
      ([> deltav (out p.1) ; deltav p.2 <] \o sqrtH (M p.1))^A).
Proof.
  by rewrite /povm_channel kraussoE.
Qed.

(* povm_channel_pairE *)
(* infra: no tex label — outcome/basis-index expansion of
   povm_channel_krausE.                                                  *)
(* path: utils:povm_channel_pairE -> utils:sqrtH_herm -> lhl:min_coll_bound -> *)
(*   bb84:privacy_amplification -> bb84:bb84_secret *)
Lemma povm_channel_pairE (L : finType) (H : L -> chsType)
    (I : finType) (S T : {set L})
    (out : I -> 'Idx[H]_T) (M : I -> 'F[H]_S)
    (rho : 'F[H]_S) :
  @povm_channel R L H I S T out M rho =
  \sum_(i : I) \sum_(x : 'Idx[H]_S)
    (([> deltav (out i) ; deltav x <] \o sqrtH (M i)) \o
      rho \o
      ([> deltav (out i) ; deltav x <] \o sqrtH (M i))^A).
Proof.
  by rewrite povm_channel_krausE pair_bigV.
Qed.

(* povm_channel_bornE *)
(* infra: no tex label — Born-rule diagonal form of a labelled POVM
   recording channel.                                                    *)
(* path: utils:povm_channel_bornE -> utils:sqrtH_herm -> lhl:min_coll_bound -> *)
(*   bb84:privacy_amplification -> bb84:bb84_secret *)
Lemma povm_channel_bornE (L : finType) (H : L -> chsType)
    (I : finType) (S T : {set L})
    (out : I -> 'Idx[H]_T) (M : I -> 'F[H]_S)
    (rho : 'F[H]_S) :
  (forall i, M i \is psdlf) ->
  @povm_channel R L H I S T out M rho =
  \sum_(i : I) \Tr (M i \o rho) *:
    [> deltav (out i) ; deltav (out i) <].
Proof.
  move=> HMpsd.
  rewrite povm_channel_pairE.
  apply: eq_bigr => i _.
  set A := sqrtH (M i).
  have Hblock :
      \sum_(x : 'Idx[H]_S)
        (([> deltav (out i) ; deltav x <] \o A) \o
          rho \o
          ([> deltav (out i) ; deltav x <] \o A)^A) =
      krausso (fun x : 'Idx[H]_S =>
        [> deltav (out i) ; deltav x <]) (A \o rho \o A^A).
  {
    rewrite kraussoE.
    apply: eq_bigr => x _.
    by rewrite adjf_comp !comp_lfunA.
  }
  rewrite Hblock krausso_outp_onbE.
  have Hsqrt_herm : A \is hermlf := sqrtH_herm (psdlf_herm (HMpsd i)).
  have Htrace : \Tr (A \o rho \o A^A) = \Tr (M i \o rho).
  {
    rewrite (hermlf_adjE Hsqrt_herm) lftraceC comp_lfunA.
    by rewrite /A sqrtHK.
  }
  by rewrite Htrace.
Qed.

(* povm_channel_cptp *)
(* infra: no tex label — a complete positive POVM induces a CPTP
   classical-output channel.                                           *)
(* path: utils:povm_channel_cptp -> entropy:smooth_hmax_labelled_mx -> *)
(*   bb84:stat -> bb84:bb84_secret *)
Lemma povm_channel_cptp (L : finType) (H : L -> chsType)
    (I : finType) (S T : {set L})
    (out : I -> 'Idx[H]_T) (M : I -> 'F[H]_S) :
  (forall i, M i \is psdlf) ->
  \sum_i M i = \1 ->
  @povm_channel R L H I S T out M \is cptp.
Proof.
  move=> HMpsd HMsum.
  rewrite /povm_channel.
  apply/krausso_qcP.
  rewrite /trace_presv pair_bigV /=.
  apply/eqP.
  rewrite (eq_bigr (fun i => (sqrtH (M i))^A \o sqrtH (M i)));
    last first.
  {
    move=> i _.
    have Hterm (x : 'Idx[H]_S) :
        (([> deltav (out i) ; deltav x <] \o sqrtH (M i))^A \o
          ([> deltav (out i) ; deltav x <] \o sqrtH (M i))) =
        (sqrtH (M i))^A \o [> deltav x ; deltav x <] \o sqrtH (M i).
    {
      rewrite adjf_comp adj_outp -comp_lfunA.
      rewrite [X in (sqrtH (M i))^A \o X]comp_lfunA.
      by rewrite outp_comp dv_dot eqxx scale1r comp_lfunA.
    }
    under eq_bigr => x _ do rewrite Hterm.
    by rewrite -linear_sumlz /= -linear_sumr /= sumonb_out comp_lfun1r.
  }
  rewrite (eq_bigr (fun i => M i)); last first.
  {
    move=> i _.
    have Hsqrt_herm : sqrtH (M i) \is hermlf :=
      sqrtH_herm (psdlf_herm (HMpsd i)).
    by rewrite (hermlf_adjE Hsqrt_herm) sqrtHK.
  }
  exact: HMsum.
Qed.

Section SqrtLfUnitSet.

(* sqrtH0 *)
(* infra: no tex label — fundamental & reusable (mathcomp-style) *)
(* consumer: sqrtH0 is used downstream by the BB84 secrecy proof. *)
(* path: utils:sqrtH0 -> entropy:smooth_hmax_labelled_mx -> bb84:stat -> *)
(*   bb84:bb84_secret *)
Lemma sqrtH0 (L : finType) (HL : L -> chsType) (S : {set L}) :
  sqrtH (0 : 'F[HL]_S) = 0.
Proof.
  by apply/h2mx_inj; rewrite sqrtH_h2mx h2mx0 sqrtmx0.
Qed.

(* sqrtH1 *)
(* infra: no tex label — fundamental & reusable (mathcomp-style) *)
(* consumer: sqrtH1 is used downstream by the BB84 secrecy proof. *)
(* path: utils:sqrtH1 -> entropy:min_koenig -> entropy:min_omni -> *)
(*   entropy:minmax_dual -> entropy:smooth_iso_hmax -> *)
(*   entropy:entropy_data_proc -> *)
(*   bb84:bb84_secret *)
Lemma sqrtH1 (L : finType) (HL : L -> chsType) (S : {set L}) :
  sqrtH (\1 : 'F[HL]_S) = \1.
Proof.
  by apply/h2mx_inj; rewrite sqrtH_h2mx h2mx1 sqrtmx1.
Qed.

End SqrtLfUnitSet.

Section SqrtLfScaleLemmas.

(* sqrtHZ_nn *)
(* infra: no tex label — fundamental & reusable (mathcomp-style) *)
(* consumer: sqrtHZ_nn is used downstream by the BB84 secrecy proof. *)
(* path: utils:sqrtHZ_nn -> entropy:hminE_EFin -> *)
(*   bb84:privacy_amplification -> bb84:bb84_secret *)
Lemma sqrtHZ_nn (L : finType) (HL : L -> chsType) (S : {set L})
    (c : R) (A : 'F[HL]_S) :
  0 <= c -> A \is psdlf ->
  sqrtH ((c%:C) *: A) = (Num.sqrt c)%:C *: sqrtH A.
Proof.
  move=> c_ge0; rewrite qualifE => PA.
  apply/h2mx_inj.
  have Hlin := @h2mxP R ('H[HL]_S) ('H[HL]_S).
  have Hscale (a : C) (x : 'F[HL]_S) :
      h2mx (a *: x) = a *: h2mx x.
  { have := Hlin a x 0.
    by rewrite addr0 h2mx0 addr0. }
  rewrite !sqrtH_h2mx !Hscale !sqrtH_h2mx /=.
  by rewrite (sqrtmxZ_nn c_ge0 PA).
Qed.

End SqrtLfScaleLemmas.

Section PinvLfLemmas.

(* h2mx of pinvlf collapses to pinvmx_ on h2mx. Bridge lemma. *)
(* path: utils:pinvlf_h2mx -> utils:pinvlf_sqrtH_pow2 -> *)
(*   lhl:uniform_collision_bound -> *)
(*   bb84:privacy_amplification -> bb84:bb84_secret *)
Lemma pinvlf_h2mx (L : finType) (HL : L -> chsType) (S : {set L}) (A : 'F[HL]_S) :
  h2mx (pinvlf A) = pinvmx_ (h2mx A).
Proof.
  by rewrite /pinvlf mx2hK.
Qed.

(* lfun-level pseudoinverse uniqueness from 4 MP conditions. *)
(* path: utils:pinvlf_uniq_MP -> utils:pinvlf_sdot_I -> *)
(*   utils:trlf_cross_system_4pt_identity -> *)
(*   bb84:privacy_amplification -> bb84:bb84_secret *)
Lemma pinvlf_uniq_MP (L : finType) (HL : L -> chsType) (S : {set L})
    (M Y : 'F[HL]_S) :
  M \o Y \o M = M ->
  Y \o M \o Y = Y ->
  (M \o Y)^A = M \o Y ->
  (Y \o M)^A = Y \o M ->
  Y = (pinvlf M)^A.
Proof.
  move=> H1 H2 H3 H4.
  apply/h2mx_inj.
  rewrite h2mx_adj pinvlf_h2mx.
  apply: pinvmx_uniq_MP.
  - have := f_equal h2mx H1.
    by rewrite !h2mx_comp.
  - have := f_equal h2mx H2.
    by rewrite !h2mx_comp.
  - have := f_equal h2mx H3.
    by rewrite h2mx_adj h2mx_comp.
  - have := f_equal h2mx H4.
    by rewrite h2mx_adj h2mx_comp.
Qed.

(* lfun-level Helper A (depends on Helper A pinvmx_MP_cond2 in comp.v). *)
(* path: utils:pinvlf_MP_cond2 -> utils:pinvlf_sdot_I -> *)
(*   utils:trlf_cross_system_4pt_identity -> *)
(*   bb84:privacy_amplification -> bb84:bb84_secret *)
Lemma pinvlf_MP_cond2 (L : finType) (HL : L -> chsType) (S : {set L})
    (M : 'F[HL]_S) :
  (pinvlf M)^A \o M \o (pinvlf M)^A = (pinvlf M)^A.
Proof.
  apply/h2mx_inj.
  rewrite !h2mx_comp h2mx_adj pinvlf_h2mx.
  exact: pinvmx_MP_cond2.
Qed.

(* lfun-level cosupplf_id: M \o (pinvlf M)^A \o M = M (foundational identity). *)
(* path: utils:pinvlf_MP_cond1 -> utils:pinvlf_sdot_I -> *)
(*   utils:trlf_cross_system_4pt_identity -> *)
(*   bb84:privacy_amplification -> bb84:bb84_secret *)
Lemma pinvlf_MP_cond1 (L : finType) (HL : L -> chsType) (S : {set L})
    (M : 'F[HL]_S) :
  M \o (pinvlf M)^A \o M = M.
Proof.
  apply/h2mx_inj.
  rewrite !h2mx_comp h2mx_adj pinvlf_h2mx.
  exact: (cosuppmx_id (h2mx M)).
Qed.

(* lfun-level cosupplf hermicity: (M \o (pinvlf M)^A)^A = M \o (pinvlf M)^A. *)
(* path: utils:pinvlf_MP_cond3 -> utils:pinvlf_sdot_I -> *)
(*   utils:trlf_cross_system_4pt_identity -> *)
(*   bb84:privacy_amplification -> bb84:bb84_secret *)
Lemma pinvlf_MP_cond3 (L : finType) (HL : L -> chsType) (S : {set L})
    (M : 'F[HL]_S) :
  (M \o (pinvlf M)^A)^A = M \o (pinvlf M)^A.
Proof.
  apply/h2mx_inj.
  rewrite h2mx_adj h2mx_comp h2mx_adj pinvlf_h2mx.
  by have/hermmxP/esym := cosuppmx_herm (h2mx M); rewrite /cosuppmx.
Qed.

(* lfun-level supplf hermicity: ((pinvlf M)^A \o M)^A = (pinvlf M)^A \o M. *)
(* path: utils:pinvlf_MP_cond4 -> utils:pinvlf_sdot_I -> *)
(*   utils:trlf_cross_system_4pt_identity -> *)
(*   bb84:privacy_amplification -> bb84:bb84_secret *)
Lemma pinvlf_MP_cond4 (L : finType) (HL : L -> chsType) (S : {set L})
    (M : 'F[HL]_S) :
  ((pinvlf M)^A \o M)^A = (pinvlf M)^A \o M.
Proof.
  apply/h2mx_inj.
  rewrite h2mx_adj h2mx_comp h2mx_adj pinvlf_h2mx.
  by have/hermmxP/esym := suppmx_herm (h2mx M); rewrite /suppmx.
Qed.

(* (X^{-1/2})^2 = X^{-1} on support: matrix-level spectral decomposition  *)
(* via mapf_mx — eigenvalues λ_i become λ_i^{-½} under pinvlf∘sqrtH,      *)
(* square to λ_i^{-¹}.                                                    *)
(* pinvlf_sqrtH_pow2 *)
(* infra: no tex label — fundamental & reusable (mathcomp-style) *)
(* consumer: pinvlf_sqrtH_pow2 is used downstream by the BB84 secrecy proof. *)
(* path: utils:pinvlf_sqrtH_pow2 -> lhl:uniform_collision_bound -> *)
(*   bb84:privacy_amplification -> bb84:bb84_secret *)
Lemma pinvlf_sqrtH_pow2 (L : finType) (HL : L -> chsType) (S : {set L})
    (A : 'F[HL]_S) :
  A \is psdlf ->
  pinvlf (sqrtH A) \o pinvlf (sqrtH A) = pinvlf A.
Proof.
  rewrite qualifE => PA.
  apply/h2mx_inj.
  rewrite h2mx_comp.
  rewrite [RHS]pinvlf_h2mx.
  rewrite [in LHS]pinvlf_h2mx.
  rewrite (sqrtH_h2mx A).
  set M : 'M[C]_(dim 'H[HL]_S) := h2mx A.
  case: (psdmx_svd PA) => -[U D] /and3P [HU HD /eqP HM].
  set Dh : 'rV[C]_(dim 'H[HL]_S) :=
    \row_j (Num.sqrt (@complex.Re R (D 0 j)))%:C.
  set Q : 'M[C]_(dim 'H[HL]_S) := U^*t *m diag_mx Dh *m U.
  have HUKV : U^*t *m U = 1%:M by exact: unitarymxKV.
  have HUK  : U *m U^*t = 1%:M by exact: unitarymxK.
  have HD_nneg : D \is a nnegmx := svd_diag_nneg HD.
  have HDnn : forall j, 0 <= D 0 j by move=> j; exact: svd_diag_ge0.
  (* Each entry of D is real and equal to its (complex Re %:C) embedding. *)
  have HD_eqRe : forall j, D 0 j = (@complex.Re R (D 0 j))%:C.
    move=> j.
    have HDjr : D 0 j \is Num.real.
      apply/orP; left; exact: (HDnn j).
    by rewrite -[in LHS](RRe_real HDjr).
  have HReD_nn : forall j, 0 <= @complex.Re R (D 0 j).
    by move=> j; have:= HDnn j; rewrite lecE/= => /andP[_].
  (* Dh is nneg. *)
  have HDh_nneg : Dh \is a nnegmx.
    apply/nnegmxP=> i j; rewrite !mxE nnegrE.
    by rewrite lecR sqrtr_ge0.
  (* Pointwise: (Dh 0 j) * (Dh 0 j) = D 0 j. *)
  have HDh_sq : forall j, (Dh 0 j) * (Dh 0 j) = D 0 j.
    move=> j; rewrite !mxE.
    rewrite -realcM -expr2.
    rewrite (sqr_sqrtr (HReD_nn j)).
    by rewrite -(HD_eqRe j).
  have HDhDh : Dh .* Dh = D.
    apply/matrixP=> i j.
    rewrite mxE (ord1 i).
    exact: HDh_sq.
  (* Q *m Q = M. *)
  have HQQ : Q *m Q = M.
    rewrite /Q.
    rewrite -!mulmxA.
    rewrite [U *m (U^*t *m _)]mulmxA HUK mul1mx.
    rewrite [diag_mx Dh *m _]mulmxA.
    rewrite diag_mx_dmul HDhDh.
    rewrite mulmxA.
    by rewrite /M HM.
  (* Q is psd (form of nneg diag). *)
  have HQ_psd : Q \is psdmx.
    rewrite /Q; exact: formV_psdmx (diagmx_nnegmx_psd HDh_nneg).
  (* Therefore sqrtmx M = Q. *)
  have HsqrtM_eq : sqrtmx M = Q by rewrite -HQQ sqrtmx_psd_square.
  (* Apply helper to get pinvmx_ Q and pinvmx_ M in U/Dh and U/D form. *)
  have HQ_eq : Q = U^*t *m diag_mx Dh *m U by [].
  have Hpinv_sqrt : pinvmx_ (sqrtmx M) = U^*t *m diag_mx Dh.^-1 *m U.
    rewrite HsqrtM_eq.
    exact: pinvmx_psdmx_svd_form HU HDh_nneg HQ_eq.
  have Hpinv_M : pinvmx_ M = U^*t *m diag_mx D.^-1 *m U.
    exact: pinvmx_psdmx_svd_form HU HD_nneg HM.
  rewrite Hpinv_sqrt Hpinv_M.
  (* Goal: U^*t *m diag Dh.^-1 *m U *m (U^*t *m diag Dh.^-1 *m U)
        = U^*t *m diag D.^-1 *m U *)
  have HDhinv_sq : Dh.^-1 .* Dh.^-1 = D.^-1.
    apply/matrixP=> i j.
    rewrite mxE [Dh.^-1 i j]mxE [(D.^-1) i j]mxE.
    rewrite (ord1 i).
    rewrite -invfM.
    by rewrite HDh_sq.
  rewrite -!mulmxA.
  rewrite [U *m (U^*t *m _)]mulmxA HUK mul1mx.
  rewrite [diag_mx Dh.^-1 *m _]mulmxA.
  rewrite diag_mx_dmul HDhinv_sq.
  rewrite [LHS]mulmxA.
  rewrite [RHS]mulmxA.
  reflexivity.
Qed.

(* pinvlf of psdlf is psdlf, by a direct spectral/SVD proof.                *)
(* Consumers (≥2): uniform_to_collision (T14i hermlf chain), privacy_amp   *)
(* (symmetric pinv-of-sqrt usage against τ_E).                             *)
(* pinvlf_psdlf *)
(* infra: no tex label — fundamental & reusable (mathcomp-style) *)
(* consumer: pinvlf_psdlf is used downstream by the BB84 secrecy proof. *)
(* path: utils:pinvlf_psdlf -> lhl:min_coll_bound -> *)
(*   bb84:privacy_amplification -> bb84:bb84_secret *)
Lemma pinvlf_psdlf (L : finType) (HL : L -> chsType) (S : {set L})
    (A : 'F[HL]_S) : A \is psdlf -> pinvlf A \is psdlf.
Proof.
  rewrite qualifE => PA.
  rewrite qualifE.
  rewrite /pinvlf mx2hK.
  set M : 'M[C]_(dim 'H[HL]_S) := h2mx A.
  case: (psdmx_svd PA) => -[U D] /and3P [HU HD /eqP HM].
  have HD_nneg : D \is a nnegmx := svd_diag_nneg HD.
  rewrite (pinvmx_psdmx_svd_form HU HD_nneg HM).
  apply: formV_psdmx.
  apply: diagmx_nnegmx_psd.
  apply/nnegmxP=> i j; rewrite mxE nnegrE.
  rewrite (ord1 i).
  case: (eqVneq (D 0 j) 0) => [-> | _].
    by rewrite invr0.
  rewrite invr_ge0.
  by have /nnegmxP/(_ 0 j) := HD_nneg; rewrite nnegrE.
Qed.

(* Pseudoinverse of a scalar multiple: pinv(c·A) = c⁻¹·pinv A for c ≠ 0.  *)
(* Textbook Moore-Penrose identity, immediate from the four defining      *)
(* conditions applied to B = c⁻¹·A⁺ against M = c·A.                      *)
(* Standalone justification: foundational pseudoinverse identity          *)
(* (Penrose 1955 §3, Stewart-Sun §3.1).                                   *)
(* Consumers: trlf_cross_system_4pt_identity (lift.v) and privacy_amp    *)
(* scalar-normalization steps (LHL arXiv:1002.2436, proof of Thm 6).                       *)
(* pinvlfZ_nn *)
(* infra: no tex label — fundamental & reusable (mathcomp-style) *)
(* consumer: pinvlfZ_nn is used downstream by the BB84 secrecy proof. *)
(* path: utils:pinvlfZ_nn -> lhl:min_coll_bound -> *)
(*   bb84:privacy_amplification -> bb84:bb84_secret *)
Lemma pinvlfZ_nn (L : finType) (HL : L -> chsType) (S : {set L})
    (c : R) (A : 'F[HL]_S) :
  c != 0 ->
  pinvlf ((c%:C) *: A) = ((c^-1)%:C) *: pinvlf A.
Proof.
  move=> Hc.
  apply/h2mx_inj.
  rewrite /pinvlf.
  set M := h2mx A.
  have Hlin := @h2mxP R ('H[HL]_S) ('H[HL]_S).
  have Hscale (a : C) (x : 'F[HL]_S) :
      h2mx (a *: x) = a *: h2mx x.
  { have := Hlin a x 0.
    by rewrite addr0 h2mx0 addr0. }
  rewrite [h2mx (((c^-1)%:C) *: _)]Hscale /=.
  rewrite [h2mx ((c%:C) *: A)]Hscale /= -/M.
  set M' : 'M[C]_(dim 'H[HL]_S) := c%:C *: M.
  change (h2mx (mx2h (pinvmx_ M')) =
          (c^-1)%:C *: h2mx (mx2h (pinvmx_ M))).
  have Hmx2hK1 :
      h2mx (mx2h (pinvmx_ M')) = pinvmx_ M' :=
    @mx2hK R ('H[HL]_S) ('H[HL]_S) (pinvmx_ M').
  have Hmx2hK2 :
      h2mx (mx2h (pinvmx_ M)) = pinvmx_ M :=
    @mx2hK R ('H[HL]_S) ('H[HL]_S) (pinvmx_ M).
  apply: (etrans Hmx2hK1).
  rewrite Hmx2hK2.
  set Y : 'M[C]_(dim 'H[HL]_S) := ((c^-1)%:C) *: (pinvmx_ M)^*t.
  have HcC : c%:C != 0 :> C.
    apply: contra Hc => /eqP /(f_equal (@complex.Re R)).
    by move/eqP.
  have Hccinv : c%:C * (c^-1)%:C = 1 :> C
    by rewrite -rmorphM mulfV.
  have Hcinvc : (c^-1)%:C * c%:C = 1 :> C by rewrite mulrC.
  (* Helper: combine three scalar-multiplied factors into one scalar. *)
  have scal3 : forall (a b cc : C) (X Y0 Z : 'M[C]_(dim 'H[HL]_S)),
    (a *: X) *m (b *: Y0) *m (cc *: Z) = (a * b * cc) *: (X *m Y0 *m Z).
    move=> a b cc X' Y' Z'.
    rewrite -[(a *: X') *m (b *: Y')]scalemxAl.
    rewrite -[X' *m (b *: Y')]scalemxAr.
    rewrite -[a *: (b *: (X' *m Y')) *m (cc *: Z')]scalemxAl.
    rewrite -[(b *: (X' *m Y')) *m (cc *: Z')]scalemxAr.
    rewrite -[(b *: (X' *m Y')) *m Z']scalemxAl.
    rewrite !scalerA.
    by rewrite mulrAC.
  have scal2 : forall (a b : C) (X Y0 : 'M[C]_(dim 'H[HL]_S)),
    (a *: X) *m (b *: Y0) = (a * b) *: (X *m Y0).
    move=> a b X' Y'.
    rewrite -[(a *: X') *m (b *: Y')]scalemxAl.
    rewrite -[X' *m (b *: Y')]scalemxAr.
    by rewrite scalerA.
  have H1 : M' *m Y *m M' = M'.
    rewrite /M' /Y scal3 Hccinv mul1r.
    have := cosuppmx_id M.
    by rewrite /cosuppmx => ->.
  have H2 : Y *m M' *m Y = Y.
    rewrite /M' /Y scal3 Hcinvc mul1r.
    by rewrite pinvmx_MP_cond2.
  have H3 : (M' *m Y)^*t = M' *m Y.
    rewrite /M' /Y scal2 Hccinv scale1r.
    have /hermmxP HCH := cosuppmx_herm M.
    by move: HCH; rewrite /cosuppmx.
  have H4 : (Y *m M')^*t = Y *m M'.
    rewrite /M' /Y scal2 Hcinvc scale1r.
    have /hermmxP HSH := suppmx_herm M.
    by move: HSH; rewrite /suppmx.
  have HY : Y = (pinvmx_ M')^*t by exact: pinvmx_uniq_MP H1 H2 H3 H4.
  have key : pinvmx_ M' = (c^-1)%:C *: pinvmx_ M.
    have step := f_equal (fun X : 'M[C]_(dim 'H[HL]_S) => X^*t) HY.
    rewrite adjmxK in step.
    rewrite /Y in step.
    rewrite adjmxZ in step.
    rewrite adjmxK in step.
    have HcinvR : ((c^-1)%:C : C)^* = (c^-1)%:C := conjc_real (c^-1).
    rewrite HcinvR in step.
    by rewrite -step.
  exact: key.
Qed.

End PinvLfLemmas.

(* ================================================================== *)
(* Tensor products in ambient matrix coordinates                        *)
(* ================================================================== *)

Section LabelledProductMatrixBridges.
Variable (L : finType) (H : L -> chsType).

(* h2mx_sdot_product *)
(* infra: no tex label -- labelled tensor in ambient matrix coordinates *)
(* path: utils:h2mx_sdot_product -> entropy:smooth_hmax_labelled_mx -> *)
(*   bb84:stat -> bb84:bb84_secret *)
Lemma h2mx_sdot_product
    (A B : {set L}) (disAB : [disjoint A & B])
    (f : 'F[H]_A) (g : 'F[H]_B) :
  let Q : 'M[C]_(dim 'H[H]_A * dim 'H[H]_B) :=
    castmx (tenv_dim disAB, erefl) (@tenv_mxU R L H A B) in
  castmx (tenv_dim disAB, tenv_dim disAB) (h2mx (f \O g)) =
  Q *m (h2mx f *t h2mx g) *m Q^*t.
Proof.
  rewrite /=.
  set Q : 'M[C]_(dim 'H[H]_A * dim 'H[H]_B) :=
    castmx (tenv_dim disAB, erefl) (@tenv_mxU R L H A B).
  have HQ_t : Q^*t = castmx (erefl, tenv_dim disAB)
                    (@tenv_mxU R L H A B)^*t.
  { rewrite /Q.
    exact: (@castmx_mx_mxT _ _ (@adjmx _) _ _ _ _
      (tenv_dim disAB, erefl)
      (@tenv_mxU R L H A B)). }
  have HQQt : Q *m Q^*t = 1%:M.
  { rewrite /Q HQ_t mcextra.castmx_mul.
    have HU : (@tenv_mxU R L H A B) *m
                (@tenv_mxU R L H A B)^*t = 1%:M.
    { exact: unitarymxK (@tenv_mxU_unitarymx R L H A B). }
    rewrite HU.
    by case: _ / (tenv_dim disAB); rewrite castmx_id. }
  have Hsdot := @biprod_mx_sdot R L H A B disAB f g.
  rewrite /biprod_mx -/Q in Hsdot.
  have := f_equal (fun X => Q *m X *m Q^*t) Hsdot.
  rewrite [Q *m ((Q^*t *m _) *m Q)]mulmxA.
  rewrite [Q *m (Q^*t *m _)]mulmxA HQQt mul1mx.
  rewrite -!mulmxA HQQt mulmx1.
  by move=> ->.
Qed.

End LabelledProductMatrixBridges.

(* ================================================================== *)
(* lnlf lemmas: spectral bridge + Hermiticity                         *)
(* ================================================================== *)

(* ================================================================== *)
(* PSD lfun bounded above by trace times identity (wrapper of          *)
(* psdmx_le_tr_id).                                                     *)
(* ================================================================== *)

(* ================================================================== *)
(* trnormH / i2norm_lf / schnorm_2 — lfun-level norm lemmas          *)
(* ================================================================== *)

Section TrNormLfLemmas.

(* tex: none (library utility — lfun-level wrapper of mxnorm.v:4228).     *)
(* math: trnormH (f - g) ≤ trnormH f + trnormH g (triangle).        *)
(* Standalone justification: textbook trace-norm triangle inequality      *)
(* (Watrous §1.1.4). Consumer: dfu_pd_triangle (lhl/def.v).              *)
(* trnormH_triangleB *)
(* infra: no tex label — fundamental & reusable (mathcomp-style) *)
(* consumer: trnormH_triangleB is used downstream by the BB84 secrecy proof. *)
(* path: utils:trnormH_triangleB -> utils:trnormH_triangle -> *)
(*   bb84:privacy_amplification -> bb84:bb84_secret *)
Lemma trnormH_triangleB (L : finType) (HL : L -> chsType) (S : {set L})
    (f g : 'F[HL]_S) :
  trnormH (f - g) <= trnormH f + trnormH g.
Proof.
  rewrite /trnormH raddfB /=.
  have Htri := trnorm_triangle (h2mx f) (- h2mx g).
  have HeqD : h2mx f + - h2mx g = h2mx f - h2mx g by [].
  rewrite HeqD in Htri.
  rewrite schnormN in Htri.
  move: Htri; rewrite lecE /= => /andP [_ Htri2].
  by move: Htri2; rewrite raddfD /=.
Qed.

(* tex: none (library utility — mxnorm.v:4228 + trnormN).                 *)
(* math: trnormH (f + g) ≤ trnormH f + trnormH g.                   *)
(* Standalone justification: textbook triangle inequality; derived from   *)
(* trnormH_triangleB via -g substitution.                               *)
(* Consumer: dfu_pd_triangle (3-term chain).                             *)
(* trnormH_triangle *)
(* infra: no tex label — fundamental & reusable (mathcomp-style) *)
(* consumer: trnormH_triangle is used downstream by the BB84 secrecy proof. *)
(* path: utils:trnormH_triangle -> *)
(*   bb84:privacy_amplification -> bb84:bb84_secret *)
Lemma trnormH_triangle (L : finType) (HL : L -> chsType) (S : {set L})
    (f g : 'F[HL]_S) :
  trnormH (f + g) <= trnormH f + trnormH g.
Proof.
  have -> : f + g = f - (- g) by rewrite opprK.
  apply: le_trans (trnormH_triangleB f (-g)) _.
  rewrite lerD2l /trnormH raddfN /= schnormN.
  exact: lexx.
Qed.

(* tex: none (library utility — mxnorm.v:4217).                           *)
(* math: trnormH (c%:C *: f) = |c| * trnormH f for c : R.             *)
(* Standalone justification: textbook trace-norm scalar-multiplication    *)
(* identity (Watrous §1.1.4). Consumer: dfu_pd_triangle.                 *)
(* trnormH_scaleZ *)
(* infra: no tex label — fundamental & reusable (mathcomp-style) *)
(* consumer: trnormH_scaleZ is used downstream by the BB84 secrecy proof. *)
(* path: utils:trnormH_scaleZ -> bb84:privacy_amplification -> *)
(*   bb84:bb84_secret *)
Lemma trnormH_scaleZ (L : finType) (HL : L -> chsType) (S : {set L})
    (c : R) (f : 'F[HL]_S) :
  trnormH (c%:C *: f) = `|c| * trnormH f.
Proof.
  rewrite /trnormH.
  have Hlin := @h2mxP R ('H[HL]_S) ('H[HL]_S).
  have Hscale (a : C) (x : 'F[HL]_S) :
      h2mx (a *: x) = a *: h2mx x.
  { have := Hlin a x 0.
    by rewrite addr0 h2mx0 addr0. }
  rewrite Hscale /= schnormZ.
  have Habs : `|c%:C| = (`|c|)%:C :> C.
    by rewrite normc_def /= expr0n /= addr0 sqrtr_sqr.
  rewrite Habs.
  set T := schnorm _ _.
  by case: T => [a b] /=; rewrite mul0r subr0.
Qed.

(* tex: none (library utility — mxnorm.v:4342).                           *)
(* math: psd f ⇒ trnormH f = Re (Tr f).                                 *)
(* Standalone justification: for PSD matrices singular values are         *)
(* eigenvalues ≥ 0, so trnorm = Σ eigenvalues = Tr (Watrous §1.1.4).      *)
(* Consumers (≥2): dfu_pd_triangle, trnormH_lift_I_psd (lift.v).        *)
(* trnormH_psd *)
(* infra: no tex label — fundamental & reusable (mathcomp-style) *)
(* consumer: trnormH_psd is used downstream by the BB84 secrecy proof. *)
(* path: utils:trnormH_psd -> entropy:smooth_hmax_labelled_mx -> bb84:stat -> *)
(*   bb84:bb84_secret *)
Lemma trnormH_psd (L : finType) (HL : L -> chsType) (S : {set L})
    (f : 'F[HL]_S) :
  f \is psdlf -> trnormH f = @complex.Re R (\Tr f).
Proof.
  move=> Pf.
  rewrite /trnormH.
  have Hpsdmx : h2mx f \is psdmx by move: Pf; rewrite qualifE.
  by rewrite (psdmx_trnorm Hpsdmx).
Qed.

End TrNormLfLemmas.

Local Close Scope lfun_scope.

End FvqkdReal.
