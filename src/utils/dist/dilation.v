(* -------------------------------------------------------------------- *)
(* dilation.v — Stinespring dilation + fidelity monotonicity (TP-CPM)   *)
(* -------------------------------------------------------------------- *)
(* Module: utils.dist.dilation                                      *)
(* Paper: Tomamichel, 'A Framework for Non-Asymptotic Quantum            *)
(*   Information Theory' (PhD thesis, arXiv:1203.2142), Chapters 2 & 3.   *)
(* Owns generic matrix-level quantum-channel primitives used by distance  *)
(* and entropy modules, including Stinespring dilation and fidelity       *)
(* monotonicity for trace-preserving completely positive maps.            *)
(* TeX labels: lm:stinespring (Lemma 2.4); tb:fid item (ii) (Table 3.1). *)
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
  cpo mxpred extnum ctopology svd mxnorm hspace autonat.
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

Section Dilation.
Variable R : realType.
Notation C := (@hermitian.C R).
Notation chsType := (@chsType R).

(* ================================================================== *)
(* tex: lm:stinespring — Tomamichel, 'A Framework for Non-Asymptotic    *)
(*   Quantum Information Theory' (PhD thesis, arXiv:1203.2142),         *)
(*   Lemma 2.4 (Stinespring Dilation)                                   *)
(* Tex statement: a super-operator ℰ is CP iff there exists a Hilbert  *)
(*   space ℋ-prime-prime and L in Hom(ℋ, ℋ-prime tensor ℋ-prime-prime)  *)
(*   such that ℰ(A) = Tr on ℋ-prime-prime of L A L-dagger. Moreover,    *)
(*   if ℰ is TP then L is an isometry. If ℰ is trace non-increasing,    *)
(*   then L is an isometry followed by a projection in Pos of the      *)
(*   ancillary space.                                                   *)
(* In finite dimensions, the existential over the ancillary Hilbert    *)
(* space is captured by an existential over z : nat with the ancilla   *)
(* being C-to-the-z. The condition `L isometry followed by projection` *)
(* is equivalent to L-dagger L ≤ I (L is a sub-isometry).               *)
(* consumer: lm_st is used downstream by the BB84 secrecy proof. *)
(* ================================================================== *)

Section Stinespring.
Variables (L : finType) (H : L -> chsType).
Variables (U V : {set L}).

(* path: entropy:stinespring -> entropy:entropy_data_proc -> *)
(*   bb84:bb84_secret *)
Lemma stinespring (F : 'SO[H]_(U, V)) :
  F \is cpmap <->
  exists (z : nat)
      (W : 'M[C]_(dim 'H[H]_V * z, dim 'H[H]_U)),
    [/\ z = dim 'H[H]_U * dim 'H[H]_V,
        forall rho : 'M[C]_(dim 'H[H]_U),
          h2mx (F (mx2h rho)) = ptrace2 (W *m rho *m W^*t),
        F \is tpmap -> W^*t *m W = 1%:M
      & F \is tnmap -> W^*t *m W <= 1%:M].
Proof.
  split.
  - move=> Hcp.
    pose z := dim 'H[H]_U * dim 'H[H]_V.
    pose Ec := CPMap_Build Hcp.
    pose K (k : 'I_z) := krausop Ec k.
    pose W : 'M[C]_(dim 'H[H]_V * z, dim 'H[H]_U) :=
      \matrix_(r, c)
        let rc := mxtens_unindex r : 'I_(dim 'H[H]_V) * 'I_z in
        (h2mx (K rc.2)) rc.1 c.
    have HKfun : K = krausop Ec.
    { apply/funext => k. by rewrite /K. }
    have HWadj :
        W^*t *m W = \sum_k (h2mx (K k))^*t *m h2mx (K k).
    { apply/matrixP => a b.
      rewrite mxE.
      transitivity
        (\sum_(i : 'I_(dim 'H[H]_V)) \sum_(k : 'I_z)
          (W^*t) a (mxtens_index (i, k)) * W (mxtens_index (i, k)) b).
      { rewrite (reindex (@mxtens_index (dim 'H[H]_V) z)) /=.
        2:{ exists (@mxtens_unindex (dim 'H[H]_V) z) => l /=;
              by rewrite ?mxtens_indexK ?mxtens_unindexK -?surjective_pairing. }
        by rewrite pair_bigV /=. }
      transitivity
        (\sum_(i : 'I_(dim 'H[H]_V)) \sum_(k : 'I_z)
          ((h2mx (K k))^*t) a i * (h2mx (K k)) i b).
      { apply: eq_bigr => i _.
        apply: eq_bigr => k _.
          by rewrite !adjmxE /W !mxE !mxtens_indexK. }
      rewrite exchange_big summxE.
      apply: eq_bigr => k _.
      rewrite mxE.
      by apply: eq_bigr => i _; rewrite !mxE. }
    have ptrace2E' : forall s t (B0 : 'M[C]_(s * t)) r1 r2,
        (ptrace2 B0) r1 r2 =
        \sum_(l : 'I_t) B0 (mxtens_index (r1, l)) (mxtens_index (r2, l)).
    { move=> s t B0 r1 r2.
      rewrite ptrace2E1 ptrace1E.
      by apply: eq_bigr => l _; rewrite mxE !mxtens_indexK. }
    have Hptr : forall rho : 'M[C]_(dim 'H[H]_U),
        ptrace2 (W *m rho *m W^*t) =
        \sum_k h2mx (K k) *m rho *m (h2mx (K k))^*t.
    { move=> rho.
      apply/matrixP => i j.
      rewrite ptrace2E' summxE.
      apply: eq_bigr => k _.
      rewrite !mxE.
      apply: eq_bigr => a _.
      have Hadj :
          (W^*t) a (mxtens_index (j, k)) = ((h2mx (K k))^*t) a j.
      { by rewrite !adjmxE /W !mxE !mxtens_indexK. }
      have HWrho :
          (W *m rho) (mxtens_index (i, k)) a = (h2mx (K k) *m rho) i a.
      { rewrite !mxE.
        by apply: eq_bigr => b _; rewrite /W !mxE !mxtens_indexK. }
      by rewrite Hadj HWrho. }
    exists z, W.
    split.
    + by [].   (* z = dim 'H[H]_U * dim 'H[H]_V from definition of z *)
    + move=> rho.
      have HEval : h2mx (F (mx2h rho)) = h2mx (Ec (mx2h rho)).
      { move: (CPMap_BuildE Hcp).
        move/(congr1 (fun G : 'SO[H]_(U, V) => h2mx (G (mx2h rho)))).
        by []. }
      rewrite HEval Hptr (krausE Ec (mx2h rho)) raddf_sum.
      apply: eq_bigr => k _.
      by rewrite /= !h2mx_comp h2mx_adj mx2hK.
    + move=> Htp.
      have HEtp : (Ec : 'SO[H]_(U, V)) \is tpmap.
        by rewrite -(CPMap_BuildE Hcp).
      have HEc_k : (Ec : 'SO[H]_(U, V)) = krausso K.
      { rewrite HKfun. exact: krausopE. }
      move: HEtp.
      rewrite HEc_k krausso_tpE /trace_presv => /eqP HKtp.
      rewrite HWadj.
      transitivity (h2mx (\sum_k ((K k)^A \o K k))).
      { by rewrite raddf_sum; apply: eq_bigr => k _; rewrite /= h2mx_comp h2mx_adj. }
      by rewrite HKtp h2mx1.
    + move=> Htn.
      have HEtn : (Ec : 'SO[H]_(U, V)) \is tnmap.
        by rewrite -(CPMap_BuildE Hcp).
      have HEc_k : (Ec : 'SO[H]_(U, V)) = krausso K.
      { rewrite HKfun. exact: krausopE. }
      have HEtnK_mx : h2mx (\sum_k ((K k)^A \o K k)) <= 1%:M.
      { move: HEtn.
        rewrite HEc_k krausso_tnE /trace_nincr => HEtnK.
        rewrite -h2mx1 -lef_h2mx.
        exact: HEtnK. }
      rewrite HWadj.
      have -> : \sum_k (h2mx (K k))^*t *m h2mx (K k) =
                h2mx (\sum_k ((K k)^A \o K k)).
      { by rewrite raddf_sum; apply: eq_bigr => k _; rewrite /= h2mx_comp h2mx_adj. }
      exact: HEtnK_mx.
  - move=> [z [W [_ Hact _ _]]].
    pose K (k : 'I_z) : 'Hom('H[H]_U, 'H[H]_V) :=
      mx2h (\matrix_(r, c) W (mxtens_index (r, k)) c).
    have HWdecomp :
        W =
        \matrix_(r, c)
          let rc := mxtens_unindex r : 'I_(dim 'H[H]_V) * 'I_z in
          (h2mx (K rc.2)) rc.1 c.
    { apply/matrixP => r c.
      case: (mxtens_indexP r) => i k {r}.
      have Hk : h2mx (K k) =
                \matrix_(r0, c0) W (mxtens_index (r0, k)) c0.
        by rewrite /K mx2hK.
      move: (congr1 (fun M : 'M[C]_(dim 'H[H]_V, dim 'H[H]_U) => M i c) Hk).
      by rewrite !mxE !mxtens_indexK. }
    have ptrace2E' : forall s t (B0 : 'M[C]_(s * t)) r1 r2,
        (ptrace2 B0) r1 r2 =
        \sum_(l : 'I_t) B0 (mxtens_index (r1, l)) (mxtens_index (r2, l)).
    { move=> s t B0 r1 r2.
      rewrite ptrace2E1 ptrace1E.
      by apply: eq_bigr => l _; rewrite mxE !mxtens_indexK. }
    have Hptr : forall rho : 'M[C]_(dim 'H[H]_U),
        ptrace2 (W *m rho *m W^*t) =
        \sum_k h2mx (K k) *m rho *m (h2mx (K k))^*t.
    { move=> rho.
      rewrite HWdecomp.
      apply/matrixP => i j.
      rewrite ptrace2E' summxE.
      apply: eq_bigr => k _.
      rewrite !mxE.
      apply: eq_bigr => a _.
      have Hadj :
          ((\matrix_(r, c)
              let rc := mxtens_unindex r : 'I_(dim 'H[H]_V) * 'I_z in
              (h2mx (K rc.2)) rc.1 c)^*t) a (mxtens_index (j, k)) =
          ((h2mx (K k))^*t) a j.
      { by rewrite !adjmxE !mxE !mxtens_indexK. }
      have HWrho :
          ((\matrix_(r, c)
             let rc := mxtens_unindex r : 'I_(dim 'H[H]_V) * 'I_z in
             (h2mx (K rc.2)) rc.1 c) *m rho) (mxtens_index (i, k)) a =
          (h2mx (K k) *m rho) i a.
      { rewrite !mxE.
        by apply: eq_bigr => b _; rewrite !mxE !mxtens_indexK. }
      by rewrite Hadj HWrho. }
    have HEk : F = krausso K.
    { apply/superopP => X.
      apply/h2mx_inj.
      have -> : X = mx2h (h2mx X) by rewrite h2mxK.
      rewrite Hact Hptr kraussoE raddf_sum.
      apply: eq_bigr => k _.
      by rewrite /= !h2mx_comp h2mx_adj mx2hK. }
    by rewrite HEk is_cpmap.
Qed.

End Stinespring.

(* ================================================================== *)
(* tex: tb:fid item (ii) — Tomamichel, 'A Framework for Non-Asymptotic  *)
(*   Quantum Information Theory' (PhD thesis, arXiv:1203.2142),         *)
(*   Table 3.1, item (ii): fidelity monotonicity under TP-CPMs          *)
(* math: sqrt(Tr ρ)·sqrt(Tr τ) ≥ F(ℰ[ρ], ℰ[τ]) ≥ F(ρ, τ)  for TP-CPM ℰ *)
(* Derived from the Stinespring dilation above + fidelity_ptrace2_      *)
(* monotonicity (partial-trace DPI) + fid_le_tr_mx (Cauchy-Schwarz).  *)
(* ================================================================== *)

Section FidelityMonoTPCPM.
Variables (L : finType) (H : L -> chsType).
Variables (U V : {set L}).

(* path: entropy:fid_ii_cptp_bounds -> entropy:min_omni -> *)
(*   entropy:minmax_dual -> entropy:smooth_iso_hmax -> *)
(*   entropy:entropy_data_proc -> *)
(*   bb84:bb84_secret *)
Lemma fid_ii_cptp_bounds (rho tau : 'F[H]_U) (E : 'SO[H]_(U, V)) :
  rho \is psdlf -> tau \is psdlf -> E \is cptp ->
  fidelity rho tau <= fidelity (E rho) (E tau) /\
  fidelity (E rho) (E tau)
    <= Num.sqrt (@complex.Re R (\Tr rho)) * Num.sqrt (@complex.Re R (\Tr tau)).
Proof.
  move=> Prho Ptau HE.
  have HEcp : E \is cpmap := cptp_cpmap HE.
  have HEtp : E \is tpmap := cptp_tpmap HE.
  have [z [W [_ Hact HWtp _]]] := (proj1 (stinespring E) HEcp).
  have HWiso : W^*t *m W = 1%:M := HWtp HEtp.
  have Hz_pos : (0 < z)%N.
  { have Hrk : \rank (W^*t *m W) = dim 'H[H]_U.
    { move: HWiso.
      move/(congr1 mxrank).
      by rewrite mxrank1. }
    have Hle : (dim 'H[H]_U <= dim 'H[H]_V * z)%N.
    { rewrite -Hrk.
      exact: leq_trans (mxrankM_maxr _ _) (rank_leq_row _). }
    have Hprod_pos : (0 < dim 'H[H]_V * z)%N := leq_trans dim_proper Hle.
    move: Hprod_pos.
    by rewrite muln_gt0 => /andP[_]. }
  have Hrho_mx : h2mx rho \is psdmx by move: Prho; rewrite qualifE.
  have Htau_mx : h2mx tau \is psdmx by move: Ptau; rewrite qualifE.
  have HErho_psd : E rho \is psdlf.
  { rewrite (CPMap_BuildE HEcp). exact: cp_psdP. }
  have HEtau_psd : E tau \is psdlf.
  { rewrite (CPMap_BuildE HEcp). exact: cp_psdP. }
  have HWrho_psd : W *m h2mx rho *m W^*t \is psdmx.
    exact: psdmx_bimap_closed_gen Hrho_mx.
  have HWtau_psd : W *m h2mx tau *m W^*t \is psdmx.
    exact: psdmx_bimap_closed_gen Htau_mx.
  have HErho : h2mx (E rho) = ptrace2 (W *m h2mx rho *m W^*t).
  { have Htmp := Hact (h2mx rho). by rewrite h2mxK in Htmp. }
  have HEtau : h2mx (E tau) = ptrace2 (W *m h2mx tau *m W^*t).
  { have Htmp := Hact (h2mx tau). by rewrite h2mxK in Htmp. }
  (* Fidelity is invariant under conjugation by the Stinespring isometry W.    *)
  (* (Previously inlined; now via the canonical matrix lemma                    *)
  (*  fid_isometry_conj_mx — W^*t is a co-isometry from HWiso : W^*t *m W = 1.) *)
  have HW_uni : W^*t \is unitarymx.
  { apply/unitarymxP. rewrite -adjmxE adjmxK. exact: HWiso. }
  have Hiso := fid_isometry_conj_mx HW_uni Hrho_mx Htau_mx.
  rewrite !adjmxK in Hiso.
  have Hdpi := fid_ptr_mono_mx Hz_pos HWrho_psd HWtau_psd.
  split.
  - rewrite /fidelity !h2mx_comp !sqrtH_h2mx.
    rewrite HErho HEtau.
    by rewrite -Hiso.
  - have HErho_mx_psd : h2mx (E rho) \is psdmx
      by move: HErho_psd; rewrite qualifE.
    have HEtau_mx_psd : h2mx (E tau) \is psdmx
      by move: HEtau_psd; rewrite qualifE.
    have Hupper :
        fidelity (E rho) (E tau) <=
        Num.sqrt (@complex.Re R (\Tr (E rho))) *
        Num.sqrt (@complex.Re R (\Tr (E tau))).
    { rewrite /fidelity /lftrace h2mx_comp !sqrtH_h2mx.
      exact: fid_le_tr_mx HErho_mx_psd HEtau_mx_psd. }
    move/tpmapP: HEtp => Htp.
    move: Hupper.
    by rewrite (Htp rho) (Htp tau).
Qed.

End FidelityMonoTPCPM.

End Dilation.
