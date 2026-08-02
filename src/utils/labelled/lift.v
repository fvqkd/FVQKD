(* -------------------------------------------------------------------- *)
(* lift.v — Ambient set-labelled lift adjunction helpers                *)
(* -------------------------------------------------------------------- *)
(* Module: utils.labelled.lift                            *)
(* TeX source: none (library utility)                                    *)
(* TeX labels: none                                                      *)
(* -------------------------------------------------------------------- *)
(* Owns the "LiftAdjunction" block — a family of labeled-lfun helpers    *)
(* expressing how the trivial A-tensor lift `(\1 : 'F_A) \O _` interacts *)
(* with trace, composition, support, adjoint, and schnorm.               *)
(* Used by lhl/prop.v (uniform_to_collision, privacy_amp).               *)
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
  cpo mxpred extnum ctopology svd mxnorm hspace hspace_extra orthomodular.
From quantum.dirac Require Import hstensor.

Import Order.TTheory GRing.Theory Num.Theory Num.Def MxLownerOrder.
Import VectorInternalTheory.

(* --- FVQKD imports --- *)
From utils.mx Require Import def prop.
From utils.labelled Require Import op sys.

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
(* Lift adjunction: partial-trace ↔ I_A ⊗ •                             *)
(* These lemmas close the partial-trace / lift duality at the scalar    *)
(* trace and lfun-composition levels.                                   *)
(* ================================================================== *)

(* ================================================================== *)
(* Helper lemmas                                                        *)
(* ================================================================== *)

Section LiftHelpers.
Variable (L : finType) (H : L -> chsType).

(* Helper: \O ↔ \⊗ conversion for disjoint sets.                       *)
(* path: utils:sdotF_to_tenF -> entropy:entropy_data_proc -> *)
(*   bb84:bb84_secret *)
Lemma sdotF_to_tenF (A B : {set L}) (disAB : [disjoint A & B])
    (f : 'F[H]_A) (g : 'F[H]_B) :
  (f \O g : 'F[H]_(A :|: B)) = f \⊗ g.
Proof.
  by apply: to_Fnd_inj; rewrite (sdotFT _ _ disAB) to_Fnd_tenE.
Qed.

Lemma h2mxZ_lf (A : {set L}) (c : C) (x : 'F[H]_A) :
  h2mx (c *: x) = c *: h2mx x.
Proof.
  have Hlin := @h2mxP R ('H[H]_A) ('H[H]_A).
  move: (Hlin c x 0).
  rewrite addr0 h2mx0 addr0.
  by move=> ->.
Qed.

(* Product partial trace over the right tensor factor.                   *)
(* math: Tr_B(x_A ⊗ y_B) = Tr(y_B) x_A.                                  *)
(* Consumers: ptrace_cast3B_sdot_mid and product-witness entropy bridges. *)
(* path: utils:ptrace_cast_sdot_trace_r -> utils:ptrace_cast3B_sdot_mid -> *)
(*   entropy:entropy_data_proc -> *)
(*   bb84:bb84_secret *)
Lemma ptrace_cast_sdot_trace_r (A B : {set L}) (disAB : [disjoint A & B])
    (x : 'F[H]_A) (y : 'F[H]_B) :
  ptrace_cast disAB (x \O y) = \Tr y *: x.
Proof.
  apply/h2mx_inj.
  rewrite h2mxZ_lf /= /lftrace.
  rewrite (sdotF_to_tenF disAB x y).
  rewrite (h2mx_ptrace_cast_ptrace2 disAB).
  rewrite h2mx_tenf.
  pose U := @tenv_mxU R L H A B.
  have HUadj : U^*t \is unitarymx := tenv_mxU_adj_unitarymx disAB.
  have HUadjU : U^*t *m U = 1%:M.
  { by have := unitarymxK HUadj; rewrite adjmxK. }
  rewrite -/U !mulmxA HUadjU mul1mx -mulmxA HUadjU mulmx1.
  by rewrite ptrace_tensmx.
Qed.

Fact ptrace_cast_linearZ (A B : {set L}) (disAB : [disjoint A & B])
    (c : C) (x : 'F[H]_(A :|: B)) :
  ptrace_cast disAB (c *: x) = c *: ptrace_cast disAB x.
Proof.
  rewrite /ptrace_cast /ptrace_cast_gen.
  rewrite [\Tr_(B) _]linearZ /=.
  by rewrite linearZ.
Qed.

Lemma ptrace_castl_linearZ (A B : {set L}) (disAB : [disjoint A & B])
    (c : C) (x : 'F[H]_(A :|: B)) :
  ptrace_castl disAB (c *: x) = c *: ptrace_castl disAB x.
Proof.
  rewrite /ptrace_castl /ptrace_cast_gen.
  rewrite [\Tr_(A) _]linearZ /=.
  by rewrite linearZ.
Qed.

Fact ptrace_cast3C_linearZ (A B C0 : {set L})
    (disAC : [disjoint A & C0]) (disBC : [disjoint B & C0])
    (c : C) (x : 'F[H]_(A :|: B :|: C0)) :
  ptrace_cast3C disAC disBC (c *: x) =
    c *: ptrace_cast3C disAC disBC x.
Proof.
  rewrite /ptrace_cast3C /ptrace_cast_gen.
  rewrite [\Tr_(C0) _]linearZ /=.
  by rewrite linearZ.
Qed.

(* Middle-register product partial trace.                                *)
(* math: Tr_B(x_AB ⊗ y_C) = Tr_B(x_AB) ⊗ y_C.                            *)
(* path: utils:ptrace_cast3B_sdot_mid -> entropy:entropy_data_proc -> *)
(*   bb84:bb84_secret *)
Lemma ptrace_cast3B_sdot_mid (A B C0 : {set L})
    (disAB : [disjoint A & B]) (disBC : [disjoint B & C0])
    (disAC : [disjoint A & C0])
    (x : 'F[H]_(A :|: B)) (y : 'F[H]_C0) :
  ptrace_cast3B disAB disBC ((x \O y) : 'F[H]_(A :|: B :|: C0)) =
  ((ptrace_cast disAB x) \O y : 'F[H]_(A :|: C0)).
Proof.
  have disCB : [disjoint C0 & B] by rewrite disjoint_sym.
  have disAC_B : [disjoint A :|: C0 & B]
    by rewrite disjointUX disAB disCB.
  set eqS := setUC_swap3 A B C0 : A :|: B :|: C0 = A :|: C0 :|: B.
  have Hrecast (f : 'F[H]_(A :|: B :|: C0)) :
      ptrace_cast3B disAB disBC f =
      ptrace_cast disAC_B (castlf (eqS, eqS) f).
  { rewrite /ptrace_cast3B /ptrace_cast /ptrace_cast_gen.
    have eq_res :
        (A :|: B :|: C0) :\: B = (A :|: C0 :|: B) :\: B
      by rewrite eqS.
    rewrite (ptracelf_castlf_eq eqS eq_res).
    rewrite castlf_comp.
    by congr (castlf (_, _) _); exact: eq_irrelevance. }
  have Hbasis (i j : 'Idx[H]_(A :|: B)) :
      ptrace_cast3B disAB disBC
        (([> deltav i ; deltav j <] \O y) :
          'F[H]_(A :|: B :|: C0)) =
      (ptrace_cast disAB [> deltav i ; deltav j <] \O y :
        'F[H]_(A :|: C0)).
  { pose xA : 'F[H]_A := [> deltav (idxSl i) ; deltav (idxSl j) <].
    pose xB : 'F[H]_B := [> deltav (idxSr i) ; deltav (idxSr j) <].
    have Hx_split :
        [> deltav i ; deltav j <] =
        (xA \O xB : 'F[H]_(A :|: B)).
    { apply: to_Fnd_inj.
      by rewrite /xA /xB !dv_split -tenf_outp to_Fnd_tenE
        (sdotFT _ _ disAB). }
    have Hcast_mid :
        castlf (eqS, eqS)
          (((xA \O xB) \O y) : 'F[H]_(A :|: B :|: C0)) =
        (((xA \O y) \O xB) : 'F[H]_(A :|: C0 :|: B)).
    { apply: to_Fnd_inj.
      rewrite Fnd_cast !to_Fnd_sdotE.
      rewrite -!dotFsA //.
      by rewrite (@dotFC R L H (to_Fnd xB) (to_Fnd y)) ?disBC ?disCB. }
    rewrite Hrecast Hx_split Hcast_mid ptrace_cast_sdot_trace_r.
    by rewrite ptrace_cast_sdot_trace_r sdotfZl. }
  have Hptr3B_sum (I0 : finType) (P : pred I0)
      (F : I0 -> 'F[H]_(A :|: B :|: C0)) :
      ptrace_cast3B disAB disBC (\sum_(i | P i) F i) =
      \sum_(i | P i) ptrace_cast3B disAB disBC (F i).
  { rewrite /ptrace_cast3B /ptrace_cast_gen.
    rewrite [\Tr_(B) _]raddf_sum /=.
    by rewrite raddf_sum. }
  have Hptr_sum (I0 : finType) (P : pred I0)
      (F : I0 -> 'F[H]_(A :|: B)) :
      ptrace_cast disAB (\sum_(i | P i) F i) =
      \sum_(i | P i) ptrace_cast disAB (F i).
  { rewrite /ptrace_cast /ptrace_cast_gen.
    rewrite [\Tr_(B) _]raddf_sum /=.
    by rewrite raddf_sum. }
  have Hptr3B_Z (c : C) (z : 'F[H]_(A :|: B :|: C0)) :
      ptrace_cast3B disAB disBC (c *: z) =
      c *: ptrace_cast3B disAB disBC z.
  { rewrite /ptrace_cast3B /ptrace_cast_gen.
    rewrite [\Tr_(B) _]linearZ /=.
    by rewrite linearZ. }
  have Hptr_Z (c : C) (z : 'F[H]_(A :|: B)) :
      ptrace_cast disAB (c *: z) =
      c *: ptrace_cast disAB z.
  { rewrite /ptrace_cast /ptrace_cast_gen.
    rewrite [\Tr_(B) _]linearZ /=.
    by rewrite linearZ. }
  rewrite [x in ptrace_cast3B _ _ (x \O y)](onb_lfun2id deltav x).
  rewrite [x in (ptrace_cast _ x \O y)](onb_lfun2id deltav x).
  rewrite sdotf_suml Hptr3B_sum Hptr_sum sdotf_suml /=.
  apply: eq_bigr=> i _.
  rewrite sdotf_suml Hptr3B_sum Hptr_sum sdotf_suml /=.
  apply: eq_bigr=> j _.
  by rewrite sdotfZl Hptr3B_Z Hptr_Z sdotfZl Hbasis.
Qed.

(* Right-register product partial trace.                                 *)
(* math: Tr_C(x_A ⊗ y_BC) = x_A ⊗ Tr_C(y_BC).                            *)
(* path: utils:ptrace_cast3C_sdot_right -> entropy:entropy_data_proc -> *)
(*   bb84:bb84_secret *)
Lemma ptrace_cast3C_sdot_right (A B C0 : {set L})
    (disAB : [disjoint A & B]) (disAC : [disjoint A & C0])
    (disBC : [disjoint B & C0])
    (x : 'F[H]_A) (y : 'F[H]_(B :|: C0)) :
  ptrace_cast3C disAC disBC
    (castlf (finset.setUA A B C0, finset.setUA A B C0)
      ((x \O y) : 'F[H]_(A :|: (B :|: C0)))) =
  (x \O ptrace_cast disBC y : 'F[H]_(A :|: B)).
Proof.
  have disAB_C : [disjoint A :|: B & C0]
    by rewrite disjointUX disAC disBC.
  have HtraceC (f : 'F[H]_(A :|: B :|: C0)) :
      ptrace_cast3C disAC disBC f = ptrace_cast disAB_C f.
  { rewrite /ptrace_cast3C /ptrace_cast /ptrace_cast_gen.
    have Hdu : setDU3_C disAC disBC = setDU_r disAB_C
      := eq_irrelevance _ _.
    by rewrite Hdu. }
  have Hbasis (i j : 'Idx[H]_(B :|: C0)) :
      ptrace_cast3C disAC disBC
        (castlf (finset.setUA A B C0, finset.setUA A B C0)
          ((x \O [> deltav i ; deltav j <]) :
            'F[H]_(A :|: (B :|: C0)))) =
      (x \O ptrace_cast disBC [> deltav i ; deltav j <] :
        'F[H]_(A :|: B)).
  { pose yB : 'F[H]_B := [> deltav (idxSl i) ; deltav (idxSl j) <].
    pose yC : 'F[H]_C0 := [> deltav (idxSr i) ; deltav (idxSr j) <].
    have Hy_split :
        [> deltav i ; deltav j <] =
        (yB \O yC : 'F[H]_(B :|: C0)).
    { apply: to_Fnd_inj.
      by rewrite /yB /yC !dv_split -tenf_outp to_Fnd_tenE
        (sdotFT _ _ disBC). }
    have Hassoc :
        castlf (finset.setUA A B C0, finset.setUA A B C0)
          ((x \O (yB \O yC)) : 'F[H]_(A :|: (B :|: C0))) =
        (((x \O yB) \O yC) : 'F[H]_(A :|: B :|: C0)).
    { apply: to_Fnd_inj.
      by rewrite Fnd_cast !to_Fnd_sdotE -!dotFsA // disjointXU disAB disAC. }
    rewrite Hy_split HtraceC Hassoc ptrace_cast_sdot_trace_r.
    by rewrite ptrace_cast_sdot_trace_r sdotfZr. }
  have Hptr3C_sum (I0 : finType) (P : pred I0)
      (F : I0 -> 'F[H]_(A :|: B :|: C0)) :
      ptrace_cast3C disAC disBC (\sum_(i | P i) F i) =
      \sum_(i | P i) ptrace_cast3C disAC disBC (F i).
  { rewrite /ptrace_cast3C /ptrace_cast_gen.
    rewrite [\Tr_(C0) _]raddf_sum /=.
    by rewrite raddf_sum. }
  have Hptr_sum (I0 : finType) (P : pred I0)
      (F : I0 -> 'F[H]_(B :|: C0)) :
      ptrace_cast disBC (\sum_(i | P i) F i) =
      \sum_(i | P i) ptrace_cast disBC (F i).
  { rewrite /ptrace_cast /ptrace_cast_gen.
    rewrite [\Tr_(C0) _]raddf_sum /=.
    by rewrite raddf_sum. }
  have Hptr3C_Z (c : C) (z : 'F[H]_(A :|: B :|: C0)) :
      ptrace_cast3C disAC disBC (c *: z) =
      c *: ptrace_cast3C disAC disBC z.
  { rewrite /ptrace_cast3C /ptrace_cast_gen.
    rewrite [\Tr_(C0) _]linearZ /=.
    by rewrite linearZ. }
  have Hptr_Z (c : C) (z : 'F[H]_(B :|: C0)) :
      ptrace_cast disBC (c *: z) =
      c *: ptrace_cast disBC z.
  { rewrite /ptrace_cast /ptrace_cast_gen.
    rewrite [\Tr_(C0) _]linearZ /=.
    by rewrite linearZ. }
  rewrite [y in castlf _ (x \O y)](onb_lfun2id deltav y).
  rewrite [y in (_ \O ptrace_cast _ y)](onb_lfun2id deltav y).
  rewrite sdotf_sumr linear_sum Hptr3C_sum Hptr_sum sdotf_sumr /=.
  apply: eq_bigr=> i _.
  rewrite sdotf_sumr linear_sum Hptr3C_sum Hptr_sum sdotf_sumr /=.
  apply: eq_bigr=> j _.
  by rewrite sdotfZr linearZ Hptr3C_Z Hptr_Z sdotfZr Hbasis.
Qed.

(* path: utils:lef_sdotfr -> entropy:smooth_hmax_labelled_mx -> bb84:stat -> *)
(*   bb84:bb84_secret *)
Lemma lef_sdotfr (A B : {set L}) (disAB : [disjoint A & B])
    (g : 'F[H]_A) (f1 f2 : 'F[H]_B) :
  (0 : 'F[H]_A) <= g -> f1 <= f2 -> g \O f1 <= g \O f2.
Proof.
  move=> Pg Hf.
  rewrite (sdotF_to_tenF disAB g f1).
  rewrite (sdotF_to_tenF disAB g f2).
  exact: lef_tenfr.
Qed.

(* path: utils:tenso_sdot_correct -> eur:ucr_pure_smooth -> *)
(*   eur:entropic_uncertainty_relation -> *)
(*   eur:entropic_uncertainty_relation -> *)
(*   bb84:entropic_uncertainty_relation_bb84 -> bb84:bb84_secret *)
Lemma tenso_sdot_correct (A A' B B' : {set L})
    (disAB : [disjoint A & B]) (disA'B' : [disjoint A' & B'])
    (E : 'SO[H]_(A, A')) (F : 'SO[H]_(B, B'))
    (x : 'F[H]_A) (y : 'F[H]_B) :
  (E :⊗ F) (x \O y) = E x \O F y.
Proof.
  rewrite (sdotF_to_tenF disAB x y).
  rewrite (sdotF_to_tenF disA'B' (E x) (F y)).
  exact: esym (tenso_correct E F disAB x y).
Qed.

(* Helper: matrix-level partial-trace adjunction.                       *)
(* For any matrix M : 'M_(m*n) and Y : 'M_n,                            *)
(* mxtrace (M *m (1%:M *t Y)) = mxtrace (ptrace1 M *m Y).               *)
(* path: utils:mxtrace_lift_partial_mx -> utils:trlf_lift_partial -> *)
(*   lhl:post_hash_ptrace_Z_CQ -> bb84:privacy_amplification -> *)
(*   bb84:bb84_secret *)
Lemma mxtrace_lift_partial_mx (m n : nat) (M : 'M[C]_(m * n)) (Y : 'M[C]_n) :
  \tr (M *m (1%:M *t Y)) = \tr (ptrace1 M *m Y).
Proof.
  by rewrite tr_ptrace1 ptrace1_mulmxI.
Qed.

(* Companion matrix adjunction for tracing out the right tensor factor. *)
(* path: utils:mxtrace_lift_partial_mx_r -> utils:trlf_lift_partial_r -> *)
(*   entropy:entropy_data_proc -> *)
(*   bb84:bb84_secret *)
Lemma mxtrace_lift_partial_mx_r (m n : nat) (M : 'M[C]_(m * n))
    (X : 'M[C]_m) :
  \tr (M *m (X *t 1%:M)) = \tr (ptrace2 M *m X).
Proof.
  by rewrite tr_ptrace2 ptrace2_mulmxI.
Qed.

End LiftHelpers.

(* ================================================================== *)
(* Helper: matrix bridge for ptrace_castl (mirror of                    *)
(* h2mx_ptrace_cast_ptrace2 from sys.v, but for the trace-over-A        *)
(* direction returning 'F_B).                                           *)
(* Consumers: trlf_lift_partial, ptrace_supph_lift, and matrix-level    *)
(* ptrace_castl work.                                                   *)
(* ================================================================== *)

Section LiftHelperPtraceCastl.
Variable (L : finType) (HL : L -> chsType) (A B : {set L}).
Hypothesis disAB : [disjoint A & B].

Let S_AB := (A :|: B).

(* Entry-wise formula for h2mx (ptrace_castl disAB rho).                       *)
(* Mirror of h2mx_ptrace_cast_dec but over 'Idx_A (sum) with (i,j)             *)
(* placed first in idxU (since ptrace_castl returns 'F_B).                    *)
(* path: utils:h2mx_ptrace_castl_dec -> utils:h2mx_ptrace_castl_ptrace1 -> *)
(*   utils:trlf_lift_partial -> lhl:post_hash_ptrace_Z_CQ -> *)
(*   bb84:privacy_amplification -> bb84:bb84_secret *)
Lemma h2mx_ptrace_castl_dec (rho : 'F[HL]_S_AB)
    (i j : 'I_(dim 'H[HL]_B)) :
  h2mx (ptrace_castl disAB rho) i j =
  \sum_(k : 'Idx[HL]_(S_AB :&: A))
    [< deltav (idxU k (castidx (esym (setDU_l disAB)) (n2i i))) ;
       castlf (esym (setID S_AB A), esym (setID S_AB A)) rho
         (deltav (idxU k (castidx (esym (setDU_l disAB)) (n2i j)))) >].
Proof.
  rewrite /ptrace_castl /ptrace_cast_gen h2mx_dec.
  have eb_dv : forall (x : 'I_(dim 'H[HL]_B)),
    eb x = deltav (n2i x) :> 'H[HL]_B.
  { by move=> x; rewrite deltav.unlock n2iK. }
  rewrite !eb_dv.
  rewrite castlfE casths_dotr !deltav_cast.
  set b1 := castidx _ (n2i i).
  set b2 := castidx _ (n2i j).
  rewrite /ptraceso {1}/fun_of_superof/= lfunE/=.
  rewrite ptraceso_fun.unlock.
  rewrite sum_lfunE dotp_sumr; apply: eq_bigr => k _.
  rewrite sum_lfunE dotp_sumr.
  under eq_bigr => i0 _.
    rewrite sum_lfunE dotp_sumr.
    under eq_bigr => j0 _.
      rewrite scale_lfunE outpE dotpZr dotpZr dv_dot dv_dot.
      over.
    over.
  simpl.
  under eq_bigr => i0 _.
    rewrite (bigD1 b2)//= eqxx mul1r big1 ?addr0.
    2: by move=> j0 /negPf ->; rewrite mul0r mulr0.
    over.
  simpl.
  rewrite (bigD1 b1)//= eqxx mulr1 big1 ?addr0//.
  by move=> i0 /negPf ni0; rewrite [b1 == i0]eq_sym ni0 mulr0.
Qed.

(* Matrix-side analog: ptrace1 of tenv_mxU-conjugated h2mx rho, entrywise. *)
(* Mirror of ptrace2_tenv_mxU_conj_dec from sys.v but for ptrace1.        *)
(* path: utils:ptrace1_tenv_mxU_conj_dec -> utils:h2mx_ptrace_castl_ptrace1 -> *)
(*   utils:trlf_lift_partial -> lhl:post_hash_ptrace_Z_CQ -> *)
(*   bb84:privacy_amplification -> bb84:bb84_secret *)
Lemma ptrace1_tenv_mxU_conj_dec (rho : 'F[HL]_S_AB)
    (i j : 'I_(dim 'H[HL]_B)) :
  ptrace1 ((@tenv_mxU R L HL A B)^*t *m h2mx rho *m
           (@tenv_mxU R L HL A B)) i j =
  \sum_(k : 'I_(dim 'H[HL]_A))
    [< deltav (idxU (n2i k) (n2i i)) ;
       rho (deltav (idxU (n2i k) (n2i j))) >].
Proof.
  rewrite ptrace1E.
  apply: eq_bigr => k _.
  rewrite mxE (bigD1 (tenv_indexl (mxtens_index (k, j))))//= big1 ?addr0.
  2: {
    move=> q Hq.
    rewrite !mxE /= (can2_eq (@tenv_indexrK R L HL A B) (tenv_indexlK disAB)).
    by rewrite (negPf Hq) !mulr0.
  }
  rewrite mxE (bigD1 (tenv_indexl (mxtens_index (k, i))))//= big1 ?addr0.
  2: {
    move=> p Hp.
    rewrite adjmxE !mxE.
    rewrite (can2_eq (@tenv_indexrK R L HL A B) (tenv_indexlK disAB)).
    by rewrite (negPf Hp) conjC0 !mul0r.
  }
  rewrite adjmxE !mxE.
  rewrite (tenv_indexlK disAB) (tenv_indexlK disAB) !eqxx !mulr1 conjC1.
  rewrite mul1r /tenv_indexl !mxtens_indexK/=.
  rewrite h2mx_dec.
  have eb_dv : forall S (x : 'Idx[HL]_S),
    eb (i2n x) = deltav x :> 'H[HL]_S.
  { by move=> S x; rewrite deltav.unlock. }
  by rewrite !eb_dv.
Qed.

(* Index identity bridging the LHS cast chain (setID + setDU_l + eqIA) and *)
(* the canonical A-first / B-second idxU ordering on S_AB = A :|: B.        *)
(* Mirror of castidx_setID_idxU_eq from sys.v but for the A side.          *)
(* path: utils:castidx_setID_idxU_eq_l -> utils:h2mx_ptrace_castl_ptrace1 -> *)
(*   utils:trlf_lift_partial -> lhl:post_hash_ptrace_Z_CQ -> *)
(*   bb84:privacy_amplification -> bb84:bb84_secret *)
Lemma castidx_setID_idxU_eq_l
    (eqIA : S_AB :&: A = A)
    (k : 'I_(dim 'H[HL]_A))
    (i : 'I_(dim 'H[HL]_B)) :
  castidx (setID S_AB A)
    (idxU (castidx (esym eqIA) (n2i k))
          (castidx (esym (setDU_l disAB)) (n2i i)))
  = idxU (n2i k) (n2i i).
Proof.
  apply/idxP => x.
  rewrite castidx_app /= idxE.
  have Hx_in : val x \in S_AB by case: x => /= ?.
  case: eqP => HA.
  - rewrite castidx_app /=.
    have HA' : val x \in A by move/setIP: HA => [].
    rewrite idxE.
    case: eqP => HAr; last by case: (HAr HA').
    exact: n2i_exist_irr.
  - rewrite castidx_app /=.
    have HnA : (val x \in A) = false.
      by apply/negP => HA'; apply: HA; rewrite inE Hx_in HA'.
    have HB : val x \in B.
      have Hx2 := Hx_in.
      rewrite finset.in_setU in Hx2.
      case/orP: Hx2 => [HxA | //].
      by rewrite HxA in HnA.
    rewrite idxE.
    case: eqP => HAr; first by rewrite HAr in HnA.
    exact: n2i_exist_irr.
Qed.

(* Full bridge: labeled ptrace_castl ↔ matrix ptrace1 via tenv_mxU conjugation. *)
(* path: utils:h2mx_ptrace_castl_ptrace1 -> utils:trlf_lift_partial -> *)
(*   lhl:post_hash_ptrace_Z_CQ -> bb84:privacy_amplification -> *)
(*   bb84:bb84_secret *)
Lemma h2mx_ptrace_castl_ptrace1 (rho : 'F[HL]_S_AB) :
  h2mx (ptrace_castl disAB rho) =
  ptrace1 ((@tenv_mxU R L HL A B)^*t *m h2mx rho *m
           (@tenv_mxU R L HL A B)).
Proof.
  apply/matrixP => i j.
  rewrite h2mx_ptrace_castl_dec ptrace1_tenv_mxU_conj_dec.
  have eqIA : S_AB :&: A = A.
  {
    by have /finset.setIidPr-> := @finset.subsetUl _ A B.
  }
  rewrite (reindex (fun k : 'I_(dim 'H[HL]_A) =>
    castidx (esym eqIA) (n2i k))) /=.
  2: {
    exists (fun k : 'Idx[HL]_(S_AB :&: A) =>
      i2n (castidx eqIA k)) => k _.
    - by rewrite castidx_comp (eq_irrelevance (etrans _ _) (erefl _)) castidx_id n2iK.
    - by rewrite i2nK castidx_comp (eq_irrelevance (etrans _ _) (erefl _)) castidx_id.
  }
  apply: eq_bigr => k _.
  rewrite castlfE casths_dotr !deltav_cast esymK.
  by rewrite !(castidx_setID_idxU_eq_l eqIA).
Qed.

End LiftHelperPtraceCastl.

Section LiftHelperPtraceCastlProduct.
Variable (L : finType) (H : L -> chsType).

(* Product partial trace over the left tensor factor.                    *)
(* math: Tr_A(x_A ⊗ y_B) = Tr(x_A) y_B.                                  *)
(* Consumers: ptrace_cast3B_sdot_right and tensor-product entropy        *)
(* feasibility bridges.                                                  *)
(* path: utils:ptrace_castl_sdot_trace_l -> utils:ptrace_cast3B_sdot_right -> *)
(*   entropy:minmax_dual -> entropy:smooth_iso_hmax -> *)
(*   entropy:entropy_data_proc -> *)
(*   bb84:bb84_secret *)
Lemma ptrace_castl_sdot_trace_l (A B : {set L}) (disAB : [disjoint A & B])
    (x : 'F[H]_A) (y : 'F[H]_B) :
  ptrace_castl disAB (x \O y) = \Tr x *: y.
Proof.
  apply/h2mx_inj.
  rewrite h2mxZ_lf /= /lftrace.
  rewrite (h2mx_ptrace_castl_ptrace1 disAB).
  rewrite (sdotF_to_tenF disAB x y).
  rewrite h2mx_tenf.
  pose U := @tenv_mxU R L H A B.
  have HUadj : U^*t \is unitarymx := tenv_mxU_adj_unitarymx disAB.
  have HUadjU : U^*t *m U = 1%:M.
  { by have := unitarymxK HUadj; rewrite adjmxK. }
  rewrite -/U !mulmxA HUadjU mul1mx -mulmxA HUadjU mulmx1.
  by rewrite ptrace1_tensmx.
Qed.

Fact ptrace_castl_sub (A B : {set L}) (disAB : [disjoint A & B])
    (x y : 'F[H]_(A :|: B)) :
  ptrace_castl disAB (x - y) =
  ptrace_castl disAB x - ptrace_castl disAB y.
Proof.
  rewrite /ptrace_castl /ptrace_cast_gen.
  rewrite -[x - y]/(x + - y).
  rewrite addrC -scaleN1r.
  rewrite [\Tr_(A) ((-1 : C) *: y + x)]linearP /=.
  rewrite [castlf _ ((-1 : C) *: _ + _)]linearP /=.
  by rewrite !scaleN1r addrC.
Qed.

End LiftHelperPtraceCastlProduct.

Section LiftHelperPtraceCast3B.
Variable (L : finType) (H : L -> chsType).

(* path: utils:h2mx_castlf -> entropy:entropy_data_proc -> *)
(*   bb84:bb84_secret *)
Lemma h2mx_castlf (S S' : {set L}) (eqSS' : S = S') (f : 'F[H]_S) :
  h2mx (castlf (eqSS', eqSS') f) =
  castmx (f_equal (fun T => dim 'H[H]_T) eqSS',
          f_equal (fun T => dim 'H[H]_T) eqSS') (h2mx f).
Proof.
  case: S' / eqSS' in f *.
  by rewrite castlf_id castmx_id.
Qed.

Variables (A B C0 : {set L}).
Hypothesis disAB : [disjoint A & B].
Hypothesis disBC : [disjoint B & C0].
Hypothesis disAC : [disjoint A & C0].

Let disAB_C : [disjoint A :|: B & C0].
Proof.
  by rewrite disjointUX disAC disBC.
Defined.

Let disAC_B : [disjoint A :|: C0 & B].
Proof.
  have disCB : [disjoint C0 & B] by rewrite disjoint_sym.
  by rewrite disjointUX disAB disCB.
Defined.

(* Middle-register product partial trace, right-block form.              *)
(* math: Tr_B(x_A ⊗ y_BC) = x_A ⊗ Tr_B(y_BC).                            *)
(* path: utils:ptrace_cast3B_sdot_right -> entropy:minmax_dual -> *)
(*   entropy:smooth_iso_hmax -> entropy:entropy_data_proc -> *)
(*   bb84:bb84_secret *)
Lemma ptrace_cast3B_sdot_right (x : 'F[H]_A) (y : 'F[H]_(B :|: C0)) :
  ptrace_cast3B disAB disBC
    (castlf (finset.setUA A B C0, finset.setUA A B C0)
      ((x \O y) : 'F[H]_(A :|: (B :|: C0)))) =
  (x \O ptrace_castl disBC y : 'F[H]_(A :|: C0)).
Proof.
  have Hbasis (i j : 'Idx[H]_(B :|: C0)) :
      ptrace_cast3B disAB disBC
        (castlf (finset.setUA A B C0, finset.setUA A B C0)
          ((x \O [> deltav i ; deltav j <]) :
            'F[H]_(A :|: (B :|: C0)))) =
      (x \O ptrace_castl disBC [> deltav i ; deltav j <] :
        'F[H]_(A :|: C0)).
  { pose yB : 'F[H]_B := [> deltav (idxSl i) ; deltav (idxSl j) <].
    pose yC : 'F[H]_C0 := [> deltav (idxSr i) ; deltav (idxSr j) <].
    have Hy_split :
        [> deltav i ; deltav j <] =
        (yB \O yC : 'F[H]_(B :|: C0)).
    { apply: to_Fnd_inj.
      by rewrite /yB /yC !dv_split -tenf_outp to_Fnd_tenE
        (sdotFT _ _ disBC). }
    have Hassoc :
        castlf (finset.setUA A B C0, finset.setUA A B C0)
          ((x \O (yB \O yC)) : 'F[H]_(A :|: (B :|: C0))) =
        (((x \O yB) \O yC) : 'F[H]_(A :|: B :|: C0)).
    { apply: to_Fnd_inj.
      by rewrite Fnd_cast !to_Fnd_sdotE -!dotFsA // disjointXU disAB disAC. }
    rewrite Hy_split Hassoc (ptrace_cast3B_sdot_mid disAB disBC disAC).
    by rewrite (ptrace_cast_sdot_trace_r disAB)
      (ptrace_castl_sdot_trace_l disBC) sdotfZl sdotfZr. }
  have Hptr3B_sum (I0 : finType) (P : pred I0)
      (F : I0 -> 'F[H]_(A :|: B :|: C0)) :
      ptrace_cast3B disAB disBC (\sum_(i | P i) F i) =
      \sum_(i | P i) ptrace_cast3B disAB disBC (F i).
  { rewrite /ptrace_cast3B /ptrace_cast_gen.
    rewrite [\Tr_(B) _]raddf_sum /=.
    by rewrite raddf_sum. }
  have Hptr_l_sum (I0 : finType) (P : pred I0)
      (F : I0 -> 'F[H]_(B :|: C0)) :
      ptrace_castl disBC (\sum_(i | P i) F i) =
      \sum_(i | P i) ptrace_castl disBC (F i).
  { rewrite /ptrace_castl /ptrace_cast_gen.
    rewrite [\Tr_(B) _]raddf_sum /=.
    by rewrite raddf_sum. }
  have Hptr3B_Z (c : C) (z : 'F[H]_(A :|: B :|: C0)) :
      ptrace_cast3B disAB disBC (c *: z) =
      c *: ptrace_cast3B disAB disBC z.
  { rewrite /ptrace_cast3B /ptrace_cast_gen.
    rewrite [\Tr_(B) _]linearZ /=.
    by rewrite linearZ. }
  have Hptr_l_Z (c : C) (z : 'F[H]_(B :|: C0)) :
      ptrace_castl disBC (c *: z) =
      c *: ptrace_castl disBC z.
  { rewrite /ptrace_castl /ptrace_cast_gen.
    rewrite [\Tr_(B) _]linearZ /=.
    by rewrite linearZ. }
  rewrite [y in castlf _ (x \O y)](onb_lfun2id deltav y).
  rewrite [y in (_ \O ptrace_castl _ y)](onb_lfun2id deltav y).
  rewrite sdotf_sumr linear_sum Hptr3B_sum Hptr_l_sum sdotf_sumr /=.
  apply: eq_bigr=> i _.
  rewrite sdotf_sumr linear_sum Hptr3B_sum Hptr_l_sum sdotf_sumr /=.
  apply: eq_bigr=> j _.
  by rewrite sdotfZr linearZ Hptr3B_Z Hptr_l_Z sdotfZr Hbasis.
Qed.

(* path: utils:ptr_cast3B_ten_mid -> entropy:smooth_hmax_labelled_mx -> *)
(*   bb84:stat -> bb84:bb84_secret *)
Lemma ptr_cast3B_ten_mid (x : 'F[H]_(A :|: B)) (y : 'F[H]_C0) :
  ptrace_cast3B disAB disBC
    ((x \⊗ y) : 'F[H]_(A :|: B :|: C0)) =
  ((ptrace_cast disAB x) \⊗ y : 'F[H]_(A :|: C0)).
Proof.
  rewrite -[x \⊗ y](sdotF_to_tenF disAB_C x y).
  rewrite -[(ptrace_cast disAB x) \⊗ y]
    (sdotF_to_tenF disAC (ptrace_cast disAB x) y).
  exact: ptrace_cast3B_sdot_mid.
Qed.

(* path: utils:ptr_cast3B_sdot_mid -> entropy:smooth_hmax_labelled_mx -> *)
(*   bb84:stat -> bb84:bb84_secret *)
Lemma ptr_cast3B_sdot_mid (x : 'F[H]_(A :|: B)) (y : 'F[H]_C0) :
  ptrace_cast3B disAB disBC ((x \O y) : 'F[H]_(A :|: B :|: C0)) =
  ((ptrace_cast disAB x) \O y : 'F[H]_(A :|: C0)).
Proof.
  rewrite (sdotF_to_tenF disAB_C x y).
  rewrite (sdotF_to_tenF disAC (ptrace_cast disAB x) y).
  exact: ptr_cast3B_ten_mid.
Qed.

End LiftHelperPtraceCast3B.

Section LiftAdjunction.
Variable (L : finType) (H : L -> chsType).

(* Partial-trace adjunction at the scalar trace level.                 *)
(* math: Tr(f · (I_A ⊗ X)) = Tr(ρ_B · X) where ρ_B = Tr_A f.          *)
(* Consumers (≥2): uniform_to_collision (LHL Lem 4), privacy_amp. *)
(* trlf_lift_partial *)
(* infra: no tex label — fundamental & reusable (mathcomp-style) *)
(* consumer: trlf_lift_partial is used downstream by the BB84 secrecy proof. *)
(* path: utils:trlf_lift_partial -> lhl:post_hash_ptrace_Z_CQ -> *)
(*   bb84:privacy_amplification -> bb84:bb84_secret *)
Lemma trlf_lift_partial (A B : {set L}) (disAB : [disjoint A & B])
    (f : 'F[H]_(A :|: B)) (X : 'F[H]_B) :
  \Tr (f \o ((\1 : 'F_A) \O X)) = \Tr (ptrace_castl disAB f \o X).
Proof.
  rewrite (sdotF_to_tenF disAB).
  rewrite /lftrace !h2mx_comp h2mx_tenf h2mx1.
  rewrite [in RHS](h2mx_ptrace_castl_ptrace1 disAB f).
  rewrite -mxtrace_lift_partial_mx.
  rewrite !mulmxA.
  by rewrite [LHS]mxtrace_mulC !mulmxA.
Qed.

(* Partial-trace adjunction for tracing out the right tensor factor.    *)
(* math: Tr(f · (X_A ⊗ I_B)) = Tr(ρ_A · X_A), where ρ_A = Tr_B f.     *)
(* trlf_lift_partial_r *)
(* infra: no tex label — fundamental & reusable (mathcomp-style) *)
(* path: utils:trlf_lift_partial_r -> entropy:entropy_data_proc -> *)
(*   bb84:bb84_secret *)
Lemma trlf_lift_partial_r (A B : {set L}) (disAB : [disjoint A & B])
    (f : 'F[H]_(A :|: B)) (X : 'F[H]_A) :
  \Tr (f \o (X \O (\1 : 'F_B))) = \Tr (ptrace_cast disAB f \o X).
Proof.
  rewrite (sdotF_to_tenF disAB).
  rewrite /lftrace !h2mx_comp h2mx_tenf h2mx1.
  rewrite [in RHS](h2mx_ptrace_cast_ptrace2 disAB f).
  rewrite -mxtrace_lift_partial_mx_r.
  rewrite !mulmxA.
  by rewrite [LHS]mxtrace_mulC !mulmxA.
Qed.

(* Support-cancellation lifted through I_A ⊗ •.                         *)
(* math: supp X ⊑ supp τ ⇒ I_A ⊗ (√τ · (√τ)⁺ · X) = I_A ⊗ X.          *)
(* Consumers (≥2): uniform_to_collision (LHL Lem 4), privacy_amp.   *)
(* liftf_supp_pinv *)
(* infra: no tex label — fundamental & reusable (mathcomp-style) *)
(* consumer: liftf_supp_pinv is used downstream by the BB84 secrecy proof. *)
(* Foundational helpers: kerh/supph identities for psd via sqrtHK + dot. *)

(* For psd tau: ker(sqrtH tau) = ker(tau).  Math: sqrtHK gives           *)
(* tau = sqrtH tau \o sqrtH tau, and ker X^2 = ker X for hermitian X    *)
(* via psdf_dot_eq0P + adj_dotEr.                                         *)
(* path: utils:kerh_sqrtH_psd -> utils:supph_sqrtH_psd -> *)
(*   utils:lift_supph_sandwich_quarter -> lhl:uniform_collision_bound -> *)
(*   bb84:privacy_amplification -> bb84:bb84_secret *)
Lemma kerh_sqrtH_psd (B : {set L}) (T : 'F[H]_B) :
  T \is psdlf -> kerh (sqrtH T) = kerh T.
Proof.
  move=> PT.
  set P := sqrtH T.
  have PP : P \is psdlf := sqrtH_psd PT.
  have PPh : P \is hermlf := psdlf_herm PP.
  apply/eqhP=> u.
  rewrite !memh_kerE.
  apply/eqb_iff; split=> /eqP HE; apply/eqP.
    by rewrite -(sqrtHK PT) comp_lfunE HE linear0.
  (* HE : T u = 0.  T = P \o P (sqrtHK).  So P (P u) = 0.
     Show P u ∈ supph P (via memh_suppP using P^A = P), AND P u ∈ kerh P
     (since P (P u) = 0).  These intersect at 0 by capOh.  Hence P u = 0. *)
  have HPPu : P (P u) = 0.
    have := HE; rewrite -(sqrtHK PT) -/P comp_lfunE => ->.
    by [].
  have HPu_in_kerh : P u \in kerh P by rewrite memh_kerE HPPu eqxx.
  have HPu_in_supph : P u \in supph P.
    apply/memh_suppP; exists u; by rewrite (hermlf_adjE PPh).
  have HPu_eq0 : P u = 0.
    apply/eqP; rewrite -dotp_eq0.
    have ->: [< P u; P u >] = [< u; P (P u) >].
      by rewrite -adj_dotEr (hermlf_adjE PPh).
    by rewrite HPPu linear0.
  by rewrite HPu_eq0.
Qed.

(* For psd tau: supph(sqrtH tau) = supph tau, by complementing kerh. *)
(* path: utils:supph_sqrtH_psd -> utils:lift_supph_sandwich_quarter -> *)
(*   lhl:uniform_collision_bound -> *)
(*   bb84:privacy_amplification -> bb84:bb84_secret *)
Lemma supph_sqrtH_psd (B : {set L}) (T : 'F[H]_B) :
  T \is psdlf -> supph (sqrtH T) = supph T.
Proof.
  by move=> PT; rewrite !supphE kerh_sqrtH_psd.
Qed.

(* For hermitian A: supph A = cosupph A (standard). *)
(* path: utils:supph_eq_cosupph_hermlf -> utils:cosupplf_compr_hermlf -> *)
(*   utils:lift_supph_sandwich_quarter -> lhl:uniform_collision_bound -> *)
(*   bb84:privacy_amplification -> bb84:bb84_secret *)
Lemma supph_eq_cosupph_hermlf (B : {set L}) (A : 'F[H]_B) :
  A \is hermlf -> supph A = cosupph A.
Proof.
  by move=> Hh; rewrite -[in LHS](hermlf_adjE Hh) supph_adj.
Qed.

(* Foundational cancellation: hermitian X with col-supph in col-cosupph    *)
(* of psd Y means cosupplf Y is identity on X.                             *)
(* path: utils:cosupplf_compr_hermlf -> utils:lift_supph_sandwich_quarter -> *)
(*   lhl:uniform_collision_bound -> *)
(*   bb84:privacy_amplification -> bb84:bb84_secret *)
Lemma cosupplf_compr_hermlf (B : {set L}) (Y : 'F[H]_B) (X : 'F[H]_B) :
  X \is hermlf -> Y \is psdlf ->
  (supph X `<=` supph Y)%HS ->
  cosupplf Y \o X = X.
Proof.
  move=> HXh PY Hsupp.
  apply/lfunP=> u; rewrite lfunE/=.
  have HXu_in_supph_X : X u \in supph X.
    apply/memh_suppP; exists u; by rewrite (hermlf_adjE HXh).
  have HXu_in_supph_Y : X u \in supph Y by move/lehP: Hsupp; apply.
  have HXu_in_cosupph_Y : X u \in cosupph Y.
    by rewrite -(@supph_eq_cosupph_hermlf B Y (psdlf_herm PY)).
  by move/memhP: HXu_in_cosupph_Y; rewrite hsE/=.
Qed.

(* path: utils:liftf_supp_pinv -> entropy:smooth_hmax_labelled_mx -> *)
(*   bb84:stat -> bb84:bb84_secret *)
Lemma liftf_supp_pinv (A B : {set L}) (X tau : 'F[H]_B) :
  (supph X `<=` supph tau)%HS ->
  X \is hermlf -> tau \is psdlf ->
  (\1 : 'F_A) \O (sqrtH tau \o pinvlf (sqrtH tau) \o X) =
  (\1 : 'F_A) \O X.
Proof.
  move=> Hsupp HXh Ptau.
  congr (_ \O _).
  have HsT_psd : sqrtH tau \is psdlf by exact: sqrtH_psd.
  have HpT_psd : pinvlf (sqrtH tau) \is psdlf by exact: pinvlf_psdlf.
  have HpT_h : pinvlf (sqrtH tau) \is hermlf := psdlf_herm HpT_psd.
  have HpT_adj : (pinvlf (sqrtH tau))^A = pinvlf (sqrtH tau).
    exact: hermlf_adjE HpT_h.
  have Hcos : sqrtH tau \o pinvlf (sqrtH tau) = cosupplf (sqrtH tau).
    by rewrite /cosupplf HpT_adj.
  rewrite Hcos.
  have Hsupph_eq : (supph X `<=` supph (sqrtH tau))%HS.
    by rewrite (@supph_sqrtH_psd B tau Ptau).
  exact: (cosupplf_compr_hermlf HXh HsT_psd Hsupph_eq).
Qed.

(* Composition of trivially-lifted B-operators through I_A ⊗ •.         *)
(* math: (I_A ⊗ f) · (I_A ⊗ g) = I_A ⊗ (f · g).                       *)
(* Consumers (≥2): uniform_to_collision, privacy_amp.                  *)
(* sdotI_comp *)
(* infra: no tex label — fundamental & reusable (mathcomp-style) *)
(* consumer: sdotI_comp is used downstream by the BB84 secrecy proof. *)
(* path: utils:sdotI_comp -> lhl:min_coll_bound -> *)
(*   bb84:privacy_amplification -> bb84:bb84_secret *)
Lemma sdotI_comp (A B : {set L}) (f g : 'F[H]_B) :
  ((\1 : 'F_A) \O f) \o ((\1 : 'F_A) \O g) = (\1 : 'F_A) \O (f \o g).
Proof.
  have lift_I (h : 'F[H]_B) :
      (\1 : 'F_A) \O h = lift_lf (@finset.subsetUr _ A B) h.
  { rewrite -(@lift_lf_id R L H (A :|: B) (subUsetPP (@finset.subsetUl _ A B)
                                            (@finset.subsetUr _ A B))
                            ((\1 : 'F_A) \O h)).
    by rewrite lift_lf_sdot lift_lf1 comp_lfun1l. }
  rewrite !(lift_I _).
  by rewrite lift_lf_comp.
Qed.

(* Trace of a trivially-lifted B-operator: Tr(I_A ⊗ f) = d_A · Tr f.    *)
(* Consumers (≥2): uniform_to_collision, privacy_amp.                  *)
(* trlf_lift_I *)
(* infra: no tex label — fundamental & reusable (mathcomp-style) *)
(* consumer: trlf_lift_I is used downstream by the BB84 secrecy proof. *)
(* path: utils:trlf_lift_I -> bb84:privacy_amplification -> *)
(*   bb84:bb84_secret *)
Lemma trlf_lift_I (A B : {set L}) (disAB : [disjoint A & B]) (f : 'F[H]_B) :
  \Tr ((\1 : 'F_A) \O f : 'F[H]_(A :|: B)) =
  (dim 'H[H]_A)%:R * \Tr f.
Proof.
  rewrite (lftrace_sdot_disj _ _ disAB).
  by rewrite /lftrace h2mx1 mxtrace1.
Qed.

(* Partial-trace support lift: supp rho_AB <= supp (I_A tensor rho_B).   *)
(* Consumers (≥2): uniform_to_collision, privacy_amp.                   *)
(* ptrace_supph_lift *)
(* infra: no tex label — fundamental & reusable (mathcomp-style) *)
(* consumer: ptrace_supph_lift is used downstream by the BB84 secrecy proof. *)
(* path: utils:ptrace_supph_lift -> lhl:uniform_collision_bound -> *)
(*   bb84:privacy_amplification -> bb84:bb84_secret *)
Lemma ptrace_supph_lift (A B : {set L}) (disAB : [disjoint A & B])
    (f : 'F[H]_(A :|: B)) :
  f \is psdlf ->
  (supph f `<=` supph ((\1 : 'F_A) \O ptrace_castl disAB f))%HS.
Proof.
  move=> Pf.
  rewrite leh_lef !hsE/= lef_h2mx.
  have h2mx_supplf : forall (X : 'End('H[H]_(A :|: B))),
      h2mx (supplf X) = suppmx (h2mx X).
    by move=> X; rewrite /supplf !h2mx_comp adj_lfun.unlock !mx2hK.
  rewrite !h2mx_supplf.
  rewrite (sdotF_to_tenF disAB) h2mx_tenf h2mx1.
  rewrite (h2mx_ptrace_castl_ptrace1 disAB f).
  set U := @tenv_mxU R L H A B.
  set Mf := h2mx f.
  set M := U^*t *m Mf *m U.
  have HUu : U \is unitarymx := tenv_mxU_unitarymx _ _.
  have HUtu : U^*t \is unitarymx := tenv_mxU_adj_unitarymx disAB.
  have HUK : U *m U^*t = 1%:M by exact: unitarymxK.
  have HUKV : U^*t *m U = 1%:M by have := unitarymxK HUtu; rewrite adjmxK.
  have PMf : Mf \is psdmx by move: Pf; rewrite qualifE.
  have PM : M \is psdmx.
    rewrite /M.
    have HrEq : U = (U^*t)^*t by rewrite adjmxK.
    rewrite {2}HrEq.
    exact: (psdmx_bimap_closed_gen U^*t PMf).
  have HMf_eq : Mf = U *m M *m U^*t.
    by rewrite /M mulmxA mulmxA HUK mul1mx -mulmxA HUK mulmx1.
  rewrite [Mf in suppmx Mf]HMf_eq.
  rewrite (suppmx_rect_unitary_conj _ HUu HUtu).
  rewrite (suppmx_rect_unitary_conj _ HUu HUtu).
  rewrite suppmx_tenmx_one_left.
  rewrite le_lownerE.
  rewrite -mulmxBl -mulmxBr.
  apply: psdmx_bimap_closed_gen.
  rewrite -le_lownerE.
  exact: suppmx_ptrace1_tens.
Qed.

(* Lift monotonicity of supph under trivial A-lift.                     *)
(* math: supph X ≤ supph Y ⇒ supph(I_A ⊗ X) ≤ supph(I_A ⊗ Y).          *)
(* Consumers (≥2): uniform_to_collision, privacy_amp.                   *)
(* supph_lift_mono *)
(* infra: no tex label — fundamental & reusable (mathcomp-style) *)
(* consumer: supph_lift_mono is used downstream by the BB84 secrecy proof. *)
(* Local port of liftf_lf_supp (from qmem.v) to lift_lf form, generic over sub. *)
(* Standalone justification: kernel hyperspace and lift_lf commute by                *)
(* membership: x \in kerh f iff f x = 0; lift_lf(f) x = lift_lf-equivalent.          *)
(* path: utils:lift_lf_supp_loc -> utils:supph_lift_mono -> *)
(*   bb84:privacy_amplification -> bb84:bb84_secret *)
Lemma lift_lf_supp_loc (S T : {set L}) (sub : (S :<=: T)%fset) (f : 'F[H]_S) :
  lift_lf sub (supplf f) = supplf (lift_lf sub f).
Proof.
  have P (g : 'F[H]_S) :
      HSType (lift_lf sub (kerh g)) = kerh (lift_lf sub g).
    apply/eqP/hseqP=> u;
      rewrite memh_kerE memhOE !hsE/= !hsE/= !hsE/= !hsE/=;
      rewrite lift_lf_cplmt cplmtK; apply/eqb_iff; split=>/eqP P.
        by rewrite -[g]suppvlf lift_lf_comp lfunE/= P linear0.
      by rewrite /supplf lift_lf_comp lfunE/= P linear0.
  move: (P f) => /(f_equal ocompl)/hspacelfP.
  do ? rewrite ![in X in X = _ -> _]hsE/=.
  do ? rewrite ![in X in _ = X -> _]hsE/=.
  by rewrite lift_lf_cplmt !cplmtK.
Qed.

(* path: utils:supph_lift_mono -> bb84:privacy_amplification -> *)
(*   bb84:bb84_secret *)
Lemma supph_lift_mono (A B : {set L}) (X Y : 'F[H]_B) :
  (supph X `<=` supph Y)%HS ->
  (supph ((\1 : 'F_A) \O X : 'F[H]_(A :|: B)) `<=`
   supph ((\1 : 'F_A) \O Y : 'F[H]_(A :|: B)))%HS.
Proof.
  move=> Hsupp.
  have lift_I : forall (h : 'F[H]_B),
      (\1 : 'F_A) \O h = lift_lf (@finset.subsetUr _ A B) h.
    move=> h.
    rewrite -(@lift_lf_id R L H (A :|: B) (subUsetPP (@finset.subsetUl _ A B)
                                            (@finset.subsetUr _ A B))
                          ((\1 : 'F_A) \O h)).
    by rewrite lift_lf_sdot lift_lf1 comp_lfun1l.
  rewrite !leh_lef !hsE/= !lift_I.
  rewrite -!lift_lf_supp_loc.
  rewrite lift_lf_lef.
  by move: Hsupp; rewrite leh_lef !hsE/=.
Qed.

(* Sandwich-cancellation with τ^{¼}/τ^{-¼}.                             *)
(* math: supph X ≤ supph(I_A ⊗ τ) ⇒ I_A⊗τ^¼ · I_A⊗τ^{-¼} · X ·          *)
(*       I_A⊗τ^{-¼} · I_A⊗τ^¼ = X.                                      *)
(* Consumers (≥2): uniform_to_collision, privacy_amp.                   *)
(* lift_supph_sandwich_quarter *)
(* infra: no tex label — fundamental & reusable (mathcomp-style) *)
(* consumer: lift_supph_sandwich_quarter is used downstream by the BB84 secrecy proof. *)
(* path: utils:lift_supph_sandwich_quarter -> lhl:uniform_collision_bound -> *)
(*   bb84:privacy_amplification -> bb84:bb84_secret *)
Lemma lift_supph_sandwich_quarter
    (A B : {set L}) (disAB : [disjoint A & B])
    (X : 'F[H]_(A :|: B)) (tau : 'F[H]_B) :
  tau \is psdlf ->
  (supph X `<=` supph ((\1 : 'F_A) \O tau))%HS ->
  X \is hermlf ->
  ((\1 : 'F_A) \O sqrtH (sqrtH tau)) \o
    ((\1 : 'F_A) \O pinvlf (sqrtH (sqrtH tau))) \o X \o
    ((\1 : 'F_A) \O pinvlf (sqrtH (sqrtH tau))) \o
    ((\1 : 'F_A) \O sqrtH (sqrtH tau)) = X.
Proof.
  move=> Ptau Hsupp HXh.
  set T := sqrtH (sqrtH tau).
  have PsT : sqrtH tau \is psdlf := sqrtH_psd Ptau.
  have PT : T \is psdlf := sqrtH_psd PsT.
  have PTh : T \is hermlf := psdlf_herm PT.
  have PpT : pinvlf T \is psdlf := pinvlf_psdlf PT.
  have HpT_h : pinvlf T \is hermlf := psdlf_herm PpT.
  have HcoT : T \o pinvlf T = cosupplf T.
    by rewrite /cosupplf (hermlf_adjE HpT_h).
  have HsuT : pinvlf T \o T = cosupplf T.
    rewrite -[in RHS](supplf_adj T) (hermlf_adjE PTh).
    by rewrite /supplf (hermlf_adjE HpT_h).
  have HcoT_eq_suT : cosupplf T = supplf T.
    by rewrite -(supplf_adj T) (hermlf_adjE PTh).
  have lift_I : forall (h : 'F[H]_B),
      (\1 : 'F_A) \O h = lift_lf (@finset.subsetUr _ A B) h.
    move=> h.
    rewrite -(@lift_lf_id R L H (A :|: B) (subUsetPP (@finset.subsetUl _ A B)
                                            (@finset.subsetUr _ A B))
                          ((\1 : 'F_A) \O h)).
    by rewrite lift_lf_sdot lift_lf1 comp_lfun1l.
  pose L1T : 'F[H]_(A :|: B) := lift_lf (@finset.subsetUr _ A B) T.
  have HL1T_def : (\1 : 'F_A) \O T = L1T by exact: lift_I.
  have HliftT_psd : L1T \is psdlf by rewrite /L1T -lift_lf_psdE.
  have HliftT_h : L1T \is hermlf := psdlf_herm HliftT_psd.
  have HleX_lhsupp : (supph tau `<=` supph T)%HS.
    have H1 := @supph_sqrtH_psd B (sqrtH tau) PsT.
    have H2 := @supph_sqrtH_psd B tau Ptau.
    have HsuppEq : supph T = supph tau by rewrite /T H1 H2.
    rewrite HsuppEq; exact: lehh.
  have HliftLE :
    (supph ((\1 : 'F_A) \O tau : 'F[H]_(A :|: B)) `<=`
     supph ((\1 : 'F_A) \O T : 'F[H]_(A :|: B)))%HS.
    exact: supph_lift_mono HleX_lhsupp.
  have Hsupp_lift : (supph X `<=` supph L1T)%HS.
    rewrite -HL1T_def.
    exact: le_trans Hsupp HliftLE.
  (* Reduce the 5-fold composition step-by-step. *)
  (* Original (left-assoc): ((((Lτ \o LpT) \o X) \o LpT) \o Lτ) where Lτ := (\1 \O T), LpT := (\1 \O pinvlf T). *)
  (* Combine leftmost two via sdotI_comp. *)
  rewrite [(\1 \O T) \o (\1 \O pinvlf T)]sdotI_comp HcoT.
  (* Goal: (\1 \O cosupplf T) \o X \o (\1 \O pinvlf T) \o (\1 \O T) = X *)
  (* Push to right-assoc, then combine rightmost two. *)
  rewrite -!comp_lfunA.
  rewrite [(\1 \O pinvlf T) \o (\1 \O T)]sdotI_comp HsuT.
  have HcoLift : (\1 : 'F_A) \O cosupplf T = cosupplf L1T.
    rewrite HcoT_eq_suT lift_I /L1T.
    rewrite lift_lf_supp_loc.
    by rewrite -[in RHS](supplf_adj L1T) (hermlf_adjE HliftT_h).
  rewrite HcoLift.
  have HleftCancel : cosupplf L1T \o X = X.
    exact: cosupplf_compr_hermlf HXh HliftT_psd Hsupp_lift.
  have HCo_h : cosupplf L1T \is hermlf.
    exact: projlf_herm (cosupplf_proj _).
  have HCo_eq_adj : (cosupplf L1T)^A = cosupplf L1T.
    exact: hermlf_adjE HCo_h.
  have HX_eq_adj : X^A = X := hermlf_adjE HXh.
  have HrightCancel : X \o cosupplf L1T = X.
    have := HleftCancel.
    move/(congr1 adj_lfun).
    rewrite adjf_comp HCo_eq_adj HX_eq_adj.
    by [].
  by rewrite HrightCancel HleftCancel.
Qed.

(* Adjoint lifts through the trivial A-factor: (\1_A ⊗ f)^A = \1_A ⊗ f^A. *)
(* Consumers (≥2): uniform_to_collision, privacy_amp.                    *)
(* sdot_I_adj *)
(* infra: no tex label — fundamental & reusable (mathcomp-style) *)
(* consumer: sdot_I_adj is used downstream by the BB84 secrecy proof. *)
(* path: utils:sdot_I_adj -> lhl:min_coll_bound -> *)
(*   bb84:privacy_amplification -> bb84:bb84_secret *)
Lemma sdot_I_adj (A B : {set L}) (f : 'F[H]_B) :
  (((\1 : 'F_A) \O f : 'F[H]_(A :|: B))^A) = (\1 : 'F_A) \O f^A.
Proof.
  have lift_I (h : 'F[H]_B) :
      (\1 : 'F_A) \O h = lift_lf (@finset.subsetUr _ A B) h.
  { rewrite -(@lift_lf_id R L H (A :|: B) (subUsetPP (@finset.subsetUl _ A B)
                                            (@finset.subsetUr _ A B))
                            ((\1 : 'F_A) \O h)).
    by rewrite lift_lf_sdot lift_lf1 comp_lfun1l. }
  rewrite !(lift_I _).
  by rewrite lift_lf_adj.
Qed.

(* Fourth power of schnorm-4 on the τ^¼-lift.                            *)
(* math: (schnorm 4 (h2mx (I_A ⊗ τ^¼)))^4 = d_A · Tr τ for psdlf τ.      *)
(* Consumers (≥2): uniform_to_collision, privacy_amp.                   *)
(* schnorm4_lift_quarter_pow4 *)
(* infra: no tex label — fundamental & reusable (mathcomp-style) *)
(* consumer: schnorm4_lift_quarter_pow4 is used downstream by the BB84 secrecy proof. *)
(* path: utils:schnorm4_lift_quarter_pow4 -> lhl:uniform_collision_bound -> *)
(*   bb84:privacy_amplification -> bb84:bb84_secret *)
Lemma schnorm4_lift_quarter_pow4
    (A B : {set L}) (disAB : [disjoint A & B]) (tau : 'F[H]_B) :
  tau \is psdlf ->
  (schnorm 4%:R (h2mx ((\1 : 'F_A) \O sqrtH (sqrtH tau) :
                       'F[H]_(A :|: B)))) ^+ 4
    = (dim 'H[H]_A)%:R%:C * \Tr tau.
Proof.
  move=> Ptau.
  have PsT : sqrtH tau \is psdlf := sqrtH_psd Ptau.
  have PS : sqrtH (sqrtH tau) \is psdlf := sqrtH_psd PsT.
  set M := h2mx tau.
  have PM : M \is psdmx by move: Ptau; rewrite qualifE.
  set N1 := sqrtmx (sqrtmx M).
  have HsM : sqrtmx M \is psdmx := sqrtmx_psd PM.
  have HN1psd : N1 \is psdmx := sqrtmx_psd HsM.
  have HN_eq : h2mx (sqrtH (sqrtH tau)) = N1 by rewrite /N1 /M !sqrtH_h2mx.
  rewrite (sdotF_to_tenF disAB) h2mx_tenf h2mx1.
  rewrite schnormUr; last by exact: (tenv_mxU_adj_unitarymx disAB).
  rewrite schnormUl_cond; last by exact: (tenv_mxU_adj_unitarymx disAB).
  rewrite schnorm_tens exprMn.
  have H4ge1 : (1 : R) <= 4%:R by rewrite ler1n.
  rewrite schnorm1_pge1//.
  have HdimA_ge0 : (0 : R) <= (dim 'H[H]_A)%:R by rewrite ler0n.
  rewrite -realcX.
  rewrite -powR_mulrn; last exact: powR_ge0.
  rewrite -powRrM.
  have H4ne0 : (4%:R : R) != 0 by rewrite pnatr_eq0.
  rewrite mulVf//.
  rewrite (powRr1 HdimA_ge0).
  congr (_ * _).
  rewrite HN_eq.
  rewrite /lftrace -/M.
  (* Goal: (schnorm 4%:R N1)^+4 = mxtrace M *)
  have HsvE_pt : forall j : 'I_(dim 'H[H]_B), (svds_d N1 0 j)^+4 = svds_d M 0 j.
    move=> j.
    have step2 : svds_d M 0 j = (svds_d (sqrtmx M) 0 j) ^+ 2.
      by rewrite -[in LHS](sqrtmxK PM) (svds_d_psdmx_sqr HsM) mxE.
    have step1 : svds_d (sqrtmx M) 0 j = (svds_d N1 0 j) ^+ 2.
      have Hpw m n (D : 'M[C]_(m, n)) (i : 'I_m) (k : 'I_n) :
          (D.^+ 2) i k = (D i k) ^+ 2 := mxE _ _ _ _.
      rewrite -[in LHS](sqrtmxK HsM) -/N1.
      rewrite (svds_d_psdmx_sqr HN1psd).
      exact: Hpw.
    have Hpow : (svds_d N1 0 j)^+4 = ((svds_d N1 0 j)^+2)^+2.
      by rewrite -exprM.
    transitivity ((svds_d (sqrtmx M) 0 j)^+2).
      transitivity (((svds_d N1 0 j)^+2)^+2).
        exact: Hpow.
      congr (_ ^+ 2).
      exact: esym step1.
    exact: esym step2.
  rewrite -(psdmx_trnorm PM) trnorm_svdE.
  rewrite schnormsE (lpnorm_pSE 3).
  rewrite -[X in _ ^+ X]/(3.+1).
  rewrite rootCK//.
  rewrite pair_bigV /= big_ord1.
  rewrite (eq_bigr (fun i => (svds_d N1 0 i)^+4));
    last by move=> i _; rewrite ger0_norm// svds_d_ge0.
  rewrite (reindex (cast_ord (esym (minn_id (dim 'H[H]_B))))) /=; last first.
    exists (cast_ord (minn_id _)); move=> i _; apply/val_inj=>//.
  apply: eq_bigr=> i _.
  rewrite HsvE_pt /svds_d castmxE/=.
  by congr (svd_d _ _ _); apply/val_inj.
Qed.
(* Proof route for the lifted trace identity: convert `\O` to tensor-matrix
   form, remove the `tenv_mxU` conjugation by unitary invariance of the
   Schatten norm, factor the tensor norm, and reduce the singular-value sum
   of the double square root to `mxtrace (h2mx tau) = \Tr tau`. *)

(* Partial trace of a trivially-A-lifted B-operator.                     *)
(* math: Tr_A (I_A ⊗ f) = d_A · f.  Standard textbook partial-trace      *)
(* identity; at the lfun level it reads                                   *)
(*   ptrace_castl disAB ((\1_A) \O f) = (dim H_A)%:R%:C *: f.             *)
(* Standalone justification: foundational partial-trace / tensor          *)
(* identity used throughout quantum info (e.g., Nielsen-Chuang §2.4,       *)
(* Watrous §1.1.2).  Consumers: min_coll_bound (supph preservation).      *)
(* ptrace_castl_sdot_I *)
(* infra: no tex label — fundamental & reusable (mathcomp-style) *)
(* consumer: ptrace_castl_sdot_I is used downstream by the BB84 secrecy proof. *)
(* path: utils:ptrace_castl_sdot_I -> lhl:min_coll_bound -> *)
(*   bb84:privacy_amplification -> bb84:bb84_secret *)
Lemma ptrace_castl_sdot_I (A B : {set L}) (disAB : [disjoint A & B])
    (f : 'F[H]_B) :
  ptrace_castl disAB ((\1 : 'F_A) \O f) =
  (dim 'H[H]_A)%:R%:C *: f.
Proof.
  apply/eqP/trlf_intror => g.
  rewrite -trlf_lift_partial sdotI_comp (trlf_lift_I disAB).
  rewrite -comp_lfunZl linearZ/=.
  by rewrite natrC.
Qed.

(* Marginal of a lifted-operator conjugation:                            *)
(*   Tr_A[(I_A ⊗ N) ρ (I_A ⊗ N)†] = N (Tr_A ρ) N†.                       *)
(* Partial trace over A commutes with conjugation by an operator that is  *)
(* trivial on A (the lift of the B-operator N). Proved here in lift.v so  *)
(* the identity `(\1 : 'F_A)` shares the same elaboration as the lemmas    *)
(* used (`sdot_I_adj`, `sdotI_comp`, `trlf_lift_partial`); cross-file `\1`*)
(* representations do not unify.  Test against g via `trlf_intror`; both  *)
(* sides reduce to Tr(ρ (I_A ⊗ N†gN)).                                    *)
(* path: utils:ptrace_castl_formlf_lift_I -> lhl:min_bound_op *)
Lemma ptrace_castl_formlf_lift_I (A B : {set L}) (disAB : [disjoint A & B])
    (N : 'F[H]_B) (rho : 'F[H]_(A :|: B)) :
  ptrace_castl disAB (formlf ((\1 : 'F_A) \O N) rho)
  = formlf N (ptrace_castl disAB rho).
Proof.
  apply/eqP/trlf_intror => g.
  have hassoc : (N^A \o g) \o N = N^A \o (g \o N)
    by exact: esym (comp_lfunA N^A g N).
  have hcyc : forall X : 'F[H]_B, (X \o (N^A \o g)) \o N = X \o (N^A \o (g \o N)).
  { by move=> X; rewrite -hassoc; exact: esym (comp_lfunA X (N^A \o g) N). }
  transitivity (\Tr (rho \o ((\1 : 'F_A) \O (N^A \o (g \o N))))).
  - rewrite -trlf_lift_partial formlfE sdot_I_adj.
    rewrite -!comp_lfunA sdotI_comp.
    rewrite lftraceC -!comp_lfunA sdotI_comp.
    by rewrite hassoc.
  - symmetry.
    by rewrite formlfE -!comp_lfunA lftraceC hcyc -trlf_lift_partial.
Qed.

(* trnormH of a trivially-A-lifted psd B-operator: factors (dim A).     *)
(* math: f psd ⇒ trnormH (I_A ⊗ f) = d_A · trnormH f.                 *)
(* Derivation: ptrace_castl_sdot_I (Qed) + trnormH_psd (lf.v) +         *)
(* tensor PSD preservation. Standalone (Watrous §1.1.4).                  *)
(* Consumers (≥2): dfu_pd_triangle (scaled ρ-witness trnorm lift +        *)
(* σ_tau's reference trnorm).                                             *)
(* trnormH_lift_I_psd *)
(* infra: no tex label — fundamental & reusable (mathcomp-style) *)
(* consumer: trnormH_lift_I_psd is used downstream by the BB84 secrecy proof. *)
(* path: utils:trnormH_lift_I_psd -> entropy:smooth_hmax_labelled_mx -> *)
(*   bb84:stat -> bb84:bb84_secret *)
Lemma trnormH_lift_I_psd (A B : {set L}) (disAB : [disjoint A & B])
    (f : 'F[H]_B) :
  f \is psdlf ->
  trnormH ((\1 : 'F_A) \O f : 'F[H]_(A :|: B)) =
  (dim 'H[H]_A)%:R * trnormH f.
Proof.
  move=> Pf.
  have H1f_ten : ((\1 : 'F_A) \O f : 'F[H]_(A :|: B)) =
                 (\1 : 'F_A) \⊗ f.
    by apply: to_Fnd_inj; rewrite (sdotFT _ _ disAB) to_Fnd_tenE.
  have H1f_psd : ((\1 : 'F_A) \O f : 'F[H]_(A :|: B)) \is psdlf.
    rewrite H1f_ten psdlfE.
    apply: tenf_ge0; first exact: disAB.
    - by rewrite -psdlfE; rewrite psdlfE; exact: lef01.
    - by move: Pf; rewrite psdlfE.
  rewrite (trnormH_psd H1f_psd) (trnormH_psd Pf).
  rewrite (trlf_lift_I disAB).
  rewrite -natrC.
  set zTr := \Tr f.
  by case: zTr => [a b] /=; rewrite mul0r subr0.
Qed.

(* trnormH of a trivially-A-lifted operator: factors (dim A).           *)
(* math: ||I_A ⊗ f||_1 = d_A · ||f||_1.                                *)
(* Consumers: BB84 fixed-marginal privacy amplification and              *)
(* distance-from-uniform transport arguments.                            *)
(* path: utils:trnormH_lift_I -> bb84:privacy_amplification -> *)
(*   bb84:bb84_secret *)
Lemma trnormH_lift_I (A B : {set L}) (disAB : [disjoint A & B])
    (f : 'F[H]_B) :
  trnormH ((\1 : 'F_A) \O f : 'F[H]_(A :|: B)) =
  (dim 'H[H]_A)%:R * trnormH f.
Proof.
  have Hten : ((\1 : 'F_A) \O f : 'F[H]_(A :|: B)) =
              (\1 : 'F_A) \⊗ f.
    by apply: to_Fnd_inj; rewrite (sdotFT _ _ disAB) to_Fnd_tenE.
  rewrite Hten /trnormH h2mx_tenf.
  rewrite trnormUr; first last.
  { by apply: tenv_mxU_adj_unitarymx; exact: disAB. }
  rewrite trnormUl_cond; first last.
  { by apply: tenv_mxU_adj_unitarymx; exact: disAB. }
  rewrite trnorm_tens h2mx1 trnorm1 /trnormH -natrC.
  by case: (trnorm (h2mx f)) => [a b] /=; rewrite mul0r subr0.
Qed.

(* Partial trace is trace-norm contractive.                              *)
(* math: ||Tr_A X||_1 <= ||X||_1.                                       *)
(* Consumers: BB84 fixed-marginal privacy amplification and              *)
(* trace-distance/partial-trace arguments.                               *)
(* path: utils:trnormH_ptrace_castl -> *)
(*   bb84:privacy_amplification -> bb84:bb84_secret *)
Lemma trnormH_ptrace_castl (A B : {set L}) (disAB : [disjoint A & B])
    (f : 'F[H]_(A :|: B)) :
  trnormH (ptrace_castl disAB f) <= trnormH f.
Proof.
  have Hcast_trn : forall (SA SB : {set L}) (eq : SA = SB)
      (g : 'F[H]_SA),
    trnormH (castlf (eq, eq) g) = trnormH g.
  { move=> SA SB eq g. by case: SB / eq; rewrite castlf_id. }
  rewrite /ptrace_castl /ptrace_cast_gen Hcast_trn.
  have Hit := itnormP (@ptraceso R L H A (A :|: B)) f.
  have Hqc : `|(@ptraceso R L H A (A :|: B)) : 'SO| = 1.
  { apply: itnorm_qcP; exact: ptraceso_qc. }
  rewrite Hqc mul1r in Hit.
  rewrite /trnormH.
  have Hre1 : trnorm (h2mx (\Tr_(A) f)) \is Num.real
    by exact: ger0_real (trnorm_ge0 _).
  have Hre2 : trnorm (h2mx f) \is Num.real
    by exact: ger0_real (trnorm_ge0 _).
  move: Hit; rewrite /Num.norm /= /trfnorm /=.
  by rewrite -(RRe_real Hre1) -(RRe_real Hre2) lecR.
Qed.

(* Square root distributes through I_A ⊗ • for psdlf on B.                *)
(* math: √(I_A ⊗ f) = I_A ⊗ √f  for f ≽ 0.                                *)
(* Derivation: spectral decomposition of I_A ⊗ f is tensor of spectra;    *)
(* sqrtH acts element-wise on eigenvalues; √1 = 1.                       *)
(* Standalone justification: tensor-product spectral functional-calculus  *)
(* identity (Watrous §1.1.2, Nielsen-Chuang §2.4.1).                      *)
(* Consumers: trlf_cross_system_4pt_identity and privacy_amp             *)
(* sqrt-lift factorization (LHL arXiv:1002.2436, proof of Thm 6).                           *)
(* sqrtH_sdot_I *)
(* infra: no tex label — fundamental & reusable (mathcomp-style) *)
(* consumer: sqrtH_sdot_I is used downstream by the BB84 secrecy proof. *)
(* path: utils:sqrtH_sdot_I -> utils:trlf_cross_system_4pt_identity -> *)
(*   bb84:privacy_amplification -> bb84:bb84_secret *)
Lemma sqrtH_sdot_I (A B : {set L}) (disAB : [disjoint A & B])
    (f : 'F[H]_B) :
  f \is psdlf ->
  sqrtH ((\1 : 'F_A) \O f : 'F[H]_(A :|: B)) =
  (\1 : 'F_A) \O sqrtH f.
Proof.
  move=> Pf.
  have HsqrtfPsd : sqrtH f \is psdlf by exact: sqrtH_psd.
  have Hsq : ((\1 : 'F_A) \O sqrtH f) \o ((\1 : 'F_A) \O sqrtH f) =
             ((\1 : 'F_A) \O f : 'F[H]_(A :|: B)).
    by rewrite sdotI_comp (sqrtHK Pf).
  have Hsqmx : h2mx ((\1 : 'F_A) \O sqrtH f : 'F[H]_(A :|: B)) *m
               h2mx ((\1 : 'F_A) \O sqrtH f : 'F[H]_(A :|: B)) =
               h2mx ((\1 : 'F_A) \O f : 'F[H]_(A :|: B)).
    by rewrite -h2mx_comp Hsq.
  have Hpsd : ((\1 : 'F_A) \O sqrtH f : 'F[H]_(A :|: B)) \is psdlf.
    rewrite (sdotF_to_tenF disAB).
    rewrite psdlfE; apply: tenf_ge0; first exact: disAB.
    - exact: lef01.
    - by rewrite -psdlfE.
  have Hpsdmx : h2mx ((\1 : 'F_A) \O sqrtH f : 'F[H]_(A :|: B)) \is psdmx
    by move: Hpsd; rewrite qualifE.
  apply/h2mx_inj.
  rewrite sqrtH_h2mx -Hsqmx.
  exact: sqrtmx_psd_square.
Qed.

(* Moore-Penrose pseudoinverse distributes through I_A ⊗ •.               *)
(* math: (I_A ⊗ f)⁺ = I_A ⊗ f⁺ (Kronecker product identity                *)
(*  (A ⊗ B)⁺ = A⁺ ⊗ B⁺ specialized to A = I, I⁺ = I).                     *)
(* Derivation: verify the four Moore-Penrose conditions on                *)
(* B = I_A ⊗ f⁺ against M = I_A ⊗ f using tenf_comp / adj / linearity.    *)
(* Standalone justification: foundational Kronecker-pseudoinverse         *)
(* identity (Penrose 1955 §3, Stewart-Sun §3.1).                          *)
(* Consumers: trlf_cross_system_4pt_identity and privacy_amp             *)
(* pinv-lift factorization (LHL arXiv:1002.2436, proof of Thm 6).                           *)
(* pinvlf_sdot_I *)
(* infra: no tex label — fundamental & reusable (mathcomp-style) *)
(* consumer: pinvlf_sdot_I is used downstream by the BB84 secrecy proof. *)
(* path: utils:pinvlf_sdot_I -> utils:trlf_cross_system_4pt_identity -> *)
(*   bb84:privacy_amplification -> bb84:bb84_secret *)
Lemma pinvlf_sdot_I (A B : {set L}) (disAB : [disjoint A & B])
    (f : 'F[H]_B) :
  pinvlf ((\1 : 'F_A) \O f : 'F[H]_(A :|: B)) =
  (\1 : 'F_A) \O pinvlf f.
Proof.
  set M : 'F[H]_(A :|: B) := (\1 : 'F_A) \O f.
  set Y : 'F[H]_(A :|: B) := (\1 : 'F_A) \O (pinvlf f)^A.
  (* By pinvlf_uniq_MP, Y = (pinvlf M)^A would yield pinvlf M = Y^A,
     and Y^A = ((\1 \O (pinvlf f)^A))^A = \1 \O ((pinvlf f)^A)^A
              = \1 \O pinvlf f.  *)
  have HYA : Y^A = (\1 : 'F_A) \O pinvlf f.
    by rewrite /Y sdot_I_adj adjfK.
  have HY_eq : Y = (pinvlf M)^A.
    apply: pinvlf_uniq_MP.
    - (* M \o Y \o M = M *)
      rewrite /M /Y !sdotI_comp.
      by rewrite pinvlf_MP_cond1.
    - (* Y \o M \o Y = Y *)
      rewrite /M /Y !sdotI_comp.
      by rewrite pinvlf_MP_cond2.
    - (* (M \o Y)^A = M \o Y *)
      rewrite /M /Y sdotI_comp sdot_I_adj.
      by rewrite pinvlf_MP_cond3.
    - (* (Y \o M)^A = Y \o M *)
      rewrite /M /Y sdotI_comp sdot_I_adj.
      by rewrite pinvlf_MP_cond4.
  by rewrite -HYA HY_eq adjfK.
Qed.

(* Cross-system 4-point trace identity.                                   *)
(* math: For ρ_A = (1/d_A)·I_A (maximally mixed), any psdlf sigma, rhoB,  *)
(*   Tr[(ρ_A ⊗ rhoB) · (I_A ⊗ pinvlf(sqrtH(ρ_A ⊗ sigma))) ·              *)
(*      (ρ_A ⊗ rhoB) · (I_A ⊗ pinvlf(sqrtH(ρ_A ⊗ sigma)))]               *)
(* = Tr(rhoB · M_σ · rhoB · M_σ)  where M_σ = pinvlf(sqrtH sigma).        *)
(* Derivation: sqrtH and pinvlf distribute over scalar·(I ⊗ ·) by         *)
(* homogeneity and tensor factorization; the resulting |A|^{±1} scalars   *)
(* and Tr(I_A) = d_A cancel exactly.  Used by thm:two-universal-hashing    *)
(* Step 4 to eliminate uniform_to_collision's 4-point trace term against   *)
(* privacy_amp's complementary term (LHL Lem 5).              *)
(* Standalone justification: structural tensor/trace identity — holds for *)
(* any psd sigma and any rhoB (not just CQ-marginal).                     *)
(* trlf_cross_system_4pt_identity *)
(* infra: no tex label — fundamental & reusable (mathcomp-style) *)
(* consumer: trlf_cross_system_4pt_identity is used downstream by the BB84 secrecy proof. *)
(* path: utils:trlf_cross_system_4pt_identity -> *)
(*   bb84:privacy_amplification -> bb84:bb84_secret *)
Lemma trlf_cross_system_4pt_identity
    (A B : {set L}) (disAB : [disjoint A & B])
    (sigma rhoB : 'F[H]_B) :
  sigma \is psdlf ->
  \Tr (
    (((dim 'H[H]_A)%:R^-1)%:C *: ((\1 : 'F_A) \O rhoB)) \o
    pinvlf (sqrtH (((dim 'H[H]_A)%:R^-1)%:C *: ((\1 : 'F_A) \O sigma))) \o
    (((dim 'H[H]_A)%:R^-1)%:C *: ((\1 : 'F_A) \O rhoB)) \o
    pinvlf (sqrtH (((dim 'H[H]_A)%:R^-1)%:C *: ((\1 : 'F_A) \O sigma)))
  ) = \Tr (rhoB \o pinvlf (sqrtH sigma) \o rhoB \o pinvlf (sqrtH sigma)).
Proof.
  move=> Psig.
  pose c : R := ((dim 'H[H]_A)%:R^-1)%R.
  have Hdim_gt0 : (0 < dim 'H[H]_A)%N := dim_proper.
  have HdimR_gt0 : (0 < (dim 'H[H]_A)%:R :> R)%R by rewrite ltr0n.
  have HdimR_neq0 : ((dim 'H[H]_A)%:R : R) != 0
    by rewrite pnatr_eq0 -lt0n.
  have Hc_gt0 : (0 < c)%R by rewrite /c invr_gt0.
  have Hc_ge0 : (0 <= c)%R by exact: ltW.
  have Hc_neq0 : (c != 0 :> R) by exact: lt0r_neq0.
  have Hsqrtc_gt0 : (0 < Num.sqrt c)%R by rewrite sqrtr_gt0.
  have Hsqrtc_neq0 : (Num.sqrt c != 0 :> R) by exact: lt0r_neq0.
  have Hsqrt_sq : (Num.sqrt c * Num.sqrt c = c :> R)%R
    by rewrite -expr2 sqr_sqrtr.
  have HIsig_psd : ((\1 : 'F_A) \O sigma : 'F[H]_(A :|: B)) \is psdlf.
    have HeqT : ((\1 : 'F_A) \O sigma : 'F[H]_(A :|: B)) =
                (\1 : 'F_A) \⊗ sigma.
      by apply: to_Fnd_inj; rewrite (sdotFT _ _ disAB) to_Fnd_tenE.
    rewrite HeqT psdlfE; apply: tenf_ge0; first exact: disAB.
    - exact: lef01.
    - by rewrite -psdlfE.
  have Hpinv_eq :
    pinvlf (sqrtH (((dim 'H[H]_A)%:R^-1)%:C *: ((\1 : 'F_A) \O sigma)) :
            'F[H]_(A :|: B)) =
    ((Num.sqrt c)^-1)%:C *: ((\1 : 'F_A) \O pinvlf (sqrtH sigma)).
    rewrite -/c (sqrtHZ_nn Hc_ge0 HIsig_psd).
    rewrite (pinvlfZ_nn _ Hsqrtc_neq0).
    rewrite (sqrtH_sdot_I disAB Psig).
    by rewrite (pinvlf_sdot_I disAB).
  rewrite !Hpinv_eq -/c.
  set M_σ : 'F[H]_B := pinvlf (sqrtH sigma).
  set k : C := ((Num.sqrt c)^-1)%:C.
  rewrite -!sdotfZr !sdotI_comp.
  rewrite (trlf_lift_I disAB).
  rewrite -!comp_lfunZl -!comp_lfunZr.
  rewrite -?comp_lfunZl -?comp_lfunZr.
  rewrite !scalerA.
  rewrite linearZ/=.
  have HK_R :
    (c * (Num.sqrt c)^-1 * c * (Num.sqrt c)^-1 = c :> R)%R.
    rewrite -mulrA mulrACA.
    rewrite -[(Num.sqrt c)^-1 * (Num.sqrt c)^-1]expr2 exprVn sqr_sqrtr //.
    by rewrite -mulrA mulfV // mulr1.
  have Hkcsq : (c%:C * k * c%:C * k = c%:C :> C).
    rewrite /k -!rmorphM/=.
    by rewrite HK_R.
  have HdimC_mul : ((dim 'H[H]_A)%:R : C) * c%:C = 1.
    rewrite /c -natrC -rmorphM/= mulfV //.
  rewrite Hkcsq.
  rewrite mulrA HdimC_mul mul1r.
  by [].
Qed.

End LiftAdjunction.

Local Close Scope lfun_scope.

End FvqkdReal.
