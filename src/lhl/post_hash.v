(* -------------------------------------------------------------------- *)
(* post_hash.v -- LHL post-hash proof-mechanics lemmas                  *)
(* -------------------------------------------------------------------- *)
(* Module: lhl.post_hash                                            *)
(* Source: Tomamichel-Schaffner-Smith-Renner, 'Leftover Hashing       *)
(*   Against Quantum Side Information' (IEEE Trans. IT 57:5524 (2011);  *)
(*   arXiv:1002.2436): proof mechanics behind lemma:privacy-amp        *)
(*   (Lem. 5) and thm:two-universal-hashing (Thm. 6).                   *)
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
From entropy.smooth Require Import dpi sm.
From lhl Require Import def dephase util.
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
(* Post-hash state: structural utilities                                *)
(* Used by lhl.v:two_universal_hashing for steps 3-5 of the glue proof. *)
(* ================================================================== *)
Section PostHashUtils.
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
(* tex: structural identity — sum of CQ blocks = partial trace over X.       *)
(* math: CQ ρ ⇒ Σ_x cq_block x ρ = Tr_X ρ                                     *)
(* Derivation: dephase_X_so is identity on CQ states (dephase.v); expanding  *)
(* its kraus form gives Σ_x K_x ρ K_x = ρ; applying ptrace_castl to both     *)
(* sides yields Σ_x cq_block x ρ = Tr_X ρ.                                   *)
(* Consumers (≥2): post_hash_ptrace_Z_CQ (this file), Gamma_C analysis       *)
(* (lhl/prop.v).                                                              *)
(* cq_sum_cq_block_eq_ptrace_castl *)
(* infra: no tex label — fundamental & reusable (mathcomp-style) *)
(* consumer: cq_sum_cq_block_eq_ptrace_castl is used downstream by the BB84 secrecy proof. *)
(* path: lhl:cq_sum_cq_block_eq_ptrace_castl -> lhl:post_hash_ptrace_Z_CQ -> *)
(*   bb84:privacy_amplification -> bb84:bb84_secret *)
Lemma cq_sum_cq_block_eq_ptrace_castl
    (rhoXE : 'F[HL]_S_XE) :
  rhoXE \is psdlf ->
  is_cq_state rhoXE ->
  \sum_(x : 'Idx[HL]_X) cq_block disXE x rhoXE =
  ptrace_castl disXE rhoXE.
Proof.
  move=> _ Hcq.
  have HKadj : forall x : 'Idx[HL]_X,
    (([> deltav x; deltav x <] \O (\1 : 'F_E) : 'F[HL]_S_XE))^A =
    [> deltav x; deltav x <] \O (\1 : 'F_E).
    move=> x.
    have Htensor : ([> deltav x; deltav x <] \O (\1 : 'F_E)
                    : 'F[HL]_S_XE) =
                   [> deltav x; deltav x <] \⊗ (\1 : 'F_E).
      by apply: to_Fnd_inj; rewrite (sdotFT _ _ disXE) to_Fnd_tenE.
    by rewrite Htensor tenf_adj adj_outp adjf1 -Htensor.
  rewrite -{2}(@dephase_X_cq_id R L HL X E disXE _ Hcq) /dephase_X_so kraussoE.
  rewrite /ptrace_castl /ptrace_cast_gen linear_sum /=.
  rewrite linear_sum /=.
  apply: eq_bigr => x _.
  rewrite /cq_block /ptrace_castl /ptrace_cast_gen.
  by rewrite HKadj.
Qed.
(* Tomamichel-Schaffner-Smith-Renner, 'Leftover Hashing Against Quantum     *)
(* Side Information' (IEEE Trans. IT 57:5524 (2011); arXiv:1002.2436),       *)
(* derived from Eq. 15 — tex eqn:after-extraction-state.                     *)
(* math: For CQ ρ_XE = Σ_x |x⟩⟨x| ⊗ ρ_E^[x],                                  *)
(*   Tr_Z (post_hash_state Fh ρ_XE) = ρ_F ⊗ Tr_X ρ_XE                         *)
(*   where ρ_F = (1/|F|)·I_F (uniform on F).                                  *)
(* Standalone justification: structural decomposition of the post-hash        *)
(* marginal on FE. Crucially uses CQ hypothesis to collapse Σ_{x:Fh(f,x)=z}  *)
(* over z (giving back all x) and the partial trace of |z⟩⟨z| (= 1).          *)
(* Tensor structure (ρ_F = (1/|F|)·I_F) emerges from the uniform F register.  *)
(* path: lhl:post_hash_ptrace_Z_CQ -> *)
(*   bb84:privacy_amplification -> bb84:bb84_secret *)
Lemma post_hash_ptrace_Z_CQ
    (Fh : 'Idx[HL]_Fl -> 'Idx[HL]_X -> 'Idx[HL]_Zl)
    (rhoXE : 'F[HL]_S_XE) :
  rhoXE \is psdlf ->
  is_cq_state rhoXE ->
  ptrace_castl disZl_FE (post_hash_state disXE Fh rhoXE) =
  ((dim 'H[HL]_Fl)%:R^-1)%:C *:
  ((\1 : 'F_Fl) \O ptrace_castl disXE rhoXE).
Proof.
  move=> Prho Hcq; pose _uses_disXF : [disjoint X & Fl] := disXF.
  pose _uses_disXZ : [disjoint X & Zl] := disXZ.
  pose _uses_disEF : [disjoint E & Fl] := disEF.
  (* Local helper: trace out the Zl register on a |z⟩⟨z| ⊗ |f⟩⟨f| ⊗ Y   *)
  (* triple tensor; used only in this post-hash marginal calculation.     *)
  have ptrace_castl_Zl_zf_inner :
    forall (z : 'Idx[HL]_Zl) (f : 'Idx[HL]_Fl)
           (inner : 'F[HL]_E),
    ptrace_castl disZl_FE
      (castlf (esym (finset.setUA Zl Fl E),
               esym (finset.setUA Zl Fl E))
        ([> deltav z ; deltav z <] \O [> deltav f ; deltav f <] \O inner)) =
    ([> deltav f ; deltav f <] \O inner).
  { move=> z f inner.
    have HrewriteCast :
      castlf (esym (finset.setUA Zl Fl E),
              esym (finset.setUA Zl Fl E))
        ([> deltav z ; deltav z <] \O [> deltav f ; deltav f <] \O inner) =
      [> deltav z ; deltav z <] \O ([> deltav f ; deltav f <] \O inner).
      apply: to_Fnd_inj.
      rewrite Fnd_cast !to_Fnd_sdotE.
      by rewrite dotFsA.
    rewrite HrewriteCast.
    apply/eqP/trlf_intror => g.
    rewrite -trlf_lift_partial.
    have HtenZ : [> deltav z; deltav z <] \O
                 ([> deltav f; deltav f <] \O inner) =
                 [> deltav z; deltav z <] \⊗
                 ([> deltav f; deltav f <] \O inner :
                  'F[HL]_(Fl :|: E)).
      by apply: to_Fnd_inj; rewrite (sdotFT _ _ disZl_FE) to_Fnd_tenE.
    have HtenI : (\1 : 'F[HL]_Zl) \O g =
                 (\1 : 'F[HL]_Zl) \⊗ g.
      by apply: to_Fnd_inj; rewrite (sdotFT _ _ disZl_FE) to_Fnd_tenE.
    rewrite HtenZ HtenI.
    have Hcomp : ([> deltav z; deltav z <] \⊗
                   ([> deltav f; deltav f <] \O inner
                    : 'F[HL]_(Fl :|: E))) \o
                  ((\1 : 'F[HL]_Zl) \⊗ g) =
                  ([> deltav z; deltav z <] \o (\1 : 'F[HL]_Zl)) \⊗
                  (([> deltav f; deltav f <] \O inner
                    : 'F[HL]_(Fl :|: E)) \o g).
      by rewrite -tenf_comp.
    rewrite Hcomp comp_lfun1r.
    rewrite lftrace_tenf; last exact: disZl_FE.
    by rewrite outp_trlf dv_dot eqxx mul1r. }
  rewrite /post_hash_state /ptrace_castl /ptrace_cast_gen.
  rewrite [castlf _ (_ *: _)]linearZ /= [\Tr_(Zl) (_ *: _)]linearZ /=.
  rewrite [castlf _ (_ *: _)]linearZ /=.
  have Hscalar_eq : @GRing.inv C ((dim 'H[HL]_Fl)%:R)
                  = ((dim 'H[HL]_Fl)%:R^-1)%:C.
    by rewrite -natrC -fmorphV.
  rewrite [X in X *: _]Hscalar_eq.
  congr (_ *: _).
  have Hpart : forall (Fh' : 'Idx[HL]_Fl -> 'Idx[HL]_X ->
                                 'Idx[HL]_Zl) (f' : 'Idx[HL]_Fl),
    \sum_(z : 'Idx[HL]_Zl)
      \sum_(x : 'Idx[HL]_X | Fh' f' x == z) cq_block disXE x rhoXE =
    \sum_(x : 'Idx[HL]_X) cq_block disXE x rhoXE.
    move=> Fh' f'; rewrite (exchange_big_dep xpredT)//=.
    apply: eq_bigr => x _.
    rewrite (eq_bigl (pred1 (Fh' f' x))); last first.
      by move=> z /=; rewrite eq_sym.
    by rewrite big_pred1_eq.
  rewrite linear_sum /=.
  rewrite linear_sum /=.
  rewrite linear_sum /=.
  under eq_bigr => f _ do rewrite linear_sum /=.
  under eq_bigr => f _ do rewrite linear_sum /=.
  under eq_bigr => f _ do rewrite linear_sum /=.
  under eq_bigr => f _ do
    under eq_bigr => z _ do
      rewrite -/(ptrace_cast_gen _ _) -/(ptrace_castl disZl_FE _)
              ptrace_castl_Zl_zf_inner.
  under eq_bigr => f _ do rewrite -linear_sum /=.
  under eq_bigr => f _ do rewrite (Hpart Fh f).
  under eq_bigr => f _ do rewrite (cq_sum_cq_block_eq_ptrace_castl Prho Hcq).
  rewrite -linear_sumlz /=.
  by rewrite sumonb_out.
Qed.
(* tex: trace-preservation of the privacy amplification channel              *)
(* math: Tr (post_hash_state Fh ρ) = Tr ρ (post_hash is TP).                   *)
(* Standalone justification: post_hash_state is a CPTP channel; TP is the     *)
(* T in CPTP.  Used to match trace constraints in dist_uniform_witness_bound.          *)
(* path: lhl:post_hash_trace_preserve -> *)
(*   bb84:privacy_amplification -> bb84:bb84_secret *)
Lemma post_hash_trace_preserve
    (Fh : 'Idx[HL]_Fl -> 'Idx[HL]_X -> 'Idx[HL]_Zl)
    (rhoXE : 'F[HL]_S_XE) :
  rhoXE \is psdlf ->
  \Tr (post_hash_state disXE Fh rhoXE) = \Tr rhoXE.
Proof.
  move=> Prho; pose _uses_disXF : [disjoint X & Fl] := disXF.
  pose _uses_disXZ : [disjoint X & Zl] := disXZ.
  have disZlF : [disjoint Zl & Fl] by rewrite disjoint_sym.
  have disZlE : [disjoint Zl & E] by rewrite disjoint_sym.
  have disFE : [disjoint Fl & E] by rewrite disjoint_sym.
  have disZF_E : [disjoint (Zl :|: Fl) & E].
    by rewrite disjointUX disZlE disjoint_sym disEF.
  have Htr_ptrace : forall (g : 'F[HL]_S_XE),
    \Tr (ptrace_castl disXE g) = \Tr g.
    move=> g; rewrite /ptrace_castl /ptrace_cast_gen castlf_trlfE.
    by case/cptpP: (@ptraceso_qc R L HL X S_XE) => _ /tpmapP ->.
  have Htrace_factor : forall (f : 'Idx[HL]_Fl) (z : 'Idx[HL]_Zl)
      (inner : 'F[HL]_E),
    \Tr ([> deltav z; deltav z <] \O [> deltav f; deltav f <] \O inner
         : 'F[HL]_((Zl :|: Fl) :|: E)) = \Tr inner.
    move=> f z inner; rewrite (lftrace_sdot_disj _ _ disZF_E).
    rewrite (lftrace_sdot_disj _ _ disZlF).
    by rewrite !outp_trlf !dv_dot !eqxx !mul1r.
  have Htr_cq : forall x : 'Idx[HL]_X,
    \Tr (cq_block disXE x rhoXE) =
    \Tr (([> deltav x; deltav x <] \O (\1 : 'F_E) : 'F[HL]_S_XE) \o rhoXE).
    move=> x; rewrite /cq_block Htr_ptrace.
    have HP_eq : [> deltav x; deltav x <] \O (\1 : 'F_E) =
                 [> deltav x; deltav x <] \⊗ (\1 : 'F_E) :>
                 'F[HL]_S_XE.
      by apply: to_Fnd_inj; rewrite (sdotFT _ _ disXE) to_Fnd_tenE.
    have HP_sq :
      ([> deltav x; deltav x <] \O (\1 : 'F_E) : 'F[HL]_S_XE) \o
      ([> deltav x; deltav x <] \O (\1 : 'F_E)) =
      [> deltav x; deltav x <] \O (\1 : 'F_E).
      rewrite {1 2}HP_eq -tenf_comp; last exact: disXE.
      rewrite comp_lfun1l.
      have -> : [> deltav x; deltav x <] \o [> deltav x; deltav x <]
                = [> deltav x; deltav x <] :> 'F[HL]_X.
        by rewrite outp_comp dv_dot eqxx scale1r.
      by rewrite -HP_eq.
    by rewrite lftraceC comp_lfunA HP_sq.
  have Hsum_I :
    \sum_(x : 'Idx[HL]_X)
      ([> deltav x; deltav x <] \O (\1 : 'F_E) : 'F[HL]_S_XE) =
    (\1 : 'F[HL]_S_XE).
    transitivity (\sum_(x : 'Idx[HL]_X)
      ([> deltav x; deltav x <] \⊗ (\1 : 'F_E) : 'F[HL]_S_XE)).
      apply: eq_bigr => x _.
      by apply: to_Fnd_inj; rewrite (sdotFT _ _ disXE) to_Fnd_tenE.
    rewrite -tenf_suml sumonb_out.
    by rewrite tenf11.
  have Hsum_x_tr :
    \sum_(x : 'Idx[HL]_X)
      \Tr (([> deltav x; deltav x <] \O (\1 : 'F_E) : 'F[HL]_S_XE)
           \o rhoXE) = \Tr rhoXE.
    rewrite -linear_sum/= -linear_sumlz/=.
    by rewrite Hsum_I comp_lfun1l.
  have Hpart : forall f : 'Idx[HL]_Fl,
    \sum_(z : 'Idx[HL]_Zl)
      \sum_(x : 'Idx[HL]_X | Fh f x == z)
        \Tr (cq_block disXE x rhoXE) =
    \sum_(x : 'Idx[HL]_X) \Tr (cq_block disXE x rhoXE).
    move=> f; rewrite (exchange_big_dep xpredT)//=.
    apply: eq_bigr => x _.
    rewrite (eq_bigl (pred1 (Fh f x))); last first.
      by move=> z /=; rewrite eq_sym.
    by rewrite big_pred1_eq.
  have Hfull :
    \Tr (\sum_(f : 'Idx[HL]_Fl) \sum_(z : 'Idx[HL]_Zl)
           [> deltav z; deltav z <] \O [> deltav f; deltav f <] \O
           (\sum_(x : 'Idx[HL]_X | Fh f x == z) cq_block disXE x rhoXE)
         : 'F[HL]_((Zl :|: Fl) :|: E)) =
    (dim 'H[HL]_Fl)%:R * \Tr rhoXE.
    rewrite !linear_sum/=.
    transitivity
      (\sum_(f : 'Idx[HL]_Fl)
         \sum_(x : 'Idx[HL]_X) \Tr (cq_block disXE x rhoXE)).
      apply: eq_bigr => f _.
      rewrite linear_sum/=.
      transitivity
        (\sum_(z : 'Idx[HL]_Zl)
           \sum_(x | Fh f x == z) \Tr (cq_block disXE x rhoXE)).
        apply: eq_bigr => z _.
        rewrite Htrace_factor linear_sum/=.
        reflexivity.
      exact: Hpart.
    transitivity
      (\sum_(f : 'Idx[HL]_Fl) \Tr rhoXE).
      apply: eq_bigr => f _.
      under eq_bigr do rewrite Htr_cq.
      exact: Hsum_x_tr.
    rewrite sumr_const idx_card.
    by rewrite mulr_natl.
  rewrite /post_hash_state castlf_trlfE linearZ/= Hfull mulrA.
  have HdimFl_neq0 : ((dim 'H[HL]_Fl)%:R : C) != 0
    by rewrite pnatr_eq0 -lt0n dim_proper.
  by rewrite mulVf // mul1r.
Qed.
(* post_hash preserves psdlf (CP part of CPTP).                               *)
(* post_hash_psdlf *)
(* infra: no tex label — fundamental & reusable (mathcomp-style) *)
(* consumer: post_hash_psdlf is used downstream by the BB84 secrecy proof. *)
(* path: lhl:post_hash_psdlf -> bb84:privacy_amplification -> *)
(*   bb84:bb84_secret *)
Lemma post_hash_psdlf
    (Fh : 'Idx[HL]_Fl -> 'Idx[HL]_X -> 'Idx[HL]_Zl)
    (rhoXE : 'F[HL]_S_XE) :
  rhoXE \is psdlf ->
  post_hash_state disXE Fh rhoXE \is psdlf.
Proof.
  move=> Prho.
  (* Force all six section disjointness hypotheses to appear in the        *)
  (* discharged signature (caller positions are fixed by lhl.v).           *)
  pose _uses_disXF : [disjoint X & Fl] := disXF.
  pose _uses_disXZ : [disjoint X & Zl] := disXZ.
  rewrite /post_hash_state.
  apply: castlf_psdlf.
  apply: psdlfZ.
    by rewrite invr_ge0 ler0n.
  apply: psdlf_sum => f _.
  apply: psdlf_sum => z _.
  have disZlF : [disjoint Zl & Fl] by rewrite disjoint_sym.
  have disZlE : [disjoint Zl & E] by rewrite disjoint_sym.
  have disFE : [disjoint Fl & E] by rewrite disjoint_sym.
  have disZlFE : [disjoint Zl & (Fl :|: E)].
    by rewrite disjointXU disZlF disZlE.
  have disZlF_E : [disjoint (Zl :|: Fl) & E].
    by rewrite disjointUX disZlE; rewrite disjoint_sym disEF.
  have Hsum_psd : \sum_(x | Fh f x == z) cq_block disXE x rhoXE \is psdlf.
    apply: psdlf_sum => x _.
    rewrite /cq_block.
    apply: ptrace_castl_psdlf.
    rewrite psdlfE.
    have HP_eq :
      ([> deltav x ; deltav x <] \O (\1 : 'F_E) : 'F[HL]_S_XE) =
      [> deltav x ; deltav x <] \⊗ (\1 : 'F_E).
      by apply: to_Fnd_inj; rewrite (sdotFT _ _ disXE) to_Fnd_tenE.
    have HP_adj :
      ((([> deltav x ; deltav x <] \O (\1 : 'F_E)) : 'F[HL]_S_XE)^A) =
      ([> deltav x ; deltav x <] \O (\1 : 'F_E)).
      by rewrite HP_eq tenf_adj adj_outp adjf1 -HP_eq.
    rewrite -{2}HP_adj.
    apply: gef0_formfV.
    by rewrite -psdlfE.
  have Hzz_psd : [> deltav z; deltav z <] \is psdlf := outp_psd _.
  have Hff_psd : [> deltav f; deltav f <] \is psdlf := outp_psd _.
  have Heq1 : [> deltav z; deltav z <] \O [> deltav f; deltav f <] =
              [> deltav z; deltav z <] \⊗ [> deltav f; deltav f <].
    by apply: to_Fnd_inj; rewrite (sdotFT _ _ disZlF) to_Fnd_tenE.
  have Hzf_psd :
    ([> deltav z; deltav z <] \O [> deltav f; deltav f <] :
       'F[HL]_(Zl :|: Fl)) \is psdlf.
    rewrite Heq1 psdlfE.
    apply: tenf_ge0; [exact: disZlF | by rewrite -psdlfE | by rewrite -psdlfE].
  have Heq2 :
    ([> deltav z; deltav z <] \O [> deltav f; deltav f <]) \O
    (\sum_(x | Fh f x == z) cq_block disXE x rhoXE) =
    ([> deltav z; deltav z <] \O [> deltav f; deltav f <]) \⊗
    (\sum_(x | Fh f x == z) cq_block disXE x rhoXE).
    apply: to_Fnd_inj.
    by rewrite (sdotFT _ _ disZlF_E) to_Fnd_tenE.
  rewrite Heq2 psdlfE.
  apply: tenf_ge0.
  - exact: disZlF_E.
  - by rewrite -psdlfE.
  - by rewrite -psdlfE.
Qed.
Lemma post_hash_state_linear
    (Fh : 'Idx[HL]_Fl -> 'Idx[HL]_X -> 'Idx[HL]_Zl) :
  linear (post_hash_state disXE Fh).
Proof.
  move=> a rho1 rho2; rewrite /post_hash_state.
  have Hcq_lin : forall x : 'Idx[HL]_X,
    cq_block disXE x (a *: rho1 + rho2) =
    a *: cq_block disXE x rho1 + cq_block disXE x rho2.
  {
    move=> x; rewrite /cq_block.
    rewrite linearPr /= linearPl /= /ptrace_castl /ptrace_cast_gen.
    rewrite linearP /=.
    by rewrite linearP /=.
  }
  have Hinner : forall (f : 'Idx[HL]_Fl) (z : 'Idx[HL]_Zl),
    \sum_(x : 'Idx[HL]_X | Fh f x == z)
      cq_block disXE x (a *: rho1 + rho2) =
    a *: (\sum_(x | Fh f x == z) cq_block disXE x rho1) +
    (\sum_(x | Fh f x == z) cq_block disXE x rho2).
  {
    move=> f z; rewrite (eq_bigr _ (fun x _ => Hcq_lin x)).
    by rewrite big_split /= scaler_sumr.
  }
  have Hdoublesum :
    \sum_(f : 'Idx[HL]_Fl) \sum_(z : 'Idx[HL]_Zl)
      [> deltav z ; deltav z <] \O [> deltav f ; deltav f <] \O
      (\sum_(x : 'Idx[HL]_X | Fh f x == z)
        cq_block disXE x (a *: rho1 + rho2)) =
    a *: (\sum_f \sum_z [> deltav z ; deltav z <] \O
             [> deltav f ; deltav f <] \O
             (\sum_(x | Fh f x == z) cq_block disXE x rho1)) +
    (\sum_f \sum_z [> deltav z ; deltav z <] \O
       [> deltav f ; deltav f <] \O
       (\sum_(x | Fh f x == z) cq_block disXE x rho2)).
  {
    rewrite linear_sum /= -big_split /=; apply: eq_bigr => f _.
    rewrite linear_sum /= -big_split /=; apply: eq_bigr => z _.
    rewrite Hinner sdotfDr sdotfZr.
    by [].
  }
  rewrite Hdoublesum scalerDr scalerA mulrC -scalerA.
  by rewrite linearP /=.
Qed.
(* Tomamichel, "A Framework for Non-Asymptotic Quantum Information Theory"   *)
(* (PhD thesis, ETH Zürich; arXiv:1203.2142), th:pd-mono (purified-distance  *)
(* contraction under trace-non-increasing CPMs), specialized to post_hash.   *)
(* math: P(post_hash ρ, post_hash τ) ≤ P(ρ, τ) (CPTP pd contraction).       *)
(* Proof: post_hash_state is CPTP (composition of X-measurement, classical   *)
(* Fh map, uniform F averaging).  Wrapped as a Superop via SOType ∘ linfun  *)
(* (requires post_hash_state linearity in rhoXE — witnessed by sum/scalar/  *)
(* castlf/sdot/cq_block linearity chain).  Apply pd_mono_cptp.              *)
(* path: lhl:pd_mono_post_hash -> bb84:privacy_amplification -> *)
(*   bb84:bb84_secret *)
Lemma pd_mono_post_hash
    (Fh : 'Idx[HL]_Fl -> 'Idx[HL]_X -> 'Idx[HL]_Zl)
    (rhoXE tauXE : 'F[HL]_S_XE) :
  rhoXE \is psdlf -> tauXE \is psdlf ->
  @complex.Re R (\Tr rhoXE) <= 1 ->
  @complex.Re R (\Tr tauXE) <= 1 ->
  pur_dist (post_hash_state disXE Fh rhoXE)
           (post_hash_state disXE Fh tauXE)
  <= pur_dist rhoXE tauXE.
Proof.
  move=> Prho Ptau Hrho_tr Htau_tr.
  have phs_lin : linear (post_hash_state disXE Fh) :=
    post_hash_state_linear Fh.
  pose phs_lfun : {linear 'F[HL]_S_XE ->
                    'F[HL]_(Zl :|: (Fl :|: E))} :=
    HB.pack (post_hash_state disXE Fh)
      (GRing.isLinear.Build C _ _ *:%R _ phs_lin).
  pose PHS : 'SO('H[HL]_S_XE,
                 'H[HL]_(Zl :|: (Fl :|: E))) :=
    SOType (linfun phs_lfun).
  have Heq : forall rho : 'F[HL]_S_XE,
    post_hash_state disXE Fh rho = PHS rho.
    move=> rho; by rewrite /PHS superopE lfunE /= /phs_lfun.
  have Hcptp : PHS \is cptp.
  { pose _uses_disXF : [disjoint X & Fl] := disXF.
    pose _uses_disXZ : [disjoint X & Zl] := disXZ.
    pose _uses_disEF : [disjoint E & Fl] := disEF.
    pose _uses_disEZ : [disjoint E & Zl] := disEZ.
    pose _uses_disFZ : [disjoint Fl & Zl] := disFZ.
    have disZlF : [disjoint Zl & Fl] by rewrite disjoint_sym.
    have disZlE : [disjoint Zl & E] by rewrite disjoint_sym.
    have disZF_E : [disjoint (Zl :|: Fl) & E].
      by rewrite disjointUX disZlE disjoint_sym disEF.
    pose invF : C := (((dim 'H[HL]_Fl)%:R)^-1)%R.
    pose alpha : C := sqrtC invF.
    pose Mbase (fx : 'Idx[HL]_Fl * 'Idx[HL]_X) :
        'F[HL]_(X :|: E,
                (Zl :|: Fl) :|: E) :=
      [> deltav (Fh fx.1 fx.2) ⊗v deltav fx.1 ; deltav fx.2 <] \⊗
      (\1 : 'F[HL]_E).
    pose Msc (fx : _ * _) :
        'F[HL]_(X :|: E,
                (Zl :|: Fl) :|: E) :=
      alpha *: Mbase fx.
    have HinvF_ge0 : 0 <= invF by rewrite /invF invr_ge0 ler0n.
    have Halpha_ge0 : 0 <= alpha by rewrite /alpha sqrtC_ge0.
    have Halpha_real : alpha^* = alpha.
      by apply: conj_Creal; apply: ger0_real.
    have Halpha_sq : alpha * alpha = invF.
      by rewrite -expr2 /alpha sqrtCK.
    have HdimF_nn : ((dim 'H[HL]_Fl)%:R : C) != 0.
      by rewrite pnatr_eq0 -lt0n dim_proper.
    have HMbase_AM : forall fx : _ * _,
      (Mbase fx)^A \o Mbase fx =
      ([> deltav fx.2; deltav fx.2 <] \⊗ (\1 : 'F[HL]_E)
        : 'F[HL]_S_XE).
    { move=> [f x'] /=.
      rewrite /Mbase tenf_adj adj_outp adjf1.
      rewrite -tenf_comp; last exact: disZF_E.
      rewrite comp_lfun1l outp_comp.
      rewrite tenv_dot; last exact: disZlF.
      by rewrite !dv_dot !eqxx mulr1 scale1r. }
    have Htrpresv : trace_presv Msc.
    { rewrite /trace_presv.
      have Hterm : forall fx : _ * _,
        (Msc fx)^A \o Msc fx =
        ((dim 'H[HL]_Fl)%:R^-1) *:
        ([> deltav fx.2; deltav fx.2 <] \⊗ (\1 : 'F[HL]_E)
          : 'F[HL]_S_XE).
      { move=> fx.
        rewrite /Msc adjfZ Halpha_real linearZl /= linearZr /= scalerA Halpha_sq.
        congr (_ *: _); exact: HMbase_AM. }
      under eq_bigr => fx _ do rewrite Hterm.
      rewrite -scaler_sumr.
      rewrite (eq_bigr (fun (fx : 'Idx[HL]_Fl * 'Idx[HL]_X) =>
        [> deltav fx.2; deltav fx.2 <] \⊗ (\1 : 'F[HL]_E)
          : 'F[HL]_S_XE)) => //.
      rewrite -(@pair_bigA _ _ _ _ _
        (fun (f : 'Idx[HL]_Fl) (x : 'Idx[HL]_X) =>
         [> deltav x; deltav x <] \⊗ (\1 : 'F[HL]_E)
           : 'F[HL]_S_XE)).
      under eq_bigr => f _ do
        rewrite -tenf_suml sumonb_out tenf11.
      rewrite sumr_const idx_card.
      have Hone_mul : (\1 : 'F[HL]_S_XE) *+ dim 'H[HL]_Fl =
                      (((dim 'H[HL]_Fl)%:R)%R : C) *:
                      (\1 : 'F[HL]_S_XE).
        by rewrite scaler_nat.
      rewrite Hone_mul scalerA /invF mulVf.
        by rewrite scale1r.
      by rewrite pnatr_eq0 -lt0n dim_proper. }
    have HMrho_sandwich : forall (fx : _ * _) (rho : 'F[HL]_S_XE),
      Mbase fx \o rho \o (Mbase fx)^A =
      [> deltav (Fh fx.1 fx.2) ⊗v deltav fx.1;
         deltav (Fh fx.1 fx.2) ⊗v deltav fx.1 <] \⊗
      cq_block disXE fx.2 rho.
    { move=> [f x'] rho /=.
      set u := deltav (Fh f x') ⊗v deltav f : 'H[HL]_(Zl :|: Fl).
      set K := [> deltav x'; deltav x' <] \O (\1 : 'F[HL]_E)
                : 'F[HL]_S_XE.
      have HK_ten : K = [> deltav x'; deltav x' <] \⊗ (\1 : 'F[HL]_E).
        by apply: to_Fnd_inj; rewrite (sdotFT _ _ disXE) to_Fnd_tenE.
      have HK_adj : K^A = K.
        by rewrite HK_ten tenf_adj adj_outp adjf1 -HK_ten.
      have HMbase_fact : (Mbase (f, x') : _) =
        ([> u; deltav x' <] \⊗ (\1 : 'F[HL]_E)) \o K.
      { rewrite /Mbase /= -/u HK_ten -tenf_comp; last exact: disXE.
        rewrite outp_comp dv_dot eqxx scale1r comp_lfun1l.
        by []. }
      rewrite HMbase_fact adjf_comp HK_adj.
      have Hreassoc :
        (([> u; deltav x' <] \⊗ (\1 : 'F[HL]_E)) \o K) \o rho \o
        (K \o ([> u; deltav x' <] \⊗ (\1 : 'F[HL]_E))^A) =
        ([> u; deltav x' <] \⊗ (\1 : 'F[HL]_E)) \o
        ((K \o rho \o K) \o
         ([> u; deltav x' <] \⊗ (\1 : 'F[HL]_E))^A).
        by rewrite !comp_lfunA.
      rewrite Hreassoc (Kbox_cq_decomp disXE x' rho).
      have HcqCQ_ten :
        ([> deltav x'; deltav x' <] \O cq_block disXE x' rho
          : 'F[HL]_S_XE) =
        [> deltav x'; deltav x' <] \⊗ cq_block disXE x' rho.
        by apply: to_Fnd_inj; rewrite (sdotFT _ _ disXE) to_Fnd_tenE.
      rewrite HcqCQ_ten tenf_adj adj_outp adjf1.
      rewrite -tenf_comp; last exact: disXE.
      rewrite outp_comp !dv_dot !eqxx /= scale1r.
      rewrite -tenf_comp; last exact: disXE.
      rewrite outp_comp !dv_dot !eqxx /= scale1r.
      by rewrite !(comp_lfun1l, comp_lfun1r) /u. }
    have HPHS_eq : PHS = castso (erefl (X :|: E),
                                  esym (finset.setUA Zl Fl E))
                                 (krausso Msc).
    { apply/superopP => rho.
      rewrite /PHS superopE lfunE /= /phs_lfun /= /post_hash_state castsoE /= kraussoE castlf_id.
      congr (castlf _ _).
      rewrite (eq_bigr (fun fx : 'Idx[HL]_Fl * 'Idx[HL]_X =>
        invF *: (Mbase fx \o rho \o (Mbase fx)^A))); last first.
      { move=> fx _.
        rewrite /Msc adjfZ Halpha_real linearZl /= linearZl /= linearZr /= scalerA Halpha_sq.
        by rewrite /invF. }
      rewrite -scaler_sumr.
      have Hscalar_eq : @GRing.inv C ((dim 'H[HL]_Fl)%:R) = invF.
        by rewrite /invF.
      rewrite Hscalar_eq.
      congr (_ *: _).
      rewrite [RHS](eq_bigr (fun fx : 'Idx[HL]_Fl * 'Idx[HL]_X =>
        [> deltav (Fh fx.1 fx.2) ⊗v deltav fx.1;
           deltav (Fh fx.1 fx.2) ⊗v deltav fx.1 <] \⊗
        cq_block disXE fx.2 rho : 'F[HL]_((Zl :|: Fl) :|: E))); last first.
      { move=> fx _. apply: HMrho_sandwich. }
      rewrite -(@pair_bigA _ _ _ _ _
        (fun (f : 'Idx[HL]_Fl) (x : 'Idx[HL]_X) =>
         [> deltav (Fh f x) ⊗v deltav f;
            deltav (Fh f x) ⊗v deltav f <] \⊗
         cq_block disXE x rho : 'F[HL]_((Zl :|: Fl) :|: E))).
      apply: eq_bigr => f _.
      have Hpart : forall (G : 'Idx[HL]_X -> 'F[HL]_((Zl :|: Fl) :|: E)),
        \sum_(x : 'Idx[HL]_X) G x =
        \sum_(z : 'Idx[HL]_Zl)
          \sum_(x : 'Idx[HL]_X | Fh f x == z) G x.
        move=> G.
        rewrite (exchange_big_dep xpredT) //=; apply: eq_bigr => x _.
        rewrite (eq_bigl (pred1 (Fh f x))); last by move=> z /=; rewrite eq_sym.
        by rewrite big_pred1_eq.
      rewrite [RHS](Hpart (fun x =>
        [> deltav (Fh f x) ⊗v deltav f;
           deltav (Fh f x) ⊗v deltav f <] \⊗
        cq_block disXE x rho)).
      apply: eq_bigr => z _.
      rewrite [RHS](eq_bigr (fun x : 'Idx[HL]_X =>
        [> deltav z; deltav z <] \O [> deltav f; deltav f <] \O
        cq_block disXE x rho :
        'F[HL]_((Zl :|: Fl) :|: E))); last first.
      { move=> x Hfx.
        rewrite (eqP Hfx) -tenf_outp.
        have HZF : ([> deltav z; deltav z <] \⊗ [> deltav f; deltav f <]
                      : 'F[HL]_(Zl :|: Fl)) =
                    [> deltav z; deltav z <] \O [> deltav f; deltav f <].
          by apply: to_Fnd_inj; rewrite (sdotFT _ _ disZlF) to_Fnd_tenE.
        rewrite HZF.
        apply: to_Fnd_inj.
        by rewrite (sdotFT _ _ disZF_E) to_Fnd_tenE. }
      by rewrite -linear_sumr /=. }
    rewrite HPHS_eq.
    apply/cptpP; split.
      rewrite castso_cpE; exact: krausso_cp.
    rewrite castso_tpE krausso_tpE.
    exact: Htrpresv. }
  rewrite !Heq.
  exact: (pd_mono_cptp Hcptp Prho Ptau Hrho_tr Htau_tr).
Qed.
(* ================================================================== *)
(* 4-point trace identity for post_hash_state with arbitrary M_E.      *)
(* Tomamichel-Schaffner-Smith-Renner, 'Leftover Hashing Against        *)
(* Quantum Side Information' (IEEE Trans. IT 57:5524 (2011);            *)
(* arXiv:1002.2436); proof step of lemma:privacy-amp (Lem. 5) Γ_C       *)
(* expansion (block-trace step).                                        *)
(* math: For Z, F, E disjoint and any M_E on E, the 4-fold trace       *)
(* (I_{Z∪F}⊗M_E)·post_hash·(I_{Z∪F}⊗M_E)·post_hash reduces to           *)
(* (1/|F|)² Σ_{f,z} Tr (S_{f,z} M_E S_{f,z} M_E) with                   *)
(* S_{f,z} := Σ_{x:Fh f x=z} cq_block x ρ.                              *)
(* Standalone justification: block-trace collapse via projector         *)
(* orthogonality on Z⊗F; M_E-independent.                               *)
(* Consumers (≥2): Gamma_C_post_hash_block_form (this file) + reusable *)
(* for almost-2-universal hash family analysis.                          *)
(* trlf_post_hash_collision_block *)
(* infra: no tex label — fundamental & reusable (mathcomp-style) *)
(* consumer: trlf_post_hash_collision_block is used downstream by the BB84 secrecy proof. *)
(* path: lhl:trlf_post_hash_collision_block -> *)
(*   lhl:Gamma_C_post_hash_block_form -> lhl:Gamma_C_post_hash_expand -> *)
(*   lhl:Gamma_C_post_hash_split -> lhl:privacy_amp -> *)
(*   bb84:privacy_amplification -> bb84:bb84_secret *)
Lemma trlf_post_hash_collision_block
    (Fh : 'Idx[HL]_Fl -> 'Idx[HL]_X -> 'Idx[HL]_Zl)
    (rhoXE : 'F[HL]_S_XE) (M_E : 'F[HL]_E) :
  \Tr (
    ((\1 : 'F_Zl) \O ((\1 : 'F_Fl) \O M_E)) \o
    post_hash_state disXE Fh rhoXE \o
    ((\1 : 'F_Zl) \O ((\1 : 'F_Fl) \O M_E)) \o
    post_hash_state disXE Fh rhoXE
  ) =
  ((dim 'H[HL]_Fl)%:R^-1)%:C * ((dim 'H[HL]_Fl)%:R^-1)%:C *
  \sum_(f : 'Idx[HL]_Fl) \sum_(z : 'Idx[HL]_Zl)
    \Tr (
      (\sum_(x : 'Idx[HL]_X | Fh f x == z) cq_block disXE x rhoXE) \o
      M_E \o
      (\sum_(x : 'Idx[HL]_X | Fh f x == z) cq_block disXE x rhoXE) \o
      M_E
    ).
Proof.
  pose _uses_disXF : [disjoint X & Fl] := disXF.
  pose _uses_disXZ : [disjoint X & Zl] := disXZ.
  pose _uses_disEZ : [disjoint E & Zl] := disEZ.
  pose _uses_disFZ : [disjoint Fl & Zl] := disFZ.
  have disZlF : [disjoint Zl & Fl] by rewrite disjoint_sym.
  have disZlE : [disjoint Zl & E] by rewrite disjoint_sym.
  have disFE  : [disjoint Fl & E] by rewrite disjoint_sym.
  have disZF_E : [disjoint (Zl :|: Fl) & E].
    by rewrite disjointUX disZlE disjoint_sym disEF.
  set eqZFE : (Zl :|: Fl) :|: E
            = Zl :|: (Fl :|: E)
    := esym (finset.setUA Zl Fl E).
  set c : C := ((dim 'H[HL]_Fl)%:R^-1)%:C.
  set M_R : 'F[HL]_(Zl :|: (Fl :|: E))
    := ((\1 : 'F_Zl) \O ((\1 : 'F_Fl) \O M_E)).
  set M_L : 'F[HL]_((Zl :|: Fl) :|: E)
    := ((\1 : 'F_(Zl :|: Fl)) \O M_E).
  have HM_R_ten :
    M_R = (\1 : 'F[HL]_Zl) \⊗ ((\1 : 'F[HL]_Fl) \⊗ M_E).
  { apply: to_Fnd_inj.
    rewrite /M_R (sdotFT _ _ disZl_FE).
    rewrite to_Fnd_tenE.
    by rewrite (sdotFT _ _ disFE) to_Fnd_tenE. }
  have HM_L_ten :
    M_L = ((\1 : 'F[HL]_Zl) \⊗ (\1 : 'F[HL]_Fl)) \⊗ M_E.
  { apply: to_Fnd_inj.
    rewrite /M_L (sdotFT _ _ disZF_E) !to_Fnd_tenE.
    by rewrite -tenf11. }
  have HM_cast : M_R = castlf (eqZFE, eqZFE) M_L.
  { apply: to_Fnd_inj.
    rewrite Fnd_cast HM_R_ten HM_L_ten.
    by rewrite !to_Fnd_tenE tenFA. }
  pose inner : 'F[HL]_((Zl :|: Fl) :|: E) :=
    \sum_(f : 'Idx[HL]_Fl) \sum_(z : 'Idx[HL]_Zl)
      [> deltav z ; deltav z <] \O [> deltav f ; deltav f <] \O
      (\sum_(x : 'Idx[HL]_X | Fh f x == z) cq_block disXE x rhoXE).
  have Hphs_eq :
    post_hash_state disXE Fh rhoXE = c *: castlf (eqZFE, eqZFE) inner.
  { rewrite /post_hash_state /inner /c -/eqZFE.
    have Hscalar_eq : @GRing.inv C ((dim 'H[HL]_Fl)%:R)
                    = ((dim 'H[HL]_Fl)%:R^-1)%:C.
      by rewrite -natrC -fmorphV.
    rewrite Hscalar_eq.
    by rewrite linearZ /=. }
  rewrite Hphs_eq.
  have HscalarPull :
    M_R \o (c *: castlf (eqZFE, eqZFE) inner) \o M_R \o
    (c *: castlf (eqZFE, eqZFE) inner) =
    (c * c) *: (M_R \o castlf (eqZFE, eqZFE) inner \o M_R \o
                castlf (eqZFE, eqZFE) inner).
  { rewrite -comp_lfunZr.
    rewrite -comp_lfunZr -comp_lfunZl.
    rewrite -comp_lfunZl.
    rewrite scalerA //. }
  rewrite HscalarPull linearZ /=.
  rewrite HM_cast.
  have Hcast_4comp :
    castlf (eqZFE, eqZFE) M_L \o castlf (eqZFE, eqZFE) inner \o
    castlf (eqZFE, eqZFE) M_L \o castlf (eqZFE, eqZFE) inner =
    castlf (eqZFE, eqZFE) (M_L \o inner \o M_L \o inner).
  { rewrite [RHS](castlf_complf eqZFE eqZFE eqZFE).
    rewrite [castlf _ ((M_L \o inner) \o M_L)](castlf_complf eqZFE eqZFE eqZFE).
    by rewrite [castlf _ (M_L \o inner)](castlf_complf eqZFE eqZFE eqZFE). }
  rewrite Hcast_4comp castlf_trlfE.
  congr (_ * _).
  pose Sfz (f : 'Idx[HL]_Fl) (z : 'Idx[HL]_Zl)
    : 'F[HL]_E :=
    \sum_(x : 'Idx[HL]_X | Fh f x == z) cq_block disXE x rhoXE.
  pose zfblk (f : 'Idx[HL]_Fl) (z : 'Idx[HL]_Zl)
    : 'F[HL]_((Zl :|: Fl) :|: E) :=
    [> deltav z ; deltav z <] \O [> deltav f ; deltav f <] \O Sfz f z.
  have Hinner_eq :
    inner = \sum_(f : 'Idx[HL]_Fl) \sum_(z : 'Idx[HL]_Zl)
              zfblk f z.
  { rewrite /inner /zfblk /Sfz. by []. }
  rewrite Hinner_eq.
  have Hcross :
    forall (f f' : 'Idx[HL]_Fl)
           (z z' : 'Idx[HL]_Zl),
    \Tr (M_L \o zfblk f z \o M_L \o zfblk f' z') =
    (z == z')%:R * (f == f')%:R *
      \Tr (Sfz f z \o M_E \o Sfz f' z' \o M_E).
  { move=> f f' z z'.
    rewrite /M_L /zfblk /Sfz.
    set Su := [> deltav z ; deltav z <] \O [> deltav f ; deltav f <] \O
                \sum_(x | Fh f x == z) cq_block disXE x rhoXE.
    set Sv := [> deltav z'; deltav z'<] \O [> deltav f'; deltav f' <] \O
                \sum_(x' | Fh f' x' == z') cq_block disXE x' rhoXE.
    set ML := (\1 : 'F_(Zl :|: Fl)) \O M_E.
    have HML_ten : ML = (\1 : 'F[HL]_(Zl :|: Fl)) \⊗ M_E.
    { rewrite /ML.
      apply: to_Fnd_inj.
      by rewrite (sdotFT _ _ disZF_E) to_Fnd_tenE. }
    have Hzfblk_ten : forall (g : 'Idx[HL]_Fl)
                             (w : 'Idx[HL]_Zl)
                             (Y : 'F[HL]_E),
      ([> deltav w; deltav w <] \O [> deltav g; deltav g <]) \O Y =
      (([> deltav w; deltav w <] \⊗ [> deltav g; deltav g <]
         : 'F[HL]_(Zl :|: Fl)) \⊗ Y).
    { move=> g w Y.
      apply: to_Fnd_inj.
      rewrite (sdotFT _ _ disZF_E) to_Fnd_tenE.
      have Hzg : [> deltav w; deltav w <] \O [> deltav g; deltav g <] =
                 [> deltav w; deltav w <] \⊗ [> deltav g; deltav g <] :>
                   'F[HL]_(Zl :|: Fl).
        by apply: to_Fnd_inj; rewrite (sdotFT _ _ disZlF) to_Fnd_tenE.
      by rewrite Hzg. }
    have HSu_ten : Su =
      ([> deltav z; deltav z <] \⊗ [> deltav f; deltav f <]
       : 'F[HL]_(Zl :|: Fl)) \⊗
      (\sum_(x | Fh f x == z) cq_block disXE x rhoXE).
    { by rewrite /Su Hzfblk_ten. }
    have HSv_ten : Sv =
      ([> deltav z'; deltav z'<] \⊗ [> deltav f'; deltav f' <]
       : 'F[HL]_(Zl :|: Fl)) \⊗
      (\sum_(x' | Fh f' x' == z') cq_block disXE x' rhoXE).
    { by rewrite /Sv Hzfblk_ten. }
    rewrite -/Su -/Sv -/ML HML_ten HSu_ten HSv_ten.
    rewrite -[(_ \⊗ M_E) \o (_ \⊗ _ \⊗ _)]tenf_comp; last exact: disZF_E.
    rewrite -[(_ \⊗ _) \o (_ \⊗ M_E)]tenf_comp; last exact: disZF_E.
    set X1 := ((\1 \o _) \o \1) : 'F[HL]_(Zl :|: Fl).
    set X2 := ((M_E \o _) \o M_E) : 'F[HL]_E.
    set Y1 := (_ \⊗ _) : 'F[HL]_(Zl :|: Fl).
    set Y2 := \sum_(x' | _) cq_block _ x' rhoXE : 'F[HL]_E.
    rewrite -[(X1 \⊗ X2) \o (Y1 \⊗ Y2)]tenf_comp; last exact: disZF_E.
    rewrite lftrace_tenf; last exact: disZF_E.
    rewrite /X1 /Y1 comp_lfun1l !comp_lfun1r.
    rewrite -tenf_comp; last exact: disZlF.
    rewrite !outp_comp !dv_dot.
    rewrite tenfZl tenfZr scalerA.
    rewrite linearZ /= lftrace_tenf; last exact: disZlF.
    rewrite !outp_trlf !dv_dot [(z' == z)]eq_sym [(f' == f)]eq_sym.
    case Hzz' : (z == z')%B; case Hff' : (f == f')%B;
      rewrite ?(mul0r, mulr0, mul1r, mulr1) //=.
    rewrite /X2 /Y2 -/(Sfz f z) -/(Sfz f' z').
    move/eqP: Hzz' => Hzz'; move/eqP: Hff' => Hff'.
    rewrite Hzz' Hff' lftraceC.
    by rewrite !comp_lfunA. }
  rewrite linear_sumr /= linear_sum /=.
  under eq_bigr => f' _ do rewrite linear_sumr /= linear_sum /=.
  under eq_bigr => f' _ do
    under eq_bigr => z' _ do
      (rewrite linear_sumr /= linear_sumlz /= linear_sumlz /=;
       rewrite linear_sum /=;
       under eq_bigr => f _ do
         (rewrite linear_sumr /= linear_sumlz /= linear_sumlz /=;
          rewrite linear_sum /=)).
  under eq_bigr => f' _ do
    under eq_bigr => z' _ do
      under eq_bigr => f _ do
        under eq_bigr => z _ do
          rewrite Hcross.
  rewrite (eq_bigr (fun f' =>
    \sum_(z' : 'Idx[HL]_Zl)
      \Tr (Sfz f' z' \o M_E \o Sfz f' z' \o M_E))); last first.
  { move=> f' _.
    apply: eq_bigr => z' _.
    rewrite (bigD1 f') //=.
    rewrite [X in _ + X]big1; last first.
    { move=> i Hi.
      rewrite big1 // => z _.
      by rewrite (negPf Hi) mulr0 mul0r. }
    rewrite addr0 (bigD1 z') //=.
    rewrite [X in _ + X]big1; last first.
    { move=> z Hz.
      by rewrite (negPf Hz) mul0r mul0r. }
    by rewrite addr0 !eqxx !mul1r. }
  apply: eq_bigr => f _.
  apply: eq_bigr => z _.
  by rewrite /Sfz.
Qed.
(* ================================================================== *)
(* Block-form Γ_C identity for post-hash CQ states (structural).       *)
(* Tomamichel-Schaffner-Smith-Renner, 'Leftover Hashing Against        *)
(* Quantum Side Information' (IEEE Trans. IT 57:5524 (2011);            *)
(* arXiv:1002.2436); proof step 1 of lemma:privacy-amp (Lem. 5) Γ_C     *)
(* expansion (intermediate form).                                      *)
(* math: For CQ ρ_XE and τ_E ∈ S_=(H_E),                                *)
(*   Γ_C(ρ_ZFE | (1/|F|)·I_F ⊗ τ_E) =                                  *)
(*     (1/|F|) Σ_f Σ_z Re Tr ( S_{f,z} · τ^{-½} · S_{f,z} · τ^{-½} )   *)
(* where S_{f,z} := Σ_{x : Fh f x = z} cq_block_x ρ_XE.                  *)
(* Consumers: Gamma_C_post_hash_expand (lhl/prop.v) and the             *)
(* almost-2-universal hash family variant.                              *)
(* ================================================================== *)
(* Gamma_C_post_hash_block_form *)
(* infra: no tex label — fundamental & reusable (mathcomp-style) *)
(* consumer: Gamma_C_post_hash_block_form is used downstream by the BB84 secrecy proof. *)
(* path: lhl:Gamma_C_post_hash_block_form -> lhl:Gamma_C_post_hash_expand -> *)
(*   lhl:Gamma_C_post_hash_split -> lhl:privacy_amp -> *)
(*   bb84:privacy_amplification -> bb84:bb84_secret *)
Lemma Gamma_C_post_hash_block_form
    (Fh : 'Idx[HL]_Fl -> 'Idx[HL]_X -> 'Idx[HL]_Zl)
    (rhoXE : 'F[HL]_S_XE) (tauE : 'F[HL]_E) :
  rhoXE \is psdlf ->
  tauE \is psdlf ->
  is_cq_state rhoXE ->
  collision_ent (post_hash_state disXE Fh rhoXE)
    (((dim 'H[HL]_Fl)%:R^-1)%:C *: ((\1 : 'F_Fl) \O tauE)) =
  ((dim 'H[HL]_Fl)%:R^-1)%R *
  \sum_(f : 'Idx[HL]_Fl) \sum_(z : 'Idx[HL]_Zl)
    @complex.Re R (\Tr (
      (\sum_(x : 'Idx[HL]_X | Fh f x == z) cq_block disXE x rhoXE) \o
      pinvlf (sqrtH tauE) \o
      (\sum_(x' : 'Idx[HL]_X | Fh f x' == z) cq_block disXE x' rhoXE) \o
      pinvlf (sqrtH tauE))).
Proof.
  move=> Prho Ptau Hcq; have disFE : [disjoint Fl & E] by rewrite disjoint_sym.
  have Htau_psd : tauE \is psdlf := Ptau.
  pose c : R := ((dim 'H[HL]_Fl)%:R^-1)%R.
  have HdimFlR_neq0 : ((dim 'H[HL]_Fl)%:R : R) != 0
    by rewrite pnatr_eq0 -lt0n dim_proper.
  have Hc_pos : (0 < c)%R by rewrite /c invr_gt0 ltr0n dim_proper.
  have Hc_ge0 : (0 <= c)%R := ltW Hc_pos.
  have Hsqrtc_pos : (0 < Num.sqrt c)%R by rewrite sqrtr_gt0.
  have Hsqrtc_neq0 : (Num.sqrt c != 0 :> R) := lt0r_neq0 Hsqrtc_pos.
  have HsqrtcC_neq0 : ((Num.sqrt c)%:C != 0 :> C).
    by rewrite realc_eq0.
  have Hsqrt_sq : (Num.sqrt c * Num.sqrt c = c :> R)%R
    by rewrite -expr2 sqr_sqrtr.
  pose P_E : 'F[HL]_E := pinvlf (sqrtH tauE).
  have HIFtau_psd : ((\1 : 'F_Fl) \O tauE :
                     'F[HL]_(Fl :|: E)) \is psdlf.
    have Hten : ((\1 : 'F_Fl) \O tauE :
                  'F[HL]_(Fl :|: E)) =
                (\1 : 'F_Fl) \⊗ tauE.
      by apply: to_Fnd_inj; rewrite (sdotFT _ _ disFE) to_Fnd_tenE.
    rewrite Hten psdlfE; apply: tenf_ge0; first exact: disFE.
    - exact: lef01.
    - by rewrite -psdlfE.
  have Hpinv_eq :
    pinvlf (sqrtH (c%:C *: ((\1 : 'F_Fl) \O tauE) :
                     'F[HL]_(Fl :|: E))) =
    ((Num.sqrt c)^-1)%:C *: ((\1 : 'F_Fl) \O P_E).
  { rewrite (sqrtHZ_nn Hc_ge0 HIFtau_psd).
    rewrite (pinvlfZ_nn _ Hsqrtc_neq0) (sqrtH_sdot_I disFE Htau_psd).
    by rewrite (pinvlf_sdot_I disFE). }
  rewrite /collision_ent /= -/c Hpinv_eq !sdotfZr.
  set kC : C := ((Num.sqrt c)^-1)%:C.
  set X_lift : 'F[HL]_(Zl :|: (Fl :|: E)) :=
    (\1 : 'F_Zl) \O ((\1 : 'F_Fl) \O P_E).
  rewrite -/X_lift.
  set rho_post : 'F[HL]_(Zl :|: (Fl :|: E)) :=
    post_hash_state disXE Fh rhoXE.
  have HscalarPull :
    (kC *: X_lift) \o rho_post \o (kC *: X_lift) \o rho_post =
    (kC * kC) *: (X_lift \o rho_post \o X_lift \o rho_post).
  { rewrite -!comp_lfunZl -!comp_lfunZr.
    rewrite -?comp_lfunZl -?comp_lfunZr.
    by rewrite !scalerA. }
  rewrite HscalarPull.
  rewrite linearZ /=.
  rewrite (trlf_post_hash_collision_block Fh rhoXE P_E).
  set Sum := (\sum_(_ : 'Idx[HL]_Fl) _).
  have Hc_neq0 : (c != 0 :> R) := lt0r_neq0 Hc_pos.
  have HcC_neq0 : ((c%:C : C) != 0).
  { by rewrite realc_eq0. }
  have Hk2 : (kC * kC = (c%:C)^-1 :> C)%R.
  { rewrite /kC.
    rewrite -rmorphM /=.
    rewrite -invfM Hsqrt_sq fmorphV //. }
  have Hreduce : (kC * kC * (c%:C * c%:C * Sum) = c%:C * Sum)%R.
  { rewrite Hk2.
    rewrite !mulrA mulVf // mul1r //. }
  rewrite Hreduce.
  have HRe_realM : forall x : C, @complex.Re R (c%:C * x) = c * @complex.Re R x.
  { move=> x; case: x => a b /=. by rewrite mul0r subr0. }
  rewrite HRe_realM.
  rewrite /Sum.
  rewrite raddf_sum /=.
  congr (_ * _).
  apply: eq_bigr => f _.
  by rewrite raddf_sum /=.
Qed.
(* ================================================================== *)
(* Pure combinatorial reindex identity for hash partition double sums. *)
(* Tomamichel-Schaffner-Smith-Renner, 'Leftover Hashing Against        *)
(* Quantum Side Information' (IEEE Trans. IT 57:5524 (2011);            *)
(* arXiv:1002.2436); proof step of lemma:privacy-amp (Lem. 5) Γ_C       *)
(* expansion.                                                           *)
(* math: Σ_f Σ_z Σ_{x|Fhfx=z} Σ_{x'|Fhfx'=z} T(x,x')                   *)
(*       = Σ_x Σ_x' #|{f|Fhfx=Fhfx'}|·T(x,x').                          *)
(* Consumers: Gamma_C_post_hash_expand (lhl/prop.v) and the             *)
(* almost-2-universal hash family variant.                              *)
(* ================================================================== *)
(* partition_count_double_sum *)
(* infra: no tex label — fundamental & reusable (mathcomp-style) *)
(* consumer: partition_count_double_sum is used downstream by the BB84 secrecy proof. *)
(* path: lhl:partition_count_double_sum -> lhl:Gamma_C_post_hash_expand -> *)
(*   lhl:Gamma_C_post_hash_split -> lhl:privacy_amp -> *)
(*   bb84:privacy_amplification -> bb84:bb84_secret *)
Lemma partition_count_double_sum
    (Fh : 'Idx[HL]_Fl -> 'Idx[HL]_X -> 'Idx[HL]_Zl)
    (T : 'Idx[HL]_X -> 'Idx[HL]_X -> R) :
  \sum_(f : 'Idx[HL]_Fl) \sum_(z : 'Idx[HL]_Zl)
    \sum_(x : 'Idx[HL]_X | Fh f x == z)
      \sum_(x' : 'Idx[HL]_X | Fh f x' == z) T x x' =
  \sum_(x : 'Idx[HL]_X) \sum_(x' : 'Idx[HL]_X)
    (#|[set f : 'Idx[HL]_Fl | Fh f x == Fh f x']|%:R : R) * T x x'.
Proof.
  transitivity
    (\sum_(f : 'Idx[HL]_Fl) \sum_(x : 'Idx[HL]_X)
      \sum_(x' : 'Idx[HL]_X | Fh f x' == Fh f x) T x x').
  { apply: eq_bigr => f _.
    rewrite (exchange_big_dep predT) //=.
    apply: eq_bigr => x _.
    rewrite (eq_bigl (pred1 (Fh f x))); last by move=> z /=; rewrite eq_sym.
    by rewrite big_pred1_eq. }
  transitivity
    (\sum_(x : 'Idx[HL]_X) \sum_(x' : 'Idx[HL]_X)
      \sum_(f : 'Idx[HL]_Fl | Fh f x' == Fh f x) T x x').
  { rewrite exchange_big /=; apply: eq_bigr => x _.
    by rewrite (exchange_big_dep predT). }
  apply: eq_bigr => x _.
  apply: eq_bigr => x' _.
  have HsumE : \sum_(f : 'Idx[HL]_Fl | Fh f x' == Fh f x) T x x' =
               T x x' *+ #|[pred f : 'Idx[HL]_Fl | Fh f x' == Fh f x]|.
  { by rewrite sumr_const. }
  have HK : #|[pred f : 'Idx[HL]_Fl | Fh f x' == Fh f x]| =
            #|[set f : 'Idx[HL]_Fl | Fh f x == Fh f x']|.
  { apply: eq_card => f. by rewrite !inE eq_sym. }
  rewrite HsumE HK mulr_natl.
  by [].
Qed.
End PostHashUtils.
End FvqkdReal.
