(* -------------------------------------------------------------------- *)
(* sys.v — Ambient set-labelled system infrastructure                    *)
(* -------------------------------------------------------------------- *)
(* Module: utils.labelled.sys                             *)
(* TeX source: none (library utility)                                    *)
(* TeX labels: none                                                      *)
(* -------------------------------------------------------------------- *)
(* Owns ambient set-labelled definitions and lemmas: the ptrace_cast    *)
(* family of cast-typed partial traces, castlf qualifier preservation,   *)
(* and lftrace identities on disjoint tensor/sdot. Bare matrix           *)
(* swap/ptrace infrastructure lives in mx/def.v + mx/prop.v;             *)
(* lift-adjunction helpers in labelled/lift.v.                           *)
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
From utils.mx Require Import def prop.
From utils.labelled Require Export def.
From utils.labelled Require Import op.

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
(* Basic labelled lfun facts                                          *)
(* ================================================================== *)

Section BasicLfFacts.
Variable (L : finType) (H : L -> chsType).

(* one_psdlf *)
(* infra: no tex label — fundamental & reusable (mathcomp-style) *)
(* path: utils:one_psdlf -> utils:max_entangled_ptrace -> *)
(*   utils:gamma_state_ptrace -> entropy:minmax_dual -> *)
(*   entropy:smooth_iso_hmax -> entropy:entropy_data_proc -> *)
(*   bb84:bb84_secret *)
Lemma one_psdlf (S : {set L}) : (\1 : 'F[H]_S) \is psdlf.
Proof.
  by rewrite qualifE h2mx1; exact: psdmx1.
Qed.

End BasicLfFacts.

(* ================================================================== *)
(* endlf: bridge from 'End(H i) to 'F[H]_[set i]                       *)
(* Converts a single-system endomorphism to the labeled lfun on the    *)
(* corresponding singleton label set.                                   *)
(*   math: H_A ≅ 'H[H]_[set A] via dim_setten + big_set1.              *)
(* ================================================================== *)

Section EndLf.
Variable (L : finType) (H : L -> chsType).

(* dim_set1 *)
(* infra: no tex label — fundamental & reusable (mathcomp-style) *)
(* consumer: dim_set1 is used downstream by the BB84 secrecy proof. *)
(* path: utils:dim_set1 -> eur:ucr_pure_smooth -> *)
(*   eur:entropic_uncertainty_relation -> *)
(*   eur:entropic_uncertainty_relation -> *)
(*   bb84:entropic_uncertainty_relation_bb84 -> bb84:bb84_secret *)
Lemma dim_set1 (i : L) : dim (H i) = dim 'H[H]_[set i].
Proof.
  by rewrite dim_setten big_set1.
Qed.

End EndLf.

(* ================================================================== *)
(* Labelled isometry from a dimension inequality                       *)
(* ================================================================== *)

Section IsolfFromDimLe.
Variable (L : finType) (H : L -> chsType).

(* labelled_isolf_via_dim_le *)
(* infra: no tex label — fundamental & reusable (mathcomp-style) *)
(* math: if dim H_S <= dim H_T, the row_mx [I 0] embedding gives an isometry S -> T. *)
(* path: utils:labelled_isolf_via_dim_le -> entropy:minmax_dual -> *)
(*   entropy:smooth_iso_hmax -> entropy:entropy_data_proc -> *)
(*   bb84:bb84_secret *)
Lemma labelled_isolf_via_dim_le (S T : {set L}) :
  (dim 'H[H]_S <= dim 'H[H]_T)%N ->
  exists (V : 'FI[H]_(S, T)), (V : 'F[H]_(S, T)) \is isolf.
Proof.
  move=> HleST.
  pose nS := dim 'H[H]_S.
  pose nT := dim 'H[H]_T.
  have Hle : (nS <= nT)%N by rewrite /nS /nT.
  pose R0 : 'M[C]_(nS, nS + (nT - nS)) :=
    row_mx (1%:M : 'M[C]_nS) (0 : 'M[C]_(nS, nT - nS)).
  pose RR : 'M[C]_(nS, nT) := castmx (erefl nS, subnKC Hle) R0.
  have HR_unit : RR \is unitarymx.
  { rewrite /RR castmx_funE.
    exact: (row_mx0_unitarymx _ (unitarymx1 _ _)). }
  pose Vraw : 'Hom('H[H]_S, 'H[H]_T) := mx2h RR^*t.
  have Vraw_iso : Vraw \is isolf.
  { apply/isolfP; apply/h2mx_inj.
    rewrite h2mx_comp h2mx_adj mx2hK adjmxK h2mx1.
    exact: unitarymxK HR_unit. }
  exists (IsoLf_Build Vraw_iso).
  exact: is_isolf.
Qed.

End IsolfFromDimLe.

(* ================================================================== *)
(* castlf qualifier preservation + lftrace on disjoint tensor/sdot     *)
(* + ptrace_cast family qualifier preservation.                         *)
(* ================================================================== *)

Section CastLfPreserve.
Variable (L : finType) (H : L -> chsType).

(* castlf_psdlf *)
(* infra: no tex label — fundamental & reusable (mathcomp-style) *)
(* consumer: castlf_psdlf is used downstream by the BB84 secrecy proof. *)
(* path: utils:castlf_psdlf -> entropy:entropy_data_proc -> *)
(*   bb84:bb84_secret *)
Lemma castlf_psdlf (S S' : {set L}) (eq : S = S') (f : 'F[H]_S) :
  f \is psdlf -> castlf (eq, eq) f \is psdlf.
Proof.
  by move=> Hf; case: _ / eq in f Hf *; rewrite castlf_id.
Qed.

(* castlf_hermlf *)
(* infra: no tex label — fundamental & reusable (mathcomp-style) *)
(* consumer: castlf_hermlf is used downstream by the BB84 secrecy proof. *)
(* path: utils:castlf_hermlf -> utils:castlf_psdlf -> *)
(*   entropy:entropy_data_proc -> *)
(*   bb84:bb84_secret *)
Lemma castlf_hermlf (S S' : {set L}) (eq : S = S') (f : 'F[H]_S) :
  f \is hermlf -> castlf (eq, eq) f \is hermlf.
Proof.
  by move=> Hf; case: _ / eq in f Hf *; rewrite castlf_id.
Qed.

(* castlf_psdlfE *)
(* infra: no tex label — fundamental & reusable (mathcomp-style) *)
(* consumer: castlf_psdlfE is used downstream by the BB84 secrecy proof. *)
(* path: utils:castlf_psdlfE -> entropy:entropy_data_proc -> *)
(*   bb84:bb84_secret *)
Lemma castlf_psdlfE (S S' : {set L}) (eq : S = S') (f : 'F[H]_S) :
  (castlf (eq, eq) f \is psdlf) = (f \is psdlf).
Proof.
  by case: _ / eq in f *; rewrite castlf_id.
Qed.

(* castlf_hermlfE *)
(* infra: no tex label — fundamental & reusable (mathcomp-style) *)
(* consumer: castlf_hermlfE is used downstream by the BB84 secrecy proof. *)
(* path: utils:castlf_hermlfE -> utils:castlf_psdlf -> *)
(*   entropy:entropy_data_proc -> *)
(*   bb84:bb84_secret *)
Lemma castlf_hermlfE (S S' : {set L}) (eq : S = S') (f : 'F[H]_S) :
  (castlf (eq, eq) f \is hermlf) = (f \is hermlf).
Proof.
  by case: _ / eq in f *; rewrite castlf_id.
Qed.

(* castlf_sub *)
(* infra: no tex label — fundamental & reusable (mathcomp-style) *)
(* consumer: castlf_sub is used downstream by the BB84 secrecy proof. *)
(* path: utils:castlf_sub -> lhl:min_coll_bound -> *)
(*   bb84:privacy_amplification -> bb84:bb84_secret *)
Lemma castlf_sub (S S' : {set L}) (eq : S = S') (f g : 'F[H]_S) :
  castlf (eq, eq) (f - g) = castlf (eq, eq) f - castlf (eq, eq) g.
Proof.
  by case: _ / eq in f g *; rewrite !castlf_id.
Qed.

(* Castlf-sdotf naturality on the right factor.                               *)
(* math: casting (\1_A) \O g along a B = B' equality is the same as           *)
(*       tensoring (\1_A) with (castlf g).                                    *)
(* Consumers (≥2): min_coll_bound (lhl/util.v, phi_min_feasible bridge),       *)
(*   privacy_amp (lhl/prop.v, τ_E feasibility witness unpack per              *)
(*   LHL Thm 6), and Tomamichel-feasibility bridges.                       *)
(* sdotIf_cast_r *)
(* infra: no tex label — fundamental & reusable (mathcomp-style) *)
(* consumer: sdotIf_cast_r is used downstream by the BB84 secrecy proof. *)
(* path: utils:sdotIf_cast_r -> entropy:entropy_data_proc -> *)
(*   bb84:bb84_secret *)
Lemma sdotIf_cast_r (A B B' : {set L})
    (eqB : B = B') (eqU : A :|: B = A :|: B') (g : 'F[H]_B) :
  castlf (eqU, eqU) ((\1 : 'F_A) \O g) = (\1 : 'F_A) \O (castlf (eqB, eqB) g).
Proof.
  case: B' / eqB in eqU *.
  by rewrite (eq_irrelevance eqU erefl) !castlf_id.
Qed.

(* Castlf-sdotf naturality on the left factor (symmetric). *)
(* sdotIf_cast_l *)
(* infra: no tex label — fundamental & reusable (mathcomp-style) *)
(* consumer: sdotIf_cast_l is used downstream by the BB84 secrecy proof. *)
(* path: utils:sdotIf_cast_l -> entropy:entropy_data_proc -> *)
(*   bb84:bb84_secret *)
Lemma sdotIf_cast_l (A A' B : {set L})
    (eqA : A = A') (eqU : A :|: B = A' :|: B) (f : 'F[H]_A) (g : 'F[H]_B) :
  castlf (eqU, eqU) (f \O g) = (castlf (eqA, eqA) f) \O g.
Proof.
  case: A' / eqA in eqU *.
  by rewrite (eq_irrelevance eqU erefl) !castlf_id.
Qed.

(* castlf_trlfE *)
(* infra: no tex label — fundamental & reusable (mathcomp-style) *)
(* consumer: castlf_trlfE is used downstream by the BB84 secrecy proof. *)
(* path: utils:castlf_trlfE -> entropy:entropy_data_proc -> *)
(*   bb84:bb84_secret *)
Lemma castlf_trlfE (S S' : {set L}) (eq : S = S') (f : 'F[H]_S) :
  \Tr (castlf (eq, eq) f) = \Tr f.
Proof.
  by case: _ / eq in f *; rewrite castlf_id.
Qed.

(* Partial trace commutes with set-regrouping castlf (simplified). *)
(* path: utils:ptracelf_castlf_eq -> entropy:entropy_data_proc -> *)
(*   bb84:bb84_secret *)
Lemma ptracelf_castlf_eq (S S' B : {set L}) (eq_S : S = S')
    (eq_res : S :\: B = S' :\: B) (f : 'F[H]_S) :
  \Tr_(B) (castlf (eq_S, eq_S) f) = castlf (eq_res, eq_res) (\Tr_(B) f).
Proof.
  by case: _ / eq_S in f eq_res *; rewrite (eq_irrelevance eq_res erefl) !castlf_id.
Qed.

(* lftrace_tenf *)
(* infra: no tex label — fundamental & reusable (mathcomp-style) *)
(* consumer: lftrace_tenf is used downstream by the BB84 secrecy proof. *)
(* path: utils:lftrace_tenf -> lhl:post_hash_ptrace_Z_CQ -> *)
(*   bb84:privacy_amplification -> bb84:bb84_secret *)
Lemma lftrace_tenf (S T : {set L}) (f : 'F[H]_S) (g : 'F[H]_T) :
  [disjoint S & T] ->
  \Tr (f \⊗ g) = \Tr f * \Tr g.
Proof.
  move=> dis; rewrite /lftrace h2mx_tenf.
  rewrite mxtrace_mulC mulmxA.
  have /unitarymxK : (@tenv_mxU R _ H S T)^*t \is unitarymx
    := tenv_mxU_adj_unitarymx dis.
  by rewrite adjmxK => ->; rewrite mul1mx mxtrace_tens.
Qed.

(* lftrace_sdot_disj *)
(* infra: no tex label — fundamental & reusable (mathcomp-style) *)
(* consumer: lftrace_sdot_disj is used downstream by the BB84 secrecy proof. *)
(* path: utils:lftrace_sdot_disj -> lhl:post_hash_trace_preserve -> *)
(*   bb84:privacy_amplification -> bb84:bb84_secret *)
Lemma lftrace_sdot_disj (S T : {set L}) (f : 'F[H]_S) (g : 'F[H]_T) :
  [disjoint S & T] ->
  \Tr (f \O g) = \Tr f * \Tr g.
Proof.
  move=> dis.
  have Heq : f \O g = f \⊗ g.
    by apply: to_Fnd_inj; rewrite (sdotFT _ _ dis) to_Fnd_tenE.
  by rewrite Heq lftrace_tenf.
Qed.

(* biprod_mx_trace *)
(* infra: no tex label -- trace preservation for product coordinates *)
(* path: utils:biprod_mx_trace -> entropy:smooth_hmax_labelled_mx -> *)
(*   bb84:stat -> bb84:bb84_secret *)
Lemma biprod_mx_trace
    (A B : {set L}) (disAB : [disjoint A & B])
    (f : 'F[H]_(A :|: B)) :
  \tr (biprod_mx disAB f) = \Tr f.
Proof.
  rewrite /biprod_mx /lftrace.
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
  rewrite mxtrace_mulC mulmxA HQQt mul1mx.
  by rewrite mxtrace_castmx_sq.
Qed.

(* ptrace_cast_gen_psdlf *)
(* infra: no tex label — fundamental & reusable (mathcomp-style) *)
(* consumer: ptrace_cast_gen_psdlf is used downstream by the BB84 secrecy proof. *)
(* path: utils:ptrace_cast_gen_psdlf -> entropy:entropy_data_proc -> *)
(*   bb84:bb84_secret *)
Lemma ptrace_cast_gen_psdlf (S T B : {set L})
    (eq : S :\: B = T) (f : 'F[H]_S) :
  f \is psdlf -> ptrace_cast_gen eq f \is psdlf.
Proof.
  move=> Hf; rewrite /ptrace_cast_gen.
  apply: castlf_psdlf.
  rewrite ptraceso_krausso.
  by apply: cp_psdP.
Qed.

(* ptrace_cast_psdlf *)
(* infra: no tex label — fundamental & reusable (mathcomp-style) *)
(* consumer: ptrace_cast_psdlf is used downstream by the BB84 secrecy proof. *)
(* path: utils:ptrace_cast_psdlf -> lhl:min_coll_bound -> *)
(*   bb84:privacy_amplification -> bb84:bb84_secret *)
Lemma ptrace_cast_psdlf (A B : {set L}) (disAB : [disjoint A & B])
    (f : 'F[H]_(A :|: B)) :
  f \is psdlf -> ptrace_cast disAB f \is psdlf.
Proof. exact: ptrace_cast_gen_psdlf. Qed.

(* ptrace_castl_psdlf *)
(* infra: no tex label — fundamental & reusable (mathcomp-style) *)
(* consumer: ptrace_castl_psdlf is used downstream by the BB84 secrecy proof. *)
(* path: utils:ptrace_castl_psdlf -> lhl:min_coll_bound -> *)
(*   bb84:privacy_amplification -> bb84:bb84_secret *)
Lemma ptrace_castl_psdlf (A B : {set L}) (disAB : [disjoint A & B])
    (f : 'F[H]_(A :|: B)) :
  f \is psdlf -> ptrace_castl disAB f \is psdlf.
Proof. exact: ptrace_cast_gen_psdlf. Qed.

End CastLfPreserve.

(* ================================================================== *)
(* Bridge: labeled ptrace_cast ↔ matrix ptrace2 via tenv_mxU          *)
(* (Uhlmann/Gram route).                          *)
(* Consumers: pd_mono_ptrace, pd_uhl, pd_ext, pd_metric_triangle       *)
(* (all in utils/dist/pd.v) via gfid ↔ gfidelity (h2mx _).     *)
(* ================================================================== *)

Section PTraceCastBridge.
Variable (L : finType) (HL : L -> chsType) (A B : {set L}).
Hypothesis disAB : [disjoint A & B].

Let S_AB := (A :|: B).

(* Entry-wise formula for h2mx (ptrace_cast disAB rho).                        *)
(* This unfolds ptraceso_fun.unlock and evaluates on delta-basis vectors. The  *)
(* summation is over 'Idx[HL]_B (the traced-out system), with index-cast *)
(* from 'I_(dim 'H_A) to 'Idx_((A:|:B):\: B) via       *)
(* setDU_r disAB.                                                              *)
(* h2mx_ptrace_cast_dec *)
(* infra: no tex label — fundamental & reusable (mathcomp-style) *)
(* consumer: h2mx_ptrace_cast_dec is used downstream by the BB84 secrecy proof. *)
(* path: utils:h2mx_ptrace_cast_dec -> utils:h2mx_ptrace_cast_ptrace2 -> *)
(*   entropy:entropy_data_proc -> *)
(*   bb84:bb84_secret *)
Lemma h2mx_ptrace_cast_dec (rho : 'F[HL]_S_AB)
    (i j : 'I_(dim 'H[HL]_A)) :
  h2mx (ptrace_cast disAB rho) i j =
  \sum_(k : 'Idx[HL]_(S_AB :&: B))
    [< deltav (idxU k (castidx (esym (setDU_r disAB)) (n2i i))) ;
       castlf (esym (setID S_AB B), esym (setID S_AB B)) rho
         (deltav (idxU k (castidx (esym (setDU_r disAB)) (n2i j)))) >].
Proof.
  rewrite /ptrace_cast /ptrace_cast_gen h2mx_dec.
  have eb_dv : forall (x : 'I_(dim 'H[HL]_A)),
    eb x = deltav (n2i x) :> 'H[HL]_A.
  { by move=> x; rewrite deltav.unlock n2iK. }
  rewrite !eb_dv.
  rewrite castlfE casths_dotr !deltav_cast.
  set a1 := castidx _ (n2i i).
  set a2 := castidx _ (n2i j).
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
  (* Inner j0 sum collapses to j0 = a2 *)
  under eq_bigr => i0 _.
    rewrite (bigD1 a2)//= eqxx mul1r big1 ?addr0.
    2: by move=> j0 /negPf ->; rewrite mul0r mulr0.
    over.
  simpl.
  (* Outer i0 sum collapses to i0 = a1 *)
  rewrite (bigD1 a1)//= eqxx mulr1 big1 ?addr0//.
  by move=> i0 /negPf ni0; rewrite [a1 == i0]eq_sym ni0 mulr0.
Qed.

(* Entry-wise formula for ptrace2 (U^*t *m h2mx rho *m U) where U = tenv_mxU.    *)
(* Directly computes matrix entries using mxE + tensmxE + tenv_mxU's delta form.  *)
(* ptrace2_tenv_mxU_conj_dec *)
(* infra: no tex label — fundamental & reusable (mathcomp-style) *)
(* consumer: ptrace2_tenv_mxU_conj_dec is used downstream by the BB84 secrecy proof. *)
(* path: utils:ptrace2_tenv_mxU_conj_dec -> utils:h2mx_ptrace_cast_ptrace2 -> *)
(*   entropy:entropy_data_proc -> *)
(*   bb84:bb84_secret *)
Lemma ptrace2_tenv_mxU_conj_dec (rho : 'F[HL]_S_AB)
    (i j : 'I_(dim 'H[HL]_A)) :
  ptrace2 ((@tenv_mxU R L HL A B)^*t *m h2mx rho *m
           (@tenv_mxU R L HL A B)) i j =
  \sum_(k : 'I_(dim 'H[HL]_B))
    [< deltav (idxU (n2i i) (n2i k)) ;
       rho (deltav (idxU (n2i j) (n2i k))) >].
Proof.
  rewrite ptrace2E1 ptrace1E.
  apply: eq_bigr => k _.
  rewrite mxE !mxtens_indexK/=.
  (* matrix multiplication expansion *)
  rewrite mxE (bigD1 (tenv_indexl (mxtens_index (j, k))))//= big1 ?addr0.
  2: {
    move=> q Hq.
    rewrite !mxE /= (can2_eq (@tenv_indexrK R L HL A B) (tenv_indexlK disAB)).
    by rewrite (negPf Hq) !mulr0.
  }
  rewrite mxE (bigD1 (tenv_indexl (mxtens_index (i, k))))//= big1 ?addr0.
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

(* Key index identity bridging the LHS cast chain (setID + setDU_r + eqIB) and  *)
(* the canonical A-first / B-second idxU ordering on S_AB = A :|: B. *)
(* Proof: characterize both sides via idxSl / idxSr projections onto A and *)
(* B; use idxBE (which states that idxU on a union is uniquely determined  *)
(* by its left and right projections) to conclude.                                *)
(* Helper: applying n2i at two 'exist' elements with the same val but different
   proofs yields the same ordinal, since bool-valued proofs are irrelevant. *)
(* n2i_exist_irr *)
(* infra: no tex label — fundamental & reusable (mathcomp-style) *)
(* consumer: n2i_exist_irr is used downstream by the BB84 secrecy proof. *)
(* path: utils:n2i_exist_irr -> utils:castidx_setID_idxU_eq -> *)
(*   utils:h2mx_ptrace_cast_ptrace2 -> entropy:entropy_data_proc -> *)
(*   bb84:bb84_secret *)
Lemma n2i_exist_irr (S : {set L}) (k : 'I_(dim 'H[HL]_S)) (a : L)
    (p1 p2 : a \in S) :
  (n2i k : 'Idx[HL]_S) (exist _ a p1) = (n2i k) (exist _ a p2).
Proof.
  by rewrite (bool_irrelevance p1 p2).
Qed.

(* castidx_setID_idxU_eq *)
(* infra: no tex label — fundamental & reusable (mathcomp-style) *)
(* consumer: castidx_setID_idxU_eq is used downstream by the BB84 secrecy proof. *)
(* path: utils:castidx_setID_idxU_eq -> utils:h2mx_ptrace_cast_ptrace2 -> *)
(*   entropy:entropy_data_proc -> *)
(*   bb84:bb84_secret *)
Lemma castidx_setID_idxU_eq
    (eqIB : S_AB :&: B = B)
    (k : 'I_(dim 'H[HL]_B))
    (i : 'I_(dim 'H[HL]_A)) :
  castidx (setID S_AB B)
    (idxU (castidx (esym eqIB) (n2i k))
          (castidx (esym (setDU_r disAB)) (n2i i)))
  = idxU (n2i i) (n2i k).
Proof.
  apply/idxP => x.
  rewrite castidx_app /= idxE.
  have Hx_in : val x \in S_AB by case: x => /= ?.
  case: eqP => HA.
  - rewrite castidx_app /=.
    have HB : val x \in B by move/setIP: HA => [].
    have HnA : (val x \in A) = false.
      by apply/negP => HA'; move/disjointP: disAB => /(_ _ HA'); rewrite HB.
    rewrite idxE.
    case: eqP => HAr; first by rewrite HAr in HnA.
    exact: n2i_exist_irr.
  - rewrite castidx_app /=.
    have HnB : (val x \in B) = false.
      by apply/negP => HB; apply: HA; rewrite inE Hx_in HB.
    have HA' : val x \in A.
      have Hx2 := Hx_in.
      rewrite finset.in_setU in Hx2.
      case/orP: Hx2 => [// | HxB].
      by rewrite HxB in HnB.
    rewrite idxE.
    case: eqP => HAr; last by case: (HAr HA').
    exact: n2i_exist_irr.
Qed.

(* Full bridge: labeled ptrace_cast ↔ matrix ptrace2 via tenv_mxU conjugation. *)
(* h2mx_ptrace_cast_ptrace2 *)
(* infra: no tex label — fundamental & reusable (mathcomp-style) *)
(* consumer: h2mx_ptrace_cast_ptrace2 is used downstream by the BB84 secrecy proof. *)
(* path: utils:h2mx_ptrace_cast_ptrace2 -> entropy:entropy_data_proc -> *)
(*   bb84:bb84_secret *)
Lemma h2mx_ptrace_cast_ptrace2 (rho : 'F[HL]_S_AB) :
  h2mx (ptrace_cast disAB rho) =
  ptrace2 ((@tenv_mxU R L HL A B)^*t *m h2mx rho *m
           (@tenv_mxU R L HL A B)).
Proof.
  apply/matrixP => i j.
  rewrite h2mx_ptrace_cast_dec ptrace2_tenv_mxU_conj_dec.
  have eqIB : S_AB :&: B = B.
  {
    by have /finset.setIidPr-> := @finset.subsetUr _ A B.
  }
  rewrite (reindex (fun k : 'I_(dim 'H[HL]_B) =>
    castidx (esym eqIB) (n2i k))) /=.
  2: {
    exists (fun k : 'Idx[HL]_(S_AB :&: B) =>
      i2n (castidx eqIB k)) => k _.
    - by rewrite castidx_comp (eq_irrelevance (etrans _ _) (erefl _)) castidx_id n2iK.
    - by rewrite i2nK castidx_comp (eq_irrelevance (etrans _ _) (erefl _)) castidx_id.
  }
  apply: eq_bigr => k _.
  rewrite castlfE casths_dotr !deltav_cast esymK.
  by rewrite !(castidx_setID_idxU_eq eqIB).
Qed.

(* Matrix-level commute fact: tracing out the right factor is invariant   *)
(* under an isometry sandwich on that right factor.                       *)
(* ptrace2_tens_iso_right *)
(* infra: no tex label — fundamental & reusable (mathcomp-style) *)
(* consumer: ptrace2_tens_iso_right is used downstream by the BB84 secrecy proof. *)
(* path: utils:ptrace2_tens_iso_right -> utils:ptrace_cast_isometry_conj -> *)
(*   entropy:smooth_iso_hmax -> entropy:entropy_data_proc -> *)
(*   bb84:bb84_secret *)
Lemma ptrace2_tens_iso_right {a b b' : nat}
    (U : 'M[C]_(b', b)) (M : 'M[C]_(a * b)) :
  U^*t *m U = 1%:M ->
  ptrace2
    ((((1%:M : 'M[C]_a) *t U) *m M) *m
       (((1%:M : 'M[C]_a) *t U)^*t)) =
  ptrace2 M.
Proof.
  move=> HU.
  have ptrace2E' : forall s t (N : 'M[C]_(s * t)) r1 r2,
    (ptrace2 N) r1 r2 =
    \sum_l N (mxtens_index (r1, l)) (mxtens_index (r2, l)).
  {
    move=> s t N r1 r2.
    rewrite ptrace2E1 ptrace1E.
    by apply: eq_bigr => l _; rewrite mxE !mxtens_indexK.
  }
  apply/matrixP => i j.
  rewrite !ptrace2E'.
  pose Rt := (((1%:M : 'M[C]_a) *t U)^*t).
  have HleftMul :
      forall (N : 'M[C]_(a * b, a * b')) (k : 'I_b') (t : 'I_(a * b')),
        ((((1%:M : 'M[C]_a) *t U) *m N)
           (mxtens_index (i, k)) t) =
        \sum_(k1 : 'I_b) U k k1 * N (mxtens_index (i, k1)) t.
  {
    move=> N k t.
    rewrite (tensmxE_mid (((1%:M : 'M[C]_a) *t U)) N
      (mxtens_index (i, k)) t).
    transitivity
      (\sum_(i1 : 'I_a) \sum_(k1 : 'I_b)
        ((i == i1)%:R * U k k1) * N (mxtens_index (i1, k1)) t).
    {
      apply: eq_bigr => i1 _.
      apply: eq_bigr => k1 _.
      by rewrite tensmxE !mxE -mulrA.
    }
    transitivity
      (\sum_(i1 : 'I_a)
        (i == i1)%:R *
        \sum_(k1 : 'I_b) U k k1 * N (mxtens_index (i1, k1)) t).
    {
      apply: eq_bigr => i1 _.
      rewrite mulr_sumr.
      by apply: eq_bigr => k1 _; rewrite -mulrA.
    }
    rewrite (bigD1 i) //= eqxx mul1r.
    rewrite [X in _ + X]big1 ?addr0 //.
    by move=> i1 Hi1; rewrite eq_sym (negPf Hi1) mul0r.
  }
  have HrightMul :
      forall (k1 : 'I_b) (k : 'I_b'),
        (M *m Rt) (mxtens_index (i, k1)) (mxtens_index (j, k)) =
        \sum_(k2 : 'I_b)
          M (mxtens_index (i, k1)) (mxtens_index (j, k2)) *
          (U^*t) k2 k.
  {
    move=> k1 k.
    rewrite /Rt.
    rewrite (tensmxE_mid M (((1%:M : 'M[C]_a) *t U)^*t)
      (mxtens_index (i, k1)) (mxtens_index (j, k))).
    transitivity
      (\sum_(j1 : 'I_a) \sum_(k2 : 'I_b)
        ((j == j1)%:R *
          M (mxtens_index (i, k1)) (mxtens_index (j1, k2))) *
        (U^*t) k2 k).
    {
      apply: eq_bigr => j1 _.
      apply: eq_bigr => k2 _.
      rewrite /Rt adjmx_tens adjmx1.
      rewrite tensmxE !mxE eq_sym.
      rewrite -mulrA.
      by rewrite mulrCA.
    }
    transitivity
      (\sum_(j1 : 'I_a)
        (j == j1)%:R *
        \sum_(k2 : 'I_b)
          M (mxtens_index (i, k1)) (mxtens_index (j1, k2)) *
          (U^*t) k2 k).
    {
      apply: eq_bigr => j1 _.
      rewrite mulr_sumr.
      by apply: eq_bigr => k2 _; rewrite -mulrA.
    }
    rewrite (bigD1 j) //= eqxx mul1r.
    rewrite [X in _ + X]big1 ?addr0 //.
    by move=> j1 Hj1; rewrite eq_sym (negPf Hj1) mul0r.
  }
  transitivity
    (\sum_(k : 'I_b') \sum_(k1 : 'I_b)
      U k k1 * (M *m Rt) (mxtens_index (i, k1)) (mxtens_index (j, k))).
  {
    apply: eq_bigr => k _.
    by rewrite -mulmxA HleftMul.
  }
  rewrite exchange_big /=.
  transitivity
    (\sum_(k1 : 'I_b) \sum_(k2 : 'I_b)
      M (mxtens_index (i, k1)) (mxtens_index (j, k2)) *
      \sum_(k : 'I_b') (U^*t) k2 k * U k k1).
  {
    apply: eq_bigr => k1 _.
    transitivity
      (\sum_(k : 'I_b') \sum_(k2 : 'I_b)
        M (mxtens_index (i, k1)) (mxtens_index (j, k2)) *
        ((U^*t) k2 k * U k k1)).
    - apply: eq_bigr => k _.
      rewrite HrightMul mulr_sumr.
      apply: eq_bigr => k2 _.
      rewrite mulrA [U k k1 * _]mulrC -mulrA.
      by rewrite [(U k k1) * _]mulrC.
    - rewrite exchange_big /=.
      apply: eq_bigr => k2 _.
      by rewrite -mulr_sumr.
  }
  transitivity
    (\sum_(k1 : 'I_b) \sum_(k2 : 'I_b)
      M (mxtens_index (i, k1)) (mxtens_index (j, k2)) *
      ((U^*t *m U) k2 k1)).
  {
    apply: eq_bigr => k1 _.
    by apply: eq_bigr => k2 _; rewrite mxE.
  }
  rewrite HU.
  transitivity
    (\sum_(k1 : 'I_b)
      M (mxtens_index (i, k1)) (mxtens_index (j, k1))).
  {
    apply: eq_bigr => k1 _.
    rewrite (bigD1 k1) //= mxE !eqxx /= mulr1.
    rewrite big1 ?addr0 //.
    move=> k2 Hk2; rewrite mxE.
    have -> : (k2 == k1) = false by rewrite (negPf Hk2).
    by rewrite /= mulr0.
  }
  by [].
Qed.

(* Matrix-level commute fact: tracing out the right factor commutes with    *)
(* (X *t I)-sandwich on the left factor, including dimension-changing X.   *)
(* Used by ptrace_cast3B_formso_commute and smooth-duality marginal bridges. *)
(* ptrace2_tens_id_sandwich *)
(* infra: no tex label — fundamental & reusable (mathcomp-style) *)
(* consumer: ptrace2_tens_id_sandwich is used downstream by the BB84 secrecy proof. *)
(* path: utils:ptrace2_tens_id_sandwich -> entropy:minmax_dual -> *)
(*   entropy:smooth_iso_hmax -> entropy:entropy_data_proc -> *)
(*   bb84:bb84_secret *)
Lemma ptrace2_tens_id_sandwich {a a' b : nat}
    (X : 'M[C]_(a', a)) (Y : 'M[C]_(a, a')) (M : 'M[C]_(a * b)) :
  ptrace2 ((X *t (1%:M : 'M[C]_b)) *m M *m (Y *t (1%:M : 'M[C]_b)))
  = X *m ptrace2 M *m Y.
Proof.
  apply/matrixP => i j.
  have ptrace2E' : forall s t (B' : 'M[C]_(s * t)) r1 r2,
    (ptrace2 B') r1 r2 = \sum_l B' (mxtens_index (r1, l)) (mxtens_index (r2, l)).
  { move=> s t B' r1 r2.
    rewrite ptrace2E1 ptrace1E.
    by apply: eq_bigr => l _; rewrite mxE !mxtens_indexK. }
  pose TS := \sum_(l : 'I_b) \sum_(i' : 'I_a) \sum_(j' : 'I_a)
    X i i' * M (mxtens_index (i', l)) (mxtens_index (j', l)) * Y j' j.
  have HLeft : (ptrace2 ((X *t (1%:M : 'M[C]_b)) *m M *m
                       (Y *t (1%:M : 'M[C]_b)))) i j = TS.
  { rewrite ptrace2E' /TS; apply: eq_bigr => l _.
    rewrite -mulmxA.
    transitivity
      (\sum_(i' : 'I_a)
         X i i' * (M *m (Y *t (1%:M : 'M[C]_b)))
                    (mxtens_index (i', l)) (mxtens_index (j, l))).
    { rewrite (tensmxE_mid (X *t _) _ _ _).
      transitivity
        (\sum_(i' : 'I_a) \sum_(k1 : 'I_b)
           (X i i' * (l == k1)%:R) *
           (M *m (Y *t (1%:M : 'M[C]_b)))
             (mxtens_index (i', k1)) (mxtens_index (j, l))).
      { apply: eq_bigr => i' _; apply: eq_bigr => k1 _.
        by rewrite tensmxE mxE. }
      apply: eq_bigr => i' _.
      rewrite (bigD1 l)//= eqxx mulr1 [X in _ + X]big1 ?addr0//.
      by move=> k1 /negbTE Hk; rewrite eq_sym Hk mulr0 mul0r. }
    apply: eq_bigr => i' _.
    rewrite (tensmxE_mid M (Y *t _) _ _).
    rewrite mulr_sumr.
    transitivity
      (\sum_(j' : 'I_a) \sum_(k2 : 'I_b)
        X i i' * (M (mxtens_index (i', l)) (mxtens_index (j', k2)) *
                    (Y j' j * (k2 == l)%:R))).
    { apply: eq_bigr => j' _; rewrite mulr_sumr; apply: eq_bigr => k2 _.
      by rewrite tensmxE mxE. }
    apply: eq_bigr => j' _.
    rewrite (bigD1 l)//= eqxx mulr1 [X in _ + X]big1 ?addr0; last first.
      move=> k2 Hk2.
      by rewrite (negbTE Hk2) /= !mulr0.
    by rewrite mulrA. }
  have HRight : (X *m ptrace2 M *m Y) i j = TS.
  { rewrite /TS mxE.
    under eq_bigr => i' _ do rewrite mxE big_distrl/=.
    (* RHS now: \sum_(i') \sum_(i'') X i i'' * (ptrace2 M) i'' i' * Y i' j   *)
    transitivity (\sum_(i' : 'I_a) \sum_(i'' : 'I_a) \sum_(l : 'I_b)
       X i i'' * M (mxtens_index (i'', l)) (mxtens_index (i', l)) * Y i' j).
    { apply: eq_bigr => i' _; apply: eq_bigr => i'' _.
      by rewrite ptrace2E' mulr_sumr mulr_suml. }
    (* Reorder big sums: i', i'', l  -->  l, i'', i' (rename i' to j', i'' to i' in TS) *)
    (* Use exchange_big to bubble l to outer. *)
    rewrite exchange_big/=. (* now i'', i', l *)
    under eq_bigr do rewrite exchange_big/=.
    (* now i'', l, i' *)
    rewrite exchange_big/=.
    (* now l, i'', i' *)
    apply: eq_bigr => l _.
    by apply: eq_bigr => i'' _; apply: eq_bigr => i' _. }
  by rewrite HLeft HRight.
Qed.

(* Partial-trace ↔ formso commutation in labelled form: tracing out B from    *)
(* (P \⊗ \1_B) sandwiches on F_(A∪B) commutes with conjugation by P on F_A.  *)
(* Mathematical fact: tr_B((P⊗I)ρ(P⊗I)) = P (tr_B ρ) P. Note: here the      *)
(* section's `A` plays the surviving register and `B` the traced register;   *)
(* the 3-register form follows by setting `A := A0 :|: B0`.   *)
(* ptrace_cast3B_formso_commute *)
(* infra: no tex label — fundamental & reusable (mathcomp-style) *)
(* consumer: ptrace_cast3B_formso_commute is used downstream by the BB84 secrecy proof. *)
(* path: utils:ptrace_cast3B_formso_commute -> *)
(*   entropy:smoothing_support_hmax -> entropy:smooth_iso_hmax -> *)
(*   entropy:entropy_data_proc -> *)
(*   bb84:bb84_secret *)
Lemma ptrace_cast3B_formso_commute
    (rho : 'F[HL]_S_AB) (P : 'F[HL]_A) :
  ptrace_cast disAB ((P \⊗ (\1 : 'F[HL]_B)) \o rho \o (P \⊗ (\1 : 'F[HL]_B)))
  = P \o ptrace_cast disAB rho \o P.
Proof.
  apply/h2mx_inj.
  rewrite !h2mx_comp.
  rewrite !(h2mx_ptrace_cast_ptrace2).
  rewrite !h2mx_comp.
  rewrite !h2mx_tenf h2mx1.
  set U := @tenv_mxU R L HL A B.
  set X := h2mx P.
  set M := h2mx rho.
  have HUUadj : U *m U^*t = 1%:M.
  { by apply/unitarymxK; exact: tenv_mxU_unitarymx. }
  have HUadjU : U^*t *m U = 1%:M.
  { have /unitarymxK : U^*t \is unitarymx
      := tenv_mxU_adj_unitarymx disAB.
    by rewrite adjmxK => ->. }
  (* Goal:
     ptrace2 (U^*t *m (U *m (X *t 1) *m U^*t *m M *m
                         U *m (X *t 1) *m U^*t) *m U)
     = X *m ptrace2 (U^*t *m M *m U) *m X.                             *)
  rewrite -ptrace2_tens_id_sandwich; congr ptrace2.
  by rewrite !mulmxA ?HUadjU ?mul1mx ?mulmx1
    -?mulmxA ?HUadjU ?mul1mx ?mulmx1.
Qed.

End PTraceCastBridge.

Section PTraceCastIsoConj.
Variable (L : finType) (HL : L -> chsType).
Variables (A B A' B' : {set L}).
Hypothesis disAB : [disjoint A & B].
Hypothesis disA'B' : [disjoint A' & B'].

(* Dimension-changing labelled partial-trace/isometry bridge.             *)
(* ptrace_cast_isometry_conj *)
(* infra: no tex label — fundamental & reusable (mathcomp-style) *)
(* consumer: ptrace_cast_isometry_conj is used downstream by the BB84 secrecy proof. *)
(* path: utils:ptrace_cast_isometry_conj -> entropy:smooth_iso_hmax -> *)
(*   entropy:entropy_data_proc -> *)
(*   bb84:bb84_secret *)
Lemma ptrace_cast_isometry_conj
    (rho : 'F[HL]_(A :|: B))
    (U : 'FI[HL]_(A, A')) (V : 'FI[HL]_(B, B')) :
  ptrace_cast disA'B' ((U \⊗ V) \o rho \o (U \⊗ V)^A) =
  U \o ptrace_cast disAB rho \o U^A.
Proof.
  apply/h2mx_inj.
  pose UA := h2mx U.
  pose VB := h2mx V.
  pose W := U \⊗ V.
  pose T := @tenv_mxU R L HL A B.
  pose T' := @tenv_mxU R L HL A' B'.
  have HUA : UA^*t *m UA = 1%:M.
  { have := f_equal h2mx (isofE U).
    by rewrite h2mx_comp h2mx_adj h2mx1. }
  have HVB : VB^*t *m VB = 1%:M.
  { have := f_equal h2mx (isofE V).
    by rewrite h2mx_comp h2mx_adj h2mx1. }
  have HW_mx : h2mx W = T' *m (UA *t VB) *m T^*t
    by rewrite /W /UA /VB /T /T' h2mx_tenf.
  have HWA_mx : h2mx W^A = T *m ((UA *t VB)^*t *m T'^*t).
  { rewrite h2mx_adj HW_mx adjmxM adjmxK.
    have -> : (T' *m (UA *t VB))^*t = (UA *t VB)^*t *m T'^*t
      by rewrite adjmxM.
    by rewrite adjmx_tens mulmxA. }
  have HT'K : T'^*t *m T' = 1%:M.
  { have /unitarymxK : T'^*t \is unitarymx :=
      tenv_mxU_adj_unitarymx disA'B'.
    by rewrite adjmxK. }
  rewrite (@h2mx_ptrace_cast_ptrace2 L HL A' B' disA'B'
    ((U \⊗ V) \o rho \o (U \⊗ V)^A)).
  rewrite !h2mx_comp HW_mx HWA_mx.
  rewrite !mulmxA HT'K !mul1mx.
  rewrite -!mulmxA HT'K ?mulmx1 //.
  pose dAp := dim 'H[HL]_A'.
  have Hfact :
      (UA *t VB) =
      (((1%:M : 'M[C]_dAp) *t VB) *m
       (UA *t (1%:M : 'M[C]_(dim 'H[HL]_B)))).
  {
    apply/matrixP => i j.
    case: (mxtens_indexP i) => iA iB.
    case: (mxtens_indexP j) => jA jB.
    rewrite tensmxE.
    symmetry.
    rewrite (tensmxE_mid
      (((1%:M : 'M[C]_dAp) *t VB))
      (UA *t (1%:M : 'M[C]_(dim 'H[HL]_B)))
      (mxtens_index (iA, iB)) (mxtens_index (jA, jB))).
    transitivity
      (\sum_(kA : 'I_dAp)
         \sum_(kB : 'I_(dim 'H[HL]_B))
           (((iA == kA)%:R * VB iB kB) *
            (UA kA jA * (kB == jB)%:R))).
    {
      apply: eq_bigr => kA _.
      apply: eq_bigr => kB _.
      by rewrite !tensmxE !mxE.
    }
    transitivity
      (\sum_(kA : 'I_dAp)
         ((iA == kA)%:R * UA kA jA) *
         \sum_(kB : 'I_(dim 'H[HL]_B))
           VB iB kB * (kB == jB)%:R).
    {
      apply: eq_bigr => kA _.
      rewrite mulr_sumr.
      apply: eq_bigr => kB _.
      rewrite -!mulrA.
      congr ((iA == kA)%:R * _).
      rewrite mulrA.
      rewrite [VB iB kB * UA kA jA]mulrC.
      by rewrite -mulrA.
    }
    transitivity
      (\sum_(kA : 'I_dAp)
         ((iA == kA)%:R * UA kA jA) * (VB iB jB)).
    {
      apply: eq_bigr => kA _.
      have -> :
          \sum_(kB : 'I_(dim 'H[HL]_B))
            VB iB kB * (kB == jB)%:R =
          VB iB jB.
      {
        rewrite (bigD1 jB) //= eqxx mulr1.
        rewrite [X in _ + X]big1 ?addr0 // => kB HkB.
        move: HkB.
        rewrite eq_sym.
        move/negPf=> ->.
        by rewrite mulr0.
      }
      reflexivity.
    }
    transitivity
      ((\sum_(kA : 'I_dAp)
          (iA == kA)%:R * UA kA jA) * (VB iB jB)).
    - by rewrite -mulr_suml.
    have -> :
        \sum_(kA : 'I_dAp)
          (iA == kA)%:R * UA kA jA =
        UA iA jA.
    {
      rewrite (bigD1 iA) //= eqxx mul1r.
      rewrite [X in _ + X]big1 ?addr0 // => kA HiA.
      by rewrite eq_sym (negPf HiA) mul0r.
    }
    reflexivity.
  }
  pose IB := (1%:M : 'M[C]_(dim 'H[HL]_B)).
  pose LV := ((1%:M : 'M[C]_dAp) *t VB).
  pose LU := (UA *t IB).
  pose M0 := (T^*t *m h2mx rho *m T).
  rewrite Hfact.
  rewrite /LV /LU /M0 /IB.
  transitivity
    (ptrace2
       (((((1%:M : 'M[C]_dAp) *t VB) *m
          (((UA *t (1%:M : 'M[C]_(dim 'H[HL]_B))) *m
            (T^*t *m h2mx rho *m T)) *m
           (UA *t (1%:M : 'M[C]_(dim 'H[HL]_B)))^*t))) *m
         (((1%:M : 'M[C]_dAp) *t VB)^*t))).
  { by rewrite adjmxM !mulmxA -!mulmxA. }
  rewrite ptrace2_tens_iso_right //.
  rewrite adjmx_tens adjmx1.
  rewrite ptrace2_tens_id_sandwich.
  rewrite (@h2mx_ptrace_cast_ptrace2 L HL A B disAB rho).
  by rewrite /UA h2mx_adj mulmxA.
Qed.

End PTraceCastIsoConj.

(* ================================================================== *)
(* 3-register ptrace-formso commutation:                                *)
(* Tr_B((PA⊗1_B⊗1_C)·ρ·(PA⊗1_B⊗1_C)) = (PA⊗1_C)·Tr_B(ρ)·(PA⊗1_C)   *)
(* where Tr_B is ptrace_cast3B tracing B from (A:|:B):|:C.             *)
(* ================================================================== *)

Section PTraceCast3BFormso.
Variable (L : finType) (HL : L -> chsType).
Variables (A B C : {set L}).
Hypothesis disAB : [disjoint A & B].
Hypothesis disBC : [disjoint B & C].
Hypothesis disAC : [disjoint A & C].

(* ptrace_cast3B_formso_commute_AC *)
(* infra: no tex label — fundamental & reusable (mathcomp-style) *)
(* consumer: ptrace_cast3B_formso_commute_AC is used downstream by the BB84 secrecy proof. *)
(* path: utils:ptrace_cast3B_formso_commute_AC -> *)
(*   entropy:smoothing_support_hmax -> entropy:smooth_iso_hmax -> *)
(*   entropy:entropy_data_proc -> *)
(*   bb84:bb84_secret *)
Lemma ptrace_cast3B_formso_commute_AC
    (rho : 'F[HL]_(A :|: B :|: C)) (P : 'F[HL]_A) :
  let _ := disAC in
  ptrace_cast3B disAB disBC
    (((P \⊗ (\1 : 'F[HL]_B)) \⊗ (\1 : 'F[HL]_C)) \o rho \o
     ((P \⊗ (\1 : 'F[HL]_B)) \⊗ (\1 : 'F[HL]_C)))
  = (P \⊗ (\1 : 'F[HL]_C)) \o ptrace_cast3B disAB disBC rho \o
    (P \⊗ (\1 : 'F[HL]_C)).
Proof.
  rewrite /ptrace_cast3B /ptrace_cast_gen.
  (* Regroup (PA⊗1_B)⊗1_C to (PA⊗1_C)⊗1_B via setUC_swap3. *)
  set eqS := setUC_swap3 A B C : A :|: B :|: C = A :|: C :|: B.
  have disAC_B : [disjoint A :|: C & B].
  { have disCB : [disjoint C & B] by rewrite disjoint_sym.
    by rewrite disjointUX disAB disCB. }
  (* Cast rho and the operators to live on (A:|:C):|:B. *)
  set rho' := castlf (eqS, eqS) rho.
  set PAC := P \⊗ (\1 : 'F[HL]_C).
  set PAC_B := PAC \⊗ (\1 : 'F[HL]_B) : 'F[HL]_(A :|: C :|: B).
  (* Key: (PA⊗1_B)⊗1_C cast to (A:|:C):|:B = (PA⊗1_C)⊗1_B. *)
  have Hcast_op : castlf (eqS, eqS)
      ((P \⊗ (\1 : 'F[HL]_B)) \⊗ (\1 : 'F[HL]_C)) = PAC_B.
  { rewrite /PAC_B /PAC.
    to_Fnd.
    by rewrite -!tenFA (tenFC (to_Fnd (\1 : 'F[HL]_B))
      (to_Fnd (\1 : 'F[HL]_C))) !tenFA. }
  (* Rewrite LHS composition through the cast. *)
  have Hcomp_cast :
    castlf (eqS, eqS)
      (((P \⊗ (\1 : 'F[HL]_B)) \⊗ (\1 : 'F[HL]_C)) \o rho \o
       ((P \⊗ (\1 : 'F[HL]_B)) \⊗ (\1 : 'F[HL]_C)))
    = PAC_B \o rho' \o PAC_B.
  { rewrite /rho' /PAC_B /PAC.
    to_Fnd.
    by rewrite -!tenFA (tenFC (to_Fnd (\1 : 'F[HL]_B))
      (to_Fnd (\1 : 'F[HL]_C))) !tenFA. }
  (* Push the cast through the partial trace. *)
  have eq_res : (A :|: B :|: C) :\: B = (A :|: C :|: B) :\: B.
  { by rewrite eqS. }
  have Hptrace_recast (f : 'F[HL]_(A :|: B :|: C)) :
    castlf (setDU3_B disAB disBC, setDU3_B disAB disBC) (\Tr_(B) f) =
    ptrace_cast disAC_B (castlf (eqS, eqS) f).
  { rewrite /ptrace_cast /ptrace_cast_gen.
    rewrite (ptracelf_castlf_eq eqS eq_res).
    rewrite castlf_comp.
    by congr (castlf (_, _) _); exact: eq_irrelevance. }
  (* Apply the 2-register ptrace_cast commutation on space (A:|:C):|:B. *)
  have Hptrace2 :
    ptrace_cast disAC_B (PAC_B \o rho' \o PAC_B) =
    PAC \o ptrace_cast disAC_B rho' \o PAC.
  { exact: (ptrace_cast3B_formso_commute disAC_B rho' PAC). }
  rewrite !Hptrace_recast Hcomp_cast -/rho'.
  exact: Hptrace2.
Qed.

(* ptrace_cast3C_formso_commute_AB *)
(* infra: no tex label — fundamental & reusable (mathcomp-style) *)
(* consumer: qkd.example.execution.state uses this to relate executable *)
(*   Alice-measurement branches to the EUR cq-block operator shape.      *)
Lemma ptrace_cast3C_formso_commute_AB
    (rho : 'F[HL]_(A :|: B :|: C)) (P : 'F[HL]_A) :
  ptrace_cast3C disAC disBC
    (((P \⊗ (\1 : 'F[HL]_B)) \⊗ (\1 : 'F[HL]_C)) \o rho \o
     ((P \⊗ (\1 : 'F[HL]_B)) \⊗ (\1 : 'F[HL]_C)))
  = (P \⊗ (\1 : 'F[HL]_B)) \o ptrace_cast3C disAC disBC rho \o
    (P \⊗ (\1 : 'F[HL]_B)).
Proof.
  have disAB_C : [disjoint A :|: B & C]
    by rewrite disjointUX disAC disBC.
  have HtraceC (f : 'F[HL]_(A :|: B :|: C)) :
      ptrace_cast3C disAC disBC f = ptrace_cast disAB_C f.
  { rewrite /ptrace_cast3C /ptrace_cast /ptrace_cast_gen.
    have Hdu : setDU3_C disAC disBC = setDU_r disAB_C
      := eq_irrelevance _ _.
    by rewrite Hdu. }
  rewrite !HtraceC.
  exact: (ptrace_cast3B_formso_commute disAB_C rho
    (P \⊗ (\1 : 'F[HL]_B))).
Qed.

End PTraceCast3BFormso.

(* ================================================================== *)
(* Partial-trace + identity-tensor projection bound (matrix level):    *)
(* ptrace2((1⊗PB)·M·(1⊗PB)) ≤ ptrace2(M)  when M psd, PB projection *)
(* ================================================================== *)

Section PTrace2IdTensProjLe.
Variables (a b : nat).

(* ptrace2_id_tens_orthogonal *)
(* infra: no tex label — fundamental & reusable (mathcomp-style) *)
(* consumer: ptrace2_id_tens_orthogonal is used downstream by the BB84 secrecy proof. *)
(* path: utils:ptrace2_id_tens_orthogonal -> utils:ptrace_cast3B_B_proj_le -> *)
(*   entropy:smoothing_support_hmax -> entropy:smooth_iso_hmax -> *)
(*   entropy:entropy_data_proc -> *)
(*   bb84:bb84_secret *)
Lemma ptrace2_id_tens_orthogonal (P Q : 'M[C]_b) (M : 'M[C]_(a * b)) :
  Q *m P = 0 ->
  ptrace2 ((1%:M *t P) *m M *m (1%:M *t Q)) = 0.
Proof.
  move=> HQP.
  (* (1*t P) *m M *m (1*t Q) = (1*t P) *m (M *m (1*t Q)).
     M *m (1*t Q) *m (1*t P) = M *m (1*t (Q*P)) = M *m (1*t 0) = M *m 0 = 0.
     So (1*t P) *m (M *m (1*t Q)) · (1*t P) = 0.
     ptrace2 of (1*t P) *m N uses the identity ptrace2_tens_id_sandwich:
     Indeed:   M *m (1*t Q) *m (1*t P) = M *m ((1*t Q) *m (1*t P))
     = M *m (1 *t (Q *m P)) = M *m (1 *t 0) = M *m 0 = 0.
     So (M *m (1*t Q)) *m (1*t P) = 0, meaning every row of M*m(1*t Q)
     is orthogonal to every column of (1*t P).

     The partial trace itself is computed entry-wise below. *)
  (* Use tensmxE_mid for the entry computation. *)
  have tensmxE_mid2 : forall (n m : nat) (A : 'M[C]_(n * m)) (B : 'M[C]_(n * m))
      (i1 : 'I_n) (k1 : 'I_m) (j1 : 'I_n) (l1 : 'I_m),
    (A *m B) (mxtens_index (i1, k1)) (mxtens_index (j1, l1)) =
    \sum_(i2 : 'I_n) \sum_(k2 : 'I_m)
      A (mxtens_index (i1, k1)) (mxtens_index (i2, k2)) *
      B (mxtens_index (i2, k2)) (mxtens_index (j1, l1)).
  { by move=> n m A0 B0 i1 k1 j1 l1; rewrite tensmxE_mid. }
  have ptrace2E' : forall s t (B' : 'M[C]_(s * t)) r1 r2,
    (ptrace2 B') r1 r2 =
    \sum_l B' (mxtens_index (r1, l)) (mxtens_index (r2, l)).
  { move=> s t B' r1 r2.
    rewrite ptrace2E1 ptrace1E.
    by apply: eq_bigr => l _; rewrite mxE !mxtens_indexK. }
  apply/matrixP => i j; rewrite mxE ptrace2E'.
  (* Goal: Σ_k entry(i,k,j,k) = 0. *)
  (* Each entry: ((1*t P) *m M *m (1*t Q))_{(i,k),(j,k)}. *)
  (* = Σ_{a1,b1} (1*t P)_{(i,k),(a1,b1)} * (M *m (1*t Q))_{(a1,b1),(j,k)}. *)
  (* = Σ_{b1} P_{k,b1} * (M *m (1*t Q))_{(i,b1),(j,k)}. *)
  (* (M *m (1*t Q))_{(i,b1),(j,k)} = Σ_{b2} M_{(i,b1),(j,b2)} * Q_{b2,k}. *)
  (* So entry = Σ_{b1,b2} P_{k,b1} * M_{(i,b1),(j,b2)} * Q_{b2,k}. *)
  (* Summing over k factors the middle term through `(Q *m P)`, which is
     zero by the orthogonality hypothesis. *)
  transitivity (\sum_(k : 'I_b) \sum_(b1 : 'I_b) \sum_(b2 : 'I_b)
      P k b1 * M (mxtens_index (i, b1)) (mxtens_index (j, b2)) * Q b2 k).
  { apply: eq_bigr => k _.
    rewrite -mulmxA
      (tensmxE_mid2 a b (1%:M *t P) (M *m (1%:M *t Q))).
    under eq_bigr => a1 _ do under eq_bigr => b1 _ do
      rewrite tensmxE mxE.
    rewrite (bigD1 i) //=.
    rewrite [X in _ + X]big1 ?addr0; last first.
    { move=> a1 /negPf Ha1; apply: big1 => b1 _.
      by rewrite eq_sym Ha1 /= ?mul0r ?mulr0. }
    rewrite eqxx /= ?mul1r ?mulr1.
    apply: eq_bigr => b1 _.
    rewrite (tensmxE_mid2 a b M (1%:M *t Q)).
    rewrite (bigD1 j) //=.
    rewrite [X in _ + X]big1 ?addr0; last first.
    { move=> a2 /negPf Ha2.
      have Hja2 : (j == a2) = false by rewrite eq_sym Ha2.
      apply: big1 => b2 _.
      by rewrite tensmxE mxE ?Ha2 ?Hja2 /= ?mul0r ?mulr0. }
    rewrite /= ?mul1r ?mulr1.
    rewrite mulr_sumr.
    by apply: eq_bigr => b2 _; rewrite tensmxE mxE eqxx /= ?mul1r ?mulr1 mulrA. }
  (* Now: Σ_k Σ_{b1,b2} P_{k,b1} * M_{(i,b1),(j,b2)} * Q_{b2,k}. *)
  (* Swap sums: Σ_{b1,b2} M_{(i,b1),(j,b2)} * Σ_k P_{k,b1} * Q_{b2,k}. *)
  (* Use Σ_k Q_{b2,k} * P_{k,b1} = (Q*P)_{b2,b1} = 0. *)
  rewrite exchange_big /=.
  apply: big1 => b1 _.
  rewrite exchange_big /=.
  transitivity (\sum_(b2 : 'I_b)
    M (mxtens_index (i, b1)) (mxtens_index (j, b2)) *
    (Q *m P) b2 b1).
  { apply: eq_bigr => b2 _.
    rewrite mxE mulr_sumr.
    apply: eq_bigr => k _.
    by rewrite -mulrA mulrCA [P k b1 * Q b2 k]mulrC. }
  by rewrite HQP; apply: big1 => b2 _; rewrite mxE mulr0.
Qed.

End PTrace2IdTensProjLe.

(* Labelled-level wrapper: ptrace_cast3B of B-projection sandwich ≤ original. *)
Section PTraceCast3BBProjection.
Variable (L : finType) (HL : L -> chsType).
Variables (A B C : {set L}).
Hypothesis disAB : [disjoint A & B].
Hypothesis disBC : [disjoint B & C].
Hypothesis disAC : [disjoint A & C].

(* path: utils:ptrace_cast3B_B_proj_le -> entropy:smoothing_support_hmax -> *)
(*   entropy:smooth_iso_hmax -> entropy:entropy_data_proc -> *)
(*   bb84:bb84_secret *)
Lemma ptrace_cast3B_B_proj_le
    (rho : 'F[HL]_(A :|: B :|: C)) (QB : 'F[HL]_B)
    (Hrho_psd : rho \is psdlf) (HQB_proj : QB \is projlf) :
  let QB_full := ((\1 : 'F[HL]_A) \⊗ QB) \⊗ (\1 : 'F[HL]_C)
                  : 'F[HL]_(A :|: B :|: C) in
  ptrace_cast3B disAB disBC (QB_full \o rho \o QB_full)
  <= ptrace_cast3B disAB disBC rho.
Proof.
  set QB_full := ((\1 : 'F[HL]_A) \⊗ QB) \⊗ (\1 : 'F[HL]_C)
                  : 'F[HL]_(A :|: B :|: C).
  have disCB : [disjoint C & B] by rewrite disjoint_sym.
  have disAB_C : [disjoint A :|: B & C] by rewrite disjointUX disAC disBC.
  (* QB_full is a projection. *)
  have HQBf_proj : QB_full \is projlf.
  { apply/projlfP; split.
    - by rewrite !tenf_adj adjf1 (hermlf_adjE (projlf_herm HQB_proj)) adjf1.
    - rewrite -tenf_comp; last exact: disAB_C.
      rewrite comp_lfun1l.
      rewrite -tenf_comp; last exact: disAB.
      rewrite comp_lfun1l.
      by move/projlfP: HQB_proj => [_ ->]. }
  have HQBf_herm : QB_full^A = QB_full
    := hermlf_adjE (projlf_herm HQBf_proj).
  have HQBf_idem : QB_full \o QB_full = QB_full
    by move/projlfP: HQBf_proj => [].
  set QBperp := (\1 : 'F[HL]_(A :|: B :|: C)) - QB_full.
  have HQBp_proj : QBperp \is projlf.
  { apply/projlfP; split.
    - by rewrite /QBperp linearB/= adjf1 HQBf_herm.
    - rewrite /QBperp comp_lfunDl !comp_lfunDr !comp_lfunNl !comp_lfunNr.
      rewrite comp_lfun1l comp_lfun1r HQBf_idem opprK.
      by rewrite comp_lfun1l addNr addr0. }
  have HQBp_herm : QBperp^A = QBperp
    := hermlf_adjE (projlf_herm HQBp_proj).
  have HQBfp_zero : QB_full \o QBperp = 0.
  { by rewrite /QBperp comp_lfunDr comp_lfunNr comp_lfun1r HQBf_idem addrN. }
  have HQBpf_zero : QBperp \o QB_full = 0.
  { by rewrite /QBperp comp_lfunDl comp_lfunNl comp_lfun1l HQBf_idem addrN. }
  (* Decompose rho = QρQ + Qρ(1-Q) + (1-Q)ρQ + (1-Q)ρ(1-Q). *)
  have Hdecomp : rho =
    (QB_full \o rho \o QB_full) +
    ((QBperp \o rho \o QB_full) +
     ((QB_full \o rho \o QBperp) + (QBperp \o rho \o QBperp))).
  { have H1eq : (\1 : 'F[HL]_(A :|: B :|: C)) = QB_full + QBperp
      by rewrite /QBperp addrC addrNK.
    transitivity ((QB_full + QBperp) \o rho \o (QB_full + QBperp)).
    { by rewrite -H1eq comp_lfun1l comp_lfun1r. }
    rewrite comp_lfunDr !comp_lfunDl.
    by rewrite -addrA. }
  have Hdiff : rho - (QB_full \o rho \o QB_full) =
    (QBperp \o rho \o QB_full) +
    ((QB_full \o rho \o QBperp) + (QBperp \o rho \o QBperp)).
  { by rewrite {1}Hdecomp [X in X - _]addrC addrK. }
  change (ptrace_cast3B disAB disBC (QB_full \o rho \o QB_full) <=
    ptrace_cast3B disAB disBC rho).
  have HptrD (x y : 'F[HL]_(A :|: B :|: C)) :
      ptrace_cast3B disAB disBC (x + y) =
      ptrace_cast3B disAB disBC x + ptrace_cast3B disAB disBC y.
  { rewrite /ptrace_cast3B /ptrace_cast_gen.
    rewrite [\Tr_(B) _]raddfD /=.
    by rewrite raddfD. }
  rewrite {2}Hdecomp HptrD HptrD HptrD.
  rewrite -subv_ge0 [X in X - _]addrC addrK.
  have Hh2mxB_B (x y : 'F[HL]_B) :
      h2mx (x - y) = h2mx x - h2mx y.
  { (* `linearB` cannot unify ?f := h2mx through the HB.lock (cf. pd.v);
       derive additivity and negation from h2mxP. *)
    have Hlin := @h2mxP R ('H[HL]_B) ('H[HL]_B).
    have Hadd (u v : 'F[HL]_B) : h2mx (u + v) = h2mx u + h2mx v.
    { rewrite -[u in h2mx (u + v)]scale1r -[h2mx u]scale1r.
      exact: (Hlin 1 u v). }
    have Hscale (c : @hermitian.C R) (z : 'F[HL]_B) :
        h2mx (c *: z) = c *: h2mx z.
    { move: (Hlin c z 0).
      by rewrite addr0 h2mx0 addr0. }
    have Hneg (z : 'F[HL]_B) : h2mx (- z) = - h2mx z.
    { have Hz : - z = (-1 : @hermitian.C R) *: z by rewrite scaleN1r.
      rewrite Hz Hscale.
      by rewrite scaleN1r. }
    change (h2mx (x + - y) = h2mx x + - h2mx y).
    by rewrite Hadd Hneg. }
  (* Show cross terms vanish and residual is psd. *)
  (* Cross term 1: ptrace_cast3B (QB_full · rho · QBperp) = 0. *)
  have Hcross1 : ptrace_cast3B disAB disBC (QB_full \o rho \o QBperp) = 0.
  { (* Use the set-regrouping to (A:|:C):|:B and matrix-level ptrace2_id_tens_orthogonal. *)
    set eqS := setUC_swap3 A B C : A :|: B :|: C = A :|: C :|: B.
    have disAC_B : [disjoint A :|: C & B] by rewrite disjointUX disAB disCB.
    rewrite /ptrace_cast3B /ptrace_cast_gen.
    (* Push the set-regrouping cast through the partial trace. *)
    set X := QB_full \o rho \o QBperp.
    have HX_recast : X = castlf (esym eqS, esym eqS) (castlf (eqS, eqS) X).
    { by rewrite castlf_comp (eq_irrelevance (etrans _ _) erefl) castlf_id. }
    rewrite {1}HX_recast.
    have eq_res : (A :|: C :|: B) :\: B = (A :|: B :|: C) :\: B by rewrite (esym eqS).
    rewrite (ptracelf_castlf_eq (esym eqS) eq_res).
    rewrite castlf_comp.
    rewrite (eq_irrelevance (etrans eq_res (setDU3_B disAB disBC))
      (setDU_r disAC_B)).
    (* Now have ptrace_cast over the regrouped (A :|: C) :|: B space. *)
    change (ptrace_cast disAC_B (castlf (eqS, eqS) X) = 0).
    apply/h2mx_inj.
    rewrite (h2mx_ptrace_cast_ptrace2 disAC_B) h2mx0.
    (* Goal: ptrace2 (U^*t *m h2mx(cast X) *m U) = 0. *)
    (* cast X = (1_{AC} ⊗ QB) · cast(rho) · (1_{AC} ⊗ (1-QB)) on (AC)⊗B. *)
    (* Under tenv_mxU conjugation, this becomes (1⊗QB') · M · (1⊗(1-QB'))
       at the matrix level, where QB' = h2mx QB. *)
    (* Need ptrace2_id_tens_orthogonal with Q*P = (1-QB)*QB = 0. *)
    set rho' := castlf (eqS, eqS) rho.
    set QB_AC := (\1 : 'F[HL]_(A :|: C)) \⊗ QB : 'F[HL]_(A :|: C :|: B).
    set QBperp_AC := (\1 : 'F[HL]_(A :|: C)) \⊗ ((\1 : 'F[HL]_B) - QB)
                     : 'F[HL]_(A :|: C :|: B).
    have Hcast_QB : castlf (eqS, eqS) QB_full = QB_AC.
    { rewrite /QB_AC /QB_full.
      to_Fnd.
      rewrite -(@tenF11 R L HL A C).
      by rewrite -!tenFA (tenFC (to_Fnd QB)
        (to_Fnd (\1 : 'F[HL]_C))) !tenFA. }
    have Hcast_QBp : castlf (eqS, eqS) QBperp = QBperp_AC.
    { rewrite /QBperp /QBperp_AC castlf_sub Hcast_QB castlf1.
      by rewrite /QB_AC tenfBr tenf11. }
    have Hcast_X : castlf (eqS, eqS) X = QB_AC \o rho' \o QBperp_AC.
    { by rewrite /X /rho' !(castlf_complf eqS eqS eqS) Hcast_QB Hcast_QBp. }
    rewrite Hcast_X.
    (* h2mx of QB_AC ∘ rho' ∘ QBperp_AC on (AC):|:B space. *)
    rewrite !h2mx_comp.
    set U := @tenv_mxU R L HL (A :|: C) B.
    have HUU : U *m U^*t = 1%:M by apply/unitarymxK; exact: tenv_mxU_unitarymx.
    have HUadjU : U^*t *m U = 1%:M.
    { have /unitarymxK : U^*t \is unitarymx := tenv_mxU_adj_unitarymx disAC_B.
      by rewrite adjmxK => ->. }
    (* h2mx QB_AC = U *m (1 *t h2mx QB) *m U^*t
       h2mx QBperp_AC = U *m (1 *t (1 - h2mx QB)) *m U^*t *)
    rewrite !h2mx_tenf h2mx1 -/U.
    rewrite !mulmxA HUadjU ?mul1mx ?mulmx1.
    rewrite -[_ *m U^*t *m U]mulmxA HUadjU ?mulmx1.
    (* Now: ptrace2 (stuff with (1*t QB) · M · (1*t (1-QB))). *)
    set Pmx := 1%:M *t h2mx QB.
    set Qmx := 1%:M *t h2mx (\1 - QB).
    rewrite -[Pmx *m U^*t *m h2mx rho']mulmxA.
    rewrite -[Pmx *m (U^*t *m h2mx rho') *m U]mulmxA.
    apply: ptrace2_id_tens_orthogonal.
    (* Goal: (1 - h2mx QB) *m h2mx QB = 0. *)
    rewrite /Qmx /Pmx Hh2mxB_B h2mx1 mulmxBl mul1mx.
    move/projlfP: HQB_proj => [_ Hidem].
    move/(congr1 h2mx): Hidem.
    rewrite h2mx_comp => ->.
    by rewrite addrN. }
  (* Cross term 2: ptrace_cast3B (QBperp · rho · QB_full) = 0. *)
  have Hcross2 : ptrace_cast3B disAB disBC (QBperp \o rho \o QB_full) = 0.
  { set eqS := setUC_swap3 A B C : A :|: B :|: C = A :|: C :|: B.
    have disAC_B : [disjoint A :|: C & B] by rewrite disjointUX disAB disCB.
    rewrite /ptrace_cast3B /ptrace_cast_gen.
    set X := QBperp \o rho \o QB_full.
    have HX_recast : X = castlf (esym eqS, esym eqS) (castlf (eqS, eqS) X).
    { by rewrite castlf_comp (eq_irrelevance (etrans _ _) erefl) castlf_id. }
    rewrite {1}HX_recast.
    have eq_res : (A :|: C :|: B) :\: B = (A :|: B :|: C) :\: B by rewrite (esym eqS).
    rewrite (ptracelf_castlf_eq (esym eqS) eq_res).
    rewrite castlf_comp.
    rewrite (eq_irrelevance (etrans eq_res (setDU3_B disAB disBC))
      (setDU_r disAC_B)).
    change (ptrace_cast disAC_B (castlf (eqS, eqS) X) = 0).
    apply/h2mx_inj.
    rewrite (h2mx_ptrace_cast_ptrace2 disAC_B) h2mx0.
    set rho' := castlf (eqS, eqS) rho.
    set QB_AC := (\1 : 'F[HL]_(A :|: C)) \⊗ QB : 'F[HL]_(A :|: C :|: B).
    set QBperp_AC := (\1 : 'F[HL]_(A :|: C)) \⊗ ((\1 : 'F[HL]_B) - QB)
                     : 'F[HL]_(A :|: C :|: B).
    have Hcast_QB : castlf (eqS, eqS) QB_full = QB_AC.
    { rewrite /QB_AC /QB_full.
      to_Fnd.
      rewrite -(@tenF11 R L HL A C).
      by rewrite -!tenFA (tenFC (to_Fnd QB)
        (to_Fnd (\1 : 'F[HL]_C))) !tenFA. }
    have Hcast_QBp : castlf (eqS, eqS) QBperp = QBperp_AC.
    { rewrite /QBperp /QBperp_AC castlf_sub Hcast_QB castlf1.
      by rewrite /QB_AC tenfBr tenf11. }
    have Hcast_X : castlf (eqS, eqS) X = QBperp_AC \o rho' \o QB_AC.
    { by rewrite /X /rho' !(castlf_complf eqS eqS eqS) Hcast_QB Hcast_QBp. }
    rewrite Hcast_X !h2mx_comp.
    set U := @tenv_mxU R L HL (A :|: C) B.
    have HUadjU : U^*t *m U = 1%:M.
    { have /unitarymxK : U^*t \is unitarymx := tenv_mxU_adj_unitarymx disAC_B.
      by rewrite adjmxK => ->. }
    rewrite !h2mx_tenf h2mx1 -/U.
    rewrite !mulmxA HUadjU ?mul1mx ?mulmx1.
    rewrite -[_ *m U^*t *m U]mulmxA HUadjU ?mulmx1.
    set Pmx := 1%:M *t h2mx (\1 - QB).
    set Qmx := 1%:M *t h2mx QB.
    rewrite -[Pmx *m U^*t *m h2mx rho']mulmxA.
    rewrite -[Pmx *m (U^*t *m h2mx rho') *m U]mulmxA.
    apply: ptrace2_id_tens_orthogonal.
    rewrite /Qmx /Pmx Hh2mxB_B h2mx1 mulmxBr mulmx1.
    move/projlfP: HQB_proj => [_ Hidem].
    move/(congr1 h2mx): Hidem.
    rewrite h2mx_comp => ->.
    by rewrite subrr. }
  move: Hcross1 Hcross2; rewrite /ptrace_cast3B /ptrace_cast_gen
    => Hcross1' Hcross2'.
  rewrite Hcross2' Hcross1' add0r add0r.
  (* Remaining: ptrace_cast3B (QBperp · rho · QBperp) \is psdlf. *)
  rewrite -psdlfE.
  apply: ptrace_cast_gen_psdlf.
  rewrite qualifE !h2mx_comp.
  have HQBp_mx_herm : (h2mx QBperp)^*t = h2mx QBperp
    by rewrite -h2mx_adj HQBp_herm.
  rewrite -{1}HQBp_mx_herm.
  apply: formV_psdmx.
  by move: Hrho_psd; rewrite qualifE.
Qed.

End PTraceCast3BBProjection.

(* ================================================================== *)
(* Stinespring-style identity-tensor matrix bridge.                    *)
(* For a CP map E with matrix Stinespring data (W, HE_act), and any    *)
(* labelled bipartite operator rhoAB, the labelled (id_A :⊗ E) action *)
(* in matrix form (cast through tenv_dim) equals the matrix-level      *)
(* (1_A *t W) sandwich followed by ptrace2 over the Stinespring        *)
(* environment, with the natural mulnA cast on the env factor.         *)
(* This is the labelled/matrix bridge consumed by smooth-entropy         *)
(* data-processing proofs.                                               *)
(* Tomamichel, 'A Framework for Non-Asymptotic Quantum     *)
(*   Information Theory' (PhD thesis, arXiv:1203.2142) — Stinespring     *)
(*   (lm:stinespring, Lemma 2.4) + th:data-proc (Theorem 5.7,           *)
(*   Generalized Data Processing).                                       *)
(* ================================================================== *)

Section IdTensStinespringBridge.
Variable (L : finType) (HL : L -> chsType).
Variables (A B : L).
Hypothesis disAB : [disjoint [set A] & [set B]].

(* h2mx_id_tens_E_via_W *)
(* infra: no tex label — fundamental & reusable (Stinespring bridge) *)
(* consumer: full dependency route is shown in assets/dep.svg. *)
(* path: utils:h2mx_id_tens_E_via_W -> entropy:smooth_hmax_labelled_mx -> *)
(*   bb84:stat -> bb84:bb84_secret *)
Lemma h2mx_id_tens_E_via_W
    {z : nat}
    (E : 'SO[HL]_[set B])
    (W : 'M[C]_(dim 'H[HL]_[set B] * z, dim 'H[HL]_[set B]))
    (HE_act : forall rho : 'M[C]_(dim 'H[HL]_[set B]),
                h2mx (E (mx2h rho)) = ptrace2 (W *m rho *m W^*t))
    (rhoAB : 'F[HL]_([set A] :|: [set B])) :
  let nA := dim 'H[HL]_[set A] in
  let nB := dim 'H[HL]_[set B] in
  let Q : 'M[C]_(nA * nB) :=
    castmx (tenv_dim disAB, erefl) (@tenv_mxU R L HL [set A] [set B]) in
  let rho_mx : 'M[C]_(nA * nB) :=
    castmx (tenv_dim disAB, tenv_dim disAB) (h2mx rhoAB) in
  castmx (tenv_dim disAB, tenv_dim disAB)
    (h2mx (((\:1 : 'SO[HL]_[set A]) :⊗ E) rhoAB))
  = Q *m
      ptrace2
        (castmx (mulnA nA nB z, mulnA nA nB z)
          (((1%:M : 'M[C]_nA) *t W) *m
           (Q^*t *m rho_mx *m Q) *m
           (((1%:M : 'M[C]_nA) *t W)^*t)))
      *m Q^*t.
Proof.
  (* Matrix/labelled Stinespring alignment route.                            *)
  (* Strategy: factor the goal through the cast-consolidation step            *)
  (* `HCast_consol` and the Stinespring marginal identity `HInner_marg`.      *)
  (* Structural `have`s keep the surrounding plumbing local.                  *)
  (* ----------------------------------------------------------------------- *)
  move=> nA nB.
  (* Abbreviation for the env-side dilation isometry on `(nA*(nB*z), nA*nB)`. *)
  pose V : 'M[C]_(nA * (nB * z), nA * nB) := (1%:M : 'M[C]_nA) *t W.
  pose rho_mx : 'M[C]_(nA * nB) :=
    castmx (tenv_dim disAB, tenv_dim disAB) (h2mx rhoAB).
  pose Q : 'M[C]_(nA * nB) :=
    castmx (tenv_dim disAB, erefl) (@tenv_mxU R L HL [set A] [set B]).
  (* ----------------------------------------------------------------------- *)
  (* HInner_marg: the labelled/matrix Stinespring                   *)
  (* identity in the consolidated form. After the cast push, both sides are   *)
  (* equal entry-wise: the LHS unfolds via `onb_lfun2id deltav rhoAB`         *)
  (* + `tenso_correct disAB` + `tensodf` + `h2mx_tenf`; each per-block        *)
  (* `h2mx (E _)` is converted to `ptrace2 (W *m _ *m W^*t)` by `HE_act`;     *)
  (* the matrix-tensor decomposition of `rho_mx` realigns via `tenv_mxU`     *)
  (* conjugation; and the resulting `ptrace2` over `z` matches the RHS       *)
  (* through `mxtens_index/unindex` bookkeeping under the `mulnA` cast.       *)
  (* ----------------------------------------------------------------------- *)
  have HInner_marg :
      castmx (tenv_dim disAB, tenv_dim disAB)
        (h2mx (((\:1 : 'SO[HL]_[set A]) :⊗ E) rhoAB))
      = Q *m
          ptrace2
            (castmx (mulnA nA nB z, mulnA nA nB z)
              (V *m (Q^*t *m rho_mx *m Q) *m V^*t))
          *m Q^*t.
  { (* Strategy: decompose `rhoAB` via `onb_lfun2id deltav` and push          *)
    (* linearity of `\:1 :⊗ E`, `h2mx`, and `castmx` through the sum.        *)
    (* For each summand `[> dv i; dv j <]`, use `dv_split`+`tenf_outp` to    *)
    (* split into `\⊗`, then `tenso_correct disAB`+`id_soE` to apply the     *)
    (* identity on the A-factor and `E` on the B-factor. Convert the          *)
    (* remaining `h2mx (E _)` terms to `ptrace2 (W *m _ *m W^*t)` via         *)
    (* `HE_act`. The RHS is reduced by linearity of `*m` and `*t` and the     *)
    (* trace-cast bridge `ptrace2_castmx_tensmx_assoc` from comp.v:490.       *)
    (* ----------------------------------------------------------------------- *)
    (* Step Inner.1: decompose rhoAB through onb_lfun2id deltav.              *)
    have H_rho_dec :
        rhoAB =
        \sum_(i : 'Idx[HL]_([set A] :|: [set B]))
          \sum_(j : 'Idx[HL]_([set A] :|: [set B]))
            [< deltav j ; rhoAB (deltav i) >] *: [> deltav j ; deltav i <].
    { exact: (onb_lfun2id deltav rhoAB). }
    (* Step Inner.2: per-summand labelled identity                            *)
    (*   ((\:1 :⊗ E) [> dv j; dv i <])                                       *)
    (*    = [> dv (idxSl j); dv (idxSl i) <] \⊗ E [> dv (idxSr j); dv (idxSr i) <]. *)
    (* Uses dv_split + tenf_outp (reverse) + tenso_correct disAB + id_soE.    *)
    have H_per_summand :
      forall (i j : 'Idx[HL]_([set A] :|: [set B])),
        ((\:1 : 'SO[HL]_[set A]) :⊗ E) [> deltav j ; deltav i <] =
        [> deltav (idxSl j) ; deltav (idxSl i) <] \⊗
          E [> deltav (idxSr j) ; deltav (idxSr i) <].
    { move=> i j.
      rewrite [in LHS](dv_split j) [in LHS](dv_split i) -tenf_outp.
      by rewrite -tenso_correct // id_soE. }
    have HSOZ (c : C) (x : 'F[HL]_([set A] :|: [set B])) :
        ((\:1 : 'SO[HL]_[set A]) :⊗ E) (c *: x) =
        c *: (((\:1 : 'SO[HL]_[set A]) :⊗ E) x).
    { have Hlin := superop_is_linear (((\:1 : 'SO[HL]_[set A]) :⊗ E)).
      have HSO0 :
          (((\:1 : 'SO[HL]_[set A]) :⊗ E)
            (0 : 'F[HL]_([set A] :|: [set B]))) = 0.
      { exact: linear0. }
      move: (Hlin c x 0).
      rewrite addr0 HSO0 addr0.
      by move=> ->. }
    have Hh2mxZ_AB (c : C) (x : 'F[HL]_([set A] :|: [set B])) :
        h2mx (c *: x) = c *: h2mx x.
    { have Hlin :=
        @h2mxP R ('H[HL]_([set A] :|: [set B]))
          ('H[HL]_([set A] :|: [set B])).
      move: (Hlin c x 0).
      rewrite addr0 h2mx0 addr0.
      by move=> ->. }
    have HcastmxZ_AB (c : C)
        (M : 'M[C]_(dim 'H[HL]_([set A] :|: [set B]))) :
        castmx (tenv_dim disAB, tenv_dim disAB) (c *: M) =
        c *: castmx (tenv_dim disAB, tenv_dim disAB) M.
    { by rewrite linearZ. }
    have HcastmxZ_assoc (c : C) (M : 'M[C]_(nA * (nB * z))) :
        castmx (mulnA nA nB z, mulnA nA nB z) (c *: M) =
        c *: castmx (mulnA nA nB z, mulnA nA nB z) M.
    { by rewrite linearZ. }
    have Hptrace2Z_assoc (c : C) (M : 'M[C]_((nA * nB) * z)) :
        ptrace2 (c *: M) = c *: ptrace2 M.
    { by rewrite linearZ. }
    (* Step Inner.3 (per-entry decomposition).                                *)
    (* Split the inner alignment into labelled, matrix, and cast blocks.      *)
    (* Each block isolates a math step; the deepest (Block.PerSummand) is    *)
    (* the main SVD-Stinespring identity per labelled-tensor summand.         *)
    (* ---------------------------------------------------------------------- *)
    (* Block.LHSLin: push H_rho_dec linearity through (\:1 :⊗ E),             *)
    (* h2mx, castmx; apply H_per_summand to each summand.                     *)
    have HLHSLin :
      castmx (tenv_dim disAB, tenv_dim disAB)
        (h2mx (((\:1 : 'SO[HL]_[set A]) :⊗ E) rhoAB)) =
      \sum_(i : 'Idx[HL]_([set A] :|: [set B]))
        \sum_(j : 'Idx[HL]_([set A] :|: [set B]))
          [< deltav j ; rhoAB (deltav i) >] *:
            castmx (tenv_dim disAB, tenv_dim disAB)
              (h2mx
                ([> deltav (idxSl j) ; deltav (idxSl i) <] \⊗
                 E [> deltav (idxSr j) ; deltav (idxSr i) <])).
    { rewrite {1}H_rho_dec.
      rewrite raddf_sum /=.
      rewrite raddf_sum /=.
      rewrite raddf_sum /=.
      apply: eq_bigr => i _.
      rewrite raddf_sum /=.
      rewrite raddf_sum /=.
      rewrite raddf_sum /=.
      apply: eq_bigr => j _.
      set cji := [< deltav j ; rhoAB (deltav i) >].
      set xji := [> deltav j ; deltav i <].
      rewrite HSOZ Hh2mxZ_AB HcastmxZ_AB.
      congr (_ *: _).
      by rewrite /xji (H_per_summand i j). }
    (* Block.RHSLin: expand rho_mx via H_rho_dec into an inner sum            *)
    (* of c_ji-scaled castmx h2mx summands.                                   *)
    have HRHSLin_inner :
      rho_mx =
      \sum_(i : 'Idx[HL]_([set A] :|: [set B]))
        \sum_(j : 'Idx[HL]_([set A] :|: [set B]))
          [< deltav j ; rhoAB (deltav i) >] *:
            castmx (tenv_dim disAB, tenv_dim disAB)
              (h2mx [> deltav j ; deltav i <]).
    { rewrite /rho_mx {1}H_rho_dec.
      rewrite raddf_sum /=.
      rewrite raddf_sum /=.
      apply: eq_bigr => i _.
      rewrite raddf_sum /=.
      rewrite raddf_sum /=.
      apply: eq_bigr => j _.
      set cji := [< deltav j ; rhoAB (deltav i) >].
      set xji := [> deltav j ; deltav i <].
      by rewrite Hh2mxZ_AB HcastmxZ_AB /xji. }
    (* Block.PerSummand: per-summand SVD-Stinespring matrix                  *)
    (* identity. For each (i,j), the labelled-tensor matrix on LHS equals     *)
    (* the (1*tW)-conjugated matrix with ptrace2 on RHS. This is the          *)
    (* per-entry tenv_mxU/mxtens_index alignment under the mulnA cast.        *)
    have HPerSummand :
      forall (i j : 'Idx[HL]_([set A] :|: [set B])),
        castmx (tenv_dim disAB, tenv_dim disAB)
          (h2mx
            ([> deltav (idxSl j) ; deltav (idxSl i) <] \⊗
             E [> deltav (idxSr j) ; deltav (idxSr i) <])) =
        Q *m
          ptrace2
            (castmx (mulnA nA nB z, mulnA nA nB z)
              (V *m
               (Q^*t *m
                castmx (tenv_dim disAB, tenv_dim disAB)
                  (h2mx [> deltav j ; deltav i <]) *m Q)
               *m V^*t))
          *m Q^*t.
    { (* === Per-summand split ============================================ *)
      (* Per-entry Stinespring matrix identity, refined into 3 tagged       *)
      (* sub-blocks (PerSummand.A, .B, .C).                                  *)
      (* PerSummand.A: rewrite LHS via h2mx_tenf (tensor-unfolding under      *)
      (*               h2mx) and HE_act (Stinespring on the B-factor).       *)
      (* PerSummand.B: rewrite the inner [> dv j; dv i <] on RHS via         *)
      (*               dv_split + tenf_outp (reverse) + h2mx_tenf, so both   *)
      (*               sides expose their tenv_mxU change-of-basis.          *)
      (* PerSummand.C: deep matrix-level identity bridging the two           *)
      (*               tenv_mxU-conjugated tensor forms under mulnA cast +   *)
      (*               ptrace2, isolating the SVD-Stinespring alignment.      *)
      (* ----------------------------------------------------------------- *)
      move=> i j.
      (* Step PerSummand.A: use the H_per_summand identity                    *)
      (* to convert E [>dv;dv<]_B via                                        *)
      (* HE_act through the mx2hK trick.                                       *)
      have HE_per :
        h2mx (E [> deltav (idxSr j) ; deltav (idxSr i) <]) =
        ptrace2 (W *m h2mx [> deltav (idxSr j) ; deltav (idxSr i) <] *m W^*t).
      { rewrite -[X in E X]h2mxK. exact: HE_act. }
      (* Step PerSummand.B: split [> dv j; dv i <] on the RHS via            *)
      (* dv_split + tenf_outp, so that h2mx [>dv j; dv i<] decomposes into    *)
      (* tenv_mxU-conjugated tensor product of the left and right blocks.     *)
      have HRHS_split :
        h2mx [> deltav j ; deltav i <] =
        @tenv_mxU R L HL [set A] [set B] *m
          (h2mx [> deltav (idxSl j) ; deltav (idxSl i) <] *t
           h2mx [> deltav (idxSr j) ; deltav (idxSr i) <]) *m
        (@tenv_mxU R L HL [set A] [set B])^*t.
      { rewrite [in LHS](dv_split j) [in LHS](dv_split i) -tenf_outp.
        exact: h2mx_tenf. }
      (* === PerSummand.C: split into C.1 / C.2 / C.3 ==================== *)
      (* C.1 (V_tens_collapse): for any M : 'M_nA, N : 'M_(nB*z),              *)
      (*     V *m (M *t N) *m V^*t = M *t (W *m N *m W^*t).                     *)
      (*     Pure tensor-product algebra: tensmx_adj+adjmx1, tensmx_mul,         *)
      (*     mul1mx, mulmx1. No casts, no tenv_mxU.                              *)
      (* C.2 (PT2_via_assoc): direct application of                         *)
      (*     ptrace2_castmx_tensmx_assoc (comp.v:490) to extract the M-factor   *)
      (*     out of ptrace2 (castmx (mulnA, mulnA) (M *t Y)).                   *)
      (* C.3 (cast/conjugation bridge): the remaining identity bridges           *)
      (*     `castmx (te,te) (tenv_mxU *m (M_l *t Y) *m tenv_mxU^*t)` with the   *)
      (*     V-conjugated castmx form on RHS, where Y is either the bare         *)
      (*     ptrace2 (LHS) or the M_r factor pre-trace (RHS). This is the        *)
      (*     SVD-Stinespring permutation/cast bridge: tenv_mxU realizes          *)
      (*     the basis change between labeled (te,te) and mxtens-product order;  *)
      (*     V = (1 *t W) does not commute with this permutation under (mulnA,   *)
      (*     mulnA) cast + ptrace2. C.1 and C.2 isolate the purely algebraic     *)
      (*     content; C.3 isolates the permutation/cast bridge.                  *)
      (* ----------------------------------------------------------------- *)
      rewrite (h2mx_tenf [> deltav (idxSl j) ; deltav (idxSl i) <]
                          (E [> deltav (idxSr j) ; deltav (idxSr i) <])).
      rewrite HE_per HRHS_split.
      (* Step C.1 (V_tens_collapse).                                           *)
      have HC1 : forall (M : 'M[C]_nA) (N : 'M[C]_nB),
        V *m (M *t N) *m V^*t = M *t (W *m N *m W^*t).
      { move=> M N.
        rewrite /V tensmx_adj adjmx1.
        rewrite mxtens.tensmx_mul mul1mx.
        by rewrite mxtens.tensmx_mul mulmx1. }
      (* Step C.2 (PT2_via_assoc).                                             *)
      have HC2 : forall (M : 'M[C]_nA) (Y : 'M[C]_(nB * z)),
        ptrace2 (castmx (mulnA nA nB z, mulnA nA nB z) (M *t Y))
        = M *t ptrace2 Y.
      { move=> M Y. exact: ptrace2_castmx_tensmx_assoc. }
      (* === Step C.3 split ================================================ *)
      (* Split into 5 named sub-blocks.                                       *)
      (*  C.3.a: define Q := castmx (te,erefl) tenv_mxU.                    *)
      (*  C.3.b: castmx (te,te) (tenv_mxU *m M *m tenv_mxU^*t)              *)
      (*    = Q *m M *m Q^*t. Pure castmx_mul algebra.                       *)
      (*  C.3.c: apply C.3.b on LHS to expose Q-conjugation.                *)
      (*  C.3.d: apply C.3.b on RHS inner to expose Q-conjugation.          *)
      (*  C.3.e: commute Q through V *m _ *m V^*t under the associativity    *)
      (*    under (mulnA, mulnA) cast + ptrace2. Residual:                   *)
      (*    ptrace2 (castmx (mulnA,mulnA) (V *m Q*K*Q^*t *m V^*t)) =          *)
      (*    Q *m ptrace2 (castmx (mulnA,mulnA) (V *m K *m V^*t)) *m Q^*t.    *)
      (*  C.3.f: ptrace2-collapse using HC1 + HC2 on the inner.             *)
      (* -------------------------------------------------------------------- *)
      (* Step C.3.a: use the outer Q (castmx-ed tenv_mxU square form).       *)
      (* Step C.3.b: castmx (te,te) (tenv_mxU *m M *m tenv_mxU^*t)            *)
      (*           = Q *m M *m Q^*t.                                          *)
      have HC3b : forall (M : 'M[C]_(nA * nB)),
        castmx (tenv_dim disAB, tenv_dim disAB)
          ((@tenv_mxU R L HL [set A] [set B]) *m M *m
           (@tenv_mxU R L HL [set A] [set B])^*t)
        = Q *m M *m Q^*t.
      { move=> M.
        rewrite /Q.
        have HQt : (castmx (tenv_dim disAB, erefl)
                    (@tenv_mxU R L HL [set A] [set B]))^*t
                 = castmx (erefl, tenv_dim disAB)
                    (@tenv_mxU R L HL [set A] [set B])^*t.
        { exact: (@castmx_mx_mxT _ _ (@adjmx _) _ _ _ _
            (tenv_dim disAB, erefl)
            (@tenv_mxU R L HL [set A] [set B])). }
        rewrite HQt.
        rewrite mcextra.castmx_mull.
        by rewrite mcextra.castmx_mul. }
      (* Product-coordinate route: first move the labelled block into the     *)
      (* product basis with Q^* _ Q, apply the Stinespring tensor identity,   *)
      (* then conjugate the marginal back by Q. No Q-V commutation is used.   *)
      rewrite [X in X = _]HC3b.
      have HS4_M1 :
          Q *m (h2mx [> deltav (idxSl j) ; deltav (idxSl i) <] *t
                h2mx [> deltav (idxSr j) ; deltav (idxSr i) <]) *m Q^*t
        = castmx (tenv_dim disAB, tenv_dim disAB)
            (h2mx [> deltav j ; deltav i <]).
      { rewrite -HC3b.
        by rewrite -HRHS_split. }
      have HQt : Q^*t = castmx (erefl, tenv_dim disAB)
                    (@tenv_mxU R L HL [set A] [set B])^*t.
      { rewrite /Q.
        exact: (@castmx_mx_mxT _ _ (@adjmx _) _ _ _ _
          (tenv_dim disAB, erefl)
          (@tenv_mxU R L HL [set A] [set B])). }
      have HQtQ : Q^*t *m Q = 1%:M.
      { rewrite /Q HQt mcextra.castmx_mul.
        have HU : (@tenv_mxU R L HL [set A] [set B])^*t
                    *m (@tenv_mxU R L HL [set A] [set B]) = 1%:M.
        { have := unitarymxK (@tenv_mxU_adj_unitarymx R L HL [set A] [set B] disAB).
          by rewrite adjmxK. }
        rewrite HU.
        by case: _ / (tenv_dim disAB); rewrite castmx_id. }
      have HQ_unit : Q \is unitarymx by apply/unitarymxPV.
      have HQQt : Q *m Q^*t = 1%:M := unitarymxK HQ_unit.
      have Hprod_block :
          Q^*t *m
            castmx (tenv_dim disAB, tenv_dim disAB)
              ((@tenv_mxU R L HL [set A] [set B]) *m
                (h2mx [> deltav (idxSl j) ; deltav (idxSl i) <] *t
                 h2mx [> deltav (idxSr j) ; deltav (idxSr i) <]) *m
               (@tenv_mxU R L HL [set A] [set B])^*t) *m Q
        = h2mx [> deltav (idxSl j) ; deltav (idxSl i) <] *t
          h2mx [> deltav (idxSr j) ; deltav (idxSr i) <].
      { rewrite HC3b.
        by rewrite !mulmxA ?HQtQ ?mulmx1 ?mul1mx
          -?mulmxA ?HQtQ ?mulmx1 ?mul1mx. }
      rewrite Hprod_block.
      rewrite HC1.
      rewrite HC2.
      reflexivity. }
    (* Block.RHSReassemble: rebuild the RHS sum via linearity of             *)
    (* *m, ptrace2, castmx through HRHSLin_inner.                             *)
    have HRHS_expand :
      Q *m
        ptrace2
          (castmx (mulnA nA nB z, mulnA nA nB z)
            (V *m (Q^*t *m rho_mx *m Q) *m V^*t))
        *m Q^*t =
      \sum_(i : 'Idx[HL]_([set A] :|: [set B]))
        \sum_(j : 'Idx[HL]_([set A] :|: [set B]))
          [< deltav j ; rhoAB (deltav i) >] *:
            (Q *m
              ptrace2
                (castmx (mulnA nA nB z, mulnA nA nB z)
                  (V *m
                   (Q^*t *m
                    castmx (tenv_dim disAB, tenv_dim disAB)
                      (h2mx [> deltav j ; deltav i <]) *m Q)
                   *m V^*t))
              *m Q^*t).
    { rewrite HRHSLin_inner.
      (* Outer-i sum: peel through Q^* _ Q, V _ V^*, ptrace2, and outer Qs. *)
      rewrite mulmx_sumr mulmx_suml.
      rewrite mulmx_sumr mulmx_suml linear_sum /= linear_sum /=.
      rewrite mulmx_sumr mulmx_suml.
      apply: eq_bigr => i _.
      (* Inner-j sum: same peel pattern. *)
      rewrite mulmx_sumr mulmx_suml.
      rewrite mulmx_sumr mulmx_suml linear_sum /= linear_sum /=.
      rewrite mulmx_sumr mulmx_suml.
      apply: eq_bigr => j _.
      rewrite -scalemxAr -scalemxAl -scalemxAr -scalemxAl.
      rewrite HcastmxZ_assoc Hptrace2Z_assoc.
      by rewrite -scalemxAr -scalemxAl. }
    (* Block.Combine: chain HLHSLin = sum-of-summands; HRHS_expand           *)
    (* = sum-of-summands; per-summand identity HPerSummand bridges them.    *)
    rewrite HLHSLin HRHS_expand.
    apply: eq_bigr => i _.
    apply: eq_bigr => j _.
    by rewrite (HPerSummand i j). }
  exact: HInner_marg.
Qed.

End IdTensStinespringBridge.

(* ================================================================== *)
(* Generic ptrace_cast3C / sdot / den1lf interaction lemmas            *)
(* ================================================================== *)
(* These are labelled-operator facts about ptrace_cast3C, sdot (\O),   *)
(* den1lf, and finset.set0.  They are protocol-independent and are     *)
(* consumed by the BB84 modules in src/qkd.                            *)
(* ================================================================== *)

Section PTraceCast3CDen1.
Variable (L : finType) (HL : L -> chsType).

(* Local helpers — these are also proved in lift.v; we re-derive them  *)
(* here to avoid a circular dependency (lift imports sys).             *)
Let sdotF_to_tenF_loc (A B : {set L}) (disAB : [disjoint A & B])
    (f : 'F[HL]_A) (g : 'F[HL]_B) :
  (f \O g : 'F[HL]_(A :|: B)) = f \⊗ g.
Proof.
  by apply: to_Fnd_inj; rewrite (sdotFT _ _ disAB) to_Fnd_tenE.
Qed.

Let h2mxZ_lf_loc (A : {set L}) (c : @hermitian.C R) (x : 'F[HL]_A) :
  h2mx (c *: x) = c *: h2mx x.
Proof.
  have Hlin := @h2mxP R ('H[HL]_A) ('H[HL]_A).
  move: (Hlin c x 0).
  rewrite addr0 h2mx0 addr0.
  by move=> ->.
Qed.

Let ptrace_cast_sdot_trace_r_loc (A B : {set L}) (disAB : [disjoint A & B])
    (x : 'F[HL]_A) (y : 'F[HL]_B) :
  ptrace_cast disAB (x \O y) = \Tr y *: x.
Proof.
  apply/h2mx_inj.
  rewrite h2mxZ_lf_loc /= /lftrace.
  rewrite (sdotF_to_tenF_loc disAB x y).
  rewrite (h2mx_ptrace_cast_ptrace2 disAB).
  rewrite h2mx_tenf.
  pose U := @tenv_mxU R L HL A B.
  have HUadj : U^*t \is unitarymx := tenv_mxU_adj_unitarymx disAB.
  have HUadjU : U^*t *m U = 1%:M.
  { by have := unitarymxK HUadj; rewrite adjmxK. }
  rewrite -/U !mulmxA HUadjU mul1mx -mulmxA HUadjU mulmx1.
  by rewrite ptrace_tensmx.
Qed.

(* path: utils:ptrace_cast3C_sdot_unit0 -> *)
(*   bb84:bb84_secure *)
Lemma ptrace_cast3C_sdot_unit0 (A B0 : {set L})
    (rhoAB : 'F[HL]_(A :|: B0)) :
  @ptrace_cast3C R L HL A B0 finset.set0
    (disjointX0 A) (disjointX0 B0)
    (rhoAB \O (\1 : 'F[HL]_finset.set0)) = rhoAB.
Proof.
  have disAB0 : [disjoint A :|: B0 & finset.set0]
    by rewrite disjointX0.
  have HtraceC (f : 'F[HL]_(A :|: B0 :|: finset.set0)) :
      ptrace_cast3C (disjointX0 A) (disjointX0 B0) f =
      ptrace_cast disAB0 f.
  { rewrite /ptrace_cast3C /ptrace_cast /ptrace_cast_gen.
    have Hdu : setDU3_C (disjointX0 A) (disjointX0 B0) =
        setDU_r disAB0 := eq_irrelevance _ _.
    by rewrite Hdu. }
  rewrite HtraceC ptrace_cast_sdot_trace_r_loc.
  by rewrite /lftrace h2mx1 mxtrace1 dim_set0 scale1r.
Qed.

(* path: utils:sdot_unit0_den1lf -> *)
(*   bb84:bb84_secure *)
Lemma sdot_unit0_den1lf (A : {set L}) (rhoA : 'F[HL]_A) :
  rhoA \is den1lf ->
  rhoA \O (\1 : 'F[HL]_finset.set0) \is den1lf.
Proof.
  move=> HrhoA.
  apply/den1lfP; split.
  - rewrite (sdotF_to_tenF_loc (disjointX0 A)).
    rewrite psdlfE.
    apply: tenf_ge0; first exact: disjointX0.
    + exact: psdlf_ge0 (den1lf_psd HrhoA).
    + by rewrite -psdlfE is_psdlf.
  - rewrite lftrace_sdot_disj ?disjointX0 //.
    by rewrite (den1lf_trlf HrhoA) /lftrace h2mx1 mxtrace1 dim_set0 mulr1.
Qed.

(* path: utils:ptrace_cast3C_den1lf -> bb84:bb84_dmc_source_den1 -> *)
(*   bb84:bb84_secure *)
Lemma ptrace_cast3C_den1lf (A B C0 : {set L})
    (disAC : [disjoint A & C0]) (disBC : [disjoint B & C0])
    (rho : 'F[HL]_(A :|: B :|: C0)) :
  rho \is den1lf ->
  @ptrace_cast3C R L HL A B C0 disAC disBC rho \is den1lf.
Proof.
  move=> Hrho.
  apply/den1lfP; split.
  - rewrite /ptrace_cast3C.
    exact: ptrace_cast_gen_psdlf (den1lf_psd Hrho).
  - rewrite /ptrace_cast3C /ptrace_cast_gen castlf_trlfE.
    have /cptpP [_ /tpmapP Htp] :=
      @ptraceso_qc R L HL C0 (A :|: B :|: C0).
    by rewrite Htp (den1lf_trlf Hrho).
Qed.

End PTraceCast3CDen1.

Local Close Scope lfun_scope.

End FvqkdReal.
