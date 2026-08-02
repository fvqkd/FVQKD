(* semantics.v -- Denotational semantics of the generic QKD language    *)
(* Module: qkd.protocol.semantics                                       *)
(* Paper: Tomamichel-Lim-Gisin-Renner, Nat. Commun. 3:634 (2012),       *)
(*   Tight finite-key analysis for quantum cryptography (Box 1, Table 1). *)
(* Classical-quantum state space and denotational semantics for the     *)
(* syntax.v command language.                                           *)

From HB Require Import structures.
From mathcomp Require Import all_boot.
From mathcomp Require Import all_order.
From mathcomp Require Import all_algebra.
From mathcomp Require Import finmap fingroup.
From mathcomp.reals Require Import reals.
From quantum.external Require Import spectral complex.
From quantum Require Import mcextra mcaextra notation hermitian quantum.
From quantum Require Import cpo mxpred extnum ctopology.
From quantum Require Import svd mxnorm hspace.
From quantum.dirac Require Import hstensor.

Import Order.TTheory GRing.Theory Num.Theory Num.Def MxLownerOrder.
Import VectorInternalTheory.

From utils Require Import exports.
From qkd.protocol Require Import syntax.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Open Scope ring_scope.
Local Open Scope lfun_scope.

Section StandardDenotation.
Variable R : realType.
Notation chsType := (@chsType R).
Variables (L : finType) (HL : L -> chsType).
Variables Cv V : finType.
Variables (qA : {set L}) (Pvar : Cv).

Notation store := (@store Cv V).
Notation expr := (@expr Cv V).
Notation bexpr := (@bexpr Cv V).
Notation dexpr := (@dexpr R Cv V).
Notation qexpr := (@qexpr R L HL Cv V).
Notation mexpr := (@mexpr R L HL Cv V).
Notation cmd := (@qkd_cmd R L HL Cv V).

Definition cq_state := {ffun store -> 'F[HL]_setT}.

Definition cq_single (s : store) (rho : 'F[HL]_setT) : cq_state := [ffun t => if t == s then rho else 0].

Definition cq_mass (xi : cq_state) : R := \sum_s @complex.Re R (\Tr (xi s)).

Definition cq_wf (xi : cq_state) : Prop := (forall s, xi s \is psdlf) /\ cq_mass xi = 1.

Definition adversary := forall Q : {set L}, V -> 'QC('H[HL]_(Q :|: qA)).

Definition appendso_fun (Q : {set L}) (rho : 'F[HL]_Q) (x : 'F[HL]_(setT :\: Q)) : 'F[HL]_setT :=
  castlf (setUD_sub (subsetT Q), setUD_sub (subsetT Q)) (rho \⊗ x).

Fact appendso_fun_is_linear (Q : {set L}) (rho : 'F[HL]_Q) : linear (appendso_fun rho).
Proof. move=> a x y; by rewrite /appendso_fun linearP/= linearP/=. Qed.

HB.instance Definition _ (Q : {set L}) (rho : 'F[HL]_Q) :=
  GRing.isLinear.Build C 'F[HL]_(setT :\: Q) 'F[HL]_setT *:%R (appendso_fun rho) (appendso_fun_is_linear rho).

Definition appendso (Q : {set L}) (rho : 'F[HL]_Q) : 'SO[HL]_(setT :\: Q, setT) := Superop (linfun (appendso_fun rho)).

Definition replaceso (Q : {set L}) (rho : 'F[HL]_Q) : 'SO[HL]_setT := appendso rho :o ptraceso Q.

Definition replacement_fun (Q : {set L}) (rho : 'F[HL]_Q) (x : 'F[HL]_Q) : 'F[HL]_Q := \Tr x *: rho.

Fact replacement_fun_is_linear (Q : {set L}) (rho : 'F[HL]_Q) : linear (replacement_fun rho).
Proof. move=> a x y; by rewrite /replacement_fun linearD linearZ scalerDl scalerA. Qed.

HB.instance Definition _ (Q : {set L}) (rho : 'F[HL]_Q) :=
  GRing.isLinear.Build C 'F[HL]_Q 'F[HL]_Q *:%R (replacement_fun rho) (replacement_fun_is_linear rho).

Definition replacementso (Q : {set L}) (rho : 'F[HL]_Q) : 'SO[HL]_Q := Superop (linfun (replacement_fun rho)).

Fact replacementsoE (Q : {set L}) (rho : 'F[HL]_Q) (x : 'F[HL]_Q) : replacementso rho x = \Tr x *: rho.
Proof. by rewrite /replacementso /fun_of_superof/= lfunE. Qed.

Lemma appendsoE (Q : {set L}) (rho : 'F[HL]_Q) (x : 'F[HL]_(setT :\: Q)) :
  appendso rho x = castlf (setUD_sub (subsetT Q), setUD_sub (subsetT Q)) (rho \⊗ x).
Proof. by rewrite /appendso /fun_of_superof/= lfunE. Qed.

Lemma replacesoE (Q : {set L}) (rho : 'F[HL]_Q) (x : 'F[HL]_setT) : replaceso rho x = appendso rho (ptraceso Q x).
Proof. by rewrite /replaceso comp_soE. Qed.

Lemma ptraceso_cast_union (Q : {set L}) (x : 'F[HL]_(Q :|: (setT :\: Q))) :
  ptraceso Q (castlf (setUD_sub (subsetT Q), setUD_sub (subsetT Q)) x) = ptrace_castl (disjointXD Q setT) x.
Proof. by rewrite /ptrace_castl /ptrace_cast_gen (@ptracelf_castlf_eq R L HL (Q :|: (setT :\: Q)) setT Q (setUD_sub (subsetT Q)) (setDU_l (disjointXD Q setT)) x). Qed.

Lemma sdot1_tenf (A B : {set L}) (N : 'F[HL]_B) : [disjoint A & B] -> ((\1 : 'F[HL]_A) \O N) = (\1 : 'F[HL]_A) \⊗ N.
Proof. by move=> HAB; apply/to_Fnd_inj; rewrite sdotFT // to_Fnd_tenE. Qed.

Lemma liftf_lf_in_compl (S Q : {set L}) (subSQ : S :<=: setT :\: Q) (f : 'F[HL]_S) :
  liftf_lf f = castlf (setUD_sub (subsetT Q), setUD_sub (subsetT Q)) ((\1 : 'F[HL]_Q) \⊗ lift_lf subSQ f).
Proof. symmetry; rewrite -[LHS](liftf_lf_id (castlf (setUD_sub (subsetT Q), setUD_sub (subsetT Q)) ((\1 : 'F[HL]_Q) \⊗ lift_lf subSQ f))). by rewrite liftf_lf_cast liftf_lf_tenf1l; [rewrite liftf_lf2 | exact: disjointXD]. Qed.

Lemma appendso_comp_keep (Q : {set L}) (rho : 'F[HL]_Q) (A B : 'F[HL]_Q) (x : 'F[HL]_(setT :\: Q)) :
  (liftf_lf A \o appendso rho x \o liftf_lf B)%VF = appendso ((A \o rho \o B)%VF) x.
Proof.
  have Happend (r : 'F[HL]_Q) : appendso r x = liftf_lf (r \⊗ x) by rewrite appendsoE -[LHS]liftf_lf_id liftf_lf_cast.
  rewrite !Happend -[liftf_lf A](liftf_lf_tenf1r A (disjointXD Q setT)).
  rewrite -[liftf_lf B](liftf_lf_tenf1r B (disjointXD Q setT)) -!liftf_lf_comp; congr (liftf_lf _).
  rewrite -[(A \⊗ _) \o (rho \⊗ x)]tenf_comp; last exact: disjointXD. rewrite comp_lfun1l -tenf_comp; last exact: disjointXD.
  by rewrite comp_lfun1r. Qed.

Lemma ptraceso_liftf_lf_tr (Q : {set L}) (x : 'F[HL]_setT) (N : 'F[HL]_(setT :\: Q)) : \Tr (ptraceso Q x \o N) = \Tr (x \o liftf_lf N).
Proof.
  set eQ := setUD_sub (subsetT Q); set xQ := castlf (esym eQ, esym eQ) x.
  have Hx : x = castlf (eQ, eQ) xQ by rewrite /xQ castlf_comp castlf_id.
  rewrite {1 2}Hx ptraceso_cast_union (liftf_lf_in_compl (subxx (setT :\: Q)) N).
  transitivity (\Tr (xQ \o ((\1 : 'F[HL]_Q) \O N))); first by symmetry; exact: trlf_lift_partial.
  rewrite (sdot1_tenf N (disjointXD Q setT)).
  by rewrite /eQ -(castlf_complf (setUD_sub (subsetT Q)) (setUD_sub (subsetT Q)) (setUD_sub (subsetT Q))) [RHS]castlf_trlfE lift_lf_id. Qed.

Fact ptraceso_weaken_eq (A Q : {set L}) (subAQ : A :<=: Q) (x y : 'F[HL]_setT) :
  ptraceso A x = ptraceso A y -> ptraceso Q x = ptraceso Q y.
Proof.
  move=> Hxy; apply/eqP/trlf_intror=> N.
  have subQA : setT :\: Q :<=: setT :\: A by exact: setDS subAQ.
  set NA := lift_lf subQA N; have Hlift : liftf_lf N = liftf_lf NA by rewrite /NA liftf_lf2. rewrite !ptraceso_liftf_lf_tr Hlift.
  move: (congr1 (fun z => \Tr (z \o NA)) Hxy); by rewrite !ptraceso_liftf_lf_tr. Qed.

Lemma ptraceso_liftfso_compl (Q S : {set L}) (subSQ : S :<=: setT :\: Q) (E : 'SO[HL]_S) (x : 'F[HL]_setT) :
  ptraceso Q (liftfso E x) = liftso subSQ E (ptraceso Q x).
Proof. apply/eqP/trlf_intror=> N. rewrite ptraceso_liftf_lf_tr dualso_trlfE liftfso_dual -(liftfso2 subSQ (E^*o)) liftfsoEf dualso_trlfE. by rewrite (@ptraceso_liftf_lf_tr Q x ((liftso subSQ E)^*o N)) liftso_dual. Qed.

Lemma ptrace_cast_gen_setC_liftf_lf_tr (T : {set L}) (eqT : setT :\: setC T = T) (x : 'F[HL]_setT) (N : 'F[HL]_T) :
  \Tr (ptrace_cast_gen eqT x \o N) = \Tr (x \o liftf_lf N).
Proof. rewrite /ptrace_cast_gen; set N0 := castlf (esym eqT, esym eqT) N. have HN : N = castlf (eqT, eqT) N0 by rewrite /N0 castlf_comp castlf_id. by rewrite {1}HN -(castlf_complf eqT eqT eqT) castlf_trlfE ptraceso_liftf_lf_tr /N0 liftf_lf_cast. Qed.

Lemma ptrace_cast_gen_sum (S T : {set L}) (eqT : setT :\: S = T) (I : finType) (F : I -> 'F[HL]_setT) :
  ptrace_cast_gen eqT (\sum_i F i) = \sum_i ptrace_cast_gen eqT (F i).
Proof. by rewrite /ptrace_cast_gen linear_sum /= linear_sum. Qed.

Lemma ptrace_cast_gen_scale (S T : {set L}) (eqT : setT :\: S = T) (c : C) (x : 'F[HL]_setT) :
  ptrace_cast_gen eqT (c *: x) = c *: ptrace_cast_gen eqT x.
Proof. by rewrite /ptrace_cast_gen linearZ /= linearZ. Qed.

Lemma ptrace_cast_gen0 (S T : {set L}) (eqT : setT :\: S = T) : ptrace_cast_gen eqT 0 = 0 :> 'F[HL]_T.
Proof. by rewrite /ptrace_cast_gen linear0 linear0. Qed.

Lemma replaceso_formso_compC (S Q : {set L}) (subSQ : S :<=: setT :\: Q) (f : 'F[HL]_S) (rho : 'F[HL]_Q) :
  formso (liftf_lf f) :o replaceso rho = replaceso rho :o formso (liftf_lf f).
Proof.
have appendso_formlf_compl : forall (Q : {set L}) (rho : 'F[HL]_Q) (N : 'F[HL]_(setT :\: Q)) (x : 'F[HL]_(setT :\: Q)), formlf (castlf (setUD_sub (subsetT Q), setUD_sub (subsetT Q)) ((\1 : 'F[HL]_Q) \⊗ N)) (appendso rho x) = appendso rho (formlf N x).
{ clear rho f subSQ Q S; move=> Q rho N x. rewrite !appendsoE !formlfE.
  rewrite castlf_adj/= -!castlf_complf -!tenf_comp ?disjointXD ?comp_lfun1l ?comp_lfun1r. rewrite tenf_adj adjf1 -tenf_comp ?comp_lfun1r //.
  all: by rewrite ?disjointXD. } have ptraceso_formlf_compl : forall (Q : {set L}) (N : 'F[HL]_(setT :\: Q)) (x : 'F[HL]_setT), ptraceso Q (formlf (castlf (setUD_sub (subsetT Q), setUD_sub (subsetT Q)) ((\1 : 'F[HL]_Q) \⊗ N)) x) = formlf N (ptraceso Q x).
{ clear rho f subSQ Q S; move=> Q N x. have ptrace_castl_formlf_tenf_I : forall (A B : {set L}) (disAB : [disjoint A & B]) (N : 'F[HL]_B) (rho : 'F[HL]_(A :|: B)), ptrace_castl disAB (formlf ((\1 : 'F[HL]_A) \⊗ N) rho) = formlf N (ptrace_castl disAB rho).
{ clear x N Q; move=> A B disAB N rho. rewrite -(@sdot1_tenf A B N disAB). exact: ptrace_castl_formlf_lift_I. } set eQ := setUD_sub (subsetT Q); set xQ := castlf (esym eQ, esym eQ) x.
  have Hx : x = castlf (eQ, eQ) xQ by rewrite /xQ castlf_comp castlf_id.
  rewrite {1 2}Hx !formlfE castlf_adj/= -!castlf_complf.
  rewrite -formlfE ptraceso_cast_union ptrace_castl_formlf_tenf_I -ptraceso_cast_union.
  by rewrite formlfE. } apply/superopP=> x; rewrite !comp_soE [X in formso X _](liftf_lf_in_compl subSQ f). rewrite -formlf_soE appendso_formlf_compl.
  rewrite [X in \Tr_(Q) (formso X x)](liftf_lf_in_compl subSQ f). by rewrite -formlf_soE ptraceso_formlf_compl. Qed.

Fact appendso0 (Q : {set L}) (rho : 'F[HL]_Q) : appendso rho 0 = 0.
Proof. by rewrite /appendso /fun_of_superof/= lfunE linear0. Qed.

Lemma replaceso0 (Q : {set L}) (rho : 'F[HL]_Q) : replaceso rho 0 = 0.
Proof. by rewrite replacesoE linear0 appendso0. Qed.

Fact appendsoZ (Q : {set L}) (a : C) (rho : 'F[HL]_Q) (x : 'F[HL]_(setT :\: Q)) : appendso (a *: rho) x = a *: appendso rho x.
Proof. by rewrite !appendsoE tenfZl linearZ. Qed.

Lemma replacesoZ (Q : {set L}) (a : C) (rho : 'F[HL]_Q) (x : 'F[HL]_setT) : replaceso (a *: rho) x = a *: replaceso rho x.
Proof. by rewrite !replacesoE appendsoZ. Qed.

Lemma liftfso0 (Q : {set L}) (E : 'SO[HL]_Q) : liftfso E 0 = 0.
Proof. by rewrite /liftfso linear0. Qed.

Lemma appendso_trlf (Q : {set L}) (rho : 'F[HL]_Q) (x : 'F[HL]_(setT :\: Q)) : \Tr (appendso rho x) = \Tr rho * \Tr x.
Proof. by rewrite appendsoE castlf_trlfE lftrace_tenf ?disjointXD. Qed.

Fact appendso_formso_sub_tr (Q S : {set L}) (subSQ : S :<=: Q) (rho : 'F[HL]_Q) (F : 'F[HL]_S) (x : 'F[HL]_(setT :\: Q)) :
  \Tr (formso (liftf_lf F) (appendso rho x)) = \Tr (formlf (lift_lf subSQ F) rho) * \Tr x.
Proof. set FQ := lift_lf subSQ F. have Hlift : liftf_lf F = liftf_lf FQ by rewrite /FQ liftf_lf2. by rewrite Hlift formsoE -liftf_lf_adj appendso_comp_keep -formlfE appendso_trlf. Qed.

Lemma replaceso_trlf_den1 (Q : {set L}) (rho : 'F[HL]_Q) (x : 'F[HL]_setT) : rho \is den1lf -> \Tr (replaceso rho x) = \Tr x.
Proof. move=> Hrho; rewrite replacesoE appendso_trlf (den1lf_trlf Hrho) mul1r. by case/cptpP: (@ptraceso_qc R L HL Q setT) => _ /tpmapP ->. Qed.

Lemma ptrace_cast3A_sdot_right (A B C0 : {set L}) (disAB : [disjoint A & B]) (disAC : [disjoint A & C0])
    (disBC : [disjoint B & C0]) (x : 'F[HL]_(A :|: B)) (y : 'F[HL]_C0) :
  ptrace_cast3A disAB disAC ((x \O y) : 'F[HL]_(A :|: B :|: C0)) = ((ptrace_castl disAB x) \O y : 'F[HL]_(B :|: C0)).
Proof.
have ptrace_cast3A_sdot_left : forall (A B C0 : {set L}) (disAB : [disjoint A & B]) (disAC : [disjoint A & C0]) (x : 'F[HL]_A) (y : 'F[HL]_(B :|: C0)), ptrace_cast3A disAB disAC (castlf (finset.setUA A B C0, finset.setUA A B C0) ((x \O y) : 'F[HL]_(A :|: (B :|: C0)))) = \Tr x *: y.
{ clear y x disBC disAC disAB C0 B A; move=> A B C0 disAB disAC x y. have disA_BC : [disjoint A & B :|: C0] by rewrite disjointXU disAB disAC. have Hrecast (z : 'F[HL]_(A :|: (B :|: C0))) : ptrace_cast3A disAB disAC (castlf (finset.setUA A B C0, finset.setUA A B C0) z) = ptrace_castl disA_BC z.
  { have eq_res : (A :|: (B :|: C0)) :\: A = (A :|: B :|: C0) :\: A by rewrite finset.setUA.
    rewrite /ptrace_cast3A /ptrace_castl /ptrace_cast_gen (ptracelf_castlf_eq (finset.setUA A B C0) eq_res) castlf_comp.
    by congr (castlf (_, _) _); exact: eq_irrelevance. } by rewrite Hrecast ptrace_castl_sdot_trace_l. } have Hbasis (i j : 'Idx[HL]_(A :|: B)) : ptrace_cast3A disAB disAC (([> deltav i ; deltav j <] \O y) : 'F[HL]_(A :|: B :|: C0)) = (ptrace_castl disAB [> deltav i ; deltav j <] \O y : 'F[HL]_(B :|: C0)).
  { pose xA : 'F[HL]_A := [> deltav (idxSl i) ; deltav (idxSl j) <].
    pose xB : 'F[HL]_B := [> deltav (idxSr i) ; deltav (idxSr j) <].
    have Hx_split : [> deltav i ; deltav j <] = (xA \O xB : 'F[HL]_(A :|: B)).
    { apply: to_Fnd_inj. by rewrite /xA /xB !dv_split -tenf_outp to_Fnd_tenE (sdotFT _ _ disAB). } have Hassoc : ((xA \O xB) \O y : 'F[HL]_(A :|: B :|: C0)) = castlf (finset.setUA A B C0, finset.setUA A B C0) ((xA \O (xB \O y)) : 'F[HL]_(A :|: (B :|: C0))).
    { apply: to_Fnd_inj. by rewrite Fnd_cast !to_Fnd_sdotE -!dotFsA // disjointXU disAB disAC. } by rewrite Hx_split Hassoc ptrace_cast3A_sdot_left ptrace_castl_sdot_trace_l sdotfZl. } have Hptr3A_sum (I0 : finType) (P0 : pred I0) (F : I0 -> 'F[HL]_(A :|: B :|: C0)) : ptrace_cast3A disAB disAC (\sum_(i | P0 i) F i) = \sum_(i | P0 i) ptrace_cast3A disAB disAC (F i).
  { rewrite /ptrace_cast3A /ptrace_cast_gen [\Tr_(A) _]raddf_sum /=. by rewrite raddf_sum. } have Hptr_l_sum (I0 : finType) (P0 : pred I0) (F : I0 -> 'F[HL]_(A :|: B)) : ptrace_castl disAB (\sum_(i | P0 i) F i) = \sum_(i | P0 i) ptrace_castl disAB (F i).
  { rewrite /ptrace_castl /ptrace_cast_gen [\Tr_(A) _]raddf_sum /=. by rewrite raddf_sum. } have Hptr3A_Z (c : C) (z : 'F[HL]_(A :|: B :|: C0)) : ptrace_cast3A disAB disAC (c *: z) = c *: ptrace_cast3A disAB disAC z.
  { rewrite /ptrace_cast3A /ptrace_cast_gen [\Tr_(A) _]linearZ /=. by rewrite linearZ. } have Hptr_l_Z (c : C) (z : 'F[HL]_(A :|: B)) : ptrace_castl disAB (c *: z) = c *: ptrace_castl disAB z.
  { rewrite /ptrace_castl /ptrace_cast_gen [\Tr_(A) _]linearZ /=. by rewrite linearZ. } rewrite [x in ptrace_cast3A _ _ (x \O y)](onb_lfun2id deltav x). rewrite [x in (ptrace_castl _ x \O y)](onb_lfun2id deltav x).
  rewrite sdotf_suml Hptr3A_sum Hptr_l_sum sdotf_suml /=; apply: eq_bigr=> i _.
  rewrite sdotf_suml Hptr3A_sum Hptr_l_sum sdotf_suml /=; apply: eq_bigr=> j _. by rewrite sdotfZl Hptr3A_Z Hptr_l_Z sdotfZl Hbasis. Qed.

Fact ptraceso_cast3A_sdot_right (A B C0 : {set L}) (disAB : [disjoint A & B]) (disAC : [disjoint A & C0])
    (disBC : [disjoint B & C0]) (eqABC : A :|: B :|: C0 = setT) (rhoAB : 'F[HL]_(A :|: B)) (x : 'F[HL]_C0) :
  ptraceso A (castlf (eqABC, eqABC) ((rhoAB \O x) : 'F[HL]_(A :|: B :|: C0))) =
  castlf (etrans (esym (setDU3_A disAB disAC)) (f_equal (fun S => S :\: A) eqABC),
     etrans (esym (setDU3_A disAB disAC)) (f_equal (fun S => S :\: A) eqABC)) ((ptrace_castl disAB rhoAB \O x) : 'F[HL]_(B :|: C0)).
Proof. have eq_res : (A :|: B :|: C0) :\: A = setT :\: A by rewrite eqABC. rewrite (ptracelf_castlf_eq eqABC eq_res) -(@ptrace_cast3A_sdot_right A B C0 disAB disAC disBC rhoAB x). by rewrite /ptrace_cast3A /ptrace_cast_gen castlf_comp; congr (castlf (_, _) _); exact: eq_irrelevance. Qed.

Fact ptraceso_appendso_union_l (A B C0 : {set L}) (disAB : [disjoint A & B]) (disAC : [disjoint A & C0])
    (disBC : [disjoint B & C0]) (disAB_C : [disjoint A :|: B & C0]) (eqABC : A :|: B :|: C0 = setT)
    (rhoAB : 'F[HL]_(A :|: B)) (x : 'F[HL]_C0) :
  ptraceso A (appendso rhoAB (castlf (etrans (esym (setDU_l disAB_C)) (f_equal (fun S => S :\: (A :|: B)) eqABC),
         etrans (esym (setDU_l disAB_C)) (f_equal (fun S => S :\: (A :|: B)) eqABC)) x)) =
  castlf (etrans (esym (setDU3_A disAB disAC)) (f_equal (fun S => S :\: A) eqABC),
     etrans (esym (setDU3_A disAB disAC)) (f_equal (fun S => S :\: A) eqABC)) ((ptrace_castl disAB rhoAB \O x) : 'F[HL]_(B :|: C0)).
Proof. rewrite appendsoE -(@ptraceso_cast3A_sdot_right A B C0 disAB disAC disBC eqABC rhoAB x). congr (ptraceso A _); apply: to_Fnd_inj. by rewrite !Fnd_cast to_Fnd_tenE to_Fnd_sdotE dotFT; [rewrite Fnd_cast | exact: disAB_C]. Qed.

Fact ptraceso_cast3A_sdot_right_den1 (A B C0 : {set L}) (disAB : [disjoint A & B]) (disAC : [disjoint A & C0])
    (disBC : [disjoint B & C0]) (eqABC : A :|: B :|: C0 = setT) (rhoA : 'F[HL]_A) (rhoB : 'F[HL]_B) (x : 'F[HL]_C0) :
  rhoA \is den1lf -> ptraceso A (castlf (eqABC, eqABC) ((((rhoA \O rhoB) : 'F[HL]_(A :|: B)) \O x) : 'F[HL]_(A :|: B :|: C0))) =
  castlf (etrans (esym (setDU3_A disAB disAC)) (f_equal (fun S => S :\: A) eqABC),
     etrans (esym (setDU3_A disAB disAC)) (f_equal (fun S => S :\: A) eqABC)) ((rhoB \O x) : 'F[HL]_(B :|: C0)).
Proof.
  move=> HrhoA; have eq_res : (A :|: B :|: C0) :\: A = setT :\: A by rewrite eqABC. rewrite (ptracelf_castlf_eq eqABC eq_res).
  have HptrAB : ptrace_castl disAB ((rhoA \O rhoB) : 'F[HL]_(A :|: B)) = rhoB by rewrite ptrace_castl_sdot_trace_l (den1lf_trlf HrhoA) scale1r.
  rewrite -{2}HptrAB.
  rewrite -(@ptrace_cast3A_sdot_right A B C0 disAB disAC disBC ((rhoA \O rhoB) : 'F[HL]_(A :|: B)) x).
  by rewrite /ptrace_cast3A /ptrace_cast_gen castlf_comp; congr (castlf (_, _) _); exact: eq_irrelevance. Qed.

Fact ptraceso_appendso_union_l_den1 (A B C0 : {set L}) (disAB : [disjoint A & B]) (disAC : [disjoint A & C0])
    (disBC : [disjoint B & C0]) (disAB_C : [disjoint A :|: B & C0]) (eqABC : A :|: B :|: C0 = setT)
    (rhoA : 'F[HL]_A) (rhoB : 'F[HL]_B) (x : 'F[HL]_C0) : rhoA \is den1lf -> ptraceso A (appendso ((rhoA \O rhoB) : 'F[HL]_(A :|: B))
      (castlf (etrans (esym (setDU_l disAB_C)) (f_equal (fun S => S :\: (A :|: B)) eqABC),
         etrans (esym (setDU_l disAB_C)) (f_equal (fun S => S :\: (A :|: B)) eqABC)) x)) =
  castlf (etrans (esym (setDU3_A disAB disAC)) (f_equal (fun S => S :\: A) eqABC),
     etrans (esym (setDU3_A disAB disAC)) (f_equal (fun S => S :\: A) eqABC)) ((rhoB \O x) : 'F[HL]_(B :|: C0)).
Proof.
  move=> HrhoA; rewrite appendsoE -(@ptraceso_cast3A_sdot_right_den1 A B C0 disAB disAC disBC eqABC rhoA rhoB x HrhoA).
  congr (ptraceso A _); apply: to_Fnd_inj. rewrite !Fnd_cast to_Fnd_tenE to_Fnd_sdotE dotFT.
  - rewrite Fnd_cast !to_Fnd_sdotE [X in (X \· to_Fnd x)%FND]dotFT; last exact: disAB.
    by rewrite dotFT; last by rewrite disjointUX disAC disBC.
  - exact: disAB. Qed.

Fact ptraceso_cast3B_sdot_right (A B C0 : {set L}) (disAB : [disjoint A & B]) (disAC : [disjoint A & C0])
    (disBC : [disjoint B & C0]) (eqABC : A :|: B :|: C0 = setT) (x : 'F[HL]_A) (y : 'F[HL]_(B :|: C0)) : ptraceso B (castlf (eqABC, eqABC)
      (castlf (finset.setUA A B C0, finset.setUA A B C0) ((x \O y) : 'F[HL]_(A :|: (B :|: C0))))) =
  castlf (etrans (esym (setDU3_B disAB disBC)) (f_equal (fun S => S :\: B) eqABC),
     etrans (esym (setDU3_B disAB disBC)) (f_equal (fun S => S :\: B) eqABC)) ((x \O ptrace_castl disBC y) : 'F[HL]_(A :|: C0)).
Proof. have eq_res : (A :|: B :|: C0) :\: B = setT :\: B by rewrite eqABC. rewrite (ptracelf_castlf_eq eqABC eq_res) -(@ptrace_cast3B_sdot_right R L HL A B C0 disAB disBC disAC x y). by rewrite /ptrace_cast3B /ptrace_cast_gen castlf_comp; congr (castlf (_, _) _); exact: eq_irrelevance. Qed.

Lemma ptraceso_appendso_complement (A B C0 : {set L}) (disAB : [disjoint A & B]) (disAC : [disjoint A & C0])
    (disBC : [disjoint B & C0]) (eqABC : A :|: B :|: C0 = setT) (rhoA : 'F[HL]_A) (y : 'F[HL]_(B :|: C0)) :
  ptraceso B (appendso rhoA (castlf (etrans (esym (setDU3_A disAB disAC)) (f_equal (fun S => S :\: A) eqABC),
         etrans (esym (setDU3_A disAB disAC)) (f_equal (fun S => S :\: A) eqABC)) y)) =
  castlf (etrans (esym (setDU3_B disAB disBC)) (f_equal (fun S => S :\: B) eqABC),
     etrans (esym (setDU3_B disAB disBC)) (f_equal (fun S => S :\: B) eqABC)) ((rhoA \O ptrace_castl disBC y) : 'F[HL]_(A :|: C0)).
Proof. rewrite appendsoE -(@ptraceso_cast3B_sdot_right A B C0 disAB disAC disBC eqABC rhoA y). congr (ptraceso B _); apply: to_Fnd_inj. by rewrite !Fnd_cast to_Fnd_tenE to_Fnd_sdotE dotFT; [rewrite Fnd_cast | rewrite disjointXU disAB disAC]. Qed.

Lemma ptrace_castl_ptraceso_union (A B C0 : {set L}) (disAB : [disjoint A & B]) (disAC : [disjoint A & C0])
    (disBC : [disjoint B & C0]) (disAB_C : [disjoint A :|: B & C0]) (eqABC : A :|: B :|: C0 = setT) (rho : 'F[HL]_setT) :
  let eqAC := etrans (esym (setDU3_B disAB disBC)) (f_equal (fun S => S :\: B) eqABC) in
  let eqC := etrans (esym (setDU_l disAB_C)) (f_equal (fun S => S :\: (A :|: B)) eqABC) in
  ptrace_castl disAC (castlf (esym eqAC, esym eqAC) (ptraceso B rho)) = castlf (esym eqC, esym eqC) (ptraceso (A :|: B) rho).
Proof.
  move=> eqAC eqC; rewrite /ptrace_castl /ptrace_cast_gen (ptracelf_castlf_eq (esym eqAC) (f_equal (fun S => S :\: A) (esym eqAC))).
  have Hcomp := congr1 (fun F : 'SO[HL]_(setTfor L, ((setTfor L :\: B) :\: A)) => F rho) (@ptraceso_comp R L HL A B (setTfor L)).
  move: Hcomp; rewrite comp_soE castsoE /= castlf_id => Hcomp; rewrite Hcomp.
  have Htrace_comm : ptraceso (B :|: A) rho = castlf (esym (f_equal (fun S => setT :\: S) (finset.setUC B A)), esym (f_equal (fun S => setT :\: S) (finset.setUC B A))) (ptraceso (A :|: B) rho).
  { by case: _ / (finset.setUC B A); rewrite castlf_id. } by rewrite Htrace_comm !castlf_comp; congr (castlf (_, _) _); exact: eq_irrelevance. Qed.

Lemma ptraceso_replaceso_disjoint_eq (A B C0 : {set L}) (disAB : [disjoint A & B]) (disAC : [disjoint A & C0])
    (disBC : [disjoint B & C0]) (eqABC : A :|: B :|: C0 = setT) (rho : 'F[HL]_A) (x y : 'F[HL]_setT) :
  ptraceso B x = ptraceso B y -> ptraceso B (replaceso rho x) = ptraceso B (replaceso rho y).
Proof.
  move=> Hxy; have disBA : [disjoint B & A] by rewrite disjoint_sym disAB.
  have disAB_C : [disjoint A :|: B & C0] by rewrite disjointUX disAC disBC.
  have disBA_C : [disjoint B :|: A & C0] by rewrite disjointUX disBC disAC.
  have eqBAC : B :|: A :|: C0 = setT by rewrite [B :|: A]finset.setUC eqABC.
  set eqBC := etrans (esym (setDU3_A disAB disAC)) (f_equal (fun S => S :\: A) eqABC).
  set eqAC := etrans (esym (setDU3_A disBA disBC)) (f_equal (fun S => S :\: B) eqBAC).
  set eqC := etrans (esym (setDU_l disAB_C)) (f_equal (fun S => S :\: (A :|: B)) eqABC).
  have Htail (z : 'F[HL]_setT) : ptrace_castl disBC (castlf (esym eqBC, esym eqBC) (ptraceso A z)) = castlf (esym eqC, esym eqC) (ptraceso (A :|: B) z).
  { have Hswap := @ptrace_castl_ptraceso_union B A C0 disBA disBC disAC disBA_C eqBAC z.
    rewrite /= in Hswap.
    transitivity (ptrace_castl disBC (castlf (esym (etrans (esym (setDU3_B disBA disAC)) (f_equal (fun S => S :\: A) eqBAC)), esym (etrans (esym (setDU3_B disBA disAC)) (f_equal (fun S => S :\: A) eqBAC))) (ptraceso A z))).
    { by congr (ptrace_castl _ (castlf (_, _) _)); exact: eq_irrelevance. } rewrite Hswap /eqC. have Htrace_comm : ptraceso (B :|: A) z = castlf (esym (f_equal (fun S => setT :\: S) (finset.setUC B A)), esym (f_equal (fun S => setT :\: S) (finset.setUC B A))) (ptraceso (A :|: B) z).
    { by case: _ / (finset.setUC B A); rewrite castlf_id. } by rewrite Htrace_comm !castlf_comp; congr (castlf (_, _) _); exact: eq_irrelevance. } have HtailB (z : 'F[HL]_setT) : ptrace_castl disAC (castlf (esym eqAC, esym eqAC) (ptraceso B z)) = castlf (esym eqC, esym eqC) (ptraceso (A :|: B) z).
  { transitivity (ptrace_castl disAC (castlf (esym (etrans (esym (setDU3_B disAB disBC)) (f_equal (fun S => S :\: B) eqABC)), esym (etrans (esym (setDU3_B disAB disBC)) (f_equal (fun S => S :\: B) eqABC))) (ptraceso B z))).
    { by congr (ptrace_castl _ (castlf (_, _) _)); exact: eq_irrelevance. } rewrite /eqAC /eqC (@ptrace_castl_ptraceso_union A B C0 disAB disAC disBC disAB_C eqABC z).
    by congr (castlf (_, _) _); exact: eq_irrelevance. } have Hunion : castlf (esym eqC, esym eqC) (ptraceso (A :|: B) x) = castlf (esym eqC, esym eqC) (ptraceso (A :|: B) y).
  { by rewrite -!(HtailB _) Hxy. } rewrite !replacesoE. set xBC := castlf (esym eqBC, esym eqBC) (ptraceso A x). set yBC := castlf (esym eqBC, esym eqBC) (ptraceso A y).
  have HxBC : ptraceso A x = castlf (eqBC, eqBC) xBC by rewrite /xBC castlf_comp (eq_irrelevance (etrans (esym eqBC) eqBC) erefl) castlf_id.
  have HyBC : ptraceso A y = castlf (eqBC, eqBC) yBC by rewrite /yBC castlf_comp (eq_irrelevance (etrans (esym eqBC) eqBC) erefl) castlf_id.
  rewrite {1}HxBC {1}HyBC.
  rewrite (@ptraceso_appendso_complement A B C0 disAB disAC disBC eqABC rho xBC).
  rewrite (@ptraceso_appendso_complement A B C0 disAB disAC disBC eqABC rho yBC).
  have Htail_xy : ptrace_castl disBC xBC = ptrace_castl disBC yBC by rewrite /xBC /yBC !Htail; exact: Hunion. by rewrite Htail_xy. Qed.

Fact appendso_psd (Q : {set L}) (rho : 'F[HL]_Q) (x : 'F[HL]_(setT :\: Q)) : rho \is psdlf -> x \is psdlf -> appendso rho x \is psdlf.
Proof. by move=> Hrho Hx; rewrite appendsoE castlf_psdlfE psdlfE; apply: tenf_ge0; [exact: disjointXD | rewrite -psdlfE | rewrite -psdlfE]. Qed.

Lemma replaceso_psd (Q : {set L}) (rho : 'F[HL]_Q) (x : 'F[HL]_setT) : rho \is psdlf -> x \is psdlf -> replaceso rho x \is psdlf.
Proof. by move=> Hrho Hx; rewrite replacesoE; apply: appendso_psd; [exact: Hrho | exact: cp_psdP Hx]. Qed.

Variable EA : adversary.

Fixpoint denote (c : cmd) (xi : cq_state) {struct c} : cq_state := match c with
  | Cskip => xi
  | Cassign x e => [ffun t : store => \sum_(s : store | store_set s x (e s) == t) xi s]
  | Csample x mu => [ffun t : store => \sum_(s : store) \sum_(v | store_set s x v == t) (mu s v)%:C *: xi s]
  | Cinit Q rho => [ffun s : store => replaceso (rho s) (xi s)]
  | Cmeasure x Q M => [ffun t : store => \sum_(s : store) \sum_(v | store_set s x v == t) formso (liftf_lf (M s v)) (xi s)]
  | Cattack Q => [ffun s : store => liftfso (EA Q (s Pvar)) (xi s)]
  | Cif b c1 c2 => denote c1 [ffun s : store => if b s then xi s else 0] + denote c2 [ffun s : store => if b s then 0 else xi s]
  | Cseq c1 c2 => denote c2 (denote c1 xi) end.

Definition denote_singleton (c : cmd) (s : store) (rho : 'F[HL]_setT) : cq_state := denote c (cq_single s rho).

Fact cq_single_same (s : store) (rho : 'F[HL]_setT) : cq_single s rho s = rho.
Proof. by rewrite /cq_single ffunE eqxx. Qed.

Fact cq_single_other (s t : store) (rho : 'F[HL]_setT) : t != s -> cq_single s rho t = 0.
Proof. by move=> Hts; rewrite /cq_single ffunE (negbTE Hts). Qed.

Lemma cq_single_scale (a : C) (s : store) (rho : 'F[HL]_setT) : cq_single s (a *: rho) = a *: cq_single s rho.
Proof. apply/ffunP=> t. rewrite /cq_single !ffunE. by case: (t == s); rewrite ?scaler0. Qed.

Lemma cq_single_zero (s : store) : cq_single s 0 = 0.
Proof. apply/ffunP=> t. by rewrite /cq_single !ffunE; case: (t == s). Qed.

Fact cq_zeroE (s : store) : (0 : cq_state) s = 0.
Proof. by rewrite /GRing.zero /= /ffun_zero ffunE. Qed.

Lemma cq_preimage (I : finType) (f : I -> store) (G : I -> 'F[HL]_setT) :
  [ffun t : store => \sum_(i | f i == t) G i] = \sum_i cq_single (f i) (G i).
Proof. by apply/ffunP=> t; rewrite ffunE sum_ffunE big_mkcond; apply: eq_bigr => i _; rewrite /cq_single ffunE eq_sym; case: (f i == t). Qed.

Lemma denote_zero_state (c : cmd) : denote c 0 = 0.
Proof.
  elim: c => //=.
  - by move=> x e; apply/ffunP=> t; rewrite !ffunE; apply: big1 => s _; rewrite ffunE.
  - by move=> x mu; apply/ffunP=> t; rewrite !ffunE; apply: big1 => s _; apply: big1 => v _; rewrite ffunE scaler0.
  - by move=> Q rho; apply/ffunP=> s; rewrite !ffunE replaceso0.
  - move=> x Q M; apply/ffunP=> t; rewrite !ffunE; apply: big1 => s _; apply: big1 => v _. by rewrite ffunE formsoE comp_lfun0r comp_lfun0l.
  - by move=> Q; apply/ffunP=> s; rewrite !ffunE liftfso0.
  - move=> b c1 IH1 c2 IH2.
    rewrite (_ : [ffun s : store => if b s then (0 : cq_state) s else 0] = 0); last by apply/ffunP=> s; rewrite !ffunE; case: (b s).
    rewrite (_ : [ffun s : store => if b s then 0 else (0 : cq_state) s] = 0); last by apply/ffunP=> s; rewrite !ffunE; case: (b s).
    by rewrite IH1 IH2 addr0.
  - by move=> c1 IH1 c2 IH2; rewrite IH1 IH2. Qed.

Lemma denote_skip_single (s : store) (rho : 'F[HL]_setT) : denote_singleton Cskip s rho = cq_single s rho.
Proof. by []. Qed.

Lemma denote_assign_single (x : Cv) (e : expr) (s : store) (rho : 'F[HL]_setT) :
  denote_singleton (Cassign x e) s rho = cq_single (store_set s x (e s)) rho.
Proof.
  apply/ffunP=> t; rewrite !ffunE /denote_singleton /cq_single /= big_mkcond (bigD1 s) //=. rewrite [X in _ + X]big1 ?addr0; last first.
    move=> u Hus; case: (store_set u x (e u) == t) => //. case Hu_s: (u == s); first by move: Hus; rewrite Hu_s.
    case Hs_u: (s == u); first by move: Hu_s; rewrite eq_sym Hs_u. by rewrite ffunE Hu_s. by rewrite ffunE eqxx eq_sym. Qed.

Lemma denote_sample_single (x : Cv) (mu : dexpr) (s : store) (rho : 'F[HL]_setT) :
  denote_singleton (Csample x mu) s rho = [ffun t : store => \sum_(v | store_set s x v == t) (mu s v)%:C *: rho].
Proof. apply/ffunP=> t; rewrite !ffunE /denote_singleton /cq_single /= (bigD1 s) //=. rewrite [X in _ + X]big1 ?addr0; last by move=> u Hus; apply: big1 => v _; rewrite ffunE (negbTE Hus) scaler0. by apply: eq_bigr => v _; rewrite ffunE eqxx. Qed.

Lemma denote_init_single (Q : {set L}) (rho0 : qexpr Q) (s : store) (rho : 'F[HL]_setT) :
  denote_singleton (Cinit Q rho0) s rho = cq_single s (replaceso (rho0 s) rho).
Proof. by apply/ffunP=> t; rewrite !ffunE /denote_singleton /cq_single /=; case Hts: (t == s); [move/eqP: Hts => -> | rewrite replaceso0]. Qed.

Lemma denote_measure_single (x : Cv) (Q : {set L}) (M : mexpr Q) (s : store) (rho : 'F[HL]_setT) : denote_singleton (Cmeasure x Q M) s rho =
  [ffun t : store => \sum_(v | store_set s x v == t) formso (liftf_lf (M s v)) rho].
Proof. apply/ffunP=> t; rewrite !ffunE /denote_singleton /cq_single /= (bigD1 s) //=. rewrite [X in _ + X]big1 ?addr0; last first. by move=> u Hus; apply: big1 => v _; rewrite ffunE (negbTE Hus) formsoE comp_lfun0r comp_lfun0l. by apply: eq_bigr => v _; rewrite ffunE eqxx. Qed.

Lemma denote_attack_single (Q : {set L}) (s : store) (rho : 'F[HL]_setT) :
  denote_singleton (Cattack Q) s rho = cq_single s (liftfso (EA Q (s Pvar)) rho).
Proof. by apply/ffunP=> t; rewrite !ffunE /denote_singleton /cq_single /=; case Hts: (t == s); [move/eqP: Hts => -> | rewrite liftfso0]. Qed.

Lemma denote_if_single (b : bexpr) (c1 c2 : cmd) (s : store) (rho : 'F[HL]_setT) :
  denote_singleton (Cif b c1 c2) s rho = if b s then denote_singleton c1 s rho else denote_singleton c2 s rho.
Proof.
  rewrite /denote_singleton /=. case Hbs: (b s).
  - rewrite (_ : [ffun t : store => if b t then cq_single s rho t else 0] = cq_single s rho); last by apply/ffunP=> t; rewrite !ffunE; case Hts: (t == s); [move/eqP: Hts => ->; rewrite Hbs | case: (b t)].
    rewrite (_ : [ffun t : store => if b t then 0 else cq_single s rho t] = 0); last by apply/ffunP=> t; rewrite !ffunE; case Hts: (t == s); [move/eqP: Hts => ->; rewrite Hbs | case: (b t)].
    by rewrite denote_zero_state addr0.
  - rewrite (_ : [ffun t : store => if b t then cq_single s rho t else 0] = 0); last by apply/ffunP=> t; rewrite !ffunE; case Hts: (t == s); [move/eqP: Hts => ->; rewrite Hbs | case: (b t)].
    rewrite (_ : [ffun t : store => if b t then 0 else cq_single s rho t] = cq_single s rho); last by apply/ffunP=> t; rewrite !ffunE; case Hts: (t == s); [move/eqP: Hts => ->; rewrite Hbs | case: (b t)].
    by rewrite denote_zero_state add0r. Qed.

Lemma denote_seq_single (c1 c2 : cmd) (s : store) (rho : 'F[HL]_setT) :
  denote_singleton (Cseq c1 c2) s rho = denote c2 (denote_singleton c1 s rho).
Proof. by []. Qed.

Lemma denote_seq_cmd (c1 c2 : cmd) (xi : cq_state) : denote (seq_cmd c1 c2) xi = denote c2 (denote c1 xi).
Proof. elim: c1 xi => /=; first by []. 1,2,3,4,5,6: by move=> *; case: (c2). by move=> c11 IH11 c12 IH12 xi; rewrite IH12. Qed.

Lemma cq_state_decomp (xi : cq_state) : xi = \sum_s cq_single s (xi s).
Proof. apply/ffunP=> t; rewrite sum_ffunE (bigD1 t) //= /cq_single ffunE eqxx. by rewrite [X in _ + X]big1 ?addr0 // => s Hst; rewrite /cq_single ffunE eq_sym (negbTE Hst). Qed.

Lemma cq_mass_single (s : store) (rho : 'F[HL]_setT) : cq_mass (cq_single s rho) = @complex.Re R (\Tr rho).
Proof. by rewrite /cq_mass (bigD1 s) //= /cq_single ffunE eqxx [X in _ + X]big1 ?addr0 // => t Hts; rewrite ffunE (negbTE Hts) linear0. Qed.

Lemma cq_mass_sum (I : finType) (F : I -> cq_state) : cq_mass (\sum_i F i) = \sum_i cq_mass (F i).
Proof. rewrite /cq_mass exchange_big /=; apply: eq_bigr => s _. have Htr : \Tr (\sum_i F i s) = \sum_i \Tr (F i s) by rewrite linear_sum. by rewrite sum_ffunE -[X in _ = X]raddf_sum -Htr /lftrace. Qed.

Fact cq_mass_scale (a : R) (xi : cq_state) : cq_mass (a%:C *: xi) = a * cq_mass xi.
Proof. rewrite /cq_mass mulr_sumr; apply: eq_bigr => s _. have HRe_realM (r : R) (z : C) : @complex.Re R (r%:C * z) = r * @complex.Re R z by case: z => zr zi /=; rewrite mul0r subr0. by rewrite ffunE linearZ /= HRe_realM. Qed.

Lemma denote_scale (c : cmd) (a : C) (xi : cq_state) : denote c (a *: xi) = a *: denote c xi.
Proof.
  elim: c xi => //=.
  - by move=> x e xi; apply/ffunP=> t; rewrite !ffunE scaler_sumr; apply: eq_bigr => s _; rewrite ffunE.
  - move=> x mu xi; apply/ffunP=> t; rewrite !ffunE scaler_sumr; apply: eq_bigr => s _; rewrite scaler_sumr.
    by apply: eq_bigr => v _; rewrite ffunE scalerA mulrC -scalerA.
  - by move=> Q rho xi; apply/ffunP=> s; rewrite !ffunE linearZ.
  - move=> x Q M xi; apply/ffunP=> t; rewrite !ffunE scaler_sumr; apply: eq_bigr => s _; rewrite scaler_sumr.
    apply: eq_bigr => v _; rewrite ffunE; have H := superop_is_linear (formso (liftf_lf (M s v))) a (xi s) 0.
    have Hf0 : formso (liftf_lf (M s v)) 0 = 0 by rewrite formsoE comp_lfun0r comp_lfun0l. by rewrite -[a *: xi s]addr0 H Hf0 addr0.
  - move=> Q xi; apply/ffunP=> s; rewrite !ffunE; have H := superop_is_linear (liftfso (EA Q (s Pvar))) a (xi s) 0.
    by rewrite -[a *: xi s]addr0 H liftfso0 addr0.
  - move=> b c1 IH1 c2 IH2 xi.
    rewrite (_ : [ffun s : store => if b s then (a *: xi) s else 0] = a *: [ffun s : store => if b s then xi s else 0]); last by apply/ffunP=> s; rewrite !ffunE; case: (b s); rewrite ?ffunE ?scaler0.
    rewrite (_ : [ffun s : store => if b s then 0 else (a *: xi) s] = a *: [ffun s : store => if b s then 0 else xi s]); last by apply/ffunP=> s; rewrite !ffunE; case: (b s); rewrite ?ffunE ?scaler0. by rewrite IH1 IH2 scalerDr.
  - by move=> c1 IH1 c2 IH2 xi; rewrite IH1 IH2. Qed.

Lemma denote_sum (I : finType) (c : cmd) (F : I -> cq_state) : denote c (\sum_i F i) = \sum_i denote c (F i).
Proof.
have denote_add : forall (c : cmd) (xi eta : cq_state), denote c (xi + eta) = denote c xi + denote c eta.
{ clear F c I; move=> c xi eta. elim: c xi eta => //=.
  - by move=> x e xi eta; apply/ffunP=> t; rewrite !ffunE -big_split /=; apply: eq_bigr => s _; rewrite ffunE.
  - move=> x mu xi eta; apply/ffunP=> t; rewrite !ffunE -big_split /=; apply: eq_bigr => s _; rewrite -big_split /=.
    by apply: eq_bigr => v _; rewrite ffunE scalerDr.
  - by move=> Q rho xi eta; apply/ffunP=> s; rewrite !ffunE linearD.
  - move=> x Q M xi eta; apply/ffunP=> t; rewrite !ffunE -big_split /=; apply: eq_bigr => s _; rewrite -big_split /=.
    by apply: eq_bigr => v _; rewrite ffunE linearD.
  - move=> Q xi eta; apply/ffunP=> s; rewrite !ffunE; have Hlin := superop_is_linear (liftfso (EA Q (s Pvar))).
    rewrite -[xi s]scale1r (Hlin 1 (xi s) (eta s)). have H0 : liftfso (EA Q (s Pvar)) (1 *: xi s) = 1 *: liftfso (EA Q (s Pvar)) (xi s).
    { by move: (Hlin 1 (xi s) 0); rewrite addr0 liftfso0 addr0. } by rewrite H0 scale1r.
  - move=> b c1 IH1 c2 IH2 xi eta. rewrite (_ : [ffun s : store => if b s then (xi + eta) s else 0] = [ffun s : store => if b s then xi s else 0] + [ffun s : store => if b s then eta s else 0]); last by apply/ffunP=> s; rewrite !ffunE; case: (b s); rewrite ?ffunE ?addr0.
    rewrite (_ : [ffun s : store => if b s then 0 else (xi + eta) s] = [ffun s : store => if b s then 0 else xi s] + [ffun s : store => if b s then 0 else eta s]); last by apply/ffunP=> s; rewrite !ffunE; case: (b s); rewrite ?ffunE ?add0r. by rewrite IH1 IH2 addrACA.
  - by move=> c1 IH1 c2 IH2 xi eta; rewrite IH1 IH2. } rewrite -!big_enum. elim: (enum xpredT) => [|i r IHr]; first by rewrite !big_nil denote_zero_state.
  by rewrite !big_cons denote_add IHr. Qed.

Lemma denote_sample_bind_single_sum (c : cmd) (x : Cv) (mu : dexpr) (s : store) (rho : 'F[HL]_setT) :
  denote c (denote_singleton (Csample x mu) s rho) = \sum_v (mu s v)%:C *: denote_singleton c (store_set s x v) rho.
Proof. rewrite denote_sample_single (cq_preimage (fun v => store_set s x v) (fun v => (mu s v)%:C *: rho)) denote_sum. by apply: eq_bigr => v _; rewrite cq_single_scale denote_scale /denote_singleton. Qed.

Fact denote_measure_bind_single_sum (c : cmd) (x : Cv) (Q : {set L}) (M : mexpr Q) (s : store) (rho : 'F[HL]_setT) :
  denote c (denote_singleton (Cmeasure x Q M) s rho) = \sum_v denote_singleton c (store_set s x v) (formso (liftf_lf (M s v)) rho).
Proof. rewrite denote_measure_single (cq_preimage (fun v => store_set s x v) (fun v => formso (liftf_lf (M s v)) rho)) denote_sum. by apply: eq_bigr => v _; rewrite /denote_singleton. Qed.

Lemma denote_assign_bind_single (c : cmd) (x : Cv) (e : expr) (s : store) (rho : 'F[HL]_setT) :
  denote c (denote_singleton (Cassign x e) s rho) = denote_singleton c (store_set s x (e s)) rho.
Proof. by rewrite denote_assign_single /denote_singleton. Qed.

Fact denote_init_bind_single (c : cmd) (Q : {set L}) (rho0 : qexpr Q) (s : store) (rho : 'F[HL]_setT) :
  denote c (denote_singleton (Cinit Q rho0) s rho) = denote_singleton c s (replaceso (rho0 s) rho).
Proof. by rewrite denote_init_single /denote_singleton. Qed.

Fact denote_attack_bind_single (c : cmd) (Q : {set L}) (s : store) (rho : 'F[HL]_setT) :
  denote c (denote_singleton (Cattack Q) s rho) = denote_singleton c s (liftfso (EA Q (s Pvar)) rho).
Proof. by rewrite denote_attack_single /denote_singleton. Qed.

Lemma denote_seq_assign_single (c : cmd) (x : Cv) (e : expr) (s : store) (rho : 'F[HL]_setT) :
  denote_singleton (seq_cmd (Cassign x e) c) s rho = denote_singleton c (store_set s x (e s)) rho.
Proof. by rewrite /denote_singleton denote_seq_cmd denote_assign_bind_single. Qed.

Lemma denote_seq_sample_single_sum (c : cmd) (x : Cv) (mu : dexpr) (s : store) (rho : 'F[HL]_setT) :
  denote_singleton (seq_cmd (Csample x mu) c) s rho = \sum_v (mu s v)%:C *: denote_singleton c (store_set s x v) rho.
Proof. by rewrite /denote_singleton denote_seq_cmd denote_sample_bind_single_sum. Qed.

Lemma denote_singleton_decomp (c : cmd) (xi : cq_state) : denote c xi = \sum_s denote_singleton c s (xi s).
Proof. by rewrite {1}(cq_state_decomp xi) denote_sum; apply: eq_bigr => s _; rewrite /denote_singleton. Qed.

Lemma denote_psd (c : cmd) (xi : cq_state) : @cmd_wf R L HL Cv V qA c -> (forall s, xi s \is psdlf) -> forall s, denote c xi s \is psdlf.
Proof.
  elim: c xi => /=.
  - by move=> xi _ Hxi s; exact: Hxi.
  - by move=> x e xi _ Hxi t; rewrite ffunE; apply: psdlf_sum => s _; exact: Hxi.
  - move=> x mu xi Hmu Hxi t; rewrite ffunE; apply: psdlf_sum => s _; apply: psdlf_sum => v _.
    by apply: psdlfZ; [rewrite ler0c; exact: (proj1 (Hmu s) v) | exact: Hxi].
  - by move=> Q rho xi [_ Hrho] Hxi s; rewrite ffunE; apply: replaceso_psd; [exact: (den1lf_psd (Hrho s)) | exact: Hxi].
  - by move=> x Q M xi _ Hxi t; rewrite ffunE; apply: psdlf_sum => s _; apply: psdlf_sum => v _; exact: cp_psdP (Hxi s).
  - move=> Q xi _ Hxi s; rewrite ffunE; have Hcptn : liftfso (EA Q (s Pvar)) \is cptn by rewrite liftfso_qoE is_cptn.
    exact: (cp_psdP (CPMap_Build (cptn_cpmap Hcptn)) (Hxi s)).
  - move=> b c1 IH1 c2 IH2 xi [Hc1 Hc2] Hxi s; rewrite ffunE; apply: psdlfD.
    + by apply: (IH1 _ Hc1) => t; rewrite ffunE; case: (b t); [exact: Hxi | exact: is_psdlf].
    + by apply: (IH2 _ Hc2) => t; rewrite ffunE; case: (b t); [exact: is_psdlf | exact: Hxi].
  - by move=> c1 IH1 c2 IH2 xi [Hc1 Hc2] Hxi s; apply: (IH2 _ Hc2); exact: (IH1 _ Hc1 Hxi). Qed.

Tactic Notation "cq_mass_decomp" uconstr(c) constr(xi) := rewrite -/(denote c xi) (denote_singleton_decomp c xi) cq_mass_sum {2}(cq_state_decomp xi) cq_mass_sum.

Lemma denote_mass (c : cmd) (xi : cq_state) : @cmd_wf R L HL Cv V qA c -> (forall s, xi s \is psdlf) -> cq_mass (denote c xi) = cq_mass xi.
Proof.
have cq_mass_add : forall (xi eta : cq_state), cq_mass (xi + eta) = cq_mass xi + cq_mass eta.
{ clear xi c; move=> xi eta. rewrite /cq_mass -big_split /=.
  by apply: eq_bigr => s _; rewrite ffunE linearD /= raddfD. } have HRe_realM (r : R) (z : C) : @complex.Re R (r%:C * z) = r * @complex.Re R z by case: z => zr zi /=; rewrite mul0r subr0.
  elim: c xi => //=.
  - by move=> x e xi _ _; cq_mass_decomp (Cassign x e) xi; apply: eq_bigr => s _; rewrite denote_assign_single !cq_mass_single.
  - move=> x mu xi Hmu _; cq_mass_decomp (Csample x mu) xi; apply: eq_bigr => s _.
    rewrite denote_sample_single (cq_preimage (fun v => store_set s x v) (fun v => (mu s v)%:C *: xi s)) cq_mass_sum.
    rewrite (eq_bigr (fun v : V => mu s v * @complex.Re R (\Tr (xi s)))).
    + by rewrite cq_mass_single -mulr_suml (proj2 (Hmu s)) mul1r.
    + by move=> v _; rewrite cq_mass_single linearZ /= HRe_realM.
  - move=> Q rho xi [_ Hrho] _; cq_mass_decomp (Cinit Q rho) xi.
    by apply: eq_bigr => s _; rewrite denote_init_single !cq_mass_single replaceso_trlf_den1.
  - move=> x Q M xi [_ HM] _; cq_mass_decomp (Cmeasure x Q M) xi; apply: eq_bigr => s _.
    rewrite denote_measure_single (cq_preimage (fun v => store_set s x v) (fun v => formso (liftf_lf (M s v)) (xi s))) cq_mass_sum.
    rewrite (eq_bigr (fun v : V => @complex.Re R (\Tr (formso (liftf_lf (M s v)) (xi s))))); last by move=> v _; rewrite cq_mass_single.
    rewrite cq_mass_single -raddf_sum; congr (@complex.Re R). have Hsum_lift : \sum_v ((liftf_lf (M s v))^A \o liftf_lf (M s v)) = \1.
    { under eq_bigr do rewrite -liftf_lf_adj -liftf_lf_comp. by rewrite -linear_sum /= (HM s) liftf_lf1. } rewrite (eq_bigr (fun v : V => \Tr (xi s \o ((liftf_lf (M s v))^A \o liftf_lf (M s v))))); last by move=> v _; rewrite formsoE -!comp_lfunA [LHS]lftraceC comp_lfunA.
    by rewrite -linear_sum /= -linear_sumr /= Hsum_lift comp_lfun1r.
  - move=> Q xi _ _; cq_mass_decomp (Cattack Q) xi; apply: eq_bigr => s _.
    have /tpmapP Htp : liftfso (EA Q (s Pvar)) \is tpmap by apply: liftso_tp. by rewrite denote_attack_single !cq_mass_single Htp.
  - move=> b c1 IH1 c2 IH2 xi [Hc1 Hc2] Hxi. have Hpsd1 : forall s, [ffun s : store => if b s then xi s else 0] s \is psdlf.
      by move=> s; rewrite ffunE; case: (b s); [exact: Hxi | exact: is_psdlf].
    have Hpsd2 : forall s, [ffun s : store => if b s then 0 else xi s] s \is psdlf.
      by move=> s; rewrite ffunE; case: (b s); [exact: is_psdlf | exact: Hxi].
    rewrite cq_mass_add (IH1 _ Hc1 Hpsd1) (IH2 _ Hc2 Hpsd2) /cq_mass -big_split /=.
    by apply: eq_bigr => s _; rewrite !ffunE; case: (b s); rewrite ?linear0 ?addr0 ?add0r.
  - by move=> c1 IH1 c2 IH2 xi [Hc1 Hc2] Hxi; rewrite (IH2 _ Hc2 (denote_psd Hc1 Hxi)); exact: (IH1 _ Hc1 Hxi). Qed.

Fact denote_cq_wf (c : cmd) (xi : cq_state) : @cmd_wf R L HL Cv V qA c -> cq_wf xi -> cq_wf (denote c xi).
Proof. by move=> Hc [Hpsd Hmass]; split; [exact: (denote_psd Hc Hpsd) | rewrite (denote_mass Hc Hpsd) Hmass]. Qed.

End StandardDenotation.
