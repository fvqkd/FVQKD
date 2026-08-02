(* -------------------------------------------------------------------- *)
(* prop.v -- Ambient set-labelled proof facts                           *)
(* -------------------------------------------------------------------- *)
(* Module: utils.labelled.prop                            *)
(* TeX source: none (library utility)                                    *)
(* TeX labels: none                                                      *)
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
From utils.labelled Require Import def.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Open Scope ring_scope.
Local Open Scope lfun_scope.

Section FvqkdReal.
Variable R : realType.
Notation C := (@hermitian.C R).
Notation chsType := (@chsType R).

Section BipartiteMatrixDefinitions.
Variable (L : finType) (H : L -> chsType).

(* biprod_of_mx_psd *)
(* infra: no tex label -- product-coordinate PSD transport *)
(* path: utils:biprod_of_mx_psd -> bb84:bb84_rhoZZ_passH_psd -> *)
(*   bb84:bb84_secret *)
Lemma biprod_of_mx_psd
    (A B : {set L}) (disAB : [disjoint A & B])
    (rhoAB : 'M[C]_(dim ('H[H]_A) * dim ('H[H]_B))) :
  rhoAB \is psdmx -> biprod_of_mx disAB rhoAB \is psdlf.
Proof.
  move=> Hrho.
  rewrite /biprod_of_mx qualifE mx2hK.
  apply: castmx_sq_psdmx.
  exact: psdmx_bimap_closed_gen Hrho.
Qed.

(* biprod_mxK *)
(* infra: no tex label -- product-coordinate round trip *)
(* path: utils:biprod_mxK -> bb84:bb84_rhoZZ_passH_biprod -> *)
(*   bb84:bb84_secret *)
Lemma biprod_mxK
    (A B : {set L}) (disAB : [disjoint A & B])
    (rhoAB : 'M[C]_(dim ('H[H]_A) * dim ('H[H]_B))) :
  biprod_mx disAB (biprod_of_mx disAB rhoAB) = rhoAB.
Proof.
  rewrite /biprod_mx /biprod_of_mx mx2hK.
  set Q : 'M[C]_(dim 'H[H]_A * dim 'H[H]_B) :=
    castmx (tenv_dim disAB, erefl) (@tenv_mxU R L H A B).
  have HQ_t : Q^*t = castmx (erefl, tenv_dim disAB)
                    (@tenv_mxU R L H A B)^*t.
  { rewrite /Q.
    exact: (@castmx_mx_mxT _ _ (@adjmx _) _ _ _ _
      (tenv_dim disAB, erefl)
      (@tenv_mxU R L H A B)). }
  have HQtQ : Q^*t *m Q = 1%:M.
  { rewrite /Q HQ_t mcextra.castmx_mul.
    have HU : (@tenv_mxU R L H A B)^*t
                *m (@tenv_mxU R L H A B) = 1%:M.
    { have := unitarymxK
        (@tenv_mxU_adj_unitarymx R L H A B disAB).
      by rewrite adjmxK. }
    rewrite HU.
    by case: _ / (tenv_dim disAB); rewrite castmx_id. }
  rewrite castmx_comp.
  rewrite (eq_irrelevance
    (etrans (esym (tenv_dim disAB)) (tenv_dim disAB)) (erefl _)).
  by rewrite castmx_id !mulmxA HQtQ mul1mx -mulmxA HQtQ mulmx1.
Qed.

(* biprod_mx_comp *)
(* infra: no tex label -- product-coordinate multiplication *)
(* path: utils:biprod_mx_comp -> bb84:eur_rho_XB_cq -> bb84:bb84_secret *)
Lemma biprod_mx_comp
    (A B : {set L}) (disAB : [disjoint A & B])
    (f g : 'F[H]_(A :|: B)) :
  biprod_mx disAB (f \o g) =
  biprod_mx disAB f *m biprod_mx disAB g.
Proof.
  rewrite /biprod_mx h2mx_comp -(mcextra.castmx_mul (tenv_dim disAB)).
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
  rewrite -[RHS]mulmxA.
  rewrite [Q *m ((Q^*t *m _) *m Q)]mulmxA.
  rewrite [Q *m (Q^*t *m _)]mulmxA HQQt mul1mx.
  by rewrite -!mulmxA.
Qed.

(* biprod_mx_sdot *)
(* infra: no tex label -- labelled tensor product in product coordinates *)
(* path: utils:biprod_mx_sdot -> bb84:eur_rho_XB_cq -> bb84:bb84_secret *)
Lemma biprod_mx_sdot
    (A B : {set L}) (disAB : [disjoint A & B])
    (f : 'F[H]_A) (g : 'F[H]_B) :
  biprod_mx disAB (f \O g) = h2mx f *t h2mx g.
Proof.
  have Hten : (f \O g : 'F[H]_(A :|: B)) = f \⊗ g.
  { by apply: to_Fnd_inj; rewrite (sdotFT _ _ disAB) to_Fnd_tenE. }
  rewrite /biprod_mx Hten h2mx_tenf.
  set Q : 'M[C]_(dim 'H[H]_A * dim 'H[H]_B) :=
    castmx (tenv_dim disAB, erefl) (@tenv_mxU R L H A B).
  have HQ_t : Q^*t = castmx (erefl, tenv_dim disAB)
                    (@tenv_mxU R L H A B)^*t.
  { rewrite /Q.
    exact: (@castmx_mx_mxT _ _ (@adjmx _) _ _ _ _
      (tenv_dim disAB, erefl)
      (@tenv_mxU R L H A B)). }
  have HQtQ : Q^*t *m Q = 1%:M.
  { rewrite /Q HQ_t mcextra.castmx_mul.
    have HU : (@tenv_mxU R L H A B)^*t
                *m (@tenv_mxU R L H A B) = 1%:M.
    { have := unitarymxK
        (@tenv_mxU_adj_unitarymx R L H A B disAB).
      by rewrite adjmxK. }
    rewrite HU.
    by case: _ / (tenv_dim disAB); rewrite castmx_id. }
  have HC : forall (M : 'M[C]_(dim 'H[H]_A * dim 'H[H]_B)),
    castmx (tenv_dim disAB, tenv_dim disAB)
      ((@tenv_mxU R L H A B) *m M *m
       (@tenv_mxU R L H A B)^*t) =
    Q *m M *m Q^*t.
  { move=> M.
    rewrite /Q HQ_t mcextra.castmx_mull.
    by rewrite mcextra.castmx_mul. }
  by rewrite HC !mulmxA HQtQ mul1mx -mulmxA HQtQ mulmx1.
Qed.

(* biprod_mx0_inj *)
(* infra: no tex label -- product-coordinate zero reflection *)
(* path: utils:biprod_mx0_inj -> bb84:eur_rho_XB_cq -> bb84:bb84_secret *)
Lemma biprod_mx0_inj
    (A B : {set L}) (disAB : [disjoint A & B])
    (f : 'F[H]_(A :|: B)) :
  biprod_mx disAB f = 0 -> f = 0.
Proof.
  rewrite /biprod_mx.
  set Q : 'M[C]_(dim 'H[H]_A * dim 'H[H]_B) :=
    castmx (tenv_dim disAB, erefl) (@tenv_mxU R L H A B).
  have HQ_t : Q^*t = castmx (erefl, tenv_dim disAB)
                    (@tenv_mxU R L H A B)^*t.
  { rewrite /Q.
    exact: (@castmx_mx_mxT _ _ (@adjmx _) _ _ _ _
      (tenv_dim disAB, erefl)
      (@tenv_mxU R L H A B)). }
  have HQtQ : Q^*t *m Q = 1%:M.
  { rewrite /Q HQ_t mcextra.castmx_mul.
    have HU : (@tenv_mxU R L H A B)^*t
                *m (@tenv_mxU R L H A B) = 1%:M.
    { have := unitarymxK
        (@tenv_mxU_adj_unitarymx R L H A B disAB).
      by rewrite adjmxK. }
    rewrite HU.
    by case: _ / (tenv_dim disAB); rewrite castmx_id. }
  have HQQt : Q *m Q^*t = 1%:M.
  { rewrite /Q HQ_t mcextra.castmx_mul.
    have HU : (@tenv_mxU R L H A B) *m
                (@tenv_mxU R L H A B)^*t = 1%:M.
    { exact: unitarymxK (@tenv_mxU_unitarymx R L H A B). }
    rewrite HU.
    by case: _ / (tenv_dim disAB); rewrite castmx_id. }
  move=> H0.
  have Hcast0 :
      castmx (tenv_dim disAB, tenv_dim disAB) (h2mx f) = 0.
  { have := f_equal (fun X => Q *m X *m Q^*t) H0.
    rewrite mulmx0 mul0mx.
    move=> Htmp.
    move: Htmp.
    rewrite [Q *m ((Q^*t *m _) *m Q)]mulmxA.
    rewrite [Q *m (Q^*t *m _)]mulmxA HQQt mul1mx.
    by rewrite -!mulmxA HQQt mulmx1. }
  apply/h2mx_inj; rewrite h2mx0.
  move: Hcast0.
  by case: _ / (tenv_dim disAB); rewrite castmx_id => ->.
Qed.

(* biprod_mx_inj *)
(* infra: no tex label -- product-coordinate equality reflection *)
(* path: utils:biprod_mx_inj -> *)
(*   bb84:bb84_secure *)
Lemma biprod_mx_inj
    (A B : {set L}) (disAB : [disjoint A & B])
    (f g : 'F[H]_(A :|: B)) :
  biprod_mx disAB f = biprod_mx disAB g -> f = g.
Proof.
  rewrite /biprod_mx.
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
  move=> Heq.
  have Hcast :
      castmx (tenv_dim disAB, tenv_dim disAB) (h2mx f) =
      castmx (tenv_dim disAB, tenv_dim disAB) (h2mx g).
  { have := f_equal (fun X => Q *m X *m Q^*t) Heq.
    move=> Htmp.
    move: Htmp.
    rewrite ![Q *m ((Q^*t *m _) *m Q)]mulmxA.
    rewrite ![Q *m (Q^*t *m _)]mulmxA HQQt !mul1mx.
    by rewrite -!mulmxA HQQt !mulmx1. }
  apply/h2mx_inj.
  move: Hcast.
  by case: _ / (tenv_dim disAB); rewrite !castmx_id => ->.
Qed.

(* biprod_mxZ *)
(* infra: no tex label -- scalar linearity of product-coordinate matrix form *)
(* path: utils:biprod_mxZ -> utils:biprod_of_mxZ -> *)
(*   (via the bb84 layer) -> *)
(*   bb84:bb84_secure *)
Lemma biprod_mxZ
    (A B : {set L}) (disAB : [disjoint A & B])
    (c : C) (rhoAB : 'F[H]_(A :|: B)) :
  biprod_mx disAB (c *: rhoAB) = c *: biprod_mx disAB rhoAB.
Proof.
  rewrite /biprod_mx.
  set Q : 'M[C]_(dim 'H[H]_A * dim 'H[H]_B) :=
    castmx (tenv_dim disAB, erefl) (@tenv_mxU R L H A B).
  have Hh2 : h2mx (c *: rhoAB) = c *: h2mx rhoAB.
  { have Hlin :=
      @h2mxP R ('H[H]_(A :|: B)) ('H[H]_(A :|: B)).
    have := Hlin c rhoAB 0.
    by rewrite addr0 h2mx0 addr0. }
  have Hcast (M : 'M[C]_(dim 'H[H]_(A :|: B))) :
      castmx (tenv_dim disAB, tenv_dim disAB) (c *: M) =
      c *: castmx (tenv_dim disAB, tenv_dim disAB) M.
  { by case: _ / (tenv_dim disAB); rewrite castmx_id. }
  rewrite Hh2 Hcast.
  by rewrite -scalemxAr -scalemxAl.
Qed.

(* biprod_of_mx_sdot *)
(* infra: no tex label -- product-coordinate matrix to labelled tensor product *)
(* path: utils:biprod_of_mx_sdot -> entropy:smooth_hmax_labelled_mx -> *)
(*   bb84:stat -> bb84:bb84_secret *)
Lemma biprod_of_mx_sdot
    (A B : {set L}) (disAB : [disjoint A & B])
    (f : 'F[H]_A) (g : 'F[H]_B) :
  biprod_of_mx disAB (h2mx f *t h2mx g) = f \O g.
Proof.
  apply: biprod_mx_inj.
  by rewrite biprod_mxK biprod_mx_sdot.
Qed.

(* biprod_of_mxZ *)
(* infra: no tex label -- linearity of product-coordinate decoding *)
(* path: utils:biprod_of_mxZ -> *)
(*   bb84:bb84_secure *)
Lemma biprod_of_mxZ
    (A B : {set L}) (disAB : [disjoint A & B])
    (c : C) (rhoAB : 'M[C]_(dim ('H[H]_A) * dim ('H[H]_B))) :
  biprod_of_mx disAB (c *: rhoAB) = c *: biprod_of_mx disAB rhoAB.
Proof.
  apply: biprod_mx_inj.
  by rewrite biprod_mxK biprod_mxZ biprod_mxK.
Qed.

(* biprod_of_mx_sum *)
(* infra: no tex label -- finite-sum linearity of product-coordinate decoding *)
(* path: utils:biprod_of_mx_sum -> *)
(*   bb84:bb84_secure *)
Lemma biprod_of_mx_sum
    (A B : {set L}) (disAB : [disjoint A & B])
    (I : finType) (P : pred I)
    (rhoAB : I -> 'M[C]_(dim ('H[H]_A) * dim ('H[H]_B))) :
  biprod_of_mx disAB (\sum_(i | P i) rhoAB i) =
  \sum_(i | P i) biprod_of_mx disAB (rhoAB i).
Proof.
  rewrite /biprod_of_mx.
  rewrite mulmx_sumr mulmx_suml.
  rewrite !linear_sum /=.
  by apply: eq_bigr => i _.
Qed.

(* h2mx_deltav_outp *)
(* infra: no tex label -- labelled computational outer products in coordinates *)
(* path: utils:h2mx_deltav_outp -> *)
(*   bb84:bb84_secure *)
Lemma h2mx_deltav_outp
    (A B : {set L}) (i : 'Idx[H]_A) (j : 'Idx[H]_B) :
  h2mx [> deltav i ; deltav j <] =
  delta_mx (@i2n R L H A i) (@i2n R L H B j).
Proof.
  by rewrite !deltav.unlock h2mx_eb.
Qed.

End BipartiteMatrixDefinitions.

End FvqkdReal.
