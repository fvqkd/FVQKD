(* -------------------------------------------------------------------- *)
(* prop.v — EUR proof infrastructure for smooth entropic uncertainty    *)
(* -------------------------------------------------------------------- *)
(* Module: eur.prop                                       *)
(* Paper: Tomamichel & Renner, 'The Uncertainty Relation for Smooth     *)
(*   Entropies' (PRL 106, 110506 (2011); arXiv:1009.2015).             *)
(* tex labels: thm:mother proof steps, eqn:dual, eqn:mo9               *)
(*                                                                       *)
(* Formalises the statement and proof structure of Theorem 1            *)
(* (tex thm:mother):                                                    *)
(*   H^ε_min(X|B)_ρ + H^ε_max(Z|C)_ρ ≥ q                                *)
(*                                                                       *)
(* Proof strategy (paper's "Proof of the Main Result"):                 *)
(*   Stage 0: pure ρ_{ABC}, ε = 0  (pure ε=0 case, Eqs. (6)-(11))         *)
(*   Stage 1: pure ρ_{ABC}, ε ≥ 0  (ε-smooth generalization, Uhlmann)     *)
(*   Stage 2: mixed ρ_{ABC}, ε ≥ 0 (mixed: purification + DPI)            *)
(*                                                                       *)
(* The default ambient set-labelled theorem                             *)
(* `entropic_uncertainty_relation` lives in `eur/eur.v`.                *)
(*                                                                       *)
(* A single matrix-level operator-inequality helper (eqn:mo9) is        *)
(* retained from the paper's proof because it is entirely about        *)
(* matrices (no lifted registers) and is used to characterise the       *)
(* overlap definition.                                                   *)
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
From Stdlib Require Import Lia.
Require Import mathcomp.algebra.archimedean.
From quantum Require Import mcextra mcaextra notation hermitian quantum
  cpo mxpred extnum ctopology svd mxnorm hspace inhabited.
From quantum.dirac Require Import hstensor.
Import Order.TTheory GRing.Theory Num.Theory Num.Def MxLownerOrder.
Import VectorInternalTheory.
(* --- FVQKD imports --- *)
From utils Require Import exports.
From entropy Require Import def prop util.
From entropy.conv Require Import minmax_dual.
From entropy.smooth Require Import sm dpi class prop.
From eur Require Import def.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Local Open Scope lfun_scope.
Section FvqkdReal.
Variable R : realType.
Notation C := (@hermitian.C R).
Notation chsType := (@chsType R).
Local Notation "''Hs' T" := (@ihb_chsType R T%type)
  (at level 8, T at level 2, format "''Hs'  T").
(* ================================================================== *)
(* Definition-level facts moved out of eur/def.v                       *)
(* ================================================================== *)
Section Povm.
Variable (na nx : nat).
(* path: eur:is_povm_mxP -> eur:is_povm_mx_psd -> eur:rho_XB_subden -> *)
(*   eur:eur_rho_XB_psd -> bb84:bb84_secret *)
Lemma is_povm_mxP (M : 'I_nx -> 'M[C]_na) :
  reflect ((forall x, M x \is psdmx) /\ \sum_(x < nx) M x = 1%:M)
          (is_povm_mx M).
Proof.
  rewrite /is_povm_mx; apply: (iffP andP).
  - by case=> /forallP Hpsd /eqP Hsum.
  - by case=> Hpsd /eqP Hsum; split; [apply/forallP|].
Qed.
(* path: eur:is_povm_mx_psd -> eur:rho_XB_subden -> eur:eur_rho_XB_psd -> *)
(*   bb84:bb84_secret *)
Lemma is_povm_mx_psd (M : 'I_nx -> 'M[C]_na) (x : 'I_nx) :
  is_povm_mx M -> M x \is psdmx.
Proof.
  by case/is_povm_mxP=> H _; apply: H.
Qed.
(* path: eur:is_povm_mx_sum -> eur:rho_XB_subden -> eur:eur_rho_XB_psd -> *)
(*   bb84:bb84_secret *)
Lemma is_povm_mx_sum (M : 'I_nx -> 'M[C]_na) :
  is_povm_mx M -> \sum_(x < nx) M x = 1%:M.
Proof.
  by case/is_povm_mxP.
Qed.
End Povm.
(* path: eur:std_projective_povm_is_povm -> eur:is_povm_mx_psd -> *)
(*   eur:rho_XB_subden -> eur:eur_rho_XB_psd -> bb84:bb84_secret *)
Lemma std_projective_povm_is_povm (n : nat) :
  @is_povm_mx R n n (@std_projective_povm R n).
Proof.
  apply/is_povm_mxP; split.
  - by move=> i; exact: delta_mx_ii_psdmx.
  - by rewrite /std_projective_povm mx1_sum_delta.
Qed.
(* path: eur:unitary_projective_povm_is_povm -> *)
(*   eur:entropic_uncertainty_relation -> *)
(*   eur:entropic_uncertainty_relation -> *)
(*   bb84:entropic_uncertainty_relation_bb84 -> bb84:bb84_secret *)
Lemma unitary_projective_povm_is_povm (n : nat) (U : 'M[C]_n) :
  U \is unitarymx ->
  is_povm_mx (fun x : 'I_n => U^*t *m delta_mx x x *m U).
Proof.
  move=> HU.
  apply/is_povm_mxP; split.
  - move=> x.
    have Hpsd := @psdmx_bimap_closed_gen C _ (delta_mx x x) _ U^*t
      (@delta_mx_ii_psdmx R n x).
    by move: Hpsd; rewrite adjmxK.
  - rewrite -mulmx_suml -mulmx_sumr -mx1_sum_delta.
    by rewrite mulmx1 unitarymxKV.
Qed.
(* path: eur:sqrt2_inv_div -> eur:entropic_uncertainty_relation -> *)
(*   eur:entropic_uncertainty_relation -> *)
(*   bb84:entropic_uncertainty_relation_bb84 -> bb84:bb84_secret *)
Local Lemma sqrt2_inv_div :
  (((Num.sqrt (2%:R))^-1)%R / Num.sqrt (2%:R) =
   ((2%:R)^-1)%R :> R).
Proof.
  by rewrite -invrM ?unitf_gt0 ?sqrtr_gt0 ?ltr0n // -expr2
    sqr_sqrtr ?ler0n.
Qed.
(* path: eur:hadamard_mx2_unitary -> eur:entropic_uncertainty_relation -> *)
(*   eur:entropic_uncertainty_relation -> *)
(*   bb84:entropic_uncertainty_relation_bb84 -> bb84:bb84_secret *)
Lemma hadamard_mx2_unitary :
  (@hadamard_mx2 R) \is unitarymx.
Proof.
  apply/unitarymxP/matrixP=> i j.
  case: i => [[|[|i]] Hi]; try by [].
  - case: j => [[|[|j]] Hj]; try by [].
    + rewrite !mxE /hadamard_mx2 /xbasis_sign2 ?big_ord_recl ?big_ord0 /=.
      rewrite !mxE /= ?eqxx ?conjC1 ?conjCN1.
      simpc.
      by rewrite !sqrt2_inv_div split21.
    + rewrite !mxE /hadamard_mx2 /xbasis_sign2 ?big_ord_recl ?big_ord0 /=.
      rewrite !mxE /= ?eqxx ?conjC1 ?conjCN1.
      simpc.
      by rewrite complexr0.
  - case: j => [[|[|j]] Hj]; try by [].
    + rewrite !mxE /hadamard_mx2 /xbasis_sign2 ?big_ord_recl ?big_ord0 /=.
      rewrite !mxE /= ?eqxx ?conjC1 ?conjCN1.
      simpc.
      by rewrite complexr0.
    + rewrite !mxE /hadamard_mx2 /xbasis_sign2 ?big_ord_recl ?big_ord0 /=.
      rewrite !mxE /= ?eqxx ?conjC1 ?conjCN1.
      simpc.
      by rewrite !sqrt2_inv_div split21.
Qed.
(* path: eur:hadamard_mx_unitary -> eur:entropic_uncertainty_relation -> *)
(*   eur:entropic_uncertainty_relation -> *)
(*   bb84:entropic_uncertainty_relation_bb84 -> bb84:bb84_secret *)
Lemma hadamard_mx_unitary (n : nat) :
  (@hadamard_mx R n) \is unitarymx.
Proof. exact: bigten_unitary hadamard_mx2_unitary. Qed.
(* path: eur:x_projective_povm_is_povm -> *)
(*   eur:entropic_uncertainty_relation -> *)
(*   eur:entropic_uncertainty_relation -> *)
(*   bb84:entropic_uncertainty_relation_bb84 -> bb84:bb84_secret *)
Lemma x_projective_povm_is_povm (n : nat) :
  is_povm_mx (@x_projective_povm R n).
Proof.
  exact: (@unitary_projective_povm_is_povm (2 ^ n)
    (@hadamard_mx R n) (hadamard_mx_unitary n)).
Qed.
Local Ltac solve_x_projective_povm2_hadamard :=
  rewrite !mxE /x_projective_povm2 /xbasis_vec2 /hadamard_mx2
    /xbasis_sign2 ?big_ord_recl ?big_ord0 /=;
  rewrite !mxE ?big_ord_recl ?big_ord0 !mxE /= ?eqxx
    ?conjC1 ?conjCN1;
  simpc;
  by rewrite sqrt2_inv_div.
(* path: eur:x_projective_povm2_hadamard -> *)
(*   eur:entropic_uncertainty_relation -> *)
(*   eur:entropic_uncertainty_relation -> *)
(*   bb84:entropic_uncertainty_relation_bb84 -> bb84:bb84_secret *)
Lemma x_projective_povm2_hadamard (x : 'I_2) :
  @x_projective_povm2 R x =
  (@hadamard_mx2 R)^*t *m delta_mx x x *m (@hadamard_mx2 R).
Proof.
  apply/matrixP=> i j.
  case: x => [[|[|x]] Hx]; try by [].
  - case: i => [[|[|i]] Hi]; try by [].
    + case: j => [[|[|j]] Hj]; try by [].
      * abstract solve_x_projective_povm2_hadamard.
      * abstract solve_x_projective_povm2_hadamard.
    + case: j => [[|[|j]] Hj]; try by [].
      * abstract solve_x_projective_povm2_hadamard.
      * abstract solve_x_projective_povm2_hadamard.
  - case: i => [[|[|i]] Hi]; try by [].
    + case: j => [[|[|j]] Hj]; try by [].
      * abstract solve_x_projective_povm2_hadamard.
      * abstract solve_x_projective_povm2_hadamard.
    + case: j => [[|[|j]] Hj]; try by [].
      * abstract solve_x_projective_povm2_hadamard.
      * abstract solve_x_projective_povm2_hadamard.
Qed.
(* path: eur:x_projective_povm2_psd -> eur:entropic_uncertainty_relation -> *)
(*   eur:entropic_uncertainty_relation -> *)
(*   bb84:entropic_uncertainty_relation_bb84 -> bb84:bb84_secret *)
Lemma x_projective_povm2_psd (x : 'I_2) :
  @x_projective_povm2 R x \is psdmx.
Proof.
  rewrite /x_projective_povm2.
  apply: psdmxZ; last exact: form_psd.
  by rewrite lecR invr_ge0 ler0n.
Qed.
(* path: eur:inv2R_add -> eur:entropic_uncertainty_relation -> *)
(*   eur:entropic_uncertainty_relation -> *)
(*   bb84:entropic_uncertainty_relation_bb84 -> bb84:bb84_secret *)
Local Lemma inv2R_add : (2%:R)^-1 + (2%:R)^-1 = 1 :> R.
Proof.
  have H2 : (2%:R : R) != 0 by rewrite pnatr_eq0.
  apply: (mulIf H2).
  by rewrite mulrDl !mulVf // mul1r -mulr2n.
Qed.
(* path: eur:x_projective_povm2_sum -> eur:entropic_uncertainty_relation -> *)
(*   eur:entropic_uncertainty_relation -> *)
(*   bb84:entropic_uncertainty_relation_bb84 -> bb84:bb84_secret *)
Lemma x_projective_povm2_sum :
  \sum_(x < 2) @x_projective_povm2 R x = 1%:M.
Proof.
  apply/matrixP=> i j.
  case: i => [[|[|i]] Hi]; try by [].
  - case: j => [[|[|j]] Hj]; try by [].
    + rewrite !mxE /x_projective_povm2 /xbasis_vec2 /xbasis_sign2
        ?big_ord_recl ?big_ord0 /=.
      rewrite !mxE ?big_ord_recl ?big_ord0 !mxE /= ?eqxx ?conjC1 ?conjCN1.
      simpc.
      by rewrite complexr0 inv2R_add.
    + rewrite !mxE /x_projective_povm2 /xbasis_vec2 /xbasis_sign2
        ?big_ord_recl ?big_ord0 /=.
      rewrite !mxE ?big_ord_recl ?big_ord0 !mxE /= ?eqxx ?conjC1 ?conjCN1.
      simpc.
      by [].
  - case: j => [[|[|j]] Hj]; try by [].
    + rewrite !mxE /x_projective_povm2 /xbasis_vec2 /xbasis_sign2
        ?big_ord_recl ?big_ord0 /=.
      rewrite !mxE ?big_ord_recl ?big_ord0 !mxE /= ?eqxx ?conjC1 ?conjCN1.
      simpc.
      by [].
    + rewrite !mxE /x_projective_povm2 /xbasis_vec2 /xbasis_sign2
        ?big_ord_recl ?big_ord0 /=.
      rewrite !mxE ?big_ord_recl ?big_ord0 !mxE /= ?eqxx ?conjC1 ?conjCN1.
      simpc.
      by rewrite complexr0 inv2R_add.
Qed.
(* path: eur:x_projective_povm2_is_povm -> *)
(*   eur:entropic_uncertainty_relation -> *)
(*   eur:entropic_uncertainty_relation -> *)
(*   bb84:entropic_uncertainty_relation_bb84 -> bb84:bb84_secret *)
Lemma x_projective_povm2_is_povm :
  @is_povm_mx R 2 2 (@x_projective_povm2 R).
Proof.
  apply/is_povm_mxP; split.
  - exact: x_projective_povm2_psd.
  - exact: x_projective_povm2_sum.
Qed.
(* path: eur:x_projective_povm2_idem -> *)
(*   eur:entropic_uncertainty_relation -> *)
(*   eur:entropic_uncertainty_relation -> *)
(*   bb84:entropic_uncertainty_relation_bb84 -> bb84:bb84_secret *)
Lemma x_projective_povm2_idem (x : 'I_2) :
  @x_projective_povm2 R x *m @x_projective_povm2 R x =
  @x_projective_povm2 R x.
Proof.
  apply/matrixP=> i j.
  case: x => [[|[|x]] Hx]; try by [].
  - case: i => [[|[|i]] Hi]; try by [].
    + case: j => [[|[|j]] Hj]; try by [].
      * rewrite !mxE /x_projective_povm2 /xbasis_vec2 /xbasis_sign2
          ?big_ord_recl ?big_ord0 /=.
        rewrite !mxE ?big_ord_recl ?big_ord0 !mxE /= ?eqxx
          ?conjC1 ?conjCN1.
        simpc.
        by rewrite -mulrDr inv2R_add mulr1.
      * rewrite !mxE /x_projective_povm2 /xbasis_vec2 /xbasis_sign2
          ?big_ord_recl ?big_ord0 /=.
        rewrite !mxE ?big_ord_recl ?big_ord0 !mxE /= ?eqxx
          ?conjC1 ?conjCN1.
        simpc.
        by rewrite -mulrDr inv2R_add mulr1.
    + case: j => [[|[|j]] Hj]; try by [].
      * rewrite !mxE /x_projective_povm2 /xbasis_vec2 /xbasis_sign2
          ?big_ord_recl ?big_ord0 /=.
        rewrite !mxE ?big_ord_recl ?big_ord0 !mxE /= ?eqxx
          ?conjC1 ?conjCN1.
        simpc.
        by rewrite -mulrDr inv2R_add mulr1.
      * rewrite !mxE /x_projective_povm2 /xbasis_vec2 /xbasis_sign2
          ?big_ord_recl ?big_ord0 /=.
        rewrite !mxE ?big_ord_recl ?big_ord0 !mxE /= ?eqxx
          ?conjC1 ?conjCN1.
        simpc.
        by rewrite -mulrDr inv2R_add mulr1.
  - case: i => [[|[|i]] Hi]; try by [].
    + case: j => [[|[|j]] Hj]; try by [].
      * rewrite !mxE /x_projective_povm2 /xbasis_vec2 /xbasis_sign2
          ?big_ord_recl ?big_ord0 /=.
        rewrite !mxE ?big_ord_recl ?big_ord0 !mxE /= ?eqxx
          ?conjC1 ?conjCN1.
        simpc.
        by rewrite -mulrDr inv2R_add mulr1.
      * rewrite !mxE /x_projective_povm2 /xbasis_vec2 /xbasis_sign2
          ?big_ord_recl ?big_ord0 /=.
        rewrite !mxE ?big_ord_recl ?big_ord0 !mxE /= ?eqxx
          ?conjC1 ?conjCN1.
        simpc.
        by rewrite -opprD -mulrDr inv2R_add mulr1.
    + case: j => [[|[|j]] Hj]; try by [].
      * rewrite !mxE /x_projective_povm2 /xbasis_vec2 /xbasis_sign2
          ?big_ord_recl ?big_ord0 /=.
        rewrite !mxE ?big_ord_recl ?big_ord0 !mxE /= ?eqxx
          ?conjC1 ?conjCN1.
        simpc.
        by rewrite -opprD -mulrDr inv2R_add mulr1.
      * rewrite !mxE /x_projective_povm2 /xbasis_vec2 /xbasis_sign2
          ?big_ord_recl ?big_ord0 /=.
        rewrite !mxE ?big_ord_recl ?big_ord0 !mxE /= ?eqxx
          ?conjC1 ?conjCN1.
        simpc.
        by rewrite -mulrDr inv2R_add mulr1.
Qed.
(* path: eur:sqrtmx_x_projective_povm2 -> *)
(*   eur:entropic_uncertainty_relation -> *)
(*   eur:entropic_uncertainty_relation -> *)
(*   bb84:entropic_uncertainty_relation_bb84 -> bb84:bb84_secret *)
Lemma sqrtmx_x_projective_povm2 (x : 'I_2) :
  sqrtmx (@x_projective_povm2 R x) = @x_projective_povm2 R x.
Proof.
  have Hsq := x_projective_povm2_idem x.
  by rewrite -Hsq sqrtmx_psd_square ?x_projective_povm2_psd.
Qed.
(* ================================================================== *)
(* Tensor factorization of the aggregate X-basis projective POVM       *)
(*                                                                       *)
(* The n-qubit X-basis POVM element x_projective_povm n x is the         *)
(* n-fold tensor of single-qubit projectors x_projective_povm2 over the *)
(* bit-decomposition of x.  This is established in the recursive          *)
(* (bigten-shaped) form that mirrors hadamard_mx's bigten/tuple_tensmx   *)
(* recursion: each extra qubit splits the index via mxtens_unindex into  *)
(* a head x0 : 'I_(2^n) and a tail bit x1 : 'I_2, and the POVM element    *)
(* factors as the tensor of the size-n element on x0 and the single-qubit *)
(* element on x1, up to the expnSr reshape (x_projective_povm_tens_rec).  *)
(* The sqrt form (sqrtmx_x_projective_povm_tens_rec) follows because the  *)
(* aggregate element and each per-qubit element are projectors, hence     *)
(* each is its own square root (sqrtmx_x_projective_povm,                 *)
(* sqrtmx_x_projective_povm2).                                            *)
(* ================================================================== *)
(* Recursive (bigten-shaped) tensor step for the X-basis POVM.          *)
(* path: eur:x_projective_povm_tens_rec ->                              *)
(*   eur:entropic_uncertainty_relation ->                                *)
(*   bb84:bb84_secret *)
Lemma x_projective_povm_tens_rec (n : nat) (x : 'I_(2 ^ n.+1)) :
  let: (x0, x1) := mxtens_unindex (cast_ord (expnSr 2 n) x) in
  @x_projective_povm R n.+1 x =
  castmx_sq (esym (expnSr 2 n))
    ((@x_projective_povm R n x0) *t (@x_projective_povm2 R x1)).
Proof.
  case Hx: (mxtens_unindex (cast_ord (expnSr 2 n) x)) => [x0 x1].
  have Hxe : cast_ord (expnSr 2 n) x = mxtens_index (x0, x1).
    by rewrite -Hx mxtens_unindexK.
  (* keep x_projective_povm2 folded; fold the single-qubit factor at the end *)
  rewrite [in RHS]x_projective_povm2_hadamard.
  rewrite /x_projective_povm /hadamard_mx /castmx_sq /=.
  set e := expnSr 2 n.
  set H := bigten (@hadamard_mx2 R) n.
  (* the adjoint of the cast'd Hadamard factor *)
  rewrite -(adjmx_castV (esym e, esym e)) /= tensmx_adj.
  (* reshape delta_mx x x : 'M_(2^n.+1) as castmx (esym e) of a tensor *)
  have Hdelta :
      (delta_mx x x : 'M[C]_(2 ^ n.+1)) =
      castmx (esym e, esym e)
        ((delta_mx x0 x0 : 'M[C]_(2 ^ n)) *t (delta_mx x1 x1 : 'M[C]_2)).
  {
    apply: castmx_sym.
    rewrite delta_mx_cast /= delta_mx_tens.
    by rewrite -Hxe.
  }
  rewrite Hdelta.
  (* all three factors now share the castmx (esym e) wrapper; combine *)
  rewrite mcextra.castmx_mul mcextra.castmx_mul tensmx_mul tensmx_mul.
  by [].
Qed.
(* The aggregate n-qubit X-basis POVM element is its own square root:    *)
(* it is the unitary conjugate of an idempotent rank-1 projector, hence  *)
(* a projector itself.  (Generalises sqrtmx_x_projective_povm2 to n.)     *)
(* path: eur:sqrtmx_x_projective_povm ->                                 *)
(*   eur:entropic_uncertainty_relation -> bb84:bb84_secret *)
Lemma sqrtmx_x_projective_povm (n : nat) (x : 'I_(2 ^ n)) :
  sqrtmx (@x_projective_povm R n x) = @x_projective_povm R n x.
Proof.
  rewrite /x_projective_povm.
  exact: sqrtmx_unitary_delta_projector (hadamard_mx_unitary n).
Qed.
(* sqrt form of the tensor factorization: the square root of the         *)
(* aggregate POVM is the tensor of the per-qubit square roots.  Both      *)
(* the aggregate element and each single-qubit element are projectors,    *)
(* so each equals its own square root and the tensor identity transfers   *)
(* through sqrtmx unchanged.                                              *)
(* path: eur:sqrtmx_x_projective_povm_tens_rec ->                        *)
(*   eur:entropic_uncertainty_relation -> bb84:bb84_secret *)
Lemma sqrtmx_x_projective_povm_tens_rec (n : nat) (x : 'I_(2 ^ n.+1)) :
  let: (x0, x1) := mxtens_unindex (cast_ord (expnSr 2 n) x) in
  sqrtmx (@x_projective_povm R n.+1 x) =
  castmx_sq (esym (expnSr 2 n))
    (sqrtmx (@x_projective_povm R n x0) *t sqrtmx (@x_projective_povm2 R x1)).
Proof.
  (* Force the RHS let-binding to compute: mxtens_unindex reduces to the *)
  (* literal div/mod index pair, the very form x_projective_povm_tens_rec *)
  (* exposes, so the recursion and the per-qubit self-sqrt facts line up. *)
  rewrite (surjective_pairing (mxtens_unindex (cast_ord (expnSr 2 n) x))).
  rewrite [sqrtmx (@x_projective_povm R n.+1 x)]sqrtmx_x_projective_povm.
  rewrite (x_projective_povm_tens_rec x).
  by rewrite !(sqrtmx_x_projective_povm, sqrtmx_x_projective_povm2).
Qed.
(* path: eur:cast_square_povm_mx_is_povm -> *)
(*   eur:entropic_uncertainty_relation -> *)
(*   eur:entropic_uncertainty_relation -> *)
(*   bb84:entropic_uncertainty_relation_bb84 -> bb84:bb84_secret *)
Lemma cast_square_povm_mx_is_povm {n m : nat} (e : n = m)
    (M : 'I_m -> 'M[C]_m) :
  is_povm_mx M -> is_povm_mx (cast_square_povm_mx e M).
Proof.
  case: m / e M => M HM.
  apply/is_povm_mxP; split.
  - move=> x.
    rewrite /cast_square_povm_mx cast_ord_id /castmx_sq castmx_id.
    exact: is_povm_mx_psd HM.
  - rewrite /cast_square_povm_mx.
    under eq_bigr do rewrite cast_ord_id /castmx_sq castmx_id.
    exact: is_povm_mx_sum HM.
Qed.
(* Matrix SDP feasible-trace set used by the min-entropy transport steps. *)
(* This caches the nontrivial infimum infrastructure shared by Stage 0 and *)
(* Stage 1; it is not a theorem-wrapper around either EUR theorem.         *)
(* path: eur:eur_matrix_phi_has_inf -> eur:ucr_pure_zero, eur:ucr_pure_smooth *)
Lemma eur_matrix_phi_has_inf nA nB (rho0 : 'M[C]_(nA * nB)) :
  rho0 \is psdmx ->
  has_inf [set v : R | exists sigma : 'M[C]_nB,
    sigma \is psdmx /\
    ((1%:M : 'M[C]_nA) *t sigma - rho0) \is psdmx /\
    v = @complex.Re R (\tr sigma)]%classic.
Proof.
  move=> Hrho0.
  split.
  - pose sigma0 : 'M[C]_nB :=
      (@complex.Re R (\tr rho0))%:C *: (1%:M : 'M[C]_nB).
    exists (@complex.Re R (\tr sigma0)).
    exists sigma0; split; last split.
    + rewrite /sigma0.
      apply: psdmxZ; last exact: psdmx1.
      have Htr_ge0 : (0 : C) <= \tr rho0 := psdmx_trace Hrho0.
      have Htr_ge0R : 0 <= @complex.Re R (\tr rho0).
      { by move: Htr_ge0; rewrite lecE /= => /andP[_]. }
      by rewrite lecR.
    + have Hrho_le_trI : rho0 <= (\tr rho0)%:M := lemx_psd_ub Hrho0.
      have Htarget :
          (1%:M : 'M[C]_nA) *t sigma0 = (\tr rho0)%:M.
      {
        have Htr_ge0 : (0 : C) <= \tr rho0 := psdmx_trace Hrho0.
        have Htr_real : \tr rho0 \is Num.real := ger0_real Htr_ge0.
        have Hreal : \tr rho0 = (@complex.Re R (\tr rho0))%:C
          by rewrite RRe_real.
        apply/matrixP=> i j.
        case: (mxtens_indexP i)=> ia ib.
        case: (mxtens_indexP j)=> ja jb.
        rewrite /sigma0 tensmxE !mxE Hreal.
        rewrite (inj_eq (can_inj (@mxtens_indexK _ _))) -pair_eqE /=.
        by case: (ia == ja); case: (ib == jb);
          rewrite ?andbT ?andbF ?mul0r ?mulr0 ?mul1r ?mulr1.
      }
      by move: Hrho_le_trI; rewrite -Htarget le_lownerE.
    + by [].
  - exists 0 => v [sigma [Hsigma [_ ->]]].
    by have := psdmx_trace Hsigma; rewrite lecE /= => /andP[_].
Qed.
(* Lower bound on the same feasible-trace infimum.                         *)
(* path: eur:eur_matrix_phi_trace_lb -> eur:ucr_pure_zero, eur:ucr_pure_smooth *)
Lemma eur_matrix_phi_trace_lb nA nB (rho0 : 'M[C]_(nA * nB)) :
  (0 < nA)%N -> rho0 \is psdmx ->
  0 < @complex.Re R (\tr rho0) ->
  @complex.Re R (\tr rho0) / nA%:R <=
  inf [set v : R | exists sigma : 'M[C]_nB,
    sigma \is psdmx /\
    ((1%:M : 'M[C]_nA) *t sigma - rho0) \is psdmx /\
    v = @complex.Re R (\tr sigma)]%classic.
Proof.
  move=> HnA_pos Hrho0 Hrho0_tr_pos.
  have HRe_realM : forall (cc : R) (zz : C),
      @complex.Re R (cc%:C * zz) = cc * @complex.Re R zz.
  { move=> cc zz; case: zz => a b /=. by rewrite mul0r subr0. }
  apply: lb_le_inf.
  - have Hhas0 := eur_matrix_phi_has_inf Hrho0.
    exact: Hhas0.1.
  - move=> v [sigma [Hsigma [Hsigma_feas ->]]].
    have Hle_rho : rho0 <= (1%:M : 'M[C]_nA) *t sigma
      by move: Hsigma_feas; rewrite -le_lownerE.
    have Htr_leC := lemx_trace Hle_rho.
    have HnA_real : (nA%:R : C) = ((nA%:R : R)%:C : C)
      by rewrite -(@rmorph_nat _ _
          ((real_complex R) : {rmorphism _ -> _})).
    have HRe_tens :
        @complex.Re R (\tr ((1%:M : 'M[C]_nA) *t sigma)) =
        nA%:R * @complex.Re R (\tr sigma).
    { by rewrite mxtrace_tens mxtrace1 HnA_real HRe_realM. }
    have Htr_leR :
        @complex.Re R (\tr rho0) <=
        nA%:R * @complex.Re R (\tr sigma).
    {
      move: Htr_leC; rewrite lecE /= => /andP[_ Hre].
      by rewrite HRe_tens in Hre.
    }
    rewrite ler_pdivrMr; last by rewrite ltr0n.
    by rewrite mulrC.
Qed.
(* ================================================================== *)
(* Stage-0 proof infrastructure                                       *)
(* ================================================================== *)
Section Stage0Infra.
Variable (na nx nz : nat).
(* Paper: Tomamichel & Renner (PRL 106, 110506 (2011); arXiv:1009.2015),*)
(*   "Proof of the Main Result" (isometry property of U).               *)
(* math: U† U = Σ_x M_x = I  when  Σ_x M_x = I                         *)
(* path: eur:stinespring_U_iso -> eur:entropic_uncertainty_relation -> *)
(*   eur:entropic_uncertainty_relation -> *)
(*   bb84:entropic_uncertainty_relation_bb84 -> bb84:bb84_secret *)
Lemma stinespring_U_iso (M : 'I_nx -> 'M[C]_na) :
  (forall x, M x \is psdmx) ->
  \sum_x M x = 1%:M ->
  (stinespring_U M)^*t *m stinespring_U M = 1%:M.
Proof.
  move=> psdM sumM.
  apply/matrixP => j j'.
  rewrite mxE -sumM summxE.
  rewrite (reindex_mxtens_index (fun i =>
    ((stinespring_U M)^*t) j i * (stinespring_U M) i j')).
  rewrite pair_bigV/= exchange_big/=.
  apply: eq_bigr => x _.
  transitivity ((sqrtmx (M x) *m sqrtmx (M x)) j j'); last by rewrite sqrtmxK// psdM.
  have /hermmxP Hh : sqrtmx (M x) \is hermmx by apply/sqrtmx_herm/psdmx_herm/psdM.
  rewrite {1}Hh mxE; apply: eq_bigr => a _.
  by rewrite /stinespring_U !mxE !mxtens_indexK/=.
Qed.
(* Paper: Tomamichel & Renner (PRL 106, 110506 (2011); arXiv:1009.2015),*)
(*   "Proof of the Main Result" (double-copy Stinespring isometry).     *)
(* math: (U2)† U2 = I  when {M_x} is a POVM.                            *)
(* path: eur:stinespring_U2_iso -> eur:ucr_pure_smooth -> *)
(*   eur:entropic_uncertainty_relation -> *)
(*   eur:entropic_uncertainty_relation -> *)
(*   bb84:entropic_uncertainty_relation_bb84 -> bb84:bb84_secret *)
Lemma stinespring_U2_iso (M : 'I_nx -> 'M[C]_na) :
  (forall x, M x \is psdmx) ->
  \sum_x M x = 1%:M ->
  (stinespring_U2 M)^*t *m stinespring_U2 M = 1%:M.
Proof.
  move=> psdM sumM.
  apply/matrixP => j j'.
  rewrite mxE -sumM summxE.
  rewrite (reindex_mxtens_index (fun i =>
    ((stinespring_U2 M)^*t) j i * (stinespring_U2 M) i j')).
  rewrite pair_bigV/=.
  transitivity
    (\sum_(x < nx) \sum_(xp < nx) \sum_(a < na)
      ((x == xp)%:R * sqrtmx (M x) a j)^* *
      ((x == xp)%:R * sqrtmx (M x) a j')).
  {
    rewrite (reindex_mxtens_index
      (fun xx : 'I_(nx * nx) =>
        \sum_(a < na)
          ((stinespring_U2 M)^*t) j (mxtens_index (xx, a)) *
          (stinespring_U2 M) (mxtens_index (xx, a)) j')).
    rewrite pair_bigV/=.
    apply: eq_bigr => x _.
    apply: eq_bigr => xp _.
    apply: eq_bigr => a _.
    by rewrite /stinespring_U2 !mxE !mxtens_indexK/=.
  }
  transitivity
    (\sum_(x < nx) \sum_(a < na)
      (sqrtmx (M x) a j)^* * sqrtmx (M x) a j').
  {
    apply: eq_bigr => x _.
    rewrite (bigD1 x)//= eqxx /=.
    rewrite [X in _ + X]big1 ?addr0.
    - by apply: eq_bigr => a _; rewrite !mul1r.
    - move=> xp Hxp.
      rewrite eq_sym (negPf Hxp).
      by rewrite big1 // => a _; rewrite !mul0r !mulr0.
  }
  apply: eq_bigr => x _.
  transitivity ((sqrtmx (M x) *m sqrtmx (M x)) j j').
  {
    have /hermmxP Hh : sqrtmx (M x) \is hermmx
      by apply/sqrtmx_herm/psdmx_herm/psdM.
    rewrite mxE.
    apply: eq_bigr => a _.
    have Hentry : (sqrtmx (M x) a j)^* = sqrtmx (M x) j a.
    {
      move/matrixP: Hh => HhE.
      move: (HhE j a).
      by rewrite adjmxE !mxE => <-.
    }
    by rewrite Hentry.
  }
  by rewrite sqrtmxK// psdM.
Qed.
(* Paper: Tomamichel & Renner (PRL 106, 110506 (2011); arXiv:1009.2015),*)
(*   "Proof of the Main Result", Eq. (11) and the supporting operator   *)
(*   bound √N_z M_x √N_z = |√N_z √M_x|² ≤ c·𝟙_A — tex eqn:mo9.          *)
(* math: √N_z M_x √N_z ≤ c · I where c := overlap_mx M N               *)
(* path: eur:sqrtmx_prod_overlap_bound -> eur:ucr_pure_smooth -> *)
(*   eur:entropic_uncertainty_relation -> *)
(*   eur:entropic_uncertainty_relation -> *)
(*   bb84:entropic_uncertainty_relation_bb84 -> bb84:bb84_secret *)
Lemma sqrtmx_prod_overlap_bound
    (M : 'I_nx -> 'M[C]_na) (N : 'I_nz -> 'M[C]_na)
    (x : 'I_nx) (z : 'I_nz) :
  is_povm_mx M -> is_povm_mx N ->
  sqrtmx (N z) *m M x *m sqrtmx (N z) <=
  (overlap_mx M N)%:C *: (1%:M : 'M[C]_na).
Proof.
  move=> HM HN.
  have HpM : forall i, M i \is psdmx by move=> i; exact: is_povm_mx_psd HM.
  have HpN : forall j, N j \is psdmx by move=> j; exact: is_povm_mx_psd HN.
  have Hop := sqrtmx_prod_op_bound x z HpM HpN.
  apply: le_trans Hop _.
  have Hscalar_le :
    (@complex.Re R (i2norm (sqrtmx (M x) *m sqrtmx (N z))) ^+ 2)%:C
    <= (overlap_mx M N)%:C :> C.
  { rewrite lecR /overlap_mx.
    apply: le_trans (_ : _ <= \big[maxr/0]_(z' < nz)
        (@complex.Re R (i2norm (sqrtmx (M x) *m sqrtmx (N z')))) ^ 2) _.
    - by apply: le_bigmax_cond.
    - by apply: le_bigmax_cond. }
  apply: lev_pscale2=> //.
  - rewrite lec0R; apply: exprn_ge0.
    have Hge := i2norm_ge0 (sqrtmx (M x) *m sqrtmx (N z)).
    have Hreal : i2norm (sqrtmx (M x) *m sqrtmx (N z)) \is Num.real
      := ger0_real Hge.
    by rewrite -(RRe_real Hreal) lec0R in Hge.
  - by rewrite le_lownerE subr0; exact: psdmx1.
Qed.
(* Paper: Tomamichel & Renner (PRL 106, 110506 (2011); arXiv:1009.2015),  *)
(*   Eq. (2) — tex eqn:overlap (implicit well-formedness fact).           *)
(* math: for two POVMs on a nonzero finite-dimensional A,                 *)
(*       c(X,Z) = max_xz ||sqrt(M_x)sqrt(N_z)||_∞² is nonzero.           *)
(* path: eur:overlap_mx_povm_neq0 -> eur:entropic_uncertainty_relation -> *)
(*   eur:entropic_uncertainty_relation -> *)
(*   bb84:entropic_uncertainty_relation_bb84 -> bb84:bb84_secret *)
Lemma overlap_mx_povm_neq0
    (M : 'I_nx -> 'M[C]_na) (N : 'I_nz -> 'M[C]_na) :
  (0 < na)%N -> is_povm_mx M -> is_povm_mx N ->
  overlap_mx M N != 0.
Proof.
  move=> Hna HM HN.
  have HMpsd : forall x, M x \is psdmx
    by move=> x; exact: is_povm_mx_psd HM.
  have HNpsd : forall z, N z \is psdmx
    by move=> z; exact: is_povm_mx_psd HN.
  apply/negP => /eqP Hover0.
  have Hsqrt_zero : forall x z, sqrtmx (M x) *m sqrtmx (N z) = 0.
  {
    move=> x z.
    pose t x z :=
      (@complex.Re R (i2norm (sqrtmx (M x) *m sqrtmx (N z)))) ^+ 2.
    have Ht_le0 : t x z <= 0.
    {
      rewrite -Hover0 /overlap_mx -/t.
      apply: le_trans (_ : t x z <= \big[maxr/0]_(z' < nz) t x z') _.
      - exact: le_bigmax_cond.
      - exact: le_bigmax_cond.
    }
    have Ht_ge0 : 0 <= t x z by rewrite /t sqr_ge0.
    have Ht0 : t x z = 0 by apply/eqP; rewrite eq_le Ht_ge0 Ht_le0.
    have Hi2_re0 :
        @complex.Re R (i2norm (sqrtmx (M x) *m sqrtmx (N z))) = 0.
    {
      move/eqP: Ht0.
      by rewrite /t sqrf_eq0 => /eqP.
    }
    have Hi2_real :
        i2norm (sqrtmx (M x) *m sqrtmx (N z)) \is Num.real.
    {
      exact: ger0_real (i2norm_ge0 (sqrtmx (M x) *m sqrtmx (N z))).
    }
    have Hi2_0 : i2norm (sqrtmx (M x) *m sqrtmx (N z)) = 0.
    {
      by rewrite -(RRe_real Hi2_real) Hi2_re0.
    }
    by apply/eqP; rewrite -i2norm_eq0 Hi2_0 eqxx.
  }
  have HMN_zero : forall x z, M x *m N z = 0.
  {
    move=> x z.
    rewrite -[M x](sqrtmxK (HMpsd x)) -[N z](sqrtmxK (HNpsd z)).
    pose SM := sqrtmx (M x).
    pose SN := sqrtmx (N z).
    change ((SM *m SM) *m (SN *m SN) = 0).
    rewrite -mulmxA [SM *m (SN *m SN)]mulmxA.
    by rewrite (Hsqrt_zero x z) mul0mx mulmx0.
  }
  have Hprod_zero : (\sum_(x < nx) M x) *m (\sum_(z < nz) N z) = 0.
  {
    rewrite mulmx_suml.
    apply: big1 => x _.
    rewrite mulmx_sumr.
    by apply: big1 => z _; rewrite HMN_zero.
  }
  have H1_zero : (1%:M : 'M[C]_na) = 0.
  {
    move: Hprod_zero.
    by rewrite (is_povm_mx_sum HM) (is_povm_mx_sum HN) mulmx1.
  }
  have H1_nz : (1%:M : 'M[C]_na) != 0.
  {
    apply/eqP => Hbad.
    pose i0 := Ordinal Hna.
    move/matrixP/(_ i0 i0): Hbad.
    rewrite !mxE eqxx => Hentry.
    move: (@oner_eq0 C).
    by rewrite -Hentry eqxx.
  }
  by move: H1_nz; rewrite H1_zero eqxx.
Qed.
(* Standard computational projective measurements have maximum overlap 1. *)
(* infra: no tex label — sampled-source quality bookkeeping for BB84.      *)
(* path: eur:overlap_mx_std_projective_povm -> *)
(*   eur:entropic_uncertainty_relation -> *)
(*   eur:entropic_uncertainty_relation -> *)
(*   bb84:entropic_uncertainty_relation_bb84 -> bb84:bb84_secret *)
Lemma overlap_mx_std_projective_povm (n : nat) :
  (0 < n)%N ->
  overlap_mx (@std_projective_povm R n) (@std_projective_povm R n) = 1.
Proof.
  move=> Hn.
  pose i0 : 'I_n := Ordinal Hn.
  apply/le_anti/andP; split.
  - rewrite /overlap_mx.
    apply/bigmax_leP; split; first exact: ler01.
    move=> x _.
    apply/bigmax_leP; split; first exact: ler01.
    move=> z _.
    rewrite /std_projective_povm !sqrtmx_delta_mx_ii.
    pose A := (delta_mx x x : 'M[C]_n) *m delta_mx z z.
    have HA_ge0 : 0 <= i2norm A := i2norm_ge0 A.
    have HA_real : i2norm A \is Num.real := ger0_real HA_ge0.
    have HA_le1 : i2norm A <= 1.
    { rewrite /A.
      apply: (le_trans (i2normM _ _)).
      by rewrite !i2norm_delta mul1r. }
    have Hre_ge0 : 0 <= @complex.Re R (i2norm A).
    { by move: HA_ge0; rewrite -(RRe_real HA_real) lecR. }
    have Hre_le1 : @complex.Re R (i2norm A) <= 1.
    { by move: HA_le1; rewrite -(RRe_real HA_real) lecR. }
    exact: exprn_ile1.
  - rewrite /overlap_mx.
    apply: le_trans (_ :
      1 <= \big[maxr/0]_(z < n)
        (@complex.Re R (i2norm
          (sqrtmx (@std_projective_povm R n i0) *m
           sqrtmx (@std_projective_povm R n z)))) ^ 2) _.
    + apply: le_trans (_ :
        1 <= (@complex.Re R (i2norm
          (sqrtmx (@std_projective_povm R n i0) *m
           sqrtmx (@std_projective_povm R n i0)))) ^ 2) _.
      * by rewrite /std_projective_povm !sqrtmx_delta_mx_ii
          mul_delta_mx i2norm_delta; change (1 <= (1 : R) ^+ 2);
          rewrite expr1n.
      * exact: le_bigmax_cond.
    + exact: le_bigmax_cond.
Qed.
(* path: eur:q_of_mx_std_projective_povm0 -> *)
(*   eur:entropic_uncertainty_relation -> *)
(*   eur:entropic_uncertainty_relation -> *)
(*   bb84:entropic_uncertainty_relation_bb84 -> bb84:bb84_secret *)
Fact q_of_mx_std_projective_povm0 (n : nat) :
  (0 < n)%N ->
  q_of_mx (@std_projective_povm R n) (@std_projective_povm R n) = 0.
Proof.
  move=> Hn.
  by rewrite /q_of_mx overlap_mx_std_projective_povm // /log2 ln1 mul0r oppr0.
Qed.
(* path: eur:sqrt2_inv_sq -> eur:entropic_uncertainty_relation -> *)
(*   eur:entropic_uncertainty_relation -> *)
(*   bb84:entropic_uncertainty_relation_bb84 -> bb84:bb84_secret *)
Local Lemma sqrt2_inv_sq :
  (((Num.sqrt (2%:R))^-1)%R) ^+ 2 = ((2%:R)^-1)%R :> R.
Proof.
  by rewrite exprVn sqr_sqrtr ?ler0n.
Qed.
(* path: eur:delta_hadamard_mx2_delta -> *)
(*   eur:entropic_uncertainty_relation -> *)
(*   eur:entropic_uncertainty_relation -> *)
(*   bb84:entropic_uncertainty_relation_bb84 -> bb84:bb84_secret *)
Lemma delta_hadamard_mx2_delta (x z : 'I_2) :
  delta_mx x x *m (@hadamard_mx2 R) *m delta_mx z z =
  (((Num.sqrt (2%:R))^-1)%R)%:C * (@xbasis_sign2 R x z) *:
    delta_mx x z.
Proof.
  rewrite -mulmxA.
  apply/matrixP=> i j.
  rewrite !mcextra.delta_mx_mulEr !mcextra.delta_mx_mulEl /hadamard_mx2 !mxE mulrA.
  rewrite (eq_sym x i) (eq_sym z j).
  by case: (i == x); case: (j == z); simpc.
Qed.
(* path: eur:hadamard_mx2_entry_norm -> *)
(*   eur:entropic_uncertainty_relation -> *)
(*   eur:entropic_uncertainty_relation -> *)
(*   bb84:entropic_uncertainty_relation_bb84 -> bb84:bb84_secret *)
Lemma hadamard_mx2_entry_norm (x z : 'I_2) :
  `|((((Num.sqrt (2%:R))^-1)%R)%:C * (@xbasis_sign2 R x z))| =
  (((Num.sqrt (2%:R))^-1)%R)%:C.
Proof.
  case: x => [[|[|x]] Hx]; try by [].
  - case: z => [[|[|z]] Hz]; try by [].
    + rewrite /xbasis_sign2 /=.
      by rewrite mulr1 normc_real ger0_norm ?invr_ge0 ?sqrtr_ge0.
    + by rewrite /xbasis_sign2 /= mulr1 normc_real ger0_norm
        ?invr_ge0 ?sqrtr_ge0.
  - case: z => [[|[|z]] Hz]; try by [].
    + by rewrite /xbasis_sign2 /= mulr1 normc_real ger0_norm
        ?invr_ge0 ?sqrtr_ge0.
    + by rewrite /xbasis_sign2 /= mulrN1 normrN normc_real
        ger0_norm ?invr_ge0 ?sqrtr_ge0.
Qed.
(* path: eur:hadamard_mx_entry_norm -> eur:entropic_uncertainty_relation -> *)
(*   eur:entropic_uncertainty_relation -> *)
(*   bb84:entropic_uncertainty_relation_bb84 -> bb84:bb84_secret *)
Lemma hadamard_mx_entry_norm (n : nat) (x z : 'I_(2 ^ n)) :
  `|(@hadamard_mx R n) x z| =
  ((((Num.sqrt (2%:R))^-1)%R) ^+ n)%:C.
Proof.
  rewrite /hadamard_mx.
  apply: bigten_entry_norm => i j.
  by rewrite /hadamard_mx2 mxE hadamard_mx2_entry_norm.
Qed.
(* path: eur:sqrt2_inv_pow_sq -> eur:entropic_uncertainty_relation -> *)
(*   eur:entropic_uncertainty_relation -> *)
(*   bb84:entropic_uncertainty_relation_bb84 -> bb84:bb84_secret *)
Local Lemma sqrt2_inv_pow_sq (n : nat) :
  (((((Num.sqrt (2%:R))^-1)%R) ^+ n) ^+ 2 : R) =
  ((2%:R)^- n : R).
Proof.
  rewrite -exprM mulnC exprM sqrt2_inv_sq.
  by rewrite exprVn.
Qed.
(* path: eur:xz_projective_povm2_overlap_term -> *)
(*   eur:entropic_uncertainty_relation -> *)
(*   eur:entropic_uncertainty_relation -> *)
(*   bb84:entropic_uncertainty_relation_bb84 -> bb84:bb84_secret *)
Lemma xz_projective_povm2_overlap_term (x z : 'I_2) :
  (@complex.Re R (i2norm
    (sqrtmx (@x_projective_povm2 R x) *m
     sqrtmx (@std_projective_povm R 2 z)))) ^ 2 =
  ((2%:R)^-1)%R.
Proof.
  rewrite /std_projective_povm sqrtmx_x_projective_povm2
    sqrtmx_delta_mx_ii x_projective_povm2_hadamard.
  set A := (@hadamard_mx2 R)^*t *m delta_mx x x *m (@hadamard_mx2 R)
    *m delta_mx z z.
  have Hnorm :
      i2norm A =
      i2norm (delta_mx x x *m (@hadamard_mx2 R) *m delta_mx z z).
  {
    rewrite -[LHS](@i2normUl R 2 2 (@hadamard_mx2 R) A
      hadamard_mx2_unitary).
    rewrite /A !mulmxA.
    have HHH : (@hadamard_mx2 R) *m (@hadamard_mx2 R)^*t = 1%:M :=
      unitarymxK hadamard_mx2_unitary.
    by rewrite HHH mul1mx.
  }
  rewrite Hnorm delta_hadamard_mx2_delta i2normZ i2norm_delta mulr1.
  rewrite hadamard_mx2_entry_norm.
  by rewrite re_realid -exprnP sqrt2_inv_sq.
Qed.
(* path: eur:unitary_projective_std_i2norm -> *)
(*   eur:entropic_uncertainty_relation -> *)
(*   eur:entropic_uncertainty_relation -> *)
(*   bb84:entropic_uncertainty_relation_bb84 -> bb84:bb84_secret *)
Lemma unitary_projective_std_i2norm (n : nat) (U : 'M[C]_n)
    (HU : U \is unitarymx) (x z : 'I_n) :
  i2norm
    (sqrtmx (U^*t *m delta_mx x x *m U) *m
     sqrtmx (@std_projective_povm R n z)) =
  `|U x z|.
Proof.
  rewrite (@sqrtmx_unitary_delta_projector R n U x HU).
  rewrite /std_projective_povm sqrtmx_delta_mx_ii.
  set A := U^*t *m delta_mx x x *m U *m delta_mx z z.
  have Hnorm :
      i2norm A = i2norm (delta_mx x x *m U *m delta_mx z z).
  {
    rewrite -[LHS](@i2normUl R n n U A HU) /A !mulmxA.
    have HUU : U *m U^*t = 1%:M := unitarymxK HU.
    by rewrite HUU mul1mx.
  }
  by rewrite Hnorm delta_mx_sandwich i2normZ i2norm_delta mulr1.
Qed.
(* path: eur:xz_projective_povm_overlap_term -> *)
(*   eur:entropic_uncertainty_relation -> *)
(*   eur:entropic_uncertainty_relation -> *)
(*   bb84:entropic_uncertainty_relation_bb84 -> bb84:bb84_secret *)
Lemma xz_projective_povm_overlap_term (n : nat)
    (x z : 'I_(2 ^ n)) :
  (@complex.Re R (i2norm
    (sqrtmx (@x_projective_povm R n x) *m
     sqrtmx (@std_projective_povm R (2 ^ n) z)))) ^ 2 =
  ((2%:R)^- n)%R.
Proof.
  rewrite /x_projective_povm (unitary_projective_std_i2norm (hadamard_mx_unitary n)).
  rewrite hadamard_mx_entry_norm re_realid.
  by rewrite -exprnP sqrt2_inv_pow_sq.
Qed.
(* path: eur:overlap_mx_xz_projective_povm -> *)
(*   eur:entropic_uncertainty_relation -> *)
(*   eur:entropic_uncertainty_relation -> *)
(*   bb84:entropic_uncertainty_relation_bb84 -> bb84:bb84_secret *)
Lemma overlap_mx_xz_projective_povm (n : nat) :
  overlap_mx (@x_projective_povm R n) (@std_projective_povm R (2 ^ n)) =
  ((2%:R)^- n)%R.
Proof.
  apply/le_anti/andP; split.
  - rewrite /overlap_mx.
    apply/bigmax_leP; split; first by rewrite invr_ge0.
    move=> x _.
    apply/bigmax_leP; split; first by rewrite invr_ge0.
    by move=> z _; rewrite xz_projective_povm_overlap_term.
  - have Hdim_pos : (0 < 2 ^ n)%N by rewrite expn_gt0.
    pose i0 : 'I_(2 ^ n) := Ordinal Hdim_pos.
    rewrite /overlap_mx -(@xz_projective_povm_overlap_term n i0 i0).
    apply: le_trans (_ : _ <=
      \big[maxr/0]_(z < 2 ^ n)
        ((@complex.Re R (i2norm
          (sqrtmx (@x_projective_povm R n i0) *m
           sqrtmx (@std_projective_povm R (2 ^ n) z)))) ^ 2)) _.
    + exact: le_bigmax_cond.
    + exact: le_bigmax_cond.
Qed.
(* path: eur:q_of_mx_xz_projective_povm -> *)
(*   eur:entropic_uncertainty_relation -> *)
(*   eur:entropic_uncertainty_relation -> *)
(*   bb84:entropic_uncertainty_relation_bb84 -> bb84:bb84_secret *)
Lemma q_of_mx_xz_projective_povm (n : nat) :
  q_of_mx (@x_projective_povm R n) (@std_projective_povm R (2 ^ n)) = n%:R.
Proof.
  by rewrite /q_of_mx overlap_mx_xz_projective_povm neg_log2_inv_pow2_nat.
Qed.
(* path: eur:overlap_mx_xz_projective_povm2 -> *)
(*   eur:entropic_uncertainty_relation -> *)
(*   eur:entropic_uncertainty_relation -> *)
(*   bb84:entropic_uncertainty_relation_bb84 -> bb84:bb84_secret *)
Lemma overlap_mx_xz_projective_povm2 :
  overlap_mx (@x_projective_povm2 R) (@std_projective_povm R 2) =
  ((2%:R)^-1)%R.
Proof.
  apply/le_anti/andP; split.
  - rewrite /overlap_mx.
    apply/bigmax_leP; split; first by rewrite invr_ge0 ler0n.
    move=> x _.
    apply/bigmax_leP; split; first by rewrite invr_ge0 ler0n.
    by move=> z _; rewrite xz_projective_povm2_overlap_term.
  - pose i0 : 'I_2 := Ordinal (ltn0Sn 1).
    rewrite /overlap_mx -(@xz_projective_povm2_overlap_term i0 i0).
    apply: le_trans (_ : _ <=
      \big[maxr/0]_(z < 2)
        ((@complex.Re R (i2norm
          (sqrtmx (@x_projective_povm2 R i0) *m
           sqrtmx (@std_projective_povm R 2 z)))) ^ 2)) _.
    + exact: le_bigmax_cond.
    + exact: le_bigmax_cond.
Qed.
(* path: eur:q_of_mx_xz_projective_povm2 -> *)
(*   eur:entropic_uncertainty_relation -> *)
(*   eur:entropic_uncertainty_relation -> *)
(*   bb84:entropic_uncertainty_relation_bb84 -> bb84:bb84_secret *)
Fact q_of_mx_xz_projective_povm2 :
  q_of_mx (@x_projective_povm2 R) (@std_projective_povm R 2) = 1.
Proof.
  rewrite /q_of_mx overlap_mx_xz_projective_povm2 /log2.
  rewrite lnV ?ltr0n //.
  rewrite mulNr opprK.
  rewrite divff ?lt0r_neq0 ?ln2_gt0 //.
  by rewrite qualifE /= ltr0n.
Qed.
End Stage0Infra.
(* ================================================================== *)
(* Stinespring lifted-state preservation                                *)
(* ================================================================== *)
Section StinespringLift.
Variables (na nb nc nx : nat).
Let U_lift (M : 'I_nx -> 'M[C]_na) :
    'M[C]_(((nx * nx) * na) * nb * nc, na * nb * nc) :=
  stinespring_U2 M *t (1%:M : 'M[C]_nb) *t (1%:M : 'M[C]_nc).
(* path: eur:stinespring_U2_lift_iso -> eur:stinespring_U2_lift_denmx -> *)
(*   eur:rho_ZZpABC_denmx -> eur:ucr_pure_smooth -> *)
(*   eur:entropic_uncertainty_relation -> *)
(*   eur:entropic_uncertainty_relation -> *)
(*   bb84:entropic_uncertainty_relation_bb84 -> bb84:bb84_secret *)
Lemma stinespring_U2_lift_iso (M : 'I_nx -> 'M[C]_na) :
  is_povm_mx M ->
  (U_lift M)^*t *m U_lift M = 1%:M.
Proof.
  move=> HM.
  have HMpsd : forall x, M x \is psdmx
    by move=> x; exact: is_povm_mx_psd HM.
  have HMsum : \sum_(x < nx) M x = 1%:M := is_povm_mx_sum HM.
  rewrite /U_lift !adjmx_tens !tensmx_mul !adjmx1.
  by rewrite (stinespring_U2_iso HMpsd HMsum) !mulmx1 !tensmx11.
Qed.
(* path: eur:stinespring_U2_lift_denmx -> eur:rho_ZZpABC_denmx -> *)
(*   eur:ucr_pure_smooth -> eur:entropic_uncertainty_relation -> *)
(*   eur:entropic_uncertainty_relation -> *)
(*   bb84:entropic_uncertainty_relation_bb84 -> bb84:bb84_secret *)
Lemma stinespring_U2_lift_denmx
    (M : 'I_nx -> 'M[C]_na)
    (rhoABC : 'M[C]_(na * nb * nc)) :
  is_povm_mx M ->
  rhoABC \is denmx ->
  U_lift M *m rhoABC *m (U_lift M)^*t \is denmx.
Proof.
  move=> HM /denmxP[Hrho_psd Hrho_tr].
  have Hiso := stinespring_U2_lift_iso HM.
  apply/denmxP; split.
  - exact: form_psdmx.
  - by rewrite mxtrace_mulC mulmxA Hiso mul1mx.
Qed.
(* path: eur:stinespring_U2_lift_rank1 -> eur:rho_ZZpABC_denmx -> *)
(*   eur:ucr_pure_smooth -> eur:entropic_uncertainty_relation -> *)
(*   eur:entropic_uncertainty_relation -> *)
(*   bb84:entropic_uncertainty_relation_bb84 -> bb84:bb84_secret *)
Lemma stinespring_U2_lift_rank1
    (M : 'I_nx -> 'M[C]_na)
    (rhoABC : 'M[C]_(na * nb * nc)) :
  is_povm_mx M ->
  rhoABC \is denmx ->
  \rank rhoABC = 1%N ->
  \rank (U_lift M *m rhoABC *m (U_lift M)^*t) = 1%N.
Proof.
  move=> HM Hden Hrank.
  have [v Hv] := psdmx_rank1_form (denmx_psd Hden) Hrank.
  have Hform :
      U_lift M *m rhoABC *m (U_lift M)^*t =
      (U_lift M *m v) *m (U_lift M *m v)^*t.
  { by rewrite Hv adjmxM !mulmxA. }
  have Hrank_le :
      (\rank (U_lift M *m rhoABC *m (U_lift M)^*t) <= 1)%N.
  { rewrite Hform.
    exact: (leq_trans (mxrankM_maxl _ _) (rank_leq_col _)). }
  apply/eqP; rewrite eqn_leq Hrank_le/=.
  have Hiso := stinespring_U2_lift_iso HM.
  rewrite lt0n mxrank_eq0.
  apply/eqP=> Hzero.
  have Hrho0 : rhoABC = 0.
  { have Hcyc :
        (U_lift M)^*t *m (U_lift M *m rhoABC *m (U_lift M)^*t) *m U_lift M
        = rhoABC.
    { by rewrite !mulmxA Hiso mul1mx -mulmxA Hiso mulmx1. }
    by rewrite -Hcyc Hzero !mulmx0 mul0mx. }
  by rewrite Hrho0 mxrank0 in Hrank.
Qed.
(* path: eur:rho_XXpABC_denmx -> eur:entropic_uncertainty_relation -> *)
(*   eur:entropic_uncertainty_relation -> *)
(*   bb84:entropic_uncertainty_relation_bb84 -> bb84:bb84_secret *)
Lemma rho_XXpABC_denmx
    (M : 'I_nx -> 'M[C]_na)
    (rhoABC : 'M[C]_(na * nb * nc)) :
  is_povm_mx M ->
  rhoABC \is denmx ->
  rho_XXpABC M rhoABC \is denmx.
Proof.
  by move=> HM Hrho; exact: stinespring_U2_lift_denmx.
Qed.
(* path: eur:rho_XXpABC_rank1 -> eur:entropic_uncertainty_relation -> *)
(*   eur:entropic_uncertainty_relation -> *)
(*   bb84:entropic_uncertainty_relation_bb84 -> bb84:bb84_secret *)
Lemma rho_XXpABC_rank1
    (M : 'I_nx -> 'M[C]_na)
    (rhoABC : 'M[C]_(na * nb * nc)) :
  is_povm_mx M ->
  rhoABC \is denmx ->
  \rank rhoABC = 1%N ->
  \rank (rho_XXpABC M rhoABC) = 1%N.
Proof.
  by move=> HM Hrho Hrank; exact: stinespring_U2_lift_rank1.
Qed.
End StinespringLift.
Section StinespringLiftZ.
Variables (na nb nc nz : nat).
(* path: eur:rho_ZZpABC_denmx -> eur:ucr_pure_smooth -> *)
(*   eur:entropic_uncertainty_relation -> *)
(*   eur:entropic_uncertainty_relation -> *)
(*   bb84:entropic_uncertainty_relation_bb84 -> bb84:bb84_secret *)
Lemma rho_ZZpABC_denmx
    (N : 'I_nz -> 'M[C]_na)
    (rhoABC : 'M[C]_(na * nb * nc)) :
  is_povm_mx N ->
  rhoABC \is denmx ->
  rho_ZZpABC N rhoABC \is denmx.
Proof.
  by move=> HN Hrho; exact: stinespring_U2_lift_denmx.
Qed.
(* path: eur:rho_ZZpABC_rank1 -> eur:rho_ZC_ZpAB_extension -> *)
(*   eur:ucr_pure_smooth -> eur:entropic_uncertainty_relation -> *)
(*   eur:entropic_uncertainty_relation -> *)
(*   bb84:entropic_uncertainty_relation_bb84 -> bb84:bb84_secret *)
Lemma rho_ZZpABC_rank1
    (N : 'I_nz -> 'M[C]_na)
    (rhoABC : 'M[C]_(na * nb * nc)) :
  is_povm_mx N ->
  rhoABC \is denmx ->
  \rank rhoABC = 1%N ->
  \rank (rho_ZZpABC N rhoABC) = 1%N.
Proof.
  by move=> HN Hrho Hrank; exact: stinespring_U2_lift_rank1.
Qed.
End StinespringLiftZ.
Section StinespringZCExtension.
Variables (na nb nc nz : nat).
(* TeX Stinespring marginal used in Stage 0 and Stage 1.                *)
(* math: regrouping `rho_ZZ'ABC` as `(Z*C)*(Z'*A*B)` gives a pure       *)
(* extension of the direct post-measurement state `rho_ZC`.             *)
(* path: eur:rho_ZC_ZpAB_extension -> eur:ucr_pure_smooth -> *)
(*   eur:entropic_uncertainty_relation -> *)
(*   eur:entropic_uncertainty_relation -> *)
(*   bb84:entropic_uncertainty_relation_bb84 -> bb84:bb84_secret *)
Lemma rho_ZC_ZpAB_extension
    (N : 'I_nz -> 'M[C]_na)
    (rhoABC : 'M[C]_(na * nb * nc)) :
  is_povm_mx N ->
  rhoABC \is denmx -> \rank rhoABC = 1%N ->
  let rhoZCZpAB := rho_ZC_ZpAB N rhoABC in
  rhoZCZpAB \is denmx /\
  \rank rhoZCZpAB = 1%N /\
  ptrace2 rhoZCZpAB = rho_ZC N rhoABC.
Proof.
  move=> HN Hden Hrank /=.
  pose rhoZZ := rho_ZZpABC N rhoABC.
  pose rhoZ := rho_ZC N rhoABC.
  pose rhoZCZpAB := rho_ZC_ZpAB N rhoABC.
  have HrhoZZ_den : rhoZZ \is denmx.
  { by rewrite /rhoZZ; exact: rho_ZZpABC_denmx. }
  have HrhoZZ_rank : \rank rhoZZ = 1%N.
  { by rewrite /rhoZZ; exact: rho_ZZpABC_rank1. }
  (* TeX Stinespring marginal: the `(Z*C)*(Z'*A*B)` regrouping is only
     a permutation/cast of the pure `rho_ZZ'ABC` state. *)
  have HZC_den_rank :
      rhoZCZpAB \is denmx /\ \rank rhoZCZpAB = 1%N.
  {
    pose old_idx (i : 'I_((nz * nc) * (nz * na * nb))) :
        'I_(((nz * nz) * na) * nb * nc) :=
      let iZE := mxtens_unindex i in
      let izc := mxtens_unindex iZE.1 in
      let ienvB := mxtens_unindex iZE.2 in
      let izpa := mxtens_unindex ienvB.1 in
      mxtens_index (mxtens_index
        (mxtens_index (mxtens_index (izc.1, izpa.1), izpa.2), ienvB.2),
        izc.2).
    pose new_idx (k : 'I_(((nz * nz) * na) * nb * nc)) :
        'I_((nz * nc) * (nz * na * nb)) :=
      let kc := mxtens_unindex k in
      let kb := mxtens_unindex kc.1 in
      let ka := mxtens_unindex kb.1 in
      let kzz := mxtens_unindex ka.1 in
      mxtens_index (mxtens_index (kzz.1, kc.2),
        mxtens_index (mxtens_index (kzz.2, ka.2), kb.2)).
    pose P : 'M[C]_((nz * nc) * (nz * na * nb),
                    (((nz * nz) * na) * nb * nc)) :=
      \matrix_(i, k) ((old_idx i == k)%:R : C).
    have Hnew_oldK : cancel new_idx old_idx.
    {
      move=> k; rewrite /new_idx /old_idx.
      case Ekc: (mxtens_unindex k)=> [kabc kc].
      case Ekb: (mxtens_unindex kabc)=> [kza kb].
      case Eka: (mxtens_unindex kza)=> [kzz ka].
      case Ekzz: (mxtens_unindex kzz)=> [kz kzp].
      rewrite !mxtens_indexK /=.
      by rewrite -Ekzz mxtens_unindexK -Eka mxtens_unindexK
        -Ekb mxtens_unindexK -Ekc mxtens_unindexK.
    }
    have Hold_newK : cancel old_idx new_idx.
    {
      move=> i; rewrite /new_idx /old_idx.
      case Ei: (mxtens_unindex i)=> [izc ienv].
      case Ezc: (mxtens_unindex izc)=> [z c].
      case Eenv: (mxtens_unindex ienv)=> [izpa b].
      case Ezpa: (mxtens_unindex izpa)=> [zp a].
      rewrite !mxtens_indexK /=.
      by rewrite -Ezpa mxtens_unindexK -Eenv mxtens_unindexK
        -Ezc mxtens_unindexK -Ei mxtens_unindexK.
    }
    have HP_iso : P^*t *m P = 1%:M.
    {
      apply/matrixP=> k l.
      rewrite mxE.
      under eq_bigr => i _ do rewrite mxE_adj /P !mxE conjC_nat.
      rewrite (bigD1 (new_idx k)) //= Hnew_oldK eqxx mul1r.
      rewrite [X in _ + X]big1 ?addr0.
      - by rewrite mxE.
      - move=> i Hine.
        have Hold_ne : old_idx i != k.
        {
          apply/negP=> /eqP Hi_old.
          move: Hine.
          by rewrite -(Hold_newK i) Hi_old eqxx.
        }
        by rewrite (negPf Hold_ne) mul0r.
    }
    have HP_form : rhoZCZpAB = P *m rhoZZ *m P^*t.
    {
      apply/matrixP=> i j.
      rewrite /rhoZCZpAB /rho_ZC_ZpAB mxE [RHS]mxE.
      under [RHS]eq_bigr => l _ do rewrite [X in X * _]mxE.
      under [RHS]eq_bigr => l _ do
        under eq_bigr => k _ do rewrite /P !mxE.
      under [RHS]eq_bigr => l _ do rewrite mxE_adj /P !mxE ?conjC_nat.
      rewrite (bigD1 (old_idx j)) //= eqxx mulr1.
      rewrite [X in _ + X]big1 ?addr0.
      - rewrite (bigD1 (old_idx i)) //= eqxx mul1r.
        rewrite [X in _ + X]big1 ?addr0.
        + by rewrite /rhoZZ /rho_ZZpABC /old_idx mxE.
        + by move=> k /negPf Hk; rewrite eq_sym Hk mul0r.
      - by move=> l /negPf Hl; rewrite eq_sym Hl mulr0.
    }
    have Hrank_conj : forall m n (R0 : 'M[C]_(m, n)) (A0 : 'M[C]_n),
        (\rank (R0 *m A0 *m R0^*t) <= \rank A0)%N.
    {
      move=> m n R0 A0.
      exact: leq_trans (mxrankM_maxl _ _) (mxrankM_maxr _ _).
    }
    have Hden_perm : P *m rhoZZ *m P^*t \is denmx.
    {
      move/denmxP: HrhoZZ_den => [Hpsd Htr].
      apply/denmxP; split.
      - exact: form_psdmx.
      - by rewrite mxtrace_mulC mulmxA HP_iso mul1mx.
    }
    have Hrank_perm : \rank (P *m rhoZZ *m P^*t) = \rank rhoZZ.
    {
      apply/eqP; rewrite eqn_leq.
      apply/andP; split; first exact: Hrank_conj.
      have Hback :
          P^*t *m (P *m rhoZZ *m P^*t) *m (P^*t)^*t = rhoZZ.
      {
        by rewrite adjmxK -!mulmxA HP_iso !mulmxA HP_iso mul1mx mulmx1.
      }
      rewrite -[X in (\rank X <= _)%N]Hback.
      exact: (@Hrank_conj (((nz * nz) * na) * nb * nc)
        ((nz * nc) * (nz * na * nb)) P^*t (P *m rhoZZ *m P^*t)).
    }
    rewrite HP_form.
    by split=> //; rewrite Hrank_perm.
  }
  (* TeX Stinespring marginal: tracing out `Z'AB` leaves exactly the
     direct post-measurement state `rho_ZC`. *)
  have HZC_marginal : ptrace2 rhoZCZpAB = rhoZ.
  {
    have HrhoZZ_entry :
        forall (zl zr : 'I_nz) (zpl zpr : 'I_nz)
               (al ar : 'I_na) (bl br : 'I_nb) (cl cr : 'I_nc),
        rhoZZ
          (mxtens_index (mxtens_index
            (mxtens_index (mxtens_index (zl, zpl), al), bl), cl))
          (mxtens_index (mxtens_index
            (mxtens_index (mxtens_index (zr, zpr), ar), br), cr)) =
        ((zl == zpl)%:R : C) * ((zr == zpr)%:R : C) *
        \sum_(a0 : 'I_na) \sum_(a1 : 'I_na)
          sqrtmx (N zl) al a0 *
          rhoABC (mxtens_index (mxtens_index (a0, bl), cl))
                 (mxtens_index (mxtens_index (a1, br), cr)) *
          (sqrtmx (N zr) ar a1)^*.
    {
      move=> zl zr zpl zpr al ar bl br cl cr.
      pose Vlift : 'M[C]_(((nz * nz) * na) * nb * nc, na * nb * nc) :=
        (stinespring_U2 N *t (1%:M : 'M[C]_nb) *t
          (1%:M : 'M[C]_nc)).
      have HV_entry :
          forall (z0 zp0 : 'I_nz) (a0 a1 : 'I_na)
                 (b0 b1 : 'I_nb) (c0 c1 : 'I_nc),
          Vlift
            (mxtens_index (mxtens_index
              (mxtens_index (mxtens_index (z0, zp0), a0), b0), c0))
            (mxtens_index (mxtens_index (a1, b1), c1)) =
          ((z0 == zp0)%:R : C) * sqrtmx (N z0) a0 a1 *
          ((b0 == b1)%:R : C) * ((c0 == c1)%:R : C).
      {
        move=> z0 zp0 a0 a1 b0 b1 c0 c1.
        rewrite /Vlift !tensmxE /stinespring_U2 !mxE !mxtens_indexK /=.
        by [].
      }
      have Hraw_expand :
        rhoZZ
          (mxtens_index (mxtens_index
            (mxtens_index (mxtens_index (zl, zpl), al), bl), cl))
          (mxtens_index (mxtens_index
            (mxtens_index (mxtens_index (zr, zpr), ar), br), cr)) =
        \sum_(a1 : 'I_na) \sum_(b1 : 'I_nb) \sum_(c1 : 'I_nc)
          (\sum_(a0 : 'I_na) \sum_(b0 : 'I_nb) \sum_(c0 : 'I_nc)
            (((zl == zpl)%:R : C) * sqrtmx (N zl) al a0 *
             ((bl == b0)%:R : C) * ((cl == c0)%:R : C)) *
            rhoABC (mxtens_index (mxtens_index (a0, b0), c0))
                   (mxtens_index (mxtens_index (a1, b1), c1))) *
          ((((zr == zpr)%:R : C) * sqrtmx (N zr) ar a1 *
            ((br == b1)%:R : C) * ((cr == c1)%:R : C))^*).
      {
        rewrite /rhoZZ /rho_ZZpABC -/Vlift mxE !mxtens_index_pairV /=.
        apply: eq_bigr => a1 _.
        apply: eq_bigr => b1 _.
        apply: eq_bigr => c1 _.
        rewrite [X in X * _]mxE !mxtens_index_pairV /=.
        under eq_bigr => a0 _ do
          under eq_bigr => b0 _ do
            under eq_bigr => c0 _ do rewrite HV_entry.
        by rewrite mxE_adj HV_entry.
      }
      rewrite Hraw_expand.
      have delta_collapseR : forall (T : finType) (f : T -> C) (j : T),
          \sum_i f i * ((j == i)%:R : C) = f j.
      {
        move=> T f j.
        rewrite (bigD1 j) //= eqxx mulr1.
        rewrite [X in _ + X]big1 ?addr0 //.
        by move=> i /negPf Hi; rewrite eq_sym Hi mulr0.
      }
      case Hzl: (zl == zpl); last first.
      {
        rewrite /= ?mul0r ?mulr0.
        apply: big1 => a1 _.
        apply: big1 => b1 _.
        apply: big1 => c1 _.
        rewrite big1 ?mul0r //.
        move=> a0 _.
        apply: big1 => b0 _.
        apply: big1 => c0 _.
        by rewrite /= !mul0r.
      }
      case Hzr: (zr == zpr); last first.
      {
        rewrite /= [X in _ = X * _]mulr0 [RHS]mul0r.
        apply: big1 => a1 _.
        apply: big1 => b1 _.
        apply: big1 => c1 _.
        by rewrite !mul0r rmorph0 mulr0.
      }
      rewrite /= !mul1r.
      under eq_bigr => a1 _ do
        under eq_bigr => b1 _ do
          under eq_bigr => c1 _ do
            rewrite !rmorphM /= !conjC_nat.
      under eq_bigr => a1 _ do
        under eq_bigr => b1 _ do
          under eq_bigr => c1 _ do rewrite ?mulrA.
      under eq_bigr => a1 _ do
        under eq_bigr => b1 _ do rewrite delta_collapseR.
      under eq_bigr => a1 _ do rewrite delta_collapseR.
      under eq_bigr => a1 _ do
        under eq_bigr => a0 _ do
          under eq_bigr => b0 _ do
            under eq_bigr => c0 _ do rewrite ?mulrA.
      have delta_collapse_mid : forall (T : finType) (g h : T -> C) (j : T),
          \sum_i g i * ((j == i)%:R : C) * h i = g j * h j.
      {
        move=> T f g j.
        rewrite (bigD1 j) //= eqxx mulr1.
        rewrite [X in _ + X]big1 ?addr0 //.
        by move=> i /negPf Hi; rewrite eq_sym Hi mulr0 mul0r.
      }
      under eq_bigr => a1 _ do
        under eq_bigr => a0 _ do
          under eq_bigr => b0 _ do rewrite delta_collapse_mid.
      under eq_bigr => a1 _ do
        under eq_bigr => a0 _ do rewrite delta_collapse_mid.
      rewrite ?mulr0 ?subr0.
      under eq_bigr => a1 _ do
        under eq_bigr => a0 _ do rewrite ?mul1r ?mulr1.
      under eq_bigr => a1 _ do rewrite mulr1 mulr_suml.
      rewrite exchange_big /=.
      by apply: eq_bigr => a0 _; apply: eq_bigr => a1 _; rewrite ?mulrA.
    }
    have ptrace2E' : forall s t (B : 'M[C]_(s * t)) r1 r2,
        (ptrace2 B) r1 r2 =
        \sum_(k0 : 'I_t) B (mxtens_index (r1, k0))
                           (mxtens_index (r2, k0)).
    {
      move=> s t B r1 r2; rewrite ptrace2E1 ptrace1E.
      by apply: eq_bigr => k0 _; rewrite mxE !mxtens_indexK.
    }
    apply/matrixP=> i j.
    case: (mxtens_indexP i)=> zl cl.
    case: (mxtens_indexP j)=> zr cr.
    have HL_entry :
        (ptrace2 rhoZCZpAB) (mxtens_index (zl, cl))
          (mxtens_index (zr, cr)) =
        \sum_(zp : 'I_nz) \sum_(a : 'I_na) \sum_(b : 'I_nb)
        \sum_(a0 : 'I_na) \sum_(a1 : 'I_na)
          ((zl == zp)%:R : C) * ((zr == zp)%:R : C) *
          (sqrtmx (N zl) a a0 *
           rhoABC (mxtens_index (mxtens_index (a0, b), cl))
                  (mxtens_index (mxtens_index (a1, b), cr)) *
           (sqrtmx (N zr) a a1)^*).
    {
      rewrite ptrace2E' !mxtens_index_pairV /=.
      apply: eq_bigr => zp _.
      apply: eq_bigr => a _.
      apply: eq_bigr => b _.
      rewrite /rhoZCZpAB /rho_ZC_ZpAB mxE !mxtens_indexK /= HrhoZZ_entry.
      rewrite mulr_sumr.
      apply: eq_bigr => a0 _.
      rewrite mulr_sumr.
      by apply: eq_bigr => a1 _; rewrite mulrA.
    }
    have HR_entry :
        rhoZ (mxtens_index (zl, cl)) (mxtens_index (zr, cr)) =
        \sum_(z : 'I_nz) \sum_(a : 'I_na) \sum_(b : 'I_nb)
        \sum_(a0 : 'I_na) \sum_(a1 : 'I_na)
          ((zl == z)%:R : C) * ((zr == z)%:R : C) *
          (sqrtmx (N zl) a a0 *
           rhoABC (mxtens_index (mxtens_index (a0, b), cl))
                  (mxtens_index (mxtens_index (a1, b), cr)) *
           (sqrtmx (N zr) a a1)^*).
    {
      have HsqrtC : forall z0 a0 a1,
          (sqrtmx (N z0) a0 a1)^* = sqrtmx (N z0) a1 a0.
      {
        move=> z0 a0 a1.
        have /hermmxP Hs : sqrtmx (N z0) \is hermmx.
        {
          have HNz : N z0 \is psdmx by exact: is_povm_mx_psd HN.
          exact: sqrtmx_herm (psdmx_herm HNz).
        }
        by rewrite {2}Hs mxE_adj.
      }
      have Hsandwich_entry : forall z0 : 'I_nz,
          ptrace1
            ((sqrtmx (N z0) *t 1%:M *t 1%:M) *m rhoABC *m
             (sqrtmx (N z0) *t 1%:M *t 1%:M)) cl cr =
          \sum_(a : 'I_na) \sum_(b : 'I_nb)
          \sum_(a0 : 'I_na) \sum_(a1 : 'I_na)
            sqrtmx (N z0) a a0 *
            rhoABC (mxtens_index (mxtens_index (a0, b), cl))
                   (mxtens_index (mxtens_index (a1, b), cr)) *
            (sqrtmx (N z0) a a1)^*.
      {
        move=> z0.
        pose Kz : 'M[C]_(na * nb * nc) :=
          sqrtmx (N z0) *t (1%:M : 'M[C]_nb) *t
            (1%:M : 'M[C]_nc).
        have Kz_entry :
            forall (a0 a1 : 'I_na) (b0 b1 : 'I_nb)
                   (c0 c1 : 'I_nc),
            Kz (mxtens_index (mxtens_index (a0, b0), c0))
               (mxtens_index (mxtens_index (a1, b1), c1)) =
            sqrtmx (N z0) a0 a1 *
            ((b0 == b1)%:R : C) * ((c0 == c1)%:R : C).
        {
          move=> a0 a1 b0 b1 c0 c1.
          by rewrite /Kz !tensmxE !mxE /=.
        }
        have Hraw_sandwich :
            ptrace1
              ((sqrtmx (N z0) *t 1%:M *t 1%:M) *m rhoABC *m
               (sqrtmx (N z0) *t 1%:M *t 1%:M)) cl cr =
            \sum_(a : 'I_na) \sum_(b : 'I_nb)
            \sum_(a1 : 'I_na) \sum_(b1 : 'I_nb) \sum_(c1 : 'I_nc)
              (\sum_(a0 : 'I_na) \sum_(b0 : 'I_nb) \sum_(c0 : 'I_nc)
                sqrtmx (N z0) a a0 *
                ((b == b0)%:R : C) * ((cl == c0)%:R : C) *
                rhoABC (mxtens_index (mxtens_index (a0, b0), c0))
                       (mxtens_index (mxtens_index (a1, b1), c1))) *
              ((sqrtmx (N z0) a a1)^* *
               ((b1 == b)%:R : C) * ((c1 == cr)%:R : C)).
        {
          rewrite -/Kz ptrace1E mxtens_index_pairV /=.
          apply: eq_bigr => a _.
          apply: eq_bigr => b _.
          rewrite mxE !mxtens_index_pairV /=.
          apply: eq_bigr => a1 _.
          apply: eq_bigr => b1 _.
          apply: eq_bigr => c1 _.
          rewrite [X in X * _]mxE !mxtens_index_pairV /=.
          under eq_bigr => a0 _ do
            under eq_bigr => b0 _ do
              under eq_bigr => c0 _ do rewrite Kz_entry.
          rewrite Kz_entry -HsqrtC.
          by [].
        }
        rewrite Hraw_sandwich.
        have delta_collapseR : forall (T : finType) (f : T -> C) (jj : T),
            \sum_i f i * ((i == jj)%:R : C) = f jj.
        {
          move=> T f jj.
          rewrite (bigD1 jj) //= eqxx mulr1.
          rewrite [X in _ + X]big1 ?addr0 //.
          by move=> ii /negPf Hi; rewrite Hi mulr0.
        }
        have delta_collapse_mid : forall (T : finType) (g h : T -> C) (jj : T),
            \sum_i g i * ((jj == i)%:R : C) * h i = g jj * h jj.
        {
          move=> T f g jj.
          rewrite (bigD1 jj) //= eqxx mulr1.
          rewrite [X in _ + X]big1 ?addr0 //.
          by move=> ii /negPf Hi; rewrite eq_sym Hi mulr0 mul0r.
        }
        under eq_bigr => a _ do
          under eq_bigr => b _ do
            under eq_bigr => a1 _ do
              under eq_bigr => b1 _ do
                under eq_bigr => c1 _ do rewrite ?mulrA.
        under eq_bigr => a _ do
          under eq_bigr => b _ do
            under eq_bigr => a1 _ do
              under eq_bigr => b1 _ do rewrite delta_collapseR.
        under eq_bigr => a _ do
          under eq_bigr => b _ do
            under eq_bigr => a1 _ do rewrite delta_collapseR.
        under eq_bigr => a _ do
          under eq_bigr => b _ do
            under eq_bigr => a1 _ do
              under eq_bigr => a0 _ do
                under eq_bigr => b0 _ do
                  under eq_bigr => c0 _ do rewrite ?mulrA.
        under eq_bigr => a _ do
          under eq_bigr => b _ do
            under eq_bigr => a1 _ do
              under eq_bigr => a0 _ do
                under eq_bigr => b0 _ do rewrite delta_collapse_mid.
        under eq_bigr => a _ do
          under eq_bigr => b _ do
            under eq_bigr => a1 _ do
              under eq_bigr => a0 _ do rewrite delta_collapse_mid.
        under eq_bigr => a _ do
          under eq_bigr => b _ do
            under eq_bigr => a1 _ do rewrite mulr_suml.
        under eq_bigr => a _ do
          under eq_bigr => b _ do rewrite exchange_big.
        by [].
      }
      rewrite /rhoZ /rho_ZC summxE.
      apply: eq_bigr => z _.
      rewrite tensmxE /= Hsandwich_entry.
      case Hzl: (zl == z); case Hzr: (zr == z); rewrite /=.
      - move/eqP: Hzl=> Hzl_eq.
        move/eqP: Hzr=> Hzr_eq.
        subst z.
        move: Hzr_eq=> /eqP.
        rewrite eq_sym => /eqP Hzr_eq.
        subst zr.
        rewrite mxE eqxx /= mul1r.
        under [RHS]eq_bigr => a _ do
          under eq_bigr => b _ do
            under eq_bigr => a0 _ do
              under eq_bigr => a1 _ do rewrite !mul1r.
        by [].
      - rewrite mxE Hzl Hzr /= ?mul0r ?mulr0.
        symmetry.
        apply: big1 => a _; apply: big1 => b _.
        apply: big1 => a0 _; apply: big1 => a1 _.
        by rewrite ?mul0r ?mulr0.
      - rewrite mxE Hzl Hzr /= ?mul0r ?mulr0.
        symmetry.
        apply: big1 => a _; apply: big1 => b _.
        apply: big1 => a0 _; apply: big1 => a1 _.
        by rewrite ?mul0r ?mulr0.
      - rewrite mxE Hzl Hzr /= ?mul0r ?mulr0.
        symmetry.
        apply: big1 => a _; apply: big1 => b _.
        apply: big1 => a0 _; apply: big1 => a1 _.
        by rewrite ?mul0r ?mulr0.
    }
    by rewrite HL_entry HR_entry.
  }
  by case: HZC_den_rank => ? ?; split=> //; split.
Qed.
End StinespringZCExtension.
(* ================================================================== *)
(* Operator-norm bound used in Stage 0 (tex eqn:mo9)                    *)
(* Paper: Tomamichel & Renner (PRL 106, 110506 (2011); arXiv:1009.2015),*)
(*   "Proof of the Main Result", Eq. (11) and supporting operator bound.*)
(* math: √N_z M_x √N_z = |√N_z √M_x|² ≤ c · I_A                         *)
(*       where c := overlap_mx M N = max_{x,z} ||√M_x √N_z||_∞²        *)
(* ================================================================== *)
(* ================================================================== *)
(* Stage 0: pure ρ_{ABC}, ε = 0                                           *)
(* Paper: Tomamichel & Renner (PRL 106, 110506 (2011); arXiv:1009.2015),  *)
(*   "Proof of the Main Result", pure ε=0 case (Eqs. (6)-(11)).           *)
(* math: For pure ρ_{ABC} and c := overlap_mx M N:                        *)
(*       H_min(X|B)_ρ + H_max(Z|C)_ρ ≥ -log c                            *)
(* ================================================================== *)
(* ================================================================== *)
(* Post-measurement infrastructure: subden preservation, contraction,    *)
(* and the Uhlmann lift specialised to rho_ZC. Used by Stages 1 and 2.   *)
(* ================================================================== *)
(* Paper: Tomamichel & Renner (PRL 106, 110506 (2011); arXiv:1009.2015) —  *)
(*   ρ_ZC definition; cf. Tomamichel, 'A Framework for Non-Asymptotic      *)
(*   Quantum Information Theory' (arXiv:1203.2142), Theorem 7.2 post-       *)
(*   measurement states (Eqs. (7.16)-(7.17)).                             *)
(* math: tr ρ_ZC = tr ρ_{ABC} ≤ 1.                                        *)
(* ρ_ZC is a sub-den when ρ_{ABC} is sub-den and N a POVM (CQ-TPCP).        *)
(* path: eur:rho_ZC_subden -> eur:eur_rho_ZC_psd -> bb84:bb84_secret *)
Lemma rho_ZC_subden {na nb nc nz : nat}
    (N : 'I_nz -> 'M[C]_na) (rhoABC : 'M[C]_(na * nb * nc)) :
  is_povm_mx N -> rhoABC \is denmx ->
  rho_ZC N rhoABC \is denmx.
Proof.
  move=> HN Hrho.
  have /denmxP[Hrho_psd Hrho_tr] := Hrho.
  have HNpsd : forall z, N z \is psdmx
    by move=> z; exact: is_povm_mx_psd HN.
  have HNsum : \sum_(z < nz) N z = 1%:M := is_povm_mx_sum HN.
  apply/denmxP; split.
  - rewrite /rho_ZC.
    apply: psdmx_sum => z _.
    apply: psdmx_tens.
    + exact: delta_mx_ii_psdmx.
    + apply: ptrace1_psd.
      pose Kz : 'M[C]_(na * nb * nc) :=
        (sqrtmx (N z) *t (1%:M : 'M[C]_nb) *t (1%:M : 'M[C]_nc)).
      have HKz_herm : Kz^*t = Kz.
      {
        rewrite /Kz !adjmx_tens !adjmx1.
        have /hermmxP Hsqrt := sqrtmx_herm (psdmx_herm (HNpsd z)).
        by rewrite -Hsqrt.
      }
      change (Kz *m rhoABC *m Kz \is psdmx).
      rewrite -[X in _ *m X]HKz_herm.
      apply: form_psdmx.
      exact: Hrho_psd.
  - rewrite /rho_ZC linear_sum /=.
    have Hcyc : forall z,
        \tr ((sqrtmx (N z) *t 1%:M *t 1%:M) *m rhoABC *m
             (sqrtmx (N z) *t 1%:M *t 1%:M)) =
        \tr (rhoABC *m ((N z) *t 1%:M *t 1%:M)).
    {
      move=> z.
      rewrite mxtrace_mulC mulmxA mxtrace_mulC.
      by rewrite !tensmx_mul !mulmx1 (sqrtmxK (HNpsd z)).
    }
    under eq_bigr do rewrite mxtrace_tens tr_delta_mx_ii -tr_ptrace1 mul1r Hcyc.
    rewrite -linear_sum /= -mulmx_sumr -linear_sumlz /= -linear_sumlz /= HNsum.
    by rewrite !tensmx11 mulmx1.
Qed.
(* rho_XB_subden *)
(* infra: no tex label — fundamental & reusable (mathcomp-style) *)
(* consumer: rho_XB_subden is used downstream by the BB84 secrecy proof. *)
(* path: eur:rho_XB_subden -> eur:eur_rho_XB_psd -> bb84:bb84_secret *)
Lemma rho_XB_subden {na nb nc nx : nat}
    (M : 'I_nx -> 'M[C]_na) (rhoABC : 'M[C]_(na * nb * nc)) :
  is_povm_mx M -> rhoABC \is denmx ->
  rho_XB M rhoABC \is denmx.
Proof.
  move=> HM Hrho.
  have /denmxP[Hrho_psd Hrho_tr] := Hrho.
  have HMpsd : forall x, M x \is psdmx
    by move=> x; exact: is_povm_mx_psd HM.
  have HMsum : \sum_(x < nx) M x = 1%:M := is_povm_mx_sum HM.
  apply/denmxP; split.
  - rewrite /rho_XB.
    apply: psdmx_sum => x _.
    apply: psdmx_tens.
    + exact: delta_mx_ii_psdmx.
    + apply: ptrace1_psd.
      apply: ptrace2_psd.
      pose Kx : 'M[C]_(na * nb * nc) :=
        (sqrtmx (M x) *t (1%:M : 'M[C]_nb) *t (1%:M : 'M[C]_nc)).
      have HKx_herm : Kx^*t = Kx.
      {
        rewrite /Kx !adjmx_tens !adjmx1.
        have /hermmxP Hsqrt := sqrtmx_herm (psdmx_herm (HMpsd x)).
        by rewrite -Hsqrt.
      }
      change (Kx *m rhoABC *m Kx \is psdmx).
      rewrite -[X in _ *m X]HKx_herm.
      apply: form_psdmx.
      exact: Hrho_psd.
  - rewrite /rho_XB linear_sum /=.
    have Hcyc : forall x,
        \tr ((sqrtmx (M x) *t 1%:M *t 1%:M) *m rhoABC *m
             (sqrtmx (M x) *t 1%:M *t 1%:M)) =
        \tr (rhoABC *m ((M x) *t 1%:M *t 1%:M)).
    {
      move=> x.
      rewrite mxtrace_mulC mulmxA mxtrace_mulC.
      by rewrite !tensmx_mul !mulmx1 (sqrtmxK (HMpsd x)).
    }
    under eq_bigr do rewrite mxtrace_tens tr_delta_mx_ii -tr_ptrace1 -tr_ptrace2 mul1r Hcyc.
    rewrite -linear_sum /=.
      rewrite -mulmx_sumr -linear_sumlz /= -linear_sumlz /= HMsum.
      by rewrite !tensmx11 mulmx1.
Qed.
(* path: eur:rho_ZC_trace -> eur:eur_rho_ZC_tr1 -> bb84:bb84_secret *)
Lemma rho_ZC_trace {na nb nc nz : nat}
    (N : 'I_nz -> 'M[C]_na) (rhoABC : 'M[C]_(na * nb * nc)) :
  is_povm_mx N -> \tr (rho_ZC N rhoABC) = \tr rhoABC.
Proof.
  move=> HN.
  have HNpsd : forall z, N z \is psdmx
    by move=> z; exact: is_povm_mx_psd HN.
  have HNsum : \sum_(z < nz) N z = 1%:M := is_povm_mx_sum HN.
  rewrite /rho_ZC linear_sum /=.
  have Hcyc : forall z,
      \tr ((sqrtmx (N z) *t 1%:M *t 1%:M) *m rhoABC *m
           (sqrtmx (N z) *t 1%:M *t 1%:M)) =
      \tr (rhoABC *m ((N z) *t 1%:M *t 1%:M)).
  {
    move=> z.
    rewrite mxtrace_mulC mulmxA mxtrace_mulC.
    by rewrite !tensmx_mul !mulmx1 (sqrtmxK (HNpsd z)).
  }
  under eq_bigr do rewrite mxtrace_tens tr_delta_mx_ii -tr_ptrace1 mul1r Hcyc.
  rewrite -linear_sum /= -mulmx_sumr -linear_sumlz /= -linear_sumlz /= HNsum.
  by rewrite !tensmx11 mulmx1.
Qed.
(* rho_ZC is linear in the input state. *)
(* path: eur:rho_ZC_scale -> eur:entropic_uncertainty_relation -> *)
(*   eur:entropic_uncertainty_relation -> *)
(*   bb84:entropic_uncertainty_relation_bb84 -> bb84:bb84_secret *)
Lemma rho_ZC_scale {na nb nc nz : nat}
    (N : 'I_nz -> 'M[C]_na) (a : C)
    (rhoABC : 'M[C]_(na * nb * nc)) :
  rho_ZC N (a *: rhoABC) = a *: rho_ZC N rhoABC.
Proof.
  rewrite /rho_ZC scaler_sumr.
  apply: eq_bigr => z _.
  rewrite -scalemxAr -scalemxAl.
  set X := sqrtmx (N z) *t 1%:M *t 1%:M *m rhoABC *m
           (sqrtmx (N z) *t 1%:M *t 1%:M).
  have Hptr : ptrace1 (a *: X) = a *: ptrace1 X.
  { rewrite -[a *: X]addr0.
    by rewrite linearP /= linear0 addr0. }
  rewrite Hptr.
  by rewrite -[a *: ptrace1 X]addr0
    (linear_tensmx (delta_mx z z)) linear0r addr0.
Qed.
(* path: eur:rho_ZC_sum -> eur:entropic_uncertainty_relation -> *)
(*   eur:entropic_uncertainty_relation -> *)
(*   bb84:entropic_uncertainty_relation_bb84 -> bb84:bb84_secret *)
Lemma rho_ZC_sum {na nb nc nz : nat} {I : finType}
    (N : 'I_nz -> 'M[C]_na) (P : pred I)
    (rhoABC : I -> 'M[C]_(na * nb * nc)) :
  rho_ZC N (\sum_(i | P i) rhoABC i) =
  \sum_(i | P i) rho_ZC N (rhoABC i).
Proof.
  rewrite /rho_ZC.
  under [LHS]eq_bigr do rewrite mulmx_sumr mulmx_suml linear_sum /=.
  under [LHS]eq_bigr => z _ do rewrite tensmx_sumr.
  rewrite exchange_big /=.
  by apply: eq_bigr => i _.
Qed.
(* path: eur:rho_XB_trace -> eur:eur_rho_XB_tr1 -> bb84:bb84_secret *)
Lemma rho_XB_trace {na nb nc nx : nat}
    (M : 'I_nx -> 'M[C]_na) (rhoABC : 'M[C]_(na * nb * nc)) :
  is_povm_mx M -> \tr (rho_XB M rhoABC) = \tr rhoABC.
Proof.
  move=> HM.
  have HMpsd : forall x, M x \is psdmx
    by move=> x; exact: is_povm_mx_psd HM.
  have HMsum : \sum_(x < nx) M x = 1%:M := is_povm_mx_sum HM.
  rewrite /rho_XB linear_sum /=.
  have Hcyc : forall x,
      \tr ((sqrtmx (M x) *t 1%:M *t 1%:M) *m rhoABC *m
           (sqrtmx (M x) *t 1%:M *t 1%:M)) =
      \tr (rhoABC *m ((M x) *t 1%:M *t 1%:M)).
  {
    move=> x.
    rewrite mxtrace_mulC mulmxA mxtrace_mulC.
    by rewrite !tensmx_mul !mulmx1 (sqrtmxK (HMpsd x)).
  }
  under eq_bigr do rewrite mxtrace_tens tr_delta_mx_ii -tr_ptrace1 -tr_ptrace2 mul1r Hcyc.
  rewrite -linear_sum /= -mulmx_sumr -linear_sumlz /= -linear_sumlz /= HMsum.
  by rewrite !tensmx11 mulmx1.
Qed.
(* Matrix block of the classical X register in `rho_XB`.  This is the
   operator-level counterpart of the trace-only Born rule: projecting the
   classical outcome register onto `x` leaves exactly the `x` Kraus branch
   on Bob's retained system. *)
Lemma rho_XB_block {na nb nc nx : nat}
    (M : 'I_nx -> 'M[C]_na) (rhoABC : 'M[C]_(na * nb * nc))
    (x : 'I_nx) :
  ptrace1
    (((delta_mx x x : 'M[C]_nx) *t (1%:M : 'M[C]_nb)) *m
      rho_XB M rhoABC *m
      ((delta_mx x x : 'M[C]_nx) *t (1%:M : 'M[C]_nb))) =
  ptrace1 (ptrace2
    ((sqrtmx (M x) *t (1%:M : 'M[C]_nb) *t (1%:M : 'M[C]_nc)) *m
      rhoABC *m
      (sqrtmx (M x) *t (1%:M : 'M[C]_nb) *t (1%:M : 'M[C]_nc)))).
Proof.
  set branch := ptrace1 (ptrace2
    ((sqrtmx (M x) *t (1%:M : 'M[C]_nb) *t (1%:M : 'M[C]_nc)) *m
      rhoABC *m
      (sqrtmx (M x) *t (1%:M : 'M[C]_nb) *t (1%:M : 'M[C]_nc)))).
  change (ptrace1
    (((delta_mx x x : 'M[C]_nx) *t (1%:M : 'M[C]_nb)) *m
      rho_XB M rhoABC *m
      ((delta_mx x x : 'M[C]_nx) *t (1%:M : 'M[C]_nb))) = branch).
  rewrite /rho_XB mulmx_sumr mulmx_suml linear_sum /=.
  rewrite (eq_bigr (fun a : 'I_nx => if a == x then branch else 0));
    last first.
  {
    move=> a _.
    rewrite !tensmx_mul !mul1mx.
    case Hax: (a == x) /eqP => [-> | Hax_neq].
    - rewrite ?mul_delta_mx.
      rewrite !mulmx1.
      rewrite (@ptrace1_tensmx R nx nb
        (delta_mx x x : 'M[C]_nx) branch).
      by rewrite mxtrace_delta eqxx scale1r.
    - have Hxa : x != a by rewrite eq_sym Hax.
      rewrite ?mul_delta_mx !mulmx1.
      have Hleft0 :
          (delta_mx x x : 'M[C]_nx) *m delta_mx a a = 0.
      {
        apply/matrixP=> i j.
        rewrite !mxE.
        case Hix: (i == x) /eqP => [-> | Hix_neq].
        - rewrite (bigD1 x) //= !mxE eqxx (negbTE Hxa) mul1r.
          rewrite big1 ?addr0 // => j0 Hneq.
          rewrite mxE (negbTE Hneq).
          by rewrite eqxx andbF mul0r.
        - apply: big1 => j0 _.
          have Hix0 : i != x by rewrite Hix.
          by rewrite mxE (negbTE Hix0) mul0r.
      }
      rewrite Hleft0 mul0mx.
      by rewrite ptrace1_tensmx mxtrace0 scale0r.
  }
  rewrite (bigD1 x) //= eqxx.
  by rewrite big1 ?addr0 // => a /negPf ->.
Qed.
(* ================================================================== *)
(* Ambient set-labelled post-measurement state facts                    *)
(* ================================================================== *)
Section LabelledPostMeasurement.
Variable (L : finType) (HL : L -> chsType).
(* path: eur:eur_rho_XB_psd -> bb84:bb84_secret *)
Lemma eur_rho_XB_psd (X B : {set L}) (disXB : [disjoint X & B])
    (na nb nc nx : nat)
    (rhoSrc : 'M[C]_(na * nb * nc))
    (M : 'I_nx -> 'M[C]_na)
    (dim_eq : nx * nb = dim ('H[HL]_(X :|: B))) :
  is_povm_mx M ->
  rhoSrc \is den1mx ->
  eur_rho_XB disXB rhoSrc M dim_eq \is psdlf.
Proof.
  move=> HM Hden.
  rewrite /eur_rho_XB qualifE mx2hK.
  apply: (@castmx_sq_psdmx R _ _ (esym (tenv_dim disXB))).
  have Hprod_psd :
      castmx (etrans dim_eq (tenv_dim disXB),
              etrans dim_eq (tenv_dim disXB)) (rho_XB M rhoSrc) \is psdmx.
  { apply: (@castmx_sq_psdmx R _ _ (etrans dim_eq (tenv_dim disXB))).
    exact: denmx_psd (rho_XB_subden HM (den1mx_den Hden)). }
  exact: psdmx_bimap_closed_gen Hprod_psd.
Qed.
(* path: eur:eur_rho_XB_tr1 -> bb84:bb84_secret *)
Lemma eur_rho_XB_tr1 (X B : {set L}) (disXB : [disjoint X & B])
    (na nb nc nx : nat)
    (rhoSrc : 'M[C]_(na * nb * nc))
    (M : 'I_nx -> 'M[C]_na)
    (dim_eq : nx * nb = dim ('H[HL]_(X :|: B))) :
  is_povm_mx M ->
  rhoSrc \is den1mx ->
  \Tr (eur_rho_XB disXB rhoSrc M dim_eq) = 1.
Proof.
  move=> HM Hden.
  rewrite /eur_rho_XB /lftrace mx2hK (mxtrace_castmx_sq (esym (tenv_dim disXB)) _).
  pose Q : 'M[C]_(dim 'H[HL]_X * dim 'H[HL]_B) :=
    castmx (tenv_dim disXB, erefl) (@tenv_mxU R L HL X B).
  have HQ_t : Q^*t = castmx (erefl, tenv_dim disXB)
                    (@tenv_mxU R L HL X B)^*t.
  { rewrite /Q.
    exact: (@castmx_mx_mxT _ _ (@adjmx _) _ _ _ _
      (tenv_dim disXB, erefl)
      (@tenv_mxU R L HL X B)). }
  have HQtQ : Q^*t *m Q = 1%:M.
  { rewrite /Q HQ_t mcextra.castmx_mul.
    have HU : (@tenv_mxU R L HL X B)^*t
                *m (@tenv_mxU R L HL X B) = 1%:M.
    { have := unitarymxK
        (@tenv_mxU_adj_unitarymx R L HL X B disXB).
      by rewrite adjmxK. }
    rewrite HU.
    by case: _ / (tenv_dim disXB); rewrite castmx_id. }
  rewrite mxtrace_mulC mulmxA HQtQ mul1mx.
  rewrite (mxtrace_castmx_sq (etrans dim_eq (tenv_dim disXB)) _).
  rewrite (@rho_XB_trace na nb nc nx M rhoSrc HM).
  by have /den1mxP[_ /eqP ->] := Hden.
Qed.
(* path: eur:eur_rho_XB_den1 -> eur:entropic_uncertainty_relation -> *)
(*   bb84:entropic_uncertainty_relation_bb84 -> bb84:bb84_secret *)
Fact eur_rho_XB_den1 (X B : {set L}) (disXB : [disjoint X & B])
    (na nb nc nx : nat)
    (rhoSrc : 'M[C]_(na * nb * nc))
    (M : 'I_nx -> 'M[C]_na)
    (dim_eq : nx * nb = dim ('H[HL]_(X :|: B))) :
  is_povm_mx M ->
  rhoSrc \is den1mx ->
  eur_rho_XB disXB rhoSrc M dim_eq \is den1lf.
Proof.
  move=> HM Hden.
  apply/den1lfP; split.
  - exact: eur_rho_XB_psd.
  - exact: eur_rho_XB_tr1.
Qed.
(* path: eur:eur_rho_XB_tr_le1 -> eur:entropic_uncertainty_relation -> *)
(*   bb84:entropic_uncertainty_relation_bb84 -> bb84:bb84_secret *)
Lemma eur_rho_XB_tr_le1 (X B : {set L}) (disXB : [disjoint X & B])
    (na nb nc nx : nat)
    (rhoSrc : 'M[C]_(na * nb * nc))
    (M : 'I_nx -> 'M[C]_na)
    (dim_eq : nx * nb = dim ('H[HL]_(X :|: B))) :
  is_povm_mx M ->
  rhoSrc \is den1mx ->
  @complex.Re R
    (\Tr (eur_rho_XB disXB rhoSrc M dim_eq)) <= 1.
Proof.
  move=> HM Hden.
  by rewrite (eur_rho_XB_tr1 disXB dim_eq HM Hden) re_realid lexx.
Qed.
(* Product-coordinate view of the labelled EUR X post-measurement state. *)
(* path: eur:eur_rho_XB_biprod_mx -> bb84:eur_rho_XB_cq -> bb84:bb84_secret *)
Lemma eur_rho_XB_biprod_mx (X B : {set L}) (disXB : [disjoint X & B])
    (na nb nc nx : nat)
    (rhoSrc : 'M[C]_(na * nb * nc))
    (M : 'I_nx -> 'M[C]_na)
    (dim_eq : nx * nb = dim ('H[HL]_(X :|: B)))
    (dim_X : nx = dim ('H[HL]_X))
    (dim_B : nb = dim ('H[HL]_B)) :
  biprod_mx disXB (eur_rho_XB disXB rhoSrc M dim_eq) =
  castmx (f_equal2 muln dim_X dim_B, f_equal2 muln dim_X dim_B)
    (rho_XB M rhoSrc).
Proof.
  rewrite /eur_rho_XB /biprod_mx mx2hK.
  set Q := castmx _ (@tenv_mxU R L HL X B).
  have HQ_t : Q^*t = castmx (erefl, tenv_dim disXB)
                    (@tenv_mxU R L HL X B)^*t.
  { rewrite /Q.
    exact: (@castmx_mx_mxT _ _ (@adjmx _) _ _ _ _
      (tenv_dim disXB, erefl)
      (@tenv_mxU R L HL X B)). }
  have HQtQ : Q^*t *m Q = 1%:M.
  { rewrite /Q HQ_t mcextra.castmx_mul.
    have HU : (@tenv_mxU R L HL X B)^*t
                *m (@tenv_mxU R L HL X B) = 1%:M.
    { have := unitarymxK
        (@tenv_mxU_adj_unitarymx R L HL X B disXB).
      by rewrite adjmxK. }
    rewrite HU.
    by case: _ / (tenv_dim disXB); rewrite castmx_id. }
  rewrite castmx_comp.
  rewrite (eq_irrelevance
    (etrans (esym (tenv_dim disXB)) (tenv_dim disXB)) (erefl _)).
  rewrite castmx_id !mulmxA HQtQ mul1mx -mulmxA HQtQ mulmx1.
  by rewrite (eq_irrelevance (etrans dim_eq (tenv_dim disXB))
    (f_equal2 muln dim_X dim_B)).
Qed.
(* path: eur:eur_rho_ZC_psd -> bb84:bb84_secret *)
Lemma eur_rho_ZC_psd (Z C0 : {set L}) (disZC : [disjoint Z & C0])
    (na nb nc nz : nat)
    (rhoSrc : 'M[C]_(na * nb * nc))
    (N : 'I_nz -> 'M[C]_na)
    (dim_eq : nz * nc = dim ('H[HL]_(Z :|: C0))) :
  is_povm_mx N ->
  rhoSrc \is den1mx ->
  eur_rho_ZC disZC rhoSrc N dim_eq \is psdlf.
Proof.
  move=> HN Hden.
  rewrite /eur_rho_ZC qualifE mx2hK.
  apply: (@castmx_sq_psdmx R _ _ (esym (tenv_dim disZC))).
  have Hprod_psd :
      castmx (etrans dim_eq (tenv_dim disZC),
              etrans dim_eq (tenv_dim disZC)) (rho_ZC N rhoSrc) \is psdmx.
  { apply: (@castmx_sq_psdmx R _ _ (etrans dim_eq (tenv_dim disZC))).
    exact: denmx_psd (rho_ZC_subden HN (den1mx_den Hden)). }
  exact: psdmx_bimap_closed_gen Hprod_psd.
Qed.
(* path: eur:eur_rho_ZC_tr1 -> bb84:bb84_secret *)
Lemma eur_rho_ZC_tr1 (Z C0 : {set L}) (disZC : [disjoint Z & C0])
    (na nb nc nz : nat)
    (rhoSrc : 'M[C]_(na * nb * nc))
    (N : 'I_nz -> 'M[C]_na)
    (dim_eq : nz * nc = dim ('H[HL]_(Z :|: C0))) :
  is_povm_mx N ->
  rhoSrc \is den1mx ->
  \Tr (eur_rho_ZC disZC rhoSrc N dim_eq) = 1.
Proof.
  move=> HN Hden.
  rewrite /eur_rho_ZC /lftrace mx2hK (mxtrace_castmx_sq (esym (tenv_dim disZC)) _).
  pose Q : 'M[C]_(dim 'H[HL]_Z * dim 'H[HL]_C0) :=
    castmx (tenv_dim disZC, erefl) (@tenv_mxU R L HL Z C0).
  have HQ_t : Q^*t = castmx (erefl, tenv_dim disZC)
                    (@tenv_mxU R L HL Z C0)^*t.
  { rewrite /Q.
    exact: (@castmx_mx_mxT _ _ (@adjmx _) _ _ _ _
      (tenv_dim disZC, erefl)
      (@tenv_mxU R L HL Z C0)). }
  have HQtQ : Q^*t *m Q = 1%:M.
  { rewrite /Q HQ_t mcextra.castmx_mul.
    have HU : (@tenv_mxU R L HL Z C0)^*t
                *m (@tenv_mxU R L HL Z C0) = 1%:M.
    { have := unitarymxK
        (@tenv_mxU_adj_unitarymx R L HL Z C0 disZC).
      by rewrite adjmxK. }
    rewrite HU.
    by case: _ / (tenv_dim disZC); rewrite castmx_id. }
  rewrite mxtrace_mulC mulmxA HQtQ mul1mx.
  rewrite (mxtrace_castmx_sq (etrans dim_eq (tenv_dim disZC)) _).
  rewrite (@rho_ZC_trace na nb nc nz N rhoSrc HN).
  by have /den1mxP[_ /eqP ->] := Hden.
Qed.
(* path: eur:eur_rho_ZC_den1 -> *)
(*   bb84:bb84_secure *)
Lemma eur_rho_ZC_den1 (Z C0 : {set L}) (disZC : [disjoint Z & C0])
    (na nb nc nz : nat)
    (rhoSrc : 'M[C]_(na * nb * nc))
    (N : 'I_nz -> 'M[C]_na)
    (dim_eq : nz * nc = dim ('H[HL]_(Z :|: C0))) :
  is_povm_mx N ->
  rhoSrc \is den1mx ->
  eur_rho_ZC disZC rhoSrc N dim_eq \is den1lf.
Proof.
  move=> HN Hden.
  apply/den1lfP; split.
  - exact: eur_rho_ZC_psd.
  - exact: eur_rho_ZC_tr1.
Qed.
(* path: eur:eur_rho_ZC_tr_le1 -> eur:entropic_uncertainty_relation -> *)
(*   bb84:entropic_uncertainty_relation_bb84 -> bb84:bb84_secret *)
Lemma eur_rho_ZC_tr_le1 (Z C0 : {set L}) (disZC : [disjoint Z & C0])
    (na nb nc nz : nat)
    (rhoSrc : 'M[C]_(na * nb * nc))
    (N : 'I_nz -> 'M[C]_na)
    (dim_eq : nz * nc = dim ('H[HL]_(Z :|: C0))) :
  is_povm_mx N ->
  rhoSrc \is den1mx ->
  @complex.Re R
    (\Tr (eur_rho_ZC disZC rhoSrc N dim_eq)) <= 1.
Proof.
  move=> HN Hden.
  by rewrite (eur_rho_ZC_tr1 disZC dim_eq HN Hden) re_realid lexx.
Qed.
(* Product-coordinate view of the labelled EUR Z post-measurement state. *)
(* path: eur:eur_rho_ZC_biprod_mx -> eur:entropic_uncertainty_relation -> *)
(*   bb84:entropic_uncertainty_relation_bb84 -> bb84:bb84_secret *)
Lemma eur_rho_ZC_biprod_mx (Z C0 : {set L}) (disZC : [disjoint Z & C0])
    (na nb nc nz : nat)
    (rhoSrc : 'M[C]_(na * nb * nc))
    (N : 'I_nz -> 'M[C]_na)
    (dim_eq : nz * nc = dim ('H[HL]_(Z :|: C0)))
    (dim_Z : nz = dim ('H[HL]_Z))
    (dim_C : nc = dim ('H[HL]_C0)) :
  biprod_mx disZC (eur_rho_ZC disZC rhoSrc N dim_eq) =
  castmx (f_equal2 muln dim_Z dim_C, f_equal2 muln dim_Z dim_C)
    (rho_ZC N rhoSrc).
Proof.
  rewrite /eur_rho_ZC /biprod_mx mx2hK.
  set Q := castmx _ (@tenv_mxU R L HL Z C0).
  have HQ_t : Q^*t = castmx (erefl, tenv_dim disZC)
                    (@tenv_mxU R L HL Z C0)^*t.
  { rewrite /Q.
    exact: (@castmx_mx_mxT _ _ (@adjmx _) _ _ _ _
      (tenv_dim disZC, erefl)
      (@tenv_mxU R L HL Z C0)). }
  have HQtQ : Q^*t *m Q = 1%:M.
  { rewrite /Q HQ_t mcextra.castmx_mul.
    have HU : (@tenv_mxU R L HL Z C0)^*t
                *m (@tenv_mxU R L HL Z C0) = 1%:M.
    { have := unitarymxK
        (@tenv_mxU_adj_unitarymx R L HL Z C0 disZC).
      by rewrite adjmxK. }
    rewrite HU.
    by case: _ / (tenv_dim disZC); rewrite castmx_id. }
  rewrite castmx_comp.
  rewrite (eq_irrelevance
    (etrans (esym (tenv_dim disZC)) (tenv_dim disZC)) (erefl _)).
  rewrite castmx_id !mulmxA HQtQ mul1mx -mulmxA HQtQ mulmx1.
  by rewrite (eq_irrelevance (etrans dim_eq (tenv_dim disZC))
    (f_equal2 muln dim_Z dim_C)).
Qed.
End LabelledPostMeasurement.
(* Matrix CQ structure of the X post-measurement state.                  *)
(* Paper: Tomamichel & Renner (PRL 106, 110506 (2011); arXiv:1009.2015) *)
(*   — ρ_XB definition (text after Theorem 1).                          *)
(* math: rho_XB = Σ_x |x><x| ⊗ τ_B^x.                                   *)
(* path: eur:rho_XB_offdiag_mx -> bb84:eur_rho_XB_cq -> bb84:bb84_secret *)
Lemma rho_XB_offdiag_mx {na nb nc nx : nat}
    (M : 'I_nx -> 'M[C]_na) (rhoABC : 'M[C]_(na * nb * nc))
    (x x' : 'I_nx) :
  x' != x ->
  ((delta_mx x x : 'M[C]_nx) *t (1%:M : 'M[C]_nb)) *m
    rho_XB M rhoABC *m
  ((delta_mx x' x' : 'M[C]_nx) *t (1%:M : 'M[C]_nb)) = 0.
Proof.
  move=> Hx'x.
  rewrite /rho_XB mulmx_sumr mulmx_suml.
  apply: big1 => y _.
  rewrite !tensmx_mul !mulmx1.
  case Hxy : (x == y).
  - have Hyx' : y != x'.
    {
      apply/eqP => Hyx'.
      move: Hx'x.
      by rewrite -Hyx' eq_sym Hxy.
    }
    by rewrite mul_delta_mx_cond Hxy
      (@mul_delta_mx_0 C nx nx nx y x' x x' Hyx') tens0mx.
  - have Hxy_ne : x != y by rewrite Hxy.
    by rewrite (@mul_delta_mx_0 C nx nx nx x y x y Hxy_ne) mul0mx tens0mx.
Qed.
(* Paper: Tomamichel & Renner (PRL 106, 110506 (2011); arXiv:1009.2015),  *)
(*   "Smooth Entropies", property (i): for a trace-non-increasing CP map  *)
(*   E, ρ ≈_ε τ implies E(ρ) ≈_ε E(τ). Here ρ_XB is such a CPTN map of    *)
(*   ρ_{ABC}.                                                              *)
(* ρ_XB / ρ_ZC (as CQ-TPCP channels) contract the purified distance.     *)
(* rho_XB_pur_dist_contract *)
(* infra: no tex label — fundamental & reusable (mathcomp-style) *)
(* consumer: rho_XB_pur_dist_contract is used downstream by the BB84 secrecy proof. *)
(* path: eur:rho_XB_pur_dist_contract -> *)
(*   eur:entropic_uncertainty_relation -> *)
(*   eur:entropic_uncertainty_relation -> *)
(*   bb84:entropic_uncertainty_relation_bb84 -> bb84:bb84_secret *)
Lemma rho_XB_pur_dist_contract {na nb nc nx : nat}
    (M : 'I_nx -> 'M[C]_na)
    (rho1 rho2 : 'M[C]_(na * nb * nc)) :
  is_povm_mx M ->
  (0 < na * nb * nc)%N -> (0 < nx * nb)%N ->
  rho1 \is denmx -> rho2 \is denmx ->
  pur_dist_mx (rho_XB M rho1) (rho_XB M rho2) <= pur_dist_mx rho1 rho2.
Proof.
  move=> HM Hin Hout Hrho1 Hrho2.
  (* TeX property (i): the post-measurement-and-discarding map is CPTP. *)
  pose K (xac : 'I_nx * 'I_na * 'I_nc) :
      'M[C]_(nx * nb, na * nb * nc) :=
    \matrix_(r, s)
      let xr_b := mxtens_unindex r in
      let ab_c := mxtens_unindex s in
      let a0_b0 := mxtens_unindex ab_c.1 in
      ((xr_b.1 == xac.1.1)%:R : C) *
      ((xr_b.2 == a0_b0.2)%:R : C) *
      ((ab_c.2 == xac.2)%:R : C) *
      sqrtmx (M xac.1.1) xac.1.2 a0_b0.1.
  have HsqrtC : forall x a1 a2,
      ((sqrtmx (M x) a1 a2)^*)%C = sqrtmx (M x) a2 a1.
  {
    move=> x a1 a2.
    have /hermmxP Hs : sqrtmx (M x) \is hermmx.
    {
      have HMx : M x \is psdmx by exact: is_povm_mx_psd HM.
      exact: sqrtmx_herm (psdmx_herm HMx).
    }
    by rewrite {2}Hs mxE_adj.
  }
  have Haction : forall rho : 'M[C]_(na * nb * nc),
      \sum_(xac : 'I_nx * 'I_na * 'I_nc)
        K xac *m rho *m (K xac)^*t = rho_XB M rho.
  {
    move=> rho.
    have ptrace2E' : forall s t (B : 'M[C]_(s * t)) r1 r2,
        (ptrace2 B) r1 r2 =
        \sum_(k0 : 'I_t) B (mxtens_index (r1, k0)) (mxtens_index (r2, k0)).
    {
      move=> s0 t0 B r1 r2; rewrite ptrace2E1 ptrace1E.
      by apply: eq_bigr => k0 _; rewrite mxE !mxtens_indexK.
    }
    apply/matrixP=> r s.
    case: (mxtens_indexP r)=> xr br.
    case: (mxtens_indexP s)=> xs bs.
    rewrite /rho_XB !summxE.
    under [LHS]eq_bigr => xac _ do rewrite mxE.
    under [LHS]eq_bigr => xac _ do
      under eq_bigr => p _ do rewrite [X in X * _]mxE.
    rewrite pair_bigV /= pair_bigV /=.
    under [LHS]eq_bigr => x _ do
      under eq_bigr => a _ do
        under eq_bigr => c _ do rewrite mxtens_index_pairV.
    under [LHS]eq_bigr => x _ do
      under eq_bigr => a _ do
        under eq_bigr => c _ do
          rewrite mxtens_index_pairV.
    under [LHS]eq_bigr => x _ do
      under eq_bigr => a _ do
        under eq_bigr => c _ do
          under eq_bigr => ap _ do
            under eq_bigr => bp _ do
              under eq_bigr => cp _ do rewrite mxtens_index_pairV.
    under [LHS]eq_bigr => x _ do
      under eq_bigr => a _ do
        under eq_bigr => c _ do
          under eq_bigr => ap _ do
            under eq_bigr => bp _ do
              under eq_bigr => cp _ do rewrite mxtens_index_pairV.
    under [LHS]eq_bigr => x _ do
      under eq_bigr => a _ do
        under eq_bigr => c _ do
          under eq_bigr => ap _ do
            under eq_bigr => bp _ do
              under eq_bigr => cp _ do
                under eq_bigr => aq _ do
                  under eq_bigr => bq _ do
                    under eq_bigr => cq _ do
                      rewrite /K [X in X * rho _ _]mxE !mxtens_indexK /=.
    under [LHS]eq_bigr => x _ do
      under eq_bigr => a _ do
        under eq_bigr => c _ do
          under eq_bigr => ap _ do
            under eq_bigr => bp _ do
              under eq_bigr => cp _ do
                rewrite mxE_adj /K mxE !mxtens_indexK /=.
    rewrite /=.
    under [LHS]eq_bigr => x _ do
      under eq_bigr => a _ do
        under eq_bigr => c _ do
          under eq_bigr => ap _ do
            under eq_bigr => bp _ do
              under eq_bigr => cp _ do
                rewrite !rmorphM /= !conjC_nat.
    under [RHS]eq_bigr => k _ do rewrite tensmxE ?mxtens_indexK /=.
    under [RHS]eq_bigr => k _ do rewrite ptrace1E.
    under [RHS]eq_bigr => k _ do
      under eq_bigr => a0 _ do rewrite ptrace2E'.
    under [RHS]eq_bigr => k _ do
      under eq_bigr => a0 _ do
        under eq_bigr => c0 _ do rewrite mxE.
    under [RHS]eq_bigr => k _ do
      under eq_bigr => a0 _ do
        under eq_bigr => c0 _ do
          under eq_bigr => j0 _ do rewrite [X in X * _]mxE.
    under [RHS]eq_bigr => k _ do
      under eq_bigr => a0 _ do
        under eq_bigr => c0 _ do rewrite mxtens_index_pairV.
    under [RHS]eq_bigr => k _ do
      under eq_bigr => a0 _ do
        under eq_bigr => c0 _ do rewrite mxtens_index_pairV.
    under [RHS]eq_bigr => k _ do
      under eq_bigr => a0 _ do
        under eq_bigr => c0 _ do
          under eq_bigr => ap _ do
            under eq_bigr => bp _ do
              under eq_bigr => cp _ do rewrite mxtens_index_pairV.
    under [RHS]eq_bigr => k _ do
      under eq_bigr => a0 _ do
        under eq_bigr => c0 _ do
          under eq_bigr => ap _ do
            under eq_bigr => bp _ do
              under eq_bigr => cp _ do rewrite mxtens_index_pairV.
    under [RHS]eq_bigr => k _ do
      under eq_bigr => a0 _ do
        under eq_bigr => c0 _ do
          under eq_bigr => ap _ do
            under eq_bigr => bp _ do
              under eq_bigr => cp _ do
                under eq_bigr => aq _ do
                  under eq_bigr => bq _ do
                    under eq_bigr => cq _ do
                      rewrite !tensmxE ?mxtens_indexK /=.
    under [RHS]eq_bigr => k _ do rewrite mxE.
    under [RHS]eq_bigr => k _ do
      under eq_bigr => a0 _ do
        under eq_bigr => c0 _ do
          under eq_bigr => ap _ do
            under eq_bigr => bp _ do
              under eq_bigr => cp _ do
                under eq_bigr => aq _ do
                  under eq_bigr => bq _ do
                    under eq_bigr => cq _ do
                      rewrite [1%:M br bq]mxE [1%:M c0 cq]mxE.
    under [RHS]eq_bigr => k _ do
      under eq_bigr => a0 _ do
        under eq_bigr => c0 _ do
          under eq_bigr => ap _ do
            under eq_bigr => bp _ do
              under eq_bigr => cp _ do
                rewrite [X in _ * X]tensmxE ?mxtens_indexK /=.
    under [RHS]eq_bigr => k _ do
      under eq_bigr => a0 _ do
        under eq_bigr => c0 _ do
          under eq_bigr => ap _ do
            under eq_bigr => bp _ do
              under eq_bigr => cp _ do
                rewrite [X in X * 1%:M cp c0]tensmxE ?mxtens_indexK /=.
    under [RHS]eq_bigr => k _ do
      under eq_bigr => a0 _ do
        under eq_bigr => c0 _ do
          under eq_bigr => ap _ do
            under eq_bigr => bp _ do
              under eq_bigr => cp _ do
                rewrite [1%:M bp bs]mxE [1%:M cp c0]mxE.
    under [RHS]eq_bigr => k _ do rewrite !mulr_sumr.
    under [RHS]eq_bigr => k _ do
      under eq_bigr => a0 _ do rewrite !mulr_sumr.
    under [RHS]eq_bigr => k _ do
      under eq_bigr => a0 _ do
        under eq_bigr => c0 _ do rewrite !mulr_sumr.
    under [RHS]eq_bigr => k _ do
      under eq_bigr => a0 _ do
        under eq_bigr => c0 _ do
          under eq_bigr => ap _ do rewrite !mulr_sumr.
    under [RHS]eq_bigr => k _ do
      under eq_bigr => a0 _ do
        under eq_bigr => c0 _ do
          under eq_bigr => ap _ do
            under eq_bigr => bp _ do rewrite !mulr_sumr.
    under [LHS]eq_bigr => x _ do
      under eq_bigr => a _ do
        under eq_bigr => c _ do
          under eq_bigr => ap _ do
            under eq_bigr => bp _ do
              under eq_bigr => cp _ do
                under eq_bigr => aq _ do
                  under eq_bigr => bq _ do
                    under eq_bigr => cq _ do rewrite -!mulrA.
    under [LHS]eq_bigr => x _ do
      under eq_bigr => a _ do
        under eq_bigr => c _ do
          under eq_bigr => ap _ do
            under eq_bigr => bp _ do
              under eq_bigr => cp _ do
                under eq_bigr => aq _ do
                  under eq_bigr => bq _ do rewrite -mulr_sumr.
    under [LHS]eq_bigr => x _ do
      under eq_bigr => a _ do
        under eq_bigr => c _ do
          under eq_bigr => ap _ do
            under eq_bigr => bp _ do
              under eq_bigr => cp _ do
                under eq_bigr => aq _ do rewrite -mulr_sumr.
    under [LHS]eq_bigr => x _ do
      under eq_bigr => a _ do
        under eq_bigr => c _ do
          under eq_bigr => ap _ do
            under eq_bigr => bp _ do
              under eq_bigr => cp _ do rewrite -mulr_sumr.
    apply: eq_bigr => x _; apply: eq_bigr => a _; apply: eq_bigr => c _.
    apply: eq_bigr => ap _; apply: eq_bigr => bp _; apply: eq_bigr => cp _.
    have Hinner :
      \sum_(i < na)
        \sum_(i0 < nb)
          \sum_(i1 < nc)
            (br == i0)%:R *
            ((i1 == c)%:R *
              (sqrtmx (M x) a i *
                rho (mxtens_index (mxtens_index (i, i0), i1))
                  (mxtens_index (mxtens_index (ap, bp), cp)))) =
      \sum_(aq < na)
        \sum_(bq < nb)
          \sum_(cq < nc)
            sqrtmx (M x) a aq * (br == bq)%:R * (c == cq)%:R *
            rho (mxtens_index (mxtens_index (aq, bq), cq))
              (mxtens_index (mxtens_index (ap, bp), cp)).
    {
      apply: eq_bigr => aq _; apply: eq_bigr => bq _.
      apply: eq_bigr => cq _.
      rewrite [c == cq]eq_sym.
      by rewrite mulrA mulrACA [(_ : C) * sqrtmx (M x) a aq]mulrC !mulrA.
    }
    rewrite Hinner [bp == bs]eq_sym.
    case Hxr: (xr == x); case Hxs: (xs == x); rewrite /=.
    - have HsqrtC_ap :
          conjC (sqrtmx (M x) a ap) = sqrtmx (M x) ap a.
      { exact: HsqrtC x a ap. }
      by rewrite HsqrtC_ap !mul1r [(_ : C) * sqrtmx (M x) ap a]mulrC
        !mulrA.
    - by rewrite ?mul0r ?mulr0.
    - by rewrite ?mul0r ?mulr0.
    - by rewrite ?mul0r ?mulr0.
  }
  have HTP :
      \sum_(xac : 'I_nx * 'I_na * 'I_nc) (K xac)^*t *m K xac = 1%:M.
  {
    apply/matrixP=> p q.
    case: (mxtens_indexP p)=> abp cp.
    case: (mxtens_indexP q)=> abq cq.
    case: (mxtens_indexP abp)=> ap bp.
    case: (mxtens_indexP abq)=> aq bq.
    rewrite !summxE.
    under [LHS]eq_bigr => xac _ do rewrite !mxE.
    under [LHS]eq_bigr => xac _ do rewrite mxtens_index_pairV.
    under [LHS]eq_bigr => xac _ do
      under eq_bigr => i _ do
        under eq_bigr => j _ do rewrite mxE_adj.
    under [LHS]eq_bigr => xac _ do
      under eq_bigr => i _ do
        under eq_bigr => j _ do
          rewrite /K [X in (X^*)%C * _]mxE [X in _ * X]mxE
            !mxtens_indexK /=.
    rewrite /= pair_bigV /= pair_bigV /=.
    under [LHS]eq_bigr => x _ do
      under eq_bigr => a _ do
        under eq_bigr => c _ do
          under eq_bigr => i _ do
            under eq_bigr => b _ do
              rewrite !rmorphM /= ?conjC_nat.
    transitivity
      (\sum_(x < nx) \sum_(a < na) \sum_(c < nc)
         \sum_(b < nb)
           (b == bp)%:R * (cp == c)%:R * sqrtmx (M x) ap a *
           ((b == bq)%:R * (cq == c)%:R * sqrtmx (M x) a aq)).
    {
      apply: eq_bigr => x _; apply: eq_bigr => a _; apply: eq_bigr => c _.
      rewrite (bigD1 x) //= eqxx.
      rewrite [X in _ + X]big1 ?addr0.
      - apply: eq_bigr => b _.
        rewrite (HsqrtC x a ap) /= ?conjC1.
        by case: (b == bp); case: (cp == c);
          rewrite ?conjC1 ?conjC0 /= ?mul0r ?mulr0 ?mul1r;
          simpc; rewrite ?mul0r ?mulr0 ?mul1r.
      - move=> i Hix.
        rewrite (negPf Hix).
        by rewrite big1 // => b _; simpc; rewrite ?mul0r ?mulr0.
    }
    transitivity
      (\sum_(x < nx) \sum_(a < na) \sum_(c < nc)
         (cp == c)%:R * sqrtmx (M x) ap a *
         ((bp == bq)%:R * (cq == c)%:R * sqrtmx (M x) a aq)).
    {
      apply: eq_bigr => x _; apply: eq_bigr => a _; apply: eq_bigr => c _.
      rewrite (bigD1 bp) //= eqxx.
      rewrite [X in _ + X]big1 ?addr0.
      - by rewrite !mul1r.
      - move=> b Hbp.
        by rewrite (negPf Hbp) !mul0r.
    }
    transitivity
      (\sum_(x < nx) \sum_(a < na)
         (bp == bq)%:R * (cq == cp)%:R *
         (sqrtmx (M x) ap a * sqrtmx (M x) a aq)).
    {
      apply: eq_bigr => x _; apply: eq_bigr => a _.
      rewrite (bigD1 cp) //= eqxx.
      rewrite [X in _ + X]big1 ?addr0.
      - by rewrite mul1r mulrCA.
      - move=> c Hcp.
        by rewrite eq_sym (negPf Hcp) !mul0r.
    }
    transitivity
      (\sum_(x < nx)
         (bp == bq)%:R * (cq == cp)%:R * M x ap aq).
    {
      apply: eq_bigr => x _.
      transitivity ((bp == bq)%:R * (cq == cp)%:R *
        \sum_(a < na) (sqrtmx (M x) ap a * sqrtmx (M x) a aq)).
      {
        rewrite mulr_sumr.
        by apply: eq_bigr => a _; rewrite mulrA.
      }
      have HMx : M x \is psdmx by exact: is_povm_mx_psd HM.
      congr (_ * _).
      have /matrixP /(_ ap aq) Hsq := sqrtmxK HMx.
      by move: Hsq; rewrite mxE => <-.
    }
    transitivity ((bp == bq)%:R * (cq == cp)%:R *
        \sum_(x < nx) M x ap aq).
    {
      rewrite mulr_sumr.
      by [].
    }
    transitivity (((bp == bq)%:R : C) * ((cq == cp)%:R : C) *
      ((ap == aq)%:R : C)).
    {
      congr (_ * _).
      have /matrixP /(_ ap aq) Hsum := is_povm_mx_sum HM.
      by rewrite -summxE Hsum mxE.
    }
    rewrite mxE (can_eq (@mxtens_indexK _ _)) -pair_eqE /=.
    rewrite (can_eq (@mxtens_indexK _ _)) -pair_eqE /= [cq == cp]eq_sym.
    by case: (ap == aq); case: (bp == bq); case: (cp == cq);
      rewrite /= ?mul0r ?mulr0 ?mul1r ?mulr1.
  }
  rewrite -!(Haction _).
  exact: pur_dist_mx_cptn_kraus_contract Hin Hout Hrho1 Hrho2 HTP.
Qed.
(* ================================================================== *)
(* Core EUR proof lemmas used on the smooth uncertainty route.          *)
(* ================================================================== *)
Section EurCoreLemmas.
Variable (na nb nc : nat).
(* Extension of purified-distance proximity to arbitrary extensions     *)
(* Paper: Tomamichel & Renner (PRL 106, 110506 (2011); arXiv:1009.2015),*)
(*   "Smooth Entropies", property (ii) (purified-distance facts).       *)
(* math: Let ρ_AB be a fixed extension of ρ_A. If ρ_A ≃_ε τ_A, then    *)
(*   there exists an extension τ_AB of τ_A with ρ_AB ≃_ε τ_AB.          *)
(*   Furthermore, if ρ_AB is pure and |supp(τ_A)| ≤ dim B, then τ_AB    *)
(*   can be chosen pure. In matrix form, the support bound is expressed  *)
(*   by `\rank tauA <= dim B`; the pure branch also threads              *)
(*   `tauA != 0`, matching the matrix Uhlmann theorem already available  *)
(*   in `utils/dist/fid.v`.                                              *)
(* Proof: combination of dual:cor:purified-ext (existence of extension *)
(*   at same pd) and dual:lemma:purified-Uhlmann (pure-state variant). *)
(* path: eur:eur_ii -> eur:smooth_hmax_mx_rho_ZC_purif_dpi -> *)
(*   eur:entropic_uncertainty_relation -> *)
(*   eur:entropic_uncertainty_relation -> *)
(*   bb84:entropic_uncertainty_relation_bb84 -> bb84:bb84_secret *)
Lemma eur_ii (eps : R)
    (rhoA : 'M[C]_na) (rhoAB : 'M[C]_(na * nb))
    (tauA : 'M[C]_na) :
	  rhoAB \is denmx -> rhoAB != 0 ->
	  ptrace2 rhoAB = rhoA ->
	  (tauA \is denmx) &&
	    (Num.sqrt (1 - (gfidelity tauA rhoA)^2) <= eps) ->
  (exists tauAB : 'M[C]_(na * nb),
      tauAB \is denmx /\
      ptrace2 tauAB = tauA /\
      pur_dist_mx rhoAB tauAB <= eps)
  /\
  (\rank rhoAB = 1%N ->
   (\rank tauA <= nb)%N ->
   tauA != 0 ->
   exists tauAB : 'M[C]_(na * nb),
     tauAB \is denmx /\ \rank tauAB = 1%N /\
     ptrace2 tauAB = tauA /\ pur_dist_mx rhoAB tauAB <= eps).
Proof.
  move=> HrhoAB_den HrhoAB_nz Hptr Hcl.
  have /denmxP [HrhoAB_psd Htr_rhoAB_le] := HrhoAB_den.
  have Htr_AB_eq_A : \tr rhoAB = \tr rhoA by rewrite -Hptr -tr_ptrace2.
  have HrhoA_den : rhoA \is denmx.
  {
    apply/denmxP; split.
    - by rewrite -Hptr; exact: ptrace2_psd HrhoAB_psd.
    - by rewrite -Htr_AB_eq_A.
  }
  have HrhoA_psd : rhoA \is psdmx := denmx_psd HrhoA_den.
    have [HtauA_den Hpd_tau_rhoA] :
        tauA \is denmx /\ Num.sqrt (1 - (gfidelity tauA rhoA)^2) <= eps.
    {
      by case/andP: Hcl.
    }
  have HtauA_psd : tauA \is psdmx := denmx_psd HtauA_den.
  have Hpd_rhoA_tau : Num.sqrt (1 - (gfidelity rhoA tauA)^2) <= eps.
  {
    rewrite (gfid_sym_mx HrhoA_psd HtauA_psd).
    exact: Hpd_tau_rhoA.
  }
  have Hptrace2_regroup :
      forall m n k (A0 : 'M[C]_((m * n) * k)),
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
  split.
  - case Htau0 : (tauA == 0).
      + exists (0 : 'M[C]_(na * nb)); split.
        * exact: denmx0.
        * split.
          -- by move/eqP: Htau0 => ->; rewrite linear0.
          -- move/eqP: Htau0 => HtauA0.
             (* Subnormalised gfidelity-with-zero: gfidelity ρ 0 =
                sqrt(Re(1 - Tr ρ)). For den1mx this collapses to 0;
                for denmx the value is preserved on both rhoAB and rhoA
                sides via Tr rhoAB = Tr rhoA. *)
             have Hgfid_eq : gfidelity rhoAB 0 = gfidelity rhoA 0.
             {
               have HfAB :
                   @complex.Re R
                     (trnorm (sqrtmx rhoAB *m sqrtmx (0 : 'M[C]_(na * nb)))) = 0
                 by rewrite sqrtmx0 mulmx0 trnorm0 raddf0.
               have HfA :
                   @complex.Re R (trnorm (sqrtmx rhoA *m sqrtmx (0 : 'M[C]_na))) = 0
                 by rewrite sqrtmx0 mulmx0 trnorm0 raddf0.
               rewrite (alt_gfid_gen HrhoAB_psd (@psdmx0 C (na * nb))) HfAB.
               rewrite (alt_gfid_gen HrhoA_psd (@psdmx0 C na)) HfA.
               by rewrite !mxtrace0 Htr_AB_eq_A.
             }
             have Hpd_rhoA0 : Num.sqrt (1 - (gfidelity rhoA 0)^2) <= eps.
             { by rewrite HtauA0 in Hpd_rhoA_tau. }
             by rewrite /pur_dist_mx Hgfid_eq.
    + have HtauA_nz : tauA != 0 by rewrite Htau0.
      have [rhoABC0 [HrhoABC0_den [HptrAB HrhoABC0_rank1]]] :=
      purification_mx_exists HrhoAB_den HrhoAB_nz (leqnn (na * nb)).
      pose rhoABC : 'M[C]_(na * (nb * (na * nb))) :=
        castmx_sq (esym (mulnA na nb (na * nb))) rhoABC0.
      have HrhoABC_den : rhoABC \is denmx.
      {
        apply/denmxP; split.
        - exact: castmx_sq_psdmx (denmx_psd HrhoABC0_den).
        - rewrite mxtrace_castmx_sq tr_ptrace2 HptrAB.
          by have /denmxP[_ ?] := HrhoAB_den.
      }
      have HrhoABC_rank1 : \rank rhoABC = 1%N.
      { by rewrite /rhoABC /castmx_sq mxrank_cast HrhoABC0_rank1. }
      have HrhoABC_ptr : ptrace2 rhoABC = rhoA.
      {
        rewrite /rhoABC Hptrace2_regroup HptrAB.
        exact: Hptr.
      }
      have HrhoA_nz : rhoA != 0.
      {
        apply/negP => /eqP HrhoA0.
        have Htr_AB_zero : \tr rhoAB = 0
          by rewrite Htr_AB_eq_A HrhoA0 mxtrace0.
        have : rhoAB == 0
          by rewrite -(psdmx_trace_eq0 HrhoAB_psd); apply/eqP.
        by move/eqP=> H; move/eqP: HrhoAB_nz; rewrite H.
      }
        have Hna_pos : (0 < na)%N.
        {
          have HrhoA_rank_pos : (0 < \rank rhoA)%N.
          { by rewrite lt0n mxrank_eq0 HrhoA_nz. }
          exact: leq_trans HrhoA_rank_pos (rank_leq_row rhoA).
        }
        have Hnb_pos : (0 < nb)%N.
        {
          have Hdim_pos : (0 < na * nb)%N.
          {
            have HrhoAB_rank_pos : (0 < \rank rhoAB)%N.
            { by rewrite lt0n mxrank_eq0 HrhoAB_nz. }
            exact: leq_trans HrhoAB_rank_pos (rank_leq_row rhoAB).
          }
          by move: Hdim_pos; rewrite muln_gt0 => /andP[_].
        }
        have Hnab_pos : (0 < na * nb)%N by rewrite muln_gt0 Hna_pos Hnb_pos.
        have HtauA_rank_env : (\rank tauA <= nb * (na * nb))%N.
        {
          have Hna_le_nab : (na <= na * nb)%N.
          {
            exact: leq_pmulr Hnb_pos.
          }
          have Hnab_le_env : (na * nb <= nb * (na * nb))%N.
          {
            exact: leq_pmull Hnb_pos.
          }
          have Hna_le_env : (na <= nb * (na * nb))%N
            by exact: leq_trans Hna_le_nab Hnab_le_env.
          exact: leq_trans (rank_leq_row tauA) Hna_le_env.
        }
      have [theta [Htheta_den [Htheta_rank1 [Htheta_ptr Htheta_fid]]]] :=
        fid_iii_uhl_mx HrhoABC_den HrhoABC_rank1 HrhoABC_ptr
          HtauA_den HtauA_nz HtauA_rank_env.
        pose theta0 : 'M[C]_((na * nb) * (na * nb)) :=
          castmx_sq (mulnA na nb (na * nb)) theta.
        have Hpd_cast :
            Num.sqrt (1 - (gfidelity rhoABC0 theta0)^2) =
            Num.sqrt (1 - (gfidelity rhoABC theta)^2).
        {
          have Htheta0K :
              castmx (esym (mulnA na nb (na * nb)),
                     esym (mulnA na nb (na * nb))) theta0 = theta.
          { by rewrite /theta0 /castmx_sq castmxK. }
          have Hgfid_cast :
              gfidelity rhoABC0 theta0 = gfidelity rhoABC theta.
          {
            move: (gfid_cast_mx (esym (mulnA na nb (na * nb))) rhoABC0 theta0).
            rewrite /rhoABC /castmx_sq Htheta0K.
            by [].
          }
          by rewrite Hgfid_cast.
        }
        pose tauAB : 'M[C]_(na * nb) := ptrace2 theta0.
        have HtauAB_den : tauAB \is denmx.
        {
          move/denmxP: Htheta_den => [Htheta_psd' Htheta_tr].
          apply: ptrace2_denmx.
          apply/denmxP; split.
          - exact: castmx_sq_psdmx Htheta_psd'.
          - by rewrite mxtrace_castmx_sq.
        }
      have HtauAB_ptr : ptrace2 tauAB = tauA.
      {
          rewrite /tauAB.
          rewrite -[ptrace2 (ptrace2 (castmx_sq (mulnA na nb (na * nb)) theta))]
                  (Hptrace2_regroup _ _ _ (castmx_sq (mulnA na nb (na * nb)) theta)).
          have -> :
              castmx_sq (esym (mulnA na nb (na * nb)))
                (castmx_sq (mulnA na nb (na * nb)) theta) = theta.
          { by rewrite /castmx_sq castmxK. }
          exact: Htheta_ptr.
        }
      have Htheta_psd : theta \is psdmx := denmx_psd Htheta_den.
      have HrhoABC_psd : rhoABC \is psdmx := denmx_psd HrhoABC_den.
      have HrhoABC0_psd : rhoABC0 \is psdmx := denmx_psd HrhoABC0_den.
        have Htheta0_psd : theta0 \is psdmx :=
          castmx_sq_psdmx (mulnA na nb (na * nb)) Htheta_psd.
      have HtauAB_psd : tauAB \is psdmx := denmx_psd HtauAB_den.
        have Hpd_rhoABC_theta :
            Num.sqrt (1 - (gfidelity rhoABC theta)^2) =
            Num.sqrt (1 - (gfidelity rhoA tauA)^2).
        {
          rewrite (alt_gfid_gen HrhoABC_psd Htheta_psd).
          rewrite (alt_gfid_gen HrhoA_psd HtauA_psd).
          have HrhoABC_tr : \tr rhoABC = \tr rhoA by rewrite tr_ptrace2 HrhoABC_ptr.
          have Htheta_tr : \tr theta = \tr tauA by rewrite tr_ptrace2 Htheta_ptr.
          rewrite /gfidelity in Htheta_fid.
          by rewrite Htheta_fid HrhoABC_tr Htheta_tr.
        }
        have Hpd_mono :
            Num.sqrt (1 - (gfidelity rhoAB tauAB)^2) <=
            Num.sqrt (1 - (gfidelity rhoABC0 theta0)^2).
        {
          have Hfid_mono :=
          @gfid_ptr_mono_mx R (na * nb) (na * nb)
              rhoABC0 theta0 Hnab_pos HrhoABC0_psd Htheta0_psd.
          have Hfid_mono' :
              gfidelity rhoABC0 theta0 <= gfidelity rhoAB tauAB.
          {
            rewrite HptrAB /tauAB in Hfid_mono.
            exact: Hfid_mono.
          }
          have Hfid_ge0 := gfid_ge0_mx HrhoABC0_psd Htheta0_psd.
          have Hpt_ge0 := gfid_ge0_mx HrhoAB_psd HtauAB_psd.
          have Hsq_mono :
              (gfidelity rhoABC0 theta0)^2 <= (gfidelity rhoAB tauAB)^2.
          {
            change (gfidelity rhoABC0 theta0 * gfidelity rhoABC0 theta0 <=
                    gfidelity rhoAB tauAB * gfidelity rhoAB tauAB).
            have Hstep1 :
                gfidelity rhoABC0 theta0 * gfidelity rhoABC0 theta0 <=
                gfidelity rhoAB tauAB * gfidelity rhoABC0 theta0.
            {
              rewrite [gfidelity rhoAB tauAB * gfidelity rhoABC0 theta0]mulrC.
              apply: (ler_wpM2l Hfid_ge0).
              exact: Hfid_mono'.
            }
            have Hstep2 :
                gfidelity rhoAB tauAB * gfidelity rhoABC0 theta0 <=
                gfidelity rhoAB tauAB * gfidelity rhoAB tauAB.
            {
              apply: (ler_wpM2l Hpt_ge0).
              exact: Hfid_mono'.
            }
            exact: le_trans Hstep1 Hstep2.
          }
          apply: ler_wsqrtr.
          apply: lerB; first exact: lexx.
          exact: Hsq_mono.
        }
        exists tauAB; split=> //.
        split; first exact: HtauAB_ptr.
        apply: (le_trans Hpd_mono).
        rewrite Hpd_cast Hpd_rhoABC_theta.
        exact: Hpd_rhoA_tau.
  - move=> HrhoAB_rank1 HtauA_rank HtauA_nz.
    have [tauAB [HtauAB_den [HtauAB_rank1 [HtauAB_ptr HtauAB_fid]]]] :=
      fid_iii_uhl_mx HrhoAB_den HrhoAB_rank1 Hptr
        HtauA_den HtauA_nz HtauA_rank.
    exists tauAB; split=> //.
      split; first exact: HtauAB_rank1.
      split; first exact: HtauAB_ptr.
      have HtauAB_psd : tauAB \is psdmx := denmx_psd HtauAB_den.
      have HtauAB_tr : \tr tauAB = \tr tauA by rewrite tr_ptrace2 HtauAB_ptr.
      have Hpd_rhoAB_tauAB :
          Num.sqrt (1 - (gfidelity rhoAB tauAB)^2) =
          Num.sqrt (1 - (gfidelity rhoA tauA)^2).
      {
        rewrite (alt_gfid_gen HrhoAB_psd HtauAB_psd) (alt_gfid_gen HrhoA_psd HtauA_psd).
        rewrite /gfidelity in HtauAB_fid.
        by rewrite HtauAB_fid Htr_AB_eq_A HtauAB_tr.
      }
      rewrite /pur_dist_mx Hpd_rhoAB_tauAB.
      exact: Hpd_rhoA_tau.
Qed.
End EurCoreLemmas.
(* ================================================================== *)
(* Stage-2 proof infrastructure                                       *)
(* ================================================================== *)
Section PurificationReshape.
(* tex: castmx is a matrix isomorphism preserving denmx.               *)
(* path: eur:purif_reshape_denmx -> eur:entropic_uncertainty_relation -> *)
(*   eur:entropic_uncertainty_relation -> *)
(*   bb84:entropic_uncertainty_relation_bb84 -> bb84:bb84_secret *)
Fact purif_reshape_denmx {na nb nc nd : nat}
    (rho : 'M[C]_(na * nb * nc * nd)) :
  rho \is denmx -> purif_reshape rho \is denmx.
Proof.
  by rewrite /purif_reshape cast_qualifier_diag.
Qed.
(* purif_reshape_rank *)
(* infra: no tex label — fundamental & reusable (mathcomp-style) *)
(* consumer: purif_reshape_rank is used downstream by the BB84 secrecy proof. *)
(* path: eur:purif_reshape_rank -> eur:entropic_uncertainty_relation -> *)
(*   eur:entropic_uncertainty_relation -> *)
(*   bb84:entropic_uncertainty_relation_bb84 -> bb84:bb84_secret *)
Lemma purif_reshape_rank {na nb nc nd : nat}
    (rho : 'M[C]_(na * nb * nc * nd)) :
  \rank (purif_reshape rho) = \rank rho.
Proof.
  by rewrite /purif_reshape mxrank_cast.
Qed.
(* rho_XB_purif_reshape_marginal_mx *)
(* infra: no tex label — fundamental & reusable (mathcomp-style) *)
(* consumer: rho_XB_purif_reshape_marginal_mx is used downstream by the BB84 secrecy proof. *)
(* path: eur:rho_XB_purif_reshape_marginal_mx -> *)
(*   eur:entropic_uncertainty_relation -> *)
(*   eur:entropic_uncertainty_relation -> *)
(*   bb84:entropic_uncertainty_relation_bb84 -> bb84:bb84_secret *)
Lemma rho_XB_purif_reshape_marginal_mx
    {na nb nc nd nx : nat}
    (M : 'I_nx -> 'M[C]_na)
    (rhoABC : 'M[C]_(na * nb * nc))
    (rhoABCD : 'M[C]_(na * nb * nc * nd)) :
  ptrace2 rhoABCD = rhoABC ->
  rho_XB M (purif_reshape rhoABCD) = rho_XB M rhoABC.
Proof.
  move=> Hext.
  rewrite /rho_XB /purif_reshape.
  apply: eq_bigr => x _; congr (_ *t _).
  exact: ptrace12_sandwich_purif_slot_mx Hext.
Qed.
(* smooth_hmax_mx_rho_ZC_purif_dpi *)
(* infra: no tex label — fundamental & reusable (mathcomp-style) *)
(* consumer: smooth_hmax_mx_rho_ZC_purif_dpi is used downstream by the BB84 secrecy proof. *)
(* path: eur:smooth_hmax_mx_rho_ZC_purif_dpi -> *)
(*   eur:entropic_uncertainty_relation -> *)
(*   eur:entropic_uncertainty_relation -> *)
(*   bb84:entropic_uncertainty_relation_bb84 -> bb84:bb84_secret *)
Lemma smooth_hmax_mx_rho_ZC_purif_dpi
    {na nb nc nd nz : nat} (eps : R)
    (N : 'I_nz -> 'M[C]_na)
    (rhoABC : 'M[C]_(na * nb * nc))
    (rhoABCD : 'M[C]_(na * nb * nc * nd)) :
  rhoABCD \is denmx ->
  rhoABCD != 0 ->
  ptrace2 rhoABCD = rhoABC ->
  is_povm_mx N ->
  0 <= eps ->
  eps < Num.sqrt (@complex.Re R (\tr rhoABCD)) ->
  smooth_hmax_mx eps (rho_ZC N (purif_reshape rhoABCD)) <=
  smooth_hmax_mx eps (rho_ZC N rhoABC).
Proof.
  move=> Hden Hne Hext HN Heps0 Heps_lt.
  have Hmarg :
      ptrace2 (castmx (mulnA nz nc nd, mulnA nz nc nd)
        (rho_ZC N (purif_reshape rhoABCD))) =
      rho_ZC N rhoABC.
  {
    rewrite /rho_ZC /purif_reshape linear_sum /= linear_sum /=.
    apply: eq_bigr => z _.
    exact: rho_ZC_slot_purif_ptrace2_mx Hext.
  }
  pose rho_big := rho_ZC N (purif_reshape rhoABCD).
  pose rho_big_assoc :=
    castmx (mulnA nz nc nd, mulnA nz nc nd) rho_big.
  pose rho_small := rho_ZC N rhoABC.
  have HrhoABC_den : rhoABC \is denmx.
  {
    move/denmxP: Hden => [HrhoABCD_psd HrhoABCD_tr].
    apply/denmxP; split.
    - rewrite -Hext. exact: ptrace2_psd HrhoABCD_psd.
    - by rewrite -Hext -tr_ptrace2.
  }
  have Hcast_den : purif_reshape rhoABCD \is denmx
    by rewrite /purif_reshape cast_qualifier_diag.
  (* POVM completeness: \tr (rho_ZC N rho) = \tr rho. *)
  have Hrho_ZC_trace_eq :
      forall nB nC (rho : 'M[C]_(na * nB * nC)),
        rho \is psdmx -> \tr (rho_ZC N rho) = \tr rho.
  {
    move=> nB nC rho Hrho_psd.
    have HNpsd : forall z, N z \is psdmx
      by move=> z; exact: is_povm_mx_psd HN.
    have HNsum : \sum_(z < nz) N z = 1%:M := is_povm_mx_sum HN.
    rewrite /rho_ZC linear_sum /=.
    have Hcyc : forall z,
        \tr ((sqrtmx (N z) *t 1%:M *t 1%:M) *m rho *m
             (sqrtmx (N z) *t 1%:M *t 1%:M)) =
        \tr (rho *m ((N z) *t 1%:M *t 1%:M)).
    {
      move=> z.
      rewrite mxtrace_mulC mulmxA mxtrace_mulC.
      by rewrite !tensmx_mul !mulmx1 (sqrtmxK (HNpsd z)).
    }
    under eq_bigr do rewrite mxtrace_tens tr_delta_mx_ii -tr_ptrace1 mul1r Hcyc.
    rewrite -linear_sum /= -mulmx_sumr -linear_sumlz /= -linear_sumlz /= HNsum.
    by rewrite !tensmx11 mulmx1.
  }
  have HrhoABCD_psd : rhoABCD \is psdmx := denmx_psd Hden.
  have Hcast_psd : purif_reshape rhoABCD \is psdmx := denmx_psd Hcast_den.
  have HrhoABC_psd : rhoABC \is psdmx := denmx_psd HrhoABC_den.
  have Htr_cast_eq : \tr (purif_reshape rhoABCD) = \tr rhoABCD
    by rewrite /purif_reshape mxtrace_castmx_sq.
  have Hrho_big_trace_eq : \tr rho_big = \tr rhoABCD.
  { by rewrite /rho_big (Hrho_ZC_trace_eq nb (nc * nd) _ Hcast_psd)
       Htr_cast_eq. }
  have Hrho_small_trace_eq : \tr rho_small = \tr rhoABCD.
  { rewrite /rho_small (Hrho_ZC_trace_eq nb nc _ HrhoABC_psd).
    by rewrite -Hext -tr_ptrace2. }
  have Hrho_big_den : rho_big \is denmx :=
    rho_ZC_subden HN Hcast_den.
  have Hrho_small_den : rho_small \is denmx :=
    rho_ZC_subden HN HrhoABC_den.
  have /denmxP[Hrho_big_psd Hrho_big_trC] := Hrho_big_den.
  have /denmxP[Hrho_small_psd Hrho_small_trC] := Hrho_small_den.
  have Hrho_big_assoc_den : rho_big_assoc \is denmx.
  { by rewrite /rho_big_assoc cast_qualifier_diag. }
  have /denmxP[Hrho_big_assoc_psd _] := Hrho_big_assoc_den.
  have Hrho_big_ne : rho_big != 0.
  {
    (* rho_ZC N rho = 0 ⇒ Tr = 0 ⇒ rho = 0 (sub-normalised invariant). *)
    apply/negP => /eqP H0.
    have Htr_big_zero : \tr rho_big = 0 by rewrite H0 mxtrace0.
    have HrhoABCD_tr_zero : \tr rhoABCD = 0
      by rewrite -Hrho_big_trace_eq Htr_big_zero.
    have : rhoABCD == 0
      by rewrite -(psdmx_trace_eq0 HrhoABCD_psd); apply/eqP.
    by move/eqP=> H; move/eqP: Hne; rewrite H.
  }
  have Hdim_big_pos : (0 < nz * (nc * nd))%N.
  {
    have Hrank_pos : (0 < \rank rho_big)%N
      by rewrite lt0n mxrank_eq0 Hrho_big_ne.
    exact: leq_trans Hrank_pos (rank_leq_row rho_big).
  }
  move: Hdim_big_pos; rewrite !muln_gt0
    => /andP[Hnz_pos /andP[Hnc_pos Hnd_pos]].
  have Hncnd_pos : (0 < nc * nd)%N by rewrite muln_gt0 Hnc_pos Hnd_pos.
  have Hrho_big_tr : @complex.Re R (\tr rho_big) <= 1.
  { have Hreal := ger0_real (psdmx_trace Hrho_big_psd).
    by move: Hrho_big_trC; rewrite -(RRe_real Hreal) -[1]/(1%:C) lecR. }
  have Hrho_small_tr : @complex.Re R (\tr rho_small) <= 1.
  { have Hreal := ger0_real (psdmx_trace Hrho_small_psd).
    by move: Hrho_small_trC; rewrite -(RRe_real Hreal) -[1]/(1%:C) lecR. }
    have Heps_lt_big : eps < Num.sqrt (@complex.Re R (\tr rho_big))
      by rewrite Hrho_big_trace_eq.
    have Heps_lt_small : eps < Num.sqrt (@complex.Re R (\tr rho_small))
      by rewrite Hrho_small_trace_eq.
    have Hrho_small_pos : 0 < @complex.Re R (\tr rho_small).
    {
      have Hsqrt_gt0 : 0 < Num.sqrt (@complex.Re R (\tr rho_small)) :=
        le_lt_trans Heps0 Heps_lt_small.
      have Hrho_small_ge0 : 0 <= @complex.Re R (\tr rho_small).
      { have /= := psdmx_trace Hrho_small_psd.
        by rewrite lecE /= => /andP []. }
      have Hsqrt_sq_pos :
          0 < (Num.sqrt (@complex.Re R (\tr rho_small))) ^+ 2
        by rewrite expr2; apply: mulr_gt0.
      by rewrite (sqr_sqrtr Hrho_small_ge0) in Hsqrt_sq_pos.
    }
    have Hbig_has_inf :
        has_inf [set v : R | exists tau : 'M[C]_(nz * (nc * nd)),
          ((tau \is denmx) && (0 < @complex.Re R (\tr tau))) &&
          (pur_dist_mx tau rho_big <= eps) /\ v = hmax_mx tau].
    { exact: @smooth_hmax_mx_has_inf nz (nc * nd) eps rho_big Hnz_pos Hncnd_pos
        Hrho_big_den Heps0 Heps_lt_big. }
    rewrite /smooth_hmax_mx -/rho_big -/rho_small.
    apply: lb_le_inf.
    - exists (hmax_mx rho_small). exists rho_small; split; last reflexivity.
      by rewrite Hrho_small_den Hrho_small_pos
        (pur_dist_mx_refl Hrho_small_den).
    - move=> v [tau_small [Htau_small_feas ->]].
      move: Htau_small_feas
        => /andP[/andP[Htau_small_den _] Htau_small_pd].
      have /denmxP[Htau_small_psd Htau_small_trC] := Htau_small_den.
      have Htau_small_tr : @complex.Re R (\tr tau_small) <= 1
        by move: Htau_small_trC; rewrite lecE /= => /andP [_].
      have Htau_small_close :
          (tau_small \is denmx) &&
          (Num.sqrt (1 - (gfidelity tau_small rho_small)^2) <= eps).
      { by rewrite Htau_small_den -/(pur_dist_mx tau_small rho_small). }
    have Hrho_big_assoc_nz : rho_big_assoc != 0.
    { apply/eqP => Hz.
      have Htr_zero : \tr rho_big_assoc = 0 by rewrite Hz mxtrace0.
      have Htr_big_zero : \tr rho_big = 0
        by rewrite -[\tr rho_big](mxtrace_castmx_sq (mulnA nz nc nd)).
      have HrhoABCD_tr_zero : \tr rhoABCD = 0
        by rewrite -Hrho_big_trace_eq Htr_big_zero.
      have : rhoABCD == 0
        by rewrite -(psdmx_trace_eq0 HrhoABCD_psd); apply/eqP.
      by move/eqP=> H; move/eqP: Hne; rewrite H. }
    have [Hext_exists _] :=
      @eur_ii (nz * nc) nd eps rho_small rho_big_assoc
        tau_small Hrho_big_assoc_den Hrho_big_assoc_nz
        Hmarg Htau_small_close.
    have [tau_assoc [Htau_assoc_den [Htau_assoc_marg Htau_assoc_pd]]] :=
      Hext_exists.
    move/denmxP: Htau_assoc_den => [Htau_assoc_psd Htau_assoc_trC].
    have Htau_assoc_tr : @complex.Re R (\tr tau_assoc) <= 1.
    {
      have Htau_assoc_real :
          (\tr tau_assoc : C) = (@complex.Re R (\tr tau_assoc))%:C
        by rewrite RRe_real // ger0_real // psdmx_trace.
      by move: Htau_assoc_trC; rewrite Htau_assoc_real lecR.
    }
    pose tau_big : 'M[C]_(nz * (nc * nd)) :=
      castmx (esym (mulnA nz nc nd), esym (mulnA nz nc nd)) tau_assoc.
    have Htau_big_psd : tau_big \is psdmx.
    { rewrite /tau_big -/(castmx_sq (esym (mulnA nz nc nd)) tau_assoc).
      exact: castmx_sq_psdmx Htau_assoc_psd. }
      have Htau_big_tr : @complex.Re R (\tr tau_big) <= 1.
      { rewrite /tau_big -/(castmx_sq (esym (mulnA nz nc nd)) tau_assoc)
          mxtrace_castmx_sq.
        exact: Htau_assoc_tr. }
      have Htau_big_den : tau_big \is denmx.
      { exact: denmx_psd_re_tr_le Htau_big_psd Htau_big_tr. }
    have Htau_big_marg :
        ptrace2 (castmx (mulnA nz nc nd, mulnA nz nc nd) tau_big) =
        tau_small.
    { rewrite /tau_big castmxKV. exact: Htau_assoc_marg. }
    have Htau_assoc_pd_sym : pur_dist_mx tau_assoc rho_big_assoc <= eps.
    { rewrite /pur_dist_mx
        (gfid_sym_mx Htau_assoc_psd Hrho_big_assoc_psd).
      by rewrite -/(pur_dist_mx _ _). }
    have Htau_big_pd : pur_dist_mx tau_big rho_big <= eps.
    {
      have Hrho_big_cancel :
          castmx (esym (mulnA nz nc nd), esym (mulnA nz nc nd))
            rho_big_assoc = rho_big
        by rewrite /rho_big_assoc castmxK.
      rewrite /pur_dist_mx /tau_big -Hrho_big_cancel gfid_cast_mx.
      exact: Htau_assoc_pd_sym.
    }
    have Hnz_nc_pos : (0 < nz * nc)%N by rewrite muln_gt0 Hnz_pos Hnc_pos.
      pose gap := Num.sqrt (@complex.Re R (\tr rho_small)) - eps.
    have Hgap_pos : 0 < gap by rewrite /gap subr_gt0.
    have Hsqrt_le0 :
        Num.sqrt (@complex.Re R (\tr rho_small)) <=
          Num.sqrt (@complex.Re R (\tr tau_small)) +
            pur_dist_mx tau_small rho_small.
      { rewrite /pur_dist_mx.
        exact: pur_dist_mx_trace_sqrt_bound Hnz_nc_pos
          Hrho_small_den Htau_small_den. }
    have Hsqrt_le :
        Num.sqrt (@complex.Re R (\tr rho_small)) <=
        Num.sqrt (@complex.Re R (\tr tau_small)) + eps.
    { have Hadd_le :
          Num.sqrt (@complex.Re R (\tr tau_small)) +
            pur_dist_mx tau_small rho_small <=
          Num.sqrt (@complex.Re R (\tr tau_small)) + eps
        by rewrite lerD2l.
      exact: le_trans Hsqrt_le0 Hadd_le. }
    have Hgap_le_sqrt : gap <= Num.sqrt (@complex.Re R (\tr tau_small)).
    { have Htmp : gap + eps <=
          Num.sqrt (@complex.Re R (\tr tau_small)) + eps
        by rewrite /gap subrK; exact: Hsqrt_le.
      by move: Htmp; rewrite lerD2r. }
    have Htau_small_trace_lb :
        gap ^+ 2 <= @complex.Re R (\tr tau_small).
    { have Hsq :
          gap ^+ 2 <= (Num.sqrt (@complex.Re R (\tr tau_small))) ^+ 2.
      { rewrite (ler_sqr (ltW Hgap_pos) (sqrtr_ge0 _)).
        exact: Hgap_le_sqrt. }
      have Htau_sq :
          (Num.sqrt (@complex.Re R (\tr tau_small))) ^+ 2 <=
          @complex.Re R (\tr tau_small).
      { have Htau_tr_ge0 : 0 <= @complex.Re R (\tr tau_small).
        { have /= := psdmx_trace Htau_small_psd.
          by rewrite lecE /= => /andP [_]. }
        by rewrite sqr_sqrtr. }
      exact: le_trans Hsq Htau_sq. }
    have Htau_small_tr_pos : 0 < @complex.Re R (\tr tau_small).
    { have Hgap_sq_pos : 0 < gap ^+ 2
        by rewrite expr2; apply: mulr_gt0.
      exact: lt_le_trans Hgap_sq_pos Htau_small_trace_lb. }
    have Htau_big_tr_eq_small : \tr tau_big = \tr tau_small.
    { rewrite -Htau_big_marg -tr_ptrace2.
      symmetry.
      rewrite -/(castmx_sq (mulnA nz nc nd) tau_big).
      exact: mxtrace_castmx_sq. }
    have Htau_big_tr_pos : 0 < @complex.Re R (\tr tau_big)
      by rewrite Htau_big_tr_eq_small.
    have Hhmax_le : hmax_mx tau_big <= hmax_mx tau_small.
    { exact: hmax_mx_ptrace2_le Hnz_pos Hnc_pos Hnd_pos
        Htau_big_psd Htau_big_tr Htau_big_tr_pos Htau_small_psd
        Htau_small_tr Htau_big_marg. }
      have Hfeas_big :
          ([set w : R | exists tau : 'M[C]_(nz * (nc * nd)),
            ((tau \is denmx) && (0 < @complex.Re R (\tr tau))) &&
            (pur_dist_mx tau rho_big <= eps) /\ w = hmax_mx tau]%classic)
            (hmax_mx tau_big).
      { exists tau_big; split; last reflexivity.
        by rewrite Htau_big_den Htau_big_tr_pos Htau_big_pd. }
    exact: le_trans (ge_inf Hbig_has_inf.2 Hfeas_big) Hhmax_le.
Qed.
End PurificationReshape.
(* Paper: Tomamichel & Renner (PRL 106, 110506 (2011); arXiv:1009.2015),  *)
(*   "Proof of the Main Result", mixed-state reduction (purify + DPI).    *)
(* If Stage 1 (pure UCR) holds universally, then Stage 2 (mixed UCR)    *)
(* holds for every mixed ρ_{ABC}. This lemma packages matrix-level        *)
(* purification existence and smooth_hmax_mx DPI into the reduction used *)
(* by the matrix EUR theorem.                                            *)
(* Note: the pure-case hypothesis is dim-generic so that purification  *)
(* (which enlarges the conditioning register) can reuse it at the      *)
(* extended dimensions.                                                 *)
(* ucr_mixed_reduction_from_pure_smooth *)
(* infra: no tex label — fundamental & reusable (mathcomp-style) *)
(* consumer: ucr_mixed_reduction_from_pure_smooth is used downstream by the BB84 secrecy proof. *)
(* path: eur:ucr_mixed_reduction_from_pure_smooth -> *)
(*   eur:entropic_uncertainty_relation -> *)
(*   eur:entropic_uncertainty_relation -> *)
(*   bb84:entropic_uncertainty_relation_bb84 -> bb84:bb84_secret *)
Lemma ucr_mixed_reduction_from_pure_smooth {na nb nc nx nz : nat} :
  (forall (na' nb' nc' nx' nz' : nat) (eps : R)
          (rho_pure : 'M[C]_(na' * nb' * nc'))
          (M : 'I_nx' -> 'M[C]_na') (N : 'I_nz' -> 'M[C]_na'),
     rho_pure \is denmx -> \rank rho_pure = 1%N ->
     is_povm_mx M -> is_povm_mx N ->
     overlap_mx M N != 0 ->
     0 <= eps -> eps < Num.sqrt (@complex.Re R (\tr rho_pure)) ->
     - log2 (overlap_mx M N) <=
       smooth_hmin_mx eps (rho_XB M rho_pure)
     + smooth_hmax_mx eps (rho_ZC N rho_pure)) ->
  forall (eps : R) (rhoABC : 'M[C]_(na * nb * nc))
         (M : 'I_nx -> 'M[C]_na) (N : 'I_nz -> 'M[C]_na),
    rhoABC \is denmx -> rhoABC != 0 ->
    is_povm_mx M -> is_povm_mx N ->
    overlap_mx M N != 0 ->
    0 <= eps -> eps < Num.sqrt (@complex.Re R (\tr rhoABC)) ->
    - log2 (overlap_mx M N) <=
      smooth_hmin_mx eps (rho_XB M rhoABC)
    + smooth_hmax_mx eps (rho_ZC N rhoABC).
Proof.
  move=> Hpure eps rhoABC M N Hden Hne HM HN Hc Heps0 Heps_lt_sqrt.
  have Hpsd : rhoABC \is psdmx := denmx_psd Hden.
  have Hle : (na * nb * nc <= na * nb * nc)%N by [].
  (* Purify rhoABC at dim nd := na*nb*nc. *)
  have [rhoABCD [HrhoABCD_den [Hext HrhoABCD_rk]]] :=
    purification_mx_exists Hden Hne Hle.
  have HrhoABCD_psd : rhoABCD \is psdmx := denmx_psd HrhoABCD_den.
  have HrhoABCD_tr_eq : \tr rhoABCD = \tr rhoABC by rewrite tr_ptrace2 Hext.
  pose rhoABCD_cast := purif_reshape rhoABCD.
  have Hcast_den : rhoABCD_cast \is denmx
    by rewrite /rhoABCD_cast /purif_reshape cast_qualifier_diag.
  have Hcast_rk : \rank rhoABCD_cast = 1%N.
  { rewrite /rhoABCD_cast purif_reshape_rank; exact: HrhoABCD_rk. }
  have Hcast_tr_eq : \tr rhoABCD_cast = \tr rhoABC.
  { by rewrite /rhoABCD_cast /purif_reshape mxtrace_castmx_sq
      HrhoABCD_tr_eq. }
  have Hcast_eps_lt :
      eps < Num.sqrt (@complex.Re R (\tr rhoABCD_cast)).
  { by rewrite Hcast_tr_eq. }
  have Hstage1 :=
    Hpure na nb (nc * (na*nb*nc))%N nx nz eps rhoABCD_cast M N
      Hcast_den Hcast_rk HM HN Hc Heps0 Hcast_eps_lt.
  (* rho_XB invariance under purification+reshape. *)
  have Hinv_XB : rho_XB M rhoABCD_cast = rho_XB M rhoABC
    := rho_XB_purif_reshape_marginal_mx M Hext.
  (* DPI: bundled directly as the rho_ZC-purification-DPI helper.        *)
  have HrhoABCD_nz : rhoABCD != 0.
  { apply/eqP => Hz.
    have Htr0 : \tr rhoABCD = 0 by rewrite Hz mxtrace0.
    move: HrhoABCD_tr_eq; rewrite Htr0 => /esym /eqP.
    rewrite (psdmx_trace_eq0 Hpsd) => /eqP Hr0.
    move/eqP: Hne => Hne0.
    exact: (Hne0 Hr0). }
  have Heps_lt_sqrt_ABCD :
      eps < Num.sqrt (@complex.Re R (\tr rhoABCD)).
  { by rewrite HrhoABCD_tr_eq. }
  have HDPI : smooth_hmax_mx eps (rho_ZC N rhoABCD_cast) <=
              smooth_hmax_mx eps (rho_ZC N rhoABC)
    := @smooth_hmax_mx_rho_ZC_purif_dpi na nb nc (na*nb*nc) nz
         eps N rhoABC rhoABCD HrhoABCD_den HrhoABCD_nz
         Hext HN Heps0 Heps_lt_sqrt_ABCD.
  rewrite Hinv_XB in Hstage1.
  apply: le_trans Hstage1 _.
  by apply: lerD.
Qed.
(* ================================================================== *)
(* Stage 0: pure ρ_{ABC}, ε = 0                                           *)
(* Paper: Tomamichel & Renner (PRL 106, 110506 (2011); arXiv:1009.2015),  *)
(*   "Proof of the Main Result", pure ε=0 case (Eqs. (6)-(11)).           *)
(* math: For pure ρ_{ABC} with POVMs M, N on A:                          *)
(*       H_min(X|B)_ρ + H_max(Z|C)_ρ ≥ -log₂ c(X,Z)                    *)
(*                                                                       *)
(* Uses `ucr_stage0_pure_povm_mx` from entropy/util.v;             *)
(* eur/prop.v supplies the `rho_XB`/`rho_ZC`                             *)
(* + `overlap_mx` abstraction layer.                                    *)
(* ================================================================== *)
Section Stage0.
Variable (na nb nc nx nz : nat).
(* TeX eqn:mo1: max/min duality on the pure Stinespring Z-lift. *)
(* path: eur:ucr_pure_zero_mo1 -> eur:ucr_pure_zero -> *)
(*   eur:entropic_uncertainty_relation -> bb84:bb84_secret *)
Lemma ucr_pure_zero_mo1
    (rhoABC : 'M[C]_(na * nb * nc))
    (N : 'I_nz -> 'M[C]_na)
    (Hzz_dim : (((nz * nz) * na) * nb = nz * (nz * na * nb))%N) :
  rhoABC \is den1mx -> \rank rhoABC = 1%N -> is_povm_mx N ->
  hmax_mx (rho_ZC N rhoABC) =
  - hmin_mx (castmx_sq Hzz_dim (rho_ZZpAB N rhoABC)).
Proof.
  move=> Hden1 Hrank HN.
  pose rhoZZ := rho_ZZpABC N rhoABC.
  pose rhoZ := rho_ZC N rhoABC.
  pose rhoZZpAB : 'M[C]_(nz * (nz * na * nb)) :=
    castmx_sq Hzz_dim (rho_ZZpAB N rhoABC).
  pose rhoZCZpAB : 'M[C]_((nz * nc) * (nz * na * nb)) :=
    rho_ZC_ZpAB N rhoABC.
  have HZC_extension :
      rhoZCZpAB \is den1mx /\
      \rank rhoZCZpAB = 1%N /\
      ptrace2 rhoZCZpAB = rhoZ.
  {
    have [HZC_den [HZC_rank HZC_ptr]] :
        rhoZCZpAB \is denmx /\
        \rank rhoZCZpAB = 1%N /\
        ptrace2 rhoZCZpAB = rhoZ.
    {
      rewrite /rhoZCZpAB /rhoZ.
      exact: rho_ZC_ZpAB_extension HN (den1mx_den Hden1) Hrank.
    }
    have HZC_den1 : rhoZCZpAB \is den1mx.
    {
      apply/den1mxP; split.
      - exact: denmx_psd HZC_den.
      - apply/eqP.
        rewrite tr_ptrace2 HZC_ptr /rhoZ (@rho_ZC_trace na nb nc nz N rhoABC HN).
        by have /den1mxP[_ /eqP ->] := Hden1.
    }
    by split=> //; split.
  }
  have [HZC_den1 [HZC_rank HZC_ptr]] := HZC_extension.
  have HZC_dim_pos : (0 < (nz * nc) * (nz * na * nb))%N.
  {
    have Hrank_pos : (0 < \rank rhoZCZpAB)%N by rewrite HZC_rank.
    exact: leq_trans Hrank_pos (rank_leq_row rhoZCZpAB).
  }
  have Hnz_pos : (0 < nz)%N.
  { by move: HZC_dim_pos; rewrite !muln_gt0 => /andP[/andP[]]. }
  have Hnc_pos : (0 < nc)%N.
  { by move: HZC_dim_pos; rewrite !muln_gt0 => /andP[/andP[_ ?] _]. }
  have Hnab_pos : (0 < nz * na * nb)%N.
  { by move: HZC_dim_pos; rewrite muln_gt0 => /andP[]. }
  pose TZ : ihbFinType :=
    FinInhabited.Pack (FinInhabited.Class (Choice.on 'I_nz)
      (Countable.on 'I_nz) (Finite.on 'I_nz)
      (isPointed.Build 'I_nz (Ordinal Hnz_pos))).
  pose TC : ihbFinType :=
    FinInhabited.Pack (FinInhabited.Class (Choice.on 'I_nc)
      (Countable.on 'I_nc) (Finite.on 'I_nc)
      (isPointed.Build 'I_nc (Ordinal Hnc_pos))).
  pose TZpAB : ihbFinType :=
    FinInhabited.Pack (FinInhabited.Class (Choice.on 'I_(nz * na * nb))
      (Countable.on 'I_(nz * na * nb)) (Finite.on 'I_(nz * na * nb))
      (isPointed.Build 'I_(nz * na * nb) (Ordinal Hnab_pos))).
  have HdimZ : dim ('Hs TZ) = nz by rewrite /TZ -(@ihb_dim_cast R _) card_ord.
  have HdimC : dim ('Hs TC) = nc by rewrite /TC -(@ihb_dim_cast R _) card_ord.
  have HdimZpAB : dim ('Hs TZpAB) = nz * na * nb
    by rewrite /TZpAB -(@ihb_dim_cast R _) card_ord.
  have Hcpp_pos : (0 < (nz * na * nb) * nz * nc)%N.
  { have Hleft_pos : (0 < (nz * na * nb) * nz)%N.
    { by rewrite muln_gt0 Hnab_pos Hnz_pos. }
    by rewrite muln_gt0 Hleft_pos Hnc_pos. }
  pose TCpp : ihbFinType :=
    FinInhabited.Pack (FinInhabited.Class
      (Choice.on 'I_((nz * na * nb) * nz * nc))
      (Countable.on 'I_((nz * na * nb) * nz * nc))
      (Finite.on 'I_((nz * na * nb) * nz * nc))
      (isPointed.Build 'I_((nz * na * nb) * nz * nc)
        (Ordinal Hcpp_pos))).
  have HdimCpp : dim ('Hs TCpp) = (nz * na * nb) * nz * nc
    by rewrite /TCpp -(@ihb_dim_cast R _) card_ord.
  pose Zlbl : 'I_5 := ord0.
  pose Clbl : 'I_5 := Ordinal (isT : (1 < 5)%N).
  pose Elbl : 'I_5 := Ordinal (isT : (2 < 5)%N).
  pose Cplbl : 'I_5 := Ordinal (isT : (3 < 5)%N).
  pose Cpplbl : 'I_5 := Ordinal (isT : (4 < 5)%N).
  pose HL (i : 'I_5) : chsType :=
    if i == Zlbl then 'Hs TZ else
    if i == Clbl then 'Hs TC else
    if i == Elbl then 'Hs TZpAB else
    if i == Cplbl then 'Hs TZ else 'Hs TCpp.
  have HHLZ : dim (HL Zlbl) = nz by rewrite /HL /Zlbl eqxx HdimZ.
  have HHLC : dim (HL Clbl) = nc by rewrite /HL /Zlbl /Clbl /= HdimC.
  have HHLE : dim (HL Elbl) = nz * na * nb
    by rewrite /HL /Zlbl /Clbl /Elbl /= HdimZpAB.
  have HHLCp : dim (HL Cplbl) = nz
    by rewrite /HL /Zlbl /Clbl /Elbl /Cplbl /= HdimZ.
  have HHLCpp : dim (HL Cpplbl) = (nz * na * nb) * nz * nc
    by rewrite /HL /Zlbl /Clbl /Elbl /Cplbl /Cpplbl /= HdimCpp.
  have disZC : [disjoint [set Zlbl] & [set Clbl]].
  { by rewrite disjoint1X inE /Zlbl /Clbl. }
  have disZE : [disjoint [set Zlbl] & [set Elbl]].
  { by rewrite disjoint1X inE /Zlbl /Elbl. }
  have disCE : [disjoint [set Clbl] & [set Elbl]].
  { by rewrite disjoint1X inE /Clbl /Elbl. }
  have disZCp : [disjoint [set Zlbl] & [set Cplbl]].
  { by rewrite disjoint1X inE /Zlbl /Cplbl. }
  have disZCpp : [disjoint [set Zlbl] & [set Cpplbl]].
  { by rewrite disjoint1X inE /Zlbl /Cpplbl. }
  have disCCp : [disjoint [set Clbl] & [set Cplbl]].
  { by rewrite disjoint1X inE /Clbl /Cplbl. }
  have disCCpp : [disjoint [set Clbl] & [set Cpplbl]].
  { by rewrite disjoint1X inE /Clbl /Cpplbl. }
  have disECp : [disjoint [set Elbl] & [set Cplbl]].
  { by rewrite disjoint1X inE /Elbl /Cplbl. }
  have disECpp : [disjoint [set Elbl] & [set Cpplbl]].
  { by rewrite disjoint1X inE /Elbl /Cpplbl. }
  have disCpCpp : [disjoint [set Cplbl] & [set Cpplbl]].
  { by rewrite disjoint1X inE /Cplbl /Cpplbl. }
  have HdimZ_set : dim 'H[HL]_[set Zlbl] = nz.
  { by rewrite -(dim_set1 HL Zlbl) HHLZ. }
  have HdimC_set : dim 'H[HL]_[set Clbl] = nc.
  { by rewrite -(dim_set1 HL Clbl) HHLC. }
  have HdimE_set : dim 'H[HL]_[set Elbl] = nz * na * nb.
  { by rewrite -(dim_set1 HL Elbl) HHLE. }
  have HdimCp_set : dim 'H[HL]_[set Cplbl] = nz.
  { by rewrite -(dim_set1 HL Cplbl) HHLCp. }
  have HdimCpp_set :
      dim 'H[HL]_[set Cpplbl] = (nz * na * nb) * nz * nc.
  { by rewrite -(dim_set1 HL Cpplbl) HHLCpp. }
  have HdimZ_Cp : dim 'H[HL]_[set Zlbl] = dim 'H[HL]_[set Cplbl].
  { by rewrite HdimZ_set HdimCp_set. }
  have HdimE_Cp_Cpp :
      (dim 'H[HL]_[set Elbl] * dim 'H[HL]_[set Cplbl] <=
       dim 'H[HL]_[set Cpplbl])%N.
  { rewrite HdimE_set HdimCp_set HdimCpp_set.
    exact: leq_pmulr Hnc_pos. }
  have HdimC_Cpp : (dim 'H[HL]_[set Clbl] <= dim 'H[HL]_[set Cpplbl])%N.
  { rewrite HdimC_set HdimCpp_set.
    have Hprefix_pos : (0 < (nz * na * nb) * nz)%N
      by rewrite muln_gt0 Hnab_pos Hnz_pos.
    exact: leq_pmull Hprefix_pos. }
  pose S_ZC := [set Zlbl] :|: [set Clbl].
  pose S_ZCE3 := S_ZC :|: [set Elbl].
  have disZC_E : [disjoint S_ZC & [set Elbl]]
    by rewrite /S_ZC disjointUX disZE disCE.
  have HdimZC_set :
      dim 'H[HL]_S_ZC =
      dim 'H[HL]_[set Zlbl] * dim 'H[HL]_[set Clbl].
  {
    by rewrite /S_ZC (tenv_dim disZC).
  }
  have HdimZCE_set :
      dim 'H[HL]_S_ZCE3 =
      (dim 'H[HL]_[set Zlbl] * dim 'H[HL]_[set Clbl]) *
        dim 'H[HL]_[set Elbl].
  {
    rewrite /S_ZCE3 (tenv_dim disZC_E).
    by rewrite HdimZC_set.
  }
  have HdimZCE_col :
      dim 'H[HL]_S_ZC * dim 'H[HL]_[set Elbl] =
      (dim 'H[HL]_[set Zlbl] * dim 'H[HL]_[set Clbl]) *
        dim 'H[HL]_[set Elbl].
  {
    by rewrite HdimZC_set.
  }
  have HdimZCE_raw :
      ((dim 'H[HL]_[set Zlbl] * dim 'H[HL]_[set Clbl]) *
         dim 'H[HL]_[set Elbl] =
       (nz * nc) * (nz * na * nb))%N.
  {
    by rewrite -(dim_set1 HL Zlbl) -(dim_set1 HL Clbl)
      -(dim_set1 HL Elbl) HHLZ HHLC HHLE.
  }
  pose Q_ZC : 'M[C]_(dim 'H[HL]_[set Zlbl] *
                      dim 'H[HL]_[set Clbl]) :=
    castmx (tenv_dim disZC, erefl)
      (@tenv_mxU R _ HL [set Zlbl] [set Clbl]).
  pose U_ZCE := @tenv_mxU R _ HL S_ZC [set Elbl].
  pose Q_ZCE : 'M[C]_((dim 'H[HL]_[set Zlbl] *
                       dim 'H[HL]_[set Clbl]) *
                      dim 'H[HL]_[set Elbl]) :=
    castmx (HdimZCE_set, HdimZCE_col)
      U_ZCE.
  pose I_E : 'M[C]_(dim 'H[HL]_[set Elbl]) := 1%:M.
  have HQ_ZC_t :
      Q_ZC^*t =
      castmx (erefl, tenv_dim disZC)
        (@tenv_mxU R _ HL [set Zlbl] [set Clbl])^*t.
  {
    rewrite /Q_ZC.
    exact: (@castmx_mx_mxT _ _ (@adjmx _) _ _ _ _
      (tenv_dim disZC, erefl)
      (@tenv_mxU R _ HL [set Zlbl] [set Clbl])).
  }
  have HQtQ_ZC : Q_ZC^*t *m Q_ZC = 1%:M.
  {
    rewrite /Q_ZC HQ_ZC_t mcextra.castmx_mul.
    have HU :
        (@tenv_mxU R _ HL [set Zlbl] [set Clbl])^*t *m
        (@tenv_mxU R _ HL [set Zlbl] [set Clbl]) = 1%:M.
    {
      have := unitarymxK
        (@tenv_mxU_adj_unitarymx R _ HL [set Zlbl] [set Clbl] disZC).
      by rewrite adjmxK.
    }
    rewrite HU.
    by case: _ / (tenv_dim disZC); rewrite castmx_id.
  }
  have HQ_ZC_unit : Q_ZC \is unitarymx by apply/unitarymxPV.
  have HQQt_ZC : Q_ZC *m Q_ZC^*t = 1%:M := unitarymxK HQ_ZC_unit.
  have HQ_ZCE_t :
      Q_ZCE^*t =
      castmx (HdimZCE_col, HdimZCE_set)
        (@tenv_mxU R _ HL S_ZC [set Elbl])^*t.
  {
    rewrite /Q_ZCE.
    exact: (@castmx_mx_mxT _ _ (@adjmx _) _ _ _ _
      (HdimZCE_set, HdimZCE_col)
      (@tenv_mxU R _ HL S_ZC [set Elbl])).
  }
  have HQtQ_ZCE : Q_ZCE^*t *m Q_ZCE = 1%:M.
  {
    rewrite /Q_ZCE HQ_ZCE_t mcextra.castmx_mul.
    have HU :
        (@tenv_mxU R _ HL S_ZC [set Elbl])^*t *m
        (@tenv_mxU R _ HL S_ZC [set Elbl]) = 1%:M.
    {
      have := unitarymxK
        (@tenv_mxU_adj_unitarymx R _ HL S_ZC [set Elbl] disZC_E).
      by rewrite adjmxK.
    }
    rewrite HU.
    apply/eqP.
    by rewrite castmx_eq1 eqxx.
  }
  have HQ_ZCE_unit : Q_ZCE \is unitarymx by apply/unitarymxPV.
  have HQQt_ZCE : Q_ZCE *m Q_ZCE^*t = 1%:M :=
    unitarymxK HQ_ZCE_unit.
  have HQtQ_ZC_E :
      ((Q_ZC *t I_E)^*t *m (Q_ZC *t I_E)) = 1%:M.
  {
    by rewrite adjmx_tens adjmx1 tensmx_mul HQtQ_ZC mul1mx tensmx11.
  }
  have HQQt_ZC_E :
      (Q_ZC *t I_E) *m (Q_ZC *t I_E)^*t = 1%:M.
  {
    by rewrite adjmx_tens adjmx1 tensmx_mul HQQt_ZC mul1mx tensmx11.
  }
  have HQZC_E_adj : (Q_ZC *t I_E)^*t = Q_ZC^*t *t I_E.
  {
    by rewrite /I_E adjmx_tens adjmx1.
  }
  pose rho_raw_prod :
      'M[C]_((dim 'H[HL]_[set Zlbl] * dim 'H[HL]_[set Clbl]) *
             dim 'H[HL]_[set Elbl]) :=
    castmx (esym HdimZCE_raw, esym HdimZCE_raw) rhoZCZpAB.
  pose rho_inner_labelled :
      'M[C]_(dim 'H[HL]_S_ZC * dim 'H[HL]_[set Elbl]) :=
    castmx (esym HdimZCE_col, esym HdimZCE_col)
      (((Q_ZC *t I_E) *m
        rho_raw_prod *m
        (Q_ZC^*t *t I_E))).
  pose rho_prod_labelled : 'M[C]_(dim 'H[HL]_S_ZCE3) :=
    U_ZCE *m rho_inner_labelled *m U_ZCE^*t.
  pose rhoL3 : 'F[HL]_S_ZCE3 :=
    mx2h rho_prod_labelled.
  have HrhoL3_psd : rhoL3 \is psdlf.
  {
    rewrite qualifE /rhoL3 mx2hK.
    have Hrho_raw_prod_psd : rho_raw_prod \is psdmx.
    {
      rewrite /rho_raw_prod -/(castmx_sq (esym HdimZCE_raw) rhoZCZpAB).
      exact: castmx_sq_psdmx (denmx_psd (den1mx_den HZC_den1)).
    }
    have Hinner_psd :
        ((Q_ZC *t I_E) *m rho_raw_prod *m (Q_ZC^*t *t I_E)) \is psdmx.
    {
      rewrite -HQZC_E_adj.
      exact: psdmx_bimap_closed_gen Hrho_raw_prod_psd.
    }
    have Hinner_label_psd : rho_inner_labelled \is psdmx.
    {
      rewrite /rho_inner_labelled
        -/(castmx_sq (esym HdimZCE_col)
            ((Q_ZC *t I_E) *m rho_raw_prod *m (Q_ZC^*t *t I_E))).
      exact: castmx_sq_psdmx Hinner_psd.
    }
    rewrite /rho_prod_labelled.
    exact: psdmx_bimap_closed_gen Hinner_label_psd.
  }
  have HrhoL3_tr : @complex.Re R (\Tr rhoL3) <= 1.
  {
    rewrite /rhoL3 /lftrace mx2hK.
    have HUtU_ZCE : U_ZCE^*t *m U_ZCE = 1%:M.
    {
      have := unitarymxK (@tenv_mxU_adj_unitarymx R _ HL S_ZC
        [set Elbl] disZC_E).
      by rewrite /U_ZCE adjmxK.
    }
    have Hraw_tr1 : \tr rho_raw_prod = 1.
    {
      rewrite /rho_raw_prod mxtrace_castmx_sq.
      have /den1mxP [_ /eqP Htr1] := HZC_den1.
      exact: Htr1.
    }
    have Hinner_label_tr :
        \tr rho_inner_labelled =
        \tr rho_raw_prod.
    {
      rewrite /rho_inner_labelled mxtrace_castmx_sq -HQZC_E_adj.
      by rewrite mxtrace_mulC mulmxA HQtQ_ZC_E mul1mx.
    }
    rewrite /rho_prod_labelled mxtrace_mulC mulmxA HUtU_ZCE mul1mx.
    by rewrite Hinner_label_tr Hraw_tr1 re_realid lexx.
  }
  have HrhoL3_tr1 : \Tr rhoL3 = 1.
  {
    rewrite /rhoL3 /lftrace mx2hK.
    have HUtU_ZCE : U_ZCE^*t *m U_ZCE = 1%:M.
    {
      have := unitarymxK (@tenv_mxU_adj_unitarymx R _ HL S_ZC
        [set Elbl] disZC_E).
      by rewrite /U_ZCE adjmxK.
    }
    have Hraw_tr1 : \tr rho_raw_prod = 1.
    {
      rewrite /rho_raw_prod mxtrace_castmx_sq.
      have /den1mxP [_ /eqP Htr1] := HZC_den1.
      exact: Htr1.
    }
    have Hinner_label_tr :
        \tr rho_inner_labelled =
        \tr rho_raw_prod.
    {
      rewrite /rho_inner_labelled mxtrace_castmx_sq -HQZC_E_adj.
      by rewrite mxtrace_mulC mulmxA HQtQ_ZC_E mul1mx.
    }
    rewrite /rho_prod_labelled mxtrace_mulC mulmxA HUtU_ZCE mul1mx.
    by rewrite Hinner_label_tr Hraw_tr1.
  }
  have HrhoL3_tr_pos : 0 < @complex.Re R (\Tr rhoL3).
    by rewrite HrhoL3_tr1 re_realid ltr01.
  have HrhoL3_den : rhoL3 \is denlf.
  { apply/denlfP; split=> //.
    have Hreal : (\Tr rhoL3 : C) = (@complex.Re R (\Tr rhoL3))%:C
      by rewrite RRe_real // ger0_real // psdlf_trlf.
    by rewrite Hreal lecR. }
  have HrhoL3_rank : \Rank rhoL3 = 1%N.
  {
    rewrite /rhoL3 /lfrank mx2hK.
    have HUtU_ZCE : U_ZCE^*t *m U_ZCE = 1%:M.
    {
      have := unitarymxK (@tenv_mxU_adj_unitarymx R _ HL S_ZC
        [set Elbl] disZC_E).
      by rewrite /U_ZCE adjmxK.
    }
    have HUU_ZCE : U_ZCE *m U_ZCE^*t = 1%:M.
    {
      exact: unitarymxK (@tenv_mxU_unitarymx R _ HL S_ZC [set Elbl]).
    }
    have Hrank_conj : forall m n (R0 : 'M[C]_(m, n)) (A0 : 'M[C]_n),
        (\rank (R0 *m A0 *m R0^*t) <= \rank A0)%N.
    {
      move=> m0 n0 R0 A0.
      exact: leq_trans (mxrankM_maxl _ _) (mxrankM_maxr _ _).
    }
    have Hrank_unit_conj : forall n (U A0 : 'M[C]_n),
        U^*t *m U = 1%:M -> U *m U^*t = 1%:M ->
        \rank (U *m A0 *m U^*t) = \rank A0.
    {
      move=> n0 U A0 HUtU HUU.
      apply/eqP; rewrite eqn_leq.
      apply/andP; split; first exact: Hrank_conj.
      have Hback :
          U^*t *m (U *m A0 *m U^*t) *m (U^*t)^*t = A0.
      {
        by rewrite adjmxK -!mulmxA HUtU !mulmxA HUtU mul1mx mulmx1.
      }
      rewrite -[X in (\rank X <= _)%N]Hback.
      exact: Hrank_conj.
    }
    have Hrank_iso_conj : forall m n (U : 'M[C]_(m, n)) (A0 : 'M[C]_n),
        U^*t *m U = 1%:M ->
        \rank (U *m A0 *m U^*t) = \rank A0.
    {
      move=> m0 n0 U A0 HUtU.
      apply/eqP; rewrite eqn_leq.
      apply/andP; split; first exact: Hrank_conj.
      have Hback :
          U^*t *m (U *m A0 *m U^*t) *m (U^*t)^*t = A0.
      {
        by rewrite adjmxK -!mulmxA HUtU !mulmxA HUtU mul1mx mulmx1.
      }
      rewrite -[X in (\rank X <= _)%N]Hback.
      exact: Hrank_conj.
    }
    have Hraw_rank : \rank rho_raw_prod = 1%N.
    {
      by rewrite /rho_raw_prod mxrank_cast HZC_rank.
    }
    have Hinner_rank :
        \rank ((Q_ZC *t I_E) *m rho_raw_prod *m
               (Q_ZC^*t *t I_E)) = \rank rho_raw_prod.
    {
      rewrite -HQZC_E_adj.
      exact: Hrank_unit_conj HQtQ_ZC_E HQQt_ZC_E.
    }
    have Hinner_label_rank :
        \rank rho_inner_labelled = \rank rho_raw_prod.
    {
      by rewrite /rho_inner_labelled mxrank_cast Hinner_rank.
    }
    rewrite /rho_prod_labelled.
    have Houter_rank :
        \rank (U_ZCE *m rho_inner_labelled *m U_ZCE^*t) =
        \rank rho_inner_labelled.
    {
      exact: (@Hrank_iso_conj _ _ U_ZCE rho_inner_labelled HUtU_ZCE).
    }
    rewrite Houter_rank.
    by rewrite Hinner_label_rank Hraw_rank.
  }
  have Hdual :=
    @minmax_dual R _ HL [set Zlbl] [set Clbl] [set Elbl]
      disZC disZE disCE [set Cplbl] [set Cpplbl]
      disZCp disZCpp disCCp disCCpp disCpCpp
      HdimZ_Cp HdimE_Cp_Cpp HdimC_Cpp rhoL3 HrhoL3_den HrhoL3_rank.
  have Hmax_local :
      hmax_mx rhoZ =
      hmax [set Clbl]
        (@ptrace_cast3C R _ HL [set Zlbl] [set Clbl]
          [set Elbl] disZE disCE rhoL3).
  {
    have HrhoZ_tr1 : \tr rhoZ = 1.
    {
      have /den1mxP [_ /eqP Htr1] := HZC_den1.
      by rewrite -HZC_ptr -tr_ptrace2 Htr1.
    }
    pose rhoZL :=
      @ptrace_cast3C R _ HL [set Zlbl] [set Clbl] [set Elbl]
        disZE disCE rhoL3.
    have HdimZC_prod :
        (dim 'H[HL]_[set Zlbl] * dim 'H[HL]_[set Clbl] = nz * nc)%N.
    {
      by rewrite -(dim_set1 HL Zlbl) -(dim_set1 HL Clbl) HHLZ HHLC.
    }
    pose rhoZL_prod : 'M[C]_(nz * nc) :=
      castmx (HdimZC_prod, HdimZC_prod)
        (biprod_mx disZC rhoZL).
    have HrhoZL_prod : rhoZL_prod = rhoZ.
    {
      have HrhoZL_cast : rhoZL = ptrace_cast disZC_E rhoL3.
      {
        rewrite /rhoZL /ptrace_cast /ptrace_cast3C /ptrace_cast_gen.
        have Hdu :
            setDU3_C disZE disCE = setDU_r disZC_E := eq_irrelevance _ _.
        by rewrite Hdu.
      }
      rewrite /rhoZL_prod /biprod_mx HrhoZL_cast.
      rewrite (h2mx_ptrace_cast_ptrace2 disZC_E rhoL3).
      (* TeX eqn:mo1 bookkeeping: product-coordinate labelled `ZC`
         agrees with the raw `(Z*C)` marginal of the regrouped
         Stinespring state. *)
      have Hprod_ptr :
          castmx (HdimZC_prod, HdimZC_prod)
            ((let Q :=
                castmx
                  (tenv_dim disZC, erefl (dim 'H[HL]_[set Zlbl] *
                                           dim 'H[HL]_[set Clbl]))
                  (@tenv_mxU R _ HL [set Zlbl] [set Clbl]) in
              Q^*t *m
              castmx (tenv_dim disZC, tenv_dim disZC)
                (ptrace2
                  ((@tenv_mxU R _ HL
                      ([set Zlbl] :|: [set Clbl]) [set Elbl])^*t *m
                    h2mx rhoL3 *m
                    @tenv_mxU R _ HL
                      ([set Zlbl] :|: [set Clbl]) [set Elbl])) *m Q)) =
          ptrace2 rhoZCZpAB.
      {
        rewrite -/Q_ZC -/U_ZCE.
        have Hinner_cast_ptr :
            castmx (tenv_dim disZC, tenv_dim disZC)
              (ptrace2 rho_inner_labelled) =
            ptrace2
              ((Q_ZC *t I_E) *m
                (rho_raw_prod *m (Q_ZC^*t *t I_E))).
        {
          have Hptrace2_cast_left :
              forall m m' n (em : m = m') (A : 'M[C]_(m' * n)),
              castmx (em, em)
                (ptrace2
                  (castmx (esym (f_equal (fun k => (k * n)%N) em),
                           esym (f_equal (fun k => (k * n)%N) em)) A)) =
              ptrace2 A.
          {
            move=> m m' n em A.
            by case: m' / em A => A; rewrite castmx_id.
          }
          rewrite /rho_inner_labelled.
          have Hcol_eq :
              HdimZCE_col =
              f_equal (fun n => (n * dim 'H[HL]_[set Elbl])%N)
                (tenv_dim disZC) := eq_irrelevance _ _.
          rewrite Hcol_eq.
          transitivity
            (ptrace2 (((Q_ZC *t I_E) *m rho_raw_prod) *m
              (Q_ZC^*t *t I_E))).
          - exact: Hptrace2_cast_left.
          - by rewrite mulmxA.
        }
        have Houter_unit_ptr :
            castmx (tenv_dim disZC, tenv_dim disZC)
              (ptrace2
                (U_ZCE^*t *m h2mx rhoL3 *m U_ZCE)) =
            ptrace2
              ((Q_ZC *t I_E) *m
                (rho_raw_prod *m (Q_ZC^*t *t I_E))).
        {
          have HUtU_ZCE : U_ZCE^*t *m U_ZCE = 1%:M.
          {
            have := unitarymxK (@tenv_mxU_adj_unitarymx R _ HL S_ZC
              [set Elbl] disZC_E).
            by rewrite /U_ZCE adjmxK.
          }
          rewrite /rhoL3 mx2hK /rho_prod_labelled.
          rewrite !mulmxA HUtU_ZCE mul1mx -!mulmxA HUtU_ZCE mulmx1.
          exact: Hinner_cast_ptr.
        }
        have Hptr_inner :
            ptrace2
              ((Q_ZC *t I_E) *m
                (rho_raw_prod *m (Q_ZC^*t *t I_E))) =
            Q_ZC *m ptrace2 rho_raw_prod *m Q_ZC^*t.
        {
          by rewrite mulmxA /I_E ptrace2_mulmxI ptrace2_mulImx.
        }
        have Hraw_ptr_cast :
            castmx (HdimZC_prod, HdimZC_prod) (ptrace2 rho_raw_prod) =
            ptrace2 rhoZCZpAB.
        {
          have Hptrace2_cast_both :
              forall m m' n n' (em : m = m') (en : n = n')
                (A : 'M[C]_(m' * n')),
              castmx (em, em)
                (ptrace2
                  (castmx (esym (f_equal2 muln em en),
                           esym (f_equal2 muln em en)) A)) =
              ptrace2 A.
          {
            move=> m m' n n' em en A.
            case: m' / em in A *.
            case: n' / en in A *.
            rewrite (eq_irrelevance
              (f_equal2 muln (erefl m) (erefl n)) (erefl (m * n)%N)).
            by rewrite castmx_id.
          }
          rewrite /rho_raw_prod.
          have HdimE_prod : dim 'H[HL]_[set Elbl] = nz * na * nb.
          {
            by rewrite -(dim_set1 HL Elbl) HHLE.
          }
          have Hraw_eq :
              HdimZCE_raw =
              f_equal2 muln HdimZC_prod HdimE_prod := eq_irrelevance _ _.
          rewrite Hraw_eq.
          exact: Hptrace2_cast_both.
        }
        rewrite Houter_unit_ptr Hptr_inner.
        have Hcancel_ZC :
            Q_ZC^*t *m (Q_ZC *m ptrace2 rho_raw_prod *m Q_ZC^*t) *m
              Q_ZC =
            ptrace2 rho_raw_prod.
        {
          by rewrite !mulmxA HQtQ_ZC mul1mx -!mulmxA HQtQ_ZC mulmx1.
        }
        change (castmx (HdimZC_prod, HdimZC_prod)
          (Q_ZC^*t *m (Q_ZC *m ptrace2 rho_raw_prod *m Q_ZC^*t) *m
            Q_ZC) = ptrace2 rhoZCZpAB).
        rewrite Hcancel_ZC.
        exact: Hraw_ptr_cast.
          }
          by rewrite Hprod_ptr HZC_ptr.
          }
          (* Encoding bridge only: EUR's proof uses the ZC max marginal;
             this step identifies the labelled marginal with its product
             matrix coordinates. *)
          have HdimZ_prod : dim 'H[HL]_[set Zlbl] = nz.
          {
            by rewrite -(dim_set1 HL Zlbl) HHLZ.
          }
          have HdimC_prod : dim 'H[HL]_[set Clbl] = nc.
          {
            by rewrite -(dim_set1 HL Clbl) HHLC.
          }
          have HrhoZL_cast : rhoZL = ptrace_cast disZC_E rhoL3.
          {
            rewrite /rhoZL /ptrace_cast /ptrace_cast3C /ptrace_cast_gen.
            have Hdu :
                setDU3_C disZE disCE = setDU_r disZC_E := eq_irrelevance _ _.
            by rewrite Hdu.
          }
          have HrhoZL_psd : rhoZL \is psdlf.
          {
            rewrite HrhoZL_cast.
            exact: ptrace_cast_psdlf HrhoL3_psd.
          }
          have Hproduct_hmax :
              hmax [set Clbl] rhoZL =
              hmax_mx (biprod_mx disZC rhoZL)
            by exact: (hmax_labelled_product_mx
              (A := [set Zlbl]) (B := [set Clbl])
              disZC HrhoZL_psd).
          have Hmatrix_hmax :
              hmax_mx (biprod_mx disZC rhoZL) =
              hmax_mx rhoZ.
          {
            have Hcast_hmax :
                forall nZ nC
                  (eZ : dim 'H[HL]_[set Zlbl] = nZ)
                  (eC : dim 'H[HL]_[set Clbl] = nC)
                  (X : 'M[C]_(dim 'H[HL]_[set Zlbl] *
                              dim 'H[HL]_[set Clbl])),
                  hmax_mx X =
                  hmax_mx (castmx (f_equal2 muln eZ eC,
                                    f_equal2 muln eZ eC) X).
            {
              move=> nZ nC eZ eC X.
              case: nZ / eZ in X *.
              case: nC / eC in X *.
              rewrite (eq_irrelevance
                (f_equal2 muln (erefl _) (erefl _)) (erefl _)).
              congr hmax_mx.
            }
            rewrite -HrhoZL_prod /rhoZL_prod.
            have Hdim_prod_eq :
                HdimZC_prod = f_equal2 muln HdimZ_prod HdimC_prod
              := eq_irrelevance _ _.
            rewrite Hdim_prod_eq.
            exact: Hcast_hmax.
          }
          by rewrite Hproduct_hmax Hmatrix_hmax.
        }
      have Hmin_local :
      hmin_mx rhoZZpAB =
      hmin [set Elbl]
        (@ptrace_cast3B R _ HL [set Zlbl] [set Clbl]
          [set Elbl] disZC disCE rhoL3).
    {
      pose S_ZE := [set Zlbl] :|: [set Elbl].
      pose rhoZEL :=
        @ptrace_cast3B R _ HL [set Zlbl] [set Clbl] [set Elbl]
          disZC disCE rhoL3.
      have HdimC_prod : dim 'H[HL]_[set Clbl] = nc.
      {
        by rewrite -(dim_set1 HL Clbl) HHLC.
      }
      have HdimE_prod : dim 'H[HL]_[set Elbl] = nz * na * nb.
      {
        by rewrite -(dim_set1 HL Elbl) HHLE.
      }
    have HdimZ_prod : dim 'H[HL]_[set Zlbl] = nz.
    {
      by rewrite -(dim_set1 HL Zlbl) HHLZ.
    }
    have HdimZE_prod :
        (dim 'H[HL]_[set Zlbl] * dim 'H[HL]_[set Elbl] =
         nz * (nz * na * nb))%N.
    {
      by rewrite -(dim_set1 HL Zlbl) -(dim_set1 HL Elbl) HHLZ HHLE.
    }
    have HdimZE_cast_tensor :
        forall (sigmaE : 'M[C]_(dim 'H[HL]_[set Elbl])),
        castmx (HdimZE_prod, HdimZE_prod)
          ((1%:M : 'M[C]_(dim 'H[HL]_[set Zlbl])) *t sigmaE) =
        (1%:M : 'M[C]_nz) *t
          castmx (HdimE_prod, HdimE_prod) sigmaE.
    {
      have Hcast_tensor_gen :
          forall dz de nz0 ne
            (ez : dz = nz0) (ee : de = ne) (sigmaE : 'M[C]_de),
          castmx (f_equal2 muln ez ee, f_equal2 muln ez ee)
            ((1%:M : 'M[C]_dz) *t sigmaE) =
          (1%:M : 'M[C]_nz0) *t castmx (ee, ee) sigmaE.
      {
        move=> dz de nz0 ne ez ee sigmaE.
        case: nz0 / ez.
        case: ne / ee.
        by rewrite castmx_id.
      }
      move=> sigmaE.
      have Hprod_eq :
          HdimZE_prod = f_equal2 muln HdimZ_prod HdimE_prod
        by apply: eq_irrelevance.
      rewrite Hprod_eq.
      exact: Hcast_tensor_gen.
    }
    pose rhoZEL_prod : 'M[C]_(nz * (nz * na * nb)) :=
      castmx (HdimZE_prod, HdimZE_prod)
        (biprod_mx disZE rhoZEL).
    (* TeX eqn:mo1 bookkeeping: the complementary marginal of the
       Stinespring `ZC|Z'AB` regrouping is the paper's
       `rho_ZZ'AB`, in product `Z | Z'AB` coordinates. *)
    have HrhoZEL_prod : rhoZEL_prod = rhoZZpAB.
    {
      pose rhoZE_raw : 'M[C]_(nz * (nz * na * nb)) :=
        \matrix_(i, j)
          let iZE := mxtens_unindex i in
          let jZE := mxtens_unindex j in
          \sum_(c : 'I_nc)
            rhoZCZpAB
              (mxtens_index (mxtens_index (iZE.1, c), iZE.2))
              (mxtens_index (mxtens_index (jZE.1, c), jZE.2)).
      pose rhoZEC_raw : 'M[C]_((nz * (nz * na * nb)) * nc) :=
        \matrix_(i, j)
          let iZEC := mxtens_unindex i in
          let jZEC := mxtens_unindex j in
          let iZE := mxtens_unindex iZEC.1 in
          let jZE := mxtens_unindex jZEC.1 in
          rhoZCZpAB
            (mxtens_index (mxtens_index (iZE.1, iZEC.2), iZE.2))
            (mxtens_index (mxtens_index (jZE.1, jZEC.2), jZE.2)).
      have Hptrace_rhoZEC_raw : ptrace2 rhoZEC_raw = rhoZE_raw.
      {
        have ptrace2E' : forall s t (B : 'M[C]_(s * t)) r1 r2,
            (ptrace2 B) r1 r2 =
            \sum_(k0 : 'I_t) B (mxtens_index (r1, k0))
                               (mxtens_index (r2, k0)).
        {
          move=> s t B r1 r2; rewrite ptrace2E1 ptrace1E.
          by apply: eq_bigr => k0 _; rewrite mxE !mxtens_indexK.
        }
        apply/matrixP=> i j.
        rewrite /rhoZEC_raw /rhoZE_raw ptrace2E' mxE.
        apply: eq_bigr=> c _.
        by rewrite mxE !mxtens_indexK.
      }
      have Hptrace_cast_gen_cast :
          forall (S S' T U : {set 'I_5})
            (eqSS' : S = S') (eq1 : S :\: T = U)
            (eq2 : S' :\: T = U) (f : 'F[HL]_S),
          castlf (eq1, eq1) (\Tr_(T) f) =
          castlf (eq2, eq2) (\Tr_(T) (castlf (eqSS', eqSS') f)).
      {
        move=> S S' T U eqSS' eq1 eq2 f.
        case: S' / eqSS' in f eq2 *.
        rewrite castlf_id.
        have -> : eq2 = eq1 by apply: eq_irrelevance.
        by [].
      }
      have disZE_C : [disjoint S_ZE & [set Clbl]].
      {
        by rewrite /S_ZE disjointUX disZC disjoint_sym disCE.
      }
      have eqZCE_ZEC : S_ZCE3 = S_ZE :|: [set Clbl].
      {
        apply/setP=> x.
        rewrite /S_ZCE3 /S_ZC /S_ZE !inE.
        by case: (x == Zlbl); case: (x == Clbl); case: (x == Elbl).
      }
      have HrhoZEL_cast :
          rhoZEL =
          ptrace_cast disZE_C (castlf (eqZCE_ZEC, eqZCE_ZEC) rhoL3).
      {
        rewrite /rhoZEL /ptrace_cast3B /ptrace_cast /ptrace_cast_gen.
        exact: Hptrace_cast_gen_cast.
      }
      have HrhoZEL_ptrace_raw : rhoZEL_prod = ptrace2 rhoZEC_raw.
      {
        pose Q_ZE : 'M[C]_(dim 'H[HL]_[set Zlbl] *
                            dim 'H[HL]_[set Elbl]) :=
          castmx (tenv_dim disZE, erefl _)
            (@tenv_mxU R _ HL [set Zlbl] [set Elbl]).
        pose U_ZEC := @tenv_mxU R _ HL S_ZE [set Clbl].
        pose I_C : 'M[C]_(dim 'H[HL]_[set Clbl]) := 1%:M.
        pose rho_ZEC_label :=
          U_ZEC^*t *m h2mx (castlf (eqZCE_ZEC, eqZCE_ZEC) rhoL3) *m
            U_ZEC.
        have HdimZEC_col :
            (dim 'H[HL]_S_ZE * dim 'H[HL]_[set Clbl] =
             (dim 'H[HL]_[set Zlbl] * dim 'H[HL]_[set Elbl]) *
               dim 'H[HL]_[set Clbl])%N.
        {
          by rewrite /S_ZE (tenv_dim disZE).
        }
        have HdimZEC_raw :
            (((dim 'H[HL]_[set Zlbl] * dim 'H[HL]_[set Elbl]) *
                 dim 'H[HL]_[set Clbl]) =
             (nz * (nz * na * nb)) * nc)%N.
        {
          by rewrite HdimZ_prod HdimE_prod HdimC_prod.
        }
        pose rhoZEC_prod : 'M[C]_((nz * (nz * na * nb)) * nc) :=
          castmx (HdimZEC_raw, HdimZEC_raw)
            ((Q_ZE^*t *t I_C) *m
              castmx (HdimZEC_col, HdimZEC_col) rho_ZEC_label *m
              (Q_ZE *t I_C)).
        have Hptrace_prod : rhoZEL_prod = ptrace2 rhoZEC_prod.
        {
          rewrite /rhoZEL_prod /biprod_mx
            HrhoZEL_cast.
          rewrite (h2mx_ptrace_cast_ptrace2 disZE_C
            (castlf (eqZCE_ZEC, eqZCE_ZEC) rhoL3)).
          rewrite -/Q_ZE -/rho_ZEC_label.
          have Hptrace2_cast_forward :
              forall m m' n n' (em : m = m') (en : n = n')
                (A : 'M[C]_(m * n)),
              ptrace2
                (castmx (f_equal2 muln em en,
                         f_equal2 muln em en) A) =
              castmx (em, em) (ptrace2 A).
          {
            move=> m m' n n' em en A.
            case: m' / em in A *.
            case: n' / en in A *.
            rewrite (eq_irrelevance
              (f_equal2 muln (erefl m) (erefl n)) (erefl (m * n)%N)).
            by rewrite castmx_id.
          }
          have Hptrace_conj :
              ptrace2 rhoZEC_prod =
              castmx (HdimZE_prod, HdimZE_prod)
                (Q_ZE^*t *m
                  castmx (tenv_dim disZE, tenv_dim disZE)
                    (ptrace2 rho_ZEC_label) *m Q_ZE).
          {
            rewrite /rhoZEC_prod.
            have Hraw_eq :
                HdimZEC_raw =
                f_equal2 muln HdimZE_prod HdimC_prod :=
              eq_irrelevance _ _.
            rewrite Hraw_eq Hptrace2_cast_forward.
            congr (castmx (HdimZE_prod, HdimZE_prod)).
            rewrite /I_C ptrace2_mulmxI ptrace2_mulImx.
            have Hcol_eq :
                HdimZEC_col =
                f_equal (fun n => (n * dim 'H[HL]_[set Clbl])%N)
                  (tenv_dim disZE) := eq_irrelevance _ _.
            rewrite Hcol_eq.
            congr (Q_ZE^*t *m _ *m Q_ZE).
            have Hcast_eq :
                f_equal (muln^~ (dim 'H[HL]_[set Clbl]))
                  (tenv_dim disZE) =
                f_equal2 muln (tenv_dim disZE)
                  (erefl (dim 'H[HL]_[set Clbl])) :=
              eq_irrelevance _ _.
            rewrite Hcast_eq Hptrace2_cast_forward.
            by [].
          }
          by rewrite Hptrace_conj.
        }
        have Hptrace_prod_raw : ptrace2 rhoZEC_prod = rhoZE_raw.
        {
          have ptrace2E'' : forall s t (B : 'M[C]_(s * t)) r1 r2,
              (ptrace2 B) r1 r2 =
              \sum_(k0 : 'I_t) B (mxtens_index (r1, k0))
                                 (mxtens_index (r2, k0)).
          {
            move=> s t B r1 r2; rewrite ptrace2E1 ptrace1E.
            by apply: eq_bigr => k0 _; rewrite mxE !mxtens_indexK.
          }
          have Hh2mx_castlf :
              forall (S S' : {set 'I_5}) (eqSS' : S = S')
                (f : 'F[HL]_S),
              h2mx (castlf (eqSS', eqSS') f) =
              castmx (f_equal (fun T => dim 'H[HL]_T) eqSS',
                      f_equal (fun T => dim 'H[HL]_T) eqSS')
                (h2mx f).
          {
            move=> S S' eqSS' f.
            case: S' / eqSS' in f *.
            by rewrite castlf_id castmx_id.
          }
          have tensmxE_any :
              forall m n p q (A : 'M[C]_(m, n)) (B : 'M[C]_(p, q))
                (i0 : 'I_(m * p)) (j0 : 'I_(n * q)),
              (A *t B) i0 j0 =
              A (mxtens_unindex i0).1 (mxtens_unindex j0).1 *
              B (mxtens_unindex i0).2 (mxtens_unindex j0).2.
          {
            move=> m n p q A B i0 j0.
            case Ei: (mxtens_unindex i0)=> [i1 i2].
            case Ej: (mxtens_unindex j0)=> [j1 j2].
            rewrite -(mxtens_unindexK i0) Ei -(mxtens_unindexK j0) Ej.
            by rewrite tensmxE.
          }
          have Hcast_ZEC_unindex :
              forall (ze : 'I_(nz * (nz * na * nb))) (c0 : 'I_nc),
              mxtens_unindex
                (cast_ord (esym HdimZEC_raw) (mxtens_index (ze, c0))) =
              (cast_ord (esym HdimZE_prod) ze,
               cast_ord (esym HdimC_prod) c0).
          {
            move=> ze c0.
            case Ecast: (mxtens_unindex
                (cast_ord (esym HdimZEC_raw) (mxtens_index (ze, c0)))) =>
              [ze' c'].
            apply: (can_inj (@mxtens_indexK _ _)).
            rewrite -Ecast mxtens_unindexK.
            apply/val_inj=> /=.
            by rewrite HdimC_prod.
          }
          have HdimZC_prod_local :
              (dim 'H[HL]_[set Zlbl] * dim 'H[HL]_[set Clbl] =
               nz * nc)%N.
          {
            by rewrite -(dim_set1 HL Zlbl) -(dim_set1 HL Clbl) HHLZ HHLC.
          }
          have Hcast_ZC_index :
              forall (z0 : 'I_nz) (c0 : 'I_nc),
              cast_ord HdimZC_prod_local
                (mxtens_index (cast_ord (esym HdimZ_prod) z0,
                                cast_ord (esym HdimC_prod) c0)) =
              mxtens_index (z0, c0).
          {
            move=> z0 c0.
            apply/val_inj=> /=.
            by rewrite HdimC_prod.
          }
          have Hcast_ZCE_unindex :
              forall (zc : 'I_(nz * nc)) (e0 : 'I_(nz * na * nb)),
              mxtens_unindex
                (cast_ord (esym HdimZCE_raw) (mxtens_index (zc, e0))) =
              (cast_ord (esym HdimZC_prod_local) zc,
               cast_ord (esym HdimE_prod) e0).
          {
            move=> zc e0.
            case Ecast: (mxtens_unindex
                (cast_ord (esym HdimZCE_raw) (mxtens_index (zc, e0)))) =>
              [zc' e'].
            apply: (can_inj (@mxtens_indexK _ _)).
            rewrite -Ecast mxtens_unindexK.
            apply/val_inj=> /=.
            by rewrite HdimE_prod.
          }
          have Hcast_ZCE_unindex_fw :
              forall (zc : 'I_(dim 'H[HL]_[set Zlbl] *
                                dim 'H[HL]_[set Clbl]))
                     (e0 : 'I_(dim 'H[HL]_[set Elbl])),
              mxtens_unindex
                (cast_ord HdimZCE_raw (mxtens_index (zc, e0))) =
              (cast_ord HdimZC_prod_local zc,
               cast_ord HdimE_prod e0).
          {
            move=> zc e0.
            have Hraw_eq :
                HdimZCE_raw =
                f_equal2 muln HdimZC_prod_local HdimE_prod
              by apply: eq_irrelevance.
            rewrite Hraw_eq.
            apply: (can_inj (@mxtens_indexK _ _)).
            rewrite mxtens_unindexK.
            apply/val_inj=> /=.
            change ((zc * dim 'H[HL]_[set Elbl] + e0)%N =
                    (zc * (nz * na * nb) + e0)%N).
            exact: (f_equal2 addn
              (f_equal2 muln (erefl _) HdimE_prod) (erefl _)).
          }
          have Hcast_ZEC_col_unindex :
              forall (ze : 'I_(dim 'H[HL]_S_ZE))
                     (c0 : 'I_(dim 'H[HL]_[set Clbl])),
              mxtens_unindex
                (cast_ord (esym HdimZEC_col)
                  (mxtens_index (cast_ord (tenv_dim disZE) ze, c0))) =
              (ze, c0).
          {
            move=> ze c0.
            case Ecast: (mxtens_unindex
                (cast_ord (esym HdimZEC_col)
                  (mxtens_index (cast_ord (tenv_dim disZE) ze, c0)))) =>
              [ze' c'].
            apply: (can_inj (@mxtens_indexK _ _)).
            rewrite -Ecast mxtens_unindexK.
            apply/val_inj=> /=.
            by [].
          }
          have Hcast_ZE_unindex :
              forall (z0 : 'I_nz) (e0 : 'I_(nz * na * nb)),
              mxtens_unindex
                (cast_ord (esym HdimZE_prod) (mxtens_index (z0, e0))) =
              (cast_ord (esym HdimZ_prod) z0,
               cast_ord (esym HdimE_prod) e0).
          {
            move=> z0 e0.
            case Ecast: (mxtens_unindex
                (cast_ord (esym HdimZE_prod)
                  (mxtens_index (z0, e0)))) => [z' e'].
            apply: (can_inj (@mxtens_indexK _ _)).
            rewrite -Ecast mxtens_unindexK.
            apply/val_inj=> /=.
            by rewrite HdimE_prod.
          }
          have Hcast_ZCE_col_unindex :
              forall (zc : 'I_(dim 'H[HL]_S_ZC))
                     (e0 : 'I_(dim 'H[HL]_[set Elbl])),
              mxtens_unindex
                (cast_ord HdimZCE_col (mxtens_index (zc, e0))) =
              (cast_ord (tenv_dim disZC) zc, e0).
          {
            move=> zc e0.
            case Ecast: (mxtens_unindex
                (cast_ord HdimZCE_col (mxtens_index (zc, e0)))) =>
              [zc' e'].
            apply: (can_inj (@mxtens_indexK _ _)).
            rewrite -Ecast mxtens_unindexK.
            apply/val_inj=> /=.
            by [].
          }
          have Hn2i_cast_i2n :
              forall (S S' : {set 'I_5}) (eqSS' : S = S')
                (x : 'Idx[HL]_S),
              n2i (cast_ord
                (f_equal (fun T => dim 'H[HL]_T) eqSS') (i2n x)) =
              castidx eqSS' x.
          {
            move=> S S' eqSS' x.
            case: S' / eqSS' in x *.
            rewrite castidx_id.
            have -> :
                f_equal
                  (fun T : {set 'I_5} => dim 'H[HL]_T) (erefl S) =
                erefl (dim 'H[HL]_S) by apply: eq_irrelevance.
            by rewrite cast_ord_id i2nK.
          }
          have sum_deltaR :
              forall n (a : 'I_n) (F : 'I_n -> C),
              \sum_i F i * ((i == a)%:R : C) = F a.
          {
            move=> n a F.
            rewrite (bigD1 a) //= eqxx mulr1.
            rewrite [X in _ + X]big1 ?addr0 //.
            by move=> i0 /negPf Hi0; rewrite Hi0 mulr0.
          }
          have sum_deltaL :
              forall n (a : 'I_n) (F : 'I_n -> C),
              \sum_i ((i == a)%:R : C) * F i = F a.
          {
            move=> n a F.
            under eq_bigr => i0 _ do rewrite mulrC.
            exact: sum_deltaR.
          }
          have sum_deltaL_sym :
              forall n (a : 'I_n) (F : 'I_n -> C),
              \sum_i ((a == i)%:R : C) * F i = F a.
          {
            move=> n a F.
            under eq_bigr => i0 _ do rewrite eq_sym.
            exact: sum_deltaL.
          }
          have sum_delta_mid :
              forall n (a : 'I_n) (K : C) (F : 'I_n -> C),
              \sum_i K * ((a == i)%:R : C) * F i = K * F a.
          {
            move=> n a K F.
            rewrite (bigD1 a) //= eqxx mulr1.
            rewrite [X in _ + X]big1 ?addr0 //.
            by move=> i0 /negPf Hi0; rewrite eq_sym Hi0 mulr0 mul0r.
          }
          have HQ_ZE_delta :
              forall (jze t : 'I_(dim 'H[HL]_[set Zlbl] *
                                    dim 'H[HL]_[set Elbl])),
              Q_ZE jze t =
              ((jze == cast_ord (tenv_dim disZE) (tenv_indexl t))%:R : C).
          {
            move=> jze t.
            rewrite /Q_ZE castmxE /tenv_mxU mxE.
            pose fZE (x : 'I_(dim 'H[HL]_[set Zlbl] *
                                dim 'H[HL]_[set Elbl])) :=
              tenv_indexr (cast_ord (esym (tenv_dim disZE)) x).
            pose gZE (x : 'I_(dim 'H[HL]_[set Zlbl] *
                                dim 'H[HL]_[set Elbl])) :=
              cast_ord (tenv_dim disZE) (tenv_indexl x).
            have fZE_K : cancel fZE gZE.
            {
              move=> x.
              rewrite /fZE /gZE tenv_indexrK.
              by rewrite cast_ordKV.
            }
            have gZE_K : cancel gZE fZE.
            {
              move=> x.
              rewrite /fZE /gZE cast_ordK.
              exact: tenv_indexlK.
            }
            rewrite cast_ord_id.
            congr (_%:R).
            by rewrite -/(fZE jze) -/(gZE t) (can2_eq fZE_K gZE_K).
          }
          have HQ_ZC_delta :
              forall (jzc t : 'I_(dim 'H[HL]_[set Zlbl] *
                                    dim 'H[HL]_[set Clbl])),
              Q_ZC jzc t =
              ((jzc == cast_ord (tenv_dim disZC) (tenv_indexl t))%:R : C).
          {
            move=> jzc t.
            rewrite /Q_ZC castmxE /tenv_mxU mxE.
            pose fZC (x : 'I_(dim 'H[HL]_[set Zlbl] *
                                dim 'H[HL]_[set Clbl])) :=
              tenv_indexr (cast_ord (esym (tenv_dim disZC)) x).
            pose gZC (x : 'I_(dim 'H[HL]_[set Zlbl] *
                                dim 'H[HL]_[set Clbl])) :=
              cast_ord (tenv_dim disZC) (tenv_indexl x).
            have fZC_K : cancel fZC gZC.
            {
              move=> x.
              rewrite /fZC /gZC tenv_indexrK.
              by rewrite cast_ordKV.
            }
            have gZC_K : cancel gZC fZC.
            {
              move=> x.
              rewrite /fZC /gZC cast_ordK.
              exact: tenv_indexlK.
            }
            rewrite cast_ord_id.
            congr (_%:R).
            by rewrite -/(fZC jzc) -/(gZC t) (can2_eq fZC_K gZC_K).
          }
          have HQZC_E_delta_l :
              forall (p j0 : 'I_((dim 'H[HL]_[set Zlbl] *
                                    dim 'H[HL]_[set Clbl]) *
                                   dim 'H[HL]_[set Elbl])),
              (Q_ZC *t I_E) p j0 =
              ((j0 ==
                mxtens_index
                  (tenv_indexr
                    (cast_ord (esym (tenv_dim disZC))
                      (mxtens_unindex p).1),
                   (mxtens_unindex p).2))%:R : C).
          {
            move=> p j0.
            rewrite tensmxE_any HQ_ZC_delta /I_E mxE.
            case Ep: (mxtens_unindex p)=> [pzc pe].
            case Ej: (mxtens_unindex j0)=> [jzc je].
            rewrite /=.
            have Hzc :
                (pzc ==
                  cast_ord (tenv_dim disZC) (tenv_indexl jzc)) =
                (jzc ==
                  tenv_indexr (cast_ord (esym (tenv_dim disZC)) pzc)).
            {
              rewrite eq_sym.
              pose fZC (x : 'I_(dim 'H[HL]_[set Zlbl] *
                                  dim 'H[HL]_[set Clbl])) :=
                tenv_indexr (cast_ord (esym (tenv_dim disZC)) x).
              pose gZC (x : 'I_(dim 'H[HL]_[set Zlbl] *
                                  dim 'H[HL]_[set Clbl])) :=
                cast_ord (tenv_dim disZC) (tenv_indexl x).
              have fZC_K : cancel fZC gZC.
              {
                move=> x.
                rewrite /fZC /gZC tenv_indexrK.
                by rewrite cast_ordKV.
              }
              have gZC_K : cancel gZC fZC.
              {
                move=> x.
                rewrite /fZC /gZC cast_ordK.
                exact: tenv_indexlK.
              }
              rewrite [jzc == _]eq_sym.
              by rewrite -/(fZC pzc) -/(gZC jzc)
                (can2_eq fZC_K gZC_K).
            }
            rewrite Hzc.
            have Hpair :
                (j0 ==
                  mxtens_index
                    (tenv_indexr (cast_ord (esym (tenv_dim disZC)) pzc),
                     pe)) =
                ((jzc ==
                  tenv_indexr (cast_ord (esym (tenv_dim disZC)) pzc)) &&
                 (je == pe)).
            {
              rewrite -(mxtens_unindexK j0) Ej (inj_eq (can_inj (@mxtens_indexK _ _))).
              by rewrite -pair_eqE.
            }
            rewrite Hpair [je == pe]eq_sym.
            by case: (jzc == _); case: (pe == je);
              rewrite ?mul0r ?mulr0 ?mul1r ?mulr1.
          }
          have HQZC_E_delta_r :
              forall (k q : 'I_((dim 'H[HL]_[set Zlbl] *
                                  dim 'H[HL]_[set Clbl]) *
                                 dim 'H[HL]_[set Elbl])),
              (Q_ZC^*t *t I_E) k q =
              ((k ==
                mxtens_index
                  (tenv_indexr
                    (cast_ord (esym (tenv_dim disZC))
                      (mxtens_unindex q).1),
                   (mxtens_unindex q).2))%:R : C).
          {
            move=> k q.
            rewrite tensmxE_any adjmxE /I_E mxE.
            case Ek: (mxtens_unindex k)=> [kzc ke].
            case Eq: (mxtens_unindex q)=> [qzc qe].
            rewrite /= mxE HQ_ZC_delta conjC_nat.
            have Hzc :
                (qzc ==
                  cast_ord (tenv_dim disZC) (tenv_indexl kzc)) =
                (kzc ==
                  tenv_indexr (cast_ord (esym (tenv_dim disZC)) qzc)).
            {
              rewrite eq_sym.
              pose fZC (x : 'I_(dim 'H[HL]_[set Zlbl] *
                                  dim 'H[HL]_[set Clbl])) :=
                tenv_indexr (cast_ord (esym (tenv_dim disZC)) x).
              pose gZC (x : 'I_(dim 'H[HL]_[set Zlbl] *
                                  dim 'H[HL]_[set Clbl])) :=
                cast_ord (tenv_dim disZC) (tenv_indexl x).
              have fZC_K : cancel fZC gZC.
              {
                move=> x.
                rewrite /fZC /gZC tenv_indexrK.
                by rewrite cast_ordKV.
              }
              have gZC_K : cancel gZC fZC.
              {
                move=> x.
                rewrite /fZC /gZC cast_ordK.
                exact: tenv_indexlK.
              }
              rewrite [kzc == _]eq_sym.
              by rewrite -/(fZC qzc) -/(gZC kzc)
                (can2_eq fZC_K gZC_K).
            }
            rewrite Hzc.
            have Hpair :
                (k ==
                  mxtens_index
                    (tenv_indexr (cast_ord (esym (tenv_dim disZC)) qzc),
                     qe)) =
                ((kzc ==
                  tenv_indexr (cast_ord (esym (tenv_dim disZC)) qzc)) &&
                 (ke == qe)).
            {
              rewrite -(mxtens_unindexK k) Ek (inj_eq (can_inj (@mxtens_indexK _ _))).
              by rewrite -pair_eqE.
            }
            rewrite Hpair mxE.
            by case: (kzc == _); case: (ke == qe);
              rewrite ?mul0r ?mulr0 ?mul1r ?mulr1.
          }
          have Htenv_adj_conj_entry :
              forall (A B : {set 'I_5}) (disAB : [disjoint A & B])
                (M0 : 'M[C]_(dim 'H[HL]_(A :|: B)))
                (p q : 'I_(dim 'H[HL]_A * dim 'H[HL]_B)),
              ((@tenv_mxU R _ HL A B)^*t *m M0 *m
                @tenv_mxU R _ HL A B) p q =
              M0 (@tenv_indexl R _ HL A B p)
                 (@tenv_indexl R _ HL A B q).
          {
            move=> A B disAB M0 p q.
            rewrite mxE
              (bigD1 (@tenv_indexl R _ HL A B q)) //= big1 ?addr0.
            2: {
              move=> k /negPf Hk.
              rewrite !mxE
                  (can2_eq (@tenv_indexrK R _ HL A B)
                  (tenv_indexlK disAB)).
              by rewrite Hk !mulr0.
            }
            rewrite mxE
              (bigD1 (@tenv_indexl R _ HL A B p)) //= big1 ?addr0.
            2: {
              move=> k /negPf Hk.
              rewrite adjmxE !mxE
                  (can2_eq (@tenv_indexrK R _ HL A B)
                  (tenv_indexlK disAB)).
              by rewrite Hk conjC0 !mul0r.
            }
            by rewrite adjmxE !mxE (tenv_indexlK disAB)
              (tenv_indexlK disAB) !eqxx !mulr1 conjC1 mul1r.
          }
          have Htenv_conj_adj_entry :
              forall (A B : {set 'I_5})
                (M0 : 'M[C]_(dim 'H[HL]_A * dim 'H[HL]_B))
                (p q : 'I_(dim 'H[HL]_(A :|: B))),
              (@tenv_mxU R _ HL A B *m M0 *m
                (@tenv_mxU R _ HL A B)^*t) p q =
              M0 (@tenv_indexr R _ HL A B p)
                 (@tenv_indexr R _ HL A B q).
          {
            move=> A B M0 p q.
            rewrite mxE
              (bigD1 (@tenv_indexr R _ HL A B q)) //= big1 ?addr0.
            2: {
              move=> k /negPf Hk.
              by rewrite adjmxE !mxE eq_sym Hk conjC0 mulr0.
            }
            rewrite mxE
              (bigD1 (@tenv_indexr R _ HL A B p)) //= big1 ?addr0.
            2: by move=> k /negPf Hk; rewrite !mxE eq_sym Hk mul0r.
            by rewrite adjmxE !mxE !eqxx conjC1 !mulr1 mul1r.
          }
          (* TeX eqn:mo1 bookkeeping: the cast from the labelled
             `(Z,E),C` order to `(Z,C),E` keeps the visible `Z`
             coordinate fixed, moves `C` into the left tensor factor,
             and leaves the environment coordinate as the right factor. *)
          have Hidx_ZEC_ZCE_assoc :
              forall (z : 'Idx[HL]_[set Zlbl])
                     (e0 : 'Idx[HL]_[set Elbl])
                     (c0 : 'Idx[HL]_[set Clbl]),
              idxSl
                (castidx (esym eqZCE_ZEC)
                  (idxU (idxU z e0 : 'Idx[HL]_S_ZE) c0)) =
                (idxU z c0 : 'Idx[HL]_S_ZC) /\
              idxSr
                (castidx (esym eqZCE_ZEC)
                  (idxU (idxU z e0 : 'Idx[HL]_S_ZE) c0)) = e0.
          {
            move=> z e0 c0.
            pose eAB := (idxU (idxU z e0 : 'Idx[HL]_S_ZE) c0 :
              'Idx[HL]_(S_ZE :|: [set Clbl])).
            have HsubZC_ZEC : S_ZC :<=: S_ZE :|: [set Clbl].
            {
              apply/mathcomp.boot.fintype.subsetP=> x.
              rewrite /S_ZC /S_ZE !inE.
              by case/orP=> ->; rewrite ?orbT.
            }
            have HsubE_ZEC : [set Elbl] :<=: S_ZE :|: [set Clbl].
            {
              apply/mathcomp.boot.fintype.subsetP=> x.
              by rewrite /S_ZE !inE => ->; rewrite orbT.
            }
            have Hleft :
                idxSl (castidx (esym eqZCE_ZEC) eAB) =
                (idxU z c0 : 'Idx[HL]_S_ZC).
            {
              apply/eqP.
              rewrite -idxBE.
              apply/andP; split; apply/eqP.
              - rewrite !idxSl_idxR !idxRA.
                rewrite (@idxR_castR R _ HL [set Zlbl]
                  (S_ZE :|: [set Clbl]) S_ZCE3
                  (esym eqZCE_ZEC)
                  (mathcomp.boot.fintype.subset_trans
                    (mathcomp.boot.finset.subsetUl
                      [set Zlbl] [set Clbl])
                    HsubZC_ZEC)
                  (mathcomp.boot.fintype.subset_trans
                    (mathcomp.boot.finset.subsetUl
                      [set Zlbl] [set Clbl])
                    (mathcomp.boot.finset.subsetUl
                      S_ZC [set Elbl])) eAB).
                rewrite -idxSl_idxR (idxSUl z c0) -[RHS](idxSUl z e0).
                rewrite -[idxU z e0](@idxSUl R _ HL S_ZE [set Clbl]
                  (idxU z e0) c0).
                rewrite !idxSl_idxR !idxRA.
                by congr (idxR _ eAB); apply: eq_irrelevance.
              - rewrite !idxSr_idxR !idxRA.
                rewrite (@idxR_castR R _ HL [set Clbl]
                  (S_ZE :|: [set Clbl]) S_ZCE3
                  (esym eqZCE_ZEC)
                  (mathcomp.boot.fintype.subset_trans
                    (mathcomp.boot.finset.subsetUr
                      [set Zlbl] [set Clbl])
                    HsubZC_ZEC)
                  (mathcomp.boot.fintype.subset_trans
                    (mathcomp.boot.finset.subsetUr
                      [set Zlbl] [set Clbl])
                    (mathcomp.boot.finset.subsetUl
                      S_ZC [set Elbl])) eAB).
                rewrite -idxSr_idxR (idxSUr disZC z c0).
                rewrite -[RHS](idxSUr disZE_C (idxU z e0) c0)
                  idxSr_idxR.
                by congr (idxR _ eAB); apply: eq_irrelevance.
            }
            have Hright :
                idxSr (castidx (esym eqZCE_ZEC) eAB) = e0.
            {
              rewrite idxSr_idxR.
              rewrite (@idxR_castR R _ HL [set Elbl]
                (S_ZE :|: [set Clbl]) S_ZCE3
                (esym eqZCE_ZEC) HsubE_ZEC
                (mathcomp.boot.finset.subsetUr
                  S_ZC [set Elbl]) eAB).
              rewrite -[RHS](idxSUr disZE z e0).
              rewrite -[idxU z e0](@idxSUl R _ HL S_ZE [set Clbl]
                (idxU z e0) c0) idxSr_idxR idxSl_idxR.
              rewrite idxRA.
              by congr (idxR _ eAB); apply: eq_irrelevance.
            }
            by split.
          }
          apply/matrixP=> i j.
          case: (mxtens_indexP i)=> zi ei.
          case: (mxtens_indexP ei)=> zpai bi.
          case: (mxtens_indexP zpai)=> zpi ai.
          case: (mxtens_indexP j)=> zj ej.
          case: (mxtens_indexP ej)=> zpaj bj.
          case: (mxtens_indexP zpaj)=> zpj aj.
          rewrite /rhoZE_raw ptrace2E'' mxE.
          apply: eq_bigr=> c _.
          rewrite /rhoZEC_prod /rho_ZEC_label.
          rewrite Hh2mx_castlf /rhoL3 mx2hK /rho_prod_labelled
            /rho_inner_labelled /rho_raw_prod.
          rewrite ?[LHS]castmxE ![LHS]mxE [LHS]mxtens_index_pairV /=.
          rewrite ?mxtens_indexK ?Hcast_ZEC_unindex.
          under eq_bigr => jze _ do
            under eq_bigr => jc _ do rewrite tensmxE_any /I_C mxE
              mxtens_indexK Hcast_ZEC_unindex.
          under eq_bigr => jze _ do
            under eq_bigr => jc _ do rewrite mxE /=.
          under eq_bigr => jze _ do
            under eq_bigr => jc _ do rewrite mulrA.
          under eq_bigr => jze _ do rewrite sum_deltaR.
          under eq_bigr => jze _ do rewrite HQ_ZE_delta.
          under eq_bigr => jze _ do rewrite ?mulrA.
          rewrite sum_deltaR [LHS]mxtens_index_pairV /=.
          under eq_bigr => ize _ do
            under eq_bigr => ic _ do rewrite tensmxE_any adjmxE mxE
              mxtens_indexK ?HQ_ZE_delta ?conjC_nat /I_C mxE
              Hcast_ZEC_unindex /=.
          under eq_bigr => ize _ do
            under eq_bigr => ic _ do rewrite HQ_ZE_delta conjC_nat mxE
              eq_sym.
          under eq_bigr => ize _ do rewrite sum_delta_mid.
          rewrite sum_deltaL_sym.
          rewrite castmxE
            (Htenv_adj_conj_entry S_ZE [set Clbl] disZE_C).
          rewrite castmxE
            (Htenv_conj_adj_entry S_ZC [set Elbl]).
          rewrite /tenv_indexr /tenv_indexl ?Hcast_ZEC_col_unindex
            ?Hcast_ZE_unindex /= ?mxtens_indexK.
          rewrite /Zlbl /Clbl /Elbl /HL /= castmxE !mxE.
          under eq_bigr => k _ do rewrite mxE.
          under eq_bigr => k _ do
            under eq_bigr => j0 _ do rewrite HQZC_E_delta_l.
          under eq_bigr => k _ do rewrite sum_deltaL.
          under eq_bigr => k _ do rewrite HQZC_E_delta_r.
          rewrite sum_deltaR castmxE.
          set rowL := (X in rhoZCZpAB X _).
          set colL := (X in rhoZCZpAB _ X).
          set rowR := mxtens_index
            (mxtens_index (zi, c), mxtens_index (mxtens_index (zpi, ai), bi)).
          set colR := mxtens_index
            (mxtens_index (zj, c), mxtens_index (mxtens_index (zpj, aj), bj)).
          have HrowL : rowL = rowR.
          {
            rewrite /rowL /rowR.
            have Hraw_cast :
                esym (esym HdimZCE_raw, esym HdimZCE_raw).1 =
                HdimZCE_raw by apply: eq_irrelevance.
            rewrite Hraw_cast.
            apply: (can_inj (@mxtens_unindexK _ _)).
            have Hcol_cast :
                esym (esym HdimZCE_col, esym HdimZCE_col).1 =
                HdimZCE_col by apply: eq_irrelevance.
            rewrite Hcol_cast Hcast_ZCE_col_unindex
              Hcast_ZCE_unindex_fw mxtens_indexK.
            rewrite cast_ordK /tenv_indexr !i2nK.
            have Hcast_assoc :
                esym
                  (f_equal (fun T : {set 'I_5} => dim 'H[HL]_T)
                    eqZCE_ZEC) =
                f_equal (fun T : {set 'I_5} => dim 'H[HL]_T)
                  (esym eqZCE_ZEC) by apply: eq_irrelevance.
            rewrite Hcast_assoc !Hn2i_cast_i2n.
            set z0 := n2i (cast_ord (esym HdimZ_prod) zi).
            set e0 := n2i (cast_ord (esym HdimE_prod)
              (mxtens_index (mxtens_index (zpi, ai), bi))).
            set c0 := n2i (cast_ord (esym HdimC_prod) c).
            have [Hleft Hright] := Hidx_ZEC_ZCE_assoc z0 e0 c0.
            rewrite Hleft Hright idxSUl idxSUr //.
            rewrite /z0 /e0 /c0 !n2iK Hcast_ZC_index.
            by rewrite /= cast_ordKV.
          }
          have HcolL : colL = colR.
          {
            rewrite /colL /colR.
            have Hraw_cast :
                esym (esym HdimZCE_raw, esym HdimZCE_raw).2 =
                HdimZCE_raw by apply: eq_irrelevance.
            rewrite Hraw_cast.
            apply: (can_inj (@mxtens_unindexK _ _)).
            have Hcol_cast :
                esym (esym HdimZCE_col, esym HdimZCE_col).2 =
                HdimZCE_col by apply: eq_irrelevance.
            rewrite Hcol_cast Hcast_ZCE_col_unindex
              Hcast_ZCE_unindex_fw mxtens_indexK.
            rewrite cast_ordK /tenv_indexr !i2nK.
            have Hcast_assoc :
                esym
                  (f_equal (fun T : {set 'I_5} => dim 'H[HL]_T)
                    eqZCE_ZEC) =
                f_equal (fun T : {set 'I_5} => dim 'H[HL]_T)
                  (esym eqZCE_ZEC) by apply: eq_irrelevance.
            rewrite Hcast_assoc !Hn2i_cast_i2n.
            set z0 := n2i (cast_ord (esym HdimZ_prod) zj).
            set e0 := n2i (cast_ord (esym HdimE_prod)
              (mxtens_index (mxtens_index (zpj, aj), bj))).
            set c0 := n2i (cast_ord (esym HdimC_prod) c).
            have [Hleft Hright] := Hidx_ZEC_ZCE_assoc z0 e0 c0.
            rewrite Hleft Hright idxSUl idxSUr //.
            rewrite /z0 /e0 /c0 !n2iK Hcast_ZC_index.
            by rewrite /= cast_ordKV.
          }
          rewrite HrowL HcolL /rowR /colR /rhoZCZpAB mxE ?mxtens_indexK /=.
          have Hflat_val :
              forall (z0 zp0 : 'I_nz) (a0 : 'I_na) (b0 : 'I_nb)
                (c0 : 'I_nc),
              (z0 * nz * na * nb * nc + zp0 * na * nb * nc +
               a0 * nb * nc + b0 * nc + c0 =
               (z0 * nz * na * nb + zp0 * na * nb + a0 * nb + b0)
                 %/ (nz * na * nb) * nz * na * nb * nc +
               (((z0 * nz * na * nb + zp0 * na * nb + a0 * nb + b0)
                 %% (nz * na * nb)) %/ nb) %/ na * na * nb * nc +
               (((z0 * nz * na * nb + zp0 * na * nb + a0 * nb + b0)
                 %% (nz * na * nb)) %/ nb) %% na * nb * nc +
               ((z0 * nz * na * nb + zp0 * na * nb + a0 * nb + b0)
                 %% (nz * na * nb)) %% nb * nc + c0)%N.
          {
            move=> z0 zp0 a0 b0 c0.
            have Hnb0 : (0 < nb)%N :=
              leq_ltn_trans (leq0n b0) (ltn_ord b0).
            have Hna0 : (0 < na)%N :=
              leq_ltn_trans (leq0n a0) (ltn_ord a0).
            set env := (zp0 * na * nb + a0 * nb + b0)%N.
            have HenvE : env = ((zp0 * na + a0) * nb + b0)%N.
            {
              by rewrite /env mulnDl.
            }
            have Henv_small : (env < nz * na * nb)%N.
            {
              rewrite HenvE.
              exact: ltn_ord (mxtens_index (mxtens_index (zp0, a0), b0)).
            }
            set N0 := (nz * na * nb)%N.
            have HN0 : (0 < N0)%N by rewrite /N0.
            have Hzfold :
                (z0 * nz * na * nb + zp0 * na * nb + a0 * nb + b0 =
                 z0 * N0 + env)%N.
            {
              by rewrite /N0 /env !mulnA !addnA.
            }
            have Hleft_fold :
                (z0 * nz * na * nb * nc + zp0 * na * nb * nc +
                 a0 * nb * nc + b0 * nc + c0 =
                 z0 * N0 * nc + env * nc + c0)%N.
            {
              by rewrite /N0 /env !mulnDl !mulnA !addnA.
            }
            rewrite Hleft_fold !Hzfold divnMDl // (divn_small Henv_small) addn0.
            rewrite modnMDl (modn_small Henv_small) HenvE.
            rewrite divnMDl // (divn_small (ltn_ord b0)) addn0 modnMDl.
            rewrite divnMDl // (divn_small (ltn_ord a0)) addn0 modnMDl.
            rewrite /N0 !mulnDl !mulnA !addnA.
            by rewrite (modn_small (ltn_ord a0))
              (modn_small (ltn_ord b0)).
          }
          congr (rhoZZ _ _).
          - apply: val_inj=> /=.
            rewrite !mulnDl !mulnA !addnA divnMDl // (divn_small (ltn_ord c)) addn0.
            rewrite modnMDl (modn_small (ltn_ord c)) -[RHS](Hflat_val zi zpi ai bi c).
            have HenvE :
                (zpi * na * nb + ai * nb + bi =
                 (zpi * na + ai) * nb + bi)%N.
            { by rewrite mulnDl. }
            have Hnb0 : (0 < nb)%N :=
              leq_ltn_trans (leq0n bi) (ltn_ord bi).
            have Hna0 : (0 < na)%N :=
              leq_ltn_trans (leq0n ai) (ltn_ord ai).
            rewrite HenvE.
            rewrite divnMDl //.
            rewrite (divn_small (ltn_ord bi)) addn0 modnMDl.
            rewrite divnMDl //.
            rewrite modnMDl (divn_small (ltn_ord ai)) addn0.
            rewrite (modn_small (ltn_ord ai)) (modn_small (ltn_ord bi)).
            by rewrite ?mulnDl ?mulnA ?addnA.
          - apply/val_inj=> /=.
            rewrite !mulnDl !mulnA !addnA divnMDl // (divn_small (ltn_ord c)) addn0.
            rewrite modnMDl (modn_small (ltn_ord c)) -[RHS](Hflat_val zj zpj aj bj c).
            have HenvE :
                (zpj * na * nb + aj * nb + bj =
                 (zpj * na + aj) * nb + bj)%N.
            { by rewrite mulnDl. }
            have Hnb0 : (0 < nb)%N :=
              leq_ltn_trans (leq0n bj) (ltn_ord bj).
            have Hna0 : (0 < na)%N :=
              leq_ltn_trans (leq0n aj) (ltn_ord aj).
            rewrite HenvE.
            rewrite divnMDl //.
            rewrite (divn_small (ltn_ord bj)) addn0 modnMDl.
            rewrite divnMDl //.
            rewrite modnMDl (divn_small (ltn_ord aj)) addn0.
            rewrite (modn_small (ltn_ord aj)) (modn_small (ltn_ord bj)).
            by rewrite ?mulnDl ?mulnA ?addnA.
        }
        by rewrite Hptrace_prod Hptrace_prod_raw -Hptrace_rhoZEC_raw.
      }
      have HrhoZEL_raw : rhoZEL_prod = rhoZE_raw.
      {
        by rewrite HrhoZEL_ptrace_raw Hptrace_rhoZEC_raw.
      }
      have Hraw_rhoZZ : rhoZE_raw = rhoZZpAB.
      {
        have Hcast_zz :
            forall (z : 'I_nz) (zp : 'I_nz)
                   (a : 'I_na) (b : 'I_nb),
            cast_ord (esym Hzz_dim)
              (mxtens_index (z, mxtens_index (mxtens_index (zp, a), b))) =
            mxtens_index (mxtens_index (mxtens_index (z, zp), a), b).
        {
          move=> z zp a b.
          apply/val_inj=> /=.
          by rewrite !mulnDl !mulnA !addnA.
        }
        have Hcast_unindex :
            forall (k : 'I_(nz * (nz * na * nb))),
            let kZE := mxtens_unindex k in
            let kenv := mxtens_unindex kZE.2 in
            let kzpa := mxtens_unindex kenv.1 in
            mxtens_index
              (mxtens_index
                (mxtens_index (kZE.1, kzpa.1), kzpa.2), kenv.2) =
            cast_ord (esym Hzz_dim) k.
        {
          move=> k.
          case Ek: (mxtens_unindex k)=> [zk ek].
          case Eek: (mxtens_unindex ek)=> [zak bk].
          case Ezak: (mxtens_unindex zak)=> [zpk ak].
          rewrite /= -(mxtens_unindexK k) Ek /=.
          rewrite -(mxtens_unindexK ek) Eek /= -(mxtens_unindexK zak) Ezak /=.
          apply/val_inj=> /=.
          have Hnb0 : (0 < nb)%N :=
            leq_ltn_trans (leq0n bk) (ltn_ord bk).
          have Hna0 : (0 < na)%N :=
            leq_ltn_trans (leq0n ak) (ltn_ord ak).
          rewrite [(((zpk * na + ak) * nb + bk) %/ nb)%N]divnMDl //.
          rewrite (divn_small (ltn_ord bk)) addn0.
          rewrite [((zpk * na + ak) %/ na)%N]divnMDl //.
          rewrite (divn_small (ltn_ord ak)) addn0.
          rewrite [(((zpk * na + ak) * nb + bk) %% nb)%N]modnMDl.
          rewrite (modn_small (ltn_ord bk)).
          rewrite [((zpk * na + ak) %% na)%N]modnMDl.
          rewrite (modn_small (ltn_ord ak)).
          by rewrite !mulnDl !mulnA !addnA.
        }
        have Hpacked_val :
            forall (z0 zp0 : 'I_nz) (a0 : 'I_na) (b0 : 'I_nb)
              (cidx : 'I_nc),
            let z0v := nat_of_ord z0 in
            let zp0v := nat_of_ord zp0 in
            let a0v := nat_of_ord a0 in
            let b0v := nat_of_ord b0 in
            let cidxv := nat_of_ord cidx in
            (
            ((((((((z0v * (nz * na * nb) +
                    ((zp0v * na + a0v) * nb + b0v)) %/ (nz * na * nb)) *
                   nc + cidxv) %/ nc * nz +
                  (((z0v * (nz * na * nb) +
                    ((zp0v * na + a0v) * nb + b0v)) %% (nz * na * nb))
                   %/ nb) %/ na) * na +
                 (((z0v * (nz * na * nb) +
                    ((zp0v * na + a0v) * nb + b0v)) %% (nz * na * nb))
                  %/ nb) %% na) * nb +
                ((z0v * (nz * na * nb) +
                  ((zp0v * na + a0v) * nb + b0v)) %% (nz * na * nb))
                %% nb) * nc +
               (((z0v * (nz * na * nb) +
                 ((zp0v * na + a0v) * nb + b0v)) %/ (nz * na * nb)) *
                nc + cidxv) %% nc)) =
              ((((z0v * nz + zp0v) * na + a0v) * nb + b0v) * nc + cidxv))%N.
        {
          move=> z0 zp0 a0 b0 cidx.
          set env := (((zp0 * na + a0) * nb + b0))%N.
          have Henv_small : (env < nz * na * nb)%N.
          {
            rewrite /env.
            exact: ltn_ord (mxtens_index (mxtens_index (zp0, a0), b0)).
          }
          have HN0 : (0 < nz * na * nb)%N :=
            leq_ltn_trans (leq0n env) Henv_small.
          have Hnb0 : (0 < nb)%N :=
            leq_ltn_trans (leq0n b0) (ltn_ord b0).
          have Hna0 : (0 < na)%N :=
            leq_ltn_trans (leq0n a0) (ltn_ord a0).
          have Hnc0 : (0 < nc)%N :=
            leq_ltn_trans (leq0n cidx) (ltn_ord cidx).
          rewrite /= -/env.
          rewrite divnMDl // ?(divn_small Henv_small) ?addn0.
          rewrite modnMDl ?(modn_small Henv_small).
          rewrite divnMDl // ?(divn_small (ltn_ord cidx)) ?addn0.
          rewrite modnMDl ?(modn_small (ltn_ord cidx)).
          rewrite /env.
          rewrite divnMDl //.
          rewrite ?(divn_small (ltn_ord b0)) ?addn0.
          rewrite modnMDl.
          rewrite ?(modn_small (ltn_ord b0)).
          rewrite divnMDl //.
          rewrite ?(divn_small (ltn_ord a0)) ?addn0.
          rewrite modnMDl.
          rewrite ?(modn_small (ltn_ord a0)).
          rewrite -/env (divn_small Henv_small) (modn_small (ltn_ord b0)).
          by rewrite addn0 ?mulnDl ?mulnA ?addnA.
        }
        apply/matrixP=> i j.
        case: (mxtens_indexP i)=> zi ei.
        case: (mxtens_indexP ei)=> zpai bi.
        case: (mxtens_indexP zpai)=> zpi ai.
        case: (mxtens_indexP j)=> zj ej.
        case: (mxtens_indexP ej)=> zpaj bj.
        case: (mxtens_indexP zpaj)=> zpj aj.
        rewrite /rhoZE_raw /rhoZZpAB /rho_ZZpAB /rhoZZ mxE
          /castmx_sq castmxE /=.
        rewrite ptrace2E1 ptrace1E.
        apply: eq_bigr=> c _.
        rewrite /rhoZCZpAB !mxE !mxtens_indexK /=.
        rewrite /rhoZZ /rho_ZZpABC !mxE ?mxtens_indexK /=
          Hcast_zz Hcast_zz.
        apply: eq_bigr=> k _.
        congr (_ * _).
        - congr (((stinespring_U2 N *t 1%:M *t 1%:M *m rhoABC) _ k)).
          apply/val_inj=> /=.
          exact: (Hpacked_val zi zpi ai bi c).
        - congr (((stinespring_U2 N *t 1%:M *t 1%:M)^*t k _)).
          apply/val_inj=> /=.
          exact: (Hpacked_val zj zpj aj bj c).
      }
      by rewrite HrhoZEL_raw Hraw_rhoZZ.
    }
    have Hphi_feasible_eq :
        forall v : R,
        (exists sigma : 'M[C]_(nz * na * nb),
          sigma \is psdmx /\
          ((1%:M : 'M[C]_nz) *t sigma - rhoZZpAB) \is psdmx /\
          v = @complex.Re R (\tr sigma)) <->
        phi_min_feasible [set Elbl] rhoZEL v.
    {
      have eqE_ZE : S_ZE :&: [set Elbl] = [set Elbl].
      {
        apply/setP=> x.
        rewrite /S_ZE !inE.
        by case: (x == Elbl); case: (x == Zlbl).
      }
      have HtargetE_eq_local :
          forall
            (e : (S_ZE :\: [set Elbl]) :|:
                 (S_ZE :&: [set Elbl]) = S_ZE)
            (s0 : 'F[HL]_(S_ZE :&: [set Elbl])),
            castlf (e, e)
              ((\1 : 'F[HL]_(S_ZE :\: [set Elbl])) \O s0) =
            ((\1 : 'F[HL]_[set Zlbl]) \O
              castlf (eqE_ZE, eqE_ZE) s0 : 'F[HL]_S_ZE).
      {
        move=> e s0.
        have eqA : S_ZE :\: [set Elbl] = [set Zlbl].
        {
          rewrite /S_ZE.
          exact: setDU_r.
        }
        have eqU1 :
            (S_ZE :\: [set Elbl]) :|: (S_ZE :&: [set Elbl]) =
            [set Zlbl] :|: (S_ZE :&: [set Elbl]).
        {
          by rewrite eqA.
        }
        have eqU2 : [set Zlbl] :|: (S_ZE :&: [set Elbl]) = S_ZE.
        {
          by rewrite eqE_ZE /S_ZE.
        }
        transitivity
          (castlf (etrans eqU1 eqU2, etrans eqU1 eqU2)
            ((\1 : 'F[HL]_(S_ZE :\: [set Elbl])) \O s0)).
        {
          by rewrite (eq_irrelevance (etrans eqU1 eqU2) e).
        }
        rewrite -(castlf_comp eqU1 eqU1 eqU2 eqU2).
        rewrite (sdotIf_cast_l eqA eqU1) castlf1.
        by rewrite (sdotIf_cast_r eqE_ZE eqU2).
      }
      have eqST_ZE :
          (S_ZE :\: [set Elbl]) :|: (S_ZE :&: [set Elbl]) = S_ZE.
      {
        by rewrite finset.setUC finset.setID.
      }
      have Hdiff_psd_iff :
          forall
            (e : (S_ZE :\: [set Elbl]) :|:
                 (S_ZE :&: [set Elbl]) = S_ZE)
            (sigma0 : 'F[HL]_(S_ZE :&: [set Elbl]))
            (sigma : 'M[C]_(nz * na * nb)),
            castmx (HdimE_prod, HdimE_prod)
              (h2mx (castlf (eqE_ZE, eqE_ZE) sigma0)) = sigma ->
            ((castlf (e, e)
                ((\1 : 'F[HL]_(S_ZE :\: [set Elbl])) \O sigma0)
              - rhoZEL) \is psdlf <->
             ((1%:M : 'M[C]_nz) *t sigma - rhoZZpAB) \is psdmx).
      {
        move=> e sigma0 sigma Hsigma_cast.
        have Htarget_prod :
            castmx (HdimZE_prod, HdimZE_prod)
              (biprod_mx disZE
                (castlf (e, e)
                  ((\1 : 'F[HL]_(S_ZE :\: [set Elbl])) \O sigma0))) =
            (1%:M : 'M[C]_nz) *t sigma.
        {
          rewrite (biprod_lift_mx disZE e eqE_ZE).
          rewrite HdimZE_cast_tensor.
          by rewrite Hsigma_cast.
        }
        have Hdiff_prod :
            castmx (HdimZE_prod, HdimZE_prod)
              (biprod_mx disZE
                (castlf (e, e)
                  ((\1 : 'F[HL]_(S_ZE :\: [set Elbl])) \O sigma0)
                 - rhoZEL)) =
            (1%:M : 'M[C]_nz) *t sigma - rhoZZpAB.
          {
            set aZE :=
              castlf (e, e)
                ((\1 : 'F[HL]_(S_ZE :\: [set Elbl])) \O sigma0).
            have HbiprodB :
                biprod_mx disZE (aZE - rhoZEL) =
                biprod_mx disZE aZE - biprod_mx disZE rhoZEL.
            {
              rewrite /biprod_mx.
              set Q_ZE :=
                castmx _ (@tenv_mxU R _ HL [set Zlbl] [set Elbl]).
              have Hh2B :
                  h2mx (aZE - rhoZEL) = h2mx aZE - h2mx rhoZEL.
              {
                exact: raddfB.
              }
              rewrite Hh2B.
              have HcastB (M0 M1 : 'M[C]_(dim 'H[HL]_S_ZE)) :
                  castmx (tenv_dim disZE, tenv_dim disZE) (M0 - M1) =
                  castmx (tenv_dim disZE, tenv_dim disZE) M0 -
                  castmx (tenv_dim disZE, tenv_dim disZE) M1.
              {
                by case: _ / (tenv_dim disZE); rewrite castmx_id.
              }
              rewrite HcastB.
              by rewrite mulmxBr mulmxBl.
            }
            have HcastZE_B
                (M0 M1 : 'M[C]_(dim 'H[HL]_[set Zlbl] *
                                dim 'H[HL]_[set Elbl])) :
                castmx (HdimZE_prod, HdimZE_prod) (M0 - M1) =
                castmx (HdimZE_prod, HdimZE_prod) M0 -
                castmx (HdimZE_prod, HdimZE_prod) M1.
            {
              exact: raddfB.
            }
            rewrite HbiprodB HcastZE_B /aZE Htarget_prod
              -/rhoZEL_prod HrhoZEL_prod.
            done.
          }
            have Hprod_psd_iff :
                forall (x : 'F[HL]_S_ZE)
                  (xm : 'M[C]_(nz * (nz * na * nb))),
                castmx (HdimZE_prod, HdimZE_prod)
                  (biprod_mx disZE x) = xm ->
                (x \is psdlf <-> xm \is psdmx).
            {
              pose Q_ZE : 'M[C]_(dim 'H[HL]_[set Zlbl] *
                                  dim 'H[HL]_[set Elbl]) :=
                castmx (tenv_dim disZE, erefl _)
                  (@tenv_mxU R _ HL [set Zlbl] [set Elbl]).
              have HQ_ZE_t :
                  Q_ZE^*t =
                  castmx (erefl _, tenv_dim disZE)
                    (@tenv_mxU R _ HL [set Zlbl] [set Elbl])^*t.
              {
                rewrite /Q_ZE.
                exact: (@castmx_mx_mxT _ _ (@adjmx _) _ _ _ _
                  (tenv_dim disZE, erefl _)
                  (@tenv_mxU R _ HL [set Zlbl] [set Elbl])).
              }
              have HQtQ_ZE : Q_ZE^*t *m Q_ZE = 1%:M.
              {
                rewrite /Q_ZE HQ_ZE_t mcextra.castmx_mul.
                have HU :
                    (@tenv_mxU R _ HL [set Zlbl] [set Elbl])^*t *m
                    (@tenv_mxU R _ HL [set Zlbl] [set Elbl]) = 1%:M.
                {
                  have := unitarymxK
                    (@tenv_mxU_adj_unitarymx R _ HL
                      [set Zlbl] [set Elbl] disZE).
                  by rewrite adjmxK.
                }
                rewrite HU.
                by case: _ / (tenv_dim disZE); rewrite castmx_id.
              }
              have HQ_ZE_unit : Q_ZE \is unitarymx by apply/unitarymxPV.
              have HQQt_ZE : Q_ZE *m Q_ZE^*t = 1%:M :=
                unitarymxK HQ_ZE_unit.
              move=> x xm Hxm; split.
              - move=> Px.
                  rewrite -Hxm.
                  apply: castmx_sq_psdmx.
                  rewrite /biprod_mx -/Q_ZE.
                  have Praw :
                      castmx (tenv_dim disZE, tenv_dim disZE)
                        (h2mx x) \is psdmx.
                  {
                    rewrite -/(castmx_sq (tenv_dim disZE) (h2mx x)).
                    apply: castmx_sq_psdmx.
                    by move: Px; rewrite qualifE.
                  }
                  have Ptmp := psdmx_bimap_closed_gen Q_ZE^*t Praw.
                  by move: Ptmp; rewrite adjmxK.
              - move=> Pxm.
                have Pprod_cast :
                    castmx (HdimZE_prod, HdimZE_prod)
                      (biprod_mx disZE x) \is psdmx
                  by rewrite Hxm.
                have Pprod :
                    biprod_mx disZE x \is psdmx.
                {
                  have Pback :=
                    castmx_sq_psdmx (esym HdimZE_prod) Pprod_cast.
                  by move: Pback; rewrite /castmx_sq castmxK.
                }
                have Praw_cast :
                    castmx (tenv_dim disZE, tenv_dim disZE)
                      (h2mx x) \is psdmx.
                {
                    have Pback := psdmx_bimap_closed_gen Q_ZE Pprod.
                  rewrite /biprod_mx -/Q_ZE in Pback.
                  have Hback :
                      Q_ZE *m
                        (Q_ZE^*t *m
                          castmx (tenv_dim disZE, tenv_dim disZE)
                            (h2mx x) *m Q_ZE) *m Q_ZE^*t =
                      castmx (tenv_dim disZE, tenv_dim disZE) (h2mx x).
                  {
                    by rewrite !mulmxA HQQt_ZE mul1mx
                      -!mulmxA HQQt_ZE mulmx1.
                  }
                  by move: Pback; rewrite Hback.
                }
                have Ph2 := castmx_sq_psdmx (esym (tenv_dim disZE)) Praw_cast.
                by move: Ph2; rewrite /castmx_sq castmxK qualifE.
            }
            exact: Hprod_psd_iff Hdiff_prod.
      }
      move=> v; split.
      - move=> [sigma [Psigma [Hdiff Hv]]].
        pose sigmaE : 'F[HL]_[set Elbl] :=
          mx2h (castmx (esym HdimE_prod, esym HdimE_prod) sigma).
        pose sigma0 : 'F[HL]_(S_ZE :&: [set Elbl]) :=
          castlf (esym eqE_ZE, esym eqE_ZE) sigmaE.
        rewrite /phi_min_feasible.
        exists sigma0; split.
        + rewrite /sigma0 castlf_psdlfE /sigmaE qualifE /= mx2hK.
          rewrite -/(castmx_sq (esym HdimE_prod) sigma).
          exact: castmx_sq_psdmx Psigma.
        + split.
          * have Hsigma_cast :
                    castmx (HdimE_prod, HdimE_prod)
                      (h2mx (castlf (eqE_ZE, eqE_ZE) sigma0)) = sigma.
                {
                  by rewrite /sigma0 castlfKV /sigmaE mx2hK castmxKV.
                }
                set ephi := (X in castlf (X, X) _).
                move: (Hdiff_psd_iff ephi sigma0 sigma Hsigma_cast)
                  => [_ Hback].
                exact: (Hback Hdiff).
          * rewrite /sigma0 castlf_trlfE /sigmaE /lftrace /= mx2hK
              mxtrace_castmx_sq.
            exact: Hv.
          - rewrite /phi_min_feasible.
            move=> [sigma0 [Psigma0 [Hdiff Hv]]].
            set ephi := (X in
              (castlf (X, X)
                ((\1 : 'F[HL]_(S_ZE :\: [set Elbl])) \O sigma0)
               - rhoZEL) \is psdlf) in Hdiff.
            pose sigmaE : 'F[HL]_[set Elbl] :=
              castlf (eqE_ZE, eqE_ZE) sigma0.
        pose sigma : 'M[C]_(nz * na * nb) :=
          castmx (HdimE_prod, HdimE_prod) (h2mx sigmaE).
        have Psigma : sigma \is psdmx.
        {
          rewrite /sigma -/(castmx_sq HdimE_prod (h2mx sigmaE)).
          apply: castmx_sq_psdmx.
          have PsigmaE : sigmaE \is psdlf
            by rewrite /sigmaE castlf_psdlfE.
          by move: PsigmaE; rewrite qualifE.
        }
        exists sigma; split; first exact: Psigma.
        split.
        + have Hsigma_cast :
              castmx (HdimE_prod, HdimE_prod)
                (h2mx (castlf (eqE_ZE, eqE_ZE) sigma0)) = sigma.
              {
                by rewrite /sigma /sigmaE.
              }
              move: (Hdiff_psd_iff ephi sigma0 sigma Hsigma_cast)
                => [Hfwd _].
              exact: (Hfwd Hdiff).
        + rewrite /sigma mxtrace_castmx_sq /sigmaE
            -/(\Tr (castlf _ sigma0)) castlf_trlfE.
          exact: Hv.
    }
        rewrite /hmin_mx /hmin /phi_min.
        congr (- log2 _).
        congr inf.
        apply/funext=> v.
        apply/propext.
        exact: Hphi_feasible_eq.
      }
  have Hphi_pos_trace :
      forall (S T : {set 'I_5}) (x : 'F[HL]_S),
      x \is psdlf -> @complex.Re R (\Tr x) <= 1 ->
      0 < @complex.Re R (\Tr x) -> 0 < phi_min T x.
  {
    move=> S T x Px Hx_tr Hx_tr_pos.
    have eqST : (S :\: T) :|: (S :&: T) = S.
      by rewrite finset.setUC finset.setID.
    have disSplit : [disjoint (S :\: T) & (S :&: T)].
    { apply/disjointP=> z; rewrite !inE.
      by case: (z \in T); rewrite ?andbF ?andbT. }
    pose dT : R := (dim 'H[HL]_(S :\: T))%:R.
    have HdT_pos : 0 < dT by rewrite /dT ltr0n dim_proper.
    rewrite /phi_min.
    apply: (@lt_le_trans _ _ ((@complex.Re R (\Tr x)) / dT)).
    - by apply: divr_gt0.
    - apply: lb_le_inf.
      + pose sigma1 : 'F[HL]_(S :&: T) := \1.
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
        have Hx_le1 : x ⊑ (\1 : 'F[HL]_S)
          := denf_le1 (DenLf_Build Hx_den).
        by move: Hx_le1; rewrite lefE.
      + move=> v [sigma [Psigma [Hfeas ->]]].
        have Htr_sigma_real :
            (\Tr sigma : C) = (@complex.Re R (\Tr sigma))%:C
          by rewrite RRe_real // ger0_real // psdlf_trlf.
        have Hx_tr_real : (\Tr x : C) = (@complex.Re R (\Tr x))%:C
          by rewrite RRe_real // ger0_real // psdlf_trlf.
          have Hx_leC :
              \Tr x <= (dim 'H[HL]_(S :\: T))%:R * \Tr sigma.
          { have Hgap_nonneg := psdlf_trlf Hfeas.
            set liftST := (X0 in \Tr (X0 - x)) in Hgap_nonneg.
            have Htr_gap :
                \Tr (liftST - x) = \Tr liftST - \Tr x.
            {
              have HlinTr := @lftrace_is_linear R ('H[HL]_S).
              have Htr := HlinTr (-1 : C) x liftST.
              rewrite !scaleN1r !mulN1r in Htr.
              rewrite [\Tr liftST - \Tr x]addrC -Htr.
              by rewrite [liftST - x]addrC.
            }
            move: Hgap_nonneg.
            rewrite Htr_gap /liftST castlf_trlfE (trlf_lift_I disSplit).
            by rewrite subr_ge0. }
        move: Hx_leC; rewrite Hx_tr_real Htr_sigma_real.
        rewrite /dT -natrC -rmorphM /= lecR => Hx_leR.
        rewrite ler_pdivrMr //.
        by rewrite mulrC.
  }
  have HrhoZL_psd_dual :
      @ptrace_cast3C R _ HL [set Zlbl] [set Clbl] [set Elbl]
        disZE disCE rhoL3 \is psdlf
    by exact: ptrace_cast_gen_psdlf.
  have HrhoZL_tr_eq_dual :
      \Tr (@ptrace_cast3C R _ HL [set Zlbl] [set Clbl] [set Elbl]
        disZE disCE rhoL3) = \Tr rhoL3.
  { rewrite /ptrace_cast3C /ptrace_cast_gen castlf_trlfE.
    have /cptpP [_ /tpmapP Htp] :=
      @ptraceso_qc R _ HL [set Elbl] S_ZCE3.
    exact: Htp. }
  have HrhoZL_tr_le_dual :
      @complex.Re R (\Tr (@ptrace_cast3C R _ HL [set Zlbl] [set Clbl]
        [set Elbl] disZE disCE rhoL3)) <= 1
    by rewrite HrhoZL_tr_eq_dual.
  have HrhoZL_tr_pos_dual :
      0 < @complex.Re R (\Tr (@ptrace_cast3C R _ HL [set Zlbl] [set Clbl]
        [set Elbl] disZE disCE rhoL3))
    by rewrite HrhoZL_tr_eq_dual.
  have HrhoZEL_psd_dual :
      @ptrace_cast3B R _ HL [set Zlbl] [set Clbl] [set Elbl]
        disZC disCE rhoL3 \is psdlf
    by exact: ptrace_cast_gen_psdlf.
  have HrhoZEL_tr_eq_dual :
      \Tr (@ptrace_cast3B R _ HL [set Zlbl] [set Clbl] [set Elbl]
        disZC disCE rhoL3) = \Tr rhoL3.
  { rewrite /ptrace_cast3B /ptrace_cast_gen castlf_trlfE.
    have /cptpP [_ /tpmapP Htp] :=
      @ptraceso_qc R _ HL [set Clbl] S_ZCE3.
    exact: Htp. }
  have HrhoZEL_tr_le_dual :
      @complex.Re R (\Tr (@ptrace_cast3B R _ HL [set Zlbl] [set Clbl]
        [set Elbl] disZC disCE rhoL3)) <= 1
    by rewrite HrhoZEL_tr_eq_dual.
  have HrhoZEL_tr_pos_dual :
      0 < @complex.Re R (\Tr (@ptrace_cast3B R _ HL [set Zlbl] [set Clbl]
        [set Elbl] disZC disCE rhoL3))
    by rewrite HrhoZEL_tr_eq_dual.
  have HrhoZEL_phi_pos_dual :
      0 < phi_min [set Elbl]
        (@ptrace_cast3B R _ HL [set Zlbl] [set Clbl] [set Elbl]
          disZC disCE rhoL3)
    := Hphi_pos_trace _ _ _ HrhoZEL_psd_dual
         HrhoZEL_tr_le_dual HrhoZEL_tr_pos_dual.
  have HrhoZL_hmaxE_fin :
      hmaxE [set Clbl]
        (@ptrace_cast3C R _ HL [set Zlbl] [set Clbl] [set Elbl]
          disZE disCE rhoL3) =
      (hmax [set Clbl]
        (@ptrace_cast3C R _ HL [set Zlbl] [set Clbl] [set Elbl]
          disZE disCE rhoL3))%:E
    := @hmaxE_EFin R _ HL ([set Zlbl] :|: [set Clbl]) [set Clbl]
         (@ptrace_cast3C R _ HL [set Zlbl] [set Clbl] [set Elbl]
           disZE disCE rhoL3)
         HrhoZL_psd_dual HrhoZL_tr_le_dual HrhoZL_tr_pos_dual.
  have HrhoZEL_hminE_fin :
      hminE [set Elbl]
        (@ptrace_cast3B R _ HL [set Zlbl] [set Clbl] [set Elbl]
          disZC disCE rhoL3) =
      (hmin [set Elbl]
        (@ptrace_cast3B R _ HL [set Zlbl] [set Clbl] [set Elbl]
          disZC disCE rhoL3))%:E
    := @hminE_EFin R _ HL ([set Zlbl] :|: [set Elbl]) [set Elbl]
         (@ptrace_cast3B R _ HL [set Zlbl] [set Clbl] [set Elbl]
           disZC disCE rhoL3)
         HrhoZEL_phi_pos_dual.
  have Hdual_real :
      hmax [set Clbl]
        (@ptrace_cast3C R _ HL [set Zlbl] [set Clbl] [set Elbl]
          disZE disCE rhoL3) =
      - hmin [set Elbl]
        (@ptrace_cast3B R _ HL [set Zlbl] [set Clbl] [set Elbl]
          disZC disCE rhoL3).
  { move: Hdual.
    rewrite HrhoZL_hmaxE_fin HrhoZEL_hminE_fin EFinN.
    by case. }
  abstract (rewrite Hmax_local Hmin_local Hdual_real; exact: erefl).
Qed.
(* TeX eqn:mo6/eqn:mo10 with eqn:mo9: W-conjugation and overlap bound. *)
(* path: eur:ucr_pure_zero_mo6 -> eur:ucr_pure_zero -> *)
(*   eur:entropic_uncertainty_relation -> bb84:bb84_secret *)
Lemma ucr_pure_zero_mo6
    (rhoABC : 'M[C]_(na * nb * nc))
    (M : 'I_nx -> 'M[C]_na) (N : 'I_nz -> 'M[C]_na)
    (Hzz_dim : (((nz * nz) * na) * nb = nz * (nz * na * nb))%N) :
  rhoABC \is den1mx -> is_povm_mx M -> is_povm_mx N ->
  overlap_mx M N != 0 ->
  castmx_sq Hzz_dim (rho_ZZpAB N rhoABC) \is den1mx ->
  - log2 (overlap_mx M N) <=
  hmin_mx (rho_XB M rhoABC) +
  - hmin_mx (castmx_sq Hzz_dim (rho_ZZpAB N rhoABC)).
Proof.
  move=> Hden1 HM HN Hoverlap HrhoZZpAB_den1.
  pose rhoX := rho_XB M rhoABC.
  pose rhoZZpAB : 'M[C]_(nz * (nz * na * nb)) :=
    castmx_sq Hzz_dim (rho_ZZpAB N rhoABC).
  pose c0 := overlap_mx M N.
  have Hc0_ge0 : 0 <= c0.
  {
    rewrite /c0 /overlap_mx.
    by apply/bigmax_geP; left.
  }
  have Hc0_pos : 0 < c0.
  {
    rewrite lt_def Hc0_ge0 andbT.
    by rewrite /c0 Hoverlap.
  }
  (* TeX eqn:mo6: apply W := U V^dagger, trace out X' and A, then
     use eqn:mo9 to transport every min-entropy feasible witness. *)
  have Hfeas_transport :
      forall sigmaZpAB : 'M[C]_(nz * na * nb),
      sigmaZpAB \is psdmx ->
      ((1%:M : 'M[C]_nz) *t sigmaZpAB - rhoZZpAB) \is psdmx ->
      (c0%:C *: ((1%:M : 'M[C]_nx) *t ptrace1 sigmaZpAB) - rhoX)
        \is psdmx.
  {
    move=> sigmaZpAB Hsigma_psd Hsigma_feas.
    pose sigmaB : 'M[C]_nb := ptrace1 sigmaZpAB.
    have HsigmaB_psd : sigmaB \is psdmx.
    {
      by rewrite /sigmaB; exact: ptrace1_psd Hsigma_psd.
    }
    pose W0 : 'M[C]_((nx * nx) * na, (nz * nz) * na) :=
      partial_iso_W M N.
    pose W : 'M[C]_(((nx * nx) * na) * nb,
                    ((nz * nz) * na) * nb) :=
      W0 *t (1%:M : 'M[C]_nb).
    have HptraceXA_dim :
        (nb * (nx * nx * na) = nb * nx * (nx * na))%N.
    {
      by rewrite !mulnA.
    }
    pose ptraceXA (rho : 'M[C]_(nx * nx * na * nb)) : 'M[C]_(nx * nb) :=
      let rho1 : 'M[C]_(nb * (nx * nx * na)) := mxswap rho in
      let rho2 : 'M[C]_((nb * nx) * (nx * na)) :=
        castmx_sq HptraceXA_dim rho1 in
      let rho3 : 'M[C]_(nb * nx) := ptrace2 rho2 in
      mxswap rho3.
    pose rhoZZpAB3 : 'M[C]_(nz * nz * na * nb) :=
      castmx_sq (esym Hzz_dim) rhoZZpAB.
    have HptraceXA_le :
        forall A B : 'M[C]_(nx * nx * na * nb),
        A <= B -> ptraceXA A <= ptraceXA B.
    {
      move=> A B.
      rewrite /ptraceXA !le_lownerE -!linearB /=.
      move=> Hdiff.
      apply: mxswap_psdmx.
      apply: ptrace2_psd.
      apply: castmx_sq_psdmx.
      exact: mxswap_psdmx Hdiff.
    }
    have Hbase_le :
        rhoZZpAB3 <=
        castmx_sq (esym Hzz_dim)
          ((1%:M : 'M[C]_nz) *t sigmaZpAB).
    {
      rewrite !le_lownerE /rhoZZpAB3.
      have Hcast_diff :
          castmx_sq (esym Hzz_dim)
            ((1%:M : 'M[C]_nz) *t sigmaZpAB) -
          castmx_sq (esym Hzz_dim) rhoZZpAB =
          castmx_sq (esym Hzz_dim)
            ((1%:M : 'M[C]_nz) *t sigmaZpAB - rhoZZpAB).
      {
        by rewrite /castmx_sq linearB.
      }
      by rewrite Hcast_diff; exact: castmx_sq_psdmx Hsigma_feas.
    }
    have Hconj_le :
        W *m rhoZZpAB3 *m W^*t <=
        W *m castmx_sq (esym Hzz_dim)
          ((1%:M : 'M[C]_nz) *t sigmaZpAB) *m W^*t.
    {
      move: Hbase_le; rewrite !le_lownerE => Hdiff.
      have -> :
          W *m castmx_sq (esym Hzz_dim)
            ((1%:M : 'M[C]_nz) *t sigmaZpAB) *m W^*t -
          W *m rhoZZpAB3 *m W^*t =
          W *m (castmx_sq (esym Hzz_dim)
            ((1%:M : 'M[C]_nz) *t sigmaZpAB) - rhoZZpAB3) *m W^*t.
      {
        by rewrite mulmxBr mulmxBl.
      }
      exact: psdmx_bimap_closed_gen Hdiff.
    }
    (* TeX eqn:mo10: conjugate by W := U V^dagger and trace out X' and A. *)
    have Hmo10 :
        rhoX <= ptraceXA
          (W *m castmx_sq (esym Hzz_dim)
            ((1%:M : 'M[C]_nz) *t sigmaZpAB) *m W^*t).
    {
      have HrhoX_from_W :
          rhoX = ptraceXA (W *m rhoZZpAB3 *m W^*t).
      {
        have HN_iso :
            (stinespring_U2 N)^*t *m stinespring_U2 N = 1%:M.
        {
          have HNpsd : forall z, N z \is psdmx
            by move=> z; exact: is_povm_mx_psd HN.
          exact: stinespring_U2_iso HNpsd (is_povm_mx_sum HN).
        }
        have HrhoZZpAB3_raw :
            rhoZZpAB3 = rho_ZZpAB N rhoABC.
        {
          by rewrite /rhoZZpAB3 /rhoZZpAB /castmx_sq castmxK.
        }
        have Hwv_full :
            (W *t (1%:M : 'M[C]_nc)) *m
              rho_ZZpABC N rhoABC *m
              (W^*t *t (1%:M : 'M[C]_nc)) =
            rho_XXpABC M rhoABC.
        {
          pose UIC : 'M[C]_(((nx * nx) * na) * nb * nc,
                            na * nb * nc) :=
            stinespring_U2 M *t (1%:M : 'M[C]_nb) *t
              (1%:M : 'M[C]_nc).
          pose VIC : 'M[C]_(((nz * nz) * na) * nb * nc,
                            na * nb * nc) :=
            stinespring_U2 N *t (1%:M : 'M[C]_nb) *t
              (1%:M : 'M[C]_nc).
          pose WIC : 'M[C]_(((nx * nx) * na) * nb * nc,
                            ((nz * nz) * na) * nb * nc) :=
            W *t (1%:M : 'M[C]_nc).
          have HWV : WIC *m VIC = UIC.
          {
            rewrite /WIC /W /W0 /partial_iso_W /UIC /VIC.
            by rewrite !mxtens.tensmx_mul !mulmx1 -!mulmxA HN_iso !mulmx1.
          }
          rewrite /rho_ZZpABC /rho_XXpABC -/UIC -/VIC.
          have Hright :
              VIC^*t *m (W^*t *t (1%:M : 'M[C]_nc)) = UIC^*t.
          {
            have HWadj :
                W^*t *t (1%:M : 'M[C]_nc) =
                WIC^*t
              by rewrite /WIC [RHS]adjmx_tens adjmx1.
            by rewrite HWadj -adjmxM HWV.
          }
          transitivity
            ((WIC *m VIC) *m rhoABC *m
              (VIC^*t *m (W^*t *t (1%:M : 'M[C]_nc)))).
          {
            by rewrite /WIC !mulmxA.
          }
          by rewrite HWV Hright.
        }
        have Hwv_trace :
            W *m rhoZZpAB3 *m W^*t =
            ptrace2 (rho_XXpABC M rhoABC).
        {
          have ptrace2_conj_rect :
              forall m m' n (B : 'M[C]_(m, m')) (A : 'M[C]_(m' * n)),
              ptrace2 ((B *t (1%:M : 'M[C]_n)) *m A *m
                (B^*t *t (1%:M : 'M[C]_n))) =
              B *m ptrace2 A *m B^*t.
          {
            move=> m m' n B A.
            have ptrace2E' : forall s t (A0 : 'M[C]_(s * t)) r1 r2,
                (ptrace2 A0) r1 r2 =
                \sum_(k0 : 'I_t) A0 (mxtens_index (r1, k0))
                                       (mxtens_index (r2, k0)).
            {
              move=> s t A0 r1 r2; rewrite ptrace2E1 ptrace1E.
              by apply: eq_bigr => k0 _; rewrite mxE !mxtens_indexK.
            }
            have delta_mid : forall (T : finType) (j : T)
                (K : C) (F : T -> C),
                \sum_i K * ((j == i)%:R : C) * F i = K * F j.
            {
              move=> T j K F.
              rewrite (bigD1 j) //= eqxx mulr1.
              rewrite [X in _ + X]big1 ?addr0 //.
              by move=> i /negPf Hi; rewrite eq_sym Hi mulr0 mul0r.
            }
            have delta_right_scale : forall (T : finType) (j : T)
                (F : T -> C) (K : C),
                \sum_i F i * (K * ((i == j)%:R : C)) = F j * K.
            {
              move=> T j F K.
              rewrite (bigD1 j) //= eqxx mulr1.
              rewrite [X in _ + X]big1 ?addr0 //.
              by move=> i /negPf Hi; rewrite Hi !mulr0.
            }
            apply/matrixP=> i j.
            pose Tsum :=
              \sum_(q : 'I_m') \sum_(p : 'I_m') \sum_(k : 'I_n)
                B i p *
                A (mxtens_index (p, k)) (mxtens_index (q, k)) *
                (B j q)^*.
            have HL :
                ptrace2 ((B *t (1%:M : 'M[C]_n)) *m A *m
                  (B^*t *t (1%:M : 'M[C]_n))) i j = Tsum.
            {
              rewrite /Tsum ptrace2E'.
              transitivity
                (\sum_(k : 'I_n) \sum_(q : 'I_m') \sum_(p : 'I_m')
                  B i p *
                  A (mxtens_index (p, k)) (mxtens_index (q, k)) *
                  (B j q)^*).
              {
                apply: eq_bigr=> k _.
                rewrite mxE.
                rewrite (reindex_mxtens_index (fun r =>
                  ((B *t (1%:M : 'M[C]_n) *m A)
                     (mxtens_index (i, k)) r) *
                  (B^*t *t (1%:M : 'M[C]_n)) r
                    (mxtens_index (j, k)))).
                rewrite pair_bigV /=.
                apply: eq_bigr=> q _.
                transitivity
                  (\sum_(l : 'I_n)
                    (\sum_(p : 'I_m')
                      B i p *
                      A (mxtens_index (p, k)) (mxtens_index (q, l))) *
                    ((B j q)^* * ((l == k)%:R : C))).
                {
                  apply: eq_bigr=> l _.
                  rewrite [X in X * _]mxE.
                  rewrite (reindex_mxtens_index (fun s =>
                    (B *t (1%:M : 'M[C]_n)) (mxtens_index (i, k)) s *
                    A s (mxtens_index (q, l)))).
                  rewrite pair_bigV /=.
                  under eq_bigr=> p _ do
                    under eq_bigr=> l2 _ do
                      rewrite !tensmxE !mxE.
                  under eq_bigr=> p _ do rewrite delta_mid.
                  by rewrite adjmxE tensmxE !mxE.
                }
                rewrite delta_right_scale.
                by rewrite mulr_suml.
              }
              rewrite exchange_big /=.
              apply: eq_bigr=> q _.
              by rewrite exchange_big.
            }
            have HR :
                (B *m ptrace2 A *m B^*t) i j = Tsum.
            {
              rewrite /Tsum mxE.
              under [LHS]eq_bigr=> q _ do rewrite [X in X * _]mxE.
              under [LHS]eq_bigr=> q _ do rewrite mulr_suml.
              under [LHS]eq_bigr=> q _ do
                under eq_bigr=> p _ do rewrite ptrace2E'.
              under [LHS]eq_bigr=> q _ do
                under eq_bigr=> p _ do rewrite mulr_sumr.
              under [LHS]eq_bigr=> q _ do
                under eq_bigr=> p _ do rewrite mulr_suml.
              under [LHS]eq_bigr=> q _ do
                under eq_bigr=> p _ do
                  under eq_bigr=> k _ do rewrite adjmxE.
              under [LHS]eq_bigr=> q _ do
                under eq_bigr=> p _ do
                  under eq_bigr=> k _ do rewrite !mxE.
              by [].
            }
            by rewrite HL HR.
          }
          rewrite HrhoZZpAB3_raw -Hwv_full /rho_ZZpAB.
          by rewrite ptrace2_conj_rect.
        }
        have HrhoXX_marginal :
            ptraceXA (ptrace2 (rho_XXpABC M rhoABC)) = rhoX.
        {
          have HrhoXX_entry :
              forall (xl xr : 'I_nx) (xpl xpr : 'I_nx)
                     (al ar : 'I_na) (bl br : 'I_nb) (cl cr : 'I_nc),
              rho_XXpABC M rhoABC
                (mxtens_index (mxtens_index
                  (mxtens_index (mxtens_index (xl, xpl), al), bl), cl))
                (mxtens_index (mxtens_index
                  (mxtens_index (mxtens_index (xr, xpr), ar), br), cr)) =
              ((xl == xpl)%:R : C) * ((xr == xpr)%:R : C) *
              \sum_(a0 : 'I_na) \sum_(a1 : 'I_na)
                sqrtmx (M xl) al a0 *
                rhoABC (mxtens_index (mxtens_index (a0, bl), cl))
                       (mxtens_index (mxtens_index (a1, br), cr)) *
                (sqrtmx (M xr) ar a1)^*.
          {
            move=> xl xr xpl xpr al ar bl br cl cr.
            pose Ulift : 'M[C]_(((nx * nx) * na) * nb * nc,
                                na * nb * nc) :=
              (stinespring_U2 M *t (1%:M : 'M[C]_nb) *t
                (1%:M : 'M[C]_nc)).
            have HU_entry :
                forall (x0 xp0 : 'I_nx) (a0 a1 : 'I_na)
                       (b0 b1 : 'I_nb) (cc0 cc1 : 'I_nc),
                Ulift
                  (mxtens_index (mxtens_index
                    (mxtens_index (mxtens_index (x0, xp0), a0), b0), cc0))
                  (mxtens_index (mxtens_index (a1, b1), cc1)) =
                ((x0 == xp0)%:R : C) * sqrtmx (M x0) a0 a1 *
                ((b0 == b1)%:R : C) * ((cc0 == cc1)%:R : C).
            {
              move=> x0 xp0 a0 a1 b0 b1 cc0 cc1.
              rewrite /Ulift !tensmxE /stinespring_U2 !mxE
                !mxtens_indexK /=.
              by [].
            }
            have Hraw_expand :
                rho_XXpABC M rhoABC
                  (mxtens_index (mxtens_index
                    (mxtens_index (mxtens_index (xl, xpl), al), bl), cl))
                  (mxtens_index (mxtens_index
                    (mxtens_index (mxtens_index (xr, xpr), ar), br), cr)) =
                \sum_(a1 : 'I_na) \sum_(b1 : 'I_nb) \sum_(c1 : 'I_nc)
                  (\sum_(a0 : 'I_na) \sum_(b0 : 'I_nb) \sum_(cc0 : 'I_nc)
                    (((xl == xpl)%:R : C) * sqrtmx (M xl) al a0 *
                     ((bl == b0)%:R : C) * ((cl == cc0)%:R : C)) *
                    rhoABC (mxtens_index (mxtens_index (a0, b0), cc0))
                           (mxtens_index (mxtens_index (a1, b1), c1))) *
                  ((((xr == xpr)%:R : C) * sqrtmx (M xr) ar a1 *
                    ((br == b1)%:R : C) * ((cr == c1)%:R : C))^*).
            {
              rewrite /rho_XXpABC -/Ulift.
              rewrite mxE !mxtens_index_pairV /=.
              apply: eq_bigr => a1 _.
              apply: eq_bigr => b1 _.
              apply: eq_bigr => c1 _.
              rewrite [X in X * _]mxE !mxtens_index_pairV /=.
              under eq_bigr => a0 _ do
                under eq_bigr => b0 _ do
                  under eq_bigr => cc0 _ do rewrite HU_entry.
              by rewrite mxE_adj HU_entry.
            }
            rewrite Hraw_expand.
            have delta_collapseR : forall (T : finType) (f : T -> C) (j : T),
                \sum_i f i * ((j == i)%:R : C) = f j.
            {
              move=> T f j.
              rewrite (bigD1 j) //= eqxx mulr1.
              rewrite [X in _ + X]big1 ?addr0 //.
              by move=> i /negPf Hi; rewrite eq_sym Hi mulr0.
            }
            have delta_collapse_mid : forall (T : finType) (g h : T -> C)
                (j : T),
                \sum_i g i * ((j == i)%:R : C) * h i = g j * h j.
            {
              move=> T f g j.
              rewrite (bigD1 j) //= eqxx mulr1.
              rewrite [X in _ + X]big1 ?addr0 //.
              by move=> i /negPf Hi; rewrite eq_sym Hi mulr0 mul0r.
            }
            case Hxl: (xl == xpl); last first.
            {
              rewrite /= ?mul0r ?mulr0.
              apply: big1 => a1 _; apply: big1 => b1 _.
              apply: big1 => c1 _.
              rewrite big1 ?mul0r //.
              move=> a0 _; apply: big1 => b0 _; apply: big1 => cc0 _.
              by rewrite /= !mul0r.
            }
            case Hxr: (xr == xpr); last first.
            {
              rewrite /= [X in _ = X * _]mulr0 [RHS]mul0r.
              apply: big1 => a1 _; apply: big1 => b1 _.
              apply: big1 => c1 _.
              by rewrite !mul0r rmorph0 mulr0.
            }
            rewrite /= !mul1r.
            under eq_bigr => a1 _ do
              under eq_bigr => b1 _ do
                under eq_bigr => c1 _ do
                  rewrite !rmorphM /= !conjC_nat.
            under eq_bigr => a1 _ do
              under eq_bigr => b1 _ do
                under eq_bigr => c1 _ do rewrite ?mulrA.
            under eq_bigr => a1 _ do
              under eq_bigr => b1 _ do rewrite delta_collapseR.
            under eq_bigr => a1 _ do rewrite delta_collapseR.
            under eq_bigr => a1 _ do
              under eq_bigr => a0 _ do
                under eq_bigr => b0 _ do
                  under eq_bigr => cc0 _ do rewrite ?mulrA.
            under eq_bigr => a1 _ do
              under eq_bigr => a0 _ do
                under eq_bigr => b0 _ do rewrite delta_collapse_mid.
            under eq_bigr => a1 _ do
              under eq_bigr => a0 _ do rewrite delta_collapse_mid.
            rewrite ?mulr0 ?subr0.
            under eq_bigr => a1 _ do
              under eq_bigr => a0 _ do rewrite ?mul1r ?mulr1.
            under eq_bigr => a1 _ do rewrite mulr1 mulr_suml.
            rewrite exchange_big /=.
            by apply: eq_bigr => a0 _; apply: eq_bigr => a1 _;
              rewrite ?mulrA.
          }
          have ptrace2E' : forall s t (A0 : 'M[C]_(s * t)) r1 r2,
              (ptrace2 A0) r1 r2 =
              \sum_(k0 : 'I_t) A0 (mxtens_index (r1, k0))
                                     (mxtens_index (r2, k0)).
          {
            move=> s t A0 r1 r2; rewrite ptrace2E1 ptrace1E.
            by apply: eq_bigr => k0 _; rewrite mxE !mxtens_indexK.
          }
          have ptraceXAE :
              forall (rho' : 'M[C]_(nx * nx * na * nb))
                (ix0 : 'I_nx) (ib : 'I_nb)
                (jx : 'I_nx) (jb : 'I_nb),
              ptraceXA rho' (mxtens_index (ix0, ib))
                (mxtens_index (jx, jb)) =
              \sum_(x2 : 'I_nx) \sum_(a0 : 'I_na)
                rho'
                  (mxtens_index (mxtens_index (mxtens_index (ix0, x2), a0), ib))
                  (mxtens_index (mxtens_index (mxtens_index (jx, x2), a0), jb)).
          {
            move=> rho' ix0 ib jx jb.
            rewrite /ptraceXA /=.
            rewrite mxE !mxtens_indexK /=.
            rewrite ptrace2E1 ptrace1E mxtens_index_pairV.
            apply: eq_bigr=> x2 _.
            apply: eq_bigr=> a0 _.
            rewrite mxE !mxtens_indexK /= /castmx_sq castmxE /=.
            have Hcast_a4 : forall (bb : 'I_nb)
                (xx1 xx2 : 'I_nx) (aa : 'I_na),
                cast_ord (esym HptraceXA_dim)
                  (mxtens_index (mxtens_index (bb, xx1),
                    mxtens_index (xx2, aa))) =
                mxtens_index (bb, mxtens_index
                  (mxtens_index (xx1, xx2), aa)).
            {
              move=> bb xx1 xx2 aa.
              apply/val_inj=> /=.
              by rewrite !mulnDl !mulnA !addnA.
            }
            by rewrite !Hcast_a4 mxE !mxtens_indexK.
          }
          have Hlhs_entry :
              forall (xl xr : 'I_nx) (bl br : 'I_nb),
              ptraceXA (ptrace2 (rho_XXpABC M rhoABC))
                (mxtens_index (xl, bl)) (mxtens_index (xr, br)) =
              \sum_(x : 'I_nx) \sum_(a : 'I_na) \sum_(c : 'I_nc)
                ((xl == x)%:R : C) * ((xr == x)%:R : C) *
                \sum_(a0 : 'I_na) \sum_(a1 : 'I_na)
                  sqrtmx (M xl) a a0 *
                  rhoABC (mxtens_index (mxtens_index (a0, bl), c))
                         (mxtens_index (mxtens_index (a1, br), c)) *
                  (sqrtmx (M xr) a a1)^*.
          {
            move=> xl xr bl br.
            rewrite ptraceXAE.
            apply: eq_bigr=> x _.
            apply: eq_bigr=> a _.
            rewrite ptrace2E'.
            apply: eq_bigr=> c _.
            by rewrite HrhoXX_entry.
          }
          have HrhoX_entry :
              forall (xl xr : 'I_nx) (bl br : 'I_nb),
              rhoX (mxtens_index (xl, bl)) (mxtens_index (xr, br)) =
              \sum_(x : 'I_nx) \sum_(a : 'I_na) \sum_(c : 'I_nc)
                ((xl == x)%:R : C) * ((xr == x)%:R : C) *
                \sum_(a0 : 'I_na) \sum_(a1 : 'I_na)
                  sqrtmx (M xl) a a0 *
                  rhoABC (mxtens_index (mxtens_index (a0, bl), c))
                         (mxtens_index (mxtens_index (a1, br), c)) *
                  (sqrtmx (M xr) a a1)^*.
          {
            move=> xl xr bl br.
            have Hsandwich_entry : forall x : 'I_nx,
                ptrace1
                  (ptrace2
                    ((sqrtmx (M x) *t (1%:M : 'M[C]_nb) *t
                        (1%:M : 'M[C]_nc)) *m rhoABC *m
                     (sqrtmx (M x) *t (1%:M : 'M[C]_nb) *t
                        (1%:M : 'M[C]_nc)))) bl br =
                \sum_(a : 'I_na) \sum_(c : 'I_nc)
                \sum_(a0 : 'I_na) \sum_(a1 : 'I_na)
                  sqrtmx (M x) a a0 *
                  rhoABC (mxtens_index (mxtens_index (a0, bl), c))
                         (mxtens_index (mxtens_index (a1, br), c)) *
                  (sqrtmx (M x) a a1)^*.
            {
              move=> x.
              pose Kx : 'M[C]_(na * nb * nc) :=
                sqrtmx (M x) *t (1%:M : 'M[C]_nb) *t
                  (1%:M : 'M[C]_nc).
              pose Ulift : 'M[C]_(((nx * nx) * na) * nb * nc,
                                  na * nb * nc) :=
                stinespring_U2 M *t (1%:M : 'M[C]_nb) *t
                  (1%:M : 'M[C]_nc).
              have HKx_herm : Kx^*t = Kx.
              {
                rewrite /Kx !adjmx_tens !adjmx1.
                have HMx : M x \is psdmx by exact: is_povm_mx_psd HM.
                have /hermmxP Hsqrt := sqrtmx_herm (psdmx_herm HMx).
                by rewrite -Hsqrt.
              }
              have HU_block :
                  forall (aa aa' : 'I_na) (bb bb' : 'I_nb)
                         (cc cc' : 'I_nc),
                  Ulift
                    (mxtens_index (mxtens_index
                      (mxtens_index (mxtens_index (x, x), aa), bb), cc))
                    (mxtens_index (mxtens_index (aa', bb'), cc')) =
                  Kx (mxtens_index (mxtens_index (aa, bb), cc))
                     (mxtens_index (mxtens_index (aa', bb'), cc')).
              {
                move=> aa aa' bb bb' cc cc'.
                rewrite /Ulift /Kx !tensmxE /stinespring_U2 !mxE
                  !mxtens_indexK /= eqxx.
                by rewrite mul1r.
              }
              have Hblock_eq :
                  forall (aa aa' : 'I_na) (bb bb' : 'I_nb)
                         (cc cc' : 'I_nc),
                  (Kx *m rhoABC *m Kx)
                    (mxtens_index (mxtens_index (aa, bb), cc))
                    (mxtens_index (mxtens_index (aa', bb'), cc')) =
                  rho_XXpABC M rhoABC
                    (mxtens_index (mxtens_index
                      (mxtens_index (mxtens_index (x, x), aa), bb), cc))
                    (mxtens_index (mxtens_index
                      (mxtens_index (mxtens_index (x, x), aa'), bb'), cc')).
              {
                move=> aa aa' bb bb' cc cc'.
                have HKx_adj_form :
                    Kx *m rhoABC *m Kx =
                    Kx *m rhoABC *m Kx^*t
                  by rewrite HKx_herm.
                rewrite HKx_adj_form /rho_XXpABC -/Ulift.
                rewrite !mxE.
                apply: eq_bigr=> r _.
                case: (mxtens_indexP r)=> abr cr0.
                case: (mxtens_indexP abr)=> ar0 br0.
                rewrite [X in _ = X * _]mxE.
                rewrite [X in X * _ = _]mxE.
                have Hsum :
                    \sum_j
                      Kx (mxtens_index (mxtens_index (aa, bb), cc)) j *
                      rhoABC j (mxtens_index (mxtens_index (ar0, br0), cr0)) =
                    \sum_j
                      Ulift
                        (mxtens_index (mxtens_index
                          (mxtens_index (mxtens_index (x, x), aa), bb), cc))
                        j *
                      rhoABC j (mxtens_index (mxtens_index (ar0, br0), cr0)).
                {
                  apply: eq_bigr=> s _.
                  case: (mxtens_indexP s)=> abs cs0.
                  case: (mxtens_indexP abs)=> as0 bs0.
                  by rewrite HU_block.
                }
                rewrite Hsum.
                rewrite !mxE_adj.
                congr (_ * _).
                by rewrite HU_block.
              }
              rewrite -/Kx.
              rewrite ptrace1E.
              apply: eq_bigr=> a _.
              rewrite ptrace2E'.
              apply: eq_bigr=> c _.
              by rewrite Hblock_eq HrhoXX_entry !eqxx /= !mul1r.
            }
            rewrite /rhoX /rho_XB summxE.
            apply: eq_bigr=> x _.
            rewrite tensmxE !mxE Hsandwich_entry.
            case Hxl: (xl == x); case Hxr: (xr == x); rewrite /=.
            - move/eqP: Hxl=> ->.
              move/eqP: Hxr=> ->.
              rewrite mul1r.
              under [RHS]eq_bigr=> a _ do
                under eq_bigr=> c _ do rewrite !mul1r.
              by [].
            - rewrite mul0r.
              by rewrite big1 // => a _; rewrite big1 // => c _;
                rewrite mulr0 mul0r.
            - rewrite mul0r.
              by rewrite big1 // => a _; rewrite big1 // => c _;
                rewrite ?mul0r ?mulr0.
            - rewrite mul0r.
              by rewrite big1 // => a _; rewrite big1 // => c _;
                rewrite ?mul0r ?mulr0.
          }
          apply/matrix_tenP=> xl bl xr br.
          by rewrite Hlhs_entry HrhoX_entry.
        }
        by rewrite Hwv_trace HrhoXX_marginal.
      }
      rewrite HrhoX_from_W.
      exact: HptraceXA_le Hconj_le.
    }
    (* TeX eqn:mo8/eqn:mo9: expand the W-trace and use
       sqrt(N_z) M_x sqrt(N_z) <= c I_A pointwise. *)
    have Hmo9 :
        ptraceXA
          (W *m castmx_sq (esym Hzz_dim)
            ((1%:M : 'M[C]_nz) *t sigmaZpAB) *m W^*t)
        <= c0%:C *: ((1%:M : 'M[C]_nx) *t sigmaB).
    {
      pose S_xz (ix : 'I_nx) (jz : 'I_nz) : 'M[C]_na :=
        sqrtmx (M ix) *m sqrtmx (N jz).
      have H_SdagS_le : forall (ix : 'I_nx) (jz : 'I_nz),
          (S_xz ix jz)^*t *m S_xz ix jz <=
          c0%:C *: (1%:M : 'M[C]_na).
      {
        move=> ix jz.
        rewrite /S_xz /c0.
        have HsqrtN :
            (sqrtmx (N jz))^*t = sqrtmx (N jz).
        {
          have HNz : N jz \is psdmx by exact: is_povm_mx_psd HN.
          by apply/esym/hermmxP; exact: sqrtmx_herm (psdmx_herm HNz).
        }
        have HsqrtM :
            (sqrtmx (M ix))^*t *m sqrtmx (M ix) = M ix.
        {
          have HMx : M ix \is psdmx by exact: is_povm_mx_psd HM.
          have HsqrtM_adj :
              (sqrtmx (M ix))^*t = sqrtmx (M ix).
          {
            by apply/esym/hermmxP; exact: sqrtmx_herm (psdmx_herm HMx).
          }
          by rewrite HsqrtM_adj sqrtmxK.
        }
        have Hprod :
            (sqrtmx (M ix) *m sqrtmx (N jz))^*t *m
              (sqrtmx (M ix) *m sqrtmx (N jz)) =
            sqrtmx (N jz) *m M ix *m sqrtmx (N jz).
        {
          set SM := sqrtmx (M ix).
          set SN := sqrtmx (N jz).
          have HSN : SN^*t = SN by rewrite /SN.
          have HSM : SM^*t *m SM = M ix by rewrite /SM.
          rewrite -/SM -/SN adjmxM HSN -mulmxA.
          rewrite [SM^*t *m (SM *m SN)]mulmxA HSM.
          by rewrite mulmxA.
        }
        rewrite Hprod.
        exact: sqrtmx_prod_overlap_bound ix jz HM HN.
      }
      (* TeX eqn:mo8: expand W(I_Z ⊗ sigma)W† after tracing out X'A. *)
      have Hmo8_expand :
          ptraceXA
            (W *m castmx_sq (esym Hzz_dim)
              ((1%:M : 'M[C]_nz) *t sigmaZpAB) *m W^*t) <=
          c0%:C *: ((1%:M : 'M[C]_nx) *t sigmaB).
      {
        pose sigma_cast : 'M[C]_(nz * (na * nb)) :=
          castmx_sq (esym (mulnA nz na nb)) sigmaZpAB.
        pose sigma_block (jz : 'I_nz) : 'M[C]_(na * nb) :=
          \matrix_(i, j)
            sigma_cast (mxtens_index (jz, i)) (mxtens_index (jz, j)).
        have Hsigma_cast_psd : sigma_cast \is psdmx.
        {
          by rewrite /sigma_cast; exact: castmx_sq_psdmx Hsigma_psd.
        }
        have Hsigma_block_psd : forall jz, sigma_block jz \is psdmx.
        {
          move=> jz.
          pose Pj : 'M[C]_(na * nb, nz * (na * nb)) :=
            \matrix_(i, r)
              if r == mxtens_index (jz, i) then 1 else 0.
          suff -> : sigma_block jz = Pj *m sigma_cast *m Pj^*t.
          {
            exact: psdmx_bimap_closed_gen Hsigma_cast_psd.
          }
          have Pj_entry : forall a b,
              Pj a b =
              (if b == mxtens_index (jz, a) then 1 else 0 : C).
          {
            by move=> a b; rewrite /Pj mxE.
          }
          have adjPj_entry : forall a b,
              (Pj^*t) a b =
              (if a == mxtens_index (jz, b) then 1 else 0 : C).
          {
            move=> a b.
            by rewrite !mxE; case: eqP => _; rewrite ?conjC1 ?conjC0.
          }
          apply/matrixP=> i j.
          rewrite /sigma_block mxE mxE.
          rewrite (bigD1 (mxtens_index (jz, j))) //= big1.
          2: by move=> k Hk; rewrite adjPj_entry (negPf Hk) mulr0.
          rewrite addr0 adjPj_entry eqxx mulr1 mxE.
          rewrite (bigD1 (mxtens_index (jz, i))) //= big1.
          2: by move=> r Hr; rewrite Pj_entry (negPf Hr) mul0r.
          by rewrite Pj_entry eqxx mul1r addr0.
        }
        have Hblock_expand :
            ptraceXA
              (W *m castmx_sq (esym Hzz_dim)
                ((1%:M : 'M[C]_nz) *t sigmaZpAB) *m W^*t) =
            \sum_(ix : 'I_nx) \sum_(jz : 'I_nz)
              (delta_mx ix ix : 'M[C]_nx) *t
              ptrace1
                ((S_xz ix jz *t (1%:M : 'M[C]_nb)) *m
                  sigma_block jz *m
                     ((S_xz ix jz)^*t *t (1%:M : 'M[C]_nb))).
            {
          have Hsqrt_herm_N : forall jz0 : 'I_nz,
              (sqrtmx (N jz0))^*t = sqrtmx (N jz0).
          {
            move=> jz0.
            have HNz : N jz0 \is psdmx by exact: is_povm_mx_psd HN.
            by apply/esym/hermmxP; exact: sqrtmx_herm (psdmx_herm HNz).
          }
          have Hstinespring_mul_entry :
              forall (ix0 x2 : 'I_nx) (jz0 z2 : 'I_nz)
                (a1 a2 : 'I_na),
              (stinespring_U2 M *m (stinespring_U2 N)^*t)
                (mxtens_index (mxtens_index (ix0, x2), a1))
                (mxtens_index (mxtens_index (jz0, z2), a2)) =
              (ix0 == x2)%:R * (jz0 == z2)%:R *
              (sqrtmx (M ix0) *m (sqrtmx (N jz0))^*t) a1 a2.
          {
            move=> ix0 x2 jz0 z2 a1 a2.
            rewrite mxE.
            have HU : forall p q k (a : 'I_na),
                stinespring_U2 M
                  (mxtens_index (mxtens_index (p, q), k)) a =
                (if p == q then sqrtmx (M p) k a else 0).
            {
              move=> p q k a.
              rewrite /stinespring_U2 mxE !mxtens_indexK.
              cbv iota zeta beta.
              by case: (p == q); rewrite ?mul1r ?mul0r.
            }
            have HV : forall a p q k,
                ((stinespring_U2 N)^*t) a
                  (mxtens_index (mxtens_index (p, q), k)) =
                (if p == q then sqrtmx (N p) k a else 0)^*.
            {
              move=> a p q k.
              rewrite !mxE /stinespring_U2 !mxtens_indexK /=.
              case Hpq: (p == q).
              - rewrite /= mul1r.
                by rewrite mxE.
              - by rewrite /= mul0r conjC0 ?oppr0.
            }
            case Hx: (ix0 == x2); case Hz: (jz0 == z2);
              rewrite /nat_of_bool /= ?mulr0 ?mul0r ?mulr1 ?mul1r.
            - rewrite mxE.
              apply: eq_bigr=> a _.
              by rewrite HU HV Hx Hz adjmxE !mxE.
            - apply: big1=> a _.
              by rewrite HU HV Hx Hz conjC0 mulr0.
            - apply: big1=> a _.
              by rewrite HU HV Hx Hz mul0r.
            - apply: big1=> a _.
              by rewrite HU HV Hx Hz mul0r.
          }
          have ptraceXAE :
              forall (rho' : 'M[C]_(nx * nx * na * nb))
                (ix0 : 'I_nx) (ib : 'I_nb)
                (jx : 'I_nx) (jb : 'I_nb),
              ptraceXA rho' (mxtens_index (ix0, ib))
                (mxtens_index (jx, jb)) =
              \sum_(x2 : 'I_nx) \sum_(a0 : 'I_na)
                rho'
                  (mxtens_index (mxtens_index (mxtens_index (ix0, x2), a0), ib))
                  (mxtens_index (mxtens_index (mxtens_index (jx, x2), a0), jb)).
          {
            move=> rho' ix0 ib jx jb.
            rewrite /ptraceXA /=.
            rewrite mxE !mxtens_indexK /=.
            rewrite ptrace2E1 ptrace1E mxtens_index_pairV.
            apply: eq_bigr=> x2 _.
            apply: eq_bigr=> a0 _.
            rewrite mxE !mxtens_indexK /= /castmx_sq castmxE /=.
            have Hcast_a4 : forall (bb : 'I_nb)
                (xx1 xx2 : 'I_nx) (aa : 'I_na),
                cast_ord (esym HptraceXA_dim)
                  (mxtens_index (mxtens_index (bb, xx1),
                    mxtens_index (xx2, aa))) =
                mxtens_index (bb, mxtens_index
                  (mxtens_index (xx1, xx2), aa)).
            {
              move=> bb xx1 xx2 aa.
              apply/val_inj=> /=.
              by rewrite !mulnDl !mulnA !addnA.
            }
            by rewrite !Hcast_a4 mxE !mxtens_indexK.
          }
          have WE : forall (ix0 x2' : 'I_nx) (a0 : 'I_na) (bv : 'I_nb)
                     (jz0 z2 : 'I_nz) (c1 : 'I_na) (dv : 'I_nb),
              W (mxtens_index (mxtens_index (mxtens_index (ix0, x2'), a0), bv))
                (mxtens_index (mxtens_index (mxtens_index (jz0, z2), c1), dv)) =
              (ix0 == x2')%:R * (jz0 == z2)%:R *
              S_xz ix0 jz0 a0 c1 * (bv == dv)%:R.
          {
            move=> ix0 x2' a0 bv jz0 z2 c1 dv.
            rewrite /W /W0 /partial_iso_W tensmxE.
            rewrite Hstinespring_mul_entry Hsqrt_herm_N.
            rewrite /S_xz.
            by rewrite [1%:M bv dv]mxE.
          }
          have ME : forall (j1 j2 : 'I_nz) (c1 : 'I_na) (d1 : 'I_nb)
                     (k1 k2 : 'I_nz) (c2 : 'I_na) (d2 : 'I_nb),
              (castmx_sq (esym Hzz_dim)
                ((1%:M : 'M[C]_nz) *t sigmaZpAB))
                (mxtens_index (mxtens_index (mxtens_index (j1, j2), c1), d1))
                (mxtens_index (mxtens_index (mxtens_index (k1, k2), c2), d2)) =
              (j1 == k1)%:R *
              sigmaZpAB (mxtens_index (mxtens_index (j2, c1), d1))
                        (mxtens_index (mxtens_index (k2, c2), d2)).
          {
            move=> j1 j2 c1 d1 k1 k2 c2 d2.
            have Hcast_z : forall (jj1 jj2 : 'I_nz)
                (cc : 'I_na) (dd : 'I_nb),
                cast_ord Hzz_dim
                  (mxtens_index
                    (mxtens_index (mxtens_index (jj1, jj2), cc), dd)) =
                mxtens_index (jj1, mxtens_index
                  (mxtens_index (jj2, cc), dd)).
            {
              move=> jj1 jj2 cc dd.
              apply/val_inj=> /=.
              by rewrite !mulnDl !mulnA !addnA.
            }
            rewrite /castmx_sq castmxE /=.
            rewrite (eq_irrelevance (esym (esym Hzz_dim)) Hzz_dim).
            by rewrite !Hcast_z tensmxE !mxE.
          }
          have sigma_blockE : forall (jz0 : 'I_nz)
                (c1 : 'I_na) (d1 : 'I_nb)
                (c2 : 'I_na) (d2 : 'I_nb),
              sigma_block jz0 (mxtens_index (c1, d1))
                (mxtens_index (c2, d2)) =
              sigmaZpAB (mxtens_index (mxtens_index (jz0, c1), d1))
                        (mxtens_index (mxtens_index (jz0, c2), d2)).
          {
            move=> jz0 c1 d1 c2 d2.
            rewrite /sigma_block /sigma_cast mxE /castmx_sq castmxE /=.
            have Hcast_assoc' : forall (z : 'I_nz) (a : 'I_na) (b : 'I_nb),
                cast_ord (esym (esym (mulnA nz na nb)))
                  (mxtens_index (z, mxtens_index (a, b))) =
                mxtens_index (mxtens_index (z, a), b).
            {
              move=> z a b.
              apply/val_inj=> /=.
              by rewrite mulnDl mulnA addnA.
            }
            by rewrite !Hcast_assoc'.
          }
          have adjmxE' : forall m n (A : 'M[C]_(m, n))
              (i : 'I_n) (j : 'I_m),
              A^*t i j = conjc (A j i).
          {
            move=> m n A i j.
            by rewrite !mxE.
          }
          have product_entry : forall (ix1 ix2 x2' : 'I_nx)
              (a0' : 'I_na) (bl br : 'I_nb),
              (W *m castmx_sq (esym Hzz_dim)
                  ((1%:M : 'M[C]_nz) *t sigmaZpAB) *m W^*t)
                (mxtens_index (mxtens_index (mxtens_index (ix1, x2'), a0'), bl))
                (mxtens_index (mxtens_index (mxtens_index (ix2, x2'), a0'), br))
              =
              (ix1 == x2')%:R * (ix2 == x2')%:R *
              \sum_(jz : 'I_nz) \sum_(aa0 : 'I_na) \sum_(c1 : 'I_na)
                S_xz ix1 jz a0' aa0 *
                sigmaZpAB (mxtens_index (mxtens_index (jz, aa0), bl))
                          (mxtens_index (mxtens_index (jz, c1), br)) *
                conjc (S_xz ix2 jz a0' c1).
          {
            move=> ix1 ix2 x2' a0' bl br.
            have delta_collapseRR' : forall (T : finType)
                (f : T -> C) (j : T),
                \sum_i f i * ((j == i)%:R : C) = f j.
            {
              move=> T f j.
              under eq_bigr do rewrite eq_sym mulrC.
              rewrite (bigD1 j) //= eqxx mul1r.
              rewrite [X in _ + X]big1 ?addr0 //.
              by move=> k /negPf Hk; rewrite Hk mul0r.
            }
            have sum_delta_mid : forall (T : finType)
                (g h : T -> C) (j : T),
                \sum_i g i * ((j == i)%:R : C) * h i = g j * h j.
            {
              move=> T g h j.
              under eq_bigr => i _ do rewrite -mulrA mulrCA.
              rewrite (bigD1 j) //= eqxx mul1r.
              rewrite [X in _ + X]big1 ?addr0 //.
              by move=> k /negPf Hk; rewrite eq_sym Hk mul0r.
            }
            transitivity (
              \sum_(kz1 : 'I_nz) \sum_(kz2 : 'I_nz)
              \sum_(c2 : 'I_na) \sum_(d2 : 'I_nb)
              \sum_(jz1 : 'I_nz) \sum_(jz2 : 'I_nz)
              \sum_(aa0 : 'I_na) \sum_(d0 : 'I_nb)
                W (mxtens_index
                    (mxtens_index (mxtens_index (ix1, x2'), a0'), bl))
                  (mxtens_index
                    (mxtens_index (mxtens_index (jz1, jz2), aa0), d0)) *
                (castmx_sq (esym Hzz_dim)
                  ((1%:M : 'M[C]_nz) *t sigmaZpAB))
                  (mxtens_index
                    (mxtens_index (mxtens_index (jz1, jz2), aa0), d0))
                  (mxtens_index
                    (mxtens_index (mxtens_index (kz1, kz2), c2), d2)) *
                W^*t
                  (mxtens_index
                    (mxtens_index (mxtens_index (kz1, kz2), c2), d2))
                  (mxtens_index
                    (mxtens_index (mxtens_index (ix2, x2'), a0'), br))
            ).
            {
              rewrite mxE !mxtens_index_pairV.
              apply: eq_bigr=> kz1 _.
              apply: eq_bigr=> kz2 _.
              apply: eq_bigr=> c2 _.
              apply: eq_bigr=> d2 _.
              set M0 := castmx_sq _ _.
              rewrite [X in X * _]mxE !mxtens_index_pairV.
              rewrite mulr_suml.
              apply: eq_bigr=> jz1 _.
              rewrite mulr_suml.
              apply: eq_bigr=> jz2 _.
              rewrite mulr_suml.
              apply: eq_bigr=> aa0 _.
              rewrite mulr_suml.
              by apply: eq_bigr=> d0 _.
            }
            under eq_bigr => jz1 _ do under eq_bigr => jz2 _ do
              under eq_bigr => aa0 _ do under eq_bigr => d0 _ do
                under eq_bigr => kz1 _ do under eq_bigr => kz2 _ do
                  under eq_bigr => c2 _ do under eq_bigr => d2 _ do
                    rewrite WE ME adjmxE' WE !rmorphM ?conjC_nat.
            under eq_bigr => jz1 _ do under eq_bigr => jz2 _ do
              under eq_bigr => aa0 _ do under eq_bigr => d0 _ do
                under eq_bigr => kz1 _ do under eq_bigr => kz2 _ do
                  under eq_bigr => c2 _ do under eq_bigr => d2 _ do
                    rewrite !mulrA.
            case: (ix1 == x2') /eqP => [-> | /eqP Hneq1];
              rewrite /nat_of_bool /= ?mul0r ?mul1r.
            2: by do 8![apply: big1=> ? _]; rewrite !mul0r.
            case: (ix2 == x2') /eqP => [-> | /eqP Hneq2];
              rewrite /nat_of_bool /= ?mul0r ?mul1r.
            2: {
              rewrite big1 // => i _.
              do 7![apply: big1=> ? _].
              by simpc; rewrite ?mulr0 ?mul0r.
            }
            under eq_bigr => jz1 _ do under eq_bigr => jz2 _ do
              under eq_bigr => aa0 _ do under eq_bigr => d0 _ do
                under eq_bigr => kz1 _ do under eq_bigr => kz2 _ do
                  under eq_bigr => c2 _ do (
                    rewrite (bigD1 bl) //= big1 ?addr0;
                      [|move=> d2 /negPf Hd2;
                        rewrite /= (eq_sym bl d2) Hd2 /=
                          !mulr0 !mul0r //];
                    rewrite eqxx mul1r mulr1
                  ).
            apply: eq_bigr=> jz _.
            rewrite (bigD1 jz) //= [X in _ + X]big1 ?addr0.
            2: {
              move=> dummy /negPf Hneq.
              rewrite (eq_sym jz dummy) Hneq /=.
              by do 5![apply: big1=> ? _]; simpc; rewrite ?mulr0 ?mul0r.
            }
            rewrite eqxx.
            under eq_bigr => aa0 _ do (
              rewrite (bigD1 br) //= [X in _ + X]big1 ?addr0;
                [|move=> d0 /negPf Hneq;
                  rewrite /= (eq_sym br d0) Hneq /=;
                  do 3![apply: big1=> ? _]; simpc;
                  rewrite ?mulr0 ?mul0r //];
              rewrite (bigD1 jz) //= [X in _ + X]big1 ?addr0;
                [|move=> kz1 /negPf Hneq;
                  rewrite /= Hneq /=;
                  do 2![apply: big1=> ? _]; rewrite ?mulr0 ?mul0r //];
              rewrite (bigD1 jz) //= [X in _ + X]big1 ?addr0;
                [|move=> kz2 /negPf Hneq;
                  rewrite /= (eq_sym jz kz2) Hneq /=;
                  apply: big1=> ? _; rewrite ?mulr0 ?mul0r //]
            ).
            rewrite !eqxx.
            rewrite exchange_big /=.
            apply: eq_bigr=> c1 _.
            apply: eq_bigr=> aa0 _.
            by simpc; rewrite ?mul1r ?mulr1.
          }
          have sandwich_entry : forall (ix0 : 'I_nx) (jz0 : 'I_nz)
              (a0' : 'I_na) (bl br : 'I_nb),
              ((S_xz ix0 jz0 *t (1%:M : 'M[C]_nb)) *m
                sigma_block jz0 *m
               ((S_xz ix0 jz0)^*t *t (1%:M : 'M[C]_nb)))
                (mxtens_index (a0', bl)) (mxtens_index (a0', br)) =
              \sum_(aa0 : 'I_na) \sum_(c1 : 'I_na)
                S_xz ix0 jz0 a0' aa0 *
                sigmaZpAB (mxtens_index (mxtens_index (jz0, aa0), bl))
                          (mxtens_index (mxtens_index (jz0, c1), br)) *
                conjc (S_xz ix0 jz0 a0' c1).
          {
            move=> ix0 jz0 a0' bl br.
            have delta_collapseR : forall (T : finType)
                (f : T -> C) (j : T),
                \sum_i ((j == i)%:R : C) * f i = f j.
            {
              move=> T f j.
              under eq_bigr do rewrite eq_sym.
              rewrite (bigD1 j) //= eqxx mul1r.
              rewrite [X in _ + X]big1 ?addr0 //.
              by move=> k /negPf Hk; rewrite Hk mul0r.
            }
            have delta_collapseRR' : forall (T : finType)
                (f : T -> C) (j : T),
                \sum_i f i * ((i == j)%:R : C) = f j.
            {
              move=> T f j.
              rewrite (bigD1 j) //= eqxx mulr1.
              rewrite [X in _ + X]big1 ?addr0 //.
              by move=> k /negPf Hk; rewrite Hk mulr0.
            }
            have eq1M : forall (n : nat) (i j : 'I_n),
                (1%:M : 'M[C]_n) i j = (i == j)%:R.
            {
              move=> n i j.
              by rewrite mxE.
            }
            rewrite mxE mxtens_index_pairV.
            under eq_bigr => c1 _ do under eq_bigr => d1 _ do
              rewrite tensmxE adjmxE' eq1M mulrA.
            under eq_bigr => c1 _ do rewrite delta_collapseRR' /=.
            under eq_bigr => c1 _ do
              rewrite [X in X * _]mxE [X in X * _]mxtens_index_pairV
                mulr_suml.
            under eq_bigr => c1 _ do under eq_bigr => aa0 _ do
              rewrite mulr_suml.
            under eq_bigr => c1 _ do under eq_bigr => aa0 _ do
              under eq_bigr => d0 _ do
                rewrite [X in X * _ * _]tensmxE sigma_blockE eq1M.
            under eq_bigr => c1 _ do under eq_bigr => aa0 _ do
              under eq_bigr => d0 _ do
                rewrite [X in X * _ * _]mulrC -!mulrA.
            under eq_bigr => c1 _ do under eq_bigr => aa0 _ do
              rewrite delta_collapseR /=.
            under eq_bigr => c1 _ do under eq_bigr => aa0 _ do
              rewrite mulrA.
                by rewrite exchange_big.
              }
          have delta_collapseR_outer : forall (T : finType)
              (f : T -> C) (j : T),
              \sum_i ((j == i)%:R : C) * f i = f j.
          {
            move=> T f j.
            rewrite (bigD1 j) //= eqxx mul1r.
            rewrite [X in _ + X]big1 ?addr0 //.
            by move=> k /negPf Hk; rewrite eq_sym Hk mul0r.
          }
          apply/matrix_tenP=> ix_L b_L ix_R b_R.
          rewrite ptraceXAE.
          under eq_bigr => x2 _ do
            under eq_bigr => a0' _ do rewrite product_entry.
          under eq_bigr => x2 _ do rewrite -mulr_sumr.
          under eq_bigr => x2 _ do rewrite -mulrA.
          rewrite delta_collapseR_outer.
          rewrite [RHS]summxE.
          under [RHS]eq_bigr => ix0 _ do rewrite summxE.
          under [RHS]eq_bigr => ix0 _ do
            under eq_bigr => jz0 _ do rewrite tensmxE !mxE ptrace1E.
          under [RHS]eq_bigr => ix0 _ do
            under eq_bigr => jz0 _ do
              under eq_bigr => a0' _ do rewrite sandwich_entry.
          case Hxlr: (ix_R == ix_L).
          - move/eqP: Hxlr=> ->.
            rewrite (bigD1 ix_L) //= !eqxx /= mul1r.
            rewrite [X in _ + X]big1 ?addr0.
            2: {
              move=> ix0 /negPf Hix0.
              rewrite eq_sym Hix0 /=.
              by rewrite big1 // => jz0 _; rewrite mul0r.
            }
            rewrite [LHS]exchange_big.
            apply: eq_bigr=> jz _.
            rewrite mul1r.
            apply: eq_bigr=> a0' _.
            by [].
          - rewrite mul0r.
            rewrite big1 // => ix0 _.
            case Hli: (ix_L == ix0); last by rewrite /= big1 // => jz0 _; rewrite mul0r.
            move/eqP: Hli=> <-.
            by rewrite Hxlr /= big1 // => jz0 _; rewrite mul0r.
            }
        have HtensmxZl_local :
            forall m n (k : C) (A : 'M[C]_m) (B : 'M[C]_n),
            (k *: A) *t B = k *: (A *t B).
        {
          move=> m n k A B.
          by rewrite -[k *: A]addr0 (linear_tensmxr B) linear0l addr0.
        }
        have Hptrace1_form_le :
            forall (S : 'M[C]_na) (rho : 'M[C]_(na * nb)) (cc : R),
            rho \is psdmx ->
            0 <= cc ->
            S^*t *m S <= cc%:C *: (1%:M : 'M[C]_na) ->
            ptrace1
              ((S *t (1%:M : 'M[C]_nb)) *m rho *m
               (S^*t *t (1%:M : 'M[C]_nb))) <=
            cc%:C *: ptrace1 rho.
        {
          move=> S rho cc Hrho Hcc Hle.
          have Hkey : forall X : 'M[C]_nb, X \is psdmx ->
              \tr (S^*t *m S *t X *m rho) <=
              \tr (cc%:C *: 1%:M *t X *m rho).
          {
            move=> X HX.
            suff : S^*t *m S *t X <= cc%:C *: 1%:M *t X.
            {
              by move/le_lownerE_psdtr => /(_ rho Hrho).
            }
            rewrite le_lownerE.
            have -> :
                cc%:C *: 1%:M *t X - S^*t *m S *t X =
                (cc%:C *: 1%:M - S^*t *m S) *t X.
            {
              by apply/matrixP=> i j; rewrite !mxE mulrBl.
            }
            apply: psdmx_tens; last exact: HX.
            by move: Hle; rewrite le_lownerE.
          }
          apply/le_lownerE_psdtr => X HX.
          rewrite -ptrace1_mulmxI -tr_ptrace1.
          rewrite -scalemxAl linearZ /=.
          rewrite -ptrace1_mulmxI -tr_ptrace1.
          have -> :
              \tr (S *t 1%:M *m rho *m
                (S^*t *t 1%:M) *m (1%:M *t X)) =
              \tr (S^*t *m S *t X *m rho).
          {
            rewrite mxtrace_mulC !mulmxA tensmx_mul mul1mx mulmx1.
            by rewrite [LHS]mxtrace_mulC mulmxA tensmx_mul mul1mx.
          }
          have -> :
              cc%:C * \tr (rho *m (1%:M *t X)) =
              \tr (cc%:C *: 1%:M *t X *m rho).
          {
            by rewrite mxtrace_mulC HtensmxZl_local -scalemxAl linearZ.
          }
          exact: Hkey X HX.
        }
        have Hptrace_block_le : forall (ix : 'I_nx) (jz : 'I_nz),
            ptrace1
              ((S_xz ix jz *t (1%:M : 'M[C]_nb)) *m
                sigma_block jz *m
               ((S_xz ix jz)^*t *t (1%:M : 'M[C]_nb)))
            <= c0%:C *: ptrace1 (sigma_block jz).
        {
          move=> ix jz.
          exact: Hptrace1_form_le (Hsigma_block_psd jz) Hc0_ge0
            (H_SdagS_le ix jz).
        }
        rewrite Hblock_expand.
        have Htens_psdmx_le_l :
            forall m n (P : 'M[C]_m) (A B : 'M[C]_n),
            P \is psdmx -> A <= B -> P *t A <= P *t B.
        {
          move=> m n P A B HP.
          rewrite !le_lownerE -bregvBr.
          exact: psdmx_tens HP.
        }
        have Hsum_bound :
            \sum_(ix : 'I_nx) \sum_(jz : 'I_nz)
              (delta_mx ix ix : 'M[C]_nx) *t
              ptrace1
                ((S_xz ix jz *t (1%:M : 'M[C]_nb)) *m
                  sigma_block jz *m
                 ((S_xz ix jz)^*t *t (1%:M : 'M[C]_nb)))
            <=
            \sum_(ix : 'I_nx) \sum_(jz : 'I_nz)
              (delta_mx ix ix : 'M[C]_nx) *t
              (c0%:C *: ptrace1 (sigma_block jz)).
        {
          rewrite le_lownerE -sumrB.
          apply: psdmx_sum=> ix _.
          rewrite -sumrB.
            apply: psdmx_sum=> jz _.
            rewrite -le_lownerE.
            rewrite !le_lownerE -bregvBr.
            apply: psdmx_tens.
            - exact: delta_mx_ii_psdmx.
            - by move: (Hptrace_block_le ix jz); rewrite le_lownerE.
        }
        have Hptrace1_block_sum :
            ptrace1 sigmaZpAB =
            \sum_(jz : 'I_nz) ptrace1 (sigma_block jz).
        {
          have Hcast_assoc :
              forall (z : 'I_nz) (a : 'I_na) (b : 'I_nb),
              cast_ord (mulnA nz na nb)
                (mxtens_index (z, mxtens_index (a, b))) =
              mxtens_index (mxtens_index (z, a), b).
          {
            move=> z a b.
            apply/val_inj=> /=.
            by rewrite mulnDl mulnA addnA.
          }
          have Hcast_assoc' :
              forall (z : 'I_nz) (a : 'I_na) (b : 'I_nb),
              cast_ord (esym (esym (mulnA nz na nb)))
                (mxtens_index (z, mxtens_index (a, b))) =
              mxtens_index (mxtens_index (z, a), b).
          {
            move=> z a b.
            by rewrite (eq_irrelevance (esym (esym (mulnA nz na nb)))
              (mulnA nz na nb)) Hcast_assoc.
          }
          apply/matrixP=> b1 b2.
          rewrite ptrace1E.
          rewrite (reindex (@mxtens_index nz na)) /=.
          2: {
            exists (@mxtens_unindex nz na).
            - by move=> [z a] /=; rewrite mxtens_indexK.
            - by move=> k /=; rewrite mxtens_unindexK.
          }
          rewrite pair_bigV /=.
          rewrite summxE.
          apply: eq_bigr=> z _.
          rewrite ptrace1E.
          apply: eq_bigr=> a _.
          rewrite /sigma_block /sigma_cast mxE /castmx_sq castmxE /=.
          by rewrite Hcast_assoc' Hcast_assoc'.
        }
        have Hsum_id :
            \sum_(ix : 'I_nx) \sum_(jz : 'I_nz)
              (delta_mx ix ix : 'M[C]_nx) *t
              (c0%:C *: ptrace1 (sigma_block jz)) =
            c0%:C *: ((1%:M : 'M[C]_nx) *t sigmaB).
        {
          apply/matrix_tenP=> ix_l bv_l ix_r bv_r.
          rewrite summxE.
          under eq_bigr => ix _ do rewrite summxE.
          under eq_bigr => ix _ do
            under eq_bigr => jz _ do rewrite tensmxE !mxE.
          rewrite mxE tensmxE !mxE.
          rewrite exchange_big /=.
          under eq_bigr => jz _ do rewrite -mulr_suml.
          have Hdelta_sum :
              \sum_(ix : 'I_nx)
                (((ix_l == ix) && (ix_r == ix))%:R : C) =
              ((ix_l == ix_r)%:R : C).
          {
            case Hlr: (ix_l == ix_r).
            - move/eqP: Hlr=> ->.
              rewrite (bigD1 ix_r) //= !eqxx /=.
              rewrite big1 ?addr0 //.
              move=> ix /negPf Hix.
              by rewrite eq_sym Hix andbF.
            - rewrite big1 // => ix _.
              case Hli: (ix_l == ix); last by [].
              by move/eqP: Hli=> <-; rewrite eq_sym Hlr.
          }
          under eq_bigr => jz _ do rewrite Hdelta_sum.
          rewrite -mulr_sumr -mulr_sumr.
          rewrite /sigmaB Hptrace1_block_sum summxE.
          by rewrite !mulrA [((ix_l == ix_r)%:R : C) * c0%:C]mulrC.
        }
        rewrite -Hsum_id.
        exact: Hsum_bound.
      }
      exact: Hmo8_expand.
    }
    have Htarget_le :
        rhoX <= c0%:C *: ((1%:M : 'M[C]_nx) *t ptrace1 sigmaZpAB).
    {
      rewrite -/sigmaB.
      exact: le_trans Hmo10 Hmo9.
    }
    by move: Htarget_le; rewrite le_lownerE.
  }
  pose SX : set R := [set v : R | exists sigmaB : 'M[C]_nb,
        sigmaB \is psdmx /\
        ((1%:M : 'M[C]_nx) *t sigmaB - rhoX) \is psdmx /\
        v = @complex.Re R (\tr sigmaB)]%classic.
  pose SZ : set R := [set v : R | exists sigmaZpAB : 'M[C]_(nz * na * nb),
        sigmaZpAB \is psdmx /\
        ((1%:M : 'M[C]_nz) *t sigmaZpAB - rhoZZpAB) \is psdmx /\
        v = @complex.Re R (\tr sigmaZpAB)]%classic.
  have HRe_realM : forall (cc : R) (zz : C),
      @complex.Re R (cc%:C * zz) = cc * @complex.Re R zz.
  { move=> cc zz; case: zz => a b /=. by rewrite mul0r subr0. }
  have HtensmxZr_local :
      forall m n (k : C) (A : 'M[C]_m) (B : 'M[C]_n),
      A *t (k *: B) = k *: (A *t B).
  {
    move=> m n k A B.
    by rewrite -[k *: B]addr0 (linear_tensmx A) linear0r addr0.
  }
  have HrhoX_den : rhoX \is denmx := rho_XB_subden HM (den1mx_den Hden1).
  have /denmxP[HrhoX_psd _] := HrhoX_den.
  have /den1mxP[HrhoZZpAB_psd /eqP HrhoZZpAB_tr1] := HrhoZZpAB_den1.
  have HSX_has : has_inf SX.
  { exact: (@eur_matrix_phi_has_inf nx nb rhoX HrhoX_psd). }
  have HSZ_has : has_inf SZ.
  { exact: (@eur_matrix_phi_has_inf nz (nz * na * nb) rhoZZpAB
      HrhoZZpAB_psd). }
  (* TeX eqn:mo3: the transported witnesses imply
     Phi_min(X|B) <= c * Phi_min(Z|Z'AB). *)
  have Hphi_transport : inf SX <= c0 * inf SZ.
  {
    have Hdiv_le : c0^-1 * inf SX <= inf SZ.
    {
      rewrite /SZ.
      apply: lb_le_inf.
      - exact: HSZ_has.1.
      - move=> v [sigmaZpAB [Hsigma_psd [Hsigma_feas Hv]]].
        have HinfX_le : inf SX <= c0 * v.
        {
          apply: ge_inf.
          - exact: HSX_has.2.
          - exists (c0%:C *: ptrace1 sigmaZpAB).
            split; last split.
            + apply: psdmxZ; last exact: ptrace1_psd Hsigma_psd.
              by rewrite lecR.
            + rewrite HtensmxZr_local.
              exact: Hfeas_transport Hsigma_psd Hsigma_feas.
            + by rewrite mxtraceZ -tr_ptrace1 HRe_realM Hv.
        }
        have Hdiv_v : inf SX / c0 <= v.
        {
          rewrite ler_pdivrMr // mulrC.
          exact: HinfX_le.
        }
        by rewrite mulrC.
    }
    have Hscaled := ler_wpM2l (ltW Hc0_pos) Hdiv_le.
    have Hlhs :
        c0 * (c0^-1 * inf SX) = inf SX.
    {
      have Hc0_unit : c0 \is a GRing.unit := unitf_gt0 Hc0_pos.
      by rewrite mulrA (mulrV Hc0_unit) mul1r.
    }
    by move: Hscaled; rewrite Hlhs.
  }
  (* TeX q-shift: q = -log c converts the Phi_min comparison into
     H_min(X|B) >= H_min(Z|Z'AB) - log c. *)
  have Hnx_pos : (0 < nx)%N.
  {
    have HrhoX_tr1 : \tr rhoX = 1.
    {
      have HMpsd : forall x, M x \is psdmx
        by move=> x; exact: is_povm_mx_psd HM.
      have HMsum : \sum_(x < nx) M x = 1%:M := is_povm_mx_sum HM.
      have /den1mxP[_ /eqP Hrho_tr1] := Hden1.
      rewrite /rhoX /rho_XB linear_sum /=.
      have Hcyc : forall x,
          \tr ((sqrtmx (M x) *t 1%:M *t 1%:M) *m rhoABC *m
               (sqrtmx (M x) *t 1%:M *t 1%:M)) =
          \tr (rhoABC *m ((M x) *t 1%:M *t 1%:M)).
      {
        move=> x.
        rewrite mxtrace_mulC mulmxA mxtrace_mulC.
        by rewrite !tensmx_mul !mulmx1 (sqrtmxK (HMpsd x)).
      }
      under eq_bigr do rewrite mxtrace_tens tr_delta_mx_ii
        -tr_ptrace1 -tr_ptrace2 mul1r Hcyc.
      rewrite -linear_sum /=.
      rewrite -mulmx_sumr -linear_sumlz /= -linear_sumlz /= HMsum.
      by rewrite !tensmx11 mulmx1 Hrho_tr1.
    }
    have HrhoX_ne : rhoX != 0.
    {
      apply/negP=> /eqP HrhoX0.
      move: HrhoX_tr1.
      by rewrite HrhoX0 mxtrace0 => /eqP; rewrite eq_sym oner_eq0.
    }
    have Hnxnb_pos : (0 < nx * nb)%N.
    {
      have Hrank_pos : (0 < \rank rhoX)%N
        by rewrite lt0n mxrank_eq0 HrhoX_ne.
      exact: leq_trans Hrank_pos (rank_leq_row rhoX).
    }
    by move: Hnxnb_pos; rewrite muln_gt0 => /andP[].
  }
  have Hnz_pos : (0 < nz)%N.
  {
    have HrhoZZpAB_ne : rhoZZpAB != 0.
    {
      apply/negP=> /eqP Hrho0.
      move: HrhoZZpAB_tr1.
      by rewrite -/rhoZZpAB Hrho0 mxtrace0 => /eqP; rewrite eq_sym oner_eq0.
    }
    have Hdim_pos : (0 < nz * (nz * na * nb))%N.
    {
      have Hrank_pos : (0 < \rank rhoZZpAB)%N
        by rewrite lt0n mxrank_eq0 HrhoZZpAB_ne.
      exact: leq_trans Hrank_pos (rank_leq_row rhoZZpAB).
    }
    by move: Hdim_pos; rewrite muln_gt0 => /andP[].
  }
  have HrhoX_tr1 : \tr rhoX = 1.
  {
    have HMpsd : forall x, M x \is psdmx
      by move=> x; exact: is_povm_mx_psd HM.
    have HMsum : \sum_(x < nx) M x = 1%:M := is_povm_mx_sum HM.
    have /den1mxP[_ /eqP Hrho_tr1] := Hden1.
    rewrite /rhoX /rho_XB linear_sum /=.
    have Hcyc : forall x,
        \tr ((sqrtmx (M x) *t 1%:M *t 1%:M) *m rhoABC *m
             (sqrtmx (M x) *t 1%:M *t 1%:M)) =
        \tr (rhoABC *m ((M x) *t 1%:M *t 1%:M)).
    {
      move=> x.
      rewrite mxtrace_mulC mulmxA mxtrace_mulC.
      by rewrite !tensmx_mul !mulmx1 (sqrtmxK (HMpsd x)).
    }
    under eq_bigr do rewrite mxtrace_tens tr_delta_mx_ii
      -tr_ptrace1 -tr_ptrace2 mul1r Hcyc.
    rewrite -linear_sum /=.
    rewrite -mulmx_sumr -linear_sumlz /= -linear_sumlz /= HMsum.
    by rewrite !tensmx11 mulmx1 Hrho_tr1.
  }
  have HPX_pos : 0 < inf SX.
  {
    have HrhoX_tr_pos : 0 < @complex.Re R (\tr rhoX)
      by rewrite HrhoX_tr1 re_realid ltr01.
    have Hlb : @complex.Re R (\tr rhoX) / nx%:R <= inf SX.
    { exact: (@eur_matrix_phi_trace_lb nx nb rhoX
        Hnx_pos HrhoX_psd HrhoX_tr_pos). }
    have Hdiv_pos : 0 < @complex.Re R (\tr rhoX) / nx%:R.
    { apply: divr_gt0=> //; by rewrite ltr0n. }
    exact: lt_le_trans Hdiv_pos Hlb.
  }
  have HPZ_pos : 0 < inf SZ.
  {
    have HrhoZZpAB_tr_pos : 0 < @complex.Re R (\tr rhoZZpAB)
      by rewrite -/rhoZZpAB HrhoZZpAB_tr1 re_realid ltr01.
    have Hlb :
        @complex.Re R (\tr rhoZZpAB) / nz%:R <= inf SZ.
    { exact: (@eur_matrix_phi_trace_lb nz (nz * na * nb) rhoZZpAB
        Hnz_pos HrhoZZpAB_psd HrhoZZpAB_tr_pos). }
    have Hdiv_pos : 0 < @complex.Re R (\tr rhoZZpAB) / nz%:R.
    { apply: divr_gt0=> //; by rewrite ltr0n. }
    exact: lt_le_trans Hdiv_pos Hlb.
  }
  have Hlog2_mul_local : forall x y : R, 0 < x -> 0 < y ->
      log2 (x * y) = log2 x + log2 y.
  { move=> x y Hx Hy; by rewrite /log2 lnM // mulrDl. }
  have Hlog_le : log2 (inf SX) <= log2 (c0 * inf SZ).
  { exact: log2_le_pos HPX_pos Hphi_transport. }
  have Hdiff_le : log2 (inf SX) - log2 (inf SZ) <= log2 c0.
  {
    move: Hlog_le.
    rewrite Hlog2_mul_local //.
    move=> Hlog0.
    rewrite lerBlDr.
    exact: Hlog0.
  }
  rewrite /hmin_mx -/rhoX -/rhoZZpAB -/SX -/SZ.
  move: Hdiff_le.
  by rewrite -lerN2 opprB opprK addrC.
Qed.
(* path: eur:ucr_pure_zero -> eur:entropic_uncertainty_relation -> *)
(*   eur:entropic_uncertainty_relation -> *)
(*   bb84:entropic_uncertainty_relation_bb84 -> bb84:bb84_secret *)
Lemma ucr_pure_zero
    (rhoABC : 'M[C]_(na * nb * nc))
    (M : 'I_nx -> 'M[C]_na) (N : 'I_nz -> 'M[C]_na) :
  rhoABC \is den1mx -> \rank rhoABC = 1%N ->
  is_povm_mx M -> is_povm_mx N ->
  overlap_mx M N != 0 ->
  hmin_mx (rho_XB M rhoABC) + hmax_mx (rho_ZC N rhoABC) >=
  - log2 (overlap_mx M N).
Proof.
  move=> Hden1 Hrank HM HN Hoverlap.
  pose rhoZZ := rho_ZZpABC N rhoABC.
  have HrhoZZ_den1 : rhoZZ \is den1mx.
  { (* Lift den1mx through the Stinespring isometry (trace preserved). *)
    have /den1mxP[Hpsd /eqP Htr] := Hden1.
    have HNpsd : forall z, N z \is psdmx
      by move=> z; exact: is_povm_mx_psd HN.
    have HNsum : \sum_(z < nz) N z = 1%:M := is_povm_mx_sum HN.
    apply/den1mxP; split.
    - rewrite /rhoZZ /rho_ZZpABC; exact: form_psdmx.
    - apply/eqP; rewrite /rhoZZ /rho_ZZpABC.
      rewrite mxtrace_mulC mulmxA !adjmx_tens !tensmx_mul !mulmx1 !adjmx1.
      by rewrite (stinespring_U2_iso HNpsd HNsum) !tensmx11 mul1mx Htr. }
  have Hzz_dim :
      (((nz * nz) * na) * nb = nz * (nz * na * nb))%N.
  { by rewrite !mulnA. }
  have HrhoZZpAB_den1 :
      castmx_sq Hzz_dim (rho_ZZpAB N rhoABC) \is den1mx.
  {
    rewrite cast_qualifier_diag /rho_ZZpAB -/rhoZZ.
    move/den1mxP: HrhoZZ_den1 => [Hzz_psd /eqP Hzz_tr].
    apply/den1mxP; split.
    - exact: ptrace2_psd Hzz_psd.
    - by apply/eqP; rewrite -tr_ptrace2 Hzz_tr.
  }
  (* TeX eqn:mo1: max/min duality on the pure Stinespring Z-lift. *)
  have Hmo1 :
      hmax_mx (rho_ZC N rhoABC) =
      - hmin_mx (castmx_sq Hzz_dim (rho_ZZpAB N rhoABC)).
  { exact: (@ucr_pure_zero_mo1 rhoABC N Hzz_dim Hden1 Hrank HN). }
  (* TeX eqn:mo6/eqn:mo10 with eqn:mo9: W-conjugation and overlap bound. *)
  have Hmo6 :
      - log2 (overlap_mx M N) <=
      hmin_mx (rho_XB M rhoABC) +
      - hmin_mx (castmx_sq Hzz_dim (rho_ZZpAB N rhoABC)).
  { exact: (@ucr_pure_zero_mo6 rhoABC M N Hzz_dim
      Hden1 HM HN Hoverlap HrhoZZpAB_den1). }
  rewrite Hmo1.
  exact: Hmo6.
Qed.
End Stage0.
(* ================================================================== *)
(* Stage 1: pure ρ_{ABC}, ε ≥ 0 via Uhlmann                              *)
(* Paper: Tomamichel & Renner (PRL 106, 110506 (2011); arXiv:1009.2015),  *)
(*   "Proof of the Main Result", ε-smooth generalization (close states).  *)
(* math: For pure ρ_{ABC} and 0 ≤ ε < 1:                                   *)
(*       H^ε_min(X|B)_ρ + H^ε_max(Z|C)_ρ ≥ -log c                        *)
(* ================================================================== *)
Section Stage1.
Variable (na nb nc nx nz : nat).
(* Paper: Tomamichel & Renner (PRL 106, 110506 (2011); arXiv:1009.2015),       *)
(*   "Proof of the Main Result", Stage 1 (ε-smooth, pure ρ).                    *)
(* math: smooth_hmin_mx ε ρ_XB + smooth_hmax_mx ε ρ_ZC ≥ -log c  for pure ρ    *)
(* path: eur:ucr_pure_smooth -> eur:entropic_uncertainty_relation -> *)
(*   eur:entropic_uncertainty_relation -> *)
(*   bb84:entropic_uncertainty_relation_bb84 -> bb84:bb84_secret *)
Lemma ucr_pure_smooth
    (eps : R)
    (rhoABC : 'M[C]_(na * nb * nc))
    (M : 'I_nx -> 'M[C]_na) (N : 'I_nz -> 'M[C]_na) :
  rhoABC \is denmx -> \rank rhoABC = 1%N ->
  is_povm_mx M -> is_povm_mx N ->
  overlap_mx M N != 0 ->
  0 <= eps -> eps < Num.sqrt (@complex.Re R (\tr rhoABC)) ->
  smooth_hmin_mx eps (rho_XB M rhoABC) +
  smooth_hmax_mx eps (rho_ZC N rhoABC) >=
  - log2 (overlap_mx M N).
Proof.
  move=> Hden Hrank HM HN Hoverlap Heps0 Heps_lt_sqrt.
  pose rhoX := rho_XB M rhoABC.
  pose rhoZ := rho_ZC N rhoABC.
  have /denmxP[Hrho_psd Hrho_tr_C] := Hden.
  have Hrho_tr : @complex.Re R (\tr rhoABC) <= 1.
  { have Hreal := ger0_real (psdmx_trace Hrho_psd).
    by move: Hrho_tr_C; rewrite -(RRe_real Hreal) -[1]/(1%:C) lecR. }
  have Hrho_ne : rhoABC != 0
    by apply/eqP=> H0; rewrite H0 mxrank0 in Hrank.
  have Hrho_tr_pos : 0 < @complex.Re R (\tr rhoABC).
  { have Htr_real := ger0_real (psdmx_trace Hrho_psd).
    have Htr_re_ge0 : 0 <= @complex.Re R (\tr rhoABC)
      by move: (psdmx_trace Hrho_psd);
         rewrite -(RRe_real Htr_real) -[0]/(0%:C) lecR.
    rewrite lt_def Htr_re_ge0 andbT.
    apply/eqP => Htr0.
    have HrhoABC_zero : rhoABC == 0.
    { rewrite -(psdmx_trace_eq0 Hrho_psd); apply/eqP.
      by rewrite -(RRe_real Htr_real) Htr0 rmorph0. }
    by move/eqP: Hrho_ne; rewrite (eqP HrhoABC_zero). }
  have HrhoZ_den : rhoZ \is denmx := rho_ZC_subden HN Hden.
  (* Derived `eps < 1` from `eps < sqrt(Re(Tr ρ))` and `Re(Tr ρ) ≤ 1`. *)
  have Heps_lt_1 : eps < 1.
  { apply: lt_le_trans Heps_lt_sqrt _.
    have Hsqrt_mono :
        Num.sqrt (@complex.Re R (\tr rhoABC)) <= Num.sqrt 1
      by apply: ler_wsqrtr.
    by rewrite sqrtr1 in Hsqrt_mono. }
  have Heps1 : eps < 1 := Heps_lt_1.
  have /denmxP[HrhoZ_psd HrhoZ_tr] := HrhoZ_den.
  have HrhoZ_trR : @complex.Re R (\tr rhoZ) <= 1.
  {
    have Hreal := ger0_real (psdmx_trace HrhoZ_psd).
    by move: HrhoZ_tr; rewrite -(RRe_real Hreal) -[1]/(1%:C) lecR.
  }
  have HNpsd : forall z, N z \is psdmx
    by move=> z; exact: is_povm_mx_psd HN.
  have HNsum : \sum_(z < nz) N z = 1%:M := is_povm_mx_sum HN.
  (* POVM completeness: \tr ρ_Z = \tr ρ_{ABC} (replaces den1mx-specific Tr=1). *)
  have HrhoZ_tr_eq : \tr rhoZ = \tr rhoABC.
  {
    rewrite /rhoZ /rho_ZC linear_sum /=.
    have Hcyc : forall z,
        \tr ((sqrtmx (N z) *t 1%:M *t 1%:M) *m rhoABC *m
             (sqrtmx (N z) *t 1%:M *t 1%:M)) =
        \tr (rhoABC *m ((N z) *t 1%:M *t 1%:M)).
    {
      move=> z.
      rewrite mxtrace_mulC mulmxA mxtrace_mulC.
      by rewrite !tensmx_mul !mulmx1 (sqrtmxK (HNpsd z)).
    }
    under eq_bigr do rewrite mxtrace_tens tr_delta_mx_ii -tr_ptrace1 mul1r Hcyc.
    rewrite -linear_sum /=.
    rewrite -mulmx_sumr -linear_sumlz /= -linear_sumlz /= HNsum.
    by rewrite !tensmx11 mulmx1.
  }
  have Habc_pos : (0 < na * nb * nc)%N.
  {
    have Hrank_pos : (0 < \rank rhoABC)%N
      by rewrite lt0n mxrank_eq0 Hrho_ne.
    exact: leq_trans Hrank_pos (rank_leq_row rhoABC).
  }
  have Hnc_pos : (0 < nc)%N.
  { by move: Habc_pos; rewrite !muln_gt0 => /andP[/andP[_ _] ?]. }
  have HrhoZ_ne : rhoZ != 0.
  {
    apply/eqP => HrhoZ0.
    have Htr_zero : \tr rhoABC = 0
      by rewrite -HrhoZ_tr_eq HrhoZ0 mxtrace0.
    have Hre_zero : @complex.Re R (\tr rhoABC) = 0
      by rewrite Htr_zero raddf0.
    by move: Hrho_tr_pos; rewrite Hre_zero ltxx.
  }
  have Hnz_pos : (0 < nz)%N.
  {
    have Hrank_pos : (0 < \rank rhoZ)%N
      by rewrite lt0n mxrank_eq0 HrhoZ_ne.
    have Hdim_pos : (0 < nz * nc)%N :=
      leq_trans Hrank_pos (rank_leq_row rhoZ).
    by move: Hdim_pos; rewrite muln_gt0 => /andP[].
  }
  (* TeX Stinespring marginal: fixed pure extension of rho_ZC. *)
  pose rhoZZ := rho_ZZpABC N rhoABC.
  have Hzz_dim :
      (((nz * nz) * na) * nb = nz * (nz * na * nb))%N.
  { by rewrite !mulnA. }
  pose rhoZZpAB : 'M[C]_(nz * (nz * na * nb)) :=
    castmx_sq Hzz_dim (rho_ZZpAB N rhoABC).
  pose rhoZCZpAB : 'M[C]_((nz * nc) * (nz * na * nb)) :=
    rho_ZC_ZpAB N rhoABC.
  have HrhoZZ_den : rhoZZ \is denmx.
  { by rewrite /rhoZZ; exact: rho_ZZpABC_denmx. }
  have HrhoZZpAB_den : rhoZZpAB \is denmx.
  { rewrite /rhoZZpAB cast_qualifier_diag /rho_ZZpAB -/rhoZZ.
    move/denmxP: HrhoZZ_den => [Hzz_psd Hzz_tr].
    apply/denmxP; split.
    - exact: ptrace2_psd Hzz_psd.
    - by rewrite -tr_ptrace2. }
  have HZC_extension :
      rhoZCZpAB \is denmx /\
      \rank rhoZCZpAB = 1%N /\
      ptrace2 rhoZCZpAB = rhoZ.
  { exact: rho_ZC_ZpAB_extension HN Hden Hrank. }
  have Heps_lt_rhoZ :
      eps < Num.sqrt (@complex.Re R (\tr rhoZ)).
  { by rewrite HrhoZ_tr_eq. }
    have Hmax_has_inf :
        has_inf [set v : R | exists tau : 'M[C]_(nz * nc),
          ((tau \is denmx) && (0 < @complex.Re R (\tr tau))) &&
          (pur_dist_mx tau rhoZ <= eps) /\ v = hmax_mx tau].
    {
      exact: @smooth_hmax_mx_has_inf nz nc eps rhoZ Hnz_pos Hnc_pos
        HrhoZ_den Heps0 Heps_lt_rhoZ.
    }
  rewrite /smooth_hmax_mx -/rhoZ -/rhoX.
    suff Hinf :
        - log2 (overlap_mx M N) - smooth_hmin_mx eps rhoX <=
        inf [set v : R | exists tau : 'M[C]_(nz * nc),
          ((tau \is denmx) && (0 < @complex.Re R (\tr tau))) &&
          (pur_dist_mx tau rhoZ <= eps) /\ v = hmax_mx tau].
  { by move: Hinf; rewrite lerBlDr addrC. }
  apply: lb_le_inf.
    - exact: Hmax_has_inf.1.
    - move=> v [tau [Htau_feas ->]].
      move: Htau_feas => /andP[/andP[Htau_den Htau_pos] Htau_pd].
      have Htau_psd : tau \is psdmx := denmx_psd Htau_den.
      have Htau_close : eps_close eps rhoZ tau.
      { by rewrite /eps_close Htau_den Htau_pd. }
    (* TeX Stage 1 property (ii): extend the smooth-max witness on ZC.
       The auxiliary R makes the purifier large enough for arbitrary
       subnormalized witnesses in the epsilon ball. *)
    pose Rdim := nz * nc.
    have HRdim_pos : (0 < Rdim)%N by rewrite /Rdim muln_gt0 Hnz_pos Hnc_pos.
    pose r0 : 'I_Rdim := Ordinal HRdim_pos.
    pose etaR : 'M[C]_Rdim := delta_mx r0 r0.
    have Heta_tr1 : \tr etaR = 1.
    { by rewrite /etaR tr_delta_mx_ii. }
    have Heta_den1 : etaR \is den1mx.
    {
      apply/den1mxP; split.
      - exact: delta_mx_ii_psdmx.
      - by apply/eqP; rewrite Heta_tr1.
    }
    have Heta_rank1 : \rank etaR = 1%N.
    {
      have Houter :
          etaR =
          (delta_mx r0 (0 : 'I_1) : 'M[C]_(Rdim, 1)) *m
            (delta_mx r0 (0 : 'I_1))^*t.
      {
        apply/matrixP => p q.
        rewrite !mxE big_ord1 !mxE conjC_nat.
        by case: (p == r0); case: (q == r0) => //=;
          rewrite ?mul1r ?mul0r ?mulr0.
      }
      apply/eqP; rewrite eqn_leq; apply/andP; split.
      - rewrite Houter.
        apply: (leq_trans (mxrankM_maxl _ _)).
        exact: rank_leq_col.
      - rewrite lt0n mxrank_eq0.
        apply/eqP => Heta0.
        have Htr_ne0 : \tr etaR != 0 by rewrite Heta_tr1 oner_eq0.
        by rewrite Heta0 mxtrace0 eqxx in Htr_ne0.
    }
    pose rhoZC_big0 : 'M[C]_(((nz * nc) * (nz * na * nb)) * Rdim) :=
      rhoZCZpAB *t etaR.
    pose rhoZC_big : 'M[C]_((nz * nc) * ((nz * na * nb) * Rdim)) :=
      castmx_sq (esym (mulnA (nz * nc) (nz * na * nb) Rdim))
        rhoZC_big0.
    have [HZC_den [HZC_rank HZC_ptr]] := HZC_extension.
    have HrhoZC_big_den : rhoZC_big \is denmx.
    { rewrite /rhoZC_big cast_qualifier_diag.
      exact: denmx_tens HZC_den (den1mx_den Heta_den1). }
    have HrhoZC_big_rank : \rank rhoZC_big = 1%N.
    {
      rewrite /rhoZC_big /castmx_sq mxrank_cast /rhoZC_big0.
      by rewrite rank_tens HZC_rank Heta_rank1.
    }
    have HrhoZC_big_ptr : ptrace2 rhoZC_big = rhoZ.
    {
      rewrite /rhoZC_big /rhoZC_big0 ptrace2_compose.
      by rewrite ptrace_tensmx Heta_tr1 scale1r HZC_ptr.
    }
    have Htau_ne : tau != 0.
    {
      apply/negP=> /eqP Htau0.
      have Hnz_nc_pos : (0 < nz * nc)%N
        by rewrite muln_gt0 Hnz_pos Hnc_pos.
      have Hzero_psd : (0 : 'M[C]_(nz * nc)) \is psdmx :=
        psdmx0 C (nz * nc).
      have Hzero_tr : @complex.Re R (\tr (0 : 'M[C]_(nz * nc))) <= 1
        by rewrite mxtrace0 raddf0 ler01.
      have Htrace_lb :
          Num.sqrt (@complex.Re R (\tr rhoZ))
            <= pur_dist_mx (0 : 'M[C]_(nz * nc)) rhoZ.
      {
        have Hsqrt_le :
            Num.sqrt (@complex.Re R (\tr rhoZ)) <=
            Num.sqrt (@complex.Re R (\tr (0 : 'M[C]_(nz * nc)))) +
            pur_dist_mx (0 : 'M[C]_(nz * nc)) rhoZ.
          {
            have Hzero_den : (0 : 'M[C]_(nz * nc)) \is denmx :=
              @denmx0 R (nz * nc).
            rewrite /pur_dist_mx.
            exact: pur_dist_mx_trace_sqrt_bound Hnz_nc_pos
              HrhoZ_den Hzero_den.
          }
        move: Hsqrt_le.
        by rewrite mxtrace0 raddf0 sqrtr0 add0r.
      }
      have Hpd_le_eps : pur_dist_mx (0 : 'M[C]_(nz * nc)) rhoZ <= eps
        by move: Htau_pd; rewrite Htau0.
      have := lt_le_trans Heps_lt_rhoZ (le_trans Htrace_lb Hpd_le_eps).
      by rewrite ltxx.
    }
    have Henv0_pos : (0 < nz * na * nb)%N.
    {
      have Habc_mul : ((0 < na)%N && (0 < nb)%N) && (0 < nc)%N.
      { by move: Habc_pos; rewrite !muln_gt0. }
      move/andP: Habc_mul => [/andP[Hna_pos Hnb_pos] _].
      by rewrite muln_gt0 muln_gt0 Hnz_pos Hna_pos Hnb_pos.
    }
    have Htau_rank_big : (\rank tau <= (nz * na * nb) * Rdim)%N.
    {
      have Hrank_le_R : (\rank tau <= Rdim)%N
        by rewrite /Rdim; exact: rank_leq_row.
      have HR_le_big : (Rdim <= (nz * na * nb) * Rdim)%N.
      { by rewrite /Rdim; exact: leq_pmull Henv0_pos. }
      exact: leq_trans Hrank_le_R HR_le_big.
    }
    have HrhoZC_big_nz : rhoZC_big != 0
      by apply/eqP => H0; rewrite H0 mxrank0 in HrhoZC_big_rank.
    have [_ Htau_pure_ext] :=
      @eur_ii (nz * nc) ((nz * na * nb) * Rdim) eps
        rhoZ rhoZC_big tau HrhoZC_big_den HrhoZC_big_nz
        HrhoZC_big_ptr Htau_close.
    have [tauZC_big
      [HtauZC_big_den [HtauZC_big_rank [HtauZC_big_ptr HtauZC_big_pd]]]] :=
      Htau_pure_ext HrhoZC_big_rank Htau_rank_big Htau_ne.
    (* TeX Stage 1 dual side: the complementary Z|Z'ABR marginal of the
       purified smooth-max witness. *)
    pose Ebig := (nz * na * nb) * Rdim.
    pose tauZpABR : 'M[C]_(nz * Ebig) :=
      @rho_AC_mx R nz nc Ebig tauZC_big.
    have HtauZC_big_psd : tauZC_big \is psdmx :=
      denmx_psd HtauZC_big_den.
      have HtauZpABR_psd : tauZpABR \is psdmx.
      {
        rewrite /tauZpABR /rho_AC_mx.
        apply: ptrace2_psd.
        exact: mxswap23_psdmx HtauZC_big_psd.
      }
    (* TeX Stage 1 W-transport: view the complementary register as
       Z' A (B R), apply W := U V^dagger on Z Z' A, and keep B R. *)
    pose nBR := nb * Rdim.
    have HEbig_BR : (Ebig = nz * na * nBR)%N
      by rewrite /Ebig /nBR mulnA.
    have HtauZE_dim : (nz * Ebig = nz * (nz * na * nBR))%N
      by rewrite HEbig_BR.
    pose tauZpA_BR : 'M[C]_(nz * (nz * na * nBR)) :=
      castmx_sq HtauZE_dim tauZpABR.
    have Hzz_dim_BR :
        (((nz * nz) * na) * nBR = nz * (nz * na * nBR))%N.
    { by rewrite !mulnA. }
    pose tauZZpABR3 : 'M[C]_(((nz * nz) * na) * nBR) :=
      castmx_sq (esym Hzz_dim_BR) tauZpA_BR.
    pose W0 : 'M[C]_((nx * nx) * na, (nz * nz) * na) :=
      partial_iso_W M N.
    pose WBR : 'M[C]_(((nx * nx) * na) * nBR,
                      ((nz * nz) * na) * nBR) :=
      W0 *t (1%:M : 'M[C]_nBR).
    have Hisometry_outer_le :
        forall m n (V0 : 'M[C]_(m, n)),
        V0^*t *m V0 = 1%:M -> V0 *m V0^*t <= 1%:M.
    {
      move=> m n V0 HV0; rewrite le_lownerE.
      set P := V0 *m V0^*t.
      have HP2 : P *m P = P.
      {
        have H1 : V0 *m V0^*t *m V0 = V0
          by rewrite -mulmxA HV0 mulmx1.
        by rewrite /P mulmxA H1.
      }
      have Hherm : P^*t = P by rewrite /P adjmxM adjmxK.
      have -> : 1%:M - P = (1%:M - P) *m (1%:M - P)^*t.
      {
        rewrite linearB /= adjmx1 Hherm.
        rewrite mulmxBl !mulmxBr !mul1mx !mulmx1.
        by rewrite HP2 addrN subr0.
      }
      exact: form_psd.
    }
    have HM_iso :
        (stinespring_U2 M)^*t *m stinespring_U2 M = 1%:M.
    {
      have HMpsd : forall x, M x \is psdmx
        by move=> x; exact: is_povm_mx_psd HM.
      exact: stinespring_U2_iso HMpsd (is_povm_mx_sum HM).
    }
    have HN_iso :
        (stinespring_U2 N)^*t *m stinespring_U2 N = 1%:M.
    {
      have HNpsd' : forall z, N z \is psdmx
        by move=> z; exact: is_povm_mx_psd HN.
      exact: stinespring_U2_iso HNpsd' (is_povm_mx_sum HN).
    }
    have HW0_le : W0^*t *m W0 <= 1%:M.
    {
      have HW0E :
          W0^*t *m W0 =
          stinespring_U2 N *m
            ((stinespring_U2 M)^*t *m stinespring_U2 M) *m
            (stinespring_U2 N)^*t.
      { by rewrite /W0 /partial_iso_W adjmxM adjmxK !mulmxA. }
      rewrite HW0E HM_iso mulmx1.
      exact: Hisometry_outer_le HN_iso.
    }
    have HWBR_le : WBR^*t *m WBR <= 1%:M.
    {
      rewrite /WBR adjmx_tens adjmx1 tensmx_mul mul1mx.
      rewrite le_lownerE.
      have HW0_diff : (1%:M - W0^*t *m W0) \is psdmx
        by move: HW0_le; rewrite le_lownerE.
      have -> :
          1%:M - W0^*t *m W0 *t (1%:M : 'M[C]_nBR) =
          (1%:M - W0^*t *m W0) *t (1%:M : 'M[C]_nBR).
      { by rewrite -tensmx11 -linearBl. }
      exact: psdmx_tens HW0_diff (psdmx1 _ _).
    }
    pose tauXXpABR : 'M[C]_(((nx * nx) * na) * nBR) :=
      WBR *m tauZZpABR3 *m WBR^*t.
    have HptraceXA_dim_BR :
        (nBR * (nx * nx * na) = nBR * nx * (nx * na))%N.
    { by rewrite !mulnA. }
    pose ptraceXA_BR
        (rho : 'M[C]_(((nx * nx) * na) * nBR)) : 'M[C]_(nx * nBR) :=
      let rho1 : 'M[C]_(nBR * (nx * nx * na)) := mxswap rho in
      let rho2 : 'M[C]_((nBR * nx) * (nx * na)) :=
        castmx_sq HptraceXA_dim_BR rho1 in
      let rho3 : 'M[C]_(nBR * nx) := ptrace2 rho2 in
      mxswap rho3.
    pose tauXBR : 'M[C]_(nx * nBR) := ptraceXA_BR tauXXpABR.
    pose tauXB_full : 'M[C]_((nx * nb) * Rdim) :=
      castmx_sq (mulnA nx nb Rdim) tauXBR.
    pose tauXB : 'M[C]_(nx * nb) := ptrace2 tauXB_full.
    have HtauZpA_BR_psd : tauZpA_BR \is psdmx.
    {
      rewrite /tauZpA_BR.
      exact: castmx_sq_psdmx HtauZpABR_psd.
    }
    have HtauZZpABR3_psd : tauZZpABR3 \is psdmx.
    {
      rewrite /tauZZpABR3.
      exact: castmx_sq_psdmx HtauZpA_BR_psd.
    }
    have HtauXXpABR_psd : tauXXpABR \is psdmx.
    {
      rewrite /tauXXpABR.
      exact: psdmx_bimap_closed_gen HtauZZpABR3_psd.
    }
    have HtauXBR_psd : tauXBR \is psdmx.
    {
      rewrite /tauXBR /ptraceXA_BR.
      apply: mxswap_psdmx.
      apply: ptrace2_psd.
      apply: castmx_sq_psdmx.
      exact: mxswap_psdmx HtauXXpABR_psd.
    }
    have HtauXB_psd : tauXB \is psdmx.
    {
      rewrite /tauXB /tauXB_full.
      apply: ptrace2_psd.
      exact: castmx_sq_psdmx HtauXBR_psd.
    }
    have HtauZpABR_den : tauZpABR \is denmx.
    {
      rewrite /tauZpABR /rho_AC_mx.
      apply: ptrace2_denmx.
      exact: mxswap23_denmx HtauZC_big_den.
    }
    have HtauZpA_BR_den : tauZpA_BR \is denmx.
    { by rewrite /tauZpA_BR cast_qualifier_diag. }
    have HtauZZpABR3_den : tauZZpABR3 \is denmx.
    { by rewrite /tauZZpABR3 cast_qualifier_diag. }
    have HtauXXpABR_den : tauXXpABR \is denmx.
    {
      rewrite /tauXXpABR.
      exact: denmx_conj_contraction HWBR_le HtauZZpABR3_den.
    }
    have HtauXBR_den : tauXBR \is denmx.
    {
      rewrite /tauXBR /ptraceXA_BR.
      apply: mxswap_denmx.
      apply: ptrace2_denmx.
      rewrite cast_qualifier_diag.
      exact: mxswap_denmx HtauXXpABR_den.
    }
    have HtauXB_den : tauXB \is denmx.
    {
      rewrite /tauXB /tauXB_full.
      apply: ptrace2_denmx.
      by rewrite cast_qualifier_diag.
    }
    have HtauZC_big_pd_sym :
        pur_dist_mx tauZC_big rhoZC_big <= eps.
    {
      have HrhoZC_big_psd : rhoZC_big \is psdmx :=
        denmx_psd HrhoZC_big_den.
      move: HtauZC_big_pd.
      by rewrite /pur_dist_mx (gfid_sym_mx HrhoZC_big_psd HtauZC_big_psd).
    }
    have /denmxP[HtauXB_psd' HtauXB_tr] := HtauXB_den.
    have HtauXB_trR : @complex.Re R (\tr tauXB) <= 1.
    {
      have Hreal := ger0_real (psdmx_trace HtauXB_psd').
      by move: HtauXB_tr; rewrite -(RRe_real Hreal) -[1]/(1%:C) lecR.
    }
    (* TeX property (i) after property (ii): contract the purified-distance
       bound along the proof-local map
       ZZ'ABR -> XX'ABR -> XBR -> XB. *)
    have HrhoX_den : rhoX \is denmx := rho_XB_subden HM Hden.
    have /denmxP[HrhoX_psd HrhoX_tr] := HrhoX_den.
    have HrhoX_trR : @complex.Re R (\tr rhoX) <= 1.
    {
      have Hreal := ger0_real (psdmx_trace HrhoX_psd).
      by move: HrhoX_tr; rewrite -(RRe_real Hreal) -[1]/(1%:C) lecR.
    }
    have HMpsd : forall x, M x \is psdmx
      by move=> x; exact: is_povm_mx_psd HM.
    have HMsum : \sum_(x < nx) M x = 1%:M := is_povm_mx_sum HM.
    have HrhoX_tr_eq : \tr rhoX = \tr rhoABC.
    {
      rewrite /rhoX /rho_XB linear_sum /=.
      have Hcyc : forall x,
          \tr ((sqrtmx (M x) *t 1%:M *t 1%:M) *m rhoABC *m
               (sqrtmx (M x) *t 1%:M *t 1%:M)) =
          \tr (rhoABC *m ((M x) *t 1%:M *t 1%:M)).
      {
        move=> x.
        rewrite mxtrace_mulC mulmxA mxtrace_mulC.
        by rewrite !tensmx_mul !mulmx1 (sqrtmxK (HMpsd x)).
      }
      under eq_bigr do rewrite mxtrace_tens tr_delta_mx_ii
        -tr_ptrace1 -tr_ptrace2 mul1r Hcyc.
      rewrite -linear_sum /=.
      rewrite -mulmx_sumr -linear_sumlz /= -linear_sumlz /= HMsum.
      by rewrite !tensmx11 mulmx1.
    }
    have HrhoX_ne : rhoX != 0.
    {
      apply/eqP => HrhoX0.
      have Htr_zero : \tr rhoABC = 0
        by rewrite -HrhoX_tr_eq HrhoX0 mxtrace0.
      have Hre_zero : @complex.Re R (\tr rhoABC) = 0
        by rewrite Htr_zero raddf0.
      by move: Hrho_tr_pos; rewrite Hre_zero ltxx.
    }
    have Hnxnb_pos : (0 < nx * nb)%N.
    {
      have Hrank_pos : (0 < \rank rhoX)%N
        by rewrite lt0n mxrank_eq0 HrhoX_ne.
      exact: leq_trans Hrank_pos (rank_leq_row rhoX).
    }
    have Hnx_pos : (0 < nx)%N.
    { by move: Hnxnb_pos; rewrite muln_gt0 => /andP[]. }
    have HXB_pd :
        pur_dist_mx tauXB rhoX <= eps.
    {
      (* TeX property (i): apply purified-distance monotonicity to the
         proof-local CPTN map
         ZC(Z'ABR) -> Z(Z'ABR) -> XX'ABR -> XBR -> XB. *)
      pose rhoZpABR_ref : 'M[C]_(nz * Ebig) :=
        @rho_AC_mx R nz nc Ebig rhoZC_big.
      pose rhoZpA_BR_ref : 'M[C]_(nz * (nz * na * nBR)) :=
        castmx_sq HtauZE_dim rhoZpABR_ref.
      pose rhoZZpABR3_ref : 'M[C]_(((nz * nz) * na) * nBR) :=
        castmx_sq (esym Hzz_dim_BR) rhoZpA_BR_ref.
      pose rhoXXpABR_ref : 'M[C]_(((nx * nx) * na) * nBR) :=
        WBR *m rhoZZpABR3_ref *m WBR^*t.
      pose rhoXBR_ref : 'M[C]_(nx * nBR) :=
        ptraceXA_BR rhoXXpABR_ref.
      pose rhoXB_full_ref : 'M[C]_((nx * nb) * Rdim) :=
        castmx_sq (mulnA nx nb Rdim) rhoXBR_ref.
      pose rhoXB_ref : 'M[C]_(nx * nb) := ptrace2 rhoXB_full_ref.
      have Hpd_transport :
          pur_dist_mx tauXB rhoXB_ref <=
          pur_dist_mx tauZC_big rhoZC_big.
      {
        pose pdmx := fun n (X Y : 'M[C]_n) =>
          Num.sqrt (1 - (gfidelity X Y)^2).
        change (pdmx (nx * nb) tauXB rhoXB_ref <=
                pdmx ((nz * nc) * Ebig) tauZC_big rhoZC_big).
        have Hpd_AC :
            pdmx (nz * Ebig) tauZpABR rhoZpABR_ref <=
            pdmx ((nz * nc) * Ebig) tauZC_big rhoZC_big.
        {
          pose Kac (c0 : 'I_nc) :
              'M[C]_(nz * Ebig, (nz * nc) * Ebig) :=
            \matrix_(i, j)
              if j == mxtens_index
                   (mxtens_index ((mxtens_unindex i).1, c0),
                    (mxtens_unindex i).2)
              then 1 else 0.
          have Kac_row : forall c0 (z0 : 'I_nz) (e0 : 'I_Ebig) p,
              Kac c0 (mxtens_index (z0, e0)) p =
              (if p == mxtens_index (mxtens_index (z0, c0), e0)
               then 1 else 0 : C).
          { by move=> c0 z0 e0 p; rewrite /Kac mxE !mxtens_indexK. }
          have Kac_adj_col : forall c0 (z0 : 'I_nz) (e0 : 'I_Ebig) p,
              (Kac c0)^*t p (mxtens_index (z0, e0)) =
              (if p == mxtens_index (mxtens_index (z0, c0), e0)
               then 1 else 0 : C).
          {
            move=> c0 z0 e0 p.
            rewrite mxE_adj /Kac mxE !mxtens_indexK.
            by case: eqP=> _; rewrite ?conjC1 ?conjC0.
          }
          have Hac_action : forall X : 'M[C]_((nz * nc) * Ebig),
              \sum_(c0 : 'I_nc) Kac c0 *m X *m (Kac c0)^*t =
              @rho_AC_mx R nz nc Ebig X.
          {
            move=> X; apply/matrixP=> i j.
            case: (mxtens_indexP i)=> zi ei.
            case: (mxtens_indexP j)=> zj ej.
            transitivity
              (\sum_(c0 : 'I_nc)
                X (mxtens_index (mxtens_index (zi, c0), ei))
                  (mxtens_index (mxtens_index (zj, c0), ej))).
            {
              rewrite summxE.
              apply: eq_bigr=> c0 _.
              rewrite !mxE.
              rewrite (bigD1 (mxtens_index (mxtens_index (zj, c0), ej))) //=.
              rewrite [X in _ + X]big1 ?addr0.
              2: {
                move=> q /negPf Hq.
                by rewrite Kac_adj_col Hq mulr0.
              }
              rewrite Kac_adj_col eqxx mulr1.
              rewrite mxE.
              rewrite (bigD1 (mxtens_index (mxtens_index (zi, c0), ei))) //=.
              rewrite [X in _ + X]big1 ?addr0.
              2: {
                move=> p /negPf Hp.
                by rewrite Kac_row Hp mul0r.
              }
              by rewrite Kac_row eqxx mul1r.
            }
            rewrite /rho_AC_mx ptrace2E1 ptrace1E.
            apply: eq_bigr=> c0 _.
            by rewrite mxE !mxtens_indexK mxswap23E !sigma23_tens.
          }
          have Hac_tp :
              \sum_(c0 : 'I_nc) (Kac c0)^*t *m Kac c0 = 1%:M.
          {
            have Kac_col : forall c0 (z0 : 'I_nz) (c1 : 'I_nc)
                (e0 : 'I_Ebig) i,
                Kac c0 i (mxtens_index (mxtens_index (z0, c1), e0)) =
                (if (c1 == c0) && (i == mxtens_index (z0, e0))
                 then 1 else 0 : C).
            {
              move=> c0 z0 c1 e0 i.
              case: (mxtens_indexP i)=> zi ei.
              rewrite Kac_row.
              have Hidx :
                  (mxtens_index (mxtens_index (z0, c1), e0) ==
                   mxtens_index (mxtens_index (zi, c0), ei)) =
                  ((c1 == c0) &&
                   (mxtens_index (zi, ei) == mxtens_index (z0, e0))).
              {
                rewrite (inj_eq (can_inj (@mxtens_indexK _ _))) -pair_eqE /=.
                rewrite (inj_eq (can_inj (@mxtens_indexK _ _))) -pair_eqE /=.
                rewrite (inj_eq (can_inj (@mxtens_indexK _ _))) -pair_eqE /=.
                rewrite [z0 == zi]eq_sym [e0 == ei]eq_sym.
                by case: (zi == z0); case: (c1 == c0); case: (ei == e0).
              }
              by rewrite Hidx.
            }
            have Kac_adj_in : forall c0 (z0 : 'I_nz) (c1 : 'I_nc)
                (e0 : 'I_Ebig) i,
                (Kac c0)^*t
                  (mxtens_index (mxtens_index (z0, c1), e0)) i =
                (if (c1 == c0) && (i == mxtens_index (z0, e0))
                 then 1 else 0 : C).
            {
              move=> c0 z0 c1 e0 i.
              rewrite mxE_adj Kac_col.
              by case: (_ && _); rewrite ?conjC1 ?conjC0.
            }
            apply/matrixP=> p q.
            case: (mxtens_indexP p)=> zcp ep.
            case: (mxtens_indexP zcp)=> zp cp.
            case: (mxtens_indexP q)=> zcq eq.
            case: (mxtens_indexP zcq)=> zq cq.
            have Hterm : forall c0 : 'I_nc,
                ((Kac c0)^*t *m Kac c0)
                  (mxtens_index (mxtens_index (zp, cp), ep))
                  (mxtens_index (mxtens_index (zq, cq), eq)) =
                (if ((cp == c0) && (cq == c0) &&
                    (mxtens_index (zp, ep) == mxtens_index (zq, eq)))
                 then 1 else 0 : C).
            {
              move=> c0.
              rewrite mxE.
              transitivity
                (\sum_(i : 'I_(nz * Ebig))
                  (if (cp == c0) && (i == mxtens_index (zp, ep))
                   then 1 else 0 : C) *
                  (if (cq == c0) && (i == mxtens_index (zq, eq))
                   then 1 else 0 : C)).
              {
                apply: eq_bigr=> i _.
                by rewrite Kac_adj_in Kac_col.
              }
              case Hcp: (cp == c0); case Hcq: (cq == c0); rewrite /=.
              - case Hout: (mxtens_index (zp, ep) == mxtens_index (zq, eq)).
                + move/eqP: Hout=> Hout_eq.
                  rewrite Hout_eq (bigD1 (mxtens_index (zq, eq))) //= !eqxx.
                  rewrite [X in _ + X]big1.
                  * by rewrite addr0 ?mul1r ?mulr1.
                  * by move=> i /negPf Hi; rewrite Hi ?mul0r ?mulr0.
                + rewrite (bigD1 (mxtens_index (zp, ep))) //= eqxx.
                  rewrite Hout mulr0.
                  rewrite [X in _ + X]big1.
                  * by rewrite addr0 ?mul1r ?mulr1.
                  * by move=> i /negPf Hi; rewrite Hi ?mul0r ?mulr0.
              - apply: big1=> i _.
                by rewrite ?mulr0 ?mul0r.
              - apply: big1=> i _.
                by rewrite ?mulr0 ?mul0r.
              - apply: big1=> i _.
                by rewrite ?mulr0 ?mul0r.
            }
            rewrite summxE.
            under eq_bigr=> c0 _ do rewrite Hterm.
            rewrite mxE.
            have Hinput_eq :
                (mxtens_index (mxtens_index (zp, cp), ep) ==
                 mxtens_index (mxtens_index (zq, cq), eq)) =
                ((cp == cq) &&
                 (mxtens_index (zp, ep) == mxtens_index (zq, eq))).
            {
              rewrite (inj_eq (can_inj (@mxtens_indexK _ _))) -pair_eqE /=.
              rewrite (inj_eq (can_inj (@mxtens_indexK _ _))) -pair_eqE /=.
              rewrite (inj_eq (can_inj (@mxtens_indexK _ _))) -pair_eqE /=.
              by case: (zp == zq); case: (cp == cq); case: (ep == eq).
            }
            rewrite Hinput_eq.
            case Hout: (mxtens_index (zp, ep) == mxtens_index (zq, eq)).
            - rewrite andbT.
              case Hcq: (cp == cq).
              + move/eqP: Hcq=> <-.
                rewrite (bigD1 cp) //= !eqxx /=.
                rewrite [X in _ + X]big1.
                * by rewrite addr0.
                * move=> c0 /negPf Hc0.
                  by rewrite eq_sym Hc0 andbF.
              + rewrite big1 // => c0 _.
                case Hcp0: (cp == c0); last by [].
                move/eqP: Hcp0=> <-.
                by rewrite eq_sym Hcq.
            - rewrite andbF.
              apply: big1=> c0 _.
              by rewrite andbF.
          }
          have /denmxP[_ HtauZC_big_tr] := HtauZC_big_den.
          have HrhoZC_big_psd : rhoZC_big \is psdmx :=
            denmx_psd HrhoZC_big_den.
          have /denmxP[_ HrhoZC_big_tr] :=
            HrhoZC_big_den.
          have Hna_pos : (0 < na)%N.
          { by move: Habc_pos; rewrite !muln_gt0 => /andP[/andP[]]. }
          have Hnb_pos : (0 < nb)%N.
          { by move: Habc_pos; rewrite !muln_gt0 => /andP[/andP[_]]. }
          have Hnin_pos : (0 < (nz * nc) * Ebig)%N.
          { by rewrite /Ebig /Rdim !muln_gt0 Hnz_pos Hnc_pos Hna_pos Hnb_pos. }
          have Hout_pos : (0 < nz * Ebig)%N.
          { by rewrite /Ebig /Rdim !muln_gt0 Hnz_pos Hnc_pos Hna_pos Hnb_pos. }
          have HtauZC_big_trR : @complex.Re R (\tr tauZC_big) <= 1.
          {
            have Hreal := ger0_real (psdmx_trace HtauZC_big_psd).
            by move: HtauZC_big_tr; rewrite -(RRe_real Hreal) -[1]/(1%:C) lecR.
          }
          have HrhoZC_big_trR : @complex.Re R (\tr rhoZC_big) <= 1.
          {
            have Hreal := ger0_real (psdmx_trace HrhoZC_big_psd).
            by move: HrhoZC_big_tr; rewrite -(RRe_real Hreal) -[1]/(1%:C) lecR.
          }
          have Hcontract :=
              @pur_dist_mx_cptn_kraus_contract R 'I_nc
                ((nz * nc) * Ebig) (nz * Ebig)
                Kac tauZC_big rhoZC_big
                Hnin_pos Hout_pos HtauZC_big_den HrhoZC_big_den Hac_tp.
          move: Hcontract.
          by rewrite !Hac_action /pdmx -/tauZpABR -/rhoZpABR_ref.
        }
        have Hpd_cast_ZE :
            pdmx (nz * (nz * na * nBR)) tauZpA_BR rhoZpA_BR_ref =
            pdmx (nz * Ebig) tauZpABR rhoZpABR_ref.
        { by rewrite /pdmx /tauZpA_BR /rhoZpA_BR_ref /castmx_sq gfid_cast_mx. }
        have Hpd_cast_ZZA :
            pdmx (((nz * nz) * na) * nBR) tauZZpABR3 rhoZZpABR3_ref =
            pdmx (nz * (nz * na * nBR)) tauZpA_BR rhoZpA_BR_ref.
        { by rewrite /pdmx /tauZZpABR3 /rhoZZpABR3_ref /castmx_sq gfid_cast_mx. }
        have Hpd_W :
            pdmx (((nx * nx) * na) * nBR) tauXXpABR rhoXXpABR_ref <=
            pdmx (((nz * nz) * na) * nBR) tauZZpABR3 rhoZZpABR3_ref.
        {
          have HrhoZpABR_ref_den : rhoZpABR_ref \is denmx.
          {
            rewrite /rhoZpABR_ref /rho_AC_mx.
            apply: ptrace2_denmx.
            exact: mxswap23_denmx HrhoZC_big_den.
          }
          have HrhoZpA_BR_ref_den : rhoZpA_BR_ref \is denmx.
          { by rewrite /rhoZpA_BR_ref cast_qualifier_diag. }
          have HrhoZZpABR3_ref_den : rhoZZpABR3_ref \is denmx.
          { by rewrite /rhoZZpABR3_ref cast_qualifier_diag. }
          have /denmxP[_ HtauZZpABR3_tr] := HtauZZpABR3_den.
          have /denmxP[HrhoZZpABR3_ref_psd HrhoZZpABR3_ref_tr] :=
            HrhoZZpABR3_ref_den.
          have HtauZZpABR3_trR :
              @complex.Re R (\tr tauZZpABR3) <= 1.
          {
            have Hreal := ger0_real (psdmx_trace HtauZZpABR3_psd).
            by move: HtauZZpABR3_tr;
              rewrite -(RRe_real Hreal) -[1]/(1%:C) lecR.
          }
          have HrhoZZpABR3_ref_trR :
              @complex.Re R (\tr rhoZZpABR3_ref) <= 1.
          {
            have Hreal := ger0_real (psdmx_trace HrhoZZpABR3_ref_psd).
            by move: HrhoZZpABR3_ref_tr;
              rewrite -(RRe_real Hreal) -[1]/(1%:C) lecR.
          }
          have Hna_pos : (0 < na)%N.
          { by move: Habc_pos; rewrite !muln_gt0 => /andP[/andP[]]. }
          have Hnb_pos : (0 < nb)%N.
          { by move: Habc_pos; rewrite !muln_gt0 => /andP[/andP[_]]. }
          have HnBR_pos : (0 < nBR)%N.
          { by rewrite /nBR /Rdim !muln_gt0 Hnb_pos Hnz_pos Hnc_pos. }
          have Hwin_pos : (0 < ((nz * nz) * na) * nBR)%N.
          { by rewrite /nBR /Rdim !muln_gt0 Hnz_pos Hna_pos Hnb_pos Hnc_pos. }
          have Hwout_pos : (0 < ((nx * nx) * na) * nBR)%N.
          { by rewrite /nBR /Rdim !muln_gt0 Hnx_pos Hna_pos Hnb_pos Hnz_pos Hnc_pos. }
          pose KW (b : bool) : 'M[C]_(((nx * nx) * na) * nBR,
                                      ((nz * nz) * na) * nBR) :=
            if b then WBR else 0.
          have HW_kraus :
              \sum_(b : bool) (KW b)^*t *m KW b <= 1%:M.
          {
            rewrite /KW big_bool /= linear0 ?mul0mx ?mulmx0 ?add0r ?addr0.
            exact: HWBR_le.
          }
          have Hcontract :=
                @pur_dist_mx_cptn_kraus_contract_le R bool
                (((nz * nz) * na) * nBR) (((nx * nx) * na) * nBR)
                KW tauZZpABR3 rhoZZpABR3_ref
                Hwin_pos Hwout_pos HtauZZpABR3_den
                HrhoZZpABR3_ref_den HW_kraus.
          have HW_action : forall X : 'M[C]_(((nz * nz) * na) * nBR),
              \sum_(b : bool) KW b *m X *m (KW b)^*t =
              WBR *m X *m WBR^*t.
          {
            move=> X.
            by rewrite /KW big_bool /= linear0 ?mul0mx ?mulmx0
              ?add0r ?addr0.
          }
          pose A : 'M[C]_(((nx * nx) * na) * nBR) :=
            WBR *m tauZZpABR3 *m WBR^*t.
          pose B : 'M[C]_(((nx * nx) * na) * nBR) :=
            WBR *m rhoZZpABR3_ref *m WBR^*t.
          rewrite /pdmx /tauXXpABR /rhoXXpABR_ref.
          change (Num.sqrt (1 - (gfidelity A B)^2) <=
                  Num.sqrt (1 - (gfidelity tauZZpABR3 rhoZZpABR3_ref)^2)).
          have HA :
              A = \sum_(b : bool) KW b *m tauZZpABR3 *m (KW b)^*t.
          { by rewrite /A HW_action. }
          have HB :
              B = \sum_(b : bool) KW b *m rhoZZpABR3_ref *m (KW b)^*t.
          { by rewrite /B HW_action. }
          rewrite HA HB.
          exact: Hcontract.
        }
        have Hpd_XA :
            pdmx (nx * nBR) tauXBR rhoXBR_ref <=
            pdmx (((nx * nx) * na) * nBR) tauXXpABR rhoXXpABR_ref.
        {
          (* TeX property (i): trace out the copied X' register and A by
             the proof-local Kraus family indexed by (X',A). *)
          pose xain (x0 : 'I_nx) (br0 : 'I_nBR) (k : 'I_(nx * na)) :
              'I_(((nx * nx) * na) * nBR) :=
            mxtens_index
              (mxtens_index
                (mxtens_index (x0, (mxtens_unindex k).1),
                 (mxtens_unindex k).2), br0).
          pose Kxa (k : 'I_(nx * na)) :
              'M[C]_(nx * nBR, ((nx * nx) * na) * nBR) :=
            \matrix_(i, j)
              if j == xain (mxtens_unindex i).1 (mxtens_unindex i).2 k
              then 1 else 0.
          have Kxa_row : forall k (x0 : 'I_nx) (br0 : 'I_nBR) p,
              Kxa k (mxtens_index (x0, br0)) p =
              (if p == xain x0 br0 k then 1 else 0 : C).
          { by move=> k x0 br0 p; rewrite /Kxa mxE !mxtens_indexK. }
          have Kxa_adj_col : forall k (x0 : 'I_nx) (br0 : 'I_nBR) p,
              (Kxa k)^*t p (mxtens_index (x0, br0)) =
              (if p == xain x0 br0 k then 1 else 0 : C).
          {
            move=> k x0 br0 p.
            rewrite mxE_adj /Kxa mxE !mxtens_indexK.
            by case: eqP=> _; rewrite ?conjC1 ?conjC0.
          }
          have ptraceXA_BRE :
              forall (rho' : 'M[C]_(((nx * nx) * na) * nBR))
                (ix0 : 'I_nx) (ibr : 'I_nBR)
                (jx : 'I_nx) (jbr : 'I_nBR),
              ptraceXA_BR rho' (mxtens_index (ix0, ibr))
                (mxtens_index (jx, jbr)) =
              \sum_(k : 'I_(nx * na)) rho' (xain ix0 ibr k) (xain jx jbr k).
          {
            move=> rho' ix0 ibr jx jbr.
            rewrite /ptraceXA_BR /=.
            rewrite mxE !mxtens_indexK /=.
            rewrite ptrace2E1 ptrace1E.
            apply: eq_bigr=> k _.
            case: (mxtens_indexP k)=> x2 a0.
            rewrite mxE !mxtens_indexK /= /castmx_sq castmxE /=.
            have Hcast_a4 : forall (br : 'I_nBR)
                (xx1 xx2 : 'I_nx) (aa : 'I_na),
                cast_ord (esym HptraceXA_dim_BR)
                  (mxtens_index (mxtens_index (br, xx1),
                    mxtens_index (xx2, aa))) =
                mxtens_index (br, mxtens_index
                  (mxtens_index (xx1, xx2), aa)).
            {
              move=> br xx1 xx2 aa.
              apply/val_inj=> /=.
              by rewrite !mulnDl !mulnA !addnA.
            }
            by rewrite /xain !mxtens_indexK !Hcast_a4 mxE !mxtens_indexK.
          }
          have Hxa_action : forall X : 'M[C]_(((nx * nx) * na) * nBR),
              \sum_(k : 'I_(nx * na)) Kxa k *m X *m (Kxa k)^*t =
              ptraceXA_BR X.
          {
            move=> X; apply/matrixP=> i j.
            case: (mxtens_indexP i)=> xi bri.
            case: (mxtens_indexP j)=> xj brj.
            transitivity
              (\sum_(k : 'I_(nx * na)) X (xain xi bri k) (xain xj brj k)).
            {
              rewrite summxE.
              apply: eq_bigr=> k _.
              rewrite !mxE.
              rewrite (bigD1 (xain xj brj k)) //=.
              rewrite [X in _ + X]big1 ?addr0.
              2: {
                move=> q /negPf Hq.
                by rewrite Kxa_adj_col Hq mulr0.
              }
              rewrite Kxa_adj_col eqxx mulr1.
              rewrite mxE.
              rewrite (bigD1 (xain xi bri k)) //=.
              rewrite [X in _ + X]big1 ?addr0.
              2: {
                move=> p /negPf Hp.
                by rewrite Kxa_row Hp mul0r.
              }
              by rewrite Kxa_row eqxx mul1r.
            }
            by rewrite ptraceXA_BRE.
          }
          have Hxa_tp :
              \sum_(k : 'I_(nx * na)) (Kxa k)^*t *m Kxa k = 1%:M.
          {
            have Kxa_col : forall k (x0 xp0 : 'I_nx)
                (a0 : 'I_na) (br0 : 'I_nBR) i,
                Kxa k i
                  (mxtens_index (mxtens_index (mxtens_index (x0, xp0), a0), br0)) =
                (if (k == mxtens_index (xp0, a0)) &&
                    (i == mxtens_index (x0, br0))
                 then 1 else 0 : C).
            {
              move=> k x0 xp0 a0 br0 i.
              case: (mxtens_indexP i)=> xi bri.
              rewrite Kxa_row.
              have Hidx :
                  (mxtens_index (mxtens_index (mxtens_index (x0, xp0), a0), br0)
                    == xain xi bri k) =
                  ((k == mxtens_index (xp0, a0)) &&
                   (mxtens_index (xi, bri) == mxtens_index (x0, br0))).
              {
                case: (mxtens_indexP k)=> xk ak.
                rewrite /xain !mxtens_indexK.
                rewrite !(inj_eq (can_inj (@mxtens_indexK _ _))) -!pair_eqE /=.
                rewrite ?[xk == xp0]eq_sym ?[ak == a0]eq_sym
                        ?[xi == x0]eq_sym ?[bri == br0]eq_sym.
                rewrite [mxtens_index (mxtens_index (x0, xp0), a0) == _]
                  (inj_eq (can_inj (@mxtens_indexK _ _))) -pair_eqE /=.
                rewrite [mxtens_index (x0, xp0) == _]
                  (inj_eq (can_inj (@mxtens_indexK _ _))) -pair_eqE /=.
                by case: (x0 == xi); case: (xp0 == xk);
                   case: (a0 == ak); case: (br0 == bri).
              }
              by rewrite Hidx.
            }
            have Kxa_adj_in : forall k (x0 xp0 : 'I_nx)
                (a0 : 'I_na) (br0 : 'I_nBR) i,
                (Kxa k)^*t
                  (mxtens_index (mxtens_index (mxtens_index (x0, xp0), a0), br0)) i =
                (if (k == mxtens_index (xp0, a0)) &&
                    (i == mxtens_index (x0, br0))
                 then 1 else 0 : C).
            {
              move=> k x0 xp0 a0 br0 i.
              rewrite mxE_adj Kxa_col.
              by case: (_ && _); rewrite ?conjC1 ?conjC0.
            }
            apply/matrixP=> p q.
            case: (mxtens_indexP p)=> pxabr pbr.
            case: (mxtens_indexP pxabr)=> pxx pa.
            case: (mxtens_indexP pxx)=> px pxp.
            case: (mxtens_indexP q)=> qxabr qbr.
            case: (mxtens_indexP qxabr)=> qxx qa.
            case: (mxtens_indexP qxx)=> qx qxp.
            have Hterm : forall k : 'I_(nx * na),
                ((Kxa k)^*t *m Kxa k)
                  (mxtens_index (mxtens_index (mxtens_index (px, pxp), pa), pbr))
                  (mxtens_index (mxtens_index (mxtens_index (qx, qxp), qa), qbr)) =
                (if ((k == mxtens_index (pxp, pa)) &&
                     (k == mxtens_index (qxp, qa)) &&
                     (mxtens_index (px, pbr) == mxtens_index (qx, qbr)))
                 then 1 else 0 : C).
            {
              move=> k.
              rewrite mxE.
              transitivity
                (\sum_(i : 'I_(nx * nBR))
                  (if (k == mxtens_index (pxp, pa)) &&
                       (i == mxtens_index (px, pbr))
                   then 1 else 0 : C) *
                  (if (k == mxtens_index (qxp, qa)) &&
                       (i == mxtens_index (qx, qbr))
                   then 1 else 0 : C)).
              {
                apply: eq_bigr=> i _.
                by rewrite Kxa_adj_in Kxa_col.
              }
              case Hkp: (k == mxtens_index (pxp, pa));
                case Hkq: (k == mxtens_index (qxp, qa)); rewrite /=.
              - case Hout: (mxtens_index (px, pbr) == mxtens_index (qx, qbr)).
                + move/eqP: Hout=> Hout_eq.
                  rewrite Hout_eq (bigD1 (mxtens_index (qx, qbr))) //= !eqxx.
                  rewrite [X in _ + X]big1.
                  * by rewrite addr0 ?mul1r ?mulr1.
                  * by move=> i /negPf Hi; rewrite Hi ?mul0r ?mulr0.
                + rewrite (bigD1 (mxtens_index (px, pbr))) //= eqxx.
                  rewrite Hout mulr0.
                  rewrite [X in _ + X]big1.
                  * by rewrite addr0 ?mul1r ?mulr1.
                  * by move=> i /negPf Hi; rewrite Hi ?mul0r ?mulr0.
              - apply: big1=> i _.
                by rewrite ?mulr0 ?mul0r.
              - apply: big1=> i _.
                by rewrite ?mulr0 ?mul0r.
              - apply: big1=> i _.
                by rewrite ?mulr0 ?mul0r.
            }
            rewrite summxE.
            under eq_bigr=> k _ do rewrite Hterm.
            rewrite mxE.
            have Hinput_eq :
                (mxtens_index (mxtens_index (mxtens_index (px, pxp), pa), pbr) ==
                 mxtens_index (mxtens_index (mxtens_index (qx, qxp), qa), qbr)) =
                ((mxtens_index (pxp, pa) == mxtens_index (qxp, qa)) &&
                 (mxtens_index (px, pbr) == mxtens_index (qx, qbr))).
            {
              rewrite !(inj_eq (can_inj (@mxtens_indexK _ _))) -!pair_eqE /=.
              rewrite [mxtens_index (mxtens_index (px, pxp), pa) == _]
                (inj_eq (can_inj (@mxtens_indexK _ _))) -pair_eqE /=.
              rewrite [mxtens_index (px, pxp) == _]
                (inj_eq (can_inj (@mxtens_indexK _ _))) -pair_eqE /=.
              by case: (px == qx); case: (pxp == qxp);
                 case: (pa == qa); case: (pbr == qbr).
            }
            rewrite Hinput_eq.
            case Hout: (mxtens_index (px, pbr) == mxtens_index (qx, qbr)).
            - rewrite andbT.
              case Hkidx: (mxtens_index (pxp, pa) == mxtens_index (qxp, qa)).
              + move/eqP: Hkidx=> Hkidx_eq.
                rewrite Hkidx_eq (bigD1 (mxtens_index (qxp, qa))) //= !eqxx /=.
                rewrite [X in _ + X]big1.
                * by rewrite addr0.
                * move=> k /negPf Hk.
                  have Hk' : (mxtens_index (qxp, qa) == k) = false
                    by rewrite eq_sym Hk.
                  by rewrite ?Hk ?Hk' andbF.
              + rewrite big1 // => k _.
                case Hkp0: (k == mxtens_index (pxp, pa)); last by [].
                move/eqP: Hkp0=> ->.
                have Hkidx' :
                    (mxtens_index (qxp, qa) == mxtens_index (pxp, pa)) = false
                  by rewrite eq_sym Hkidx.
                by rewrite ?Hkidx ?Hkidx'.
            - rewrite andbF.
              apply: big1=> k _.
              by rewrite andbF.
          }
          have HrhoZpABR_ref_den : rhoZpABR_ref \is denmx.
          {
            rewrite /rhoZpABR_ref /rho_AC_mx.
            apply: ptrace2_denmx.
            exact: mxswap23_denmx HrhoZC_big_den.
          }
          have HrhoZpA_BR_ref_den : rhoZpA_BR_ref \is denmx.
          { by rewrite /rhoZpA_BR_ref cast_qualifier_diag. }
          have HrhoZZpABR3_ref_den : rhoZZpABR3_ref \is denmx.
          { by rewrite /rhoZZpABR3_ref cast_qualifier_diag. }
          have HrhoXXpABR_ref_den : rhoXXpABR_ref \is denmx.
          {
            rewrite /rhoXXpABR_ref.
            exact: denmx_conj_contraction HWBR_le HrhoZZpABR3_ref_den.
          }
          have /denmxP[_ HtauXXpABR_tr] := HtauXXpABR_den.
          have /denmxP[HrhoXXpABR_ref_psd HrhoXXpABR_ref_tr] :=
            HrhoXXpABR_ref_den.
          have HtauXXpABR_trR :
              @complex.Re R (\tr tauXXpABR) <= 1.
          {
            have Hreal := ger0_real (psdmx_trace HtauXXpABR_psd).
            by move: HtauXXpABR_tr;
              rewrite -(RRe_real Hreal) -[1]/(1%:C) lecR.
          }
          have HrhoXXpABR_ref_trR :
              @complex.Re R (\tr rhoXXpABR_ref) <= 1.
          {
            have Hreal := ger0_real (psdmx_trace HrhoXXpABR_ref_psd).
            by move: HrhoXXpABR_ref_tr;
              rewrite -(RRe_real Hreal) -[1]/(1%:C) lecR.
          }
          have Hna_pos : (0 < na)%N.
          { by move: Habc_pos; rewrite !muln_gt0 => /andP[/andP[]]. }
          have Hnb_pos : (0 < nb)%N.
          { by move: Habc_pos; rewrite !muln_gt0 => /andP[/andP[_]]. }
          have HnBR_pos : (0 < nBR)%N.
          { by rewrite /nBR /Rdim !muln_gt0 Hnb_pos Hnz_pos Hnc_pos. }
          have Hnin_pos : (0 < ((nx * nx) * na) * nBR)%N.
          { by rewrite /nBR /Rdim !muln_gt0 Hnx_pos Hna_pos Hnb_pos Hnz_pos Hnc_pos. }
          have Hout_pos : (0 < nx * nBR)%N.
          { by rewrite /nBR /Rdim !muln_gt0 Hnx_pos Hnb_pos Hnz_pos Hnc_pos. }
          have Hcontract :=
                @pur_dist_mx_cptn_kraus_contract R 'I_(nx * na)
                (((nx * nx) * na) * nBR) (nx * nBR)
                Kxa tauXXpABR rhoXXpABR_ref
                Hnin_pos Hout_pos HtauXXpABR_den HrhoXXpABR_ref_den Hxa_tp.
          pose A : 'M[C]_(nx * nBR) := ptraceXA_BR tauXXpABR.
          pose B : 'M[C]_(nx * nBR) := ptraceXA_BR rhoXXpABR_ref.
          rewrite /pdmx /tauXBR /rhoXBR_ref.
          change (Num.sqrt (1 - (gfidelity A B)^2) <=
                  Num.sqrt (1 - (gfidelity tauXXpABR rhoXXpABR_ref)^2)).
          have HA :
              A = \sum_(k : 'I_(nx * na))
                    Kxa k *m tauXXpABR *m (Kxa k)^*t.
          { by rewrite /A Hxa_action. }
          have HB :
              B = \sum_(k : 'I_(nx * na))
                    Kxa k *m rhoXXpABR_ref *m (Kxa k)^*t.
          { by rewrite /B Hxa_action. }
          rewrite HA HB.
          exact: Hcontract.
        }
        have Hpd_cast_XBR :
            pdmx ((nx * nb) * Rdim) tauXB_full rhoXB_full_ref =
            pdmx (nx * nBR) tauXBR rhoXBR_ref.
        { by rewrite /pdmx /tauXB_full /rhoXB_full_ref /castmx_sq gfid_cast_mx. }
        have Hpd_R :
            pdmx (nx * nb) tauXB rhoXB_ref <=
            pdmx ((nx * nb) * Rdim) tauXB_full rhoXB_full_ref.
        {
          (* TeX property (i): discard the auxiliary purifier R by purified
             distance monotonicity under partial trace. *)
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
          have HtauXB_full_psd : tauXB_full \is psdmx.
          { by rewrite /tauXB_full; exact: castmx_sq_psdmx HtauXBR_psd. }
          have HrhoZpABR_ref_den : rhoZpABR_ref \is denmx.
          {
            rewrite /rhoZpABR_ref /rho_AC_mx.
            apply: ptrace2_denmx.
            exact: mxswap23_denmx HrhoZC_big_den.
          }
          have HrhoZpA_BR_ref_den : rhoZpA_BR_ref \is denmx.
          { by rewrite /rhoZpA_BR_ref cast_qualifier_diag. }
          have HrhoZZpABR3_ref_den : rhoZZpABR3_ref \is denmx.
          { by rewrite /rhoZZpABR3_ref cast_qualifier_diag. }
          have HrhoXXpABR_ref_den : rhoXXpABR_ref \is denmx.
          {
            rewrite /rhoXXpABR_ref.
            exact: denmx_conj_contraction HWBR_le HrhoZZpABR3_ref_den.
          }
          have HrhoXBR_ref_psd : rhoXBR_ref \is psdmx.
          {
            rewrite /rhoXBR_ref /ptraceXA_BR.
            apply: mxswap_psdmx.
            apply: ptrace2_psd.
            apply: castmx_sq_psdmx.
            apply: mxswap_psdmx.
            exact: denmx_psd HrhoXXpABR_ref_den.
          }
          have HrhoXB_full_ref_psd : rhoXB_full_ref \is psdmx.
          { by rewrite /rhoXB_full_ref; exact: castmx_sq_psdmx HrhoXBR_ref_psd. }
          rewrite /tauXB /rhoXB_ref.
          exact: (Hpdmx_ptrace2 (nx * nb) Rdim tauXB_full rhoXB_full_ref
            HRdim_pos HtauXB_full_psd HrhoXB_full_ref_psd).
        }
        apply: (le_trans Hpd_R).
        rewrite Hpd_cast_XBR.
        apply: (le_trans Hpd_XA).
        apply: (le_trans Hpd_W).
        rewrite Hpd_cast_ZZA Hpd_cast_ZE.
        exact: Hpd_AC.
      }
      have HrhoXB_ref : rhoXB_ref = rhoX.
      {
        (* TeX property (i), reference side: the lifted reference state is the
           original Stinespring reference with an inert purifier R; the W-map
           and X'A trace preserve that tensor factor. *)
        have HrhoXB_full_ref :
            rhoXB_full_ref = rhoX *t etaR.
        {
          pose W : 'M[C]_(((nx * nx) * na) * nb,
                          ((nz * nz) * na) * nb) :=
            W0 *t (1%:M : 'M[C]_nb).
          have HptraceXA_dim :
              (nb * (nx * nx * na) = nb * nx * (nx * na))%N.
          { by rewrite !mulnA. }
          pose ptraceXA
              (rho : 'M[C]_(((nx * nx) * na) * nb)) : 'M[C]_(nx * nb) :=
            let rho1 : 'M[C]_(nb * (nx * nx * na)) := mxswap rho in
            let rho2 : 'M[C]_((nb * nx) * (nx * na)) :=
              castmx_sq HptraceXA_dim rho1 in
            let rho3 : 'M[C]_(nb * nx) := ptrace2 rho2 in
            mxswap rho3.
          pose rhoZZpAB3_noR : 'M[C]_(((nz * nz) * na) * nb) :=
            castmx_sq (esym Hzz_dim) rhoZZpAB.
          have HzzR_dim :
              ((((nz * nz) * na) * nb) * Rdim =
               ((nz * nz) * na) * nBR)%N.
          { by rewrite /nBR !mulnA. }
          have HrhoZZ_ref_tensor :
              rhoZZpABR3_ref =
              castmx_sq HzzR_dim (rhoZZpAB3_noR *t etaR).
          {
            (* TeX property (ii), reference specialization: the complementary
               marginal of rho_ZC(Z'AB) ⊗ etaR is rho_ZZ'AB ⊗ etaR. *)
            have rho_AC_mxE :
                forall (X : 'M[C]_((nz * nc) * Ebig))
                  (z1 z2 : 'I_nz) (e1 e2 : 'I_Ebig),
                @rho_AC_mx R nz nc Ebig X
                  (mxtens_index (z1, e1)) (mxtens_index (z2, e2)) =
                \sum_(c0 : 'I_nc)
                  X (mxtens_index (mxtens_index (z1, c0), e1))
                    (mxtens_index (mxtens_index (z2, c0), e2)).
            {
              move=> X z1 z2 e1 e2.
              rewrite /rho_AC_mx ptrace2E1 ptrace1E.
              apply: eq_bigr=> c0 _.
              by rewrite mxE !mxtens_indexK mxswap23E !sigma23_tens.
            }
            have Hcast_R : forall (zza : 'I_((nz * nz) * na))
                (br : 'I_nb) (r : 'I_Rdim),
                cast_ord (esym HzzR_dim)
                  (mxtens_index (zza, mxtens_index (br, r))) =
                mxtens_index (mxtens_index (zza, br), r).
            {
              move=> zza br r; apply/val_inj=> /=.
              by rewrite /nBR !mulnDl !mulnA !addnA.
            }
            have Hcast_BR : forall (z zp : 'I_nz) (a : 'I_na)
                (br : 'I_nBR),
                cast_ord Hzz_dim_BR
                  (mxtens_index (mxtens_index (mxtens_index (z, zp), a), br)) =
                mxtens_index (z, mxtens_index (mxtens_index (zp, a), br)).
            {
              move=> z zp a br; apply/val_inj=> /=.
              by rewrite !mulnDl !mulnA !addnA.
            }
            have Hcast_BR2 : forall (z zp : 'I_nz) (a : 'I_na)
                (br : 'I_nBR),
                cast_ord (esym (esym Hzz_dim_BR))
                  (mxtens_index (mxtens_index (mxtens_index (z, zp), a), br)) =
                mxtens_index (z, mxtens_index (mxtens_index (zp, a), br)).
            {
              move=> z zp a br; apply/val_inj=> /=.
              by rewrite !mulnDl !mulnA !addnA.
            }
            have Hcast_tauZE : forall (z zp : 'I_nz) (a : 'I_na)
                (b : 'I_nb) (r : 'I_Rdim),
                cast_ord (esym HtauZE_dim)
                  (mxtens_index
                    (z, mxtens_index (mxtens_index (zp, a),
                      mxtens_index (b, r)))) =
                mxtens_index
                  (z, mxtens_index
                    (mxtens_index (mxtens_index (zp, a), b), r)).
            {
              move=> z zp a b r; apply/val_inj=> /=.
              by rewrite /Ebig /nBR !mulnDl !mulnA !addnA.
            }
            have Hcast_big : forall (z : 'I_nz) (c : 'I_nc)
                (zp : 'I_nz) (a : 'I_na) (b : 'I_nb) (r : 'I_Rdim),
                cast_ord (mulnA (nz * nc) (nz * na * nb) Rdim)
                  (mxtens_index
                    (mxtens_index (z, c),
                     mxtens_index (mxtens_index (mxtens_index (zp, a), b), r))) =
                mxtens_index
                  (mxtens_index
                    (mxtens_index (z, c),
                     mxtens_index (mxtens_index (zp, a), b)), r).
            {
              move=> z c zp a b r; apply/val_inj=> /=.
              by rewrite !mulnDl !mulnA !addnA.
            }
            have Hcast_big2 : forall (z : 'I_nz) (c : 'I_nc)
                (zp : 'I_nz) (a : 'I_na) (b : 'I_nb) (r : 'I_Rdim),
                cast_ord (esym (esym (mulnA (nz * nc) (nz * na * nb) Rdim)))
                  (mxtens_index
                    (mxtens_index (z, c),
                     mxtens_index (mxtens_index (mxtens_index (zp, a), b), r))) =
                mxtens_index
                  (mxtens_index
                    (mxtens_index (z, c),
                     mxtens_index (mxtens_index (zp, a), b)), r).
            {
              move=> z c zp a b r; apply/val_inj=> /=.
              by rewrite !mulnDl !mulnA !addnA.
            }
            have Hcast_zz : forall (z zp : 'I_nz) (a : 'I_na) (b : 'I_nb),
                cast_ord Hzz_dim
                  (mxtens_index
                    (mxtens_index (mxtens_index (z, zp), a), b)) =
                mxtens_index (z, mxtens_index (mxtens_index (zp, a), b)).
            {
              move=> z zp a b; apply/val_inj=> /=.
              by rewrite !mulnDl !mulnA !addnA.
            }
            have Hcast_zz2 : forall (z zp : 'I_nz) (a : 'I_na) (b : 'I_nb),
                cast_ord (esym (esym Hzz_dim))
                  (mxtens_index
                    (mxtens_index (mxtens_index (z, zp), a), b)) =
                mxtens_index (z, mxtens_index (mxtens_index (zp, a), b)).
            {
              move=> z zp a b; apply/val_inj=> /=.
              by rewrite !mulnDl !mulnA !addnA.
            }
            have Hcast_zz_back :
                forall (z zp : 'I_nz) (a : 'I_na) (b : 'I_nb),
                cast_ord (esym Hzz_dim)
                  (mxtens_index
                    (z, mxtens_index (mxtens_index (zp, a), b))) =
                mxtens_index (mxtens_index (mxtens_index (z, zp), a), b).
            {
              move=> z zp a b; apply/val_inj=> /=.
              by rewrite !mulnDl !mulnA !addnA.
            }
            have Hraw_rhoZZ :
                forall (z1 z2 : 'I_nz) (zp1 zp2 : 'I_nz)
                  (a1 a2 : 'I_na) (b1 b2 : 'I_nb),
                \sum_(c0 : 'I_nc)
                  rhoZCZpAB
                    (mxtens_index
                      (mxtens_index (z1, c0),
                       mxtens_index (mxtens_index (zp1, a1), b1)))
                    (mxtens_index
                      (mxtens_index (z2, c0),
                       mxtens_index (mxtens_index (zp2, a2), b2))) =
                rhoZZpAB
                  (mxtens_index (z1, mxtens_index (mxtens_index (zp1, a1), b1)))
                  (mxtens_index (z2, mxtens_index (mxtens_index (zp2, a2), b2))).
            {
              move=> z1 z2 zp1 zp2 a1 a2 b1 b2.
              rewrite /rhoZZpAB /castmx_sq castmxE /= /rho_ZZpAB /rhoZZ.
              rewrite ptrace2E1 ptrace1E.
              apply: eq_bigr=> c0 _.
              by rewrite /rhoZCZpAB /rho_ZC_ZpAB !mxE !mxtens_indexK /rhoZZ
                /rho_ZZpABC Hcast_zz_back Hcast_zz_back.
            }
            apply/matrixP=> i j.
            case: (mxtens_indexP i)=> izza ibrR.
            case: (mxtens_indexP izza)=> izz ia.
            case: (mxtens_indexP izz)=> iz izp.
            case: (mxtens_indexP ibrR)=> ib ir.
            case: (mxtens_indexP j)=> jzza jbrR.
            case: (mxtens_indexP jzza)=> jzz ja.
            case: (mxtens_indexP jzz)=> jz jzp.
            case: (mxtens_indexP jbrR)=> jb jr.
            rewrite /rhoZZpABR3_ref /rhoZpA_BR_ref
              /rhoZZpAB3_noR /castmx_sq !castmxE.
            rewrite Hcast_BR2 Hcast_BR2 Hcast_tauZE Hcast_tauZE.
            rewrite /rhoZpABR_ref.
            have HrhoAC := rho_AC_mxE rhoZC_big iz jz
              (mxtens_index (mxtens_index (mxtens_index (izp, ia), ib), ir))
              (mxtens_index (mxtens_index (mxtens_index (jzp, ja), jb), jr)).
            rewrite /rho_AC_mx in HrhoAC.
            rewrite /ptrace2 in HrhoAC.
            rewrite castmxE in HrhoAC.
            rewrite HrhoAC.
            under eq_bigr=> c0 _ do
              rewrite /rhoZC_big /rhoZC_big0 /castmx_sq castmxE /=
                Hcast_big2 Hcast_big2 tensmxE.
            rewrite -mulr_suml Hraw_rhoZZ.
            by rewrite !Hcast_R !tensmxE !castmxE /= !Hcast_zz2.
          }
          have HrhoX_from_W :
              rhoX = ptraceXA (W *m rhoZZpAB3_noR *m W^*t).
          {
            pose rhoZZpAB3 : 'M[C]_(((nz * nz) * na) * nb) :=
              castmx_sq (esym Hzz_dim) rhoZZpAB.
            change (rhoX = ptraceXA (W *m rhoZZpAB3 *m W^*t)).
          have HrhoZZpAB3_raw :
              rhoZZpAB3 = rho_ZZpAB N rhoABC.
          {
            by rewrite /rhoZZpAB3 /rhoZZpAB /castmx_sq castmxK.
          }
          have Hwv_full :
              (W *t (1%:M : 'M[C]_nc)) *m
                rho_ZZpABC N rhoABC *m
                (W^*t *t (1%:M : 'M[C]_nc)) =
              rho_XXpABC M rhoABC.
          {
            pose UIC : 'M[C]_(((nx * nx) * na) * nb * nc,
                              na * nb * nc) :=
              stinespring_U2 M *t (1%:M : 'M[C]_nb) *t
                (1%:M : 'M[C]_nc).
            pose VIC : 'M[C]_(((nz * nz) * na) * nb * nc,
                              na * nb * nc) :=
              stinespring_U2 N *t (1%:M : 'M[C]_nb) *t
                (1%:M : 'M[C]_nc).
            pose WIC : 'M[C]_(((nx * nx) * na) * nb * nc,
                              ((nz * nz) * na) * nb * nc) :=
              W *t (1%:M : 'M[C]_nc).
            have HWV : WIC *m VIC = UIC.
            {
              rewrite /WIC /W /W0 /partial_iso_W /UIC /VIC.
              by rewrite !mxtens.tensmx_mul !mulmx1 -!mulmxA HN_iso !mulmx1.
            }
            rewrite /rho_ZZpABC /rho_XXpABC -/UIC -/VIC.
            have Hright :
                VIC^*t *m (W^*t *t (1%:M : 'M[C]_nc)) = UIC^*t.
            {
              have HWadj :
                  W^*t *t (1%:M : 'M[C]_nc) =
                  WIC^*t
                by rewrite /WIC [RHS]adjmx_tens adjmx1.
              by rewrite HWadj -adjmxM HWV.
            }
            transitivity
              ((WIC *m VIC) *m rhoABC *m
                (VIC^*t *m (W^*t *t (1%:M : 'M[C]_nc)))).
            {
              by rewrite /WIC !mulmxA.
            }
            by rewrite HWV Hright.
          }
          have Hwv_trace :
              W *m rhoZZpAB3 *m W^*t =
              ptrace2 (rho_XXpABC M rhoABC).
          {
            have ptrace2_conj_rect :
                forall m m' n (B : 'M[C]_(m, m')) (A : 'M[C]_(m' * n)),
                ptrace2 ((B *t (1%:M : 'M[C]_n)) *m A *m
                  (B^*t *t (1%:M : 'M[C]_n))) =
                B *m ptrace2 A *m B^*t.
            {
              move=> m m' n B A.
              have ptrace2E' : forall s t (A0 : 'M[C]_(s * t)) r1 r2,
                  (ptrace2 A0) r1 r2 =
                  \sum_(k0 : 'I_t) A0 (mxtens_index (r1, k0))
                                         (mxtens_index (r2, k0)).
              {
                move=> s t A0 r1 r2; rewrite ptrace2E1 ptrace1E.
                by apply: eq_bigr => k0 _; rewrite mxE !mxtens_indexK.
              }
              have delta_mid : forall (T : finType) (j : T)
                  (K : C) (F : T -> C),
                  \sum_i K * ((j == i)%:R : C) * F i = K * F j.
              {
                move=> T j K F.
                rewrite (bigD1 j) //= eqxx mulr1.
                rewrite [X in _ + X]big1 ?addr0 //.
                by move=> i /negPf Hi; rewrite eq_sym Hi mulr0 mul0r.
              }
              have delta_right_scale : forall (T : finType) (j : T)
                  (F : T -> C) (K : C),
                  \sum_i F i * (K * ((i == j)%:R : C)) = F j * K.
              {
                move=> T j F K.
                rewrite (bigD1 j) //= eqxx mulr1.
                rewrite [X in _ + X]big1 ?addr0 //.
                by move=> i /negPf Hi; rewrite Hi !mulr0.
              }
              apply/matrixP=> i j.
              pose Tsum :=
                \sum_(q : 'I_m') \sum_(p : 'I_m') \sum_(k : 'I_n)
                  B i p *
                  A (mxtens_index (p, k)) (mxtens_index (q, k)) *
                  (B j q)^*.
              have HL :
                  ptrace2 ((B *t (1%:M : 'M[C]_n)) *m A *m
                    (B^*t *t (1%:M : 'M[C]_n))) i j = Tsum.
              {
                rewrite /Tsum ptrace2E'.
                transitivity
                  (\sum_(k : 'I_n) \sum_(q : 'I_m') \sum_(p : 'I_m')
                    B i p *
                    A (mxtens_index (p, k)) (mxtens_index (q, k)) *
                    (B j q)^*).
                {
                  apply: eq_bigr=> k _.
                  rewrite mxE.
                  rewrite (reindex_mxtens_index (fun r =>
                    ((B *t (1%:M : 'M[C]_n) *m A)
                       (mxtens_index (i, k)) r) *
                    (B^*t *t (1%:M : 'M[C]_n)) r
                      (mxtens_index (j, k)))).
                  rewrite pair_bigV /=.
                  apply: eq_bigr=> q _.
                  transitivity
                    (\sum_(l : 'I_n)
                      (\sum_(p : 'I_m')
                        B i p *
                        A (mxtens_index (p, k)) (mxtens_index (q, l))) *
                      ((B j q)^* * ((l == k)%:R : C))).
                  {
                    apply: eq_bigr=> l _.
                    rewrite [X in X * _]mxE.
                    rewrite (reindex_mxtens_index (fun s =>
                      (B *t (1%:M : 'M[C]_n)) (mxtens_index (i, k)) s *
                      A s (mxtens_index (q, l)))).
                    rewrite pair_bigV /=.
                    under eq_bigr=> p _ do
                      under eq_bigr=> l2 _ do
                        rewrite !tensmxE !mxE.
                    under eq_bigr=> p _ do rewrite delta_mid.
                    by rewrite adjmxE tensmxE !mxE.
                  }
                  rewrite delta_right_scale.
                  by rewrite mulr_suml.
                }
                rewrite exchange_big /=.
                apply: eq_bigr=> q _.
                by rewrite exchange_big.
              }
              have HR :
                  (B *m ptrace2 A *m B^*t) i j = Tsum.
              {
                rewrite /Tsum mxE.
                under [LHS]eq_bigr=> q _ do rewrite [X in X * _]mxE.
                under [LHS]eq_bigr=> q _ do rewrite mulr_suml.
                under [LHS]eq_bigr=> q _ do
                  under eq_bigr=> p _ do rewrite ptrace2E'.
                under [LHS]eq_bigr=> q _ do
                  under eq_bigr=> p _ do rewrite mulr_sumr.
                under [LHS]eq_bigr=> q _ do
                  under eq_bigr=> p _ do rewrite mulr_suml.
                under [LHS]eq_bigr=> q _ do
                  under eq_bigr=> p _ do
                    under eq_bigr=> k _ do rewrite adjmxE.
                under [LHS]eq_bigr=> q _ do
                  under eq_bigr=> p _ do
                    under eq_bigr=> k _ do rewrite !mxE.
                by [].
              }
              by rewrite HL HR.
            }
            rewrite HrhoZZpAB3_raw -Hwv_full /rho_ZZpAB.
            by rewrite ptrace2_conj_rect.
          }
          have HrhoXX_marginal :
              ptraceXA (ptrace2 (rho_XXpABC M rhoABC)) = rhoX.
          {
            have HrhoXX_entry :
                forall (xl xr : 'I_nx) (xpl xpr : 'I_nx)
                       (al ar : 'I_na) (bl br : 'I_nb) (cl cr : 'I_nc),
                rho_XXpABC M rhoABC
                  (mxtens_index (mxtens_index
                    (mxtens_index (mxtens_index (xl, xpl), al), bl), cl))
                  (mxtens_index (mxtens_index
                    (mxtens_index (mxtens_index (xr, xpr), ar), br), cr)) =
                ((xl == xpl)%:R : C) * ((xr == xpr)%:R : C) *
                \sum_(a0 : 'I_na) \sum_(a1 : 'I_na)
                  sqrtmx (M xl) al a0 *
                  rhoABC (mxtens_index (mxtens_index (a0, bl), cl))
                         (mxtens_index (mxtens_index (a1, br), cr)) *
                  (sqrtmx (M xr) ar a1)^*.
            {
              move=> xl xr xpl xpr al ar bl br cl cr.
              pose Ulift : 'M[C]_(((nx * nx) * na) * nb * nc,
                                  na * nb * nc) :=
                (stinespring_U2 M *t (1%:M : 'M[C]_nb) *t
                  (1%:M : 'M[C]_nc)).
              have HU_entry :
                  forall (x0 xp0 : 'I_nx) (a0 a1 : 'I_na)
                         (b0 b1 : 'I_nb) (cc0 cc1 : 'I_nc),
                  Ulift
                    (mxtens_index (mxtens_index
                      (mxtens_index (mxtens_index (x0, xp0), a0), b0), cc0))
                    (mxtens_index (mxtens_index (a1, b1), cc1)) =
                  ((x0 == xp0)%:R : C) * sqrtmx (M x0) a0 a1 *
                  ((b0 == b1)%:R : C) * ((cc0 == cc1)%:R : C).
              {
                move=> x0 xp0 a0 a1 b0 b1 cc0 cc1.
                rewrite /Ulift !tensmxE /stinespring_U2 !mxE
                  !mxtens_indexK /=.
                by [].
              }
              have Hraw_expand :
                  rho_XXpABC M rhoABC
                    (mxtens_index (mxtens_index
                      (mxtens_index (mxtens_index (xl, xpl), al), bl), cl))
                    (mxtens_index (mxtens_index
                      (mxtens_index (mxtens_index (xr, xpr), ar), br), cr)) =
                  \sum_(a1 : 'I_na) \sum_(b1 : 'I_nb) \sum_(c1 : 'I_nc)
                    (\sum_(a0 : 'I_na) \sum_(b0 : 'I_nb) \sum_(cc0 : 'I_nc)
                      (((xl == xpl)%:R : C) * sqrtmx (M xl) al a0 *
                       ((bl == b0)%:R : C) * ((cl == cc0)%:R : C)) *
                      rhoABC (mxtens_index (mxtens_index (a0, b0), cc0))
                             (mxtens_index (mxtens_index (a1, b1), c1))) *
                    ((((xr == xpr)%:R : C) * sqrtmx (M xr) ar a1 *
                      ((br == b1)%:R : C) * ((cr == c1)%:R : C))^*).
              {
                rewrite /rho_XXpABC -/Ulift.
                rewrite mxE !mxtens_index_pairV /=.
                apply: eq_bigr => a1 _.
                apply: eq_bigr => b1 _.
                apply: eq_bigr => c1 _.
                rewrite [X in X * _]mxE !mxtens_index_pairV /=.
                under eq_bigr => a0 _ do
                  under eq_bigr => b0 _ do
                    under eq_bigr => cc0 _ do rewrite HU_entry.
                by rewrite mxE_adj HU_entry.
              }
              rewrite Hraw_expand.
              have delta_collapseR : forall (T : finType) (f : T -> C) (j : T),
                  \sum_i f i * ((j == i)%:R : C) = f j.
              {
                move=> T f j.
                rewrite (bigD1 j) //= eqxx mulr1.
                rewrite [X in _ + X]big1 ?addr0 //.
                by move=> i /negPf Hi; rewrite eq_sym Hi mulr0.
              }
              have delta_collapse_mid : forall (T : finType) (g h : T -> C)
                  (j : T),
                  \sum_i g i * ((j == i)%:R : C) * h i = g j * h j.
              {
                move=> T f g j.
                rewrite (bigD1 j) //= eqxx mulr1.
                rewrite [X in _ + X]big1 ?addr0 //.
                by move=> i /negPf Hi; rewrite eq_sym Hi mulr0 mul0r.
              }
              case Hxl: (xl == xpl); last first.
              {
                rewrite /= ?mul0r ?mulr0.
                apply: big1 => a1 _; apply: big1 => b1 _.
                apply: big1 => c1 _.
                rewrite big1 ?mul0r //.
                move=> a0 _; apply: big1 => b0 _; apply: big1 => cc0 _.
                by rewrite /= !mul0r.
              }
              case Hxr: (xr == xpr); last first.
              {
                rewrite /= [X in _ = X * _]mulr0 [RHS]mul0r.
                apply: big1 => a1 _; apply: big1 => b1 _.
                apply: big1 => c1 _.
                by rewrite !mul0r rmorph0 mulr0.
              }
              rewrite /= !mul1r.
              under eq_bigr => a1 _ do
                under eq_bigr => b1 _ do
                  under eq_bigr => c1 _ do
                    rewrite !rmorphM /= !conjC_nat.
              under eq_bigr => a1 _ do
                under eq_bigr => b1 _ do
                  under eq_bigr => c1 _ do rewrite ?mulrA.
              under eq_bigr => a1 _ do
                under eq_bigr => b1 _ do rewrite delta_collapseR.
              under eq_bigr => a1 _ do rewrite delta_collapseR.
              under eq_bigr => a1 _ do
                under eq_bigr => a0 _ do
                  under eq_bigr => b0 _ do
                    under eq_bigr => cc0 _ do rewrite ?mulrA.
              under eq_bigr => a1 _ do
                under eq_bigr => a0 _ do
                  under eq_bigr => b0 _ do rewrite delta_collapse_mid.
              under eq_bigr => a1 _ do
                under eq_bigr => a0 _ do rewrite delta_collapse_mid.
              rewrite ?mulr0 ?subr0.
              under eq_bigr => a1 _ do
                under eq_bigr => a0 _ do rewrite ?mul1r ?mulr1.
              under eq_bigr => a1 _ do rewrite mulr1 mulr_suml.
              rewrite exchange_big /=.
              by apply: eq_bigr => a0 _; apply: eq_bigr => a1 _;
                rewrite ?mulrA.
            }
            have ptrace2E' : forall s t (A0 : 'M[C]_(s * t)) r1 r2,
                (ptrace2 A0) r1 r2 =
                \sum_(k0 : 'I_t) A0 (mxtens_index (r1, k0))
                                       (mxtens_index (r2, k0)).
            {
              move=> s t A0 r1 r2; rewrite ptrace2E1 ptrace1E.
              by apply: eq_bigr => k0 _; rewrite mxE !mxtens_indexK.
            }
            have ptraceXAE :
                forall (rho' : 'M[C]_(nx * nx * na * nb))
                  (ix0 : 'I_nx) (ib : 'I_nb)
                  (jx : 'I_nx) (jb : 'I_nb),
                ptraceXA rho' (mxtens_index (ix0, ib))
                  (mxtens_index (jx, jb)) =
                \sum_(x2 : 'I_nx) \sum_(a0 : 'I_na)
                  rho'
                    (mxtens_index (mxtens_index (mxtens_index (ix0, x2), a0), ib))
                    (mxtens_index (mxtens_index (mxtens_index (jx, x2), a0), jb)).
            {
              move=> rho' ix0 ib jx jb.
              rewrite /ptraceXA /=.
              rewrite mxE !mxtens_indexK /=.
              rewrite ptrace2E1 ptrace1E mxtens_index_pairV.
              apply: eq_bigr=> x2 _.
              apply: eq_bigr=> a0 _.
              rewrite mxE !mxtens_indexK /= /castmx_sq castmxE /=.
              have Hcast_a4 : forall (bb : 'I_nb)
                  (xx1 xx2 : 'I_nx) (aa : 'I_na),
                  cast_ord (esym HptraceXA_dim)
                    (mxtens_index (mxtens_index (bb, xx1),
                      mxtens_index (xx2, aa))) =
                  mxtens_index (bb, mxtens_index
                    (mxtens_index (xx1, xx2), aa)).
              {
                move=> bb xx1 xx2 aa.
                apply/val_inj=> /=.
                by rewrite !mulnDl !mulnA !addnA.
              }
              by rewrite !Hcast_a4 mxE !mxtens_indexK.
            }
            have Hlhs_entry :
                forall (xl xr : 'I_nx) (bl br : 'I_nb),
                ptraceXA (ptrace2 (rho_XXpABC M rhoABC))
                  (mxtens_index (xl, bl)) (mxtens_index (xr, br)) =
                \sum_(x : 'I_nx) \sum_(a : 'I_na) \sum_(c : 'I_nc)
                  ((xl == x)%:R : C) * ((xr == x)%:R : C) *
                  \sum_(a0 : 'I_na) \sum_(a1 : 'I_na)
                    sqrtmx (M xl) a a0 *
                    rhoABC (mxtens_index (mxtens_index (a0, bl), c))
                           (mxtens_index (mxtens_index (a1, br), c)) *
                    (sqrtmx (M xr) a a1)^*.
            {
              move=> xl xr bl br.
              rewrite ptraceXAE.
              apply: eq_bigr=> x _.
              apply: eq_bigr=> a _.
              rewrite ptrace2E'.
              apply: eq_bigr=> c _.
              by rewrite HrhoXX_entry.
            }
            have HrhoX_entry :
                forall (xl xr : 'I_nx) (bl br : 'I_nb),
                rhoX (mxtens_index (xl, bl)) (mxtens_index (xr, br)) =
                \sum_(x : 'I_nx) \sum_(a : 'I_na) \sum_(c : 'I_nc)
                  ((xl == x)%:R : C) * ((xr == x)%:R : C) *
                  \sum_(a0 : 'I_na) \sum_(a1 : 'I_na)
                    sqrtmx (M xl) a a0 *
                    rhoABC (mxtens_index (mxtens_index (a0, bl), c))
                           (mxtens_index (mxtens_index (a1, br), c)) *
                    (sqrtmx (M xr) a a1)^*.
            {
              move=> xl xr bl br.
              have Hsandwich_entry : forall x : 'I_nx,
                  ptrace1
                    (ptrace2
                      ((sqrtmx (M x) *t (1%:M : 'M[C]_nb) *t
                          (1%:M : 'M[C]_nc)) *m rhoABC *m
                       (sqrtmx (M x) *t (1%:M : 'M[C]_nb) *t
                          (1%:M : 'M[C]_nc)))) bl br =
                  \sum_(a : 'I_na) \sum_(c : 'I_nc)
                  \sum_(a0 : 'I_na) \sum_(a1 : 'I_na)
                    sqrtmx (M x) a a0 *
                    rhoABC (mxtens_index (mxtens_index (a0, bl), c))
                           (mxtens_index (mxtens_index (a1, br), c)) *
                    (sqrtmx (M x) a a1)^*.
              {
                move=> x.
                pose Kx : 'M[C]_(na * nb * nc) :=
                  sqrtmx (M x) *t (1%:M : 'M[C]_nb) *t
                    (1%:M : 'M[C]_nc).
                pose Ulift : 'M[C]_(((nx * nx) * na) * nb * nc,
                                    na * nb * nc) :=
                  stinespring_U2 M *t (1%:M : 'M[C]_nb) *t
                    (1%:M : 'M[C]_nc).
                have HKx_herm : Kx^*t = Kx.
                {
                  rewrite /Kx !adjmx_tens !adjmx1.
                  have HMx : M x \is psdmx by exact: is_povm_mx_psd HM.
                  have /hermmxP Hsqrt := sqrtmx_herm (psdmx_herm HMx).
                  by rewrite -Hsqrt.
                }
                have HU_block :
                    forall (aa aa' : 'I_na) (bb bb' : 'I_nb)
                           (cc cc' : 'I_nc),
                    Ulift
                      (mxtens_index (mxtens_index
                        (mxtens_index (mxtens_index (x, x), aa), bb), cc))
                      (mxtens_index (mxtens_index (aa', bb'), cc')) =
                    Kx (mxtens_index (mxtens_index (aa, bb), cc))
                       (mxtens_index (mxtens_index (aa', bb'), cc')).
                {
                  move=> aa aa' bb bb' cc cc'.
                  rewrite /Ulift /Kx !tensmxE /stinespring_U2 !mxE
                    !mxtens_indexK /= eqxx.
                  by rewrite mul1r.
                }
                have Hblock_eq :
                    forall (aa aa' : 'I_na) (bb bb' : 'I_nb)
                           (cc cc' : 'I_nc),
                    (Kx *m rhoABC *m Kx)
                      (mxtens_index (mxtens_index (aa, bb), cc))
                      (mxtens_index (mxtens_index (aa', bb'), cc')) =
                    rho_XXpABC M rhoABC
                      (mxtens_index (mxtens_index
                        (mxtens_index (mxtens_index (x, x), aa), bb), cc))
                      (mxtens_index (mxtens_index
                        (mxtens_index (mxtens_index (x, x), aa'), bb'), cc')).
                {
                  move=> aa aa' bb bb' cc cc'.
                  have HKx_adj_form :
                      Kx *m rhoABC *m Kx =
                      Kx *m rhoABC *m Kx^*t
                    by rewrite HKx_herm.
                  rewrite HKx_adj_form /rho_XXpABC -/Ulift.
                  rewrite !mxE.
                  apply: eq_bigr=> r _.
                  case: (mxtens_indexP r)=> abr cr0.
                  case: (mxtens_indexP abr)=> ar0 br0.
                  rewrite [X in _ = X * _]mxE.
                  rewrite [X in X * _ = _]mxE.
                  have Hsum :
                      \sum_j
                        Kx (mxtens_index (mxtens_index (aa, bb), cc)) j *
                        rhoABC j (mxtens_index (mxtens_index (ar0, br0), cr0)) =
                      \sum_j
                        Ulift
                          (mxtens_index (mxtens_index
                            (mxtens_index (mxtens_index (x, x), aa), bb), cc))
                          j *
                        rhoABC j (mxtens_index (mxtens_index (ar0, br0), cr0)).
                  {
                    apply: eq_bigr=> s _.
                    case: (mxtens_indexP s)=> abs cs0.
                    case: (mxtens_indexP abs)=> as0 bs0.
                    by rewrite HU_block.
                  }
                  rewrite Hsum.
                  rewrite !mxE_adj.
                  congr (_ * _).
                  by rewrite HU_block.
                }
                rewrite -/Kx.
                rewrite ptrace1E.
                apply: eq_bigr=> a _.
                rewrite ptrace2E'.
                apply: eq_bigr=> c _.
                by rewrite Hblock_eq HrhoXX_entry !eqxx /= !mul1r.
              }
              rewrite /rhoX /rho_XB summxE.
              apply: eq_bigr=> x _.
              rewrite tensmxE !mxE Hsandwich_entry.
              case Hxl: (xl == x); case Hxr: (xr == x); rewrite /=.
              - move/eqP: Hxl=> ->.
                move/eqP: Hxr=> ->.
                rewrite mul1r.
                under [RHS]eq_bigr=> a _ do
                  under eq_bigr=> c _ do rewrite !mul1r.
                by [].
              - rewrite mul0r.
                by rewrite big1 // => a _; rewrite big1 // => c _;
                  rewrite mulr0 mul0r.
              - rewrite mul0r.
                by rewrite big1 // => a _; rewrite big1 // => c _;
                  rewrite ?mul0r ?mulr0.
              - rewrite mul0r.
                by rewrite big1 // => a _; rewrite big1 // => c _;
                  rewrite ?mul0r ?mulr0.
            }
            apply/matrix_tenP=> xl bl xr br.
            by rewrite Hlhs_entry HrhoX_entry.
          }
          by rewrite Hwv_trace HrhoXX_marginal.
        }
          have HrhoXB_full_ref_factor :
              rhoXB_full_ref =
              ptraceXA (W *m rhoZZpAB3_noR *m W^*t) *t etaR.
          {
            (* The W-map acts as W ⊗ I_R and ptraceXA_BR traces only X'A, so
               the tensor factor etaR is unchanged. *)
            have HxxR_dim :
                ((((nx * nx) * na) * nb) * Rdim =
                 ((nx * nx) * na) * nBR)%N.
            { by rewrite /nBR !mulnA. }
            have HrhoXX_ref_tensor :
                rhoXXpABR_ref =
                castmx_sq HxxR_dim
                  ((W *m rhoZZpAB3_noR *m W^*t) *t etaR).
            {
              (* WBR = W ⊗ I_R and the lifted reference marginal is
                 rhoZZpAB3_noR ⊗ etaR, up to the local associativity casts. *)
              have HWBR_cast :
                  WBR =
                  castmx (HxxR_dim, HzzR_dim)
                    (W *t (1%:M : 'M[C]_Rdim)).
              {
                have Hcast_xxR : forall (xxa : 'I_((nx * nx) * na))
                    (b : 'I_nb) (r : 'I_Rdim),
                    cast_ord (esym HxxR_dim)
                      (mxtens_index (xxa, mxtens_index (b, r))) =
                    mxtens_index (mxtens_index (xxa, b), r).
                {
                  move=> xxa b r; apply/val_inj=> /=.
                  by rewrite /nBR !mulnDl !mulnA !addnA.
                }
                have Hcast_zzR : forall (zza : 'I_((nz * nz) * na))
                    (b : 'I_nb) (r : 'I_Rdim),
                    cast_ord (esym HzzR_dim)
                      (mxtens_index (zza, mxtens_index (b, r))) =
                    mxtens_index (mxtens_index (zza, b), r).
                {
                  move=> zza b r; apply/val_inj=> /=.
                  by rewrite /nBR !mulnDl !mulnA !addnA.
                }
                apply/matrixP=> i j.
                case: (mxtens_indexP i)=> xxa ibr.
                case: (mxtens_indexP ibr)=> ib ir.
                case: (mxtens_indexP j)=> zza jbr.
                case: (mxtens_indexP jbr)=> jb jr.
                rewrite /WBR /W /castmx_sq castmxE Hcast_xxR Hcast_zzR.
                rewrite !tensmxE !mxE.
                rewrite (inj_eq (can_inj (@mxtens_indexK _ _))) -pair_eqE /=.
                by case: (ib == jb); case: (ir == jr); rewrite ?mulr0 ?mulr1.
              }
              rewrite /rhoXXpABR_ref HrhoZZ_ref_tensor HWBR_cast.
              have HWBR_adj :
                  (castmx (HxxR_dim, HzzR_dim)
                    (W *t (1%:M : 'M[C]_Rdim)))^*t =
                  castmx (HzzR_dim, HxxR_dim)
                    ((W *t (1%:M : 'M[C]_Rdim))^*t).
              {
                exact: (@castmx_mx_mxT _ _ (@adjmx _) _ _ _ _
                  (HxxR_dim, HzzR_dim)
                  (W *t (1%:M : 'M[C]_Rdim))).
              }
              rewrite HWBR_adj.
              rewrite -[RHS]/(castmx (HxxR_dim, HxxR_dim)
                ((W *m rhoZZpAB3_noR *m W^*t) *t etaR)).
              rewrite -(castmx_mulmx3 HxxR_dim HzzR_dim
                (W *t (1%:M : 'M[C]_Rdim))
                (rhoZZpAB3_noR *t etaR)
                ((W *t (1%:M : 'M[C]_Rdim))^*t)).
              congr (castmx (HxxR_dim, HxxR_dim) _).
              by rewrite adjmx_tens adjmx1 !mxtens.tensmx_mul !mulmx1 !mul1mx.
            }
            have Hptrace_factor :
                rhoXB_full_ref =
                ptraceXA (W *m rhoZZpAB3_noR *m W^*t) *t etaR.
            {
              (* ptraceXA_BR discards only X' and A, so it commutes with the
                 untouched right tensor factor etaR. *)
              pose Y : 'M[C]_(((nx * nx) * na) * nb) :=
                W *m rhoZZpAB3_noR *m W^*t.
              pose xain_noR (x0 : 'I_nx) (b0 : 'I_nb)
                  (k : 'I_(nx * na)) :
                  'I_(((nx * nx) * na) * nb) :=
                mxtens_index
                  (mxtens_index
                    (mxtens_index (x0, (mxtens_unindex k).1),
                     (mxtens_unindex k).2), b0).
              pose xain_BR (x0 : 'I_nx) (br0 : 'I_nBR)
                  (k : 'I_(nx * na)) :
                  'I_(((nx * nx) * na) * nBR) :=
                mxtens_index
                  (mxtens_index
                    (mxtens_index (x0, (mxtens_unindex k).1),
                     (mxtens_unindex k).2), br0).
              have Hcast_XBR : forall (x0 : 'I_nx) (b0 : 'I_nb)
                  (rr : 'I_Rdim),
                  cast_ord (esym (mulnA nx nb Rdim))
                    (mxtens_index (mxtens_index (x0, b0), rr)) =
                  mxtens_index (x0, mxtens_index (b0, rr)).
              {
                move=> x0 b0 rr; apply/val_inj=> /=.
                by rewrite !mulnDl !mulnA !addnA.
              }
              have Hcast_xxR : forall (xxa : 'I_((nx * nx) * na))
                  (b0 : 'I_nb) (rr : 'I_Rdim),
                  cast_ord (esym HxxR_dim)
                    (mxtens_index (xxa, mxtens_index (b0, rr))) =
                  mxtens_index (mxtens_index (xxa, b0), rr).
              {
                move=> xxa b0 rr; apply/val_inj=> /=.
                by rewrite /nBR !mulnDl !mulnA !addnA.
              }
              have ptraceXA_BRE :
                  forall (rho' : 'M[C]_(((nx * nx) * na) * nBR))
                    (ix0 : 'I_nx) (ibr : 'I_nBR)
                    (jx : 'I_nx) (jbr : 'I_nBR),
                  ptraceXA_BR rho' (mxtens_index (ix0, ibr))
                    (mxtens_index (jx, jbr)) =
                  \sum_(k : 'I_(nx * na))
                    rho' (xain_BR ix0 ibr k) (xain_BR jx jbr k).
              {
                move=> rho' ix0 ibr jx jbr.
                rewrite /ptraceXA_BR /=.
                rewrite mxE !mxtens_indexK /=.
                rewrite ptrace2E1 ptrace1E.
                apply: eq_bigr=> k _.
                case: (mxtens_indexP k)=> x2 a0.
                rewrite mxE !mxtens_indexK /= /castmx_sq castmxE /=.
                have Hcast_a4 : forall (br : 'I_nBR)
                    (xx1 xx2 : 'I_nx) (aa : 'I_na),
                    cast_ord (esym HptraceXA_dim_BR)
                      (mxtens_index (mxtens_index (br, xx1),
                        mxtens_index (xx2, aa))) =
                    mxtens_index (br, mxtens_index
                      (mxtens_index (xx1, xx2), aa)).
                {
                  move=> br xx1 xx2 aa.
                  apply/val_inj=> /=.
                  by rewrite !mulnDl !mulnA !addnA.
                }
                by rewrite /xain_BR !mxtens_indexK !Hcast_a4 mxE !mxtens_indexK.
              }
              have ptraceXA_E :
                  forall (rho' : 'M[C]_(((nx * nx) * na) * nb))
                    (ix0 : 'I_nx) (ib : 'I_nb)
                    (jx : 'I_nx) (jb : 'I_nb),
                  ptraceXA rho' (mxtens_index (ix0, ib))
                    (mxtens_index (jx, jb)) =
                  \sum_(k : 'I_(nx * na))
                    rho' (xain_noR ix0 ib k) (xain_noR jx jb k).
              {
                move=> rho' ix0 ib jx jb.
                rewrite /ptraceXA /=.
                rewrite mxE !mxtens_indexK /=.
                rewrite ptrace2E1 ptrace1E.
                apply: eq_bigr=> k _.
                case: (mxtens_indexP k)=> x2 a0.
                rewrite mxE !mxtens_indexK /= /castmx_sq castmxE /=.
                have Hcast_a4 : forall (bb : 'I_nb)
                    (xx1 xx2 : 'I_nx) (aa : 'I_na),
                    cast_ord (esym HptraceXA_dim)
                      (mxtens_index (mxtens_index (bb, xx1),
                        mxtens_index (xx2, aa))) =
                    mxtens_index (bb, mxtens_index
                      (mxtens_index (xx1, xx2), aa)).
                {
                  move=> bb xx1 xx2 aa.
                  apply/val_inj=> /=.
                  by rewrite !mulnDl !mulnA !addnA.
                }
                by rewrite /xain_noR !mxtens_indexK !Hcast_a4 mxE !mxtens_indexK.
              }
              rewrite /rhoXB_full_ref /rhoXBR_ref HrhoXX_ref_tensor -/Y.
              apply/matrixP=> i j.
              case: (mxtens_indexP i)=> ixbr ir.
              case: (mxtens_indexP ixbr)=> ix ib.
              case: (mxtens_indexP j)=> jxbr jr.
              case: (mxtens_indexP jxbr)=> jx jb.
              rewrite /castmx_sq castmxE /= Hcast_XBR Hcast_XBR.
              rewrite ptraceXA_BRE.
              under eq_bigr=> k _ do
                rewrite /castmx_sq castmxE /= /xain_BR /xain_noR
                  Hcast_xxR Hcast_xxR tensmxE.
              rewrite -mulr_suml -ptraceXA_E.
              by rewrite tensmxE.
            }
            exact: Hptrace_factor.
          }
          by rewrite HrhoXB_full_ref_factor -HrhoX_from_W.
        }
        by rewrite /rhoXB_ref HrhoXB_full_ref ptrace_tensmx Heta_tr1 scale1r.
      }
      rewrite -HrhoXB_ref.
      apply: (le_trans Hpd_transport).
      exact: HtauZC_big_pd_sym.
    }
      have HtauXB_pos_smin : 0 < @complex.Re R (\tr tauXB).
      {
        have Heps_lt_X : eps < Num.sqrt (@complex.Re R (\tr rhoX))
          by rewrite HrhoX_tr_eq.
        pose gapXB := Num.sqrt (@complex.Re R (\tr rhoX)) - eps.
        have HgapXB_pos : 0 < gapXB by rewrite /gapXB subr_gt0.
        have Hsqrt_le0 :
            Num.sqrt (@complex.Re R (\tr rhoX)) <=
            Num.sqrt (@complex.Re R (\tr tauXB)) + pur_dist_mx tauXB rhoX.
        { rewrite /pur_dist_mx.
          exact: pur_dist_mx_trace_sqrt_bound Hnxnb_pos
            HrhoX_den HtauXB_den. }
        have Hsqrt_le :
            Num.sqrt (@complex.Re R (\tr rhoX)) <=
            Num.sqrt (@complex.Re R (\tr tauXB)) + eps.
        { apply: le_trans Hsqrt_le0 _.
          by rewrite lerD2l. }
        have HgapXB_le_sqrt :
            gapXB <= Num.sqrt (@complex.Re R (\tr tauXB)).
        { have Htmp :
              gapXB + eps <= Num.sqrt (@complex.Re R (\tr tauXB)) + eps
            by rewrite /gapXB subrK.
          by move: Htmp; rewrite lerD2r. }
        have Hsq_pos : 0 < (Num.sqrt (@complex.Re R (\tr tauXB))) ^+ 2.
        {
          have Hgap_sq_pos : 0 < gapXB ^+ 2
            by rewrite expr2; apply: mulr_gt0.
          have Hsq_le :
              gapXB ^+ 2 <=
              (Num.sqrt (@complex.Re R (\tr tauXB))) ^+ 2.
          { rewrite !expr2.
            have HgapXB_le_sqrt2 := HgapXB_le_sqrt.
            exact: ler_pM (ltW HgapXB_pos) (ltW HgapXB_pos)
              HgapXB_le_sqrt HgapXB_le_sqrt2. }
          exact: lt_le_trans Hgap_sq_pos Hsq_le.
        }
        have HtauXB_ge0 : 0 <= @complex.Re R (\tr tauXB).
        { have /= := psdmx_trace HtauXB_psd.
          by rewrite lecE /= => /andP []. }
        by rewrite (sqr_sqrtr HtauXB_ge0) in Hsq_pos.
      }
      pose Smin : set R :=
        [set w : R | exists tau0 : 'M[C]_(nx * nb),
          ((tau0 \is denmx) && (0 < @complex.Re R (\tr tau0))) &&
          (pur_dist_mx tau0 rhoX <= eps) /\ w = hmin_mx tau0]%classic.
      have HtauXB_feas : Smin (hmin_mx tauXB).
      {
        exists tauXB; split; last reflexivity.
        by rewrite HtauXB_den HtauXB_pos_smin HXB_pd.
      }
    have Hsmooth_min_ub : has_ubound Smin.
    {
      pose gapX : R := Num.sqrt (@complex.Re R (\tr rhoABC)) - eps.
      pose ubX : R := - log2 (gapX ^+ 2 / nx%:R).
        exists ubX.
        apply/ubP=> w [tau0 [Htau0_feas ->]].
        move: Htau0_feas => /andP[/andP[Htau0_den _] Htau0_pd].
        have /denmxP[Htau0_psd Htau0_trC] := Htau0_den.
        have Htau0_tr : @complex.Re R (\tr tau0) <= 1
          by move: Htau0_trC; rewrite lecE /= => /andP [_].
      have HgapX_pos : 0 < gapX by rewrite /gapX subr_gt0.
        have Hsqrt_le0 :
            Num.sqrt (@complex.Re R (\tr rhoX)) <=
            Num.sqrt (@complex.Re R (\tr tau0)) + pur_dist_mx tau0 rhoX.
          { rewrite /pur_dist_mx.
            exact: pur_dist_mx_trace_sqrt_bound Hnxnb_pos
              HrhoX_den Htau0_den. }
      have Hsqrt_le :
          Num.sqrt (@complex.Re R (\tr rhoABC))
            <= Num.sqrt (@complex.Re R (\tr tau0)) + eps.
      {
        have Hadd_le :
            Num.sqrt (@complex.Re R (\tr tau0)) + pur_dist_mx tau0 rhoX <=
            Num.sqrt (@complex.Re R (\tr tau0)) + eps
          by rewrite lerD2l.
        move: (le_trans Hsqrt_le0 Hadd_le).
        by rewrite HrhoX_tr_eq.
      }
      have Hgap_le_sqrt :
          gapX <= Num.sqrt (@complex.Re R (\tr tau0)).
      {
        have Htmp :
            gapX + eps <= Num.sqrt (@complex.Re R (\tr tau0)) + eps
          by rewrite /gapX subrK.
        by move: Htmp; rewrite lerD2r.
      }
      have Htrace_lb : gapX ^+ 2 <= @complex.Re R (\tr tau0).
      {
        have Hsq :
            gapX ^+ 2 <= (Num.sqrt (@complex.Re R (\tr tau0))) ^+ 2.
        { rewrite (ler_sqr (ltW HgapX_pos) (sqrtr_ge0 _)).
          exact: Hgap_le_sqrt. }
        have Htau0_sq :
            (Num.sqrt (@complex.Re R (\tr tau0))) ^+ 2 <=
            @complex.Re R (\tr tau0).
        { have Htau0_tr_ge0 : 0 <= @complex.Re R (\tr tau0).
          { have /= := psdmx_trace Htau0_psd.
            by rewrite lecE /= => /andP [_]. }
          by rewrite sqr_sqrtr. }
        exact: le_trans Hsq Htau0_sq.
      }
      have Hconst_pos : 0 < gapX ^+ 2 / nx%:R.
      { apply: divr_gt0; first by rewrite expr2; apply: mulr_gt0.
        by rewrite ltr0n. }
      have HRe_realM : forall (cc : R) (zz : C),
          @complex.Re R (cc%:C * zz) = cc * @complex.Re R zz.
      { move=> cc zz; case: zz => a b /=. by rewrite mul0r subr0. }
      have Hmin_trace_lb :
          gapX ^+ 2 / nx%:R <=
          inf [set v : R | exists sigma : 'M[C]_nb,
            sigma \is psdmx /\
            (1%:M *t sigma - tau0) \is psdmx /\
            v = @complex.Re R (\tr sigma)].
      {
        apply: lb_le_inf.
        - pose sigma0 : 'M[C]_nb :=
            (@complex.Re R (\tr tau0))%:C *: (1%:M : 'M[C]_nb).
          exists (@complex.Re R (\tr sigma0)).
          exists sigma0; split; last split.
          + rewrite /sigma0.
            apply: psdmxZ; last exact: psdmx1.
            have Htau0_tr_ge0 : 0 <= @complex.Re R (\tr tau0).
            { have /= := psdmx_trace Htau0_psd.
              by rewrite lecE /= => /andP [_]. }
            by rewrite -[0]/(0%:C) lecR.
          + have Htau0_le_trI : tau0 <= (\tr tau0)%:M
              := lemx_psd_ub Htau0_psd.
            have Htarget :
                (1%:M : 'M[C]_nx) *t sigma0 = (\tr tau0)%:M.
            {
              have Htr_ge0C : (0 : C) <= \tr tau0 := psdmx_trace Htau0_psd.
              have Htr_real : \tr tau0 \is Num.real := ger0_real Htr_ge0C.
              have Hreal :
                  \tr tau0 = (@complex.Re R (\tr tau0))%:C
                by rewrite RRe_real.
              apply/matrixP=> i j.
              case: (mxtens_indexP i)=> ix ib.
              case: (mxtens_indexP j)=> jx jb.
              rewrite /sigma0 tensmxE !mxE Hreal.
              rewrite (inj_eq (can_inj (@mxtens_indexK _ _))) -pair_eqE /=.
              by case: (ix == jx); case: (ib == jb);
                rewrite ?andbT ?andbF ?mul0r ?mulr0 ?mul1r ?mulr1.
            }
            move: Htau0_le_trI.
            by rewrite -Htarget le_lownerE.
          + by [].
        - move=> tval [sigma [Hsigma_psd [Hsigma_feas ->]]].
          have Hle_tau : tau0 <= (1%:M : 'M[C]_nx) *t sigma
            by move: Hsigma_feas; rewrite -le_lownerE.
          have Htr_leC := lemx_trace Hle_tau.
          have Hnx_real : (nx%:R : C) = ((nx%:R : R)%:C : C)
            by rewrite -(@rmorph_nat _ _ ((real_complex R) : {rmorphism _ -> _})).
          have HRe_tens :
              @complex.Re R (\tr ((1%:M : 'M[C]_nx) *t sigma)) =
              nx%:R * @complex.Re R (\tr sigma).
          { by rewrite mxtrace_tens mxtrace1 Hnx_real HRe_realM. }
          have Htr_leR :
              @complex.Re R (\tr tau0) <=
              nx%:R * @complex.Re R (\tr sigma).
          {
            move: Htr_leC; rewrite lecE /= => /andP[_ Hre].
            by rewrite HRe_tens in Hre.
          }
          rewrite ler_pdivrMr; last by rewrite ltr0n.
          rewrite mulrC.
          exact: le_trans Htrace_lb Htr_leR.
      }
      rewrite /ubX /hmin_mx.
      rewrite lerN2.
      exact: log2_le_pos Hconst_pos Hmin_trace_lb.
    }
    have Hhmin_smooth :
        hmin_mx tauXB <= smooth_hmin_mx eps rhoX.
    { rewrite /smooth_hmin_mx -/rhoX.
      change (hmin_mx tauXB <= sup Smin).
      have Hub : ubound Smin (sup Smin) := ub_le_sup Hsmooth_min_ub.
      by move/ubP: Hub; apply. }
    (* TeX Stage 1 max/min comparison: dualize the lifted pure
       ZC|Z'ABR witness, transport min-entropy through W := U V^dagger,
       and weaken the conditioning system from BR back to B. *)
    have Hzero :
        - log2 (overlap_mx M N) <= hmin_mx tauXB + hmax_mx tau.
    {
      have Hdual_tau :
          - hmin_mx tauZpABR <= hmax_mx tau.
      {
        (* TeX eqn:dual/eqn:mo1 on the lifted pure state
           tau_ZC(Z'ABR), with the auxiliary R kept in the purifying
           register.  Since the matrix max surface uses generalized
           fidelity, the proof only needs the direction from Tomamichel's
           labelled max value into `hmax_mx tau`. *)
        have Hdual_lift :
            exists hmax_lbl hmin_lbl : R,
              hmax_lbl = - hmin_lbl /\
              hmin_lbl = hmin_mx tauZpABR /\
              hmax_lbl <= hmax_mx tau.
        {
          (* TeX eqn:dual/eqn:mo1, proof-local form: build the labelled
             Z|C|Z'ABR version of tau_ZC(Z'ABR), apply Tomamichel pure
             duality, bridge hmin exactly, and bridge hmax one-way via
             fidelity <= gfidelity. *)
          have HEbig_pos : (0 < Ebig)%N by rewrite /Ebig muln_gt0 Henv0_pos HRdim_pos.
          pose TZ : ihbFinType :=
            FinInhabited.Pack (FinInhabited.Class (Choice.on 'I_nz)
              (Countable.on 'I_nz) (Finite.on 'I_nz)
              (isPointed.Build 'I_nz (Ordinal Hnz_pos))).
          pose TC : ihbFinType :=
            FinInhabited.Pack (FinInhabited.Class (Choice.on 'I_nc)
              (Countable.on 'I_nc) (Finite.on 'I_nc)
              (isPointed.Build 'I_nc (Ordinal Hnc_pos))).
          pose TE : ihbFinType :=
            FinInhabited.Pack (FinInhabited.Class (Choice.on 'I_Ebig)
              (Countable.on 'I_Ebig) (Finite.on 'I_Ebig)
              (isPointed.Build 'I_Ebig (Ordinal HEbig_pos))).
          have HdimZ : dim ('Hs TZ) = nz by rewrite /TZ -(@ihb_dim_cast R _) card_ord.
          have HdimC : dim ('Hs TC) = nc by rewrite /TC -(@ihb_dim_cast R _) card_ord.
          have HdimE : dim ('Hs TE) = Ebig
            by rewrite /TE -(@ihb_dim_cast R _) card_ord.
          have Hcpp_pos : (0 < Ebig * nz * nc)%N.
          { have Hleft_pos : (0 < Ebig * nz)%N
              by rewrite muln_gt0 HEbig_pos Hnz_pos.
            by rewrite muln_gt0 Hleft_pos Hnc_pos. }
          pose TCpp : ihbFinType :=
            FinInhabited.Pack (FinInhabited.Class
              (Choice.on 'I_(Ebig * nz * nc))
              (Countable.on 'I_(Ebig * nz * nc))
              (Finite.on 'I_(Ebig * nz * nc))
              (isPointed.Build 'I_(Ebig * nz * nc)
                (Ordinal Hcpp_pos))).
          have HdimCpp : dim ('Hs TCpp) = Ebig * nz * nc
            by rewrite /TCpp -(@ihb_dim_cast R _) card_ord.
          pose Zlbl : 'I_5 := ord0.
          pose Clbl : 'I_5 := Ordinal (isT : (1 < 5)%N).
          pose Elbl : 'I_5 := Ordinal (isT : (2 < 5)%N).
          pose Cplbl : 'I_5 := Ordinal (isT : (3 < 5)%N).
          pose Cpplbl : 'I_5 := Ordinal (isT : (4 < 5)%N).
          pose HL (i : 'I_5) : chsType :=
            if i == Zlbl then 'Hs TZ else
            if i == Clbl then 'Hs TC else
            if i == Elbl then 'Hs TE else
            if i == Cplbl then 'Hs TZ else 'Hs TCpp.
          have HHLZ : dim (HL Zlbl) = nz by rewrite /HL /Zlbl eqxx HdimZ.
          have HHLC : dim (HL Clbl) = nc by rewrite /HL /Zlbl /Clbl /= HdimC.
          have HHLE : dim (HL Elbl) = Ebig
            by rewrite /HL /Zlbl /Clbl /Elbl /= HdimE.
          have HHLCp : dim (HL Cplbl) = nz
            by rewrite /HL /Zlbl /Clbl /Elbl /Cplbl /= HdimZ.
          have HHLCpp : dim (HL Cpplbl) = Ebig * nz * nc
            by rewrite /HL /Zlbl /Clbl /Elbl /Cplbl /Cpplbl /= HdimCpp.
          have disZC : [disjoint [set Zlbl] & [set Clbl]].
          { by rewrite disjoint1X inE /Zlbl /Clbl. }
          have disZE : [disjoint [set Zlbl] & [set Elbl]].
          { by rewrite disjoint1X inE /Zlbl /Elbl. }
          have disCE : [disjoint [set Clbl] & [set Elbl]].
          { by rewrite disjoint1X inE /Clbl /Elbl. }
          have disZCp : [disjoint [set Zlbl] & [set Cplbl]].
          { by rewrite disjoint1X inE /Zlbl /Cplbl. }
          have disZCpp : [disjoint [set Zlbl] & [set Cpplbl]].
          { by rewrite disjoint1X inE /Zlbl /Cpplbl. }
          have disCCp : [disjoint [set Clbl] & [set Cplbl]].
          { by rewrite disjoint1X inE /Clbl /Cplbl. }
          have disCCpp : [disjoint [set Clbl] & [set Cpplbl]].
          { by rewrite disjoint1X inE /Clbl /Cpplbl. }
          have disECp : [disjoint [set Elbl] & [set Cplbl]].
          { by rewrite disjoint1X inE /Elbl /Cplbl. }
            have disECpp : [disjoint [set Elbl] & [set Cpplbl]].
            { by rewrite disjoint1X inE /Elbl /Cpplbl. }
            have disCpCpp : [disjoint [set Cplbl] & [set Cpplbl]].
            { by rewrite disjoint1X inE /Cplbl /Cpplbl. }
            have HdimZ_set : dim 'H[HL]_[set Zlbl] = nz.
            { by rewrite -(dim_set1 HL Zlbl) HHLZ. }
            have HdimC_set : dim 'H[HL]_[set Clbl] = nc.
            { by rewrite -(dim_set1 HL Clbl) HHLC. }
            have HdimE_set : dim 'H[HL]_[set Elbl] = Ebig.
            { by rewrite -(dim_set1 HL Elbl) HHLE. }
            have HdimCp_set : dim 'H[HL]_[set Cplbl] = nz.
            { by rewrite -(dim_set1 HL Cplbl) HHLCp. }
            have HdimCpp_set : dim 'H[HL]_[set Cpplbl] = Ebig * nz * nc.
            { by rewrite -(dim_set1 HL Cpplbl) HHLCpp. }
            have HdimZ_Cp : dim 'H[HL]_[set Zlbl] = dim 'H[HL]_[set Cplbl].
            { by rewrite HdimZ_set HdimCp_set. }
            have HdimE_Cp_Cpp :
                (dim 'H[HL]_[set Elbl] * dim 'H[HL]_[set Cplbl] <=
                 dim 'H[HL]_[set Cpplbl])%N.
            { rewrite HdimE_set HdimCp_set HdimCpp_set.
              exact: leq_pmulr Hnc_pos. }
            have HdimC_Cpp :
                (dim 'H[HL]_[set Clbl] <= dim 'H[HL]_[set Cpplbl])%N.
            { rewrite HdimC_set HdimCpp_set.
              have Hprefix_pos : (0 < Ebig * nz)%N
                by rewrite muln_gt0 HEbig_pos Hnz_pos.
              exact: leq_pmull Hprefix_pos. }
          pose S_ZC := [set Zlbl] :|: [set Clbl].
          pose S_ZCE3 := S_ZC :|: [set Elbl].
          have disZC_E : [disjoint S_ZC & [set Elbl]]
            by rewrite /S_ZC disjointUX disZE disCE.
          have HdimZC_set :
              dim 'H[HL]_S_ZC =
              dim 'H[HL]_[set Zlbl] * dim 'H[HL]_[set Clbl].
          { by rewrite /S_ZC (tenv_dim disZC). }
          have HdimZCE_set :
              dim 'H[HL]_S_ZCE3 =
              (dim 'H[HL]_[set Zlbl] * dim 'H[HL]_[set Clbl]) *
                dim 'H[HL]_[set Elbl].
          {
            rewrite /S_ZCE3 (tenv_dim disZC_E).
            by rewrite HdimZC_set.
          }
          have HdimZCE_col :
              dim 'H[HL]_S_ZC * dim 'H[HL]_[set Elbl] =
              (dim 'H[HL]_[set Zlbl] * dim 'H[HL]_[set Clbl]) *
                dim 'H[HL]_[set Elbl].
          { by rewrite HdimZC_set. }
          have HdimZCE_raw :
              ((dim 'H[HL]_[set Zlbl] * dim 'H[HL]_[set Clbl]) *
                 dim 'H[HL]_[set Elbl] =
               (nz * nc) * Ebig)%N.
          {
            by rewrite -(dim_set1 HL Zlbl) -(dim_set1 HL Clbl)
              -(dim_set1 HL Elbl) HHLZ HHLC HHLE.
          }
          pose Q_ZC : 'M[C]_(dim 'H[HL]_[set Zlbl] *
                              dim 'H[HL]_[set Clbl]) :=
            castmx (tenv_dim disZC, erefl)
              (@tenv_mxU R _ HL [set Zlbl] [set Clbl]).
          pose U_ZCE := @tenv_mxU R _ HL S_ZC [set Elbl].
          pose I_E : 'M[C]_(dim 'H[HL]_[set Elbl]) := 1%:M.
          have HQ_ZC_t :
              Q_ZC^*t =
              castmx (erefl, tenv_dim disZC)
                (@tenv_mxU R _ HL [set Zlbl] [set Clbl])^*t.
          {
            rewrite /Q_ZC.
            exact: (@castmx_mx_mxT _ _ (@adjmx _) _ _ _ _
              (tenv_dim disZC, erefl)
              (@tenv_mxU R _ HL [set Zlbl] [set Clbl])).
          }
          have HQtQ_ZC : Q_ZC^*t *m Q_ZC = 1%:M.
          {
            rewrite /Q_ZC HQ_ZC_t mcextra.castmx_mul.
            have HU :
                (@tenv_mxU R _ HL [set Zlbl] [set Clbl])^*t *m
                (@tenv_mxU R _ HL [set Zlbl] [set Clbl]) = 1%:M.
            {
              have := unitarymxK
                (@tenv_mxU_adj_unitarymx R _ HL [set Zlbl] [set Clbl] disZC).
              by rewrite adjmxK.
            }
            rewrite HU.
            by case: _ / (tenv_dim disZC); rewrite castmx_id.
          }
          have HQ_ZC_unit : Q_ZC \is unitarymx by apply/unitarymxPV.
          have HQQt_ZC : Q_ZC *m Q_ZC^*t = 1%:M := unitarymxK HQ_ZC_unit.
          have HQtQ_ZC_E :
              ((Q_ZC *t I_E)^*t *m (Q_ZC *t I_E)) = 1%:M.
          { by rewrite adjmx_tens adjmx1 tensmx_mul HQtQ_ZC mul1mx tensmx11. }
          have HQQt_ZC_E :
              (Q_ZC *t I_E) *m (Q_ZC *t I_E)^*t = 1%:M.
          { by rewrite adjmx_tens adjmx1 tensmx_mul HQQt_ZC mul1mx tensmx11. }
          have HQZC_E_adj : (Q_ZC *t I_E)^*t = Q_ZC^*t *t I_E.
          { by rewrite /I_E adjmx_tens adjmx1. }
          pose tau_raw_prod :
              'M[C]_((dim 'H[HL]_[set Zlbl] * dim 'H[HL]_[set Clbl]) *
                     dim 'H[HL]_[set Elbl]) :=
            castmx (esym HdimZCE_raw, esym HdimZCE_raw) tauZC_big.
          pose tau_inner_labelled :
              'M[C]_(dim 'H[HL]_S_ZC * dim 'H[HL]_[set Elbl]) :=
            castmx (esym HdimZCE_col, esym HdimZCE_col)
              (((Q_ZC *t I_E) *m tau_raw_prod *m (Q_ZC^*t *t I_E))).
          pose tau_prod_labelled : 'M[C]_(dim 'H[HL]_S_ZCE3) :=
            U_ZCE *m tau_inner_labelled *m U_ZCE^*t.
          pose tauL3 : 'F[HL]_S_ZCE3 := mx2h tau_prod_labelled.
          have HtauL3_psd : tauL3 \is psdlf.
          {
            rewrite qualifE /tauL3 mx2hK.
            have Hraw_psd : tau_raw_prod \is psdmx.
            {
              rewrite /tau_raw_prod -/(castmx_sq (esym HdimZCE_raw) tauZC_big).
              exact: castmx_sq_psdmx HtauZC_big_psd.
            }
            have Hinner_psd :
                ((Q_ZC *t I_E) *m tau_raw_prod *m (Q_ZC^*t *t I_E)) \is psdmx.
            {
              rewrite -HQZC_E_adj.
              exact: psdmx_bimap_closed_gen Hraw_psd.
            }
            have Hinner_label_psd : tau_inner_labelled \is psdmx.
            {
              rewrite /tau_inner_labelled
                -/(castmx_sq (esym HdimZCE_col)
                    ((Q_ZC *t I_E) *m tau_raw_prod *m (Q_ZC^*t *t I_E))).
              exact: castmx_sq_psdmx Hinner_psd.
            }
            rewrite /tau_prod_labelled.
            exact: psdmx_bimap_closed_gen Hinner_label_psd.
          }
          have HtauL3_tr : @complex.Re R (\Tr tauL3) <= 1.
          {
            rewrite /tauL3 /lftrace mx2hK.
            have HUtU_ZCE : U_ZCE^*t *m U_ZCE = 1%:M.
            {
              have := unitarymxK (@tenv_mxU_adj_unitarymx R _ HL S_ZC
                [set Elbl] disZC_E).
              by rewrite /U_ZCE adjmxK.
            }
            have Hraw_tr : \tr tau_raw_prod = \tr tauZC_big
              by rewrite /tau_raw_prod mxtrace_castmx_sq.
            have Hinner_label_tr :
                \tr tau_inner_labelled = \tr tau_raw_prod.
            {
              rewrite /tau_inner_labelled mxtrace_castmx_sq.
              rewrite -HQZC_E_adj.
              by rewrite mxtrace_mulC mulmxA HQtQ_ZC_E mul1mx.
            }
            rewrite /tau_prod_labelled mxtrace_mulC mulmxA HUtU_ZCE mul1mx.
            rewrite Hinner_label_tr Hraw_tr.
            have /denmxP[Htau_big_psd' Htau_big_tr] := HtauZC_big_den.
            have Htau_big_real := ger0_real (psdmx_trace Htau_big_psd').
            by move: Htau_big_tr; rewrite -(RRe_real Htau_big_real)
              -[1]/(1%:C) lecR.
          }
          have HtauL3_den : tauL3 \is denlf.
          { apply/denlfP; split=> //.
            have Hreal : (\Tr tauL3 : C) =
                         (@complex.Re R (\Tr tauL3))%:C
              by rewrite RRe_real // ger0_real // psdlf_trlf.
            by rewrite Hreal lecR. }
          have HtauL3_rank : \Rank tauL3 = 1%N.
          {
            rewrite /tauL3 /lfrank mx2hK.
            have HUtU_ZCE : U_ZCE^*t *m U_ZCE = 1%:M.
            {
              have := unitarymxK (@tenv_mxU_adj_unitarymx R _ HL S_ZC
                [set Elbl] disZC_E).
              by rewrite /U_ZCE adjmxK.
            }
            have Hrank_conj : forall m n (R0 : 'M[C]_(m, n)) (A0 : 'M[C]_n),
                (\rank (R0 *m A0 *m R0^*t) <= \rank A0)%N.
            { move=> m0 n0 R0 A0.
              exact: leq_trans (mxrankM_maxl _ _) (mxrankM_maxr _ _). }
            have Hrank_unit_conj : forall n (U A0 : 'M[C]_n),
                U^*t *m U = 1%:M -> U *m U^*t = 1%:M ->
                \rank (U *m A0 *m U^*t) = \rank A0.
            {
              move=> n0 U A0 HUtU HUU.
              apply/eqP; rewrite eqn_leq.
              apply/andP; split; first exact: Hrank_conj.
              have Hback :
                  U^*t *m (U *m A0 *m U^*t) *m (U^*t)^*t = A0.
              { by rewrite adjmxK -!mulmxA HUtU !mulmxA HUtU mul1mx mulmx1. }
              rewrite -[X in (\rank X <= _)%N]Hback.
              exact: Hrank_conj.
            }
            have Hrank_iso_conj : forall m n (U : 'M[C]_(m, n)) (A0 : 'M[C]_n),
                U^*t *m U = 1%:M ->
                \rank (U *m A0 *m U^*t) = \rank A0.
            {
              move=> m0 n0 U A0 HUtU.
              apply/eqP; rewrite eqn_leq.
              apply/andP; split; first exact: Hrank_conj.
              have Hback :
                  U^*t *m (U *m A0 *m U^*t) *m (U^*t)^*t = A0.
              { by rewrite adjmxK -!mulmxA HUtU !mulmxA HUtU mul1mx mulmx1. }
              rewrite -[X in (\rank X <= _)%N]Hback.
              exact: Hrank_conj.
            }
            have Hraw_rank : \rank tau_raw_prod = 1%N.
            { by rewrite /tau_raw_prod mxrank_cast HtauZC_big_rank. }
            have Hinner_rank :
                \rank ((Q_ZC *t I_E) *m tau_raw_prod *m
                       (Q_ZC^*t *t I_E)) = \rank tau_raw_prod.
            {
              rewrite -HQZC_E_adj.
              exact: Hrank_unit_conj HQtQ_ZC_E HQQt_ZC_E.
            }
            have Hinner_label_rank :
                \rank tau_inner_labelled = \rank tau_raw_prod.
            { by rewrite /tau_inner_labelled mxrank_cast Hinner_rank. }
            rewrite /tau_prod_labelled.
            have Houter_rank :
                \rank (U_ZCE *m tau_inner_labelled *m U_ZCE^*t) =
                \rank tau_inner_labelled.
            { exact: (@Hrank_iso_conj _ _ U_ZCE tau_inner_labelled HUtU_ZCE). }
            by rewrite Houter_rank Hinner_label_rank Hraw_rank.
            }
            have Hlabelled_dual :=
              @minmax_dual R _ HL [set Zlbl] [set Clbl] [set Elbl]
                disZC disZE disCE [set Cplbl] [set Cpplbl]
                  disZCp disZCpp disCCp disCCpp disCpCpp
                HdimZ_Cp HdimE_Cp_Cpp HdimC_Cpp tauL3 HtauL3_den HtauL3_rank.
          pose tauZL :=
            @ptrace_cast3C R _ HL [set Zlbl] [set Clbl] [set Elbl]
              disZE disCE tauL3.
          pose tauZEL :=
            @ptrace_cast3B R _ HL [set Zlbl] [set Clbl] [set Elbl]
              disZC disCE tauL3.
          have Hmin_bridge :
              hmin [set Elbl] tauZEL = hmin_mx tauZpABR.
          {
            (* Product-coordinate min bridge for the complementary
               Z|Z'ABR marginal of tau_ZC(Z'ABR). *)
            pose S_ZE := [set Zlbl] :|: [set Elbl].
            have HdimC_prod : dim 'H[HL]_[set Clbl] = nc.
            {
              by rewrite -(dim_set1 HL Clbl) HHLC.
            }
            have HdimE_prod : dim 'H[HL]_[set Elbl] = Ebig.
            {
              by rewrite -(dim_set1 HL Elbl) HHLE.
            }
            have HdimZ_prod : dim 'H[HL]_[set Zlbl] = nz.
            {
              by rewrite -(dim_set1 HL Zlbl) HHLZ.
            }
            have HdimZE_prod :
                (dim 'H[HL]_[set Zlbl] * dim 'H[HL]_[set Elbl] =
                 nz * Ebig)%N.
            {
              by rewrite -(dim_set1 HL Zlbl) -(dim_set1 HL Elbl) HHLZ HHLE.
            }
            have HdimZE_cast_tensor :
                forall (sigmaE : 'M[C]_(dim 'H[HL]_[set Elbl])),
                castmx (HdimZE_prod, HdimZE_prod)
                  ((1%:M : 'M[C]_(dim 'H[HL]_[set Zlbl])) *t sigmaE) =
                (1%:M : 'M[C]_nz) *t
                  castmx (HdimE_prod, HdimE_prod) sigmaE.
            {
              have Hcast_tensor_gen :
                  forall dz de nz0 ne
                    (ez : dz = nz0) (ee : de = ne)
                    (sigmaE : 'M[C]_de),
                  castmx (f_equal2 muln ez ee, f_equal2 muln ez ee)
                    ((1%:M : 'M[C]_dz) *t sigmaE) =
                  (1%:M : 'M[C]_nz0) *t castmx (ee, ee) sigmaE.
              {
                move=> dz de nz0 ne ez ee sigmaE.
                case: nz0 / ez.
                case: ne / ee.
                by rewrite castmx_id.
              }
              move=> sigmaE.
              have Hprod_eq :
                  HdimZE_prod = f_equal2 muln HdimZ_prod HdimE_prod
                by apply: eq_irrelevance.
              rewrite Hprod_eq.
              exact: Hcast_tensor_gen.
            }
            pose tauZEL_prod : 'M[C]_(nz * Ebig) :=
              castmx (HdimZE_prod, HdimZE_prod)
                (biprod_mx disZE tauZEL).
            have HtauZEL_prod : tauZEL_prod = tauZpABR.
            {
              (* TeX eqn:dual/eqn:mo1 bookkeeping: the labelled
                 Z|Z'ABR marginal is the product-coordinate partial trace
                 of the raw `(Z*C)*E` purification. *)
              pose tauZE_raw : 'M[C]_(nz * Ebig) :=
                \matrix_(i, j)
                  let iZE := mxtens_unindex i in
                  let jZE := mxtens_unindex j in
                  \sum_(c : 'I_nc)
                    tauZC_big
                      (mxtens_index (mxtens_index (iZE.1, c), iZE.2))
                      (mxtens_index (mxtens_index (jZE.1, c), jZE.2)).
              pose tauZEC_raw : 'M[C]_((nz * Ebig) * nc) :=
                \matrix_(i, j)
                  let iZEC := mxtens_unindex i in
                  let jZEC := mxtens_unindex j in
                  let iZE := mxtens_unindex iZEC.1 in
                  let jZE := mxtens_unindex jZEC.1 in
                  tauZC_big
                    (mxtens_index (mxtens_index (iZE.1, iZEC.2), iZE.2))
                    (mxtens_index (mxtens_index (jZE.1, jZEC.2), jZE.2)).
              have Hptrace_tauZEC_raw : ptrace2 tauZEC_raw = tauZE_raw.
              {
                have ptrace2E' : forall s t (B : 'M[C]_(s * t)) r1 r2,
                    (ptrace2 B) r1 r2 =
                    \sum_(k0 : 'I_t) B (mxtens_index (r1, k0))
                                       (mxtens_index (r2, k0)).
                {
                  move=> s t B r1 r2; rewrite ptrace2E1 ptrace1E.
                  by apply: eq_bigr => k0 _; rewrite mxE !mxtens_indexK.
                }
                apply/matrixP=> i j.
                rewrite /tauZEC_raw /tauZE_raw ptrace2E' mxE.
                apply: eq_bigr=> c _.
                by rewrite mxE !mxtens_indexK.
              }
              have HtauZEL_ptrace_raw : tauZEL_prod = ptrace2 tauZEC_raw.
              {
                (* Product-coordinate trace bookkeeping from labelled
                   `(Z,E),C` back to raw `(Z,C),E`. *)
                have Hptrace_cast_gen_cast :
                    forall (S S' T U : {set 'I_5})
                      (eqSS' : S = S') (eq1 : S :\: T = U)
                      (eq2 : S' :\: T = U) (f : 'F[HL]_S),
                    castlf (eq1, eq1) (\Tr_(T) f) =
                    castlf (eq2, eq2) (\Tr_(T) (castlf (eqSS', eqSS') f)).
                {
                  move=> S S' T U eqSS' eq1 eq2 f.
                  case: S' / eqSS' in f eq2 *.
                  rewrite castlf_id.
                  have -> : eq2 = eq1 by apply: eq_irrelevance.
                  by [].
                }
                have disZE_C : [disjoint S_ZE & [set Clbl]].
                {
                  by rewrite /S_ZE disjointUX disZC disjoint_sym disCE.
                }
                have eqZCE_ZEC : S_ZCE3 = S_ZE :|: [set Clbl].
                {
                  apply/setP=> x.
                  rewrite /S_ZCE3 /S_ZC /S_ZE !inE.
                  by case: (x == Zlbl); case: (x == Clbl);
                    case: (x == Elbl).
                }
                have HtauZEL_cast :
                    tauZEL =
                    ptrace_cast disZE_C (castlf (eqZCE_ZEC, eqZCE_ZEC) tauL3).
                {
                  rewrite /tauZEL /ptrace_cast3B /ptrace_cast
                    /ptrace_cast_gen.
                  exact: Hptrace_cast_gen_cast.
                }
                pose Q_ZE : 'M[C]_(dim 'H[HL]_[set Zlbl] *
                                    dim 'H[HL]_[set Elbl]) :=
                  castmx (tenv_dim disZE, erefl _)
                    (@tenv_mxU R _ HL [set Zlbl] [set Elbl]).
                pose U_ZEC := @tenv_mxU R _ HL S_ZE [set Clbl].
                pose I_C : 'M[C]_(dim 'H[HL]_[set Clbl]) := 1%:M.
                pose tau_ZEC_label :=
                  U_ZEC^*t *m h2mx (castlf (eqZCE_ZEC, eqZCE_ZEC) tauL3) *m
                    U_ZEC.
                have HdimZEC_col :
                    (dim 'H[HL]_S_ZE * dim 'H[HL]_[set Clbl] =
                     (dim 'H[HL]_[set Zlbl] * dim 'H[HL]_[set Elbl]) *
                       dim 'H[HL]_[set Clbl])%N.
                {
                  by rewrite /S_ZE (tenv_dim disZE).
                }
                have HdimZEC_raw :
                    (((dim 'H[HL]_[set Zlbl] * dim 'H[HL]_[set Elbl]) *
                         dim 'H[HL]_[set Clbl]) =
                     (nz * Ebig) * nc)%N.
                {
                  by rewrite HdimZ_prod HdimE_prod HdimC_prod.
                }
                pose tauZEC_prod : 'M[C]_((nz * Ebig) * nc) :=
                  castmx (HdimZEC_raw, HdimZEC_raw)
                    ((Q_ZE^*t *t I_C) *m
                      castmx (HdimZEC_col, HdimZEC_col) tau_ZEC_label *m
                      (Q_ZE *t I_C)).
                have Hptrace_prod : tauZEL_prod = ptrace2 tauZEC_prod.
                {
                  rewrite /tauZEL_prod /biprod_mx
                    HtauZEL_cast.
                  rewrite (h2mx_ptrace_cast_ptrace2 disZE_C
                    (castlf (eqZCE_ZEC, eqZCE_ZEC) tauL3)).
                  rewrite -/Q_ZE -/tau_ZEC_label.
                  have Hptrace2_cast_forward :
                      forall m m' n n' (em : m = m') (en : n = n')
                        (A : 'M[C]_(m * n)),
                      ptrace2
                        (castmx (f_equal2 muln em en,
                                 f_equal2 muln em en) A) =
                      castmx (em, em) (ptrace2 A).
                  {
                    move=> m m' n n' em en A.
                    case: m' / em in A *.
                    case: n' / en in A *.
                    rewrite (eq_irrelevance
                      (f_equal2 muln (erefl m) (erefl n))
                      (erefl (m * n)%N)).
                    by rewrite castmx_id.
                  }
                  have Hptrace_conj :
                      ptrace2 tauZEC_prod =
                      castmx (HdimZE_prod, HdimZE_prod)
                        (Q_ZE^*t *m
                          castmx (tenv_dim disZE, tenv_dim disZE)
                            (ptrace2 tau_ZEC_label) *m Q_ZE).
                  {
                    rewrite /tauZEC_prod.
                    have Hraw_eq :
                        HdimZEC_raw =
                        f_equal2 muln HdimZE_prod HdimC_prod :=
                      eq_irrelevance _ _.
                    rewrite Hraw_eq.
                    rewrite Hptrace2_cast_forward.
                    congr (castmx (HdimZE_prod, HdimZE_prod)).
                    rewrite /I_C ptrace2_mulmxI ptrace2_mulImx.
                    have Hcol_eq :
                        HdimZEC_col =
                        f_equal (fun n => (n * dim 'H[HL]_[set Clbl])%N)
                          (tenv_dim disZE) := eq_irrelevance _ _.
                    rewrite Hcol_eq.
                    congr (Q_ZE^*t *m _ *m Q_ZE).
                    have Hcast_eq :
                        f_equal (muln^~ (dim 'H[HL]_[set Clbl]))
                          (tenv_dim disZE) =
                        f_equal2 muln (tenv_dim disZE)
                          (erefl (dim 'H[HL]_[set Clbl])) :=
                      eq_irrelevance _ _.
                    rewrite Hcast_eq.
                    rewrite Hptrace2_cast_forward.
                    by [].
                  }
                  by rewrite Hptrace_conj.
                }
                have Hptrace_prod_raw : ptrace2 tauZEC_prod = tauZE_raw.
                {
                  have ptrace2E'' : forall s t (B : 'M[C]_(s * t)) r1 r2,
                      (ptrace2 B) r1 r2 =
                      \sum_(k0 : 'I_t) B (mxtens_index (r1, k0))
                                         (mxtens_index (r2, k0)).
                  {
                    move=> s t B r1 r2; rewrite ptrace2E1 ptrace1E.
                    by apply: eq_bigr => k0 _; rewrite mxE !mxtens_indexK.
                  }
                  have Hh2mx_castlf :
                      forall (S S' : {set 'I_5}) (eqSS' : S = S')
                        (f : 'F[HL]_S),
                      h2mx (castlf (eqSS', eqSS') f) =
                      castmx (f_equal (fun T => dim 'H[HL]_T) eqSS',
                              f_equal (fun T => dim 'H[HL]_T) eqSS')
                        (h2mx f).
                  {
                    move=> S S' eqSS' f.
                    case: S' / eqSS' in f *.
                    by rewrite castlf_id castmx_id.
                  }
                  have tensmxE_any :
                      forall m n p q (A : 'M[C]_(m, n)) (B : 'M[C]_(p, q))
                        (i0 : 'I_(m * p)) (j0 : 'I_(n * q)),
                      (A *t B) i0 j0 =
                      A (mxtens_unindex i0).1 (mxtens_unindex j0).1 *
                      B (mxtens_unindex i0).2 (mxtens_unindex j0).2.
                  {
                    move=> m n p q A B i0 j0.
                    case Ei: (mxtens_unindex i0)=> [i1 i2].
                    case Ej: (mxtens_unindex j0)=> [j1 j2].
                    rewrite -(mxtens_unindexK i0) Ei.
                    rewrite -(mxtens_unindexK j0) Ej.
                    by rewrite tensmxE.
                  }
                  have Hcast_ZEC_unindex :
                      forall (ze : 'I_(nz * Ebig)) (c0 : 'I_nc),
                      mxtens_unindex
                        (cast_ord (esym HdimZEC_raw)
                          (mxtens_index (ze, c0))) =
                      (cast_ord (esym HdimZE_prod) ze,
                       cast_ord (esym HdimC_prod) c0).
                  {
                    move=> ze c0.
                    case Ecast: (mxtens_unindex
                        (cast_ord (esym HdimZEC_raw)
                          (mxtens_index (ze, c0)))) => [ze' c'].
                    apply: (can_inj (@mxtens_indexK _ _)).
                    rewrite -Ecast mxtens_unindexK.
                    apply/val_inj=> /=.
                    by rewrite HdimC_prod.
                  }
                  have HdimZC_prod_local :
                      (dim 'H[HL]_[set Zlbl] * dim 'H[HL]_[set Clbl] =
                       nz * nc)%N.
                  {
                    by rewrite -(dim_set1 HL Zlbl) -(dim_set1 HL Clbl)
                      HHLZ HHLC.
                  }
                  have Hcast_ZC_index :
                      forall (z0 : 'I_nz) (c0 : 'I_nc),
                      cast_ord HdimZC_prod_local
                        (mxtens_index (cast_ord (esym HdimZ_prod) z0,
                                        cast_ord (esym HdimC_prod) c0)) =
                      mxtens_index (z0, c0).
                  {
                    move=> z0 c0.
                    apply/val_inj=> /=.
                    by rewrite HdimC_prod.
                  }
                  have Hcast_ZCE_unindex :
                      forall (zc : 'I_(nz * nc)) (e0 : 'I_Ebig),
                      mxtens_unindex
                        (cast_ord (esym HdimZCE_raw) (mxtens_index (zc, e0))) =
                      (cast_ord (esym HdimZC_prod_local) zc,
                       cast_ord (esym HdimE_prod) e0).
                  {
                    move=> zc e0.
                    case Ecast: (mxtens_unindex
                        (cast_ord (esym HdimZCE_raw)
                          (mxtens_index (zc, e0)))) => [zc' e'].
                    apply: (can_inj (@mxtens_indexK _ _)).
                    rewrite -Ecast mxtens_unindexK.
                    apply/val_inj=> /=.
                    by rewrite HdimE_prod.
                  }
                  have Hcast_ZCE_unindex_fw :
                      forall (zc : 'I_(dim 'H[HL]_[set Zlbl] *
                                        dim 'H[HL]_[set Clbl]))
                             (e0 : 'I_(dim 'H[HL]_[set Elbl])),
                      mxtens_unindex
                        (cast_ord HdimZCE_raw (mxtens_index (zc, e0))) =
                      (cast_ord HdimZC_prod_local zc,
                       cast_ord HdimE_prod e0).
                  {
                    move=> zc e0.
                    have Hraw_eq :
                        HdimZCE_raw =
                        f_equal2 muln HdimZC_prod_local HdimE_prod
                      by apply: eq_irrelevance.
                    rewrite Hraw_eq.
                    apply: (can_inj (@mxtens_indexK _ _)).
                    rewrite mxtens_unindexK.
                    apply/val_inj=> /=.
                    change ((zc * dim 'H[HL]_[set Elbl] + e0)%N =
                            (zc * Ebig + e0)%N).
                    exact: (f_equal2 addn
                      (f_equal2 muln (erefl _) HdimE_prod) (erefl _)).
                  }
                  have Hcast_ZEC_col_unindex :
                      forall (ze : 'I_(dim 'H[HL]_S_ZE))
                             (c0 : 'I_(dim 'H[HL]_[set Clbl])),
                      mxtens_unindex
                        (cast_ord (esym HdimZEC_col)
                          (mxtens_index (cast_ord (tenv_dim disZE) ze, c0))) =
                      (ze, c0).
                  {
                    move=> ze c0.
                    case Ecast: (mxtens_unindex
                        (cast_ord (esym HdimZEC_col)
                          (mxtens_index (cast_ord (tenv_dim disZE) ze, c0)))) =>
                      [ze' c'].
                    apply: (can_inj (@mxtens_indexK _ _)).
                    rewrite -Ecast mxtens_unindexK.
                    apply/val_inj=> /=.
                    by [].
                  }
                  have Hcast_ZE_unindex :
                      forall (z0 : 'I_nz) (e0 : 'I_Ebig),
                      mxtens_unindex
                        (cast_ord (esym HdimZE_prod) (mxtens_index (z0, e0))) =
                      (cast_ord (esym HdimZ_prod) z0,
                       cast_ord (esym HdimE_prod) e0).
                  {
                    move=> z0 e0.
                    case Ecast: (mxtens_unindex
                        (cast_ord (esym HdimZE_prod)
                          (mxtens_index (z0, e0)))) => [z' e'].
                    apply: (can_inj (@mxtens_indexK _ _)).
                    rewrite -Ecast mxtens_unindexK.
                    apply/val_inj=> /=.
                    by rewrite HdimE_prod.
                  }
                  have Hcast_ZCE_col_unindex :
                      forall (zc : 'I_(dim 'H[HL]_S_ZC))
                             (e0 : 'I_(dim 'H[HL]_[set Elbl])),
                      mxtens_unindex
                        (cast_ord HdimZCE_col (mxtens_index (zc, e0))) =
                      (cast_ord (tenv_dim disZC) zc, e0).
                  {
                    move=> zc e0.
                    case Ecast: (mxtens_unindex
                        (cast_ord HdimZCE_col (mxtens_index (zc, e0)))) =>
                      [zc' e'].
                    apply: (can_inj (@mxtens_indexK _ _)).
                    rewrite -Ecast mxtens_unindexK.
                    apply/val_inj=> /=.
                    by [].
                  }
                  have Hn2i_cast_i2n :
                      forall (S S' : {set 'I_5}) (eqSS' : S = S')
                        (x : 'Idx[HL]_S),
                      n2i (cast_ord
                        (f_equal (fun T => dim 'H[HL]_T) eqSS') (i2n x)) =
                      castidx eqSS' x.
                  {
                    move=> S S' eqSS' x.
                    case: S' / eqSS' in x *.
                    rewrite castidx_id.
                    have -> :
                        f_equal
                          (fun T : {set 'I_5} => dim 'H[HL]_T) (erefl S) =
                        erefl (dim 'H[HL]_S) by apply: eq_irrelevance.
                    by rewrite cast_ord_id i2nK.
                  }
                  have sum_deltaR :
                      forall n (a : 'I_n) (F : 'I_n -> C),
                      \sum_i F i * ((i == a)%:R : C) = F a.
                  {
                    move=> n a F.
                    rewrite (bigD1 a) //= eqxx mulr1.
                    rewrite [X in _ + X]big1 ?addr0 //.
                    by move=> i0 /negPf Hi0; rewrite Hi0 mulr0.
                  }
                  have sum_deltaL :
                      forall n (a : 'I_n) (F : 'I_n -> C),
                      \sum_i ((i == a)%:R : C) * F i = F a.
                  {
                    move=> n a F.
                    under eq_bigr => i0 _ do rewrite mulrC.
                    exact: sum_deltaR.
                  }
                  have sum_deltaL_sym :
                      forall n (a : 'I_n) (F : 'I_n -> C),
                      \sum_i ((a == i)%:R : C) * F i = F a.
                  {
                    move=> n a F.
                    under eq_bigr => i0 _ do rewrite eq_sym.
                    exact: sum_deltaL.
                  }
                  have sum_delta_mid :
                      forall n (a : 'I_n) (K : C) (F : 'I_n -> C),
                      \sum_i K * ((a == i)%:R : C) * F i = K * F a.
                  {
                    move=> n a K F.
                    rewrite (bigD1 a) //= eqxx mulr1.
                    rewrite [X in _ + X]big1 ?addr0 //.
                    by move=> i0 /negPf Hi0; rewrite eq_sym Hi0 mulr0
                      mul0r.
                  }
                  have HQ_ZE_delta :
                      forall (jze t : 'I_(dim 'H[HL]_[set Zlbl] *
                                            dim 'H[HL]_[set Elbl])),
                      Q_ZE jze t =
                      ((jze ==
                        cast_ord (tenv_dim disZE) (tenv_indexl t))%:R : C).
                  {
                    move=> jze t.
                    rewrite /Q_ZE castmxE /tenv_mxU mxE.
                    pose fZE (x : 'I_(dim 'H[HL]_[set Zlbl] *
                                        dim 'H[HL]_[set Elbl])) :=
                      tenv_indexr (cast_ord (esym (tenv_dim disZE)) x).
                    pose gZE (x : 'I_(dim 'H[HL]_[set Zlbl] *
                                        dim 'H[HL]_[set Elbl])) :=
                      cast_ord (tenv_dim disZE) (tenv_indexl x).
                    have fZE_K : cancel fZE gZE.
                    {
                      move=> x.
                      rewrite /fZE /gZE tenv_indexrK.
                      by rewrite cast_ordKV.
                    }
                    have gZE_K : cancel gZE fZE.
                    {
                      move=> x.
                      rewrite /fZE /gZE cast_ordK.
                      exact: tenv_indexlK.
                    }
                    rewrite cast_ord_id.
                    congr (_%:R).
                    by rewrite -/(fZE jze) -/(gZE t)
                      (can2_eq fZE_K gZE_K).
                  }
                  have HQ_ZC_delta :
                      forall (jzc t : 'I_(dim 'H[HL]_[set Zlbl] *
                                            dim 'H[HL]_[set Clbl])),
                      Q_ZC jzc t =
                      ((jzc ==
                        cast_ord (tenv_dim disZC) (tenv_indexl t))%:R : C).
                  {
                    move=> jzc t.
                    rewrite /Q_ZC castmxE /tenv_mxU mxE.
                    pose fZC (x : 'I_(dim 'H[HL]_[set Zlbl] *
                                        dim 'H[HL]_[set Clbl])) :=
                      tenv_indexr (cast_ord (esym (tenv_dim disZC)) x).
                    pose gZC (x : 'I_(dim 'H[HL]_[set Zlbl] *
                                        dim 'H[HL]_[set Clbl])) :=
                      cast_ord (tenv_dim disZC) (tenv_indexl x).
                    have fZC_K : cancel fZC gZC.
                    {
                      move=> x.
                      rewrite /fZC /gZC tenv_indexrK.
                      by rewrite cast_ordKV.
                    }
                    have gZC_K : cancel gZC fZC.
                    {
                      move=> x.
                      rewrite /fZC /gZC cast_ordK.
                      exact: tenv_indexlK.
                    }
                    rewrite cast_ord_id.
                    congr (_%:R).
                    by rewrite -/(fZC jzc) -/(gZC t)
                      (can2_eq fZC_K gZC_K).
                  }
                  have HQZC_E_delta_l :
                      forall (p j0 : 'I_((dim 'H[HL]_[set Zlbl] *
                                            dim 'H[HL]_[set Clbl]) *
                                           dim 'H[HL]_[set Elbl])),
                      (Q_ZC *t I_E) p j0 =
                      ((j0 ==
                        mxtens_index
                          (tenv_indexr
                            (cast_ord (esym (tenv_dim disZC))
                              (mxtens_unindex p).1),
                           (mxtens_unindex p).2))%:R : C).
                  {
                    move=> p j0.
                    rewrite tensmxE_any HQ_ZC_delta /I_E mxE.
                    case Ep: (mxtens_unindex p)=> [pzc pe].
                    case Ej: (mxtens_unindex j0)=> [jzc je].
                    rewrite /=.
                    have Hzc :
                        (pzc ==
                          cast_ord (tenv_dim disZC) (tenv_indexl jzc)) =
                        (jzc ==
                          tenv_indexr (cast_ord (esym (tenv_dim disZC))
                            pzc)).
                    {
                      rewrite eq_sym.
                      pose fZC (x : 'I_(dim 'H[HL]_[set Zlbl] *
                                          dim 'H[HL]_[set Clbl])) :=
                        tenv_indexr (cast_ord (esym (tenv_dim disZC)) x).
                      pose gZC (x : 'I_(dim 'H[HL]_[set Zlbl] *
                                          dim 'H[HL]_[set Clbl])) :=
                        cast_ord (tenv_dim disZC) (tenv_indexl x).
                      have fZC_K : cancel fZC gZC.
                      {
                        move=> x.
                        rewrite /fZC /gZC tenv_indexrK.
                        by rewrite cast_ordKV.
                      }
                      have gZC_K : cancel gZC fZC.
                      {
                        move=> x.
                        rewrite /fZC /gZC cast_ordK.
                        exact: tenv_indexlK.
                      }
                      rewrite [jzc == _]eq_sym.
                      by rewrite -/(fZC pzc) -/(gZC jzc)
                        (can2_eq fZC_K gZC_K).
                    }
                    rewrite Hzc.
                    have Hpair :
                        (j0 ==
                          mxtens_index
                            (tenv_indexr (cast_ord (esym (tenv_dim disZC))
                              pzc), pe)) =
                        ((jzc ==
                          tenv_indexr (cast_ord (esym (tenv_dim disZC))
                            pzc)) && (je == pe)).
                    {
                      rewrite -(mxtens_unindexK j0) Ej.
                      rewrite (inj_eq (can_inj (@mxtens_indexK _ _))).
                      by rewrite -pair_eqE.
                    }
                    rewrite Hpair [je == pe]eq_sym.
                    by case: (jzc == _); case: (pe == je);
                      rewrite ?mul0r ?mulr0 ?mul1r ?mulr1.
                  }
                  have HQZC_E_delta_r :
                      forall (k q : 'I_((dim 'H[HL]_[set Zlbl] *
                                          dim 'H[HL]_[set Clbl]) *
                                         dim 'H[HL]_[set Elbl])),
                      (Q_ZC^*t *t I_E) k q =
                      ((k ==
                        mxtens_index
                          (tenv_indexr
                            (cast_ord (esym (tenv_dim disZC))
                              (mxtens_unindex q).1),
                           (mxtens_unindex q).2))%:R : C).
                  {
                    move=> k q.
                    rewrite tensmxE_any adjmxE /I_E mxE.
                    case Ek: (mxtens_unindex k)=> [kzc ke].
                    case Eq: (mxtens_unindex q)=> [qzc qe].
                    rewrite /= mxE HQ_ZC_delta conjC_nat.
                    have Hzc :
                        (qzc ==
                          cast_ord (tenv_dim disZC) (tenv_indexl kzc)) =
                        (kzc ==
                          tenv_indexr (cast_ord (esym (tenv_dim disZC))
                            qzc)).
                    {
                      rewrite eq_sym.
                      pose fZC (x : 'I_(dim 'H[HL]_[set Zlbl] *
                                          dim 'H[HL]_[set Clbl])) :=
                        tenv_indexr (cast_ord (esym (tenv_dim disZC)) x).
                      pose gZC (x : 'I_(dim 'H[HL]_[set Zlbl] *
                                          dim 'H[HL]_[set Clbl])) :=
                        cast_ord (tenv_dim disZC) (tenv_indexl x).
                      have fZC_K : cancel fZC gZC.
                      {
                        move=> x.
                        rewrite /fZC /gZC tenv_indexrK.
                        by rewrite cast_ordKV.
                      }
                      have gZC_K : cancel gZC fZC.
                      {
                        move=> x.
                        rewrite /fZC /gZC cast_ordK.
                        exact: tenv_indexlK.
                      }
                      rewrite [kzc == _]eq_sym.
                      by rewrite -/(fZC qzc) -/(gZC kzc)
                        (can2_eq fZC_K gZC_K).
                    }
                    rewrite Hzc.
                    have Hpair :
                        (k ==
                          mxtens_index
                            (tenv_indexr (cast_ord (esym (tenv_dim disZC))
                              qzc), qe)) =
                        ((kzc ==
                          tenv_indexr (cast_ord (esym (tenv_dim disZC))
                            qzc)) && (ke == qe)).
                    {
                      rewrite -(mxtens_unindexK k) Ek.
                      rewrite (inj_eq (can_inj (@mxtens_indexK _ _))).
                      by rewrite -pair_eqE.
                    }
                    rewrite Hpair mxE.
                    by case: (kzc == _); case: (ke == qe);
                      rewrite ?mul0r ?mulr0 ?mul1r ?mulr1.
                  }
                  have Htenv_adj_conj_entry :
                      forall (A B : {set 'I_5}) (disAB0 : [disjoint A & B])
                        (M0 : 'M[C]_(dim 'H[HL]_(A :|: B)))
                        (p q : 'I_(dim 'H[HL]_A * dim 'H[HL]_B)),
                      ((@tenv_mxU R _ HL A B)^*t *m M0 *m
                        @tenv_mxU R _ HL A B) p q =
                      M0 (@tenv_indexl R _ HL A B p)
                         (@tenv_indexl R _ HL A B q).
                  {
                    move=> A B disAB0 M0 p q.
                    rewrite mxE
                      (bigD1 (@tenv_indexl R _ HL A B q)) //= big1
                      ?addr0.
                    2: {
                      move=> k /negPf Hk.
                      rewrite !mxE
                          (can2_eq (@tenv_indexrK R _ HL A B)
                          (tenv_indexlK disAB0)).
                      by rewrite Hk !mulr0.
                    }
                    rewrite mxE
                      (bigD1 (@tenv_indexl R _ HL A B p)) //= big1
                      ?addr0.
                    2: {
                      move=> k /negPf Hk.
                      rewrite adjmxE !mxE
                          (can2_eq (@tenv_indexrK R _ HL A B)
                          (tenv_indexlK disAB0)).
                      by rewrite Hk conjC0 !mul0r.
                    }
                    by rewrite adjmxE !mxE (tenv_indexlK disAB0)
                      (tenv_indexlK disAB0) !eqxx !mulr1 conjC1 mul1r.
                  }
                  have Htenv_conj_adj_entry :
                      forall (A B : {set 'I_5})
                        (M0 : 'M[C]_(dim 'H[HL]_A * dim 'H[HL]_B))
                        (p q : 'I_(dim 'H[HL]_(A :|: B))),
                      (@tenv_mxU R _ HL A B *m M0 *m
                        (@tenv_mxU R _ HL A B)^*t) p q =
                      M0 (@tenv_indexr R _ HL A B p)
                         (@tenv_indexr R _ HL A B q).
                  {
                    move=> A B M0 p q.
                    rewrite mxE
                      (bigD1 (@tenv_indexr R _ HL A B q)) //= big1
                      ?addr0.
                    2: {
                      move=> k /negPf Hk.
                      by rewrite adjmxE !mxE eq_sym Hk conjC0 mulr0.
                    }
                    rewrite mxE
                      (bigD1 (@tenv_indexr R _ HL A B p)) //= big1
                      ?addr0.
                    2: by move=> k /negPf Hk; rewrite !mxE eq_sym Hk mul0r.
                    by rewrite adjmxE !mxE !eqxx conjC1 !mulr1 mul1r.
                  }
                  have Hidx_ZEC_ZCE_assoc :
                      forall (z : 'Idx[HL]_[set Zlbl])
                             (e0 : 'Idx[HL]_[set Elbl])
                             (c0 : 'Idx[HL]_[set Clbl]),
                      idxSl
                        (castidx (esym eqZCE_ZEC)
                          (idxU (idxU z e0 : 'Idx[HL]_S_ZE) c0)) =
                        (idxU z c0 : 'Idx[HL]_S_ZC) /\
                      idxSr
                        (castidx (esym eqZCE_ZEC)
                          (idxU (idxU z e0 : 'Idx[HL]_S_ZE) c0)) = e0.
                  {
                    move=> z e0 c0.
                    pose eAB := (idxU (idxU z e0 : 'Idx[HL]_S_ZE) c0 :
                      'Idx[HL]_(S_ZE :|: [set Clbl])).
                    have HsubZC_ZEC : S_ZC :<=: S_ZE :|: [set Clbl].
                    {
                      apply/mathcomp.boot.fintype.subsetP=> x.
                      rewrite /S_ZC /S_ZE !inE.
                      by case/orP=> ->; rewrite ?orbT.
                    }
                    have HsubE_ZEC : [set Elbl] :<=: S_ZE :|: [set Clbl].
                    {
                      apply/mathcomp.boot.fintype.subsetP=> x.
                      by rewrite /S_ZE !inE => ->; rewrite orbT.
                    }
                    have Hleft :
                        idxSl (castidx (esym eqZCE_ZEC) eAB) =
                        (idxU z c0 : 'Idx[HL]_S_ZC).
                    {
                      apply/eqP.
                      rewrite -idxBE.
                      apply/andP; split; apply/eqP.
                      - rewrite !idxSl_idxR !idxRA.
                        rewrite (@idxR_castR R _ HL [set Zlbl]
                          (S_ZE :|: [set Clbl]) S_ZCE3
                          (esym eqZCE_ZEC)
                          (mathcomp.boot.fintype.subset_trans
                            (mathcomp.boot.finset.subsetUl
                              [set Zlbl] [set Clbl])
                            HsubZC_ZEC)
                          (mathcomp.boot.fintype.subset_trans
                            (mathcomp.boot.finset.subsetUl
                              [set Zlbl] [set Clbl])
                            (mathcomp.boot.finset.subsetUl
                              S_ZC [set Elbl])) eAB).
                        rewrite -idxSl_idxR (idxSUl z c0).
                        rewrite -[RHS](idxSUl z e0).
                        rewrite -[idxU z e0](@idxSUl R _ HL S_ZE
                          [set Clbl] (idxU z e0) c0).
                        rewrite !idxSl_idxR !idxRA.
                        by congr (idxR _ eAB); apply: eq_irrelevance.
                      - rewrite !idxSr_idxR !idxRA.
                        rewrite (@idxR_castR R _ HL [set Clbl]
                          (S_ZE :|: [set Clbl]) S_ZCE3
                          (esym eqZCE_ZEC)
                          (mathcomp.boot.fintype.subset_trans
                            (mathcomp.boot.finset.subsetUr
                              [set Zlbl] [set Clbl])
                            HsubZC_ZEC)
                          (mathcomp.boot.fintype.subset_trans
                            (mathcomp.boot.finset.subsetUr
                              [set Zlbl] [set Clbl])
                            (mathcomp.boot.finset.subsetUl
                              S_ZC [set Elbl])) eAB).
                        rewrite -idxSr_idxR (idxSUr disZC z c0).
                        rewrite -[RHS](idxSUr disZE_C (idxU z e0) c0)
                          idxSr_idxR.
                        by congr (idxR _ eAB); apply: eq_irrelevance.
                    }
                    have Hright :
                        idxSr (castidx (esym eqZCE_ZEC) eAB) = e0.
                    {
                      rewrite idxSr_idxR.
                      rewrite (@idxR_castR R _ HL [set Elbl]
                        (S_ZE :|: [set Clbl]) S_ZCE3
                        (esym eqZCE_ZEC) HsubE_ZEC
                        (mathcomp.boot.finset.subsetUr
                          S_ZC [set Elbl]) eAB).
                      rewrite -[RHS](idxSUr disZE z e0).
                      rewrite -[idxU z e0](@idxSUl R _ HL S_ZE [set Clbl]
                        (idxU z e0) c0) idxSr_idxR idxSl_idxR.
                      rewrite idxRA.
                      by congr (idxR _ eAB); apply: eq_irrelevance.
                    }
                    by split.
                  }
                  apply/matrixP=> i j.
                  case: (mxtens_indexP i)=> zi ei.
                  case: (mxtens_indexP j)=> zj ej.
                  rewrite /tauZE_raw ptrace2E'' mxE.
                  apply: eq_bigr=> c _.
                  rewrite /tauZEC_prod /tau_ZEC_label.
                  rewrite Hh2mx_castlf /tauL3 mx2hK /tau_prod_labelled
                    /tau_inner_labelled /tau_raw_prod.
                  rewrite ?[LHS]castmxE ![LHS]mxE.
                  rewrite [LHS]mxtens_index_pairV /=.
                  rewrite ?mxtens_indexK.
                  rewrite ?Hcast_ZEC_unindex.
                  under eq_bigr => jze _ do
                    under eq_bigr => jc _ do rewrite tensmxE_any /I_C mxE
                      mxtens_indexK Hcast_ZEC_unindex.
                  under eq_bigr => jze _ do
                    under eq_bigr => jc _ do rewrite mxE /=.
                  under eq_bigr => jze _ do
                    under eq_bigr => jc _ do rewrite mulrA.
                  under eq_bigr => jze _ do rewrite sum_deltaR.
                  under eq_bigr => jze _ do rewrite HQ_ZE_delta.
                  under eq_bigr => jze _ do rewrite ?mulrA.
                  rewrite sum_deltaR.
                  rewrite [LHS]mxtens_index_pairV /=.
                  under eq_bigr => ize _ do
                    under eq_bigr => ic _ do rewrite tensmxE_any adjmxE mxE
                      mxtens_indexK ?HQ_ZE_delta ?conjC_nat /I_C mxE
                      Hcast_ZEC_unindex /=.
                  under eq_bigr => ize _ do
                    under eq_bigr => ic _ do rewrite HQ_ZE_delta conjC_nat mxE
                      eq_sym.
                  under eq_bigr => ize _ do rewrite sum_delta_mid.
                  rewrite sum_deltaL_sym.
                  rewrite castmxE
                    (Htenv_adj_conj_entry S_ZE [set Clbl] disZE_C).
                  rewrite castmxE
                    (Htenv_conj_adj_entry S_ZC [set Elbl]).
                  rewrite /tenv_indexr /tenv_indexl ?Hcast_ZEC_col_unindex
                    ?Hcast_ZE_unindex /= ?mxtens_indexK.
                  rewrite /Zlbl /Clbl /Elbl /HL /=.
                  rewrite castmxE !mxE.
                  under eq_bigr => k _ do rewrite mxE.
                  under eq_bigr => k _ do
                    under eq_bigr => j0 _ do rewrite HQZC_E_delta_l.
                  under eq_bigr => k _ do rewrite sum_deltaL.
                  under eq_bigr => k _ do rewrite HQZC_E_delta_r.
                  rewrite sum_deltaR.
                  rewrite castmxE.
                  set rowL := (X in tauZC_big X _ = _).
                  set colL := (X in tauZC_big _ X = _).
                  set rowR := (X in _ = tauZC_big X _).
                  set colR := (X in _ = tauZC_big _ X).
                  set rowT := mxtens_index (mxtens_index (zi, c), ei).
                  set colT := mxtens_index (mxtens_index (zj, c), ej).
                  have HrowL : rowL = rowT.
                  {
                    rewrite /rowL /rowT.
                    have Hraw_cast :
                        esym (esym HdimZCE_raw, esym HdimZCE_raw).1 =
                        HdimZCE_raw by apply: eq_irrelevance.
                    rewrite Hraw_cast.
                    apply: (can_inj (@mxtens_unindexK _ _)).
                    have Hcol_cast :
                        esym (esym HdimZCE_col, esym HdimZCE_col).1 =
                        HdimZCE_col by apply: eq_irrelevance.
                    rewrite Hcol_cast Hcast_ZCE_col_unindex
                      Hcast_ZCE_unindex_fw mxtens_indexK.
                    rewrite cast_ordK.
                    rewrite /tenv_indexr !i2nK.
                    have Hcast_assoc :
                        esym
                          (f_equal (fun T : {set 'I_5} => dim 'H[HL]_T)
                            eqZCE_ZEC) =
                        f_equal (fun T : {set 'I_5} => dim 'H[HL]_T)
                          (esym eqZCE_ZEC) by apply: eq_irrelevance.
                    rewrite Hcast_assoc !Hn2i_cast_i2n.
                    set z0 := n2i (cast_ord (esym HdimZ_prod) zi).
                    set e0 := n2i (cast_ord (esym HdimE_prod) ei).
                    set c0 := n2i (cast_ord (esym HdimC_prod) c).
                    have [Hleft Hright] := Hidx_ZEC_ZCE_assoc z0 e0 c0.
                    rewrite Hleft Hright idxSUl idxSUr //.
                    rewrite /z0 /e0 /c0 !n2iK Hcast_ZC_index.
                    by rewrite /= cast_ordKV.
                  }
                  have HcolL : colL = colT.
                  {
                    rewrite /colL /colT.
                    have Hraw_cast :
                        esym (esym HdimZCE_raw, esym HdimZCE_raw).2 =
                        HdimZCE_raw by apply: eq_irrelevance.
                    rewrite Hraw_cast.
                    apply: (can_inj (@mxtens_unindexK _ _)).
                    have Hcol_cast :
                        esym (esym HdimZCE_col, esym HdimZCE_col).2 =
                        HdimZCE_col by apply: eq_irrelevance.
                    rewrite Hcol_cast Hcast_ZCE_col_unindex
                      Hcast_ZCE_unindex_fw mxtens_indexK.
                    rewrite cast_ordK.
                    rewrite /tenv_indexr !i2nK.
                    have Hcast_assoc :
                        esym
                          (f_equal (fun T : {set 'I_5} => dim 'H[HL]_T)
                            eqZCE_ZEC) =
                        f_equal (fun T : {set 'I_5} => dim 'H[HL]_T)
                          (esym eqZCE_ZEC) by apply: eq_irrelevance.
                    rewrite Hcast_assoc !Hn2i_cast_i2n.
                    set z0 := n2i (cast_ord (esym HdimZ_prod) zj).
                    set e0 := n2i (cast_ord (esym HdimE_prod) ej).
                    set c0 := n2i (cast_ord (esym HdimC_prod) c).
                    have [Hleft Hright] := Hidx_ZEC_ZCE_assoc z0 e0 c0.
                    rewrite Hleft Hright idxSUl idxSUr //.
                    rewrite /z0 /e0 /c0 !n2iK Hcast_ZC_index.
                    by rewrite /= cast_ordKV.
                  }
                  have HrowR : rowR = rowT.
                  {
                    rewrite /rowR /rowT.
                    apply: (can_inj (@mxtens_unindexK _ _)).
                    rewrite !mxtens_indexK.
                    have Hzei := mxtens_indexK (zi, ei).
                    case: Hzei => Hzi Hei.
                    by rewrite Hzi Hei.
                  }
                  have HcolR : colR = colT.
                  {
                    rewrite /colR /colT.
                    apply: (can_inj (@mxtens_unindexK _ _)).
                    rewrite !mxtens_indexK.
                    have Hzej := mxtens_indexK (zj, ej).
                    case: Hzej => Hzj Hej.
                    by rewrite Hzj Hej.
                  }
                  by rewrite HrowL HcolL HrowR HcolR.
                }
                by rewrite Hptrace_prod Hptrace_prod_raw.
              }
              have Hraw_tau : tauZE_raw = tauZpABR.
              {
                (* Direct raw form of the semantic AC marginal:
                   mxswap23 sends `(Z*C)*E` to `(Z*E)*C`, then traces C. *)
                have ptrace2E_raw :
                    forall s t (B : 'M[C]_(s * t)) r1 r2,
                    (ptrace2 B) r1 r2 =
                    \sum_(k : 'I_t)
                      B (mxtens_index (r1, k)) (mxtens_index (r2, k)).
                {
                  move=> s t B r1 r2; rewrite ptrace2E1 ptrace1E.
                  by apply: eq_bigr=> k _; rewrite mxE !mxtens_indexK.
                }
                apply/matrixP=> i j.
                case: (mxtens_indexP i)=> zi ei.
                case: (mxtens_indexP j)=> zj ej.
                rewrite /tauZE_raw /tauZpABR /rho_AC_mx ptrace2E_raw mxE.
                apply: eq_bigr=> c _.
                by rewrite mxswap23E !sigma23_tens !mxtens_indexK.
              }
              by rewrite HtauZEL_ptrace_raw Hptrace_tauZEC_raw Hraw_tau.
            }
            have Hphi_feasible_eq :
                forall v0 : R,
                (exists sigma : 'M[C]_Ebig,
                  sigma \is psdmx /\
                  ((1%:M : 'M[C]_nz) *t sigma - tauZpABR) \is psdmx /\
                  v0 = @complex.Re R (\tr sigma)) <->
                phi_min_feasible [set Elbl] tauZEL v0.
            {
              have eqE_ZE : S_ZE :&: [set Elbl] = [set Elbl].
              {
                apply/setP=> x.
                rewrite /S_ZE !inE.
                by case: (x == Elbl); case: (x == Zlbl).
              }
              have HtargetE_eq_local :
                  forall
                    (e : (S_ZE :\: [set Elbl]) :|:
                         (S_ZE :&: [set Elbl]) = S_ZE)
                    (s0 : 'F[HL]_(S_ZE :&: [set Elbl])),
                    castlf (e, e)
                      ((\1 : 'F[HL]_(S_ZE :\: [set Elbl])) \O s0) =
                    ((\1 : 'F[HL]_[set Zlbl]) \O
                      castlf (eqE_ZE, eqE_ZE) s0 : 'F[HL]_S_ZE).
              {
                move=> e s0.
                have eqA : S_ZE :\: [set Elbl] = [set Zlbl].
                {
                  rewrite /S_ZE.
                  exact: setDU_r.
                }
                have eqU1 :
                    (S_ZE :\: [set Elbl]) :|: (S_ZE :&: [set Elbl]) =
                    [set Zlbl] :|: (S_ZE :&: [set Elbl]).
                {
                  by rewrite eqA.
                }
                have eqU2 : [set Zlbl] :|: (S_ZE :&: [set Elbl]) = S_ZE.
                {
                  by rewrite eqE_ZE /S_ZE.
                }
                transitivity
                  (castlf (etrans eqU1 eqU2, etrans eqU1 eqU2)
                    ((\1 : 'F[HL]_(S_ZE :\: [set Elbl])) \O s0)).
                {
                  by rewrite (eq_irrelevance (etrans eqU1 eqU2) e).
                }
                rewrite -(castlf_comp eqU1 eqU1 eqU2 eqU2).
                rewrite (sdotIf_cast_l eqA eqU1) castlf1.
                by rewrite (sdotIf_cast_r eqE_ZE eqU2).
              }
              have Hdiff_psd_iff :
                  forall
                    (e : (S_ZE :\: [set Elbl]) :|:
                         (S_ZE :&: [set Elbl]) = S_ZE)
                    (sigma0 : 'F[HL]_(S_ZE :&: [set Elbl]))
                    (sigma : 'M[C]_Ebig),
                    castmx (HdimE_prod, HdimE_prod)
                      (h2mx (castlf (eqE_ZE, eqE_ZE) sigma0)) = sigma ->
                    ((castlf (e, e)
                        ((\1 : 'F[HL]_(S_ZE :\: [set Elbl])) \O sigma0)
                      - tauZEL) \is psdlf <->
                     ((1%:M : 'M[C]_nz) *t sigma - tauZpABR) \is psdmx).
              {
                move=> e sigma0 sigma Hsigma_cast.
                have Htarget_prod :
                    castmx (HdimZE_prod, HdimZE_prod)
                      (biprod_mx disZE
                        (castlf (e, e)
                          ((\1 : 'F[HL]_(S_ZE :\: [set Elbl])) \O sigma0))) =
                    (1%:M : 'M[C]_nz) *t sigma.
                {
                  rewrite (biprod_lift_mx disZE e
                    eqE_ZE).
                  rewrite HdimZE_cast_tensor.
                  by rewrite Hsigma_cast.
                }
                have Hdiff_prod :
                    castmx (HdimZE_prod, HdimZE_prod)
                      (biprod_mx disZE
                        (castlf (e, e)
                          ((\1 : 'F[HL]_(S_ZE :\: [set Elbl])) \O sigma0)
                         - tauZEL)) =
                    (1%:M : 'M[C]_nz) *t sigma - tauZpABR.
                  {
                    set aZE :=
                      castlf (e, e)
                        ((\1 : 'F[HL]_(S_ZE :\: [set Elbl])) \O sigma0).
                    have HbiprodB :
                        biprod_mx disZE (aZE - tauZEL) =
                        biprod_mx disZE aZE - biprod_mx disZE tauZEL.
                    {
                      rewrite /biprod_mx.
                      set Q_ZE :=
                        castmx _ (@tenv_mxU R _ HL [set Zlbl] [set Elbl]).
                      have Hh2B :
                          h2mx (aZE - tauZEL) = h2mx aZE - h2mx tauZEL.
                      {
                        exact: raddfB.
                      }
                      rewrite Hh2B.
                      have HcastB (M0 M1 : 'M[C]_(dim 'H[HL]_S_ZE)) :
                          castmx (tenv_dim disZE, tenv_dim disZE) (M0 - M1) =
                          castmx (tenv_dim disZE, tenv_dim disZE) M0 -
                          castmx (tenv_dim disZE, tenv_dim disZE) M1.
                      {
                        by case: _ / (tenv_dim disZE); rewrite castmx_id.
                      }
                      rewrite HcastB.
                      by rewrite mulmxBr mulmxBl.
                    }
                    have HcastZE_B
                        (M0 M1 : 'M[C]_(dim 'H[HL]_[set Zlbl] *
                                        dim 'H[HL]_[set Elbl])) :
                        castmx (HdimZE_prod, HdimZE_prod) (M0 - M1) =
                        castmx (HdimZE_prod, HdimZE_prod) M0 -
                        castmx (HdimZE_prod, HdimZE_prod) M1.
                    {
                      exact: raddfB.
                    }
                    rewrite HbiprodB HcastZE_B /aZE Htarget_prod
                      -/tauZEL_prod HtauZEL_prod.
                    done.
                  }
                have Hprod_psd_iff :
                    forall (x : 'F[HL]_S_ZE) (xm : 'M[C]_(nz * Ebig)),
                    castmx (HdimZE_prod, HdimZE_prod)
                      (biprod_mx disZE x) = xm ->
                    (x \is psdlf <-> xm \is psdmx).
                {
                  pose Q_ZE : 'M[C]_(dim 'H[HL]_[set Zlbl] *
                                      dim 'H[HL]_[set Elbl]) :=
                    castmx (tenv_dim disZE, erefl _)
                      (@tenv_mxU R _ HL [set Zlbl] [set Elbl]).
                  have HQ_ZE_t :
                      Q_ZE^*t =
                      castmx (erefl _, tenv_dim disZE)
                        (@tenv_mxU R _ HL [set Zlbl] [set Elbl])^*t.
                  {
                    rewrite /Q_ZE.
                    exact: (@castmx_mx_mxT _ _ (@adjmx _) _ _ _ _
                      (tenv_dim disZE, erefl _)
                      (@tenv_mxU R _ HL [set Zlbl] [set Elbl])).
                  }
                  have HQtQ_ZE : Q_ZE^*t *m Q_ZE = 1%:M.
                  {
                    rewrite /Q_ZE HQ_ZE_t mcextra.castmx_mul.
                    have HU :
                        (@tenv_mxU R _ HL [set Zlbl] [set Elbl])^*t *m
                        (@tenv_mxU R _ HL [set Zlbl] [set Elbl]) = 1%:M.
                    {
                      have := unitarymxK
                        (@tenv_mxU_adj_unitarymx R _ HL
                          [set Zlbl] [set Elbl] disZE).
                      by rewrite adjmxK.
                    }
                    rewrite HU.
                    by case: _ / (tenv_dim disZE); rewrite castmx_id.
                  }
                  have HQ_ZE_unit : Q_ZE \is unitarymx by apply/unitarymxPV.
                  have HQQt_ZE : Q_ZE *m Q_ZE^*t = 1%:M :=
                    unitarymxK HQ_ZE_unit.
                  move=> x xm Hxm; split.
                  - move=> Px.
                    rewrite -Hxm.
                    apply: castmx_sq_psdmx.
                    rewrite /biprod_mx -/Q_ZE.
                    have Praw :
                        castmx (tenv_dim disZE, tenv_dim disZE) (h2mx x)
                          \is psdmx.
                    {
                      rewrite -/(castmx_sq (tenv_dim disZE) (h2mx x)).
                      apply: castmx_sq_psdmx.
                      by move: Px; rewrite qualifE.
                    }
                    have Ptmp := psdmx_bimap_closed_gen Q_ZE^*t Praw.
                    by move: Ptmp; rewrite adjmxK.
                  - move=> Pxm.
                    have Pprod_cast :
                        castmx (HdimZE_prod, HdimZE_prod)
                          (biprod_mx disZE x) \is psdmx
                      by rewrite Hxm.
                    have Pprod :
                        biprod_mx disZE x \is psdmx.
                    {
                      have Pback :=
                        castmx_sq_psdmx (esym HdimZE_prod) Pprod_cast.
                      by move: Pback; rewrite /castmx_sq castmxK.
                    }
                    have Praw_cast :
                        castmx (tenv_dim disZE, tenv_dim disZE) (h2mx x)
                          \is psdmx.
                    {
                      have Pback := psdmx_bimap_closed_gen Q_ZE Pprod.
                      rewrite /biprod_mx -/Q_ZE in Pback.
                      have Hback :
                          Q_ZE *m
                            (Q_ZE^*t *m
                              castmx (tenv_dim disZE, tenv_dim disZE)
                                (h2mx x) *m Q_ZE) *m Q_ZE^*t =
                          castmx (tenv_dim disZE, tenv_dim disZE) (h2mx x).
                      {
                        by rewrite !mulmxA HQQt_ZE mul1mx
                          -!mulmxA HQQt_ZE mulmx1.
                      }
                      by move: Pback; rewrite Hback.
                    }
                    have Ph2 := castmx_sq_psdmx (esym (tenv_dim disZE))
                      Praw_cast.
                    by move: Ph2; rewrite /castmx_sq castmxK qualifE.
                }
                exact: Hprod_psd_iff Hdiff_prod.
              }
              move=> v0; split.
              - move=> [sigma [Psigma [Hdiff Hv]]].
                pose sigmaE : 'F[HL]_[set Elbl] :=
                  mx2h (castmx (esym HdimE_prod, esym HdimE_prod) sigma).
                pose sigma0 : 'F[HL]_(S_ZE :&: [set Elbl]) :=
                  castlf (esym eqE_ZE, esym eqE_ZE) sigmaE.
                rewrite /phi_min_feasible.
                exists sigma0; split.
                + rewrite /sigma0 castlf_psdlfE /sigmaE qualifE /= mx2hK.
                  rewrite -/(castmx_sq (esym HdimE_prod) sigma).
                  exact: castmx_sq_psdmx Psigma.
                + split.
                  * have Hsigma_cast :
                        castmx (HdimE_prod, HdimE_prod)
                          (h2mx (castlf (eqE_ZE, eqE_ZE) sigma0)) = sigma.
                    {
                      by rewrite /sigma0 castlfKV /sigmaE mx2hK castmxKV.
                    }
                    set ephi := (X in castlf (X, X) _).
                    move: (Hdiff_psd_iff ephi sigma0 sigma Hsigma_cast)
                      => [_ Hback].
                    exact: (Hback Hdiff).
                  * rewrite /sigma0 castlf_trlfE /sigmaE /lftrace /= mx2hK
                      mxtrace_castmx_sq.
                    exact: Hv.
              - rewrite /phi_min_feasible.
                move=> [sigma0 [Psigma0 [Hdiff Hv]]].
                set ephi := (X in
                  (castlf (X, X)
                    ((\1 : 'F[HL]_(S_ZE :\: [set Elbl])) \O sigma0)
                   - tauZEL) \is psdlf) in Hdiff.
                pose sigmaE : 'F[HL]_[set Elbl] :=
                  castlf (eqE_ZE, eqE_ZE) sigma0.
                pose sigma : 'M[C]_Ebig :=
                  castmx (HdimE_prod, HdimE_prod) (h2mx sigmaE).
                have Psigma : sigma \is psdmx.
                {
                  rewrite /sigma -/(castmx_sq HdimE_prod (h2mx sigmaE)).
                  apply: castmx_sq_psdmx.
                  have PsigmaE : sigmaE \is psdlf
                    by rewrite /sigmaE castlf_psdlfE.
                  by move: PsigmaE; rewrite qualifE.
                }
                exists sigma; split; first exact: Psigma.
                split.
                + have Hsigma_cast :
                      castmx (HdimE_prod, HdimE_prod)
                        (h2mx (castlf (eqE_ZE, eqE_ZE) sigma0)) = sigma.
                  {
                    by rewrite /sigma /sigmaE.
                  }
                  move: (Hdiff_psd_iff ephi sigma0 sigma Hsigma_cast)
                    => [Hfwd _].
                  exact: (Hfwd Hdiff).
                + rewrite /sigma mxtrace_castmx_sq /sigmaE
                    -/(\Tr (castlf _ sigma0)) castlf_trlfE.
                  exact: Hv.
            }
            symmetry.
            rewrite /hmin_mx /hmin /phi_min.
            congr (- log2 _).
            congr inf.
            apply/funext=> v0.
            apply/propext.
            exact: Hphi_feasible_eq.
          }
          have Hmax_bridge :
              hmax [set Clbl] tauZL <= hmax_mx tau.
          {
            (* Product-coordinate max bridge for tau_ZC.  This is one-way:
               each labelled fidelity witness is a matrix generalized-
               fidelity witness, because fidelity <= gfidelity. *)
            have HdimZC_prod :
                (dim 'H[HL]_[set Zlbl] * dim 'H[HL]_[set Clbl] =
                 nz * nc)%N.
            {
              by rewrite -(dim_set1 HL Zlbl) -(dim_set1 HL Clbl) HHLZ HHLC.
            }
            pose tauZL_prod : 'M[C]_(nz * nc) :=
              castmx (HdimZC_prod, HdimZC_prod)
                (biprod_mx disZC tauZL).
            have HtauZL_prod : tauZL_prod = tau.
            {
              have HtauZL_cast : tauZL = ptrace_cast disZC_E tauL3.
              {
                rewrite /tauZL /ptrace_cast /ptrace_cast3C
                  /ptrace_cast_gen.
                have Hdu :
                    setDU3_C disZE disCE = setDU_r disZC_E :=
                  eq_irrelevance _ _.
                by rewrite Hdu.
              }
              rewrite /tauZL_prod /biprod_mx
                HtauZL_cast.
              rewrite (h2mx_ptrace_cast_ptrace2 disZC_E tauL3).
              have Hprod_ptr :
                  castmx (HdimZC_prod, HdimZC_prod)
                    ((let Q :=
                        castmx
                          (tenv_dim disZC,
                           erefl (dim 'H[HL]_[set Zlbl] *
                                  dim 'H[HL]_[set Clbl]))
                          (@tenv_mxU R _ HL [set Zlbl] [set Clbl]) in
                      Q^*t *m
                      castmx (tenv_dim disZC, tenv_dim disZC)
                        (ptrace2
                          ((@tenv_mxU R _ HL
                              ([set Zlbl] :|: [set Clbl]) [set Elbl])^*t *m
                            h2mx tauL3 *m
                            @tenv_mxU R _ HL
                              ([set Zlbl] :|: [set Clbl]) [set Elbl])) *m Q)) =
                  ptrace2 tauZC_big.
              {
                rewrite -/Q_ZC -/U_ZCE.
                have Hinner_cast_ptr :
                    castmx (tenv_dim disZC, tenv_dim disZC)
                      (ptrace2 tau_inner_labelled) =
                    ptrace2
                      ((Q_ZC *t I_E) *m
                        (tau_raw_prod *m (Q_ZC^*t *t I_E))).
                {
                  have Hptrace2_cast_left :
                      forall m m' n (em : m = m') (A : 'M[C]_(m' * n)),
                      castmx (em, em)
                        (ptrace2
                          (castmx
                            (esym (f_equal (fun k => (k * n)%N) em),
                             esym (f_equal (fun k => (k * n)%N) em)) A)) =
                      ptrace2 A.
                  {
                    move=> m m' n em A.
                    by case: m' / em A => A; rewrite castmx_id.
                  }
                  rewrite /tau_inner_labelled.
                  have Hcol_eq :
                      HdimZCE_col =
                      f_equal (fun n => (n * dim 'H[HL]_[set Elbl])%N)
                        (tenv_dim disZC) := eq_irrelevance _ _.
                  rewrite Hcol_eq.
                  transitivity
                    (ptrace2 (((Q_ZC *t I_E) *m tau_raw_prod) *m
                      (Q_ZC^*t *t I_E))).
                  - exact: Hptrace2_cast_left.
                  - by rewrite mulmxA.
                }
                have Houter_unit_ptr :
                    castmx (tenv_dim disZC, tenv_dim disZC)
                      (ptrace2
                        (U_ZCE^*t *m h2mx tauL3 *m U_ZCE)) =
                    ptrace2
                      ((Q_ZC *t I_E) *m
                        (tau_raw_prod *m (Q_ZC^*t *t I_E))).
                {
                  have HUtU_ZCE : U_ZCE^*t *m U_ZCE = 1%:M.
                  {
                    have := unitarymxK
                      (@tenv_mxU_adj_unitarymx R _ HL S_ZC
                        [set Elbl] disZC_E).
                    by rewrite /U_ZCE adjmxK.
                  }
                  rewrite /tauL3 mx2hK /tau_prod_labelled.
                  rewrite !mulmxA HUtU_ZCE mul1mx -!mulmxA HUtU_ZCE
                    mulmx1.
                  exact: Hinner_cast_ptr.
                }
                have Hptr_inner :
                    ptrace2
                      ((Q_ZC *t I_E) *m
                        (tau_raw_prod *m (Q_ZC^*t *t I_E))) =
                    Q_ZC *m ptrace2 tau_raw_prod *m Q_ZC^*t.
                {
                  by rewrite mulmxA /I_E ptrace2_mulmxI ptrace2_mulImx.
                }
                have Hraw_ptr_cast :
                    castmx (HdimZC_prod, HdimZC_prod)
                      (ptrace2 tau_raw_prod) =
                    ptrace2 tauZC_big.
                {
                  have Hptrace2_cast_both :
                      forall m m' n n' (em : m = m') (en : n = n')
                        (A : 'M[C]_(m' * n')),
                      castmx (em, em)
                        (ptrace2
                          (castmx (esym (f_equal2 muln em en),
                                   esym (f_equal2 muln em en)) A)) =
                      ptrace2 A.
                  {
                    move=> m m' n n' em en A.
                    case: m' / em in A *.
                    case: n' / en in A *.
                    rewrite (eq_irrelevance
                      (f_equal2 muln (erefl m) (erefl n))
                      (erefl (m * n)%N)).
                    by rewrite castmx_id.
                  }
                  rewrite /tau_raw_prod.
                  have HdimE_prod : dim 'H[HL]_[set Elbl] = Ebig.
                  {
                    by rewrite -(dim_set1 HL Elbl) HHLE.
                  }
                  have Hraw_eq :
                      HdimZCE_raw =
                      f_equal2 muln HdimZC_prod HdimE_prod :=
                    eq_irrelevance _ _.
                  rewrite Hraw_eq.
                  exact: Hptrace2_cast_both.
                }
                rewrite Houter_unit_ptr Hptr_inner.
                have Hcancel_ZC :
                    Q_ZC^*t *m
                      (Q_ZC *m ptrace2 tau_raw_prod *m Q_ZC^*t) *m
                      Q_ZC =
                    ptrace2 tau_raw_prod.
                {
                  by rewrite !mulmxA HQtQ_ZC mul1mx -!mulmxA HQtQ_ZC
                    mulmx1.
                }
                change (castmx (HdimZC_prod, HdimZC_prod)
                  (Q_ZC^*t *m
                    (Q_ZC *m ptrace2 tau_raw_prod *m Q_ZC^*t) *m Q_ZC) =
                  ptrace2 tauZC_big).
                rewrite Hcancel_ZC.
                exact: Hraw_ptr_cast.
              }
              by rewrite Hprod_ptr HtauZC_big_ptr.
            }
            (* Encoding bridge only: EUR's proof uses the ZC max marginal;
               this identifies the labelled marginal with product matrix
               coordinates for the Tomamichel hmax definition. *)
            have HdimZ_prod : dim 'H[HL]_[set Zlbl] = nz.
            {
              by rewrite -(dim_set1 HL Zlbl) HHLZ.
            }
            have HdimC_prod : dim 'H[HL]_[set Clbl] = nc.
            {
              by rewrite -(dim_set1 HL Clbl) HHLC.
            }
            have HtauZL_cast : tauZL = ptrace_cast disZC_E tauL3.
            {
              rewrite /tauZL /ptrace_cast /ptrace_cast3C /ptrace_cast_gen.
              have Hdu :
                  setDU3_C disZE disCE = setDU_r disZC_E :=
                eq_irrelevance _ _.
              by rewrite Hdu.
            }
            have HtauZL_psd : tauZL \is psdlf.
            {
              rewrite HtauZL_cast.
              exact: ptrace_cast_psdlf HtauL3_psd.
            }
            have Hproduct_hmax :
                hmax [set Clbl] tauZL =
                hmax_mx (biprod_mx disZC tauZL)
              by exact: (hmax_labelled_product_mx
                (A := [set Zlbl]) (B := [set Clbl])
                disZC HtauZL_psd).
            have Hmatrix_hmax :
                hmax_mx (biprod_mx disZC tauZL) =
                hmax_mx tau.
            {
              have Hcast_hmax :
                  forall nZ nC
                    (eZ : dim 'H[HL]_[set Zlbl] = nZ)
                    (eC : dim 'H[HL]_[set Clbl] = nC)
                    (X : 'M[C]_(dim 'H[HL]_[set Zlbl] *
                                dim 'H[HL]_[set Clbl])),
                    hmax_mx X =
                    hmax_mx (castmx (f_equal2 muln eZ eC,
                                      f_equal2 muln eZ eC) X).
              {
                move=> nZ nC eZ eC X.
                case: nZ / eZ in X *.
                case: nC / eC in X *.
                rewrite (eq_irrelevance
                  (f_equal2 muln (erefl _) (erefl _)) (erefl _)).
                congr hmax_mx.
              }
              rewrite -HtauZL_prod /tauZL_prod.
              have Hdim_prod_eq :
                  HdimZC_prod = f_equal2 muln HdimZ_prod HdimC_prod
                := eq_irrelevance _ _.
              rewrite Hdim_prod_eq.
              exact: Hcast_hmax.
            }
            by rewrite Hproduct_hmax Hmatrix_hmax.
          }
          have Hphi_pos_trace :
              forall (S T : {set 'I_5}) (x : 'F[HL]_S),
              x \is psdlf -> @complex.Re R (\Tr x) <= 1 ->
              0 < @complex.Re R (\Tr x) -> 0 < phi_min T x.
          {
            move=> S T x Px Hx_tr Hx_tr_pos.
            have eqST : (S :\: T) :|: (S :&: T) = S.
              by rewrite finset.setUC finset.setID.
            have disSplit : [disjoint (S :\: T) & (S :&: T)].
            { apply/disjointP=> z; rewrite !inE.
              by case: (z \in T); rewrite ?andbF ?andbT. }
            pose dT : R := (dim 'H[HL]_(S :\: T))%:R.
            have HdT_pos : 0 < dT by rewrite /dT ltr0n dim_proper.
            rewrite /phi_min.
            apply: (@lt_le_trans _ _ ((@complex.Re R (\Tr x)) / dT)).
            - by apply: divr_gt0.
            - apply: lb_le_inf.
              + pose sigma1 : 'F[HL]_(S :&: T) := \1.
                exists (@complex.Re R (\Tr sigma1)).
                rewrite /phi_min_feasible.
                exists sigma1; split.
                { by rewrite qualifE h2mx1; apply: psdmx1. }
                split; last by [].
                rewrite sdotf11 castlf1.
                have Hx_den : x \is denlf.
                { apply/denlfP; split=> //.
                  have Hreal : \Tr x \is Num.real :=
                    ger0_real (psdlf_trlf Px).
                  by rewrite -(RRe_real Hreal) lecR. }
                have Hx_le1 : x ⊑ (\1 : 'F[HL]_S)
                  := denf_le1 (DenLf_Build Hx_den).
                by move: Hx_le1; rewrite lefE.
              + move=> v0 [sigma [Psigma [Hfeas ->]]].
                have Htr_sigma_real :
                    (\Tr sigma : C) = (@complex.Re R (\Tr sigma))%:C
                  by rewrite RRe_real // ger0_real // psdlf_trlf.
                have Hx_tr_real :
                    (\Tr x : C) = (@complex.Re R (\Tr x))%:C
                  by rewrite RRe_real // ger0_real // psdlf_trlf.
                  have Hx_leC :
                      \Tr x <= (dim 'H[HL]_(S :\: T))%:R * \Tr sigma.
                  { have Hgap_nonneg := psdlf_trlf Hfeas.
                    set liftST := (X0 in \Tr (X0 - x)) in Hgap_nonneg.
                    have Htr_gap :
                        \Tr (liftST - x) = \Tr liftST - \Tr x.
                    {
                      have HlinTr := @lftrace_is_linear R ('H[HL]_S).
                      have Htr := HlinTr (-1 : C) x liftST.
                      rewrite !scaleN1r !mulN1r in Htr.
                      rewrite [\Tr liftST - \Tr x]addrC -Htr.
                      by rewrite [liftST - x]addrC.
                    }
                    move: Hgap_nonneg.
                    rewrite Htr_gap /liftST castlf_trlfE
                      (trlf_lift_I disSplit).
                    by rewrite subr_ge0. }
                move: Hx_leC; rewrite Hx_tr_real Htr_sigma_real.
                rewrite /dT -natrC -rmorphM /= lecR => Hx_leR.
                rewrite ler_pdivrMr //.
                by rewrite mulrC.
          }
            have HtauL3_ne0 : tauL3 != 0.
            { apply/negP=> /eqP HtauL3_eq0.
              move: HtauL3_rank.
              by rewrite HtauL3_eq0 /lfrank h2mx0 mxrank0. }
          have HtauL3_tr_pos_C : (0 : C) < \Tr tauL3.
          { rewrite lt_def psdlf_trlf // andbT.
            apply/negP=> /eqP Htr0.
            apply/negP: HtauL3_ne0; rewrite negbK.
            have HtauL3_ge0 : 0 ⊑ tauL3.
              by move: HtauL3_psd; rewrite psdlfE.
            apply/trlf0_eq0.
            exact: (conj HtauL3_ge0 Htr0). }
          have HtauL3_tr_pos : 0 < @complex.Re R (\Tr tauL3).
          { have Hreal : \Tr tauL3 \is Num.real :=
              ger0_real (psdlf_trlf HtauL3_psd).
            by move: HtauL3_tr_pos_C; rewrite -{1}(RRe_real Hreal) ltcR. }
          have HtauZL_psd_dual : tauZL \is psdlf
            by rewrite /tauZL; exact: ptrace_cast_gen_psdlf.
          have HtauZL_tr_eq_dual : \Tr tauZL = \Tr tauL3.
          { rewrite /tauZL /ptrace_cast3C /ptrace_cast_gen castlf_trlfE.
            have /cptpP [_ /tpmapP Htp] :=
              @ptraceso_qc R _ HL [set Elbl] S_ZCE3.
            exact: Htp. }
          have HtauZL_tr_le_dual : @complex.Re R (\Tr tauZL) <= 1
            by rewrite HtauZL_tr_eq_dual.
          have HtauZL_tr_pos_dual : 0 < @complex.Re R (\Tr tauZL)
            by rewrite HtauZL_tr_eq_dual.
          have HtauZEL_psd_dual : tauZEL \is psdlf
            by rewrite /tauZEL; exact: ptrace_cast_gen_psdlf.
          have HtauZEL_tr_eq_dual : \Tr tauZEL = \Tr tauL3.
          { rewrite /tauZEL /ptrace_cast3B /ptrace_cast_gen castlf_trlfE.
            have /cptpP [_ /tpmapP Htp] :=
              @ptraceso_qc R _ HL [set Clbl] S_ZCE3.
            exact: Htp. }
          have HtauZEL_tr_le_dual : @complex.Re R (\Tr tauZEL) <= 1
            by rewrite HtauZEL_tr_eq_dual.
          have HtauZEL_tr_pos_dual : 0 < @complex.Re R (\Tr tauZEL)
            by rewrite HtauZEL_tr_eq_dual.
          have HtauZEL_phi_pos_dual :
              0 < phi_min [set Elbl] tauZEL
            := Hphi_pos_trace _ _ _ HtauZEL_psd_dual
                 HtauZEL_tr_le_dual HtauZEL_tr_pos_dual.
          have HtauZL_hmaxE_fin :
              hmaxE [set Clbl] tauZL = (hmax [set Clbl] tauZL)%:E
            := @hmaxE_EFin R _ HL S_ZC [set Clbl] tauZL
                 HtauZL_psd_dual HtauZL_tr_le_dual HtauZL_tr_pos_dual.
          have HtauZEL_hminE_fin :
              hminE [set Elbl] tauZEL = (hmin [set Elbl] tauZEL)%:E
            := @hminE_EFin R _ HL ([set Zlbl] :|: [set Elbl])
                 [set Elbl] tauZEL HtauZEL_phi_pos_dual.
          have Hlabelled_dual_real :
              hmax [set Clbl] tauZL = - hmin [set Elbl] tauZEL.
          { move: Hlabelled_dual.
            rewrite -/tauZL -/tauZEL HtauZL_hmaxE_fin
              HtauZEL_hminE_fin EFinN.
            by case. }
            exists (hmax [set Clbl] tauZL), (hmin [set Elbl] tauZEL).
            split; first exact: Hlabelled_dual_real.
            by split.
          }
        move: Hdual_lift => [hmax_lbl [hmin_lbl [Hdual_eq [Hmin_eq Hmax_le]]]].
        rewrite -Hmin_eq -Hdual_eq.
        exact: Hmax_le.
      }
      have Htransport_tau :
          - log2 (overlap_mx M N) <=
          hmin_mx tauXB + - hmin_mx tauZpABR.
      {
        (* TeX eqn:mo6/eqn:mo9/eqn:mo10: transport every
           Z|Z'ABR min-entropy witness through W := U V^dagger,
           trace out X'A, then trace out R to weaken back to XB. *)
        pose c0 := overlap_mx M N.
        have Hc0_ge0 : 0 <= c0.
        {
          rewrite /c0 /overlap_mx.
          by apply/bigmax_geP; left.
        }
        have Hc0_pos : 0 < c0.
        {
          rewrite lt_def Hc0_ge0 andbT.
          by rewrite /c0 Hoverlap.
        }
        pose SX : set R := [set v : R | exists sigmaB : 'M[C]_nb,
          sigmaB \is psdmx /\
          ((1%:M : 'M[C]_nx) *t sigmaB - tauXB) \is psdmx /\
          v = @complex.Re R (\tr sigmaB)]%classic.
        pose SZ : set R := [set v : R | exists sigmaE : 'M[C]_Ebig,
          sigmaE \is psdmx /\
          ((1%:M : 'M[C]_nz) *t sigmaE - tauZpABR) \is psdmx /\
          v = @complex.Re R (\tr sigmaE)]%classic.
        have HRe_realM : forall (cc : R) (zz : C),
            @complex.Re R (cc%:C * zz) = cc * @complex.Re R zz.
        { move=> cc zz; case: zz => a b /=. by rewrite mul0r subr0. }
        have HtensmxZr_local :
            forall m n (k : C) (A : 'M[C]_m) (B : 'M[C]_n),
            A *t (k *: B) = k *: (A *t B).
        {
          move=> m n k A B.
          by rewrite -[k *: B]addr0 (linear_tensmx A) linear0r addr0.
        }
        have Hfeas_transport_tau :
            forall sigmaE : 'M[C]_Ebig,
            sigmaE \is psdmx ->
            ((1%:M : 'M[C]_nz) *t sigmaE - tauZpABR) \is psdmx ->
            (c0%:C *: ((1%:M : 'M[C]_nx) *t
                ptrace2 (ptrace1 (castmx_sq HEbig_BR sigmaE))) - tauXB)
              \is psdmx.
        {
          move=> sigmaE Hsigma_psd Hsigma_feas.
          pose sigmaZpA_BR : 'M[C]_(nz * na * nBR) :=
            castmx_sq HEbig_BR sigmaE.
          pose sigmaBR : 'M[C]_nBR := ptrace1 sigmaZpA_BR.
          have HsigmaZpA_BR_psd : sigmaZpA_BR \is psdmx.
          {
            rewrite /sigmaZpA_BR.
            exact: castmx_sq_psdmx Hsigma_psd.
          }
          have HsigmaZpA_BR_feas :
              ((1%:M : 'M[C]_nz) *t sigmaZpA_BR - tauZpA_BR) \is psdmx.
          {
            have Hcast_tens :
                (1%:M : 'M[C]_nz) *t sigmaZpA_BR =
                castmx_sq HtauZE_dim
                  ((1%:M : 'M[C]_nz) *t sigmaE).
            {
              have Hcast_e : forall (z0 : 'I_nz) (e0 : 'I_(nz * na * nBR)),
                  cast_ord (esym HtauZE_dim) (mxtens_index (z0, e0)) =
                  mxtens_index (z0, cast_ord (esym HEbig_BR) e0).
              {
                move=> z0 [e0 He0]; apply/val_inj=> /=.
                rewrite /Ebig /nBR /=.
                by rewrite -[nz * na * nb * Rdim]mulnA.
              }
              apply/matrixP=> i j.
              case: (mxtens_indexP i)=> zi ei.
              case: (mxtens_indexP j)=> zj ej.
              rewrite tensmxE /sigmaZpA_BR /castmx_sq !castmxE /=.
              by rewrite Hcast_e Hcast_e tensmxE !mxE.
            }
            have -> :
                (1%:M : 'M[C]_nz) *t sigmaZpA_BR - tauZpA_BR =
                castmx_sq HtauZE_dim
                  ((1%:M : 'M[C]_nz) *t sigmaE - tauZpABR).
            {
              by rewrite /tauZpA_BR Hcast_tens /castmx_sq -linearB.
            }
            exact: castmx_sq_psdmx Hsigma_feas.
          }
          have HptraceXA_BR_le :
              forall A B : 'M[C]_(((nx * nx) * na) * nBR),
              A <= B -> ptraceXA_BR A <= ptraceXA_BR B.
          {
            move=> A B.
            rewrite /ptraceXA_BR !le_lownerE -!linearB /=.
            move=> Hdiff.
            apply: mxswap_psdmx.
            apply: ptrace2_psd.
            apply: castmx_sq_psdmx.
            exact: mxswap_psdmx Hdiff.
          }
          have Hbase_le :
              tauZZpABR3 <=
              castmx_sq (esym Hzz_dim_BR)
                ((1%:M : 'M[C]_nz) *t sigmaZpA_BR).
          {
            rewrite !le_lownerE /tauZZpABR3.
            have Hcast_diff :
                castmx_sq (esym Hzz_dim_BR)
                  ((1%:M : 'M[C]_nz) *t sigmaZpA_BR) -
                castmx_sq (esym Hzz_dim_BR) tauZpA_BR =
                castmx_sq (esym Hzz_dim_BR)
                  ((1%:M : 'M[C]_nz) *t sigmaZpA_BR - tauZpA_BR).
            {
              by rewrite /castmx_sq linearB.
            }
            by rewrite Hcast_diff; exact: castmx_sq_psdmx HsigmaZpA_BR_feas.
          }
          have Hconj_le :
              WBR *m tauZZpABR3 *m WBR^*t <=
              WBR *m castmx_sq (esym Hzz_dim_BR)
                ((1%:M : 'M[C]_nz) *t sigmaZpA_BR) *m WBR^*t.
          {
            move: Hbase_le; rewrite !le_lownerE => Hdiff.
            have -> :
                WBR *m castmx_sq (esym Hzz_dim_BR)
                  ((1%:M : 'M[C]_nz) *t sigmaZpA_BR) *m WBR^*t -
                WBR *m tauZZpABR3 *m WBR^*t =
                WBR *m (castmx_sq (esym Hzz_dim_BR)
                  ((1%:M : 'M[C]_nz) *t sigmaZpA_BR) - tauZZpABR3) *m WBR^*t.
            {
              by rewrite mulmxBr mulmxBl.
            }
            exact: psdmx_bimap_closed_gen Hdiff.
          }
          have Hmo9 :
              ptraceXA_BR
                (WBR *m castmx_sq (esym Hzz_dim_BR)
                  ((1%:M : 'M[C]_nz) *t sigmaZpA_BR) *m WBR^*t)
              <= c0%:C *: ((1%:M : 'M[C]_nx) *t sigmaBR).
          {
            pose S_xz (ix : 'I_nx) (jz : 'I_nz) : 'M[C]_na :=
              sqrtmx (M ix) *m sqrtmx (N jz).
            have H_SdagS_le : forall (ix : 'I_nx) (jz : 'I_nz),
                (S_xz ix jz)^*t *m S_xz ix jz <=
                c0%:C *: (1%:M : 'M[C]_na).
            {
              move=> ix jz.
              rewrite /S_xz /c0.
              have HsqrtN :
                  (sqrtmx (N jz))^*t = sqrtmx (N jz).
              {
                have HNz : N jz \is psdmx by exact: is_povm_mx_psd HN.
                by apply/esym/hermmxP; exact: sqrtmx_herm (psdmx_herm HNz).
              }
              have HsqrtM :
                  (sqrtmx (M ix))^*t *m sqrtmx (M ix) = M ix.
              {
                have HMx : M ix \is psdmx by exact: is_povm_mx_psd HM.
                have HsqrtM_adj :
                    (sqrtmx (M ix))^*t = sqrtmx (M ix).
                {
                  by apply/esym/hermmxP; exact: sqrtmx_herm (psdmx_herm HMx).
                }
                by rewrite HsqrtM_adj sqrtmxK.
              }
              have Hprod :
                  (sqrtmx (M ix) *m sqrtmx (N jz))^*t *m
                    (sqrtmx (M ix) *m sqrtmx (N jz)) =
                  sqrtmx (N jz) *m M ix *m sqrtmx (N jz).
              {
                set SM := sqrtmx (M ix).
                set SN := sqrtmx (N jz).
                have HSN : SN^*t = SN by rewrite /SN.
                have HSM : SM^*t *m SM = M ix by rewrite /SM.
                rewrite -/SM -/SN adjmxM HSN -mulmxA.
                rewrite [SM^*t *m (SM *m SN)]mulmxA HSM.
                by rewrite mulmxA.
              }
              rewrite Hprod.
              exact: sqrtmx_prod_overlap_bound ix jz HM HN.
            }
            (* TeX eqn:mo8: expand WBR(I_Z ⊗ sigma)WBR† after tracing out X'A. *)
            have Hmo8_expand :
                ptraceXA_BR
                  (WBR *m castmx_sq (esym Hzz_dim_BR)
                    ((1%:M : 'M[C]_nz) *t sigmaZpA_BR) *m WBR^*t) <=
                c0%:C *: ((1%:M : 'M[C]_nx) *t sigmaBR).
            {
              pose sigma_cast : 'M[C]_(nz * (na * nBR)) :=
                castmx_sq (esym (mulnA nz na nBR)) sigmaZpA_BR.
              pose sigma_block (jz : 'I_nz) : 'M[C]_(na * nBR) :=
                \matrix_(i, j)
                  sigma_cast (mxtens_index (jz, i)) (mxtens_index (jz, j)).
              have Hsigma_cast_psd : sigma_cast \is psdmx.
              {
                by rewrite /sigma_cast; exact: castmx_sq_psdmx HsigmaZpA_BR_psd.
              }
              have Hsigma_block_psd : forall jz, sigma_block jz \is psdmx.
              {
                move=> jz.
                pose Pj : 'M[C]_(na * nBR, nz * (na * nBR)) :=
                  \matrix_(i, r)
                    if r == mxtens_index (jz, i) then 1 else 0.
                suff -> : sigma_block jz = Pj *m sigma_cast *m Pj^*t.
                {
                  exact: psdmx_bimap_closed_gen Hsigma_cast_psd.
                }
                have Pj_entry : forall a b,
                    Pj a b =
                    (if b == mxtens_index (jz, a) then 1 else 0 : C).
                {
                  by move=> a b; rewrite /Pj mxE.
                }
                have adjPj_entry : forall a b,
                    (Pj^*t) a b =
                    (if a == mxtens_index (jz, b) then 1 else 0 : C).
                {
                  move=> a b.
                  by rewrite !mxE; case: eqP => _; rewrite ?conjC1 ?conjC0.
                }
                apply/matrixP=> i j.
                rewrite /sigma_block mxE mxE.
                rewrite (bigD1 (mxtens_index (jz, j))) //= big1.
                2: by move=> k Hk; rewrite adjPj_entry (negPf Hk) mulr0.
                rewrite addr0 adjPj_entry eqxx mulr1 mxE.
                rewrite (bigD1 (mxtens_index (jz, i))) //= big1.
                2: by move=> r Hr; rewrite Pj_entry (negPf Hr) mul0r.
                by rewrite Pj_entry eqxx mul1r addr0.
              }
              have Hblock_expand :
                  ptraceXA_BR
                    (WBR *m castmx_sq (esym Hzz_dim_BR)
                      ((1%:M : 'M[C]_nz) *t sigmaZpA_BR) *m WBR^*t) =
                  \sum_(ix : 'I_nx) \sum_(jz : 'I_nz)
                    (delta_mx ix ix : 'M[C]_nx) *t
                    ptrace1
                      ((S_xz ix jz *t (1%:M : 'M[C]_nBR)) *m
                        sigma_block jz *m
                         ((S_xz ix jz)^*t *t (1%:M : 'M[C]_nBR))).
                {
                have Hsqrt_herm_N : forall jz0 : 'I_nz,
                    (sqrtmx (N jz0))^*t = sqrtmx (N jz0).
                {
                  move=> jz0.
                  have HNz : N jz0 \is psdmx by exact: is_povm_mx_psd HN.
                  by apply/esym/hermmxP; exact: sqrtmx_herm (psdmx_herm HNz).
                }
                have Hstinespring_mul_entry :
                    forall (ix0 x2 : 'I_nx) (jz0 z2 : 'I_nz)
                      (a1 a2 : 'I_na),
                    (stinespring_U2 M *m (stinespring_U2 N)^*t)
                      (mxtens_index (mxtens_index (ix0, x2), a1))
                      (mxtens_index (mxtens_index (jz0, z2), a2)) =
                    (ix0 == x2)%:R * (jz0 == z2)%:R *
                    (sqrtmx (M ix0) *m (sqrtmx (N jz0))^*t) a1 a2.
                {
                  move=> ix0 x2 jz0 z2 a1 a2.
                  rewrite mxE.
                  have HU : forall p q k (a : 'I_na),
                      stinespring_U2 M
                        (mxtens_index (mxtens_index (p, q), k)) a =
                      (if p == q then sqrtmx (M p) k a else 0).
                  {
                    move=> p q k a.
                    rewrite /stinespring_U2 mxE !mxtens_indexK.
                    cbv iota zeta beta.
                    by case: (p == q); rewrite ?mul1r ?mul0r.
                  }
                  have HV : forall a p q k,
                      ((stinespring_U2 N)^*t) a
                        (mxtens_index (mxtens_index (p, q), k)) =
                      (if p == q then sqrtmx (N p) k a else 0)^*.
                  {
                    move=> a p q k.
                    rewrite !mxE /stinespring_U2 !mxtens_indexK /=.
                    case Hpq: (p == q).
                    - rewrite /= mul1r.
                      by rewrite mxE.
                    - by rewrite /= mul0r conjC0 ?oppr0.
                  }
                  case Hx: (ix0 == x2); case Hz: (jz0 == z2);
                    rewrite /nat_of_bool /= ?mulr0 ?mul0r ?mulr1 ?mul1r.
                  - rewrite mxE.
                    apply: eq_bigr=> a _.
                    by rewrite HU HV Hx Hz adjmxE !mxE.
                  - apply: big1=> a _.
                    by rewrite HU HV Hx Hz conjC0 mulr0.
                  - apply: big1=> a _.
                    by rewrite HU HV Hx Hz mul0r.
                  - apply: big1=> a _.
                    by rewrite HU HV Hx Hz mul0r.
                }
                have ptraceXA_BRE :
                    forall (rho' : 'M[C]_(nx * nx * na * nBR))
                      (ix0 : 'I_nx) (ib : 'I_nBR)
                      (jx : 'I_nx) (jb : 'I_nBR),
                    ptraceXA_BR rho' (mxtens_index (ix0, ib))
                      (mxtens_index (jx, jb)) =
                    \sum_(x2 : 'I_nx) \sum_(a0 : 'I_na)
                      rho'
                        (mxtens_index (mxtens_index (mxtens_index (ix0, x2), a0), ib))
                        (mxtens_index (mxtens_index (mxtens_index (jx, x2), a0), jb)).
                {
                  move=> rho' ix0 ib jx jb.
                  rewrite /ptraceXA_BR /=.
                  rewrite mxE !mxtens_indexK /=.
                  rewrite ptrace2E1 ptrace1E mxtens_index_pairV.
                  apply: eq_bigr=> x2 _.
                  apply: eq_bigr=> a0 _.
                  rewrite mxE !mxtens_indexK /= /castmx_sq castmxE /=.
                  have Hcast_a4 : forall (bb : 'I_nBR)
                      (xx1 xx2 : 'I_nx) (aa : 'I_na),
                      cast_ord (esym HptraceXA_dim_BR)
                        (mxtens_index (mxtens_index (bb, xx1),
                          mxtens_index (xx2, aa))) =
                      mxtens_index (bb, mxtens_index
                        (mxtens_index (xx1, xx2), aa)).
                  {
                    move=> bb xx1 xx2 aa.
                    apply/val_inj=> /=.
                    by rewrite !mulnDl !mulnA !addnA.
                  }
                  by rewrite !Hcast_a4 mxE !mxtens_indexK.
                }
                have WE : forall (ix0 x2' : 'I_nx) (a0 : 'I_na) (bv : 'I_nBR)
                           (jz0 z2 : 'I_nz) (c1 : 'I_na) (dv : 'I_nBR),
                    WBR (mxtens_index (mxtens_index (mxtens_index (ix0, x2'), a0), bv))
                      (mxtens_index (mxtens_index (mxtens_index (jz0, z2), c1), dv)) =
                    (ix0 == x2')%:R * (jz0 == z2)%:R *
                    S_xz ix0 jz0 a0 c1 * (bv == dv)%:R.
                {
                  move=> ix0 x2' a0 bv jz0 z2 c1 dv.
                  rewrite /WBR /W0 /partial_iso_W tensmxE.
                  rewrite Hstinespring_mul_entry Hsqrt_herm_N.
                  rewrite /S_xz.
                  by rewrite [1%:M bv dv]mxE.
                }
                have ME : forall (j1 j2 : 'I_nz) (c1 : 'I_na) (d1 : 'I_nBR)
                           (k1 k2 : 'I_nz) (c2 : 'I_na) (d2 : 'I_nBR),
                    (castmx_sq (esym Hzz_dim_BR)
                      ((1%:M : 'M[C]_nz) *t sigmaZpA_BR))
                      (mxtens_index (mxtens_index (mxtens_index (j1, j2), c1), d1))
                      (mxtens_index (mxtens_index (mxtens_index (k1, k2), c2), d2)) =
                    (j1 == k1)%:R *
                    sigmaZpA_BR (mxtens_index (mxtens_index (j2, c1), d1))
                              (mxtens_index (mxtens_index (k2, c2), d2)).
                {
                  move=> j1 j2 c1 d1 k1 k2 c2 d2.
                  have Hcast_z : forall (jj1 jj2 : 'I_nz)
                      (cc : 'I_na) (dd : 'I_nBR),
                      cast_ord Hzz_dim_BR
                        (mxtens_index
                          (mxtens_index (mxtens_index (jj1, jj2), cc), dd)) =
                      mxtens_index (jj1, mxtens_index
                        (mxtens_index (jj2, cc), dd)).
                  {
                    move=> jj1 jj2 cc dd.
                    apply/val_inj=> /=.
                    by rewrite !mulnDl !mulnA !addnA.
                  }
                  rewrite /castmx_sq castmxE /=.
                  rewrite (eq_irrelevance (esym (esym Hzz_dim_BR)) Hzz_dim_BR).
                  by rewrite !Hcast_z tensmxE !mxE.
                }
                have sigma_blockE : forall (jz0 : 'I_nz)
                      (c1 : 'I_na) (d1 : 'I_nBR)
                      (c2 : 'I_na) (d2 : 'I_nBR),
                    sigma_block jz0 (mxtens_index (c1, d1))
                      (mxtens_index (c2, d2)) =
                    sigmaZpA_BR (mxtens_index (mxtens_index (jz0, c1), d1))
                              (mxtens_index (mxtens_index (jz0, c2), d2)).
                {
                  move=> jz0 c1 d1 c2 d2.
                  rewrite /sigma_block /sigma_cast mxE /castmx_sq castmxE /=.
                  have Hcast_assoc' : forall (z : 'I_nz) (a : 'I_na) (b : 'I_nBR),
                      cast_ord (esym (esym (mulnA nz na nBR)))
                        (mxtens_index (z, mxtens_index (a, b))) =
                      mxtens_index (mxtens_index (z, a), b).
                  {
                    move=> z a b.
                    apply/val_inj=> /=.
                    by rewrite mulnDl mulnA addnA.
                  }
                  by rewrite !Hcast_assoc'.
                }
                have adjmxE' : forall m n (A : 'M[C]_(m, n))
                    (i : 'I_n) (j : 'I_m),
                    A^*t i j = conjc (A j i).
                {
                  move=> m n A i j.
                  by rewrite !mxE.
                }
                have product_entry : forall (ix1 ix2 x2' : 'I_nx)
                    (a0' : 'I_na) (bl br : 'I_nBR),
                    (WBR *m castmx_sq (esym Hzz_dim_BR)
                        ((1%:M : 'M[C]_nz) *t sigmaZpA_BR) *m WBR^*t)
                      (mxtens_index (mxtens_index (mxtens_index (ix1, x2'), a0'), bl))
                      (mxtens_index (mxtens_index (mxtens_index (ix2, x2'), a0'), br))
                    =
                    (ix1 == x2')%:R * (ix2 == x2')%:R *
                    \sum_(jz : 'I_nz) \sum_(aa0 : 'I_na) \sum_(c1 : 'I_na)
                      S_xz ix1 jz a0' aa0 *
                      sigmaZpA_BR (mxtens_index (mxtens_index (jz, aa0), bl))
                                (mxtens_index (mxtens_index (jz, c1), br)) *
                      conjc (S_xz ix2 jz a0' c1).
                {
                  move=> ix1 ix2 x2' a0' bl br.
                  have delta_collapseRR' : forall (T : finType)
                      (f : T -> C) (j : T),
                      \sum_i f i * ((j == i)%:R : C) = f j.
                  {
                    move=> T f j.
                    under eq_bigr do rewrite eq_sym mulrC.
                    rewrite (bigD1 j) //= eqxx mul1r.
                    rewrite [X in _ + X]big1 ?addr0 //.
                    by move=> k /negPf Hk; rewrite Hk mul0r.
                  }
                  have sum_delta_mid : forall (T : finType)
                      (g h : T -> C) (j : T),
                      \sum_i g i * ((j == i)%:R : C) * h i = g j * h j.
                  {
                    move=> T g h j.
                    under eq_bigr => i _ do rewrite -mulrA mulrCA.
                    rewrite (bigD1 j) //= eqxx mul1r.
                    rewrite [X in _ + X]big1 ?addr0 //.
                    by move=> k /negPf Hk; rewrite eq_sym Hk mul0r.
                  }
                  transitivity (
                    \sum_(kz1 : 'I_nz) \sum_(kz2 : 'I_nz)
                    \sum_(c2 : 'I_na) \sum_(d2 : 'I_nBR)
                    \sum_(jz1 : 'I_nz) \sum_(jz2 : 'I_nz)
                    \sum_(aa0 : 'I_na) \sum_(d0 : 'I_nBR)
                      WBR (mxtens_index
                          (mxtens_index (mxtens_index (ix1, x2'), a0'), bl))
                        (mxtens_index
                          (mxtens_index (mxtens_index (jz1, jz2), aa0), d0)) *
                      (castmx_sq (esym Hzz_dim_BR)
                        ((1%:M : 'M[C]_nz) *t sigmaZpA_BR))
                        (mxtens_index
                          (mxtens_index (mxtens_index (jz1, jz2), aa0), d0))
                        (mxtens_index
                          (mxtens_index (mxtens_index (kz1, kz2), c2), d2)) *
                      WBR^*t
                        (mxtens_index
                          (mxtens_index (mxtens_index (kz1, kz2), c2), d2))
                        (mxtens_index
                          (mxtens_index (mxtens_index (ix2, x2'), a0'), br))
                  ).
                  {
                    rewrite mxE !mxtens_index_pairV.
                    apply: eq_bigr=> kz1 _.
                    apply: eq_bigr=> kz2 _.
                    apply: eq_bigr=> c2 _.
                    apply: eq_bigr=> d2 _.
                    set M0 := castmx_sq _ _.
                    rewrite [X in X * _]mxE !mxtens_index_pairV.
                    rewrite mulr_suml.
                    apply: eq_bigr=> jz1 _.
                    rewrite mulr_suml.
                    apply: eq_bigr=> jz2 _.
                    rewrite mulr_suml.
                    apply: eq_bigr=> aa0 _.
                    rewrite mulr_suml.
                    by apply: eq_bigr=> d0 _.
                  }
                  under eq_bigr => jz1 _ do under eq_bigr => jz2 _ do
                    under eq_bigr => aa0 _ do under eq_bigr => d0 _ do
                      under eq_bigr => kz1 _ do under eq_bigr => kz2 _ do
                        under eq_bigr => c2 _ do under eq_bigr => d2 _ do
                          rewrite WE ME adjmxE' WE !rmorphM ?conjC_nat.
                  under eq_bigr => jz1 _ do under eq_bigr => jz2 _ do
                    under eq_bigr => aa0 _ do under eq_bigr => d0 _ do
                      under eq_bigr => kz1 _ do under eq_bigr => kz2 _ do
                        under eq_bigr => c2 _ do under eq_bigr => d2 _ do
                          rewrite !mulrA.
                  case: (ix1 == x2') /eqP => [-> | /eqP Hneq1];
                    rewrite /nat_of_bool /= ?mul0r ?mul1r.
                  2: by do 8![apply: big1=> ? _]; rewrite !mul0r.
                  case: (ix2 == x2') /eqP => [-> | /eqP Hneq2];
                    rewrite /nat_of_bool /= ?mul0r ?mul1r.
                  2: by rewrite big1 // => i _; do 7![apply: big1=> ? _];
                    simpc; rewrite ?mulr0 ?mul0r.
                  under eq_bigr => jz1 _ do under eq_bigr => jz2 _ do
                    under eq_bigr => aa0 _ do under eq_bigr => d0 _ do
                      under eq_bigr => kz1 _ do under eq_bigr => kz2 _ do
                        under eq_bigr => c2 _ do (
                          rewrite (bigD1 bl) //= big1 ?addr0;
                            [|move=> d2 /negPf Hd2;
                              rewrite /= (eq_sym bl d2) Hd2 /=
                                !mulr0 !mul0r //];
                          rewrite eqxx mul1r mulr1
                        ).
                  apply: eq_bigr=> jz _.
                  rewrite (bigD1 jz) //= [X in _ + X]big1 ?addr0.
                  2: {
                    move=> dummy /negPf Hneq.
                    rewrite (eq_sym jz dummy) Hneq /=.
                    by do 5![apply: big1=> ? _]; simpc; rewrite ?mulr0 ?mul0r.
                  }
                  rewrite eqxx.
                  under eq_bigr => aa0 _ do (
                    rewrite (bigD1 br) //= [X in _ + X]big1 ?addr0;
                      [|move=> d0 /negPf Hneq;
                        rewrite /= (eq_sym br d0) Hneq /=;
                        do 3![apply: big1=> ? _]; simpc;
                        rewrite ?mulr0 ?mul0r //];
                    rewrite (bigD1 jz) //= [X in _ + X]big1 ?addr0;
                      [|move=> kz1 /negPf Hneq;
                        rewrite /= Hneq /=;
                        do 2![apply: big1=> ? _]; rewrite ?mulr0 ?mul0r //];
                    rewrite (bigD1 jz) //= [X in _ + X]big1 ?addr0;
                      [|move=> kz2 /negPf Hneq;
                        rewrite /= (eq_sym jz kz2) Hneq /=;
                        apply: big1=> ? _; rewrite ?mulr0 ?mul0r //]
                  ).
                  rewrite !eqxx.
                  rewrite exchange_big /=.
                  apply: eq_bigr=> c1 _.
                  apply: eq_bigr=> aa0 _.
                  by simpc; rewrite ?mul1r ?mulr1.
                }
                have sandwich_entry : forall (ix0 : 'I_nx) (jz0 : 'I_nz)
                    (a0' : 'I_na) (bl br : 'I_nBR),
                    ((S_xz ix0 jz0 *t (1%:M : 'M[C]_nBR)) *m
                      sigma_block jz0 *m
                     ((S_xz ix0 jz0)^*t *t (1%:M : 'M[C]_nBR)))
                      (mxtens_index (a0', bl)) (mxtens_index (a0', br)) =
                    \sum_(aa0 : 'I_na) \sum_(c1 : 'I_na)
                      S_xz ix0 jz0 a0' aa0 *
                      sigmaZpA_BR (mxtens_index (mxtens_index (jz0, aa0), bl))
                                (mxtens_index (mxtens_index (jz0, c1), br)) *
                      conjc (S_xz ix0 jz0 a0' c1).
                {
                  move=> ix0 jz0 a0' bl br.
                  have delta_collapseR : forall (T : finType)
                      (f : T -> C) (j : T),
                      \sum_i ((j == i)%:R : C) * f i = f j.
                  {
                    move=> T f j.
                    under eq_bigr do rewrite eq_sym.
                    rewrite (bigD1 j) //= eqxx mul1r.
                    rewrite [X in _ + X]big1 ?addr0 //.
                    by move=> k /negPf Hk; rewrite Hk mul0r.
                  }
                  have delta_collapseRR' : forall (T : finType)
                      (f : T -> C) (j : T),
                      \sum_i f i * ((i == j)%:R : C) = f j.
                  {
                    move=> T f j.
                    rewrite (bigD1 j) //= eqxx mulr1.
                    rewrite [X in _ + X]big1 ?addr0 //.
                    by move=> k /negPf Hk; rewrite Hk mulr0.
                  }
                  have eq1M : forall (n : nat) (i j : 'I_n),
                      (1%:M : 'M[C]_n) i j = (i == j)%:R.
                  {
                    move=> n i j.
                    by rewrite mxE.
                  }
                  rewrite mxE mxtens_index_pairV.
                  under eq_bigr => c1 _ do under eq_bigr => d1 _ do
                    rewrite tensmxE adjmxE' eq1M mulrA.
                  under eq_bigr => c1 _ do rewrite delta_collapseRR' /=.
                  under eq_bigr => c1 _ do
                    rewrite [X in X * _]mxE [X in X * _]mxtens_index_pairV
                      mulr_suml.
                  under eq_bigr => c1 _ do under eq_bigr => aa0 _ do
                    rewrite mulr_suml.
                  under eq_bigr => c1 _ do under eq_bigr => aa0 _ do
                    under eq_bigr => d0 _ do
                      rewrite [X in X * _ * _]tensmxE sigma_blockE eq1M.
                  under eq_bigr => c1 _ do under eq_bigr => aa0 _ do
                    under eq_bigr => d0 _ do
                      rewrite [X in X * _ * _]mulrC -!mulrA.
                  under eq_bigr => c1 _ do under eq_bigr => aa0 _ do
                    rewrite delta_collapseR /=.
                  under eq_bigr => c1 _ do under eq_bigr => aa0 _ do
                    rewrite mulrA.
                    by rewrite exchange_big.
                  }
                have delta_collapseR_outer : forall (T : finType)
                    (f : T -> C) (j : T),
                    \sum_i ((j == i)%:R : C) * f i = f j.
                {
                  move=> T f j.
                  rewrite (bigD1 j) //= eqxx mul1r.
                  rewrite [X in _ + X]big1 ?addr0 //.
                  by move=> k /negPf Hk; rewrite eq_sym Hk mul0r.
                }
                apply/matrix_tenP=> ix_L b_L ix_R b_R.
                rewrite ptraceXA_BRE.
                under eq_bigr => x2 _ do
                  under eq_bigr => a0' _ do rewrite product_entry.
                under eq_bigr => x2 _ do rewrite -mulr_sumr.
                under eq_bigr => x2 _ do rewrite -mulrA.
                rewrite delta_collapseR_outer.
                rewrite [RHS]summxE.
                under [RHS]eq_bigr => ix0 _ do rewrite summxE.
                under [RHS]eq_bigr => ix0 _ do
                  under eq_bigr => jz0 _ do rewrite tensmxE !mxE ptrace1E.
                under [RHS]eq_bigr => ix0 _ do
                  under eq_bigr => jz0 _ do
                    under eq_bigr => a0' _ do rewrite sandwich_entry.
                case Hxlr: (ix_R == ix_L).
                - move/eqP: Hxlr=> ->.
                  rewrite (bigD1 ix_L) //= !eqxx /= mul1r.
                  rewrite [X in _ + X]big1 ?addr0.
                  2: {
                    move=> ix0 /negPf Hix0.
                    rewrite eq_sym Hix0 /=.
                    by rewrite big1 // => jz0 _; rewrite mul0r.
                  }
                  rewrite [LHS]exchange_big.
                  apply: eq_bigr=> jz _.
                  rewrite mul1r.
                  apply: eq_bigr=> a0' _.
                  by [].
                - rewrite mul0r.
                  rewrite big1 // => ix0 _.
                  case Hli: (ix_L == ix0); last by rewrite /= big1 // => jz0 _; rewrite mul0r.
                  move/eqP: Hli=> <-.
                  by rewrite Hxlr /= big1 // => jz0 _; rewrite mul0r.
                }
              have HtensmxZl_local :
                  forall m n (k : C) (A : 'M[C]_m) (B : 'M[C]_n),
                  (k *: A) *t B = k *: (A *t B).
              {
                move=> m n k A B.
                by rewrite -[k *: A]addr0 (linear_tensmxr B) linear0l addr0.
              }
              have Hptrace1_form_le :
                  forall (S : 'M[C]_na) (rho : 'M[C]_(na * nBR)) (cc : R),
                  rho \is psdmx ->
                  0 <= cc ->
                  S^*t *m S <= cc%:C *: (1%:M : 'M[C]_na) ->
                  ptrace1
                    ((S *t (1%:M : 'M[C]_nBR)) *m rho *m
                     (S^*t *t (1%:M : 'M[C]_nBR))) <=
                  cc%:C *: ptrace1 rho.
              {
                move=> S rho cc Hrho Hcc Hle.
                have Hkey : forall X : 'M[C]_nBR, X \is psdmx ->
                    \tr (S^*t *m S *t X *m rho) <=
                    \tr (cc%:C *: 1%:M *t X *m rho).
                {
                  move=> X HX.
                  suff : S^*t *m S *t X <= cc%:C *: 1%:M *t X.
                  {
                    by move/le_lownerE_psdtr => /(_ rho Hrho).
                  }
                  rewrite le_lownerE.
                  have -> :
                      cc%:C *: 1%:M *t X - S^*t *m S *t X =
                      (cc%:C *: 1%:M - S^*t *m S) *t X.
                  {
                    by apply/matrixP=> i j; rewrite !mxE mulrBl.
                  }
                  apply: psdmx_tens; last exact: HX.
                  by move: Hle; rewrite le_lownerE.
                }
                apply/le_lownerE_psdtr => X HX.
                rewrite -ptrace1_mulmxI -tr_ptrace1.
                rewrite -scalemxAl linearZ /=.
                rewrite -ptrace1_mulmxI -tr_ptrace1.
                have -> :
                    \tr (S *t 1%:M *m rho *m
                      (S^*t *t 1%:M) *m (1%:M *t X)) =
                    \tr (S^*t *m S *t X *m rho).
                {
                  rewrite mxtrace_mulC !mulmxA tensmx_mul mul1mx mulmx1.
                  by rewrite [LHS]mxtrace_mulC mulmxA tensmx_mul mul1mx.
                }
                have -> :
                    cc%:C * \tr (rho *m (1%:M *t X)) =
                    \tr (cc%:C *: 1%:M *t X *m rho).
                {
                  by rewrite mxtrace_mulC HtensmxZl_local -scalemxAl linearZ.
                }
                exact: Hkey X HX.
              }
              have Hptrace_block_le : forall (ix : 'I_nx) (jz : 'I_nz),
                  ptrace1
                    ((S_xz ix jz *t (1%:M : 'M[C]_nBR)) *m
                      sigma_block jz *m
                     ((S_xz ix jz)^*t *t (1%:M : 'M[C]_nBR)))
                  <= c0%:C *: ptrace1 (sigma_block jz).
              {
                move=> ix jz.
                exact: Hptrace1_form_le (Hsigma_block_psd jz) Hc0_ge0
                  (H_SdagS_le ix jz).
              }
              rewrite Hblock_expand.
              have Htens_psdmx_le_l :
                  forall m n (P : 'M[C]_m) (A B : 'M[C]_n),
                  P \is psdmx -> A <= B -> P *t A <= P *t B.
              {
                move=> m n P A B HP.
                rewrite !le_lownerE -bregvBr.
                exact: psdmx_tens HP.
              }
              have Hsum_bound :
                  \sum_(ix : 'I_nx) \sum_(jz : 'I_nz)
                    (delta_mx ix ix : 'M[C]_nx) *t
                    ptrace1
                      ((S_xz ix jz *t (1%:M : 'M[C]_nBR)) *m
                        sigma_block jz *m
                       ((S_xz ix jz)^*t *t (1%:M : 'M[C]_nBR)))
                  <=
                  \sum_(ix : 'I_nx) \sum_(jz : 'I_nz)
                    (delta_mx ix ix : 'M[C]_nx) *t
                    (c0%:C *: ptrace1 (sigma_block jz)).
              {
                rewrite le_lownerE -sumrB.
                apply: psdmx_sum=> ix _.
                rewrite -sumrB.
                  apply: psdmx_sum=> jz _.
                  rewrite -le_lownerE.
                  rewrite !le_lownerE -bregvBr.
                  apply: psdmx_tens.
                  - exact: delta_mx_ii_psdmx.
                  - by move: (Hptrace_block_le ix jz); rewrite le_lownerE.
              }
              have Hptrace1_block_sum :
                  ptrace1 sigmaZpA_BR =
                  \sum_(jz : 'I_nz) ptrace1 (sigma_block jz).
              {
                have Hcast_assoc :
                    forall (z : 'I_nz) (a : 'I_na) (b : 'I_nBR),
                    cast_ord (mulnA nz na nBR)
                      (mxtens_index (z, mxtens_index (a, b))) =
                    mxtens_index (mxtens_index (z, a), b).
                {
                  move=> z a b.
                  apply/val_inj=> /=.
                  by rewrite mulnDl mulnA addnA.
                }
                have Hcast_assoc' :
                    forall (z : 'I_nz) (a : 'I_na) (b : 'I_nBR),
                    cast_ord (esym (esym (mulnA nz na nBR)))
                      (mxtens_index (z, mxtens_index (a, b))) =
                    mxtens_index (mxtens_index (z, a), b).
                {
                  move=> z a b.
                  by rewrite (eq_irrelevance (esym (esym (mulnA nz na nBR)))
                    (mulnA nz na nBR)) Hcast_assoc.
                }
                apply/matrixP=> b1 b2.
                rewrite ptrace1E.
                rewrite (reindex (@mxtens_index nz na)) /=.
                2: {
                  exists (@mxtens_unindex nz na).
                  - by move=> [z a] /=; rewrite mxtens_indexK.
                  - by move=> k /=; rewrite mxtens_unindexK.
                }
                rewrite pair_bigV /=.
                rewrite summxE.
                apply: eq_bigr=> z _.
                rewrite ptrace1E.
                apply: eq_bigr=> a _.
                rewrite /sigma_block /sigma_cast mxE /castmx_sq castmxE /=.
                by rewrite Hcast_assoc' Hcast_assoc'.
              }
              have Hsum_id :
                  \sum_(ix : 'I_nx) \sum_(jz : 'I_nz)
                    (delta_mx ix ix : 'M[C]_nx) *t
                    (c0%:C *: ptrace1 (sigma_block jz)) =
                  c0%:C *: ((1%:M : 'M[C]_nx) *t sigmaBR).
              {
                apply/matrix_tenP=> ix_l bv_l ix_r bv_r.
                rewrite summxE.
                under eq_bigr => ix _ do rewrite summxE.
                under eq_bigr => ix _ do
                  under eq_bigr => jz _ do rewrite tensmxE !mxE.
                rewrite mxE tensmxE !mxE.
                rewrite exchange_big /=.
                under eq_bigr => jz _ do rewrite -mulr_suml.
                have Hdelta_sum :
                    \sum_(ix : 'I_nx)
                      (((ix_l == ix) && (ix_r == ix))%:R : C) =
                    ((ix_l == ix_r)%:R : C).
                {
                  case Hlr: (ix_l == ix_r).
                  - move/eqP: Hlr=> ->.
                    rewrite (bigD1 ix_r) //= !eqxx /=.
                    rewrite big1 ?addr0 //.
                    move=> ix /negPf Hix.
                    by rewrite eq_sym Hix andbF.
                  - rewrite big1 // => ix _.
                    case Hli: (ix_l == ix); last by [].
                    by move/eqP: Hli=> <-; rewrite eq_sym Hlr.
                }
                under eq_bigr => jz _ do rewrite Hdelta_sum.
                rewrite -mulr_sumr -mulr_sumr.
                rewrite /sigmaBR Hptrace1_block_sum summxE.
                by rewrite !mulrA [((ix_l == ix_r)%:R : C) * c0%:C]mulrC.
              }
              rewrite -Hsum_id.
              exact: Hsum_bound.
            }
            exact: Hmo8_expand.
          }

          have Htarget_le_XBR :
              tauXBR <= c0%:C *: ((1%:M : 'M[C]_nx) *t sigmaBR).
          {
            rewrite /tauXBR /tauXXpABR.
            exact: le_trans (HptraceXA_BR_le _ _ Hconj_le) Hmo9.
          }
          have Hdiff_XBR :
              (c0%:C *: ((1%:M : 'M[C]_nx) *t sigmaBR) - tauXBR)
                \is psdmx.
          {
            by move: Htarget_le_XBR; rewrite le_lownerE.
          }
          have Hdiff_XB :
              ptrace2 (castmx_sq (mulnA nx nb Rdim)
                (c0%:C *: ((1%:M : 'M[C]_nx) *t sigmaBR) - tauXBR))
                \is psdmx.
          {
            apply: ptrace2_psd.
            exact: castmx_sq_psdmx Hdiff_XBR.
          }
          have Hptrace2Z_local :
              forall m n (k : C) (A : 'M[C]_(m * n)),
              ptrace2 (k *: A) = k *: ptrace2 A.
          {
            move=> m n k A.
            have ptrace2E' : forall s t (B : 'M[C]_(s * t)) r1 r2,
                (ptrace2 B) r1 r2 =
                \sum_(k0 : 'I_t) B (mxtens_index (r1, k0))
                                       (mxtens_index (r2, k0)).
            {
              move=> s t B r1 r2; rewrite ptrace2E1 ptrace1E.
              by apply: eq_bigr => k0 _; rewrite mxE !mxtens_indexK.
            }
            apply/matrixP=> i j.
            rewrite ptrace2E' mxE.
            under eq_bigr=> r _ do rewrite mxE.
            by rewrite -mulr_sumr -ptrace2E'.
          }
          have Htarget_diff :
              ptrace2 (castmx_sq (mulnA nx nb Rdim)
                (c0%:C *: ((1%:M : 'M[C]_nx) *t sigmaBR) - tauXBR)) =
              c0%:C *: ((1%:M : 'M[C]_nx) *t ptrace2 sigmaBR) - tauXB.
          {
            rewrite /tauXB /tauXB_full /castmx_sq linearB /= linearZ /=.
            rewrite linearB /= Hptrace2Z_local.
            by rewrite ptrace2_castmx_tensmx_assoc.
          }
          by rewrite -Htarget_diff.

        }
        have HSX_has : has_inf SX.
        { exact: (@eur_matrix_phi_has_inf nx nb tauXB HtauXB_psd). }
        have HSZ_has : has_inf SZ.
        { exact: (@eur_matrix_phi_has_inf nz Ebig tauZpABR
            HtauZpABR_psd). }
        have Hphi_transport : inf SX <= c0 * inf SZ.
        {
          have Hdiv_le : c0^-1 * inf SX <= inf SZ.
          {
            rewrite /SZ.
            apply: lb_le_inf.
            - exact: HSZ_has.1.
            - move=> valZ [sigmaE [Hsigma_psd [Hsigma_feas HvalZ]]].
              have HinfX_le : inf SX <= c0 * valZ.
              {
                apply: ge_inf.
                - exact: HSX_has.2.
                - exists (c0%:C *:
                    ptrace2 (ptrace1 (castmx_sq HEbig_BR sigmaE))).
                  split; last split.
                  + apply: psdmxZ.
                    * by rewrite lecR.
                    * apply: ptrace2_psd.
                      apply: ptrace1_psd.
                      exact: castmx_sq_psdmx Hsigma_psd.
                  + rewrite HtensmxZr_local.
                    exact: Hfeas_transport_tau Hsigma_psd Hsigma_feas.
                  + rewrite mxtraceZ -tr_ptrace2 -tr_ptrace1.
                    rewrite mxtrace_castmx_sq HRe_realM HvalZ.
                    by rewrite /c0.
              }
              have Hdiv_v : inf SX / c0 <= valZ.
              {
                rewrite ler_pdivrMr // mulrC.
                exact: HinfX_le.
              }
              by rewrite mulrC.
          }
          have Hscaled := ler_wpM2l (ltW Hc0_pos) Hdiv_le.
          have Hlhs :
              c0 * (c0^-1 * inf SX) = inf SX.
          {
            have Hc0_unit : c0 \is a GRing.unit := unitf_gt0 Hc0_pos.
            by rewrite mulrA (mulrV Hc0_unit) mul1r.
          }
          by move: Hscaled; rewrite Hlhs.
        }
        have HtauXB_tr_pos : 0 < @complex.Re R (\tr tauXB).
        {
            have Hsqrt_le0 :
                Num.sqrt (@complex.Re R (\tr rhoX)) <=
                Num.sqrt (@complex.Re R (\tr tauXB)) + pur_dist_mx tauXB rhoX.
            { rewrite /pur_dist_mx.
              exact: pur_dist_mx_trace_sqrt_bound Hnxnb_pos
                HrhoX_den HtauXB_den. }
          have Hsqrt_le :
              Num.sqrt (@complex.Re R (\tr rhoABC))
                <= Num.sqrt (@complex.Re R (\tr tauXB)) + eps.
          {
            have Hadd_le :
                Num.sqrt (@complex.Re R (\tr tauXB)) + pur_dist_mx tauXB rhoX <=
                Num.sqrt (@complex.Re R (\tr tauXB)) + eps
              by rewrite lerD2l.
            move: (le_trans Hsqrt_le0 Hadd_le).
            by rewrite HrhoX_tr_eq.
          }
          have Hgap_le_sqrt :
              Num.sqrt (@complex.Re R (\tr rhoABC)) - eps
                <= Num.sqrt (@complex.Re R (\tr tauXB)).
          {
            have Htmp :
                (Num.sqrt (@complex.Re R (\tr rhoABC)) - eps) + eps
                  <= Num.sqrt (@complex.Re R (\tr tauXB)) + eps
              by rewrite subrK.
            by move: Htmp; rewrite lerD2r.
          }
          have Hgap_pos :
              0 < Num.sqrt (@complex.Re R (\tr rhoABC)) - eps
            by rewrite subr_gt0.
          have Hsqrt_pos := lt_le_trans Hgap_pos Hgap_le_sqrt.
          by move: Hsqrt_pos; rewrite sqrtr_gt0.
        }
        have HtauZpABR_tr_pos : 0 < @complex.Re R (\tr tauZpABR).
        {
          have Htau_tr_pos : 0 < @complex.Re R (\tr tau).
          {
            have Htau_tr_ge0 : 0 <= @complex.Re R (\tr tau).
            { have /= := psdmx_trace Htau_psd.
              by rewrite lecE /= => /andP[_]. }
            rewrite lt_def Htau_tr_ge0 andbT.
            apply/negP=> /eqP Htr0R.
            have Htr0C : \tr tau = 0.
            {
              have Hreal := ger0_real (psdmx_trace Htau_psd).
              by rewrite -(RRe_real Hreal) Htr0R.
            }
            move: Htau_ne.
            by rewrite -(psdmx_trace_eq0 Htau_psd) Htr0C eqxx.
          }
          have Htr_tauZp :
              \tr tauZpABR = \tr tau.
          {
            by rewrite /tauZpABR /rho_AC_mx -tr_ptrace2
              mxswap23_trace tr_ptrace2 HtauZC_big_ptr.
          }
          by rewrite Htr_tauZp.
        }
        have HPX_pos : 0 < inf SX.
        {
          have Hlb : @complex.Re R (\tr tauXB) / nx%:R <= inf SX.
          { exact: (@eur_matrix_phi_trace_lb nx nb tauXB
              Hnx_pos HtauXB_psd HtauXB_tr_pos). }
          have Hdiv_pos : 0 < @complex.Re R (\tr tauXB) / nx%:R.
          { apply: divr_gt0=> //; by rewrite ltr0n. }
          exact: lt_le_trans Hdiv_pos Hlb.
        }
        have HPZ_pos : 0 < inf SZ.
        {
          have Hlb :
              @complex.Re R (\tr tauZpABR) / nz%:R <= inf SZ.
          { exact: (@eur_matrix_phi_trace_lb nz Ebig tauZpABR
              Hnz_pos HtauZpABR_psd HtauZpABR_tr_pos). }
          have Hdiv_pos : 0 < @complex.Re R (\tr tauZpABR) / nz%:R.
          { apply: divr_gt0=> //; by rewrite ltr0n. }
          exact: lt_le_trans Hdiv_pos Hlb.
        }
        have Hlog2_mul_local : forall x y : R, 0 < x -> 0 < y ->
            log2 (x * y) = log2 x + log2 y.
        { move=> x y Hx Hy; by rewrite /log2 lnM // mulrDl. }
        have Hlog_le : log2 (inf SX) <= log2 (c0 * inf SZ).
        { exact: log2_le_pos HPX_pos Hphi_transport. }
        have Hdiff_le : log2 (inf SX) - log2 (inf SZ) <= log2 c0.
        {
          move: Hlog_le.
          rewrite Hlog2_mul_local //.
          move=> Hlog0.
          rewrite lerBlDr.
          exact: Hlog0.
        }
        rewrite /hmin_mx -/tauXB -/tauZpABR -/SX -/SZ.
        move: Hdiff_le.
        by rewrite -lerN2 opprB opprK addrC /c0.
      }
      apply: le_trans Htransport_tau _.
      by rewrite lerD2l.
    }
    have Hq_le :
        - log2 (overlap_mx M N) <= smooth_hmin_mx eps rhoX + hmax_mx tau.
    {
      apply: le_trans Hzero _.
      by rewrite lerD2r.
    }
    by move: Hq_le; rewrite lerBlDr addrC.
Qed.
End Stage1.
(* ================================================================== *)
(* labeled `eur_data_proc`                                 *)
(* Paper: Tomamichel & Renner (PRL 106, 110506 (2011); arXiv:1009.2015) *)
(*   — mixed-state reduction step ("Proof of the Main Result"); the     *)
(*   underlying DPI is Tomamichel, 'A Framework for Non-Asymptotic      *)
(*   Quantum Information Theory' (arXiv:1203.2142), Theorem 5.7         *)
(*   (Generalized Data Processing) — max half, partial-trace-over-D     *)
(*   instance.                                                           *)
(* math: For τ_{ZCD} ∈ S_sub(ℋ_{ZCD}) and τ_{ZC} := Tr_D(τ_{ZCD}),     *)
(*   H^ε_max(Z|CD)[τ] ≤ H^ε_max(Z|C)[τ].                                *)
(*                                                                       *)
(* Uses the extended-real smooth max-entropy                   *)
(* (`smooth_hmaxE` on 'F[H]_S with conditioning set T).                 *)
(*                                                                       *)
(* Proof route: instantiate Theorem 5.7 (Generalized Data Processing)  *)
(* with A=Z, B=C∪D, C0=∅, A'=Z, B'=C, C0'=∅, E=id_Z, F=Tr_D, G=id_∅.   *)
(* The only work outside that theorem is local cast/empty-register      *)
(* bookkeeping.                                                          *)
(* ================================================================== *)
Section EurDataProcLabeled.
Variable (L : finType) (HL : L -> chsType) (Z C D : L).
Hypothesis disZC : [disjoint [set Z] & [set C]].
Hypothesis disZD : [disjoint [set Z] & [set D]].
Hypothesis disCD : [disjoint [set C] & [set D]].
Hypothesis disZC_D : [disjoint ([set Z] :|: [set C]) & [set D]].
(* Upstream-ambient proof labels used only to instantiate Tomamichel data
   processing: App/Bpp are Stinespring environments, and the remaining
   labels are purifier/copy rooms consumed by smooth-isometry infrastructure. *)
Variables (App Bpp Ciso Cp_src Cpp_src Cp_tgt Cpp_tgt : {set L}).
Hypothesis disZ_App : [disjoint [set Z] & App].
Hypothesis disC_Bpp : [disjoint [set C] & Bpp].
Hypothesis disZ_Bpp : [disjoint [set Z] & Bpp].
Hypothesis disApp_C : [disjoint App & [set C]].
Hypothesis disApp_Bpp : [disjoint App & Bpp].
Hypothesis dimApp_enough :
  (dim 'H[HL]_[set Z] * dim 'H[HL]_[set Z] <= dim 'H[HL]_App)%N.
Hypothesis dimBpp_enough :
  (dim 'H[HL]_([set C] :|: [set D]) * dim 'H[HL]_[set C] <=
   dim 'H[HL]_Bpp)%N.
Hypothesis disZ_Ciso : [disjoint [set Z] & Ciso].
Hypothesis disCD_Ciso : [disjoint [set C] :|: [set D] & Ciso].
Hypothesis disZApp_Ciso : [disjoint [set Z] :|: App & Ciso].
Hypothesis disCBpp_Ciso : [disjoint [set C] :|: Bpp & Ciso].
Hypothesis dimZCD_Ciso :
  (dim 'H[HL]_([set Z] :|: ([set C] :|: [set D])) <=
   dim 'H[HL]_Ciso)%N.
Hypothesis dimZAppCBpp_Ciso :
  (dim 'H[HL]_(([set Z] :|: App) :|: ([set C] :|: Bpp)) <=
   dim 'H[HL]_Ciso)%N.
Hypothesis disZ_Cp_src : [disjoint [set Z] & Cp_src].
Hypothesis disZ_Cpp_src : [disjoint [set Z] & Cpp_src].
Hypothesis disCD_Cp_src : [disjoint [set C] :|: [set D] & Cp_src].
Hypothesis disCD_Cpp_src : [disjoint [set C] :|: [set D] & Cpp_src].
Hypothesis disCiso_Cp_src : [disjoint Ciso & Cp_src].
Hypothesis disCiso_Cpp_src : [disjoint Ciso & Cpp_src].
Hypothesis disCp_Cpp_src : [disjoint Cp_src & Cpp_src].
Hypothesis dimZ_Cp_src : dim 'H[HL]_[set Z] = dim 'H[HL]_Cp_src.
Hypothesis dimCisoCp_Cpp_src :
  (dim 'H[HL]_Ciso * dim 'H[HL]_Cp_src <= dim 'H[HL]_Cpp_src)%N.
Hypothesis dimCD_Cpp_src :
  (dim 'H[HL]_([set C] :|: [set D]) <= dim 'H[HL]_Cpp_src)%N.
Hypothesis disZApp_Cp_tgt : [disjoint [set Z] :|: App & Cp_tgt].
Hypothesis disZApp_Cpp_tgt : [disjoint [set Z] :|: App & Cpp_tgt].
Hypothesis disCBpp_Cp_tgt : [disjoint [set C] :|: Bpp & Cp_tgt].
Hypothesis disCBpp_Cpp_tgt : [disjoint [set C] :|: Bpp & Cpp_tgt].
Hypothesis disCiso_Cp_tgt : [disjoint Ciso & Cp_tgt].
Hypothesis disCiso_Cpp_tgt : [disjoint Ciso & Cpp_tgt].
Hypothesis disCp_Cpp_tgt : [disjoint Cp_tgt & Cpp_tgt].
Hypothesis dimZApp_Cp_tgt :
  dim 'H[HL]_([set Z] :|: App) = dim 'H[HL]_Cp_tgt.
Hypothesis dimCisoCp_Cpp_tgt :
  (dim 'H[HL]_Ciso * dim 'H[HL]_Cp_tgt <= dim 'H[HL]_Cpp_tgt)%N.
Hypothesis dimCBpp_Cpp_tgt :
  (dim 'H[HL]_([set C] :|: Bpp) <= dim 'H[HL]_Cpp_tgt)%N.
Notation S_ZC  := ([set Z] :|: [set C]).
Notation S_ZCD := (S_ZC :|: [set D]).
(* path: eur:eur_data_proc -> eur:ucr_pure_smooth -> *)
(*   eur:entropic_uncertainty_relation -> *)
(*   eur:entropic_uncertainty_relation -> *)
(*   bb84:entropic_uncertainty_relation_bb84 -> bb84:bb84_secret *)
Lemma eur_data_proc (eps : R) (tauZCD : 'F[HL]_S_ZCD) :
    tauZCD \is denlf ->
    0 <= eps ->
    eps < Num.sqrt (@complex.Re R (\Tr tauZCD)) ->
    (smooth_hmaxE ([set C] :|: [set D]) eps tauZCD <=
     smooth_hmaxE [set C] eps (ptrace_cast disZC_D tauZCD))%E.
  Proof.
    move=> Htau_den Heps Heps_lt.
  have HdisZ_CD : [disjoint [set Z] & [set C] :|: [set D]]
    by rewrite disjointXU disZC disZD.
  have HdisZ_0 : [disjoint [set Z] & finset.set0] := disjointX0 [set Z].
  have HdisCD_0 : [disjoint [set C] :|: [set D] & finset.set0] :=
    disjointX0 ([set C] :|: [set D]).
  have HdisC_0 : [disjoint [set C] & finset.set0] := disjointX0 [set C].
  have Heq_full :
      S_ZCD =
      (([set Z] :|: ([set C] :|: [set D])) :|: finset.set0).
  { apply/setP=> x. by rewrite /S_ZCD /S_ZC !inE orbF orbA. }
  have Heq_lhs : S_ZCD = [set Z] :|: ([set C] :|: [set D]).
  { apply/setP=> x. by rewrite /S_ZCD /S_ZC !inE orbA. }
  have Hlhs_cast :
      smooth_hmaxE ([set C] :|: [set D]) eps
        (castlf (Heq_lhs, Heq_lhs) tauZCD) =
      smooth_hmaxE ([set C] :|: [set D]) eps tauZCD.
    {
      by case: _ / Heq_lhs in tauZCD Htau_den Heps_lt *; rewrite castlf_id.
    }
  pose tau_full :
      'F[HL]_(([set Z] :|: ([set C] :|: [set D])) :|: finset.set0) :=
    castlf (Heq_full, Heq_full) tauZCD.
    pose F0 : 'QC[HL]_([set C] :|: [set D],
        ([set C] :|: [set D]) :\: [set D]) :=
      QChannel_Build (@ptraceso_qc R L HL [set D] ([set C] :|: [set D])).
  pose Fcd : 'SO[HL]_([set C] :|: [set D], [set C]) :=
    castso (erefl _, setDU_r disCD) F0.
  have Ptau : tauZCD \is psdlf.
  {
    exact: denlf_psd Htau_den.
  }
  have Ptau_full : tau_full \is psdlf.
  {
    rewrite /tau_full.
    exact: castlf_psdlf Ptau.
  }
  have Htau_full_den : tau_full \is denlf.
  { apply/denlfP; split; first exact: Ptau_full.
    by rewrite /tau_full castlf_trlfE; exact: (denlf_trlf Htau_den). }
    have Htau_tr_real :
        (\Tr tauZCD : @hermitian.C R) =
          (@complex.Re R (\Tr tauZCD))%:C.
  {
    by rewrite RRe_real // ger0_real // psdlf_trlf.
  }
  have Htau_tr : @complex.Re R (\Tr tauZCD) <= 1.
  {
    move: (denlf_trlf Htau_den).
    rewrite Htau_tr_real lecR.
    exact.
  }
  have Htau_full_tr : @complex.Re R (\Tr tau_full) <= 1.
  {
    by rewrite /tau_full castlf_trlfE.
  }
    have [_ Hmax] :=
      @entropy_data_proc R L HL [set Z] ([set C] :|: [set D]) finset.set0
      [set Z] [set C] finset.set0 HdisZ_CD HdisZ_0 HdisCD_0
      disZC HdisZ_0 HdisC_0
      HdisZ_CD App Bpp disZ_App disC_Bpp disZ_Bpp disApp_C disApp_Bpp
      dimApp_enough dimBpp_enough
      Ciso Cp_src Cpp_src Cp_tgt Cpp_tgt
      disZ_Ciso disCD_Ciso disZApp_Ciso disCBpp_Ciso
      dimZCD_Ciso dimZAppCBpp_Ciso
      disZ_Cp_src disZ_Cpp_src disCD_Cp_src disCD_Cpp_src
      disCp_Cpp_src
      dimZ_Cp_src dimCisoCp_Cpp_src dimCD_Cpp_src
      disZApp_Cp_tgt disZApp_Cpp_tgt disCBpp_Cp_tgt disCBpp_Cpp_tgt
      disCp_Cpp_tgt
      dimZApp_Cp_tgt dimCisoCp_Cpp_tgt dimCBpp_Cpp_tgt
      eps tau_full
      (\:1 : 'SO[HL]_[set Z]) Fcd (\:1 : 'SO[HL]_finset.set0)
      Htau_full_den Heps.
  have Hstep := Hmax (idso_qc 'H[HL]_[set Z])
    (ltac:(by rewrite dualso1 is_tnmap))
    (ltac:(exact: is_cptp))
    (idso_qc 'H[HL]_finset.set0).
  have Hz0 : HdisZ_0 = disjointX0 [set Z] := eq_irrelevance _ _.
  have Hcd0 : HdisCD_0 = disjointX0 ([set C] :|: [set D])
    := eq_irrelevance _ _.
  have Hc0 : HdisC_0 = disjointX0 [set C] := eq_irrelevance _ _.
  rewrite Hz0 Hcd0 Hc0 in Hstep.
  rewrite /dpi.entropy_data_proc_tau /dpi.entropy_data_proc_map /Fcd in Hstep.
  have Hlhs_state :
      ptrace_cast3C (disjointX0 [set Z])
        (disjointX0 ([set C] :|: [set D])) tau_full =
      castlf (Heq_lhs, Heq_lhs) tauZCD.
  {
    rewrite /tau_full /ptrace_cast3C /ptrace_cast_gen.
    apply: to_Fnd_inj.
    rewrite Fnd_cast.
    rewrite /ptraceso {1}/fun_of_superof/= lfunE/=.
    rewrite ptraceso_fun.unlock.
    have HeqI0 :
        (([set Z] :|: ([set C] :|: [set D])) :|: finset.set0)
          :&: finset.set0 = finset.set0.
    { apply/setP=> x. by rewrite !inE andbF. }
    pose k0 : 'Idx[HL]_((([set Z] :|: ([set C] :|: [set D])) :|: finset.set0)
        :&: finset.set0) := castidx (esym HeqI0) idx0.
    have Hk0 (k : 'Idx[HL]_((([set Z] :|: ([set C] :|: [set D]))
        :|: finset.set0) :&: finset.set0)) :
        k = k0.
    {
      apply/idxP=> y.
      have Hyfalse :
          val y \in ((([set Z] :|: ([set C] :|: [set D])) :|:
            finset.set0) :&: finset.set0) = false
        by rewrite !inE andbF.
      by move: (valP y); rewrite Hyfalse.
    }
    have Heq_raw :
        [set Z] :|: ([set C] :|: [set D]) =
        ((([set Z] :|: ([set C] :|: [set D])) :|: finset.set0)
          :\: finset.set0).
    { apply/setP=> x. by rewrite !inE orbF. }
    have Hidx0 (x : 'Idx[HL]_((([set Z] :|: ([set C] :|: [set D]))
        :|: finset.set0) :\: finset.set0)) :
      castidx (esym Heq_full)
        (castidx
          (esym (esym (setID
            (([set Z] :|: ([set C] :|: [set D])) :|: finset.set0)
            finset.set0)))
          (idxU k0 x)) =
      castidx (esym Heq_lhs) (castidx (esym Heq_raw) x).
    {
      apply/idxP=> y.
      rewrite !castidx_app.
      set yy := (exist _ _ _).
      have Hyfalse :
          val yy \in ((([set Z] :|: ([set C] :|: [set D])) :|:
            finset.set0) :&: finset.set0) = false.
      { by rewrite /yy !inE andbF. }
      rewrite /idxU idxE.
      case: eqP=> Hy_left.
      - exfalso. by move: Hy_left; rewrite Hyfalse.
      - rewrite /setsub.
        congr (x (exist _ _ _)).
        apply eq_irrelevance.
    }
    rewrite (bigD1 k0)//=.
    rewrite [X in (_ + X)%R]big1 ?addr0.
    2: by move=> k /negPf nk; move: nk; rewrite (Hk0 k) eqxx.
    rewrite -[RHS](@Fnd_cast R L HL _ _ _ _ (Heq_raw, Heq_raw)
      (castlf (Heq_lhs, Heq_lhs) tauZCD)).
    rewrite [X in _ = to_Fnd X](onb_lfun2id deltav
      (castlf (Heq_raw, Heq_raw)
        (castlf (Heq_lhs, Heq_lhs) tauZCD))).
    match goal with
    | |- to_Fnd ?lhs = to_Fnd ?rhs => suff -> : lhs = rhs by []
    end.
    rewrite exchange_big/=.
    apply: eq_bigr=> i _.
    apply: eq_bigr=> j _.
    congr (_ *: _).
    rewrite !castlfE !casths_dotr !deltav_cast.
    by rewrite !Hidx0.
  }
  have Hrhs_state :
      ptrace_cast3C (disjointX0 [set Z]) (disjointX0 [set C])
        ((((\:1 : 'SO[HL]_[set Z]) :⊗ Fcd)
          :⊗ (\:1 : 'SO[HL]_finset.set0)) tau_full) =
      ptrace_cast disZC_D tauZCD.
  {
    have Htarget_empty :
        ptrace_cast3C (disjointX0 [set Z]) (disjointX0 [set C])
          ((((\:1 : 'SO[HL]_[set Z]) :⊗ Fcd)
            :⊗ (\:1 : 'SO[HL]_finset.set0)) tau_full) =
        ((\:1 : 'SO[HL]_[set Z]) :⊗ Fcd)
          (ptrace_cast3C (disjointX0 [set Z])
            (disjointX0 ([set C] :|: [set D])) tau_full).
    {
      apply/eqP/trlf_intror=> X.
      pose tau_after :
          'F[HL]_(([set Z] :|: [set C]) :|: finset.set0) :=
        ((((\:1 : 'SO[HL]_[set Z]) :⊗ Fcd)
          :⊗ (\:1 : 'SO[HL]_finset.set0)) tau_full).
      pose Y : 'F[HL]_([set Z] :|: ([set C] :|: [set D])) :=
        ((\:1 : 'SO[HL]_[set Z]) :⊗ Fcd)^*o X.
      have Hptr_tau_after :
          ptrace_cast (disjointX0 ([set Z] :|: [set C])) tau_after =
          ptrace_cast3C (disjointX0 [set Z]) (disjointX0 [set C])
            tau_after.
      {
        rewrite /tau_after /ptrace_cast /ptrace_cast3C /ptrace_cast_gen.
        have Heq : setDU_r (disjointX0 ([set Z] :|: [set C])) =
                   setDU3_C (disjointX0 [set Z]) (disjointX0 [set C]).
        { exact: eq_irrelevance. }
        by rewrite Heq.
      }
      rewrite -Hptr_tau_after.
      rewrite -(trlf_lift_partial_r (disjointX0 ([set Z] :|: [set C]))
        tau_after X).
      rewrite /tau_after /Y.
      rewrite dualso_trlfE tenso_dual.
      rewrite (tenso_sdot_correct (disjointX0 ([set Z] :|: [set C]))
        (disjointX0 ([set Z] :|: ([set C] :|: [set D])))).
      rewrite dualso1.
      rewrite soE.
      rewrite (trlf_lift_partial_r (disjointX0 ([set Z] :|:
        ([set C] :|: [set D]))) tau_full
        (((\:1 : 'SO[HL]_[set Z]) :⊗ Fcd)^*o X)).
      have Hptr_tau_full :
          ptrace_cast (disjointX0 ([set Z] :|: ([set C] :|: [set D])))
            tau_full =
          ptrace_cast3C (disjointX0 [set Z])
            (disjointX0 ([set C] :|: [set D])) tau_full.
      {
        rewrite /ptrace_cast /ptrace_cast3C /ptrace_cast_gen.
        have Heq :
            setDU_r (disjointX0 ([set Z] :|: ([set C] :|: [set D]))) =
            setDU3_C (disjointX0 [set Z])
              (disjointX0 ([set C] :|: [set D])).
        { exact: eq_irrelevance. }
        by rewrite Heq.
      }
      rewrite Hptr_tau_full Hlhs_state.
      by rewrite dualso_trlfE.
    }
    have Hmap_ptr :
        ((\:1 : 'SO[HL]_[set Z]) :⊗ Fcd) =
        castso (Heq_lhs, setDU_r disZC_D)
          (@ptraceso R L HL [set D] S_ZCD).
    {
      rewrite /Fcd /F0 /= -formso1.
      rewrite ptraceso_krausso.
      rewrite castso_krausso.
      rewrite tenso_formso_krausso //.
      rewrite ptraceso_krausso.
      rewrite castso_krausso.
      have HeqI :
          S_ZCD :&: [set D] = ([set C] :|: [set D]) :&: [set D].
      {
        apply/setP=> x.
        rewrite /S_ZCD /S_ZC !inE.
        by case: (x == D); rewrite ?andbF ?andbT ?orbT.
      }
      pose h (k : 'Idx[HL]_(S_ZCD :&: [set D])) :
          'Idx[HL]_(([set C] :|: [set D]) :&: [set D]) :=
        castidx HeqI k.
      have h_bij : bijective h.
      {
        exists (fun k : 'Idx[HL]_(([set C] :|: [set D]) :&: [set D]) =>
          castidx (esym HeqI) k) => k.
        - by rewrite /h castidx_comp
            (eq_irrelevance (etrans _ _) (erefl _)) castidx_id.
        - by rewrite /h castidx_comp
            (eq_irrelevance (etrans _ _) (erefl _)) castidx_id.
      }
      apply: (krausso_reindex h_bij)=> k /=.
      apply: to_Fnd_inj.
      rewrite !Fnd_cast !to_Fnd_tenE !Fnd_cast.
      rewrite [X in (_ \⊗ X)%FND]to_Fnd_tenE.
      rewrite tenFA.
      have HIdZC :
          to_Fnd (\1 : 'F[HL]_(S_ZCD :\: [set D])) =
          ((\1 : 'F[HL]_[set Z]) \⊗ (\1 : 'F[HL]_[set C]))%FND.
      {
        rewrite tenF11.
        apply Fnd_eq1.
        exact: setDU_r disZC_D.
      }
      rewrite HIdZC -tenFA.
      rewrite !tenFA.
      rewrite [(\1 \⊗ [> deltav idx0; deltav (h k) <])%FND]tenFC.
      rewrite /h.
      have -> :
          [> deltav idx0; deltav k <] =
          castlf (esym HeqI, erefl _)
            [> deltav idx0; deltav (castidx HeqI k) <].
      {
        rewrite castlf_outp casths_id deltav_cast.
        by rewrite castidxK.
      }
      rewrite -!tenFA.
      do 2 f_equal.
      - by rewrite Fnd_cast.
      - apply Fnd_eq1.
        exact: setDU_r disCD.
    }
    rewrite Htarget_empty Hlhs_state Hmap_ptr.
    rewrite castsoE /ptrace_cast /ptrace_cast_gen.
    rewrite !castlf_comp.
    have Heq_cancel :
        etrans Heq_lhs (esym (Heq_lhs, setDU_r disZC_D).1) =
        erefl S_ZCD
      by apply eq_irrelevance.
    rewrite Heq_cancel castlf_id.
    done.
  }
    rewrite Hlhs_state in Hstep.
    have Hrange_cast :
        eps <
        Num.sqrt (@complex.Re R (\Tr (castlf (Heq_lhs, Heq_lhs) tauZCD))).
    { by rewrite castlf_trlfE. }
    have Hstep_final := Hstep Hrange_cast.
    rewrite Hlhs_cast in Hstep_final.
    rewrite Hrhs_state in Hstep_final.
    exact: Hstep_final.
Qed.
End EurDataProcLabeled.
(* ================================================================== *)
(* Lift -> partial-trace trace-duality (general CoqQ lemma).           *)
(* ------------------------------------------------------------------ *)
(* The trace of a FULL-SPACE-lifted operator `liftf_lf P` (P on the    *)
(* register S, lifted to the ambient setT by tensoring with identity)  *)
(* composed with a state `rho` on setT equals the trace of P against   *)
(* the partial trace of `rho` over the complementary registers `~: S`. *)
(* This is the operator-side adjoint of the partial-trace channel:     *)
(* lifting `liftf_lf` IS the Hilbert-Schmidt dual of `ptraceso (~:S)`  *)
(* (Born duality `Tr((P (x) 1) rho) = Tr(P . tr_{~:S} rho)`).  CoqQ    *)
(* has `liftf_lf_tr` (the transpose) and `ptraceso`/`ptraceso_krausso` *)
(* but NOT this trace-duality; it is foundational + reusable.          *)
(* The S-marginal `\Tr_(~: S) rho` lives on `setT :\: ~: S = S`, so a  *)
(* dimension cast `eqcompl` carries it onto S.  Two forms are proved:  *)
(*   - `m1_trace_dual_lab`: labelled, with the marginal kept on the    *)
(*       complementary carrier `setT :\: ~: S` (no extra cast);        *)
(*   - `m1_trace_dual_mx`: the matrix Born-weight form                 *)
(*       `\tr (h2mx P *m h2mx(<S-marginal of rho>))`, the next bridge  *)
(*       rewrites the per-outcome measure trace into.                  *)
(* ================================================================== *)
Section M1TraceDuality.
Variable (L : finType) (HL : L -> chsType).
Variable (S : {set L}).
(* finset's `setT`/`:\:`/`~:`/`:&:` notations are shadowed by the
   classical_sets import; the explicit finset operations
   (`setTfor`/`setD`/`setC`/`setI`), bound to `{set L}`-typed `Let`
   abbreviations, are used below so the register-set algebra parses
   unambiguously.  `univ` = setT, `cS` = ~: S, `comp` = setT :\: ~: S
   (= S, by `eqcompl`), `inter` = setT :&: ~: S. *)
Let univ : {set L} := setTfor L.
Let cS : {set L} := mathcomp.boot.finset.setC S.
Let comp : {set L} := mathcomp.boot.finset.setD univ cS.
Let inter : {set L} := mathcomp.boot.finset.setI univ cS.
(* the complement of `~: S` inside `setT` is exactly `S`. *)
Let eqcompl : comp = S.
Proof. by apply/setP => x; rewrite !inE andbT negbK. Qed.
(* tensor-dot interchange: (a (x) c) . (b (x) d) = (a.b) (x) (c.d)
   for vertically-composable tensor factors (a after b, c after d). *)
Lemma fnd_ten_dot Q1 Q2 Q3 W1 W2 W3
  (a : 'F[HL]_(Q2,Q3)) (b : 'F[HL]_(Q1,Q2))
  (c : 'F[HL]_(W2,W3)) (d : 'F[HL]_(W1,W2)) :
  [disjoint Q2 & W2] ->
  ((a \⊗ c) \· (b \⊗ d))%FND = ((a \· b) \⊗ (c \· d))%FND.
Proof. by move=>d2; rewrite -!to_Fnd_compE -!to_Fnd_tenE -tenf_comp. Qed.
(* one dual-Kraus summand of `(ptraceso cS)^*o`, collapsed (Fnd). *)
Fact m1_summand_fnd (Pc : 'F[HL]_comp) (i : 'Idx[HL]_inter) :
  to_Fnd (
    (castlf (mathcomp.boot.finset.set0U comp, mathcomp.boot.finset.setID univ cS)
         ([> deltav i; deltav idx0 <] \⊗ \1) \o Pc) \o
      castlf (mathcomp.boot.finset.setID univ cS, mathcomp.boot.finset.set0U comp)
        ([> deltav idx0; deltav i <] \⊗ \1) )
  = to_Fnd ([> deltav i; deltav i <] \⊗ Pc).
Proof.
rewrite !to_Fnd_compE !Fnd_cast !to_Fnd_tenE.
rewrite -[X in (_ \· X \· _)%FND](ten1F (to_Fnd Pc)).
rewrite (fnd_ten_dot [> deltav i; deltav idx0 <] (\1 : 'F[HL]_(mathcomp.boot.finset.set0))
  (\1 : 'F[HL]_comp) Pc); last by rewrite disjoint0X.
rewrite dotF1 -[(\1 \· Pc)%FND]to_Fnd_compE comp_lfun1l.
rewrite (fnd_ten_dot [> deltav i; deltav idx0 <] [> deltav idx0; deltav i <]
  Pc (\1 : 'F[HL]_comp)); last by rewrite disjoint0X.
rewrite -[(Pc \· \1)%FND]to_Fnd_compE comp_lfun1r.
by rewrite -to_Fnd_compE outp_comp dv_dot eqxx scale1r.
Qed.
(* the same summand at the lfun level. *)
Fact m1_summand_lfun (Pc : 'F[HL]_comp) (i : 'Idx[HL]_inter) :
  (castlf (mathcomp.boot.finset.set0U comp, mathcomp.boot.finset.setID univ cS)
         ([> deltav i; deltav idx0 <] \⊗ \1) \o Pc) \o
      castlf (mathcomp.boot.finset.setID univ cS, mathcomp.boot.finset.set0U comp)
        ([> deltav idx0; deltav i <] \⊗ \1)
  = castlf (mathcomp.boot.finset.setID univ cS, mathcomp.boot.finset.setID univ cS)
      ([> deltav i; deltav i <] \⊗ Pc).
Proof. by apply/to_Fnd_inj; rewrite m1_summand_fnd Fnd_cast. Qed.
(* the dual of the partial-trace channel `ptraceso cS` is the
   full-space lift `liftf_lf` (with the domain cast onto S).  This is
   the crux: lifting is the Hilbert-Schmidt adjoint of partial trace.
   Here `ptraceso cS : 'F[HL]_univ -> 'F[HL]_(univ :\: cS) = 'F[HL]_comp`. *)
Fact m1_dual_ptraceso (P : 'F[HL]_S) :
  (ptraceso cS)^*o (castlf (esym eqcompl, esym eqcompl) P) = lift_lf (mathcomp.boot.finset.subsetT S) P.
Proof.
rewrite ptraceso_krausso dualso_krausso soE.
under eq_bigr do rewrite adjfK castlf_adj/= tenf_adj adjf1 adj_outp.
set Pc := castlf (esym eqcompl, esym eqcompl) P.
under eq_bigr do rewrite -/univ -/cS -/comp m1_summand_lfun.
rewrite -linear_sum/= -tenf_suml/= sumonb_out.
rewrite /lift_lf /Pc.
apply/to_Fnd_inj; rewrite !Fnd_cast !to_Fnd_tenE Fnd_cast tenFC.
have e1 : mathcomp.boot.finset.setD univ S = inter
  by apply/setP => x; rewrite !inE andbC.
by rewrite (@Fnd_eq1 R L HL _ inter e1).
Qed.
(* trace-duality, labelled form (marginal on the complement carrier). *)
Lemma m1_trace_dual_lab (P : 'F[HL]_S) (rho : 'F[HL]_univ) :
  \Tr (lift_lf (mathcomp.boot.finset.subsetT S) P \o rho)
    = \Tr (castlf (esym eqcompl, esym eqcompl) P \o ptraceso cS rho).
Proof. by rewrite -m1_dual_ptraceso dualso_trlfEV. Qed.
(* h2mx of a square cast = the matrix cast (self-contained copy). *)
Fact m1_h2mx_castlf (A B : {set L}) (eqAB : A = B) (f : 'F[HL]_A) :
  h2mx (castlf (eqAB, eqAB) f) =
  castmx (f_equal (fun T => dim 'H[HL]_T) eqAB,
          f_equal (fun T => dim 'H[HL]_T) eqAB) (h2mx f).
Proof. by case: B / eqAB in f *; rewrite castlf_id castmx_id. Qed.
(* trace cyclicity through a square cast on the left factor. *)
Fact m1_tr_cast_mulC (m n : nat) (e : m = n)
  (A : 'M[C]_m) (B : 'M[C]_n) :
  \tr (castmx (e, e) A *m B) = \tr (A *m castmx (esym e, esym e) B).
Proof. by case: n / e in B *; rewrite !castmx_id. Qed.
(* trace-duality, MATRIX Born-weight form: the S-marginal Born weight
   `\tr (h2mx P *m h2mx(<S-marginal of rho>))`.  This is the bridge
   the bridge rewrites the per-outcome measure trace into. *)
Lemma m1_trace_dual_mx (P : 'F[HL]_S) (rho : 'F[HL]_univ) :
  \Tr (lift_lf (mathcomp.boot.finset.subsetT S) P \o rho)
    = \tr (h2mx P *m
        castmx (f_equal (fun T => dim 'H[HL]_T) eqcompl,
                f_equal (fun T => dim 'H[HL]_T) eqcompl)
          (h2mx (ptraceso cS rho))).
Proof.
rewrite m1_trace_dual_lab /lftrace h2mx_comp m1_h2mx_castlf m1_tr_cast_mulC.
by rewrite (eq_irrelevance (esym _) (f_equal (fun T => dim 'H[HL]_T) eqcompl)).
Qed.
(* `liftf_lf P` (= `lift_lf (subsetT S) P`) restatements, the form a
   downstream consumer holds the lifted POVM element in.  These
   are the lemmas exported for downstream use. *)
Fact m1_liftf_trace_dual_lab (P : 'F[HL]_S) (rho : 'F[HL]_univ) :
  \Tr (liftf_lf P \o rho)
    = \Tr (castlf (esym eqcompl, esym eqcompl) P \o ptraceso cS rho).
Proof. exact: m1_trace_dual_lab. Qed.
Fact m1_liftf_trace_dual_mx (P : 'F[HL]_S) (rho : 'F[HL]_univ) :
  \Tr (liftf_lf P \o rho)
    = \tr (h2mx P *m
        castmx (f_equal (fun T => dim 'H[HL]_T) eqcompl,
                f_equal (fun T => dim 'H[HL]_T) eqcompl)
          (h2mx (ptraceso cS rho))).
Proof. exact: m1_trace_dual_mx. Qed.
End M1TraceDuality.
End FvqkdReal.
