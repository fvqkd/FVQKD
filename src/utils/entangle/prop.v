(* -------------------------------------------------------------------- *)
(* prop.v — lemmas for the maximally-entangled state + measurement       *)
(* -------------------------------------------------------------------- *)
(* Module: utils.entangle.prop                                      *)
(* TeX source: none (reusable quantum-information infrastructure)        *)
(* -------------------------------------------------------------------- *)
(* Lemmas about the constructions of def.v:                              *)
(*   max_entangled_raw_dot — squared norm of the unnormalized state      *)
(*   max_entangled_norm    — the normalized state is a unit vector       *)
(*   meas_left_cptp / meas_right_cptp — the measurement superops are CPTP*)
(*   meas_left_proj_max_entangled_raw — single-outcome collapse identity *)
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

From utils.entangle Require Export def.

Import Order.TTheory GRing.Theory Num.Theory Num.Def MxLownerOrder.
Import VectorInternalTheory.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Open Scope ring_scope.
Local Open Scope lfun_scope.

Section EntangleProp.
Variable R : realType.
Notation C := (@hermitian.C R).
Notation chsType := (@chsType R).

(* ================================================================== *)
(* Squared norm of the unnormalized maximally-entangled state           *)
(* ================================================================== *)
(* <Phi0 | Phi0> = dim 'H_A.  The double sum over (i, j) collapses on   *)
(* the diagonal i = j (each off-diagonal inner product vanishes by      *)
(* dv_dot), leaving #|'Idx_A| = dim 'H_A ones.                          *)

Lemma max_entangled_raw_dot (L : finType) (HL : L -> chsType)
    (A B : {set L}) (disAB : [disjoint A & B])
    (g : 'Idx[HL]_A -> 'Idx[HL]_B) :
  [< max_entangled_raw g ; max_entangled_raw g >] = (dim ('H[HL]_A))%:R.
Proof.
  rewrite /max_entangled_raw dotp_suml.
  transitivity (\sum_(i : 'Idx[HL]_A) (1 : C)).
  - apply: eq_bigr => i _.
    rewrite dotp_sumr (bigD1 i)//= tenv_dot// !dv_dot !eqxx mulr1.
    rewrite big1 ?addr0// => j /negPf nij.
    by rewrite tenv_dot// !dv_dot eq_sym nij mul0r.
  - by rewrite sumr_const -mulr_natl mulr1 card_idx -dim_setten.
Qed.

(* ================================================================== *)
(* The normalized maximally-entangled state is a unit vector            *)
(* ================================================================== *)

Lemma max_entangled_norm (L : finType) (HL : L -> chsType)
    (A B : {set L}) (disAB : [disjoint A & B])
    (g : 'Idx[HL]_A -> 'Idx[HL]_B) :
  (0 < dim ('H[HL]_A))%N ->
  `| max_entangled g | = 1.
Proof.
  move=> Hdim.
  have c_neq0 : sqrtC (dim ('H[HL]_A))%:R != 0 :> C
    by rewrite sqrtC_eq0 pnatr_eq0 -lt0n.
  rewrite /max_entangled hnormZ hnormE (max_entangled_raw_dot disAB g).
  by rewrite ger0_norm ?invr_ge0 ?sqrtC_ge0 ?ler0n // mulVf.
Qed.

(* ================================================================== *)
(* The two-register measurement superoperators are CPTP                 *)
(* ================================================================== *)
(* Given a trace-preserving Kraus family on the measured half           *)
(* (sum_i (k i)^A o (k i) = 1), tensoring with the identity on the      *)
(* other half preserves trace-preservation, hence the superop is CPTP.  *)

Lemma meas_left_cptp (L : finType) (HL : L -> chsType)
    (A B : {set L}) (disAB : [disjoint A & B])
    (F : finType) (k : F -> 'F[HL]_A) :
  \sum_(i : F) ((k i)^A \o (k i)) = \1 ->
  meas_left B k \is cptp.
Proof.
  move=> Hk.
  rewrite /meas_left; apply/krausso_qcP; rewrite /trace_presv; apply/eqP.
  under eq_bigr=> i _ do
    rewrite tenf_adj adjf1 -(tenf_comp _ _ _ _ disAB) comp_lfun1l.
  by rewrite -tenf_suml Hk tenf11.
Qed.

Lemma meas_right_cptp (L : finType) (HL : L -> chsType)
    (A B : {set L}) (disAB : [disjoint A & B])
    (F : finType) (k : F -> 'F[HL]_B) :
  \sum_(i : F) ((k i)^A \o (k i)) = \1 ->
  meas_right A k \is cptp.
Proof.
  move=> Hk.
  rewrite /meas_right; apply/krausso_qcP; rewrite /trace_presv; apply/eqP.
  under eq_bigr=> i _ do
    rewrite tenf_adj adjf1 -(tenf_comp _ _ _ _ disAB) comp_lfun1r.
  by rewrite -tenf_sumr Hk tenf11.
Qed.

(* ================================================================== *)
(* Single-outcome collapse of the maximally-entangled state             *)
(* ================================================================== *)
(* Applying the projector |x><x| on the A-half (identity on B) to the    *)
(* unnormalized maximally-entangled state Phi0 = sum_i |i> (x) |g i>     *)
(* leaves exactly the paired basis vector |x> (x) |g x>.  This is the    *)
(* operational content of the entanglement-based source: measuring       *)
(* Alice's half in outcome x prepares the signal in the matched state.   *)

Lemma meas_left_proj_max_entangled_raw (L : finType) (HL : L -> chsType)
    (A B : {set L}) (disAB : [disjoint A & B])
    (g : 'Idx[HL]_A -> 'Idx[HL]_B) (x : 'Idx[HL]_A) :
  (([> deltav x ; deltav x <]) \⊗ (\1 : 'F[HL]_B))
    (max_entangled_raw g) = deltav x ⊗v deltav (g x).
Proof.
  rewrite /max_entangled_raw linear_sum/= (bigD1 x)//=.
  rewrite [\sum_(i | i != x) _]big1 ?addr0; last first.
  - move=> i nix.
    by rewrite tenf_apply// id_lfunE outpE dv_dot eq_sym (negbTE nix) scale0r ten0v.
  - by rewrite tenf_apply// id_lfunE outpE dv_dot eqxx scale1r.
Qed.

(* ================================================================== *)
(* Density-level measurement: the projective outcome state             *)
(* ================================================================== *)
(* Applying the single-outcome measurement superoperator meas_left_elem *)
(* (projector |x><x| on the A-half) to the maximally-entangled DENSITY  *)
(* operator |Phi0><Phi0| yields exactly the matched product outcome     *)
(* |x>(x)|g x>  <x|(x)<g x|.  This is the operational source-replacement *)
(* content at the density level: the entangled-then-measured branch and  *)
(* a directly-prepared product state coincide.  The proof is driven by   *)
(* the collapse lemma above (K |Phi0> = |x>(x)|g x>), which is therefore  *)
(* load-bearing here.                                                    *)

Lemma meas_left_elem_max_entangled_raw (L : finType) (HL : L -> chsType)
    (A B : {set L}) (disAB : [disjoint A & B])
    (g : 'Idx[HL]_A -> 'Idx[HL]_B) (x : 'Idx[HL]_A) :
  meas_left_elem B ([> deltav x ; deltav x <])
    [> max_entangled_raw g ; max_entangled_raw g <]
  = [> deltav x ⊗v deltav (g x) ; deltav x ⊗v deltav (g x) <].
Proof.
  set K := ([> deltav x ; deltav x <]) \⊗ (\1 : 'F[HL]_B).
  have HK : K (max_entangled_raw g) = deltav x ⊗v deltav (g x)
    by rewrite /K (meas_left_proj_max_entangled_raw disAB g x).
  have HKadj : K^A = K
    by rewrite /K tenf_adj adjf1 adj_outp.
  (* meas_left_elem K (|Phi><Phi|) = K o |Phi><Phi| o K^A; the conjugation  *)
  (* of an outer product by K is the outer product of K applied to each     *)
  (* ket.  Prove that conjugation identity pointwise, then apply HK.        *)
  have Hconj : forall (u : 'H[HL]_(A :|: B)),
      (K \o [> u ; u <] \o K^A) = [> K u ; K u <].
  { move=> u; apply/lfunP => w.
    by rewrite !comp_lfunE !outpE linearZ/= adj_dotEr. }
  by rewrite /meas_left_elem formsoE -/K Hconj HK.
Qed.

(* ================================================================== *)
(* Source replacement: the full measurement reconstructs the ensemble   *)
(* ================================================================== *)
(* The projective measurement family on the A-half is  k i := |i><i|.   *)
(* Applying the WHOLE measurement superoperator meas_left B k to the     *)
(* entangled density |Phi0><Phi0| produces the classical--quantum        *)
(* ensemble  sum_x |x (x) g x><x (x) g x| : each Alice outcome x is      *)
(* paired with the signal state |g x> it steers.  This is the formal     *)
(* source-replacement identity --- the entanglement-based measurement    *)
(* reproduces exactly the directly-prepared ensemble --- proved from     *)
(* first principles via kraussoE and the per-outcome collapse.           *)
Definition proj_family (L : finType) (HL : L -> chsType) (A : {set L})
    (i : 'Idx[HL]_A) : 'F[HL]_A := [> deltav i ; deltav i <].

Fact meas_left_max_entangled_raw_ensemble (L : finType) (HL : L -> chsType)
    (A B : {set L}) (disAB : [disjoint A & B])
    (g : 'Idx[HL]_A -> 'Idx[HL]_B) :
  meas_left B (@proj_family L HL A)
    [> max_entangled_raw g ; max_entangled_raw g <]
  = \sum_(x : 'Idx[HL]_A)
      [> deltav x ⊗v deltav (g x) ; deltav x ⊗v deltav (g x) <].
Proof.
  rewrite /meas_left kraussoE.
  apply: eq_bigr => x _.
  have := meas_left_elem_max_entangled_raw disAB g x.
  by rewrite /meas_left_elem formsoE /proj_family => ->.
Qed.

(* ================================================================== *)
(* Orthonormality of the matrix-level Bell basis kets                   *)
(* ================================================================== *)
(* The kets e_i := |i> (x) |0> (x) |i> are orthonormal: <e_i | e_j> =   *)
(* [i = j].  Each factor reduces by the delta-matrix product.  This is   *)
(* the genuine content certifying rho_eb (def.v) is the normalized Bell  *)
(* state (positive by form_psd; unit-trace = this summed over i).        *)

Lemma eb_basis_dot (n : nat) (i j : 'I_(2 ^ n)) :
  (((delta_mx i (0:'I_1) *t delta_mx (0:'I_1) (0:'I_1)) *t delta_mx i (0:'I_1))^*t
   *m ((delta_mx j (0:'I_1) *t delta_mx (0:'I_1) (0:'I_1)) *t delta_mx j (0:'I_1)))
  = (if i == j then 1%:M else 0) :> 'M[C]_1.
Proof.
  have D1 : delta_mx (0:'I_1) (0:'I_1) = (1%:M : 'M[C]_1).
  by apply/matrixP=> a b; rewrite !ord1 !mxE !eqxx.
  rewrite !adjmx_tens !adjmx_delta !tensmx_mul !mul_delta_mx_cond eqxx D1 mulr1n.
  by case: (i == j); rewrite ?mulr1n ?mulr0n ?tensmx11 ?tens0mx ?tensmx0.
Qed.

(* rho_eb n is a genuine density operator: positive semi-definite (it is  *)
(* an outer product, form_psd) and unit-trace (the Bell components are     *)
(* orthonormal, eb_basis_dot, so the squared norm is 2^n, cancelled by     *)
(* the (sqrt 2^n)^-1 normalization).                                       *)

Fact rho_eb_den1 (n : nat) : rho_eb R n \is den1mx.
Proof.
  apply/den1mxP; split; first exact: form_psd.
  (* Orthonormality at the entry level: <e_i | e_j> = sum_k conj(e_i k)(e_j k). *)
  have gram : forall i j : 'I_(2 ^ n),
    \sum_(k : 'I_(2 ^ n * 1 * 2 ^ n))
      (((delta_mx i (0:'I_1) *t delta_mx (0:'I_1) (0:'I_1)) *t delta_mx i (0:'I_1)
        : 'cV[C]_(2 ^ n * 1 * 2 ^ n)) k 0)^*
      * (((delta_mx j (0:'I_1) *t delta_mx (0:'I_1) (0:'I_1)) *t delta_mx j (0:'I_1)
        : 'cV[C]_(2 ^ n * 1 * 2 ^ n)) k 0)
    = (if i == j then 1 else 0 : C).
  { move=> i j.
  transitivity
    ((((delta_mx i (0:'I_1) *t delta_mx (0:'I_1) (0:'I_1)) *t delta_mx i (0:'I_1)
       : 'cV[C]_(2 ^ n * 1 * 2 ^ n))^*t
      *m ((delta_mx j (0:'I_1) *t delta_mx (0:'I_1) (0:'I_1)) *t delta_mx j (0:'I_1))) 0 0).
  - symmetry; rewrite mxE; apply: eq_bigr => k _; by rewrite mxE_adj.
  - by rewrite (eb_basis_dot i j); case: (i == j); rewrite mxE. }
  rewrite /rho_eb mxtrace_mulC trace_mx11 /rho_eb_vec.
  rewrite adjmxZ -scalemxAl -scalemxAr scalerA mxE mxE.
  under eq_bigr => k _ do rewrite mxE_adj !summxE rmorph_sum mulr_suml.
  under eq_bigr => k _ do under eq_bigr => i _ do rewrite mulr_sumr.
  rewrite exchange_big/=.
  under eq_bigr => i _ do rewrite exchange_big/=.
  under eq_bigr => i _ do under eq_bigr => j _ do rewrite gram.
  rewrite (eq_bigr (fun=> 1)); last first.
  move=> i _; rewrite (bigD1 i)//= eqxx big1 ?addr0// => j /negPf nij.
  by rewrite eq_sym nij.
  rewrite sumr_const card_ord.
  rewrite geC0_conj ?invr_ge0 ?sqrtC_ge0 ?ler0n// -expr2 exprVn sqrtCK.
  by rewrite mulVf// pnatr_eq0 expn_eq0/=.
Qed.

End EntangleProp.
