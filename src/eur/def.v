(* -------------------------------------------------------------------- *)
(* def.v — Core definitions for the smooth-entropy UCR paper           *)
(* -------------------------------------------------------------------- *)
(* Module: eur.def                                        *)
(* Paper: Tomamichel & Renner, 'The Uncertainty Relation for Smooth     *)
(*   Entropies' (PRL 106, 110506 (2011); arXiv:1009.2015).             *)
(* tex labels: eqn:overlap, post-measurement forms,                     *)
(*             Stinespring dilation U in proof of thm:mother            *)
(* -------------------------------------------------------------------- *)
(* This file formalises the matrix-level core definitions of the paper: *)
(*   - POVM predicate (tex: POVMs X={M_x}, Z={N_z} on A)               *)
(*   - Overlap c and q (tex eqn:overlap)                               *)
(*   - Post-measurement states ρ_XB, ρ_ZC (tex: text after Theorem 1) *)
(*   - ε-close predicate ρ ≈_ε τ (tex: purified-distance definition)   *)
(*   - EUR dual-definition surface ρ_AC and H^ε_max := - H^ε_min       *)
(*     (tex eqn:dual)                                                   *)
(*   - Stinespring dilation U (tex: proof of Theorem 1)               *)
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
From utils Require Import exports.
From entropy Require Import def.
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
(* ε-close predicate ρ ≈_ε τ                                            *)
(* Paper: Tomamichel & Renner, 'The Uncertainty Relation for Smooth     *)
(*   Entropies" (PRL 106, 110506 (2011); arXiv:1009.2015), "Smooth     *)
(*   Entropies' section (purified-distance definition).                 *)
(* math: ρ ≈_ε τ iff τ ∈ S_≤(H) and P(ρ,τ) ≤ ε                          *)
(* ================================================================== *)
Section EpsClose.
Variable (na nb : nat).
Definition eps_close (eps : R) (rho tau : 'M[C]_(na * nb)) : bool :=
  (tau \is denmx) && (pur_dist_mx tau rho <= eps).
End EpsClose.
(* ================================================================== *)
(* POVM predicate on matrices                                           *)
(* Paper: Tomamichel & Renner, 'The Uncertainty Relation for Smooth     *)
(*   Entropies' (PRL 106, 110506 (2011); arXiv:1009.2015) — POVMs with  *)
(*   elements M_x, N_z on A (intro).                                     *)
(*                                                                       *)
(* A POVM on A is a family {M_x} of PSD operators on H_A summing to I. *)
(* ================================================================== *)
Section Povm.
Variable (na nx : nat).
(* Paper: Tomamichel & Renner (PRL 106, 110506 (2011); arXiv:1009.2015) *)
(*   — POVMs X={M_x}, Z={N_z} on A.                                      *)
(* math: {M_x} is a POVM iff ∀ x, M_x ≥ 0  ∧  Σ_x M_x = I_A              *)
Definition is_povm_mx (M : 'I_nx -> 'M[C]_na) : bool :=
  [forall x, M x \is psdmx] && (\sum_(x < nx) M x == 1%:M).
End Povm.
(* Computational-basis projective POVM. *)
(* tex: implicit standard measurement in BB84 Z/X basis.                *)
Definition std_projective_povm (n : nat) : 'I_n -> 'M[C]_n :=
  fun i => delta_mx i i.
(* Single-qubit X-basis projective POVM, written in computational          *)
(* coordinates: |+><+| and |-><-|.                                       *)
Definition xbasis_sign2 (x z : 'I_2) : C :=
  if (nat_of_ord x == 0%N) || (nat_of_ord z == 0%N) then 1 else -1.
Definition xbasis_vec2 (x : 'I_2) : 'cV[C]_2 :=
  \col_z xbasis_sign2 x z.
Definition x_projective_povm2 (x : 'I_2) : 'M[C]_2 :=
  (((2%:R)^-1)%:C) *: (xbasis_vec2 x *m (xbasis_vec2 x)^*t).
Definition hadamard_mx2 : 'M[C]_2 :=
  \matrix_(i, j) ((((Num.sqrt (2%:R))^-1)%R)%:C *
    (xbasis_sign2 i j)).
(* n-qubit Hadamard transform and its X-basis projective POVM. *)
Definition hadamard_mx (n : nat) : 'M[C]_(2 ^ n) :=
  bigten hadamard_mx2 n.
Definition x_projective_povm (n : nat) :
    'I_(2 ^ n) -> 'M[C]_(2 ^ n) :=
  fun x => (hadamard_mx n)^*t *m delta_mx x x *m hadamard_mx n.
Definition cast_square_povm_mx {n m : nat} (e : n = m)
    (M : 'I_m -> 'M[C]_m) : 'I_n -> 'M[C]_n :=
  fun i => castmx_sq (esym e) (M (cast_ord e i)).
(* ================================================================== *)
(* Measurement overlap c and derived q                                  *)
(* Paper: Tomamichel & Renner (PRL 106, 110506 (2011); arXiv:1009.2015),*)
(*   Eq. (2) — tex eqn:overlap.                                          *)
(* math: c := max_{x,z} ||√M_x √N_z||_∞²                               *)
(*       q := log₂(1/c) = -log₂ c                                      *)
(*                                                                       *)
(* For rank-1 projective measurements M_x = |x⟩⟨x|, N_z = |z⟩⟨z|:       *)
(*   c = max_{x,z} |⟨x|z⟩|² (maximum overlap; the paper's footnote     *)
(*   on Eq. (2)).                                                        *)
(* ================================================================== *)
Section Overlap.
Variable (na nx nz : nat).
(* Measurement overlap c                                                  *)
(* Paper: Tomamichel & Renner (PRL 106, 110506 (2011); arXiv:1009.2015), *)
(*   Eq. (2), the `c` part — tex eqn:overlap.                             *)
(* math: c(X,Z) := max_{x,z} ||√M_x √N_z||_∞²                             *)
Definition overlap_mx
    (M : 'I_nx -> 'M[C]_na) (N : 'I_nz -> 'M[C]_na) : R :=
  \big[maxr/0]_(x < nx)
    \big[maxr/0]_(z < nz)
      (@complex.Re R (i2norm (sqrtmx (M x) *m sqrtmx (N z)))) ^ 2.
(* Paper: Tomamichel & Renner (PRL 106, 110506 (2011); arXiv:1009.2015), *)
(*   Eq. (2): q := log₂(1/c) = -log₂ c — tex eqn:overlap.                *)
(* math: q := -log₂ c                                                   *)
Definition q_of_mx (M : 'I_nx -> 'M[C]_na) (N : 'I_nz -> 'M[C]_na) : R :=
  - log2 (overlap_mx M N).
End Overlap.
(* ================================================================== *)
(* Classical-quantum post-measurement states ρ_XB and ρ_ZC             *)
(* Paper: Tomamichel & Renner (PRL 106, 110506 (2011); arXiv:1009.2015) *)
(*   — definition of ρ_XB, ρ_ZC in the text after Theorem 1.            *)
(*                                                                       *)
(* After measuring A with POVM X = {M_x} and storing the outcome in a   *)
(* classical register X, the joint state on XB is                       *)
(*   ρ_XB := Σ_x |x⟩⟨x| ⊗ τ_B^x,   τ_B^x = tr_AC(M_x ρ_ABC) .           *)
(* Similarly for ρ_ZC with Z = {N_z}.                                   *)
(*                                                                       *)
(* Layout: ρ_ABC : 'M_(na * nb * nc) = 'M_((na * nb) * nc).             *)
(*   - rho_XB: trace out A and C; M_x is tensored with I_BC on the     *)
(*             left. Successive ptrace2 (drop C) + ptrace1 (drop A).    *)
(*   - rho_ZC: trace out A and B; only ptrace1 on the na*nb block.    *)
(*                                                                       *)
(* Tensor product with |x⟩⟨x| = delta_mx x x gives the classical        *)
(* register X.                                                           *)
(* ================================================================== *)
Section PostMeasState.
Variable (na nb nc nx nz : nat).
(* Paper: Tomamichel & Renner (PRL 106, 110506 (2011); arXiv:1009.2015) *)
(*   — ρ_XB definition (text after Theorem 1).                          *)
(* math: ρ_XB = Σ_x |x⟩⟨x| ⊗ tr_AC(√M_x ρ_ABC √M_x)                      *)
(*                                                                       *)
(* The paper's shorthand tr_AC(M_x ρ) for the classical-quantum state    *)
(* is the Kraus form tr_AC(√M_x ρ √M_x): each term is psd, and the      *)
(* sum is a valid (sub-)density matrix on XB.                            *)
Definition rho_XB
    (M : 'I_nx -> 'M[C]_na)
    (rhoABC : 'M[C]_(na * nb * nc)) : 'M[C]_(nx * nb) :=
  \sum_(x < nx) (delta_mx x x *t
    ptrace1 (ptrace2
      ((sqrtmx (M x) *t 1%:M *t 1%:M) *m rhoABC *m
       (sqrtmx (M x) *t 1%:M *t 1%:M)))).
(* Paper: Tomamichel & Renner (PRL 106, 110506 (2011); arXiv:1009.2015) *)
(*   — ρ_ZC definition (text after Theorem 1: Z on A, keep C).          *)
(* math: ρ_ZC = Σ_z |z⟩⟨z| ⊗ tr_AB(√N_z ρ_ABC √N_z)                      *)
Definition rho_ZC
    (N : 'I_nz -> 'M[C]_na)
    (rhoABC : 'M[C]_(na * nb * nc)) : 'M[C]_(nz * nc) :=
  \sum_(z < nz) (delta_mx z z *t
    ptrace1
      ((sqrtmx (N z) *t 1%:M *t 1%:M) *m rhoABC *m
       (sqrtmx (N z) *t 1%:M *t 1%:M))).
End PostMeasState.
(* ================================================================== *)
(* Labelled-register post-measurement state constructions              *)
(* ================================================================== *)
Section LabelledPostMeasurement.
Variable (L : finType) (HL : L -> chsType).
(* Labelled form of `rho_XB M rhoSrc` on the register pair X :|: B. *)
Definition eur_rho_XB
    (X B : {set L}) (disXB : [disjoint X & B])
    (na nb nc nx : nat)
    (rhoSrc : 'M[C]_(na * nb * nc))
    (M : 'I_nx -> 'M[C]_na)
    (dim_eq : nx * nb = dim ('H[HL]_(X :|: B)))
    : 'F[HL]_(X :|: B) :=
  let Q : 'M[C]_(dim 'H[HL]_X * dim 'H[HL]_B) :=
    castmx (tenv_dim disXB, erefl) (@tenv_mxU R L HL X B) in
  let eq_prod := etrans dim_eq (tenv_dim disXB) in
  mx2h (castmx (esym (tenv_dim disXB), esym (tenv_dim disXB))
    (Q *m castmx (eq_prod, eq_prod) (rho_XB M rhoSrc) *m Q^*t)).
(* Labelled form of `rho_ZC N rhoSrc` on the register pair Z :|: C0. *)
Definition eur_rho_ZC
    (Z C0 : {set L}) (disZC : [disjoint Z & C0])
    (na nb nc nz : nat)
    (rhoSrc : 'M[C]_(na * nb * nc))
    (N : 'I_nz -> 'M[C]_na)
    (dim_eq : nz * nc = dim ('H[HL]_(Z :|: C0)))
    : 'F[HL]_(Z :|: C0) :=
  let Q : 'M[C]_(dim 'H[HL]_Z * dim 'H[HL]_C0) :=
    castmx (tenv_dim disZC, erefl) (@tenv_mxU R L HL Z C0) in
  let eq_prod := etrans dim_eq (tenv_dim disZC) in
  mx2h (castmx (esym (tenv_dim disZC), esym (tenv_dim disZC))
    (Q *m castmx (eq_prod, eq_prod) (rho_ZC N rhoSrc) *m Q^*t)).
End LabelledPostMeasurement.
(* ================================================================== *)
(* EUR dual-definition surface for smooth max-entropy                  *)
(* Paper: Tomamichel & Renner (PRL 106, 110506 (2011);                 *)
(*   arXiv:1009.2015), Eq. (5) — tex eqn:dual                          *)
(*   — math: H^ε_max(A|B)_ρ := -H^ε_min(A|C)_ρ for a purification ρ_ABC.*)
(* ================================================================== *)
Section EurDualMarginal.
Variable (na nb nc : nat).
(* AC marginal of a purification after semantically swapping B and C.      *)
(* Paper: Tomamichel & Renner (PRL 106, 110506 (2011); arXiv:1009.2015),  *)
(*   Eq. (5) — tex eqn:dual — math: ρ_AC := tr_B of a purification ρ_ABC. *)
Definition rho_AC_mx
    (rhoABC : 'M[C]_(na * nb * nc)) : 'M[C]_(na * nc) :=
  ptrace2 (mxswap23 rhoABC).
End EurDualMarginal.
(* ================================================================== *)
(* Stinespring dilation U : A → X ⊗ X' ⊗ A  (and V for Z)              *)
(* Paper: Tomamichel & Renner (PRL 106, 110506 (2011); arXiv:1009.2015) *)
(*   — "Proof of the Main Result" (proof of Theorem 1, tex thm:mother). *)
(*                                                                       *)
(* The isometry U := Σ_x |x⟩_X ⊗ |x⟩_X' ⊗ √M_x acts on H_A and          *)
(* returns a state in H_X ⊗ H_X' ⊗ H_A. Two copies of the outcome are   *)
(* stored; the post-measurement state remains on A. The isometry        *)
(* property U† U = Σ_x M_x = I follows from the POVM axiom.             *)
(* ================================================================== *)
Section Stinespring.
Variable (na nx : nat).
(* Paper: Tomamichel & Renner (PRL 106, 110506 (2011); arXiv:1009.2015), *)
(*   "Proof of the Main Result" — isometry U := Σ_x |x⟩⊗|x⟩⊗√M_x        *)
(*   (this is the single-copy reduction of that double-copy isometry).   *)
(* math: U_single = Σ_x √M_x ⊗ |x⟩ : C^{na} → C^{na · nx}                *)
(*                                                                       *)
(* The single-copy form is isometric (U†U = I) and is the matrix-level   *)
(* primitive. The paper's double-copy form Σ_x |x⟩ ⊗ |x⟩ ⊗ √M_x is a    *)
(* tensor of an auxiliary copy register with this single-copy isometry. *)
Definition stinespring_U (M : 'I_nx -> 'M[C]_na) : 'M[C]_(na * nx, na) :=
  \matrix_(i, j)
    sqrtmx (M (mxtens_unindex i).2) (mxtens_unindex i).1 j.
(* Paper: Tomamichel & Renner (PRL 106, 110506 (2011); arXiv:1009.2015), *)
(*   "Proof of the Main Result" (double-copy Stinespring isometry U).    *)
(* math: U = Σ_x |x⟩_X ⊗ |x⟩_{X'} ⊗ √M_x : A → X ⊗ X' ⊗ A               *)
Definition stinespring_U2 (M : 'I_nx -> 'M[C]_na)
    : 'M[C]_((nx * nx) * na, na) :=
  \matrix_(i, j)
    let xxa := mxtens_unindex i in
    let xx := mxtens_unindex xxa.1 in
    (xx.1 == xx.2)%:R * sqrtmx (M xx.1) xxa.2 j.
End Stinespring.
(* ================================================================== *)
(* Lifted tripartite states ρ_XX'ABC, ρ_ZZ'ABC                         *)
(* Paper: Tomamichel & Renner (PRL 106, 110506 (2011); arXiv:1009.2015),*)
(*   "Proof of the Main Result": ρ_XX'ABC := U ρ_ABC U†,               *)
(*   ρ_ZZ'ABC := V ρ_ABC V†.                                            *)
(*                                                                       *)
(* ρ_XX'ABC := U ρ_ABC U†, living on X ⊗ X' ⊗ A ⊗ B ⊗ C.               *)
(* At matrix level, with U : 'M_(na * nx, na) and lift U ⊗ I_BC:        *)
(*   ρ_XX'ABC : 'M_((na * nx) * nb * nc)  (na first, consistent with    *)
(*              rho_ABC layout and the single-copy U structure)         *)
(* The paper's double-copy form lives on a larger space nx * nx * na.  *)
(* We give the single-copy wrapper here; the double-copy is obtained   *)
(* by further tensoring with an nx-dim identity register.               *)
(* ================================================================== *)
Section RhoLift.
Variable (na nb nc nx nz : nat).
(* path: eur:ptrace_XpAC_assoc -> eur:entropic_uncertainty_relation -> *)
(*   eur:entropic_uncertainty_relation -> *)
(*   bb84:entropic_uncertainty_relation_bb84 -> bb84:bb84_secret *)
Definition ptrace_XpAC_assoc {x xp a b c : nat} :
  (((x * xp) * a) * b) * c = ((x * (xp * a)) * b) * c.
Proof.
  by rewrite !mulrA.
Defined.
(* path: eur:ptrace_ZpAB_assoc -> eur:entropic_uncertainty_relation -> *)
(*   eur:entropic_uncertainty_relation -> *)
(*   bb84:entropic_uncertainty_relation_bb84 -> bb84:bb84_secret *)
Definition ptrace_ZpAB_assoc {z zp a b c : nat} :
  c * (((z * zp) * a) * b) = (c * z) * ((zp * a) * b).
Proof.
  by rewrite !mulrA.
Defined.
(* path: eur:ptrace_XpA_assoc -> eur:entropic_uncertainty_relation -> *)
(*   eur:entropic_uncertainty_relation -> *)
(*   bb84:entropic_uncertainty_relation_bb84 -> bb84:bb84_secret *)
Definition ptrace_XpA_assoc {x xp a b : nat} :
  b * (x * xp * a) = (b * x) * (xp * a).
Proof.
  by rewrite !mulrA.
Defined.
(* Paper: Tomamichel & Renner (PRL 106, 110506 (2011); arXiv:1009.2015),*)
(*   "Proof of the Main Result" — math: ρ_XX'ABC := U ρ_ABC U†.         *)
Definition rho_XXpABC
    (M : 'I_nx -> 'M[C]_na)
    (rhoABC : 'M[C]_(na * nb * nc))
    : 'M[C]_(((nx * nx) * na) * nb * nc) :=
  ((stinespring_U2 M) *t (1%:M : 'M[C]_nb) *t
    (1%:M : 'M[C]_nc)) *m rhoABC *m
  ((stinespring_U2 M) *t (1%:M : 'M[C]_nb) *t
    (1%:M : 'M[C]_nc))^*t.
(* Paper: Tomamichel & Renner (PRL 106, 110506 (2011); arXiv:1009.2015),  *)
(*   "Proof of the Main Result" (ρ_ZZ'ABC via Stinespring V).             *)
(* math: ρ_{Z'ABC} := V ρ_ABC V†                                          *)
Definition rho_ZZpABC
    (N : 'I_nz -> 'M[C]_na)
    (rhoABC : 'M[C]_(na * nb * nc))
    : 'M[C]_(((nz * nz) * na) * nb * nc) :=
  ((stinespring_U2 N) *t (1%:M : 'M[C]_nb) *t
    (1%:M : 'M[C]_nc)) *m rhoABC *m
  ((stinespring_U2 N) *t (1%:M : 'M[C]_nb) *t
    (1%:M : 'M[C]_nc))^*t.
(* Paper: Tomamichel & Renner (PRL 106, 110506 (2011); arXiv:1009.2015),  *)
(*   "Proof of the Main Result" — ρ_ZZ'AB appears in Eqs. (6)-(7)        *)
(*   (marginal onto Z'AB by tracing out C).                              *)
(* math: ρ_{Z'AB} := tr_C (ρ_{Z'ABC})                                     *)
Definition rho_ZZpAB
    (N : 'I_nz -> 'M[C]_na)
    (rhoABC : 'M[C]_(na * nb * nc))
    : 'M[C]_((nz * nz) * na * nb) :=
  ptrace2 (rho_ZZpABC N rhoABC).
(* Paper: Tomamichel & Renner (PRL 106, 110506 (2011); arXiv:1009.2015), *)
(*   "Proof of the Main Result" — regroup `rho_ZZ'ABC` as              *)
(*   `(Z*C)*(Z'*A*B)` (CoqQ index bookkeeping for the proof).           *)
Definition rho_ZC_ZpAB
    (N : 'I_nz -> 'M[C]_na)
    (rhoABC : 'M[C]_(na * nb * nc))
    : 'M[C]_((nz * nc) * (nz * na * nb)) :=
  \matrix_(i, j)
    let iZE := mxtens_unindex i in
    let jZE := mxtens_unindex j in
    let izc := mxtens_unindex iZE.1 in
    let jzc := mxtens_unindex jZE.1 in
    let ienvB := mxtens_unindex iZE.2 in
    let jenvB := mxtens_unindex jZE.2 in
    let izpa := mxtens_unindex ienvB.1 in
    let jzpa := mxtens_unindex jenvB.1 in
    rho_ZZpABC N rhoABC
      (mxtens_index (mxtens_index
        (mxtens_index (mxtens_index (izc.1, izpa.1), izpa.2), ienvB.2),
        izc.2))
      (mxtens_index (mxtens_index
        (mxtens_index (mxtens_index (jzc.1, jzpa.1), jzpa.2), jenvB.2),
        jzc.2)).
(* Paper: Tomamichel & Renner (PRL 106, 110506 (2011); arXiv:1009.2015),*)
(*   "Proof of the Main Result" — "ρ_XB and ρ_ZC are marginals".        *)
Definition ptrace_XpAC
    (rhoXXpABC : 'M[C]_(((nx * nx) * na) * nb * nc)) : 'M[C]_(nx * nb) :=
  let rho1 : 'M[C]_((nx * (nx * na)) * nb * nc) :=
    castmx_sq ptrace_XpAC_assoc rhoXXpABC in
  let rho2 : 'M[C]_((nx * (nx * na)) * nb) := ptrace2 rho1 in
  let rho3 : 'M[C]_(nb * (nx * (nx * na))) := mxswap rho2 in
  let rho4 : 'M[C]_((nb * nx) * (nx * na)) :=
    castmx_sq (mulnA nb nx (nx * na)) rho3 in
  let rho5 : 'M[C]_(nb * nx) := ptrace2 rho4 in
  mxswap rho5.
(* Paper: Tomamichel & Renner (PRL 106, 110506 (2011); arXiv:1009.2015),*)
(*   "Proof of the Main Result" — "ρ_XB and ρ_ZC are marginals".        *)
Definition ptrace_ZpAB
    (rhoZZpABC : 'M[C]_(((nz * nz) * na) * nb * nc)) : 'M[C]_(nz * nc) :=
  let rho1 : 'M[C]_(nc * (((nz * nz) * na) * nb)) := mxswap rhoZZpABC in
  let rho2 : 'M[C]_((nc * nz) * ((nz * na) * nb)) :=
    castmx_sq ptrace_ZpAB_assoc rho1 in
  let rho3 : 'M[C]_(nc * nz) := ptrace2 rho2 in
  mxswap rho3.
End RhoLift.
(* ================================================================== *)
(* Partial isometry W := U V†                                           *)
(* Paper: Tomamichel & Renner (PRL 106, 110506 (2011); arXiv:1009.2015),*)
(*   "Proof of the Main Result" — the partial isometry W := U V†.       *)
(*                                                                       *)
(* W takes Z ⊗ Z' ⊗ A to X ⊗ X' ⊗ A via W := U V†.                    *)
(* In the single-copy form, U has type 'M_(na * nx, na) and V has type *)
(* 'M_(na * nz, na); hence W has type 'M_(na * nx, na * nz).           *)
(* ================================================================== *)
Section PartialIso.
Variable (na nx nz : nat).
(* Paper: Tomamichel & Renner (PRL 106, 110506 (2011); arXiv:1009.2015),  *)
(*   "Proof of the Main Result".                                          *)
(* math: W := U V†                                                        *)
Definition partial_iso_W
    (M : 'I_nx -> 'M[C]_na) (N : 'I_nz -> 'M[C]_na)
    : 'M[C]_((nx * nx) * na, (nz * nz) * na) :=
  stinespring_U2 M *m (stinespring_U2 N)^*t.
End PartialIso.
(* ================================================================== *)
(* Purification reshape                                                *)
(* ================================================================== *)
Section PurificationReshapeDef.
(* Associativity equation for the castmx: (na*nb*nc)*nd = na*nb*(nc*nd). *)
Definition purif_reshape_eq (na nb nc nd : nat) :
  (na * nb * nc * nd = na * nb * (nc * nd))%N :=
  esym (mulnA (na * nb) nc nd).
(* Cast the purification output 'M_((na*nb*nc)*nd) into
   'M_(na*nb*(nc*nd)) so the pure-case hypothesis applies. *)
Definition purif_reshape {na nb nc nd : nat}
    (rho : 'M[C]_(na * nb * nc * nd)) : 'M[C]_(na * nb * (nc * nd)) :=
  castmx (purif_reshape_eq na nb nc nd, purif_reshape_eq na nb nc nd) rho.
End PurificationReshapeDef.
End FvqkdReal.
Arguments std_projective_povm {R} n.
Arguments xbasis_sign2 {R} x z.
Arguments xbasis_vec2 {R} x.
Arguments x_projective_povm2 {R} x.
Arguments hadamard_mx2 {R}.
Arguments hadamard_mx {R} n.
Arguments x_projective_povm {R} n x.
Arguments cast_square_povm_mx {R n m} e M i.
