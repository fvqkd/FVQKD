(* -------------------------------------------------------------------- *)
(* def.v — Distance from uniform, two-universal hash family             *)
(* -------------------------------------------------------------------- *)
(* Module: lhl.def                                        *)
(* Source: Tomamichel-Schaffner-Smith-Renner, 'Leftover Hashing       *)
(*   Against Quantum Side Information' (IEEE Trans. IT 57:5524 (2011);  *)
(*   arXiv:1002.2436): def:dist-from-uniform (Def. 3) and the          *)
(*   two-universal / δ-almost-two-universal hash defs (Eq. 7).         *)
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
(* X-basis dephasing channel                                          *)
(* ================================================================== *)
Section DephasingX.
Variable (L : finType) (HL : L -> chsType) (X E : {set L}).
Hypothesis disXE : [disjoint X & E].
Notation S_XE := (X :|: E).
(* dephase_X_so *)
(* infra: no tex label -- fundamental & reusable (mathcomp-style) *)
(* consumer: dephase_X_so is used downstream by the BB84 secrecy proof. *)
Definition dephase_X_so :
    'SO('H[HL]_S_XE) :=
  krausso (fun x : 'Idx[HL]_X =>
    [> deltav x ; deltav x <] \O (\1 : 'F_E) : 'F[HL]_S_XE).
End DephasingX.
(* ================================================================== *)
(* Distance from uniform                                                *)
(* Tomamichel-Schaffner-Smith-Renner, 'Leftover Hashing Against Quantum *)
(* Side Information' (IEEE Trans. IT 57:5524 (2011); arXiv:1002.2436),   *)
(* Def. 3 — tex def:dist-from-uniform                                    *)
(* ================================================================== *)
Section DistFromUniform.
Variable (L : finType) (H : L -> chsType) (A B : {set L}).
Hypothesis disAB : [disjoint A & B].
(* Tomamichel-Schaffner-Smith-Renner, 'Leftover Hashing Against Quantum *)
(* Side Information' (IEEE Trans. IT 57:5524 (2011); arXiv:1002.2436),   *)
(* Def. 3 — tex def:dist-from-uniform                                    *)
(* math: { ½||ρ_AB - ω_A ⊗ σ_B||₁ : σ_B ∈ Pos, Tr σ_B = Tr ρ_B }       *)
Definition dist_uniform_feasible (rhoAB : 'F[H]_(A :|: B)) (v : R) : Prop :=
  exists sigmaB : 'F[H]_B,
    sigmaB \is psdlf /\
    \Tr sigmaB = \Tr (\Tr_(A) rhoAB) /\
    v = (2%:R)^-1 * trnormH
      (rhoAB - (dim 'H[H]_A)%:R^-1 *: ((\1 : 'F_A) \O sigmaB)).
(* Tomamichel-Schaffner-Smith-Renner, 'Leftover Hashing Against Quantum *)
(* Side Information' (IEEE Trans. IT 57:5524 (2011); arXiv:1002.2436),   *)
(* Def. 3 — tex def:dist-from-uniform                                    *)
(* math: d_u(A|B)_ρ := min_{σ_B} ½||ρ_{AB} - ω_A ⊗ σ_B||₁               *)
Definition dist_from_uniform (rhoAB : 'F[H]_(A :|: B)) : R :=
  inf [set v : R | dist_uniform_feasible rhoAB v].
End DistFromUniform.
(* ================================================================== *)
(* Two-universal hash function family                                   *)
(* Tomamichel-Schaffner-Smith-Renner, 'Leftover Hashing Against Quantum *)
(* Side Information' (IEEE Trans. IT 57:5524 (2011); arXiv:1002.2436);   *)
(* two-universal hash def (δ = 1/|Z| case of eqn:almost-two-universal,   *)
(* Eq. 7)                                                                *)
(* ================================================================== *)
Section UniversalHashFamilies.
Variables (Fidx X Z : finType).
(* Tomamichel-Schaffner-Smith-Renner, 'Leftover Hashing Against Quantum *)
(* Side Information' (IEEE Trans. IT 57:5524 (2011); arXiv:1002.2436),   *)
(* Eq. 7 — tex eqn:almost-two-universal                                  *)
(* math: collision probability Pr_f[f(x)=f(x')].                         *)
Definition collision_probability (F : Fidx -> X -> Z) (x x' : X) : R :=
  (#|[set f : Fidx | F f x == F f x']|%:R / #|Fidx|%:R)%R.
(* Tomamichel-Schaffner-Smith-Renner, 'Leftover Hashing Against Quantum *)
(* Side Information' (IEEE Trans. IT 57:5524 (2011); arXiv:1002.2436),   *)
(* Eq. 7 — tex eqn:almost-two-universal                                  *)
(* math: ∀x≠x', Pr_f[f(x)=f(x')] ≤ δ.                                    *)
Definition delta_almost_two_univ (F : Fidx -> X -> Z) (delta : R) : Prop :=
  forall x x' : X, x != x' -> collision_probability F x x' <= delta.
(* Tomamichel-Schaffner-Smith-Renner, 'Leftover Hashing Against Quantum *)
(* Side Information' (IEEE Trans. IT 57:5524 (2011); arXiv:1002.2436),   *)
(* Eq. 7 — tex two-universal hash def — math: the δ = 1/|Z| case of      *)
(* eqn:almost-two-universal.                                            *)
Definition two_univ (F : Fidx -> X -> Z) : Prop :=
  delta_almost_two_univ F (#|Z|%:R^-1)%R.
End UniversalHashFamilies.
Arguments collision_probability {Fidx X Z} F x x'.
Arguments delta_almost_two_univ {Fidx X Z} F delta.
Arguments two_univ {Fidx X Z} F.
Section HashComposition.
Variables (F1idx F2idx X Y Z : finType).
(* Tomamichel-Schaffner-Smith-Renner, 'Leftover Hashing Against Quantum   *)
(* Side Information' (IEEE Trans. IT 57:5524 (2011); arXiv:1002.2436),     *)
(* Lem. 8 (setup) — tex lemma:concatenation                               *)
(* math: family {f2 ∘ f1 | f1∈F1, f2∈F2}.                                *)
Definition hash_comp
    (F1 : F1idx -> X -> Y) (F2 : F2idx -> Y -> Z)
    (fg : (F1idx * F2idx)%type) (x : X) : Z :=
  F2 fg.2 (F1 fg.1 x).
End HashComposition.
Arguments hash_comp {F1idx F2idx X Y Z} F1 F2 fg x.
(* ================================================================== *)
(* Collision entropy                                                    *)
(* ================================================================== *)
Section CollisionEntropy.
Variable (L : finType) (HL : L -> chsType) (A B : {set L}).
Hypothesis disAB : [disjoint A & B].
(* Gamma_C(rho_AB | sigma_B) =
   Tr((I_A tensor sigma_B^{-1/2}) rho (I_A tensor sigma_B^{-1/2}) rho). *)
(* collision_ent *)
(* infra: no tex label -- fundamental & reusable (mathcomp-style) *)
(* consumer: collision_ent is used downstream by the BB84 secrecy proof. *)
Definition collision_ent (rhoAB : 'F[HL]_(A :|: B)) (sigmaB : 'F[HL]_B) : R :=
  let sigma_inv_half := (\1 : 'F_A) \O pinvlf (sqrtH sigmaB) in
  @complex.Re R (\Tr (sigma_inv_half \o rhoAB \o sigma_inv_half \o rhoAB)).
End CollisionEntropy.
(* ================================================================== *)
(* CQ state definition                                                  *)
(* math: ρ_{XE} is classical-quantum if ρ_{XE} = Σ_x |x⟩⟨x|_X ⊗ ρ_E^x *)
(* Uses deltav from hstensor.v: [> deltav x ; deltav x <] = |x⟩⟨x|     *)
(* ================================================================== *)
Section CQState.
Variable (L : finType) (HL : L -> chsType) (X E : {set L}).
Hypothesis disXE : [disjoint X & E].
Notation S_XE := (X :|: E).
(* Strong CQ: (|x⟩⟨x|⊗I_E) ρ (|x'⟩⟨x'|⊗I_E) = 0 as an operator on H_XE,  *)
(* for every x ≠ x'.  This matches tex eqn:cq-state ρ = Σ_x |x⟩⟨x|⊗ρ^x   *)
(* and enables dephase_X_so to act as identity on CQ states.              *)
(* is_cq_state *)
(* infra: no tex label — fundamental & reusable (mathcomp-style) *)
(* consumer: is_cq_state is used downstream by the BB84 secrecy proof. *)
Definition is_cq_state (rhoXE : 'F[HL]_S_XE) : bool :=
  [forall x : 'Idx[HL]_X, forall x' : 'Idx[HL]_X,
    (x' != x) ==>
      ((([> deltav x ; deltav x <] \O (\1 : 'F_E)) \o rhoXE \o
        ([> deltav x' ; deltav x' <] \O (\1 : 'F_E))) == 0)].
End CQState.
(* ================================================================== *)
(* CQ block extraction: ρ_E^{[x]} from CQ state ρ_{XE}                *)
(* Tomamichel-Schaffner-Smith-Renner, 'Leftover Hashing Against Quantum *)
(* Side Information' (IEEE Trans. IT 57:5524 (2011); arXiv:1002.2436),   *)
(* Eq. 14 — tex eqn:cq-state                                             *)
(* math: ρ_E^{[x]} = Tr_X((|x⟩⟨x| ⊗ I_E) ρ_{XE} (|x⟩⟨x| ⊗ I_E))   *)
(* ================================================================== *)
Section CQBlock.
Variable (L : finType) (HL : L -> chsType) (X E : {set L}).
Hypothesis disXE : [disjoint X & E].
Notation S_XE := (X :|: E).
(* Tomamichel-Schaffner-Smith-Renner, 'Leftover Hashing Against Quantum *)
(* Side Information' (IEEE Trans. IT 57:5524 (2011); arXiv:1002.2436),   *)
(* Eq. 14 — tex eqn:cq-state                                             *)
(* math: ρ_E^{[x]} := Tr_X((|x⟩⟨x| ⊗ I_E) ρ_{XE} (|x⟩⟨x| ⊗ I_E))      *)
Definition cq_block (x : 'Idx[HL]_X) (rhoXE : 'F[HL]_S_XE) : 'F[HL]_E :=
  ptrace_castl disXE
    (([> deltav x ; deltav x <] \O (\1 : 'F_E)) \o rhoXE \o
     ([> deltav x ; deltav x <] \O (\1 : 'F_E))).
End CQBlock.
(* ================================================================== *)
(* Post-hash CQ state ρ_{ZFE} after privacy amplification              *)
(* Tomamichel-Schaffner-Smith-Renner, 'Leftover Hashing Against Quantum *)
(* Side Information' (IEEE Trans. IT 57:5524 (2011); arXiv:1002.2436),   *)
(* Eq. 15 — tex eqn:after-extraction-state                               *)
(* math: ρ_{ZFE} = (1/|F|) Σ_f Σ_z |z⟩⟨z| ⊗ |f⟩⟨f| ⊗ ρ_E^{[f,z]}    *)
(*       where ρ_E^{[f,z]} = Σ_{x: f(x)=z} ρ_E^{[x]}                  *)
(*                                                                       *)
(* Z and F are labels in L. The result is a labeled lfun on             *)
(* [set Z] :|: [set F] :|: E, using [> deltav ; deltav <] for    *)
(* the classical registers. The inner ρ_E^{[x]} comes from cq_block.   *)
(* ================================================================== *)
Section PostHashState.
Variable (L : finType) (HL : L -> chsType) (X E Fl Zl : {set L}).
Hypothesis disXE : [disjoint X & E].
Hypothesis disXF : [disjoint X & Fl].
Hypothesis disXZ : [disjoint X & Zl].
Hypothesis disEF : [disjoint E & Fl].
Hypothesis disEZ : [disjoint E & Zl].
Hypothesis disFZ : [disjoint Fl & Zl].
(* Tomamichel-Schaffner-Smith-Renner, 'Leftover Hashing Against Quantum *)
(* Side Information' (IEEE Trans. IT 57:5524 (2011); arXiv:1002.2436),   *)
(* Eq. 15 — tex eqn:after-extraction-state                               *)
(* math: ρ_{ZFE} := (1/|F|) Σ_f Σ_z |z⟩⟨z|⊗|f⟩⟨f|⊗ρ_E^{[f,z]}        *)
Definition post_hash_state
    (Fh : 'Idx[HL]_Fl -> 'Idx[HL]_X -> 'Idx[HL]_Zl)
    (rhoXE : 'F[HL]_(X :|: E)) :
    'F[HL]_(Zl :|: (Fl :|: E)) :=
  let eqZFE := esym (finset.setUA Zl Fl E) in
  castlf (eqZFE, eqZFE)
  ((dim 'H[HL]_Fl)%:R^-1 *:
  \sum_(f : 'Idx[HL]_Fl) \sum_(z : 'Idx[HL]_Zl)
    [> deltav z ; deltav z <] \O [> deltav f ; deltav f <] \O
    (\sum_(x : 'Idx[HL]_X | Fh f x == z) cq_block disXE x rhoXE)).
End PostHashState.
End FvqkdReal.
Arguments collision_probability {R Fidx X Z} F x x'.
Arguments delta_almost_two_univ {R Fidx X Z} F delta.
Arguments two_univ {R Fidx X Z} F.
Arguments hash_comp {F1idx F2idx X Y Z} F1 F2 fg x.
