(* -------------------------------------------------------------------- *)
(* def.v — Core entropy definitions: Hmin, Hmax, eps-ball, smooth H     *)
(* -------------------------------------------------------------------- *)
(* Module: entropy.def                              *)
(* Source: Tomamichel, 'A Framework for Non-Asymptotic Quantum          *)
(*   Information Theory' (PhD thesis, arXiv:1203.2142). Def. 4.1         *)
(*   (tex df:min-entropy), Def. 4.2 (tex df:max-entropy), Def. 5.1      *)
(*   (ε-Ball, tex df:ball), Def. 5.2 (Smooth Entropies, tex df:smooth). *)
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
From quantum.dirac Require Import hstensor.

Import Order.TTheory GRing.Theory Num.Theory Num.Def MxLownerOrder.
Import VectorInternalTheory.

(* --- FVQKD imports --- *)
From utils Require Import exports.

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
(* Matrix-level entropy primitives.                                     *)
(* ================================================================== *)

Section MatrixEntropyDefinitions.
Variable (na nb : nat).

Definition mmix_mx (n : nat) : 'M[C]_n :=
  (n%:R^-1)%:C *: 1%:M.

(* Matrix SDP-style min-entropy primitive used by the labelled bridge    *)
(* lemmas and by the EUR matrix core.                                    *)
Definition hmin_mx (rho : 'M[C]_(na * nb)) : R :=
  - log2 (inf [set v : R | exists sigma : 'M[C]_nb,
    sigma \is psdmx /\
    (1%:M *t sigma - rho) \is psdmx /\
    v = @complex.Re R (\tr sigma)]).

Definition smooth_hmin_mx (eps : R) (rho : 'M[C]_(na * nb)) : R :=
  sup [set v : R | exists tau : 'M[C]_(na * nb),
    ((tau \is denmx) && (0 < @complex.Re R (\tr tau))) &&
    (pur_dist_mx tau rho <= eps) /\
    v = hmin_mx tau].

(* Tomamichel thesis (arXiv:1203.2142), Definition 4.2 — tex df:max-entropy. *)
(* Normalized-witness / generalized-fidelity rewrite:      *)
(* sigma is normalized, the second argument is pi_A tensor sigma_B, and   *)
(* the d_A factor stays outside gfidelity.                                *)
Definition hmax_mx (rho : 'M[C]_(na * nb)) : R :=
  sup [set v : R | exists sigma : 'M[C]_nb,
    sigma \is den1mx /\
    elog2 (na%:R * (gfidelity rho (mmix_mx na *t sigma)) ^+ 2) = v%:E].

Definition smooth_hmax_mx (eps : R) (rho : 'M[C]_(na * nb)) : R :=
  inf [set v : R | exists tau : 'M[C]_(na * nb),
    ((tau \is denmx) && (0 < @complex.Re R (\tr tau))) &&
    (pur_dist_mx tau rho <= eps) /\
    v = hmax_mx tau].

End MatrixEntropyDefinitions.

(* ================================================================== *)
(* Min-entropy H_min(A|B)_ρ                                             *)
(* Tomamichel thesis (arXiv:1203.2142), Definition 4.1 — tex df:min-entropy. *)
(* math: H_min(A|B)_ρ := -log inf{ Tr σ : I_A⊗σ_B ≥ ρ_{AB}, σ ≥ 0 }  *)
(*                                                                       *)
(* The definitions are parameterized by system S and conditioning        *)
(* subsystem T. The state lives on 'F_S, and σ lives on 'F_T.          *)
(* The identity acts on S :\: T (the "non-conditioning" part).           *)
(* A cast (S:\:T) :|: T = S is absorbed into the definition.            *)
(* ================================================================== *)

Section MinEntropy.
Variable (L : finType) (H : L -> chsType).
Variable (S T : {set L}).

(* Refinement: use (S :&: T) instead of T so the cast identity
   (S :\: T) :|: (S :&: T) = S holds unconditionally via setID.
   Math is unchanged when T ⊆ S (S ∩ T = T); Definition stays total. *)
Let eqST : (S :\: T) :|: (S :&: T) = S.
Proof.
  by rewrite finset.setUC finset.setID.
Defined.

(* Tomamichel thesis (arXiv:1203.2142), Definition 4.1 — tex df:min-entropy. *)
(* math: { Tr σ : σ ∈ Pos(H_T), I_{S\T} ⊗ σ_T ≥ ρ_S } (feasible set)  *)
Definition phi_min_feasible (rhoS : 'F[H]_S) (v : R) : Prop :=
  exists sigma : 'F[H]_(S :&: T),
    sigma \is psdlf /\
    (castlf (eqST, eqST) ((\1 : 'F_(S :\: T)) \O sigma) - rhoS) \is psdlf /\
    v = @complex.Re R (\Tr sigma).

Definition phi_min (rhoS : 'F[H]_S) : R :=
  inf [set v : R | phi_min_feasible rhoS v].

(* Tomamichel thesis (arXiv:1203.2142), Definition 4.1 — tex df:min-entropy. *)
(* math: H_min(A|B)_ρ := -log₂ Φ_min(ρ)                                 *)
Definition hmin (rhoS : 'F[H]_S) : R :=
  - log2 (phi_min rhoS).

(* Tomamichel thesis (arXiv:1203.2142), Definition 4.1 — tex df:min-entropy. *)
(* math: extended-real form of H_min(A|B)_ρ := -elog₂ Φ_min(ρ) *)
(*       so that Φ_min(ρ)=0 contributes +∞. The BB84 paper only uses     *)
(*       finite real entropy values; Coq keeps this branch explicit for  *)
(*       Tomamichel infrastructure and converts to `hmin` under positivity.   *)
Definition hminE (rhoS : 'F[H]_S) : extended R :=
  - elog2 (phi_min rhoS).

End MinEntropy.

(* ================================================================== *)
(* Max-entropy H_max(A|B)_ρ                                             *)
(* Tomamichel thesis (arXiv:1203.2142), Definition 4.2 — tex df:max-entropy. *)
(* math: H_max(A|B)_ρ in the normalized generalized-fidelity rewrite:    *)
(*   sup_σ log(d_A * Fbar(ρ_AB, π_A⊗σ_B)^2), σ normalized.               *)
(* LHL appendix `def:max` defines smooth max-entropy by min/max duality  *)
(* and also introduces an alternative max-entropy. This file takes       *)
(* Tomamichel's fidelity definition as primitive; dual characterizations are  *)
(* theorem-level bridges, not separate primitive definitions.            *)
(* ================================================================== *)

Section MaxEntropy.
Variable (L : finType) (H : L -> chsType).
Variable (S T : {set L}).

(* Refinement: same rewrite as eqST — use (S :&: T) for totality. *)
Let eqST_max : (S :\: T) :|: (S :&: T) = S.
Proof.
  by rewrite finset.setUC finset.setID.
Defined.

(* Tomamichel thesis (arXiv:1203.2142), Definition 4.2 — tex df:max-entropy. *)
(* math: finite branch of the normalized generalized-fidelity rewrite     *)
(*   { elog₂(d_A * Fbar(ρ, π_(S\T) ⊗ σ)^2) : σ ∈ S_=(H_T) }.             *)
(* This is the form used in Tomamichel's min-max duality proof after max/def;  *)
(* zero-fidelity witnesses contribute -∞ in tex and are omitted here.     *)
Definition hmax_feasible (rhoS : 'F[H]_S) (v : R) : Prop :=
  exists sigma : 'F[H]_(S :&: T),
    sigma \is den1lf /\
    elog2 ((dim 'H[H]_(S :\: T))%:R *
      (gfid rhoS
      (castlf (eqST_max, eqST_max)
        ((((dim 'H[H]_(S :\: T))%:R^-1)%:C *:
          ((\1 : 'F_(S :\: T)) \O sigma))))) ^+ 2) = v%:E.

(* Tomamichel thesis (arXiv:1203.2142), Definition 4.2 — tex df:max-entropy. *)
(* math: H_max(A|B)_ρ := sup of the finite normalized-gfid branch above.  *)
Definition hmax (rhoS : 'F[H]_S) : R :=
  sup [set v : R | hmax_feasible rhoS v].

(* Tomamichel thesis (arXiv:1203.2142), Definition 4.2 — tex df:max-entropy. *)
(* math: extended-real form of H_max(A|B)_ρ.  This keeps the   *)
(*       zero-fidelity branch at -∞ instead of MathComp's totalized      *)
(*       real `log2(0)=0` convention. The zero-state case is therefore   *)
(*       represented as -∞ here and bridged back to `hmax` only when a   *)
(*       finite positive-fidelity witness is available.                  *)
Definition hmaxE (rhoS : 'F[H]_S) : extended R :=
  ereal_sup [set v : extended R | exists sigma : 'F[H]_(S :&: T),
    sigma \is den1lf /\
    v = elog2 ((dim 'H[H]_(S :\: T))%:R *
      (gfid rhoS
      (castlf (eqST_max, eqST_max)
        ((((dim 'H[H]_(S :\: T))%:R^-1)%:C *:
          ((\1 : 'F_(S :\: T)) \O sigma))))) ^+ 2)].

End MaxEntropy.

(* ================================================================== *)
(* ε-ball of sub-normalized states around ρ                             *)
(* ================================================================== *)

Section EpsBall.
Variable (L : finType) (H : L -> chsType).
Variable (S : {set L}).

(* Tomamichel thesis (arXiv:1203.2142), Definition 5.1 (ε-Ball) — tex df:ball. *)
(* math: B^ε(ρ) := { τ ∈ S_≤(H) : P(τ,ρ) ≤ ε }                        *)
Definition eps_ball (eps : R) (rho tau : 'F[H]_S) : bool :=
  ((tau \is psdlf) && (0 < @complex.Re R (\Tr tau)) &&
    (@complex.Re R (\Tr tau) <= 1)) && (pur_dist tau rho <= eps).

End EpsBall.

(* ================================================================== *)
(* Smooth min- and max-entropies                                         *)
(* ================================================================== *)

Section SmoothEntropy.
Variable (L : finType) (H : L -> chsType).
Variable (S T : {set L}).

(* Tomamichel thesis (arXiv:1203.2142), Definition 5.2 (Smooth Entropies) — tex df:smooth. *)
(* math: H_min^ε(A|B)_ρ := sup{ H_min(A|B)_τ : τ ∈ B^ε(ρ) }            *)
Definition smooth_hmin (eps : R) (rhoS : 'F[H]_S) : R :=
  sup [set v : R | exists tauS : 'F[H]_S,
    eps_ball eps rhoS tauS /\ v = hmin T tauS].

(* Tomamichel thesis (arXiv:1203.2142), Definition 5.2 (Smooth Entropies) — tex df:smooth. *)
(* math: extended-real form H_min^ε(A|B)_ρ := sup{ H_min(τ) }  *)
(*       over the ε-ball, where H_min is interpreted on \bar R.         *)
Definition smooth_hminE (eps : R) (rhoS : 'F[H]_S) : extended R :=
  ereal_sup [set v : extended R | exists tauS : 'F[H]_S,
    eps_ball eps rhoS tauS /\ v = hminE T tauS].

(* Tomamichel thesis (arXiv:1203.2142), Definition 5.2 (Smooth Entropies) — tex df:smooth. *)
(* math: H_max^ε(A|B)_ρ := inf{ H_max(A|B)_τ : τ ∈ B^ε(ρ) }            *)
Definition smooth_hmax (eps : R) (rhoS : 'F[H]_S) : R :=
  inf [set v : R | exists tauS : 'F[H]_S,
    eps_ball eps rhoS tauS /\ v = hmax T tauS].

(* Tomamichel thesis (arXiv:1203.2142), Definition 5.2 (Smooth Entropies) — tex df:smooth. *)
(* math: extended-real form H_max^ε(A|B)_ρ :=                  *)
(*       inf{ H_max(A|B)_τ : τ ∈ B^ε(ρ) }, encoded through `- sup -` on  *)
(*       extended reals so -∞ and +∞ branches are not silently collapsed. *)
Definition smooth_hmaxE (eps : R) (rhoS : 'F[H]_S) : extended R :=
  - ereal_sup [set v : extended R | exists tauS : 'F[H]_S,
    eps_ball eps rhoS tauS /\ v = - hmaxE T tauS].

End SmoothEntropy.

(* ================================================================== *)
(* SDP feasible-value sets                                               *)
(* ================================================================== *)

Section SDPValueSets.

Variables (U V : chsType).
Variables (A : 'M[C]_(dim U)) (B : 'M[C]_(dim V)).
Variable (Psi : 'SO(U, V)).

(* primal feasible values used by Tomamichel's SDP strong-duality theorem. *)
Definition sdp_primal_set : set R :=
  [set x : R | exists X : 'M[C]_(dim U),
    [/\ X \is psdmx,
        h2mx (Psi (mx2h X)) >= B &
        x = @complex.Re R (\tr (A *m X))]].

(* dual feasible values used by Tomamichel's SDP strong-duality theorem. *)
Definition sdp_dual_set : set R :=
  [set x : R | exists Y : 'M[C]_(dim V),
    [/\ Y \is psdmx,
        h2mx (Psi^*o (mx2h Y)) <= A &
        x = @complex.Re R (\tr (B *m Y))]].

End SDPValueSets.

End FvqkdReal.

Arguments mmix_mx {R} n.
Arguments hmin_mx {R na nb} rho.
Arguments smooth_hmin_mx {R na nb} eps rho.
Arguments hmax_mx {R na nb} rho.
Arguments smooth_hmax_mx {R na nb} eps rho.
Arguments phi_min_feasible {R L H S} T rhoS v.
Arguments phi_min {R L H S} T rhoS.
Arguments hmin {R L H S} T rhoS.
Arguments hminE {R L H S} T rhoS.
Arguments hmax_feasible {R L H S} T rhoS v.
Arguments hmax {R L H S} T rhoS.
Arguments hmaxE {R L H S} T rhoS.
Arguments eps_ball {R L H S} eps rho tau.
Arguments smooth_hmin {R L H S} T eps rhoS.
Arguments smooth_hminE {R L H S} T eps rhoS.
Arguments smooth_hmax {R L H S} T eps rhoS.
Arguments smooth_hmaxE {R L H S} T eps rhoS.
Arguments sdp_primal_set {R} U V A B Psi.
Arguments sdp_dual_set {R} U V A B Psi.
