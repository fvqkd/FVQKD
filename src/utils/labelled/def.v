(* -------------------------------------------------------------------- *)
(* def.v -- Ambient set-labelled definitions and matrix coordinates     *)
(* -------------------------------------------------------------------- *)
(* Module: utils.labelled.def                             *)
(* TeX source: none (library utility)                                    *)
(* TeX labels: none                                                      *)
(* -------------------------------------------------------------------- *)
(* Owns generic ambient set-labelled definitions that are not tied to a  *)
(* theorem family.  Entropy-specific consequences of these definitions   *)
(* live in entropy/prop.v.                                     *)
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
(* Computational-basis channels                                        *)
(* ================================================================== *)

(* dephaseH *)
(* infra: no tex label -- canonical dephasing in the labelled basis *)
Definition dephaseH (L : finType) (H : L -> chsType) (S : {set L}) :
    'SO[H]_S :=
  krausso (fun x : 'Idx[H]_S => [> deltav x ; deltav x <]).

(* basis_channel *)
(* infra: no tex label -- computational-basis channel between labelled systems *)
Definition basis_channel (L : finType) (H : L -> chsType)
    (S T : {set L}) (f : 'Idx[H]_S -> 'Idx[H]_T) : 'SO[H]_(S, T) :=
  krausso (fun x : 'Idx[H]_S => [> deltav (f x) ; deltav x <]).

(* ================================================================== *)
(* sqrtH / trnormH on ambient labelled systems                         *)
(* ================================================================== *)

Section SqrtLfDefSet.
Variables (L : finType) (H : L -> chsType) (S : {set L}).

(* sqrtH A = Sigma_i sqrt(Re(lambda_i)) |v_i><v_i| via spectral decomposition *)
(* sqrtH *)
(* infra: no tex label -- fundamental & reusable ambient set-labelled utility *)
(* consumer: sqrtH is used downstream by the BB84 secrecy proof. *)
Definition sqrtH (A : 'F[H]_S) : 'F[H]_S :=
  sumoutp (fun i => (Num.sqrt (@complex.Re R (eigenval_all A i)))%:C)
          (eigenvec_all A) (eigenvec_all A).

End SqrtLfDefSet.

Arguments sqrtH {L H S} A.

Section TrNormLfDefSet.
Variables (L : finType) (H : L -> chsType) (S : {set L}).

(* trnormH *)
(* infra: no tex label -- fundamental & reusable ambient set-labelled utility *)
(* consumer: trnormH is used downstream by the BB84 secrecy proof. *)
Definition trnormH (f : 'F[H]_S) : R :=
  @complex.Re R (trnorm (h2mx f)).

End TrNormLfDefSet.

Arguments trnormH {L H S} f.

(* ================================================================== *)
(* POVM-to-classical-output channels                                   *)
(* ================================================================== *)

(* povm_channel *)
(* infra: no tex label -- canonical channel that records a POVM outcome
   in a labelled computational-basis register.                         *)
Definition povm_channel (L : finType) (H : L -> chsType)
    (I : finType) (S T : {set L})
    (out : I -> 'Idx[H]_T) (M : I -> 'F[H]_S) : 'SO[H]_(S, T) :=
  krausso (fun p : I * 'Idx[H]_S =>
    [> deltav (out p.1) ; deltav p.2 <] \o sqrtH (M p.1)).

(* ================================================================== *)
(* Casting partial trace                                               *)
(* ================================================================== *)

Section PTrCastDef.
Variable (L : finType) (H : L -> chsType).

(* ptrace_cast_gen *)
(* infra: no tex label -- fundamental & reusable (mathcomp-style) *)
(* consumer: ptrace_cast_gen is used downstream by the BB84 secrecy proof. *)
Definition ptrace_cast_gen (S T B : {set L})
    (eq : S :\: B = T) (f : 'F[H]_S) : 'F[H]_T :=
  castlf (eq, eq) (\Tr_(B) f).

End PTrCastDef.

Section PTrCastConv.
Variable (L : finType) (H : L -> chsType).

(* ptrace_cast *)
(* infra: no tex label -- fundamental & reusable (mathcomp-style) *)
(* consumer: ptrace_cast is used downstream by the BB84 secrecy proof. *)
Definition ptrace_cast (A B : {set L}) (disAB : [disjoint A & B])
    (f : 'F[H]_(A :|: B)) : 'F[H]_A :=
  ptrace_cast_gen (setDU_r disAB) f.

(* ptrace_castl *)
(* infra: no tex label -- fundamental & reusable (mathcomp-style) *)
(* consumer: ptrace_castl is used downstream by the BB84 secrecy proof. *)
Definition ptrace_castl (A B : {set L}) (disAB : [disjoint A & B])
    (f : 'F[H]_(A :|: B)) : 'F[H]_B :=
  ptrace_cast_gen (setDU_l disAB) f.

(* ptrace_cast3C *)
(* infra: no tex label -- fundamental & reusable (mathcomp-style) *)
(* consumer: ptrace_cast3C is used downstream by the BB84 secrecy proof. *)
Definition ptrace_cast3C (A B C : {set L})
    (disAC : [disjoint A & C]) (disBC : [disjoint B & C])
    (f : 'F[H]_(A :|: B :|: C)) : 'F[H]_(A :|: B) :=
  ptrace_cast_gen (setDU3_C disAC disBC) f.

(* ptrace_cast3B *)
(* infra: no tex label -- fundamental & reusable (mathcomp-style) *)
(* consumer: ptrace_cast3B is used downstream by the BB84 secrecy proof. *)
Definition ptrace_cast3B (A B C : {set L})
    (disAB : [disjoint A & B]) (disBC : [disjoint B & C])
    (f : 'F[H]_(A :|: B :|: C)) : 'F[H]_(A :|: C) :=
  ptrace_cast_gen (setDU3_B disAB disBC) f.

(* ptrace_cast3A *)
(* infra: no tex label -- fundamental & reusable (mathcomp-style) *)
(* consumer: ptrace_cast3A is used downstream by the BB84 secrecy proof. *)
Definition ptrace_cast3A (A B C : {set L})
    (disAB : [disjoint A & B]) (disAC : [disjoint A & C])
    (f : 'F[H]_(A :|: B :|: C)) : 'F[H]_(B :|: C) :=
  ptrace_cast_gen (setDU3_A disAB disAC) f.

End PTrCastConv.

(* ================================================================== *)
(* Ambient bipartite systems as matrix coordinates                     *)
(* ================================================================== *)

Section BipartiteMatrixDefinitions.
Variable (L : finType) (H : L -> chsType).

(* bip_mx *)
(* infra: no tex label -- ambient labelled state in raw matrix shape *)
Definition bip_mx
    (A B : {set L}) (disAB : [disjoint A & B])
    (rhoAB : 'F[H]_(A :|: B))
    : 'M[C]_(dim ('H[H]_A) * dim ('H[H]_B)) :=
  castmx (tenv_dim disAB, tenv_dim disAB) (h2mx rhoAB).

(* biprod_mx *)
(* infra: no tex label -- product-coordinate matrix for a bipartite state *)
Definition biprod_mx
    (A B : {set L}) (disAB : [disjoint A & B])
    (rhoAB : 'F[H]_(A :|: B))
    : 'M[C]_(dim ('H[H]_A) * dim ('H[H]_B)) :=
  let Q : 'M[C]_(dim 'H[H]_A * dim 'H[H]_B) :=
    castmx (tenv_dim disAB, erefl)
      (@tenv_mxU R L H A B) in
  Q^*t *m castmx (tenv_dim disAB, tenv_dim disAB) (h2mx rhoAB) *m Q.

(* biprod_of_mx *)
(* infra: no tex label -- labelled state from product-coordinate matrix *)
Definition biprod_of_mx
    (A B : {set L}) (disAB : [disjoint A & B])
    (rhoAB : 'M[C]_(dim ('H[H]_A) * dim ('H[H]_B)))
    : 'F[H]_(A :|: B) :=
  let Q : 'M[C]_(dim 'H[H]_A * dim 'H[H]_B) :=
    castmx (tenv_dim disAB, erefl)
      (@tenv_mxU R L H A B) in
  mx2h (castmx (esym (tenv_dim disAB), esym (tenv_dim disAB))
    (Q *m rhoAB *m Q^*t)).

End BipartiteMatrixDefinitions.

End FvqkdReal.

Arguments sqrtH {R L H S} A.
Arguments trnormH {R L H S} f.
