(* syntax.v -- Generic QKD protocol language (syntax only)              *)
(* Module: qkd.protocol.syntax                                          *)
(* Paper: Tomamichel-Lim-Gisin-Renner, Nat. Commun. 3:634 (2012),       *)
(*   Tight finite-key analysis for quantum cryptography (Box 1, Table 1). *)
(* Command syntax for QKD protocol descriptions; generic semantics are  *)
(* in semantics.v.                                                      *)

From mathcomp Require Import all_boot all_order all_algebra.
From mathcomp.reals Require Import reals.
From quantum.external Require Import spectral complex.
From quantum Require Import mcextra mcaextra notation hermitian quantum
  cpo mxpred extnum ctopology svd mxnorm hspace.
From quantum.dirac Require Import hstensor.

Import Order.TTheory GRing.Theory Num.Theory Num.Def MxLownerOrder.
Import VectorInternalTheory.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Open Scope ring_scope.
Local Open Scope lfun_scope.

Section StandardLanguage.
Variable R : realType.
Notation chsType := (@chsType R).
Variables (L : finType) (HL : L -> chsType).
Variables Cv V : finType.
Variables (qA : {set L}) (Pvar : Cv).

Definition store := {ffun Cv -> V}.

Definition store_set (s : store) (x : Cv) (v : V) : store :=
  [ffun y => if y == x then v else s y].

Lemma store_set_same (s : store) (x : Cv) (v : V) :
  store_set s x v x = v.
Proof. by rewrite /store_set ffunE eqxx. Qed.

Lemma store_set_other (s : store) (x y : Cv) (v : V) :
  y != x -> store_set s x v y = s y.
Proof. by move=> Hyx; rewrite /store_set ffunE (negbTE Hyx). Qed.

Definition expr := store -> V.
Definition bexpr := store -> bool.
Definition dexpr := store -> V -> R.
Definition qexpr (Q : {set L}) := store -> 'F[HL]_Q.
Definition mexpr (Q : {set L}) := store -> V -> 'F[HL]_Q.

Inductive qkd_cmd : Type :=
  | Cskip
  | Cassign (x : Cv) (e : expr)
  | Csample (x : Cv) (mu : dexpr)
  | Cinit (Q : {set L}) (rho : qexpr Q)
  | Cmeasure (x : Cv) (Q : {set L}) (M : mexpr Q)
  | Cattack (Q : {set L})
  | Cif (b : bexpr) (c1 c2 : qkd_cmd)
  | Cseq (c1 c2 : qkd_cmd).

Fixpoint cmd_wf (c : qkd_cmd) : Prop :=
  match c with
  | Cskip => True
  | Cassign _ _ => True
  | Csample _ mu =>
      forall s, (forall v, 0 <= mu s v) /\ \sum_v mu s v = 1
  | Cinit Q rho =>
      [disjoint Q & qA] /\ forall s, rho s \is den1lf
  | Cmeasure _ Q M =>
      [disjoint Q & qA] /\
      forall s, \sum_v ((M s v)^A \o (M s v)) = \1
  | Cattack Q => [disjoint Q & qA]
  | Cif _ c1 c2 => cmd_wf c1 /\ cmd_wf c2
  | Cseq c1 c2 => cmd_wf c1 /\ cmd_wf c2
  end.

Fixpoint seq_cmd (c1 c2 : qkd_cmd) : qkd_cmd :=
  match c1 with
  | Cskip => c2
  | Cseq c11 c12 => Cseq c11 (seq_cmd c12 c2)
  | _ => if c2 is Cskip then c1 else Cseq c1 c2
  end.

Lemma cmd_seqA : associative seq_cmd.
Proof. move=> x y z; elim: x => //=. 1,2,3,4,5,6: by move=> *; case: (y) => //=; try by move=> *; case: (z). by move=> c1 IH1 c2 IH2; rewrite IH2. Qed.

Fact cmd_seq_skip_l : left_id Cskip seq_cmd.
Proof. by move=> x. Qed.

Fact cmd_seq_skip_r : right_id Cskip seq_cmd.
Proof. by elim=> //= c1 IH1 c2 IH2; rewrite IH2. Qed.

Canonical cmd_seq_monoid : Monoid.law Cskip :=
  Monoid.Law.Pack
    (Monoid.Law.Class
      (SemiGroup.isLaw.Axioms_ seq_cmd cmd_seqA)
      (Monoid.isMonoidLaw.Axioms_ Cskip seq_cmd
        cmd_seq_skip_l cmd_seq_skip_r)).

Definition for_cmd {limit : nat} (body : 'I_limit -> qkd_cmd) : qkd_cmd :=
  \big[seq_cmd/Cskip]_(i <- enum 'I_limit) body i.

Lemma cmd_wf_seq_cmd (c1 c2 : qkd_cmd) :
  cmd_wf c1 -> cmd_wf c2 -> cmd_wf (seq_cmd c1 c2).
Proof.
  elim: c1 c2 => //=.
  1,2,3: by move=> ? ? c2 ? Hc2; case: c2 Hc2 => //=; try by move=> *; split.
  1,2: by [move=> ? ? ? c2 ? Hc2; case: c2 Hc2 => //=; try by move=> *; split | move=> ? c2 ? Hc2; case: c2 Hc2 => //=; try by move=> *; split].
  1,2: by [move=> ? ? ? ? ? c2 ? Hc2; case: c2 Hc2 => //=; try by move=> *; split | move=> ? ? ? IH2 ? Hseq Hc2; split; [exact: Hseq.1 | exact: IH2 _ Hseq.2 Hc2]]. Qed.

Lemma cmd_wf_for_cmd {limit : nat}
    (body : 'I_limit -> qkd_cmd) :
  (forall i, cmd_wf (body i)) -> cmd_wf (for_cmd body).
Proof. by rewrite /for_cmd; elim/big_rec: _ => // i c _ Hc Hbody; apply: cmd_wf_seq_cmd; [exact: Hbody i | exact: Hc]. Qed.

End StandardLanguage.

Arguments Cskip {R L HL Cv V}.
Arguments Cassign {R L HL Cv V} x e.
Arguments Csample {R L HL Cv V} x mu.
Arguments Cinit {R L HL Cv V} Q rho.
Arguments Cmeasure {R L HL Cv V} x Q M.
Arguments Cattack {R L HL Cv V} Q.
Arguments Cif {R L HL Cv V} b c1 c2.
Arguments Cseq {R L HL Cv V} c1 c2.

Declare Scope qkd_scope.
Delimit Scope qkd_scope with qkd.
Bind Scope qkd_scope with qkd_cmd.

Notation "c1 ;; c2" := (seq_cmd c1 c2)
  (at level 60, right associativity) : qkd_scope.
Notation "x '<-c' e" := (Cassign x e)
  (at level 58, no associativity) : qkd_scope.
Notation "x '<-^$' mu" := (Csample x mu)
  (at level 58, no associativity) : qkd_scope.
Notation "Q '<-q' rho" := (Cinit Q rho)
  (at level 58, no associativity) : qkd_scope.
Notation "x ':=M[' Q ']' M" := (Cmeasure x Q M)
  (at level 58, Q at level 50, M at level 50, no associativity) : qkd_scope.
Notation "'Attack[' Q ']'" := (Cattack Q)
  (at level 58, Q at level 50, no associativity) : qkd_scope.
Notation "'IF' b 'THEN' c1 'ELSE' c2" := (Cif b c1 c2)
  (at level 55, b at level 50, c1 at level 55, c2 at level 55) : qkd_scope.
Notation "'SKIP'" := Cskip : qkd_scope.
Notation "'FOR' i '<' n ',' body" :=
  (@for_cmd _ _ _ _ _ n (fun i => body))
  (at level 60, i ident, n at level 50, body at level 60) : qkd_scope.
