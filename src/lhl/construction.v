(* -------------------------------------------------------------------- *)
(* construction.v — a concrete, fully-proved two-universal hash family.   *)
(* -------------------------------------------------------------------- *)
(* Module: lhl.construction                                          *)
(*                                                                       *)
(* The library (def.v) specifies the two-universal interface abstractly  *)
(* but ships no concrete instance.  This file provides one: the family   *)
(* of ALL functions X -> Z, indexed by the function itself.  For x <> x' *)
(* the collision probability is exactly 1/|Z|, so the family is          *)
(* two-universal for any finite X, Z.  This is the canonical example of  *)
(* a (strongly) universal family; it is the cleanest one to certify in a *)
(* proof assistant because the collision count is an exact cardinality   *)
(* identity rather than a field computation.                             *)
(*                                                                       *)
(* A reindexing lemma transports the two-universal bound along any       *)
(* bijection of seed indices, so the family can be presented over an     *)
(* ordinal seed register 'I_nf (via enum_val) as the protocol records    *)
(* require.                                                               *)
(* -------------------------------------------------------------------- *)
From mathcomp Require Import all_boot all_order all_algebra finmap fingroup perm.
From mathcomp.reals Require Import reals.
From lhl Require Import def.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
(* ================================================================== *)
(* The all-functions hash family                                       *)
(* ================================================================== *)
Section AllFunctionsHash.
Variable R : realType.
Variables (X Z : finType).
(* The seed IS the function. *)
Definition allfun_hash (f : {ffun X -> Z}) (x : X) : Z := f x.
(* Exact collision count: |{f | f x = f x'}| * |Z| = |all functions|. *)
(* Bijection: g  <->  ([ffun y => if y==x' then g x else g y], g x').   *)
Fact allfun_collision_cardM (x x' : X) : x != x' ->
  (#|[set f : {ffun X -> Z} | f x == f x']| * #|Z|)%N
    = #|{ffun X -> Z}|.
Proof.
  move=> Hxx.
  pose phi (g : {ffun X -> Z}) : ({ffun X -> Z} * Z)%type :=
  ([ffun y => if y == x' then g x else g y], g x').
  have phi_inj : injective phi.
  move=> g1 g2 [] /ffunP HF Hx'.
  apply/ffunP => y; case: (eqVneq y x') => [->|Hy]; first exact: Hx'.
  by move: (HF y); rewrite !ffunE (negPf Hy).
  have phi_img :
    phi @: [set: {ffun X -> Z}]
    = setX [set f : {ffun X -> Z} | f x == f x'] [set: Z].
  apply/setP => -[f c]; rewrite in_setX !inE /= andbT.
  apply/imsetP/idP.
  - by move=> [g _ [-> _]]; rewrite !ffunE (negPf Hxx) !eqxx.
  - move=> /eqP Hcoll.
    exists [ffun y => if y == x' then c else f y]; first by rewrite inE.
    rewrite /phi; congr (_, _); last by rewrite ffunE eqxx.
    apply/ffunP => y; rewrite ffunE.
    case: (eqVneq y x') => [->|Hy].
    + by rewrite ffunE (negPf Hxx) Hcoll.
    + by rewrite ffunE (negPf Hy).
  have HT : #|phi @: [set: {ffun X -> Z}]| = #|{ffun X -> Z}|.
  by rewrite (card_imset _ phi_inj) cardsT.
  by rewrite -HT phi_img cardsX !cardsT.
Qed.
(* The collision set is nonempty whenever Z is (constant functions). *)
Fact allfun_collision_gt0 (x x' : X) : (0 < #|Z|)%N ->
  (0 < #|[set f : {ffun X -> Z} | f x == f x']|)%N.
Proof.
  move=> /card_gt0P [z0 _].
  apply/card_gt0P; exists [ffun _ => z0]; by rewrite inE !ffunE.
Qed.
(* Collision probability is exactly 1/|Z| (so a fortiori two-universal). *)
Theorem allfun_two_univ :
  @two_univ R [the finType of {ffun X -> Z}] X Z allfun_hash.
Proof.
  move=> x x' Hxx; rewrite /collision_probability /allfun_hash.
  have HM := allfun_collision_cardM Hxx.
  have [Hc0|Hc0] := posnP #|[set f : {ffun X -> Z} | f x == f x']|.
  by rewrite Hc0 mul0r invr_ge0 ler0n.
  rewrite -HM natrM invfM mulrA mulfV ?mul1r; first exact: lexx.
  by rewrite pnatr_eq0 -lt0n.
Qed.
End AllFunctionsHash.
(* ================================================================== *)
(* Reindexing two-universality along a bijection of seeds              *)
(* ================================================================== *)
(* Lets the all-functions family be presented over an ordinal seed      *)
(* register 'I_nf, e.g. via enum_val : 'I_#|{ffun X->Z}| -> {ffun X->Z}.*)
Section Reindex.
Variable R : realType.
Variables (Fidx Gidx X Z : finType).
Lemma reindex_delta_almost_two_univ (e : Gidx -> Fidx)
    (F : Fidx -> X -> Z) (d : R) :
  bijective e ->
  delta_almost_two_univ (R := R) F d ->
  delta_almost_two_univ (R := R) (fun i x => F (e i) x) d.
Proof.
  move=> bij_e HF x x' Hxx.
  have e_inj := bij_inj bij_e.
  rewrite /collision_probability.
  have Hset :
    #|[set i : Gidx | F (e i) x == F (e i) x']|
    = #|[set f : Fidx | F f x == F f x']|.
  rewrite -(card_imset _ e_inj); apply: eq_card => f; rewrite !inE.
  apply/imsetP/idP.
  - by move=> [i]; rewrite inE => Hi ->.
  - case: bij_e => g _ gK Hf; exists (g f); by rewrite ?inE gK.
  have Hcard : #|Gidx| = #|Fidx| := bij_eq_card bij_e.
  by rewrite Hset Hcard; apply: HF.
Qed.
End Reindex.
(* ================================================================== *)
(* Transport of two-universality across bijective seed / injective      *)
(* input / bijective output relabelings.  Needed to lift a raw ordinal  *)
(* hash family to the labelled-register ('Idx) form via n2i/cast.       *)
(* ================================================================== *)
Section TwoUnivTransport.
Variable R : realType.
Lemma two_univ_transport (Fidx Fidx' X X' Z Z' : finType)
    (F : Fidx -> X -> Z) (e : Fidx' -> Fidx) (hX : X' -> X) (gZ : Z -> Z') :
  bijective e -> injective hX -> bijective gZ ->
  two_univ (R := R) F ->
  two_univ (R := R) (fun f' x' => gZ (F (e f') (hX x'))).
Proof.
  move=> bij_e hX_inj bij_gZ HF x' x'' Hx'.
  have e_inj := bij_inj bij_e.
  have gZ_inj := bij_inj bij_gZ.
  rewrite /collision_probability -(bij_eq_card bij_gZ).
  have -> : [set f' : Fidx' | gZ (F (e f') (hX x')) == gZ (F (e f') (hX x''))]
        = [set f' : Fidx' | F (e f') (hX x') == F (e f') (hX x'')].
  by apply/setP => f'; rewrite !inE (inj_eq gZ_inj).
  have -> : #|[set f' : Fidx' | F (e f') (hX x') == F (e f') (hX x'')]|
        = #|[set f : Fidx | F f (hX x') == F f (hX x'')]|.
  rewrite -(card_imset _ e_inj); apply: eq_card => f; rewrite !inE.
  apply/imsetP/idP.
  - by move=> [i]; rewrite inE => Hi ->.
  - case: bij_e => g _ gK Hf; exists (g f); by rewrite ?inE gK.
  rewrite (bij_eq_card bij_e).
  by apply: HF; rewrite (inj_eq hX_inj).
Qed.
End TwoUnivTransport.
