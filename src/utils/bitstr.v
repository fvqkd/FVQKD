(* -------------------------------------------------------------------- *)
(* bitstr.v — Bitstring type, Hamming weight, Hamming distance           *)
(* -------------------------------------------------------------------- *)
(* Module: utils.bitstr                                   *)
(* TeX source: none (library utility)                                   *)
(* TeX labels: none                                                      *)
(* -------------------------------------------------------------------- *)
(* --- Library imports --- *)
From HB Require Import structures.
From mathcomp Require Import all_boot all_order all_algebra.
From mathcomp.reals Require Import reals.
From mathcomp.analysis Require Import exp.
From mathcomp.classical Require Import boolp.
From mathcomp.real_closed Require Import mxtens.
Require Import mathcomp.algebra.archimedean.
From quantum Require Import mcextra mxpred svd notation qtype.
(* --- FVQKD imports --- *)
From utils Require Import arith.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Import Order.TTheory GRing.Theory Num.Def Num.Theory.
Section FvqkdReal.
Variable R : realType.
(* ================================================================== *)
(* Bitstring: n-tuples over bool                                        *)
(* ================================================================== *)
(* A bitstring of length n is a function 'I_n -> bool *)
(* bitstr *)
(* infra: no tex label — fundamental & reusable (mathcomp-style) *)
(* consumer: bitstr is used downstream by the BB84 secrecy proof. *)
Definition bitstr (n : nat) := 'I_n -> bool.
(* ================================================================== *)
(* Hamming weight: number of 1-bits                                     *)
(* ================================================================== *)
Section HammingWeight.
(* wt_ham *)
(* infra: no tex label — fundamental & reusable (mathcomp-style) *)
(* consumer: wt_ham is used downstream by the BB84 secrecy proof. *)
Definition wt_ham {n : nat} (x : bitstr n) : nat :=
  #|[set i : 'I_n | x i]|.
End HammingWeight.
(* ================================================================== *)
(* XOR of two bitstrings                                                *)
(* ================================================================== *)
Section XorStr.
(* xor_str *)
(* infra: no tex label — fundamental & reusable (mathcomp-style) *)
(* consumer: xor_str is used downstream by the BB84 secrecy proof. *)
Definition xor_str {n : nat} (x y : bitstr n) : bitstr n :=
  fun i => x i (+) y i.
(* Hamming distance on bitstrings. *)
(* d_ham *)
(* infra: no tex label — fundamental & reusable (mathcomp-style) *)
(* consumer: d_ham is used downstream by the BB84 secrecy proof. *)
Definition d_ham {n : nat} (x y : bitstr n) : nat :=
  wt_ham (xor_str x y).
End XorStr.
(* ================================================================== *)
(* Bitstring ↔ ordinal coding                                          *)
(* ================================================================== *)
Section BitstringOrd.
Local Definition bitstring_to_tuple {n : nat} (s : bitstr n) : n.-tuple bool :=
  [tuple s i | i < n].
Local Definition tuple_to_bitstring {n : nat} (t : n.-tuple bool) : bitstr n :=
  fun i => tnth t i.
(* ord_to_bitstring *)
(* infra: no tex label — fundamental & reusable (mathcomp-style) *)
(* consumer: ord_to_bitstring is used downstream by the BB84 secrecy proof. *)
Definition ord_to_bitstring {n : nat} (x : 'I_(2 ^ n)) : bitstr n :=
  tuple_to_bitstring (ord2bseq x).
(* bitstring_to_ord *)
(* infra: no tex label — fundamental & reusable (mathcomp-style) *)
(* consumer: bitstring_to_ord is used downstream by the BB84 secrecy proof. *)
Definition bitstring_to_ord {n : nat} (s : bitstr n) : 'I_(2 ^ n) :=
  bseq2ord (bitstring_to_tuple s).
(* Appending a binary digit corresponds to the right tensor component. *)
(* bseq2ord_rcons_mxtens *)
(* infra: no tex label — fundamental bitstring/ordinal tensor indexing. *)
(* path: utils:bseq2ord_rcons_mxtens -> *)
(*   utils:hamming_ball_count_max_entropy_bound -> bb84:stat -> *)
(*   bb84:bb84_secret *)
Lemma bseq2ord_rcons_mxtens {n : nat} (t : n.-tuple bool) (b : bool) :
  cast_ord (expnSr 2 n) (bseq2ord [tuple of rcons t b]) =
  mxtens_index (bseq2ord t, bseq2ord [tuple b]).
Proof.
  apply/val_inj=> /=.
  rewrite /bseq2ord /= bseq2nat_rcons /mxtens_index /=.
  case: b.
  - by rewrite /= mulnC.
  - by rewrite /= !addn0 mulnC.
Qed.
(* path: utils:bitstring_tuple_cancel -> utils:bitstring_to_ordK -> *)
(*   utils:diff_set_inj -> *)
(*   utils:relative_hamming_ball_count_le_card_subsets -> *)
(*   utils:relative_hamming_ball_count_le_prefix -> *)
(*   utils:relative_hamming_ball_count_max_le_prefix -> *)
(*   utils:hamming_ball_count_max_entropy_bound -> bb84:stat -> *)
(*   bb84:bb84_secret *)
Local Lemma bitstring_tuple_cancel {n : nat} (t : n.-tuple bool) :
  bitstring_to_tuple (tuple_to_bitstring t) = t.
Proof.
  apply: eq_from_tnth => i.
  by rewrite /bitstring_to_tuple /tuple_to_bitstring tnth_mktuple.
Qed.
(* path: utils:tuple_bitstring_cancel -> *)
(*   utils:hamming_ball_count_max_entropy_bound -> bb84:stat -> *)
(*   bb84:bb84_secret *)
Local Lemma tuple_bitstring_cancel {n : nat} (s : bitstr n) :
  tuple_to_bitstring (bitstring_to_tuple s) = s.
Proof.
  rewrite /tuple_to_bitstring /bitstring_to_tuple.
  by apply/funext=> i; rewrite tnth_mktuple.
Qed.
(* path: utils:bitstring_to_ordK -> utils:diff_set_inj -> *)
(*   utils:relative_hamming_ball_count_le_card_subsets -> *)
(*   utils:relative_hamming_ball_count_le_prefix -> *)
(*   utils:relative_hamming_ball_count_max_le_prefix -> *)
(*   utils:hamming_ball_count_max_entropy_bound -> bb84:stat -> *)
(*   bb84:bb84_secret *)
Lemma bitstring_to_ordK {n : nat} :
  cancel (@ord_to_bitstring n) (@bitstring_to_ord n).
Proof.
  move=> x.
  rewrite /bitstring_to_ord /ord_to_bitstring bitstring_tuple_cancel.
  exact: ord2bseqK.
Qed.
(* path: utils:ord_to_bitstringK -> *)
(*   utils:hamming_ball_count_max_entropy_bound -> bb84:stat -> *)
(*   bb84:bb84_secret *)
Lemma ord_to_bitstringK {n : nat} :
  cancel (@bitstring_to_ord n) (@ord_to_bitstring n).
Proof.
  move=> s.
  rewrite /ord_to_bitstring /bitstring_to_ord.
  have -> : ord2bseq (bseq2ord (bitstring_to_tuple s)) = bitstring_to_tuple s.
    exact: bseq2ordK.
  exact: tuple_bitstring_cancel.
Qed.
(* Value formula for a single big-endian bit of an ordinal.  The k-th   *)
(* slot of `ord_to_bitstring x` (slot 0 = most significant) is the       *)
(* parity of `val x` shifted right by `d - k.+1` places.  Additive,      *)
(* purely arithmetic; used to compute `bit_of_ord` of the concrete       *)
(* preparation-pointer ordinals in the BB84 deferred-readout collapse.   *)
(* nth_nat2bseq *)
(* infra: no tex label — big-endian nth-bit value of nat2bseq. *)
Lemma nth_nat2bseq (d m k : nat) : (k < d)%N ->
  nth false (nat2bseq d m) k = odd (m %/ 2 ^ (d - k.+1)).
Proof.
elim: d m k => [|d IH] m k // Hk.
rewrite nat2bseqS.
case: k Hk => [|k] Hk /=.
- by rewrite subn1 /=.
- by rewrite IH// subSS.
Qed.
(* ord_to_bitstring_valE *)
(* infra: no tex label — big-endian nth-bit value of an ordinal. *)
Lemma ord_to_bitstring_valE (d : nat) (x : 'I_(2 ^ d)) (k : 'I_d) :
  ord_to_bitstring x k = odd (nat_of_ord x %/ 2 ^ (d - k.+1)).
Proof.
rewrite /ord_to_bitstring /tuple_to_bitstring (tnth_nth false).
by rewrite /ord2bseq /= nth_nat2bseq.
Qed.
(* Same value formula stated with the ordinal at the LITERAL dimension    *)
(* 4 = 2^2 (the BB84 preparation-pointer register).  Because the ordinal  *)
(* argument here is syntactically `'I_4`, a `rewrite` with this lemma      *)
(* matches ordinals of type `'I_4` (e.g. `bb84_prep_index`) directly,      *)
(* without the `2 ^ ?d` vs `4` unification the generic form triggers.      *)
(* ord_to_bitstring_val4 *)
(* infra: no tex label — nth-bit value at the 4-dim source register. *)
Lemma ord_to_bitstring_val4 (x : 'I_4) (k : 'I_2) :
  @ord_to_bitstring 2 x k = odd (nat_of_ord x %/ 2 ^ (2 - k.+1)).
Proof.
rewrite /ord_to_bitstring /tuple_to_bitstring (tnth_nth false).
by rewrite /ord2bseq /= nth_nat2bseq.
Qed.

(* Value of a 2-bit big-endian bitstring's ordinal: high bit weighted 2,  *)
(* low bit weighted 1.  Derived from the bit formula via the cancellation *)
(* `ord_to_bitstringK` (the ordinal here is genuinely `'I_(2^2)`, so the   *)
(* bit lemma applies with no `4` vs `2^2` unification issue).  Used by the *)
(* BB84 collapse to read off the preparation-pointer ordinal value.        *)
(* bitstring_to_ord2_valE *)
(* infra: no tex label — 2-bit big-endian ordinal value. *)
Fact bitstring_to_ord2_valE (s : bitstr 2) :
  nat_of_ord (@bitstring_to_ord 2 s)
  = (s ord0 * 2 + s (Ordinal (isT : (1 < 2)%N)))%N.
Proof.
have Hb0 : s ord0 = odd (nat_of_ord (@bitstring_to_ord 2 s) %/ 2).
{ by rewrite -{1}(ord_to_bitstringK s) ord_to_bitstring_valE. }
have Hb1 : s (Ordinal (isT : (1 < 2)%N))
         = odd (nat_of_ord (@bitstring_to_ord 2 s)).
{ by rewrite -{1}(ord_to_bitstringK s) ord_to_bitstring_valE subnn expn0 divn1. }
have HV : (nat_of_ord (@bitstring_to_ord 2 s) < 4)%N := ltn_ord _.
rewrite Hb0 Hb1; clear Hb0 Hb1; move: HV.
move: (nat_of_ord (@bitstring_to_ord 2 s)) => v.
by case: v => [|[|[|[|v']]]] Hlt.
Qed.

End BitstringOrd.

(* ================================================================== *)
(* Relative Hamming balls                                               *)
(* ================================================================== *)

Section RelativeHammingBall.

(* relative_hamming_ball *)
(* infra: no tex label — fundamental & reusable (mathcomp-style) *)
(* consumer: relative_hamming_ball is used downstream by the BB84 secrecy proof. *)
Definition relative_hamming_ball {n : nat} (delta : R)
    (x x' : 'I_(2 ^ n)) : bool :=
  (((d_ham (ord_to_bitstring x) (ord_to_bitstring x'))%:R / n%:R) < delta)%R.

(* relative_hamming_ball_count *)
(* infra: no tex label — fundamental & reusable (mathcomp-style) *)
(* consumer: relative_hamming_ball_count is used downstream by the BB84 secrecy proof. *)
Definition relative_hamming_ball_count (n : nat) (delta : R)
    (x' : 'I_(2 ^ n)) : nat :=
  \sum_(x : 'I_(2 ^ n) | @relative_hamming_ball n delta x x') 1%N.

(* relative_hamming_ball_count_max *)
(* infra: no tex label — fundamental & reusable (mathcomp-style) *)
(* consumer: relative_hamming_ball_count_max is used downstream by the BB84 secrecy proof. *)
Definition relative_hamming_ball_count_max (n : nat) (delta : R) : nat :=
  \big[maxn/0]_(x' : 'I_(2 ^ n)) (@relative_hamming_ball_count n delta x').

Local Definition diff_set {n : nat} (x x' : 'I_(2 ^ n)) : {set 'I_n} :=
  [set i : 'I_n | ord_to_bitstring x i != ord_to_bitstring x' i].

(* path: utils:diff_set_inj -> *)
(*   utils:relative_hamming_ball_count_le_card_subsets -> *)
(*   utils:relative_hamming_ball_count_le_prefix -> *)
(*   utils:relative_hamming_ball_count_max_le_prefix -> *)
(*   utils:hamming_ball_count_max_entropy_bound -> bb84:stat -> *)
(*   bb84:bb84_secret *)
Local Lemma diff_set_inj {n : nat} (x' : 'I_(2 ^ n)) :
  injective (fun x : 'I_(2 ^ n) => diff_set x x').
Proof.
  move=> x y Hxy.
  apply: (can_inj (@bitstring_to_ordK n)).
  apply/funext=> i.
  have Hmem := congr1 (fun A : {set 'I_n} => i \in A) Hxy.
  rewrite /diff_set !inE /= in Hmem.
  move: Hmem.
  case Hxi: (ord_to_bitstring x i);
    case Hyi: (ord_to_bitstring y i);
    case Hxpi: (ord_to_bitstring x' i)=> //=.
Qed.

(* path: utils:d_hamxx -> utils:relative_hamming_ball_self -> *)
(*   utils:relative_hamming_ball_count_ge1 -> *)
(*   utils:relative_hamming_ball_count_max_ge1 -> *)
(*   utils:hamming_ball_count_max_entropy_bound -> bb84:stat -> *)
(*   bb84:bb84_secret *)
Local Lemma d_hamxx {n : nat} (s : bitstr n) :
  d_ham s s = 0%N.
Proof.
  rewrite /d_ham /wt_ham /xor_str.
  apply/eqP; rewrite cards_eq0; apply/eqP; apply/setP=> i.
  by rewrite !inE addbb.
Qed.

(* path: utils:diff_set_cardE -> *)
(*   utils:relative_hamming_ball_count_le_card_subsets -> *)
(*   utils:relative_hamming_ball_count_le_prefix -> *)
(*   utils:relative_hamming_ball_count_max_le_prefix -> *)
(*   utils:hamming_ball_count_max_entropy_bound -> bb84:stat -> *)
(*   bb84:bb84_secret *)
Local Lemma diff_set_cardE {n : nat} (x x' : 'I_(2 ^ n)) :
  #|diff_set x x'| = d_ham (ord_to_bitstring x) (ord_to_bitstring x').
Proof.
  rewrite /diff_set /d_ham /wt_ham.
  apply: eq_card => i.
  rewrite !inE /xor_str.
  case: (ord_to_bitstring x i);
    case: (ord_to_bitstring x' i); reflexivity.
Qed.

(* path: utils:hdist_lt_floor_le -> *)
(*   utils:relative_hamming_ball_count_le_card_subsets -> *)
(*   utils:relative_hamming_ball_count_le_prefix -> *)
(*   utils:relative_hamming_ball_count_max_le_prefix -> *)
(*   utils:hamming_ball_count_max_entropy_bound -> bb84:stat -> *)
(*   bb84:bb84_secret *)
Local Lemma hdist_lt_floor_le {n : nat} (delta : R) (x x' : 'I_(2 ^ n)) :
  (0 < n)%N ->
  @relative_hamming_ball n delta x x' ->
  (d_ham (ord_to_bitstring x) (ord_to_bitstring x')
    <= `|floor (n%:R * delta)|%N)%N.
Proof.
  move=> Hn_pos.
  rewrite /relative_hamming_ball.
  set d := d_ham _ _.
  move=> Hlt.
  have Hdlt : d%:R < n%:R * delta.
  {
    move: Hlt.
    rewrite ltr_pdivrMr; last by rewrite ltr0n.
    by rewrite mulrC.
  }
  rewrite -(@ler_nat R).
  rewrite natr_absz intr_norm.
  have Hdle_x : (((d%:Z)%:~R : R) <= n%:R * delta)%R.
    exact: ltW Hdlt.
  have Hd_le_floor : (((d%:Z)%:~R : R) <= (floor (n%:R * delta))%:~R)%R.
  {
    move: (@Rfloor_ge_int R (n%:R * delta) (d%:Z)).
    by rewrite Hdle_x.
  }
  have Hd_nonnegR : (0 <= (((d%:Z)%:~R : R)))%R by rewrite ler0z.
  have Hfloor_nonnegR' : (0 <= ((floor (n%:R * delta))%:~R : R))%R.
    exact: le_trans Hd_nonnegR Hd_le_floor.
  have Hfloor_nonneg : 0 <= floor (n%:R * delta).
    by rewrite -(@ler0z R).
  rewrite (ger0_norm Hfloor_nonnegR').
  exact: Hd_le_floor.
Qed.

(* path: utils:card_subsets_leq_ord -> *)
(*   utils:relative_hamming_ball_count_le_prefix -> *)
(*   utils:relative_hamming_ball_count_max_le_prefix -> *)
(*   utils:hamming_ball_count_max_entropy_bound -> bb84:stat -> *)
(*   bb84:bb84_secret *)
Local Lemma card_subsets_leq_ord (n m : nat) :
  #|[set A : {set 'I_n} | (#|A| <= m)%N]%SET| =
    \sum_(k < n.+1 | (k <= m)%N) 'C(n, k).
Proof.
  pose Sm : {set {set 'I_n}} := [set A : {set 'I_n} | (#|A| <= m)%N]%SET.
  transitivity #|Sm|; first by [].
  have -> : #|Sm| = \sum_(A : {set 'I_n} | A \in Sm) 1%N.
  {
    symmetry.
    rewrite sum1dep_card.
    apply: eq_card => A.
    by rewrite inE.
  }
  rewrite (partition_big (fun A : {set 'I_n} => inord #|A|)
    (fun k : 'I_(n.+1) => (k <= m)%N)) /=.
  2:{
    move=> A HA.
    have HcardA_le : (#|A| <= n)%N.
    {
      have Hsub_card : (#|A| <= #|[set: 'I_n]|)%N :=
        subset_leq_card (finset.subsetT A).
      by rewrite cardsT card_ord in Hsub_card.
    }
    have HcardA : (#|A| < n.+1)%N by rewrite ltnS HcardA_le.
    rewrite (inordK HcardA).
    by rewrite /Sm inE in HA.
  }
  apply: eq_bigr => k Hk.
  pose Pk (A : {set 'I_n}) := (A \in Sm) && (inord #|A| == k).
  rewrite sum_nat_cond_const muln1.
  have -> :
      #|[set A : {set 'I_n} | Pk A]| =
      #|[set A : {set 'I_n} | #|A| == k]|.
  {
    apply: eq_card => A.
    rewrite !inE.
    have HcardA_le : (#|A| <= n)%N.
    {
      have Hsub_card : (#|A| <= #|[set: 'I_n]|)%N :=
        subset_leq_card (finset.subsetT A).
      by rewrite cardsT card_ord in Hsub_card.
    }
    have HcardA : (#|A| < n.+1)%N by rewrite ltnS HcardA_le.
    apply/idP/idP.
    - move=> /andP [HA HAk].
      apply/eqP.
      move: HAk.
      rewrite -val_eqE /= inordK //.
      by move/eqP.
    - move=> /eqP HAk.
      apply/andP; split.
      * by rewrite /Sm inE HAk.
      * by rewrite -val_eqE /= inordK // HAk eqxx.
  }
  by rewrite card_draws card_ord.
Qed.

Local Definition diff_ball_set {n : nat} (delta : R) (x' : 'I_(2 ^ n)) :
    {set 'I_(2 ^ n)} :=
  [set x : 'I_(2 ^ n) | @relative_hamming_ball n delta x x'].

(* path: utils:relative_hamming_ball_self -> *)
(*   utils:relative_hamming_ball_count_ge1 -> *)
(*   utils:relative_hamming_ball_count_max_ge1 -> *)
(*   utils:hamming_ball_count_max_entropy_bound -> bb84:stat -> *)
(*   bb84:bb84_secret *)
Local Lemma relative_hamming_ball_self {n : nat} (delta : R) (x : 'I_(2 ^ n)) :
  0 < delta ->
  @relative_hamming_ball n delta x x.
Proof.
  move=> Hdelta_pos.
  rewrite /relative_hamming_ball d_hamxx /= mul0r.
  exact: Hdelta_pos.
Qed.

(* path: utils:relative_hamming_ball_count_ge1 -> *)
(*   utils:relative_hamming_ball_count_max_ge1 -> *)
(*   utils:hamming_ball_count_max_entropy_bound -> bb84:stat -> *)
(*   bb84:bb84_secret *)
Local Lemma relative_hamming_ball_count_ge1 (n : nat) (delta : R)
  (x' : 'I_(2 ^ n)) :
  0 < delta ->
  (1 <= @relative_hamming_ball_count n delta x')%N.
Proof.
  move=> Hdelta_pos.
  rewrite /relative_hamming_ball_count sum_nat_cond_const muln1.
  have Hself : @relative_hamming_ball n delta x' x'.
    exact: relative_hamming_ball_self.
  have Hsubset :
      [set x'] \subset [set x : 'I_(2 ^ n) | @relative_hamming_ball n delta x x'].
  {
    apply/mathcomp.boot.fintype.subsetP=> x.
    rewrite !inE.
    move/eqP=> ->.
    exact: Hself.
  }
  apply: (leq_trans _ (subset_leq_card Hsubset)).
  by rewrite cards1.
Qed.

(* path: utils:relative_hamming_ball_count_max_ge1 -> *)
(*   utils:hamming_ball_count_max_entropy_bound -> bb84:stat -> *)
(*   bb84:bb84_secret *)
Local Lemma relative_hamming_ball_count_max_ge1 (n : nat) (delta : R) :
  0 < delta ->
  (1 <= @relative_hamming_ball_count_max n delta)%N.
Proof.
  move=> Hdelta_pos.
  pose x0 : 'I_(2 ^ n) := @Ordinal (2 ^ n) 0 (expn_gt0 2 n).
  have Hord0 : (1 <= @relative_hamming_ball_count n delta x0)%N.
    exact: relative_hamming_ball_count_ge1.
  apply: (leq_trans Hord0).
  rewrite /relative_hamming_ball_count_max.
  apply: leq_bigmax_cond.
  by [].
Qed.

(* path: utils:relative_hamming_ball_count_le_card_subsets -> *)
(*   utils:relative_hamming_ball_count_le_prefix -> *)
(*   utils:relative_hamming_ball_count_max_le_prefix -> *)
(*   utils:hamming_ball_count_max_entropy_bound -> bb84:stat -> *)
(*   bb84:bb84_secret *)
Local Lemma relative_hamming_ball_count_le_card_subsets (n : nat) (delta : R)
  (x' : 'I_(2 ^ n)) :
  (0 < n)%N ->
  0 < delta ->
  (@relative_hamming_ball_count n delta x' <=
    #|[set A : {set 'I_n} |
      (#|A| <= `|floor (n%:R * delta)|%N)%N]%SET|)%N.
Proof.
  move=> Hn_pos Hdelta_pos.
  pose B := diff_ball_set delta x'.
  pose I := [set diff_set x x' | x in B].
  have HcardI : #|I| = #|B|.
  {
    rewrite /I.
    apply: card_in_imset.
    move=> x y _ _.
    exact: diff_set_inj.
  }
  have HI_sub :
      I \subset [set A : {set 'I_n} |
        (#|A| <= `|floor (n%:R * delta)|%N)%N]%SET.
  {
    apply/mathcomp.boot.fintype.subsetP=> A.
    rewrite /I.
    move/imsetP=> [x Hx ->].
    rewrite inE diff_set_cardE.
    have Hx_ball : @relative_hamming_ball n delta x x'.
    {
      move: Hx.
      rewrite /B /diff_ball_set inE.
      by move=> ->.
    }
    exact: hdist_lt_floor_le Hn_pos Hx_ball.
  }
  have -> : @relative_hamming_ball_count n delta x' = #|B|.
  {
    rewrite /relative_hamming_ball_count /B /diff_ball_set sum1dep_card.
    by [].
  }
  rewrite -HcardI.
  exact: subset_leq_card HI_sub.
Qed.

(* path: utils:relative_hamming_ball_count_le_prefix -> *)
(*   utils:relative_hamming_ball_count_max_le_prefix -> *)
(*   utils:hamming_ball_count_max_entropy_bound -> bb84:stat -> *)
(*   bb84:bb84_secret *)
Local Lemma relative_hamming_ball_count_le_prefix (n : nat) (delta : R)
  (x' : 'I_(2 ^ n)) :
  (0 < n)%N ->
  0 < delta ->
  (@relative_hamming_ball_count n delta x' <=
    \sum_(k < n.+1 | (k <= `|floor (n%:R * delta)|%N)%N) 'C(n, k))%N.
Proof.
  move=> Hn_pos Hdelta_pos.
  have Hcount :=
    @relative_hamming_ball_count_le_card_subsets n delta x' Hn_pos Hdelta_pos.
  have Hcard := card_subsets_leq_ord n `|floor (n%:R * delta)|%N.
  apply: (leq_trans Hcount).
  rewrite -Hcard.
  exact: leqnn.
Qed.

(* path: utils:relative_hamming_ball_count_max_le_prefix -> *)
(*   utils:hamming_ball_count_max_entropy_bound -> bb84:stat -> *)
(*   bb84:bb84_secret *)
Local Lemma relative_hamming_ball_count_max_le_prefix (n : nat) (delta : R) :
  (0 < n)%N ->
  0 < delta ->
  (@relative_hamming_ball_count_max n delta <=
    \sum_(k < n.+1 | (k <= `|floor (n%:R * delta)|%N)%N) 'C(n, k))%N.
Proof.
  move=> Hn_pos Hdelta_pos.
  apply/bigmax_leqP => x' _.
  exact: (@relative_hamming_ball_count_le_prefix n delta x' Hn_pos Hdelta_pos).
Qed.

(* path: utils:exprDnrR -> utils:prefix_binomial_weighted_bound -> *)
(*   utils:prefix_binomial_entropy_bound -> *)
(*   utils:hamming_ball_count_max_entropy_bound -> bb84:stat -> *)
(*   bb84:bb84_secret *)
Local Lemma exprDnrR (a b : R) (n : nat) :
  (a + b) ^+ n =
    \sum_(i < n.+1) ('C(n, i)%:R * (a ^+ i) * (b ^+ (n - i))).
Proof.
  rewrite big_ord_rev /= exprDn.
  apply: eq_bigr => i _.
  by rewrite subSS subKn ?bin_sub // -1 ?ltnS // -mulr_natl mulrA.
Qed.

(* path: utils:expr_le1_nat -> utils:q_pow_m_le_q_pow_k -> *)
(*   utils:prefix_binomial_weighted_bound -> *)
(*   utils:prefix_binomial_entropy_bound -> *)
(*   utils:hamming_ball_count_max_entropy_bound -> bb84:stat -> *)
(*   bb84:bb84_secret *)
Local Lemma expr_le1_nat (q : R) (m : nat) :
  0 <= q ->
  q <= 1 ->
  q ^+ m <= 1.
Proof.
  move=> Hq_nonneg Hq_le1.
  elim: m => [|m IH].
  - by rewrite expr0.
  - rewrite exprS.
    have Hqm_nonneg : 0 <= q ^+ m by exact: exprn_ge0.
    have Hmul : q ^+ m * q <= 1 * 1.
    {
      exact: ler_pM Hqm_nonneg Hq_nonneg IH Hq_le1.
    }
    rewrite mul1r in Hmul.
    rewrite mulrC.
    exact: Hmul.
Qed.

(* path: utils:q_pow_m_le_q_pow_k -> utils:prefix_binomial_weighted_bound -> *)
(*   utils:prefix_binomial_entropy_bound -> *)
(*   utils:hamming_ball_count_max_entropy_bound -> bb84:stat -> *)
(*   bb84:bb84_secret *)
Local Lemma q_pow_m_le_q_pow_k (q : R) (k m : nat) :
  0 <= q ->
  q <= 1 ->
  (k <= m)%N ->
  q ^+ m <= q ^+ k.
Proof.
  move=> Hq_nonneg Hq_le1 Hkm.
  rewrite -(subnKC Hkm) exprD.
  have Htail_le1 : q ^+ (m - k) <= 1 by exact: expr_le1_nat.
  have Hqk_nonneg : 0 <= q ^+ k by exact: exprn_ge0.
  have Htail_nonneg : 0 <= q ^+ (m - k) by exact: exprn_ge0.
  have := ler_pM Htail_nonneg Hqk_nonneg Htail_le1 (lexx (q ^+ k)).
  by rewrite mul1r mulrC.
Qed.

(* path: utils:prefix_binomial_weighted_bound -> *)
(*   utils:prefix_binomial_entropy_bound -> *)
(*   utils:hamming_ball_count_max_entropy_bound -> bb84:stat -> *)
(*   bb84:bb84_secret *)
Local Lemma prefix_binomial_weighted_bound (n m : nat) (q : R) :
  0 < q ->
  q <= 1 ->
  q ^+ m * (\sum_(k < n.+1 | (k <= m)%N) 'C(n, k))%:R <=
  (1 + q) ^+ n.
Proof.
  move=> Hq_pos Hq_le1.
  have Hq_nonneg : 0 <= q by exact: ltW Hq_pos.
  have Hsum :
      q ^+ m * (\sum_(k < n.+1 | (k <= m)%N) 'C(n, k))%:R
      <= \sum_(k < n.+1 | (k <= m)%N) ('C(n, k)%:R * q ^+ k).
  {
    rewrite natr_sum mulr_sumr.
    apply: ler_sum => k Hkm.
    have Hchoose_nonneg : 0 <= 'C(n, k)%:R :> R by exact: ler0n.
    have Hpow_le : q ^+ m <= q ^+ k.
      by apply: q_pow_m_le_q_pow_k.
    have Hqpowm_nonneg : 0 <= q ^+ m by exact: exprn_ge0.
    have Hprod :
        'C(n, k)%:R * q ^+ m <= 'C(n, k)%:R * q ^+ k.
    {
      exact: ler_pM Hchoose_nonneg Hqpowm_nonneg (lexx _) Hpow_le.
    }
    by rewrite mulrC in Hprod.
  }
  apply: (le_trans Hsum).
  have Hfilter_le :
      \sum_(k < n.+1 | (k <= m)%N) ('C(n, k)%:R * q ^+ k)
      <= \sum_(k < n.+1) ('C(n, k)%:R * q ^+ k).
  {
    rewrite [X in X <= _]big_mkcond.
    apply: ler_sum => k _.
    case: ifP => _; first exact: lexx.
    have Hchoose_nonneg : 0 <= 'C(n, k)%:R :> R by exact: ler0n.
    have Hpow_nonneg : 0 <= q ^+ k by exact: exprn_ge0.
    exact: mulr_ge0.
  }
  apply: (le_trans Hfilter_le).
  rewrite addrC (exprDnrR q 1 n).
  have -> :
      \sum_(k < n.+1) ('C(n, k)%:R * q ^+ k * 1 ^+ (n - k)) =
      \sum_(k < n.+1) ('C(n, k)%:R * q ^+ k).
  {
    apply: eq_bigr => k _.
    by rewrite expr1n mulr1.
  }
  exact: lexx.
Qed.

(* path: utils:prefix_sum_ge1 -> utils:prefix_sum_posR -> *)
(*   utils:prefix_binomial_entropy_bound -> *)
(*   utils:hamming_ball_count_max_entropy_bound -> bb84:stat -> *)
(*   bb84:bb84_secret *)
Local Lemma prefix_sum_ge1 (n m : nat) :
  (1 <= \sum_(k < n.+1 | (k <= m)%N) 'C(n, k))%N.
Proof.
  rewrite (bigD1 ord0) /=.
  - rewrite bin0.
    exact: leq_addr.
  - by [].
Qed.

(* path: utils:prefix_sum_posR -> utils:prefix_binomial_entropy_bound -> *)
(*   utils:hamming_ball_count_max_entropy_bound -> bb84:stat -> *)
(*   bb84:bb84_secret *)
Local Lemma prefix_sum_posR (n m : nat) :
  0 < (\sum_(k < n.+1 | (k <= m)%N) 'C(n, k))%:R :> R.
Proof.
  have Hge1 : (1 <= \sum_(k < n.+1 | (k <= m)%N) 'C(n, k))%N.
    exact: prefix_sum_ge1.
  by rewrite ltr0n (leq_trans (leqnn 1) Hge1).
Qed.

(* path: utils:delta_le_one_minus -> utils:prefix_binomial_entropy_bound -> *)
(*   utils:hamming_ball_count_max_entropy_bound -> bb84:stat -> *)
(*   bb84:bb84_secret *)
Local Lemma delta_le_one_minus (delta : R) :
  delta <= 1 / 2 ->
  delta <= 1 - delta.
Proof.
  move=> Hdelta_half.
  have Hdouble : delta * (2%N)%:R <= 1.
  {
    have Htwo_pos : 0 < (2%N)%:R :> R.
    {
      change (0 < (1.+1)%:R :> R).
      by rewrite ltr0Sn.
    }
    have Htmp : delta * (2%N)%:R <= (1 / 2) * (2%N)%:R.
    {
      apply: (ler_wpM2r (ltW Htwo_pos)).
      exact: Hdelta_half.
    }
    have Htwo_neq : ((2%N)%:R : R) != 0 by exact: lt0r_neq0 Htwo_pos.
    have Hhalf2 : (1 / 2) * (2%N)%:R = 1 :> R.
    {
      rewrite -mulrA (mulVf Htwo_neq) mulr1.
      by [].
    }
    by rewrite Hhalf2 in Htmp.
  }
  have Hdouble' : delta + delta <= 1.
  {
    have HtwiceE : delta * (2%N)%:R = delta + delta.
    {
      rewrite mulr_natr.
      by [].
    }
    by rewrite HtwiceE in Hdouble.
  }
  rewrite lerBrDr.
  exact: Hdouble'.
Qed.

(* path: utils:log2M_pos -> utils:prefix_binomial_entropy_bound -> *)
(*   utils:hamming_ball_count_max_entropy_bound -> bb84:stat -> *)
(*   bb84:bb84_secret *)
Local Lemma log2M_pos (x y : R) :
  0 < x ->
  0 < y ->
  log2 (x * y) = log2 x + log2 y.
Proof.
  move=> Hx_pos Hy_pos.
  rewrite /log2 lnM // mulrDl.
  by [].
Qed.

(* path: utils:log2V_pos -> utils:prefix_binomial_entropy_bound -> *)
(*   utils:hamming_ball_count_max_entropy_bound -> bb84:stat -> *)
(*   bb84:bb84_secret *)
Local Lemma log2V_pos (x : R) :
  0 < x ->
  log2 x^-1 = - log2 x.
Proof.
  move=> Hx_pos.
  rewrite /log2 lnV //.
  by rewrite mulNr.
Qed.

(* path: utils:log2Xn_pos -> bb84:bb84_secret *)
Local Lemma log2Xn_pos (x : R) (m : nat) :
  0 < x ->
  log2 (x ^+ m) = log2 x *+ m.
Proof.
  move=> Hx_pos.
  rewrite /log2 lnXn //.
  symmetry.
  rewrite /log2.
  by rewrite -mulrnAl.
Qed.

(* path: utils:floor_abs_le -> utils:prefix_binomial_entropy_bound -> *)
(*   utils:hamming_ball_count_max_entropy_bound -> bb84:stat -> *)
(*   bb84:bb84_secret *)
Local Lemma floor_abs_le (x : R) :
  0 <= x ->
  (`|floor x|%N)%:R <= x.
Proof.
  move=> Hx_nonneg.
  have Hfloor_nonnegR : 0 <= (floor x)%:~R :> R.
  {
    move: (@Rfloor_ge_int R x 0%Z).
    by rewrite Hx_nonneg.
  }
  have Hfloor_nonneg : 0 <= floor x.
    by rewrite -(@ler0z R).
  rewrite natr_absz intr_norm.
  rewrite (ger0_norm Hfloor_nonnegR).
  exact: (@Rfloor_le R x).
Qed.

(* path: utils:prefix_binomial_entropy_bound -> *)
(*   utils:hamming_ball_count_max_entropy_bound -> bb84:stat -> *)
(*   bb84:bb84_secret *)
Local Lemma prefix_binomial_entropy_bound (n : nat) (delta : R) :
  (0 < n)%N ->
  0 < delta ->
  delta < 1 / 2 ->
  log2
    (\sum_(k < n.+1 | (k <= `|floor (n%:R * delta)|%N)%N) 'C(n, k))%:R <=
  n%:R * h_bin delta.
Proof.
  move=> Hn_pos Hdelta_pos Hdelta_half.
  have HtruncE :
      h_bin delta =
      - delta * log2 delta - (1 - delta) * log2 (1 - delta).
  {
    rewrite /h_bin.
    case: ifP => Hdelta_nonpos.
    - move: (lt_le_trans Hdelta_pos Hdelta_nonpos).
      by rewrite ltxx.
    - case: ifP => Hdelta_ge1.
      + have Hhalf_lt1 : (1 / 2 < 1 :> R).
        {
          rewrite ltr_pdivrMr; last by rewrite ltr0Sn.
          by rewrite mul1r ltr1n.
        }
        have Hdelta_lt1 : delta < 1 := lt_trans Hdelta_half Hhalf_lt1.
        by move: (lt_le_trans Hdelta_lt1 Hdelta_ge1); rewrite ltxx.
      + by rewrite mulNr.
  }
  rewrite HtruncE.
  pose m := `|floor (n%:R * delta)|%N.
  pose S := \sum_(k < n.+1 | (k <= m)%N) 'C(n, k).
  pose q := delta / (1 - delta).
  have Hhalf_lt1 : (1 / 2 < 1 :> R).
  {
    rewrite ltr_pdivrMr; last by rewrite ltr0Sn.
    by rewrite mul1r ltr1n.
  }
  have Hdelta_lt1 : delta < 1 := lt_trans Hdelta_half Hhalf_lt1.
  have Hone_minus_pos : 0 < 1 - delta by rewrite subr_gt0.
  have Hq_pos : 0 < q by rewrite /q divr_gt0.
  have Hq_le1 : q <= 1.
  {
    rewrite /q ler_pdivrMr // mul1r.
    exact: delta_le_one_minus (ltW Hdelta_half).
  }
  have Hweighted := @prefix_binomial_weighted_bound n m q Hq_pos Hq_le1.
  have HS_pos : 0 < S%:R :> R by exact: (@prefix_sum_posR n m).
  have Hlhs_pos : 0 < q ^+ m * S%:R :> R.
  {
    apply: mulr_gt0.
    - exact: exprn_gt0.
    - exact: HS_pos.
  }
  have Hqpow_pos : 0 < q ^+ m :> R by exact: exprn_gt0.
  have Hlog :=
    @log2_le_pos R (q ^+ m * S%:R) ((1 + q) ^+ n) Hlhs_pos Hweighted.
  have HlogS :
      log2 S%:R <= log2 ((1 + q) ^+ n) - log2 (q ^+ m).
  {
    move: Hlog.
    rewrite (@log2M_pos (q ^+ m) S%:R Hqpow_pos HS_pos).
    move=> Hlog0.
    rewrite lerBrDr addrC.
    exact: Hlog0.
  }
  have H1q_pos : 0 < 1 + q.
  {
    apply: addr_gt0.
    - exact: ltr01.
    - exact: Hq_pos.
  }
  have Hlog_pow_1q : log2 ((1 + q) ^+ n) = n%:R * log2 (1 + q).
  {
    rewrite (@log2Xn_pos (1 + q) n H1q_pos).
    by rewrite mulr_natl.
  }
  have Hlog_pow_q : log2 (q ^+ m) = m%:R * log2 q.
  {
    rewrite (@log2Xn_pos q m Hq_pos).
    by rewrite mulr_natl.
  }
  have Honeplusq : 1 + q = (1 - delta)^-1.
  {
    have Hone_minus_neq : 1 - delta != 0 by exact: lt0r_neq0 Hone_minus_pos.
    have Hcancel : (1 + q) * (1 - delta) = 1.
    {
      rewrite mulrDl.
      have -> : 1 * (1 - delta) = 1 - delta :> R by rewrite mul1r.
      rewrite /q divfK //.
      by rewrite subrK.
    }
    apply: (mulIf Hone_minus_neq).
    rewrite Hcancel.
    by rewrite (mulVf Hone_minus_neq).
  }
  have Hlog_1q : log2 (1 + q) = - log2 (1 - delta).
  {
    rewrite Honeplusq.
    exact: log2V_pos Hone_minus_pos.
  }
  have Hlog_q : log2 q = log2 delta - log2 (1 - delta).
  {
    have Hone_minus_inv_pos : 0 < (1 - delta)^-1 by rewrite invr_gt0.
    rewrite /q.
    rewrite (@log2M_pos delta (1 - delta)^-1 Hdelta_pos Hone_minus_inv_pos).
    rewrite (@log2V_pos (1 - delta) Hone_minus_pos).
    by [].
  }
  pose a := - log2 delta.
  pose b := - log2 (1 - delta).
  have Hm_le : m%:R <= n%:R * delta.
  {
    have Hn_nonneg : 0 <= n%:R :> R by rewrite ler0n.
    exact: floor_abs_le (mulr_ge0 Hn_nonneg (ltW Hdelta_pos)).
  }
  have Hlog_delta_le : log2 delta <= log2 (1 - delta).
  {
    apply: log2_le_pos => //.
    exact: delta_le_one_minus (ltW Hdelta_half).
  }
  have Hab_nonneg : 0 <= a - b.
  {
    rewrite /a /b opprK addrC.
    have -> :
        log2 (1 - delta) + - log2 delta =
        log2 (1 - delta) - log2 delta :> R by [].
    rewrite subr_ge0.
    exact: Hlog_delta_le.
  }
  move: HlogS.
  rewrite Hlog_pow_1q Hlog_pow_q Hlog_1q Hlog_q.
  have -> :
      n%:R * (- log2 (1 - delta)) - m%:R * (log2 delta - log2 (1 - delta)) =
      n%:R * b + m%:R * (a - b).
  {
    rewrite /a /b.
    have -> :
        - log2 delta - - log2 (1 - delta) =
        log2 (1 - delta) - log2 delta :> R.
    {
      rewrite opprK addrC.
      by [].
    }
    have <- :
        - (log2 delta - log2 (1 - delta)) =
        log2 (1 - delta) - log2 delta :> R.
      by rewrite opprB.
    rewrite [m%:R * _ in RHS]mulrN.
    by [].
  }
  move=> HlogS.
  apply: (le_trans HlogS).
  have Hstep :
      n%:R * b + m%:R * (a - b) <=
      n%:R * b + (n%:R * delta) * (a - b).
  {
    rewrite (lerD2l (n%:R * b)).
    exact: ler_wpM2r.
  }
  apply: (le_trans Hstep).
  have -> :
      n%:R * b + (n%:R * delta) * (a - b) =
      n%:R * (- delta * log2 delta - (1 - delta) * log2 (1 - delta)).
  {
    rewrite /a /b.
    have HabE :
        - log2 delta - - log2 (1 - delta) =
        log2 (1 - delta) - log2 delta :> R.
    {
      rewrite opprK addrC.
      by [].
    }
    rewrite HabE.
    have -> :
        n%:R * (- log2 (1 - delta)) +
        (n%:R * delta) * (log2 (1 - delta) - log2 delta) =
        n%:R * (- log2 (1 - delta) + delta * (log2 (1 - delta) - log2 delta)).
    {
      rewrite -[((n%:R * delta) * (log2 (1 - delta) - log2 delta))]mulrA.
      by rewrite -mulrDr.
    }
    have -> :
        - log2 (1 - delta) + delta * (log2 (1 - delta) - log2 delta) =
        - delta * log2 delta - (1 - delta) * log2 (1 - delta) :> R.
    {
      rewrite mulrBr addrA.
      have -> :
          - log2 (1 - delta) + delta * log2 (1 - delta) =
          - (1 - delta) * log2 (1 - delta) :> R.
      {
        have -> : - log2 (1 - delta) = -1 * log2 (1 - delta) :> R by rewrite mulN1r.
        rewrite -mulrDl.
        have -> : -1 + delta = - (1 - delta) :> R.
          by rewrite opprB addrC.
        by [].
      }
      have -> :
          - (1 - delta) * log2 (1 - delta) - delta * log2 delta =
          - ((1 - delta) * log2 (1 - delta)) + - (delta * log2 delta) :> R.
        by rewrite mulNr.
      have -> :
          - delta * log2 delta - (1 - delta) * log2 (1 - delta) =
          - (delta * log2 delta) + - ((1 - delta) * log2 (1 - delta)) :> R.
        by rewrite mulNr.
      by rewrite addrC.
    }
    by [].
  }
  exact: lexx.
Qed.

(* hamming_ball_count_max_entropy_bound *)
(* tex: Nat. Commun. 3:634 (2012), Suppl. Lemma 3                                           *)
(* math: log₂ |B_δ(x')| ≤ n · h(δ) for 0 < δ < 1/2.                      *)
(* Scope (intentional, complete-for-purpose): `0 < δ < 1/2` is exactly   *)
(* van Lint §1.4's regime and exactly what the consumer needs. The       *)
(* boundaries are discharged in `bb84:stat`, not by a wrapper here:       *)
(* δ ≥ 1/2 uses the truncation `bb84_h_trunc = 1` with the trivial       *)
(* `H_max ≤ n` bound, and δ ≤ 0 collapses via the good-event             *)
(* (`good_cond = 0`). So no total `0 ≤ δ ≤ 1/2` boundary form is needed.  *)
(* path: utils:hamming_ball_count_max_entropy_bound -> bb84:stat -> *)
(*   bb84:bb84_secret *)
Lemma hamming_ball_count_max_entropy_bound (n : nat) (delta : R) :
  (0 < n)%N ->
  0 < delta ->
  delta < 1 / 2 ->
  log2 (@relative_hamming_ball_count_max n delta)%:R <=
    n%:R * h_bin delta.
Proof.
  move=> Hn_pos Hdelta_pos Hdelta_half.
  have Hcount_pos :
      0 < (@relative_hamming_ball_count_max n delta)%:R :> R.
    by rewrite ltr0n; exact: (@relative_hamming_ball_count_max_ge1 n delta Hdelta_pos).
  have Hcount_prefixR :
      (@relative_hamming_ball_count_max n delta)%:R <=
      (\sum_(k < n.+1 |
        (k <= `|floor (n%:R * delta)|%N)%N) 'C(n, k))%:R :> R.
  {
    rewrite ler_nat.
    exact: (@relative_hamming_ball_count_max_le_prefix n delta Hn_pos Hdelta_pos).
  }
  have Hlog_count :
      log2 ((@relative_hamming_ball_count_max n delta)%:R) <=
      log2 ((\sum_(k < n.+1 |
        (k <= `|floor (n%:R * delta)|%N)%N) 'C(n, k))%:R :> R).
    exact: (@log2_le_pos R ((@relative_hamming_ball_count_max n delta)%:R)
      ((\sum_(k < n.+1 |
        (k <= `|floor (n%:R * delta)|%N)%N) 'C(n, k))%:R :> R)
      Hcount_pos Hcount_prefixR).
  exact: le_trans Hlog_count
    (@prefix_binomial_entropy_bound n delta Hn_pos Hdelta_pos Hdelta_half).
Qed.

(* hamming_ball_count_max_entropy_bound_total *)
(* tex: Nat. Commun. 3:634 (2012), Suppl. Lemma 3 (van Lint §1.4, full δ ≤ 1/2 domain)      *)
(* math: log₂ |B_δ(x')| ≤ n · h(δ) for ALL δ ≤ 1/2 (n > 0).              *)
(* Boundary completion of `hamming_ball_count_max_entropy_bound`:         *)
(*   δ ≤ 0  : the strict ball `d_ham/n < δ` is empty, count_max = 0, and  *)
(*            both sides are ≤ 0 (h_bin δ = 0);                           *)
(*   0<δ<1/2: delegates to `hamming_ball_count_max_entropy_bound`;        *)
(*   δ = 1/2: the trivial `count_max ≤ 2^n` gives log₂ ≤ n = n·h(1/2).    *)
(* Standalone total van Lint utility — NOT consumed by `bb84:stat`, which *)
(* truncates the entropy via `bb84_h_trunc` and so only needs 0<δ<1/2.    *)
(* infra: no tex label — reusable completion of the van Lint entropy bound *)
Lemma hamming_ball_count_max_entropy_bound_total (n : nat) (delta : R) :
  (0 < n)%N ->
  delta <= 1 / 2 ->
  log2 (@relative_hamming_ball_count_max n delta)%:R <=
    n%:R * h_bin delta.
Proof.
  move=> Hn_pos Hhalf.
  case: (lerP delta 0) => Hd0.
  - (* δ ≤ 0: the strict relative ball is empty, so count_max = 0. *)
    have Hcm0 : @relative_hamming_ball_count_max n delta = 0%N.
    {
      rewrite /relative_hamming_ball_count_max.
      apply: big1 => x' _.
      rewrite /relative_hamming_ball_count.
      apply: big_pred0 => x.
      rewrite /relative_hamming_ball.
      apply/negbTE; rewrite -leNgt.
      apply: (le_trans Hd0).
      by apply: divr_ge0; rewrite ler0n.
    }
    have Hhb0 : h_bin delta = 0 by rewrite /h_bin Hd0.
    rewrite Hcm0 Hhb0 mulr0 /log2.
    apply: mulr_le0_ge0.
    + by apply: ln_le0; exact: ler01.
    + by rewrite invr_ge0; exact: ltW ln2_gt0.
  - (* 0 < δ *)
    case: (ltrP delta (1 / 2)) => Hdh.
    + (* 0 < δ < 1/2: the published interior bound. *)
      exact: hamming_ball_count_max_entropy_bound Hn_pos Hd0 Hdh.
    + (* δ = 1/2: h(1/2) = 1 and count_max ≤ 2^n give log₂ ≤ n. *)
      have Hd_eq : delta = 1 / 2 by apply/le_anti/andP; split.
      have Hlog_half : log2 (1 / 2 : R) = - 1.
      {
        have H2 : (0 : R) < 2 by rewrite ltr0n.
        by rewrite div1r (log2V_pos H2) log2_2.
      }
      have Honeminus : (1 - 1 / 2 : R) = 1 / 2 by rewrite {1}[1](splitr) addrK.
      have Hhb_half : h_bin delta = 1.
      {
        have Hhalf_pos : (0 : R) < 1 / 2.
        { apply: divr_gt0; [exact: ltr01 | by rewrite ltr0n]. }
        have Hhalf_lt1 : (1 / 2 : R) < 1.
        { rewrite ltr_pdivrMr; last by rewrite ltr0Sn. by rewrite mul1r ltr1n. }
        rewrite Hd_eq /h_bin.
        case: ifP => [H10|_];
          first by move: (lt_le_trans Hhalf_pos H10); rewrite ltxx.
        case: ifP => [H11|_];
          first by move: (lt_le_trans Hhalf_lt1 H11); rewrite ltxx.
        by rewrite Honeminus !Hlog_half -opprD -mulrDl -splitr mul1r opprK.
      }
      have Hge1 : (1 <= @relative_hamming_ball_count_max n delta)%N
        := @relative_hamming_ball_count_max_ge1 n delta Hd0.
      have Hle2n : (@relative_hamming_ball_count_max n delta <= 2 ^ n)%N.
      {
        rewrite /relative_hamming_ball_count_max.
        apply: (big_ind (fun k => (k <= 2 ^ n)%N)).
        - exact: leq0n.
        - by move=> a b Ha Hb; rewrite geq_max Ha Hb.
        - move=> x' _.
          rewrite /relative_hamming_ball_count sum1dep_card.
          apply: (leq_trans (max_card _)).
          by rewrite card_ord.
      }
      rewrite Hhb_half mulr1.
      apply: (@le_trans _ _ (log2 ((2 ^ n)%:R : R))).
      * apply: log2_le_pos; first by rewrite ltr0n.
        by rewrite ler_nat.
      * by rewrite log2_pow2_nat.
Qed.

End RelativeHammingBall.

End FvqkdReal.
