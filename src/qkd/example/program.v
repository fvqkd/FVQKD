(* program.v -- BB84 finite program over the generic protocol language  *)
(* Module: qkd.example.program                                          *)
(* The concrete BB84 program: classical variable and value spaces,      *)
(* quantum label layout, and the component-wired program bb84_program.  *)

From mathcomp Require Import all_boot all_order all_algebra finmap.
From mathcomp.reals Require Import reals.
From quantum.external Require Import spectral complex.
From quantum Require Import mcextra mcaextra notation hermitian quantum cpo mxpred extnum ctopology svd mxnorm hspace inhabited.
From quantum.dirac Require Import hstensor.

Import Order.TTheory GRing.Theory Num.Theory Num.Def MxLownerOrder.
Import VectorInternalTheory.

From utils Require Import bitstr prob exports.
From lhl Require Import def.
From qkd.bb84 Require Import def model.
From qkd.protocol Require Import syntax semantics qkd_cmd.
From qkd.example Require Import device.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Open Scope ring_scope.
Local Open Scope qkd_scope.

Definition bb84_round_cvar (M : nat) := ('I_M + ('I_M + ('I_M + ('I_M + 'I_M))))%type.

Definition bb84_cvar (M : nat) := (bb84_round_cvar M + 'I_18)%type.

Definition BVa {M : nat} (i : 'I_M) : bb84_cvar M := inl (inl i).
Definition BVy {M : nat} (i : 'I_M) : bb84_cvar M := inl (inr (inl i)).
Definition BVb {M : nat} (i : 'I_M) : bb84_cvar M := inl (inr (inr (inl i))).
Definition BVy' {M : nat} (i : 'I_M) : bb84_cvar M := inl (inr (inr (inr (inl i)))).
Definition BVd {M : nat} (i : 'I_M) : bb84_cvar M := inl (inr (inr (inr (inr i)))).

Definition BVP {M : nat} : bb84_cvar M := inr (inord 0).
Definition BVX {M : nat} : bb84_cvar M := inr (inord 1).
Definition BVZ {M : nat} : bb84_cvar M := inr (inord 2).
Definition BVK {M : nat} : bb84_cvar M := inr (inord 3).
Definition BVXA {M : nat} : bb84_cvar M := inr (inord 4).
Definition BVXB {M : nat} : bb84_cvar M := inr (inord 5).
Definition BVZA {M : nat} : bb84_cvar M := inr (inord 6).
Definition BVZB {M : nat} : bb84_cvar M := inr (inord 7).
Definition BVlam {M : nat} : bb84_cvar M := inr (inord 8).
Definition BVpec {M : nat} : bb84_cvar M := inr (inord 9).
Definition BVXhat {M : nat} : bb84_cvar M := inr (inord 10).
Definition BVg {M : nat} : bb84_cvar M := inr (inord 11).
Definition BVtA {M : nat} : bb84_cvar M := inr (inord 12).
Definition BVtB {M : nat} : bb84_cvar M := inr (inord 13).
Definition BVf {M : nat} : bb84_cvar M := inr (inord 14).
Definition BVS {M : nat} : bb84_cvar M := inr (inord 15).
Definition BVSh {M : nat} : bb84_cvar M := inr (inord 16).
Definition BVabort {M : nat} : bb84_cvar M := inr (inord 17).

Lemma bb84_cvar_inr_neq {M : nat} (x y : 'I_18) : x != y -> (inr x : bb84_cvar M) != inr y.
Proof. move=> Hxy; apply/eqP=> Hsum. case: Hsum => Hxy_eq. by move: Hxy; rewrite Hxy_eq eqxx. Qed.

Fact bb84_abort_neq_f {M : nat} : @BVabort M != @BVf M.
Proof. by rewrite /BVabort /BVf /=; apply: bb84_cvar_inr_neq; rewrite -val_eqE /= !inordK. Qed.

Lemma bb84_abort_neq_S {M : nat} : @BVabort M != @BVS M.
Proof. by rewrite /BVabort /BVS /=; apply: bb84_cvar_inr_neq; rewrite -val_eqE /= !inordK. Qed.

Lemma bb84_abort_neq_Sh {M : nat} : @BVabort M != @BVSh M.
Proof. by rewrite /BVabort /BVSh /=; apply: bb84_cvar_inr_neq; rewrite -val_eqE /= !inordK. Qed.

Lemma bb84_abort_neq_P {M : nat} : @BVabort M != @BVP M.
Proof. by rewrite /BVabort /BVP /=; apply: bb84_cvar_inr_neq; rewrite -val_eqE /= !inordK. Qed.

Definition bb84_partial_bits (M : nat) := {ffun 'I_M -> option bool}.
Definition bb84_round_transcript (M : nat) := {ffun 'I_M -> option (bool * bool * bool)}.

Definition bb84_transcript (M ec_bits vseed_count tag_count paseed_count : nat) := (bb84_round_transcript M *
   option ({set 'I_M} * bb84_partial_bits M * bb84_partial_bits M) * option (option 'I_(2 ^ ec_bits) * option 'I_vseed_count *
           option 'I_tag_count) * option (option 'I_paseed_count))%type.

Definition bb84_eur_public (M vseed_count : nat) := (bb84_round_transcript M * {set 'I_M} * bb84_partial_bits M *
   bb84_partial_bits M * option 'I_vseed_count)%type.

Definition bb84_error_value (M : nat) := ('I_M.+1 * 'I_M.+1)%type.

Definition bb84_val (M n l ec_bits vseed_count tag_count paseed_count : nat) := (bool + (bool + (bool + (option bool + ({set 'I_M} +
  (bb84_partial_bits M + (bb84_error_value M + (bb84_transcript M ec_bits vseed_count tag_count paseed_count + (option 'I_(2 ^ ec_bits) +
  (option 'I_vseed_count + (option 'I_tag_count + (option 'I_paseed_count + (option 'I_(2 ^ n) +
  (option 'I_(2 ^ l) + unit))))))))))))))%type.

Definition bb84_bool_val {M n l ec_bits vseed_count tag_count paseed_count : nat} (b : bool)
    : bb84_val M n l ec_bits vseed_count tag_count paseed_count := inl b.

Definition bb84_basis_bool_val {M n l ec_bits vseed_count tag_count paseed_count : nat} (b : bool)
    : bb84_val M n l ec_bits vseed_count tag_count paseed_count := inr (inl b).

Definition bb84_bit_val {M n l ec_bits vseed_count tag_count paseed_count : nat} (b : bool)
    : bb84_val M n l ec_bits vseed_count tag_count paseed_count := inr (inr (inl b)).

Definition bb84_outcome_val {M n l ec_bits vseed_count tag_count paseed_count : nat} (o : option bool)
    : bb84_val M n l ec_bits vseed_count tag_count paseed_count := inr (inr (inr (inl o))).

Definition bb84_set_val {M n l ec_bits vseed_count tag_count paseed_count : nat} (X : {set 'I_M})
    : bb84_val M n l ec_bits vseed_count tag_count paseed_count := inr (inr (inr (inr (inl X)))).

Definition bb84_partial_bits_val {M n l ec_bits vseed_count tag_count paseed_count : nat} (bits : bb84_partial_bits M)
    : bb84_val M n l ec_bits vseed_count tag_count paseed_count := inr (inr (inr (inr (inr (inl bits))))).

Definition bb84_error_val {M n l ec_bits vseed_count tag_count paseed_count : nat} (err total : nat)
    : bb84_val M n l ec_bits vseed_count tag_count paseed_count := inr (inr (inr (inr (inr (inr (inl (inord err, inord total))))))).

Definition bb84_transcript_val {M n l ec_bits vseed_count tag_count paseed_count : nat} (tr : bb84_transcript M ec_bits vseed_count
    tag_count paseed_count) : bb84_val M n l ec_bits vseed_count tag_count paseed_count := inr (inr (inr (inr (inr (inr (inr (inl tr))))))).

Definition bb84_vseed_val {M n l ec_bits vseed_count tag_count paseed_count : nat} (x : option 'I_vseed_count)
    : bb84_val M n l ec_bits vseed_count tag_count paseed_count := inr (inr (inr (inr (inr (inr (inr (inr (inr (inl x))))))))).

Definition bb84_ec_val {M n l ec_bits vseed_count tag_count paseed_count : nat} (x : option 'I_(2 ^ ec_bits))
    : bb84_val M n l ec_bits vseed_count tag_count paseed_count := inr (inr (inr (inr (inr (inr (inr (inr (inl x)))))))).

Definition bb84_tag_val {M n l ec_bits vseed_count tag_count paseed_count : nat} (x : option 'I_tag_count)
    : bb84_val M n l ec_bits vseed_count tag_count paseed_count := inr (inr (inr (inr (inr (inr (inr (inr (inr (inr (inl x)))))))))).

Definition bb84_paseed_val {M n l ec_bits vseed_count tag_count paseed_count : nat} (x : option 'I_paseed_count)
    : bb84_val M n l ec_bits vseed_count tag_count paseed_count := inr (inr (inr (inr (inr (inr (inr (inr (inr (inr (inr (inl x))))))))))).

Definition bb84_raw_key_val {M n l ec_bits vseed_count tag_count paseed_count : nat} (x : option 'I_(2 ^ n)) : bb84_val M n l ec_bits
    vseed_count tag_count paseed_count := inr (inr (inr (inr (inr (inr (inr (inr (inr (inr (inr (inr (inl x)))))))))))).

Definition bb84_final_key_val {M n l ec_bits vseed_count tag_count paseed_count : nat} (x : option 'I_(2 ^ l)) : bb84_val M n l ec_bits
    vseed_count tag_count paseed_count := inr (inr (inr (inr (inr (inr (inr (inr (inr (inr (inr (inr (inr (inl x))))))))))))).

Definition bb84_bot_val {M n l ec_bits vseed_count tag_count paseed_count : nat} : bb84_val M n l ec_bits vseed_count tag_count paseed_count
    := inr (inr (inr (inr (inr (inr (inr (inr (inr (inr (inr (inr (inr (inr tt))))))))))))).

Definition bb84_bit_of {M n l ec_bits vseed_count tag_count paseed_count : nat} (v : bb84_val M n l ec_bits vseed_count tag_count
    paseed_count) : option bool := match v with | inr (inr (inl b)) => Some b | _ => None end.

Definition bb84_basis_bool_of {M n l ec_bits vseed_count tag_count paseed_count : nat}
    (v : bb84_val M n l ec_bits vseed_count tag_count paseed_count) : option bool := match v with | inr (inl b) => Some b | _ => None end.

Definition bb84_outcome_of {M n l ec_bits vseed_count tag_count paseed_count : nat} (v : bb84_val M n l ec_bits vseed_count tag_count
    paseed_count) : option (option bool) := match v with | inr (inr (inr (inl o))) => Some o | _ => None end.

Definition bb84_read_bit {M n l ec_bits vseed_count tag_count paseed_count : nat}
    (v : bb84_val M n l ec_bits vseed_count tag_count paseed_count) : option bool := match bb84_bit_of v with | Some b => Some b | None =>
      match bb84_outcome_of v with | Some (Some b) => Some b | _ => None end end.

Lemma bb84_bool_val_neq {M n l ec_bits vseed_count tag_count paseed_count : nat} : @bb84_bool_val M n l ec_bits vseed_count tag_count
    paseed_count true != @bb84_bool_val M n l ec_bits vseed_count tag_count paseed_count false.
Proof. by []. Qed.

Fact bb84_basis_bool_val_neq {M n l ec_bits vseed_count tag_count paseed_count : nat} : @bb84_basis_bool_val M n l ec_bits vseed_count
    tag_count paseed_count false != @bb84_basis_bool_val M n l ec_bits vseed_count tag_count paseed_count true.
Proof. by []. Qed.

Definition bb84_set_of {M n l ec_bits vseed_count tag_count paseed_count : nat} (v : bb84_val M n l ec_bits vseed_count tag_count
    paseed_count) : {set 'I_M} := match v with | inr (inr (inr (inr (inl X)))) => X | _ => set0 end.

Definition bb84_partial_bits_of {M n l ec_bits vseed_count tag_count paseed_count : nat} (v : bb84_val M n l ec_bits vseed_count tag_count
    paseed_count) : option (bb84_partial_bits M) := match v with | inr (inr (inr (inr (inr (inl bits))))) => Some bits | _ => None end.

Definition bb84_error_of {M n l ec_bits vseed_count tag_count paseed_count : nat} (v : bb84_val M n l ec_bits vseed_count tag_count
    paseed_count) : nat := match v with | inr (inr (inr (inr (inr (inr (inl e)))))) => nat_of_ord e.1 | _ => 0%N end.

Definition bb84_transcript_of {M n l ec_bits vseed_count tag_count paseed_count : nat} (v : bb84_val M n l ec_bits vseed_count tag_count
    paseed_count) : option (bb84_transcript M ec_bits vseed_count tag_count paseed_count) := match v with | inr (inr (inr (inr (inr (inr
    (inr (inl tr))))))) => Some tr | _ => None end.

Definition bb84_vseed_of {M n l ec_bits vseed_count tag_count paseed_count : nat}
    (v : bb84_val M n l ec_bits vseed_count tag_count paseed_count) : option 'I_vseed_count := match v with
  | inr (inr (inr (inr (inr (inr (inr (inr (inr (inl x))))))))) => x | _ => None end.

Definition bb84_ec_of {M n l ec_bits vseed_count tag_count paseed_count : nat} (v : bb84_val M n l ec_bits vseed_count tag_count
    paseed_count) : option 'I_(2 ^ ec_bits) := match v with | inr (inr (inr (inr (inr (inr (inr (inr (inl x)))))))) => x | _ => None end.

Definition bb84_tag_of {M n l ec_bits vseed_count tag_count paseed_count : nat}
    (v : bb84_val M n l ec_bits vseed_count tag_count paseed_count) : option 'I_tag_count := match v with
  | inr (inr (inr (inr (inr (inr (inr (inr (inr (inr (inl x)))))))))) => x | _ => None end.

Definition bb84_paseed_of {M n l ec_bits vseed_count tag_count paseed_count : nat}
    (v : bb84_val M n l ec_bits vseed_count tag_count paseed_count) : option 'I_paseed_count := match v with
  | inr (inr (inr (inr (inr (inr (inr (inr (inr (inr (inr (inl x))))))))))) => x | _ => None end.

Definition bb84_raw_key_of {M n l ec_bits vseed_count tag_count paseed_count : nat}
    (v : bb84_val M n l ec_bits vseed_count tag_count paseed_count) : option 'I_(2 ^ n) := match v with
  | inr (inr (inr (inr (inr (inr (inr (inr (inr (inr (inr (inr (inl x)))))))))))) => x | _ => None end.

Definition bb84_final_key_of {M n l ec_bits vseed_count tag_count paseed_count : nat}
    (v : bb84_val M n l ec_bits vseed_count tag_count paseed_count) : option 'I_(2 ^ l) := match v with
  | inr (inr (inr (inr (inr (inr (inr (inr (inr (inr (inr (inr (inr (inl x))))))))))))) => x | _ => None end.

Definition bb84_verify_hash_val {M n l ec_bits vseed_count tag_count paseed_count : nat} (vh : 'I_vseed_count -> 'I_(2 ^ n) -> 'I_tag_count)
    (seed raw : bb84_val M n l ec_bits vseed_count tag_count paseed_count) : bb84_val M n l ec_bits vseed_count tag_count paseed_count :=
  match bb84_vseed_of seed, bb84_raw_key_of raw with | Some g, Some x => bb84_tag_val (Some (vh g x)) | _, _ => bb84_tag_val None end.

Definition bb84_ir_pub_val {M n l ec_bits vseed_count tag_count paseed_count : nat} (ir_pub : 'I_(2 ^ n) -> 'I_(2 ^ n) -> 'I_(2 ^ ec_bits))
    (_leakEC : nat) (alice bob : bb84_val M n l ec_bits vseed_count tag_count paseed_count)
    : bb84_val M n l ec_bits vseed_count tag_count paseed_count := match bb84_raw_key_of alice, bb84_raw_key_of bob with
  | Some x, Some y => bb84_ec_val (Some (ir_pub x y)) | _, _ => bb84_ec_val None end.

Definition bb84_ir_dec_val {M n l ec_bits vseed_count tag_count paseed_count : nat} (ir_dec : 'I_(2 ^ ec_bits) -> 'I_(2 ^ n) -> 'I_(2 ^ n))
    (transcript bob : bb84_val M n l ec_bits vseed_count tag_count paseed_count)
    : bb84_val M n l ec_bits vseed_count tag_count paseed_count := match bb84_ec_of transcript, bb84_raw_key_of bob with
  | Some p, Some y => bb84_raw_key_val (Some (ir_dec p y)) | _, _ => bb84_raw_key_val None end.

Definition bb84_privacy_hash_val {M n l ec_bits vseed_count tag_count paseed_count : nat} (pa : 'I_paseed_count -> 'I_(2 ^ n) -> 'I_(2 ^ l))
    (_l : nat) (seed raw : bb84_val M n l ec_bits vseed_count tag_count paseed_count)
    : bb84_val M n l ec_bits vseed_count tag_count paseed_count := match bb84_paseed_of seed, bb84_raw_key_of raw with
  | Some f, Some x => bb84_final_key_val (Some (pa f x)) | _, _ => bb84_final_key_val None end.

Definition bb84_selected_index {M n : nat} (K : {set 'I_M}) (j : 'I_n) : option 'I_M := nth None [seq Some i | i <- enum K] j.

Fact bb84_selected_index_enum_val {M : nat} (K : {set 'I_M}) (j : 'I_#|K|) : bb84_selected_index K j = Some (enum_val j).
Proof. rewrite /bb84_selected_index (nth_map (enum_val j)); last by rewrite -cardE. by congr Some; rewrite -enum_val_nth. Qed.

Lemma bb84_selected_index_mem {M n : nat} (K : {set 'I_M}) (j : 'I_n) (i : 'I_M) : bb84_selected_index K j = Some i -> i \in K.
Proof.
  rewrite /bb84_selected_index => Hnth.
  have Hj : (j < size [seq Some x | x <- enum K])%N.
  { apply/negPn/negP=> Hj; have Hle : (size [seq Some x | x <- enum K] <= j)%N by rewrite leqNgt Hj.
    by move: Hnth; rewrite (nth_default None Hle). } have Hin : Some i \in [seq Some x | x <- enum K] by rewrite -Hnth; exact: mem_nth.
  by move/mapP: Hin => [x Hx [= ->]]; rewrite mem_enum in Hx. Qed.

Lemma bb84_selected_index_some {M n : nat} (K : {set 'I_M}) : n = #|K| -> forall j : 'I_n, exists i, bb84_selected_index K j = Some i.
Proof. move=> -> j; exists (enum_val j). exact: bb84_selected_index_enum_val. Qed.

Definition bb84_bits_on_val {M n l ec_bits vseed_count tag_count paseed_count : nat} (K : {set 'I_M}) (bits : 'I_M -> bb84_val M n l ec_bits
    vseed_count tag_count paseed_count) : bb84_val M n l ec_bits vseed_count tag_count paseed_count := if #|K| == n then bb84_raw_key_val
    (Some (bitstring_to_ord (fun j => match bb84_selected_index K j with | Some i => if bb84_read_bit (bits i) is Some b then b else false |
    None => false end))) else bb84_raw_key_val None.

Definition bb84_partial_bits_on_val {M n l ec_bits vseed_count tag_count paseed_count : nat} (K : {set 'I_M}) (bits : 'I_M -> bb84_val M n l
    ec_bits vseed_count tag_count paseed_count) : bb84_val M n l ec_bits vseed_count tag_count paseed_count := bb84_partial_bits_val [ffun i
    => if i \in K then bb84_read_bit (bits i) else None].

Definition bb84_partial_error_count (M : nat) (a b : bb84_partial_bits M) : nat := #|[set i : 'I_M | if a i is Some x then
      if b i is Some y then x != y else false else false]|.

Definition bb84_err_count_val {M n l ec_bits vseed_count tag_count paseed_count : nat}
    (a b : bb84_val M n l ec_bits vseed_count tag_count paseed_count) : nat := match bb84_partial_bits_of a, bb84_partial_bits_of b with
  | Some aa, Some bb => bb84_partial_error_count aa bb | _, _ => match bb84_raw_key_of a, bb84_raw_key_of b with
      | Some x, Some y => d_ham (ord_to_bitstring x) (ord_to_bitstring y) | _, _ => 0%N end end.

Definition bb84_empty_transcript (M ec_bits vseed_count tag_count paseed_count : nat)
    : bb84_transcript M ec_bits vseed_count tag_count paseed_count := ([ffun _ => None], None, None, None).

Definition bb84_empty_transcript_val {M n l ec_bits vseed_count tag_count paseed_count : nat} : bb84_val M n l ec_bits vseed_count tag_count
    paseed_count := bb84_transcript_val (bb84_empty_transcript M ec_bits vseed_count tag_count paseed_count).

Definition bb84_transcript_or_empty {M n l ec_bits vseed_count tag_count paseed_count : nat}
    (v : bb84_val M n l ec_bits vseed_count tag_count paseed_count) : bb84_transcript M ec_bits vseed_count tag_count paseed_count :=
  if bb84_transcript_of v is Some tr then tr else bb84_empty_transcript M ec_bits vseed_count tag_count paseed_count.

Definition bb84_tr_app_rounds {M n l ec_bits vseed_count tag_count paseed_count : nat} (rounds : 'I_M -> bb84_val M n l ec_bits vseed_count
    tag_count paseed_count * bb84_val M n l ec_bits vseed_count tag_count paseed_count * bb84_val M n l ec_bits vseed_count tag_count
    paseed_count) (trv : bb84_val M n l ec_bits vseed_count tag_count paseed_count) : bb84_val M n l ec_bits vseed_count tag_count
    paseed_count := let '(round_old, pe, ec, pa) := bb84_transcript_or_empty trv in let round_new := [ffun i => let '(a, b, d) := rounds i
    in match bb84_basis_bool_of a, bb84_basis_bool_of b with | Some aa, Some bb => match d with | inl detected => Some (aa, bb, detected) |
    _ => None end | _, _ => None end] in bb84_transcript_val (round_new, pe, ec, pa).

Definition bb84_tr_app_pe {M n l ec_bits vseed_count tag_count paseed_count : nat} (K ZA ZB trv : bb84_val M n l ec_bits vseed_count
    tag_count paseed_count) : bb84_val M n l ec_bits vseed_count tag_count paseed_count := let '(rounds, _pe, ec, pa) :=
    bb84_transcript_or_empty trv in let empty_bits : bb84_partial_bits M := [ffun _ => None] in let ZA_bits := if bb84_partial_bits_of ZA is
    Some bits then bits else empty_bits in let ZB_bits := if bb84_partial_bits_of ZB is Some bits then bits else empty_bits in
    bb84_transcript_val (rounds, Some (bb84_set_of K, ZA_bits, ZB_bits), ec, pa).

Definition bb84_tr_app_ec {M n l ec_bits vseed_count tag_count paseed_count : nat} (pEC g tA trv : bb84_val M n l ec_bits vseed_count
    tag_count paseed_count) : bb84_val M n l ec_bits vseed_count tag_count paseed_count := let '(rounds, pe, _ec, pa) :=
    bb84_transcript_or_empty trv in bb84_transcript_val (rounds, pe, Some (bb84_ec_of pEC, bb84_vseed_of g, bb84_tag_of tA), pa).

Definition bb84_tr_app_pa {M n l ec_bits vseed_count tag_count paseed_count : nat}
    (f trv : bb84_val M n l ec_bits vseed_count tag_count paseed_count) : bb84_val M n l ec_bits vseed_count tag_count paseed_count :=
  let '(rounds, pe, ec, _pa) := bb84_transcript_or_empty trv in bb84_transcript_val (rounds, pe, ec, Some (bb84_paseed_of f)).

Definition bb84_eur_public_of_transcript {M ec_bits vseed_count tag_count paseed_count : nat} (tr : bb84_transcript M ec_bits vseed_count
    tag_count paseed_count) : bb84_eur_public M vseed_count := let empty_bits : bb84_partial_bits M := [ffun _ => None] in let empty_set :
    {set 'I_M} := [set i : 'I_M | false] in let '(rounds, pe, ec, _pa) := tr in let '(K, ZA, ZB) := if pe is Some pe_data then pe_data else
    (empty_set, empty_bits, empty_bits) in let g := if ec is Some (_, g, _) then g else None in (rounds, K, ZA, ZB, g).

Definition bb84_eur_public_of_value {M n l ec_bits vseed_count tag_count paseed_count : nat} (v : bb84_val M n l ec_bits vseed_count
    tag_count paseed_count) : bb84_eur_public M vseed_count := bb84_eur_public_of_transcript (bb84_transcript_or_empty v).

Fact bb84_eur_public_of_tr_app_pa {M n l ec_bits vseed_count tag_count paseed_count : nat} (f trv : bb84_val M n l ec_bits vseed_count
    tag_count paseed_count) : bb84_eur_public_of_value (bb84_tr_app_pa f trv) = bb84_eur_public_of_value trv.
Proof. rewrite /bb84_eur_public_of_value /bb84_tr_app_pa /bb84_eur_public_of_transcript. by case: (bb84_transcript_or_empty trv) => [[[rounds pe] ec] pa]. Qed.

Definition bb84_eur_public_of_store {M n l ec_bits vseed_count tag_count paseed_count : nat} (s : @store (bb84_cvar M)
      (bb84_val M n l ec_bits vseed_count tag_count paseed_count)) : bb84_eur_public M vseed_count := bb84_eur_public_of_value (s (@BVP M)).

Definition bb84_nsubset_count (M : nat) (m : nat) (X : {set 'I_M}) : nat := #|[set K : {set 'I_M} | (#|K| == m) && (K \subset X)]|.

Fact bb84_nsubset_count_pos (M m : nat) (X : {set 'I_M}) : (m <= #|X|)%N -> (0 < bb84_nsubset_count m X)%N.
Proof. move=> /card_geqP [s [Hsuniq Hsize Hsub]]; apply/card_gt0P. exists [set x : 'I_M | x \in s]; rewrite /bb84_nsubset_count inE. apply/andP; split; first by apply/eqP; rewrite cardsE (card_uniqP Hsuniq) Hsize. by apply/subsetP=> x; rewrite inE => Hxs; exact: Hsub. Qed.

Definition bb84_unif_nsubset_mass {R : realType} {M n l ec_bits vseed_count tag_count paseed_count : nat} (m : nat) (X : {set 'I_M})
    (v : bb84_val M n l ec_bits vseed_count tag_count paseed_count) : R := \sum_(K : {set 'I_M} | (#|K| == m) && (K \subset X))
    if v == bb84_set_val K then (bb84_nsubset_count m X)%:R^-1 else 0.

Lemma bb84_unif_nsubset_mass_nonneg {R : realType} {M n l ec_bits vseed_count tag_count paseed_count : nat} (m : nat) (X : {set 'I_M})
    (v : bb84_val M n l ec_bits vseed_count tag_count paseed_count) : 0 <= @bb84_unif_nsubset_mass R M n l ec_bits vseed_count tag_count
    paseed_count m X v.
Proof. by rewrite /bb84_unif_nsubset_mass; apply: sumr_ge0 => K _; case: ifP => _; rewrite ?invr_ge0 ?ler0n ?lexx. Qed.

Lemma bb84_unif_nsubset_mass_outside {R : realType} {M n l ec_bits vseed_count tag_count paseed_count : nat} (m : nat) (X : {set 'I_M})
    (v : bb84_val M n l ec_bits vseed_count tag_count paseed_count) : ~~ ((#|bb84_set_of v| == m) && (bb84_set_of v \subset X)) ->
  @bb84_unif_nsubset_mass R M n l ec_bits vseed_count tag_count paseed_count m X v = 0.
Proof. move=> Hout; rewrite /bb84_unif_nsubset_mass; apply: big1 => K /andP [HKm HKX]. by case Hval: (v == bb84_set_val K) => //; move: Hout; rewrite (eqP Hval) /bb84_set_of /bb84_set_val HKm HKX. Qed.

Lemma bb84_unif_nsubset_mass_support {R : realType} {M n l ec_bits vseed_count tag_count paseed_count : nat} (m : nat) (X : {set 'I_M})
    (v : bb84_val M n l ec_bits vseed_count tag_count paseed_count) : @bb84_unif_nsubset_mass R M n l ec_bits vseed_count tag_count
    paseed_count m X v != 0 -> (#|bb84_set_of v| == m) && (bb84_set_of v \subset X).
Proof. by move=> Hnz; apply/negPn/negP=> Hout; move: Hnz; rewrite (bb84_unif_nsubset_mass_outside Hout) eqxx. Qed.

Fact bb84_unif_nsubset_mass_set_val {R : realType} {M n l ec_bits vseed_count tag_count paseed_count : nat} (m : nat) (X K : {set 'I_M}) :
  #|K| = m -> K \subset X -> @bb84_unif_nsubset_mass R M n l ec_bits vseed_count tag_count paseed_count m X (bb84_set_val K) =
    (bb84_nsubset_count m X)%:R^-1.
Proof.
  move=> Hcard Hsub; rewrite /bb84_unif_nsubset_mass.
  rewrite (bigD1 K); last by rewrite Hcard eqxx Hsub.
  rewrite eqxx /= [X in _ + X]big1 ?addr0 // => J /andP[_ HJK].
  case Hval: (bb84_set_val K == bb84_set_val J) => //.
  move/eqP: Hval => Hval; have HKJ : K = J.
  { by have := congr1 (@bb84_set_of M n l ec_bits vseed_count tag_count paseed_count) Hval; rewrite /bb84_set_of /bb84_set_val. } by move: HJK; rewrite HKJ eqxx. Qed.

Fact bb84_unif_nsubset_mass_sum1 {R : realType} {M n l ec_bits vseed_count tag_count paseed_count : nat} (m : nat) (X : {set 'I_M}) :
  (0 < bb84_nsubset_count m X)%N -> \sum_v @bb84_unif_nsubset_mass R M n l ec_bits vseed_count tag_count paseed_count m X v = 1.
Proof.
  move=> Hcount; rewrite /bb84_unif_nsubset_mass exchange_big /=.
  rewrite (eq_bigr (fun _ : {set 'I_M} => (bb84_nsubset_count m X)%:R^-1)).
  - rewrite sumr_const; set c := (bb84_nsubset_count m X)%:R^-1.
    rewrite -mulr_natr -/(@bb84_nsubset_count M m X) /c.
    have Hcards : #|(fun K : {set 'I_M} => (#|K| == m) && (K \subset X))| = #|[set K : {set 'I_M} | (#|K| == m) && (K \subset X)]| by rewrite cardsE.
    by rewrite Hcards -/(@bb84_nsubset_count M m X) mulVf // lt0r_neq0 // ltr0n.
  - move=> K _; rewrite (bigD1 (bb84_set_val K)) //= eqxx.
    by rewrite [X in _ + X]big1 ?addr0 // => v Hv; case: ifP => // /eqP Hsame; move: Hv; rewrite Hsame eqxx. Qed.

Definition bb84_unif_vseed_mass {R : realType} {M n l ec_bits vseed_count tag_count paseed_count : nat} : @dexpr R (bb84_cvar M) (bb84_val M
    n l ec_bits vseed_count tag_count paseed_count) := fun _ v => \sum_g if v == bb84_vseed_val (Some g) then (vseed_count%:R)^-1 else 0.

Definition bb84_unif_pseed_mass {R : realType} {M n l ec_bits vseed_count tag_count paseed_count : nat} : @dexpr R (bb84_cvar M) (bb84_val M
    n l ec_bits vseed_count tag_count paseed_count) := fun _ v => \sum_f if v == bb84_paseed_val (Some f) then (paseed_count%:R)^-1 else 0.

Lemma bb84_vseed_of_val {M n l ec_bits vseed_count tag_count paseed_count : nat} (x : option 'I_vseed_count) :
  @bb84_vseed_of M n l ec_bits vseed_count tag_count paseed_count (bb84_vseed_val x) = x.
Proof. by []. Qed.

Fact bb84_paseed_of_val {M n l ec_bits vseed_count tag_count paseed_count : nat} (x : option 'I_paseed_count) :
  @bb84_paseed_of M n l ec_bits vseed_count tag_count paseed_count (bb84_paseed_val x) = x.
Proof. by []. Qed.

Lemma bb84_raw_key_of_val {M n l ec_bits vseed_count tag_count paseed_count : nat} (x : option 'I_(2 ^ n)) :
  @bb84_raw_key_of M n l ec_bits vseed_count tag_count paseed_count (bb84_raw_key_val x) = x.
Proof. by []. Qed.

Fact bb84_final_key_of_val {M n l ec_bits vseed_count tag_count paseed_count : nat} (x : option 'I_(2 ^ l)) :
  @bb84_final_key_of M n l ec_bits vseed_count tag_count paseed_count (bb84_final_key_val x) = x.
Proof. by []. Qed.

Lemma bb84_bit_of_val {M n l ec_bits vseed_count tag_count paseed_count : nat} (b : bool) :
  @bb84_bit_of M n l ec_bits vseed_count tag_count paseed_count (bb84_bit_val b) = Some b.
Proof. by []. Qed.

Fact bb84_basis_bool_of_val {M n l ec_bits vseed_count tag_count paseed_count : nat} (b : bool) :
  @bb84_basis_bool_of M n l ec_bits vseed_count tag_count paseed_count (bb84_basis_bool_val b) = Some b.
Proof. by []. Qed.

Section BB84ValueSupport.
Variable R : realType.
Notation C := (@hermitian.C R).
Variables M n l ec_bits vseed_count tag_count paseed_count : nat.
Variable T : lmodType C.

Definition bb84_basis_bool_mass (px : R) (v : bb84_val M n l ec_bits vseed_count tag_count paseed_count) : R :=
  if v == bb84_basis_bool_val false then px else if v == bb84_basis_bool_val true then 1 - px else 0.

Definition bb84_bit_mass (v : bb84_val M n l ec_bits vseed_count tag_count paseed_count) : R := if v == bb84_bit_val false then (2%:R)^-1
  else if v == bb84_bit_val true then (2%:R)^-1 else 0.

Fact bb84_basis_bool_mass_nonneg (px : R) (v : bb84_val M n l ec_bits vseed_count tag_count paseed_count) :
  0 <= px -> px <= 1 -> 0 <= bb84_basis_bool_mass px v.
Proof. move=> Hpx0 Hpx1; rewrite /bb84_basis_bool_mass; case: ifP => _; first exact: Hpx0. by case: ifP => _; [rewrite subr_ge0 | exact: lexx]. Qed.

Fact bb84_basis_bool_mass_sum1 (px : R) : \sum_v bb84_basis_bool_mass px v = 1.
Proof. rewrite /bb84_basis_bool_mass /bb84_val /bb84_basis_bool_val big_sumType /= [\sum_(b : bool) _]big1; last by move=> b _. rewrite add0r big_sumType /= big_bool /= [X in _ + X]big1; last by move=> x _. by rewrite addr0 subrK. Qed.

Fact bb84_bit_mass_nonneg (v : bb84_val M n l ec_bits vseed_count tag_count paseed_count) : 0 <= bb84_bit_mass v.
Proof. by rewrite /bb84_bit_mass; case: ifP => _; [rewrite invr_ge0 ler0n | case: ifP => _; [rewrite invr_ge0 ler0n | exact: lexx]]. Qed.

Fact bb84_bit_mass_sum1 : \sum_v bb84_bit_mass v = 1.
Proof.
  rewrite /bb84_bit_mass /bb84_val /bb84_bit_val big_sumType /= [\sum_(b : bool) _]big1; last by move=> b _.
  rewrite add0r big_sumType /= [\sum_(b : bool) _]big1; last by move=> b _.
  rewrite add0r big_sumType /= big_bool /= [X in _ + X]big1; last by move=> x _.
  rewrite addr0; have H2 : (2%:R : R) != 0 by rewrite pnatr_eq0.
  by apply: (mulIf H2); rewrite mulrDl !mulVf // mul1r -mulr2n. Qed.

Fact bb84_outcome_support_sum (F : option bool -> T) : \sum_v (if @bb84_outcome_of M n l ec_bits vseed_count tag_count
      paseed_count v is Some outcome then F outcome else 0) = F None + F (Some false) + F (Some true).
Proof.
  have bb84_outcome_val_support_sum : forall (F : bb84_val M n l ec_bits vseed_count tag_count paseed_count -> T), \sum_v (if bb84_outcome_of v is Some _ then F v else 0) = F (bb84_outcome_val None) + F (bb84_outcome_val (Some false)) + F (bb84_outcome_val (Some true)).
  { move=> {}F. rewrite /bb84_val /bb84_outcome_val /bb84_outcome_of big_sumType /=. rewrite [\sum_(b : bool) _]big1; last by move=> b _.
    rewrite add0r big_sumType /=. rewrite [\sum_(b : bool) _]big1; last by move=> b _. rewrite add0r big_sumType /=. rewrite [\sum_(b : bool) _]big1; last by move=> b _. rewrite add0r big_sumType /=. rewrite [X in _ + X]big1; last by move=> x _. rewrite addr0 (bigD1 None) //=. rewrite (bigD1 (Some false)) //=. rewrite (bigD1 (Some true)) //=. rewrite [X in _ + (_ + (_ + X))]big1; last first. { by move=> [[|]|] /andP []. } by rewrite addr0 !addrA. } rewrite -(bb84_outcome_val_support_sum (fun v => if @bb84_outcome_of M n l ec_bits vseed_count tag_count paseed_count v is Some outcome then F outcome else 0)).
  by apply: eq_bigr => v _; case: (@bb84_outcome_of M n l ec_bits vseed_count tag_count paseed_count v). Qed.

Fact bb84_unif_pseed_val_support_sum (s : @store (bb84_cvar M) (bb84_val M n l ec_bits vseed_count tag_count paseed_count)) (F : bb84_val M
    n l ec_bits vseed_count tag_count paseed_count -> T) : \sum_v ((@bb84_unif_pseed_mass R M n l ec_bits vseed_count tag_count paseed_count
    s v)%:C *: F v) = \sum_f (((paseed_count%:R)^-1)%:C *: F (bb84_paseed_val (Some f))).
Proof.
  rewrite /bb84_unif_pseed_mass; under eq_bigr => v _ do rewrite rmorph_sum scaler_suml.
  rewrite exchange_big /=; apply: eq_bigr => f _.
  rewrite (bigD1 (bb84_paseed_val (Some f))) //= eqxx [X in _ + X]big1 ?addr0 // => v Hv.
  by case: ifP => [/eqP Hsame | _]; [move: Hv; rewrite Hsame eqxx | rewrite rmorph0 scale0r]. Qed.

End BB84ValueSupport.

Fact bb84_set_of_val {M n l ec_bits vseed_count tag_count paseed_count : nat} (X : {set 'I_M}) :
  @bb84_set_of M n l ec_bits vseed_count tag_count paseed_count (bb84_set_val X) = X.
Proof. by []. Qed.

Fact bb84_raw_key_of_bits_on_val {M n l ec_bits vseed_count tag_count paseed_count : nat} (K : {set 'I_M}) (bits : 'I_M -> bb84_val M n l
    ec_bits vseed_count tag_count paseed_count) : @bb84_raw_key_of M n l ec_bits vseed_count tag_count paseed_count (bb84_bits_on_val K
    bits) = if #|K| == n then Some (bitstring_to_ord (fun j => match bb84_selected_index K j with | Some i => if bb84_read_bit (bits i) is
    Some b then b else false | None => false end)) else None.
Proof. by rewrite /bb84_bits_on_val; case: ifP; rewrite bb84_raw_key_of_val. Qed.

Fact bb84_bits_on_val_raw_key {M n l ec_bits vseed_count tag_count paseed_count : nat} (K : {set 'I_M}) (bits : 'I_M -> bb84_val M n l
    ec_bits vseed_count tag_count paseed_count) : bb84_bits_on_val K bits = bb84_raw_key_val (bb84_raw_key_of (bb84_bits_on_val K bits)).
Proof. rewrite /bb84_bits_on_val. by case: ifP; rewrite bb84_raw_key_of_val. Qed.

Fact bb84_partial_bits_of_partial_bits_on_val {M n l ec_bits vseed_count tag_count paseed_count : nat} (K : {set 'I_M}) (bits : 'I_M ->
    bb84_val M n l ec_bits vseed_count tag_count paseed_count) : @bb84_partial_bits_of M n l ec_bits vseed_count tag_count paseed_count
    (bb84_partial_bits_on_val K bits) = Some [ffun i => if i \in K then bb84_read_bit (bits i) else None].
Proof. by []. Qed.

Fact bb84_err_count_partial_bits_on_val {M n l ec_bits vseed_count tag_count paseed_count : nat} (K : {set 'I_M})
    (alice bob : 'I_M -> bb84_val M n l ec_bits vseed_count tag_count paseed_count) :
  @bb84_err_count_val M n l ec_bits vseed_count tag_count paseed_count (bb84_partial_bits_on_val K alice) (bb84_partial_bits_on_val K bob) =
  #|[set i : 'I_M | (i \in K) && match bb84_read_bit (alice i), bb84_read_bit (bob i) with | Some x, Some y => x != y | _, _ => false end]|.
Proof. rewrite /bb84_err_count_val !bb84_partial_bits_of_partial_bits_on_val /bb84_partial_error_count. by apply/eq_card=> i; rewrite !inE !ffunE; case: (i \in K). Qed.

Fact bb84_verify_hash_valE {M n l ec_bits vseed_count tag_count paseed_count : nat} (vh : 'I_vseed_count -> 'I_(2 ^ n) -> 'I_tag_count)
    (g : 'I_vseed_count) (x : 'I_(2 ^ n)) : @bb84_verify_hash_val M n l ec_bits vseed_count tag_count paseed_count
    vh (bb84_vseed_val (Some g)) (bb84_raw_key_val (Some x)) = bb84_tag_val (Some (vh g x)).
Proof. by rewrite /bb84_verify_hash_val !bb84_vseed_of_val !bb84_raw_key_of_val. Qed.

Lemma bb84_verify_hash_val_collision {M n l ec_bits vseed_count tag_count paseed_count : nat} (vh : 'I_vseed_count -> 'I_(2 ^ n) ->
    'I_tag_count) (g : 'I_vseed_count) (x x' : 'I_(2 ^ n)) : (@bb84_verify_hash_val M n l ec_bits vseed_count tag_count paseed_count vh
    (bb84_vseed_val (Some g)) (bb84_raw_key_val (Some x)) == @bb84_verify_hash_val M n l ec_bits vseed_count tag_count paseed_count vh
    (bb84_vseed_val (Some g)) (bb84_raw_key_val (Some x'))) = (vh g x == vh g x').
Proof. by rewrite !bb84_verify_hash_valE. Qed.

Lemma bb84_unif_vseed_mass_nonneg {R : realType} {M n l ec_bits vseed_count tag_count paseed_count : nat} (s : @store (bb84_cvar M)
      (bb84_val M n l ec_bits vseed_count tag_count paseed_count)) (v : bb84_val M n l ec_bits vseed_count tag_count paseed_count) : 0 <=
  @bb84_unif_vseed_mass R M n l ec_bits vseed_count tag_count paseed_count s v.
Proof. by rewrite /bb84_unif_vseed_mass; apply: sumr_ge0 => g _; case: ifP => _; rewrite ?invr_ge0 ?ler0n ?lexx. Qed.

Lemma bb84_unif_vseed_mass_sum1 {R : realType} {M n l ec_bits vseed_count tag_count paseed_count : nat} (s : @store (bb84_cvar M)
      (bb84_val M n l ec_bits vseed_count tag_count paseed_count)) : (0 < vseed_count)%N -> \sum_v
    @bb84_unif_vseed_mass R M n l ec_bits vseed_count tag_count paseed_count s v = 1.
Proof.
  move=> Hvseed_pos; rewrite /bb84_unif_vseed_mass exchange_big /=.
  rewrite (eq_bigr (fun _ : 'I_vseed_count => (vseed_count%:R)^-1)).
  - by transitivity (((vseed_count%:R)^-1) * (vseed_count%:R : R)); [rewrite sumr_const card_ord mulr_natr | rewrite mulVf // lt0r_neq0 // ltr0n].
  - move=> g _; rewrite (bigD1 (bb84_vseed_val (Some g))) //= eqxx.
    by rewrite [X in _ + X]big1 ?addr0 // => v Hv; case: ifP => // /eqP Hsame; move: Hv; rewrite Hsame eqxx. Qed.

Lemma bb84_unif_pseed_mass_nonneg {R : realType} {M n l ec_bits vseed_count tag_count paseed_count : nat} (s : @store (bb84_cvar M)
      (bb84_val M n l ec_bits vseed_count tag_count paseed_count)) (v : bb84_val M n l ec_bits vseed_count tag_count paseed_count) : 0 <=
  @bb84_unif_pseed_mass R M n l ec_bits vseed_count tag_count paseed_count s v.
Proof. by rewrite /bb84_unif_pseed_mass; apply: sumr_ge0 => f _; case: ifP => _; rewrite ?invr_ge0 ?ler0n ?lexx. Qed.

Lemma bb84_unif_pseed_mass_sum1 {R : realType} {M n l ec_bits vseed_count tag_count paseed_count : nat} (s : @store (bb84_cvar M)
      (bb84_val M n l ec_bits vseed_count tag_count paseed_count)) : (0 < paseed_count)%N -> \sum_v
    @bb84_unif_pseed_mass R M n l ec_bits vseed_count tag_count paseed_count s v = 1.
Proof.
  move=> Hpaseed_pos; rewrite /bb84_unif_pseed_mass exchange_big /=.
  rewrite (eq_bigr (fun _ : 'I_paseed_count => (paseed_count%:R)^-1)).
  - by transitivity (((paseed_count%:R)^-1) * (paseed_count%:R : R)); [rewrite sumr_const card_ord mulr_natr | rewrite mulVf // lt0r_neq0 // ltr0n].
  - move=> f _; rewrite (bigD1 (bb84_paseed_val (Some f))) //= eqxx.
    by rewrite [X in _ + X]big1 ?addr0 // => v Hv; case: ifP => // /eqP Hsame; move: Hv; rewrite Hsame eqxx. Qed.

Lemma bb84_unif_vseed_mass_support_sum {R : realType} {M n l ec_bits vseed_count tag_count paseed_count : nat} (s : @store (bb84_cvar M)
      (bb84_val M n l ec_bits vseed_count tag_count paseed_count)) (F : bb84_val M n l ec_bits vseed_count tag_count paseed_count -> R) :
  \sum_v @bb84_unif_vseed_mass R M n l ec_bits vseed_count tag_count paseed_count s v * F v = \sum_g (vseed_count%:R)^-1 *
    F (bb84_vseed_val (Some g)).
Proof. rewrite /bb84_unif_vseed_mass; under eq_bigr => v _ do rewrite mulr_suml. rewrite exchange_big /=; apply: eq_bigr => g _. rewrite (bigD1 (bb84_vseed_val (Some g))) //= eqxx [X in _ + X]big1 ?addr0 // => v Hv. by case: ifP => [/eqP Hsame | _]; [move: Hv; rewrite Hsame eqxx | rewrite mul0r]. Qed.

Fact bb84_verify_hash_value_collision_probE {R : realType} {M n l ec_bits vseed_count tag_count paseed_count : nat} (s : @store (bb84_cvar
    M) (bb84_val M n l ec_bits vseed_count tag_count paseed_count)) (vh : 'I_vseed_count -> 'I_(2 ^ n) -> 'I_tag_count) (x x' : 'I_(2 ^ n))
    : \sum_v @bb84_unif_vseed_mass R M n l ec_bits vseed_count tag_count paseed_count s v * ((bb84_verify_hash_val vh v (bb84_raw_key_val
    (Some x)) == bb84_verify_hash_val vh v (bb84_raw_key_val (Some x')))%:R) = (#|[set g : 'I_vseed_count | vh g x == vh g x']|%:R : R) *
    (vseed_count%:R)^-1.
Proof.
  rewrite bb84_unif_vseed_mass_support_sum (eq_bigr (fun g : 'I_vseed_count => (vseed_count%:R)^-1 * ((vh g x == vh g x')%:R))).
  - rewrite (bigID (fun g : 'I_vseed_count => vh g x == vh g x')) /= [X in _ + X]big1 ?addr0.
    + rewrite (eq_bigr (fun _ : 'I_vseed_count => (vseed_count%:R)^-1)).
      * have Hcard : #|[pred g : 'I_vseed_count | vh g x == vh g x']| = #|[set g : 'I_vseed_count | vh g x == vh g x']| by apply: eq_card => g; rewrite inE. by rewrite sumr_const Hcard mulr_natl.
      * by move=> g Hg; rewrite Hg mulr1.
    + by move=> g /negbTE Hg; rewrite Hg mulr0.
  - by move=> g _; rewrite bb84_verify_hash_val_collision. Qed.

Fact bb84_verify_hash_raw_key_mismatch_probE {R : realType} {M n l ec_bits vseed_count tag_count paseed_count : nat} (s : @store (bb84_cvar
    M) (bb84_val M n l ec_bits vseed_count tag_count paseed_count)) (vh : 'I_vseed_count -> 'I_(2 ^ n) -> 'I_tag_count) (ox ox' : option
    'I_(2 ^ n)) : \sum_v @bb84_unif_vseed_mass R M n l ec_bits vseed_count tag_count paseed_count s v * (((bb84_verify_hash_val vh v
    (@bb84_raw_key_val M n l ec_bits vseed_count tag_count paseed_count ox) == bb84_verify_hash_val vh v (@bb84_raw_key_val M n l ec_bits
    vseed_count tag_count paseed_count ox')) && (@bb84_raw_key_val M n l ec_bits vseed_count tag_count paseed_count ox != @bb84_raw_key_val
    M n l ec_bits vseed_count tag_count paseed_count ox'))%:R) = match ox, ox' with | Some x, Some x' => if x == x' then 0 else (#|[set g :
    'I_vseed_count | vh g x == vh g x']|%:R : R) * (vseed_count%:R)^-1 | _, _ => 0 end.
Proof.
  case: ox => [x|]; case: ox' => [x'|] /=.
  - case Hxx: (x == x').
    + move/eqP: Hxx => ->; rewrite bb84_unif_vseed_mass_support_sum.
      by apply: big1 => g _; rewrite bb84_verify_hash_val_collision !eqxx mulr0.
    + have Hraw : @bb84_raw_key_val M n l ec_bits vseed_count tag_count paseed_count (Some x) != @bb84_raw_key_val M n l ec_bits vseed_count tag_count paseed_count (Some x').
      { have bb84_raw_key_of_neq : forall (v v' : bb84_val M n l ec_bits vseed_count tag_count paseed_count) (x0 x0' : 'I_(2 ^ n)), bb84_raw_key_of v = Some x0 -> bb84_raw_key_of v' = Some x0' -> x0 != x0' -> v != v'.
        { move=> v v' x0 x0' Hv Hv' Hxx0; apply/eqP=> Hvv'.
          by move: Hv; rewrite Hvv' Hv' => -[] Hxx'; move: Hxx0; rewrite Hxx' eqxx. } apply: (bb84_raw_key_of_neq (@bb84_raw_key_val M n l ec_bits vseed_count tag_count paseed_count (Some x)) (@bb84_raw_key_val M n l ec_bits vseed_count tag_count paseed_count (Some x')) x x').
        all: by rewrite ?Hxx. } rewrite (eq_bigr (fun v => @bb84_unif_vseed_mass R M n l ec_bits vseed_count tag_count paseed_count s v * ((bb84_verify_hash_val vh v (@bb84_raw_key_val M n l ec_bits vseed_count tag_count paseed_count (Some x)) == bb84_verify_hash_val vh v (@bb84_raw_key_val M n l ec_bits vseed_count tag_count paseed_count (Some x')))%:R))).
      * exact: bb84_verify_hash_value_collision_probE.
      * by move=> v _; rewrite Hraw andbT.
  1,2,3: by rewrite bb84_unif_vseed_mass_support_sum; apply: big1 => g _; by [rewrite /bb84_verify_hash_val bb84_vseed_of_val !bb84_raw_key_of_val mulr0 | rewrite eqxx andbF mulr0]. Qed.

Fact bb84_raw_key_option_pair_sum {R : realType} {M n l ec_bits vseed_count tag_count paseed_count : nat} (ox ox' : option 'I_(2 ^ n))
    (F : 'I_(2 ^ n) -> 'I_(2 ^ n) -> R) : \sum_x \sum_(x' | x != x') ((((ox == Some x) && (ox' == Some x'))%:R : R) * F x x') =
  match ox, ox' with | Some x, Some x' => if x == x' then 0 else F x x' | _, _ => 0 end.
Proof.
  case: ox => [x|]; case: ox' => [y|] /=.
  - case Hxy: (x == y).
    + move/eqP: Hxy => ->; apply: big1 => a _; apply: big1 => b Hab.
      have Hzero : ((Some y == Some a) && (Some y == Some b)) = false.
      { apply/negP=> /andP [/eqP Hya /eqP Hyb]; case: Hya => Hya; case: Hyb => Hyb.
        by move: Hab; rewrite -Hya -Hyb eqxx. } by rewrite Hzero mul0r.
    + rewrite (bigD1 x) //=.
      rewrite (bigD1 y) /=; last by rewrite Hxy.
      rewrite !eqxx /= mul1r [X in _ + X]big1 ?addr0.
      * rewrite [X in _ + X]big1 ?addr0 // => a Ha. have Hzero : (Some y == Some a) = false by apply/negP=> /eqP Hya; case: Hya => Hya; move: Ha; rewrite -Hya eqxx andbF. by rewrite Hzero mul0r.
      * move=> b Hb; apply: big1 => c _. have Hzero : (Some x == Some b) = false by apply/negP=> /eqP Hxb; case: Hxb => Hxb; move: Hb; rewrite -Hxb eqxx. by rewrite Hzero mul0r.
  1,2,3: by apply: big1 => a _; apply: big1 => b _; by [rewrite andbF mul0r | rewrite mul0r]. Qed.

Fact bb84_verify_hash_normalized_raw_key_mismatch_guard_sumE {R : realType} {M n l ec_bits vseed_count tag_count paseed_count : nat}
    (s : @store (bb84_cvar M) (bb84_val M n l ec_bits vseed_count tag_count paseed_count))
    (vh : 'I_vseed_count -> 'I_(2 ^ n) -> 'I_tag_count) (ok : bool) (raw raw' : bb84_val M n l ec_bits vseed_count tag_count paseed_count) :
  raw = bb84_raw_key_val (bb84_raw_key_of raw) -> raw' = bb84_raw_key_val (bb84_raw_key_of raw') -> \sum_v
    @bb84_unif_vseed_mass R M n l ec_bits vseed_count tag_count paseed_count s v * ((ok && (bb84_verify_hash_val vh v raw ==
       bb84_verify_hash_val vh v raw') && (raw != raw'))%:R) = \sum_x \sum_(x' | x != x') ((((ok && (bb84_raw_key_of raw == Some x) &&
       (bb84_raw_key_of raw' == Some x')))%:R : R) * ((#|[set g : 'I_vseed_count | vh g x == vh g x']|%:R : R) * (vseed_count%:R)^-1)).
Proof.
  move=> Hraw Hraw'.
  have bb84_verify_hash_normalized_raw_key_mismatch_sumE : raw = bb84_raw_key_val (bb84_raw_key_of raw) -> raw' = bb84_raw_key_val (bb84_raw_key_of raw') -> \sum_v @bb84_unif_vseed_mass R M n l ec_bits vseed_count tag_count paseed_count s v * (((bb84_verify_hash_val vh v raw == bb84_verify_hash_val vh v raw') && (raw != raw'))%:R) = \sum_x \sum_(x' | x != x') ((((bb84_raw_key_of raw == Some x) && (bb84_raw_key_of raw' == Some x'))%:R : R) * ((#|[set g : 'I_vseed_count | vh g x == vh g x']|%:R : R) * (vseed_count%:R)^-1)).
  { have bb84_verify_hash_raw_key_mismatch_sumE : forall (ox ox' : option 'I_(2 ^ n)), \sum_v @bb84_unif_vseed_mass R M n l ec_bits vseed_count tag_count paseed_count s v * (((bb84_verify_hash_val vh v (@bb84_raw_key_val M n l ec_bits vseed_count tag_count paseed_count ox) == bb84_verify_hash_val vh v (@bb84_raw_key_val M n l ec_bits vseed_count tag_count paseed_count ox')) && (@bb84_raw_key_val M n l ec_bits vseed_count tag_count paseed_count ox != @bb84_raw_key_val M n l ec_bits vseed_count tag_count paseed_count ox'))%:R) = \sum_x \sum_(x' | x != x') ((((ox == Some x) && (ox' == Some x'))%:R : R) * ((#|[set g : 'I_vseed_count | vh g x == vh g x']|%:R : R) * (vseed_count%:R)^-1)).
    { by move=> ox ox'; rewrite bb84_verify_hash_raw_key_mismatch_probE bb84_raw_key_option_pair_sum. } by move=> -> ->; rewrite !bb84_raw_key_of_val; exact: bb84_verify_hash_raw_key_mismatch_sumE. } case: ok; first exact: bb84_verify_hash_normalized_raw_key_mismatch_sumE.
  rewrite /= big1; last by move=> v _; rewrite mulr0.
  by apply: esym; apply: big1 => x _; apply: big1 => x' _; rewrite mul0r. Qed.

Fact bb84_verify_hash_normalized_raw_key_mismatch_guard_seed_sumE {R : realType} {M n l ec_bits vseed_count tag_count paseed_count : nat}
    (s : @store (bb84_cvar M) (bb84_val M n l ec_bits vseed_count tag_count paseed_count))
    (vh : 'I_vseed_count -> 'I_(2 ^ n) -> 'I_tag_count) (ok : bool) (raw raw' : bb84_val M n l ec_bits vseed_count tag_count paseed_count) :
  (0 < vseed_count)%N -> raw = bb84_raw_key_val (bb84_raw_key_of raw) -> raw' = bb84_raw_key_val (bb84_raw_key_of raw') -> \sum_v
    @bb84_unif_vseed_mass R M n l ec_bits vseed_count tag_count paseed_count s v * ((ok && (bb84_verify_hash_val vh v raw ==
       bb84_verify_hash_val vh v raw') && (raw != raw'))%:R) = \sum_x \sum_(x' | x != x') ((\sum_v
        @bb84_unif_vseed_mass R M n l ec_bits vseed_count tag_count paseed_count s v * ((ok && (bb84_raw_key_of raw == Some x) &&
          (bb84_raw_key_of raw' == Some x'))%:R)) * ((#|[set g : 'I_vseed_count | vh g x == vh g x']|%:R : R) * (vseed_count%:R)^-1)).
Proof. move=> Hvseed_pos Hraw Hraw'; rewrite (bb84_verify_hash_normalized_raw_key_mismatch_guard_sumE s vh ok Hraw Hraw'). apply: eq_bigr => x _; apply: eq_bigr => x' _; congr (_ * _). by rewrite -mulr_suml (bb84_unif_vseed_mass_sum1 s Hvseed_pos) mul1r. Qed.

Fact bb84_verify_hash_errcorr_mismatch_guard_seed_sumE {R : realType} {M n l ec_bits vseed_count tag_count paseed_count : nat} (s : @store
    (bb84_cvar M) (bb84_val M n l ec_bits vseed_count tag_count paseed_count)) (vh : 'I_vseed_count -> 'I_(2 ^ n) -> 'I_tag_count) (ir_pub :
    'I_(2 ^ n) -> 'I_(2 ^ n) -> 'I_(2 ^ ec_bits)) (ir_dec : 'I_(2 ^ ec_bits) -> 'I_(2 ^ n) -> 'I_(2 ^ n)) (leakEC : nat) (ok : bool) (raw
    bob : bb84_val M n l ec_bits vseed_count tag_count paseed_count) : (0 < vseed_count)%N -> raw = bb84_raw_key_val (bb84_raw_key_of raw)
    -> let raw' := bb84_ir_dec_val ir_dec (bb84_ir_pub_val ir_pub leakEC raw bob) bob in \sum_v @bb84_unif_vseed_mass R M n l ec_bits
    vseed_count tag_count paseed_count s v * ((ok && (bb84_verify_hash_val vh v raw == bb84_verify_hash_val vh v raw') && (raw != raw'))%:R)
    = \sum_x \sum_(x' | x != x') ((\sum_v @bb84_unif_vseed_mass R M n l ec_bits vseed_count tag_count paseed_count s v * ((ok &&
    (bb84_raw_key_of raw == Some x) && (bb84_raw_key_of raw' == Some x'))%:R)) * ((#|[set g : 'I_vseed_count | vh g x == vh g x']|%:R : R) *
    (vseed_count%:R)^-1)).
Proof.
  move=> Hvseed_pos Hraw raw'.
  have bb84_ir_dec_val_raw_key : forall (transcript bob0 : bb84_val M n l ec_bits vseed_count tag_count paseed_count), bb84_ir_dec_val ir_dec transcript bob0 = bb84_raw_key_val (bb84_raw_key_of (bb84_ir_dec_val ir_dec transcript bob0)).
  { by move=> transcript bob0; rewrite /bb84_ir_dec_val; case: (bb84_ec_of transcript); case: (bb84_raw_key_of bob0). } exact: (bb84_verify_hash_normalized_raw_key_mismatch_guard_seed_sumE s vh ok Hvseed_pos Hraw (bb84_ir_dec_val_raw_key (bb84_ir_pub_val ir_pub leakEC raw bob) bob)). Qed.

Definition bb84_label (M : nat) (LE LB : finType) := ('I_M + ('I_M + (LE + LB)))%type.

Definition bb84_signal_label {M : nat} {LE LB : finType} (i : 'I_M) : bb84_label M LE LB := inl i.

Definition bb84_source_label {M : nat} {LE LB : finType} (i : 'I_M) : bb84_label M LE LB := inr (inl i).

Definition bb84_bridge_label {M : nat} {LE LB : finType} (b : LB) : bb84_label M LE LB := inr (inr (inr b)).

Definition bb84_signal_reg {M : nat} {LE LB : finType} (i : 'I_M) : {set bb84_label M LE LB} := [set bb84_signal_label i].

Definition bb84_signal_regs {M : nat} {LE LB : finType} : 'I_M -> {set bb84_label M LE LB} := bb84_signal_reg.

Definition bb84_source_reg {M : nat} {LE LB : finType} (i : 'I_M) : {set bb84_label M LE LB} := [set bb84_source_label i].

Definition bb84_eve_reg (M : nat) (LE LB : finType) : {set bb84_label M LE LB} := [set x | if x is inr (inr (inl _)) then true else false].

Definition bb84_bridge_reg {M : nat} {LE LB : finType} (b : LB) : {set bb84_label M LE LB} := [set bb84_bridge_label b].

Section BB84LabelSpace.
Variable R : realType.
Notation C := (@hermitian.C R).
Notation chsType := (@chsType R).
Variable M : nat.
Variables LE LB : finType.
Variables (HE : LE -> chsType) (HB : LB -> chsType).

Definition bb84_label_space (x : bb84_label M LE LB) : chsType := match x with | inl _ => @ihb_chsType R 'I_2
  | inr (inl _) => @ihb_chsType R 'I_4 | inr (inr (inl e)) => HE e | inr (inr (inr b)) => HB b end.

Lemma bb84_signal_reg_dim (i : 'I_M) : dim 'H[bb84_label_space]_(bb84_signal_reg i) = 2%N.
Proof. by rewrite /bb84_signal_reg dim_setten big_set1 /bb84_label_space -(@ihb_dim_cast R 'I_2) card_ord. Qed.

Definition bb84_signal_lfun (i : 'I_M) (rho : 'M[C]_2) : 'F[bb84_label_space]_(bb84_signal_reg i) := mx2h (castmx
    (esym (bb84_signal_reg_dim i), esym (bb84_signal_reg_dim i)) rho).

Lemma bb84_source_reg_dim (i : 'I_M) : dim 'H[bb84_label_space]_(@bb84_source_reg M LE LB i) = 4%N.
Proof. by rewrite /bb84_source_reg dim_setten big_set1 /bb84_label_space -(@ihb_dim_cast R 'I_4) card_ord. Qed.

Definition bb84_source_lfun (i : 'I_M) (rho : 'M[C]_4) : 'F[bb84_label_space]_(@bb84_source_reg M LE LB i) := mx2h (castmx
    (esym (bb84_source_reg_dim i), esym (bb84_source_reg_dim i)) rho).

Lemma bb84_source_signal_disjoint (i : 'I_M) : [disjoint @bb84_source_reg M LE LB i & @bb84_signal_reg M LE LB i].
Proof. by rewrite /bb84_source_reg /bb84_signal_reg disjoint1X !inE. Qed.

Definition bb84_source_signal_lfun (i : 'I_M) (rho : 'M[C]_(4 * 2)) : 'F[bb84_label_space]_(@bb84_source_reg M LE LB i :|:
      @bb84_signal_reg M LE LB i) := let dim_source_signal := f_equal2 muln (bb84_source_reg_dim i) (bb84_signal_reg_dim i) in
  biprod_of_mx (bb84_source_signal_disjoint i) (castmx (esym dim_source_signal, esym dim_source_signal) rho).

End BB84LabelSpace.

Section BB84Program.
Variable R : realType.
Notation chsType := (@chsType R).
Variables (L : finType) (HL : L -> chsType).
Variables Cv V : finType.

Notation store := (@store Cv V).
Notation dexpr := (@dexpr R Cv V).

Variables n k l leakEC M : nat.
Variables Qtol eps_c : R.
Variables (a_ y_ b_ y'_ d_ : 'I_M -> Cv).
Variable Q : 'I_M -> {set L}.
Variables Xv Zv Kv XA XB ZA ZB lamv pECv Xhatv : Cv.
Variables gv tAv tBv fv Sv Shv abortv Pvar : Cv.

Variables basisX basisZ outEmpty bot empty_transcript : V.
Variables (vbool : bool -> V) (vbit : bool -> V) (vset : {set 'I_M} -> V) (vset_of : V -> {set 'I_M}) (vrat : nat -> nat -> V).

Variables (dev_rho : forall i : 'I_M, V -> V -> 'F[HL]_(Q i)) (dev_meas : forall i : 'I_M, V -> V -> 'F[HL]_(Q i)).

Variables (tr_app_rounds : ('I_M -> V * V * V) -> V -> V) (tr_app_pe : V -> V -> V -> V -> V) (tr_app_ec : V -> V -> V -> V -> V).
Variables (tr_app_pa : V -> V -> V).

Variables (key_bits_on : {set 'I_M} -> ('I_M -> V) -> V) (test_bits_on : {set 'I_M} -> ('I_M -> V) -> V) (err_count : V -> V -> nat).
Variables (err_of : V -> nat) (unif_nsubset_mass : nat -> {set 'I_M} -> V -> R).

Variables (ir_pub : nat -> V -> V -> V) (ir_dec : V -> V -> V) (unif_vseed : dexpr) (verify_hash : V -> V -> V).

Variables (unif_pseed : dexpr) (privacy_hash : nat -> V -> V -> V).

Definition bb84_program_scheme : @qkd_cmd R L HL Cv V := (Pvar <-c (fun _ : store => empty_transcript)) ;; (Xv <-c (fun _ : store => vset
    set0)) ;; (Zv <-c (fun _ : store => vset set0)) ;; (abortv <-c (fun _ : store => vbool false)) ;; (FOR i < M, @Round R L HL Cv V n k M
    a_ y_ b_ y'_ d_ Q Xv Zv basisX basisZ outEmpty vbool vbit vset dev_rho dev_meas i) ;; @Announce R L HL Cv V M a_ b_ d_ Pvar
    tr_app_rounds ;; @ParamEst R L HL Cv V n M y_ y'_ Xv Zv Kv XA XB ZA ZB lamv Pvar bot vset_of vrat tr_app_pe key_bits_on test_bits_on
    err_count unif_nsubset_mass ;; IF @pe_fail R Cv V n k M Qtol Xv Zv lamv vset_of err_of THEN @Abort_cmd R L HL Cv V Sv Shv abortv bot
    vbool ELSE (@ErrCorr R L HL Cv V leakEC XA XB pECv Xhatv gv tAv tBv Pvar tr_app_ec ir_pub ir_dec unif_vseed verify_hash ;; IF (fun s :
    store => s tAv != s tBv) THEN @Abort_cmd R L HL Cv V Sv Shv abortv bot vbool ELSE @PrivAmp R L HL Cv V l XA Xhatv fv Sv Shv Pvar
    tr_app_pa unif_pseed privacy_hash).

Definition bb84_eval_scheme (qA : {set L}) (EA : @adversary R L HL V qA) (xi : @cq_state R L HL Cv V) : @cq_state R L HL Cv V :=
  @denote R L HL Cv V qA Pvar EA bb84_program_scheme xi.

Fact bb84_program_scheme_wf (qA : {set L}) : (forall i, cmd_wf qA (@Round R L HL Cv V n k M a_ y_ b_ y'_ d_ Q Xv Zv
      basisX basisZ outEmpty vbool vbit vset dev_rho dev_meas i)) -> cmd_wf qA (@ParamEst R L HL Cv V n M y_ y'_ Xv Zv Kv XA XB ZA ZB lamv
      Pvar bot vset_of vrat tr_app_pe key_bits_on test_bits_on err_count unif_nsubset_mass) -> cmd_wf qA
    (@ErrCorr R L HL Cv V leakEC XA XB pECv Xhatv gv tAv tBv Pvar tr_app_ec ir_pub ir_dec unif_vseed verify_hash) -> cmd_wf qA
    (@PrivAmp R L HL Cv V l XA Xhatv fv Sv Shv Pvar tr_app_pa unif_pseed privacy_hash) -> cmd_wf qA bb84_program_scheme.
Proof.
  move=> Hround Hpe Hec Hpa; rewrite /bb84_program_scheme.
  do 4 (apply: cmd_wf_seq_cmd; first by []).
  apply: cmd_wf_seq_cmd; [by apply: cmd_wf_for_cmd | apply: cmd_wf_seq_cmd; first by []].
  apply: cmd_wf_seq_cmd; [exact: Hpe | split; first by []].
  by apply: cmd_wf_seq_cmd; [exact: Hec | split; [by [] | exact: Hpa]]. Qed.

End BB84Program.

Section ConcreteBB84Program.
Variable R : realType.
Notation C := (@hermitian.C R).
Notation chsType := (@chsType R).
Variables (P : @bb84_protocol R) (q : R) (LE : finType) (HE : LE -> chsType) (LB : finType) (HB : LB -> chsType) (dev :
  bb84_certified_device P q).

Notation M := (bb84_round_limit P).
Notation L := (bb84_label M LE LB).
Notation HL := (bb84_label_space HE HB).
Notation Cv := (bb84_cvar M).
Notation V := (bb84_val M (bb84_n P) (bb84_l P) (cd_ir_bits dev) (cd_vseed_count dev) (cd_tag_count dev) (cd_paseed_count dev)).
Notation store := (@store Cv V).

Local Notation vidx f := (f M (bb84_n P) (bb84_l P) (cd_ir_bits dev) (cd_vseed_count dev) (cd_tag_count dev) (cd_paseed_count dev)).
Local Notation vidxR f := (f R M (bb84_n P) (bb84_l P) (cd_ir_bits dev) (cd_vseed_count dev) (cd_tag_count dev) (cd_paseed_count dev)).

Definition bb84_program_basis_value (basis : bb84_basis) : V := match basis with | BasisX => bb84_basis_bool_val false
  | BasisZ => bb84_basis_bool_val true end.

Definition bb84_program_basis_of_value (v : V) : option bb84_basis := match bb84_basis_bool_of v with | Some false => Some BasisX
  | Some true => Some BasisZ | None => None end.

Definition bb84_program_device_rho (i : 'I_M) (basis bit : V) : 'F[HL]_(bb84_signal_reg i) :=
  match bb84_program_basis_of_value basis, bb84_bit_of bit with | Some BasisX, Some b => bb84_signal_lfun HE HB i (cd_rho dev BasisX b)
  | Some BasisZ, Some b => bb84_signal_lfun HE HB i (cd_rho dev BasisZ b) | _, _ => bb84_signal_lfun HE HB i (cd_rho dev BasisX false) end.

Definition bb84_program_device_meas (i : 'I_M) (basis outcome : V) : 'F[HL]_(bb84_signal_reg i) := match bb84_program_basis_of_value basis,
    bb84_outcome_of outcome with | Some BasisX, Some o => bb84_signal_lfun HE HB i (cd_meas dev BasisX o) | Some BasisZ, Some o =>
    bb84_signal_lfun HE HB i (cd_meas dev BasisZ o) | None, Some o => bb84_signal_lfun HE HB i (cd_meas dev BasisX o) | _, None => 0 end.

Definition bb84_program : @qkd_cmd R L HL Cv V := (BVP <-c (fun _ : store => bb84_empty_transcript_val)) ;; (BVX <-c (fun _ : store =>
    bb84_set_val set0)) ;; (BVZ <-c (fun _ : store => bb84_set_val set0)) ;; (BVabort <-c (fun _ : store => bb84_bool_val false)) ;; (FOR i
    < M, @Round R L HL Cv V (bb84_n P) (bb84_k P) M (@BVa M) (@BVy M) (@BVb M) (@BVy' M) (@BVd M) (@bb84_signal_regs M LE LB) (@BVX M) (@BVZ
    M) (bb84_program_basis_value BasisX) (bb84_program_basis_value BasisZ) (bb84_outcome_val None) (vidx (@bb84_bool_val)) (vidx
    (@bb84_bit_val)) (vidx (@bb84_set_val)) bb84_program_device_rho bb84_program_device_meas i) ;; @Announce R L HL Cv V M (@BVa M) (@BVb M)
    (@BVd M) (@BVP M) (vidx (@bb84_tr_app_rounds)) ;; @ParamEst R L HL Cv V (bb84_n P) M (@BVy M) (@BVy' M) (@BVX M) (@BVZ M) (@BVK M)
    (@BVXA M) (@BVXB M) (@BVZA M) (@BVZB M) (@BVlam M) (@BVP M) (vidx (@bb84_bot_val)) (vidx (@bb84_set_of)) (vidx (@bb84_error_val)) (vidx
    (@bb84_tr_app_pe)) (vidx (@bb84_bits_on_val)) (vidx (@bb84_partial_bits_on_val)) (vidx (@bb84_err_count_val)) (vidxR
    (@bb84_unif_nsubset_mass)) ;; IF @pe_fail R Cv V (bb84_n P) (bb84_k P) M (bb84_Qtol P) (@BVX M) (@BVZ M) (@BVlam M) (vidx
    (@bb84_set_of)) (vidx (@bb84_error_of)) THEN @Abort_cmd R L HL Cv V (@BVS M) (@BVSh M) (@BVabort M) (vidx (@bb84_bot_val)) (vidx
    (@bb84_bool_val)) ELSE (@ErrCorr R L HL Cv V (cd_ir_bits dev) (@BVXA M) (@BVXB M) (@BVpec M) (@BVXhat M) (@BVg M) (@BVtA M) (@BVtB M)
    (@BVP M) (vidx (@bb84_tr_app_ec)) ((vidx (@bb84_ir_pub_val)) (@cd_ir_pub R P q dev)) ((vidx (@bb84_ir_dec_val)) (@cd_ir_dec R P q dev))
    (vidxR (@bb84_unif_vseed_mass)) ((vidx (@bb84_verify_hash_val)) (@cd_vh R P q dev)) ;; IF (fun s : store => s (@BVtA M) != s (@BVtB M))
    THEN @Abort_cmd R L HL Cv V (@BVS M) (@BVSh M) (@BVabort M) (vidx (@bb84_bot_val)) (vidx (@bb84_bool_val)) ELSE @PrivAmp R L HL Cv V
    (bb84_l P) (@BVXA M) (@BVXhat M) (@BVf M) (@BVS M) (@BVSh M) (@BVP M) (vidx (@bb84_tr_app_pa)) (vidxR (@bb84_unif_pseed_mass)) ((vidx
    (@bb84_privacy_hash_val)) (@cd_pa R P q dev))).

Definition bb84_eval (qA : {set L}) (EA : @adversary R L HL V qA) (xi : @cq_state R L HL Cv V) : @cq_state R L HL Cv V :=
  @denote R L HL Cv V qA (@BVP M) EA bb84_program xi.

End ConcreteBB84Program.
