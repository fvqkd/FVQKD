(* model.v — BB84 protocol infrastructure types                         *)
(* Module: qkd.bb84.model                                               *)
(* Paper: Tomamichel-Lim-Gisin-Renner, Nat. Commun. 3:634 (2012),       *)
(*   "Tight finite-key analysis for quantum cryptography" (Suppl. Note 1). *)
(* Infrastructure records and definitions consumed by bb84.v and the    *)
(* example-layer theorem files.                                         *)

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
From Stdlib Require Import Psatz.
From quantum Require Import mcextra mcaextra notation hermitian quantum
  cpo mxpred extnum ctopology svd mxnorm hspace hspace_extra qtype.
From quantum.dirac Require Import hstensor setdec.

Import Order.TTheory GRing.Theory Num.Theory Num.Def MxLownerOrder.
Import VectorInternalTheory.

From utils Require Import exports.
From entropy Require Import def prop.
From entropy.smooth Require Import class prop dpi.
From eur Require Import def prop eur.
From lhl Require Import def util post_hash prop lhl.
From qkd.bb84 Require Import def.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Open Scope ring_scope.
Local Open Scope lfun_scope.

Section FvqkdReal.
Variable R : realType.
Notation C := (@hermitian.C R).
Notation chsType := (@chsType R).
Notation bb84_protocol := (@bb84_protocol R).

Inductive bb84_basis := BasisX | BasisZ.
Inductive bb84_outcome := Out0 | Out1 | OutEmpty.

Record bb84_round := BB84Round { bb84_round_alice_basis : bb84_basis; bb84_round_alice_bit   : bool; bb84_round_bob_basis   : bb84_basis; bb84_round_bob_outcome : bb84_outcome; }.

Definition bb84_basis_eq (a b : bb84_basis) : bool :=
  match a, b with BasisX, BasisX | BasisZ, BasisZ => true | _, _ => false end.

Definition bb84_detected (o : bb84_outcome) : bool :=
  match o with OutEmpty => false | _ => true end.

Definition bb84_outcome_bit (o : bb84_outcome) : bool :=
  match o with Out0 => false | Out1 => true | OutEmpty => false end.

Section SiftingSets.
Variable (M : nat) (rounds : 'I_M -> bb84_round).

Definition bb84_key_round (i : 'I_M) : bool :=
  bb84_basis_eq (bb84_round_alice_basis (rounds i)) BasisX &&
  bb84_basis_eq (bb84_round_bob_basis (rounds i)) BasisX &&
  bb84_detected (bb84_round_bob_outcome (rounds i)).

Definition bb84_test_round (i : 'I_M) : bool :=
  bb84_basis_eq (bb84_round_alice_basis (rounds i)) BasisZ &&
  bb84_basis_eq (bb84_round_bob_basis (rounds i)) BasisZ &&
  bb84_detected (bb84_round_bob_outcome (rounds i)).

Definition bb84_set_X : {set 'I_M} := [set i | bb84_key_round i].
Definition bb84_set_Z : {set 'I_M} := [set i | bb84_test_round i].

Definition bb84_sift_complete (P : bb84_protocol) : bool :=
  (bb84_n P <= #|bb84_set_X|)%N && (bb84_k P <= #|bb84_set_Z|)%N.

End SiftingSets.

Section ErrorRate.
Variable (M : nat) (rounds : 'I_M -> bb84_round).

Definition bb84_error_count : nat :=
  let Z := bb84_set_Z rounds in
  #|[set i in Z |
      bb84_round_alice_bit (rounds i) !=
      bb84_outcome_bit (bb84_round_bob_outcome (rounds i))]|.

Definition bb84_error_rate : R :=
  let Z := bb84_set_Z rounds in
  if (0 < #|Z|)%N then
    (bb84_error_count%:R : R) / (#|Z|%:R : R)
  else 0.

End ErrorRate.

Record bb84_sample (P : bb84_protocol) := BB84Sample { bb84_sample_alice : bitstr (bb84_k P + bb84_n P); bb84_sample_bob   : bitstr (bb84_k P + bb84_n P); }.

Definition bb84_pass_event (P : bb84_protocol) (s : bb84_sample P)
    : {set 'S_(bb84_k P + bb84_n P)} :=
  @perm_pair_sample_le_event R (bb84_n P) (bb84_k P)
    (bb84_sample_alice s) (bb84_sample_bob s) (bb84_Qtol P).

Definition bb84_p_pass (P : bb84_protocol) (s : bb84_sample P) : R :=
  @perm_pair_sample_le_prob R (bb84_n P) (bb84_k P)
    (bb84_sample_alice s) (bb84_sample_bob s) (bb84_Qtol P).

Definition bb84_total_rounds (P : bb84_protocol) : nat :=
  bb84_k P + bb84_n P.

Definition bb84_full_string_count (P : bb84_protocol) : nat :=
  2 ^ bb84_total_rounds P.

Record bb84_zsource (P : bb84_protocol) := BB84ZSource { bb84_zsrc_nb : nat; bb84_zsrc_rho : 'M[C]_(bb84_full_string_count P * bb84_zsrc_nb * bb84_full_string_count P); bb84_zsrc_den1 : bb84_zsrc_rho \is den1mx; }.

Definition bb84_W (P : bb84_protocol) (G : bb84_zsource P)
    (z z' : 'I_(bb84_full_string_count P)) : R :=
  let Pzz :=
    (delta_mx z z : 'M[C]_(bb84_full_string_count P)) *t
    (1%:M : 'M[C]_(bb84_zsrc_nb G)) *t
    (delta_mx z' z' : 'M[C]_(bb84_full_string_count P)) in
  @complex.Re R (\tr (Pzz *m bb84_zsrc_rho G)).

Fact bb84_W_traceE (P : bb84_protocol) (G : bb84_zsource P)
    (z z' : 'I_(bb84_full_string_count P)) :
  \tr ((((delta_mx z z : 'M[C]_(bb84_full_string_count P)) *t
        (1%:M : 'M[C]_(bb84_zsrc_nb G))) *t
        (delta_mx z' z' : 'M[C]_(bb84_full_string_count P))) *m
      bb84_zsrc_rho G) =
  (bb84_W G z z')%:C.
Proof.
  rewrite /bb84_W.
  set Pzz : 'M[C]_(bb84_full_string_count P * bb84_zsrc_nb G * bb84_full_string_count P) := ((delta_mx z z : 'M[C]_(bb84_full_string_count P)) *t (1%:M : 'M[C]_(bb84_zsrc_nb G))) *t (delta_mx z' z' : 'M[C]_(bb84_full_string_count P)).
  have /den1mxP [Hrho_psd _] := bb84_zsrc_den1 G.
  have HP_adj : Pzz^*t = Pzz by rewrite /Pzz !adjmx_tens !adjmx_delta adjmx1.
  have HP_id : Pzz *m Pzz = Pzz by rewrite /Pzz !tensmx_mul !mul_delta_mx !mul1mx.
  have HtrE : \tr (Pzz *m bb84_zsrc_rho G) = \tr (Pzz *m bb84_zsrc_rho G *m Pzz) by rewrite [RHS]mxtrace_mulC mulmxA HP_id.
  have Hsand_psd : Pzz *m bb84_zsrc_rho G *m Pzz \is psdmx.
  { have -> : Pzz *m bb84_zsrc_rho G *m Pzz = Pzz *m bb84_zsrc_rho G *m Pzz^*t by rewrite HP_adj. exact: form_psdmx. } by rewrite HtrE RRe_real // ger0_real // psdmx_trace. Qed.
Lemma bb84_W_ge0 (P : bb84_protocol) (G : bb84_zsource P)
    (z z' : 'I_(bb84_full_string_count P)) :
  0 <= bb84_W G z z'.
Proof.
  rewrite /bb84_W.
  set Pzz : 'M[C]_(bb84_full_string_count P * bb84_zsrc_nb G * bb84_full_string_count P) := ((delta_mx z z : 'M[C]_(bb84_full_string_count P)) *t (1%:M : 'M[C]_(bb84_zsrc_nb G))) *t (delta_mx z' z' : 'M[C]_(bb84_full_string_count P)).
  have /den1mxP [Hrho_psd _] := bb84_zsrc_den1 G.
  have HP_adj : Pzz^*t = Pzz by rewrite /Pzz !adjmx_tens !adjmx_delta adjmx1.
  have HP_id : Pzz *m Pzz = Pzz by rewrite /Pzz !tensmx_mul !mul_delta_mx !mul1mx.
  have HtrE : \tr (Pzz *m bb84_zsrc_rho G) = \tr (Pzz *m bb84_zsrc_rho G *m Pzz) by rewrite [RHS]mxtrace_mulC mulmxA HP_id.
  have Hsand_psd : Pzz *m bb84_zsrc_rho G *m Pzz \is psdmx.
  { have -> : Pzz *m bb84_zsrc_rho G *m Pzz = Pzz *m bb84_zsrc_rho G *m Pzz^*t by rewrite HP_adj. exact: form_psdmx. } rewrite HtrE.
  set t := @complex.Re R (\tr (Pzz *m bb84_zsrc_rho G *m Pzz)).
  have Htr_real : \tr (Pzz *m bb84_zsrc_rho G *m Pzz) = t%:C by rewrite /t RRe_real // ger0_real // psdmx_trace.
  by have := psdmx_trace Hsand_psd; rewrite Htr_real lecR. Qed.
Lemma bb84_W_sum1 (P : bb84_protocol) (G : bb84_zsource P) :
  \sum_z \sum_z' bb84_W G z z' = 1.
Proof.
have bb84_zsource_projector_sum : forall (P : bb84_protocol) (G : bb84_zsource P), \sum_(z : 'I_(bb84_full_string_count P)) \sum_(z' : 'I_(bb84_full_string_count P)) (((delta_mx z z : 'M[C]_(bb84_full_string_count P)) *t (1%:M : 'M[C]_(bb84_zsrc_nb G))) *t (delta_mx z' z' : 'M[C]_(bb84_full_string_count P))) = 1%:M.
{ clear G P; move=> P G. have Hinner (z : 'I_(bb84_full_string_count P)) : \sum_(zp : 'I_(bb84_full_string_count P)) (((delta_mx z z : 'M[C]_(bb84_full_string_count P)) *t (1%:M : 'M[C]_(bb84_zsrc_nb G))) *t (delta_mx zp zp : 'M[C]_(bb84_full_string_count P))) = (((delta_mx z z : 'M[C]_(bb84_full_string_count P)) *t (1%:M : 'M[C]_(bb84_zsrc_nb G))) *t (1%:M : 'M[C]_(bb84_full_string_count P))).
  { by rewrite [X in _ = _ *t X]mx1_sum_delta tensmx_sumr. } rewrite (eq_bigr _ (fun z _ => Hinner z)) -tensmx_suml.
  have Hleft_sum : \sum_(z : 'I_(bb84_full_string_count P)) ((delta_mx z z : 'M[C]_(bb84_full_string_count P)) *t (1%:M : 'M[C]_(bb84_zsrc_nb G))) = (1%:M : 'M[C]_(bb84_full_string_count P * bb84_zsrc_nb G)).
  { rewrite -[RHS](@tensmx11 C (bb84_full_string_count P) (bb84_zsrc_nb G)).
    by rewrite [X in _ = X *t _]mx1_sum_delta tensmx_suml. } by rewrite Hleft_sum tensmx11. } rewrite /bb84_W.
  have HRe_sum : \sum_(z : 'I_(bb84_full_string_count P)) \sum_(z' : 'I_(bb84_full_string_count P)) @complex.Re R (\tr ((((delta_mx z z : 'M[C]_(bb84_full_string_count P)) *t (1%:M : 'M[C]_(bb84_zsrc_nb G))) *t (delta_mx z' z' : 'M[C]_(bb84_full_string_count P))) *m bb84_zsrc_rho G)) = @complex.Re R (\sum_(z : 'I_(bb84_full_string_count P)) \sum_(z' : 'I_(bb84_full_string_count P)) \tr ((((delta_mx z z : 'M[C]_(bb84_full_string_count P)) *t (1%:M : 'M[C]_(bb84_zsrc_nb G))) *t (delta_mx z' z' : 'M[C]_(bb84_full_string_count P))) *m bb84_zsrc_rho G)).
  { by rewrite raddf_sum /=; apply: eq_bigr => z _; rewrite raddf_sum. } rewrite HRe_sum.
  have Htr_sum : \sum_(z : 'I_(bb84_full_string_count P)) \sum_(z' : 'I_(bb84_full_string_count P)) \tr ((((delta_mx z z : 'M[C]_(bb84_full_string_count P)) *t (1%:M : 'M[C]_(bb84_zsrc_nb G))) *t (delta_mx z' z' : 'M[C]_(bb84_full_string_count P))) *m bb84_zsrc_rho G) = \tr ((\sum_(z : 'I_(bb84_full_string_count P)) \sum_(z' : 'I_(bb84_full_string_count P)) (((delta_mx z z : 'M[C]_(bb84_full_string_count P)) *t (1%:M : 'M[C]_(bb84_zsrc_nb G))) *t (delta_mx z' z' : 'M[C]_(bb84_full_string_count P)))) *m bb84_zsrc_rho G).
  { by rewrite mulmx_suml linear_sum /=; apply: eq_bigr => z _; rewrite mulmx_suml linear_sum. } rewrite Htr_sum bb84_zsource_projector_sum mul1mx.
  by have /den1mxP [_ /eqP Hrho_tr] := bb84_zsrc_den1 G; rewrite Hrho_tr /=. Qed.
Definition bb84_p_pass_pair (P : bb84_protocol)
    (z z' : 'I_(bb84_full_string_count P)) : R :=
  @perm_pair_sample_le_prob R (bb84_n P) (bb84_k P)
    (ord_to_bitstring z) (ord_to_bitstring z') (bb84_Qtol P).

Fact bb84_p_pass_pair_ge0 (P : bb84_protocol)
    (z z' : 'I_(bb84_full_string_count P)) :
  0 <= bb84_p_pass_pair z z'.
Proof. by rewrite /bb84_p_pass_pair /perm_pair_sample_le_prob /Pr_event; apply: sumr_ge0 => pi _; exact: uniform_perm_mu_nonneg. Qed.

Definition bb84_p_pass_tot (P : bb84_protocol) (G : bb84_zsource P) : R :=
  \sum_z \sum_z' bb84_W G z z' * @bb84_p_pass_pair P z z'.

Definition bb84_bad_weight (P : bb84_protocol) (G : bb84_zsource P)
    (eps : R) : R :=
  \sum_(z : 'I_(bb84_full_string_count P))
    \sum_(z' : 'I_(bb84_full_string_count P))
      bb84_W G z z' *
        Pr_event (fun pi : 'S_(bb84_total_rounds P) =>
            @uniform_perm_mu R (bb84_total_rounds P) pi)
          (@perm_pair_deviation_event R (bb84_n P) (bb84_k P)
            (ord_to_bitstring z) (ord_to_bitstring z')
            (bb84_mu (bb84_n P) (bb84_k P) eps)).

Definition bb84_pass_bad_weight (P : bb84_protocol) (G : bb84_zsource P)
    (eps : R) : R :=
  \sum_(z : 'I_(bb84_full_string_count P))
    \sum_(z' : 'I_(bb84_full_string_count P))
      bb84_W G z z' *
        Pr_event (fun pi : 'S_(bb84_total_rounds P) =>
            @uniform_perm_mu R (bb84_total_rounds P) pi)
          ((@perm_pair_sample_le_event R (bb84_n P) (bb84_k P)
              (ord_to_bitstring z) (ord_to_bitstring z') (bb84_Qtol P)) :&:
           (@perm_pair_deviation_event R (bb84_n P) (bb84_k P)
              (ord_to_bitstring z) (ord_to_bitstring z')
              (bb84_mu (bb84_n P) (bb84_k P) eps))).

Fact bb84_bad_weight_le (P : bb84_protocol) (G : bb84_zsource P)
    (eps : R) :
  (0 < bb84_n P)%N -> (0 < bb84_k P)%N -> 0 < eps -> bb84_bad_weight G eps <= eps ^+ 2.
Proof.
  move=> Hn_pos Hk_pos Heps_pos; rewrite /bb84_bad_weight.
  have Heps_sum : \sum_(z : 'I_(bb84_full_string_count P)) \sum_(z' : 'I_(bb84_full_string_count P)) bb84_W G z z' * eps ^+ 2 = eps ^+ 2.
  { under eq_bigr do rewrite -mulr_suml. by rewrite -mulr_suml bb84_W_sum1 mul1r. } rewrite -Heps_sum; apply: ler_sum => z _; apply: ler_sum => z' _; apply: ler_pM.
  1,2,3,4: by [exact: bb84_W_ge0 | rewrite /Pr_event; apply: sumr_ge0 => pi _; exact: uniform_perm_mu_nonneg | exact: lexx | exact: bb84_bad_event_prob_le]. Qed.

Fact bb84_pass_bad_weight_le (P : bb84_protocol) (G : bb84_zsource P)
    (eps : R) :
  (0 < bb84_n P)%N -> (0 < bb84_k P)%N -> 0 < eps -> bb84_pass_bad_weight G eps <= eps ^+ 2.
Proof.
  move=> Hn_pos Hk_pos Heps_pos; rewrite /bb84_pass_bad_weight.
  have Heps_sum : \sum_(z : 'I_(bb84_full_string_count P)) \sum_(z' : 'I_(bb84_full_string_count P)) bb84_W G z z' * eps ^+ 2 = eps ^+ 2.
  { under eq_bigr do rewrite -mulr_suml. by rewrite -mulr_suml bb84_W_sum1 mul1r. } rewrite -Heps_sum; apply: ler_sum => z _; apply: ler_sum => z' _; apply: ler_pM.
  1,2,3: by [exact: bb84_W_ge0 | rewrite /Pr_event; apply: sumr_ge0 => pi _; exact: uniform_perm_mu_nonneg | exact: lexx].
  - have Hcap : Pr_event (fun pi : 'S_(bb84_total_rounds P) => @uniform_perm_mu R (bb84_total_rounds P) pi) ((@perm_pair_sample_le_event R (bb84_n P) (bb84_k P) (ord_to_bitstring z) (ord_to_bitstring z') (bb84_Qtol P)) :&: (@perm_pair_deviation_event R (bb84_n P) (bb84_k P) (ord_to_bitstring z) (ord_to_bitstring z') (bb84_mu (bb84_n P) (bb84_k P) eps))) <= Pr_event (fun pi : 'S_(bb84_total_rounds P) => @uniform_perm_mu R (bb84_total_rounds P) pi) (@perm_pair_deviation_event R (bb84_n P) (bb84_k P) (ord_to_bitstring z) (ord_to_bitstring z') (bb84_mu (bb84_n P) (bb84_k P) eps)).
    { rewrite /Pr_event. have HcapE : \sum_(pi in ((@perm_pair_sample_le_event R (bb84_n P) (bb84_k P) (ord_to_bitstring z) (ord_to_bitstring z') (bb84_Qtol P)) :&: (@perm_pair_deviation_event R (bb84_n P) (bb84_k P) (ord_to_bitstring z) (ord_to_bitstring z') (bb84_mu (bb84_n P) (bb84_k P) eps)))) @uniform_perm_mu R (bb84_total_rounds P) pi = \sum_(pi in @perm_pair_deviation_event R (bb84_n P) (bb84_k P) (ord_to_bitstring z) (ord_to_bitstring z') (bb84_mu (bb84_n P) (bb84_k P) eps) | pi \in @perm_pair_sample_le_event R (bb84_n P) (bb84_k P) (ord_to_bitstring z) (ord_to_bitstring z') (bb84_Qtol P)) @uniform_perm_mu R (bb84_total_rounds P) pi. { by apply: eq_bigl => pi; rewrite !inE andbC. } rewrite HcapE [X in _ <= X](bigID (mem (@perm_pair_sample_le_event R (bb84_n P) (bb84_k P) (ord_to_bitstring z) (ord_to_bitstring z') (bb84_Qtol P)))) /=. by rewrite -[leLHS]addr0 lerD2l; apply: sumr_ge0 => pi _; exact: uniform_perm_mu_nonneg. } by apply: (le_trans Hcap); exact: (bb84_bad_event_prob_le (ord_to_bitstring z) (ord_to_bitstring z') Hn_pos Hk_pos Heps_pos). Qed.

Fact bb84_pass_bad_weight_le_pass (P : bb84_protocol) (G : bb84_zsource P)
    (eps : R) :
  bb84_pass_bad_weight G eps <= bb84_p_pass_tot G.
Proof.
  rewrite /bb84_pass_bad_weight /bb84_p_pass_tot /bb84_p_pass_pair /perm_pair_sample_le_prob.
  apply: ler_sum => z _; apply: ler_sum => z' _; apply: ler_pM.
  1,2,3: by [exact: bb84_W_ge0 | rewrite /Pr_event; apply: sumr_ge0 => pi _; exact: uniform_perm_mu_nonneg | exact: lexx].
  - apply: (@Pr_event_cap_le R 'S_(bb84_total_rounds P) (fun pi : 'S_(bb84_total_rounds P) => @uniform_perm_mu R (bb84_total_rounds P) pi) (@perm_pair_sample_le_event R (bb84_n P) (bb84_k P) (ord_to_bitstring z) (ord_to_bitstring z') (bb84_Qtol P)) (@perm_pair_deviation_event R (bb84_n P) (bb84_k P) (ord_to_bitstring z) (ord_to_bitstring z') (bb84_mu (bb84_n P) (bb84_k P) eps))).
    exact: uniform_perm_mu_nonneg. Qed.

Lemma bb84_p_pass_tot_ge0 (P : bb84_protocol) (G : bb84_zsource P) :
  0 <= bb84_p_pass_tot G.
Proof. rewrite /bb84_p_pass_tot; apply: sumr_ge0 => z _; apply: sumr_ge0 => z' _. exact: mulr_ge0 (bb84_W_ge0 G z z') (bb84_p_pass_pair_ge0 z z'). Qed.

Lemma bb84_p_pass_tot_le1 (P : bb84_protocol) (G : bb84_zsource P) :
  bb84_p_pass_tot G <= 1.
Proof.
  have bb84_p_pass_pair_le1 : forall (z z' : 'I_(bb84_full_string_count P)), bb84_p_pass_pair z z' <= 1.
  { move=> z z'; rewrite /bb84_p_pass_pair /perm_pair_sample_le_prob.
    by apply: Pr_event_le1; [exact: uniform_perm_mu_nonneg | exact: uniform_perm_mu_sum1]. } rewrite /bb84_p_pass_tot -(bb84_W_sum1 G); apply: ler_sum => z _; apply: ler_sum => z' _.
  rewrite -[X in _ <= X]mulr1.
  exact: ler_pM (bb84_W_ge0 G z z') (bb84_p_pass_pair_ge0 z z') (lexx _) (bb84_p_pass_pair_le1 z z'). Qed.

Definition bb84_pass_prob_le (p_abort p_pass : R) : Prop :=
  0 <= p_abort /\ p_abort <= 1 /\ 1 - p_abort <= p_pass.

Fact bb84_pe_pass_prob_le_of_zsource
    (P : bb84_protocol) (G : bb84_zsource P) :
  bb84_pass_prob_le (1 - bb84_p_pass_tot G) (bb84_p_pass_tot G).
Proof. have Hpass_ge0 := @bb84_p_pass_tot_ge0 P G; have Hpass_le1 := @bb84_p_pass_tot_le1 P G. by split; [rewrite subr_ge0 | split; [rewrite lerBlDr lerDl | rewrite opprB addrC subrK]]. Qed.

Definition bb84_pair_projector (n : nat) (x x' : 'I_(2 ^ n))
    : 'M[C]_((2 ^ n) * (2 ^ n)) :=
  (delta_mx x x : 'M[C]_(2 ^ n)) *t
  (delta_mx x' x' : 'M[C]_(2 ^ n)).

Fact bb84_pair_projector_psdmx (n : nat) (x x' : 'I_(2 ^ n)) :
  @bb84_pair_projector n x x' \is psdmx.
Proof. rewrite /bb84_pair_projector. apply: psdmx_tens; exact: delta_mx_ii_psdmx. Qed.

Lemma bb84_pair_projector_trace (n : nat) (x x' : 'I_(2 ^ n)) :
  \tr (@bb84_pair_projector n x x') = 1.
Proof. by rewrite /bb84_pair_projector mxtrace_tens !mxtrace_delta !eqxx mul1r. Qed.

Fact bb84_pair_projector_diag_trace (n : nat)
    (A : 'M[C]_((2 ^ n) * (2 ^ n))) (x x' : 'I_(2 ^ n)) :
  \tr (@bb84_pair_projector n x x' *m A) =
  A (mxtens_index (x, x')) (mxtens_index (x, x')).
Proof. rewrite /bb84_pair_projector delta_mx_tens /mxtrace (bigD1 (mxtens_index (x, x'))) //=. rewrite mcextra.delta_mx_mulEr eqxx mul1r big1 ?addr0 // => i Hi. by rewrite mcextra.delta_mx_mulEr eq_sym (negbTE Hi) mul0r. Qed.

Fact bb84_pair_projector_ptrace1 (n : nat) (x x' : 'I_(2 ^ n)) :
  ptrace1 (@bb84_pair_projector n x x') = delta_mx x' x'.
Proof. by rewrite /bb84_pair_projector ptrace1_tensmx mxtrace_delta eqxx scale1r. Qed.

Lemma bb84_pair_projector_mul (n : nat)
    (x x' y y' : 'I_(2 ^ n)) :
  @bb84_pair_projector n x x' *m @bb84_pair_projector n y y' =
    if (x == y) && (x' == y') then @bb84_pair_projector n x x' else 0.
Proof.
  rewrite /bb84_pair_projector tensmx_mul.
  case Hxy : (x == y).
  - move/eqP: Hxy => ->; case Hx'y' : (x' == y').
    + by move/eqP: Hx'y' => ->; rewrite !mul_delta_mx.
    + have Hdelta0 : (delta_mx x' x' *m delta_mx y' y' : 'M[C]_(2 ^ n)) = 0 by rewrite mul_delta_mx_cond Hx'y' mulr0n.
      by rewrite mul_delta_mx Hdelta0 linear0r.
  - have Hdelta0 : (delta_mx x x *m delta_mx y y : 'M[C]_(2 ^ n)) = 0 by rewrite mul_delta_mx_cond Hxy mulr0n.
    by rewrite Hdelta0 linear0l. Qed.

Definition bb84_good_projector (n : nat) (delta : R)
    : 'M[C]_((2 ^ n) * (2 ^ n)) :=
  \sum_(x : 'I_(2 ^ n))
    \sum_(x' : 'I_(2 ^ n) | @relative_hamming_ball R n delta x x')
      @bb84_pair_projector n x x'.

Fact bb84_good_projector_psdmx (n : nat) (delta : R) :
  @bb84_good_projector n delta \is psdmx.
Proof. by rewrite /bb84_good_projector; apply: psdmx_sum => x _; apply: psdmx_sum => x' _; exact: bb84_pair_projector_psdmx. Qed.

Fact bb84_good_projector_ptrace1 (n : nat) (delta : R) :
  ptrace1 (@bb84_good_projector n delta) =
  \sum_(x' : 'I_(2 ^ n))
    ((@relative_hamming_ball_count R n delta x')%:R%:C *:
      (delta_mx x' x' : 'M[C]_(2 ^ n))).
Proof.
  rewrite /bb84_good_projector linear_sum.
  under eq_bigr do rewrite linear_sum.
  rewrite (exchange_big_dep xpredT) //=; apply: eq_bigr => x' _.
  rewrite (eq_bigr (fun _ => delta_mx x' x' : 'M[C]_(2 ^ n))); last by move=> x _; exact: bb84_pair_projector_ptrace1.
  rewrite (eq_bigr (fun _ => (1%:R%:C *: (delta_mx x' x' : 'M[C]_(2 ^ n))))); last by move=> x _; rewrite scale1r.
  rewrite -scaler_suml; congr (_ *: _).
  by rewrite /relative_hamming_ball_count [in RHS]natr_sum !big_mkcond -big_mkcond -rmorph_sum. Qed.

Fact bb84_good_projector_ptrace1_le_max (n : nat) (delta : R) :
  ptrace1 (@bb84_good_projector n delta) <=
    ((@relative_hamming_ball_count_max R n delta)%:R)%:C *:
      (1%:M : 'M[C]_(2 ^ n)).
Proof.
  rewrite le_lownerE bb84_good_projector_ptrace1.
  have Hdelta_diag_sum : \sum_(x' : 'I_(2 ^ n)) (delta_mx x' x' : 'M[C]_(2 ^ n)) = 1%:M by rewrite mx1_sum_delta.
  have -> : ((@relative_hamming_ball_count_max R n delta)%:R)%:C *: (1%:M : 'M[C]_(2 ^ n)) - \sum_(x' : 'I_(2 ^ n)) ((@relative_hamming_ball_count R n delta x')%:R%:C *: (delta_mx x' x' : 'M[C]_(2 ^ n))) = \sum_(x' : 'I_(2 ^ n)) (((@relative_hamming_ball_count_max R n delta - @relative_hamming_ball_count R n delta x')%:R)%:C *: (delta_mx x' x' : 'M[C]_(2 ^ n))).
  { rewrite -Hdelta_diag_sum scaler_sumr -sumrB; apply: eq_bigr => x' _.
    by rewrite -scalerBl -rmorphB natrB // /relative_hamming_ball_count_max; exact: leq_bigmax x'. } apply: psdmx_sum => x' _; apply: psdmxZ.
  - rewrite lec0R.
    change (((0%N)%:R : R) <= ((@relative_hamming_ball_count_max R n delta - @relative_hamming_ball_count R n delta x')%:R : R)).
    by rewrite ler_nat; exact: leq0n.
  - exact: delta_mx_ii_psdmx. Qed.

Fact bb84_pair_projector_mul_good_projector (n : nat) (delta : R)
    (x x' : 'I_(2 ^ n)) :
  @bb84_pair_projector n x x' *m @bb84_good_projector n delta =
    if @relative_hamming_ball R n delta x x'
    then @bb84_pair_projector n x x' else 0.
Proof.
  case Hgood : (@relative_hamming_ball R n delta x x').
  - rewrite /bb84_good_projector mulmx_sumr (bigD1 x) //=.
    have Hrest_x : \sum_(y : 'I_(2 ^ n) | y != x) @bb84_pair_projector n x x' *m (\sum_(y' : 'I_(2 ^ n) | @relative_hamming_ball R n delta y y') @bb84_pair_projector n y y') = 0.
    { apply: big1 => y /negPf Hyx; rewrite mulmx_sumr.
      by apply: big1 => y' _; rewrite bb84_pair_projector_mul eq_sym Hyx. } rewrite [X in _ + X]Hrest_x addr0 mulmx_sumr (bigD1 x') //=.
    have Hrest_x' : \sum_(y' : 'I_(2 ^ n) | @relative_hamming_ball R n delta x y' && (y' != x')) @bb84_pair_projector n x x' *m @bb84_pair_projector n x y' = 0.
    { apply: big1 => y' /andP [_ /negPf Hy'x]. by rewrite bb84_pair_projector_mul eqxx eq_sym Hy'x. } by rewrite [X in _ + X]Hrest_x' addr0 bb84_pair_projector_mul !eqxx.
  - rewrite /bb84_good_projector mulmx_sumr (bigD1 x) //=.
    have Hrest_x : \sum_(y : 'I_(2 ^ n) | y != x) @bb84_pair_projector n x x' *m (\sum_(y' : 'I_(2 ^ n) | @relative_hamming_ball R n delta y y') @bb84_pair_projector n y y') = 0.
    { apply: big1 => y /negPf Hyx; rewrite mulmx_sumr.
      by apply: big1 => y' _; rewrite bb84_pair_projector_mul eq_sym Hyx. } rewrite [X in _ + X]Hrest_x addr0 mulmx_sumr; apply: big1 => y' Hxy'.
    rewrite bb84_pair_projector_mul eqxx; case Hx'y' : (x' == y').
    + move/eqP: Hx'y' => Hx'y'_eq; have Hgood_xx' : @relative_hamming_ball R n delta x x' by rewrite -Hx'y'_eq in Hxy'.
      by rewrite Hgood in Hgood_xx'.
    + by []. Qed.

Fact bb84_good_projector_mul_pair_projector (n : nat) (delta : R)
    (x x' : 'I_(2 ^ n)) :
  @bb84_good_projector n delta *m @bb84_pair_projector n x x' =
    if @relative_hamming_ball R n delta x x'
    then @bb84_pair_projector n x x' else 0.
Proof.
  case Hgood : (@relative_hamming_ball R n delta x x').
  - rewrite /bb84_good_projector mulmx_suml (bigD1 x) //=.
    have Hrest_x : \sum_(y : 'I_(2 ^ n) | y != x) (\sum_(y' : 'I_(2 ^ n) | @relative_hamming_ball R n delta y y') @bb84_pair_projector n y y') *m @bb84_pair_projector n x x' = 0.
    { apply: big1 => y /negPf Hyx; rewrite mulmx_suml.
      by apply: big1 => y' _; rewrite bb84_pair_projector_mul Hyx. } rewrite [X in _ + X]Hrest_x addr0 mulmx_suml (bigD1 x') //=.
    have Hrest_x' : \sum_(y' : 'I_(2 ^ n) | @relative_hamming_ball R n delta x y' && (y' != x')) @bb84_pair_projector n x y' *m @bb84_pair_projector n x x' = 0.
    { apply: big1 => y' /andP [_ /negPf Hy'x].
      rewrite bb84_pair_projector_mul eqxx; case Hx'y' : (x' == y').
      - by move/eqP: Hx'y' => Hx'y'_eq; move/eqP: Hy'x; rewrite eq_sym Hx'y'_eq.
      - by rewrite eq_sym Hx'y'. } by rewrite [X in _ + X]Hrest_x' addr0 bb84_pair_projector_mul !eqxx.
  - rewrite /bb84_good_projector mulmx_suml (bigD1 x) //=.
    have Hrest_x : \sum_(y : 'I_(2 ^ n) | y != x) (\sum_(y' : 'I_(2 ^ n) | @relative_hamming_ball R n delta y y') @bb84_pair_projector n y y') *m @bb84_pair_projector n x x' = 0.
    { apply: big1 => y /negPf Hyx; rewrite mulmx_suml.
      by apply: big1 => y' _; rewrite bb84_pair_projector_mul Hyx. } rewrite [X in _ + X]Hrest_x addr0 mulmx_suml; apply: big1 => y' Hxy'.
    rewrite bb84_pair_projector_mul eqxx; case Hx'y' : (y' == x').
    + move/eqP: Hx'y' => Hx'y'_eq; have Hgood_xx' : @relative_hamming_ball R n delta x x' by rewrite Hx'y'_eq in Hxy'.
      by rewrite Hgood in Hgood_xx'.
    + by []. Qed.

Fact bb84_good_projector_sandwich_pair_projector (n : nat) (delta : R)
    (x x' : 'I_(2 ^ n)) :
  @bb84_good_projector n delta *m @bb84_pair_projector n x x' *m
      @bb84_good_projector n delta =
    if @relative_hamming_ball R n delta x x'
    then @bb84_pair_projector n x x' else 0.
Proof. rewrite bb84_good_projector_mul_pair_projector; case Hgood : (@relative_hamming_ball R n delta x x'). - by rewrite bb84_pair_projector_mul_good_projector Hgood. - by rewrite mul0mx. Qed.

Fact bb84_good_projector_proj (n : nat) (delta : R) :
  @bb84_good_projector n delta \is projmx.
Proof.
  have Hpair_left_fix (x x' : 'I_(2 ^ n)) : @relative_hamming_ball R n delta x x' -> @bb84_good_projector n delta *m @bb84_pair_projector n x x' = @bb84_pair_projector n x x'.
  { move=> Hgood; rewrite /bb84_good_projector mulmx_suml (bigD1 x) //=.
    have Hrest_x : \sum_(y : 'I_(2 ^ n) | y != x) (\sum_(y' : 'I_(2 ^ n) | @relative_hamming_ball R n delta y y') @bb84_pair_projector n y y') *m @bb84_pair_projector n x x' = 0.
    { apply: big1 => y /negPf Hyx; rewrite mulmx_suml.
      by apply: big1 => y' _; rewrite bb84_pair_projector_mul Hyx. } rewrite [X in _ + X]Hrest_x addr0 mulmx_suml (bigD1 x') //=.
    have Hrest_x' : \sum_(y' : 'I_(2 ^ n) | @relative_hamming_ball R n delta x y' && (y' != x')) @bb84_pair_projector n x y' *m @bb84_pair_projector n x x' = 0.
    { apply: big1 => y' /andP [_ /negPf Hy'x].
      rewrite bb84_pair_projector_mul eqxx; case Hx'y' : (x' == y').
      - by move/eqP: Hx'y' => Hx'y'_eq; move/eqP: Hy'x; rewrite eq_sym Hx'y'_eq.
      - by rewrite eq_sym Hx'y'. } by rewrite [X in _ + X]Hrest_x' addr0 bb84_pair_projector_mul !eqxx. }
apply/projmxP_id; split; first exact: psdmx_herm (bb84_good_projector_psdmx n delta).
  rewrite [RHS]/bb84_good_projector mulmx_sumr; apply: eq_bigr => x _.
  by rewrite mulmx_sumr; apply: eq_bigr => x' Hgood; exact: Hpair_left_fix. Qed.

Definition bb84_holdout_iso (n k : nat)
    (pi : 'S_(k + n)) (sample : bitstr k)
    : 'M[C]_(2 ^ n, 2 ^ (k + n)) :=
  \sum_(w : 'I_(2 ^ n))
    delta_mx w
      (bitstring_to_ord
        (@perm_pair_assemble n k pi sample (ord_to_bitstring w))).

Lemma bb84_holdout_isoE (n k : nat)
    (pi : 'S_(k + n)) (sample : bitstr k)
    (w : 'I_(2 ^ n)) (z : 'I_(2 ^ (k + n))) :
  bb84_holdout_iso pi sample w z =
  ((z == bitstring_to_ord
      (@perm_pair_assemble n k pi sample (ord_to_bitstring w)))%:R)%:C.
Proof.
  rewrite /bb84_holdout_iso summxE (bigD1 w) //= mxE eqxx andTb eq_sym.
  have Hrest : \sum_(i : 'I_(2 ^ n) | i != w) ((delta_mx i (bitstring_to_ord (@perm_pair_assemble n k pi sample (ord_to_bitstring i)))) w z) = 0 :> C.
  { by apply: big1 => i /negPf Hiw; rewrite mxE eq_sym Hiw. } by rewrite Hrest addr0; case: eqP. Qed.

Definition bb84_sample_projector (n k : nat)
    (pi : 'S_(k + n)) (sample : bitstr k)
    : 'M[C]_(2 ^ (k + n)) :=
  \sum_(w : 'I_(2 ^ n))
    let z := bitstring_to_ord
      (@perm_pair_assemble n k pi sample (ord_to_bitstring w)) in
    delta_mx z z.

Fact bb84_sample_projector_sum1 (n k : nat)
    (pi : 'S_(k + n)) :
  \sum_(a : 'I_(2 ^ k))
    bb84_sample_projector pi (ord_to_bitstring a) =
  (1%:M : 'M[C]_(2 ^ (k + n))).
Proof. rewrite [RHS]mx1_sum_delta (@perm_pair_sum_split_ord n k _ pi (fun z : 'I_(2 ^ (k + n)) => delta_mx z z)). apply: eq_bigr => a _; rewrite /bb84_sample_projector. by apply: eq_bigr => w _; rewrite /perm_pair_assemble_ord /=. Qed.

Definition bb84_holdout_kraus (P : bb84_protocol) (G : bb84_zsource P)
    (pi : 'S_(bb84_total_rounds P))
    (a b : 'I_(2 ^ bb84_k P))
    : 'M[C]_((2 ^ bb84_n P) * bb84_zsrc_nb G * (2 ^ bb84_n P),
             bb84_full_string_count P * bb84_zsrc_nb G *
             bb84_full_string_count P) :=
  ((bb84_holdout_iso pi (ord_to_bitstring a) *t
      (1%:M : 'M[C]_(bb84_zsrc_nb G))) *t
    bb84_holdout_iso pi (ord_to_bitstring b)).

Fact bb84_holdout_kraus_coiso (P : bb84_protocol) (G : bb84_zsource P)
    (pi : 'S_(bb84_total_rounds P))
    (a b : 'I_(2 ^ bb84_k P)) :
  bb84_holdout_kraus G pi a b *m (bb84_holdout_kraus G pi a b)^*t = 1%:M.
Proof.
have bb84_holdout_iso_coiso : forall (n k : nat) (pi : 'S_(k + n)) (sample : bitstr k), bb84_holdout_iso pi sample *m (bb84_holdout_iso pi sample)^*t = 1%:M.
{ clear b a pi G P; move=> n k pi sample; apply/matrixP => i j; rewrite !mxE.
  pose ai := bitstring_to_ord (@perm_pair_assemble n k pi sample (ord_to_bitstring i)).
  pose aj := bitstring_to_ord (@perm_pair_assemble n k pi sample (ord_to_bitstring j)).
  have Hsum : \sum_(z : 'I_(2 ^ (k + n)))
        ((((z == ai)%:R : R)%:C) * (((z == aj)%:R : R)%:C)^*) =
      (((ai == aj)%:R : R)%:C).
  { case Hai : (ai == aj).
    - move/eqP: Hai => <-; rewrite (bigD1 (ai : 'I_(2 ^ (k + n)))) //= eqxx conjC1 mulr1.
      have Hrest : \sum_(z : 'I_(2 ^ (k + n)) | z != ai)
            ((((z == ai)%:R : R)%:C) * (((z == ai)%:R : R)%:C)^*) = 0 :> C.
      { by apply: big1 => z /negPf Hz; rewrite Hz mul0r. } by rewrite Hrest addr0; change ((1 : R)%:C = 1%:C); rewrite rmorph1.
    - change (\sum_(z : 'I_(2 ^ (k + n))) ((((z == ai)%:R : R)%:C) * (((z == aj)%:R : R)%:C)^*) = 0 :> C); apply: big1 => z _.
      case Hzi : (z == ai); case Hzj : (z == aj).
      + move/eqP: Hzi => Hzi; move/eqP: Hzj => Hzj; have Hai' : ai == aj by apply/eqP; rewrite -Hzi -Hzj.
        by rewrite Hai in Hai'.
      1,2,3: by [change ((1 : C) * (0 : C)^* = 0); rewrite conjC0 mulr0 | change ((0 : C) * (1 : C)^* = 0); rewrite mul0r | change ((0 : C) * (0 : C)^* = 0); rewrite mul0r]. }
rewrite (eq_bigr (fun z : 'I_(2 ^ (k + n)) =>
    ((((z == ai)%:R : R)%:C) * (((z == aj)%:R : R)%:C)^*))); last first.
  { move=> z _; rewrite (@bb84_holdout_isoE n k pi sample i z).
    rewrite mxE mxE (@bb84_holdout_isoE n k pi sample j z) /ai /aj.
    by case Hzi : (z == ai); case Hzj : (z == aj); rewrite /=. } rewrite Hsum.
  have HaiE : (ai == aj) = (i == j).
  { apply/idP/idP.
    - by move/eqP=> Ha; apply/eqP; exact: (@perm_pair_assemble_holdout_ord_inj n k pi sample i j Ha).
    - by move/eqP=> Hij; rewrite /ai /aj Hij eqxx. } by rewrite HaiE; case: (i == j). } by rewrite /bb84_holdout_kraus !adjmx_tens !tensmx_mul !bb84_holdout_iso_coiso adjmx1 !mul1mx !tensmx11. Qed.

Fact bb84_holdout_kraus_adjoint_mul
    (P : bb84_protocol) (G : bb84_zsource P)
    (pi : 'S_(bb84_total_rounds P))
    (a b : 'I_(2 ^ bb84_k P)) :
  (bb84_holdout_kraus G pi a b)^*t *m bb84_holdout_kraus G pi a b =
  ((bb84_sample_projector pi (ord_to_bitstring a) *t
      (1%:M : 'M[C]_(bb84_zsrc_nb G))) *t
    bb84_sample_projector pi (ord_to_bitstring b)).
Proof.
have bb84_holdout_iso_adjoint_mul : forall (n k : nat) (pi : 'S_(k + n)) (sample : bitstr k), (bb84_holdout_iso pi sample)^*t *m bb84_holdout_iso pi sample = bb84_sample_projector pi sample.
{ clear b a pi G P; move=> n k pi sample; apply/matrixP => x y.
  rewrite !mxE /bb84_sample_projector summxE; apply: eq_bigr => w _.
  rewrite !mxE (@bb84_holdout_isoE n k pi sample w x) (@bb84_holdout_isoE n k pi sample w y).
  case Hx : (x == bitstring_to_ord (@perm_pair_assemble n k pi sample (ord_to_bitstring w))); case Hy : (y == bitstring_to_ord (@perm_pair_assemble n k pi sample (ord_to_bitstring w))).
  1,2,3,4: by [rewrite /= conjC1 mul1r | change ((1 : C)^* * 0 = 0); rewrite mulr0 | change ((0 : C)^* * 1 = 0); rewrite conjC0 mul0r | change ((0 : C)^* * 0 = 0); rewrite conjC0 mul0r]. }
  by rewrite /bb84_holdout_kraus !adjmx_tens !tensmx_mul !bb84_holdout_iso_adjoint_mul adjmx1 !mul1mx. Qed.

Fact bb84_holdout_kraus_adjmul_sum
    (P : bb84_protocol) (G : bb84_zsource P)
    (pi : 'S_(bb84_total_rounds P)) :
  \sum_(a : 'I_(2 ^ bb84_k P))
    \sum_(b : 'I_(2 ^ bb84_k P))
      (bb84_holdout_kraus G pi a b)^*t *m bb84_holdout_kraus G pi a b =
  1%:M.
Proof.
  rewrite (eq_bigr _ (fun a _ => eq_bigr _ (fun b _ => bb84_holdout_kraus_adjoint_mul G pi a b))).
  have Hinner (a : 'I_(2 ^ bb84_k P)) : \sum_(b : 'I_(2 ^ bb84_k P)) ((bb84_sample_projector pi (ord_to_bitstring a) *t (1%:M : 'M[C]_(bb84_zsrc_nb G))) *t bb84_sample_projector pi (ord_to_bitstring b)) = ((bb84_sample_projector pi (ord_to_bitstring a) *t (1%:M : 'M[C]_(bb84_zsrc_nb G))) *t (1%:M : 'M[C]_(2 ^ (bb84_k P + bb84_n P)))).
  { by rewrite -tensmx_sumr (@bb84_sample_projector_sum1 (bb84_n P) (bb84_k P)). } rewrite (eq_bigr _ (fun a _ => Hinner a)) -tensmx_suml.
  have Hleft : \sum_(a : 'I_(2 ^ bb84_k P)) (bb84_sample_projector pi (ord_to_bitstring a) *t (1%:M : 'M[C]_(bb84_zsrc_nb G))) = (1%:M : 'M[C]_(2 ^ (bb84_k P + bb84_n P) * bb84_zsrc_nb G)).
  { rewrite -[RHS](@tensmx11 C (2 ^ (bb84_k P + bb84_n P)) (bb84_zsrc_nb G)).
    by rewrite -tensmx_suml (@bb84_sample_projector_sum1 (bb84_n P) (bb84_k P)). } by rewrite Hleft tensmx11. Qed.

Definition bb84_holdout_projector (P : bb84_protocol) (G : bb84_zsource P)
    (w w' : 'I_(2 ^ bb84_n P))
    : 'M[C]_((2 ^ bb84_n P) * bb84_zsrc_nb G * (2 ^ bb84_n P)) :=
  ((delta_mx w w : 'M[C]_(2 ^ bb84_n P)) *t
    (1%:M : 'M[C]_(bb84_zsrc_nb G))) *t
    (delta_mx w' w' : 'M[C]_(2 ^ bb84_n P)).

Definition bb84_holdout_measure_ZZ (P : bb84_protocol) (G : bb84_zsource P)
    (rho : 'M[C]_((2 ^ bb84_n P) * bb84_zsrc_nb G * (2 ^ bb84_n P)))
    : 'M[C]_((2 ^ bb84_n P) * (2 ^ bb84_n P)) :=
  \sum_(w : 'I_(2 ^ bb84_n P))
    \sum_(w' : 'I_(2 ^ bb84_n P))
      (\tr (bb84_holdout_projector G w w' *m rho)) *:
        bb84_pair_projector w w'.

Definition bb84_sample_pair_passes (P : bb84_protocol)
    (a b : 'I_(2 ^ bb84_k P)) : bool :=
  ((d_ham (ord_to_bitstring a) (ord_to_bitstring b))%:R /
    (bb84_k P)%:R <= bb84_Qtol P)%R.

Lemma bb84_sample_pair_passes_assemble_ord
    (P : bb84_protocol) (pi : 'S_(bb84_total_rounds P))
    (a b : 'I_(2 ^ bb84_k P))
    (w w' : 'I_(2 ^ bb84_n P)) :
  (pi \in @perm_pair_sample_le_event R (bb84_n P) (bb84_k P)
      (ord_to_bitstring (perm_pair_assemble_ord pi (a, w)))
      (ord_to_bitstring (perm_pair_assemble_ord pi (b, w')))
      (bb84_Qtol P)) =
  @bb84_sample_pair_passes P a b.
Proof. rewrite /bb84_sample_pair_passes /perm_pair_sample_le_event inE. by rewrite /perm_pair_sample_err /perm_pair_sample_count /perm_pair_assemble_ord !ord_to_bitstringK !perm_pair_sample_assemble. Qed.

Definition bb84_cond_rho_raw (P : bb84_protocol) (G : bb84_zsource P)
    : 'M[C]_((2 ^ bb84_n P) * bb84_zsrc_nb G * (2 ^ bb84_n P)) :=
  \sum_(pi : 'S_(bb84_total_rounds P))
    \sum_(a : 'I_(2 ^ bb84_k P))
      \sum_(b : 'I_(2 ^ bb84_k P) | @bb84_sample_pair_passes P a b)
        ((@uniform_perm_mu R (bb84_total_rounds P) pi)%:C) *:
          (bb84_holdout_kraus G pi a b *m bb84_zsrc_rho G *m
            (bb84_holdout_kraus G pi a b)^*t).

Definition bb84_cond_rho (P : bb84_protocol) (G : bb84_zsource P)
    : 'M[C]_((2 ^ bb84_n P) * bb84_zsrc_nb G * (2 ^ bb84_n P)) :=
  ((bb84_p_pass_tot G)^-1)%:C *: bb84_cond_rho_raw G.

Fact bb84_cond_rho_raw_trace1 (P : bb84_protocol) (G : bb84_zsource P) :
  \tr (bb84_cond_rho_raw G) = (bb84_p_pass_tot G)%:C.
Proof.
have bb84_cond_rho_raw_traceW : forall (P : bb84_protocol) (G : bb84_zsource P), \tr (bb84_cond_rho_raw G) = \sum_(pi : 'S_(bb84_total_rounds P)) \sum_(a : 'I_(2 ^ bb84_k P)) \sum_(b : 'I_(2 ^ bb84_k P) | @bb84_sample_pair_passes P a b) ((@uniform_perm_mu R (bb84_total_rounds P) pi)%:C * \sum_(w : 'I_(2 ^ bb84_n P)) \sum_(w' : 'I_(2 ^ bb84_n P)) (bb84_W G (bitstring_to_ord (@perm_pair_assemble (bb84_n P) (bb84_k P) pi (ord_to_bitstring a) (ord_to_bitstring w))) (bitstring_to_ord (@perm_pair_assemble (bb84_n P) (bb84_k P) pi (ord_to_bitstring b) (ord_to_bitstring w'))))%:C).
{ clear G P; move=> P G. have bb84_sample_projector_pair_traceW : forall (P : bb84_protocol) (G : bb84_zsource P) (pi : 'S_(bb84_total_rounds P)) (a b : 'I_(2 ^ bb84_k P)), \tr (((bb84_sample_projector pi (ord_to_bitstring a) *t (1%:M : 'M[C]_(bb84_zsrc_nb G))) *t bb84_sample_projector pi (ord_to_bitstring b)) *m bb84_zsrc_rho G) = \sum_(w : 'I_(2 ^ bb84_n P)) \sum_(w' : 'I_(2 ^ bb84_n P)) (bb84_W G (bitstring_to_ord (@perm_pair_assemble (bb84_n P) (bb84_k P) pi (ord_to_bitstring a) (ord_to_bitstring w))) (bitstring_to_ord (@perm_pair_assemble (bb84_n P) (bb84_k P) pi (ord_to_bitstring b) (ord_to_bitstring w'))))%:C.
{ clear G P; move=> P G pi a b. have bb84_sample_projector_pair_traceE : forall (P : bb84_protocol) (G : bb84_zsource P) (pi : 'S_(bb84_total_rounds P)) (a b : 'I_(2 ^ bb84_k P)), \tr (((bb84_sample_projector pi (ord_to_bitstring a) *t (1%:M : 'M[C]_(bb84_zsrc_nb G))) *t bb84_sample_projector pi (ord_to_bitstring b)) *m bb84_zsrc_rho G) = \sum_(w : 'I_(2 ^ bb84_n P)) \sum_(w' : 'I_(2 ^ bb84_n P)) \tr ((((delta_mx (bitstring_to_ord (@perm_pair_assemble (bb84_n P) (bb84_k P) pi (ord_to_bitstring a) (ord_to_bitstring w))) (bitstring_to_ord (@perm_pair_assemble (bb84_n P) (bb84_k P) pi (ord_to_bitstring a) (ord_to_bitstring w))) : 'M[C]_(bb84_full_string_count P)) *t (1%:M : 'M[C]_(bb84_zsrc_nb G))) *t (delta_mx (bitstring_to_ord (@perm_pair_assemble (bb84_n P) (bb84_k P) pi (ord_to_bitstring b) (ord_to_bitstring w'))) (bitstring_to_ord (@perm_pair_assemble (bb84_n P) (bb84_k P) pi (ord_to_bitstring b) (ord_to_bitstring w'))) : 'M[C]_(bb84_full_string_count P))) *m bb84_zsrc_rho G).
{ clear b a pi G P; move=> P G pi a b. rewrite /bb84_sample_projector.
  have Hleft : ((\sum_(w : 'I_(2 ^ bb84_n P)) delta_mx (bitstring_to_ord (@perm_pair_assemble (bb84_n P) (bb84_k P) pi (ord_to_bitstring a) (ord_to_bitstring w))) (bitstring_to_ord (@perm_pair_assemble (bb84_n P) (bb84_k P) pi (ord_to_bitstring a) (ord_to_bitstring w)))) *t (1%:M : 'M[C]_(bb84_zsrc_nb G))) *t (\sum_(w' : 'I_(2 ^ bb84_n P)) delta_mx (bitstring_to_ord (@perm_pair_assemble (bb84_n P) (bb84_k P) pi (ord_to_bitstring b) (ord_to_bitstring w'))) (bitstring_to_ord (@perm_pair_assemble (bb84_n P) (bb84_k P) pi (ord_to_bitstring b) (ord_to_bitstring w')))) = \sum_(w : 'I_(2 ^ bb84_n P)) \sum_(w' : 'I_(2 ^ bb84_n P)) (((delta_mx (bitstring_to_ord (@perm_pair_assemble (bb84_n P) (bb84_k P) pi (ord_to_bitstring a) (ord_to_bitstring w))) (bitstring_to_ord (@perm_pair_assemble (bb84_n P) (bb84_k P) pi (ord_to_bitstring a) (ord_to_bitstring w))) : 'M[C]_(bb84_full_string_count P)) *t (1%:M : 'M[C]_(bb84_zsrc_nb G))) *t (delta_mx (bitstring_to_ord (@perm_pair_assemble (bb84_n P) (bb84_k P) pi (ord_to_bitstring b) (ord_to_bitstring w'))) (bitstring_to_ord (@perm_pair_assemble (bb84_n P) (bb84_k P) pi (ord_to_bitstring b) (ord_to_bitstring w'))) : 'M[C]_(bb84_full_string_count P))).
  { by rewrite tensmx_suml tensmx_suml; apply: eq_bigr => w _; rewrite tensmx_sumr. } by rewrite Hleft mulmx_suml linear_sum; apply: eq_bigr => w _; rewrite mulmx_suml linear_sum. } by rewrite bb84_sample_projector_pair_traceE; apply: eq_bigr => w _; apply: eq_bigr => w' _; exact: bb84_W_traceE. } have bb84_cond_rho_raw_traceE : forall (P : bb84_protocol) (G : bb84_zsource P), \tr (bb84_cond_rho_raw G) = \sum_(pi : 'S_(bb84_total_rounds P)) \sum_(a : 'I_(2 ^ bb84_k P)) \sum_(b : 'I_(2 ^ bb84_k P) | @bb84_sample_pair_passes P a b) ((@uniform_perm_mu R (bb84_total_rounds P) pi)%:C * \tr (((bb84_sample_projector pi (ord_to_bitstring a) *t (1%:M : 'M[C]_(bb84_zsrc_nb G))) *t bb84_sample_projector pi (ord_to_bitstring b)) *m bb84_zsrc_rho G)).
{ clear G P; move=> P G. have bb84_holdout_kraus_trace : forall (P : bb84_protocol) (G : bb84_zsource P) (pi : 'S_(bb84_total_rounds P)) (a b : 'I_(2 ^ bb84_k P)), \tr (bb84_holdout_kraus G pi a b *m bb84_zsrc_rho G *m (bb84_holdout_kraus G pi a b)^*t) = \tr (((bb84_sample_projector pi (ord_to_bitstring a) *t (1%:M : 'M[C]_(bb84_zsrc_nb G))) *t bb84_sample_projector pi (ord_to_bitstring b)) *m bb84_zsrc_rho G).
{ clear G P; move=> P G pi a b. rewrite mxtrace_mulC mulmxA. by rewrite bb84_holdout_kraus_adjoint_mul. } rewrite /bb84_cond_rho_raw linear_sum; apply: eq_bigr => pi _; rewrite linear_sum; apply: eq_bigr => a _.
  rewrite linear_sum; apply: eq_bigr => b _.
  by rewrite linearZ; congr (_ * _); exact: bb84_holdout_kraus_trace. } rewrite bb84_cond_rho_raw_traceE; apply: eq_bigr => pi _; apply: eq_bigr => a _; apply: eq_bigr => b _.
  by congr (_ * _); exact: bb84_sample_projector_pair_traceW. } have bb84_p_pass_tot_assemble : forall (P : bb84_protocol) (G : bb84_zsource P), bb84_p_pass_tot G = \sum_(pi : 'S_(bb84_total_rounds P)) @uniform_perm_mu R (bb84_total_rounds P) pi * \sum_(a : 'I_(2 ^ bb84_k P)) \sum_(b : 'I_(2 ^ bb84_k P) | @bb84_sample_pair_passes P a b) \sum_(w : 'I_(2 ^ bb84_n P)) \sum_(w' : 'I_(2 ^ bb84_n P)) bb84_W G (perm_pair_assemble_ord pi (a, w)) (perm_pair_assemble_ord pi (b, w')).
{ clear G P; move=> P G. have bb84_pass_weight_sum_assemble : forall (P : bb84_protocol) (G : bb84_zsource P) (pi : 'S_(bb84_total_rounds P)), \sum_(a : 'I_(2 ^ bb84_k P)) \sum_(b : 'I_(2 ^ bb84_k P) | @bb84_sample_pair_passes P a b) \sum_(w : 'I_(2 ^ bb84_n P)) \sum_(w' : 'I_(2 ^ bb84_n P)) bb84_W G (perm_pair_assemble_ord pi (a, w)) (perm_pair_assemble_ord pi (b, w')) = \sum_(z : 'I_(bb84_full_string_count P)) \sum_(z' : 'I_(bb84_full_string_count P) | pi \in @perm_pair_sample_le_event R (bb84_n P) (bb84_k P) (ord_to_bitstring z) (ord_to_bitstring z') (bb84_Qtol P)) bb84_W G z z'.
{ clear G P; move=> P G pi. rewrite [RHS](perm_pair_sum_split_ord pi (fun z : 'I_(bb84_full_string_count P) => \sum_(z' : 'I_(bb84_full_string_count P) | pi \in @perm_pair_sample_le_event R (bb84_n P) (bb84_k P) (ord_to_bitstring z) (ord_to_bitstring z') (bb84_Qtol P)) bb84_W G z z')).
  apply: eq_bigr => a _; rewrite exchange_big /=; apply: eq_bigr => w _.
  rewrite big_mkcond [RHS]big_mkcond.
  rewrite [RHS](perm_pair_sum_split_ord pi (fun z' : 'I_(bb84_full_string_count P) => if pi \in @perm_pair_sample_le_event R (bb84_n P) (bb84_k P) (ord_to_bitstring (perm_pair_assemble_ord pi (a, w))) (ord_to_bitstring z') (bb84_Qtol P) then bb84_W G (perm_pair_assemble_ord pi (a, w)) z' else 0)).
  apply: eq_bigr => b _; case Hpass : (@bb84_sample_pair_passes P a b).
  - by apply: eq_bigr => w' _; rewrite bb84_sample_pair_passes_assemble_ord Hpass.
  - by rewrite big1 // => w' _; rewrite bb84_sample_pair_passes_assemble_ord Hpass. } rewrite /bb84_p_pass_tot /bb84_p_pass_pair /perm_pair_sample_le_prob /Pr_event.
  rewrite (eq_bigr (fun z : 'I_(bb84_full_string_count P) => \sum_(z' : 'I_(bb84_full_string_count P)) \sum_(pi : 'S_(bb84_total_rounds P) | pi \in @perm_pair_sample_le_event R (bb84_n P) (bb84_k P) (ord_to_bitstring z) (ord_to_bitstring z') (bb84_Qtol P)) (bb84_W G z z' * @uniform_perm_mu R (bb84_total_rounds P) pi))); last first.
  { move=> z _; apply: eq_bigr => z' _. by rewrite mulr_sumr. } rewrite (eq_bigr (fun z : 'I_(bb84_full_string_count P) => \sum_(pi : 'S_(bb84_total_rounds P)) \sum_(z' : 'I_(bb84_full_string_count P) | pi \in @perm_pair_sample_le_event R (bb84_n P) (bb84_k P) (ord_to_bitstring z) (ord_to_bitstring z') (bb84_Qtol P)) (bb84_W G z z' * @uniform_perm_mu R (bb84_total_rounds P) pi))); last first.
  { move=> z _; by rewrite (exchange_big_dep xpredT) //=. } rewrite exchange_big /=; apply: eq_bigr => pi _.
  rewrite bb84_pass_weight_sum_assemble mulr_sumr; apply: eq_bigr => z _.
  by rewrite mulr_sumr; apply: eq_bigr => z' _; exact: mulrC. } rewrite bb84_cond_rho_raw_traceW bb84_p_pass_tot_assemble [RHS]rmorph_sum.
  apply: eq_bigr => pi _; rewrite [RHS]rmorphM.
  rewrite [X in _ = _ * X]rmorph_sum; rewrite [RHS]mulr_sumr; apply: eq_bigr => a _.
  rewrite [X in _ = _ * X]rmorph_sum; rewrite [RHS]mulr_sumr; apply: eq_bigr => b _.
  congr (_ * _); rewrite [RHS]rmorph_sum.
  by apply: eq_bigr => w _; rewrite [RHS]rmorph_sum; apply: eq_bigr => w' _; rewrite /perm_pair_assemble_ord. Qed.

Lemma bb84_cond_rho_den1 (P : bb84_protocol) (G : bb84_zsource P) :
  0 < bb84_p_pass_tot G -> bb84_cond_rho G \is den1mx.
Proof.
have bb84_cond_rho_psdmx : forall (P : bb84_protocol) (G : bb84_zsource P), bb84_cond_rho G \is psdmx.
{ clear G P; move=> P G. have bb84_cond_rho_raw_psdmx : forall (P : bb84_protocol) (G : bb84_zsource P), bb84_cond_rho_raw G \is psdmx.
{ clear G P; move=> P G; have /den1mxP [Hrho_psd _] := bb84_zsrc_den1 G; rewrite /bb84_cond_rho_raw.
  apply: psdmx_sum => pi _; apply: psdmx_sum => a _; apply: psdmx_sum => b _; apply: psdmxZ.
  - by rewrite lecR uniform_perm_mu_nonneg.
  - exact: form_psdmx. } rewrite /bb84_cond_rho; apply: psdmxZ.
  - by rewrite lecR invr_ge0 bb84_p_pass_tot_ge0.
  - exact: bb84_cond_rho_raw_psdmx. } have bb84_cond_rho_tr1 : forall (P : bb84_protocol) (G : bb84_zsource P), 0 < bb84_p_pass_tot G -> \tr (bb84_cond_rho G) = 1.
{ clear G P; move=> P G. move=> Hpass_pos; have Hpass_nz : bb84_p_pass_tot G != 0 := lt0r_neq0 Hpass_pos.
  by rewrite /bb84_cond_rho linearZ /= bb84_cond_rho_raw_trace1 -rmorphM mulVf ?rmorph1. } by move=> Hpass_pos; apply/den1mxP; split; [exact: bb84_cond_rho_psdmx | apply/eqP; exact: bb84_cond_rho_tr1]. Qed.

Fact bb84_cond_rho_zero (P : bb84_protocol) (G : bb84_zsource P) :
  bb84_p_pass_tot G = 0 -> bb84_cond_rho G = 0.
Proof. move=> Hpass0; by rewrite /bb84_cond_rho Hpass0 invr0 scale0r. Qed.

Definition bb84_holdout_pair_mx (n k : nat)
    (z z' : bitstr (k + n)) (pi : 'S_(k + n))
    : 'M[C]_((2 ^ n) * (2 ^ n)) :=
  bb84_pair_projector
    (bitstring_to_ord (@perm_pair_holdout n k z pi))
    (bitstring_to_ord (@perm_pair_holdout n k z' pi)).

Fact bb84_holdout_pair_mx_trace (n k : nat)
    (z z' : bitstr (k + n)) (pi : 'S_(k + n)) :
  \tr (@bb84_holdout_pair_mx n k z z' pi) = 1.
Proof. exact: bb84_pair_projector_trace. Qed.

Definition bb84_rhoZZ_pass_mix (P : bb84_protocol) (G : bb84_zsource P)
    : 'M[C]_((2 ^ bb84_n P) * (2 ^ bb84_n P)) :=
  \sum_(z : 'I_(bb84_full_string_count P))
    \sum_(z' : 'I_(bb84_full_string_count P))
      \sum_(pi : 'S_(bb84_total_rounds P)
          | pi \in @perm_pair_sample_le_event R (bb84_n P) (bb84_k P)
              (ord_to_bitstring z) (ord_to_bitstring z') (bb84_Qtol P))
        ((((bb84_W G z z' * @uniform_perm_mu R (bb84_total_rounds P) pi) /
            bb84_p_pass_tot G)%:C) *:
          @bb84_holdout_pair_mx (bb84_n P) (bb84_k P)
            (ord_to_bitstring z) (ord_to_bitstring z') pi).

Fact bb84_cond_rho_born_consistency
    (P : bb84_protocol) (G : bb84_zsource P) :
  @bb84_holdout_measure_ZZ P G (bb84_cond_rho G) =
  bb84_rhoZZ_pass_mix G.
Proof.
have bb84_rhoZZ_pass_mix_assembleE : forall (P : bb84_protocol) (G : bb84_zsource P), bb84_rhoZZ_pass_mix G = \sum_(pi : 'S_(bb84_total_rounds P)) \sum_(a : 'I_(2 ^ bb84_k P)) \sum_(b : 'I_(2 ^ bb84_k P) | @bb84_sample_pair_passes P a b) \sum_(w : 'I_(2 ^ bb84_n P)) \sum_(w' : 'I_(2 ^ bb84_n P)) ((((bb84_W G (perm_pair_assemble_ord pi (a, w)) (perm_pair_assemble_ord pi (b, w')) * @uniform_perm_mu R (bb84_total_rounds P) pi) / bb84_p_pass_tot G)%:C) *: bb84_pair_projector w w').
{ clear G P; move=> P G. have bb84_rhoZZ_pass_mix_assemble_fixed : forall (P : bb84_protocol) (G : bb84_zsource P) (pi : 'S_(bb84_total_rounds P)), \sum_(z : 'I_(bb84_full_string_count P)) \sum_(z' : 'I_(bb84_full_string_count P) | pi \in @perm_pair_sample_le_event R (bb84_n P) (bb84_k P) (ord_to_bitstring z) (ord_to_bitstring z') (bb84_Qtol P)) ((((bb84_W G z z' * @uniform_perm_mu R (bb84_total_rounds P) pi) / bb84_p_pass_tot G)%:C) *: @bb84_holdout_pair_mx (bb84_n P) (bb84_k P) (ord_to_bitstring z) (ord_to_bitstring z') pi) = \sum_(a : 'I_(2 ^ bb84_k P)) \sum_(b : 'I_(2 ^ bb84_k P) | @bb84_sample_pair_passes P a b) \sum_(w : 'I_(2 ^ bb84_n P)) \sum_(w' : 'I_(2 ^ bb84_n P)) ((((bb84_W G (perm_pair_assemble_ord pi (a, w)) (perm_pair_assemble_ord pi (b, w')) * @uniform_perm_mu R (bb84_total_rounds P) pi) / bb84_p_pass_tot G)%:C) *: bb84_pair_projector w w').
{ clear G P; move=> P G pi. rewrite [LHS](perm_pair_sum_split_ord pi (fun z : 'I_(bb84_full_string_count P) => \sum_(z' : 'I_(bb84_full_string_count P) | pi \in @perm_pair_sample_le_event R (bb84_n P) (bb84_k P) (ord_to_bitstring z) (ord_to_bitstring z') (bb84_Qtol P)) ((((bb84_W G z z' * @uniform_perm_mu R (bb84_total_rounds P) pi) / bb84_p_pass_tot G)%:C) *: @bb84_holdout_pair_mx (bb84_n P) (bb84_k P) (ord_to_bitstring z) (ord_to_bitstring z') pi))).
  apply: eq_bigr => a _; rewrite exchange_big /=; apply: eq_bigr => w _.
  rewrite big_mkcond [LHS]big_mkcond.
  rewrite [LHS](perm_pair_sum_split_ord pi (fun z' : 'I_(bb84_full_string_count P) => if pi \in @perm_pair_sample_le_event R (bb84_n P) (bb84_k P) (ord_to_bitstring (perm_pair_assemble_ord pi (a, w))) (ord_to_bitstring z') (bb84_Qtol P) then ((((bb84_W G (perm_pair_assemble_ord pi (a, w)) z' * @uniform_perm_mu R (bb84_total_rounds P) pi) / bb84_p_pass_tot G)%:C) *: @bb84_holdout_pair_mx (bb84_n P) (bb84_k P) (ord_to_bitstring (perm_pair_assemble_ord pi (a, w))) (ord_to_bitstring z') pi) else 0)).
  rewrite [RHS]big_mkcond; apply: eq_bigr => b _; case Hpass : (@bb84_sample_pair_passes P a b).
  - apply: eq_bigr => w' _; rewrite bb84_sample_pair_passes_assemble_ord Hpass.
    by rewrite /bb84_holdout_pair_mx /perm_pair_assemble_ord !ord_to_bitstringK !perm_pair_holdout_assemble !bitstring_to_ordK.
  - by rewrite big1 // => w' _; rewrite bb84_sample_pair_passes_assemble_ord Hpass. } rewrite /bb84_rhoZZ_pass_mix.
  rewrite (eq_bigr (fun z : 'I_(bb84_full_string_count P) => \sum_(pi : 'S_(bb84_total_rounds P)) \sum_(z' : 'I_(bb84_full_string_count P) | pi \in @perm_pair_sample_le_event R (bb84_n P) (bb84_k P) (ord_to_bitstring z) (ord_to_bitstring z') (bb84_Qtol P)) ((((bb84_W G z z' * @uniform_perm_mu R (bb84_total_rounds P) pi) / bb84_p_pass_tot G)%:C) *: @bb84_holdout_pair_mx (bb84_n P) (bb84_k P) (ord_to_bitstring z) (ord_to_bitstring z') pi))); last first.
  { move=> z _; by rewrite (exchange_big_dep xpredT) //=. } by rewrite exchange_big /=; apply: eq_bigr => pi _; exact: bb84_rhoZZ_pass_mix_assemble_fixed. } have bb84_holdout_measure_ZZ_condE : forall (P : bb84_protocol) (G : bb84_zsource P), @bb84_holdout_measure_ZZ P G (bb84_cond_rho G) = \sum_(w : 'I_(2 ^ bb84_n P)) \sum_(w' : 'I_(2 ^ bb84_n P)) (((bb84_p_pass_tot G)^-1)%:C * \sum_(pi : 'S_(bb84_total_rounds P)) \sum_(a : 'I_(2 ^ bb84_k P)) \sum_(b : 'I_(2 ^ bb84_k P) | @bb84_sample_pair_passes P a b) ((@uniform_perm_mu R (bb84_total_rounds P) pi)%:C * (bb84_W G (bitstring_to_ord (@perm_pair_assemble (bb84_n P) (bb84_k P) pi (ord_to_bitstring a) (ord_to_bitstring w))) (bitstring_to_ord (@perm_pair_assemble (bb84_n P) (bb84_k P) pi (ord_to_bitstring b) (ord_to_bitstring w'))))%:C)) *: bb84_pair_projector w w'.
{ clear G P; move=> P G. have bb84_holdout_measure_ZZ_scale : forall (P : bb84_protocol) (G : bb84_zsource P) (c : C) (rho : 'M[C]_((2 ^ bb84_n P) * bb84_zsrc_nb G * (2 ^ bb84_n P))), @bb84_holdout_measure_ZZ P G (c *: rho) = c *: @bb84_holdout_measure_ZZ P G rho.
{ clear G P; move=> P G c rho. rewrite /bb84_holdout_measure_ZZ scaler_sumr.
  apply: eq_bigr => w _; rewrite scaler_sumr; apply: eq_bigr => w' _.
  by rewrite scalerA; congr (_ *: _); rewrite -scalemxAr linearZ. } have bb84_holdout_measure_ZZ_rawE : forall (P : bb84_protocol) (G : bb84_zsource P), @bb84_holdout_measure_ZZ P G (bb84_cond_rho_raw G) = \sum_(w : 'I_(2 ^ bb84_n P)) \sum_(w' : 'I_(2 ^ bb84_n P)) (\sum_(pi : 'S_(bb84_total_rounds P)) \sum_(a : 'I_(2 ^ bb84_k P)) \sum_(b : 'I_(2 ^ bb84_k P) | @bb84_sample_pair_passes P a b) ((@uniform_perm_mu R (bb84_total_rounds P) pi)%:C * (bb84_W G (bitstring_to_ord (@perm_pair_assemble (bb84_n P) (bb84_k P) pi (ord_to_bitstring a) (ord_to_bitstring w))) (bitstring_to_ord (@perm_pair_assemble (bb84_n P) (bb84_k P) pi (ord_to_bitstring b) (ord_to_bitstring w'))))%:C)) *: bb84_pair_projector w w'.
{ clear G P; move=> P G. have bb84_holdout_projector_kraus_traceW : forall (P : bb84_protocol) (G : bb84_zsource P) (pi : 'S_(bb84_total_rounds P)) (a b : 'I_(2 ^ bb84_k P)) (w w' : 'I_(2 ^ bb84_n P)), \tr (bb84_holdout_projector G w w' *m (bb84_holdout_kraus G pi a b *m bb84_zsrc_rho G *m (bb84_holdout_kraus G pi a b)^*t)) = (bb84_W G (bitstring_to_ord (@perm_pair_assemble (bb84_n P) (bb84_k P) pi (ord_to_bitstring a) (ord_to_bitstring w))) (bitstring_to_ord (@perm_pair_assemble (bb84_n P) (bb84_k P) pi (ord_to_bitstring b) (ord_to_bitstring w'))))%:C.
{ clear G P; move=> P G pi a b w w'. have bb84_holdout_kraus_adjoint_projector_mul : forall (P : bb84_protocol) (G : bb84_zsource P) (pi : 'S_(bb84_total_rounds P)) (a b : 'I_(2 ^ bb84_k P)) (w w' : 'I_(2 ^ bb84_n P)), (bb84_holdout_kraus G pi a b)^*t *m bb84_holdout_projector G w w' *m bb84_holdout_kraus G pi a b = (((delta_mx (bitstring_to_ord (@perm_pair_assemble (bb84_n P) (bb84_k P) pi (ord_to_bitstring a) (ord_to_bitstring w))) (bitstring_to_ord (@perm_pair_assemble (bb84_n P) (bb84_k P) pi (ord_to_bitstring a) (ord_to_bitstring w))) : 'M[C]_(bb84_full_string_count P)) *t (1%:M : 'M[C]_(bb84_zsrc_nb G))) *t (delta_mx (bitstring_to_ord (@perm_pair_assemble (bb84_n P) (bb84_k P) pi (ord_to_bitstring b) (ord_to_bitstring w'))) (bitstring_to_ord (@perm_pair_assemble (bb84_n P) (bb84_k P) pi (ord_to_bitstring b) (ord_to_bitstring w'))) : 'M[C]_(bb84_full_string_count P))).
{ clear w' w b a pi G P; move=> P G pi a b w w'. have bb84_holdout_iso_adjoint_projector_mul : forall (n k : nat) (pi : 'S_(k + n)) (sample : bitstr k) (w : 'I_(2 ^ n)), (bb84_holdout_iso pi sample)^*t *m (delta_mx w w : 'M[C]_(2 ^ n)) *m bb84_holdout_iso pi sample = delta_mx (bitstring_to_ord (@perm_pair_assemble n k pi sample (ord_to_bitstring w))) (bitstring_to_ord (@perm_pair_assemble n k pi sample (ord_to_bitstring w))).
{ clear w' w b a pi G P; move=> n k pi sample w; apply/matrixP => x y.
  rewrite !mxE (bigD1 w) //= big1 ?addr0; last first.
  { move=> i Hiw; rewrite mxE (bigD1 w) //=.
    rewrite big1 ?addr0; last first.
    { move=> j Hjw; rewrite !mxE.
      case HiwE : (i == w); first by move: Hiw; rewrite HiwE.
      case HwiE : (w == i); first by move: Hiw; rewrite eq_sym HwiE.
      case HjwE : (j == w); first by move: Hjw; rewrite HjwE.
      case HwjE : (w == j); first by move: Hjw; rewrite eq_sym HwjE.
      by rewrite ?mxE ?HiwE ?HwiE ?HjwE ?HwjE /= ?mulr0 ?mul0r ?mulr1 ?mul1r ?conjC0 ?addr0 ?add0r. }
have Hwi : w != i by rewrite eq_sym.
    rewrite !mxE.
    case HiwE : (i == w); first by move: Hiw; rewrite HiwE.
    case HwiE : (w == i); first by move: Hiw; rewrite eq_sym HwiE.
    by rewrite ?mxE ?HiwE ?HwiE /= ?mulr0 ?mul0r ?mulr1 ?mul1r ?conjC0 ?addr0 ?add0r ?eqxx ?andbF ?mulr0n ?mulr1n mulr0 mul0r. }
rewrite mxE (bigD1 w) //= big1 ?addr0; last first.
  { move=> j Hjw; have Hwj : w != j by rewrite eq_sym.
    rewrite !mxE.
    case HjwE : (j == w); first by move: Hjw; rewrite HjwE.
    case HwjE : (w == j); first by move: Hjw; rewrite eq_sym HwjE.
    by rewrite ?mxE ?HjwE ?HwjE /= ?mulr0 ?mul0r ?mulr1 ?mul1r ?conjC0 ?addr0 ?add0r ?eqxx ?andbF ?mulr0n ?mulr1n ?mulr0 ?mul0r. }
rewrite !mxE ?eqxx ?mulr1 ?mulr1n (@bb84_holdout_isoE n k pi sample w x) (@bb84_holdout_isoE n k pi sample w y).
  by case: (x == bitstring_to_ord (@perm_pair_assemble n k pi sample (ord_to_bitstring w))); case: (y == bitstring_to_ord (@perm_pair_assemble n k pi sample (ord_to_bitstring w))); rewrite /= ?conjC0 ?conjC1 ?mul0r ?mulr0 ?mul1r ?mulr0n ?mulr1n. } by rewrite /bb84_holdout_kraus /bb84_holdout_projector !adjmx_tens adjmx1 !tensmx3_mul !bb84_holdout_iso_adjoint_projector_mul !mul1mx. } by rewrite !mulmxA [LHS]mxtrace_mulC -!mulmxA !mulmxA bb84_holdout_kraus_adjoint_projector_mul; exact: bb84_W_traceE. } rewrite /bb84_holdout_measure_ZZ.
  apply: eq_bigr => w _; apply: eq_bigr => w' _; congr (_ *: _).
  rewrite /bb84_cond_rho_raw mulmx_sumr linear_sum; apply: eq_bigr => pi _; rewrite mulmx_sumr linear_sum; apply: eq_bigr => a _.
  rewrite mulmx_sumr linear_sum; apply: eq_bigr => b _.
  by rewrite -scalemxAr linearZ /=; congr (_ * _); exact: bb84_holdout_projector_kraus_traceW. } rewrite /bb84_cond_rho bb84_holdout_measure_ZZ_scale bb84_holdout_measure_ZZ_rawE scaler_sumr.
  by apply: eq_bigr => w _; rewrite scaler_sumr; apply: eq_bigr => w' _; rewrite scalerA. } rewrite bb84_holdout_measure_ZZ_condE bb84_rhoZZ_pass_mix_assembleE.
  rewrite [LHS](eq_bigr (fun w : 'I_(2 ^ bb84_n P) => \sum_(w' : 'I_(2 ^ bb84_n P)) \sum_(pi : 'S_(bb84_total_rounds P)) \sum_(a : 'I_(2 ^ bb84_k P)) \sum_(b : 'I_(2 ^ bb84_k P) | @bb84_sample_pair_passes P a b) ((((bb84_W G (perm_pair_assemble_ord pi (a, w)) (perm_pair_assemble_ord pi (b, w')) * @uniform_perm_mu R (bb84_total_rounds P) pi) / bb84_p_pass_tot G)%:C) *: bb84_pair_projector w w'))); last first.
  { move=> w _; apply: eq_bigr => w' _; rewrite mulr_sumr scaler_suml; apply: eq_bigr => pi _.
    rewrite mulr_sumr scaler_suml; apply: eq_bigr => a _; rewrite mulr_sumr scaler_suml; apply: eq_bigr => b _.
    congr (_ *: _); rewrite -!rmorphM /=; congr (_%:C).
    by rewrite mulrC [@uniform_perm_mu R (bb84_total_rounds P) pi * _]mulrC. }
under eq_bigr => w _ do rewrite exchange_big /=.
  rewrite exchange_big /=; apply: eq_bigr => pi _.
  under eq_bigr => w _ do rewrite exchange_big /=.
  rewrite exchange_big /=; apply: eq_bigr => a _.
  under eq_bigr => w _ do rewrite (exchange_big_dep xpredT) //=.
  rewrite (exchange_big_dep xpredT) //= [RHS]big_mkcond.
  apply: eq_bigr => b _; case Hpass : (@bb84_sample_pair_passes P a b); first by [].
  by apply: big1 => w _; rewrite big_pred0. Qed.

Fact bb84_rhoZZ_pass_mix_tr1 (P : bb84_protocol) (G : bb84_zsource P) :
  0 < bb84_p_pass_tot G -> @complex.Re R (\tr (bb84_rhoZZ_pass_mix G)) = 1.
Proof.
  move=> Hpass_pos; have Hpass_nz : bb84_p_pass_tot G != 0 := lt0r_neq0 Hpass_pos.
  have Hpass_unit : bb84_p_pass_tot G \is a GRing.unit by rewrite unitfE.
  have HtraceE : \tr (bb84_rhoZZ_pass_mix G) = (\sum_(z : 'I_(bb84_full_string_count P)) \sum_(z' : 'I_(bb84_full_string_count P)) \sum_(pi : 'S_(bb84_total_rounds P) | pi \in @perm_pair_sample_le_event R (bb84_n P) (bb84_k P) (ord_to_bitstring z) (ord_to_bitstring z') (bb84_Qtol P)) ((bb84_W G z z' * @uniform_perm_mu R (bb84_total_rounds P) pi) / bb84_p_pass_tot G))%:C.
  { rewrite /bb84_rhoZZ_pass_mix linear_sum [RHS]rmorph_sum; apply: eq_bigr => z _; rewrite linear_sum [RHS]rmorph_sum.
    apply: eq_bigr => z' _; rewrite linear_sum [RHS]rmorph_sum; apply: eq_bigr => pi _.
    rewrite linearZ /bb84_holdout_pair_mx.
    have Htr_pair : \tr (((delta_mx (bitstring_to_ord (@perm_pair_holdout (bb84_n P) (bb84_k P) (ord_to_bitstring z) pi)) (bitstring_to_ord (@perm_pair_holdout (bb84_n P) (bb84_k P) (ord_to_bitstring z) pi)) : 'M[C]_(2 ^ bb84_n P)) *t (delta_mx (bitstring_to_ord (@perm_pair_holdout (bb84_n P) (bb84_k P) (ord_to_bitstring z') pi)) (bitstring_to_ord (@perm_pair_holdout (bb84_n P) (bb84_k P) (ord_to_bitstring z') pi)) : 'M[C]_(2 ^ bb84_n P)))) = 1.
    { by rewrite mxtrace_tens !mxtrace_delta !eqxx mul1r. } by rewrite -[RHS]mulr1; congr (_ * _); exact: Htr_pair. }
rewrite HtraceE re_realid.
  have Hnum : \sum_(z : 'I_(bb84_full_string_count P)) \sum_(z' : 'I_(bb84_full_string_count P)) \sum_(pi : 'S_(bb84_total_rounds P) | pi \in @perm_pair_sample_le_event R (bb84_n P) (bb84_k P) (ord_to_bitstring z) (ord_to_bitstring z') (bb84_Qtol P)) (bb84_W G z z' * @uniform_perm_mu R (bb84_total_rounds P) pi) = bb84_p_pass_tot G.
  { rewrite /bb84_p_pass_tot /bb84_p_pass_pair /perm_pair_sample_le_prob /Pr_event.
    by apply: eq_bigr => z _; apply: eq_bigr => z' _; rewrite mulr_sumr. } apply: (mulIf Hpass_nz); rewrite mulr_suml mul1r.
  rewrite (eq_bigr (fun z : 'I_(bb84_full_string_count P) => \sum_(z' : 'I_(bb84_full_string_count P)) \sum_(pi : 'S_(bb84_total_rounds P) | pi \in @perm_pair_sample_le_event R (bb84_n P) (bb84_k P) (ord_to_bitstring z) (ord_to_bitstring z') (bb84_Qtol P)) (bb84_W G z z' * @uniform_perm_mu R (bb84_total_rounds P) pi))); last first.
  { move=> z _; rewrite mulr_suml; apply: eq_bigr => z' _.
    by rewrite mulr_suml; apply: eq_bigr => pi _; exact: divrK Hpass_unit _. } by rewrite Hnum. Qed.

Fact bb84_good_projector_pass_mass
    (P : bb84_protocol) (G : bb84_zsource P) (eps : R) :
  (0 < bb84_n P)%N -> 0 < bb84_p_pass_tot G -> let delta := bb84_Qtol P + bb84_mu (bb84_n P) (bb84_k P) eps in
  1 - bb84_pass_bad_weight G eps / bb84_p_pass_tot G <=
  @complex.Re R
    (\tr (@bb84_good_projector (bb84_n P) delta *m
      bb84_rhoZZ_pass_mix G *m @bb84_good_projector (bb84_n P) delta)).
Proof.
  move=> Hn_pos Hpass_pos /=; pose delta := bb84_Qtol P + bb84_mu (bb84_n P) (bb84_k P) eps.
  remember (@bb84_good_projector (bb84_n P) delta) as Pgood eqn:HPgoodE.
  have Hpass_nz : bb84_p_pass_tot G != 0 := lt0r_neq0 Hpass_pos.
  have Hpass_unit : bb84_p_pass_tot G \is a GRing.unit by rewrite unitfE.
  pose pass_event (z z' : 'I_(bb84_full_string_count P)) := @perm_pair_sample_le_event R (bb84_n P) (bb84_k P) (ord_to_bitstring z) (ord_to_bitstring z') (bb84_Qtol P).
  pose bad_event (z z' : 'I_(bb84_full_string_count P)) := @perm_pair_deviation_event R (bb84_n P) (bb84_k P) (ord_to_bitstring z) (ord_to_bitstring z') (bb84_mu (bb84_n P) (bb84_k P) eps).
  pose coeff (z z' : 'I_(bb84_full_string_count P)) (pi : 'S_(bb84_total_rounds P)) := (bb84_W G z z' * @uniform_perm_mu R (bb84_total_rounds P) pi) / bb84_p_pass_tot G.
  pose holdout_good (z z' : 'I_(bb84_full_string_count P)) (pi : 'S_(bb84_total_rounds P)) := @relative_hamming_ball R (bb84_n P) delta (bitstring_to_ord (@perm_pair_holdout (bb84_n P) (bb84_k P) (ord_to_bitstring z) pi)) (bitstring_to_ord (@perm_pair_holdout (bb84_n P) (bb84_k P) (ord_to_bitstring z') pi)).
  have Hgood_of_pass_not_bad (z z' : 'I_(bb84_full_string_count P)) (pi : 'S_(bb84_total_rounds P)) : pi \in pass_event z z' -> pi \notin bad_event z z' -> holdout_good z z' pi.
  { move=> Hpass Hnotbad. have Hsample : @perm_pair_sample_err R (bb84_n P) (bb84_k P) (ord_to_bitstring z) (ord_to_bitstring z') pi <= bb84_Qtol P. { move: Hpass; by rewrite /pass_event /perm_pair_sample_le_event !inE. } have Hholdout_sample : @perm_pair_holdout_err R (bb84_n P) (bb84_k P) (ord_to_bitstring z) (ord_to_bitstring z') pi < @perm_pair_sample_err R (bb84_n P) (bb84_k P) (ord_to_bitstring z) (ord_to_bitstring z') pi + bb84_mu (bb84_n P) (bb84_k P) eps. { move: Hnotbad; by rewrite /bad_event /perm_pair_deviation_event !inE ltNge. } have Hholdout_delta : @perm_pair_holdout_err R (bb84_n P) (bb84_k P) (ord_to_bitstring z) (ord_to_bitstring z') pi < delta. { apply: (lt_le_trans Hholdout_sample). by rewrite /delta lerD2r. } rewrite /holdout_good /relative_hamming_ball /perm_pair_holdout_err. by rewrite !ord_to_bitstringK. } have Hcoeff_ge0 (z z' : 'I_(bb84_full_string_count P)) (pi : 'S_(bb84_total_rounds P)) : 0 <= coeff z z' pi.
  { rewrite /coeff; apply: divr_ge0; last exact: ltW Hpass_pos.
    by apply: mulr_ge0; [exact: bb84_W_ge0 | exact: uniform_perm_mu_nonneg]. } have HtraceE : \tr (Pgood *m bb84_rhoZZ_pass_mix G *m Pgood) = (\sum_(z : 'I_(bb84_full_string_count P)) \sum_(z' : 'I_(bb84_full_string_count P)) \sum_(pi : 'S_(bb84_total_rounds P) | pi \in pass_event z z') (if holdout_good z z' pi then coeff z z' pi else 0))%:C.
  { rewrite /bb84_rhoZZ_pass_mix -mulmxA mulmx_suml mulmx_sumr linear_sum [RHS]rmorph_sum; apply: eq_bigr => z _.
    rewrite mulmx_suml mulmx_sumr linear_sum [RHS]rmorph_sum; apply: eq_bigr => z' _.
    rewrite mulmx_suml mulmx_sumr linear_sum [RHS]rmorph_sum; apply: eq_bigr => pi Hpi.
    rewrite -scalemxAl linearZ HPgoodE /bb84_holdout_pair_mx /holdout_good bb84_pair_projector_mul_good_projector.
    case Hgood : (@relative_hamming_ball R (bb84_n P) delta (bitstring_to_ord (@perm_pair_holdout (bb84_n P) (bb84_k P) (ord_to_bitstring z) pi)) (bitstring_to_ord (@perm_pair_holdout (bb84_n P) (bb84_k P) (ord_to_bitstring z') pi))).
    - set hx := bitstring_to_ord (@perm_pair_holdout (bb84_n P) (bb84_k P) (ord_to_bitstring z) pi).
      set hy := bitstring_to_ord (@perm_pair_holdout (bb84_n P) (bb84_k P) (ord_to_bitstring z') pi).
      have Hleft : @bb84_good_projector (bb84_n P) delta *m @bb84_pair_projector (bb84_n P) hx hy = @bb84_pair_projector (bb84_n P) hx hy.
      { by rewrite bb84_good_projector_mul_pair_projector Hgood. } change (\tr (((coeff z z' pi)%:C) *: (@bb84_good_projector (bb84_n P) delta *m @bb84_pair_projector (bb84_n P) hx hy)) = (coeff z z' pi)%:C).
      rewrite Hleft linearZ.
      change ((coeff z z' pi)%:C * \tr (@bb84_pair_projector (bb84_n P) hx hy) = (coeff z z' pi)%:C).
      by rewrite bb84_pair_projector_trace mulr1 /coeff.
    - change (\tr (((coeff z z' pi)%:C) *: (@bb84_good_projector (bb84_n P) delta *m (0 : 'M[C]_((2 ^ bb84_n P) * (2 ^ bb84_n P))))) = 0).
      by rewrite mulmx0 scaler0 mxtrace0. }
pose nonbad_mass := \sum_(z : 'I_(bb84_full_string_count P)) \sum_(z' : 'I_(bb84_full_string_count P)) \sum_(pi : 'S_(bb84_total_rounds P) | (pi \in pass_event z z') && (pi \notin bad_event z z')) coeff z z' pi.
  have Hnonbad_le_trace : nonbad_mass <= @complex.Re R (\tr (Pgood *m bb84_rhoZZ_pass_mix G *m Pgood)).
  { rewrite HtraceE re_realid /nonbad_mass; apply: ler_sum => z _; apply: ler_sum => z' _.
    rewrite [X in _ <= X](bigID (fun pi => pi \notin bad_event z z')) /= -[leLHS]addr0.
    apply: lerD.
    - apply: ler_sum => pi /andP [Hpass Hnotbad]; rewrite (Hgood_of_pass_not_bad z z' pi Hpass Hnotbad); exact: lexx.
    - apply: sumr_ge0 => pi _; case: ifP => _; [exact: Hcoeff_ge0 | exact: lexx]. }
have HnonbadE : nonbad_mass = 1 - bb84_pass_bad_weight G eps / bb84_p_pass_tot G.
  { apply: (mulIf Hpass_nz); rewrite [RHS]mulrBl mul1r divfK //.
    rewrite /nonbad_mass /coeff /bb84_pass_bad_weight /bb84_p_pass_tot /bb84_p_pass_pair /perm_pair_sample_le_prob /Pr_event /pass_event /bad_event mulr_suml.
    rewrite (eq_bigr (fun z : 'I_(bb84_full_string_count P) => \sum_(z' : 'I_(bb84_full_string_count P)) \sum_(pi : 'S_(bb84_total_rounds P) | (pi \in @perm_pair_sample_le_event R (bb84_n P) (bb84_k P) (ord_to_bitstring z) (ord_to_bitstring z') (bb84_Qtol P)) && (pi \notin @perm_pair_deviation_event R (bb84_n P) (bb84_k P) (ord_to_bitstring z) (ord_to_bitstring z') (bb84_mu (bb84_n P) (bb84_k P) eps))) (bb84_W G z z' * @uniform_perm_mu R (bb84_total_rounds P) pi))); last first.
    { move=> z _; rewrite mulr_suml; apply: eq_bigr => z' _.
      by rewrite mulr_suml; apply: eq_bigr => pi _; rewrite divrK. } rewrite -sumrB; apply: eq_bigr => z _; rewrite -sumrB; apply: eq_bigr => z' _.
    rewrite mulr_sumr mulr_sumr.
    rewrite [X in _ - X](eq_bigl (fun pi : 'S_(bb84_total_rounds P) => (pi \in @perm_pair_sample_le_event R (bb84_n P) (bb84_k P) (ord_to_bitstring z) (ord_to_bitstring z') (bb84_Qtol P)) && (pi \in @perm_pair_deviation_event R (bb84_n P) (bb84_k P) (ord_to_bitstring z) (ord_to_bitstring z') (bb84_mu (bb84_n P) (bb84_k P) eps)))).
    - rewrite [X in _ = X - _](bigID (fun pi : 'S_(bb84_total_rounds P) => pi \in @perm_pair_deviation_event R (bb84_n P) (bb84_k P) (ord_to_bitstring z) (ord_to_bitstring z') (bb84_mu (bb84_n P) (bb84_k P) eps))) /=.
      by rewrite addrC addrK.
    - by move=> pi; rewrite !inE andbC. }
by rewrite -HnonbadE -HPgoodE; exact: Hnonbad_le_trace. Qed.

Fact bb84_p_pass_mem_pos (P : bb84_protocol) (s : bb84_sample P)
    (pi : 'S_(bb84_k P + bb84_n P)) :
  pi \in bb84_pass_event s -> 0 < bb84_p_pass s.
Proof. move=> Hpi; rewrite /bb84_pass_event in Hpi. apply: (lt_le_trans (@uniform_perm_mu_pos R (bb84_k P + bb84_n P) pi)). rewrite /bb84_p_pass /perm_pair_sample_le_prob /Pr_event (bigD1 pi) //= lerDl. by apply: sumr_ge0 => pi' _; exact: uniform_perm_mu_nonneg. Qed.

Fact bb84_p_pass_uniform_fraction (P : bb84_protocol) (s : bb84_sample P) :
  bb84_p_pass s =
  #|bb84_pass_event s|%:R * (#|{: 'S_(bb84_k P + bb84_n P)}|%:R)^-1.
Proof. rewrite /bb84_p_pass /perm_pair_sample_le_prob /bb84_pass_event /perm_pair_sample_le_event; exact: Pr_event_uniform_fin. Qed.

Definition bb84_pass_prob (p_abort p_pass : R) : Prop :=
  0 <= p_abort /\ p_abort <= 1 /\ 1 - p_abort = p_pass.

Fact bb84_pass_prob_leP p_abort p_pass :
  bb84_pass_prob p_abort p_pass -> bb84_pass_prob_le p_abort p_pass.
Proof. move=> [Habort_ge0 [Habort_le1 HpassE]]. split=> //; split=> //. by rewrite HpassE. Qed.

Fact bb84_pass_prob_le_abort_ge0 p_abort p_pass :
  bb84_pass_prob_le p_abort p_pass -> 0 <= p_abort.
Proof. by case. Qed.

Fact bb84_pass_prob_le_abort_le1 p_abort p_pass :
  bb84_pass_prob_le p_abort p_pass -> p_abort <= 1.
Proof. by case=> _ []. Qed.

Lemma bb84_pass_prob_le_bound p_abort p_pass :
  bb84_pass_prob_le p_abort p_pass -> 1 - p_abort <= p_pass.
Proof. by case=> _ [_]. Qed.

Fact bb84_pass_pos p_abort p_pass :
  bb84_pass_prob p_abort p_pass -> 0 <= p_pass.
Proof. by move=> [Ha [Hb <-]]; rewrite subr_ge0. Qed.

Fact bb84_abort_ge0 p_abort p_pass :
  bb84_pass_prob p_abort p_pass -> 0 <= p_abort.
Proof. by case. Qed.

Fact bb84_abort_le1 p_abort p_pass :
  bb84_pass_prob p_abort p_pass -> p_abort <= 1.
Proof. by case=> _ []. Qed.

Fact bb84_pass_abort_bound p_abort p_pass :
  bb84_pass_prob p_abort p_pass -> 1 - p_abort <= p_pass.
Proof. by move=> [_ [_ <-]]; apply: lexx. Qed.

Definition bb84_rhoZZ_pass (P : bb84_protocol) (s : bb84_sample P)
    : 'M[C]_((2 ^ bb84_n P) * (2 ^ bb84_n P)) :=
  let z := bb84_sample_alice s in
  let z' := bb84_sample_bob s in
  \sum_(pi : 'S_(bb84_k P + bb84_n P)
       | pi \in @perm_pair_sample_le_event R (bb84_n P) (bb84_k P) z z' (bb84_Qtol P))
    ((((@uniform_perm_mu R (bb84_k P + bb84_n P) pi /
       Pr_event (fun pi : 'S_(bb84_k P + bb84_n P) =>
                   @uniform_perm_mu R (bb84_k P + bb84_n P) pi)
         (@perm_pair_sample_le_event R (bb84_n P) (bb84_k P) z z' (bb84_Qtol P)))%:C) *:
     ((delta_mx
         (bitstring_to_ord (@perm_pair_holdout (bb84_n P) (bb84_k P) z pi))
         (bitstring_to_ord (@perm_pair_holdout (bb84_n P) (bb84_k P) z pi))
       : 'M[C]_(2 ^ bb84_n P))
      *t
      (delta_mx
         (bitstring_to_ord (@perm_pair_holdout (bb84_n P) (bb84_k P) z' pi))
         (bitstring_to_ord (@perm_pair_holdout (bb84_n P) (bb84_k P) z' pi))
       : 'M[C]_(2 ^ bb84_n P))))).

Section LabelledPassState.
Variable (L : finType) (HL : L -> chsType).
Variables (Zkey Zp : {set L}).
Hypothesis disZZp : [disjoint Zkey & Zp].

Definition bb84_rhoZZ_passH (P : bb84_protocol) (s : bb84_sample P)
    (dim_Zk : (2 ^ bb84_n P)%N = dim ('H[HL]_Zkey))
    (dim_Zp : (2 ^ bb84_n P)%N = dim ('H[HL]_Zp))
    : 'F[HL]_(Zkey :|: Zp) :=
  @biprod_of_mx R _ HL Zkey Zp disZZp
    (castmx (f_equal2 muln dim_Zk dim_Zp, f_equal2 muln dim_Zk dim_Zp)
      (bb84_rhoZZ_pass s)).

Definition bb84_rhoZZ_pass_mixH (P : bb84_protocol) (G : bb84_zsource P)
    (dim_Zk : (2 ^ bb84_n P)%N = dim ('H[HL]_Zkey))
    (dim_Zp : (2 ^ bb84_n P)%N = dim ('H[HL]_Zp))
    : 'F[HL]_(Zkey :|: Zp) :=
  @biprod_of_mx R _ HL Zkey Zp disZZp
    (castmx (f_equal2 muln dim_Zk dim_Zp, f_equal2 muln dim_Zk dim_Zp)
      (bb84_rhoZZ_pass_mix G)).

Lemma delta_mx_psdmx n (i : 'I_n) : @delta_mx C n n i i \is psdmx.
Proof. suff -> : @delta_mx C n n i i = @delta_mx C n 1 i ord0 *m (@delta_mx C n 1 i ord0)^*t by exact: form_psd. apply/matrixP => a b; rewrite !mxE big_ord1 !mxE conjC_nat /=. by case: eqP => _; case: eqP => _ //=; rewrite ?mulr1 ?mulr0 ?mul0r. Qed.

Fact bb84_rhoZZ_pass_mix_psdmx (P : bb84_protocol) (G : bb84_zsource P) :
  0 < bb84_p_pass_tot G -> bb84_rhoZZ_pass_mix G \is psdmx.
Proof.
have bb84_holdout_pair_mx_psdmx : forall (n k : nat) (z z' : bitstr (k + n)) (pi : 'S_(k + n)), @bb84_holdout_pair_mx n k z z' pi \is psdmx.
{ clear G P; move=> n k z z' pi. rewrite /bb84_holdout_pair_mx. exact: psdmx_tens (delta_mx_psdmx _) (delta_mx_psdmx _). } move=> Hpass_pos; rewrite /bb84_rhoZZ_pass_mix.
  apply/psdmx_sum => z _; apply/psdmx_sum => z' _; apply/psdmx_sum => pi _.
  apply: psdmxZ; last exact: bb84_holdout_pair_mx_psdmx.
  rewrite lecR; apply: divr_ge0; last exact: ltW Hpass_pos.
  by apply: mulr_ge0; [exact: bb84_W_ge0 | exact: uniform_perm_mu_nonneg]. Qed.

Lemma bb84_rhoZZ_passH_psd (P : bb84_protocol) (s : bb84_sample P)
    (dim_Zk : (2 ^ bb84_n P)%N = dim ('H[HL]_Zkey))
    (dim_Zp : (2 ^ bb84_n P)%N = dim ('H[HL]_Zp)) :
  bb84_rhoZZ_passH s dim_Zk dim_Zp \is psdlf.
Proof.
  have bb84_rhoZZ_pass_psdmx : forall (s0 : bb84_sample P), bb84_rhoZZ_pass s0 \is psdmx.
  { move=> s0; rewrite /bb84_rhoZZ_pass; apply/psdmx_sum => pi _.
    apply: psdmxZ; last exact: psdmx_tens (delta_mx_psdmx _) (delta_mx_psdmx _).
    rewrite lec0R divr_ge0 // ?uniform_perm_mu_nonneg //.
    rewrite /Pr_event; apply: sumr_ge0 => i _; exact: uniform_perm_mu_nonneg. } by apply: (@biprod_of_mx_psd R _ HL Zkey Zp disZZp); exact: castmx_sq_psdmx (bb84_rhoZZ_pass_psdmx s). Qed.

Fact bb84_rhoZZ_pass_mixH_psd (P : bb84_protocol) (G : bb84_zsource P)
    (dim_Zk : (2 ^ bb84_n P)%N = dim ('H[HL]_Zkey))
    (dim_Zp : (2 ^ bb84_n P)%N = dim ('H[HL]_Zp)) :
  0 < bb84_p_pass_tot G -> bb84_rhoZZ_pass_mixH G dim_Zk dim_Zp \is psdlf.
Proof. by move=> Hpass_pos; apply: (@biprod_of_mx_psd R _ HL Zkey Zp disZZp); exact: castmx_sq_psdmx (bb84_rhoZZ_pass_mix_psdmx Hpass_pos). Qed.

Fact bb84_rhoZZ_passH_biprod (P : bb84_protocol) (s : bb84_sample P)
    (dim_Zk : (2 ^ bb84_n P)%N = dim ('H[HL]_Zkey))
    (dim_Zp : (2 ^ bb84_n P)%N = dim ('H[HL]_Zp)) :
  biprod_mx disZZp (bb84_rhoZZ_passH s dim_Zk dim_Zp) =
  castmx (f_equal2 muln dim_Zk dim_Zp, f_equal2 muln dim_Zk dim_Zp)
    (bb84_rhoZZ_pass s).
Proof. exact: (@biprod_mxK R _ HL Zkey Zp disZZp). Qed.

Fact bb84_rhoZZ_pass_mixH_biprod
    (P : bb84_protocol) (G : bb84_zsource P)
    (dim_Zk : (2 ^ bb84_n P)%N = dim ('H[HL]_Zkey))
    (dim_Zp : (2 ^ bb84_n P)%N = dim ('H[HL]_Zp)) :
  biprod_mx disZZp (bb84_rhoZZ_pass_mixH G dim_Zk dim_Zp) =
  castmx (f_equal2 muln dim_Zk dim_Zp, f_equal2 muln dim_Zk dim_Zp)
    (bb84_rhoZZ_pass_mix G).
Proof. exact: (@biprod_mxK R _ HL Zkey Zp disZZp). Qed.

End LabelledPassState.

Record bb84_source_model (P : bb84_protocol) (q : R) := BB84SourceModel { bb84_src_na : nat; bb84_src_nb : nat; bb84_src_nc : nat; bb84_src_nx : nat; bb84_src_nz : nat; bb84_src_rho : 'M[C]_(bb84_src_na * bb84_src_nb * bb84_src_nc); bb84_src_M : 'I_bb84_src_nx -> 'M[C]_bb84_src_na; bb84_src_N : 'I_bb84_src_nz -> 'M[C]_bb84_src_na; bb84_src_den1 : bb84_src_rho \is den1mx; bb84_src_M_povm : is_povm_mx bb84_src_M; bb84_src_N_povm : is_povm_mx bb84_src_N; bb84_src_overlap_quality : (bb84_n P)%:R * q <= q_of_mx bb84_src_M bb84_src_N; bb84_src_dim_Z : bb84_src_nz = (2 ^ bb84_n P)%N; bb84_src_dim_B : bb84_src_nc = (2 ^ bb84_n P)%N; }.

Record bb84_pm_source (P : bb84_protocol) := BB84PMSource { pm_states_X : 'I_(2 ^ bb84_n P) -> 'cV[C]_2; pm_states_Z : 'I_(2 ^ bb84_n P) -> 'cV[C]_2; }.

Definition pm_povm_X (P : bb84_protocol) (s : bb84_pm_source P)
    (x : 'I_(2 ^ bb84_n P)) : 'M[C]_2 :=
  pm_states_X s x *m (pm_states_X s x)^*t.

Definition pm_povm_Z (P : bb84_protocol) (s : bb84_pm_source P)
    (z : 'I_(2 ^ bb84_n P)) : 'M[C]_2 :=
  pm_states_Z s z *m (pm_states_Z s z)^*t.

Definition pm_to_source_model (P : bb84_protocol) (q : R)
    (s : bb84_pm_source P)
    (nb nc : nat)
    (rho_post_channel : 'M[C]_(2 * nb * nc))
    (Hden1 : rho_post_channel \is den1mx)
    (Hpovm_X : is_povm_mx (pm_povm_X s))
    (Hpovm_Z : is_povm_mx (pm_povm_Z s))
    (Hquality : (bb84_n P)%:R * q <=
      q_of_mx (pm_povm_X s) (pm_povm_Z s))
    (Hdim_Z : (2 ^ bb84_n P)%N = (2 ^ bb84_n P)%N)
    (Hdim_B : nc = (2 ^ bb84_n P)%N)
    : bb84_source_model P q :=
  {| bb84_src_na := 2; bb84_src_nb := nb; bb84_src_nc := nc;
     bb84_src_nx := 2 ^ bb84_n P; bb84_src_nz := 2 ^ bb84_n P;
     bb84_src_rho := rho_post_channel;
     bb84_src_M := pm_povm_X s; bb84_src_N := pm_povm_Z s;
     bb84_src_den1 := Hden1;
     bb84_src_M_povm := Hpovm_X; bb84_src_N_povm := Hpovm_Z;
     bb84_src_overlap_quality := Hquality;
     bb84_src_dim_Z := Hdim_Z; bb84_src_dim_B := Hdim_B |}.

Fact pm_povm_psd (P : bb84_protocol) (s : bb84_pm_source P)
    (x : 'I_(2 ^ bb84_n P)) :
  pm_povm_X s x \is psdmx.
Proof. exact: form_psd. Qed.

Fact pm_povm_Z_psd (P : bb84_protocol) (s : bb84_pm_source P)
    (z : 'I_(2 ^ bb84_n P)) :
  pm_povm_Z s z \is psdmx.
Proof. exact: form_psd. Qed.

Definition pm_source_model (P : bb84_protocol) (q : R)
    (s : bb84_pm_source P)
    (nb nc : nat)
    (rho_post_channel : 'M[C]_(2 * nb * nc))
    (Hden1 : rho_post_channel \is den1mx)
    (Honb_X : \sum_(x < 2 ^ bb84_n P) pm_povm_X s x = 1%:M)
    (Honb_Z : \sum_(z < 2 ^ bb84_n P) pm_povm_Z s z = 1%:M)
    (Hquality : (bb84_n P)%:R * q <=
      q_of_mx (pm_povm_X s) (pm_povm_Z s))
    (Hdim_B : nc = (2 ^ bb84_n P)%N)
    : bb84_source_model P q.
Proof.
  refine {| bb84_src_na := 2; bb84_src_nb := nb; bb84_src_nc := nc; bb84_src_nx := 2 ^ bb84_n P; bb84_src_nz := 2 ^ bb84_n P; bb84_src_rho := rho_post_channel; bb84_src_M := pm_povm_X s; bb84_src_N := pm_povm_Z s; bb84_src_den1 := Hden1; bb84_src_overlap_quality := Hquality; bb84_src_dim_Z := erefl; bb84_src_dim_B := Hdim_B |}.
  - apply/is_povm_mxP; split; [exact: pm_povm_psd | exact: Honb_X].
  - apply/is_povm_mxP; split; [exact: pm_povm_Z_psd | exact: Honb_Z]. Defined.

Definition eb_source_model (P : bb84_protocol) (q : R)
    (na nb nc nx nz : nat)
    (rho : 'M[C]_(na * nb * nc))
    (M : 'I_nx -> 'M[C]_na) (N : 'I_nz -> 'M[C]_na)
    (Hden1 : rho \is den1mx)
    (HM_povm : is_povm_mx M) (HN_povm : is_povm_mx N)
    (Hquality : (bb84_n P)%:R * q <= q_of_mx M N)
    (Hdim_Z : nz = (2 ^ bb84_n P)%N)
    (Hdim_B : nc = (2 ^ bb84_n P)%N)
    : bb84_source_model P q :=
  {| bb84_src_rho := rho; bb84_src_M := M; bb84_src_N := N;
     bb84_src_den1 := Hden1;
     bb84_src_M_povm := HM_povm; bb84_src_N_povm := HN_povm;
     bb84_src_overlap_quality := Hquality;
     bb84_src_dim_Z := Hdim_Z; bb84_src_dim_B := Hdim_B |}.

Definition bb84_src_with_rho (P : bb84_protocol) (q : R)
    (s : bb84_source_model P q)
    (r : 'M[C]_(bb84_src_na s * bb84_src_nb s * bb84_src_nc s))
    (rden1 : r \is den1mx)
    : bb84_source_model P q :=
  {| bb84_src_na := bb84_src_na s;
     bb84_src_nb := bb84_src_nb s;
     bb84_src_nc := bb84_src_nc s;
     bb84_src_nx := bb84_src_nx s;
     bb84_src_nz := bb84_src_nz s;
     bb84_src_rho := r;
     bb84_src_M := @bb84_src_M P q s;
     bb84_src_N := @bb84_src_N P q s;
     bb84_src_den1 := rden1;
     bb84_src_M_povm := @bb84_src_M_povm P q s;
     bb84_src_N_povm := @bb84_src_N_povm P q s;
     bb84_src_overlap_quality := @bb84_src_overlap_quality P q s;
     bb84_src_dim_Z := @bb84_src_dim_Z P q s;
     bb84_src_dim_B := @bb84_src_dim_B P q s |}.

Definition bb84_entropy_domain (eps p_pass : R) : Prop :=
  0 < eps /\ eps < Num.sqrt p_pass.

Lemma bb84_eps_lt_sqrt_pass eps p_pass :
  bb84_entropy_domain eps p_pass -> eps < Num.sqrt p_pass.
Proof. by case. Qed.

Record bb84_numeric_side (P : bb84_protocol) (eps : R) := BB84NumericSide { bb84_epsc_pos : 0 < bb84_eps_c P; bb84_epsc_le1 : bb84_eps_c P <= 1; bb84_leak_nonneg : 0 <= bb84_leak_EC P; }.

End FvqkdReal.

Arguments bb84_sample {R} P.
Arguments bb84_source_model {R} P q.
Arguments bb84_numeric_side {R} P eps.


Import Order.TTheory GRing.Theory Num.Theory Num.Def MxLownerOrder.
Import VectorInternalTheory.


Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Open Scope ring_scope.
Local Open Scope lfun_scope.

Section FvqkdReal.
Variable R : realType.
Notation C := (@hermitian.C R).
Notation chsType := (@chsType R).

Fact bb84_p_pass_tot_eventE
    (P : @bb84_protocol R) (G : bb84_zsource P) :
  bb84_p_pass_tot G =
    \sum_(pi : 'S_(bb84_total_rounds P))
      @uniform_perm_mu R (bb84_total_rounds P) pi *
        \sum_(z : 'I_(bb84_full_string_count P))
          \sum_(z' : 'I_(bb84_full_string_count P))
            if pi \in bb84_pass_event
                (BB84Sample (ord_to_bitstring z) (ord_to_bitstring z'))
            then bb84_W G z z' else 0.
Proof.
  rewrite /bb84_p_pass_tot /bb84_p_pass_pair /perm_pair_sample_le_prob /Pr_event /bb84_pass_event.
  rewrite (eq_bigr (fun z : 'I_(bb84_full_string_count P) => \sum_(z' : 'I_(bb84_full_string_count P)) \sum_(pi : 'S_(bb84_total_rounds P) | pi \in @perm_pair_sample_le_event R (bb84_n P) (bb84_k P) (ord_to_bitstring z) (ord_to_bitstring z') (bb84_Qtol P)) (bb84_W G z z' * @uniform_perm_mu R (bb84_total_rounds P) pi))); last first.
  { move=> z _; apply: eq_bigr => z' _. by rewrite mulr_sumr. } rewrite (eq_bigr (fun z : 'I_(bb84_full_string_count P) => \sum_(pi : 'S_(bb84_total_rounds P)) \sum_(z' : 'I_(bb84_full_string_count P) | pi \in @perm_pair_sample_le_event R (bb84_n P) (bb84_k P) (ord_to_bitstring z) (ord_to_bitstring z') (bb84_Qtol P)) (bb84_W G z z' * @uniform_perm_mu R (bb84_total_rounds P) pi))); last first.
  { move=> z _; by rewrite (exchange_big_dep xpredT) //=. } rewrite exchange_big /=; apply: eq_bigr => pi _; rewrite mulr_sumr; apply: eq_bigr => z _.
  rewrite mulr_sumr big_mkcond; apply: eq_bigr => z' _.
  by case Hpass: (pi \in bb84_pass_event (BB84Sample (ord_to_bitstring z) (ord_to_bitstring z'))); [rewrite mulrC | rewrite mulr0]. Qed.

Section EURBB84Bridge.
Variable (L : finType) (HL : L -> chsType).

Corollary entropic_uncertainty_relation_bb84 (S0 E0 Zkey B : {set L})
    (disSE0 : [disjoint S0 & E0])
    (disSZ : [disjoint S0 & Zkey])
    (disSB : [disjoint S0 & B])
    (disEZ : [disjoint E0 & Zkey])
    (disEB : [disjoint E0 & B])
    (disZB : [disjoint Zkey & B])
    (n_key : nat) (eps' q : R)
    (na nb nc nx nz : nat)
    (rhoSrc : 'M[C]_(na * nb * nc))
    (M : 'I_nx -> 'M[C]_na) (N : 'I_nz -> 'M[C]_na)
    (dimSE : nx * nb = dim ('H[HL]_(S0 :|: E0)))
    (dimZB : nz * nc = dim ('H[HL]_(Zkey :|: B)))
    (dim_S : nx = dim ('H[HL]_S0))
    (dim_E : nb = dim ('H[HL]_E0))
    (dim_Zk : nz = dim ('H[HL]_Zkey))
    (dim_B : nc = dim ('H[HL]_B)) :
  (0 < n_key)%N -> rhoSrc \is denmx -> 0 <= eps' -> eps' < Num.sqrt (@complex.Re R (\tr rhoSrc)) ->
  is_povm_mx M -> is_povm_mx N -> n_key%:R * q <= q_of_mx M N ->
  smooth_hmin E0 eps' (eur_rho_XB disSE0 rhoSrc M dimSE) +
  smooth_hmax B eps' (eur_rho_ZC disZB rhoSrc N dimZB)
    >= n_key%:R * q.
Proof.
  move=> _ Hden Heps0 Heps_lt HM HN Hq.
  have Heur := @entropic_uncertainty_relation R L HL S0 E0 Zkey B disSE0 disZB na nb nc nx nz eps' rhoSrc M N dimSE dimZB dim_S dim_E dim_Zk dim_B Hden HM HN Heps0 Heps_lt.
  exact: le_trans Hq Heur. Qed.

Lemma eur_rho_XB_cq (X B : {set L}) (disXB : [disjoint X & B])
    (na nb nc nx : nat)
    (rhoSrc : 'M[C]_(na * nb * nc))
    (M : 'I_nx -> 'M[C]_na)
    (dim_eq : nx * nb = dim ('H[HL]_(X :|: B)))
    (dim_X : nx = dim ('H[HL]_X))
    (dim_B : nb = dim ('H[HL]_B)) :
  @is_cq_state R L HL X B (eur_rho_XB disXB rhoSrc M dim_eq).
Proof.
  rewrite /is_cq_state; apply/forallP => x; apply/forallP => x'; apply/implyP => Hx'x.
  apply/eqP; apply: (@biprod_mx0_inj R L HL X B disXB).
  rewrite !biprod_mx_comp !biprod_mx_sdot h2mx1 (@eur_rho_XB_biprod_mx R L HL X B disXB na nb nc nx rhoSrc M dim_eq dim_X dim_B).
  rewrite !outp.unlock /= !mx2hK.
  have Hix : i2n x' != i2n x. { apply/eqP => Hix. move: Hx'x; by rewrite (i2n_inj Hix) eqxx. } rewrite !deltav.unlock !h2c_eb !adjmx_delta !mul_delta_mx.
  pose ix := cast_ord (esym dim_X) (i2n x).
  pose ix' := cast_ord (esym dim_X) (i2n x').
  have Hix' : ix' != ix.
  { apply/eqP => Hc. move: Hix. by rewrite /ix' /ix in Hc; rewrite (cast_ord_inj Hc) eqxx. } have HIB : castmx (dim_B, dim_B) (1%:M : 'M[C]_nb) = 1%:M by case: _ / dim_B; rewrite castmx_id.
  move: (f_equal (fun Y => castmx (f_equal2 muln dim_X dim_B, f_equal2 muln dim_X dim_B) Y) (@rho_XB_offdiag_mx R na nb nc nx M rhoSrc ix ix' Hix')).
  rewrite linear0 (castmx_mulmx3 (f_equal2 muln dim_X dim_B) (f_equal2 muln dim_X dim_B)).
  by rewrite !castmx_tensmx !mcextra.delta_mx_cast !cast_ordKV !HIB. Qed.

Fact eur_rho_XB_cq_block_project_mx
    (X B : {set L}) (disXB : [disjoint X & B])
    (na nb nc nx : nat)
    (rhoSrc : 'M[C]_(na * nb * nc))
    (M : 'I_nx -> 'M[C]_na)
    (dim_eq : nx * nb = dim ('H[HL]_(X :|: B)))
    (dim_X : nx = dim ('H[HL]_X))
    (dim_B : nb = dim ('H[HL]_B))
    (x : 'Idx[HL]_X) :
  h2mx (cq_block disXB x (eur_rho_XB disXB rhoSrc M dim_eq)) =
  ptrace1
    (((h2mx [> deltav x; deltav x <]) *t
        (1%:M : 'M[C]_(dim 'H[HL]_B))) *m
      castmx (f_equal2 muln dim_X dim_B, f_equal2 muln dim_X dim_B)
        (rho_XB M rhoSrc) *m
      ((h2mx [> deltav x; deltav x <]) *t
        (1%:M : 'M[C]_(dim 'H[HL]_B)))).
Proof. by rewrite cq_block_biprod_mx_project (@eur_rho_XB_biprod_mx R L HL X B disXB na nb nc nx rhoSrc M dim_eq dim_X dim_B). Qed.

Fact eur_rho_XB_cq_block_branch_mx
    (X B : {set L}) (disXB : [disjoint X & B])
    (na nb nc nx : nat)
    (rhoSrc : 'M[C]_(na * nb * nc))
    (M : 'I_nx -> 'M[C]_na)
    (dim_eq : nx * nb = dim ('H[HL]_(X :|: B)))
    (dim_X : nx = dim ('H[HL]_X))
    (dim_B : nb = dim ('H[HL]_B))
    (x : 'Idx[HL]_X) :
  castmx (esym dim_B, esym dim_B)
    (h2mx (cq_block disXB x (eur_rho_XB disXB rhoSrc M dim_eq))) =
  ptrace1 (ptrace2
    ((sqrtmx (M (cast_ord (esym dim_X) (i2n x))) *t
        (1%:M : 'M[C]_nb) *t (1%:M : 'M[C]_nc)) *m
      rhoSrc *m
      (sqrtmx (M (cast_ord (esym dim_X) (i2n x))) *t
        (1%:M : 'M[C]_nb) *t (1%:M : 'M[C]_nc)))).
Proof. case: _ / (esym dim_X) in rhoSrc M dim_eq x *. case: _ / (esym dim_B) in rhoSrc M dim_eq *. by rewrite castmx_id eur_rho_XB_cq_block_project_mx !castmx_id h2mx_deltav_outp cast_ord_id; exact: rho_XB_block. Qed.

Fact eur_rho_ZC_cq (Z C0 : {set L}) (disZC : [disjoint Z & C0])
    (na nb nc nz : nat)
    (rhoSrc : 'M[C]_(na * nb * nc))
    (N : 'I_nz -> 'M[C]_na)
    (dim_eq : nz * nc = dim ('H[HL]_(Z :|: C0)))
    (dim_Z : nz = dim ('H[HL]_Z))
    (dim_C : nc = dim ('H[HL]_C0)) :
  @is_cq_state R L HL Z C0 (eur_rho_ZC disZC rhoSrc N dim_eq).
Proof.
  have rho_ZC_offdiag_mx : forall (na0 nb0 nc0 nz0 : nat) (N0 : 'I_nz0 -> 'M[C]_na0) (rhoABC : 'M[C]_(na0 * nb0 * nc0)) (z z' : 'I_nz0), z' != z -> ((delta_mx z z : 'M[C]_nz0) *t (1%:M : 'M[C]_nc0)) *m rho_ZC N0 rhoABC *m ((delta_mx z' z' : 'M[C]_nz0) *t (1%:M : 'M[C]_nc0)) = 0.
  { move=> na0 nb0 nc0 nz0 N0 rhoABC z z' Hz'z; rewrite /rho_ZC mulmx_sumr mulmx_suml.
    apply: big1 => y _; rewrite !tensmx_mul !mulmx1.
    case Hzy : (z == y).
    - have Hyz' : y != z' by apply/eqP => Hyz'; move: Hz'z; rewrite -Hyz' eq_sym Hzy.
      by rewrite mul_delta_mx_cond Hzy (@mul_delta_mx_0 C nz0 nz0 nz0 y z' z z' Hyz') tens0mx.
    - have Hzy_ne : z != y by rewrite Hzy.
      by rewrite (@mul_delta_mx_0 C nz0 nz0 nz0 z y z y Hzy_ne) mul0mx tens0mx. } rewrite /is_cq_state; apply/forallP => z; apply/forallP => z'; apply/implyP => Hz'z.
  apply/eqP; apply: (@biprod_mx0_inj R L HL Z C0 disZC).
  rewrite !biprod_mx_comp !biprod_mx_sdot h2mx1 (@eur_rho_ZC_biprod_mx R L HL Z C0 disZC na nb nc nz rhoSrc N dim_eq dim_Z dim_C).
  rewrite !outp.unlock /= !mx2hK.
  have Hiz : i2n z' != i2n z. { apply/eqP => Hiz. move: Hz'z; by rewrite (i2n_inj Hiz) eqxx. } rewrite !deltav.unlock !h2c_eb !adjmx_delta !mul_delta_mx.
  pose iz := cast_ord (esym dim_Z) (i2n z).
  pose iz' := cast_ord (esym dim_Z) (i2n z').
  have Hiz' : iz' != iz.
  { apply/eqP => Hc. move: Hiz. by rewrite /iz' /iz in Hc; rewrite (cast_ord_inj Hc) eqxx. } have HIC : castmx (dim_C, dim_C) (1%:M : 'M[C]_nc) = 1%:M by case: _ / dim_C; rewrite castmx_id.
  move: (f_equal (fun Y => castmx (f_equal2 muln dim_Z dim_C, f_equal2 muln dim_Z dim_C) Y) (rho_ZC_offdiag_mx na nb nc nz N rhoSrc iz iz' Hiz')).
  rewrite linear0 (castmx_mulmx3 (f_equal2 muln dim_Z dim_C) (f_equal2 muln dim_Z dim_C)).
  by rewrite !castmx_tensmx !mcextra.delta_mx_cast !cast_ordKV !HIC. Qed.

Fact eur_rho_ZC_cq_block_branch_mx
    (Z C0 : {set L}) (disZC : [disjoint Z & C0])
    (na nb nc nz : nat)
    (rhoSrc : 'M[C]_(na * nb * nc))
    (N : 'I_nz -> 'M[C]_na)
    (dim_eq : nz * nc = dim ('H[HL]_(Z :|: C0)))
    (dim_Z : nz = dim ('H[HL]_Z))
    (dim_C : nc = dim ('H[HL]_C0))
    (z : 'Idx[HL]_Z) :
  castmx (esym dim_C, esym dim_C)
    (h2mx (cq_block disZC z (eur_rho_ZC disZC rhoSrc N dim_eq))) =
  ptrace1
    ((sqrtmx (N (cast_ord (esym dim_Z) (i2n z))) *t
        (1%:M : 'M[C]_nb) *t (1%:M : 'M[C]_nc)) *m
      rhoSrc *m
      (sqrtmx (N (cast_ord (esym dim_Z) (i2n z))) *t
        (1%:M : 'M[C]_nb) *t (1%:M : 'M[C]_nc))).
Proof.
have eur_rho_ZC_cq_block_project_mx : forall (Z C0 : {set L}) (disZC : [disjoint Z & C0]) (na nb nc nz : nat) (rhoSrc : 'M[C]_(na * nb * nc)) (N : 'I_nz -> 'M[C]_na) (dim_eq : nz * nc = dim ('H[HL]_(Z :|: C0))) (dim_Z : nz = dim ('H[HL]_Z)) (dim_C : nc = dim ('H[HL]_C0)) (z : 'Idx[HL]_Z), h2mx (cq_block disZC z (eur_rho_ZC disZC rhoSrc N dim_eq)) = ptrace1 (((h2mx [> deltav z; deltav z <]) *t (1%:M : 'M[C]_(dim 'H[HL]_C0))) *m castmx (f_equal2 muln dim_Z dim_C, f_equal2 muln dim_Z dim_C) (rho_ZC N rhoSrc) *m ((h2mx [> deltav z; deltav z <]) *t (1%:M : 'M[C]_(dim 'H[HL]_C0)))).
{ clear z dim_C dim_Z dim_eq N rhoSrc nz nc nb na disZC C0 Z; move=> Z C0 disZC na nb nc nz rhoSrc N dim_eq dim_Z dim_C z. rewrite cq_block_biprod_mx_project.
  by rewrite (@eur_rho_ZC_biprod_mx R L HL Z C0 disZC na nb nc nz rhoSrc N dim_eq dim_Z dim_C). } have rho_ZC_block : forall (na nb nc nz : nat) (N : 'I_nz -> 'M[C]_na) (rhoABC : 'M[C]_(na * nb * nc)) (z : 'I_nz), ptrace1 (((delta_mx z z : 'M[C]_nz) *t (1%:M : 'M[C]_nc)) *m rho_ZC N rhoABC *m ((delta_mx z z : 'M[C]_nz) *t (1%:M : 'M[C]_nc))) = ptrace1 ((sqrtmx (N z) *t (1%:M : 'M[C]_nb) *t (1%:M : 'M[C]_nc)) *m rhoABC *m (sqrtmx (N z) *t (1%:M : 'M[C]_nb) *t (1%:M : 'M[C]_nc))).
{ clear z dim_C dim_Z dim_eq N rhoSrc nz nc nb na disZC C0 Z; move=> na nb nc nz N rhoABC z. set branch := ptrace1 ((sqrtmx (N z) *t (1%:M : 'M[C]_nb) *t (1%:M : 'M[C]_nc)) *m rhoABC *m (sqrtmx (N z) *t (1%:M : 'M[C]_nb) *t (1%:M : 'M[C]_nc))).
  change (ptrace1 (((delta_mx z z : 'M[C]_nz) *t (1%:M : 'M[C]_nc)) *m rho_ZC N rhoABC *m ((delta_mx z z : 'M[C]_nz) *t (1%:M : 'M[C]_nc))) = branch).
  rewrite /rho_ZC mulmx_sumr mulmx_suml linear_sum /=.
  rewrite (eq_bigr (fun a : 'I_nz => if a == z then branch else 0)); last first.
  { move=> a _; rewrite !tensmx_mul !mul1mx.
    case Hax: (a == z) /eqP => [-> | Hax_neq].
    - rewrite ?mul_delta_mx.
      rewrite !mulmx1.
      rewrite (@ptrace1_tensmx R nz nc (delta_mx z z : 'M[C]_nz) branch).
      by rewrite mxtrace_delta eqxx scale1r.
    - have Hza : z != a by rewrite eq_sym Hax.
      rewrite ?mul_delta_mx !mulmx1.
      have Hleft0 : (delta_mx z z : 'M[C]_nz) *m delta_mx a a = 0.
      { by rewrite mul_delta_mx_cond (negPf Hza) mulr0n. } rewrite Hleft0 mul0mx.
      by rewrite ptrace1_tensmx mxtrace0 scale0r. }
rewrite (bigD1 z) //= eqxx.
  by rewrite big1 ?addr0 // => a /negPf ->. } case: _ / (esym dim_Z) in rhoSrc N dim_eq z *.
  case: _ / (esym dim_C) in rhoSrc N dim_eq *.
  rewrite castmx_id eur_rho_ZC_cq_block_project_mx !castmx_id h2mx_deltav_outp cast_ord_id.
  exact: rho_ZC_block. Qed.

End EURBB84Bridge.

Fact std_projective_povm_rcons_mx {n : nat} (t : n.-tuple bool) (b : bool) :
  @std_projective_povm R (2 ^ n.+1) (bseq2ord [tuple of rcons t b]) =
  castmx (esym (expnSr 2 n), esym (expnSr 2 n))
    ((@std_projective_povm R (2 ^ n) (bseq2ord t)) *t
     (@std_projective_povm R 2 (bseq2ord [tuple b]))).
Proof. rewrite /std_projective_povm delta_mx_tens mcextra.delta_mx_cast. by have Hr := bseq2ord_rcons_mxtens t b; rewrite -Hr !cast_ordK. Qed.

Fixpoint computational_projector_tensor_mx (n : nat) {struct n}
    : n.-tuple bool -> 'M[C]_(2 ^ n) :=
  match n return n.-tuple bool -> 'M[C]_(2 ^ n) with
  | 0 => fun _ => 1%:M
  | n'.+1 => fun t =>
      castmx (esym (expnSr 2 n'), esym (expnSr 2 n'))
        ((computational_projector_tensor_mx (tfirst_tuple t)) *t
         (@std_projective_povm R 2 (bseq2ord [tuple tlast t])))
  end.

Fact computational_projector_tensor_mx_eq
    (n : nat) (t : n.-tuple bool) :
  computational_projector_tensor_mx t =
  @std_projective_povm R (2 ^ n) (bseq2ord t).
Proof.
  elim: n t => [t|n IH t].
  - rewrite /computational_projector_tensor_mx /= /std_projective_povm.
    by apply/matrixP=> i j; rewrite !mxE (ord1 i) (ord1 j) (ord1 (bseq2ord t)) eqxx.
  - case/tupleNP: t => b t; rewrite /= /tlast tnthN.
    have Hfirst : tfirst_tuple [tuple of rcons t b] = t by apply/val_inj=> /=; rewrite tfirst_rcons.
    by rewrite Hfirst IH -std_projective_povm_rcons_mx. Qed.

Lemma eur_rho_ZC_std_projective_pair_with_eve (d ne : nat)
    (z c : 'I_d) (sigmaE : 'M[C]_ne) :
  rho_ZC (@std_projective_povm R d)
    (((delta_mx z z : 'M[C]_d) *t sigmaE) *t
      (delta_mx c c : 'M[C]_d)) =
  \tr sigmaE *: ((delta_mx z z : 'M[C]_d) *t
    (delta_mx c c : 'M[C]_d)).
Proof.
  have HtensmxZr : forall (k : C) (A B : 'M[C]_d), A *t (k *: B) = k *: (A *t B).
  { move=> k A B; by rewrite -[k *: B]addr0 (linear_tensmx A) linear0r addr0. } rewrite /rho_ZC /std_projective_povm (bigD1 z)//= sqrtmx_delta_mx_ii !tensmx_mul !mul_delta_mx.
  rewrite !mul1mx !mulmx1 ptrace1_tensmx !mxtrace_tens tr_delta_mx_ii mul1r HtensmxZr.
  rewrite big1 ?addr0// => z' Hz'z.
  rewrite sqrtmx_delta_mx_ii !tensmx_mul !mul1mx !mulmx1.
  have Hz'z_ne : z' != z by exact: Hz'z.
  by rewrite (@mul_delta_mx_0 C d d d z' z z' z Hz'z_ne) mul0mx !tens0mx linear0 tensmx0. Qed.

Fact eur_rho_ZC_std_projective_pair (d : nat) (z c : 'I_d) :
  rho_ZC (@std_projective_povm R d)
    (((delta_mx z z : 'M[C]_d) *t (1%:M : 'M[C]_1)) *t
      (delta_mx c c : 'M[C]_d)) =
  (delta_mx z z : 'M[C]_d) *t (delta_mx c c : 'M[C]_d).
Proof. by rewrite (@eur_rho_ZC_std_projective_pair_with_eve d 1 z c 1%:M) mxtrace1 mulr1n scale1r. Qed.

Local Lemma eur_sum_deltaR (n : nat) (a : 'I_n) (F : 'I_n -> C) :
  \sum_i F i * ((i == a)%:R : C) = F a.
Proof. rewrite (bigD1 a) //= eqxx mulr1 [X in _ + X]big1 ?addr0 //. by move=> i /negPf Hi; rewrite Hi mulr0. Qed.

Local Lemma eur_sum_deltaL_sym (n : nat) (a : 'I_n) (F : 'I_n -> C) :
  \sum_i ((a == i)%:R : C) * F i = F a.
Proof. under eq_bigr => i _ do rewrite eq_sym mulrC. exact: eur_sum_deltaR. Qed.

Local Lemma eur_sum_delta_mx_row (n : nat) (x y : 'I_n)
    (F : 'I_n -> C) :
  \sum_i (delta_mx x x : 'M[C]_n) y i * F i =
  (delta_mx x x : 'M[C]_n) y x * F x.
Proof. rewrite (bigD1 x) //= [X in _ + X]big1 ?addr0 // => i Hix. by rewrite mxE eq_sym (negPf Hix) andbF mul0r. Qed.

Local Lemma eur_sum_delta_mx_col (n : nat) (x y : 'I_n)
    (F : 'I_n -> C) :
  \sum_i F i * (delta_mx x x : 'M[C]_n) i y =
  F x * (delta_mx x x : 'M[C]_n) x y.
Proof. rewrite (bigD1 x) //= [X in _ + X]big1 ?addr0 // => i Hix. by rewrite mxE (negPf Hix) andFb mulr0. Qed.

Local Lemma eur_projective_pair_projector_mulEl_mx (d ne : nat)
    (z c a b : 'I_d) (e : 'I_ne)
    (rho : 'M[C]_(d * ne * d))
    (j : 'I_(d * ne * d)) :
  let P : 'M[C]_(d * ne * d) :=
    ((delta_mx z z : 'M[C]_d) *t (1%:M : 'M[C]_ne)) *t
      (delta_mx c c : 'M[C]_d) in
  (P *m rho) (mxtens_index (mxtens_index (a, e), b)) j =
  ((delta_mx z z : 'M[C]_d) a z *
   (delta_mx c c : 'M[C]_d) b c) *
  rho (mxtens_index (mxtens_index (z, e), c)) j.
Proof.
  rewrite /= (tensmxE_mid (((delta_mx z z : 'M[C]_d) *t (1%:M : 'M[C]_ne)) *t (delta_mx c c : 'M[C]_d)) rho (mxtens_index (mxtens_index (a, e), b)) j).
  rewrite mxtens_index_pairV /=.
  under eq_bigr => a' _ do under eq_bigr => e' _ do under eq_bigr => b' _ do rewrite !tensmxE.
  under eq_bigr => a' _ do under eq_bigr => e' _ do under eq_bigr => b' _ do rewrite -!mulrA.
  under eq_bigr => a' _ do under eq_bigr => e' _ do rewrite -mulr_sumr.
  under eq_bigr => a' _ do under eq_bigr => e' _ do rewrite -mulr_sumr.
  under eq_bigr => a' _ do under eq_bigr => e' _ do rewrite eur_sum_delta_mx_row.
  under eq_bigr => a' _ do under eq_bigr => e' _ do rewrite [1%:M e e']mxE.
  under eq_bigr => a' _ do rewrite -mulr_sumr eur_sum_deltaL_sym.
  by rewrite eur_sum_delta_mx_row mulrA. Qed.

Local Lemma eur_projective_pair_projector_mulEr_mx (d ne : nat)
    (z c a b : 'I_d) (e : 'I_ne)
    (rho : 'M[C]_(d * ne * d))
    (i : 'I_(d * ne * d)) :
  let P : 'M[C]_(d * ne * d) :=
    ((delta_mx z z : 'M[C]_d) *t (1%:M : 'M[C]_ne)) *t
      (delta_mx c c : 'M[C]_d) in
  (rho *m P) i (mxtens_index (mxtens_index (a, e), b)) =
  rho i (mxtens_index (mxtens_index (z, e), c)) *
  ((delta_mx z z : 'M[C]_d) z a *
   (delta_mx c c : 'M[C]_d) c b).
Proof.
  rewrite /= (tensmxE_mid rho (((delta_mx z z : 'M[C]_d) *t (1%:M : 'M[C]_ne)) *t (delta_mx c c : 'M[C]_d)) i (mxtens_index (mxtens_index (a, e), b))).
  rewrite mxtens_index_pairV /=.
  under eq_bigr => a' _ do under eq_bigr => e' _ do under eq_bigr => b' _ do rewrite !tensmxE.
  under eq_bigr => a' _ do under eq_bigr => e' _ do under eq_bigr => b' _ do rewrite !mulrA.
  under eq_bigr => a' _ do under eq_bigr => e' _ do rewrite eur_sum_delta_mx_col.
  under eq_bigr => a' _ do rewrite -mulr_suml.
  under eq_bigr => a' _ do under eq_bigr => e' _ do rewrite [1%:M e' e]mxE.
  under eq_bigr => a' _ do rewrite eur_sum_deltaR.
  by rewrite -mulr_suml eur_sum_delta_mx_col !mulrA. Qed.

Local Lemma eur_projective_left_projector_mulEl_mx (d ne : nat)
    (z a b : 'I_d) (e : 'I_ne)
    (rho : 'M[C]_(d * ne * d))
    (j : 'I_(d * ne * d)) :
  let Pz : 'M[C]_(d * ne * d) :=
    ((delta_mx z z : 'M[C]_d) *t (1%:M : 'M[C]_ne)) *t
      (1%:M : 'M[C]_d) in
  (Pz *m rho) (mxtens_index (mxtens_index (a, e), b)) j =
  (delta_mx z z : 'M[C]_d) a z *
  rho (mxtens_index (mxtens_index (z, e), b)) j.
Proof.
  rewrite /= (tensmxE_mid (((delta_mx z z : 'M[C]_d) *t (1%:M : 'M[C]_ne)) *t (1%:M : 'M[C]_d)) rho (mxtens_index (mxtens_index (a, e), b)) j).
  rewrite mxtens_index_pairV /=.
  under eq_bigr => a' _ do under eq_bigr => e' _ do under eq_bigr => b' _ do rewrite !tensmxE.
  under eq_bigr => a' _ do under eq_bigr => e' _ do under eq_bigr => b' _ do rewrite -!mulrA.
  under eq_bigr => a' _ do under eq_bigr => e' _ do under eq_bigr => b' _ do rewrite [1%:M b b']mxE.
  under eq_bigr => a' _ do under eq_bigr => e' _ do rewrite -mulr_sumr.
  under eq_bigr => a' _ do under eq_bigr => e' _ do rewrite -mulr_sumr.
  under eq_bigr => a' _ do under eq_bigr => e' _ do rewrite eur_sum_deltaL_sym.
  under eq_bigr => a' _ do under eq_bigr => e' _ do rewrite [1%:M e e']mxE.
  under eq_bigr => a' _ do rewrite -mulr_sumr eur_sum_deltaL_sym.
  by rewrite eur_sum_delta_mx_row. Qed.

Local Lemma eur_projective_left_projector_mulEr_mx (d ne : nat)
    (z a b : 'I_d) (e : 'I_ne)
    (rho : 'M[C]_(d * ne * d))
    (i : 'I_(d * ne * d)) :
  let Pz : 'M[C]_(d * ne * d) :=
    ((delta_mx z z : 'M[C]_d) *t (1%:M : 'M[C]_ne)) *t
      (1%:M : 'M[C]_d) in
  (rho *m Pz) i (mxtens_index (mxtens_index (a, e), b)) =
  rho i (mxtens_index (mxtens_index (z, e), b)) *
  (delta_mx z z : 'M[C]_d) z a.
Proof.
  rewrite /= (tensmxE_mid rho (((delta_mx z z : 'M[C]_d) *t (1%:M : 'M[C]_ne)) *t (1%:M : 'M[C]_d)) i (mxtens_index (mxtens_index (a, e), b))).
  rewrite mxtens_index_pairV /=.
  under eq_bigr => a' _ do under eq_bigr => e' _ do under eq_bigr => b' _ do rewrite !tensmxE.
  under eq_bigr => a' _ do under eq_bigr => e' _ do under eq_bigr => b' _ do rewrite !mulrA.
  under eq_bigr => a' _ do under eq_bigr => e' _ do under eq_bigr => b' _ do rewrite [1%:M b' b]mxE.
  under eq_bigr => a' _ do under eq_bigr => e' _ do rewrite eur_sum_deltaR.
  under eq_bigr => a' _ do under eq_bigr => e' _ do rewrite [1%:M e' e]mxE.
  under eq_bigr => a' _ do rewrite eur_sum_deltaR.
  by rewrite eur_sum_delta_mx_col. Qed.

Fact eur_rho_ZC_std_projective_entry_mx (d ne : nat)
    (rho : 'M[C]_(d * ne * d))
    (z z' c c' : 'I_d) :
  (rho_ZC (@std_projective_povm R d) rho)
    (mxtens_index (z, c)) (mxtens_index (z', c')) =
  if z == z' then
    \sum_(e : 'I_ne)
      rho (mxtens_index (mxtens_index (z, e), c))
          (mxtens_index (mxtens_index (z, e), c'))
  else 0.
Proof.
  rewrite /rho_ZC /std_projective_povm summxE.
  case Hz_eq: (z == z').
  - move/eqP: Hz_eq => <-; rewrite (bigD1 z) //= sqrtmx_delta_mx_ii.
    set Pz : 'M[C]_(d * ne * d) := (((delta_mx z z : 'M[C]_d) *t (1%:M : 'M[C]_ne)) *t (1%:M : 'M[C]_d)).
    set M := ptrace1 (Pz *m rho *m Pz).
    have Hhead : ((delta_mx z z : 'M[C]_d) *t M) (mxtens_index (z, c)) (mxtens_index (z, c')) = M c c' by rewrite tensmxE !mxE !eqxx /= mul1r.
    rewrite [X in _ + X = _]big1 ?addr0; last first.
    { move=> x Hxz; rewrite sqrtmx_delta_mx_ii.
      set Mx := ptrace1 _; rewrite tensmxE !mxE.
      have Hzx : z != x by rewrite eq_sym.
      by rewrite (negPf Hzx) /= mul0r. } apply: (etrans Hhead); rewrite /M /Pz ptrace1E mxtens_index_pairV /=.
    under eq_bigr => a _ do under eq_bigr => e _ do rewrite eur_projective_left_projector_mulEr_mx eur_projective_left_projector_mulEl_mx.
    under eq_bigr => a _ do under eq_bigr => e _ do rewrite !mxE.
    rewrite (bigD1 z) //= !eqxx /=.
    under eq_bigr => e _ do rewrite !mul1r mulr1.
    rewrite [X in _ + X = _]big1 ?addr0 // => a Haz.
    rewrite big1 // => e _; have Haz_ne : a != z by exact: Haz.
    by rewrite (negPf Haz_ne) /= !mul0r.
  - rewrite big1 // => x _; rewrite sqrtmx_delta_mx_ii.
    set Mx := ptrace1 _; rewrite tensmxE !mxE [z == x]eq_sym.
    case Hxz: (x == z); last by rewrite /= ?mul0r ?mulr0.
    have Hxz' : x != z'.
    { apply/eqP=> Hxz'_eq; move/eqP: Hxz => Hxz_eq; have Hzz'_eq : z = z' by rewrite -Hxz_eq Hxz'_eq.
      by move: Hz_eq; rewrite Hzz'_eq eqxx. } have Hz'x : z' != x by rewrite eq_sym.
    by rewrite ?(negPf Hxz') ?(negPf Hz'x) /= ?mul0r ?mulr0. Qed.

Lemma eur_projective_pair_sandwich_factor_mx (d ne : nat)
    (z c : 'I_d) (rho : 'M[C]_(d * ne * d)) :
  let P : 'M[C]_(d * ne * d) :=
    ((delta_mx z z : 'M[C]_d) *t (1%:M : 'M[C]_ne)) *t
      (delta_mx c c : 'M[C]_d) in
  let sigmaE : 'M[C]_ne :=
    \matrix_(i, j)
      rho (mxtens_index (mxtens_index (z, i), c))
          (mxtens_index (mxtens_index (z, j), c)) in
  P *m rho *m P =
  ((delta_mx z z : 'M[C]_d) *t sigmaE) *t
    (delta_mx c c : 'M[C]_d).
Proof.
  rewrite /=; set sigmaE := \matrix_(i0, j0) rho (mxtens_index (mxtens_index (z, i0), c)) (mxtens_index (mxtens_index (z, j0), c)).
  apply/matrixP => i j; case: (mxtens_indexP i) => iae ib; case: (mxtens_indexP iae) => ia ie.
  case: (mxtens_indexP j) => jae jb; case: (mxtens_indexP jae) => ja je.
  rewrite eur_projective_pair_projector_mulEr_mx eur_projective_pair_projector_mulEl_mx !tensmxE.
  rewrite /sigmaE [X in _ = _ * X * _]mxE !mxE !eqxx /= !andbT.
  case: (ia == z); case: (ib == c); case: (ja == z); case: (jb == c); rewrite ?andbT ?andbF ?andFb ?mul0r ?mulr0 ?mul1r ?mulr1.
  all: by rewrite ?mul0r. Qed.

Lemma eur_projective_pair_sandwich_trace_mx (d ne : nat)
    (z c : 'I_d) (rho : 'M[C]_(d * ne * d)) :
  let P : 'M[C]_(d * ne * d) :=
    ((delta_mx z z : 'M[C]_d) *t (1%:M : 'M[C]_ne)) *t
      (delta_mx c c : 'M[C]_d) in
  let sigmaE : 'M[C]_ne :=
    \matrix_(i, j)
      rho (mxtens_index (mxtens_index (z, i), c))
          (mxtens_index (mxtens_index (z, j), c)) in
  \tr (P *m rho *m P) = \tr sigmaE.
Proof.
  rewrite /= eur_projective_pair_sandwich_factor_mx.
  set sigmaE := \matrix_(i, j) rho (mxtens_index (mxtens_index (z, i), c)) (mxtens_index (mxtens_index (z, j), c)).
  change (\tr (((delta_mx z z : 'M[C]_d) *t sigmaE) *t (delta_mx c c : 'M[C]_d)) = \tr sigmaE).
  rewrite (trace_tensmx (((delta_mx z z : 'M[C]_d) *t sigmaE)) (delta_mx c c : 'M[C]_d)).
  by rewrite (trace_tensmx (delta_mx z z : 'M[C]_d) sigmaE) !tr_delta_mx_ii !mul1r !mulr1. Qed.

Fact rho_ZC_std_projective_diag_mx (d ne : nat)
    (z c : 'I_d) (rho : 'M[C]_(d * ne * d)) :
  (rho_ZC (@std_projective_povm R d) rho)
    (mxtens_index (z, c)) (mxtens_index (z, c)) =
  (ptrace1
    (((delta_mx z z : 'M[C]_d) *t 1%:M *t 1%:M) *m rho *m
     ((delta_mx z z : 'M[C]_d) *t 1%:M *t 1%:M))) c c.
Proof.
  rewrite /rho_ZC /std_projective_povm summxE (bigD1 z) //= sqrtmx_delta_mx_ii.
  set B := ptrace1 _.
  have Hmain : ((delta_mx z z : 'M[C]_d) *t B) (mxtens_index (z, c)) (mxtens_index (z, c)) = B c c by rewrite tensmxE !mxE !eqxx /= mul1r.
  rewrite [X in X + _ = _]Hmain /B [X in _ + X = _]big1 ?addr0 // => z' Hz'z.
  rewrite sqrtmx_delta_mx_ii tensmxE !mxE; have Hzz' : z != z' by rewrite eq_sym.
  by rewrite (negPf Hzz') /= mul0r. Qed.

Fact eur_rho_ZC_std_projective_pair_diag_trace_mx (d ne : nat)
    (z c : 'I_d) (rho : 'M[C]_(d * ne * d)) :
  let P : 'M[C]_(d * ne * d) :=
    ((delta_mx z z : 'M[C]_d) *t (1%:M : 'M[C]_ne)) *t
      (delta_mx c c : 'M[C]_d) in
  (rho_ZC (@std_projective_povm R d) rho)
    (mxtens_index (z, c)) (mxtens_index (z, c)) =
  \tr (P *m rho *m P).
Proof.
  rewrite /=; set sigmaE : 'M[C]_ne := \matrix_(i, j) rho (mxtens_index (mxtens_index (z, i), c)) (mxtens_index (mxtens_index (z, j), c)).
  rewrite (@eur_projective_pair_sandwich_trace_mx d ne z c rho) /rho_ZC /std_projective_povm.
  rewrite summxE (bigD1 z)//= sqrtmx_delta_mx_ii.
  set A := ptrace1 _.
  have Hmain : ((delta_mx z z : 'M[C]_d) *t A) (mxtens_index (z, c)) (mxtens_index (z, c)) = \tr sigmaE.
  { rewrite tensmxE !mxE !eqxx /= mul1r /A ptrace1E mxtens_index_pairV /=.
    under eq_bigr => a _ do under eq_bigr => e _ do rewrite eur_projective_left_projector_mulEr_mx.
    under eq_bigr => a _ do under eq_bigr => e _ do rewrite eur_projective_left_projector_mulEl_mx.
    rewrite (bigD1 z)//= !mxE !eqxx /=.
    rewrite [X in _ + X = _]big1 ?addr0; last first.
    { move=> a Haz; rewrite big1// => e _; rewrite !mxE.
      have Hza : a != z by exact: Haz.
      by rewrite (negPf Hza) andbF /= !mul0r. } rewrite /sigmaE /mxtrace.
    under eq_bigr => e _ do rewrite mul1r mulr1.
    by apply: eq_bigr => e _; rewrite mxE. }
rewrite [X in _ + X = _]big1; last first.
  { move=> z' Hz'z; rewrite sqrtmx_delta_mx_ii tensmxE !mxE.
    have Hz'z_ne : z' != z by exact: Hz'z.
    have Hzz'_ne : z != z' by rewrite eq_sym.
    by rewrite (negPf Hzz'_ne) /= mul0r. } by rewrite addr0 Hmain. Qed.

Fact bb84_holdout_measure_ZZ_rho_ZC
    (P : bb84_protocol) (G : bb84_zsource P)
    (rho : 'M[C]_((2 ^ bb84_n P) * bb84_zsrc_nb G *
                  (2 ^ bb84_n P))) :
  @bb84_holdout_measure_ZZ R P G rho =
  \sum_(w : 'I_(2 ^ bb84_n P))
    \sum_(w' : 'I_(2 ^ bb84_n P))
      (\tr (@bb84_pair_projector R (bb84_n P) w w' *m
        rho_ZC (@std_projective_povm R (2 ^ bb84_n P)) rho)) *:
        @bb84_pair_projector R (bb84_n P) w w'.
Proof.
  have Hdiag_trace (A : 'M[C]_((2 ^ bb84_n P) * (2 ^ bb84_n P))) (w w' : 'I_(2 ^ bb84_n P)) : \tr (@bb84_pair_projector R (bb84_n P) w w' *m A) = A (mxtens_index (w, w')) (mxtens_index (w, w')).
  { rewrite /bb84_pair_projector delta_mx_tens /mxtrace (bigD1 (mxtens_index (w, w'))) //=.
    rewrite mcextra.delta_mx_mulEr eqxx mul1r big1 ?addr0 // => i Hi.
    by rewrite mcextra.delta_mx_mulEr eq_sym (negbTE Hi) mul0r. } rewrite /bb84_holdout_measure_ZZ; apply: eq_bigr => w _; apply: eq_bigr => w' _; congr (_ *: _).
  rewrite Hdiag_trace.
  rewrite (@eur_rho_ZC_std_projective_pair_diag_trace_mx (2 ^ bb84_n P) (bb84_zsrc_nb G) w w' rho).
  have Hproj_id : bb84_holdout_projector G w w' *m bb84_holdout_projector G w w' = bb84_holdout_projector G w w' by rewrite /bb84_holdout_projector !tensmx_mul !mul_delta_mx !mul1mx.
  by rewrite [RHS]mxtrace_mulC mulmxA Hproj_id. Qed.

Fact eur_projective_pair_sandwich_normalized_den1_mx
    (d ne : nat) (z c : 'I_d) (rho : 'M[C]_(d * ne * d)) :
  rho \is psdmx -> let P : 'M[C]_(d * ne * d) :=
    ((delta_mx z z : 'M[C]_d) *t (1%:M : 'M[C]_ne)) *t
      (delta_mx c c : 'M[C]_d) in
  \tr (P *m rho *m P) != 0 -> ((\tr (P *m rho *m P))^-1 *: (P *m rho *m P)) \is den1mx.
Proof.
  rewrite /= => Hrho Htr.
  set P : 'M[C]_(d * ne * d) := ((delta_mx z z : 'M[C]_d) *t (1%:M : 'M[C]_ne)) *t (delta_mx c c : 'M[C]_d).
  set M := P *m rho *m P.
  have HP_adj : P^*t = P by rewrite /P !adjmx_tens !adjmx_delta adjmx1.
  have HM_psd : M \is psdmx.
  { have HM_form : M = P *m rho *m P^*t by rewrite /M HP_adj. by rewrite HM_form; exact: (form_psdmx P Hrho). } apply/den1mxP; split.
  - apply: psdmxZ; last exact: HM_psd.
    by rewrite invr_ge0; exact: psdmx_trace.
  - by apply/eqP; rewrite linearZ /= mulVf. Qed.

Fact eur_rho_ZC_std_projective_pair_sandwich_normalized_mx
    (d ne : nat) (z c : 'I_d) (rho : 'M[C]_(d * ne * d)) :
  let P : 'M[C]_(d * ne * d) :=
    ((delta_mx z z : 'M[C]_d) *t (1%:M : 'M[C]_ne)) *t
      (delta_mx c c : 'M[C]_d) in
  \tr (P *m rho *m P) != 0 -> rho_ZC (@std_projective_povm R d)
    ((\tr (P *m rho *m P))^-1 *: (P *m rho *m P)) =
  (delta_mx z z : 'M[C]_d) *t (delta_mx c c : 'M[C]_d).
Proof.
  rewrite /= => Htr.
  set P : 'M[C]_(d * ne * d) := ((delta_mx z z : 'M[C]_d) *t (1%:M : 'M[C]_ne)) *t (delta_mx c c : 'M[C]_d).
  set sigmaE : 'M[C]_ne := \matrix_(i, j) rho (mxtens_index (mxtens_index (z, i), c)) (mxtens_index (mxtens_index (z, j), c)).
  rewrite rho_ZC_scale.
  have Hexec : rho_ZC (@std_projective_povm R d) (P *m rho *m P) = \tr sigmaE *: ((delta_mx z z : 'M[C]_d) *t (delta_mx c c : 'M[C]_d)).
  { by rewrite /P /sigmaE eur_projective_pair_sandwich_factor_mx; exact: eur_rho_ZC_std_projective_pair_with_eve. } rewrite Hexec.
  have Htrace : \tr sigmaE = \tr (P *m rho *m P) by rewrite /P /sigmaE eur_projective_pair_sandwich_trace_mx.
  by rewrite Htrace scalerA mulVf ?scale1r. Qed.

Section FixedMarginalPA.
Variable (L : finType) (HL : L -> chsType) (S E : {set L}).
Hypothesis disSE : [disjoint S & E].

Corollary privacy_amplification
    (Fl Zl : {set L})
    (disSF : [disjoint S & Fl])
    (disSZ : [disjoint S & Zl])
    (disEF : [disjoint E & Fl])
    (disEZ : [disjoint E & Zl])
    (disFZ : [disjoint Fl & Zl])
    (Fh : 'Idx[HL]_Fl -> 'Idx[HL]_S -> 'Idx[HL]_Zl)
    (eps' : R) (rhoXE : 'F[HL]_(S :|: E)) :
  rhoXE \is psdlf -> @complex.Re R (\Tr rhoXE) <= 1 -> @is_cq_state R L HL S E rhoXE ->
  @two_univ R _ _ _ Fh -> 0 <= eps' -> dist_from_uniform (post_hash_state disSE Fh rhoXE) <=
    eps' + (2%:R)^-1 * Num.sqrt (expR
      ((log2 (dim 'H[HL]_Zl)%:R - smooth_hmin E eps' rhoXE) * ln 2%:R)).
Proof.
  move=> Hrho Hrho_tr Hcq HFh Heps'.
  exact: (@two_universal_hashing R L HL S E Fl Zl disSE disSF disSZ disEF disEZ disFZ Fh eps' rhoXE Hrho Hrho_tr Hcq HFh Heps'). Qed.

End FixedMarginalPA.

End FvqkdReal.
