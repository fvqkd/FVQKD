(* qkd_cmd.v -- QKD protocol component syntax sugar                     *)
(* Module: qkd.protocol.qkd_cmd                                         *)
(* Paper: Tomamichel-Lim-Gisin-Renner, Nat. Commun. 3:634 (2012),       *)
(*   Tight finite-key analysis for quantum cryptography (Box 1).        *)
(* The QKD protocol components as qkd_cmd terms over syntax.v.          *)

From mathcomp Require Import all_boot all_order all_algebra.
From mathcomp.reals Require Import reals.
From quantum.external Require Import spectral complex.
From quantum Require Import mcextra mcaextra notation hermitian quantum
  cpo mxpred extnum ctopology svd mxnorm hspace.
From quantum.dirac Require Import hstensor.

Import Order.TTheory GRing.Theory Num.Theory Num.Def MxLownerOrder.
Import VectorInternalTheory.

From qkd.protocol Require Import syntax.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Open Scope ring_scope.
Local Open Scope qkd_scope.

Section QKDCmd.
Variable R : realType.
Notation chsType := (@chsType R).
Variables (L : finType) (HL : L -> chsType).
Variables Cv V : finType.

Notation store := (@store Cv V).
Notation expr := (@expr Cv V).
Notation bexpr := (@bexpr Cv V).
Notation dexpr := (@dexpr R Cv V).

Variables n k l leakEC M : nat.
Variables Qtol eps_c : R.

Variables (a_ y_ b_ y'_ d_ : 'I_M -> Cv).
Variable Q : 'I_M -> {set L}.
Variables Xv Zv Kv XA XB ZA ZB lamv pECv Xhatv : Cv.
Variables gv tAv tBv fv Sv Shv abortv Pvar : Cv.

Variables basisX basisZ outEmpty bot : V.
Variables (vbool : bool -> V) (vbit : bool -> V) (vset : {set 'I_M} -> V) (vset_of : V -> {set 'I_M}) (vrat : nat -> nat -> V).

Variables (dev_rho : forall i : 'I_M, V -> V -> 'F[HL]_(Q i)) (dev_meas : forall i : 'I_M, V -> V -> 'F[HL]_(Q i)).

Variables (tr_app_rounds : ('I_M -> V * V * V) -> V -> V) (tr_app_pe : V -> V -> V -> V -> V) (tr_app_ec : V -> V -> V -> V -> V).
Variables (tr_app_pa : V -> V -> V).

Variables (key_bits_on : {set 'I_M} -> ('I_M -> V) -> V) (test_bits_on : {set 'I_M} -> ('I_M -> V) -> V) (err_count : V -> V -> nat).
Variables (err_of : V -> nat) (unif_nsubset_mass : nat -> {set 'I_M} -> V -> R).

Variables (ir_pub : nat -> V -> V -> V) (ir_dec : V -> V -> V) (unif_vseed : dexpr) (verify_hash : V -> V -> V).

Variables (unif_pseed : dexpr) (privacy_hash : nat -> V -> V -> V).

Definition pX : R := (1 + Num.sqrt (k%:R / n%:R))^-1.

Definition mu_basis : dexpr := fun _ v =>
  if v == basisX then pX else if v == basisZ then 1 - pX else 0.

Definition mu_bit : dexpr := fun _ v =>
  if v == vbit false then (2%:R)^-1
  else if v == vbit true then (2%:R)^-1
  else 0.

Definition detected (s : store) (i : 'I_M) : bool :=
  s (y'_ i) != outEmpty.

Definition sift_X (s : store) (i : 'I_M) : bool :=
  (s (a_ i) == basisX) && (s (b_ i) == basisX) &&
  (s (d_ i) == vbool true).

Definition sift_Z (s : store) (i : 'I_M) : bool :=
  (s (a_ i) == basisZ) && (s (b_ i) == basisZ) &&
  (s (d_ i) == vbool true).

Definition rounds_through (i : 'I_M) (p : 'I_M -> bool) : {set 'I_M} :=
  [set j : 'I_M | (nat_of_ord j <= nat_of_ord i)%N && p j].

Definition Abort_cmd : @qkd_cmd R L HL Cv V :=
  (abortv <-c (fun _ => vbool true)) ;;
  (Sv <-c (fun _ => bot)) ;;
  (Shv <-c (fun _ => bot)).

Definition Prep (i : 'I_M) : @qkd_cmd R L HL Cv V :=
  (a_ i <-^$ mu_basis) ;;
  (y_ i <-^$ mu_bit) ;;
  (Q i <-q (fun s => dev_rho i (s (a_ i)) (s (y_ i)))).

Definition Dist (i : 'I_M) : @qkd_cmd R L HL Cv V :=
  Attack[Q i].

Definition Meas (i : 'I_M) : @qkd_cmd R L HL Cv V :=
  (b_ i <-^$ mu_basis) ;;
  (y'_ i :=M[Q i] (fun s v => dev_meas i (s (b_ i)) v)).

Definition Sift (i : 'I_M) : @qkd_cmd R L HL Cv V :=
  (d_ i <-c (fun s => vbool (detected s i))) ;;
  (Xv <-c (fun s => vset (rounds_through i (sift_X s)))) ;;
  (Zv <-c (fun s => vset (rounds_through i (sift_Z s)))).

Definition Round (i : 'I_M) : @qkd_cmd R L HL Cv V :=
  Prep i ;; Dist i ;; Meas i ;; Sift i.

Definition Announce : @qkd_cmd R L HL Cv V :=
  (Pvar <-c (fun s =>
    tr_app_rounds (fun i => (s (a_ i), s (b_ i), s (d_ i))) (s Pvar))).

Definition has_key_sample (s : store) : bool :=
  (n <= #|vset_of (s Xv)|)%N.

Definition has_test_sample (s : store) : bool :=
  (k <= #|vset_of (s Zv)|)%N.

Definition sift_ok : bexpr := fun s =>
  has_key_sample s && has_test_sample s.

Definition paramest_K_mu : dexpr := fun s v =>
  if has_key_sample s then unif_nsubset_mass n (vset_of (s Xv)) v
  else (v == bot)%:R.

Definition alice_bits (s : store) : 'I_M -> V := fun i => s (y_ i).
Definition bob_bits (s : store) : 'I_M -> V := fun i => s (y'_ i).

Definition ParamEst : @qkd_cmd R L HL Cv V :=
  (Kv <-^$ paramest_K_mu) ;;
  (XA <-c (fun s => key_bits_on (vset_of (s Kv)) (alice_bits s))) ;;
  (XB <-c (fun s => key_bits_on (vset_of (s Kv)) (bob_bits s))) ;;
  (ZA <-c (fun s => test_bits_on (vset_of (s Zv)) (alice_bits s))) ;;
  (ZB <-c (fun s => test_bits_on (vset_of (s Zv)) (bob_bits s))) ;;
  (Pvar <-c (fun s => tr_app_pe (s Kv) (s ZA) (s ZB) (s Pvar))) ;;
  (lamv <-c (fun s => vrat (err_count (s ZA) (s ZB)) #|vset_of (s Zv)|)).

Definition pe_error_high : bexpr := fun s =>
  Qtol * (#|vset_of (s Zv)|)%:R < (err_of (s lamv))%:R.

Definition pe_fail : bexpr := fun s =>
  ~~ sift_ok s || pe_error_high s.

Definition ErrCorr : @qkd_cmd R L HL Cv V :=
  (pECv <-c (fun s => ir_pub leakEC (s XA) (s XB))) ;;
  (Xhatv <-c (fun s => ir_dec (s pECv) (s XB))) ;;
  (gv <-^$ unif_vseed) ;;
  (tAv <-c (fun s => verify_hash (s gv) (s XA))) ;;
  (tBv <-c (fun s => verify_hash (s gv) (s Xhatv))) ;;
  (Pvar <-c (fun s => tr_app_ec (s pECv) (s gv) (s tAv) (s Pvar))).

Definition PrivAmp : @qkd_cmd R L HL Cv V :=
  (fv <-^$ unif_pseed) ;;
  (Sv <-c (fun s => privacy_hash l (s fv) (s XA))) ;;
  (Shv <-c (fun s => privacy_hash l (s fv) (s Xhatv))) ;;
  (Pvar <-c (fun s => tr_app_pa (s fv) (s Pvar))).

Fact Round_wf (qA : {set L}) (i : 'I_M) :
  (forall s, (forall v, 0 <= mu_basis s v) /\ \sum_v mu_basis s v = 1) ->
  (forall s, (forall v, 0 <= mu_bit s v) /\ \sum_v mu_bit s v = 1) -> [disjoint Q i & qA] ->
  (forall s, dev_rho i (s (a_ i)) (s (y_ i)) \is den1lf) ->
  (forall s, \sum_v (((dev_meas i (s (b_ i)) v)^A) \o
                     (dev_meas i (s (b_ i)) v))%VF = \1%VF) -> cmd_wf qA (Round i).
Proof.
  move=> Hbasis Hbit Hdis Hrho Hmeas; rewrite /Round.
  apply: cmd_wf_seq_cmd; first by rewrite /Prep; apply: cmd_wf_seq_cmd; [exact: Hbasis | apply: cmd_wf_seq_cmd; [exact: Hbit | split]].
  apply: cmd_wf_seq_cmd; first by rewrite /Dist /=.
  by apply: cmd_wf_seq_cmd; [rewrite /Meas; apply: cmd_wf_seq_cmd; [exact: Hbasis | split] | rewrite /Sift /=]. Qed.

Fact ParamEst_wf (qA : {set L}) :
  (forall s,
    (forall v, 0 <= paramest_K_mu s v) /\
    \sum_v paramest_K_mu s v = 1) -> cmd_wf qA ParamEst.
Proof. by move=> HK; rewrite /ParamEst; apply: cmd_wf_seq_cmd; [exact: HK | do 5 (apply: cmd_wf_seq_cmd; first by [])]. Qed.

Fact ErrCorr_wf (qA : {set L}) :
  (forall s,
    (forall v, 0 <= unif_vseed s v) /\ \sum_v unif_vseed s v = 1) -> cmd_wf qA ErrCorr.
Proof. move=> Hg; rewrite /ErrCorr; do 2 (apply: cmd_wf_seq_cmd; first by []). by apply: cmd_wf_seq_cmd; [exact: Hg | do 2 (apply: cmd_wf_seq_cmd; first by [])]. Qed.

Fact PrivAmp_wf (qA : {set L}) :
  (forall s,
    (forall v, 0 <= unif_pseed s v) /\ \sum_v unif_pseed s v = 1) -> cmd_wf qA PrivAmp.
Proof. by move=> Hf; rewrite /PrivAmp; apply: cmd_wf_seq_cmd; [exact: Hf | do 2 (apply: cmd_wf_seq_cmd; first by [])]. Qed.

End QKDCmd.
