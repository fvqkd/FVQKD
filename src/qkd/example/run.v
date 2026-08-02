(* run.v -- BB84 denotational run histories                             *)
(* Module: qkd.example.run                                              *)
(* Normal form of the BB84 program denotation as a sum over classical   *)
(* run histories.                                                       *)
From mathcomp Require Import all_boot all_order all_algebra finmap.
From mathcomp.classical Require Import boolp.
From mathcomp.reals Require Import reals.
From quantum.external Require Import spectral complex.
From quantum Require Import mcextra mcaextra notation hermitian quantum cpo mxpred extnum ctopology svd mxnorm hspace.
From quantum.dirac Require Import hstensor.
Import Order.TTheory GRing.Theory Num.Theory Num.Def MxLownerOrder.
Import VectorInternalTheory.
From qkd.protocol Require Import syntax semantics qkd_cmd.
From qkd.example Require Import program.
From utils Require Import bitstr.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Local Open Scope qkd_scope.
Section BB84Run.
Variable R : realType.
Notation chsType := (@chsType R).
Variables (L : finType) (HL : L -> chsType).
Variables Cv V : finType.
Notation store := (@store Cv V). Notation dexpr := (@dexpr R Cv V).
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
Variables (bits_on : {set 'I_M} -> ('I_M -> V) -> V) (test_bits_on : {set 'I_M} -> ('I_M -> V) -> V) (err_count : V -> V -> nat) (err_of : V
  -> nat).
Variables (unif_nsubset_mass : nat -> {set 'I_M} -> V -> R).
Variables (ir_pub : nat -> V -> V -> V) (ir_dec : V -> V -> V) (unif_vseed : dexpr) (verify_hash : V -> V -> V).
Variables (unif_pseed : dexpr) (privacy_hash : nat -> V -> V -> V).
Local Notation pubwall P := ((forall i, Pvar != a_ i) -> (forall i, Pvar != y_ i) -> (forall i, Pvar != b_ i) -> (forall i, Pvar != y'_ i)
  -> (forall i, Pvar != d_ i) -> Pvar != Xv -> Pvar != Zv -> P).
Local Notation abwall P := ((forall i, abortv != a_ i) -> (forall i, abortv != y_ i) -> (forall i, abortv != b_ i) -> (forall i, abortv !=
  y'_ i) -> (forall i, abortv != d_ i) -> abortv != Xv -> abortv != Zv -> abortv != Pvar -> abortv != Kv -> abortv != XA -> abortv != XB ->
  abortv != ZA -> abortv != ZB -> abortv != lamv -> abortv != pECv -> abortv != Xhatv -> abortv != gv -> abortv != tAv -> abortv != tBv ->
  abortv != fv -> abortv != Sv -> abortv != Shv -> P).
Local Notation pewall P := (XA != XB -> XA != ZA -> XA != ZB -> XA != Pvar -> XA != lamv -> XB != ZA -> XB != ZB -> XB != Pvar -> XB != lamv
  -> ZA != ZB -> ZA != Pvar -> ZA != lamv -> ZB != Pvar -> ZB != lamv -> P).
Local Notation ecwall P := (abortv != pECv -> abortv != Xhatv -> abortv != gv -> abortv != tAv -> abortv != tBv -> abortv != Pvar -> P).
Local Notation xawall P := (XA != pECv -> XA != Xhatv -> XA != gv -> XA != tAv -> XA != tBv -> XA != Pvar -> XB != pECv -> P).
Local Notation tagwall P := (gv != tAv -> gv != tBv -> tAv != tBv -> tAv != Pvar -> tBv != Pvar -> P).
Local Notation xhwall P := (Xhatv != gv -> Xhatv != tAv -> Xhatv != tBv -> Xhatv != Pvar -> P).
Local Notation ADVq := (@adversary R L HL V). Local Notation CQs := (@cq_state R L HL Cv V).
Local Notation DSg qA EA := (@denote_singleton R L HL Cv V qA Pvar EA). Local Notation DNg qA EA := (@denote R L HL Cv V qA Pvar EA).
Local Notation RNDs := (@Round R L HL Cv V n k M a_ y_ b_ y'_ d_ Q Xv Zv basisX basisZ outEmpty vbool vbit vset dev_rho dev_meas).
Local Notation PEs := (@ParamEst R L HL Cv V n M y_ y'_ Xv Zv Kv XA XB ZA ZB lamv Pvar bot vset_of vrat tr_app_pe bits_on test_bits_on
  err_count unif_nsubset_mass).
Local Notation ECs := (@ErrCorr R L HL Cv V leakEC XA XB pECv Xhatv gv tAv tBv Pvar tr_app_ec ir_pub ir_dec unif_vseed verify_hash).
Local Notation PAs := (@PrivAmp R L HL Cv V l XA Xhatv fv Sv Shv Pvar tr_app_pa unif_pseed privacy_hash).
Local Notation ABs := (@Abort_cmd R L HL Cv V Sv Shv abortv bot vbool).
Local Notation ANNs := (@Announce R L HL Cv V M a_ b_ d_ Pvar tr_app_rounds).
Local Notation PFs := (@pe_fail R Cv V n k M Qtol Xv Zv lamv vset_of err_of).
Local Notation PROGs := (@bb84_program_scheme R L HL Cv V n k l leakEC M Qtol a_ y_ b_ y'_ d_ Q Xv Zv Kv XA XB ZA ZB lamv pECv Xhatv gv tAv
  tBv fv Sv Shv abortv Pvar basisX basisZ outEmpty bot empty_transcript vbool vbit vset vset_of vrat dev_rho dev_meas tr_app_rounds
  tr_app_pe tr_app_ec tr_app_pa bits_on test_bits_on err_count err_of unif_nsubset_mass ir_pub ir_dec unif_vseed verify_hash unif_pseed
  privacy_hash).
Local Notation EVALs qA EA xi := (@bb84_eval_scheme R L HL Cv V n k l leakEC M Qtol a_ y_ b_ y'_ d_ Q Xv Zv Kv XA XB ZA ZB lamv pECv Xhatv
  gv tAv tBv fv Sv Shv abortv Pvar basisX basisZ outEmpty bot empty_transcript vbool vbit vset vset_of vrat dev_rho dev_meas tr_app_rounds
  tr_app_pe tr_app_ec tr_app_pa bits_on test_bits_on err_count err_of unif_nsubset_mass ir_pub ir_dec unif_vseed verify_hash unif_pseed
  privacy_hash qA EA xi).
Definition round_choice := ((V * V) * (V * V))%type.
Definition choice_a (c : round_choice) : V := c.1.1.
Definition choice_y (c : round_choice) : V := c.1.2.
Definition choice_b (c : round_choice) : V := c.2.1.
Definition choice_y' (c : round_choice) : V := c.2.2.
Definition round_trace := {ffun 'I_M -> round_choice}.
Definition round_choice_default : round_choice := ((bot, bot), (bot, bot)).
Definition round_trace_default : round_trace := [ffun _ => round_choice_default].
Definition round_trace_set (t : round_trace) (i : 'I_M) (c : round_choice) : round_trace := [ffun j => if j == i then c else t j].
Lemma round_trace_set_same (t : round_trace) (i : 'I_M) (c : round_choice) : round_trace_set t i c i = c.
Proof. by rewrite /round_trace_set ffunE eqxx. Qed.

Lemma round_trace_set_other (t : round_trace) (i j : 'I_M) (c : round_choice) : j != i -> round_trace_set t i c j = t j.
Proof. by move=> Hji; rewrite /round_trace_set ffunE (negbTE Hji). Qed.

Definition run_history := (round_trace * ((V * V) * V))%type.
Definition run_prefix := (round_trace * (V * V))%type.
Definition prefix_history (p : run_prefix) (f : V) : run_history := let '(t, (K, g)) := p in (t, ((K, g), f)).
Definition hist_choice (h : run_history) (i : 'I_M) : round_choice := h.1 i.
Definition hist_a (h : run_history) : 'I_M -> V := fun i => choice_a (hist_choice h i).
Definition hist_y (h : run_history) : 'I_M -> V := fun i => choice_y (hist_choice h i).
Definition hist_b (h : run_history) : 'I_M -> V := fun i => choice_b (hist_choice h i).
Definition hist_y' (h : run_history) : 'I_M -> V := fun i => choice_y' (hist_choice h i).
Definition hist_K (h : run_history) : V := h.2.1.1.
Definition hist_g (h : run_history) : V := h.2.1.2.
Definition hist_f (h : run_history) : V := h.2.2.
Definition start_store (s : store) : store := store_set (store_set (store_set (store_set s Pvar empty_transcript) Xv (vset set0)) Zv (vset
  set0)) abortv (vbool false).
Definition start_cmd : @qkd_cmd R L HL Cv V := (Pvar <-c (fun _ : store => empty_transcript)) ;; (Xv <-c (fun _ : store => vset set0)) ;;
  (Zv <-c (fun _ : store => vset set0)) ;; (abortv <-c (fun _ : store => vbool false)).
Lemma start_store_abort (s : store) : start_store s abortv = vbool false.
Proof. by rewrite /start_store store_set_same. Qed.

Definition replay_sift_X (s : store) (i : 'I_M) : bool := (s (a_ i) == basisX) && (s (b_ i) == basisX) && (s (d_ i) == vbool true).
Definition replay_sift_Z (s : store) (i : 'I_M) : bool := (s (a_ i) == basisZ) && (s (b_ i) == basisZ) && (s (d_ i) == vbool true).
Definition replay_rounds_through (i : 'I_M) (p : 'I_M -> bool) : {set 'I_M} := [set j : 'I_M | (nat_of_ord j <= nat_of_ord i)%N && p j].
Definition trace_detected (t : round_trace) (i : 'I_M) : bool := choice_y' (t i) != outEmpty.
Definition trace_key_round (t : round_trace) (i : 'I_M) : bool := (choice_a (t i) == basisX) && (choice_b (t i) == basisX) && trace_detected
  t i.
Definition trace_test_round (t : round_trace) (i : 'I_M) : bool := (choice_a (t i) == basisZ) && (choice_b (t i) == basisZ) &&
  trace_detected t i.
Definition trace_key_set_through (t : round_trace) (i : 'I_M) : {set 'I_M} := [set j : 'I_M | (nat_of_ord j <= nat_of_ord i)%N &&
  trace_key_round t j].
Definition trace_test_set_through (t : round_trace) (i : 'I_M) : {set 'I_M} := [set j : 'I_M | (nat_of_ord j <= nat_of_ord i)%N &&
  trace_test_round t j].
Definition trace_key_set (t : round_trace) : {set 'I_M} := [set i : 'I_M | trace_key_round t i].
Definition trace_test_set (t : round_trace) : {set 'I_M} := [set i : 'I_M | trace_test_round t i].
Definition replay_pX : R := (1 + Num.sqrt (k%:R / n%:R))^-1.
Definition basis_mass : dexpr := fun _ v => if v == basisX then replay_pX else if v == basisZ then 1 - replay_pX else 0.
Definition bit_mass : dexpr := fun _ v => if v == vbit false then (2%:R)^-1 else if v == vbit true then (2%:R)^-1 else 0.
Fact basis_mass_nonneg (s : store) (v : V) : 0 <= basis_mass s v.
Proof. rewrite /basis_mass /replay_pX. case: ifP => _; first by rewrite invr_ge0 addr_ge0 ?ler01 ?sqrtr_ge0. case: ifP => _; last by rewrite lexx. by rewrite subr_ge0 invf_le1; [rewrite lerDl sqrtr_ge0 | rewrite ltr_wpDr ?ltr01 ?sqrtr_ge0]. Qed.

Definition replay_sift_ok (s : store) : bool := (n <= #|vset_of (s Xv)|)%N && (k <= #|vset_of (s Zv)|)%N.
Definition key_sample_mass : dexpr := fun s v => if (n <= #|vset_of (s Xv)|)%N then unif_nsubset_mass n (vset_of (s Xv)) v else (v ==
  bot)%:R.
Definition replay_pe_error_high (s : store) : bool := Qtol * (#|vset_of (s Zv)|)%:R < (err_of (s lamv))%:R.
Definition replay_pe_fail (s : store) : bool := ~~ replay_sift_ok s || replay_pe_error_high s.
Definition round_prepare_store (c : round_choice) (i : 'I_M) (s : store) : store := let s1 := store_set s (a_ i) (choice_a c) in store_set
  s1 (y_ i) (choice_y c).
Definition round_measure_store (c : round_choice) (i : 'I_M) (s : store) : store := let s1 := store_set (round_prepare_store c i s) (b_ i)
  (choice_b c) in store_set s1 (y'_ i) (choice_y' c).
Definition round_sift_store (c : round_choice) (i : 'I_M) (s : store) : store := let s4 := round_measure_store c i s in let s5 := store_set
  s4 (d_ i) (vbool (choice_y' c != outEmpty)) in let s6 := store_set s5 Xv (vset (replay_rounds_through i (replay_sift_X s5))) in store_set
  s6 Zv (vset (replay_rounds_through i (replay_sift_Z s6))).
Definition write_round_choice (c : round_choice) (i : 'I_M) (s : store) : store := round_sift_store c i s.
Lemma round_measure_store_y' (c : round_choice) (i : 'I_M) (s : store) : round_measure_store c i s (y'_ i) = choice_y' c.
Proof. by rewrite /round_measure_store store_set_same. Qed.

Definition write_trace_round (t : round_trace) (i : 'I_M) (s : store) : store := write_round_choice (t i) i s.
Definition rounds_store_seq (h : run_history) (r : seq 'I_M) (s : store) : store := foldl (fun t i => write_trace_round h.1 i t) s r.
Definition rounds_store (h : run_history) (s : store) : store := rounds_store_seq h (enum 'I_M) s.
Definition trace_store_seq (t : round_trace) (r : seq 'I_M) (s : store) : store := foldl (fun u i => write_trace_round t i u) s r.
Lemma rounds_store_seqE (h : run_history) (r : seq 'I_M) (s : store) : rounds_store_seq h r s = trace_store_seq h.1 r s.
Proof. by []. Qed.

Lemma rounds_store_trace_eq (h h' : run_history) (s : store) : h.1 = h'.1 -> rounds_store h s = rounds_store h' s.
Proof. by move=> Htrace; rewrite /rounds_store !rounds_store_seqE Htrace. Qed.

Fact replay_sift_X_trace (t : round_trace) (s : store) (i : 'I_M) : vbool true != vbool false -> s (a_ i) = choice_a (t i) -> s (b_ i) =
  choice_b (t i) -> s (d_ i) = vbool (trace_detected t i) -> replay_sift_X s i = trace_key_round t i.
Proof. move=> Htf Ha Hb Hd; rewrite /replay_sift_X /trace_key_round Ha Hb Hd. case: (trace_detected t i) => /=; first by rewrite eqxx. have Hft : vbool false != vbool true by rewrite eq_sym Htf. by rewrite (negbTE Hft). Qed.

Lemma rounds_store_seq_other (h : run_history) (r : seq 'I_M) (s : store) (x : Cv) : (forall i, i \in r -> x != a_ i) -> (forall i, i \in r
  -> x != y_ i) -> (forall i, i \in r -> x != b_ i) -> (forall i, i \in r -> x != y'_ i) -> (forall i, i \in r -> x != d_ i) -> x != Xv -> x
  != Zv -> rounds_store_seq h r s x = s x.
Proof.
have write_round_choice_other : forall (c : round_choice) (i : 'I_M) (s : store) (x : Cv), x != a_ i -> x != y_ i -> x != b_ i -> x != y'_ i -> x != d_ i -> x != Xv -> x != Zv -> write_round_choice c i s x = s x.
{ clear x s r h; move=> c i s x Hxa Hxy Hxb Hxy' Hxd HxX HxZ. rewrite /write_round_choice /round_sift_store /round_measure_store /round_prepare_store. by rewrite store_set_other // store_set_other // store_set_other // store_set_other // store_set_other // store_set_other // store_set_other. } move=> Hxa Hxy Hxb Hxy' Hxd HxX HxZ. elim: r s Hxa Hxy Hxb Hxy' Hxd => [|i r IHr] s Hxa Hxy Hxb Hxy' Hxd //=. rewrite IHr.
  - by apply: write_round_choice_other; [exact: Hxa i (mem_head i r) | exact: Hxy i (mem_head i r) | exact: Hxb i (mem_head i r) | exact: Hxy' i (mem_head i r) | exact: Hxd i (mem_head i r) | exact: HxX | exact: HxZ].
  - by move=> j Hj; apply: Hxa; rewrite in_cons Hj orbT.
  - by move=> j Hj; apply: Hxy; rewrite in_cons Hj orbT.
  - by move=> j Hj; apply: Hxb; rewrite in_cons Hj orbT.
  - by move=> j Hj; apply: Hxy'; rewrite in_cons Hj orbT.
  - by move=> j Hj; apply: Hxd; rewrite in_cons Hj orbT. Qed.

Lemma rounds_store_other (h : run_history) (s : store) (x : Cv) : (forall i, x != a_ i) -> (forall i, x != y_ i) -> (forall i, x != b_ i) ->
  (forall i, x != y'_ i) -> (forall i, x != d_ i) -> x != Xv -> x != Zv -> rounds_store h s x = s x.
Proof. move=> Hxa Hxy Hxb Hxy' Hxd HxX HxZ; rewrite /rounds_store. by apply: rounds_store_seq_other; [move=> i _; exact: Hxa i | move=> i _; exact: Hxy i | move=> i _; exact: Hxb i | move=> i _; exact: Hxy' i | move=> i _; exact: Hxd i | exact: HxX | exact: HxZ]. Qed.

Fact write_round_choice_a (c : round_choice) (i : 'I_M) (s : store) : a_ i != y_ i -> a_ i != b_ i -> a_ i != y'_ i -> a_ i != d_ i -> a_ i
  != Xv -> a_ i != Zv -> write_round_choice c i s (a_ i) = choice_a c.
Proof. move=> Hay Hab Hay' Had HaX HaZ. rewrite /write_round_choice /round_sift_store /round_measure_store /round_prepare_store. by rewrite store_set_other // store_set_other // store_set_other // store_set_other // store_set_other // store_set_other // store_set_same. Qed.

Fact write_round_choice_y (c : round_choice) (i : 'I_M) (s : store) : y_ i != b_ i -> y_ i != y'_ i -> y_ i != d_ i -> y_ i != Xv -> y_ i
  != Zv -> write_round_choice c i s (y_ i) = choice_y c.
Proof. move=> Hyb Hyy' Hyd HyX HyZ. rewrite /write_round_choice /round_sift_store /round_measure_store /round_prepare_store. by rewrite store_set_other // store_set_other // store_set_other // store_set_other // store_set_other // store_set_same. Qed.

Fact write_round_choice_b (c : round_choice) (i : 'I_M) (s : store) : b_ i != y'_ i -> b_ i != d_ i -> b_ i != Xv -> b_ i != Zv ->
  write_round_choice c i s (b_ i) = choice_b c.
Proof. move=> Hby' Hbd HbX HbZ; rewrite /write_round_choice /round_sift_store /round_measure_store. by rewrite store_set_other // store_set_other // store_set_other // store_set_other // store_set_same. Qed.

Fact write_round_choice_y' (c : round_choice) (i : 'I_M) (s : store) : y'_ i != d_ i -> y'_ i != Xv -> y'_ i != Zv -> write_round_choice c
  i s (y'_ i) = choice_y' c.
Proof. move=> Hy'd Hy'X Hy'Z; rewrite /write_round_choice /round_sift_store. by rewrite store_set_other // store_set_other // store_set_other // round_measure_store_y'. Qed.

Fact write_round_choice_d (c : round_choice) (i : 'I_M) (s : store) : d_ i != Xv -> d_ i != Zv -> write_round_choice c i s (d_ i) = vbool
  (choice_y' c != outEmpty).
Proof. move=> HdX HdZ; rewrite /write_round_choice /round_sift_store. by rewrite store_set_other // store_set_other // store_set_same. Qed.

Fact rounds_store_seq_slot (h : run_history) (r : seq 'I_M) (i : 'I_M) (x : Cv) (v : V) (s : store) : i \in r -> uniq r -> (forall j, j !=
  i -> x != a_ j) -> (forall j, j != i -> x != y_ j) -> (forall j, j != i -> x != b_ j) -> (forall j, j != i -> x != y'_ j) -> (forall j, j
  != i -> x != d_ j) -> x != Xv -> x != Zv -> (forall u : store, write_round_choice (h.1 i) i u x = v) -> rounds_store_seq h r s x = v.
Proof.
  move=> Hir Huniq Hxa Hxy Hxb Hxy' Hxd HxX HxZ Hw. elim: r s Hir Huniq => [|j r IHr] s. by rewrite in_nil. move=> Hir Huniq; move/andP: Huniq => [Hjr Huniq]; move: Hir; rewrite in_cons => /orP [/eqP Hji | Hir].
  - subst j; rewrite /=. have Hne t : t \in r -> t != i by move=> Htr; apply/eqP=> Hti; move: Hjr; rewrite -Hti Htr. rewrite (@rounds_store_seq_other h r (write_trace_round h.1 i s) x).
    + by rewrite /write_trace_round; exact: Hw.
    + by move=> t Htr; apply: Hxa; exact: Hne.
    + by move=> t Htr; apply: Hxy; exact: Hne.
    + by move=> t Htr; apply: Hxb; exact: Hne.
    + by move=> t Htr; apply: Hxy'; exact: Hne.
    + by move=> t Htr; apply: Hxd; exact: Hne.
    + exact: HxX.
    + exact: HxZ.
  - by rewrite /=; apply: IHr. Qed.

Lemma rounds_store_slot (h : run_history) (i : 'I_M) (x : Cv) (v : V) (s : store) : (forall j, j != i -> x != a_ j) -> (forall j, j != i ->
  x != y_ j) -> (forall j, j != i -> x != b_ j) -> (forall j, j != i -> x != y'_ j) -> (forall j, j != i -> x != d_ j) -> x != Xv -> x != Zv
  -> (forall u : store, write_round_choice (h.1 i) i u x = v) -> rounds_store h s x = v.
Proof. move=> Hxa Hxy Hxb Hxy' Hxd HxX HxZ Hw; rewrite /rounds_store. by apply: (rounds_store_seq_slot (i := i)); [rewrite mem_enum | exact: enum_uniq | exact: Hxa | exact: Hxy | exact: Hxb | exact: Hxy' | exact: Hxd | exact: HxX | exact: HxZ | exact: Hw]. Qed.

Lemma rounds_store_y (h : run_history) (s : store) (i : 'I_M) : (forall j, j != i -> y_ i != a_ j) -> (forall j, y_ i != b_ j) -> (forall j,
  j != i -> y_ i != y_ j) -> (forall j, y_ i != y'_ j) -> (forall j, y_ i != d_ j) -> y_ i != Xv -> y_ i != Zv -> rounds_store h s (y_ i) =
  hist_y h i.
Proof.
  move=> Hya Hyb Hyy Hyy' Hyd HyX HyZ. apply: (rounds_store_slot (i := i)); [exact: Hya | exact: Hyy | move=> j _; exact: Hyb | move=> j _; exact: Hyy' | move=> j _; exact: Hyd | exact: HyX | exact: HyZ | move=> u]. rewrite /hist_y /hist_choice. by apply: write_round_choice_y; [exact: Hyb | exact: Hyy' | exact: Hyd | exact: HyX | exact: HyZ]. Qed.

Lemma rounds_store_y' (h : run_history) (s : store) (i : 'I_M) : (forall j, y'_ i != a_ j) -> (forall j, y'_ i != y_ j) -> (forall j, y'_ i
  != b_ j) -> (forall j, j != i -> y'_ i != y'_ j) -> (forall j, y'_ i != d_ j) -> y'_ i != Xv -> y'_ i != Zv -> rounds_store h s (y'_ i) =
  hist_y' h i.
Proof.
  move=> Hy'a Hy'y Hy'b Hy'y' Hy'd Hy'X Hy'Z. apply: (rounds_store_slot (i := i)); [move=> j _; exact: Hy'a | move=> j _; exact: Hy'y | move=> j _; exact: Hy'b | exact: Hy'y' | move=> j _; exact: Hy'd | exact: Hy'X | exact: Hy'Z | move=> u]. rewrite /hist_y' /hist_choice.
    by apply: write_round_choice_y'; [exact: Hy'd | exact: Hy'X | exact: Hy'Z]. Qed.

Definition announce_store (s : store) : store := store_set s Pvar (tr_app_rounds (fun i => (s (a_ i), s (b_ i), s (d_ i))) (s Pvar)).
Lemma announce_store_other (s : store) (x : Cv) : x != Pvar -> announce_store s x = s x.
Proof. by move=> HxP; rewrite /announce_store store_set_other. Qed.

Definition paramest_store (h : run_history) (s : store) : store := let s1 := store_set s Kv (hist_K h) in let s2 := store_set s1 XA (bits_on
  (vset_of (s1 Kv)) (fun i => s1 (y_ i))) in let s3 := store_set s2 XB (bits_on (vset_of (s2 Kv)) (fun i => s2 (y'_ i))) in let s4 :=
  store_set s3 ZA (test_bits_on (vset_of (s3 Zv)) (fun i => s3 (y_ i))) in let s5 := store_set s4 ZB (test_bits_on (vset_of (s4 Zv)) (fun i
  => s4 (y'_ i))) in let s6 := store_set s5 Pvar (tr_app_pe (s5 Kv) (s5 ZA) (s5 ZB) (s5 Pvar)) in store_set s6 lamv (vrat (err_count (s6 ZA)
  (s6 ZB)) #|vset_of (s6 Zv)|).
Tactic Notation "pe_sets" constr(s) ident(s1) ident(s2) ident(s3) ident(s4) ident(s5) ident(s6) := set s1 := store_set s Kv _; set s2 :=
  store_set s1 XA _; set s3 := store_set s2 XB _; set s4 := store_set s3 ZA _; set s5 := store_set s4 ZB _; set s6 := store_set s5 Pvar _.
Definition key_sample_deviation_store (mu : nat -> R) (s : store) : bool := let z_count := #|vset_of (s Zv)| in (err_count (s XA) (s XB))%:R
  / n%:R >= (err_count (s ZA) (s ZB))%:R / z_count%:R + mu z_count.
Definition key_sample_deviation_event (mu : nat -> R) (t : round_trace) (s : store) : {set V} := [set K : V | key_sample_deviation_store mu
  (paramest_store (t, ((K, bot), bot)) s)].
Lemma paramest_store_future_irrel (t : round_trace) (K g f g' f' : V) (s : store) : paramest_store (t, ((K, g), f)) s = paramest_store (t,
  ((K, g'), f')) s.
Proof. by rewrite /paramest_store /hist_K. Qed.
Lemma paramest_store_other (h : run_history) (s : store) (x : Cv) : x != Kv -> x != XA -> x != XB -> x != ZA -> x != ZB -> x != Pvar -> x !=
  lamv -> paramest_store h s x = s x.
Proof. move=> HxK HxXA HxXB HxZA HxZB HxP Hxlam; rewrite /paramest_store. by rewrite store_set_other // store_set_other // store_set_other // store_set_other // store_set_other // store_set_other // store_set_other. Qed.
Lemma paramest_store_XA (h : run_history) (s : store) : XA != XB -> XA != ZA -> XA != ZB -> XA != Pvar -> XA != lamv -> let s1 := store_set
  s Kv (hist_K h) in paramest_store h s XA = bits_on (vset_of (s1 Kv)) (fun i => s1 (y_ i)).
Proof. move=> HXAB HXAZA HXAZB HXAP HXAlam; rewrite /paramest_store; pe_sets s s1 s2 s3 s4 s5 s6. by rewrite store_set_other // /s6 store_set_other // /s5 store_set_other // /s4 store_set_other // /s3 store_set_other // /s2 store_set_same. Qed.
Lemma paramest_store_XB (h : run_history) (s : store) : XB != ZA -> XB != ZB -> XB != Pvar -> XB != lamv -> let s1 := store_set s Kv (hist_K
  h) in let s2 := store_set s1 XA (bits_on (vset_of (s1 Kv)) (fun i => s1 (y_ i))) in paramest_store h s XB = bits_on (vset_of (s2 Kv)) (fun
  i => s2 (y'_ i)).
Proof. move=> HXBZA HXBZB HXBP HXBlam; rewrite /paramest_store; pe_sets s s1 s2 s3 s4 s5 s6. by rewrite store_set_other // /s6 store_set_other // /s5 store_set_other // /s4 store_set_other // /s3 store_set_same. Qed.
Lemma paramest_store_ZA (h : run_history) (s : store) : ZA != ZB -> ZA != Pvar -> ZA != lamv -> let s1 := store_set s Kv (hist_K h) in let
  s2 := store_set s1 XA (bits_on (vset_of (s1 Kv)) (fun i => s1 (y_ i))) in let s3 := store_set s2 XB (bits_on (vset_of (s2 Kv)) (fun i =>
  s2 (y'_ i))) in paramest_store h s ZA = test_bits_on (vset_of (s3 Zv)) (fun i => s3 (y_ i)).
Proof. move=> HZAZB HZAP HZAlam; rewrite /paramest_store; pe_sets s s1 s2 s3 s4 s5 s6. by rewrite store_set_other // /s6 store_set_other // /s5 store_set_other // /s4 store_set_same. Qed.
Lemma paramest_store_ZB (h : run_history) (s : store) : ZB != Pvar -> ZB != lamv -> let s1 := store_set s Kv (hist_K h) in let s2 :=
  store_set s1 XA (bits_on (vset_of (s1 Kv)) (fun i => s1 (y_ i))) in let s3 := store_set s2 XB (bits_on (vset_of (s2 Kv)) (fun i => s2 (y'_
  i))) in let s4 := store_set s3 ZA (test_bits_on (vset_of (s3 Zv)) (fun i => s3 (y_ i))) in paramest_store h s ZB = test_bits_on (vset_of
  (s4 Zv)) (fun i => s4 (y'_ i)).
Proof. move=> HZBP HZBlam; rewrite /paramest_store; pe_sets s s1 s2 s3 s4 s5 s6. by rewrite store_set_other // /s6 store_set_other // /s5 store_set_same. Qed.
Fact key_sample_deviation_store_paramest_bits (mu : nat -> R) (t : round_trace) (K g f : V) (s : store) : pewall (Zv != Kv -> Zv != XA ->
  Zv != XB -> Zv != ZA -> Zv != ZB -> Zv != Pvar -> Zv != lamv -> Kv != XA -> Kv != XB -> Kv != ZA -> Kv != ZB -> Kv != Pvar -> Kv != lamv
  -> (forall i, y_ i != Kv) -> (forall i, y_ i != XA) -> (forall i, y_ i != XB) -> (forall i, y'_ i != Kv) -> (forall i, y'_ i != XA) ->
  (forall i, y'_ i != XB) -> (forall i, y'_ i != ZA) -> key_sample_deviation_store mu (paramest_store (t, ((K, g), f)) s) = ((err_count
  (bits_on (vset_of K) (fun i => s (y_ i))) (bits_on (vset_of K) (fun i => s (y'_ i))))%:R / n%:R >= (err_count (test_bits_on (vset_of (s
  Zv)) (fun i => s (y_ i))) (test_bits_on (vset_of (s Zv)) (fun i => s (y'_ i))))%:R / (#|vset_of (s Zv)|)%:R + mu #|vset_of (s Zv)|)).
Proof.
  move=> HXAB HXAZA HXAZB HXAP HXAlam HXBZA HXBZB HXBP HXBlam HZAZB HZAP HZAlam HZBP HZBlam HZK HZXA HZXB HZZA HZZB HZP HZlam HKXA HKXB HKZA HKZB HKP HKlam HyK HyXA HyXB Hy'K Hy'XA Hy'XB Hy'ZA. set h := (t, ((K, g), f)); set pe := paramest_store h s. have HXAread : pe XA = bits_on (vset_of K) (fun i => s (y_ i)).
  { rewrite /pe (paramest_store_XA h s HXAB HXAZA HXAZB HXAP HXAlam); set s1 := store_set s Kv (hist_K h). have HK : vset_of (s1 Kv) = vset_of K by rewrite /s1 /h /hist_K store_set_same. have Hy : (fun i => s1 (y_ i)) = (fun i => s (y_ i)) by apply/funext=> i; rewrite /s1 store_set_other. by rewrite HK Hy. } have HXBread : pe XB = bits_on (vset_of K) (fun i => s (y'_ i)).
  { rewrite /pe (paramest_store_XB h s HXBZA HXBZB HXBP HXBlam); set s1 := store_set s Kv (hist_K h). set s2 := store_set s1 XA (bits_on (vset_of (s1 Kv)) (fun i => s1 (y_ i))). have HK : vset_of (s2 Kv) = vset_of K by rewrite /s2 store_set_other // /s1 /h /hist_K store_set_same. have Hy' : (fun i => s2 (y'_ i)) = (fun i => s (y'_ i)) by apply/funext=> i; rewrite /s2 store_set_other // /s1 store_set_other. by rewrite HK Hy'. } have HZAread : pe ZA = test_bits_on (vset_of (s Zv)) (fun i => s (y_ i)).
  { rewrite /pe (paramest_store_ZA h s HZAZB HZAP HZAlam); set s1 := store_set s Kv (hist_K h). set s2 := store_set s1 XA (bits_on (vset_of (s1 Kv)) (fun i => s1 (y_ i))). set s3 := store_set s2 XB (bits_on (vset_of (s2 Kv)) (fun i => s2 (y'_ i))). have HZ : vset_of (s3 Zv) = vset_of (s Zv) by rewrite /s3 store_set_other // /s2 store_set_other // /s1 store_set_other. have Hy : (fun i => s3 (y_ i)) = (fun i => s (y_ i)).
    { by apply/funext=> i; rewrite /s3 store_set_other // /s2 store_set_other // /s1 store_set_other. } by rewrite HZ Hy. } have HZBread : pe ZB = test_bits_on (vset_of (s Zv)) (fun i => s (y'_ i)).
  { rewrite /pe (paramest_store_ZB h s HZBP HZBlam); set s1 := store_set s Kv (hist_K h). set s2 := store_set s1 XA (bits_on (vset_of (s1 Kv)) (fun i => s1 (y_ i))). set s3 := store_set s2 XB (bits_on (vset_of (s2 Kv)) (fun i => s2 (y'_ i))). set s4 := store_set s3 ZA (test_bits_on (vset_of (s3 Zv)) (fun i => s3 (y_ i))). have HZ : vset_of (s4 Zv) = vset_of (s Zv). by rewrite /s4 store_set_other // /s3 store_set_other // /s2 store_set_other // /s1 store_set_other. have Hy' : (fun i => s4 (y'_ i)) = (fun i => s (y'_ i)).
    { by apply/funext=> i; rewrite /s4 store_set_other // /s3 store_set_other // /s2 store_set_other // /s1 store_set_other. } by rewrite HZ Hy'. } have HZread : pe Zv = s Zv by rewrite /pe paramest_store_other. by rewrite /key_sample_deviation_store -/pe HZread HXAread HXBread HZAread HZBread. Qed.
Definition errcorr_seed_store (s : store) : store := let s1 := store_set s pECv (ir_pub leakEC (s XA) (s XB)) in store_set s1 Xhatv (ir_dec
  (s1 pECv) (s1 XB)).
Definition errcorr_store (h : run_history) (s : store) : store := let s1 := errcorr_seed_store s in let s2 := store_set s1 gv (hist_g h) in
  let s3 := store_set s2 tAv (verify_hash (s2 gv) (s2 XA)) in let s4 := store_set s3 tBv (verify_hash (s3 gv) (s3 Xhatv)) in store_set s4
  Pvar (tr_app_ec (s4 pECv) (s4 gv) (s4 tAv) (s4 Pvar)).
Tactic Notation "ec_sets" constr(s) ident(s1) ident(s2) ident(s3) ident(s4) := set s1 := errcorr_seed_store s; set s2 := store_set s1 gv _;
  set s3 := store_set s2 tAv _; set s4 := store_set s3 tBv _.
Lemma errcorr_store_f_irrel (t : round_trace) (K g f f' : V) (s : store) : errcorr_store (t, ((K, g), f)) s = errcorr_store (t, ((K, g),
  f')) s.
Proof. by rewrite /errcorr_store /hist_g. Qed.
Fact errcorr_paramest_store_f_irrel (t : round_trace) (K g f f' : V) (s : store) : errcorr_store (t, ((K, g), f)) (paramest_store (t, ((K,
  g), f)) s) = errcorr_store (t, ((K, g), f')) (paramest_store (t, ((K, g), f')) s).
Proof. rewrite (paramest_store_future_irrel t K g f g f' s). exact: errcorr_store_f_irrel. Qed.
Lemma errcorr_seed_store_other (s : store) (x : Cv) : x != pECv -> x != Xhatv -> errcorr_seed_store s x = s x.
Proof. by move=> Hxp HxXhat; rewrite /errcorr_seed_store store_set_other // store_set_other. Qed.
Lemma errcorr_store_other (h : run_history) (s : store) (x : Cv) : x != pECv -> x != Xhatv -> x != gv -> x != tAv -> x != tBv -> x != Pvar
  -> errcorr_store h s x = s x.
Proof. move=> Hxp HxXhat Hxg HxtA HxtB HxP; rewrite /errcorr_store. by rewrite store_set_other // store_set_other // store_set_other // store_set_other // errcorr_seed_store_other. Qed.
Lemma errcorr_store_tAv (h : run_history) (s : store) : tAv != tBv -> tAv != Pvar -> let s1 := errcorr_seed_store s in let s2 := store_set
  s1 gv (hist_g h) in errcorr_store h s tAv = verify_hash (s2 gv) (s2 XA).
Proof. move=> HtAtB HtAP; rewrite /errcorr_store; ec_sets s s1 s2 s3 s4. by rewrite store_set_other // /s4 store_set_other // /s3 store_set_same. Qed.
Lemma errcorr_store_tBv (h : run_history) (s : store) : tBv != Pvar -> let s1 := errcorr_seed_store s in let s2 := store_set s1 gv (hist_g
  h) in let s3 := store_set s2 tAv (verify_hash (s2 gv) (s2 XA)) in errcorr_store h s tBv = verify_hash (s3 gv) (s3 Xhatv).
Proof. move=> HtBP; rewrite /errcorr_store; ec_sets s s1 s2 s3 s4. by rewrite store_set_other // /s4 store_set_same. Qed.
Lemma errcorr_store_XA (h : run_history) (s : store) : XA != pECv -> XA != Xhatv -> XA != gv -> XA != tAv -> XA != tBv -> XA != Pvar ->
  errcorr_store h s XA = s XA.
Proof. exact: errcorr_store_other. Qed.
Lemma errcorr_seed_store_Xhatv (s : store) : XB != pECv -> errcorr_seed_store s Xhatv = ir_dec (ir_pub leakEC (s XA) (s XB)) (s XB).
Proof. move=> HXBp; rewrite /errcorr_seed_store; set s1 := store_set s pECv (ir_pub leakEC (s XA) (s XB)). by rewrite store_set_same /s1 store_set_same store_set_other. Qed.
Lemma errcorr_store_Xhatv (h : run_history) (s : store) : XB != pECv -> xhwall (errcorr_store h s Xhatv = ir_dec (ir_pub leakEC (s XA) (s
  XB)) (s XB)).
Proof. move=> HXBp HXg HXtA HXtB HXP; rewrite /errcorr_store; ec_sets s s1 s2 s3 s4. rewrite store_set_other // /s4 store_set_other // /s3 store_set_other // /s2 store_set_other // /s1; exact: errcorr_seed_store_Xhatv. Qed.
Definition privamp_store (h : run_history) (s : store) : store := let s1 := store_set s fv (hist_f h) in let s2 := store_set s1 Sv
  (privacy_hash l (s1 fv) (s1 XA)) in let s3 := store_set s2 Shv (privacy_hash l (s2 fv) (s2 Xhatv)) in store_set s3 Pvar (tr_app_pa (s3 fv)
  (s3 Pvar)).
Definition abort_store (s : store) : store := store_set (store_set (store_set s abortv (vbool true)) Sv bot) Shv bot.
Lemma abort_store_abort (s : store) : abortv != Sv -> abortv != Shv -> abort_store s abortv = vbool true.
Proof. by move=> HAS HAH; rewrite /abort_store store_set_other // store_set_other // store_set_same. Qed.
Lemma abort_store_not_pass (s : store) : vbool true != vbool false -> abortv != Sv -> abortv != Shv -> (abort_store s abortv == vbool false)
  = false.
Proof. move=> Htf HAS HAH; by rewrite (abort_store_abort s HAS HAH) (negbTE Htf). Qed.
Fact abort_store_Sv (s : store) : Sv != Shv -> abort_store s Sv = bot.
Proof. by move=> HSH; rewrite /abort_store store_set_other // store_set_same. Qed.
Fact abort_store_Shv (s : store) : abort_store s Shv = bot.
Proof. by rewrite /abort_store store_set_same. Qed.
Lemma privamp_store_Sv (h : run_history) (s : store) : Sv != Shv -> Sv != Pvar -> let s1 := store_set s fv (hist_f h) in privamp_store h s
  Sv = privacy_hash l (s1 fv) (s1 XA).
Proof. move=> HSH HSP; rewrite /privamp_store; set s1 := store_set s fv (hist_f h); set s2 := store_set s1 Sv (privacy_hash l (s1 fv) (s1 XA)). by set s3 := store_set s2 Shv (privacy_hash l (s2 fv) (s2 Xhatv)); rewrite store_set_other // /s3 store_set_other // /s2 store_set_same. Qed.
Lemma privamp_store_Shv (h : run_history) (s : store) : Shv != Pvar -> let s1 := store_set s fv (hist_f h) in let s2 := store_set s1 Sv
  (privacy_hash l (s1 fv) (s1 XA)) in privamp_store h s Shv = privacy_hash l (s2 fv) (s2 Xhatv).
Proof. move=> HSP; rewrite /privamp_store; set s1 := store_set s fv (hist_f h); set s2 := store_set s1 Sv (privacy_hash l (s1 fv) (s1 XA)). by set s3 := store_set s2 Shv (privacy_hash l (s2 fv) (s2 Xhatv)); rewrite store_set_other // /s3 store_set_same. Qed.
Lemma privamp_store_other (h : run_history) (s : store) (x : Cv) : x != fv -> x != Sv -> x != Shv -> x != Pvar -> privamp_store h s x = s x.
Proof. by move=> Hxf HxS HxSh HxP; rewrite /privamp_store; rewrite store_set_other // store_set_other // store_set_other // store_set_other. Qed.
Lemma denote_abort_single (qA : {set L}) (EA : ADVq qA) (s : store) (rho : 'F[HL]_setT) : DSg qA EA (ABs) s rho = cq_single (abort_store s)
  rho.
Proof. rewrite /Abort_cmd /abort_store denote_seq_single denote_assign_bind_single; rewrite denote_seq_single denote_assign_bind_single. by rewrite denote_assign_single. Qed.
Fact denote_paramest_single_sum (qA : {set L}) (EA : ADVq qA) (t : round_trace) (g f : V) (s : store) (rho : 'F[HL]_setT) : DSg qA EA (PEs)
  s rho = \sum_K cq_single (paramest_store (t, ((K, g), f)) s) ((key_sample_mass s K)%:C *: rho).
Proof.
  rewrite /ParamEst denote_seq_sample_single_sum; apply: eq_bigr => K _. rewrite /key_sample_mass /paramest_K_mu /has_key_sample cq_single_scale. congr (_ *: _). set s1 := store_set s Kv K; rewrite denote_seq_single denote_assign_bind_single. set s2 := store_set s1 XA (bits_on (vset_of (s1 Kv)) (fun i => s1 (y_ i))); rewrite denote_seq_single denote_assign_bind_single. set s3 := store_set s2 XB (bits_on (vset_of (s2 Kv)) (fun i => s2 (y'_ i))); rewrite denote_seq_single denote_assign_bind_single. set s4 := store_set s3 ZA (test_bits_on (vset_of (s3 Zv)) (fun i => s3 (y_ i))); rewrite denote_seq_single denote_assign_bind_single. set s5 := store_set s4 ZB (test_bits_on (vset_of (s4 Zv)) (fun i => s4 (y'_ i))); rewrite denote_seq_single denote_assign_bind_single. set s6 := store_set s5 Pvar (tr_app_pe (s5 Kv) (s5 ZA) (s5 ZB) (s5 Pvar)); rewrite denote_assign_single. by rewrite /paramest_store /hist_K /s1 /s2 /s3 /s4 /s5 /s6 /alice_bits /bob_bits. Qed.
Lemma denote_privamp_single_sum (qA : {set L}) (EA : ADVq qA) (t : round_trace) (K g : V) (s : store) (rho : 'F[HL]_setT) : DSg qA EA (PAs)
  s rho = \sum_f cq_single (privamp_store (t, ((K, g), f)) s) ((unif_pseed s f)%:C *: rho).
Proof.
  rewrite /PrivAmp denote_seq_sample_single_sum; apply: eq_bigr => f _. rewrite cq_single_scale. congr (_ *: _). set s1 := store_set s fv f; rewrite denote_seq_assign_single; set s2 := store_set s1 Sv (privacy_hash l (s1 fv) (s1 XA)). rewrite denote_seq_assign_single; set s3 := store_set s2 Shv (privacy_hash l (s2 fv) (s2 Xhatv)); rewrite denote_assign_single. by rewrite /privamp_store /hist_f /s1 /s2 /s3. Qed.
Definition pe_failed (s : store) : bool := replay_pe_fail s.
Lemma pe_fail_replayE (s : store) : PFs s = pe_failed s.
Proof. by rewrite /pe_fail /pe_failed /replay_pe_fail /sift_ok /replay_sift_ok /has_key_sample /has_test_sample /pe_error_high /replay_pe_error_high. Qed.
Definition final_store (h : run_history) (s : store) : store := let s0 := start_store s in let s1 := rounds_store h s0 in let s2 :=
  announce_store s1 in let s3 := paramest_store h s2 in if pe_failed s3 then abort_store s3 else let s4 := errcorr_store h s3 in if s4 tAv
  != s4 tBv then abort_store s4 else privamp_store h s4.
Fact final_store_pe_abort (h : run_history) (s : store) : pe_failed (paramest_store h (announce_store (rounds_store h (start_store s)))) ->
  final_store h s = abort_store (paramest_store h (announce_store (rounds_store h (start_store s)))).
Proof. by move=> Hpe; rewrite /final_store Hpe. Qed.
Fact final_store_verify_abort (h : run_history) (s : store) : let spe := paramest_store h (announce_store (rounds_store h (start_store s)))
  in let sec := errcorr_store h spe in ~~ pe_failed spe -> sec tAv != sec tBv -> final_store h s = abort_store sec.
Proof. rewrite /final_store; set spe := paramest_store h (announce_store (rounds_store h (start_store s))); set sec := errcorr_store h spe. by move=> Hpe Hverify; rewrite (negbTE Hpe) Hverify. Qed.
Lemma final_store_privamp (h : run_history) (s : store) : let spe := paramest_store h (announce_store (rounds_store h (start_store s))) in
  let sec := errcorr_store h spe in ~~ pe_failed spe -> ~~ (sec tAv != sec tBv) -> final_store h s = privamp_store h sec.
Proof. rewrite /final_store; set spe := paramest_store h (announce_store (rounds_store h (start_store s))); set sec := errcorr_store h spe. by move=> Hpe Hverify; rewrite (negbTE Hpe) (negbTE Hverify). Qed.
Lemma final_store_privamp_pass (h : run_history) (s : store) : let spe := paramest_store h (announce_store (rounds_store h (start_store s)))
  in let sec := errcorr_store h spe in ~~ pe_failed spe -> ~~ (sec tAv != sec tBv) -> abwall (final_store h s abortv == vbool false).
Proof.
  have final_store_privamp_abort_value : forall (h : run_history) (s : store), let spe := paramest_store h (announce_store (rounds_store h (start_store s))) in let sec := errcorr_store h spe in ~~ pe_failed spe -> ~~ (sec tAv != sec tBv) -> abortv != fv -> abortv != Sv -> abortv != Shv -> abortv != Pvar -> final_store h s abortv = sec abortv.
  { move=> {}h {}s. move=> spe sec Hpe Hverify HAf HAS HAH HAP. rewrite /final_store -/spe (negbTE Hpe) -/sec (negbTE Hverify). exact: privamp_store_other. } move=> spe sec Hpe Hverify Ha Hy Hb Hy' Hd HX HZ HP HK HXA HXB HZA HZB Hlam HpEC HXhat Hg HtA HtB HAf HAS HAH. rewrite (final_store_privamp_abort_value h s) // /sec (errcorr_store_other (x := abortv) h spe) //. rewrite /spe (paramest_store_other (x := abortv) h (announce_store (rounds_store h (start_store s)))) //. by rewrite announce_store_other // rounds_store_other // start_store_abort eqxx. Qed.
Lemma final_store_XA (h : run_history) (s : store) : XA != abortv -> XA != Sv -> XA != Shv -> XA != pECv -> XA != Xhatv -> XA != gv -> XA !=
  tAv -> XA != tBv -> XA != Pvar -> XA != fv -> final_store h s XA = paramest_store h (announce_store (rounds_store h (start_store s))) XA.
Proof.
  move=> HXAabort HXAS HXASh HXAp HXAXhat HXAg HXAtA HXAtB HXAP HXAf; rewrite /final_store. set spe := paramest_store h (announce_store (rounds_store h (start_store s))). case: (pe_failed spe).
  - rewrite /abort_store. rewrite (store_set_other (x := Shv) (y := XA) (store_set (store_set spe abortv (vbool true)) Sv bot) bot HXASh).
    rewrite (store_set_other (x := Sv) (y := XA) (store_set spe abortv (vbool true)) bot HXAS). by rewrite (store_set_other (x := abortv) (y := XA) spe (vbool true) HXAabort). set sec := errcorr_store h spe. case: (sec tAv != sec tBv).
  - rewrite /abort_store. rewrite (store_set_other (x := Shv) (y := XA) (store_set (store_set sec abortv (vbool true)) Sv bot) bot HXASh).
    rewrite (store_set_other (x := Sv) (y := XA) (store_set sec abortv (vbool true)) bot HXAS). rewrite (store_set_other (x := abortv) (y := XA) sec (vbool true) HXAabort). exact: errcorr_store_XA.
  - rewrite (privamp_store_other (x := XA) h sec) //. exact: errcorr_store_XA. Qed.
Fact final_store_XA_bits_on (h : run_history) (s : store) : XA != abortv -> XA != Sv -> XA != Shv -> XA != pECv -> XA != Xhatv -> XA != gv
  -> XA != tAv -> XA != tBv -> XA != Pvar -> XA != fv -> XA != XB -> XA != ZA -> XA != ZB -> XA != lamv -> (forall i, y_ i != Kv) ->
  final_store h s XA = bits_on (vset_of (hist_K h)) (fun i => announce_store (rounds_store h (start_store s)) (y_ i)).
Proof.
  move=> HXAabort HXAS HXASh HXAp HXAXhat HXAg HXAtA HXAtB HXAP HXAf HXAXB HXAZA HXAZB HXAlam HyK. rewrite (final_store_XA h s HXAabort HXAS HXASh HXAp HXAXhat HXAg HXAtA HXAtB HXAP HXAf). rewrite (paramest_store_XA h (announce_store (rounds_store h (start_store s))) HXAXB HXAZA HXAZB HXAP HXAlam). by rewrite store_set_same; congr bits_on; apply/funext => i; rewrite store_set_other. Qed.
Fact final_store_abort_flag (h : run_history) (s : store) : abwall ((final_store h s abortv == vbool true) || (final_store h s abortv ==
  vbool false)).
Proof.
  move=> Ha Hy Hb Hy' Hd HX HZ HP HK HXA HXB HZA HZB Hlam HpEC HXhat Hg HtA HtB Hf HS HSh; rewrite /final_store; set s0 := start_store s.
    set s1 := rounds_store h s0; set s2 := announce_store s1; set s3 := paramest_store h s2. case Hpe: (pe_failed s3). by rewrite abort_store_abort // eqxx. set s4 := errcorr_store h s3. case Hverify: (s4 tAv != s4 tBv). by rewrite abort_store_abort // eqxx. rewrite (privamp_store_other (x := abortv) h s4) // /s4 (errcorr_store_other (x := abortv) h s3) //. rewrite /s3 (paramest_store_other (x := abortv) h s2) // /s2 (announce_store_other (x := abortv) s1) //. by rewrite /s1 (rounds_store_other (x := abortv) h s0) // /s0 start_store_abort eqxx orbT. Qed.
Fact final_store_abort_f_irrel (t : round_trace) (K g f f' : V) (s : store) : abortv != fv -> abortv != Sv -> abortv != Shv -> abortv !=
  Pvar -> final_store (t, ((K, g), f)) s abortv = final_store (t, ((K, g), f')) s abortv.
Proof.
  move=> HAf HAS HAH HAP; rewrite /final_store /=; set s0 := start_store s; set s1 := rounds_store _ s0. set s2 := announce_store s1; rewrite (paramest_store_future_irrel t K g f g f' s2); set s3 := paramest_store _ s2. case: (pe_failed s3); first by []. rewrite (errcorr_store_f_irrel t K g f f' s3); set s4 := errcorr_store _ s3. case: (s4 tAv != s4 tBv); first by []. by transitivity (s4 abortv); [exact: privamp_store_other | symmetry; exact: privamp_store_other]. Qed.
Lemma final_store_pass_pe_ok (h : run_history) (s : store) : vbool true != vbool false -> abortv != Sv -> abortv != Shv -> final_store h s
  abortv == vbool false -> let spe := paramest_store h (announce_store (rounds_store h (start_store s))) in ~~ pe_failed spe.
Proof. move=> Htf HAS HAH Habort; set spe := paramest_store h (announce_store (rounds_store h (start_store s))). rewrite /final_store in Habort; rewrite -/spe in Habort *. case Hpe: (pe_failed spe). - by move: Habort; rewrite Hpe abort_store_not_pass. - by apply/negP=> Hbad; move: Hpe; rewrite Hbad. Qed.
Lemma final_store_Sv (h : run_history) (s : store) : vbool true != vbool false -> abortv != Sv -> abortv != Shv -> XA != fv -> Sv != Shv ->
  Sv != Pvar -> final_store h s abortv == vbool false -> let spe := paramest_store h (announce_store (rounds_store h (start_store s))) in
  let sec := errcorr_store h spe in final_store h s Sv = privacy_hash l (hist_f h) (sec XA).
Proof.
  move=> Htf HAS HAH HXAf HSS HSP Habort; set spe := paramest_store h (announce_store (rounds_store h (start_store s))). set sec := errcorr_store h spe. have Hpe := final_store_pass_pe_ok (h := h) (s := s) Htf HAS HAH Habort; rewrite -/spe in Hpe. have Hverify : ~~ (sec tAv != sec tBv).
  { rewrite /final_store -/spe (negbTE Hpe) -/sec in Habort. case Hbad: (sec tAv != sec tBv); last by []. by move: Habort; rewrite Hbad abort_store_not_pass. } rewrite (final_store_privamp (h := h) (s := s)) //. by rewrite -/spe -/sec (privamp_store_Sv h sec HSS HSP) store_set_same store_set_other. Qed.
Fact privamp_store_Shv_reduced (h : run_history) (s : store) : Shv != Pvar -> fv != Sv -> Xhatv != Sv -> Xhatv != fv -> privamp_store h s
  Shv = privacy_hash l (hist_f h) (s Xhatv).
Proof. move=> HShP HfS HXhatS HXhatf; rewrite (privamp_store_Shv h s HShP). by rewrite store_set_other // store_set_same store_set_other // store_set_other. Qed.
Fact final_store_Shv (h : run_history) (s : store) : vbool true != vbool false -> abortv != Sv -> abortv != Shv -> Xhatv != fv -> fv != Sv
  -> Xhatv != Sv -> Shv != Pvar -> final_store h s abortv == vbool false -> let spe := paramest_store h (announce_store (rounds_store h
  (start_store s))) in let sec := errcorr_store h spe in final_store h s Shv = privacy_hash l (hist_f h) (sec Xhatv).
Proof.
  move=> Htf HAS HAH HXhatf HfS HXhatS HShP Habort; set spe := paramest_store h (announce_store (rounds_store h (start_store s))). set sec := errcorr_store h spe. have Hpe := final_store_pass_pe_ok (h := h) (s := s) Htf HAS HAH Habort; rewrite -/spe in Hpe. have Hverify : ~~ (sec tAv != sec tBv).
  { rewrite /final_store -/spe (negbTE Hpe) -/sec in Habort. case Hbad: (sec tAv != sec tBv); last by []. by move: Habort; rewrite Hbad abort_store_not_pass. } by rewrite (final_store_privamp (h := h) (s := s)) //; rewrite -/spe -/sec (privamp_store_Shv_reduced h sec HShP HfS HXhatS HXhatf). Qed.
Lemma final_store_branch_shape (h : run_history) (s : store) : vbool true != vbool false -> abwall (Sv != Shv -> Sv != Pvar -> Shv != Pvar
  -> XA != fv -> Xhatv != fv -> fv != Sv -> Xhatv != Sv -> let spe := paramest_store h (announce_store (rounds_store h (start_store s))) in
  let sec := errcorr_store h spe in (final_store h s abortv = vbool true /\ final_store h s Sv = bot /\ final_store h s Shv = bot) \/
  (final_store h s abortv = vbool false /\ final_store h s Sv = privacy_hash l (hist_f h) (sec XA) /\ final_store h s Shv = privacy_hash l
  (hist_f h) (sec Xhatv))).
Proof.
  move=> Htf Ha Hy Hb Hy' Hd HX HZ HP HK HXA HXB HZA HZB Hlam HpEC HXhat Hg HtA HtB Hf HS HSh HSSh HSP HShP HXAf HXhatf HfS HXhatS. set spe := paramest_store h (announce_store (rounds_store h (start_store s))); set sec := errcorr_store h spe. case Hpe: (pe_failed spe).
  { left. have Efs : final_store h s = abort_store spe by exact: (final_store_pe_abort (h := h) (s := s) Hpe). by rewrite Efs; split; [apply: abort_store_abort | split; [apply: abort_store_Sv | exact: abort_store_Shv]]. } case Hverify: (sec tAv != sec tBv).
  { left. have Efs : final_store h s = abort_store sec.
    { apply: (final_store_verify_abort (h := h) (s := s)). - by rewrite -/spe Hpe. - by rewrite -/spe -/sec Hverify. } by rewrite Efs; split; [apply: abort_store_abort | split; [apply: abort_store_Sv | exact: abort_store_Shv]]. } right. have Hnpe : ~~ pe_failed spe by rewrite Hpe. have Hnvf : ~~ (sec tAv != sec tBv) by rewrite Hverify. have Habf : final_store h s abortv == vbool false by apply: (final_store_privamp_pass (h := h) (s := s) Hnpe Hnvf). by split; [apply/eqP | split; [exact: (final_store_Sv (h := h) (s := s) Htf HS HSh HXAf HSSh HSP Habf) | exact: (final_store_Shv (h := h) (s := s) Htf HS HSh HXhatf HfS HXhatS HShP Habf)]]. Qed.
Fact final_store_fv (h : run_history) (s : store) : vbool true != vbool false -> abortv != Sv -> abortv != Shv -> fv != Sv -> fv != Shv ->
  fv != Pvar -> final_store h s abortv == vbool false -> final_store h s fv = hist_f h.
Proof.
have privamp_store_fv : forall (h : run_history) (s : store), fv != Sv -> fv != Shv -> fv != Pvar -> privamp_store h s fv = hist_f h.
{ clear s h; move=> h s HfS HfSh HfP; rewrite /privamp_store. set s1 := store_set s fv (hist_f h); set s2 := store_set s1 Sv (privacy_hash l (s1 fv) (s1 XA)). set s3 := store_set s2 Shv (privacy_hash l (s2 fv) (s2 Xhatv)). by rewrite store_set_other // /s3 store_set_other // /s2 store_set_other // /s1 store_set_same. } move=> Htf HAS HAH HfS HfSh HfP Habort; set spe := paramest_store h (announce_store (rounds_store h (start_store s))). set sec := errcorr_store h spe. have Hpe := final_store_pass_pe_ok (h := h) (s := s) Htf HAS HAH Habort; rewrite -/spe in Hpe. have Hverify : ~~ (sec tAv != sec tBv).
  { rewrite /final_store -/spe (negbTE Hpe) -/sec in Habort. case Hbad: (sec tAv != sec tBv); last by []. by move: Habort; rewrite Hbad abort_store_not_pass. } by rewrite (final_store_privamp (h := h) (s := s)) //; exact: privamp_store_fv. Qed.
Fact final_store_pass_key_sample_enabled (h : run_history) (s : store) : vbool true != vbool false -> abortv != Sv -> abortv != Shv -> Xv
  != Kv -> Xv != XA -> Xv != XB -> Xv != ZA -> Xv != ZB -> Xv != Pvar -> Xv != lamv -> final_store h s abortv == vbool false -> let s2 :=
  announce_store (rounds_store h (start_store s)) in (n <= #|vset_of (s2 Xv)|)%N.
Proof.
  move=> Htf HAS HAH HXK HXXA HXXB HXZA HXZB HXP HXlam Habort; set s2 := announce_store (rounds_store h (start_store s)). set spe := paramest_store h s2. have Hpe := final_store_pass_pe_ok (h := h) (s := s) Htf HAS HAH Habort. rewrite -/s2 -/spe in Hpe. have Hsift : replay_sift_ok spe.
  { move: Hpe; rewrite /pe_failed /replay_pe_fail. case Hsift: (replay_sift_ok spe) => //=. } by move/andP: Hsift => [HX _]; move: HX; rewrite /spe (paramest_store_other (x := Xv) h s2). Qed.
Fact pe_pass_key_sample_enabled (h : run_history) (s : store) : Xv != Kv -> Xv != XA -> Xv != XB -> Xv != ZA -> Xv != ZB -> Xv != Pvar ->
  Xv != lamv -> let s2 := announce_store (rounds_store h (start_store s)) in ~~ pe_failed (paramest_store h s2) -> (n <= #|vset_of (s2
  Xv)|)%N.
Proof. move=> HXK HXXA HXXB HXZA HXZB HXP HXlam s2 Hpe; set spe := paramest_store h s2. have Hsift : replay_sift_ok spe. { move: Hpe; rewrite /pe_failed /replay_pe_fail. by case Hsift: (replay_sift_ok spe) => //=. } by move/andP: Hsift => [HX _]; move: HX; rewrite /spe (paramest_store_other (x := Xv) h s2). Qed.
Definition verify_accept_raw_mismatch (s : store) : bool := (s abortv == vbool false) && (s tAv == s tBv) && (s XA != s Xhatv).
Fact verify_accept_raw_mismatch_errcorr_storeE (h : run_history) (s : store) : ecwall (tagwall (xawall (xhwall (verify_accept_raw_mismatch
  (errcorr_store h s) = (s abortv == vbool false) && (verify_hash (hist_g h) (s XA) == verify_hash (hist_g h) (ir_dec (ir_pub leakEC (s XA)
  (s XB)) (s XB))) && (s XA != ir_dec (ir_pub leakEC (s XA) (s XB)) (s XB)))))).
Proof.
  move=> HAp HAXhat HAg HAtA HAtB HAP HgtA HgtB HtAtB HtAP HtBP HXAp HXAXhat HXAg HXAtA HXAtB HXAP HXBp HXhatg HXhattA HXhattB HXhatP.
    rewrite /verify_accept_raw_mismatch (errcorr_store_other (x := abortv) h s) //. rewrite (errcorr_store_tAv h s HtAtB HtAP) (errcorr_store_tBv h s HtBP). rewrite (errcorr_store_XA h s HXAp HXAXhat HXAg HXAtA HXAtB HXAP); rewrite (errcorr_store_Xhatv h s HXBp HXhatg HXhattA HXhattB HXhatP). set seed := errcorr_seed_store s; set s2 := store_set seed gv (hist_g h); set s3 := store_set s2 tAv (verify_hash (s2 gv) (s2 XA)). have Hs2g : s2 gv = hist_g h by rewrite /s2 store_set_same. have Hs2XA : s2 XA = s XA by rewrite /s2 store_set_other // /seed errcorr_seed_store_other. have Hs3g : s3 gv = hist_g h by rewrite /s3 store_set_other // Hs2g. have Hs3Xhat : s3 Xhatv = ir_dec (ir_pub leakEC (s XA) (s XB)) (s XB). by rewrite /s3 store_set_other // /s2 store_set_other // /seed errcorr_seed_store_Xhatv. by rewrite Hs2g Hs2XA Hs3g Hs3Xhat. Qed.
Definition output_mismatch_event (s : store) : bool := (s Sv != s Shv) && (s abortv == vbool false).
Definition round_choice_weight (c : round_choice) (s : store) : R := basis_mass s (choice_a c) * bit_mass s (choice_y c) * basis_mass s
  (choice_b c).
Definition round_sample_weight (h : run_history) (s : store) (i : 'I_M) : R := round_choice_weight (hist_choice h i) s.
Definition trace_sample_weight (t : round_trace) (s : store) (i : 'I_M) : R := round_choice_weight (t i) s.
Definition round_samples_weight (h : run_history) (s : store) : R := \prod_(i <- enum 'I_M) round_sample_weight h s i.
Definition trace_samples_weight (t : round_trace) (r : seq 'I_M) (s : store) : R := \prod_(i <- r) trace_sample_weight t s i.
Definition round_choice_unused (c : round_choice) : R := (c == round_choice_default)%:R.
Definition trace_unused_weight (t : round_trace) (r : seq 'I_M) : R := \prod_(i | i \notin r) round_choice_unused (t i).
Fact round_samples_weight_gt0 (h : run_history) (s : store) : (forall i, 0 < round_choice_weight (hist_choice h i) s) -> 0 <
  round_samples_weight h s.
Proof. by move=> Hround; rewrite /round_samples_weight /round_sample_weight; apply: prodr_gt0 => i _; exact: Hround. Qed.
Fact trace_unused_weight_nilN (t : round_trace) : t != round_trace_default -> trace_unused_weight t [::] = 0.
Proof.
  move=> Ht; have [i Hi] : exists i, t i != round_choice_default.
  { case: (pickP [pred i | t i != round_choice_default]) => [i Hi|Hall]; first by exists i. move/negP: Ht => Hneq; exfalso; apply: Hneq; apply/eqP/ffunP=> i. rewrite /round_trace_default ffunE. case Hti: (t i == round_choice_default); first by move/eqP: Hti. by move: (Hall i); rewrite /= Hti. } by rewrite /trace_unused_weight (bigD1 i) //= /round_choice_unused (negbTE Hi) mul0r. Qed.
Fact round_choice_weight_store (c : round_choice) (s t : store) : round_choice_weight c s = round_choice_weight c t.
Proof. by rewrite /round_choice_weight /basis_mass /bit_mass. Qed.
Fact trace_unused_weight_nondefault (t : round_trace) (i : 'I_M) (r : seq 'I_M) : i \notin r -> t i != round_choice_default ->
  trace_unused_weight t r = 0.
Proof. by move=> Hir Hti; rewrite /trace_unused_weight (bigD1 i) //= /round_choice_unused (negbTE Hti) mul0r. Qed.
Definition seed_unused (v : V) : R := (v == bot)%:R.
Definition hist_wt (h : run_history) (s : store) : R := let s0 := start_store s in let s1 := rounds_store h s0 in let s2 := announce_store
  s1 in let s3 := paramest_store h s2 in round_samples_weight h s0 * key_sample_mass s2 (hist_K h) * if pe_failed s3 then seed_unused
  (hist_g h) * seed_unused (hist_f h) else let sg := errcorr_seed_store s3 in let s4 := errcorr_store h s3 in unif_vseed sg (hist_g h) * if
  s4 tAv != s4 tBv then seed_unused (hist_f h) else unif_pseed s4 (hist_f h).
Definition history_post_weight (h : run_history) (s : store) : R := let s0 := start_store s in let s1 := rounds_store h s0 in let s2 :=
  announce_store s1 in let s3 := paramest_store h s2 in key_sample_mass s2 (hist_K h) * if pe_failed s3 then seed_unused (hist_g h) *
  seed_unused (hist_f h) else let sg := errcorr_seed_store s3 in let s4 := errcorr_store h s3 in unif_vseed sg (hist_g h) * if s4 tAv != s4
  tBv then seed_unused (hist_f h) else unif_pseed s4 (hist_f h).
Definition history_announce_store (h : run_history) (s : store) : store := announce_store (rounds_store h (start_store s)).
Definition history_paramest_store (h : run_history) (s : store) : store := paramest_store h (history_announce_store h s).
Definition history_errcorr_store (h : run_history) (s : store) : store := errcorr_store h (history_paramest_store h s).
Definition history_privamp_weight (h : run_history) (s : store) : R := key_sample_mass (history_announce_store h s) (hist_K h) * (unif_vseed
  (errcorr_seed_store (history_paramest_store h s)) (hist_g h) * unif_pseed (history_errcorr_store h s) (hist_f h)).
Definition history_pass_weight (h : run_history) (s : store) : R := (final_store h s abortv == vbool false)%:R * history_privamp_weight h s.
Definition history_pass_prefix_weight (h : run_history) (s : store) : R := (final_store h s abortv == vbool false)%:R * (key_sample_mass
  (history_announce_store h s) (hist_K h) * unif_vseed (errcorr_seed_store (history_paramest_store h s)) (hist_g h)).
Lemma history_post_weight_final_pass (h : run_history) (s : store) : vbool true != vbool false -> abortv != Sv -> abortv != Shv ->
  final_store h s abortv == vbool false -> let s0 := start_store s in let s1 := rounds_store h s0 in let s2 := announce_store s1 in let s3
  := paramest_store h s2 in let s4 := errcorr_store h s3 in history_post_weight h s = key_sample_mass s2 (hist_K h) * (unif_vseed
  (errcorr_seed_store s3) (hist_g h) * unif_pseed s4 (hist_f h)).
Proof.
  move=> Htf HAS HAH Hpass s0 s1 s2 s3 s4. have Hpe := final_store_pass_pe_ok (h := h) (s := s) Htf HAS HAH Hpass. rewrite -/s3 in Hpe. have Hverify : ~~ (s4 tAv != s4 tBv).
  { move: Hpass; rewrite /final_store -/s0 -/s1 -/s2 -/s3 (negbTE Hpe) -/s4. case Hbad: (s4 tAv != s4 tBv); last by []. by rewrite abort_store_not_pass. } by rewrite /history_post_weight -/s0 -/s1 -/s2 -/s3 (negbTE Hpe) -/s4 (negbTE Hverify) /hist_K /hist_g /hist_f /=. Qed.
Lemma history_post_store_f_irrel (t : round_trace) (K g f f0 : V) (s : store) : let h := (t, ((K, g), f)) in let h0 := (t, ((K, g), f0)) in
  history_errcorr_store h s = history_errcorr_store h0 s.
Proof. move=> h h0; rewrite /history_errcorr_store /history_paramest_store /history_announce_store. by rewrite (@rounds_store_trace_eq h0 h (start_store s)) // (errcorr_paramest_store_f_irrel t K g f f0). Qed.
Lemma history_post_coeff_f_irrel (t : round_trace) (K g f f0 : V) (s : store) : abortv != fv -> abortv != Sv -> abortv != Shv -> abortv !=
  Pvar -> let h := (t, ((K, g), f)) in let h0 := (t, ((K, g), f0)) in history_pass_weight h s = history_pass_prefix_weight h0 s * unif_pseed
  (history_errcorr_store h0 s) f.
Proof.
have history_post_factor_f_irrel : forall (t : round_trace) (K g f f0 : V) (s : store), let h := (t, ((K, g), f)) in let h0 := (t, ((K, g), f0)) in history_privamp_weight h s = key_sample_mass (history_announce_store h0 s) K * (unif_vseed (errcorr_seed_store (history_paramest_store h0 s)) g * unif_pseed (history_errcorr_store h0 s) f).
{ clear s f0 f g K t; move=> t K g f f0 s h h0. rewrite /history_privamp_weight /history_errcorr_store /history_paramest_store /history_announce_store. by rewrite /hist_K /hist_g /hist_f /= (@rounds_store_trace_eq h0 h (start_store s)) // (paramest_store_future_irrel t K g f g f0) (errcorr_store_f_irrel t K g f f0). } move=> HAf HAS HAH HAP h h0; rewrite /history_pass_weight. have Habort : final_store h s abortv = final_store h0 s abortv.
  { rewrite /h /h0. exact: (@final_store_abort_f_irrel t K g f f0 s HAf HAS HAH HAP). } have Habort_coeff := f_equal (fun v : V => ((v == vbool false)%:R : R)) Habort. have Hfactor := @history_post_factor_f_irrel t K g f f0 s.
    transitivity ((final_store h0 s abortv == vbool false)%:R * (key_sample_mass (history_announce_store h0 s) K * (unif_vseed (errcorr_seed_store (history_paramest_store h0 s)) g * unif_pseed (history_errcorr_store h0 s) f))).
  - exact: (f_equal2 (fun x y : R => x * y) Habort_coeff Hfactor).
  - by rewrite /history_pass_prefix_weight /h0 /hist_K /hist_g /= !mulrA. Qed.
Lemma key_sample_mass_nonneg (s : store) (v : V) : (forall m X v0, 0 <= unif_nsubset_mass m X v0) -> 0 <= key_sample_mass s v.
Proof. move=> Hunif; rewrite /key_sample_mass. case: ifP => _; first exact: Hunif. by case: (v == bot). Qed.
Lemma seed_unused_nonneg (v : V) : 0 <= seed_unused v.
Proof. by rewrite /seed_unused; case: (v == bot). Qed.
Lemma history_post_weight_nonneg (h : run_history) (s : store) : (forall m X v, 0 <= unif_nsubset_mass m X v) -> (forall s0 v, 0 <=
  unif_vseed s0 v) -> (forall s0 v, 0 <= unif_pseed s0 v) -> 0 <= history_post_weight h s.
Proof.
  move=> Hunif HKseed HPseed; rewrite /history_post_weight; set s0 := start_store s; set s1 := rounds_store h s0. set s2 := announce_store s1; set s3 := paramest_store h s2; apply: mulr_ge0; first exact: key_sample_mass_nonneg. case: ifP => _.
  - apply: mulr_ge0; exact: seed_unused_nonneg.
  - set sg := errcorr_seed_store s3; set s4 := errcorr_store h s3; apply: mulr_ge0; first exact: HKseed. case: ifP => _; [exact: seed_unused_nonneg | exact: HPseed]. Qed.
Lemma history_post_weight_key_sample_nonzero (h : run_history) (s : store) : history_post_weight h s != 0 -> let s0 := start_store s in let
  s1 := rounds_store h s0 in let s2 := announce_store s1 in key_sample_mass s2 (hist_K h) != 0.
Proof.
  have history_post_weight_key_sample0 : forall (h : run_history) (s : store), let s0 := start_store s in let s1 := rounds_store h s0 in let s2 := announce_store s1 in key_sample_mass s2 (hist_K h) = 0 -> history_post_weight h s = 0.
  { move=> {}h {}s. rewrite /history_post_weight. set s0 := start_store s. set s1 := rounds_store h s0. set s2 := announce_store s1. set s3 := paramest_store h s2. by move=> Hkey; rewrite Hkey mul0r. } by move=> Hpost; apply/eqP=> Hkey; move: Hpost; rewrite (history_post_weight_key_sample0 h s Hkey) eqxx. Qed.
Lemma hist_wt_split (h : run_history) (s : store) : hist_wt h s = round_samples_weight h (start_store s) * history_post_weight h s.
Proof.
  rewrite /hist_wt /history_post_weight; set s0 := start_store s; set s1 := rounds_store h s0; set s2 := announce_store s1. set s3 := paramest_store h s2. case: (pe_failed s3); first by rewrite -mulrA. by set sg := errcorr_seed_store s3; set s4 := errcorr_store h s3; case: (s4 tAv != s4 tBv); rewrite -!mulrA. Qed.
Fact history_post_weight_seed_collapse (t : round_trace) (K : V) (s : store) : (forall s', \sum_(v : V) unif_vseed s' v = 1) -> (forall s',
  \sum_(v : V) unif_pseed s' v = 1) -> \sum_(g : V) \sum_(f : V) history_post_weight (t, ((K, g), f)) s = key_sample_mass (announce_store
  (rounds_store (t, ((K, bot), bot)) (start_store s))) K.
Proof.
have history_post_weight_shape : forall (t : round_trace) (K g f : V) (s : store), history_post_weight (t, ((K, g), f)) s = key_sample_mass (announce_store (rounds_store (t, ((K, bot), bot)) (start_store s))) K * (if pe_failed (paramest_store (t, ((K, bot), bot)) (announce_store (rounds_store (t, ((K, bot), bot)) (start_store s)))) then seed_unused g * seed_unused f else unif_vseed (errcorr_seed_store (paramest_store (t, ((K, bot), bot)) (announce_store (rounds_store (t, ((K, bot), bot)) (start_store s))))) g * (if (errcorr_store (t, ((K, g), bot)) (paramest_store (t, ((K, bot), bot)) (announce_store (rounds_store (t, ((K, bot), bot)) (start_store s))))) tAv != (errcorr_store (t, ((K, g), bot)) (paramest_store (t, ((K, bot), bot)) (announce_store (rounds_store (t, ((K, bot), bot)) (start_store s))))) tBv then seed_unused f else unif_pseed (errcorr_store (t, ((K, g), bot)) (paramest_store (t, ((K, bot), bot)) (announce_store (rounds_store (t, ((K, bot), bot)) (start_store s))))) f)).
{ clear s K t; move=> t K g f s. have Hrs : rounds_store (t, ((K, g), f)) (start_store s) = rounds_store (t, ((K, bot), bot)) (start_store s) by apply: rounds_store_trace_eq. rewrite /history_post_weight !Hrs !(paramest_store_future_irrel t K g f bot bot). rewrite !(errcorr_store_f_irrel t K g f bot). by []. } have seed_collapse_bigop : forall (Rr : nzRingType) (Iv : finType) (c0 : Rr) (pb : bool) (af : Iv -> Rr) (qb : Iv -> bool) (bf : Iv -> Iv -> Rr) (su : Iv -> Rr), \sum_(v : Iv) su v = 1 -> \sum_(g : Iv) af g = 1 -> (forall g, \sum_(f : Iv) bf g f = 1) -> \sum_(g : Iv) \sum_(f : Iv) (c0 * (if pb then su g * su f else af g * (if qb g then su f else bf g f))) = c0.
{ clear s K t; move=> Rr Iv c0 pb af qb bf su. move=> Hsu HA HB; under eq_bigr => g _ do rewrite -mulr_sumr. rewrite -mulr_sumr. suff -> : \sum_(g : Iv) \sum_(f : Iv) (if pb then su g * su f else af g * (if qb g then su f else bf g f)) = 1 by rewrite mulr1. case: pb.
  - under eq_bigr => g _ do rewrite -mulr_sumr Hsu mulr1. exact: Hsu.
  - under eq_bigr => g _.
    { rewrite -mulr_sumr. rewrite (_ : \sum_(f : Iv) (if qb g then su f else bf g f) = 1); last first.
      { by case: (qb g); [exact: Hsu | exact: HB]. } rewrite mulr1. over. } exact: HA. } move=> HV HP. under eq_bigr => g _ do under eq_bigr => f _ do rewrite history_post_weight_shape. set s2 := announce_store (rounds_store (t, ((K, bot), bot)) (start_store s)). set s3 := paramest_store (t, ((K, bot), bot)) s2. apply: seed_collapse_bigop.
  - rewrite /seed_unused (bigD1 bot) //= eqxx big1 ?addr0 // => v Hv. by rewrite (negbTE Hv).
  - exact: (HV (errcorr_seed_store s3)).
  - by move=> g; exact: (HP (errcorr_store (t, ((K, g), bot)) s3)). Qed.
Fact hist_wt_privamp_branch_gt0 (h : run_history) (s : store) : let s0 := start_store s in let s1 := rounds_store h s0 in let s2 :=
  announce_store s1 in let s3 := paramest_store h s2 in let s4 := errcorr_store h s3 in 0 < round_samples_weight h s0 -> 0 < key_sample_mass
  s2 (hist_K h) -> ~~ pe_failed s3 -> 0 < unif_vseed (errcorr_seed_store s3) (hist_g h) -> ~~ (s4 tAv != s4 tBv) -> 0 < unif_pseed s4
  (hist_f h) -> 0 < hist_wt h s.
Proof. move=> s0 s1 s2 s3 s4 Hround Hkey Hpe Hg Hverify Hf; rewrite /hist_wt -/s0 -/s1 -/s2 -/s3 (negbTE Hpe) -/s4 (negbTE Hverify) -!mulrA. by apply: mulr_gt0; [exact: Hround | apply: mulr_gt0; [exact: Hkey | apply: mulr_gt0; [exact: Hg | exact: Hf]]]. Qed.
Lemma hist_wt_nonneg (h : run_history) (s : store) : (forall m X v, 0 <= unif_nsubset_mass m X v) -> (forall s0 v, 0 <= unif_vseed s0 v) ->
  (forall s0 v, 0 <= unif_pseed s0 v) -> 0 <= hist_wt h s.
Proof.
have round_choice_weight_nonneg : forall (c : round_choice) (s : store), 0 <= round_choice_weight c s.
{ clear s h; move=> c s. have bit_mass_nonneg : forall (s : store) (v : V), 0 <= bit_mass s v.
{ clear s c; move=> s v. rewrite /bit_mass. case: ifP => _; first by rewrite invr_ge0 ler0n. case: ifP => _; first by rewrite invr_ge0 ler0n. by rewrite lexx. } rewrite /round_choice_weight; apply: mulr_ge0; last exact: basis_mass_nonneg. apply: mulr_ge0; [exact: basis_mass_nonneg | exact: bit_mass_nonneg]. } move=> Hunif HKseed HPseed; rewrite hist_wt_split; apply: mulr_ge0.
  - rewrite /round_samples_weight. apply: prodr_ge0 => i _. exact: round_choice_weight_nonneg.
  - exact: history_post_weight_nonneg. Qed.
Local Open Scope lfun_scope.
Definition attack_transcript (_h : run_history) (_i : 'I_M) : V := empty_transcript.
Definition round_choice_so (qA : {set L}) (EA : ADVq qA) (c : round_choice) (i : 'I_M) (p : V) : 'SO[HL]_setT := formso (liftf_lf (dev_meas
  i (choice_b c) (choice_y' c))) :o liftfso (EA (Q i) p) :o replaceso (dev_rho i (choice_a c) (choice_y c)).
Definition round_so (qA : {set L}) (EA : ADVq qA) (h : run_history) (i : 'I_M) : 'SO[HL]_setT := round_choice_so EA (hist_choice h i) i
  (attack_transcript h i).
Definition trace_round_so (qA : {set L}) (EA : ADVq qA) (t : round_trace) (i : 'I_M) : 'SO[HL]_setT := round_choice_so EA (t i) i
  empty_transcript.
Definition round_choice_branch (qA : {set L}) (EA : ADVq qA) (c : round_choice) (i : 'I_M) (s : store) (rho : 'F[HL]_setT) : CQs :=
  (round_choice_weight c s)%:C *: cq_single (write_round_choice c i s) (round_choice_so EA c i (s Pvar) rho).
Definition rounds_cmd_seq (r : seq 'I_M) : @qkd_cmd R L HL Cv V := \big[@seq_cmd R L HL Cv V/@Cskip R L HL Cv V]_(i <- r) RNDs i.
Lemma rounds_cmd_seq_enum : rounds_cmd_seq (enum 'I_M) = @for_cmd R L HL Cv V M (fun i => RNDs i).
Proof. by rewrite /rounds_cmd_seq /for_cmd. Qed.
Definition hist_so (qA : {set L}) (EA : ADVq qA) (h : run_history) : 'SO[HL]_setT := \compr_(i <- enum 'I_M) round_so EA h i.
Definition trace_so_seq (qA : {set L}) (EA : ADVq qA) (t : round_trace) (r : seq 'I_M) : 'SO[HL]_setT := \compr_(i <- r) trace_round_so EA t
  i.
Fact round_choice_so_trace_id (qA : {set L}) (EA : ADVq qA) (c : round_choice) (i : 'I_M) (p : V) (Z : 'F[HL]_setT) : liftfso (EA (Q i) p)
  = \:1 -> \Tr (round_choice_so EA c i p Z) = \Tr (formlf (dev_meas i (choice_b c) (choice_y' c)) (dev_rho i (choice_a c) (choice_y c))) *
  \Tr Z.
Proof. move=> Hid; rewrite /round_choice_so !comp_soE Hid id_soE; rewrite formsoE -liftf_lf_adj appendso_comp_keep -formlfE appendso_trlf. congr (_ * _). by case/cptpP: (@ptraceso_qc R L HL (Q i) setT) => _ /tpmapP ->. Qed.
Fact trace_so_seq_trace_id (qA : {set L}) (EA : ADVq qA) (t : round_trace) (r : seq 'I_M) (Z : 'F[HL]_setT) : (forall i, liftfso (EA (Q i)
  empty_transcript) = \:1) -> \Tr (trace_so_seq EA t r Z) = (\prod_(i <- r) \Tr (formlf (dev_meas i (choice_b (t i)) (choice_y' (t i)))
  (dev_rho i (choice_a (t i)) (choice_y (t i))))) * \Tr Z.
Proof. move=> Hid; elim: r Z => [|j r IHr] Z. - by rewrite /trace_so_seq big_nil id_soE big_nil mul1r. - rewrite /trace_so_seq big_cons comp_sorE -/(trace_so_seq EA t r). by rewrite IHr /trace_round_so round_choice_so_trace_id ?Hid //; rewrite big_cons mulrA [_ * \Tr (formlf _ _)]mulrC -mulrA. Qed.
Fact trace_so_seq_set_tail (qA : {set L}) (EA : ADVq qA) (t : round_trace) (i : 'I_M) (c : round_choice) (r : seq 'I_M) : i \notin r ->
  trace_so_seq EA (round_trace_set t i c) r = trace_so_seq EA t r.
Proof. rewrite /trace_so_seq; move=> Hir; apply: eq_big_seq => j Hj; rewrite /trace_round_so round_trace_set_other //. apply/eqP=> Hji. by move: Hir; rewrite -Hji Hj. Qed.
Definition trace_branch_seq (qA : {set L}) (EA : ADVq qA) (r : seq 'I_M) (t : round_trace) (s : store) (rho : 'F[HL]_setT) : CQs :=
  cq_single (trace_store_seq t r s) ((trace_samples_weight t r s * trace_unused_weight t r)%:C *: trace_so_seq EA t r rho).
Fact trace_branch_seq_nil_sum (qA : {set L}) (EA : ADVq qA) (s : store) (rho : 'F[HL]_setT) : \sum_(t : round_trace) trace_branch_seq EA
  [::] t s rho = cq_single s rho.
Proof.
have trace_unused_weight_nil_default : trace_unused_weight round_trace_default [::] = 1.
{ rewrite /trace_unused_weight. by apply: big1 => i _; rewrite /round_choice_unused /round_trace_default ffunE eqxx. } rewrite (bigD1 round_trace_default) //=. rewrite /trace_branch_seq /trace_store_seq /trace_samples_weight /trace_so_seq !big_nil id_soE trace_unused_weight_nil_default. rewrite mulr1 rmorph1 scale1r; rewrite [X in _ + X]big1 ?addr0 // => t Ht. rewrite /trace_branch_seq /trace_store_seq /trace_samples_weight /trace_so_seq !big_nil id_soE (trace_unused_weight_nilN Ht). by rewrite mulr0 rmorph0 scale0r cq_single_zero. Qed.
Fact trace_branch_seq_nondefault (qA : {set L}) (EA : ADVq qA) (r : seq 'I_M) (t : round_trace) (i : 'I_M) (s : store) (rho : 'F[HL]_setT)
  : i \notin r -> t i != round_choice_default -> trace_branch_seq EA r t s rho = 0.
Proof. by move=> Hir Hti; rewrite /trace_branch_seq (trace_unused_weight_nondefault Hir Hti); rewrite mulr0 rmorph0 scale0r cq_single_zero. Qed.
Fact denote_rounds_seq_sum (qA : {set L}) (EA : ADVq qA) (r : seq 'I_M) (s : store) (rho : 'F[HL]_setT) : uniq r -> (forall i, i \in r ->
  a_ i != y_ i) -> (forall i, i \in r -> Pvar != a_ i) -> (forall i, i \in r -> Pvar != y_ i) -> (forall i, i \in r -> Pvar != b_ i) ->
  (forall i, i \in r -> Pvar != y'_ i) -> (forall i, i \in r -> Pvar != d_ i) -> Pvar != Xv -> Pvar != Zv -> s Pvar = empty_transcript ->
  DSg qA EA (rounds_cmd_seq r) s rho = \sum_(t : round_trace) trace_branch_seq EA r t s rho.
Proof.
have trace_branch_seq_cons_sum : forall (qA : {set L}) (EA : ADVq qA) (i : 'I_M) (r : seq 'I_M) (s : store) (rho : 'F[HL]_setT), i \notin r -> \sum_(t : round_trace) trace_branch_seq EA (i :: r) t s rho = \sum_(c : round_choice) (round_choice_weight c s)%:C *: \sum_(t : round_trace) trace_branch_seq EA r t (write_round_choice c i s) (round_choice_so EA c i empty_transcript rho).
{ clear rho s r EA qA; move=> qA EA i r s rho. have trace_branch_seq_set_cons : forall (qA : {set L}) (EA : ADVq qA) (t : round_trace) (i : 'I_M) (c : round_choice) (r : seq 'I_M) (s : store) (rho : 'F[HL]_setT), i \notin r -> t i = round_choice_default -> trace_branch_seq EA (i :: r) (round_trace_set t i c) s rho = (round_choice_weight c s)%:C *: trace_branch_seq EA r t (write_round_choice c i s) (round_choice_so EA c i empty_transcript rho).
{ clear rho s r i EA qA; move=> qA EA t i c r s rho. have trace_so_seq_set_cons : forall (qA : {set L}) (EA : ADVq qA) (t : round_trace) (i : 'I_M) (c : round_choice) (r : seq 'I_M) (rho : 'F[HL]_setT), i \notin r -> trace_so_seq EA (round_trace_set t i c) (i :: r) rho = trace_so_seq EA t r (round_choice_so EA c i empty_transcript rho).
{ clear rho s r c i t EA qA; move=> qA EA t i c r rho. move=> Hir. rewrite /trace_so_seq big_cons /trace_round_so round_trace_set_same comp_sorE. rewrite -/(trace_so_seq EA (round_trace_set t i c) r) -/(trace_so_seq EA t r). by rewrite (@trace_so_seq_set_tail qA EA t i c r Hir). } have trace_unused_weight_set_cons : forall (t : round_trace) (i : 'I_M) (c : round_choice) (r : seq 'I_M), i \notin r -> t i = round_choice_default -> trace_unused_weight (round_trace_set t i c) (i :: r) = trace_unused_weight t r.
{ clear rho s r c i t EA qA; move=> t i c r. move=> Hir Hti; rewrite /trace_unused_weight. rewrite [in RHS](bigD1 i) //= Hti /round_choice_unused eqxx mul1r; apply: eq_big => [j|j Hj]. by case Hji: (j == i); case Hjr: (j \in r); rewrite in_cons Hji Hjr /= ?eq_sym ?Hji. have Hji : j != i by move: Hj; rewrite in_cons negb_or => /andP[]. by rewrite round_trace_set_other. } have trace_samples_weight_set_cons : forall (t : round_trace) (i : 'I_M) (c : round_choice) (r : seq 'I_M) (s : store), i \notin r -> trace_samples_weight (round_trace_set t i c) (i :: r) s = round_choice_weight c s * trace_samples_weight t r (write_round_choice c i s).
{ clear rho s r c i t EA qA; move=> t i c r s. move=> Hir. rewrite /trace_samples_weight big_cons /trace_sample_weight round_trace_set_same.
  congr (_ * _). apply: eq_big_seq => j Hj. rewrite /trace_sample_weight round_trace_set_other ?(round_choice_weight_store (t j) s (write_round_choice c i s)) //; apply/eqP=> Hji. by move: Hir; rewrite -Hji Hj. } have trace_store_seq_set_cons : forall (t : round_trace) (i : 'I_M) (c : round_choice) (r : seq 'I_M) (s : store), i \notin r -> trace_store_seq (round_trace_set t i c) (i :: r) s = trace_store_seq t r (write_round_choice c i s).
{ clear rho s r c i t EA qA; move=> t i c r s. move=> Hir; rewrite /trace_store_seq /= /write_trace_round round_trace_set_same. elim: r (write_round_choice c i s) Hir => [|j r IHr] u Hir //=. move: Hir; rewrite in_cons negb_or => /andP [Hij Hir]; rewrite /write_trace_round round_trace_set_other; last by rewrite eq_sym. exact: IHr. } move=> Hir Hti; rewrite /trace_branch_seq; rewrite trace_store_seq_set_cons //; rewrite trace_samples_weight_set_cons //. rewrite trace_unused_weight_set_cons //; rewrite trace_so_seq_set_cons //; rewrite -cq_single_scale. by rewrite !scalerA -!rmorphM mulrA. } have trace_branch_seq_tail_sum : forall (qA : {set L}) (EA : ADVq qA) (i : 'I_M) (r : seq 'I_M) (s : store) (rho : 'F[HL]_setT), i \notin r -> \sum_(u : {t : round_trace | t i == round_choice_default}) trace_branch_seq EA r (val u) s rho = \sum_(t : round_trace) trace_branch_seq EA r t s rho.
{ clear rho s r i EA qA; move=> qA EA i r s rho. move=> Hir. pose t0 : {t : round_trace | t i == round_choice_default} := Sub round_trace_default _. have t0P : round_trace_default i == round_choice_default by rewrite /round_trace_default ffunE eqxx. rewrite /t0 in t0P *; symmetry. rewrite (bigID (fun t : round_trace => t i == round_choice_default)) /=; rewrite [X in _ + X]big1 ?addr0.
  - rewrite (reindex (fun u : {t : round_trace | t i == round_choice_default} => val u)); last first. exists (insubd (Sub round_trace_default t0P)).
      + by move=> u _; apply: val_inj; rewrite (insubdK (Sub round_trace_default t0P) (valP u)).
      + by move=> t Ht; rewrite (insubdK (Sub round_trace_default t0P) Ht). by apply: eq_bigl => -[t Ht]; rewrite /= Ht.
  - move=> t Ht; apply: (@trace_branch_seq_nondefault qA EA r t i s rho Hir). exact: Ht. } move=> Hir; pose tail_trace := {t : round_trace | t i == round_choice_default}. pose put_head (p : round_choice * tail_trace) := round_trace_set (val p.2) i p.1. have drop_head_subproof t : round_trace_set t i round_choice_default i == round_choice_default by rewrite round_trace_set_same eqxx. pose drop_head (t : round_trace) : round_choice * tail_trace := (t i, Sub (round_trace_set t i round_choice_default) (drop_head_subproof t)). have put_dropK : cancel drop_head put_head.
  { move=> t; apply/ffunP=> j. case Hji: (j == i). by move/eqP: Hji => ->; rewrite /put_head /= round_trace_set_same. by rewrite /put_head /= !round_trace_set_other ?(negbT Hji). } have drop_putK : cancel put_head drop_head.
  { move=> [c [t Ht]]; rewrite /drop_head /put_head /=. congr (_, _). by rewrite round_trace_set_same. apply: val_inj=> /=; apply/ffunP=> j.
    case Hji: (j == i). by move/eqP: Hji => ->; move/eqP: Ht => ->; rewrite round_trace_set_same. by rewrite !round_trace_set_other ?(negbT Hji). } rewrite (reindex put_head); last by exists drop_head => x _; rewrite ?put_dropK ?drop_putK. change (\sum_(p : round_choice * tail_trace) (fun c u => trace_branch_seq EA (i :: r) (put_head (c, u)) s rho) p.1 p.2 = \sum_(c : round_choice) (round_choice_weight c s)%:C *: \sum_(t : round_trace) trace_branch_seq EA r t (write_round_choice c i s) (round_choice_so EA c i empty_transcript rho)). rewrite -pair_bigA /=; apply: eq_bigr => c _. transitivity (\sum_(u : tail_trace) (round_choice_weight c s)%:C *: trace_branch_seq EA r (val u) (write_round_choice c i s) (round_choice_so EA c i empty_transcript rho)).
  { apply: eq_bigr => u _. rewrite /put_head /=; apply: trace_branch_seq_set_cons => //. by move/eqP: (valP u). } by rewrite -scaler_sumr trace_branch_seq_tail_sum. } have write_round_choice_public : forall (c : round_choice) (i : 'I_M) (s : store), Pvar != a_ i -> Pvar != y_ i -> Pvar != b_ i -> Pvar != y'_ i -> Pvar != d_ i -> Pvar != Xv -> Pvar != Zv -> write_round_choice c i s Pvar = s Pvar.
{ clear rho s r EA qA; move=> c i s. move=> HPa HPy HPb HPy' HPd HPX HPZ. rewrite /write_round_choice /round_sift_store /round_measure_store /round_prepare_store. by rewrite store_set_other // store_set_other // store_set_other // store_set_other // store_set_other // store_set_other // store_set_other. } have denote_round_choices_sum : forall (qA : {set L}) (EA : ADVq qA) (i : 'I_M) (s : store) (rho : 'F[HL]_setT), a_ i != y_ i -> Pvar != a_ i -> Pvar != y_ i -> DSg qA EA (RNDs i) s rho = \sum_(c : round_choice) round_choice_branch EA c i s rho.
{ clear rho s r EA qA; move=> qA EA i s rho. have denote_round_choices_nested : forall (qA : {set L}) (EA : ADVq qA) (i : 'I_M) (s : store) (rho : 'F[HL]_setT), a_ i != y_ i -> Pvar != a_ i -> Pvar != y_ i -> DSg qA EA (RNDs i) s rho = \sum_a \sum_y \sum_b \sum_yp round_choice_branch EA ((a, y), (b, yp)) i s rho.
{ clear rho s i EA qA; move=> qA EA i s rho. have denote_sift_single : forall (qA : {set L}) (EA : ADVq qA) (c : round_choice) (i : 'I_M) (s : store) (rho : 'F[HL]_setT), DSg qA EA (@Sift R L HL Cv V M a_ b_ y'_ d_ Xv Zv basisX basisZ outEmpty vbool vset i) (round_measure_store c i s) rho = cq_single (round_sift_store c i s) rho.
{ clear rho s i EA qA; move=> qA EA c i s rho. rewrite /Sift /round_sift_store. set s4 := round_measure_store c i s; rewrite denote_seq_single /detected denote_assign_bind_single. rewrite (_ : s4 (y'_ i) = choice_y' c); last by rewrite /s4 round_measure_store_y'.
  set s5 := store_set s4 (d_ i) (vbool (choice_y' c != outEmpty)); rewrite /rounds_through /sift_X denote_seq_assign_single. set s6 := store_set s5 Xv (vset [set j : 'I_M | (nat_of_ord j <= nat_of_ord i)%N && ((s5 (a_ j) == basisX) && (s5 (b_ j) == basisX) && (s5 (d_ j) == vbool true))]). rewrite denote_assign_single. by rewrite /sift_Z /replay_rounds_through /replay_sift_X /replay_sift_Z. } move=> Hay HPa HPy; rewrite /Round /Prep /Dist /Meas; rewrite denote_seq_single denote_sample_bind_single_sum; apply: eq_bigr => a _.
    rewrite denote_seq_single denote_sample_bind_single_sum scaler_sumr; apply: eq_bigr => y _. set sp := store_set (store_set s (a_ i) a) (y_ i) y; rewrite denote_seq_single denote_init_bind_single. rewrite (_ : sp (a_ i) = a); last first. by rewrite /sp store_set_other ?store_set_same. rewrite (_ : sp (y_ i) = y); last by rewrite /sp store_set_same. rewrite denote_seq_single denote_attack_bind_single; rewrite (_ : sp Pvar = s Pvar); last first. by rewrite /sp store_set_other // store_set_other. rewrite /Meas denote_seq_single denote_sample_bind_single_sum !scaler_sumr; apply: eq_bigr => b _. set sb := store_set sp (b_ i) b; rewrite denote_seq_single denote_measure_bind_single_sum !scaler_sumr; apply: eq_bigr => yp _. rewrite (_ : sb (b_ i) = b); last by rewrite /sb store_set_same.
    change (store_set sb (y'_ i) yp) with (round_measure_store ((a, y), (b, yp)) i s). rewrite denote_sift_single; rewrite /round_choice_branch /round_choice_weight /round_choice_so /write_round_choice. rewrite /basis_mass /bit_mass. by rewrite !comp_soE !scalerA -!rmorphM /= ?mulrA. } move=> Hay HPa HPy; rewrite denote_round_choices_nested //. change (\sum_a \sum_y \sum_b \sum_yp round_choice_branch EA ((a, y), (b, yp)) i s rho = \sum_(p : (V * V) * (V * V)) (fun ay byp => round_choice_branch EA (ay, byp) i s rho) p.1 p.2). rewrite -[RHS]pair_bigA /= [LHS]pair_bigA /=; apply: eq_bigr => ay _. by rewrite [LHS]pair_bigA. } have denote_rounds_seq_nil : forall (qA : {set L}) (EA : ADVq qA) (s : store) (rho : 'F[HL]_setT), DSg qA EA (rounds_cmd_seq [::]) s rho = \sum_(t : round_trace) trace_branch_seq EA [::] t s rho.
{ clear rho s r EA qA; move=> qA EA s rho. by rewrite /rounds_cmd_seq big_nil /denote_singleton trace_branch_seq_nil_sum. } have denote_rounds_seq_cons : forall (qA : {set L}) (EA : ADVq qA) (i : 'I_M) (r : seq 'I_M) (s : store) (rho : 'F[HL]_setT), DSg qA EA (rounds_cmd_seq (i :: r)) s rho = DNg qA EA (rounds_cmd_seq r) (DSg qA EA (RNDs i) s rho).
{ clear rho s r EA qA; move=> qA EA i r s rho. by rewrite /rounds_cmd_seq big_cons /denote_singleton denote_seq_cmd. } elim: r s rho => [|i r IHr] s rho Huniq Hay HPa HPy HPb HPy' HPd HPX HPZ Hpub. exact: denote_rounds_seq_nil. move: Huniq; rewrite /= => /andP [Hir Huniq]; rewrite denote_rounds_seq_cons denote_round_choices_sum.
  - rewrite denote_sum. transitivity (\sum_(c : round_choice) (round_choice_weight c s)%:C *: \sum_(t : round_trace) trace_branch_seq EA r t (write_round_choice c i s) (round_choice_so EA c i empty_transcript rho)).
    { apply: eq_bigr => c _. rewrite /round_choice_branch denote_scale /denote_singleton Hpub; congr (_ *: _). apply: (IHr (write_round_choice c i s) (round_choice_so EA c i empty_transcript rho) Huniq).
      - by move=> j Hj; apply: Hay; rewrite in_cons Hj orbT.
      - by move=> j Hj; apply: HPa; rewrite in_cons Hj orbT.
      - by move=> j Hj; apply: HPy; rewrite in_cons Hj orbT.
      - by move=> j Hj; apply: HPb; rewrite in_cons Hj orbT.
      - by move=> j Hj; apply: HPy'; rewrite in_cons Hj orbT.
      - by move=> j Hj; apply: HPd; rewrite in_cons Hj orbT.
      - exact: HPX.
      - exact: HPZ.
      - rewrite write_round_choice_public; [exact: Hpub | exact: HPa i (mem_head i r) | exact: HPy i (mem_head i r) | exact: HPb i (mem_head i r) | exact: HPy' i (mem_head i r) | exact: HPd i (mem_head i r) | exact: HPX | exact: HPZ]. } by rewrite -trace_branch_seq_cons_sum.
  - exact: Hay i (mem_head i r).
  - exact: HPa i (mem_head i r).
  - exact: HPy i (mem_head i r). Qed.
Definition trace_announce_branch (qA : {set L}) (EA : ADVq qA) (r : seq 'I_M) (t : round_trace) (s : store) (rho : 'F[HL]_setT) : CQs :=
  cq_single (announce_store (trace_store_seq t r s)) ((trace_samples_weight t r s * trace_unused_weight t r)%:C *: trace_so_seq EA t r rho).
Definition trace_paramest_sample_branch (qA : {set L}) (EA : ADVq qA) (r : seq 'I_M) (t : round_trace) (K g f : V) (s : store) (rho :
  'F[HL]_setT) : CQs := let s_ann := announce_store (trace_store_seq t r s) in cq_single (paramest_store (t, ((K, g), f)) s_ann)
  ((trace_samples_weight t r s * trace_unused_weight t r * key_sample_mass s_ann K)%:C *: trace_so_seq EA t r rho).
Definition trace_paramest_branch (qA : {set L}) (EA : ADVq qA) (r : seq 'I_M) (h : run_history) (s : store) (rho : 'F[HL]_setT) : CQs := let
  s_ann := announce_store (trace_store_seq h.1 r s) in cq_single (paramest_store h s_ann) ((trace_samples_weight h.1 r s *
  trace_unused_weight h.1 r * key_sample_mass s_ann (hist_K h) * seed_unused (hist_g h) * seed_unused (hist_f h))%:C *: trace_so_seq EA h.1
  r rho).
Definition trace_pe_abort_branch (qA : {set L}) (EA : ADVq qA) (r : seq 'I_M) (h : run_history) (s : store) (rho : 'F[HL]_setT) : CQs := let
  s_ann := announce_store (trace_store_seq h.1 r s) in let s_pe := paramest_store h s_ann in cq_single (abort_store s_pe)
  ((trace_samples_weight h.1 r s * trace_unused_weight h.1 r * key_sample_mass s_ann (hist_K h) * seed_unused (hist_g h) * seed_unused
  (hist_f h))%:C *: trace_so_seq EA h.1 r rho).
Definition trace_errcorr_branch (qA : {set L}) (EA : ADVq qA) (r : seq 'I_M) (h : run_history) (s : store) (rho : 'F[HL]_setT) : CQs := let
  s_ann := announce_store (trace_store_seq h.1 r s) in let s_pe := paramest_store h s_ann in cq_single (errcorr_store h s_pe)
  ((trace_samples_weight h.1 r s * trace_unused_weight h.1 r * key_sample_mass s_ann (hist_K h) * unif_vseed (errcorr_seed_store s_pe)
  (hist_g h) * seed_unused (hist_f h))%:C *: trace_so_seq EA h.1 r rho).
Definition trace_verify_abort_branch (qA : {set L}) (EA : ADVq qA) (r : seq 'I_M) (h : run_history) (s : store) (rho : 'F[HL]_setT) : CQs :=
  let s_ann := announce_store (trace_store_seq h.1 r s) in let s_pe := paramest_store h s_ann in let s_ec := errcorr_store h s_pe in
  cq_single (abort_store s_ec) ((trace_samples_weight h.1 r s * trace_unused_weight h.1 r * key_sample_mass s_ann (hist_K h) * unif_vseed
  (errcorr_seed_store s_pe) (hist_g h) * seed_unused (hist_f h))%:C *: trace_so_seq EA h.1 r rho).
Definition trace_privamp_branch (qA : {set L}) (EA : ADVq qA) (r : seq 'I_M) (h : run_history) (s : store) (rho : 'F[HL]_setT) : CQs := let
  s_ann := announce_store (trace_store_seq h.1 r s) in let s_pe := paramest_store h s_ann in let s_ec := errcorr_store h s_pe in cq_single
  (privamp_store h s_ec) ((trace_samples_weight h.1 r s * trace_unused_weight h.1 r * key_sample_mass s_ann (hist_K h) * unif_vseed
  (errcorr_seed_store s_pe) (hist_g h) * unif_pseed s_ec (hist_f h))%:C *: trace_so_seq EA h.1 r rho).
Definition trace_final_branch (qA : {set L}) (EA : ADVq qA) (r : seq 'I_M) (h : run_history) (s : store) (rho : 'F[HL]_setT) : CQs := let
  s_ann := announce_store (trace_store_seq h.1 r s) in let s_pe := paramest_store h s_ann in if pe_failed s_pe then trace_pe_abort_branch EA
  r h s rho else let s_ec := errcorr_store h s_pe in if s_ec tAv != s_ec tBv then trace_verify_abort_branch EA r h s rho else
  trace_privamp_branch EA r h s rho.
Definition trace_preverify_branch (qA : {set L}) (EA : ADVq qA) (r : seq 'I_M) (h : run_history) (s : store) (rho : 'F[HL]_setT) : CQs :=
  let s_ann := announce_store (trace_store_seq h.1 r s) in let s_pe := paramest_store h s_ann in if pe_failed s_pe then
  trace_pe_abort_branch EA r h s rho else trace_errcorr_branch EA r h s rho.
Definition postprocess_cmd : @qkd_cmd R L HL Cv V := IF PFs THEN ABs ELSE (ECs ;; IF (fun u : store => u tAv != u tBv) THEN ABs ELSE PAs).
Lemma trace_paramest_full_sum (qA : {set L}) (EA : ADVq qA) (r : seq 'I_M) (s : store) (rho : 'F[HL]_setT) : \sum_(t : round_trace) \sum_K
  trace_paramest_sample_branch EA r t K bot bot s rho = \sum_(h : run_history) trace_paramest_branch EA r h s rho.
Proof.
have trace_paramest_sample_seed_sum : forall (qA : {set L}) (EA : ADVq qA) (r : seq 'I_M) (t : round_trace) (K : V) (s : store) (rho : 'F[HL]_setT), \sum_g \sum_f trace_paramest_branch EA r (t, ((K, g), f)) s rho = trace_paramest_sample_branch EA r t K bot bot s rho.
{ clear rho s r EA qA; move=> qA EA r t K s rho. rewrite (bigD1 bot) //=. rewrite [X in _ + X]big1 ?addr0; last first. move=> g Hg; apply: big1 => f _; rewrite /trace_paramest_branch /seed_unused /hist_g /= (negbTE Hg). by rewrite ?mulr0 ?mul0r rmorph0 scale0r cq_single_zero.
  rewrite (bigD1 bot) //=; rewrite [X in _ + X]big1 ?addr0; last first. move=> f Hf; rewrite /trace_paramest_branch /seed_unused /hist_f /= (negbTE Hf). by rewrite ?mulr0 ?mul0r rmorph0 scale0r cq_single_zero. rewrite /trace_paramest_branch /trace_paramest_sample_branch /seed_unused /hist_K /hist_g /hist_f /= !eqxx. by rewrite !mulr1. } change (\sum_(t : round_trace) \sum_K trace_paramest_sample_branch EA r t K bot bot s rho = \sum_(p : round_trace * ((V * V) * V)) (fun t gf => trace_paramest_branch EA r (t, gf) s rho) p.1 p.2). rewrite -[RHS]pair_bigA /=; apply: eq_bigr => t _. change (\sum_K trace_paramest_sample_branch EA r t K bot bot s rho = \sum_(p : (V * V) * V) (fun kg f => trace_paramest_branch EA r (t, (kg, f)) s rho) p.1 p.2). rewrite -[RHS]pair_bigA /=. change (\sum_K trace_paramest_sample_branch EA r t K bot bot s rho = \sum_(kg : V * V) (fun K g => \sum_f trace_paramest_branch EA r (t, ((K, g), f)) s rho) kg.1 kg.2). rewrite -[RHS]pair_bigA /=; apply: eq_bigr => K _. by rewrite trace_paramest_sample_seed_sum. Qed.
Lemma denote_errcorr_trace_paramest_sample_branch (qA : {set L}) (EA : ADVq qA) (r : seq 'I_M) (t : round_trace) (K : V) (s : store) (rho :
  'F[HL]_setT) : DNg qA EA (ECs) (trace_paramest_sample_branch EA r t K bot bot s rho) = \sum_g trace_errcorr_branch EA r (t, ((K, g), bot))
  s rho.
Proof.
  have denote_errcorr_single_sum : forall (qA : {set L}) (EA : ADVq qA) (t : round_trace) (K f : V) (s : store) (rho : 'F[HL]_setT), DSg qA EA (ECs) s rho = \sum_g cq_single (errcorr_store (t, ((K, g), f)) s) ((unif_vseed (errcorr_seed_store s) g)%:C *: rho).
  { move=> {}qA {}EA {}t {}K f {}s {}rho. rewrite /ErrCorr denote_seq_assign_single. set s1 := store_set s pECv (ir_pub leakEC (s XA) (s XB)). rewrite denote_seq_assign_single. set s2 := store_set s1 Xhatv (ir_dec (s1 pECv) (s1 XB)). rewrite denote_seq_sample_single_sum.
    apply: eq_bigr => g _. rewrite cq_single_scale. congr (_ *: _). set s3 := store_set s2 gv g. rewrite denote_seq_assign_single. set s4 := store_set s3 tAv (verify_hash (s3 gv) (s3 XA)). rewrite denote_seq_assign_single. set s5 := store_set s4 tBv (verify_hash (s4 gv) (s4 Xhatv)). rewrite denote_assign_single. by rewrite /errcorr_store /errcorr_seed_store /hist_g /s1 /s2 /s3 /s4 /s5. } rewrite /trace_paramest_sample_branch /trace_errcorr_branch; set s_ann := announce_store (trace_store_seq t r s). rewrite -/(DSg qA EA (ECs) (paramest_store (t, ((K, bot), bot)) s_ann) ((trace_samples_weight t r s * trace_unused_weight t r * key_sample_mass s_ann K)%:C *: trace_so_seq EA t r rho)). rewrite (@denote_errcorr_single_sum qA EA t K bot (paramest_store (t, ((K, bot), bot)) s_ann) ((trace_samples_weight t r s * trace_unused_weight t r * key_sample_mass s_ann K)%:C *: trace_so_seq EA t r rho)). apply: eq_bigr => g _. congr (cq_single _ _). by rewrite /hist_K /hist_g /hist_f /seed_unused /= eqxx; rewrite !mulr1 !scalerA -!rmorphM mulrC. Qed.
Lemma denote_verify_privamp_trace_errcorr_branch (qA : {set L}) (EA : ADVq qA) (r : seq 'I_M) (t : round_trace) (K g : V) (s : store) (rho :
  'F[HL]_setT) : ~~ pe_failed (paramest_store (t, ((K, g), bot)) (announce_store (trace_store_seq t r s))) -> DNg qA EA (IF (fun u : store
  => u tAv != u tBv) THEN ABs ELSE PAs) (trace_errcorr_branch EA r (t, ((K, g), bot)) s rho) = \sum_f trace_final_branch EA r (t, ((K, g),
  f)) s rho.
Proof.
  have denote_verify_if_trace_errcorr_branch : forall (qA : {set L}) (EA : ADVq qA) (r : seq 'I_M) (h : run_history) (s : store) (rho : 'F[HL]_setT) (cont : @qkd_cmd R L HL Cv V), let s_ann := announce_store (trace_store_seq h.1 r s) in let s_pe := paramest_store h s_ann in let s_ec := errcorr_store h s_pe in DNg qA EA (IF (fun u : store => u tAv != u tBv) THEN ABs ELSE cont) (trace_errcorr_branch EA r h s rho) = if s_ec tAv != s_ec tBv then trace_verify_abort_branch EA r h s rho else DNg qA EA cont (trace_errcorr_branch EA r h s rho).
  { move=> {}qA {}EA {}r h {}s {}rho cont. rewrite /trace_errcorr_branch /trace_verify_abort_branch. set s_ann := announce_store (trace_store_seq h.1 r s). set s_pe := paramest_store h s_ann. set s_ec := errcorr_store h s_pe. set q := ((trace_samples_weight h.1 r s
    * trace_unused_weight h.1 r * key_sample_mass s_ann (hist_K h) * unif_vseed (errcorr_seed_store s_pe) (hist_g h) * seed_unused (hist_f h))%:C *: trace_so_seq EA h.1 r rho). rewrite -/(DSg qA EA (IF (fun u : store => u tAv != u tBv) THEN ABs ELSE cont) s_ec q). rewrite denote_if_single. case: (s_ec tAv != s_ec tBv) => //. by rewrite denote_abort_single. } have denote_privamp_trace_errcorr_branch : forall (qA : {set L}) (EA : ADVq qA) (r : seq 'I_M) (t : round_trace) (K g : V) (s : store) (rho : 'F[HL]_setT), DNg qA EA (PAs) (trace_errcorr_branch EA r (t, ((K, g), bot)) s rho) = \sum_f trace_privamp_branch EA r (t, ((K, g), f)) s rho.
{ clear rho s g K t r EA qA; move=> qA EA r t K g s rho. rewrite /trace_errcorr_branch. set s_ann := announce_store (trace_store_seq t r s); set s_pe := paramest_store (t, ((K, g), bot)) s_ann. set s_ec := errcorr_store (t, ((K, g), bot)) s_pe; rewrite /hist_K /hist_g /hist_f /seed_unused /= eqxx !mulr1. change (DSg qA EA (PAs) s_ec ((trace_samples_weight t r s * trace_unused_weight t r * key_sample_mass s_ann K
  * unif_vseed (errcorr_seed_store s_pe) g)%:C *: trace_so_seq EA t r rho) = \sum_f trace_privamp_branch EA r (t, ((K, g), f)) s rho).
  rewrite (@denote_privamp_single_sum qA EA t K g s_ec ((trace_samples_weight t r s * trace_unused_weight t r * key_sample_mass s_ann K * unif_vseed (errcorr_seed_store s_pe) g)%:C *: trace_so_seq EA t r rho)). apply: eq_bigr => f _. rewrite /trace_privamp_branch. congr (cq_single _ _). rewrite /hist_K /hist_g /hist_f /= -/s_ann; rewrite (paramest_store_future_irrel t K g f g bot s_ann) -/s_pe. rewrite (errcorr_store_f_irrel t K g f bot s_pe) -/s_ec. by rewrite !scalerA -!rmorphM mulrC. } set h0 := (t, ((K, g), bot)); set s_ann := announce_store (trace_store_seq t r s); set s_pe := paramest_store h0 s_ann. set s_ec := errcorr_store h0 s_pe; move=> /negbTE Hpass. rewrite (@denote_verify_if_trace_errcorr_branch qA EA r h0 s rho (PAs)). rewrite /h0 -/s_ann -/s_pe -/s_ec. case Hverify: (s_ec tAv != s_ec tBv).
  - rewrite (bigD1 bot) //=. rewrite /trace_final_branch /= -/s_ann -/h0 -/s_pe Hpass -/s_ec Hverify; rewrite [X in _ + X]big1 ?addr0 // => f Hf. by rewrite /trace_verify_abort_branch /seed_unused /hist_f /= (negbTE Hf); rewrite ?mulr0 ?mul0r rmorph0 scale0r cq_single_zero.
  - rewrite denote_privamp_trace_errcorr_branch. apply: eq_bigr => f _. rewrite /trace_final_branch /= -/s_ann. rewrite (paramest_store_future_irrel t K g f g bot s_ann) -/h0 -/s_pe Hpass. by rewrite (errcorr_store_f_irrel t K g f bot s_pe) -/h0 -/s_ec Hverify. Qed.
Lemma run_history_sum_split (T : zmodType) (F : round_trace -> V -> V -> V -> T) : \sum_(t : round_trace) \sum_K \sum_g \sum_f F t K g f =
  \sum_(h : run_history) F h.1 h.2.1.1 h.2.1.2 h.2.2.
Proof.
  change (\sum_(t : round_trace) \sum_K \sum_g \sum_f F t K g f = \sum_(p : round_trace * ((V * V) * V)) (fun t kgf => F t kgf.1.1 kgf.1.2 kgf.2) p.1 p.2). rewrite -[RHS]pair_bigA /=; apply: eq_bigr => t _. change (\sum_K \sum_g \sum_f F t K g f = \sum_(p : (V * V) * V) (fun kg f => F t kg.1 kg.2 f) p.1 p.2). rewrite -[RHS]pair_bigA /=. change (\sum_K \sum_g \sum_f F t K g f = \sum_(kg : V * V) (fun K g => \sum_f F t K g f) kg.1 kg.2). by rewrite -[RHS]pair_bigA. Qed.
Lemma run_history_sum_split_history (T : zmodType) (F : run_history -> T) : \sum_(t : round_trace) \sum_K \sum_g \sum_f F (t, ((K, g), f)) =
  \sum_(h : run_history) F h.
Proof. transitivity (\sum_(h : run_history) F (h.1, ((h.2.1.1, h.2.1.2), h.2.2))). - exact: (run_history_sum_split (fun t K g f => F (t, ((K, g), f)))). - apply: eq_bigr => h _. by case: h => t [[K g] f]. Qed.
Fact run_history_sum_split_prefix (T : zmodType) (F : run_history -> T) : \sum_(t : round_trace) \sum_K \sum_g \sum_f F (t, ((K, g), f)) =
  \sum_(p : round_trace * (V * V)) \sum_f F (p.1, ((p.2.1, p.2.2), f)).
Proof.
  change (\sum_(t : round_trace) \sum_K \sum_g \sum_f F (t, ((K, g), f)) = \sum_(p : round_trace * (V * V)) (fun t kg => \sum_f F (t, ((kg.1, kg.2), f))) p.1 p.2). rewrite -[RHS]pair_bigA /=; apply: eq_bigr => t _. change (\sum_K \sum_g \sum_f F (t, ((K, g), f)) = \sum_(kg : V * V) (fun K g => \sum_f F (t, ((K, g), f))) kg.1 kg.2). by rewrite -[RHS]pair_bigA. Qed.
Lemma run_prefix_sum_split (T : zmodType) (F : run_prefix -> V -> T) : \sum_(t : round_trace) \sum_K \sum_g \sum_f F (t, (K, g)) f = \sum_(p
  : run_prefix) \sum_f F p f.
Proof. transitivity (\sum_(p : run_prefix) \sum_f F (p.1, (p.2.1, p.2.2)) f). - exact: (run_history_sum_split_prefix (fun h => F (h.1, (h.2.1.1, h.2.1.2)) h.2.2)). - by apply: eq_bigr => p _; case: p => t [K g]. Qed.
Lemma run_history_sum_splitR (F : round_trace -> V -> V -> V -> R) : \sum_(t : round_trace) \sum_K \sum_g \sum_f F t K g f = \sum_(h :
  run_history) F h.1 h.2.1.1 h.2.1.2 h.2.2.
Proof. exact: (run_history_sum_split F). Qed.
Lemma trace_final_full_sum (qA : {set L}) (EA : ADVq qA) (r : seq 'I_M) (s : store) (rho : 'F[HL]_setT) : \sum_(t : round_trace) \sum_K
  \sum_g \sum_f trace_final_branch EA r (t, ((K, g), f)) s rho = \sum_(h : run_history) trace_final_branch EA r h s rho.
Proof. exact: run_history_sum_split_history. Qed.
Lemma trace_preverify_bot_full_sum (qA : {set L}) (EA : ADVq qA) (r : seq 'I_M) (s : store) (rho : 'F[HL]_setT) : \sum_(t : round_trace)
  \sum_K \sum_g trace_preverify_branch EA r (t, ((K, g), bot)) s rho = \sum_(h : run_history) trace_preverify_branch EA r h s rho.
Proof.
  have trace_preverify_full_sum : forall (qA : {set L}) (EA : ADVq qA) (r : seq 'I_M) (s : store) (rho : 'F[HL]_setT), \sum_(t : round_trace) \sum_K \sum_g \sum_f trace_preverify_branch EA r (t, ((K, g), f)) s rho = \sum_(h : run_history) trace_preverify_branch EA r h s rho.
  { move=> {}qA {}EA {}r {}s {}rho. exact: run_history_sum_split_history. } rewrite -(@trace_preverify_full_sum qA EA r s rho); apply: eq_bigr => t _. apply: eq_bigr => K _; apply: eq_bigr => g _. rewrite (bigD1 bot) //=; rewrite [X in _ + X]big1 ?addr0 // => f Hf; rewrite /trace_preverify_branch /=. set s_ann := announce_store (trace_store_seq t r s); set h := (t, ((K, g), f)); set s_pe := paramest_store h s_ann. case Hpe: (pe_failed s_pe).
  - rewrite /trace_pe_abort_branch /seed_unused /hist_f /= (negbTE Hf). by rewrite ?mulr0 ?mul0r rmorph0 scale0r cq_single_zero.
  - rewrite /trace_errcorr_branch /seed_unused /hist_f /= (negbTE Hf). by rewrite ?mulr0 ?mul0r rmorph0 scale0r cq_single_zero. Qed.
Fact denote_paramest_trace_announce_branch (qA : {set L}) (EA : ADVq qA) (r : seq 'I_M) (t : round_trace) (g f : V) (s : store) (rho :
  'F[HL]_setT) : DNg qA EA (PEs) (trace_announce_branch EA r t s rho) = \sum_K trace_paramest_sample_branch EA r t K g f s rho.
Proof.
  rewrite /trace_announce_branch /trace_paramest_sample_branch. rewrite -/(DSg qA EA (PEs) (announce_store (trace_store_seq t r s)) ((trace_samples_weight t r s * trace_unused_weight t r)%:C *: trace_so_seq EA t r rho)). rewrite (@denote_paramest_single_sum qA EA t g f (announce_store (trace_store_seq t r s)) ((trace_samples_weight t r s * trace_unused_weight t r)%:C *: trace_so_seq EA t r rho)).
    apply: eq_bigr => K _. congr (cq_single _ _). by rewrite scalerA -rmorphM mulrC. Qed.
Fact denote_start_rounds_announce_seq_sum (qA : {set L}) (EA : ADVq qA) (r : seq 'I_M) (s : store) (rho : 'F[HL]_setT) : uniq r -> (forall
  i, i \in r -> a_ i != y_ i) -> (forall i, i \in r -> Pvar != a_ i) -> (forall i, i \in r -> Pvar != y_ i) -> (forall i, i \in r -> Pvar !=
  b_ i) -> (forall i, i \in r -> Pvar != y'_ i) -> (forall i, i \in r -> Pvar != d_ i) -> Pvar != Xv -> Pvar != Zv -> Pvar != abortv -> DSg
  qA EA (seq_cmd start_cmd (seq_cmd (rounds_cmd_seq r) (ANNs))) s rho = \sum_(t : round_trace) trace_announce_branch EA r t (start_store s)
  rho.
Proof.
have start_store_public : forall (s : store), Pvar != Xv -> Pvar != Zv -> Pvar != abortv -> start_store s Pvar = empty_transcript.
{ clear rho s r EA qA; move=> s. move=> HPX HPZ HPabort. by rewrite /start_store store_set_other // store_set_other // store_set_other // store_set_same. } have denote_rounds_announce_seq_sum : forall (qA : {set L}) (EA : ADVq qA) (r : seq 'I_M) (s : store) (rho : 'F[HL]_setT), uniq r -> (forall i, i \in r -> a_ i != y_ i) -> (forall i, i \in r -> Pvar != a_ i) -> (forall i, i \in r -> Pvar != y_ i) -> (forall i, i \in r -> Pvar != b_ i) -> (forall i, i \in r -> Pvar != y'_ i) -> (forall i, i \in r -> Pvar != d_ i) -> Pvar != Xv -> Pvar != Zv -> s Pvar = empty_transcript -> DSg qA EA (seq_cmd (rounds_cmd_seq r) (ANNs)) s rho = \sum_(t : round_trace) trace_announce_branch EA r t s rho.
{ clear rho s r EA qA; move=> qA EA r s rho. have denote_announce_trace_branch : forall (qA : {set L}) (EA : ADVq qA) (r : seq 'I_M) (t : round_trace) (s : store) (rho : 'F[HL]_setT), DNg qA EA (ANNs) (trace_branch_seq EA r t s rho) = trace_announce_branch EA r t s rho.
{ clear rho s r EA qA; move=> qA EA r t s rho. have denote_announce_single : forall (qA : {set L}) (EA : ADVq qA) (s : store) (rho : 'F[HL]_setT), DSg qA EA (ANNs) s rho = cq_single (announce_store s) rho.
{ clear rho s t r EA qA; move=> qA EA s rho. by rewrite /Announce /announce_store denote_assign_single. } rewrite /trace_branch_seq /trace_announce_branch. rewrite -/(DSg qA EA (ANNs) (trace_store_seq t r s) ((trace_samples_weight t r s * trace_unused_weight t r)%:C *: trace_so_seq EA t r rho)). by rewrite denote_announce_single. } move=> Huniq Hay HPa HPy HPb HPy' HPd HPX HPZ Hpub; rewrite /denote_singleton denote_seq_cmd. rewrite -/(DSg qA EA (rounds_cmd_seq r) s rho). rewrite (@denote_rounds_seq_sum qA EA r s rho Huniq Hay HPa HPy HPb HPy' HPd HPX HPZ Hpub); rewrite denote_sum. by apply: eq_bigr => t _; rewrite denote_announce_trace_branch. } have denote_start_single : forall (qA : {set L}) (EA : ADVq qA) (s : store) (rho : 'F[HL]_setT), DSg qA EA start_cmd s rho = cq_single (start_store s) rho.
{ clear rho s r EA qA; move=> qA EA s rho. rewrite /start_cmd /start_store /denote_singleton !denote_seq_cmd. rewrite -/(DSg qA EA (Cassign Pvar (fun _ : store => empty_transcript)) s rho). rewrite denote_assign_single. rewrite -/(DSg qA EA (Cassign Xv (fun _ : store => vset set0)) (store_set s Pvar empty_transcript) rho). rewrite denote_assign_single. rewrite -/(DSg qA EA (Cassign Zv (fun _ : store => vset set0)) (store_set (store_set s Pvar empty_transcript) Xv (vset set0)) rho). rewrite denote_assign_single. rewrite -/(DSg qA EA (Cassign abortv (fun _ : store => vbool false)) (store_set (store_set (store_set s Pvar empty_transcript) Xv (vset set0)) Zv (vset set0)) rho). by rewrite denote_assign_single. } move=> Huniq Hay HPa HPy HPb HPy' HPd HPX HPZ HPabort; rewrite /denote_singleton denote_seq_cmd. rewrite -/(DSg qA EA start_cmd s rho) denote_start_single. rewrite -/(DSg qA EA (seq_cmd (rounds_cmd_seq r) (ANNs)) (start_store s) rho). apply: denote_rounds_announce_seq_sum => //. exact: start_store_public. Qed.
Fact denote_start_rounds_announce_paramest_seq_sum (qA : {set L}) (EA : ADVq qA) (r : seq 'I_M) (g f : V) (s : store) (rho : 'F[HL]_setT) :
  uniq r -> (forall i, i \in r -> a_ i != y_ i) -> (forall i, i \in r -> Pvar != a_ i) -> (forall i, i \in r -> Pvar != y_ i) -> (forall i,
  i \in r -> Pvar != b_ i) -> (forall i, i \in r -> Pvar != y'_ i) -> (forall i, i \in r -> Pvar != d_ i) -> Pvar != Xv -> Pvar != Zv ->
  Pvar != abortv -> DSg qA EA (seq_cmd (seq_cmd start_cmd (seq_cmd (rounds_cmd_seq r) (ANNs))) (PEs)) s rho = \sum_(t : round_trace) \sum_K
  trace_paramest_sample_branch EA r t K g f (start_store s) rho.
Proof.
  move=> Huniq Hay HPa HPy HPb HPy' HPd HPX HPZ HPabort; rewrite /denote_singleton denote_seq_cmd. rewrite -/(DSg qA EA (seq_cmd start_cmd (seq_cmd (rounds_cmd_seq r) (ANNs))) s rho). rewrite (@denote_start_rounds_announce_seq_sum qA EA r s rho Huniq Hay HPa HPy HPb HPy' HPd HPX HPZ HPabort); rewrite denote_sum. by apply: eq_bigr => t _; rewrite (@denote_paramest_trace_announce_branch qA EA r t g f (start_store s) rho). Qed.
Fact denote_start_rounds_announce_paramest_full_sum (qA : {set L}) (EA : ADVq qA) (r : seq 'I_M) (s : store) (rho : 'F[HL]_setT) : uniq r
  -> (forall i, i \in r -> a_ i != y_ i) -> (forall i, i \in r -> Pvar != a_ i) -> (forall i, i \in r -> Pvar != y_ i) -> (forall i, i \in r
  -> Pvar != b_ i) -> (forall i, i \in r -> Pvar != y'_ i) -> (forall i, i \in r -> Pvar != d_ i) -> Pvar != Xv -> Pvar != Zv -> Pvar !=
  abortv -> DSg qA EA (seq_cmd (seq_cmd start_cmd (seq_cmd (rounds_cmd_seq r) (ANNs))) (PEs)) s rho = \sum_(h : run_history)
  trace_paramest_branch EA r h (start_store s) rho.
Proof. move=> Huniq Hay HPa HPy HPb HPy' HPd HPX HPZ HPabort. rewrite (@denote_start_rounds_announce_paramest_seq_sum qA EA r bot bot s rho Huniq Hay HPa HPy HPb HPy' HPd HPX HPZ HPabort). exact: trace_paramest_full_sum. Qed.
Fact denote_start_rounds_announce_paramest_program_sum (qA : {set L}) (EA : ADVq qA) (r : seq 'I_M) (s : store) (rho : 'F[HL]_setT) : uniq
  r -> (forall i, i \in r -> a_ i != y_ i) -> (forall i, i \in r -> Pvar != a_ i) -> (forall i, i \in r -> Pvar != y_ i) -> (forall i, i \in
  r -> Pvar != b_ i) -> (forall i, i \in r -> Pvar != y'_ i) -> (forall i, i \in r -> Pvar != d_ i) -> Pvar != Xv -> Pvar != Zv -> Pvar !=
  abortv -> DSg qA EA (seq_cmd start_cmd (seq_cmd (rounds_cmd_seq r) (seq_cmd (ANNs) (PEs)))) s rho = \sum_(h : run_history)
  trace_paramest_branch EA r h (start_store s) rho.
Proof.
  move=> Huniq Hay HPa HPy HPb HPy' HPd HPX HPZ HPabort. rewrite [seq_cmd (rounds_cmd_seq r) (seq_cmd (ANNs) (PEs))]cmd_seqA. rewrite cmd_seqA. change (DSg qA EA (seq_cmd (seq_cmd start_cmd (seq_cmd (rounds_cmd_seq r) (ANNs))) (PEs)) s rho = \sum_(h : run_history) trace_paramest_branch EA r h (start_store s) rho). exact: (@denote_start_rounds_announce_paramest_full_sum qA EA r s rho Huniq Hay HPa HPy HPb HPy' HPd HPX HPZ HPabort). Qed.
Lemma denote_start_rounds_announce_paramest_program_denote_sum (qA : {set L}) (EA : ADVq qA) (r : seq 'I_M) (s : store) (rho : 'F[HL]_setT)
  : uniq r -> (forall i, i \in r -> a_ i != y_ i) -> (forall i, i \in r -> Pvar != a_ i) -> (forall i, i \in r -> Pvar != y_ i) -> (forall
  i, i \in r -> Pvar != b_ i) -> (forall i, i \in r -> Pvar != y'_ i) -> (forall i, i \in r -> Pvar != d_ i) -> Pvar != Xv -> Pvar != Zv ->
  Pvar != abortv -> DNg qA EA (PEs) (DNg qA EA (ANNs) (DNg qA EA (rounds_cmd_seq r) (DSg qA EA start_cmd s rho))) = \sum_(h : run_history)
  trace_paramest_branch EA r h (start_store s) rho.
Proof. move=> Huniq Hay HPa HPy HPb HPy' HPd HPX HPZ HPabort. rewrite -(@denote_start_rounds_announce_paramest_program_sum qA EA r s rho Huniq Hay HPa HPy HPb HPy' HPd HPX HPZ HPabort). by rewrite /denote_singleton !denote_seq_cmd. Qed.
Definition history_branch (qA : {set L}) (EA : ADVq qA) (s : store) (h : run_history) (rho : 'F[HL]_setT) : CQs := cq_single (final_store h
  s) ((hist_wt h s)%:C *: hist_so EA h rho).
Lemma trace_store_seq_enum (h : run_history) (s : store) : trace_store_seq h.1 (enum 'I_M) s = rounds_store h s.
Proof. by rewrite /rounds_store rounds_store_seqE. Qed.
Lemma trace_store_seq_enum_a (t : round_trace) (s : store) (i : 'I_M) : (forall j, j != i -> a_ i != a_ j) -> (forall j, a_ i != y_ j) ->
  (forall j, a_ i != b_ j) -> (forall j, a_ i != y'_ j) -> (forall j, a_ i != d_ j) -> a_ i != Xv -> a_ i != Zv -> trace_store_seq t (enum
  'I_M) s (a_ i) = choice_a (t i).
Proof.
  move=> Haa Hay Hab Hay' Had HaX HaZ; pose h : run_history := (t, ((bot, bot), bot)). have Hread : rounds_store h s (a_ i) = choice_a (h.1 i).
  { apply: (rounds_store_slot (i := i)); [exact: Haa | move=> j _; exact: Hay | move=> j _; exact: Hab | move=> j _; exact: Hay' | move=> j _; exact: Had | exact: HaX | exact: HaZ | move=> u]. by apply: write_round_choice_a; [exact: Hay | exact: Hab | exact: Hay' | exact: Had | exact: HaX | exact: HaZ]. } by rewrite -[t]/h.1 trace_store_seq_enum Hread. Qed.
Lemma trace_store_seq_enum_y (t : round_trace) (s : store) (i : 'I_M) : (forall j, j != i -> y_ i != a_ j) -> (forall j, y_ i != b_ j) ->
  (forall j, j != i -> y_ i != y_ j) -> (forall j, y_ i != y'_ j) -> (forall j, y_ i != d_ j) -> y_ i != Xv -> y_ i != Zv -> trace_store_seq
  t (enum 'I_M) s (y_ i) = choice_y (t i).
Proof.
  move=> Hya Hyb Hyy Hyy' Hyd HyX HyZ; pose h : run_history := (t, ((bot, bot), bot)). have Hread : rounds_store h s (y_ i) = hist_y h i.
  { by apply: rounds_store_y; [exact: Hya | exact: Hyb | exact: Hyy | exact: Hyy' | exact: Hyd | exact: HyX | exact: HyZ]. } by rewrite -[t]/h.1 trace_store_seq_enum Hread /h /hist_y /hist_choice. Qed.
Lemma trace_store_seq_enum_b (t : round_trace) (s : store) (i : 'I_M) : (forall j, b_ i != a_ j) -> (forall j, b_ i != y_ j) -> (forall j, j
  != i -> b_ i != b_ j) -> (forall j, b_ i != y'_ j) -> (forall j, b_ i != d_ j) -> b_ i != Xv -> b_ i != Zv -> trace_store_seq t (enum
  'I_M) s (b_ i) = choice_b (t i).
Proof.
  move=> Hba Hby Hbb Hby' Hbd HbX HbZ; pose h : run_history := (t, ((bot, bot), bot)). have Hread : rounds_store h s (b_ i) = choice_b (h.1 i).
  { apply: (rounds_store_slot (i := i)); [move=> j _; exact: Hba | move=> j _; exact: Hby | exact: Hbb | move=> j _; exact: Hby' | move=> j _; exact: Hbd | exact: HbX | exact: HbZ | move=> u]. by apply: write_round_choice_b; [exact: Hby' | exact: Hbd | exact: HbX | exact: HbZ]. } by rewrite -[t]/h.1 trace_store_seq_enum Hread. Qed.
Lemma trace_store_seq_enum_y' (t : round_trace) (s : store) (i : 'I_M) : (forall j, y'_ i != a_ j) -> (forall j, y'_ i != y_ j) -> (forall
  j, y'_ i != b_ j) -> (forall j, j != i -> y'_ i != y'_ j) -> (forall j, y'_ i != d_ j) -> y'_ i != Xv -> y'_ i != Zv -> trace_store_seq t
  (enum 'I_M) s (y'_ i) = choice_y' (t i).
Proof.
  move=> Hy'a Hy'y Hy'b Hy'y' Hy'd Hy'X Hy'Z; pose h : run_history := (t, ((bot, bot), bot)). have Hread : rounds_store h s (y'_ i) = hist_y' h i.
  { by apply: rounds_store_y'; [exact: Hy'a | exact: Hy'y | exact: Hy'b | exact: Hy'y' | exact: Hy'd | exact: Hy'X | exact: Hy'Z]. } by rewrite -[t]/h.1 trace_store_seq_enum Hread /h /hist_y' /hist_choice. Qed.
Lemma trace_store_seq_enum_d (t : round_trace) (s : store) (i : 'I_M) : (forall j, d_ i != a_ j) -> (forall j, d_ i != y_ j) -> (forall j,
  d_ i != b_ j) -> (forall j, d_ i != y'_ j) -> (forall j, j != i -> d_ i != d_ j) -> d_ i != Xv -> d_ i != Zv -> trace_store_seq t (enum
  'I_M) s (d_ i) = vbool (trace_detected t i).
Proof.
  move=> Hda Hdy Hdb Hdy' Hdd HdX HdZ; pose h : run_history := (t, ((bot, bot), bot)). have Hread : rounds_store h s (d_ i) = vbool (trace_detected h.1 i).
  { rewrite /trace_detected; apply: (rounds_store_slot (i := i)); [move=> j _; exact: Hda | move=> j _; exact: Hdy | move=> j _; exact: Hdb | move=> j _; exact: Hdy' | exact: Hdd | exact: HdX | exact: HdZ | move=> u]. by apply: write_round_choice_d; [exact: HdX | exact: HdZ]. }
by rewrite -[t]/h.1 trace_store_seq_enum Hread. Qed.
Lemma enum_rcons_last_max (r : seq 'I_M) (i : 'I_M) : enum 'I_M = rcons r i -> forall j : 'I_M, (nat_of_ord j <= nat_of_ord i)%N.
Proof.
  move=> Henum j; rewrite -!index_enum_ord Henum. have Hj : j \in rcons r i by rewrite -Henum mem_enum. have Hj_lt : (index j (rcons r i) < size (rcons r i))%N by rewrite index_mem. have Hi_notin : i \notin r.
  { have Huniq : uniq (rcons r i) by rewrite -Henum enum_uniq. by move: Huniq; rewrite rcons_uniq => /andP[]. } have Hi_index : index i (rcons r i) = size r by rewrite -cats1 index_cat (negbTE Hi_notin) /= eqxx addn0. by rewrite Hi_index; move: Hj_lt; rewrite size_rcons ltnS. Qed.
Fact trace_store_enum_key_set (vsetK : forall X : {set 'I_M}, vset_of (vset X) = X) (t : round_trace) (r : seq 'I_M) (i : 'I_M) (s : store)
  : enum 'I_M = rcons r i -> vbool true != vbool false -> Xv != Zv -> (forall j, trace_store_seq t (enum 'I_M) s (a_ j) = choice_a (t j)) ->
  (forall j, trace_store_seq t (enum 'I_M) s (b_ j) = choice_b (t j)) -> (forall j, trace_store_seq t (enum 'I_M) s (d_ j) = vbool
  (trace_detected t j)) -> (forall j, a_ j != Xv) -> (forall j, a_ j != Zv) -> (forall j, b_ j != Xv) -> (forall j, b_ j != Zv) -> (forall
  j, d_ j != Xv) -> (forall j, d_ j != Zv) -> vset_of (trace_store_seq t (enum 'I_M) s Xv) = trace_key_set t.
Proof.
have trace_store_seq_rcons_Xv_trace : forall (vsetK : forall X : {set 'I_M}, vset_of (vset X) = X) (t : round_trace) (r : seq 'I_M) (i : 'I_M) (s : store), vbool true != vbool false -> Xv != Zv -> let spre := trace_store_seq t r s in let s5 := store_set (round_measure_store (t i) i spre) (d_ i) (vbool (trace_detected t i)) in (forall j, (nat_of_ord j <= nat_of_ord i)%N -> s5 (a_ j) = choice_a (t j)) -> (forall j, (nat_of_ord j <= nat_of_ord i)%N -> s5 (b_ j) = choice_b (t j)) -> (forall j, (nat_of_ord j <= nat_of_ord i)%N -> s5 (d_ j) = vbool (trace_detected t j)) -> vset_of (trace_store_seq t (rcons r i) s Xv) = trace_key_set_through t i.
{ clear s i r t vsetK; move=> vsetK t r i s. move=> Htf HXZ /= Ha Hb Hd; rewrite /trace_store_seq foldl_rcons. change (vset_of (write_trace_round t i (trace_store_seq t r s) Xv) = trace_key_set_through t i). rewrite /write_trace_round /write_round_choice /round_sift_store; set s4 := round_measure_store _ _ _; set s5 := store_set s4 (d_ i) _. set s6 := store_set s5 Xv _; rewrite store_set_other // /s6 store_set_same vsetK; apply/setP=> j. rewrite /replay_rounds_through /trace_key_set_through !inE. case Hle: (nat_of_ord j <= nat_of_ord i)%N => //. by rewrite (replay_sift_X_trace (t := t) (s := s5) (i := j) Htf (Ha j Hle) (Hb j Hle) (Hd j Hle)). }
move=> Henum Htf HXZ Ha Hb Hd HaX HaZ HbX HbZ HdX HdZ; have Hmax := enum_rcons_last_max Henum. rewrite Henum. transitivity (trace_key_set_through t i).
  - apply: trace_store_seq_rcons_Xv_trace => //=.
    + move=> j _; move: (Ha j); rewrite Henum /trace_store_seq foldl_rcons /write_trace_round /write_round_choice /round_sift_store. set s4 := round_measure_store _ _ _; set s5 := store_set s4 (d_ i) _; set s6 := store_set s5 Xv _. rewrite store_set_other; last exact: HaZ.
      rewrite store_set_other; last exact: HaX. by [].
    + move=> j _; move: (Hb j); rewrite Henum /trace_store_seq foldl_rcons /write_trace_round /write_round_choice /round_sift_store. set s4 := round_measure_store _ _ _; set s5 := store_set s4 (d_ i) _; set s6 := store_set s5 Xv _. rewrite store_set_other; last exact: HbZ.
      rewrite store_set_other; last exact: HbX. by [].
    + move=> j _; move: (Hd j); rewrite Henum /trace_store_seq foldl_rcons /write_trace_round /write_round_choice /round_sift_store. set s4 := round_measure_store _ _ _; set s5 := store_set s4 (d_ i) _; set s6 := store_set s5 Xv _. rewrite store_set_other; last exact: HdZ.
      rewrite store_set_other; last exact: HdX. by [].
  - by apply/setP=> j; rewrite /trace_key_set_through /trace_key_set !inE (Hmax j). Qed.
Lemma trace_store_enum_test_set (vsetK : forall X : {set 'I_M}, vset_of (vset X) = X) (t : round_trace) (r : seq 'I_M) (i : 'I_M) (s :
  store) : enum 'I_M = rcons r i -> vbool true != vbool false -> (forall j, trace_store_seq t (enum 'I_M) s (a_ j) = choice_a (t j)) ->
  (forall j, trace_store_seq t (enum 'I_M) s (b_ j) = choice_b (t j)) -> (forall j, trace_store_seq t (enum 'I_M) s (d_ j) = vbool
  (trace_detected t j)) -> (forall j, a_ j != Xv) -> (forall j, a_ j != Zv) -> (forall j, b_ j != Xv) -> (forall j, b_ j != Zv) -> (forall
  j, d_ j != Xv) -> (forall j, d_ j != Zv) -> vset_of (trace_store_seq t (enum 'I_M) s Zv) = trace_test_set t.
Proof.
  have replay_sift_Z_trace : forall (t : round_trace) (s : store) (i : 'I_M), vbool true != vbool false -> s (a_ i) = choice_a (t i) -> s (b_ i) = choice_b (t i) -> s (d_ i) = vbool (trace_detected t i) -> replay_sift_Z s i = trace_test_round t i.
  { move=> {}t {}s {}i. move=> Htf Ha Hb Hd; rewrite /replay_sift_Z /trace_test_round Ha Hb Hd. case: (trace_detected t i) => /=; first by rewrite eqxx. have Hft : vbool false != vbool true by rewrite eq_sym Htf. by rewrite (negbTE Hft). } have trace_store_seq_rcons_Zv_trace : forall (vsetK : forall X : {set 'I_M}, vset_of (vset X) = X) (t : round_trace) (r : seq 'I_M) (i : 'I_M) (s : store), vbool true != vbool false -> let spre := trace_store_seq t r s in let s5 := store_set (round_measure_store (t i) i spre) (d_ i) (vbool (trace_detected t i)) in (forall j, (nat_of_ord j <= nat_of_ord i)%N -> s5 (a_ j) = choice_a (t j)) -> (forall j, (nat_of_ord j <= nat_of_ord i)%N -> s5 (b_ j) = choice_b (t j)) -> (forall j, (nat_of_ord j <= nat_of_ord i)%N -> s5 (d_ j) = vbool (trace_detected t j)) -> (forall j, (nat_of_ord j <= nat_of_ord i)%N -> Xv != a_ j) -> (forall j, (nat_of_ord j <= nat_of_ord i)%N -> Xv != b_ j) -> (forall j, (nat_of_ord j <= nat_of_ord i)%N -> Xv != d_ j) -> vset_of (trace_store_seq t (rcons r i) s Zv) = trace_test_set_through t i.
{ clear s i r t vsetK; move=> vsetK t r i s. move=> Htf /= Ha Hb Hd HXa HXb HXd; rewrite /trace_store_seq foldl_rcons. change (vset_of (write_trace_round t i (trace_store_seq t r s) Zv) = trace_test_set_through t i). rewrite /write_trace_round /write_round_choice /round_sift_store; set s4 := round_measure_store _ _ _; set s5 := store_set s4 (d_ i) _. set s6 := store_set s5 Xv _; rewrite store_set_same vsetK; apply/setP=> j. rewrite /replay_rounds_through /trace_test_set_through !inE. case Hle: (nat_of_ord j <= nat_of_ord i)%N => //. have Ha6 : s6 (a_ j) = choice_a (t j).
  { have Hja : a_ j != Xv by rewrite eq_sym (HXa j Hle). by rewrite /s6 store_set_other //; exact: Ha j Hle. } have Hb6 : s6 (b_ j) = choice_b (t j).
  { have Hjb : b_ j != Xv by rewrite eq_sym (HXb j Hle). by rewrite /s6 store_set_other //; exact: Hb j Hle. } have Hd6 : s6 (d_ j) = vbool (trace_detected t j).
  { have Hjd : d_ j != Xv by rewrite eq_sym (HXd j Hle). by rewrite /s6 store_set_other //; exact: Hd j Hle. } by rewrite (replay_sift_Z_trace t s6 j Htf Ha6 Hb6 Hd6). } move=> Henum Htf Ha Hb Hd HaX HaZ HbX HbZ HdX HdZ; have Hmax := enum_rcons_last_max Henum. rewrite Henum. transitivity (trace_test_set_through t i).
  - apply: trace_store_seq_rcons_Zv_trace => //=.
    + move=> j _; move: (Ha j); rewrite Henum /trace_store_seq foldl_rcons /write_trace_round /write_round_choice /round_sift_store. set s4 := round_measure_store _ _ _; set s5 := store_set s4 (d_ i) _; set s6 := store_set s5 Xv _. rewrite store_set_other; last exact: HaZ.
      rewrite store_set_other; last exact: HaX. by [].
    + move=> j _; move: (Hb j); rewrite Henum /trace_store_seq foldl_rcons /write_trace_round /write_round_choice /round_sift_store. set s4 := round_measure_store _ _ _; set s5 := store_set s4 (d_ i) _; set s6 := store_set s5 Xv _. rewrite store_set_other; last exact: HbZ.
      rewrite store_set_other; last exact: HbX. by [].
    + move=> j _; move: (Hd j); rewrite Henum /trace_store_seq foldl_rcons /write_trace_round /write_round_choice /round_sift_store. set s4 := round_measure_store _ _ _; set s5 := store_set s4 (d_ i) _; set s6 := store_set s5 Xv _. rewrite store_set_other; last exact: HdZ.
      rewrite store_set_other; last exact: HdX. by [].
    + by move=> j _; rewrite eq_sym (HaX j).
    + by move=> j _; rewrite eq_sym (HbX j).
    + by move=> j _; rewrite eq_sym (HdX j).
  - by apply/setP=> j; rewrite /trace_test_set_through /trace_test_set !inE (Hmax j). Qed.
Fact announce_store_trace_key_set (vsetK : forall X : {set 'I_M}, vset_of (vset X) = X) (t : round_trace) (r : seq 'I_M) (i : 'I_M) (s :
  store) : enum 'I_M = rcons r i -> vbool true != vbool false -> Xv != Zv -> Pvar != Xv -> (forall j, trace_store_seq t (enum 'I_M) s (a_ j)
  = choice_a (t j)) -> (forall j, trace_store_seq t (enum 'I_M) s (b_ j) = choice_b (t j)) -> (forall j, trace_store_seq t (enum 'I_M) s (d_
  j) = vbool (trace_detected t j)) -> (forall j, a_ j != Xv) -> (forall j, a_ j != Zv) -> (forall j, b_ j != Xv) -> (forall j, b_ j != Zv)
  -> (forall j, d_ j != Xv) -> (forall j, d_ j != Zv) -> vset_of (announce_store (trace_store_seq t (enum 'I_M) s) Xv) = trace_key_set t.
Proof. move=> Henum Htf HXZ HPX Ha Hb Hd HaX HaZ HbX HbZ HdX HdZ; rewrite announce_store_other; last by rewrite eq_sym. exact: (trace_store_enum_key_set vsetK Henum Htf HXZ Ha Hb Hd HaX HaZ HbX HbZ HdX HdZ). Qed.
Fact announce_store_trace_test_set (vsetK : forall X : {set 'I_M}, vset_of (vset X) = X) (t : round_trace) (r : seq 'I_M) (i : 'I_M) (s :
  store) : enum 'I_M = rcons r i -> vbool true != vbool false -> Pvar != Zv -> (forall j, trace_store_seq t (enum 'I_M) s (a_ j) = choice_a
  (t j)) -> (forall j, trace_store_seq t (enum 'I_M) s (b_ j) = choice_b (t j)) -> (forall j, trace_store_seq t (enum 'I_M) s (d_ j) = vbool
  (trace_detected t j)) -> (forall j, a_ j != Xv) -> (forall j, a_ j != Zv) -> (forall j, b_ j != Xv) -> (forall j, b_ j != Zv) -> (forall
  j, d_ j != Xv) -> (forall j, d_ j != Zv) -> vset_of (announce_store (trace_store_seq t (enum 'I_M) s) Zv) = trace_test_set t.
Proof. move=> Henum Htf HPZ Ha Hb Hd HaX HaZ HbX HbZ HdX HdZ; rewrite announce_store_other; last by rewrite eq_sym. exact: (trace_store_enum_test_set vsetK Henum Htf Ha Hb Hd HaX HaZ HbX HbZ HdX HdZ). Qed.
Fact key_sample_deviation_store_trace_sets (vsetK : forall X : {set 'I_M}, vset_of (vset X) = X) (mu : nat -> R) (t : round_trace) (r : seq
  'I_M) (i : 'I_M) (s : store) (K : V) : enum 'I_M = rcons r i -> vbool true != vbool false -> (forall j, trace_store_seq t (enum 'I_M) s
  (a_ j) = choice_a (t j)) -> (forall j, trace_store_seq t (enum 'I_M) s (b_ j) = choice_b (t j)) -> (forall j, trace_store_seq t (enum
  'I_M) s (d_ j) = vbool (trace_detected t j)) -> (forall j, a_ j != Xv) -> (forall j, a_ j != Zv) -> (forall j, b_ j != Xv) -> (forall j,
  b_ j != Zv) -> (forall j, d_ j != Xv) -> (forall j, d_ j != Zv) -> pewall (Zv != Kv -> Zv != XA -> Zv != XB -> Zv != ZA -> Zv != ZB -> Zv
  != Pvar -> Zv != lamv -> Kv != XA -> (forall j, y_ j != Kv) -> (forall j, y_ j != XA) -> (forall j, y_ j != XB) -> (forall j, y'_ j != Kv)
  -> (forall j, y'_ j != XA) -> (forall j, y'_ j != XB) -> (forall j, y'_ j != ZA) -> let s_ann := announce_store (trace_store_seq t (enum
  'I_M) s) in key_sample_deviation_store mu (paramest_store (t, ((K, bot), bot)) s_ann) = (let alice_bits := fun j => s_ann (y_ j) in let
  bob_bits := fun j => s_ann (y'_ j) in (err_count (bits_on (vset_of K) alice_bits) (bits_on (vset_of K) bob_bits))%:R / n%:R >= (err_count
  (test_bits_on (trace_test_set t) alice_bits) (test_bits_on (trace_test_set t) bob_bits))%:R / (#|trace_test_set t|)%:R + mu
  #|trace_test_set t|)).
Proof.
  move=> Henum Htf Ha Hb Hd HaX HaZ HbX HbZ HdX HdZ HXAB HXAZA HXAZB HXAP HXAlam HXBZA HXBZB HXBP HXBlam HZAZB HZAP HZAlam HZBP HZBlam HZK HZXA HZXB HZZA HZZB HZP HZlam HKXA HyK HyXA HyXB Hy'K Hy'XA Hy'XB Hy'ZA s_ann. set h := (t, ((K, bot), bot)). have HZv : vset_of (paramest_store h s_ann Zv) = trace_test_set t.
  { rewrite (paramest_store_other (x := Zv) h s_ann) //; rewrite /s_ann announce_store_other //. exact: (trace_store_enum_test_set vsetK Henum Htf Ha Hb Hd HaX HaZ HbX HbZ HdX HdZ). } have HXAread : paramest_store h s_ann XA = bits_on (vset_of K) (fun j => s_ann (y_ j)).
  { rewrite (paramest_store_XA h s_ann HXAB HXAZA HXAZB HXAP HXAlam) store_set_same. by congr bits_on; apply/funext=> j; rewrite store_set_other. } have HXBread : paramest_store h s_ann XB = bits_on (vset_of K) (fun j => s_ann (y'_ j)).
  { rewrite (paramest_store_XB h s_ann HXBZA HXBZB HXBP HXBlam); set s1 := store_set s_ann Kv K; set s2 := store_set s1 XA _. rewrite /s2 store_set_other // /s1 store_set_same. by congr bits_on; apply/funext=> j; rewrite /s2 store_set_other // /s1 store_set_other. } have HZAread : paramest_store h s_ann ZA = test_bits_on (trace_test_set t) (fun j => s_ann (y_ j)).
  { rewrite (paramest_store_ZA h s_ann HZAZB HZAP HZAlam); set s1 := store_set s_ann Kv K; set s2 := store_set s1 XA _. set s3 := store_set s2 XB _. have Hs3Zv : vset_of (s3 Zv) = trace_test_set t.
    { rewrite /s3 store_set_other // /s2 store_set_other // /s1 store_set_other //; rewrite /s_ann announce_store_other //. exact: (trace_store_enum_test_set vsetK Henum Htf Ha Hb Hd HaX HaZ HbX HbZ HdX HdZ). } rewrite Hs3Zv; congr test_bits_on; apply/funext=> j. by rewrite /s3 store_set_other // /s2 store_set_other // /s1 store_set_other. } have HZBread : paramest_store h s_ann ZB = test_bits_on (trace_test_set t) (fun j => s_ann (y'_ j)).
  { rewrite (paramest_store_ZB h s_ann HZBP HZBlam); set s1 := store_set s_ann Kv K; set s2 := store_set s1 XA _. set s3 := store_set s2 XB _; set s4 := store_set s3 ZA _. have Hs4Zv : vset_of (s4 Zv) = trace_test_set t.
    { rewrite /s4 store_set_other // /s3 store_set_other // /s2 store_set_other // /s1 store_set_other //. rewrite /s_ann announce_store_other //; exact: (trace_store_enum_test_set vsetK Henum Htf Ha Hb Hd HaX HaZ HbX HbZ HdX HdZ). } rewrite Hs4Zv; congr test_bits_on; apply/funext=> j. by rewrite /s4 store_set_other // /s3 store_set_other // /s2 store_set_other // /s1 store_set_other. } by rewrite /key_sample_deviation_store HZv HXAread HXBread HZAread HZBread. Qed.
Lemma key_sample_deviation_event_trace_sets (vsetK : forall X : {set 'I_M}, vset_of (vset X) = X) (mu : nat -> R) (t : round_trace) (r : seq
  'I_M) (i : 'I_M) (s : store) (K : V) : enum 'I_M = rcons r i -> vbool true != vbool false -> (forall j, trace_store_seq t (enum 'I_M) s
  (a_ j) = choice_a (t j)) -> (forall j, trace_store_seq t (enum 'I_M) s (b_ j) = choice_b (t j)) -> (forall j, trace_store_seq t (enum
  'I_M) s (d_ j) = vbool (trace_detected t j)) -> (forall j, a_ j != Xv) -> (forall j, a_ j != Zv) -> (forall j, b_ j != Xv) -> (forall j,
  b_ j != Zv) -> (forall j, d_ j != Xv) -> (forall j, d_ j != Zv) -> pewall (Zv != Kv -> Zv != XA -> Zv != XB -> Zv != ZA -> Zv != ZB -> Zv
  != Pvar -> Zv != lamv -> Kv != XA -> (forall j, y_ j != Kv) -> (forall j, y_ j != XA) -> (forall j, y_ j != XB) -> (forall j, y'_ j != Kv)
  -> (forall j, y'_ j != XA) -> (forall j, y'_ j != XB) -> (forall j, y'_ j != ZA) -> let s_ann := announce_store (trace_store_seq t (enum
  'I_M) s) in (K \in key_sample_deviation_event mu t s_ann) = (let alice_bits := fun j => s_ann (y_ j) in let bob_bits := fun j => s_ann
  (y'_ j) in (err_count (bits_on (vset_of K) alice_bits) (bits_on (vset_of K) bob_bits))%:R / n%:R >= (err_count (test_bits_on
  (trace_test_set t) alice_bits) (test_bits_on (trace_test_set t) bob_bits))%:R / (#|trace_test_set t|)%:R + mu #|trace_test_set t|)).
Proof.
  move=> Henum Htf Ha Hb Hd HaX HaZ HbX HbZ HdX HdZ HXAB HXAZA HXAZB HXAP HXAlam HXBZA HXBZB HXBP HXBlam HZAZB HZAP HZAlam HZBP HZBlam HZK HZXA HZXB HZZA HZZB HZP HZlam HKXA HyK HyXA HyXB Hy'K Hy'XA Hy'XB Hy'ZA s_ann. rewrite /key_sample_deviation_event inE /s_ann. rewrite (key_sample_deviation_store_trace_sets (t := t) (r := r) (i := i) (s := s) vsetK mu K Henum Htf Ha Hb Hd HaX HaZ HbX HbZ HdX HdZ HXAB HXAZA HXAZB HXAP HXAlam HXBZA HXBZB HXBP HXBlam HZAZB HZAP HZAlam HZBP HZBlam HZK HZXA HZXB HZZA HZZB HZP HZlam HKXA HyK HyXA HyXB Hy'K Hy'XA Hy'XB Hy'ZA). by []. Qed.
Lemma key_sample_deviation_event_trace_choices (vsetK : forall X : {set 'I_M}, vset_of (vset X) = X) (mu : nat -> R) (t : round_trace) (r :
  seq 'I_M) (i : 'I_M) (s : store) (K : V) : enum 'I_M = rcons r i -> vbool true != vbool false -> (forall j, trace_store_seq t (enum 'I_M)
  s (a_ j) = choice_a (t j)) -> (forall j, trace_store_seq t (enum 'I_M) s (b_ j) = choice_b (t j)) -> (forall j, trace_store_seq t (enum
  'I_M) s (d_ j) = vbool (trace_detected t j)) -> (forall j, trace_store_seq t (enum 'I_M) s (y_ j) = choice_y (t j)) -> (forall j,
  trace_store_seq t (enum 'I_M) s (y'_ j) = choice_y' (t j)) -> (forall j, a_ j != Xv) -> (forall j, a_ j != Zv) -> (forall j, b_ j != Xv)
  -> (forall j, b_ j != Zv) -> (forall j, d_ j != Xv) -> (forall j, d_ j != Zv) -> (forall j, y_ j != Pvar) -> (forall j, y'_ j != Pvar) ->
  pewall (Zv != Kv -> Zv != XA -> Zv != XB -> Zv != ZA -> Zv != ZB -> Zv != Pvar -> Zv != lamv -> Kv != XA -> (forall j, y_ j != Kv) ->
  (forall j, y_ j != XA) -> (forall j, y_ j != XB) -> (forall j, y'_ j != Kv) -> (forall j, y'_ j != XA) -> (forall j, y'_ j != XB) ->
  (forall j, y'_ j != ZA) -> let s_ann := announce_store (trace_store_seq t (enum 'I_M) s) in (K \in key_sample_deviation_event mu t s_ann)
  = ((err_count (bits_on (vset_of K) (fun j => choice_y (t j))) (bits_on (vset_of K) (fun j => choice_y' (t j))))%:R / n%:R >= (err_count
  (test_bits_on (trace_test_set t) (fun j => choice_y (t j))) (test_bits_on (trace_test_set t) (fun j => choice_y' (t j))))%:R /
  (#|trace_test_set t|)%:R + mu #|trace_test_set t|)).
Proof.
  move=> Henum Htf Ha Hb Hd Hy Hy' HaX HaZ HbX HbZ HdX HdZ HyP Hy'P HXAB HXAZA HXAZB HXAP HXAlam HXBZA HXBZB HXBP HXBlam HZAZB HZAP HZAlam HZBP HZBlam HZK HZXA HZXB HZZA HZZB HZP HZlam HKXA HyK HyXA HyXB Hy'K Hy'XA Hy'XB Hy'ZA s_ann. rewrite (key_sample_deviation_event_trace_sets (t := t) (r := r) (i := i) (s := s) vsetK mu K Henum Htf Ha Hb Hd HaX HaZ HbX HbZ HdX HdZ HXAB HXAZA HXAZB HXAP HXAlam HXBZA HXBZB HXBP HXBlam HZAZB HZAP HZAlam HZBP HZBlam HZK HZXA HZXB HZZA HZZB HZP HZlam HKXA HyK HyXA HyXB Hy'K Hy'XA Hy'XB Hy'ZA). set s_ann0 := announce_store _. have HyE : (fun j => s_ann0 (y_ j)) = (fun j => choice_y (t j)) by apply/funext=> j; rewrite /s_ann0 announce_store_other ?Hy. have Hy'E : (fun j => s_ann0 (y'_ j)) = (fun j => choice_y' (t j)) by apply/funext=> j; rewrite /s_ann0 announce_store_other ?Hy'. by rewrite HyE Hy'E. Qed.
Lemma key_sample_deviation_event_enum_choices (vsetK : forall X : {set 'I_M}, vset_of (vset X) = X) (mu : nat -> R) (t : round_trace) (r :
  seq 'I_M) (i : 'I_M) (s : store) (K : V) : enum 'I_M = rcons r i -> vbool true != vbool false -> (forall i j, j != i -> a_ i != a_ j) ->
  (forall i j, a_ i != y_ j) -> (forall i j, a_ i != b_ j) -> (forall i j, a_ i != y'_ j) -> (forall i j, a_ i != d_ j) -> (forall i, a_ i
  != Xv) -> (forall i, a_ i != Zv) -> (forall i j, b_ i != a_ j) -> (forall i j, b_ i != y_ j) -> (forall i j, j != i -> b_ i != b_ j) ->
  (forall i j, b_ i != y'_ j) -> (forall i j, b_ i != d_ j) -> (forall i, b_ i != Xv) -> (forall i, b_ i != Zv) -> (forall i j, d_ i != a_
  j) -> (forall i j, d_ i != y_ j) -> (forall i j, d_ i != b_ j) -> (forall i j, d_ i != y'_ j) -> (forall i j, j != i -> d_ i != d_ j) ->
  (forall i, d_ i != Xv) -> (forall i, d_ i != Zv) -> (forall i j, j != i -> y_ i != a_ j) -> (forall i j, y_ i != b_ j) -> (forall i j, j
  != i -> y_ i != y_ j) -> (forall i j, y_ i != y'_ j) -> (forall i j, y_ i != d_ j) -> (forall i, y_ i != Xv) -> (forall i, y_ i != Zv) ->
  (forall i j, y'_ i != a_ j) -> (forall i j, y'_ i != y_ j) -> (forall i j, y'_ i != b_ j) -> (forall i j, j != i -> y'_ i != y'_ j) ->
  (forall i j, y'_ i != d_ j) -> (forall i, y'_ i != Xv) -> (forall i, y'_ i != Zv) -> (forall j, y_ j != Pvar) -> (forall j, y'_ j != Pvar)
  -> pewall (Zv != Kv -> Zv != XA -> Zv != XB -> Zv != ZA -> Zv != ZB -> Zv != Pvar -> Zv != lamv -> Kv != XA -> (forall j, y_ j != Kv) ->
  (forall j, y_ j != XA) -> (forall j, y_ j != XB) -> (forall j, y'_ j != Kv) -> (forall j, y'_ j != XA) -> (forall j, y'_ j != XB) ->
  (forall j, y'_ j != ZA) -> let s_ann := announce_store (trace_store_seq t (enum 'I_M) s) in (K \in key_sample_deviation_event mu t s_ann)
  = ((err_count (bits_on (vset_of K) (fun j => choice_y (t j))) (bits_on (vset_of K) (fun j => choice_y' (t j))))%:R / n%:R >= (err_count
  (test_bits_on (trace_test_set t) (fun j => choice_y (t j))) (test_bits_on (trace_test_set t) (fun j => choice_y' (t j))))%:R /
  (#|trace_test_set t|)%:R + mu #|trace_test_set t|)).
Proof.
  move=> Henum Htf Haa Hay Hab Hay' Had HaX HaZ Hba Hby Hbb Hby' Hbd HbX HbZ Hda Hdy Hdb Hdy' Hdd HdX HdZ Hya Hyb Hyy Hyy' Hyd HyX HyZ Hy'a Hy'y Hy'b Hy'y' Hy'd Hy'X Hy'Z HyP Hy'P HXAB HXAZA HXAZB HXAP HXAlam HXBZA HXBZB HXBP HXBlam HZAZB HZAP HZAlam HZBP HZBlam HZK HZXA HZXB HZZA HZZB HZP HZlam HKXA HyK HyXA HyXB Hy'K Hy'XA Hy'XB Hy'ZA s_ann. have HaR : forall j, trace_store_seq t (enum 'I_M) s (a_ j) = choice_a (t j).
  { move=> j; exact: (trace_store_seq_enum_a t s (Haa j) (Hay j) (Hab j) (Hay' j) (Had j) (HaX j) (HaZ j)). } have HbR : forall j, trace_store_seq t (enum 'I_M) s (b_ j) = choice_b (t j).
  { move=> j; exact: (trace_store_seq_enum_b t s (Hba j) (Hby j) (Hbb j) (Hby' j) (Hbd j) (HbX j) (HbZ j)). } have HdR : forall j, trace_store_seq t (enum 'I_M) s (d_ j) = vbool (trace_detected t j).
  { move=> j; exact: (trace_store_seq_enum_d t s (Hda j) (Hdy j) (Hdb j) (Hdy' j) (Hdd j) (HdX j) (HdZ j)). } have HyR : forall j, trace_store_seq t (enum 'I_M) s (y_ j) = choice_y (t j).
  { move=> j; exact: (trace_store_seq_enum_y t s (Hya j) (Hyb j) (Hyy j) (Hyy' j) (Hyd j) (HyX j) (HyZ j)). } have Hy'R : forall j, trace_store_seq t (enum 'I_M) s (y'_ j) = choice_y' (t j).
  { move=> j; exact: (trace_store_seq_enum_y' t s (Hy'a j) (Hy'y j) (Hy'b j) (Hy'y' j) (Hy'd j) (Hy'X j) (Hy'Z j)). } by rewrite (key_sample_deviation_event_trace_choices (t := t) (r := r) (i := i) (s := s) vsetK mu K Henum Htf HaR HbR HdR HyR Hy'R HaX HaZ HbX HbZ HdX HdZ HyP Hy'P HXAB HXAZA HXAZB HXAP HXAlam HXBZA HXBZB HXBP HXBlam HZAZB HZAP HZAlam HZBP HZBlam HZK HZXA HZXB HZZA HZZB HZP HZlam HKXA HyK HyXA HyXB Hy'K Hy'XA Hy'XB Hy'ZA). Qed.
Fact key_sample_deviation_event_enum_choices_sum (vsetK : forall X : {set 'I_M}, vset_of (vset X) = X) (mu : nat -> R) (r : seq 'I_M) (i :
  'I_M) (s : store) (w : round_trace -> V -> R) : enum 'I_M = rcons r i -> vbool true != vbool false -> (forall i j, j != i -> a_ i != a_ j)
  -> (forall i j, a_ i != y_ j) -> (forall i j, a_ i != b_ j) -> (forall i j, a_ i != y'_ j) -> (forall i j, a_ i != d_ j) -> (forall i, a_
  i != Xv) -> (forall i, a_ i != Zv) -> (forall i j, b_ i != a_ j) -> (forall i j, b_ i != y_ j) -> (forall i j, j != i -> b_ i != b_ j) ->
  (forall i j, b_ i != y'_ j) -> (forall i j, b_ i != d_ j) -> (forall i, b_ i != Xv) -> (forall i, b_ i != Zv) -> (forall i j, d_ i != a_
  j) -> (forall i j, d_ i != y_ j) -> (forall i j, d_ i != b_ j) -> (forall i j, d_ i != y'_ j) -> (forall i j, j != i -> d_ i != d_ j) ->
  (forall i, d_ i != Xv) -> (forall i, d_ i != Zv) -> (forall i j, j != i -> y_ i != a_ j) -> (forall i j, y_ i != b_ j) -> (forall i j, j
  != i -> y_ i != y_ j) -> (forall i j, y_ i != y'_ j) -> (forall i j, y_ i != d_ j) -> (forall i, y_ i != Xv) -> (forall i, y_ i != Zv) ->
  (forall i j, y'_ i != a_ j) -> (forall i j, y'_ i != y_ j) -> (forall i j, y'_ i != b_ j) -> (forall i j, j != i -> y'_ i != y'_ j) ->
  (forall i j, y'_ i != d_ j) -> (forall i, y'_ i != Xv) -> (forall i, y'_ i != Zv) -> (forall j, y_ j != Pvar) -> (forall j, y'_ j != Pvar)
  -> pewall (Zv != Kv -> Zv != XA -> Zv != XB -> Zv != ZA -> Zv != ZB -> Zv != Pvar -> Zv != lamv -> Kv != XA -> (forall j, y_ j != Kv) ->
  (forall j, y_ j != XA) -> (forall j, y_ j != XB) -> (forall j, y'_ j != Kv) -> (forall j, y'_ j != XA) -> (forall j, y'_ j != XB) ->
  (forall j, y'_ j != ZA) -> \sum_(t : round_trace) \sum_K ((K \in key_sample_deviation_event mu t (announce_store (trace_store_seq t (enum
  'I_M) s)))%:R) * w t K = \sum_(t : round_trace) \sum_K (if (err_count (bits_on (vset_of K) (fun j => choice_y (t j))) (bits_on (vset_of K)
  (fun j => choice_y' (t j))))%:R / n%:R >= (err_count (test_bits_on (trace_test_set t) (fun j => choice_y (t j))) (test_bits_on
  (trace_test_set t) (fun j => choice_y' (t j))))%:R / (#|trace_test_set t|)%:R + mu #|trace_test_set t| then 1 else 0) * w t K).
Proof.
  move=> Henum Htf Haa Hay Hab Hay' Had HaX HaZ Hba Hby Hbb Hby' Hbd HbX HbZ Hda Hdy Hdb Hdy' Hdd HdX HdZ Hya Hyb Hyy Hyy' Hyd HyX HyZ Hy'a Hy'y Hy'b Hy'y' Hy'd Hy'X Hy'Z HyP Hy'P HXAB HXAZA HXAZB HXAP HXAlam HXBZA HXBZB HXBP HXBlam HZAZB HZAP HZAlam HZBP HZBlam HZK HZXA HZXB HZZA HZZB HZP HZlam HKXA HyK HyXA HyXB Hy'K Hy'XA Hy'XB Hy'ZA. apply: eq_bigr => t _; apply: eq_bigr => K _. rewrite (key_sample_deviation_event_enum_choices vsetK mu t (r := r) (i := i) s K Henum Htf Haa Hay Hab Hay' Had HaX HaZ Hba Hby Hbb Hby' Hbd HbX HbZ Hda Hdy Hdb Hdy' Hdd HdX HdZ Hya Hyb Hyy Hyy' Hyd HyX HyZ Hy'a Hy'y Hy'b Hy'y' Hy'd Hy'X Hy'Z HyP Hy'P HXAB HXAZA HXAZB HXAP HXAlam HXBZA HXBZB HXBP HXBlam HZAZB HZAP HZAlam HZBP HZBlam HZK HZXA HZXB HZZA HZZB HZP HZlam HKXA HyK HyXA HyXB Hy'K Hy'XA Hy'XB Hy'ZA). by case: (_ >= _); rewrite ?mul1r ?mul0r. Qed.
Lemma trace_samples_weight_enum (h : run_history) (s : store) : trace_samples_weight h.1 (enum 'I_M) s = round_samples_weight h s.
Proof. rewrite /trace_samples_weight /round_samples_weight. by apply: eq_big_seq => i _; rewrite /trace_sample_weight /round_sample_weight /hist_choice. Qed.
Lemma trace_unused_weight_enum (t : round_trace) : trace_unused_weight t (enum 'I_M) = 1.
Proof. rewrite /trace_unused_weight. apply: big1 => i Hi. by move: Hi; rewrite mem_enum. Qed.
Lemma trace_so_seq_enum (qA : {set L}) (EA : ADVq qA) (h : run_history) (rho : 'F[HL]_setT) : trace_so_seq EA h.1 (enum 'I_M) rho = hist_so
  EA h rho.
Proof. by rewrite /trace_so_seq /hist_so /trace_round_so /round_so /hist_choice /attack_transcript. Qed.
Lemma trace_final_branch_history (qA : {set L}) (EA : ADVq qA) (s : store) (h : run_history) (rho : 'F[HL]_setT) : trace_final_branch EA
  (enum 'I_M) h (start_store s) rho = history_branch EA s h rho.
Proof.
  rewrite /trace_final_branch /history_branch /final_store /hist_wt trace_store_seq_enum; set s0 := start_store s. set s1 := rounds_store h s0; set s2 := announce_store s1; set s3 := paramest_store h s2. case Hpe: (pe_failed s3).
  - rewrite /trace_pe_abort_branch trace_store_seq_enum -/s0 -/s1 -/s2 -/s3; congr (cq_single _ _). by rewrite trace_samples_weight_enum trace_unused_weight_enum trace_so_seq_enum; rewrite mulr1 !mulrA.
  - set s4 := errcorr_store h s3. case Hverify: (s4 tAv != s4 tBv).
    + rewrite /trace_verify_abort_branch trace_store_seq_enum -/s0 -/s1 -/s2 -/s3 -/s4; congr (cq_single _ _). by rewrite trace_samples_weight_enum trace_unused_weight_enum trace_so_seq_enum; rewrite mulr1 !mulrA.
    + rewrite /trace_privamp_branch trace_store_seq_enum -/s0 -/s1 -/s2 -/s3 -/s4; congr (cq_single _ _). by rewrite trace_samples_weight_enum trace_unused_weight_enum trace_so_seq_enum; rewrite mulr1 !mulrA. Qed.
Definition history_sum (qA : {set L}) (EA : ADVq qA) (s : store) (rho : 'F[HL]_setT) : CQs := \sum_(h : run_history) history_branch EA s h
  rho.
Definition preverify_cmd : @qkd_cmd R L HL Cv V := start_cmd ;; rounds_cmd_seq (enum 'I_M) ;; ANNs ;; PEs ;; IF PFs THEN ABs ELSE ECs.
Definition finish_after_preverify_cmd : @qkd_cmd R L HL Cv V := IF (fun s : store => s abortv != vbool false) THEN Cskip ELSE (IF (fun s :
  store => s tAv != s tBv) THEN ABs ELSE PAs).
Fact denote_finish_trace_preverify_enum_bot (qA : {set L}) (EA : ADVq qA) (t : round_trace) (K g : V) (s : store) (rho : 'F[HL]_setT) :
  vbool true != vbool false -> abortv != Sv -> abortv != Shv -> (forall i, abortv != a_ i) -> (forall i, abortv != y_ i) -> (forall i,
  abortv != b_ i) -> (forall i, abortv != y'_ i) -> (forall i, abortv != d_ i) -> abortv != Xv -> abortv != Zv -> abortv != Pvar -> abortv
  != Kv -> abortv != XA -> abortv != XB -> abortv != ZA -> abortv != ZB -> abortv != lamv -> abortv != pECv -> abortv != Xhatv -> abortv !=
  gv -> abortv != tAv -> abortv != tBv -> DNg qA EA finish_after_preverify_cmd (trace_preverify_branch EA (enum 'I_M) (t, ((K, g), bot))
  (start_store s) rho) = \sum_f trace_final_branch EA (enum 'I_M) (t, ((K, g), f)) (start_store s) rho.
Proof.
  move=> Htf HAS HAH Ha Hy Hb Hy' Hd HX HZ HP HK HXA HXB HZA HZB Hlam HpEC HXhat Hg HtA HtB; set h0 := (t, ((K, g), bot)). set s0 := start_store s; set s_ann := announce_store (trace_store_seq t (enum 'I_M) s0); set s_pe := paramest_store h0 s_ann. rewrite /trace_preverify_branch /= -/s_ann -/h0 -/s_pe. case Hpe: (pe_failed s_pe).
  - rewrite /finish_after_preverify_cmd /trace_pe_abort_branch. rewrite /= -/s_ann -/h0 -/s_pe. set q := ((trace_samples_weight t (enum 'I_M) s0 * trace_unused_weight t (enum 'I_M) * key_sample_mass s_ann K * seed_unused g * seed_unused bot)%:C *: trace_so_seq EA t (enum 'I_M) rho). change (DSg qA EA (IF (fun u : store => u abortv != vbool false) THEN Cskip ELSE (IF (fun u : store => u tAv != u tBv) THEN ABs ELSE PAs)) (abort_store s_pe) q = \sum_f trace_final_branch EA (enum 'I_M) (t, ((K, g), f)) s0 rho). rewrite denote_if_single abort_store_not_pass // denote_skip_single (bigD1 bot) //=; rewrite [X in _ + X]big1 ?addr0; last first. move=> f Hf; rewrite /trace_final_branch /= -/s_ann. rewrite (paramest_store_future_irrel t K g f g bot s_ann) -/h0 -/s_pe Hpe. by rewrite /trace_pe_abort_branch /seed_unused /hist_f /= (negbTE Hf); rewrite ?mulr0 ?mul0r rmorph0 scale0r cq_single_zero. by rewrite /trace_final_branch /= -/s_ann -/h0 -/s_pe Hpe /trace_pe_abort_branch /h0 /=; rewrite /q /seed_unused /hist_f /= eqxx !mulr1.
  - have Habort : errcorr_store h0 s_pe abortv = vbool false.
    { rewrite (errcorr_store_other (x := abortv) h0 s_pe) //; rewrite /s_pe (paramest_store_other (x := abortv) h0 s_ann) //. rewrite /s_ann (announce_store_other _ HP) (@trace_store_seq_enum (t, ((K, g), bot)) s0). by rewrite (rounds_store_other (x := abortv) h0 s0) //; rewrite /s0 start_store_abort. } rewrite /finish_after_preverify_cmd /trace_errcorr_branch /= -/s_ann -/h0 -/s_pe; set s_ec := errcorr_store h0 s_pe. set q := ((trace_samples_weight t (enum 'I_M) s0 * trace_unused_weight t (enum 'I_M) * key_sample_mass s_ann K * unif_vseed (errcorr_seed_store s_pe) g * seed_unused bot)%:C *: trace_so_seq EA t (enum 'I_M) rho). change (DSg qA EA (IF (fun u : store => u abortv != vbool false) THEN Cskip ELSE (IF (fun u : store => u tAv != u tBv) THEN ABs ELSE PAs)) s_ec q = \sum_f trace_final_branch EA (enum 'I_M) (t, ((K, g), f)) s0 rho). rewrite denote_if_single /s_ec in Habort *; rewrite Habort eqxx -/h0 -/s_ann -/s_pe. change (DNg qA EA (IF (fun u : store => u tAv != u tBv) THEN ABs ELSE PAs) (trace_errcorr_branch EA (enum 'I_M) h0 s0 rho) = \sum_f trace_final_branch EA (enum 'I_M) (t, ((K, g), f)) s0 rho). have Hpass : ~~ pe_failed (paramest_store (t, ((K, g), bot)) (announce_store (trace_store_seq t (enum 'I_M) s0))). by rewrite -/h0 -/s_ann -/s_pe Hpe. by rewrite (@denote_verify_privamp_trace_errcorr_branch qA EA (enum 'I_M) t K g s0 rho Hpass). Qed.
Definition preverify_eval (qA : {set L}) (EA : ADVq qA) (xi : CQs) : CQs := DNg qA EA preverify_cmd xi.
Lemma preverify_eval_decomp (qA : {set L}) (EA : ADVq qA) (xi : CQs) : (forall i, a_ i != y_ i) -> pubwall (Pvar != abortv -> preverify_eval
  EA xi = \sum_s \sum_(h : run_history) trace_preverify_branch EA (enum 'I_M) h (start_store s) (xi s)).
Proof.
have denote_preverify_cmd_single : forall (qA : {set L}) (EA : ADVq qA) (s : store) (rho : 'F[HL]_setT), (forall i, a_ i != y_ i) -> (forall i, Pvar != a_ i) -> (forall i, Pvar != y_ i) -> (forall i, Pvar != b_ i) -> (forall i, Pvar != y'_ i) -> (forall i, Pvar != d_ i) -> Pvar != Xv -> Pvar != Zv -> Pvar != abortv -> DSg qA EA preverify_cmd s rho = \sum_(h : run_history) trace_preverify_branch EA (enum 'I_M) h (start_store s) rho.
{ clear xi EA qA; move=> qA EA s rho. have denote_preverify_paramest_full_sum : forall (qA : {set L}) (EA : ADVq qA) (r : seq 'I_M) (s : store) (rho : 'F[HL]_setT), DNg qA EA (IF PFs THEN ABs ELSE ECs) (\sum_(h : run_history) trace_paramest_branch EA r h s rho) = \sum_(h : run_history) trace_preverify_branch EA r h s rho.
{ clear rho s EA qA; move=> qA EA r s rho. have denote_preverify_paramest_sample_sum : forall (qA : {set L}) (EA : ADVq qA) (r : seq 'I_M) (s : store) (rho : 'F[HL]_setT), DNg qA EA (IF PFs THEN ABs ELSE ECs) (\sum_(t : round_trace) \sum_K trace_paramest_sample_branch EA r t K bot bot s rho) = \sum_(h : run_history) trace_preverify_branch EA r h s rho.
{ clear rho s r EA qA; move=> qA EA r s rho. have denote_preverify_trace_paramest_sample_branch : forall (qA : {set L}) (EA : ADVq qA) (r : seq 'I_M) (t : round_trace) (K : V) (s : store) (rho : 'F[HL]_setT), DNg qA EA (IF PFs THEN ABs ELSE ECs) (trace_paramest_sample_branch EA r t K bot bot s rho) = \sum_g trace_preverify_branch EA r (t, ((K, g), bot)) s rho.
{ clear rho s r EA qA; move=> qA EA r t K s rho. rewrite /trace_paramest_sample_branch. set h0 := (t, ((K, bot), bot)); set s_ann := announce_store (trace_store_seq t r s); set s_pe := paramest_store h0 s_ann. set q := ((trace_samples_weight t r s * trace_unused_weight t r * key_sample_mass s_ann K)%:C *: trace_so_seq EA t r rho). change (DSg qA EA (IF PFs THEN ABs ELSE ECs) s_pe q = \sum_g trace_preverify_branch EA r (t, ((K, g), bot)) s rho). rewrite denote_if_single pe_fail_replayE -/s_pe. case Hpe: (pe_failed s_pe).
  - rewrite denote_abort_single. rewrite (bigD1 bot) //=; rewrite [X in _ + X]big1 ?addr0; last first. move=> g Hg; rewrite /trace_preverify_branch /= -/s_ann. rewrite (paramest_store_future_irrel t K g bot bot bot s_ann) -/h0 -/s_pe Hpe. by rewrite /trace_pe_abort_branch /seed_unused /hist_g /= (negbTE Hg); rewrite ?mulr0 ?mul0r rmorph0 scale0r cq_single_zero. rewrite /trace_preverify_branch /= -/s_ann -/h0 -/s_pe Hpe; rewrite /trace_pe_abort_branch /q /seed_unused /hist_g /hist_f /=. by rewrite !eqxx !mulr1.
  - change (DNg qA EA (ECs) (trace_paramest_sample_branch EA r t K bot bot s rho) = \sum_g trace_preverify_branch EA r (t, ((K, g), bot)) s rho). rewrite denote_errcorr_trace_paramest_sample_branch; apply: eq_bigr => g _. rewrite /trace_preverify_branch /= -/s_ann. rewrite (paramest_store_future_irrel t K g bot bot bot s_ann) -/h0 -/s_pe Hpe. by rewrite /trace_errcorr_branch. } rewrite denote_sum. transitivity (\sum_(t : round_trace) \sum_K \sum_g trace_preverify_branch EA r (t, ((K, g), bot)) s rho).
  { apply: eq_bigr => t _. by rewrite denote_sum; apply: eq_bigr => K _; rewrite denote_preverify_trace_paramest_sample_branch. } exact: trace_preverify_bot_full_sum. } rewrite -(@trace_paramest_full_sum qA EA r s rho). exact: denote_preverify_paramest_sample_sum. } move=> Hay HPa HPy HPb HPy' HPd HPX HPZ HPabort; rewrite /preverify_cmd /denote_singleton !denote_seq_cmd. change (DNg qA EA (IF PFs THEN ABs ELSE ECs) (DNg qA EA (PEs) (DNg qA EA (ANNs) (DNg qA EA (rounds_cmd_seq (enum 'I_M)) (DSg qA EA start_cmd s rho)))) = \sum_(h : run_history) trace_preverify_branch EA (enum 'I_M) h (start_store s) rho). by rewrite (@denote_start_rounds_announce_paramest_program_denote_sum qA EA (enum 'I_M) s rho (enum_uniq 'I_M) _ _ _ _ _ _ HPX HPZ HPabort); [exact: denote_preverify_paramest_full_sum | move=> i _; exact: Hay | move=> i _; exact: HPa | move=> i _; exact: HPy | move=> i _; exact: HPb | move=> i _; exact: HPy' | move=> i _; exact: HPd]. } move=> Hay HPa HPy HPb HPy' HPd HPX HPZ HPabort; rewrite /preverify_eval denote_singleton_decomp; apply: eq_bigr => s _. exact: denote_preverify_cmd_single. Qed.
Definition corr_prob_event (key_count : nat) (key_of : V -> option 'I_key_count) (x x' : 'I_key_count) (s : store) : bool := (s abortv ==
  vbool false) && (key_of (s XA) == Some x) && (key_of (s Xhatv) == Some x').
Fact corr_prob_event_errcorr_storeE (key_count : nat) (key_of : V -> option 'I_key_count) (h : run_history) (s : store) (x x' :
  'I_key_count) : ecwall (xawall (xhwall (corr_prob_event key_of x x' (errcorr_store h s) = (s abortv == vbool false) && (key_of (s XA) ==
  Some x) && (key_of (ir_dec (ir_pub leakEC (s XA) (s XB)) (s XB)) == Some x')))).
Proof.
  move=> HAp HAXhat HAg HAtA HAtB HAP HXAp HXAXhat HXAg HXAtA HXAtB HXAP HXBp HXhatg HXhattA HXhattB HXhatP; rewrite /corr_prob_event.
    rewrite (errcorr_store_other (x := abortv) h s) //; rewrite (errcorr_store_XA h s HXAp HXAXhat HXAg HXAtA HXAtB HXAP). by rewrite (errcorr_store_Xhatv h s HXBp HXhatg HXhattA HXhattB HXhatP). Qed.
Definition corr_key_pair (key_count : nat) (key_of : V -> option 'I_key_count) (s : store) : option ('I_key_count * 'I_key_count) := if s
  abortv == vbool false then match key_of (s XA), key_of (s Xhatv) with | Some x, Some x' => Some (x, x') | _, _ => None end else None.
Definition run_event_prob (ev : store -> bool) (xi : CQs) : R := \sum_(s | ev s) @complex.Re R (\Tr (xi s)).
Lemma run_event_prob_single (ev : store -> bool) (s : store) (rho : 'F[HL]_setT) : run_event_prob ev (cq_single s rho) = (ev s)%:R *
  @complex.Re R (\Tr rho).
Proof. rewrite /run_event_prob big_mkcond (bigD1 s) //= /cq_single ffunE eqxx; rewrite [X in _ + X]big1 ?addr0. - by case: (ev s); rewrite ?mul1r ?mul0r. - move=> t Hts. by rewrite ffunE; case: (ev t); rewrite ?(negbTE Hts) ?linear0 ?mulr0. Qed.
Lemma run_event_prob_sum (I : finType) (ev : store -> bool) (F : I -> CQs) : run_event_prob ev (\sum_i F i) = \sum_i run_event_prob ev (F
  i).
Proof. rewrite /run_event_prob exchange_big /=; apply: eq_bigr => s _. rewrite sum_ffunE -[X in _ = X]raddf_sum. have Htr : \Tr (\sum_i F i s) = \sum_i \Tr (F i s) by rewrite linear_sum. by rewrite -Htr /lftrace. Qed.
Lemma trace_weight_mul (a b : R) (rho : 'F[HL]_setT) : @complex.Re R (\Tr (((a * b)%:C) *: rho)) = b * @complex.Re R (\Tr (a%:C *: rho)).
Proof. have HRe_realM : forall (r : R) (z : @hermitian.C R), @complex.Re R (r%:C * z) = r * @complex.Re R z. { move=> r z. by case: z => zr zi /=; rewrite mul0r subr0. } by rewrite !linearZ /= !HRe_realM mulrA [a * b]mulrC -mulrA. Qed.
Fact finite_pair_sum_exchange3 (A B J : finType) (key_count : nat) (F : A -> B -> J -> 'I_key_count -> 'I_key_count -> R) (G : A -> B -> J
  -> R) (H : 'I_key_count -> 'I_key_count -> R) : \sum_a \sum_b \sum_j ((\sum_x \sum_(x' | x != x') F a b j x x' * H x x') * G a b j) =
  \sum_x \sum_(x' | x != x') ((\sum_a \sum_b \sum_j F a b j x x' * G a b j) * H x x').
Proof.
  transitivity (\sum_a \sum_b \sum_j \sum_x \sum_(x' | x != x') (F a b j x x' * G a b j) * H x x').
  { apply: eq_bigr => a _; apply: eq_bigr => b _; apply: eq_bigr => j _. rewrite mulr_suml; apply: eq_bigr => x _. rewrite mulr_suml; apply: eq_bigr => x' _. by rewrite -mulrA [H x x' * G a b j]mulrC mulrA. } transitivity (\sum_x \sum_(x' | x != x') \sum_a \sum_b \sum_j (F a b j x x' * G a b j) * H x x').
  { under eq_bigr => a _ do under eq_bigr => b _ do rewrite exchange_big /=. under eq_bigr => a _ do rewrite exchange_big /=. rewrite exchange_big /=; apply: eq_bigr => x _. under eq_bigr => a _ do under eq_bigr => b _ do rewrite exchange_big /=. under eq_bigr => a _ do rewrite exchange_big /=. by rewrite exchange_big /=. } apply: eq_bigr => x _; apply: eq_bigr => x' _. under eq_bigr => a _ do under eq_bigr => b _ do rewrite -mulr_suml. under eq_bigr => a _ do rewrite -mulr_suml. by rewrite -mulr_suml. Qed.
Lemma run_event_prob_history_branch (qA : {set L}) (EA : ADVq qA) (ev : store -> bool) (s : store) (h : run_history) (rho : 'F[HL]_setT) :
  run_event_prob ev (history_branch EA s h rho) = (ev (final_store h s))%:R * @complex.Re R (\Tr ((hist_wt h s)%:C *: hist_so EA h rho)).
Proof. by rewrite /history_branch run_event_prob_single. Qed.
Fact run_event_prob_verify_accept_trace_preverify_branch_readout (qA : {set L}) (EA : ADVq qA) (r : seq 'I_M) (h : run_history) (s : store)
  (rho : 'F[HL]_setT) : vbool true != vbool false -> abortv != Sv -> abortv != Shv -> ecwall (tagwall (xawall (xhwall (run_event_prob
  verify_accept_raw_mismatch (trace_preverify_branch EA r h s rho) = let s_ann := announce_store (trace_store_seq h.1 r s) in let s_pe :=
  paramest_store h s_ann in if pe_failed s_pe then 0 else (((s_pe abortv == vbool false) && (verify_hash (hist_g h) (s_pe XA) == verify_hash
  (hist_g h) (ir_dec (ir_pub leakEC (s_pe XA) (s_pe XB)) (s_pe XB))) && (s_pe XA != ir_dec (ir_pub leakEC (s_pe XA) (s_pe XB)) (s_pe
  XB)))%:R) * @complex.Re R (\Tr (((trace_samples_weight h.1 r s * trace_unused_weight h.1 r * key_sample_mass s_ann (hist_K h) * unif_vseed
  (errcorr_seed_store s_pe) (hist_g h) * seed_unused (hist_f h))%:C *: trace_so_seq EA h.1 r rho))))))).
Proof.
  move=> Htf HAS HAH HAp HAXhat HAg HAtA HAtB HAP HgtA HgtB HtAtB HtAP HtBP HXAp HXAXhat HXAg HXAtA HXAtB HXAP HXBp HXhatg HXhattA HXhattB HXhatP. rewrite /trace_preverify_branch; set s_ann := announce_store (trace_store_seq h.1 r s); set s_pe := paramest_store h s_ann. case Hpe: (pe_failed s_pe).
  - rewrite /trace_pe_abort_branch -/s_ann -/s_pe run_event_prob_single. have Habort : (abort_store s_pe abortv == vbool false) = false.
    { rewrite abort_store_abort //. by rewrite (negbTE Htf). } by rewrite /verify_accept_raw_mismatch Habort /= mul0r.
  - rewrite /trace_errcorr_branch -/s_ann -/s_pe run_event_prob_single. by rewrite (verify_accept_raw_mismatch_errcorr_storeE h s_pe HAp HAXhat HAg HAtA HAtB HAP HgtA HgtB HtAtB HtAP HtBP HXAp HXAXhat HXAg HXAtA HXAtB HXAP HXBp HXhatg HXhattA HXhattB HXhatP). Qed.
Fact run_event_prob_corr_event_trace_preverify_branch_readout (key_count : nat) (key_of : V -> option 'I_key_count) (qA : {set L}) (EA :
  ADVq qA) (r : seq 'I_M) (h : run_history) (s : store) (rho : 'F[HL]_setT) (x x' : 'I_key_count) : vbool true != vbool false -> abortv !=
  Sv -> abortv != Shv -> ecwall (xawall (xhwall (run_event_prob (corr_prob_event key_of x x') (trace_preverify_branch EA r h s rho) = let
  s_ann := announce_store (trace_store_seq h.1 r s) in let s_pe := paramest_store h s_ann in if pe_failed s_pe then 0 else (((s_pe abortv ==
  vbool false) && (key_of (s_pe XA) == Some x) && (key_of (ir_dec (ir_pub leakEC (s_pe XA) (s_pe XB)) (s_pe XB)) == Some x'))%:R) *
  @complex.Re R (\Tr (((trace_samples_weight h.1 r s * trace_unused_weight h.1 r * key_sample_mass s_ann (hist_K h) * unif_vseed
  (errcorr_seed_store s_pe) (hist_g h) * seed_unused (hist_f h))%:C *: trace_so_seq EA h.1 r rho)))))).
Proof.
  move=> Htf HAS HAH HAp HAXhat HAg HAtA HAtB HAP HXAp HXAXhat HXAg HXAtA HXAtB HXAP HXBp HXhatg HXhattA HXhattB HXhatP. rewrite /trace_preverify_branch; set s_ann := announce_store (trace_store_seq h.1 r s); set s_pe := paramest_store h s_ann. case Hpe: (pe_failed s_pe).
  - rewrite /trace_pe_abort_branch -/s_ann -/s_pe run_event_prob_single. have Habort : (abort_store s_pe abortv == vbool false) = false. {  exact: abort_store_not_pass. } by rewrite /corr_prob_event Habort /= mul0r.
  - rewrite /trace_errcorr_branch -/s_ann -/s_pe run_event_prob_single. by rewrite (corr_prob_event_errcorr_storeE key_of h s_pe x x' HAp HAXhat HAg HAtA HAtB HAP HXAp HXAXhat HXAg HXAtA HXAtB HXAP HXBp HXhatg HXhattA HXhattB HXhatP). Qed.
Definition run_abort_prob (xi : CQs) : R := run_event_prob (fun s => s abortv == vbool true) xi.
Definition run_pass_prob (xi : CQs) : R := run_event_prob (fun s => s abortv == vbool false) xi.
Definition run_output_mismatch_prob (xi : CQs) : R := run_event_prob output_mismatch_event xi.
Definition corr_prob_prog (key_count : nat) (key_of : V -> option 'I_key_count) (qA : {set L}) (EA : ADVq qA) (xi : CQs) (x x' :
  'I_key_count) : R := \sum_s (corr_prob_event key_of x x' s)%:R * @complex.Re R (\Tr (preverify_eval EA xi s)).
Lemma preverify_cmd_wf (qA : {set L}) : (forall i, cmd_wf qA (RNDs i)) -> cmd_wf qA (PEs) -> cmd_wf qA (ECs) -> cmd_wf qA preverify_cmd.
Proof. move=> Hround Hpe Hec; rewrite /preverify_cmd; apply: cmd_wf_seq_cmd; first by []. apply: cmd_wf_seq_cmd. - by rewrite rounds_cmd_seq_enum; apply: cmd_wf_for_cmd. apply: cmd_wf_seq_cmd; first by []. apply: cmd_wf_seq_cmd; first exact: Hpe. split; first by []. exact: Hec. Qed.
Fact corr_prob_prog_nonneg (key_count : nat) (key_of : V -> option 'I_key_count) (qA : {set L}) (EA : ADVq qA) (xi : CQs) : (forall i,
  cmd_wf qA (RNDs i)) -> cmd_wf qA (PEs) -> cmd_wf qA (ECs) -> (forall s, xi s \is psdlf) -> forall x x', 0 <= corr_prob_prog key_of EA xi x
  x'.
Proof.
  move=> Hround Hpe Hec Hxi x x'; rewrite /corr_prob_prog; apply: sumr_ge0 => s _. apply: mulr_ge0.
  - by case: (corr_prob_event key_of x x' s); rewrite ?ler01 ?lexx. have Hwf := preverify_cmd_wf Hround Hpe Hec. have Hpsd := @denote_psd R L HL Cv V qA Pvar EA preverify_cmd xi Hwf Hxi s. by have := psdlf_trlf Hpsd; rewrite lecE /= => /andP[]. Qed.
Fact corr_key_pair_count_le1 (key_count : nat) (key_of : V -> option 'I_key_count) (s : store) : \sum_p (corr_key_pair key_of s == Some
  p)%:R <= (1 : R).
Proof. case Hpair: (corr_key_pair key_of s) => [p0|]. - rewrite (bigD1 p0) //= eqxx. rewrite [X in _ + X]big1; first by rewrite addr0 lexx. move=> p Hp; case Hsp: (Some p0 == Some p) => //. by move/eqP: Hsp => [] Hp0p; move: Hp; rewrite -Hp0p eqxx. - rewrite big1 // => p _. Qed.
Fact corr_prob_prog_mismatch_mass_le1 (key_count : nat) (key_of : V -> option 'I_key_count) (qA : {set L}) (EA : ADVq qA) (xi : CQs) :
  (forall i, cmd_wf qA (RNDs i)) -> cmd_wf qA (PEs) -> cmd_wf qA (ECs) -> cq_wf xi -> \sum_x \sum_(x' | x != x') corr_prob_prog key_of EA xi
  x x' <= 1.
Proof.
have corr_prob_event_count_le1 : forall (key_count : nat) (key_of : V -> option 'I_key_count) (s : store), \sum_x \sum_(x' | x != x') (corr_prob_event key_of x x' s)%:R <= (1 : R).
{ clear xi EA qA key_of key_count; move=> key_count key_of s. have corr_prob_event_pairE : forall (key_count : nat) (key_of : V -> option 'I_key_count) (s : store) (x x' : 'I_key_count), corr_prob_event key_of x x' s = (corr_key_pair key_of s == Some (x, x')).
{ clear s key_of key_count; move=> key_count key_of s x x'. rewrite /corr_prob_event /corr_key_pair. case: (s abortv == vbool false) => //=.
  case: (key_of (s XA)) => [xa|] //=. case: (key_of (s Xhatv)) => [xb|] /=.
  - by case: (xa == x); case: (xb == x').
  - have Hnone_key : (None : option 'I_key_count) != Some x' by []. have Hnone_pair : (None : option ('I_key_count * 'I_key_count)) != Some (x, x') by []. by rewrite (negbTE Hnone_key) (negbTE Hnone_pair) andbF. } have corr_key_pair_mismatch_count_le1 : forall (key_count : nat) (key_of : V -> option 'I_key_count) (s : store), \sum_(p : 'I_key_count * 'I_key_count | p.1 != p.2) (corr_key_pair key_of s == Some p)%:R <= (1 : R).
{ clear s key_of key_count; move=> key_count key_of s. have sum_filter_le : forall (T : finType) (P : pred T) (F : T -> R), (forall i, 0 <= F i) -> \sum_(i | P i) F i <= \sum_i F i.
{ clear s key_of key_count; move=> T P F. move=> HF; rewrite [X in _ <= X](bigID P) /=. by rewrite -[leLHS]addr0 lerD2l; exact: sumr_ge0. } apply: (le_trans _ (corr_key_pair_count_le1 key_of s)); apply: sum_filter_le => p. by case: (corr_key_pair key_of s == Some p); rewrite ?ler01 ?lexx. } rewrite (eq_bigr (fun x : 'I_key_count => \sum_(x' | x != x') (corr_key_pair key_of s == Some (x, x'))%:R)).
  - rewrite pair_big_dep /=. rewrite (eq_bigl (fun p : 'I_key_count * 'I_key_count => p.1 != p.2)).
    + rewrite (eq_bigr (fun p : 'I_key_count * 'I_key_count => (corr_key_pair key_of s == Some p)%:R)). * exact: corr_key_pair_mismatch_count_le1. * by move=> [x x'] _.
    + by move=> [x x'].
  - by move=> x _; apply: eq_bigr => x' _; rewrite corr_prob_event_pairE. } move=> Hround Hpe Hec [Hxi_psd Hxi_mass]; set xi_pre := preverify_eval EA xi. have Hwf := preverify_cmd_wf Hround Hpe Hec. have Hpre_psd : forall s, xi_pre s \is psdlf.
  { move=> s. exact: (@denote_psd R L HL Cv V qA Pvar EA preverify_cmd xi Hwf Hxi_psd s). } have Hpre_mass : cq_mass xi_pre = 1.
  { by rewrite /xi_pre /preverify_eval (@denote_mass R L HL Cv V qA Pvar EA preverify_cmd xi Hwf Hxi_psd) Hxi_mass. } rewrite /corr_prob_prog. under eq_bigr => x _ do rewrite exchange_big /=. rewrite exchange_big /=. under eq_bigr => s _ do (under eq_bigr => x _ do rewrite -mulr_suml; rewrite -mulr_suml). apply: (le_trans _ _).
  - apply: ler_sum => s _; apply: ler_pM.
    + apply: sumr_ge0 => x _; apply: sumr_ge0 => x' _. by case: (corr_prob_event key_of x x' s); rewrite ?ler01 ?lexx.
    + by have := psdlf_trlf (Hpre_psd s); rewrite lecE /= => /andP[].
    + exact: corr_prob_event_count_le1.
    + exact: lexx. rewrite (eq_bigr (fun s : store => @complex.Re R (\Tr (preverify_eval EA xi s)))).
  - by rewrite -Hpre_mass /cq_mass /xi_pre.
  - by move=> s _; rewrite mul1r. Qed.
Lemma run_event_prob_nonneg (ev : store -> bool) (xi : CQs) : (forall s, xi s \is psdlf) -> 0 <= run_event_prob ev xi.
Proof. move=> Hpsd; rewrite /run_event_prob; apply: sumr_ge0 => s _. by have := psdlf_trlf (Hpsd s); rewrite lecE /= => /andP[]. Qed.
Fact run_event_prob_le_mass (ev : store -> bool) (xi : CQs) : (forall s, xi s \is psdlf) -> run_event_prob ev xi <= cq_mass xi.
Proof. move=> Hpsd; rewrite /run_event_prob /cq_mass; rewrite [X in _ <= X](bigID ev) /=; rewrite lerDl. apply: sumr_ge0 => s _. by have := psdlf_trlf (Hpsd s); rewrite lecE /= => /andP[]. Qed.
Fact privamp_single_mismatch_le_raw (qA : {set L}) (EA : ADVq qA) (s : store) (rho : 'F[HL]_setT) : XA != fv -> Xhatv != fv -> fv != Sv ->
  Xhatv != Sv -> Sv != Shv -> Sv != Pvar -> Shv != Pvar -> (forall s, (forall f, 0 <= unif_pseed s f) /\ \sum_f unif_pseed s f = 1) -> rho
  \is psdlf -> run_event_prob output_mismatch_event (DSg qA EA (PAs) s rho) <= ((s XA != s Xhatv)%:R : R) * @complex.Re R (\Tr rho).
Proof.
have privamp_store_same_raw_key : forall (h : run_history) (s : store), XA != fv -> Xhatv != fv -> fv != Sv -> Xhatv != Sv -> Sv != Shv -> Sv != Pvar -> Shv != Pvar -> s XA = s Xhatv -> privamp_store h s Sv = privamp_store h s Shv.
{ clear rho s EA qA; move=> h s. move=> HXAf HXhatf HfS HXhatS HSS HSP HShP Hraw; rewrite (privamp_store_Sv h s HSS HSP). rewrite (privamp_store_Shv h s HShP); set s1 := store_set s fv (hist_f h); set s2 := store_set s1 Sv (privacy_hash l (s1 fv) (s1 XA)). have Hs2f : s2 fv = s1 fv by rewrite /s2 store_set_other. have Hs2Xhat : s2 Xhatv = s1 Xhatv by rewrite /s2 store_set_other. rewrite Hs2f Hs2Xhat /s1; rewrite store_set_same !store_set_other //. by rewrite Hraw. } move=> HXAf HXhatf HfS HXhatS HSS HSP HShP Hseed Hrho; case Hraw: (s XA == s Xhatv).
  - move/eqP: Hraw => Hsame. rewrite mul0r; rewrite (@denote_privamp_single_sum qA EA round_trace_default bot bot s rho); rewrite run_event_prob_sum. rewrite big1 // => f _; rewrite run_event_prob_single. have Hkeys := @privamp_store_same_raw_key (round_trace_default, ((bot, bot), f)) s HXAf HXhatf HfS HXhatS HSS HSP HShP Hsame. by rewrite /output_mismatch_event Hkeys eqxx mul0r.
  - rewrite mul1r. have Hwf : @cmd_wf R L HL Cv V qA (PAs).
    { rewrite /PrivAmp; apply: cmd_wf_seq_cmd; first exact: Hseed. do 2 (apply: cmd_wf_seq_cmd; first by []). by []. } have Hpsd : forall t, DSg qA EA (PAs) s rho t \is psdlf.
    { move=> t. apply: (@denote_psd R L HL Cv V qA Pvar EA (PAs) (cq_single s rho) Hwf _ t). by move=> u; rewrite /cq_single ffunE; case: (u == s); [exact: Hrho | exact: is_psdlf]. } have Hmass : cq_mass (DSg qA EA (PAs) s rho) = @complex.Re R (\Tr rho).
    { rewrite /denote_singleton (@denote_mass R L HL Cv V qA Pvar EA (PAs) (cq_single s rho) Hwf _).
      - exact: cq_mass_single.
      - by move=> u; rewrite /cq_single ffunE; case: (u == s); [exact: Hrho | exact: is_psdlf]. } apply: (le_trans (run_event_prob_le_mass output_mismatch_event Hpsd)). by rewrite Hmass. Qed.
Fact finish_after_preverify_single_mismatch_le (qA : {set L}) (EA : ADVq qA) (s : store) (rho : 'F[HL]_setT) : vbool true != vbool false ->
  abortv != Sv -> abortv != Shv -> XA != fv -> Xhatv != fv -> fv != Sv -> Xhatv != Sv -> Sv != Shv -> Sv != Pvar -> Shv != Pvar -> (forall
  s, (forall f, 0 <= unif_pseed s f) /\ \sum_f unif_pseed s f = 1) -> rho \is psdlf -> run_event_prob output_mismatch_event (DSg qA EA
  finish_after_preverify_cmd s rho) <= run_event_prob verify_accept_raw_mismatch (cq_single s rho).
Proof.
  move=> Htf HAS HAH HXAf HXhatf HfS HXhatS HSS HSP HShP Hseed Hrho; rewrite /finish_after_preverify_cmd denote_if_single. case Habort: (s abortv != vbool false).
  - rewrite denote_skip_single !run_event_prob_single. have Hnot_pass : (s abortv == vbool false) = false by move: Habort; case: (s abortv == vbool false). by rewrite /output_mismatch_event /verify_accept_raw_mismatch Hnot_pass !andbF !mul0r.
  - have Hpass : s abortv == vbool false. by move: Habort; case: (s abortv == vbool false). rewrite denote_if_single. case Hverify: (s tAv != s tBv).
    + rewrite denote_abort_single !run_event_prob_single. have Htag : (s tAv == s tBv) = false by exact: negbTE Hverify. by rewrite /output_mismatch_event /verify_accept_raw_mismatch; rewrite (abort_store_not_pass s Htf HAS HAH) Htag !andbF !andFb !mul0r.
    + have Htag : s tAv == s tBv. by move: Hverify; case: (s tAv == s tBv). apply: (le_trans (privamp_single_mismatch_le_raw EA s HXAf HXhatf HfS HXhatS HSS HSP HShP Hseed Hrho)). by rewrite run_event_prob_single /verify_accept_raw_mismatch Hpass Htag !andbT. Qed.
Fact finish_after_preverify_mismatch_le_verify_accept (qA : {set L}) (EA : ADVq qA) (xi : CQs) : vbool true != vbool false -> abortv != Sv
  -> abortv != Shv -> XA != fv -> Xhatv != fv -> fv != Sv -> Xhatv != Sv -> Sv != Shv -> Sv != Pvar -> Shv != Pvar -> (forall s, (forall f,
  0 <= unif_pseed s f) /\ \sum_f unif_pseed s f = 1) -> (forall s, xi s \is psdlf) -> run_event_prob output_mismatch_event (DNg qA EA
  finish_after_preverify_cmd xi) <= run_event_prob verify_accept_raw_mismatch xi.
Proof.
  move=> Htf HAS HAH HXAf HXhatf HfS HXhatS HSS HSP HShP Hseed Hxi. rewrite denote_singleton_decomp run_event_prob_sum {2}(cq_state_decomp xi) run_event_prob_sum. apply: ler_sum => s _. exact: (finish_after_preverify_single_mismatch_le EA s Htf HAS HAH HXAf HXhatf HfS HXhatS HSS HSP HShP Hseed (Hxi s)). Qed.
Fact run_abort_pass_prob_partition (xi : CQs) : vbool true != vbool false -> (forall s, xi s != 0 -> (s abortv == vbool true) || (s abortv
  == vbool false)) -> run_abort_prob xi + run_pass_prob xi = cq_mass xi.
Proof.
  move=> Htf Hsupport; rewrite /run_abort_prob /run_pass_prob /run_event_prob /cq_mass. rewrite [X in X + _]big_mkcond [X in _ + X]big_mkcond -big_split /=; apply: eq_bigr => s _. case Htrue: (s abortv == vbool true). move/eqP: Htrue => ->; by rewrite (negbTE Htf) addr0. case Hfalse: (s abortv == vbool false). by rewrite add0r. have Hzero : xi s = 0.
  { case Hnz: (xi s == 0); first by move/eqP: Hnz. have Hnz' : xi s != 0 by rewrite Hnz. by move: (Hsupport s Hnz'); rewrite Htrue Hfalse. } by rewrite Hzero linear0 addr0. Qed.
Lemma denote_run_decomp (qA : {set L}) (EA : ADVq qA) (xi : CQs) : (forall i, a_ i != y_ i) -> pubwall (Pvar != abortv -> EVALs qA EA xi =
  \sum_s history_sum EA s (xi s)).
Proof.
have denote_bb84_program_single : forall (qA : {set L}) (EA : ADVq qA) (s : store) (rho : 'F[HL]_setT), (forall i, a_ i != y_ i) -> (forall i, Pvar != a_ i) -> (forall i, Pvar != y_ i) -> (forall i, Pvar != b_ i) -> (forall i, Pvar != y'_ i) -> (forall i, Pvar != d_ i) -> Pvar != Xv -> Pvar != Zv -> Pvar != abortv -> DSg qA EA (PROGs) s rho = history_sum EA s rho.
{ clear xi EA qA; move=> qA EA s rho. have denote_postprocess_paramest_full_sum : forall (qA : {set L}) (EA : ADVq qA) (r : seq 'I_M) (s : store) (rho : 'F[HL]_setT), DNg qA EA postprocess_cmd (\sum_(h : run_history) trace_paramest_branch EA r h s rho) = \sum_(h : run_history) trace_final_branch EA r h s rho.
{ clear rho s EA qA; move=> qA EA r s rho. have denote_postprocess_paramest_sample_sum : forall (qA : {set L}) (EA : ADVq qA) (r : seq 'I_M) (s : store) (rho : 'F[HL]_setT), DNg qA EA postprocess_cmd (\sum_(t : round_trace) \sum_K trace_paramest_sample_branch EA r t K bot bot s rho) = \sum_(h : run_history) trace_final_branch EA r h s rho.
{ clear rho s r EA qA; move=> qA EA r s rho. have denote_postprocess_trace_paramest_sample_branch : forall (qA : {set L}) (EA : ADVq qA) (r : seq 'I_M) (t : round_trace) (K : V) (s : store) (rho : 'F[HL]_setT), DNg qA EA postprocess_cmd (trace_paramest_sample_branch EA r t K bot bot s rho) = \sum_g \sum_f trace_final_branch EA r (t, ((K, g), f)) s rho.
{ clear rho s r EA qA; move=> qA EA r t K s rho. rewrite /trace_paramest_sample_branch /postprocess_cmd. set h0 := (t, ((K, bot), bot)); set s_ann := announce_store (trace_store_seq t r s); set s_pe := paramest_store h0 s_ann. set q := ((trace_samples_weight t r s * trace_unused_weight t r * key_sample_mass s_ann K)%:C *: trace_so_seq EA t r rho). change (DSg qA EA (IF PFs THEN ABs ELSE (ECs ;; IF (fun u : store => u tAv != u tBv) THEN ABs ELSE PAs)) s_pe q = \sum_g \sum_f trace_final_branch EA r (t, ((K, g), f)) s rho). rewrite denote_if_single pe_fail_replayE -/s_pe. case Hpe: (pe_failed s_pe).
  - rewrite denote_abort_single. rewrite (bigD1 bot) //=; rewrite [X in _ + X]big1 ?addr0; last first. move=> g Hg; apply: big1 => f _; rewrite /trace_final_branch /= -/s_ann. rewrite (paramest_store_future_irrel t K g f bot bot s_ann) -/h0 -/s_pe Hpe. by rewrite /trace_pe_abort_branch /seed_unused /hist_g /= (negbTE Hg); rewrite ?mulr0 ?mul0r rmorph0 scale0r cq_single_zero. rewrite (bigD1 bot) //= /trace_final_branch /= -/s_ann -/h0 -/s_pe Hpe; rewrite [X in _ + X]big1 ?addr0; last first. move=> f Hf; rewrite /trace_pe_abort_branch /seed_unused /hist_f /= (negbTE Hf). by rewrite ?mulr0 ?mul0r rmorph0 scale0r cq_single_zero. by rewrite /trace_pe_abort_branch /h0 /s_pe /q /=; rewrite /seed_unused /hist_g /hist_f /= !eqxx !mulr1.
  - change (DNg qA EA (ECs ;; IF (fun u : store => u tAv != u tBv) THEN ABs ELSE PAs) (trace_paramest_sample_branch EA r t K bot bot s rho) = \sum_g \sum_f trace_final_branch EA r (t, ((K, g), f)) s rho). rewrite denote_seq_cmd denote_errcorr_trace_paramest_sample_branch denote_sum; apply: eq_bigr => g _. rewrite denote_verify_privamp_trace_errcorr_branch //; rewrite (paramest_store_future_irrel t K g bot bot bot s_ann). by rewrite -/h0 -/s_pe Hpe. } rewrite denote_sum. transitivity (\sum_(t : round_trace) \sum_K \sum_g \sum_f trace_final_branch EA r (t, ((K, g), f)) s rho).
  { apply: eq_bigr => t _. by rewrite denote_sum; apply: eq_bigr => K _; rewrite denote_postprocess_trace_paramest_sample_branch. } exact: trace_final_full_sum. } rewrite -(@trace_paramest_full_sum qA EA r s rho). exact: denote_postprocess_paramest_sample_sum. } move=> Hay HPa HPy HPb HPy' HPd HPX HPZ HPabort; rewrite /bb84_program_scheme /denote_singleton -rounds_cmd_seq_enum !denote_seq_cmd.
    change (DNg qA EA postprocess_cmd (DNg qA EA (PEs) (DNg qA EA (ANNs) (DNg qA EA (rounds_cmd_seq (enum 'I_M)) (DSg qA EA start_cmd s rho)))) = history_sum EA s rho). by rewrite (@denote_start_rounds_announce_paramest_program_denote_sum qA EA (enum 'I_M) s rho (enum_uniq 'I_M) _ _ _ _ _ _ HPX HPZ HPabort); [rewrite denote_postprocess_paramest_full_sum /history_sum; apply: eq_bigr => h _; rewrite trace_final_branch_history | move=> i _; exact: Hay | move=> i _; exact: HPa | move=> i _; exact: HPy | move=> i _; exact: HPb | move=> i _; exact: HPy' | move=> i _; exact: HPd]. } move=> Hay HPa HPy HPb HPy' HPd HPX HPZ HPabort; rewrite /bb84_eval_scheme denote_singleton_decomp. by apply: eq_bigr => s _; rewrite denote_bb84_program_single. Qed.
Fact denote_finish_preverify_eval (qA : {set L}) (EA : ADVq qA) (xi : CQs) : vbool true != vbool false -> abortv != Sv -> abortv != Shv ->
  (forall i, a_ i != y_ i) -> pubwall (Pvar != abortv -> (forall i, abortv != a_ i) -> (forall i, abortv != y_ i) -> (forall i, abortv != b_
  i) -> (forall i, abortv != y'_ i) -> (forall i, abortv != d_ i) -> abortv != Xv -> abortv != Zv -> abortv != Pvar -> abortv != Kv ->
  abortv != XA -> abortv != XB -> abortv != ZA -> abortv != ZB -> abortv != lamv -> abortv != pECv -> abortv != Xhatv -> abortv != gv ->
  abortv != tAv -> abortv != tBv -> DNg qA EA finish_after_preverify_cmd (preverify_eval EA xi) = EVALs qA EA xi).
Proof.
  move=> Htf HAS HAH Hay HPa HPy HPb HPy' HPd HPX HPZ HPabort Ha Hy Hb Hy' Hd HX HZ HP HK HXA HXB HZA HZB Hlam HpEC HXhat Hg HtA HtB.
    rewrite (preverify_eval_decomp EA xi Hay HPa HPy HPb HPy' HPd HPX HPZ HPabort); rewrite denote_sum. rewrite (@denote_run_decomp qA EA xi Hay HPa HPy HPb HPy' HPd HPX HPZ HPabort); apply: eq_bigr => s _. rewrite /history_sum; rewrite -(@trace_preverify_bot_full_sum qA EA (enum 'I_M) (start_store s) (xi s)); rewrite denote_sum. transitivity (\sum_(t : round_trace) \sum_K \sum_g \sum_f trace_final_branch EA (enum 'I_M) (t, ((K, g), f)) (start_store s) (xi s)).
  { apply: eq_bigr => t _. rewrite denote_sum; apply: eq_bigr => K _. rewrite denote_sum; apply: eq_bigr => g _. exact: (denote_finish_trace_preverify_enum_bot EA t K g s (xi s) Htf HAS HAH Ha Hy Hb Hy' Hd HX HZ HP HK HXA HXB HZA HZB Hlam HpEC HXhat Hg HtA HtB). } by rewrite trace_final_full_sum; apply: eq_bigr => h _; rewrite trace_final_branch_history. Qed.
Fact run_output_mismatch_prob_le_preverify_verify_accept (qA : {set L}) (EA : ADVq qA) (xi : CQs) : vbool true != vbool false -> abortv !=
  Sv -> abortv != Shv -> (forall i, a_ i != y_ i) -> pubwall (Pvar != abortv -> (forall i, abortv != a_ i) -> (forall i, abortv != y_ i) ->
  (forall i, abortv != b_ i) -> (forall i, abortv != y'_ i) -> (forall i, abortv != d_ i) -> abortv != Xv -> abortv != Zv -> abortv != Pvar
  -> abortv != Kv -> abortv != XA -> abortv != XB -> abortv != ZA -> abortv != ZB -> abortv != lamv -> abortv != pECv -> abortv != Xhatv ->
  abortv != gv -> abortv != tAv -> abortv != tBv -> XA != fv -> Xhatv != fv -> fv != Sv -> Xhatv != Sv -> Sv != Shv -> Sv != Pvar -> Shv !=
  Pvar -> (forall s, (forall f, 0 <= unif_pseed s f) /\ \sum_f unif_pseed s f = 1) -> (forall i, cmd_wf qA (RNDs i)) -> cmd_wf qA (PEs) ->
  cmd_wf qA (ECs) -> (forall s, xi s \is psdlf) -> run_output_mismatch_prob (EVALs qA EA xi) <= run_event_prob verify_accept_raw_mismatch
  (preverify_eval EA xi)).
Proof.
  move=> Htf HAS HAH Hay HPa HPy HPb HPy' HPd HPX HPZ HPabort Ha Hy Hb Hy' Hd HX HZ HP HK HXA HXB HZA HZB Hlam HpEC HXhat Hg HtA HtB HXAf HXhatf HfS HXhatS HSS HSP HShP Hseed Hround Hpe Hec Hxi. rewrite /run_output_mismatch_prob. rewrite -(@denote_finish_preverify_eval qA EA xi Htf HAS HAH Hay HPa HPy HPb HPy' HPd HPX HPZ HPabort Ha Hy Hb Hy' Hd HX HZ HP HK HXA HXB HZA HZB Hlam HpEC HXhat Hg HtA HtB).
    apply: (finish_after_preverify_mismatch_le_verify_accept EA Htf HAS HAH HXAf HXhatf HfS HXhatS HSS HSP HShP Hseed). have Hwf := preverify_cmd_wf Hround Hpe Hec. move=> s; exact: (@denote_psd R L HL Cv V qA Pvar EA preverify_cmd xi Hwf Hxi s). Qed.
Lemma run_pass_prob_decomp (qA : {set L}) (EA : ADVq qA) (xi : CQs) : (forall i, a_ i != y_ i) -> pubwall (Pvar != abortv -> run_pass_prob
  (EVALs qA EA xi) = \sum_s \sum_(h : run_history) (final_store h s abortv == vbool false)%:R * @complex.Re R (\Tr ((hist_wt h s)%:C *:
  hist_so EA h (xi s)))).
Proof.
  move=> Hay HPa HPy HPb HPy' HPd HPX HPZ HPabort; rewrite /run_pass_prob. rewrite (@denote_run_decomp qA EA xi Hay HPa HPy HPb HPy' HPd HPX HPZ HPabort); rewrite run_event_prob_sum; apply: eq_bigr => s _. rewrite /history_sum run_event_prob_sum; apply: eq_bigr => h _. by rewrite run_event_prob_history_branch. Qed.
Definition run_pass_history_state (qA : {set L}) (EA : ADVq qA) (xi : CQs) : 'F[HL]_setT := \sum_s \sum_(h : run_history) (((final_store h s
  abortv == vbool false)%:R)%:C *: ((hist_wt h s)%:C *: hist_so EA h (xi s))).
Fact run_pass_history_state_trace (qA : {set L}) (EA : ADVq qA) (xi : CQs) : (forall i, a_ i != y_ i) -> pubwall (Pvar != abortv ->
  @complex.Re R (\Tr (run_pass_history_state EA xi)) = run_pass_prob (EVALs qA EA xi)).
Proof.
  move=> Hay HPa HPy HPb HPy' HPd HPX HPZ HPabort; rewrite (run_pass_prob_decomp EA xi Hay HPa HPy HPb HPy' HPd HPX HPZ HPabort). have Htrace : \Tr (run_pass_history_state EA xi) = \sum_s \sum_h \Tr ((((final_store h s abortv == vbool false)%:R)%:C *: ((hist_wt h s)%:C *: hist_so EA h (xi s)))).
  { rewrite /run_pass_history_state linear_sum. apply: eq_bigr => s _. by rewrite linear_sum. } rewrite Htrace raddf_sum /=; apply: eq_bigr => s _. rewrite raddf_sum /=; apply: eq_bigr => h _. rewrite scalerA -rmorphM /= [((final_store h s abortv == vbool false)%:R * hist_wt h s)]mulrC; exact: trace_weight_mul. Qed.
Fact preverify_verify_accept_prob_decomp (qA : {set L}) (EA : ADVq qA) (xi : CQs) : (forall i, a_ i != y_ i) -> pubwall (Pvar != abortv ->
  run_event_prob verify_accept_raw_mismatch (preverify_eval EA xi) = \sum_s \sum_(h : run_history) run_event_prob verify_accept_raw_mismatch
  (trace_preverify_branch EA (enum 'I_M) h (start_store s) (xi s))).
Proof. move=> Hay HPa HPy HPb HPy' HPd HPX HPZ HPabort; rewrite (preverify_eval_decomp EA xi Hay HPa HPy HPb HPy' HPd HPX HPZ HPabort). rewrite run_event_prob_sum; apply: eq_bigr => s _. by rewrite run_event_prob_sum. Qed.
Fact preverify_corr_prob_event_decomp (key_count : nat) (key_of : V -> option 'I_key_count) (qA : {set L}) (EA : ADVq qA) (xi : CQs) (x x'
  : 'I_key_count) : (forall i, a_ i != y_ i) -> pubwall (Pvar != abortv -> run_event_prob (corr_prob_event key_of x x') (preverify_eval EA
  xi) = \sum_s \sum_(h : run_history) run_event_prob (corr_prob_event key_of x x') (trace_preverify_branch EA (enum 'I_M) h (start_store s)
  (xi s))).
Proof. move=> Hay HPa HPy HPb HPy' HPd HPX HPZ HPabort; rewrite (preverify_eval_decomp EA xi Hay HPa HPy HPb HPy' HPd HPX HPZ HPabort). rewrite run_event_prob_sum; apply: eq_bigr => s _. by rewrite run_event_prob_sum. Qed.
Fact preverify_verify_accept_prob_decomp_readout (qA : {set L}) (EA : ADVq qA) (xi : CQs) : vbool true != vbool false -> (forall i, a_ i !=
  y_ i) -> pubwall (Pvar != abortv -> abortv != Sv -> abortv != Shv -> ecwall (tagwall (xawall (xhwall (run_event_prob
  verify_accept_raw_mismatch (preverify_eval EA xi) = \sum_s \sum_(h : run_history) let s0 := start_store s in let s_ann := announce_store
  (trace_store_seq h.1 (enum 'I_M) s0) in let s_pe := paramest_store h s_ann in if pe_failed s_pe then 0 else (((s_pe abortv == vbool false)
  && (verify_hash (hist_g h) (s_pe XA) == verify_hash (hist_g h) (ir_dec (ir_pub leakEC (s_pe XA) (s_pe XB)) (s_pe XB))) && (s_pe XA !=
  ir_dec (ir_pub leakEC (s_pe XA) (s_pe XB)) (s_pe XB)))%:R) * @complex.Re R (\Tr (((trace_samples_weight h.1 (enum 'I_M) s0 *
  trace_unused_weight h.1 (enum 'I_M) * key_sample_mass s_ann (hist_K h) * unif_vseed (errcorr_seed_store s_pe) (hist_g h) * seed_unused
  (hist_f h))%:C *: trace_so_seq EA h.1 (enum 'I_M) (xi s))))))))).
Proof.
  move=> Htf Hay HPa HPy HPb HPy' HPd HPX HPZ HPabort HAS HAH HAp HAXhat HAg HAtA HAtB HAP HgtA HgtB HtAtB HtAP HtBP HXAp HXAXhat HXAg HXAtA HXAtB HXAP HXBp HXhatg HXhattA HXhattB HXhatP. rewrite (preverify_verify_accept_prob_decomp EA xi Hay HPa HPy HPb HPy' HPd HPX HPZ HPabort); apply: eq_bigr => s _. apply: eq_bigr => h _. exact: (run_event_prob_verify_accept_trace_preverify_branch_readout EA (enum 'I_M) h (start_store s) (xi s) Htf HAS HAH HAp HAXhat HAg HAtA HAtB HAP HgtA HgtB HtAtB HtAP HtBP HXAp HXAXhat HXAg HXAtA HXAtB HXAP HXBp HXhatg HXhattA HXhattB HXhatP). Qed.
Fact preverify_corr_prob_event_decomp_readout (key_count : nat) (key_of : V -> option 'I_key_count) (qA : {set L}) (EA : ADVq qA) (xi :
  CQs) (x x' : 'I_key_count) : vbool true != vbool false -> (forall i, a_ i != y_ i) -> pubwall (Pvar != abortv -> abortv != Sv -> abortv !=
  Shv -> ecwall (xawall (xhwall (run_event_prob (corr_prob_event key_of x x') (preverify_eval EA xi) = \sum_s \sum_(h : run_history) let s0
  := start_store s in let s_ann := announce_store (trace_store_seq h.1 (enum 'I_M) s0) in let s_pe := paramest_store h s_ann in if pe_failed
  s_pe then 0 else (((s_pe abortv == vbool false) && (key_of (s_pe XA) == Some x) && (key_of (ir_dec (ir_pub leakEC (s_pe XA) (s_pe XB))
  (s_pe XB)) == Some x'))%:R) * @complex.Re R (\Tr (((trace_samples_weight h.1 (enum 'I_M) s0 * trace_unused_weight h.1 (enum 'I_M) *
  key_sample_mass s_ann (hist_K h) * unif_vseed (errcorr_seed_store s_pe) (hist_g h) * seed_unused (hist_f h))%:C *: trace_so_seq EA h.1
  (enum 'I_M) (xi s)))))))).
Proof.
  move=> Htf Hay HPa HPy HPb HPy' HPd HPX HPZ HPabort HAS HAH HAp HAXhat HAg HAtA HAtB HAP HXAp HXAXhat HXAg HXAtA HXAtB HXAP HXBp HXhatg HXhattA HXhattB HXhatP. rewrite (preverify_corr_prob_event_decomp key_of EA xi x x' Hay HPa HPy HPb HPy' HPd HPX HPZ HPabort); apply: eq_bigr => s _. apply: eq_bigr => h _. exact: (run_event_prob_corr_event_trace_preverify_branch_readout key_of EA (enum 'I_M) h (start_store s) (xi s) x x' Htf HAS HAH HAp HAXhat HAg HAtA HAtB HAP HXAp HXAXhat HXAg HXAtA HXAtB HXAP HXBp HXhatg HXhattA HXhattB HXhatP). Qed.
Fact preverify_verify_accept_prob_decomp_readout_fbot (qA : {set L}) (EA : ADVq qA) (xi : CQs) : vbool true != vbool false -> (forall i, a_
  i != y_ i) -> pubwall (Pvar != abortv -> abortv != Sv -> abortv != Shv -> ecwall (tagwall (xawall (xhwall (run_event_prob
  verify_accept_raw_mismatch (preverify_eval EA xi) = \sum_s \sum_(t : round_trace) \sum_K \sum_g let h := (t, ((K, g), bot)) in let s0 :=
  start_store s in let s_ann := announce_store (trace_store_seq t (enum 'I_M) s0) in let s_pe := paramest_store h s_ann in if pe_failed s_pe
  then 0 else (((s_pe abortv == vbool false) && (verify_hash g (s_pe XA) == verify_hash g (ir_dec (ir_pub leakEC (s_pe XA) (s_pe XB)) (s_pe
  XB))) && (s_pe XA != ir_dec (ir_pub leakEC (s_pe XA) (s_pe XB)) (s_pe XB)))%:R) * @complex.Re R (\Tr (((trace_samples_weight t (enum 'I_M)
  s0 * trace_unused_weight t (enum 'I_M) * key_sample_mass s_ann K * unif_vseed (errcorr_seed_store s_pe) g)%:C *: trace_so_seq EA t (enum
  'I_M) (xi s))))))))).
Proof.
  move=> Htf Hay HPa HPy HPb HPy' HPd HPX HPZ HPabort HAS HAH HAp HAXhat HAg HAtA HAtB HAP HgtA HgtB HtAtB HtAP HtBP HXAp HXAXhat HXAg HXAtA HXAtB HXAP HXBp HXhatg HXhattA HXhattB HXhatP. rewrite (preverify_verify_accept_prob_decomp_readout EA xi Htf Hay HPa HPy HPb HPy' HPd HPX HPZ HPabort HAS HAH HAp HAXhat HAg HAtA HAtB HAP HgtA HgtB HtAtB HtAP HtBP HXAp HXAXhat HXAg HXAtA HXAtB HXAP HXBp HXhatg HXhattA HXhattB HXhatP). apply: eq_bigr => s _. rewrite -[LHS](run_history_sum_splitR (fun t K g f => let h := (t, ((K, g), f)) in let s0 := start_store s in let s_ann := announce_store (trace_store_seq t (enum 'I_M) s0) in let s_pe := paramest_store h s_ann in if pe_failed s_pe then 0 else (((s_pe abortv == vbool false) && (verify_hash g (s_pe XA) == verify_hash g (ir_dec (ir_pub leakEC (s_pe XA) (s_pe XB)) (s_pe XB))) && (s_pe XA != ir_dec (ir_pub leakEC (s_pe XA) (s_pe XB)) (s_pe XB)))%:R) * @complex.Re R (\Tr (((trace_samples_weight t (enum 'I_M) (start_store s) * trace_unused_weight t (enum 'I_M) * key_sample_mass s_ann K * unif_vseed (errcorr_seed_store s_pe) g * seed_unused f)%:C *: trace_so_seq EA t (enum 'I_M) (xi s)))))). apply: eq_bigr => t _; apply: eq_bigr => K _; apply: eq_bigr => g _.
    rewrite (bigD1 bot) //=; rewrite [X in _ + X]big1 ?addr0.
  - rewrite /seed_unused eqxx !mulr1. by [].
  - move=> f Hf; rewrite /seed_unused (negbTE Hf). case: (pe_failed (paramest_store (t, ((K, g), f)) (announce_store (trace_store_seq t (enum 'I_M) (start_store s))))) => //. by rewrite mulr0 rmorph0 scale0r linear0 mulr0. Qed.
Fact preverify_verify_accept_prob_decomp_seed_factor (qA : {set L}) (EA : ADVq qA) (xi : CQs) : vbool true != vbool false -> (forall i, a_
  i != y_ i) -> pubwall (Pvar != abortv -> abortv != Sv -> abortv != Shv -> ecwall (tagwall (xawall (xhwall (run_event_prob
  verify_accept_raw_mismatch (preverify_eval EA xi) = \sum_s \sum_(t : round_trace) \sum_K \sum_g let h := (t, ((K, g), bot)) in let s0 :=
  start_store s in let s_ann := announce_store (trace_store_seq t (enum 'I_M) s0) in let s_pe := paramest_store h s_ann in if pe_failed s_pe
  then 0 else (((s_pe abortv == vbool false) && (verify_hash g (s_pe XA) == verify_hash g (ir_dec (ir_pub leakEC (s_pe XA) (s_pe XB)) (s_pe
  XB))) && (s_pe XA != ir_dec (ir_pub leakEC (s_pe XA) (s_pe XB)) (s_pe XB)))%:R) * (unif_vseed (errcorr_seed_store s_pe) g * @complex.Re R
  (\Tr (((trace_samples_weight t (enum 'I_M) s0 * trace_unused_weight t (enum 'I_M) * key_sample_mass s_ann K)%:C *: trace_so_seq EA t (enum
  'I_M) (xi s)))))))))).
Proof.
  move=> Htf Hay HPa HPy HPb HPy' HPd HPX HPZ HPabort HAS HAH HAp HAXhat HAg HAtA HAtB HAP HgtA HgtB HtAtB HtAP HtBP HXAp HXAXhat HXAg HXAtA HXAtB HXAP HXBp HXhatg HXhattA HXhattB HXhatP. rewrite (preverify_verify_accept_prob_decomp_readout_fbot EA xi Htf Hay HPa HPy HPb HPy' HPd HPX HPZ HPabort HAS HAH HAp HAXhat HAg HAtA HAtB HAP HgtA HgtB HtAtB HtAP HtBP HXAp HXAXhat HXAg HXAtA HXAtB HXAP HXBp HXhatg HXhattA HXhattB HXhatP). apply: eq_bigr => s _; apply: eq_bigr => t _; apply: eq_bigr => K _. apply: eq_bigr => g _. set h0 := (t, ((K, g), bot)); set s_start := start_store s; set s_pub := announce_store (trace_store_seq t (enum 'I_M) s_start). set s_param := paramest_store h0 s_pub. case Hpe: (pe_failed s_param). by rewrite /s_param /s_pub /s_start /h0 Hpe. rewrite /s_param /s_pub /s_start /h0 Hpe. set base := trace_samples_weight t (enum 'I_M) s_start * trace_unused_weight t (enum 'I_M) * key_sample_mass s_pub K. set seed := unif_vseed (errcorr_seed_store s_param) g; set rho := trace_so_seq EA t (enum 'I_M) (xi s). set event := (((s_param abortv == vbool false) && (verify_hash g (s_param XA) == verify_hash g (ir_dec (ir_pub leakEC (s_param XA) (s_param XB)) (s_param XB))) && (s_param XA != ir_dec (ir_pub leakEC (s_param XA) (s_param XB)) (s_param XB)))%:R : R). change (event * @complex.Re R (\Tr (((base * seed)%:C) *: rho)) = event * (seed * @complex.Re R (\Tr (base%:C *: rho)))). by rewrite trace_weight_mul. Qed.
Fact preverify_verify_accept_prob_decomp_seed_independent (qA : {set L}) (EA : ADVq qA) (xi : CQs) : vbool true != vbool false -> (forall
  i, a_ i != y_ i) -> pubwall (Pvar != abortv -> abortv != Sv -> abortv != Shv -> ecwall (tagwall (xawall (xhwall (run_event_prob
  verify_accept_raw_mismatch (preverify_eval EA xi) = \sum_s \sum_(t : round_trace) \sum_K \sum_g let h := (t, ((K, bot), bot)) in let s0 :=
  start_store s in let s_ann := announce_store (trace_store_seq t (enum 'I_M) s0) in let s_pe := paramest_store h s_ann in if pe_failed s_pe
  then 0 else (((s_pe abortv == vbool false) && (verify_hash g (s_pe XA) == verify_hash g (ir_dec (ir_pub leakEC (s_pe XA) (s_pe XB)) (s_pe
  XB))) && (s_pe XA != ir_dec (ir_pub leakEC (s_pe XA) (s_pe XB)) (s_pe XB)))%:R) * (unif_vseed (errcorr_seed_store s_pe) g * @complex.Re R
  (\Tr (((trace_samples_weight t (enum 'I_M) s0 * trace_unused_weight t (enum 'I_M) * key_sample_mass s_ann K)%:C *: trace_so_seq EA t (enum
  'I_M) (xi s)))))))))).
Proof.
  move=> Htf Hay HPa HPy HPb HPy' HPd HPX HPZ HPabort HAS HAH HAp HAXhat HAg HAtA HAtB HAP HgtA HgtB HtAtB HtAP HtBP HXAp HXAXhat HXAg HXAtA HXAtB HXAP HXBp HXhatg HXhattA HXhattB HXhatP. rewrite (preverify_verify_accept_prob_decomp_seed_factor EA xi Htf Hay HPa HPy HPb HPy' HPd HPX HPZ HPabort HAS HAH HAp HAXhat HAg HAtA HAtB HAP HgtA HgtB HtAtB HtAP HtBP HXAp HXAXhat HXAg HXAtA HXAtB HXAP HXBp HXhatg HXhattA HXhattB HXhatP). apply: eq_bigr => s _; apply: eq_bigr => t _; apply: eq_bigr => K _. apply: eq_bigr => g _. set s0 := start_store s; set s_ann := announce_store (trace_store_seq t (enum 'I_M) s0); rewrite /=. by rewrite (paramest_store_future_irrel t K g bot bot bot s_ann). Qed.
Fact preverify_verify_accept_prob_decomp_seed_sum (qA : {set L}) (EA : ADVq qA) (xi : CQs) : vbool true != vbool false -> (forall i, a_ i
  != y_ i) -> pubwall (Pvar != abortv -> abortv != Sv -> abortv != Shv -> ecwall (tagwall (xawall (xhwall (run_event_prob
  verify_accept_raw_mismatch (preverify_eval EA xi) = \sum_s \sum_(t : round_trace) \sum_K let h := (t, ((K, bot), bot)) in let s0 :=
  start_store s in let s_ann := announce_store (trace_store_seq t (enum 'I_M) s0) in let s_pe := paramest_store h s_ann in if pe_failed s_pe
  then 0 else (\sum_g unif_vseed (errcorr_seed_store s_pe) g * (((s_pe abortv == vbool false) && (verify_hash g (s_pe XA) == verify_hash g
  (ir_dec (ir_pub leakEC (s_pe XA) (s_pe XB)) (s_pe XB))) && (s_pe XA != ir_dec (ir_pub leakEC (s_pe XA) (s_pe XB)) (s_pe XB)))%:R)) *
  @complex.Re R (\Tr (((trace_samples_weight t (enum 'I_M) s0 * trace_unused_weight t (enum 'I_M) * key_sample_mass s_ann K)%:C *:
  trace_so_seq EA t (enum 'I_M) (xi s))))))))).
Proof.
  move=> Htf Hay HPa HPy HPb HPy' HPd HPX HPZ HPabort HAS HAH HAp HAXhat HAg HAtA HAtB HAP HgtA HgtB HtAtB HtAP HtBP HXAp HXAXhat HXAg HXAtA HXAtB HXAP HXBp HXhatg HXhattA HXhattB HXhatP. rewrite (preverify_verify_accept_prob_decomp_seed_independent EA xi Htf Hay HPa HPy HPb HPy' HPd HPX HPZ HPabort HAS HAH HAp HAXhat HAg HAtA HAtB HAP HgtA HgtB HtAtB HtAP HtBP HXAp HXAXhat HXAg HXAtA HXAtB HXAP HXBp HXhatg HXhattA HXhattB HXhatP). apply: eq_bigr => s _; apply: eq_bigr => t _; apply: eq_bigr => K _. rewrite /=. case: (pe_failed (paramest_store (t, ((K, bot), bot)) (announce_store (trace_store_seq t (enum 'I_M) (start_store s))))) => /=.
  - by rewrite big1. under eq_bigr => g _ do rewrite mulrA [X in X * _]mulrC. by rewrite -mulr_suml. Qed.
Fact preverify_corr_prob_event_decomp_readout_fbot (key_count : nat) (key_of : V -> option 'I_key_count) (qA : {set L}) (EA : ADVq qA) (xi
  : CQs) (x x' : 'I_key_count) : vbool true != vbool false -> (forall i, a_ i != y_ i) -> pubwall (Pvar != abortv -> abortv != Sv -> abortv
  != Shv -> ecwall (xawall (xhwall (run_event_prob (corr_prob_event key_of x x') (preverify_eval EA xi) = \sum_s \sum_(t : round_trace)
  \sum_K \sum_g let h := (t, ((K, g), bot)) in let s0 := start_store s in let s_ann := announce_store (trace_store_seq t (enum 'I_M) s0) in
  let s_pe := paramest_store h s_ann in if pe_failed s_pe then 0 else (((s_pe abortv == vbool false) && (key_of (s_pe XA) == Some x) &&
  (key_of (ir_dec (ir_pub leakEC (s_pe XA) (s_pe XB)) (s_pe XB)) == Some x'))%:R) * @complex.Re R (\Tr (((trace_samples_weight t (enum 'I_M)
  s0 * trace_unused_weight t (enum 'I_M) * key_sample_mass s_ann K * unif_vseed (errcorr_seed_store s_pe) g)%:C *: trace_so_seq EA t (enum
  'I_M) (xi s)))))))).
Proof.
  move=> Htf Hay HPa HPy HPb HPy' HPd HPX HPZ HPabort HAS HAH HAp HAXhat HAg HAtA HAtB HAP HXAp HXAXhat HXAg HXAtA HXAtB HXAP HXBp HXhatg HXhattA HXhattB HXhatP. rewrite (preverify_corr_prob_event_decomp_readout key_of EA xi x x' Htf Hay HPa HPy HPb HPy' HPd HPX HPZ HPabort HAS HAH HAp HAXhat HAg HAtA HAtB HAP HXAp HXAXhat HXAg HXAtA HXAtB HXAP HXBp HXhatg HXhattA HXhattB HXhatP). apply: eq_bigr => s _.
    rewrite -[LHS](run_history_sum_splitR (fun t K g f => let h := (t, ((K, g), f)) in let s0 := start_store s in let s_ann := announce_store (trace_store_seq t (enum 'I_M) s0) in let s_pe := paramest_store h s_ann in if pe_failed s_pe then 0 else (((s_pe abortv == vbool false) && (key_of (s_pe XA) == Some x) && (key_of (ir_dec (ir_pub leakEC (s_pe XA) (s_pe XB)) (s_pe XB)) == Some x'))%:R) * @complex.Re R (\Tr (((trace_samples_weight t (enum 'I_M) (start_store s) * trace_unused_weight t (enum 'I_M) * key_sample_mass s_ann K * unif_vseed (errcorr_seed_store s_pe) g * seed_unused f)%:C *: trace_so_seq EA t (enum 'I_M) (xi s)))))). apply: eq_bigr => t _; apply: eq_bigr => K _; apply: eq_bigr => g _. rewrite (bigD1 bot) //=; rewrite [X in _ + X]big1 ?addr0.
  - rewrite /seed_unused eqxx !mulr1. by [].
  - move=> f Hf; rewrite /seed_unused (negbTE Hf). case: (pe_failed (paramest_store (t, ((K, g), f)) (announce_store (trace_store_seq t (enum 'I_M) (start_store s))))) => //. by rewrite mulr0 rmorph0 scale0r linear0 mulr0. Qed.
Fact preverify_corr_prob_event_decomp_seed_factor (key_count : nat) (key_of : V -> option 'I_key_count) (qA : {set L}) (EA : ADVq qA) (xi :
  CQs) (x x' : 'I_key_count) : vbool true != vbool false -> (forall i, a_ i != y_ i) -> pubwall (Pvar != abortv -> abortv != Sv -> abortv !=
  Shv -> ecwall (xawall (xhwall (run_event_prob (corr_prob_event key_of x x') (preverify_eval EA xi) = \sum_s \sum_(t : round_trace) \sum_K
  \sum_g let h := (t, ((K, g), bot)) in let s0 := start_store s in let s_ann := announce_store (trace_store_seq t (enum 'I_M) s0) in let
  s_pe := paramest_store h s_ann in if pe_failed s_pe then 0 else (((s_pe abortv == vbool false) && (key_of (s_pe XA) == Some x) && (key_of
  (ir_dec (ir_pub leakEC (s_pe XA) (s_pe XB)) (s_pe XB)) == Some x'))%:R) * (unif_vseed (errcorr_seed_store s_pe) g * @complex.Re R (\Tr
  (((trace_samples_weight t (enum 'I_M) s0 * trace_unused_weight t (enum 'I_M) * key_sample_mass s_ann K)%:C *: trace_so_seq EA t (enum
  'I_M) (xi s))))))))).
Proof.
  move=> Htf Hay HPa HPy HPb HPy' HPd HPX HPZ HPabort HAS HAH HAp HAXhat HAg HAtA HAtB HAP HXAp HXAXhat HXAg HXAtA HXAtB HXAP HXBp HXhatg HXhattA HXhattB HXhatP. rewrite (preverify_corr_prob_event_decomp_readout_fbot key_of EA xi x x' Htf Hay HPa HPy HPb HPy' HPd HPX HPZ HPabort HAS HAH HAp HAXhat HAg HAtA HAtB HAP HXAp HXAXhat HXAg HXAtA HXAtB HXAP HXBp HXhatg HXhattA HXhattB HXhatP). apply: eq_bigr => s _; apply: eq_bigr => t _; apply: eq_bigr => K _. apply: eq_bigr => g _. set h0 := (t, ((K, g), bot)); set s_start := start_store s; set s_pub := announce_store (trace_store_seq t (enum 'I_M) s_start). set s_param := paramest_store h0 s_pub. case Hpe: (pe_failed s_param).
    by rewrite /s_param /s_pub /s_start /h0 Hpe. rewrite /s_param /s_pub /s_start /h0 Hpe. set base := trace_samples_weight t (enum 'I_M) s_start * trace_unused_weight t (enum 'I_M) * key_sample_mass s_pub K. set seed := unif_vseed (errcorr_seed_store s_param) g; set rho := trace_so_seq EA t (enum 'I_M) (xi s). set event := (((s_param abortv == vbool false) && (key_of (s_param XA) == Some x) && (key_of (ir_dec (ir_pub leakEC (s_param XA) (s_param XB)) (s_param XB)) == Some x'))%:R : R). change (event * @complex.Re R (\Tr (((base * seed)%:C) *: rho)) = event * (seed * @complex.Re R (\Tr (base%:C *: rho)))). by rewrite trace_weight_mul. Qed.
Fact preverify_corr_prob_event_decomp_seed_independent (key_count : nat) (key_of : V -> option 'I_key_count) (qA : {set L}) (EA : ADVq qA)
  (xi : CQs) (x x' : 'I_key_count) : vbool true != vbool false -> (forall i, a_ i != y_ i) -> pubwall (Pvar != abortv -> abortv != Sv ->
  abortv != Shv -> ecwall (xawall (xhwall (run_event_prob (corr_prob_event key_of x x') (preverify_eval EA xi) = \sum_s \sum_(t :
  round_trace) \sum_K \sum_g let h := (t, ((K, bot), bot)) in let s0 := start_store s in let s_ann := announce_store (trace_store_seq t
  (enum 'I_M) s0) in let s_pe := paramest_store h s_ann in if pe_failed s_pe then 0 else (((s_pe abortv == vbool false) && (key_of (s_pe XA)
  == Some x) && (key_of (ir_dec (ir_pub leakEC (s_pe XA) (s_pe XB)) (s_pe XB)) == Some x'))%:R) * (unif_vseed (errcorr_seed_store s_pe) g *
  @complex.Re R (\Tr (((trace_samples_weight t (enum 'I_M) s0 * trace_unused_weight t (enum 'I_M) * key_sample_mass s_ann K)%:C *:
  trace_so_seq EA t (enum 'I_M) (xi s))))))))).
Proof.
  move=> Htf Hay HPa HPy HPb HPy' HPd HPX HPZ HPabort HAS HAH HAp HAXhat HAg HAtA HAtB HAP HXAp HXAXhat HXAg HXAtA HXAtB HXAP HXBp HXhatg HXhattA HXhattB HXhatP. rewrite (preverify_corr_prob_event_decomp_seed_factor key_of EA xi x x' Htf Hay HPa HPy HPb HPy' HPd HPX HPZ HPabort HAS HAH HAp HAXhat HAg HAtA HAtB HAP HXAp HXAXhat HXAg HXAtA HXAtB HXAP HXBp HXhatg HXhattA HXhattB HXhatP). apply: eq_bigr => s _; apply: eq_bigr => t _; apply: eq_bigr => K _. apply: eq_bigr => g _. set s0 := start_store s; set s_ann := announce_store (trace_store_seq t (enum 'I_M) s0); rewrite /=. by rewrite (paramest_store_future_irrel t K g bot bot bot s_ann). Qed.
Fact preverify_corr_prob_event_decomp_seed_sum (key_count : nat) (key_of : V -> option 'I_key_count) (qA : {set L}) (EA : ADVq qA) (xi :
  CQs) (x x' : 'I_key_count) : vbool true != vbool false -> (forall i, a_ i != y_ i) -> pubwall (Pvar != abortv -> abortv != Sv -> abortv !=
  Shv -> ecwall (xawall (xhwall (run_event_prob (corr_prob_event key_of x x') (preverify_eval EA xi) = \sum_s \sum_(t : round_trace) \sum_K
  let h := (t, ((K, bot), bot)) in let s0 := start_store s in let s_ann := announce_store (trace_store_seq t (enum 'I_M) s0) in let s_pe :=
  paramest_store h s_ann in if pe_failed s_pe then 0 else (\sum_g unif_vseed (errcorr_seed_store s_pe) g * (((s_pe abortv == vbool false) &&
  (key_of (s_pe XA) == Some x) && (key_of (ir_dec (ir_pub leakEC (s_pe XA) (s_pe XB)) (s_pe XB)) == Some x'))%:R)) * @complex.Re R (\Tr
  (((trace_samples_weight t (enum 'I_M) s0 * trace_unused_weight t (enum 'I_M) * key_sample_mass s_ann K)%:C *: trace_so_seq EA t (enum
  'I_M) (xi s)))))))).
Proof.
  move=> Htf Hay HPa HPy HPb HPy' HPd HPX HPZ HPabort HAS HAH HAp HAXhat HAg HAtA HAtB HAP HXAp HXAXhat HXAg HXAtA HXAtB HXAP HXBp HXhatg HXhattA HXhattB HXhatP. rewrite (preverify_corr_prob_event_decomp_seed_independent key_of EA xi x x' Htf Hay HPa HPy HPb HPy' HPd HPX HPZ HPabort HAS HAH HAp HAXhat HAg HAtA HAtB HAP HXAp HXAXhat HXAg HXAtA HXAtB HXAP HXBp HXhatg HXhattA HXhattB HXhatP). apply: eq_bigr => s _; apply: eq_bigr => t _; apply: eq_bigr => K _. rewrite /=. case: (pe_failed (paramest_store (t, ((K, bot), bot)) (announce_store (trace_store_seq t (enum 'I_M) (start_store s))))) => /=.
  - by rewrite big1. under eq_bigr => g _ do rewrite mulrA [X in X * _]mulrC. by rewrite -mulr_suml. Qed.
Fact preverify_verify_accept_prob_collision_sumE (key_count : nat) (key_of : V -> option 'I_key_count) (collision : 'I_key_count ->
  'I_key_count -> R) (qA : {set L}) (EA : ADVq qA) (xi : CQs) : vbool true != vbool false -> (forall i, a_ i != y_ i) -> pubwall (Pvar !=
  abortv -> abortv != Sv -> abortv != Shv -> ecwall (tagwall (xawall (xhwall ((forall s t K, let h := (t, ((K, bot), bot)) in let s0 :=
  start_store s in let s_ann := announce_store (trace_store_seq t (enum 'I_M) s0) in let s_pe := paramest_store h s_ann in ~~ pe_failed s_pe
  -> \sum_g unif_vseed (errcorr_seed_store s_pe) g * (((s_pe abortv == vbool false) && (verify_hash g (s_pe XA) == verify_hash g (ir_dec
  (ir_pub leakEC (s_pe XA) (s_pe XB)) (s_pe XB))) && (s_pe XA != ir_dec (ir_pub leakEC (s_pe XA) (s_pe XB)) (s_pe XB)))%:R) = \sum_x
  \sum_(x' | x != x') ((\sum_g unif_vseed (errcorr_seed_store s_pe) g * (((s_pe abortv == vbool false) && (key_of (s_pe XA) == Some x) &&
  (key_of (ir_dec (ir_pub leakEC (s_pe XA) (s_pe XB)) (s_pe XB)) == Some x'))%:R)) * collision x x')) -> run_event_prob
  verify_accept_raw_mismatch (preverify_eval EA xi) = \sum_x \sum_(x' | x != x') corr_prob_prog key_of EA xi x x' * collision x x'))))).
Proof.
have corr_prob_progE : forall (key_count : nat) (key_of : V -> option 'I_key_count) (qA : {set L}) (EA : ADVq qA) (xi : CQs) (x x' : 'I_key_count), corr_prob_prog key_of EA xi x x' = run_event_prob (corr_prob_event key_of x x') (preverify_eval EA xi).
{ clear xi EA qA collision key_of key_count; move=> key_count key_of qA EA xi x x'. rewrite /corr_prob_prog /run_event_prob [RHS]big_mkcond [LHS]big_mkcond /=. apply: eq_bigr => s _. by case: (corr_prob_event key_of x x' s); rewrite ?mul1r ?mul0r. } move=> Htf Hay HPa HPy HPb HPy' HPd HPX HPZ HPabort HAS HAH HAp HAXhat HAg HAtA HAtB HAP HgtA HgtB HtAtB HtAP HtBP HXAp HXAXhat HXAg HXAtA HXAtB HXAP HXBp HXhatg HXhattA HXhattB HXhatP Hbranch. rewrite (preverify_verify_accept_prob_decomp_seed_sum EA xi Htf Hay HPa HPy HPb HPy' HPd HPX HPZ HPabort HAS HAH HAp HAXhat HAg HAtA HAtB HAP HgtA HgtB HtAtB HtAP HtBP HXAp HXAXhat HXAg HXAtA HXAtB HXAP HXBp HXhatg HXhattA HXhattB HXhatP). set F := fun s t K (x x' : 'I_key_count) => let h := (t, ((K, bot), bot)) in let s0 := start_store s in let s_ann := announce_store (trace_store_seq t (enum 'I_M) s0) in let s_pe := paramest_store h s_ann in if pe_failed s_pe then 0 else \sum_g unif_vseed (errcorr_seed_store s_pe) g * (((s_pe abortv == vbool false) && (key_of (s_pe XA) == Some x) && (key_of (ir_dec (ir_pub leakEC (s_pe XA) (s_pe XB)) (s_pe XB)) == Some x'))%:R). set G := fun s t K => let h := (t, ((K, bot), bot)) in let s0 := start_store s in let s_ann := announce_store (trace_store_seq t (enum 'I_M) s0) in @complex.Re R (\Tr (((trace_samples_weight t (enum 'I_M) s0 * trace_unused_weight t (enum 'I_M) * key_sample_mass s_ann K)%:C *: trace_so_seq EA t (enum 'I_M) (xi s)))). transitivity (\sum_s \sum_(t : round_trace) \sum_K ((\sum_x \sum_(x' | x != x') F s t K x x' * collision x x') * G s t K)).
  { apply: eq_bigr => s _; apply: eq_bigr => t _; apply: eq_bigr => K _. rewrite /F /G; set h := (t, ((K, bot), bot)); set s0 := start_store s; set s_ann := announce_store (trace_store_seq t (enum 'I_M) s0). set s_pe := paramest_store h s_ann. case Hpe: (pe_failed s_pe).
    { rewrite big1 ?mul0r // => x _. apply: big1 => x' _. by rewrite mul0r. } congr (_ * _); apply: Hbranch. by rewrite Hpe. } rewrite (finite_pair_sum_exchange3 F G collision); apply: eq_bigr => x _. apply: eq_bigr => x' _; congr (_ * _); rewrite /F /G corr_prob_progE. rewrite (preverify_corr_prob_event_decomp_seed_sum key_of EA xi x x' Htf Hay HPa HPy HPb HPy' HPd HPX HPZ HPabort HAS HAH HAp HAXhat HAg HAtA HAtB HAP HXAp HXAXhat HXAg HXAtA HXAtB HXAP HXBp HXhatg HXhattA HXhattB HXhatP). apply: eq_bigr => s _; apply: eq_bigr => t _; apply: eq_bigr => K _. set h := (t, ((K, bot), bot)); set s0 := start_store s; set s_ann := announce_store (trace_store_seq t (enum 'I_M) s0). set s_pe := paramest_store h s_ann. case Hpe: (pe_failed s_pe). by rewrite /s_pe /s_ann /s0 /h Hpe ?mul0r ?mulr0. by rewrite /s_pe /s_ann /s0 /h Hpe ?mul0r ?mulr0. Qed.
Fact run_output_mismatch_prob_le_collision_sum (key_count : nat) (key_of : V -> option 'I_key_count) (collision : 'I_key_count ->
  'I_key_count -> R) (qA : {set L}) (EA : ADVq qA) (xi : CQs) : vbool true != vbool false -> abortv != Sv -> abortv != Shv -> (forall i, a_
  i != y_ i) -> pubwall (Pvar != abortv -> (forall i, abortv != a_ i) -> (forall i, abortv != y_ i) -> (forall i, abortv != b_ i) -> (forall
  i, abortv != y'_ i) -> (forall i, abortv != d_ i) -> abortv != Xv -> abortv != Zv -> abortv != Pvar -> abortv != Kv -> abortv != XA ->
  abortv != XB -> abortv != ZA -> abortv != ZB -> abortv != lamv -> abortv != pECv -> abortv != Xhatv -> abortv != gv -> abortv != tAv ->
  abortv != tBv -> XA != fv -> Xhatv != fv -> fv != Sv -> Xhatv != Sv -> Sv != Shv -> Sv != Pvar -> Shv != Pvar -> tagwall (xawall (xhwall
  ((forall s, (forall f, 0 <= unif_pseed s f) /\ \sum_f unif_pseed s f = 1) -> (forall i, cmd_wf qA (RNDs i)) -> cmd_wf qA (PEs) -> cmd_wf
  qA (ECs) -> (forall s, xi s \is psdlf) -> (forall s t K, let h := (t, ((K, bot), bot)) in let s0 := start_store s in let s_ann :=
  announce_store (trace_store_seq t (enum 'I_M) s0) in let s_pe := paramest_store h s_ann in ~~ pe_failed s_pe -> \sum_g unif_vseed
  (errcorr_seed_store s_pe) g * (((s_pe abortv == vbool false) && (verify_hash g (s_pe XA) == verify_hash g (ir_dec (ir_pub leakEC (s_pe XA)
  (s_pe XB)) (s_pe XB))) && (s_pe XA != ir_dec (ir_pub leakEC (s_pe XA) (s_pe XB)) (s_pe XB)))%:R) = \sum_x \sum_(x' | x != x') ((\sum_g
  unif_vseed (errcorr_seed_store s_pe) g * (((s_pe abortv == vbool false) && (key_of (s_pe XA) == Some x) && (key_of (ir_dec (ir_pub leakEC
  (s_pe XA) (s_pe XB)) (s_pe XB)) == Some x'))%:R)) * collision x x')) -> run_output_mismatch_prob (EVALs qA EA xi) <= \sum_x \sum_(x' | x
  != x') corr_prob_prog key_of EA xi x x' * collision x x')))).
Proof.
  move=> Htf HAS HAH Hay HPa HPy HPb HPy' HPd HPX HPZ HPabort Ha Hy Hb Hy' Hd HX HZ HP HK HXA HXB HZA HZB Hlam HpEC HXhat Hg HtA HtB HXAf HXhatf HfS HXhatS HSS HSP HShP HgtA HgtB HtAtB HtAP HtBP HXAp HXAXhat HXAg HXAtA HXAtB HXAP HXBp HXhatg HXhattA HXhattB HXhatP Hseed Hround Hpe Hec Hxi Hbranch. have Hle := run_output_mismatch_prob_le_preverify_verify_accept (qA := qA) (xi := xi) EA Htf HAS HAH Hay HPa HPy HPb HPy' HPd HPX HPZ HPabort Ha Hy Hb Hy' Hd HX HZ HP HK HXA HXB HZA HZB Hlam HpEC HXhat Hg HtA HtB HXAf HXhatf HfS HXhatS HSS HSP HShP Hseed Hround Hpe Hec Hxi. rewrite (preverify_verify_accept_prob_collision_sumE (key_count := key_count) (key_of := key_of) (collision := collision) (qA := qA) EA xi Htf Hay HPa HPy HPb HPy' HPd HPX HPZ HPabort HAS HAH HpEC HXhat Hg HtA HtB HP HgtA HgtB HtAtB HtAP HtBP HXAp HXAXhat HXAg HXAtA HXAtB HXAP HXBp HXhatg HXhattA HXhattB HXhatP Hbranch) in Hle. exact: Hle. Qed.
Fact bb84_eval_abort_support (qA : {set L}) (EA : ADVq qA) (xi : CQs) : (forall i, a_ i != y_ i) -> pubwall (Pvar != abortv -> abwall
  (forall t, EVALs qA EA xi t != 0 -> (t abortv == vbool true) || (t abortv == vbool false))).
Proof.
  move=> Hay HPa HPy HPb HPy' HPd HPX HPZ HPabort Ha Hy Hb Hy' Hd HAX HAZ HAP HK HXA HXB HZA HZB Hlam HpEC HXhat Hg HtA HtB Hf HS HSh t Hnz.
    case Hflag: ((t abortv == vbool true) || (t abortv == vbool false)) => //. have Hz : EVALs qA EA xi t = 0.
  { rewrite (@denote_run_decomp qA EA xi Hay HPa HPy HPb HPy' HPd HPX HPZ HPabort); rewrite sum_ffunE; apply: big1 => s _. rewrite /history_sum sum_ffunE; apply: big1 => h _. rewrite /history_branch. have Hfinal := final_store_abort_flag h s Ha Hy Hb Hy' Hd HAX HAZ HAP HK HXA HXB HZA HZB Hlam HpEC HXhat Hg HtA HtB Hf HS HSh. have Hneq : t != final_store h s. { apply/eqP=> Ht. by move: Hflag; rewrite Ht Hfinal. } by rewrite (cq_single_other ((hist_wt h s)%:C *: hist_so EA h (xi s)) Hneq). } by move: Hnz; rewrite Hz eqxx. Qed.
Fact bb84_eval_mass1 (qA : {set L}) (EA : ADVq qA) (xi : CQs) : (forall i, cmd_wf qA (RNDs i)) -> cmd_wf qA (PEs) -> cmd_wf qA (ECs) ->
  cmd_wf qA (PAs) -> cq_wf xi -> cq_mass (EVALs qA EA xi) = 1.
Proof.
  move=> Hround Hpe Hec Hpa [Hpsd Hmass]. have Hwf : @cmd_wf R L HL Cv V qA (PROGs).
  { exact: (@bb84_program_scheme_wf R L HL Cv V n k l leakEC M Qtol a_ y_ b_ y'_ d_ Q Xv Zv Kv XA XB ZA ZB lamv pECv Xhatv gv tAv tBv fv Sv Shv abortv Pvar basisX basisZ outEmpty bot empty_transcript vbool vbit vset vset_of vrat dev_rho dev_meas tr_app_rounds tr_app_pe tr_app_ec tr_app_pa bits_on test_bits_on err_count err_of unif_nsubset_mass ir_pub ir_dec unif_vseed verify_hash unif_pseed privacy_hash qA Hround Hpe Hec Hpa). } by rewrite /bb84_eval_scheme (@denote_mass R L HL Cv V qA Pvar EA _ xi Hwf Hpsd) Hmass. Qed.
Fact run_mass_from_abort_support (qA : {set L}) (EA : ADVq qA) (xi : CQs) : vbool true != vbool false -> (forall i, a_ i != y_ i) ->
  pubwall (Pvar != abortv -> abwall ((forall i, cmd_wf qA (RNDs i)) -> cmd_wf qA (PEs) -> cmd_wf qA (ECs) -> cmd_wf qA (PAs) -> cq_wf xi ->
  let xi_out := EVALs qA EA xi in run_abort_prob xi_out + run_pass_prob xi_out = 1)).
Proof.
  move=> Htf Hay HPa HPy HPb HPy' HPd HPX HPZ HPabort Ha Hy Hb Hy' Hd HAX HAZ HAP HK HXA HXB HZA HZB Hlam HpEC HXhat Hg HtA HtB Hf HS HSh Hround Hpe Hec Hpa Hxi xi_out. have Hsupport : forall s, xi_out s != 0 -> (s abortv == vbool true) || (s abortv == vbool false).
  { move=> s Hnz; rewrite /xi_out in Hnz. exact: (@bb84_eval_abort_support qA EA xi Hay HPa HPy HPb HPy' HPd HPX HPZ HPabort Ha Hy Hb Hy' Hd HAX HAZ HAP HK HXA HXB HZA HZB Hlam HpEC HXhat Hg HtA HtB Hf HS HSh s Hnz). } rewrite (run_abort_pass_prob_partition Htf Hsupport); exact: (bb84_eval_mass1 EA Hround Hpe Hec Hpa Hxi). Qed.
Fact paramest_store_XA_satisfies (P : V -> Prop) (h : run_history) (s : store) : XA != XB -> XA != ZA -> XA != ZB -> XA != Pvar -> XA !=
  lamv -> (forall K bits, P (bits_on K bits)) -> P (paramest_store h s XA).
Proof. move=> HXAB HXAZA HXAZB HXAP HXAlam HP; rewrite (paramest_store_XA h s HXAB HXAZA HXAZB HXAP HXAlam); exact: HP. Qed.
Fact run_output_mismatch_prob_le_collision_sum_from_paramest (key_count : nat) (key_of : V -> option 'I_key_count) (raw_val : option
  'I_key_count -> V) (collision : 'I_key_count -> 'I_key_count -> R) (qA : {set L}) (EA : ADVq qA) (xi : CQs) : vbool true != vbool false ->
  abortv != Sv -> abortv != Shv -> (forall i, a_ i != y_ i) -> pubwall (Pvar != abortv -> (forall i, abortv != a_ i) -> (forall i, abortv !=
  y_ i) -> (forall i, abortv != b_ i) -> (forall i, abortv != y'_ i) -> (forall i, abortv != d_ i) -> abortv != Xv -> abortv != Zv -> abortv
  != Pvar -> abortv != Kv -> abortv != XA -> abortv != XB -> abortv != ZA -> abortv != ZB -> abortv != lamv -> abortv != pECv -> abortv !=
  Xhatv -> abortv != gv -> abortv != tAv -> abortv != tBv -> XA != fv -> Xhatv != fv -> fv != Sv -> Xhatv != Sv -> Sv != Shv -> Sv != Pvar
  -> Shv != Pvar -> tagwall (XA != XB -> XA != ZA -> XA != ZB -> XA != Pvar -> XA != lamv -> XA != pECv -> XA != Xhatv -> XA != gv -> XA !=
  tAv -> XA != tBv -> XB != pECv -> xhwall ((forall s, (forall f, 0 <= unif_pseed s f) /\ \sum_f unif_pseed s f = 1) -> (forall i, cmd_wf qA
  (RNDs i)) -> cmd_wf qA (PEs) -> cmd_wf qA (ECs) -> (forall s, xi s \is psdlf) -> (forall K bits, bits_on K bits = raw_val (key_of (bits_on
  K bits))) -> (forall seed_store ok raw bob, raw = raw_val (key_of raw) -> \sum_g unif_vseed seed_store g * ((ok && (verify_hash g raw ==
  verify_hash g (ir_dec (ir_pub leakEC raw bob) bob)) && (raw != ir_dec (ir_pub leakEC raw bob) bob))%:R) = \sum_x \sum_(x' | x != x')
  ((\sum_g unif_vseed seed_store g * ((ok && (key_of raw == Some x) && (key_of (ir_dec (ir_pub leakEC raw bob) bob) == Some x'))%:R)) *
  collision x x')) -> run_output_mismatch_prob (EVALs qA EA xi) <= \sum_x \sum_(x' | x != x') corr_prob_prog key_of EA xi x x' * collision x
  x'))).
Proof.
  move=> Htf HAS HAH Hay HPa HPy HPb HPy' HPd HPX HPZ HPabort Ha Hy Hb Hy' Hd HX HZ HP HK HXA HXB HZA HZB Hlam HpEC HXhat Hg HtA HtB HXAf HXhatf HfS HXhatS HSS HSP HShP HgtA HgtB HtAtB HtAP HtBP HXAXB HXAZA HXAZB HXAP HXAlam HXAp HXAXhat HXAg HXAtA HXAtB HXBp HXhatg HXhattA HXhattB HXhatP Hseed Hround Hpe Hec Hxi Hraw_bits Hhash. apply: (run_output_mismatch_prob_le_collision_sum (key_count := key_count) (key_of := key_of) (collision := collision) (qA := qA) (xi := xi) EA); try by []. move=> s t K /= _; set h := (t, ((K, bot), bot)); set s0 := start_store s; set s_ann := announce_store (trace_store_seq t (enum 'I_M) s0). set s_pe := paramest_store h s_ann. have Hraw : s_pe XA = raw_val (key_of (s_pe XA)).
  { rewrite /s_pe. apply: (paramest_store_XA_satisfies (P := fun v => v = raw_val (key_of v)) h s_ann); try exact: HXAXB; try exact: HXAZA; try exact: HXAZB; try exact: HXAP; try exact: HXAlam. exact: Hraw_bits. } by rewrite -/h -/s0 -/s_ann -/s_pe; rewrite (Hhash (errcorr_seed_store s_pe) (s_pe abortv == vbool false) (s_pe XA) (s_pe XB) Hraw). Qed.
End BB84Run.
Arguments history_post_store_f_irrel
  {Cv V leakEC M a_ y_ b_ y'_ d_ Xv Zv Kv XA XB ZA ZB lamv pECv Xhatv gv tAv tBv abortv Pvar basisX basisZ outEmpty empty_transcript vbool
    vset vset_of vrat tr_app_rounds tr_app_pe tr_app_ec bits_on test_bits_on err_count ir_pub ir_dec verify_hash}
  t K g f f0 s.
Arguments history_post_coeff_f_irrel
  {R Cv V n k l leakEC M Qtol a_ y_ b_ y'_ d_ Xv Zv Kv XA XB ZA ZB lamv pECv Xhatv gv tAv tBv fv Sv Shv abortv Pvar basisX basisZ outEmpty
    bot empty_transcript vbool vset vset_of vrat tr_app_rounds tr_app_pe tr_app_ec tr_app_pa bits_on test_bits_on err_count err_of
    unif_nsubset_mass ir_pub ir_dec unif_vseed verify_hash unif_pseed privacy_hash}
  t K g f f0 s _ _ _ _.
Arguments key_sample_deviation_event_trace_sets
  {R Cv V n M a_ y_ b_ y'_ d_ Xv Zv Kv XA XB ZA ZB lamv Pvar basisX basisZ outEmpty bot vbool vset vset_of vrat tr_app_rounds tr_app_pe
    bits_on test_bits_on err_count}
  vsetK mu t r i s K.
Arguments key_sample_deviation_event_trace_choices
  {R Cv V n M a_ y_ b_ y'_ d_ Xv Zv Kv XA XB ZA ZB lamv Pvar basisX basisZ outEmpty bot vbool vset vset_of vrat tr_app_rounds tr_app_pe
    bits_on test_bits_on err_count}
  vsetK mu t r i s K.
Arguments key_sample_deviation_event_enum_choices
  {R Cv V n M a_ y_ b_ y'_ d_ Xv Zv Kv XA XB ZA ZB lamv Pvar basisX basisZ outEmpty bot vbool vset vset_of vrat tr_app_rounds tr_app_pe
    bits_on test_bits_on err_count}
  vsetK mu t r i s K.
Arguments key_sample_deviation_event_enum_choices_sum
  {R Cv V n M a_ y_ b_ y'_ d_ Xv Zv Kv XA XB ZA ZB lamv Pvar basisX basisZ outEmpty bot vbool vset vset_of vrat tr_app_rounds tr_app_pe
    bits_on test_bits_on err_count}
  vsetK mu r i s w.
Arguments key_sample_deviation_store_paramest_bits
  {R Cv V n M y_ y'_ Zv Kv XA XB ZA ZB lamv Pvar vset_of vrat tr_app_pe bits_on test_bits_on err_count}
  mu t K g f s.
Section GenericReach.
Variable R : realType.
Notation chsType := (@chsType R). Notation C := (@hermitian.C R).
Variables (L : finType) (HL : L -> chsType).
Variables n k l leakEC M : nat.
Variables ec_bits vseed_count tag_count paseed_count : nat.
Variable Qtol : R.
Notation Cv := (bb84_cvar M). Notation V := (bb84_val M n l ec_bits vseed_count tag_count paseed_count). Notation store := (@store Cv V).
Notation a_ := (@BVa M). Notation y_ := (@BVy M). Notation b_ := (@BVb M). Notation y'_ := (@BVy' M). Notation d_ := (@BVd M).
Notation Xv := (@BVX M). Notation Zv := (@BVZ M). Notation Kv := (@BVK M). Notation XA := (@BVXA M). Notation XB := (@BVXB M).
Notation ZA := (@BVZA M). Notation ZB := (@BVZB M). Notation lamv := (@BVlam M). Notation pECv := (@BVpec M).
Notation Xhatv := (@BVXhat M). Notation gv := (@BVg M). Notation tAv := (@BVtA M). Notation tBv := (@BVtB M). Notation fv := (@BVf M).
Notation Sv := (@BVS M). Notation Shv := (@BVSh M). Notation abortv := (@BVabort M). Notation Pvar := (@BVP M).
Notation basisX := (@bb84_basis_bool_val M n l ec_bits vseed_count tag_count paseed_count false).
Notation basisZ := (@bb84_basis_bool_val M n l ec_bits vseed_count tag_count paseed_count true).
Notation outEmpty := (@bb84_outcome_val M n l ec_bits vseed_count tag_count paseed_count None).
Notation bot := (@bb84_bot_val M n l ec_bits vseed_count tag_count paseed_count).
Notation empty_transcript := (@bb84_empty_transcript_val M n l ec_bits vseed_count tag_count paseed_count).
Notation vbool := (@bb84_bool_val M n l ec_bits vseed_count tag_count paseed_count).
Notation vbit := (@bb84_bit_val M n l ec_bits vseed_count tag_count paseed_count).
Notation vset := (@bb84_set_val M n l ec_bits vseed_count tag_count paseed_count).
Notation vset_of := (@bb84_set_of M n l ec_bits vseed_count tag_count paseed_count).
Notation vrat := (@bb84_error_val M n l ec_bits vseed_count tag_count paseed_count).
Notation tr_app_rounds := (@bb84_tr_app_rounds M n l ec_bits vseed_count tag_count paseed_count).
Notation tr_app_pe := (@bb84_tr_app_pe M n l ec_bits vseed_count tag_count paseed_count).
Notation tr_app_ec := (@bb84_tr_app_ec M n l ec_bits vseed_count tag_count paseed_count).
Notation tr_app_pa := (@bb84_tr_app_pa M n l ec_bits vseed_count tag_count paseed_count).
Notation bits_on := (@bb84_bits_on_val M n l ec_bits vseed_count tag_count paseed_count).
Notation test_bits_on := (@bb84_partial_bits_on_val M n l ec_bits vseed_count tag_count paseed_count).
Notation err_count := (@bb84_err_count_val M n l ec_bits vseed_count tag_count paseed_count).
Notation err_of := (@bb84_error_of M n l ec_bits vseed_count tag_count paseed_count).
Notation unif_nsubset_mass := (@bb84_unif_nsubset_mass R M n l ec_bits vseed_count tag_count paseed_count).
Notation unif_vseed := (@bb84_unif_vseed_mass R M n l ec_bits vseed_count tag_count paseed_count).
Notation unif_pseed := (@bb84_unif_pseed_mass R M n l ec_bits vseed_count tag_count paseed_count).
Notation vread := (@bb84_read_bit M n l ec_bits vseed_count tag_count paseed_count).
Notation ADVq := (@adversary R L HL V). Notation CQs := (@cq_state R L HL Cv V).
Variables (Q : 'I_M -> {set L}) (dev_rho : forall i : 'I_M, V -> V -> 'F[HL]_(Q i)) (dev_meas : forall i : 'I_M, V -> V -> 'F[HL]_(Q i)).
Variables (ipub : 'I_(2 ^ n) -> 'I_(2 ^ n) -> 'I_(2 ^ ec_bits)) (idec : 'I_(2 ^ ec_bits) -> 'I_(2 ^ n) -> 'I_(2 ^ n)).
Variables (vh : 'I_vseed_count -> 'I_(2 ^ n) -> 'I_tag_count) (pa : 'I_paseed_count -> 'I_(2 ^ n) -> 'I_(2 ^ l)).
Notation ir_pub := (bb84_ir_pub_val ipub). Notation ir_dec := (bb84_ir_dec_val idec). Notation verify_hash := (bb84_verify_hash_val vh).
Notation privacy_hash := (bb84_privacy_hash_val pa).
Notation EVALs qA EA xi := (@bb84_eval_scheme R L HL Cv V n k l leakEC M Qtol a_ y_ b_ y'_ d_ Q Xv Zv Kv XA XB ZA ZB lamv pECv Xhatv gv tAv
  tBv fv Sv Shv abortv Pvar basisX basisZ outEmpty bot empty_transcript vbool vbit vset vset_of vrat dev_rho dev_meas tr_app_rounds
  tr_app_pe tr_app_ec tr_app_pa bits_on test_bits_on err_count err_of unif_nsubset_mass ir_pub ir_dec unif_vseed verify_hash unif_pseed
  privacy_hash qA EA xi).
Notation Sstart := (start_store Xv Zv abortv Pvar empty_transcript vbool vset).
Notation Srounds := (rounds_store a_ y_ b_ y'_ d_ Xv Zv basisX basisZ outEmpty vbool vset).
Notation Sann := (announce_store a_ b_ d_ Pvar tr_app_rounds).
Notation Spe := (paramest_store y_ y'_ Zv Kv XA XB ZA ZB lamv Pvar vset_of vrat tr_app_pe bits_on test_bits_on err_count).
Notation Sec := (errcorr_store leakEC XA XB pECv Xhatv gv tAv tBv Pvar tr_app_ec ir_pub ir_dec verify_hash).
Notation TSseq := (trace_store_seq a_ y_ b_ y'_ d_ Xv Zv basisX basisZ outEmpty vbool vset).
Notation TKset := (@trace_key_set V M basisX outEmpty). Notation TTset := (@trace_test_set V M basisZ outEmpty).
Local Lemma gen_Re_gt0 (z : C) : 0 < z -> 0 < complex.Re z.
Proof. by case: z => zr zi; rewrite ltcE /= => /andP[_]. Qed.
Local Lemma gen_Re_ge0 (z : C) : 0 <= z -> 0 <= complex.Re z.
Proof. by case: z => zr zi; rewrite lecE /= => /andP[_]. Qed.
Local Lemma gen_Re_realM (r : R) (z : C) : complex.Re (r%:C * z) = r * complex.Re z.
Proof. by case: z => zr zi /=; rewrite mul0r subr0. Qed.
Local Lemma gen_paramest_store_lamv (h : @run_history V M) (s : store) : Zv != Kv -> Zv != XA -> Zv != XB -> Zv != ZA -> Zv != ZB -> Zv !=
  Pvar -> ZA != ZB -> ZA != Pvar -> ZB != Pvar -> (forall i, y_ i != Kv) -> (forall i, y_ i != XA) -> (forall i, y_ i != XB) -> (forall i,
  y'_ i != Kv) -> (forall i, y'_ i != XA) -> (forall i, y'_ i != XB) -> (forall i, y'_ i != ZA) -> Spe h s lamv = vrat (err_count
  (test_bits_on (vset_of (s Zv)) (fun i => s (y_ i))) (test_bits_on (vset_of (s Zv)) (fun i => s (y'_ i)))) #|vset_of (s Zv)|.
Proof.
  move=> HZK HZXA HZXB HZZA HZZB HZP HZAZB HZAP HZBP HyK HyXA HyXB Hy'K Hy'XA Hy'XB Hy'ZA; rewrite /paramest_store. set s1 := store_set s Kv (hist_K h); set s2 := store_set s1 XA (bits_on (vset_of (s1 Kv)) (fun i => s1 (y_ i))). set s3 := store_set s2 XB (bits_on (vset_of (s2 Kv)) (fun i => s2 (y'_ i))). set s4 := store_set s3 ZA (test_bits_on (vset_of (s3 Zv)) (fun i => s3 (y_ i))). set s5 := store_set s4 ZB (test_bits_on (vset_of (s4 Zv)) (fun i => s4 (y'_ i))). set s6 := store_set s5 Pvar (tr_app_pe (s5 Kv) (s5 ZA) (s5 ZB) (s5 Pvar)); rewrite store_set_same. have Hs3Zv : s3 Zv = s Zv by rewrite /s3 store_set_other // /s2 store_set_other // /s1 store_set_other. have Hs4Zv : s4 Zv = s Zv by rewrite /s4 store_set_other. have Hs6Zv : s6 Zv = s Zv by rewrite /s6 store_set_other // /s5 store_set_other.
    have Hs3y : forall i, s3 (y_ i) = s (y_ i) by move=> i; rewrite /s3 store_set_other // /s2 store_set_other // /s1 store_set_other. have Hs4y' : forall i, s4 (y'_ i) = s (y'_ i).
  { by move=> i; rewrite /s4 store_set_other // /s3 store_set_other // /s2 store_set_other // /s1 store_set_other. } have Hs6ZA : s6 ZA = test_bits_on (vset_of (s Zv)) (fun i => s (y_ i)).
  { rewrite /s6 store_set_other // /s5 store_set_other // /s4 store_set_same. rewrite Hs3Zv; congr (test_bits_on _ _). by apply: funext => i; rewrite Hs3y. } have Hs6ZB : s6 ZB = test_bits_on (vset_of (s Zv)) (fun i => s (y'_ i)).
  { rewrite /s6 store_set_other // /s5 store_set_same. rewrite Hs4Zv; congr (test_bits_on _ _). by apply: funext => i; rewrite Hs4y'. } by rewrite Hs6ZA Hs6ZB Hs6Zv. Qed.
Local Lemma gen_paramest_store_XA (h : @run_history V M) (s : store) : XA != XB -> XA != ZA -> XA != ZB -> XA != Pvar -> XA != lamv -> Kv !=
  XA -> Kv != XB -> Kv != ZA -> Kv != ZB -> Kv != Pvar -> Kv != lamv -> (forall i, y_ i != Kv) -> Spe h s XA = bits_on (vset_of (hist_K h))
  (fun i => s (y_ i)).
Proof. move=> HXAXB HXAZA HXAZB HXAP HXAlam HKXA HKXB HKZA HKZB HKP HKlam HyK; rewrite paramest_store_XA //; rewrite store_set_same. congr (bits_on _ _). by apply: funext => i; rewrite store_set_other. Qed.
Local Lemma gen_paramest_store_XB (h : @run_history V M) (s : store) : XB != ZA -> XB != ZB -> XB != Pvar -> XB != lamv -> Kv != XA -> Kv !=
  XB -> Kv != ZA -> Kv != ZB -> Kv != Pvar -> Kv != lamv -> XA != XB -> (forall i, y'_ i != Kv) -> (forall i, y'_ i != XA) -> Spe h s XB =
  bits_on (vset_of (hist_K h)) (fun i => s (y'_ i)).
Proof. move=> HXBZA HXBZB HXBP HXBlam HKXA HKXB HKZA HKZB HKP HKlam HXAXB Hy'K Hy'XA; rewrite paramest_store_XB //. rewrite store_set_other // store_set_same. congr (bits_on _ _). by apply: funext => i; rewrite store_set_other // store_set_other. Qed.
Local Lemma gen_errcorr_store_tAv (h : @run_history V M) (s : store) : tAv != tBv -> tAv != Pvar -> gv != tAv -> XA != gv -> XA != pECv ->
  XA != Xhatv -> Sec h s tAv = verify_hash (hist_g h) (s XA).
Proof. move=> HtAtB HtAP HgtA HXAg HXApec HXAXhat; rewrite errcorr_store_tAv //; rewrite store_set_same store_set_other //. by rewrite errcorr_seed_store_other. Qed.
Local Lemma gen_errcorr_store_tBv (h : @run_history V M) (s : store) : tBv != Pvar -> gv != tAv -> Xhatv != gv -> Xhatv != tAv -> XB != pECv
  -> Sec h s tBv = verify_hash (hist_g h) (ir_dec (ir_pub leakEC (s XA) (s XB)) (s XB)).
Proof. move=> HtBP HgtA HXhg HXhtA HXBpec; rewrite errcorr_store_tBv //. by rewrite store_set_other // store_set_same store_set_other // store_set_other //; rewrite errcorr_seed_store_Xhatv. Qed.
Local Lemma gen_round_choice_so_psd (qA : {set L}) (EA : ADVq qA) (c : @round_choice V) (i : 'I_M) (p : V) (rho : 'F[HL]_setT) : (forall (i'
  : 'I_M) (a y : V), dev_rho i' a y \is psdlf) -> rho \is psdlf -> round_choice_so dev_rho dev_meas EA c i p rho \is psdlf.
Proof. move=> Hdev Hrho; rewrite /round_choice_so !comp_soE; apply: cp_psdP. apply: cp_psdP; apply: appendso_psd. - exact: Hdev. - exact: cp_psdP Hrho. Qed.
Local Lemma gen_hist_so_psd (qA : {set L}) (EA : ADVq qA) (h : @run_history V M) (rho : 'F[HL]_setT) : (forall (i : 'I_M) (a y : V), dev_rho
  i a y \is psdlf) -> rho \is psdlf -> hist_so empty_transcript dev_rho dev_meas EA h rho \is psdlf.
Proof. move=> Hdev Hrho; rewrite -trace_so_seq_enum. elim: (enum 'I_M) rho Hrho => [|j r IHr] rho Hrho. - by rewrite /trace_so_seq big_nil id_soE. - rewrite /trace_so_seq big_cons comp_sorE; apply: IHr. exact: gen_round_choice_so_psd. Qed.
Local Lemma gen_indicator_gt0 (b : bool) : b -> 0 < ((b%:R : R)).
Proof. by move=> ->; rewrite ltr01. Qed.
Local Ltac bvne := apply: bb84_cvar_inr_neq; rewrite -val_eqE /= !inordK.
Lemma run_pass_prob_reachable (qA : {set L}) (EA : ADVq qA) (xi : CQs) (h0 : @run_history V M) (s0 : store) : (forall s, xi s \is psdlf) ->
  (forall (i : 'I_M) (a y : V), dev_rho i a y \is psdlf) -> (0 < M)%N -> 0 <= Qtol -> (forall p y, idec p y = y) -> (forall i : 'I_M,
  liftfso (EA (Q i) empty_transcript) = idso) -> \Tr (xi s0) = 1 -> (forall i : 'I_M, (0 : C) < \Tr (formlf (dev_meas i (choice_b (h0.1 i))
  (choice_y' (h0.1 i))) (dev_rho i (choice_a (h0.1 i)) (choice_y (h0.1 i))))) -> (forall i : 'I_M, choice_y' (h0.1 i) != outEmpty) -> (n <=
  #|@trace_key_set V M basisX outEmpty h0.1|)%N -> (k <= #|@trace_test_set V M basisZ outEmpty h0.1|)%N -> (forall i : 'I_M, vread (choice_y
  (h0.1 i)) = Some false) -> (forall i : 'I_M, vread (choice_y' (h0.1 i)) = Some false) -> (forall (i : 'I_M) (s : store), 0 <
  round_choice_weight R n k basisX basisZ vbit (h0.1 i) s) -> 0 < unif_nsubset_mass n (@trace_key_set V M basisX outEmpty h0.1) h0.2.1.1 ->
  (forall s : store, 0 < unif_vseed s h0.2.1.2) -> (forall s : store, 0 < unif_pseed s h0.2.2) -> 0 < run_pass_prob abortv vbool (EVALs qA
  EA xi).
Proof.
  move=> Hxipsd Hdevpsd HM HQtol Hidec Hlift HZ1 Hfac Hdet Hkeyle Htestle Hready Hready' Hwt Hkmass Hgm Hfm. have HaX : forall i, a_ i != Xv by move=> i. have HaZ : forall i, a_ i != Zv by move=> i. have HyX : forall i, y_ i != Xv by move=> i. have HyZ : forall i, y_ i != Zv by move=> i. have HbX : forall i, b_ i != Xv by move=> i. have HbZ : forall i, b_ i != Zv by move=> i. have Hy'X : forall i, y'_ i != Xv by move=> i. have Hy'Z : forall i, y'_ i != Zv by move=> i. have HdX : forall i, d_ i != Xv by move=> i. have HdZ : forall i, d_ i != Zv by move=> i. have HyK : forall i, y_ i != Kv by move=> i. have HyXA : forall i, y_ i != XA by move=> i. have HyXB : forall i, y_ i != XB by move=> i. have HyZA : forall i, y_ i != ZA by move=> i. have HyZB : forall i, y_ i != ZB by move=> i. have HyP : forall i, y_ i != Pvar by move=> i. have Hylam : forall i, y_ i != lamv by move=> i. have Hy'K : forall i, y'_ i != Kv by move=> i. have Hy'XA : forall i, y'_ i != XA by move=> i. have Hy'XB : forall i, y'_ i != XB by move=> i. have Hy'ZA : forall i, y'_ i != ZA by move=> i. have Hy'ZB : forall i, y'_ i != ZB by move=> i. have Hy'P : forall i, y'_ i != Pvar by move=> i. have Hy'lam : forall i, y'_ i != lamv by move=> i.
    have Hay : forall i, a_ i != y_ i by move=> i. have HPa : forall i, Pvar != a_ i by move=> i. have HPy : forall i, Pvar != y_ i by move=> i. have HPb : forall i, Pvar != b_ i by move=> i. have HPy' : forall i, Pvar != y'_ i by move=> i. have HPd : forall i, Pvar != d_ i by move=> i. have HAa : forall i, abortv != a_ i by move=> i. have HAy : forall i, abortv != y_ i by move=> i. have HAb : forall i, abortv != b_ i by move=> i. have HAy' : forall i, abortv != y'_ i by move=> i. have HAd : forall i, abortv != d_ i by move=> i. have Haa : forall i j : 'I_M, i != j -> a_ i != a_ j by move=> i j Hij; exact: Hij. have Hyy : forall i j : 'I_M, i != j -> y_ i != y_ j by move=> i j Hij; exact: Hij. have Hbb : forall i j : 'I_M, i != j -> b_ i != b_ j by move=> i j Hij; exact: Hij. have Hy'y' : forall i j : 'I_M, i != j -> y'_ i != y'_ j by move=> i j Hij; exact: Hij. have Hdd : forall i j : 'I_M, i != j -> d_ i != d_ j by move=> i j Hij; exact: Hij. have Hay2 : forall i j, a_ i != y_ j by move=> i j. have Hab : forall i j, a_ i != b_ j by move=> i j. have Hay'2 : forall i j, a_ i != y'_ j by move=> i j. have Had : forall i j, a_ i != d_ j by move=> i j. have Hyb : forall i j, y_ i != b_ j by move=> i j.
    have Hyy' : forall i j, y_ i != y'_ j by move=> i j. have Hyd : forall i j, y_ i != d_ j by move=> i j. have Hby' : forall i j, b_ i != y'_ j by move=> i j. have Hbd : forall i j, b_ i != d_ j by move=> i j. have Hy'd : forall i j, y'_ i != d_ j by move=> i j. have HXZ : Xv != Zv by bvne. have HXK : Xv != Kv by bvne. have HXXA : Xv != XA by bvne. have HXXB : Xv != XB by bvne. have HXZA : Xv != ZA by bvne.
    have HXZB : Xv != ZB by bvne. have HXlam : Xv != lamv by bvne. have HXP : Xv != Pvar by bvne. have HZK : Zv != Kv by bvne. have HZXA : Zv != XA by bvne. have HZXB : Zv != XB by bvne. have HZZA : Zv != ZA by bvne. have HZZB : Zv != ZB by bvne. have HZlam : Zv != lamv by bvne. have HZP : Zv != Pvar by bvne. have HKXA : Kv != XA by bvne. have HKXB : Kv != XB by bvne. have HKZA : Kv != ZA by bvne. have HKZB : Kv != ZB by bvne. have HKP : Kv != Pvar by bvne. have HKlam : Kv != lamv by bvne. have HXAXB : XA != XB by bvne. have HXAZA : XA != ZA by bvne. have HXAZB : XA != ZB by bvne. have HXAP : XA != Pvar by bvne. have HXAlam : XA != lamv by bvne. have HXApec : XA != pECv by bvne. have HXAXhat : XA != Xhatv by bvne. have HXAg : XA != gv by bvne. have HXAtA : XA != tAv by bvne. have HXAtB : XA != tBv by bvne.
    have HXBZA : XB != ZA by bvne. have HXBZB : XB != ZB by bvne. have HXBP : XB != Pvar by bvne. have HXBlam : XB != lamv by bvne. have HXBpec : XB != pECv by bvne. have HZAZB : ZA != ZB by bvne. have HZAP : ZA != Pvar by bvne. have HZAlam : ZA != lamv by bvne. have HZBP : ZB != Pvar by bvne. have HZBlam : ZB != lamv by bvne. have HgtA : gv != tAv by bvne. have HgtB : gv != tBv by bvne. have HgP : gv != Pvar by bvne. have HtAtB : tAv != tBv by bvne. have HtAP : tAv != Pvar by bvne. have HtBP : tBv != Pvar by bvne. have HXhg : Xhatv != gv by bvne. have HXhtA : Xhatv != tAv by bvne. have HXhtB : Xhatv != tBv by bvne. have HXhP : Xhatv != Pvar by bvne. have HAX : abortv != Xv by bvne. have HAZ : abortv != Zv by bvne. have HAP : abortv != Pvar by bvne. have HAK : abortv != Kv by bvne. have HAXA : abortv != XA by bvne. have HAXB : abortv != XB by bvne. have HAZA : abortv != ZA by bvne. have HAZB : abortv != ZB by bvne. have HAlam : abortv != lamv by bvne. have HApec : abortv != pECv by bvne. have HAXhat : abortv != Xhatv by bvne. have HAg : abortv != gv by bvne. have HAtA : abortv != tAv by bvne. have HAtB : abortv != tBv by bvne. have HAf : abortv != fv by bvne. have HAS : abortv != Sv by bvne. have HASh : abortv != Shv by bvne. have HPX : Pvar != Xv by bvne. have HPZ : Pvar != Zv by bvne. have HPabort : Pvar != abortv by bvne. have Htf : vbool true != vbool false by []. have HvsetK : forall X : {set 'I_M}, vset_of (vset X) = X by move=> X. have Hnsub0 : forall m X v, 0 <= unif_nsubset_mass m X v by move=> *; exact: bb84_unif_nsubset_mass_nonneg. have Hvs0 : forall s v, 0 <= unif_vseed s v by move=> *; exact: bb84_unif_vseed_mass_nonneg. have Hps0 : forall s v, 0 <= unif_pseed s v by move=> *; exact: bb84_unif_pseed_mass_nonneg. have Hbits_ext : forall (K : {set 'I_M}) (f g : 'I_M -> V), (forall i, i \in K -> vread (f i) = vread (g i)) -> bits_on K f = bits_on K g.
  { move=> K f g Hfg; rewrite /bb84_bits_on_val. case: ifP => // HK. congr (bb84_raw_key_val (Some (bitstring_to_ord _))); apply: funext => j. case Hj: (bb84_selected_index K j) => [i|//]. by rewrite Hfg //; exact: bb84_selected_index_mem Hj. } have Herr_matched : forall (K : {set 'I_M}) (f g : 'I_M -> V), (forall i, i \in K -> vread (f i) = Some false) -> (forall i, i \in K -> vread (g i) = Some false) -> err_count (test_bits_on K f) (test_bits_on K g) = 0%N.
  { move=> K f g Hf Hg; rewrite (bb84_err_count_partial_bits_on_val K f g). apply/eqP; rewrite cards_eq0; apply/eqP. apply/setP=> i; rewrite !inE. case Hi: (i \in K) => //=. by rewrite Hf // Hg // eqxx. } have Herr0 : forall z : nat, err_of (vrat (err_count (test_bits_on (@trace_test_set V M basisZ outEmpty h0.1) (fun i => choice_y (h0.1 i))) (test_bits_on (@trace_test_set V M basisZ outEmpty h0.1) (fun i => choice_y' (h0.1 i)))) z) = 0%N.
  { move=> z; rewrite Herr_matched.
    - by rewrite /bb84_error_of /bb84_error_val /= inordK.
    - by move=> i _; rewrite Hready.
    - by move=> i _; rewrite Hready'. } have Hird : forall (K : {set 'I_M}) (f : 'I_M -> V), ir_dec (ir_pub leakEC (bits_on K f) (bits_on K f)) (bits_on K f) = bits_on K f.
  { move=> K f; rewrite /bb84_bits_on_val. case: (#|K| == n).
    - by rewrite /bb84_ir_pub_val /bb84_ir_dec_val !bb84_raw_key_of_val /= Hidec.
    - by rewrite /bb84_ir_pub_val /bb84_ir_dec_val !bb84_raw_key_of_val /=. } have [r0 [iM Henum]] : exists r0 iM, enum 'I_M = rcons r0 iM.
  { move: (size_enum_ord M); case/lastP: (enum 'I_M) => [|r0 iM] Hsz; [by move: HM; rewrite -Hsz ltn0 | by exists r0, iM]. } have HraE : forall i, TSseq h0.1 (enum 'I_M) (Sstart s0) (a_ i) = choice_a (h0.1 i).
  { by move=> i; apply: trace_store_seq_enum_a; [exact: bot | move=> j Hji; apply: Haa; rewrite eq_sym | move=> j; exact: Hay2 | move=> j; exact: Hab | move=> j; exact: Hay'2 | move=> j; exact: Had | exact: HaX | exact: HaZ]. } have HrbE : forall i, TSseq h0.1 (enum 'I_M) (Sstart s0) (b_ i) = choice_b (h0.1 i).
  { by move=> i; apply: trace_store_seq_enum_b; [exact: bot | move=> j; rewrite eq_sym; exact: Hab | move=> j; rewrite eq_sym; exact: Hyb | move=> j Hji; apply: Hbb; rewrite eq_sym | move=> j; exact: Hby' | move=> j; exact: Hbd | exact: HbX | exact: HbZ]. } have HrdE : forall i, TSseq h0.1 (enum 'I_M) (Sstart s0) (d_ i) = vbool (trace_detected outEmpty h0.1 i).
  { by move=> i; apply: trace_store_seq_enum_d; [exact: bot | move=> j; rewrite eq_sym; exact: Had | move=> j; rewrite eq_sym; exact: Hyd | move=> j; rewrite eq_sym; exact: Hbd | move=> j; rewrite eq_sym; exact: Hy'd | move=> j Hji; apply: Hdd; rewrite eq_sym | exact: HdX | exact: HdZ]. } have HXset : vset_of (Sann (Srounds h0 (Sstart s0)) Xv) = TKset h0.1.
  { rewrite -trace_store_seq_enum. exact: (announce_store_trace_key_set tr_app_rounds HvsetK Henum Htf HXZ HPX HraE HrbE HrdE HaX HaZ HbX HbZ HdX HdZ). } have HZset : vset_of (Sann (Srounds h0 (Sstart s0)) Zv) = TTset h0.1.
  { rewrite -trace_store_seq_enum. exact: (announce_store_trace_test_set tr_app_rounds HvsetK Henum Htf HPZ HraE HrbE HrdE HaX HaZ HbX HbZ HdX HdZ). } have HryE : forall i, TSseq h0.1 (enum 'I_M) (Sstart s0) (y_ i) = choice_y (h0.1 i).
  { by move=> i; apply: trace_store_seq_enum_y; [exact: bot | move=> j Hji; rewrite eq_sym; apply: Hay2 | move=> j; exact: Hyb | move=> j Hji; apply: Hyy; rewrite eq_sym | move=> j; exact: Hyy' | move=> j; exact: Hyd | exact: HyX | exact: HyZ]. } have Hry'E : forall i, TSseq h0.1 (enum 'I_M) (Sstart s0) (y'_ i) = choice_y' (h0.1 i).
  { by move=> i; apply: trace_store_seq_enum_y'; [exact: bot | move=> j; rewrite eq_sym; apply: Hay'2 | move=> j; rewrite eq_sym; apply: Hyy' | move=> j; rewrite eq_sym; apply: Hby' | move=> j Hji; apply: Hy'y'; rewrite eq_sym | move=> j; exact: Hy'd | exact: Hy'X | exact: Hy'Z]. } have HannY : forall i, Sann (Srounds h0 (Sstart s0)) (y_ i) = choice_y (h0.1 i).
  { move=> i. rewrite announce_store_other; last exact: HyP. by rewrite -trace_store_seq_enum HryE. } have HannY' : forall i, Sann (Srounds h0 (Sstart s0)) (y'_ i) = choice_y' (h0.1 i).
  { move=> i. rewrite announce_store_other; last exact: Hy'P. by rewrite -trace_store_seq_enum Hry'E. } have Hpe : ~~ pe_failed n k Qtol Xv Zv lamv vset_of err_of (Spe h0 (Sann (Srounds h0 (Sstart s0)))).
  { rewrite /pe_failed /replay_pe_fail negb_or negbK; apply/andP; split.
    - rewrite /replay_sift_ok; apply/andP; split.
      + rewrite paramest_store_other // HXset; exact: Hkeyle.
      + rewrite paramest_store_other // HZset; exact: Htestle.
    - rewrite /replay_pe_error_high paramest_store_other // HZset gen_paramest_store_lamv // HZset. have -> : (fun i => Sann (Srounds h0 (Sstart s0)) (y_ i)) = (fun i => choice_y (h0.1 i)) by apply: funext => i; rewrite HannY. have -> : (fun i => Sann (Srounds h0 (Sstart s0)) (y'_ i)) = (fun i => choice_y' (h0.1 i)) by apply: funext => i; rewrite HannY'. rewrite Herr0 -leNgt; apply: mulr_ge0; first exact: HQtol. exact: ler0n. } have Hbits : bits_on (vset_of (hist_K h0)) (fun i => choice_y (h0.1 i)) = bits_on (vset_of (hist_K h0)) (fun i => choice_y' (h0.1 i)).
  { apply: Hbits_ext => i _. by rewrite Hready Hready'. } have Hverify : ~~ (Sec h0 (Spe h0 (Sann (Srounds h0 (Sstart s0)))) tAv != Sec h0 (Spe h0 (Sann (Srounds h0 (Sstart s0)))) tBv).
  { rewrite negbK gen_errcorr_store_tAv // gen_errcorr_store_tBv //; rewrite gen_paramest_store_XA // gen_paramest_store_XB //. have -> : (fun i => Sann (Srounds h0 (Sstart s0)) (y_ i)) = (fun i => choice_y (h0.1 i)) by apply: funext => i; rewrite HannY. have -> : (fun i => Sann (Srounds h0 (Sstart s0)) (y'_ i)) = (fun i => choice_y' (h0.1 i)) by apply: funext => i; rewrite HannY'. by rewrite Hbits Hird eqxx. } rewrite run_pass_prob_decomp; [ | exact: Hay | exact: HPa | exact: HPy | exact: HPb | exact: HPy' | exact: HPd | exact: HPX | exact: HPZ | exact: HPabort]. rewrite (bigD1 s0) //=; rewrite [in X in 0 < X + _](bigD1 h0) //=; apply: ltr_wpDr.
  { apply: sumr_ge0 => s _; apply: sumr_ge0 => h _. apply: mulr_ge0; first by case: (_ == _). apply: gen_Re_ge0; apply: psdlf_trlf; apply: psdlfZ.
    - rewrite lecR; apply: hist_wt_nonneg.
      + by move=> *; exact: Hnsub0.
      + by move=> *; exact: Hvs0.
      + by move=> *; exact: Hps0.
    - by apply: gen_hist_so_psd; [exact: Hdevpsd | exact: Hxipsd]. } apply: ltr_wpDr.
  { apply: sumr_ge0 => h _. apply: mulr_ge0; first by case: (_ == _). apply: gen_Re_ge0; apply: psdlf_trlf; apply: psdlfZ.
    - rewrite lecR; apply: hist_wt_nonneg.
      + by move=> *; exact: Hnsub0.
      + by move=> *; exact: Hvs0.
      + by move=> *; exact: Hps0.
    - by apply: gen_hist_so_psd; [exact: Hdevpsd | exact: Hxipsd]. } apply: mulr_gt0.
  { apply: gen_indicator_gt0. by apply: final_store_privamp_pass; [exact: Hpe | exact: Hverify | exact: HAa | exact: HAy | exact: HAb | exact: HAy' | exact: HAd | exact: HAX | exact: HAZ | exact: HAP | exact: HAK | exact: HAXA | exact: HAXB | exact: HAZA | exact: HAZB | exact: HAlam | exact: HApec | exact: HAXhat | exact: HAg | exact: HAtA | exact: HAtB | exact: HAf | exact: HAS | exact: HASh]. } rewrite linearZ /= gen_Re_realM; apply: mulr_gt0.
  { by apply: hist_wt_privamp_branch_gt0; [apply: round_samples_weight_gt0 => i; exact: Hwt | rewrite /key_sample_mass HXset Hkeyle; exact: Hkmass | exact: Hpe | exact: Hgm | exact: Hverify | exact: Hfm]. } apply: gen_Re_gt0. rewrite -trace_so_seq_enum; rewrite trace_so_seq_trace_id; last exact: Hlift. by rewrite HZ1 mulr1; apply: prodr_gt0 => i _; exact: Hfac. Qed.
End GenericReach.
Arguments run_pass_prob_reachable {R L HL n k l leakEC M ec_bits vseed_count tag_count paseed_count Qtol Q dev_rho dev_meas ipub idec vh pa
  qA EA xi} h0 s0.
