(* stat.v -- BB84 program-side sampling statistics                      *)
(* Module: qkd.example.stat                                             *)
(* Classical sampling-statistics support for the concrete BB84 run,     *)
(* consumed by the theorem layer in example.v.                          *)
From mathcomp Require Import all_boot all_order all_algebra finmap fingroup perm.
From mathcomp.classical Require Import boolp.
From mathcomp.reals Require Import reals.
From mathcomp.real_closed Require Import mxtens.
From quantum.external Require Import spectral complex.
From quantum Require Import mcextra mcaextra notation hermitian quantum cpo mxpred extnum ctopology svd mxnorm hspace.
From quantum.dirac Require Import hstensor.

Import Order.TTheory GRing.Theory Num.Theory Num.Def MxLownerOrder.
Import VectorInternalTheory.

From utils Require Import bitstr prob exports.
From utils.mx Require Import prop.
From qkd.bb84 Require Import def model prop.
From qkd.protocol Require Import syntax semantics qkd_cmd.
From qkd.example Require Import device program run.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Local Open Scope qkd_scope.
Section ConcreteBB84ProgramStatistics.
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
Notation bool_val := (@bb84_bool_val M (bb84_n P) (bb84_l P) (cd_ir_bits dev) (cd_vseed_count dev) (cd_tag_count dev)
  (cd_paseed_count dev)).
Notation outcome_val := (@bb84_outcome_val M (bb84_n P) (bb84_l P) (cd_ir_bits dev) (cd_vseed_count dev) (cd_tag_count dev)
  (cd_paseed_count dev)).
Notation set_val := (@bb84_set_val M (bb84_n P) (bb84_l P) (cd_ir_bits dev) (cd_vseed_count dev) (cd_tag_count dev) (cd_paseed_count dev)).
Notation bot_val := (@bb84_bot_val M (bb84_n P) (bb84_l P) (cd_ir_bits dev) (cd_vseed_count dev) (cd_tag_count dev) (cd_paseed_count dev)).
Notation set_of := (@bb84_set_of M (bb84_n P) (bb84_l P) (cd_ir_bits dev) (cd_vseed_count dev) (cd_tag_count dev) (cd_paseed_count dev)).
Notation pX := ((1 + Num.sqrt ((bb84_k P)%:R / (bb84_n P)%:R))^-1).
Notation tr_app_rounds := (@bb84_tr_app_rounds M (bb84_n P) (bb84_l P) (cd_ir_bits dev) (cd_vseed_count dev) (cd_tag_count dev)
  (cd_paseed_count dev)).
Notation tr_app_pe := (@bb84_tr_app_pe M (bb84_n P) (bb84_l P) (cd_ir_bits dev) (cd_vseed_count dev) (cd_tag_count dev)
  (cd_paseed_count dev)).
Notation unif_nsubset_mass := (@bb84_unif_nsubset_mass R M (bb84_n P) (bb84_l P) (cd_ir_bits dev) (cd_vseed_count dev) (cd_tag_count dev)
  (cd_paseed_count dev)).
Notation basis_value := (@bb84_program_basis_value R P q dev).
Notation device_rho := (@bb84_program_device_rho R P q LE HE LB HB dev).
Notation trace_key_set_of := (@trace_key_set V M (basis_value BasisX) (outcome_val None)).
Notation trace_test_set_of := (@trace_test_set V M (basis_value BasisZ) (outcome_val None)).
Lemma enum_ord_rcons (HM : (0 < M)%N) : exists r i, enum 'I_M = rcons r i.
Proof. case Henum: (enum 'I_M) => [|i r]. { have Hsize := size_enum_ord M. rewrite Henum in Hsize. by move: HM; rewrite -Hsize ltnn. } by exists (belast i r), (last i r); rewrite lastI. Qed.
Lemma announce_trace_key_set (t : round_trace V M) (s : store) : let r := enum 'I_M in let s0 := @start_store Cv V M (@BVX M) (@BVZ M)
    (@BVabort M) (@BVP M) bb84_empty_transcript_val bool_val set_val s in let s_ann := announce_store (@BVa M) (@BVb M) (@BVd M) (@BVP M)
    tr_app_rounds (trace_store_seq (@BVa M) (@BVy M) (@BVb M) (@BVy' M) (@BVd M) (@BVX M) (@BVZ M) (basis_value BasisX) (basis_value BasisZ)
    (outcome_val None) bool_val set_val t r s0) in (0 < M)%N -> set_of (s_ann (@BVX M)) = trace_key_set_of t.
Proof.
  move=> r s0 s_ann HMpos; have [r0 [i0 Henum]] := enum_ord_rcons HMpos.
  rewrite /s_ann (announce_store_trace_key_set tr_app_rounds (@bb84_set_of_val M (bb84_n P) (bb84_l P) (cd_ir_bits dev) (cd_vseed_count dev) (cd_tag_count dev) (cd_paseed_count dev)) Henum).
  - by [].
  - exact: bb84_bool_val_neq.
  - by rewrite /BVX /BVZ; apply/eqP=> H; case: H => Hord; move/eqP: Hord; rewrite -val_eqE /= !inordK.
  - by rewrite /BVP /BVX; apply/eqP=> H; case: H => Hord; move/eqP: Hord; rewrite -val_eqE /= !inordK.
  - move=> j; apply: (@trace_store_seq_enum_a Cv V M (@BVa M) (@BVy M) (@BVb M) (@BVy' M) (@BVd M) (@BVX M) (@BVZ M) (basis_value BasisX) (basis_value BasisZ) (outcome_val None) bot_val bool_val set_val t s0 j).
    + by move=> h Hhj; rewrite eq_sym.
    1,2,3,4: by move=> h.
    1,2: by [].
  - move=> j; apply: (@trace_store_seq_enum_b Cv V M (@BVa M) (@BVy M) (@BVb M) (@BVy' M) (@BVd M) (@BVX M) (@BVZ M) (basis_value BasisX) (basis_value BasisZ) (outcome_val None) bot_val bool_val set_val t s0 j).
    1,2: by move=> h.
    + by move=> h Hhj; rewrite eq_sym.
    1,2: by move=> h.
    1,2: by [].
  - move=> j; apply: (@trace_store_seq_enum_d Cv V M (@BVa M) (@BVy M) (@BVb M) (@BVy' M) (@BVd M) (@BVX M) (@BVZ M) (basis_value BasisX) (basis_value BasisZ) (outcome_val None) bot_val bool_val set_val t s0 j).
    1,2,3,4: by move=> h.
    + by move=> h Hhj; rewrite eq_sym.
    1,2: by [].
  1,2,3,4,5,6: by move=> j. Qed.
Lemma announce_trace_test_set (t : round_trace V M) (s : store) : let r := enum 'I_M in let s0 := @start_store Cv V M (@BVX M) (@BVZ M)
    (@BVabort M) (@BVP M) bb84_empty_transcript_val bool_val set_val s in let s_ann := announce_store (@BVa M) (@BVb M) (@BVd M) (@BVP M)
    tr_app_rounds (trace_store_seq (@BVa M) (@BVy M) (@BVb M) (@BVy' M) (@BVd M) (@BVX M) (@BVZ M) (basis_value BasisX) (basis_value BasisZ)
    (outcome_val None) bool_val set_val t r s0) in (0 < M)%N -> set_of (s_ann (@BVZ M)) = trace_test_set_of t.
Proof.
  move=> r s0 s_ann HMpos; have [r0 [i0 Henum]] := enum_ord_rcons HMpos.
  rewrite /s_ann (announce_store_trace_test_set tr_app_rounds (@bb84_set_of_val M (bb84_n P) (bb84_l P) (cd_ir_bits dev) (cd_vseed_count dev) (cd_tag_count dev) (cd_paseed_count dev)) Henum).
  - by [].
  - exact: bb84_bool_val_neq.
  - by rewrite /BVP /BVZ; apply/eqP=> H; case: H => Hord; move/eqP: Hord; rewrite -val_eqE /= !inordK.
  - move=> j; apply: (@trace_store_seq_enum_a Cv V M (@BVa M) (@BVy M) (@BVb M) (@BVy' M) (@BVd M) (@BVX M) (@BVZ M) (basis_value BasisX) (basis_value BasisZ) (outcome_val None) bot_val bool_val set_val t s0 j).
    + by move=> h Hhj; rewrite eq_sym.
    1,2,3,4: by move=> h.
    1,2: by [].
  - move=> j; apply: (@trace_store_seq_enum_b Cv V M (@BVa M) (@BVy M) (@BVb M) (@BVy' M) (@BVd M) (@BVX M) (@BVZ M) (basis_value BasisX) (basis_value BasisZ) (outcome_val None) bot_val bool_val set_val t s0 j).
    1,2: by move=> h.
    + by move=> h Hhj; rewrite eq_sym.
    1,2: by move=> h.
    1,2: by [].
  - move=> j; apply: (@trace_store_seq_enum_d Cv V M (@BVa M) (@BVy M) (@BVb M) (@BVy' M) (@BVd M) (@BVX M) (@BVZ M) (basis_value BasisX) (basis_value BasisZ) (outcome_val None) bot_val bool_val set_val t s0 j).
    1,2,3,4: by move=> h.
    + by move=> h Hhj; rewrite eq_sym.
    1,2: by [].
  1,2,3,4,5,6: by move=> j. Qed.
End ConcreteBB84ProgramStatistics.
Import Order.TTheory GRing.Theory Num.Theory Num.Def MxLownerOrder.
Import VectorInternalTheory.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Local Open Scope qkd_scope.
Section LabelSet.
Variable L : finType.
Lemma bb84_setT_diff_complement (A : {set L}) : mathcomp.boot.finset.setD (setTfor L) (mathcomp.boot.finset.setC A) = A.
Proof. by apply/setP => x; rewrite !inE andbT negbK. Qed.
End LabelSet.
Section PrepDenotation.
Variable R : realType.
Notation chsType := (@chsType R).
Variables (L : finType) (HL : L -> chsType).
Variables Cv V : finType.
Notation store := (@store Cv V).
Variables n k l leakEC M : nat.
Variables Qtol eps_c : R.
Variables (a_ y_ b_ y'_ d_ : 'I_M -> Cv).
Variable Q : 'I_M -> {set L}.
Variables Xv Zv : Cv.
Variables basisX basisZ outEmpty : V.
Variables (vbool : bool -> V) (vbit : bool -> V) (vset : {set 'I_M} -> V).
Variables (dev_rho : forall i : 'I_M, V -> V -> 'F[HL]_(Q i)) (dev_meas : forall i : 'I_M, V -> V -> 'F[HL]_(Q i)).

End PrepDenotation.

Section CertifiedPreparation.
Variable R : realType.
Notation C := (@hermitian.C R).
Variables (P : @bb84_protocol R) (q : R) (dev : bb84_certified_device P q) (LE : finType) (HE : LE -> @chsType R) (LB : finType).
Variables (HB : LB -> @chsType R).

Notation M := (bb84_round_limit P).
Notation L := (bb84_label M LE LB).
Notation HL := (bb84_label_space HE HB).
Notation ec_bits := (cd_ir_bits dev).
Notation vseed_count := (cd_vseed_count dev).
Notation tag_count := (cd_tag_count dev).
Notation paseed_count := (cd_paseed_count dev).
Notation V := (bb84_val M (bb84_n P) (bb84_l P) ec_bits vseed_count tag_count paseed_count).

Definition empty_transcript : V := bb84_empty_transcript_val.

Definition bb84_basis_value (basis : bb84_basis) : V := match basis with | BasisX => bb84_basis_bool_val false
  | BasisZ => bb84_basis_bool_val true end.

Definition bb84_basis_of_value (v : V) : option bb84_basis := match bb84_basis_bool_of v with | Some false => Some BasisX
  | Some true => Some BasisZ | None => None end.

Local Notation adv := (@adversary R L HL V (bb84_eve_reg M LE LB)).
Local Notation hist := (@run_history V M).
Local Notation cstore := (@store (bb84_cvar M) V).
Local Notation Qsrc_all := [set x : L | if x is inr (inl _) then true else false].
Local Notation vX := (bb84_basis_value BasisX).
Local Notation vZ := (bb84_basis_value BasisZ).
Local Notation vO := (bb84_outcome_val None).
Local Notation bitV := (@bb84_bit_val M (bb84_n P) (bb84_l P) ec_bits vseed_count tag_count paseed_count).
Local Notation sigL := (bb84_signal_lfun HE HB).
Local Notation srcL := (bb84_source_lfun HE HB).
Local Notation ssL := (bb84_source_signal_lfun HE HB).
Local Notation SigR := (@bb84_signal_reg M LE LB).
Local Notation SrcR := (@bb84_source_reg M LE LB).

Fact bb84_basis_of_valueK (basis : bb84_basis) : bb84_basis_of_value (bb84_basis_value basis) = Some basis.
Proof. by case: basis. Qed.

Fact bb84_basis_bool_of_some (v : V) (b : bool) : bb84_basis_bool_of v = Some b -> v = bb84_basis_bool_val b.
Proof. by rewrite /bb84_basis_bool_of /bb84_basis_bool_val; case: v => //= v; case: v => //= b' [->]. Qed.

Lemma bb84_basis_of_value_some (v : V) (basis : bb84_basis) : bb84_basis_of_value v = Some basis -> v = bb84_basis_value basis.
Proof. case: basis; rewrite /bb84_basis_of_value /bb84_basis_value. - by case Hb: (bb84_basis_bool_of v) => [[|]|] //= _; exact: bb84_basis_bool_of_some. - by case Hb: (bb84_basis_bool_of v) => [[|]|] //= _; exact: bb84_basis_bool_of_some. Qed.

Local Lemma bb84_signal_lfun_den1 (i : 'I_M) (rho : 'M[C]_2) : rho \is den1mx -> sigL i rho \is den1lf.
Proof. move=> Hrho; apply/den1lfP; split. - by rewrite qualifE /bb84_signal_lfun mx2hK; exact: castmx_sq_psdmx (denmx_psd (den1mx_den Hrho)). - by rewrite /bb84_signal_lfun /lftrace mx2hK mxtrace_castmx_sq; have /den1mxP [_ /eqP ->] := Hrho. Qed.

Local Lemma bb84_signal_lfun0 (i : 'I_M) : sigL i (0 : 'M[C]_2) = 0.
Proof. by rewrite /bb84_signal_lfun raddf0 linear0. Qed.

Local Lemma bb84_signal_lfunD (i : 'I_M) (A B : 'M[C]_2) : sigL i (A + B) = sigL i A + sigL i B.
Proof. by rewrite /bb84_signal_lfun -linearD -raddfD. Qed.

Local Lemma bb84_signal_lfun1 (i : 'I_M) : sigL i (1%:M : 'M[C]_2) = (\1%VF : 'F[HL]_(SigR i)).
Proof. apply/h2mx_inj; rewrite /bb84_signal_lfun mx2hK h2mx1. by case: (dim 'H[HL]_(SigR i)) / (esym (bb84_signal_reg_dim HE HB i)); rewrite castmx_id. Qed.

Local Lemma bb84_signal_lfun_adj_comp (i : 'I_M) (A : 'M[C]_2) : ((sigL i A)^A \o sigL i A)%VF = sigL i (A^*t *m A).
Proof. apply/h2mx_inj; rewrite h2mx_comp adj_lfun.unlock /bb84_signal_lfun !mx2hK. by case: (dim 'H[HL]_(SigR i)) / (esym (bb84_signal_reg_dim HE HB i)); rewrite !castmx_id. Qed.

Definition bb84_device_dev_rho (i : 'I_M) (basis bit : V) : 'F[HL]_(SigR i) :=
  match bb84_basis_of_value basis, bb84_bit_of bit with | Some BasisX, Some b => sigL i (cd_rho dev BasisX b)
  | Some BasisZ, Some b => sigL i (cd_rho dev BasisZ b) | _, _ => sigL i (cd_rho dev BasisX false) end.

Lemma bb84_device_dev_rhoE (i : 'I_M) (basis : bb84_basis) (bit : bool) :
  bb84_device_dev_rho i (bb84_basis_value basis) (bb84_bit_val bit) = sigL i (cd_rho dev basis bit).
Proof. by case: basis. Qed.

Fact bb84_device_dev_rho_den1 (i : 'I_M) (basis bit : V) : bb84_device_dev_rho i basis bit \is den1lf.
Proof. rewrite /bb84_device_dev_rho; case: (bb84_basis_of_value basis) => [[|]|]; case: (bb84_bit_of bit) => [b|]; exact: bb84_signal_lfun_den1 (cd_rho_den1 dev _ _). Qed.

Definition bb84_device_dev_meas (i : 'I_M) (basis outcome : V) : 'F[HL]_(SigR i) := match bb84_basis_of_value basis, bb84_outcome_of outcome
    with | Some BasisX, Some o => sigL i (cd_meas dev BasisX o) | Some BasisZ, Some o => sigL i (cd_meas dev BasisZ o) | None, Some o =>
    sigL i (cd_meas dev BasisX o) | _, None => 0 end.

Lemma bb84_device_dev_measE (i : 'I_M) (basis : bb84_basis) (outcome : option bool) : bb84_device_dev_meas i
    (bb84_basis_value basis) (bb84_outcome_val outcome) = sigL i (cd_meas dev basis outcome).
Proof. by case: basis; case: outcome => [[]|]. Qed.

Fact bb84_device_dev_meas_complete (i : 'I_M) (basis : bb84_basis) : \sum_o (((bb84_device_dev_meas i (bb84_basis_value basis) o)^A) \o
          (bb84_device_dev_meas i (bb84_basis_value basis) o))%VF = \1%VF.
Proof.
  transitivity (\sum_o if @bb84_outcome_of M (bb84_n P) (bb84_l P) ec_bits vseed_count tag_count paseed_count o is Some outcome then (((sigL i (cd_meas dev basis outcome))^A) \o (sigL i (cd_meas dev basis outcome)))%VF else 0).
  - apply: eq_bigr => o _; rewrite /bb84_device_dev_meas bb84_basis_of_valueK.
    case Hout: (@bb84_outcome_of M (bb84_n P) (bb84_l P) ec_bits vseed_count tag_count paseed_count o) => [outcome|].
    + by case: basis.
    + by case: basis; rewrite adjf0 comp_lfun0l.
  - rewrite bb84_outcome_support_sum !bb84_signal_lfun_adj_comp -!bb84_signal_lfunD (cd_meas_complete dev basis).
    exact: bb84_signal_lfun1. Qed.

Fact bb84_device_dev_meas_complete_any (i : 'I_M) (basis : V) : \sum_o (((bb84_device_dev_meas i basis o)^A) \o
          (bb84_device_dev_meas i basis o))%VF = \1%VF.
Proof.
  case Hb: (bb84_basis_of_value basis) => [basis'|].
  - by rewrite (bb84_basis_of_value_some Hb); exact: bb84_device_dev_meas_complete.
  - transitivity (\sum_o if @bb84_outcome_of M (bb84_n P) (bb84_l P) ec_bits vseed_count tag_count paseed_count o is Some outcome then (((sigL i (cd_meas dev BasisX outcome))^A) \o (sigL i (cd_meas dev BasisX outcome)))%VF else 0).
    + apply: eq_bigr => o _; rewrite /bb84_device_dev_meas Hb.
      by case Hout: (@bb84_outcome_of M (bb84_n P) (bb84_l P) ec_bits vseed_count tag_count paseed_count o) => [outcome|] //; rewrite adjf0 comp_lfun0l.
    + rewrite bb84_outcome_support_sum !bb84_signal_lfun_adj_comp -!bb84_signal_lfunD (cd_meas_complete dev BasisX).
      exact: bb84_signal_lfun1. Qed.

Fact bb84_device_dev_meas_bound1 (i : 'I_M) (basis : bb84_basis) (outcome : V) :
  bb84_device_dev_meas i (bb84_basis_value basis) outcome \is bound1lf.
Proof. rewrite bound1lf_form_le1 -(bb84_device_dev_meas_complete i basis) (bigD1 outcome) //=. by rewrite levDl sumv_ge0 // => o _; rewrite form_gef0. Qed.

Fact bb84_device_dev_meas_any_bound1 (i : 'I_M) (basis outcome : V) : bb84_device_dev_meas i basis outcome \is bound1lf.
Proof.
  case Hb: (bb84_basis_of_value basis) => [basis'|].
  - by rewrite (bb84_basis_of_value_some Hb); exact: bb84_device_dev_meas_bound1.
  - rewrite /bb84_device_dev_meas Hb.
    case Hout: (bb84_outcome_of outcome) => [outcome'|].
    + have Hbound := bb84_device_dev_meas_bound1 i BasisX outcome.
      rewrite /bb84_device_dev_meas bb84_basis_of_valueK Hout in Hbound; exact: Hbound.
    + by rewrite bound1lf_form_le1 adjf0 comp_lfun0l lef01. Qed.

Fact bb84_device_dev_meas_case (i : 'I_M) (basis : bb84_basis) (outcome : option bool) : bb84_device_dev_meas i
    (bb84_basis_value basis) (bb84_outcome_val outcome) = match outcome with | None => sigL i (cd_meas dev BasisX None)
  | Some bit => sigL i (cd_meas dev basis (Some bit)) end.
Proof. case: outcome => [bit|]. - by rewrite bb84_device_dev_measE. - by rewrite bb84_device_dev_measE; case: basis => //=; rewrite -(cd_detect_basis_indep dev). Qed.

Local Definition bb84_hist_wt (h : hist) (s : cstore) : R := hist_wt (R:=R) (Cv:=bb84_cvar M) (V:=V) (M:=M) (bb84_n P) (bb84_k P)
    (cd_ir_bits dev) (bb84_Qtol P) (@BVa M) (@BVy M) (@BVb M) (@BVy' M) (@BVd M) (@BVX M) (@BVZ M) (@BVK M) (@BVXA M) (@BVXB M) (@BVZA M)
    (@BVZB M) (@BVlam M) (@BVpec M) (@BVXhat M) (@BVg M) (@BVtA M) (@BVtB M) (@BVabort M) (@BVP M) vX vZ vO bb84_bot_val empty_transcript
    bb84_bool_val bb84_bit_val bb84_set_val bb84_set_of bb84_error_val bb84_tr_app_rounds bb84_tr_app_pe bb84_tr_app_ec bb84_bits_on_val
    bb84_partial_bits_on_val bb84_err_count_val bb84_error_of bb84_unif_nsubset_mass (bb84_ir_pub_val (@cd_ir_pub R P q dev))
    (bb84_ir_dec_val (@cd_ir_dec R P q dev)) bb84_unif_vseed_mass (bb84_verify_hash_val (@cd_vh R P q dev)) bb84_unif_pseed_mass h s.

Local Definition bb84_history_post_weight (h : hist) (s : cstore) : R := history_post_weight (R:=R) (Cv:=bb84_cvar M) (V:=V) (M:=M) (bb84_n
    P) (bb84_k P) (cd_ir_bits dev) (bb84_Qtol P) (@BVa M) (@BVy M) (@BVb M) (@BVy' M) (@BVd M) (@BVX M) (@BVZ M) (@BVK M) (@BVXA M) (@BVXB
    M) (@BVZA M) (@BVZB M) (@BVlam M) (@BVpec M) (@BVXhat M) (@BVg M) (@BVtA M) (@BVtB M) (@BVabort M) (@BVP M) vX vZ vO bb84_bot_val
    empty_transcript bb84_bool_val bb84_set_val bb84_set_of bb84_error_val bb84_tr_app_rounds bb84_tr_app_pe bb84_tr_app_ec bb84_bits_on_val
    bb84_partial_bits_on_val bb84_err_count_val bb84_error_of bb84_unif_nsubset_mass (bb84_ir_pub_val (@cd_ir_pub R P q dev))
    (bb84_ir_dec_val (@cd_ir_dec R P q dev)) bb84_unif_vseed_mass (bb84_verify_hash_val (@cd_vh R P q dev)) bb84_unif_pseed_mass h s.

Local Definition bb84_start_store (s : cstore) : cstore := @start_store (bb84_cvar M) V M
    (@BVX M) (@BVZ M) (@BVabort M) (@BVP M) empty_transcript bb84_bool_val bb84_set_val s.

Local Definition bb84_final_store (h : hist) (s : cstore) : cstore := @final_store R (bb84_cvar M) V (bb84_n P) (bb84_k P) (bb84_l P)
    (cd_ir_bits dev) M (bb84_Qtol P) (@BVa M) (@BVy M) (@BVb M) (@BVy' M) (@BVd M) (@BVX M) (@BVZ M) (@BVK M) (@BVXA M) (@BVXB M) (@BVZA M)
    (@BVZB M) (@BVlam M) (@BVpec M) (@BVXhat M) (@BVg M) (@BVtA M) (@BVtB M) (@BVf M) (@BVS M) (@BVSh M) (@BVabort M) (@BVP M) vX vZ vO
    bb84_bot_val empty_transcript bb84_bool_val bb84_set_val bb84_set_of bb84_error_val bb84_tr_app_rounds bb84_tr_app_pe bb84_tr_app_ec
    bb84_tr_app_pa bb84_bits_on_val bb84_partial_bits_on_val bb84_err_count_val bb84_error_of (bb84_ir_pub_val (@cd_ir_pub R P q dev))
    (bb84_ir_dec_val (@cd_ir_dec R P q dev)) (bb84_verify_hash_val (@cd_vh R P q dev)) (bb84_privacy_hash_val (@cd_pa R P q dev)) h s.

Fact bb84_pass_history_key_sample_support (h : hist) (s : cstore) : ((bb84_final_store h s (@BVabort M) == bb84_bool_val false)%:R *
    bb84_history_post_weight h s != 0) -> let s2 := @announce_store (bb84_cvar M) V M (@BVa M) (@BVb M) (@BVd M) (@BVP M) bb84_tr_app_rounds
    (@rounds_store (bb84_cvar M) V M (@BVa M) (@BVy M) (@BVb M) (@BVy' M) (@BVd M) (@BVX M) (@BVZ M) vX vZ vO bb84_bool_val bb84_set_val h
    (bb84_start_store s)) in (#|bb84_set_of (@hist_K V M h)| = bb84_n P) /\ (bb84_set_of (@hist_K V M h) \subset bb84_set_of (s2 (@BVX M))).
Proof.
  move=> Hcoef.
  set s2 := @announce_store (bb84_cvar M) V M (@BVa M) (@BVb M) (@BVd M) (@BVP M) bb84_tr_app_rounds (@rounds_store (bb84_cvar M) V M (@BVa M) (@BVy M) (@BVb M) (@BVy' M) (@BVd M) (@BVX M) (@BVZ M) vX vZ vO bb84_bool_val bb84_set_val h (bb84_start_store s)).
  have Hpass : bb84_final_store h s (@BVabort M) == bb84_bool_val false.
  { apply/negPn/negP=> Hnot. by move: Hcoef; rewrite (negbTE Hnot) mul0r eqxx. } have Hpost : bb84_history_post_weight h s != 0. { apply/eqP=> Hzero. by move: Hcoef; rewrite Hzero mulr0 eqxx. } have Henabled : (bb84_n P <= #|bb84_set_of (s2 (@BVX M))|)%N.
  { rewrite /s2. apply: final_store_pass_key_sample_enabled; last exact: Hpass.
    - exact: bb84_bool_val_neq.
    - by rewrite /BVabort /BVS /=; apply: bb84_cvar_inr_neq; rewrite -val_eqE /= !inordK.
    - by rewrite /BVabort /BVSh /=; apply: bb84_cvar_inr_neq; rewrite -val_eqE /= !inordK.
    - by rewrite /BVX /BVK /=; apply: bb84_cvar_inr_neq; rewrite -val_eqE /= !inordK.
    - by rewrite /BVX /BVXA /=; apply: bb84_cvar_inr_neq; rewrite -val_eqE /= !inordK.
    - by rewrite /BVX /BVXB /=; apply: bb84_cvar_inr_neq; rewrite -val_eqE /= !inordK.
    - by rewrite /BVX /BVZA /=; apply: bb84_cvar_inr_neq; rewrite -val_eqE /= !inordK.
    - by rewrite /BVX /BVZB /=; apply: bb84_cvar_inr_neq; rewrite -val_eqE /= !inordK.
    - by rewrite /BVX /BVP /=; apply: bb84_cvar_inr_neq; rewrite -val_eqE /= !inordK.
    - by rewrite /BVX /BVlam /=; apply: bb84_cvar_inr_neq; rewrite -val_eqE /= !inordK. } have Hkey : @key_sample_mass R (bb84_cvar M) V (bb84_n P) M (@BVX M) bb84_bot_val bb84_set_of (@bb84_unif_nsubset_mass R M (bb84_n P) (bb84_l P) (cd_ir_bits dev) (cd_vseed_count dev) (cd_tag_count dev) (cd_paseed_count dev)) s2 (@hist_K V M h) != 0.
  { move: Hpost; rewrite /bb84_history_post_weight /s2. exact: history_post_weight_key_sample_nonzero. } rewrite /key_sample_mass Henabled in Hkey.
  have Hsupport := bb84_unif_nsubset_mass_support (m := bb84_n P) (X := bb84_set_of (s2 (@BVX M))) (v := @hist_K V M h) Hkey.
  move/andP: Hsupport => [/eqP Hcard Hsub]; exact: conj Hcard Hsub. Qed.

Local Open Scope lfun_scope.

Fact bb84_attack_formso_compC (EA : adv) (i j : 'I_M) (v : V) (f : 'F[HL]_(SigR i)) :
  i != j -> formso (liftf_lf f) :o liftfso (EA (SigR j) v) = liftfso (EA (SigR j) v) :o formso (liftf_lf f).
Proof. move=> Hij; rewrite -liftfso_formso; apply: liftfso_compC. rewrite /bb84_signal_reg disjoint1X !inE /bb84_signal_label /bb84_eve_reg orbF. change (i != j); exact: Hij. Qed.

Fact bb84_readout_prepare_compC (i j : 'I_M) (f : 'F[HL]_(SigR i)) (rho : 'F[HL]_(SigR j)) :
  i != j -> formso (liftf_lf f) :o replaceso rho = replaceso rho :o formso (liftf_lf f).
Proof. move=> Hij; have subij : SigR i :<=: setT :\: SigR j. { rewrite (@mathcomp.boot.finset.setTD L (SigR j)). by rewrite -disjointX_subset /bb84_signal_reg disjoint1X !inE /bb84_signal_label Hij. } exact: (replaceso_formso_compC subij f rho). Qed.

Definition bb84_round_readout_so (h : hist) (i : 'I_M) : 'SO[HL]_setT := formso (liftf_lf
    (bb84_device_dev_meas i (hist_b h i) (hist_y' h i))).

Definition bb84_round_update_so (EA : adv) (h : hist) (i : 'I_M) : 'SO[HL]_setT :=
  liftfso (EA (SigR i) empty_transcript) :o replaceso (bb84_device_dev_rho i (hist_a h i) (hist_y h i)).

Definition bb84_readout_so_seq (h : hist) (r : seq 'I_M) : 'SO[HL]_setT := \compr_(i <- r) bb84_round_readout_so h i.

Definition bb84_update_so_seq (EA : adv) (h : hist) (r : seq 'I_M) : 'SO[HL]_setT := \compr_(i <- r) bb84_round_update_so EA h i.

Definition bb84_trace_so_seq (EA : adv) (h : hist) (r : seq 'I_M) : 'SO[HL]_setT :=
  \compr_(i <- r) (bb84_round_readout_so h i :o bb84_round_update_so EA h i).

Fact bb84_readout_update_compC (EA : adv) (h : hist) (i j : 'I_M) :
  i != j -> bb84_round_readout_so h i :o bb84_round_update_so EA h j = bb84_round_update_so EA h j :o bb84_round_readout_so h i.
Proof. move=> Hij; rewrite /bb84_round_readout_so /bb84_round_update_so comp_soA. rewrite (bb84_attack_formso_compC EA (i := i) (j := j) empty_transcript _ Hij). by rewrite -comp_soA (bb84_readout_prepare_compC (i := i) (j := j) _ _ Hij) comp_soA. Qed.

Fact bb84_readout_update_seq_compC (EA : adv) (h : hist) (i : 'I_M) (r : seq 'I_M) :
  i \notin r -> bb84_round_readout_so h i :o bb84_update_so_seq EA h r = bb84_update_so_seq EA h r :o bb84_round_readout_so h i.
Proof. elim: r => [|j r IHr] //=. - by rewrite /bb84_update_so_seq big_nil comp_so1r comp_so1l. - rewrite in_cons negb_or => /andP [Hij Hir]. rewrite /bb84_update_so_seq big_cons -/bb84_update_so_seq comp_soA (IHr Hir) -!comp_soA. by rewrite (bb84_readout_update_compC EA h Hij) !comp_soA. Qed.

Fact bb84_trace_so_seq_deferred (EA : adv) (h : hist) (r : seq 'I_M) :
  uniq r -> bb84_trace_so_seq EA h r = bb84_readout_so_seq h r :o bb84_update_so_seq EA h r.
Proof.
  elim: r => [|i r IHr] //=.
  - by rewrite /bb84_trace_so_seq /bb84_readout_so_seq /bb84_update_so_seq !big_nil comp_so1r.
  - move=> /andP [Hir Huniq].
    rewrite /bb84_trace_so_seq /bb84_readout_so_seq /bb84_update_so_seq !big_cons !comp_soErl -/bb84_trace_so_seq -/bb84_readout_so_seq -/bb84_update_so_seq -/(bb84_trace_so_seq EA h r) -/(bb84_readout_so_seq h r) -/(bb84_update_so_seq EA h r).
    rewrite IHr // !comp_soA; f_equal.
    rewrite -!comp_soA; f_equal.
    by rewrite !comp_soA -(bb84_readout_update_seq_compC EA h Hir). Qed.

Fact bb84_hist_so_deferred (EA : adv) (h : hist) : @hist_so R L HL V M (@bb84_signal_regs M LE LB) empty_transcript (bb84_device_dev_rho)
    (bb84_device_dev_meas) (bb84_eve_reg M LE LB) EA h = bb84_readout_so_seq h (enum 'I_M) :o bb84_update_so_seq EA h (enum 'I_M).
Proof.
  rewrite /hist_so /round_so /round_choice_so /attack_transcript.
  rewrite (eq_bigr (fun i : 'I_M => bb84_round_readout_so h i :o bb84_round_update_so EA h i)).
  - by rewrite -/(bb84_trace_so_seq EA h (enum 'I_M)) (bb84_trace_so_seq_deferred EA h (r := enum 'I_M)) //; exact: enum_uniq.
  - by move=> i _; rewrite /bb84_round_readout_so /bb84_round_update_so /hist_a /hist_y /hist_b /hist_y' -comp_soA. Qed.

Definition bb84_round_readout_lf (i : 'I_M) (basis : bb84_basis) (outcome : option bool) : 'F[HL]_(SigR i) := match outcome with
  | None => sigL i (cd_meas dev BasisX None) | Some bit => sigL i (cd_meas dev basis (Some bit)) end.

Lemma bb84_round_readout_so_case (h : hist) (i : 'I_M) (basis : bb84_basis) (outcome : option bool) :
  bb84_basis_of_value (hist_b h i) = Some basis -> bb84_outcome_of (hist_y' h i) = Some outcome -> bb84_round_readout_so h i =
  formso (liftf_lf (bb84_round_readout_lf i basis outcome)).
Proof. rewrite /bb84_round_readout_so /bb84_round_readout_lf /bb84_device_dev_meas. move=> -> ->; case: outcome => [bit|] /=. - by case: basis. - by case: basis => //=; rewrite -(cd_detect_basis_indep dev). Qed.

Fact bb84_round_readout_so_invalid (h : hist) (i : 'I_M) : bb84_outcome_of (hist_y' h i) = None -> bb84_round_readout_so h i = 0.
Proof. rewrite /bb84_round_readout_so /bb84_device_dev_meas. have Hlift0 : liftf_lf (0 : 'F[HL]_(SigR i)) = 0 by apply/eqP; rewrite liftf_lf_eq0 eqxx. move=> Ho; case: (bb84_basis_of_value (hist_b h i)) => [[|]|]; rewrite Ho; change (formso (liftf_lf (0 : 'F[HL]_(SigR i))) = 0); by rewrite Hlift0 formso0. Qed.

Fact bb84_readout_so_seq_invalid (h : hist) (r : seq 'I_M) (i : 'I_M) :
  i \in r -> bb84_outcome_of (hist_y' h i) = None -> bb84_readout_so_seq h r = 0.
Proof.
  elim: r => [|j r IHr] //=.
  rewrite in_cons => /orP [/eqP -> | Hir] Hbad.
  - by rewrite /bb84_readout_so_seq big_cons (bb84_round_readout_so_invalid (h := h) (i := j) Hbad) comp_sor0l.
  - rewrite /bb84_readout_so_seq big_cons -/bb84_readout_so_seq.
    change (\compr_(i0 <- r) bb84_round_readout_so h i0) with (bb84_readout_so_seq h r); by rewrite (IHr Hir Hbad) comp_sor0r. Qed.

Fact bb84_hist_so_invalid_readout (EA : adv) (h : hist) : (exists i, bb84_outcome_of (hist_y' h i) = None) -> @hist_so R L HL V M
    (@bb84_signal_regs M LE LB) empty_transcript (bb84_device_dev_rho) (bb84_device_dev_meas) (bb84_eve_reg M LE LB) EA h = 0.
Proof. move=> [i Hbad]; rewrite (bb84_hist_so_deferred EA h). by rewrite (bb84_readout_so_seq_invalid (h := h) (r := enum 'I_M) (i := i)); [rewrite comp_so0l | rewrite mem_enum | exact: Hbad]. Qed.

Local Close Scope lfun_scope.

Definition bb84_prep_basis_prob (basis : bb84_basis) : R := match basis with | BasisX => (1 + Num.sqrt ((bb84_k P)%:R / (bb84_n P)%:R))^-1
  | BasisZ => 1 - (1 + Num.sqrt ((bb84_k P)%:R / (bb84_n P)%:R))^-1 end.

Definition bb84_prep_branch_prob (basis : bb84_basis) : R := bb84_prep_basis_prob basis * (2%:R)^-1.

Local Notation pbP := bb84_prep_basis_prob.
Local Notation roLf := bb84_round_readout_lf.

Lemma bb84_prep_basis_prob_nonneg (basis : bb84_basis) : 0 <= pbP basis.
Proof. rewrite /bb84_prep_basis_prob; case: basis. - by rewrite invr_ge0 addr_ge0 ?ler01 ?sqrtr_ge0. - by rewrite subr_ge0 invf_le1; [rewrite lerDl sqrtr_ge0 | rewrite ltr_wpDr ?ltr01 ?sqrtr_ge0]. Qed.

Lemma bb84_prep_branch_prob_nonneg (basis : bb84_basis) : 0 <= bb84_prep_branch_prob basis.
Proof. rewrite /bb84_prep_branch_prob; apply: mulr_ge0; first exact: bb84_prep_basis_prob_nonneg. by rewrite invr_ge0 ler0n. Qed.

Definition bb84_prep_index (basis : bb84_basis) (bit : bool) : 'I_4 := inord (match basis, bit with | BasisX, false => 0 | BasisX, true => 1
         | BasisZ, false => 2 | BasisZ, true => 3 end).

Local Lemma bb84_source_lfun_delta_den1 (i : 'I_M) (basis : bb84_basis) (bit : bool) : srcL i
    ((delta_mx (bb84_prep_index basis bit) (bb84_prep_index basis bit)) : 'M[C]_4) \is den1lf.
Proof. apply/den1lfP; split. - by rewrite qualifE /bb84_source_lfun mx2hK; exact: castmx_sq_psdmx (@delta_mx_psdmx R 4 (bb84_prep_index basis bit)). - by rewrite /bb84_source_lfun /lftrace mx2hK mxtrace_castmx_sq mxtrace_delta eqxx. Qed.

Definition bb84_prep_basis_of_index (j : 'I_4) : bb84_basis := if (nat_of_ord j < 2)%N then BasisX else BasisZ.

Definition bb84_prep_bit_of_index (j : 'I_4) : bool := odd j.

Fact bb84_prep_basis_of_indexK (basis : bb84_basis) (bit : bool) : bb84_prep_basis_of_index (bb84_prep_index basis bit) = basis.
Proof. by case: basis; case: bit; rewrite /bb84_prep_basis_of_index /bb84_prep_index inordK. Qed.

Lemma bb84_prep_bit_of_indexK (basis : bb84_basis) (bit : bool) : bb84_prep_bit_of_index (bb84_prep_index basis bit) = bit.
Proof. by case: basis; case: bit; rewrite /bb84_prep_bit_of_index /bb84_prep_index inordK. Qed.

Definition bb84_prep_source_mx : 'M[C]_(4 * 2) := \sum_(j < 4) ((bb84_prep_branch_prob (bb84_prep_basis_of_index j))%:C *:
      ((delta_mx j j : 'M[C]_4) *t cd_rho dev (bb84_prep_basis_of_index j) (bb84_prep_bit_of_index j))).

Definition bb84_prep_source_projector (basis : bb84_basis) (bit : bool) : 'M[C]_(4 * 2) :=
  (delta_mx (bb84_prep_index basis bit) (bb84_prep_index basis bit) : 'M[C]_4) *t (1%:M : 'M[C]_2).

Definition bb84_prep_source_signal_branch (basis : bb84_basis) (bit : bool) : 'M[C]_(4 * 2) := bb84_prep_source_projector basis bit *m
    bb84_prep_source_mx *m bb84_prep_source_projector basis bit.

Lemma bb84_prep_source_signal_branchE (basis : bb84_basis) (bit : bool) : bb84_prep_source_signal_branch basis bit = (bb84_prep_branch_prob
    basis)%:C *: ((delta_mx (bb84_prep_index basis bit) (bb84_prep_index basis bit) : 'M[C]_4) *t cd_rho dev basis bit).
Proof.
  rewrite /bb84_prep_source_signal_branch /bb84_prep_source_mx mulmx_sumr mulmx_suml /=.
  rewrite (bigD1 (bb84_prep_index basis bit)) //= -scalemxAr -scalemxAl /=.
  rewrite /bb84_prep_source_projector !tensmx_mul !mul_delta_mx !mulmx1 !mul1mx bb84_prep_basis_of_indexK bb84_prep_bit_of_indexK.
  rewrite [X in _ + X = _]big1 ?addr0 // => j Hj.
  rewrite -scalemxAr -scalemxAl /=.
  have Hidxj : bb84_prep_index basis bit != j by rewrite eq_sym.
  rewrite /bb84_prep_source_projector !tensmx_mul !mulmx1.
  rewrite (@mul_delta_mx_0 C 4 4 4 (bb84_prep_index basis bit) j (bb84_prep_index basis bit) j Hidxj).
  by rewrite ?mul0mx ?mulmx0 ?tens0mx ?tensmx0 ?scale0r ?scaler0. Qed.

Local Lemma bb84_source_signal_biprod_mx_adj (i : 'I_M) (f : 'F[HL]_(SrcR i :|: SigR i)) :
  biprod_mx (bb84_source_signal_disjoint LE LB i) f^A = (biprod_mx (bb84_source_signal_disjoint LE LB i) f)^*t.
Proof.
  rewrite /biprod_mx h2mx_adj; set dis := bb84_source_signal_disjoint LE LB i.
  set Q : 'M[C]_(dim 'H[HL]_(SrcR i) * dim 'H[HL]_(SigR i)) := castmx (tenv_dim dis, erefl) (@tenv_mxU R L HL (SrcR i) (SigR i)).
  have Hcast_adj : castmx (tenv_dim dis, tenv_dim dis) (h2mx f)^*t = (castmx (tenv_dim dis, tenv_dim dis) (h2mx f))^*t.
  { by rewrite (@castmx_mx_mxT _ _ (@adjmx _) _ _ _ _ (tenv_dim dis, tenv_dim dis) (h2mx f)). } by rewrite Hcast_adj adjmxM adjmxM adjmxK !mulmxA. Qed.

Local Lemma bb84_source_signal_lfunZ (i : 'I_M) (c : C) (A : 'M[C]_(4 * 2)) : ssL i (c *: A) = c *: ssL i A.
Proof.
  rewrite /bb84_source_signal_lfun.
  have Hdim : (dim 'H[HL]_(SrcR i) * dim 'H[HL]_(SigR i))%N = (4 * 2)%N by rewrite (bb84_source_reg_dim HE HB i) (bb84_signal_reg_dim HE HB i).
  rewrite !(eq_irrelevance (f_equal2 muln (bb84_source_reg_dim HE HB i) (bb84_signal_reg_dim HE HB i)) Hdim).
  by rewrite linearZ biprod_of_mxZ. Qed.

Fact bb84_source_signal_lfun_tens (i : 'I_M) (A : 'M[C]_4) (B : 'M[C]_2) : ssL i (A *t B) = (sdot_lfun (srcL i A) (sigL i B) : 'F[HL]_(SrcR
    i :|: SigR i)).
Proof.
  apply: (@biprod_mx_inj R L HL _ _ (bb84_source_signal_disjoint LE LB i)).
  rewrite biprod_mxK biprod_mx_sdot /bb84_source_signal_lfun /bb84_source_lfun /bb84_signal_lfun !mx2hK.
  rewrite -(@castmx_tensmx R _ _ _ _ _ _ _ _ (esym (bb84_source_reg_dim HE HB i)) (esym (bb84_source_reg_dim HE HB i)) (esym (bb84_signal_reg_dim HE HB i)) (esym (bb84_signal_reg_dim HE HB i)) A B).
  by congr (castmx (_, _) _); exact: eq_irrelevance. Qed.

Definition bb84_prep_source_branch (basis : bb84_basis) (bit : bool) : 'M[C]_2 := ptrace1 (bb84_prep_source_projector basis bit *m
    bb84_prep_source_mx *m bb84_prep_source_projector basis bit).

Local Notation prepB := bb84_prep_source_branch.

Fact bb84_prep_source_branchE (basis : bb84_basis) (bit : bool) : prepB basis bit =
  (bb84_prep_branch_prob basis)%:C *: cd_rho dev basis bit.
Proof.
  rewrite /bb84_prep_source_branch /bb84_prep_source_mx mulmx_sumr mulmx_suml linear_sum /=.
  rewrite (bigD1 (bb84_prep_index basis bit)) //= -scalemxAr -scalemxAl linearZ /=.
  rewrite /bb84_prep_source_projector !tensmx_mul !mul_delta_mx !mulmx1.
  rewrite ptrace1_tensmx mxtrace_delta eqxx scale1r bb84_prep_basis_of_indexK bb84_prep_bit_of_indexK mul1mx.
  rewrite [X in _ + X = _]big1 ?addr0 // => j Hj.
  rewrite -scalemxAr -scalemxAl linearZ /=.
  have Hidxj : bb84_prep_index basis bit != j by rewrite eq_sym.
  rewrite /bb84_prep_source_projector !tensmx_mul !mulmx1.
  rewrite (@mul_delta_mx_0 C 4 4 4 (bb84_prep_index basis bit) j (bb84_prep_index basis bit) j Hidxj).
  by rewrite mul0mx tens0mx linear0 scaler0. Qed.

Lemma bb84_prep_source_branch_lfunE (i : 'I_M) (basis : bb84_basis) (bit : bool) : sigL i (prepB basis bit) = (bb84_prep_branch_prob
    basis)%:C *: sigL i (cd_rho dev basis bit).
Proof. by rewrite bb84_prep_source_branchE /bb84_signal_lfun !linearZ. Qed.

Fact bb84_signal_lfun_prep_source_branch_tr (i : 'I_M) (basis : bb84_basis) (bit : bool) : \Tr (sigL i
    (prepB basis bit)) = (bb84_prep_branch_prob basis)%:C.
Proof. by rewrite bb84_prep_source_branch_lfunE linearZ /= (den1lf_trlf (bb84_signal_lfun_den1 i (cd_rho_den1 dev basis bit))) mulr1. Qed.

Fact bb84_basis_mass_none (s : cstore) (v : V) : bb84_basis_of_value v = None -> @basis_mass R (bb84_cvar M) V (bb84_n P) (bb84_k P) vX vZ
    s v = 0.
Proof.
  rewrite /bb84_basis_of_value; case Hb: (bb84_basis_bool_of v) => [[|]|] // _.
  rewrite /basis_mass /bb84_basis_value.
  have Hx : v != bb84_basis_bool_val false by apply/eqP=> Hv; move: Hb; rewrite Hv bb84_basis_bool_of_val.
  have Hz : v != bb84_basis_bool_val true by apply/eqP=> Hv; move: Hb; rewrite Hv bb84_basis_bool_of_val.
  by rewrite (negbTE Hx) (negbTE Hz). Qed.

Fact bb84_bit_mass_none (s : cstore) (v : V) : bb84_bit_of v = None -> @bit_mass R (bb84_cvar M) V bitV s v = 0.
Proof. move=> Hv_none; rewrite /bit_mass. have Hf : v != bb84_bit_val false. { apply/eqP=> Hv. by move: Hv_none; rewrite Hv bb84_bit_of_val. } have Ht : v != bb84_bit_val true. { apply/eqP=> Hv. by move: Hv_none; rewrite Hv bb84_bit_of_val. } by rewrite (negbTE Hf) (negbTE Ht). Qed.

Fact bb84_round_sample_weight_invalid (h : hist) (s : cstore) (i : 'I_M) : bb84_basis_of_value (hist_a h i) = None \/ bb84_bit_of (hist_y h
    i) = None \/ bb84_basis_of_value (hist_b h i) = None -> @round_sample_weight R (bb84_cvar M) V (bb84_n P) (bb84_k P) M vX vZ bitV h s i
    = 0.
Proof.
  rewrite /round_sample_weight /round_choice_weight.
  change (choice_a (hist_choice h i)) with (hist_a h i); change (choice_y (hist_choice h i)) with (hist_y h i).
  change (choice_b (hist_choice h i)) with (hist_b h i).
  move=> [Ha | [Hy | Hb]].
  - by rewrite (bb84_basis_mass_none s Ha) mul0r mul0r.
  - by rewrite (bb84_bit_mass_none s Hy) mulr0 mul0r.
  - by rewrite (bb84_basis_mass_none s Hb) mulr0. Qed.

Fact bb84_round_samples_weight_invalid (h : hist) (s : cstore) : (exists i, bb84_basis_of_value (hist_a h i) = None \/ bb84_bit_of (hist_y
    h i) = None \/ bb84_basis_of_value (hist_b h i) = None) -> @round_samples_weight R (bb84_cvar M) V (bb84_n P) (bb84_k P) M vX vZ bitV h
    s = 0.
Proof. move=> [i Hbad]; rewrite /round_samples_weight (bigD1_seq i) ?mem_enum ?enum_uniq //=. by rewrite (bb84_round_sample_weight_invalid s (h := h) (i := i) Hbad) mul0r. Qed.

Local Open Scope lfun_scope.

Fact bb84_round_update_so_source_branch (EA : adv) (h : hist) (i : 'I_M) (basis : bb84_basis) (bit : bool) (rho : 'F[HL]_setT) :
    bb84_basis_of_value (hist_a h i) = Some basis -> bb84_bit_of (hist_y h i) = Some bit -> (bb84_prep_branch_prob basis)%:C *:
    (bb84_round_update_so EA h i rho) = liftfso (EA (SigR i) empty_transcript) (replaceso (sigL i (prepB basis bit)) rho).
Proof.
have replaceso_prep_source_branchE : forall (i : 'I_M) (basis : bb84_basis) (bit : bool) (rho : 'F[HL]_setT), replaceso (sigL i (prepB basis bit)) rho = (bb84_prep_branch_prob basis)%:C *: replaceso (bb84_device_dev_rho i (bb84_basis_value basis) (bb84_bit_val bit)) rho.
{ clear rho bit basis i h EA; move=> i basis bit rho. by rewrite bb84_prep_source_branch_lfunE bb84_device_dev_rhoE replacesoZ. } move=> Hbasis Hbit; rewrite replaceso_prep_source_branchE bb84_device_dev_rhoE.
  rewrite /bb84_round_update_so /bb84_device_dev_rho Hbasis Hbit comp_sorE.
  case: basis Hbasis => Hbasis /=.
  - set Eop := liftfso _; set X := replaceso _ rho.
    have Hscale : Eop ((bb84_prep_branch_prob BasisX)%:C *: X) = (bb84_prep_branch_prob BasisX)%:C *: Eop X.
    { have Hlin := superop_is_linear Eop; have H := Hlin (bb84_prep_branch_prob BasisX)%:C X 0.
      have H0 : Eop 0 = 0 by rewrite /Eop liftfso0. by rewrite -[(bb84_prep_branch_prob BasisX)%:C *: X]addr0 H H0 addr0. } by rewrite -Hscale.
  - set Eop := liftfso _; set X := replaceso _ rho.
    have Hscale : Eop ((bb84_prep_branch_prob BasisZ)%:C *: X) = (bb84_prep_branch_prob BasisZ)%:C *: Eop X.
    { have Hlin := superop_is_linear Eop; have H := Hlin (bb84_prep_branch_prob BasisZ)%:C X 0.
      have H0 : Eop 0 = 0 by rewrite /Eop liftfso0. by rewrite -[(bb84_prep_branch_prob BasisZ)%:C *: X]addr0 H H0 addr0. } by rewrite -Hscale. Qed.

Fact bb84_round_readout_update_source_branch (EA : adv) (h : hist) (i : 'I_M) (alice_basis bob_basis : bb84_basis) (alice_bit : bool)
    (bob_outcome : option bool) (rho : 'F[HL]_setT) : bb84_basis_of_value (hist_a h i) = Some alice_basis -> bb84_bit_of (hist_y h i) = Some
    alice_bit -> bb84_basis_of_value (hist_b h i) = Some bob_basis -> bb84_outcome_of (hist_y' h i) = Some bob_outcome ->
    (bb84_prep_branch_prob alice_basis * pbP bob_basis)%:C *: ((bb84_round_readout_so h i :o bb84_round_update_so EA h i) rho) = (pbP
    bob_basis)%:C *: (formso (liftf_lf (roLf i bob_basis bob_outcome)) (liftfso (EA (SigR i) empty_transcript) (replaceso (sigL i (prepB
    alice_basis alice_bit)) rho))).
Proof.
  move=> Ha Hy Hb Ho.
  rewrite comp_sorE (bb84_round_readout_so_case (h := h) (i := i) (basis := bob_basis) (outcome := bob_outcome) Hb Ho).
  set Fop := formso (liftf_lf _); set Ux := bb84_round_update_so EA h i rho.
  rewrite -(bb84_round_update_so_source_branch EA rho (h := h) (i := i) (basis := alice_basis) (bit := alice_bit) Ha Hy).
  have Hscale : Fop ((bb84_prep_branch_prob alice_basis)%:C *: Ux) = (bb84_prep_branch_prob alice_basis)%:C *: Fop Ux.
  { have Hlin := superop_is_linear Fop; have H := Hlin (bb84_prep_branch_prob alice_basis)%:C Ux 0.
    have H0 : Fop 0 = 0 by rewrite /Fop formsoE comp_lfun0r comp_lfun0l.
    by rewrite -[(bb84_prep_branch_prob alice_basis)%:C *: Ux]addr0 H H0 addr0. } by rewrite Hscale !scalerA -!rmorphM /= mulrC. Qed.

Fact bb84_hist_weighted_so_invalid (EA : adv) (h : hist) (s : cstore) (rho : 'F[HL]_setT) : (exists i, bb84_basis_of_value (hist_a h i) =
    None \/ bb84_bit_of (hist_y h i) = None \/ bb84_basis_of_value (hist_b h i) = None) \/ (exists i, bb84_basis_of_value (hist_b h i) =
    None \/ bb84_outcome_of (hist_y' h i) = None) -> (@round_samples_weight R (bb84_cvar M) V (bb84_n P) (bb84_k P) M vX vZ bitV h s)%:C *:
    @hist_so R L HL V M (@bb84_signal_regs M LE LB) empty_transcript (bb84_device_dev_rho) (bb84_device_dev_meas) (bb84_eve_reg M LE LB) EA
    h rho = 0.
Proof.
  move=> [Hsample | Hreadout].
  - by rewrite (bb84_round_samples_weight_invalid s (h := h) Hsample) rmorph0 scale0r.
  - move: Hreadout => [i [Hb | Ho]].
    + by rewrite (bb84_round_samples_weight_invalid s (h := h)); [rewrite rmorph0 scale0r | exists i; right; right].
    + by rewrite (bb84_hist_so_invalid_readout EA (h := h)); [rewrite superopE lfunE scaler0 | exists i]. Qed.

Definition bb84_has_basis_value (v : V) : bool := if bb84_basis_of_value v is Some _ then true else false.

Definition bb84_has_bit_value (v : V) : bool := if bb84_bit_of v is Some _ then true else false.

Definition bb84_has_outcome_value (v : V) : bool := if bb84_outcome_of v is Some _ then true else false.

Definition bb84_history_round_decoded (h : hist) (i : 'I_M) : bool := [&& bb84_has_basis_value (hist_a h i),
      bb84_has_bit_value (hist_y h i), bb84_has_basis_value (hist_b h i) & bb84_has_outcome_value (hist_y' h i)].

Definition bb84_history_decoded (h : hist) : bool := [forall i : 'I_M, bb84_history_round_decoded h i].

Definition bb84_history_alice_basis (h : hist) (i : 'I_M) : bb84_basis := odflt BasisX (bb84_basis_of_value (hist_a h i)).

Definition bb84_history_alice_bit (h : hist) (i : 'I_M) : bool := odflt false (bb84_bit_of (hist_y h i)).

Definition bb84_history_bob_basis (h : hist) (i : 'I_M) : bb84_basis := odflt BasisX (bb84_basis_of_value (hist_b h i)).

Definition bb84_history_bob_outcome (h : hist) (i : 'I_M) : option bool := odflt None (bb84_outcome_of (hist_y' h i)).

Local Notation haB := bb84_history_alice_basis.
Local Notation haY := bb84_history_alice_bit.
Local Notation hbB := bb84_history_bob_basis.
Local Notation hbO := bb84_history_bob_outcome.

Definition bb84_trace_round_decoded (t : @round_trace V M) (i : 'I_M) : bool := [&& bb84_has_basis_value (choice_a (t i)),
      bb84_has_bit_value (choice_y (t i)), bb84_has_basis_value (choice_b (t i)) & bb84_has_outcome_value (choice_y' (t i))].

Definition bb84_trace_decoded (t : @round_trace V M) : bool := [forall i : 'I_M, bb84_trace_round_decoded t i].

Definition bb84_trace_alice_basis (t : @round_trace V M) (i : 'I_M) : bb84_basis := odflt BasisX (bb84_basis_of_value (choice_a (t i))).

Definition bb84_trace_alice_bit (t : @round_trace V M) (i : 'I_M) : bool := odflt false (bb84_bit_of (choice_y (t i))).

Definition bb84_trace_bob_basis (t : @round_trace V M) (i : 'I_M) : bb84_basis := odflt BasisX (bb84_basis_of_value (choice_b (t i))).

Definition bb84_trace_bob_outcome (t : @round_trace V M) (i : 'I_M) : option bool := odflt None (bb84_outcome_of (choice_y' (t i))).

Lemma bb84_history_decoded_traceE (h : hist) : bb84_history_decoded h = bb84_trace_decoded h.1.
Proof. by apply/eq_forallb=> i; rewrite /bb84_history_round_decoded /bb84_trace_round_decoded /hist_a /hist_y /hist_b /hist_y' /hist_choice. Qed.

Fact bb84_basis_of_value_decoded (v : V) : bb84_has_basis_value v -> bb84_basis_of_value v = Some (odflt BasisX (bb84_basis_of_value v)).
Proof. by rewrite /bb84_has_basis_value; case: (bb84_basis_of_value v). Qed.

Fact bb84_bit_of_decoded (v : V) : bb84_has_bit_value v -> bb84_bit_of v = Some (odflt false (bb84_bit_of v)).
Proof. by rewrite /bb84_has_bit_value; case: (bb84_bit_of v). Qed.

Lemma bb84_outcome_of_decoded (v : V) : bb84_has_outcome_value v -> bb84_outcome_of v = Some (odflt None (bb84_outcome_of v)).
Proof. by rewrite /bb84_has_outcome_value; case: (bb84_outcome_of v). Qed.

Fact bb84_basis_of_value_none (v : V) : ~~ bb84_has_basis_value v -> bb84_basis_of_value v = None.
Proof. by rewrite /bb84_has_basis_value; case: (bb84_basis_of_value v). Qed.

Lemma bb84_history_decoded_bob_basis (h : hist) (i : 'I_M) : bb84_history_decoded h -> bb84_basis_of_value (hist_b h i) = Some (hbB h i).
Proof. by move/forallP/(_ i); rewrite /bb84_history_round_decoded => /and4P [_ _ Hb _]; exact: bb84_basis_of_value_decoded. Qed.

Lemma bb84_history_decoded_outcome (h : hist) (i : 'I_M) : bb84_history_decoded h -> bb84_outcome_of (hist_y' h i) = Some (hbO h i).
Proof. by move/forallP/(_ i); rewrite /bb84_history_round_decoded => /and4P [_ _ _ Ho]; exact: bb84_outcome_of_decoded. Qed.

Definition bb84_trace_source_state (EA : adv) (t : @round_trace V M) (rho : 'F[HL]_setT) : 'F[HL]_setT := if bb84_trace_decoded t then
    (\compr_(i <- enum 'I_M) ((pbP (bb84_trace_bob_basis t i))%:C *: (formso (liftf_lf (roLf i (bb84_trace_bob_basis t i)
    (bb84_trace_bob_outcome t i))) :o (liftfso (EA (SigR i) empty_transcript) :o replaceso (sigL i (prepB (bb84_trace_alice_basis t i)
    (bb84_trace_alice_bit t i))))))) rho else 0.

Definition bb84_history_source_state (EA : adv) (h : hist) (rho : 'F[HL]_setT) : 'F[HL]_setT := bb84_trace_source_state EA h.1 rho.

Lemma bb84_history_source_state_case (EA : adv) (h : hist) (rho : 'F[HL]_setT) : bb84_history_decoded h -> bb84_history_source_state EA h
    rho = (\compr_(i <- enum 'I_M) ((pbP (hbB h i))%:C *: (formso (liftf_lf (roLf i (hbB h i) (hbO h i))) :o (liftfso (EA (SigR i)
    empty_transcript) :o replaceso (sigL i (prepB (haB h i) (haY h i))))))) rho.
Proof. move=> Hdecoded; rewrite /bb84_history_source_state /bb84_trace_source_state -bb84_history_decoded_traceE Hdecoded. by congr (fun E : 'SO[HL]_setT => E rho). Qed.

Definition bb84_round_source_update_so (EA : adv) (h : hist) (i : 'I_M) : 'SO[HL]_setT := liftfso (EA (SigR i) empty_transcript) :o
    replaceso (ssL i (bb84_prep_source_signal_branch (haB h i) (haY h i))).

Fact bb84_round_source_update_so_formso_ptraceso_all_sources (EA : adv) (h : hist) (i : 'I_M) (F : 'F[HL]_(SigR i)) (rho : 'F[HL]_setT) :
    ptraceso Qsrc_all (formso (liftf_lf F) (bb84_round_source_update_so EA h i rho)) = ptraceso Qsrc_all (formso (liftf_lf F) (liftfso (EA
    (SigR i) empty_transcript) (replaceso (sigL i (prepB (haB h i) (haY h i))) rho))).
Proof.
have bb84_round_source_update_so_formso_ptraceso : forall (EA : adv) (h : hist) (i : 'I_M) (F : 'F[HL]_(SigR i)) (rho : 'F[HL]_setT), ptraceso (SrcR i) (formso (liftf_lf F) (bb84_round_source_update_so EA h i rho)) = ptraceso (SrcR i) (formso (liftf_lf F) (liftfso (EA (SigR i) empty_transcript) (replaceso (sigL i (prepB (haB h i) (haY h i))) rho))).
{ clear rho F i h EA; move=> EA h i F rho. have bb84_round_source_update_so_ptraceso : forall (EA : adv) (h : hist) (i : 'I_M) (rho : 'F[HL]_setT), ptraceso (SrcR i) (bb84_round_source_update_so EA h i rho) = ptraceso (SrcR i) (liftfso (EA (SigR i) empty_transcript) (replaceso (sigL i (prepB (haB h i) (haY h i))) rho)).
{ clear rho F i h EA; move=> EA h i rho. have bb84_source_signal_replaceso_ptraceso_source : forall (i : 'I_M) (basis : bb84_basis) (bit : bool) (rho : 'F[HL]_setT), ptraceso (SrcR i) (replaceso (ssL i (bb84_prep_source_signal_branch basis bit)) rho) = ptraceso (SrcR i) (replaceso (sigL i (prepB basis bit)) rho).
{ clear rho i h EA; move=> i basis bit rho. have bb84_source_signal_lfun_prep_source_signal_branch_ptrace : forall (i : 'I_M) (basis : bb84_basis) (bit : bool), ptrace_castl (bb84_source_signal_disjoint LE LB i) (ssL i (bb84_prep_source_signal_branch basis bit)) = sigL i (prepB basis bit).
{ clear rho bit basis i; move=> i basis bit. rewrite bb84_prep_source_signal_branchE bb84_source_signal_lfunZ bb84_source_signal_lfun_tens ptrace_castl_linearZ.
  by rewrite ptrace_castl_sdot_trace_l (den1lf_trlf (bb84_source_lfun_delta_den1 i basis bit)) scale1r bb84_prep_source_branch_lfunE. } set A := SrcR i; set B := SigR i.
  set C0 := ([set: L] : {set L}) :\: (A :|: B).
  have HAB : [disjoint A & B] by rewrite /A /B; exact: bb84_source_signal_disjoint.
  have HA_C0 : [disjoint A & C0].
  { apply/disjointP => x HxA; apply/negP => /setDP [_ /negP Hn]. by apply: Hn; rewrite inE HxA. } have HB_C0 : [disjoint B & C0].
  { apply/disjointP => x HxB; apply/negP => /setDP [_ /negP Hn]. by apply: Hn; rewrite inE HxB orbT. } have HAB_C0 : [disjoint A :|: B & C0] by rewrite disjointUX HA_C0 HB_C0.
  have eqABC : A :|: B :|: C0 = ([set: L] : {set L}) by rewrite /C0 setUD_sub.
  rewrite !replacesoE.
  set eqC := etrans (esym (setDU_l HAB_C0)) (f_equal (fun S => S :\: (A :|: B)) eqABC).
  set xC := castlf (esym eqC, esym eqC) (ptraceso (A :|: B) rho).
  have HxC : ptraceso (A :|: B) rho = castlf (eqC, eqC) xC.
  { rewrite /xC castlf_comp. by rewrite (eq_irrelevance (etrans (esym eqC) eqC) erefl) castlf_id. } rewrite {1}HxC (@ptraceso_appendso_union_l R L HL A B C0 HAB HA_C0 HB_C0 HAB_C0 eqABC (ssL i (bb84_prep_source_signal_branch basis bit)) xC).
  have Hptr_source_signal : ptrace_castl HAB (ssL i (bb84_prep_source_signal_branch basis bit)) = sigL i (prepB basis bit).
  { by rewrite (eq_irrelevance HAB (bb84_source_signal_disjoint LE LB i)); exact: bb84_source_signal_lfun_prep_source_signal_branch_ptrace. } rewrite Hptr_source_signal.
  have HBA : [disjoint B & A] by rewrite disjoint_sym HAB.
  have eqBAC : B :|: A :|: C0 = ([set: L] : {set L}) by rewrite [B :|: A]finset.setUC eqABC.
  set eqAC := etrans (esym (setDU3_A HBA HB_C0)) (f_equal (fun S => S :\: B) eqBAC).
  set yAC := castlf (esym eqAC, esym eqAC) (ptraceso B rho).
  have HyAC : ptraceso B rho = castlf (eqAC, eqAC) yAC.
  { rewrite /yAC castlf_comp. by rewrite (eq_irrelevance (etrans (esym eqAC) eqAC) erefl) castlf_id. } rewrite {1}HyAC (@ptraceso_appendso_complement R L HL B A C0 HBA HB_C0 HA_C0 eqBAC (sigL i (prepB basis bit)) yAC).
  have Htail : ptrace_castl HA_C0 yAC = xC.
  { rewrite /ptrace_castl /ptrace_cast_gen /yAC /xC.
    rewrite (ptracelf_castlf_eq (esym eqAC) (f_equal (fun S => S :\: A) (esym eqAC))).
    have Hcomp_trace := congr1 (fun F : 'SO[HL]_(setTfor L, ((setTfor L :\: B) :\: A)) => F rho) (@ptraceso_comp R L HL A B (setTfor L)).
    move: Hcomp_trace; rewrite comp_soE castsoE /= castlf_id => Hcomp_trace; rewrite Hcomp_trace.
    have Htrace_comm : ptraceso (B :|: A) rho = castlf (esym (f_equal (fun S => ([set: L] : {set L}) :\: S) (finset.setUC B A)), esym (f_equal (fun S => ([set: L] : {set L}) :\: S) (finset.setUC B A))) (ptraceso (A :|: B) rho).
    { by case: _ / (finset.setUC B A); rewrite castlf_id. } rewrite Htrace_comm !castlf_comp.
    by congr (castlf (_, _) _); exact: eq_irrelevance. } by rewrite Htail; congr (castlf (_, _) _); exact: eq_irrelevance. } rewrite /bb84_round_source_update_so comp_sorE.
  set Q := SrcR i; set S := SigR i; set E := bb84_eve_reg M LE LB.
  have Hsub : S :|: E :<=: setT :\: Q.
  { have HdisS : [disjoint S & Q].
    { by rewrite /S /Q /bb84_source_reg /bb84_signal_reg disjoint1X !inE /bb84_source_label /bb84_signal_label. } have HdisE : [disjoint E & Q].
    { apply/disjointP=> x HxE; apply/negP=> HxQ; move: HxE HxQ; rewrite /E /Q /bb84_eve_reg /bb84_source_reg !inE.
      by case: x => [sig | [src | [eve | bridge]]]. } by rewrite (@mathcomp.boot.finset.setTD L Q) -disjointX_subset disjointUX HdisS HdisE. } by rewrite !(@ptraceso_liftfso_compl R L HL Q (S :|: E) Hsub (EA S empty_transcript)) bb84_source_signal_replaceso_ptraceso_source. } rewrite -!liftfso_formso.
  set Q := SrcR i; set S := SigR i.
  have Hsub : S :<=: setT :\: Q.
  { have HdisS : [disjoint S & Q].
    { by rewrite /S /Q /bb84_source_reg /bb84_signal_reg disjoint1X !inE /bb84_source_label /bb84_signal_label. } by rewrite (@mathcomp.boot.finset.setTD L Q) -disjointX_subset HdisS. } by rewrite !(@ptraceso_liftfso_compl R L HL Q S Hsub (formso F)) bb84_round_source_update_so_ptraceso. } set Qsrc := Qsrc_all.
  have Hsrc : SrcR i :<=: Qsrc.
  { apply/subsetP=> x. rewrite /bb84_source_reg inE => /eqP ->. by rewrite /Qsrc inE /bb84_source_label. } apply: (ptraceso_weaken_eq Hsrc); exact: bb84_round_source_update_so_formso_ptraceso. Qed.

Fact bb84_round_readout_source_update_ptraceso_all_sources (EA : adv) (h : hist) (i : 'I_M) (rho : 'F[HL]_setT) : bb84_history_decoded h ->
    ptraceso Qsrc_all ((bb84_round_readout_so h i :o bb84_round_source_update_so EA h i) rho) = ptraceso Qsrc_all (formso (liftf_lf (roLf i
    (hbB h i) (hbO h i))) (liftfso (EA (SigR i) empty_transcript) (replaceso (sigL i (prepB (haB h i) (haY h i))) rho))).
Proof. move=> Hdecoded; rewrite comp_sorE (bb84_round_readout_so_case (h := h) (i := i) (basis := hbB h i) (outcome := hbO h i)). - exact: bb84_round_source_update_so_formso_ptraceso_all_sources. - exact: bb84_history_decoded_bob_basis. - exact: bb84_history_decoded_outcome. Qed.

Definition bb84_round_pre_readout_so (EA : adv) (h : hist) (i : 'I_M) : 'SO[HL]_setT :=
  (pbP (hbB h i))%:C *: bb84_round_source_update_so EA h i.

Fact bb84_round_pre_readout_readout_ptraceso_all_sources (EA : adv) (h : hist) (i : 'I_M) (rho : 'F[HL]_setT) : bb84_history_decoded h ->
    ptraceso Qsrc_all ((bb84_round_readout_so h i :o bb84_round_pre_readout_so EA h i) rho) = ptraceso Qsrc_all ((pbP (hbB h i))%:C *:
    formso (liftf_lf (roLf i (hbB h i) (hbO h i))) (liftfso (EA (SigR i) empty_transcript) (replaceso (sigL i (prepB (haB h i) (haY h i)))
    rho))).
Proof.
  move=> Hdecoded; set Qsrc := Qsrc_all.
  set a := (pbP (hbB h i))%:C.
  apply/eqP/trlf_intror=> N; rewrite -/Qsrc !ptraceso_liftf_lf_tr.
  have Hbridge := bb84_round_readout_source_update_ptraceso_all_sources (h := h) EA i rho Hdecoded.
  rewrite -/Qsrc in Hbridge.
  move: (congr1 (fun z => \Tr (z \o N)) Hbridge) => Hbridge_tr; rewrite !ptraceso_liftf_lf_tr in Hbridge_tr.
  rewrite /bb84_round_pre_readout_so comp_sorE scale_soE.
  rewrite [bb84_round_readout_so h i (a *: _)]linearZ /= -[in LHS]comp_lfunZl [in LHS]linearZ /=.
  rewrite -[in RHS]comp_lfunZl [in RHS]linearZ /=.
  by congr (a * _); rewrite -comp_sorE; exact: Hbridge_tr. Qed.

Fact bb84_source_readout_seq_ptraceso_eq (EA : adv) (h : hist) (r : seq 'I_M) (rho sigma : 'F[HL]_setT) : ptraceso Qsrc_all rho = ptraceso
    Qsrc_all sigma -> ptraceso Qsrc_all ((\compr_(i <- r) ((pbP (hbB h i))%:C *: (formso (liftf_lf (roLf i (hbB h i) (hbO h i))) :o (liftfso
    (EA (SigR i) empty_transcript) :o replaceso (sigL i (prepB (haB h i) (haY h i))))))) rho) = ptraceso Qsrc_all ((\compr_(i <- r) ((pbP
    (hbB h i))%:C *: (formso (liftf_lf (roLf i (hbB h i) (hbO h i))) :o (liftfso (EA (SigR i) empty_transcript) :o replaceso (sigL i (prepB
    (haB h i) (haY h i))))))) sigma).
Proof.
have bb84_source_readout_round_ptraceso_eq : forall (EA : adv) (h : hist) (i : 'I_M) (rho sigma : 'F[HL]_setT), ptraceso Qsrc_all rho = ptraceso Qsrc_all sigma -> ptraceso Qsrc_all (((pbP (hbB h i))%:C *: (formso (liftf_lf (roLf i (hbB h i) (hbO h i))) :o (liftfso (EA (SigR i) empty_transcript) :o replaceso (sigL i (prepB (haB h i) (haY h i)))))) rho) = ptraceso Qsrc_all (((pbP (hbB h i))%:C *: (formso (liftf_lf (roLf i (hbB h i) (hbO h i))) :o (liftfso (EA (SigR i) empty_transcript) :o replaceso (sigL i (prepB (haB h i) (haY h i)))))) sigma).
{ clear sigma rho r h EA; move=> EA h i rho sigma. move=> Hrho; set Qsrc := Qsrc_all.
  set S := SigR i; set E := bb84_eve_reg M LE LB.
  have HdisS : [disjoint S & Qsrc].
  { apply/disjointP=> x HxS; apply/negP=> HxQ; move: HxS HxQ; rewrite /S /Qsrc /bb84_signal_reg !inE.
    by case: x => [sig | [src | [eve | bridge]]]. } have HdisE : [disjoint E & Qsrc].
  { apply/disjointP=> x HxE; apply/negP=> HxQ; move: HxE HxQ; rewrite /E /Qsrc /bb84_eve_reg !inE.
    by case: x => [sig | [src | [eve | bridge]]]. } have HsubS : S :<=: setT :\: Qsrc.
  { rewrite (@mathcomp.boot.finset.setTD L Qsrc). by rewrite -disjointX_subset HdisS. } have HsubSE : S :|: E :<=: setT :\: Qsrc.
  { rewrite (@mathcomp.boot.finset.setTD L Qsrc). by rewrite -disjointX_subset disjointUX HdisS HdisE. } set C0 := ([set: L] : {set L}) :\: (S :|: Qsrc).
  have HS_Q : [disjoint S & Qsrc] := HdisS.
  have HS_C0 : [disjoint S & C0].
  { apply/disjointP=> x HxS; apply/negP=> /setDP [_ /negP Hn]. by apply: Hn; rewrite inE HxS. } have HQ_C0 : [disjoint Qsrc & C0].
  { apply/disjointP=> x HxQ; apply/negP=> /setDP [_ /negP Hn]. by apply: Hn; rewrite inE HxQ orbT. } have Heq : S :|: Qsrc :|: C0 = ([set: L] : {set L}) by rewrite /C0 setUD_sub.
  set Prep := sigL i (prepB (haB h i) (haY h i)).
  have Hrep : ptraceso Qsrc (replaceso Prep rho) = ptraceso Qsrc (replaceso Prep sigma).
  { exact: (@ptraceso_replaceso_disjoint_eq R L HL S Qsrc C0 HS_Q HS_C0 HQ_C0 Heq Prep rho sigma Hrho). } set a := (pbP (hbB h i))%:C.
  set Fread := roLf i (hbB h i) (hbO h i).
  set G : 'SO[HL]_setT := formso (liftf_lf Fread) :o (liftfso (EA S empty_transcript) :o replaceso Prep).
  change (ptraceso Qsrc ((a *: G) rho) = ptraceso Qsrc ((a *: G) sigma)).
  have Hscale (x : 'F[HL]_setT) : ptraceso Qsrc ((a *: G) x) = a *: ptraceso Qsrc (G x) by rewrite scale_soE linearZ.
  rewrite (Hscale rho) (Hscale sigma); congr (_ *: _); rewrite /G.
  have Hform_rho : ptraceso Qsrc ((formso (liftf_lf Fread) :o (liftfso (EA S empty_transcript) :o replaceso Prep)) rho) = liftso HsubS (formso Fread) (ptraceso Qsrc (liftfso (EA S empty_transcript) (replaceso Prep rho))).
  { rewrite !comp_soE -(@liftfso_formso R L HL (SigR i) Fread).
    by rewrite (@ptraceso_liftfso_compl R L HL Qsrc (SigR i) HsubS (formso Fread) (liftfso (EA S empty_transcript) (appendso Prep (ptraceso (SigR i) rho)))). } have Hform_sigma : ptraceso Qsrc ((formso (liftf_lf Fread) :o (liftfso (EA S empty_transcript) :o replaceso Prep)) sigma) = liftso HsubS (formso Fread) (ptraceso Qsrc (liftfso (EA S empty_transcript) (replaceso Prep sigma))).
  { rewrite !comp_soE -(@liftfso_formso R L HL (SigR i) Fread).
    by rewrite (@ptraceso_liftfso_compl R L HL Qsrc (SigR i) HsubS (formso Fread) (liftfso (EA S empty_transcript) (appendso Prep (ptraceso (SigR i) sigma)))). } rewrite Hform_rho Hform_sigma.
  have Hattack_rho : ptraceso Qsrc (liftfso (EA S empty_transcript) (replaceso Prep rho)) = liftso HsubSE (EA S empty_transcript) (ptraceso Qsrc (replaceso Prep rho)).
  { exact: (@ptraceso_liftfso_compl R L HL Qsrc (S :|: E) HsubSE (EA S empty_transcript) (replaceso Prep rho)). } have Hattack_sigma : ptraceso Qsrc (liftfso (EA S empty_transcript) (replaceso Prep sigma)) = liftso HsubSE (EA S empty_transcript) (ptraceso Qsrc (replaceso Prep sigma)).
  { exact: (@ptraceso_liftfso_compl R L HL Qsrc (S :|: E) HsubSE (EA S empty_transcript) (replaceso Prep sigma)). } rewrite Hattack_rho Hattack_sigma.
  exact: (congr1 (fun z => liftso HsubS (formso Fread) (liftso HsubSE (EA S empty_transcript) z)) Hrep). } elim: r rho sigma => [|i r IHr] rho sigma Hrho.
  - by rewrite !big_nil !id_soE.
  - by rewrite !big_cons !comp_sorE; apply: IHr; exact: bb84_source_readout_round_ptraceso_eq. Qed.

Definition bb84_pre_readout_trace_so_seq (EA : adv)
    (h : hist) (r : seq 'I_M) : 'SO[HL]_setT := \compr_(i <- r) (bb84_round_readout_so h i :o bb84_round_pre_readout_so EA h i).

Fact bb84_pre_readout_trace_so_seq_case (EA : adv) (h : hist) (r : seq 'I_M) : bb84_history_decoded h -> bb84_pre_readout_trace_so_seq EA h
    r = \compr_(i <- r) ((pbP (hbB h i))%:C *: (formso (liftf_lf (roLf i (hbB h i) (hbO h i))) :o bb84_round_source_update_so EA h i)).
Proof.
  move=> Hdecoded; rewrite /bb84_pre_readout_trace_so_seq; apply: eq_bigr => i _.
  rewrite /bb84_round_pre_readout_so (bb84_round_readout_so_case (h := h) (i := i) (basis := hbB h i) (outcome := hbO h i)).
  - by rewrite linearZ.
  - exact: bb84_history_decoded_bob_basis.
  - exact: bb84_history_decoded_outcome. Qed.

Definition bb84_history_readout_state (EA : adv) (h : hist) (rho : 'F[HL]_setT) : 'F[HL]_setT := if bb84_history_decoded h then
    bb84_pre_readout_trace_so_seq EA h (enum 'I_M) rho else 0.

Fact bb84_pre_readout_trace_source_seq_ptraceso_all_sources (EA : adv) (h : hist) (r : seq 'I_M) (rho : 'F[HL]_setT) : bb84_history_decoded
    h -> ptraceso Qsrc_all (bb84_pre_readout_trace_so_seq EA h r rho) = ptraceso Qsrc_all ((\compr_(i <- r) ((pbP (hbB h i))%:C *: (formso
    (liftf_lf (roLf i (hbB h i) (hbO h i))) :o (liftfso (EA (SigR i) empty_transcript) :o replaceso (sigL i (prepB (haB h i) (haY h i)))))))
    rho).
Proof.
  move=> Hdecoded; elim: r rho => [|i r IHr] rho.
  - by rewrite /bb84_pre_readout_trace_so_seq !big_nil !id_soE.
  - rewrite /bb84_pre_readout_trace_so_seq !big_cons !comp_sorE -/bb84_pre_readout_trace_so_seq IHr.
    apply: bb84_source_readout_seq_ptraceso_eq.
    rewrite [in RHS]scale_soE [in RHS]comp_soE [in RHS]comp_soE.
    rewrite -[bb84_round_readout_so h i (bb84_round_pre_readout_so EA h i rho)]comp_soE.
    exact: (bb84_round_pre_readout_readout_ptraceso_all_sources (h := h) EA i rho Hdecoded). Qed.

Fact bb84_history_readout_source_ptraceso_all_sources (EA : adv) (h : hist) (rho : 'F[HL]_setT) : bb84_history_decoded h -> ptraceso
    Qsrc_all (bb84_history_readout_state EA h rho) = ptraceso Qsrc_all (bb84_history_source_state EA h rho).
Proof.
  have bb84_history_readout_state_case : forall (EA : adv) (h : hist) (rho : 'F[HL]_setT), bb84_history_decoded h -> bb84_history_readout_state EA h rho = (\compr_(i <- enum 'I_M) ((pbP (hbB h i))%:C *: (formso (liftf_lf (roLf i (hbB h i) (hbO h i))) :o bb84_round_source_update_so EA h i))) rho.
  { move=> {}EA {}h {}rho. move=> Hdecoded. by rewrite /bb84_history_readout_state Hdecoded (bb84_pre_readout_trace_so_seq_case (h := h) EA (enum 'I_M) Hdecoded). } move=> Hdecoded; rewrite (bb84_history_readout_state_case EA h rho Hdecoded).
  rewrite (bb84_history_source_state_case (h := h) EA rho Hdecoded) -(bb84_pre_readout_trace_so_seq_case (h := h) EA (enum 'I_M) Hdecoded).
  exact: (bb84_pre_readout_trace_source_seq_ptraceso_all_sources (h := h) EA (enum 'I_M) rho Hdecoded). Qed.

Fact bb84_history_readout_state_trace_eq (EA : adv) (h h' : hist) (rho : 'F[HL]_setT) :
  h.1 = h'.1 -> bb84_history_readout_state EA h rho = bb84_history_readout_state EA h' rho.
Proof.
  move=> Htrace; rewrite /bb84_history_readout_state !bb84_history_decoded_traceE Htrace.
  case Hdec: (bb84_trace_decoded h'.1).
  - have Hso : bb84_pre_readout_trace_so_seq EA h (enum 'I_M) = bb84_pre_readout_trace_so_seq EA h' (enum 'I_M).
    { rewrite /bb84_pre_readout_trace_so_seq; apply: eq_bigr => i _.
      by rewrite /bb84_round_pre_readout_so /bb84_round_source_update_so /bb84_round_readout_so /bb84_round_readout_lf /bb84_history_alice_basis /bb84_history_alice_bit /bb84_history_bob_basis /bb84_history_bob_outcome /hist_a /hist_y /hist_b /hist_y' /hist_choice Htrace. } by rewrite Hso.
  - by []. Qed.

Lemma bb84_signal_lfun_prep_source_branch_psd (i : 'I_M) (basis : bb84_basis) (bit : bool) : sigL i (prepB basis bit) \is psdlf.
Proof. rewrite bb84_prep_source_branch_lfunE; apply: psdlfZ; first by rewrite lecR bb84_prep_branch_prob_nonneg. exact: den1lf_psd (bb84_signal_lfun_den1 i (cd_rho_den1 dev basis bit)). Qed.

Lemma bb84_history_readout_state_psd (EA : adv) (h : hist) (rho : 'F[HL]_setT) :
  rho \is psdlf -> bb84_history_readout_state EA h rho \is psdlf.
Proof.
  have bb84_round_pre_readout_so_psd : forall (EA : adv) (h : hist) (i : 'I_M) (rho : 'F[HL]_setT), rho \is psdlf -> bb84_round_pre_readout_so EA h i rho \is psdlf.
  { move=> {}EA {}h i {}rho. have bb84_round_source_update_so_psd : forall (EA : adv) (h : hist) (i : 'I_M) (rho : 'F[HL]_setT), rho \is psdlf -> bb84_round_source_update_so EA h i rho \is psdlf. { clear rho i h EA; move=> EA h i rho. have bb84_source_signal_lfun_prep_source_signal_branch_psd : forall (i : 'I_M) (basis : bb84_basis) (bit : bool), ssL i (bb84_prep_source_signal_branch basis bit) \is psdlf. { clear rho i h EA; move=> i basis bit. rewrite /bb84_source_signal_lfun. have Hdim : (dim 'H[HL]_(SrcR i) * dim 'H[HL]_(SigR i))%N = (4 * 2)%N by rewrite (bb84_source_reg_dim HE HB i) (bb84_signal_reg_dim HE HB i).
    rewrite !(eq_irrelevance (f_equal2 muln (bb84_source_reg_dim HE HB i) (bb84_signal_reg_dim HE HB i)) Hdim). apply: (@biprod_of_mx_psd R L HL (SrcR i) (SigR i) (bb84_source_signal_disjoint LE LB i)). apply: castmx_sq_psdmx. rewrite bb84_prep_source_signal_branchE. apply: psdmxZ; first by rewrite lecR bb84_prep_branch_prob_nonneg. apply: psdmx_tens. - exact: delta_mx_psdmx. - exact: denmx_psd (den1mx_den (cd_rho_den1 dev basis bit)). } move=> Hrho; rewrite /bb84_round_source_update_so comp_sorE. apply: cp_psdP. apply: replaceso_psd; last exact: Hrho. exact: bb84_source_signal_lfun_prep_source_signal_branch_psd. } move=> Hrho; rewrite /bb84_round_pre_readout_so scale_soE.
    apply: psdlfZ. - by rewrite lecR bb84_prep_basis_prob_nonneg. - exact: bb84_round_source_update_so_psd. } have bb84_pre_readout_trace_so_seq_psd : forall (EA : adv) (h : hist) (r : seq 'I_M) (rho : 'F[HL]_setT), rho \is psdlf -> bb84_pre_readout_trace_so_seq EA h r rho \is psdlf.
{ clear rho h EA; move=> EA h r rho. have bb84_round_pre_readout_trace_so_psd : forall (EA : adv) (h : hist) (i : 'I_M) (rho : 'F[HL]_setT), rho \is psdlf -> (bb84_round_readout_so h i :o bb84_round_pre_readout_so EA h i) rho \is psdlf.
{ clear rho r h EA; move=> EA h i rho. move=> Hrho; rewrite comp_sorE. apply: cp_psdP. exact: bb84_round_pre_readout_so_psd. } elim: r rho => [|i r IHr] rho Hrho.
  - by rewrite /bb84_pre_readout_trace_so_seq big_nil id_soE.
  - rewrite /bb84_pre_readout_trace_so_seq big_cons comp_sorE -/bb84_pre_readout_trace_so_seq.
    by apply: IHr; exact: bb84_round_pre_readout_trace_so_psd. } rewrite /bb84_history_readout_state.
  case: (bb84_history_decoded h); last by move=> _; exact: is_psdlf.
  exact: bb84_pre_readout_trace_so_seq_psd. Qed.

Fact bb84_history_source_state_psd (EA : adv) (h : hist) (rho : 'F[HL]_setT) :
  rho \is psdlf -> bb84_history_source_state EA h rho \is psdlf.
Proof.
  move=> Hrho; case Hdec: (bb84_history_decoded h); last first.
  - by rewrite /bb84_history_source_state /bb84_trace_source_state -bb84_history_decoded_traceE Hdec; exact: is_psdlf.
  - rewrite (bb84_history_source_state_case (h := h) EA rho Hdec).
    move: rho Hrho; elim: (enum 'I_M) => [|i r IHr] rho Hrho.
    + by rewrite big_nil id_soE.
    + rewrite big_cons comp_sorE; apply: IHr.
      rewrite scale_soE; apply: psdlfZ; first by rewrite lecR bb84_prep_basis_prob_nonneg.
      rewrite comp_sorE; apply: cp_psdP.
      rewrite comp_sorE; apply: cp_psdP.
      by apply: replaceso_psd; last exact: Hrho; exact: bb84_signal_lfun_prep_source_branch_psd. Qed.

Fact bb84_hist_weighted_so_source_or_zero (EA : adv) (h : hist) (s : cstore) (rho : 'F[HL]_setT) : (@round_samples_weight R (bb84_cvar M) V
    (bb84_n P) (bb84_k P) M vX vZ bitV h s)%:C *: @hist_so R L HL V M (@bb84_signal_regs M LE LB) empty_transcript (bb84_device_dev_rho)
    (bb84_device_dev_meas) (bb84_eve_reg M LE LB) EA h rho = bb84_history_source_state EA h rho.
Proof.
  have bb84_round_samples_weight_source_branch : forall (h : hist) (s : cstore) (alice_basis bob_basis : 'I_M -> bb84_basis) (alice_bit : 'I_M -> bool), (forall i, bb84_basis_of_value (hist_a h i) = Some (alice_basis i)) -> (forall i, bb84_bit_of (hist_y h i) = Some (alice_bit i)) -> (forall i, bb84_basis_of_value (hist_b h i) = Some (bob_basis i)) -> @round_samples_weight R (bb84_cvar M) V (bb84_n P) (bb84_k P) M vX vZ bitV h s = \prod_(i <- enum 'I_M) (bb84_prep_branch_prob (alice_basis i) * pbP (bob_basis i)).
  { move=> {}h {}s alice_basis bob_basis alice_bit. have bb84_round_sample_weight_source_branch : forall (h : hist) (s : cstore) (i : 'I_M) (alice_basis bob_basis : bb84_basis) (alice_bit : bool), bb84_basis_of_value (hist_a h i) = Some alice_basis -> bb84_bit_of (hist_y h i) = Some alice_bit -> bb84_basis_of_value (hist_b h i) = Some bob_basis -> @round_sample_weight R (bb84_cvar M) V (bb84_n P) (bb84_k P) M vX vZ bitV h s i = bb84_prep_branch_prob alice_basis * pbP bob_basis. { clear alice_bit bob_basis alice_basis s h; move=> h s i alice_basis bob_basis alice_bit. have bb84_bit_of_some : forall (v0 : V) (bit0 : bool), bb84_bit_of v0 = Some bit0 -> v0 = bb84_bit_val bit0. { move=> v0 bit0; rewrite /bb84_bit_of /bb84_bit_val. by case: v0 => //= v0; case: v0 => //= v0; case: v0 => //= b [->]. } move=> Ha Hy Hb; have HaE := bb84_basis_of_value_some Ha. have HyE := bb84_bit_of_some _ _ Hy. have HbE := bb84_basis_of_value_some Hb. rewrite /round_sample_weight /round_choice_weight /basis_mass /bit_mass /bb84_prep_branch_prob /bb84_prep_basis_prob. change (choice_a (hist_choice h i)) with (hist_a h i). change (choice_y (hist_choice h i)) with (hist_y h i). change (choice_b (hist_choice h i)) with (hist_b h i). rewrite HaE HyE HbE. clear Ha Hy Hb HaE HyE HbE. by case: alice_basis; case: alice_bit; case: bob_basis. } move=> Ha Hy Hb; rewrite /round_samples_weight. apply: eq_bigr => i _. exact: bb84_round_sample_weight_source_branch. } have bb84_hist_weighted_so_source_branch : forall (EA : adv) (h : hist) (s : cstore) (alice_basis bob_basis : 'I_M -> bb84_basis) (alice_bit : 'I_M -> bool) (bob_outcome : 'I_M -> option bool) (rho : 'F[HL]_setT), (forall i, bb84_basis_of_value (hist_a h i) = Some (alice_basis i)) -> (forall i, bb84_bit_of (hist_y h i) = Some (alice_bit i)) -> (forall i, bb84_basis_of_value (hist_b h i) = Some (bob_basis i)) -> (forall i, bb84_outcome_of (hist_y' h i) = Some (bob_outcome i)) -> (@round_samples_weight R (bb84_cvar M) V (bb84_n P) (bb84_k P) M vX vZ bitV h s)%:C *: @hist_so R L HL V M (@bb84_signal_regs M LE LB) empty_transcript (bb84_device_dev_rho) (bb84_device_dev_meas) (bb84_eve_reg M LE LB) EA h rho = (\compr_(i <- enum 'I_M) ((pbP (bob_basis i))%:C *: (formso (liftf_lf (roLf i (bob_basis i) (bob_outcome i))) :o (liftfso (EA (SigR i) empty_transcript) :o replaceso (sigL i (prepB (alice_basis i) (alice_bit i))))))) rho.
{ clear rho s h EA; move=> EA h s alice_basis bob_basis alice_bit bob_outcome rho. have bb84_hist_so_source_branch : forall (EA : adv) (h : hist) (alice_basis bob_basis : 'I_M -> bb84_basis) (alice_bit : 'I_M -> bool) (bob_outcome : 'I_M -> option bool) (rho : 'F[HL]_setT), (forall i, bb84_basis_of_value (hist_a h i) = Some (alice_basis i)) -> (forall i, bb84_bit_of (hist_y h i) = Some (alice_bit i)) -> (forall i, bb84_basis_of_value (hist_b h i) = Some (bob_basis i)) -> (forall i, bb84_outcome_of (hist_y' h i) = Some (bob_outcome i)) -> ((\prod_(i <- enum 'I_M) (bb84_prep_branch_prob (alice_basis i) * pbP (bob_basis i)))%:C *: @hist_so R L HL V M (@bb84_signal_regs M LE LB) empty_transcript (bb84_device_dev_rho) (bb84_device_dev_meas) (bb84_eve_reg M LE LB) EA h rho) = (\compr_(i <- enum 'I_M) ((pbP (bob_basis i))%:C *: (formso (liftf_lf (roLf i (bob_basis i) (bob_outcome i))) :o (liftfso (EA (SigR i) empty_transcript) :o replaceso (sigL i (prepB (alice_basis i) (alice_bit i))))))) rho.
{ clear rho bob_outcome alice_bit bob_basis alice_basis s h EA; move=> EA h alice_basis bob_basis alice_bit bob_outcome rho. have bb84_trace_so_seq_source_branch : forall (EA : adv) (h : hist) (r : seq 'I_M) (alice_basis bob_basis : 'I_M -> bb84_basis) (alice_bit : 'I_M -> bool) (bob_outcome : 'I_M -> option bool) (rho : 'F[HL]_setT), (forall i, i \in r -> bb84_basis_of_value (hist_a h i) = Some (alice_basis i)) -> (forall i, i \in r -> bb84_bit_of (hist_y h i) = Some (alice_bit i)) -> (forall i, i \in r -> bb84_basis_of_value (hist_b h i) = Some (bob_basis i)) -> (forall i, i \in r -> bb84_outcome_of (hist_y' h i) = Some (bob_outcome i)) -> ((\prod_(i <- r) (bb84_prep_branch_prob (alice_basis i) * pbP (bob_basis i)))%:C *: bb84_trace_so_seq EA h r rho) = (\compr_(i <- r) ((pbP (bob_basis i))%:C *: (formso (liftf_lf (roLf i (bob_basis i) (bob_outcome i))) :o (liftfso (EA (SigR i) empty_transcript) :o replaceso (sigL i (prepB (alice_basis i) (alice_bit i))))))) rho.
{ clear rho bob_outcome alice_bit bob_basis alice_basis h EA; move=> EA h r alice_basis bob_basis alice_bit bob_outcome rho. elim: r rho => [|i r IHr] rho Ha Hy Hb Ho.
  - by rewrite /bb84_trace_so_seq !big_nil scale1r !id_soE.
  - rewrite !big_cons /bb84_trace_so_seq big_cons comp_sorE -/(bb84_trace_so_seq EA h r).
    set wi := bb84_prep_branch_prob (alice_basis i) * pbP (bob_basis i).
    set wr := \prod_(j <- r) (bb84_prep_branch_prob (alice_basis j) * pbP (bob_basis j)).
    set T := bb84_trace_so_seq EA h r.
    set x := (bb84_round_readout_so h i :o bb84_round_update_so EA h i) rho.
    have Tscale : T (wi%:C *: x) = wi%:C *: T x by rewrite linearZ.
    rewrite [wi * wr]mulrC rmorphM /= -scalerA -Tscale /wi /x.
    rewrite (bb84_round_readout_update_source_branch EA rho (h := h) (i := i) (alice_basis := alice_basis i) (bob_basis := bob_basis i) (alice_bit := alice_bit i) (bob_outcome := bob_outcome i)).
    + rewrite /wi (IHr _).
      * by rewrite comp_sorE scale_soE !comp_soE.
      * by move=> j Hj; apply: Ha; rewrite in_cons Hj orbT.
      * by move=> j Hj; apply: Hy; rewrite in_cons Hj orbT.
      * by move=> j Hj; apply: Hb; rewrite in_cons Hj orbT.
      * by move=> j Hj; apply: Ho; rewrite in_cons Hj orbT.
    + exact: Ha i (mem_head i r).
    + exact: Hy i (mem_head i r).
    + exact: Hb i (mem_head i r).
    + exact: Ho i (mem_head i r). } move=> Ha Hy Hb Ho; rewrite (bb84_hist_so_deferred EA h).
  rewrite -(bb84_trace_so_seq_deferred EA h (r := enum 'I_M) (@enum_uniq 'I_M predT)).
  by apply: bb84_trace_so_seq_source_branch => i _; [exact: Ha | exact: Hy | exact: Hb | exact: Ho]. } move=> Ha Hy Hb Ho; rewrite (bb84_round_samples_weight_source_branch h s alice_basis bob_basis alice_bit Ha Hy Hb).
  exact: bb84_hist_so_source_branch. } have bb84_history_not_decoded : forall (h : hist), ~~ bb84_history_decoded h -> (exists i, bb84_basis_of_value (hist_a h i) = None \/ bb84_bit_of (hist_y h i) = None \/ bb84_basis_of_value (hist_b h i) = None) \/ (exists i, bb84_basis_of_value (hist_b h i) = None \/ bb84_outcome_of (hist_y' h i) = None).
{ clear rho s h EA; move=> h. have bb84_outcome_of_none : forall (v : V), ~~ bb84_has_outcome_value v -> bb84_outcome_of v = None.
{ clear h; move=> v. by rewrite /bb84_has_outcome_value; case: (bb84_outcome_of v). } rewrite /bb84_history_decoded => Hbad.
  have /existsP [i Hi] : [exists i, ~~ bb84_history_round_decoded h i] by rewrite -negb_forall Hbad.
  rewrite /bb84_history_round_decoded in Hi.
  case Ha: (bb84_has_basis_value (hist_a h i)).
  - case Hy: (bb84_has_bit_value (hist_y h i)).
    + case Hb: (bb84_has_basis_value (hist_b h i)).
      * case Ho: (bb84_has_outcome_value (hist_y' h i)). -- by move: Hi; rewrite Ha Hy Hb Ho. -- by right; exists i; right; apply: bb84_outcome_of_none; rewrite Ho.
      * by left; exists i; right; right; apply: bb84_basis_of_value_none; rewrite Hb.
    + left; exists i; right; left.
      have bb84_bit_of_none : forall v0 : V, ~~ bb84_has_bit_value v0 -> bb84_bit_of v0 = None.
      { by move=> v0; rewrite /bb84_has_bit_value; case: (bb84_bit_of v0). } by apply: bb84_bit_of_none; rewrite Hy.
  - by left; exists i; left; apply: bb84_basis_of_value_none; rewrite Ha. } rewrite /bb84_history_source_state /bb84_trace_source_state -bb84_history_decoded_traceE.
  case Hdecoded: (bb84_history_decoded h).
  - apply: bb84_hist_weighted_so_source_branch.
    + move=> i; rewrite /bb84_trace_alice_basis.
      have bb84_history_decoded_basis : forall (h0 : hist) (i0 : 'I_M), bb84_history_decoded h0 -> bb84_basis_of_value (hist_a h0 i0) = Some (haB h0 i0).
      { move=> h0 i0 /forallP/(_ i0); rewrite /bb84_history_round_decoded => /and4P [Ha _ _ _].
        exact: bb84_basis_of_value_decoded. } by apply: bb84_history_decoded_basis; rewrite Hdecoded.
    + move=> i; rewrite /bb84_trace_alice_bit.
      have bb84_history_decoded_bit : forall (h0 : hist) (i0 : 'I_M), bb84_history_decoded h0 -> bb84_bit_of (hist_y h0 i0) = Some (haY h0 i0).
      { move=> h0 i0 /forallP/(_ i0); rewrite /bb84_history_round_decoded => /and4P [_ Hy _ _]. exact: bb84_bit_of_decoded. } by apply: bb84_history_decoded_bit; rewrite Hdecoded.
    + by move=> i; rewrite /bb84_trace_bob_basis; apply: bb84_history_decoded_bob_basis; rewrite Hdecoded.
    + by move=> i; rewrite /bb84_trace_bob_outcome; apply: bb84_history_decoded_outcome; rewrite Hdecoded.
  - rewrite (bb84_hist_weighted_so_invalid EA s (h := h) rho); first by [].
    by apply: bb84_history_not_decoded; rewrite Hdecoded. Qed.

Local Notation bb84_scheme_args f := (f R L HL (bb84_cvar M) V (bb84_n P) (bb84_k P) (bb84_l P) (cd_ir_bits dev) M (bb84_Qtol P)
  (@BVa M) (@BVy M) (@BVb M) (@BVy' M) (@BVd M) (@bb84_signal_regs M LE LB) (@BVX M) (@BVZ M) (@BVK M)
  (@BVXA M) (@BVXB M) (@BVZA M) (@BVZB M) (@BVlam M) (@BVpec M) (@BVXhat M) (@BVg M) (@BVtA M) (@BVtB M)
  (@BVf M) (@BVS M) (@BVSh M) (@BVabort M) (@BVP M) vX vZ
  vO bb84_bot_val empty_transcript bb84_bool_val bb84_bit_val bb84_set_val bb84_set_of bb84_error_val
  bb84_device_dev_rho bb84_device_dev_meas bb84_tr_app_rounds bb84_tr_app_pe bb84_tr_app_ec bb84_tr_app_pa
  bb84_bits_on_val bb84_partial_bits_on_val bb84_err_count_val bb84_error_of bb84_unif_nsubset_mass (bb84_ir_pub_val (@cd_ir_pub R P q dev))
  (bb84_ir_dec_val (@cd_ir_dec R P q dev)) bb84_unif_vseed_mass (bb84_verify_hash_val (@cd_vh R P q dev))
  bb84_unif_pseed_mass (bb84_privacy_hash_val (@cd_pa R P q dev)) (bb84_eve_reg M LE LB)).

Ltac bb84_post_wt_nonneg := rewrite /bb84_history_post_weight; apply: history_post_weight_nonneg;
  [ move=> ? ? ?; exact: bb84_unif_nsubset_mass_nonneg | move=> ? ?; exact: bb84_unif_vseed_mass_nonneg
  | move=> ? ?; exact: bb84_unif_pseed_mass_nonneg ].

Local Notation bb84_wf_round i := (cmd_wf (bb84_eve_reg M LE LB) (@Round R L HL (bb84_cvar M) V (bb84_n P) (bb84_k P) M (@BVa M) (@BVy M)
    (@BVb M) (@BVy' M) (@BVd M) (@bb84_signal_regs M LE LB) (@BVX M) (@BVZ M) vX vZ
    vO bb84_bool_val bb84_bit_val bb84_set_val bb84_device_dev_rho bb84_device_dev_meas i)).
Local Notation bb84_wf_pe := (cmd_wf (bb84_eve_reg M LE LB) (@ParamEst R L HL (bb84_cvar M) V (bb84_n P) M
    (@BVy M) (@BVy' M) (@BVX M) (@BVZ M) (@BVK M) (@BVXA M) (@BVXB M) (@BVZA M) (@BVZB M) (@BVlam M)
    (@BVP M) bb84_bot_val bb84_set_of bb84_error_val bb84_tr_app_pe bb84_bits_on_val bb84_partial_bits_on_val bb84_err_count_val
    bb84_unif_nsubset_mass)).
Local Notation bb84_wf_ec := (cmd_wf (bb84_eve_reg M LE LB) (@ErrCorr R L HL (bb84_cvar M) V (cd_ir_bits dev)
    (@BVXA M) (@BVXB M) (@BVpec M) (@BVXhat M) (@BVg M) (@BVtA M) (@BVtB M) (@BVP M) bb84_tr_app_ec (bb84_ir_pub_val (@cd_ir_pub R P q dev))
    (bb84_ir_dec_val (@cd_ir_dec R P q dev)) bb84_unif_vseed_mass (bb84_verify_hash_val (@cd_vh R P q dev)))).
Local Notation bb84_wf_pa := (cmd_wf (bb84_eve_reg M LE LB) (@PrivAmp R L HL (bb84_cvar M) V (bb84_l P)
    (@BVXA M) (@BVXhat M) (@BVf M) (@BVS M) (@BVSh M) (@BVP M) bb84_tr_app_pa bb84_unif_pseed_mass
    (bb84_privacy_hash_val (@cd_pa R P q dev)))).

Definition bb84_run_pass_history_state (EA : adv)
    (xi : @cq_state R L HL (bb84_cvar M) V) : 'F[HL]_setT := (bb84_scheme_args (@run_pass_history_state)) EA xi.

Definition bb84_eval_scheme_state (EA : adv) (xi : @cq_state R L HL (bb84_cvar M) V)
    : @cq_state R L HL (bb84_cvar M) V := (bb84_scheme_args (@bb84_eval_scheme)) EA xi.

Definition bb84_run_pass_prob (EA : adv) (xi : @cq_state R L HL (bb84_cvar M) V) : R :=
  @run_pass_prob R L HL (bb84_cvar M) V (@BVabort M) bb84_bool_val (bb84_eval_scheme_state EA xi).

Local Definition bb84_pe_pass_indic (h : hist) (s : cstore) : bool := ~~ @pe_failed R (bb84_cvar M) V (bb84_n P) (bb84_k P) M (bb84_Qtol P)
    (@BVX M) (@BVZ M) (@BVlam M) bb84_set_of bb84_error_of (@paramest_store (bb84_cvar M) V M (@BVy M) (@BVy' M) (@BVZ M) (@BVK M) (@BVXA M)
    (@BVXB M) (@BVZA M) (@BVZB M) (@BVlam M) (@BVP M) bb84_set_of bb84_error_val bb84_tr_app_pe bb84_bits_on_val bb84_partial_bits_on_val
    bb84_err_count_val h (@announce_store (bb84_cvar M) V M (@BVa M) (@BVb M) (@BVd M) (@BVP M) bb84_tr_app_rounds (@rounds_store (bb84_cvar
    M) V M (@BVa M) (@BVy M) (@BVb M) (@BVy' M) (@BVd M) (@BVX M) (@BVZ M) vX vZ vO bb84_bool_val bb84_set_val h (bb84_start_store s)))).

Fact bb84_final_store_le_pe_pass_indic (h : hist) (s : cstore) :
  ((bb84_final_store h s (@BVabort M) == bb84_bool_val false)%:R : R) <= (bb84_pe_pass_indic h s)%:R.
Proof.
  rewrite ler_nat; case E: (bb84_final_store h s (@BVabort M) == bb84_bool_val false); last by [].
  have Hpe := final_store_pass_pe_ok (h := h) (s := s) bb84_bool_val_neq (@bb84_abort_neq_S M) (@bb84_abort_neq_Sh M) E.
  have Hindic : bb84_pe_pass_indic h s by rewrite /bb84_pe_pass_indic; exact: Hpe.
  by rewrite Hindic. Qed.

Fact bb84_pe_pass_history_key_sample_support (h : hist) (s : cstore) : ((bb84_pe_pass_indic h s)%:R * bb84_history_post_weight h s != 0) ->
    let s2 := @announce_store (bb84_cvar M) V M (@BVa M) (@BVb M) (@BVd M) (@BVP M) bb84_tr_app_rounds (@rounds_store (bb84_cvar M) V M
    (@BVa M) (@BVy M) (@BVb M) (@BVy' M) (@BVd M) (@BVX M) (@BVZ M) vX vZ vO bb84_bool_val bb84_set_val h (bb84_start_store s)) in
    (#|bb84_set_of (@hist_K V M h)| = bb84_n P) /\ (bb84_set_of (@hist_K V M h) \subset bb84_set_of (s2 (@BVX M))).
Proof.
  move=> Hcoef.
  set s2 := @announce_store (bb84_cvar M) V M (@BVa M) (@BVb M) (@BVd M) (@BVP M) bb84_tr_app_rounds (@rounds_store (bb84_cvar M) V M (@BVa M) (@BVy M) (@BVb M) (@BVy' M) (@BVd M) (@BVX M) (@BVZ M) vX vZ vO bb84_bool_val bb84_set_val h (bb84_start_store s)).
  have Hpe : bb84_pe_pass_indic h s. { apply: contraNT Hcoef => Hnot. by rewrite (negbTE Hnot) mul0r. } have Hpost : bb84_history_post_weight h s != 0. { apply/eqP=> Hzero. by move: Hcoef; rewrite Hzero mulr0 eqxx. } have Henabled : (bb84_n P <= #|bb84_set_of (s2 (@BVX M))|)%N.
  { rewrite /s2. apply: pe_pass_key_sample_enabled; last by move: Hpe; rewrite /bb84_pe_pass_indic => H'; exact: H'.
    - by rewrite /BVX /BVK; apply: bb84_cvar_inr_neq; rewrite -val_eqE /= !inordK.
    - by rewrite /BVX /BVXA; apply: bb84_cvar_inr_neq; rewrite -val_eqE /= !inordK.
    - by rewrite /BVX /BVXB; apply: bb84_cvar_inr_neq; rewrite -val_eqE /= !inordK.
    - by rewrite /BVX /BVZA; apply: bb84_cvar_inr_neq; rewrite -val_eqE /= !inordK.
    - by rewrite /BVX /BVZB; apply: bb84_cvar_inr_neq; rewrite -val_eqE /= !inordK.
    - by rewrite /BVX /BVP; apply: bb84_cvar_inr_neq; rewrite -val_eqE /= !inordK.
    - by rewrite /BVX /BVlam; apply: bb84_cvar_inr_neq; rewrite -val_eqE /= !inordK. } have Hkey : @key_sample_mass R (bb84_cvar M) V (bb84_n P) M (@BVX M) bb84_bot_val bb84_set_of (@bb84_unif_nsubset_mass R M (bb84_n P) (bb84_l P) (cd_ir_bits dev) (cd_vseed_count dev) (cd_tag_count dev) (cd_paseed_count dev)) s2 (@hist_K V M h) != 0.
  { move: Hpost; rewrite /bb84_history_post_weight /s2. exact: history_post_weight_key_sample_nonzero. } rewrite /key_sample_mass Henabled in Hkey.
  have Hsupport := bb84_unif_nsubset_mass_support (m := bb84_n P) (X := bb84_set_of (s2 (@BVX M))) (v := @hist_K V M h) Hkey.
  move/andP: Hsupport => [/eqP Hcard Hsub]; exact: conj Hcard Hsub. Qed.

Fact bb84_pe_pass_history_selected_key_basis (h : hist) (s : cstore) (j : 'I_(bb84_n P)) (i : 'I_M) :
  ((bb84_pe_pass_indic h s)%:R * bb84_history_post_weight h s != 0) -> bb84_selected_index (bb84_set_of (@hist_K V M h)) j = Some i ->
  haB h i = BasisX /\ hbB h i = BasisX.
Proof.
  move=> Hcoef Hsel; have [_ Hsub] := bb84_pe_pass_history_key_sample_support Hcoef.
  have HiK := bb84_selected_index_mem Hsel.
  have HMpos : (0 < M)%N := leq_ltn_trans (leq0n i) (ltn_ord i).
  set s2 := @announce_store (bb84_cvar M) V M (@BVa M) (@BVb M) (@BVd M) (@BVP M) bb84_tr_app_rounds (@rounds_store (bb84_cvar M) V M (@BVa M) (@BVy M) (@BVb M) (@BVy' M) (@BVd M) (@BVX M) (@BVZ M) vX vZ vO bb84_bool_val bb84_set_val h (bb84_start_store s)).
  have Hkey := announce_trace_key_set h.1 s HMpos.
  have HiX : i \in bb84_set_of (s2 (@BVX M)). { move/subsetP: Hsub => Hsub; exact: Hsub. } move: HiX; rewrite /s2 Hkey !inE /trace_key_set /trace_key_round /trace_detected => /andP [/andP [/eqP Ha /eqP Hb] _].
  split.
  - by rewrite /bb84_history_alice_basis /hist_a /hist_choice Ha.
  - by rewrite /bb84_history_bob_basis /hist_b /hist_choice Hb. Qed.

Definition bb84_pass_history_source_state (EA : adv) (xi : @cq_state R L HL (bb84_cvar M) V) : 'F[HL]_setT := \sum_s \sum_(h : hist)
    ((((bb84_pe_pass_indic h s)%:R) * bb84_history_post_weight h s)%:C *: bb84_history_source_state EA h (xi s)).

Definition bb84_pass_history_public_readout_state (Epub : {set L}) (public_register_state : cstore -> 'F[HL]_Epub)
    (EA : adv) (xi : @cq_state R L HL (bb84_cvar M) V) : 'F[HL]_setT :=
  \sum_s \sum_(h : hist) ((((bb84_final_store h s (@BVabort M) == bb84_bool_val false)%:R) * bb84_history_post_weight h s)%:C *:
      @replaceso R L HL Epub (public_register_state (bb84_final_store h s)) (bb84_history_readout_state EA h (xi s))).

Definition bb84_pass_history_public_source_state (Epub : {set L}) (public_register_state : cstore -> 'F[HL]_Epub)
    (EA : adv) (xi : @cq_state R L HL (bb84_cvar M) V) : 'F[HL]_setT :=
  \sum_s \sum_(h : hist) ((((bb84_final_store h s (@BVabort M) == bb84_bool_val false)%:R) * bb84_history_post_weight h s)%:C *:
      @replaceso R L HL Epub (public_register_state (bb84_final_store h s)) (bb84_history_source_state EA h (xi s))).

Definition bb84_pe_pass_history_public_source_state (Epub : {set L}) (public_register_state : cstore -> 'F[HL]_Epub) (EA : adv) (xi :
    @cq_state R L HL (bb84_cvar M) V) : 'F[HL]_setT := \sum_s \sum_(h : hist) ((((bb84_pe_pass_indic h s)%:R) * bb84_history_post_weight h
    s)%:C *: @replaceso R L HL Epub (public_register_state (bb84_final_store h s)) (bb84_history_source_state EA h (xi s))).

Fact bb84_run_pass_history_state_fullE (EA : adv) (xi : @cq_state R L HL (bb84_cvar M) V) :
  bb84_run_pass_history_state EA xi = \sum_s \sum_(h : hist) ((((bb84_final_store h s (@BVabort M) == bb84_bool_val false)%:R) *
      bb84_history_post_weight h s)%:C *: bb84_history_source_state EA h (xi s)).
Proof.
  rewrite /bb84_run_pass_history_state /run_pass_history_state.
  apply: eq_bigr => s _; apply: eq_bigr => h _.
  rewrite hist_wt_split -/(bb84_start_store s) -/(bb84_history_post_weight h s).
  set pass := (bb84_final_store h s (@BVabort M) == bb84_bool_val false)%:R.
  set post := bb84_history_post_weight h s.
  set samples := @round_samples_weight R (bb84_cvar M) V (bb84_n P) (bb84_k P) M vX vZ bitV h (bb84_start_store s).
  set Hso := @hist_so R L HL V M (@bb84_signal_regs M LE LB) empty_transcript (bb84_device_dev_rho) (bb84_device_dev_meas) (bb84_eve_reg M LE LB) EA h (xi s).
  rewrite [samples * post]mulrC rmorphM /= -scalerA.
  rewrite [samples%:C *: Hso] (bb84_hist_weighted_so_source_or_zero EA h (bb84_start_store s) (xi s)).
  by rewrite scalerA -rmorphM /=. Qed.

Fact bb84_run_pass_history_state_traceE (EA : adv) (xi : @cq_state R L HL (bb84_cvar M) V) : (forall i, @BVa M i != @BVy M i) -> (forall i,
    @BVP M != @BVa M i) -> (forall i, @BVP M != @BVy M i) -> (forall i, @BVP M != @BVb M i) -> (forall i, @BVP M != @BVy' M i) -> (forall i,
    @BVP M != @BVd M i) -> @BVP M != @BVX M -> @BVP M != @BVZ M -> @BVP M != @BVabort M -> @complex.Re R (\Tr (bb84_run_pass_history_state
    EA xi)) = bb84_run_pass_prob EA xi.
Proof. move=> Hay HPa HPy HPb HPy' HPd HPX HPZ HPabort. rewrite /bb84_run_pass_history_state /bb84_run_pass_prob /bb84_eval_scheme_state. exact: ((bb84_scheme_args (@run_pass_history_state_trace)) EA xi Hay HPa HPy HPb HPy' HPd HPX HPZ HPabort). Qed.

Definition bb84_source_pass_prob (EA : adv) (xi : @cq_state R L HL (bb84_cvar M) V) : R :=
  @complex.Re R (\Tr (bb84_pass_history_source_state EA xi)).

Lemma bb84_run_pass_prob_le_source (EA : adv) (xi : @cq_state R L HL (bb84_cvar M) V) : (forall i, @BVa M i != @BVy M i) -> (forall i, @BVP
    M != @BVa M i) -> (forall i, @BVP M != @BVy M i) -> (forall i, @BVP M != @BVb M i) -> (forall i, @BVP M != @BVy' M i) -> (forall i, @BVP
    M != @BVd M i) -> @BVP M != @BVX M -> @BVP M != @BVZ M -> @BVP M != @BVabort M -> (forall s, xi s \is psdlf) -> bb84_run_pass_prob EA xi
    <= bb84_source_pass_prob EA xi.
Proof.
  move=> Hay HPa HPy HPb HPy' HPd HPX HPZ HPabort Hxi.
  rewrite -(bb84_run_pass_history_state_traceE EA xi Hay HPa HPy HPb HPy' HPd HPX HPZ HPabort).
  rewrite (bb84_run_pass_history_state_fullE EA xi) /bb84_source_pass_prob /bb84_pass_history_source_state.
  have HRe_realM : forall (r : R) (z : @hermitian.C R), @complex.Re R (r%:C * z) = r * @complex.Re R z.
  { move=> r z. by case: z => zr zi /=; rewrite mul0r subr0. } rewrite [X in @complex.Re R X <= _]linear_sum /= [X in _ <= @complex.Re R X]linear_sum /=.
  rewrite raddf_sum /= raddf_sum /=.
  apply: ler_sum => s _.
  rewrite [X in @complex.Re R X <= _]linear_sum /= [X in _ <= @complex.Re R X]linear_sum /=.
  rewrite raddf_sum /= raddf_sum /=.
  apply: ler_sum => h _.
  have Hpost_ge0 : 0 <= bb84_history_post_weight h s.
  { bb84_post_wt_nonneg. } have HT_ge0 : 0 <= @complex.Re R (\Tr (bb84_history_source_state EA h (xi s))).
  { have := psdlf_trlf (bb84_history_source_state_psd EA h (Hxi s)). by rewrite lecE /= => /andP[]. } rewrite !linearZ /= !HRe_realM; apply: ler_wpM2r; first exact: HT_ge0.
  apply: ler_wpM2r; first exact: Hpost_ge0.
  exact: bb84_final_store_le_pe_pass_indic. Qed.

Lemma bb84_eval_scheme_state_psd (EA : adv) (xi : @cq_state R L HL (bb84_cvar M) V) : (forall i, bb84_wf_round i) -> bb84_wf_pe ->
    bb84_wf_ec -> bb84_wf_pa -> (forall s, xi s \is psdlf) -> forall s, bb84_eval_scheme_state EA xi s \is psdlf.
Proof. move=> Hround Hpe Hec Hpa Hxi; rewrite /bb84_eval_scheme_state /bb84_eval_scheme. apply: denote_psd; last exact: Hxi. exact: ((bb84_scheme_args (@bb84_program_scheme_wf)) Hround Hpe Hec Hpa). Qed.

Lemma bb84_pass_history_public_readout_state_psd (Epub : {set L}) (public_register_state : cstore -> 'F[HL]_Epub) (EA : adv) (xi : @cq_state
    R L HL (bb84_cvar M) V) : (forall s, public_register_state s \is den1lf) -> (forall s, xi s \is psdlf) ->
    bb84_pass_history_public_readout_state (Epub:=Epub) public_register_state EA xi \is psdlf.
Proof.
  move=> Hpub Hxi; rewrite /bb84_pass_history_public_readout_state.
  apply: psdlf_sum => s _; apply: psdlf_sum => h _.
  have Hcoef : 0 <= (bb84_final_store h s (@BVabort M) == bb84_bool_val false)%:R * bb84_history_post_weight h s.
  { apply: mulr_ge0; first by case: (bb84_final_store h s (@BVabort M) == bb84_bool_val false).
    bb84_post_wt_nonneg. } apply: psdlfZ; first by rewrite lecR.
  apply: replaceso_psd; first exact: den1lf_psd (Hpub (bb84_final_store h s)).
  exact: bb84_history_readout_state_psd (Hxi s). Qed.

Definition bb84_pe_pass_history_public_readout_state (Epub : {set L}) (public_register_state : cstore -> 'F[HL]_Epub) (EA : adv) (xi :
    @cq_state R L HL (bb84_cvar M) V) : 'F[HL]_setT := \sum_s \sum_(h : hist) ((((bb84_pe_pass_indic h s)%:R) * bb84_history_post_weight h
    s)%:C *: @replaceso R L HL Epub (public_register_state (bb84_final_store h s)) (bb84_history_readout_state EA h (xi s))).

Lemma bb84_pe_pass_history_public_readout_state_psd (Epub : {set L}) (public_register_state : cstore -> 'F[HL]_Epub) (EA : adv) (xi :
    @cq_state R L HL (bb84_cvar M) V) : (forall s, public_register_state s \is den1lf) -> (forall s, xi s \is psdlf) ->
    bb84_pe_pass_history_public_readout_state (Epub:=Epub) public_register_state EA xi \is psdlf.
Proof.
  move=> Hpub Hxi; rewrite /bb84_pe_pass_history_public_readout_state.
  apply: psdlf_sum => s _; apply: psdlf_sum => h _.
  have Hcoef : 0 <= (bb84_pe_pass_indic h s)%:R * bb84_history_post_weight h s.
  { apply: mulr_ge0; first by case: (bb84_pe_pass_indic h s).
    bb84_post_wt_nonneg. } apply: psdlfZ; first by rewrite lecR.
  apply: replaceso_psd; first exact: den1lf_psd (Hpub (bb84_final_store h s)).
  exact: bb84_history_readout_state_psd (Hxi s). Qed.

Definition bb84_vf_history_public_readout_state (Epub : {set L}) (public_register_state : cstore -> 'F[HL]_Epub) (EA : adv) (xi : @cq_state
    R L HL (bb84_cvar M) V) : 'F[HL]_setT := \sum_s \sum_(h : hist) ((((bb84_pe_pass_indic h s)%:R - (bb84_final_store h s (@BVabort M) ==
    bb84_bool_val false)%:R) * bb84_history_post_weight h s)%:C *: @replaceso R L HL Epub (public_register_state (bb84_final_store h s))
    (bb84_history_readout_state EA h (xi s))).

Fact bb84_vf_history_public_readout_state_psd (Epub : {set L}) (public_register_state : cstore -> 'F[HL]_Epub) (EA : adv) (xi : @cq_state R
    L HL (bb84_cvar M) V) : (forall s, public_register_state s \is den1lf) -> (forall s, xi s \is psdlf) ->
    bb84_vf_history_public_readout_state (Epub:=Epub) public_register_state EA xi \is psdlf.
Proof.
  move=> Hpub Hxi; rewrite /bb84_vf_history_public_readout_state.
  apply: psdlf_sum => s _; apply: psdlf_sum => h _.
  have Hcoef : 0 <= ((bb84_pe_pass_indic h s)%:R - (bb84_final_store h s (@BVabort M) == bb84_bool_val false)%:R) * bb84_history_post_weight h s.
  { apply: mulr_ge0; first by rewrite subr_ge0; exact: bb84_final_store_le_pe_pass_indic.
    bb84_post_wt_nonneg. } apply: psdlfZ; first by rewrite lecR.
  apply: replaceso_psd; first exact: den1lf_psd (Hpub (bb84_final_store h s)).
  exact: bb84_history_readout_state_psd (Hxi s). Qed.

Fact bb84_pe_pass_history_public_readout_state_split (Epub : {set L}) (public_register_state : cstore -> 'F[HL]_Epub)
    (EA : adv) (xi : @cq_state R L HL (bb84_cvar M) V) :
  bb84_pe_pass_history_public_readout_state (Epub:=Epub) public_register_state EA xi = bb84_pass_history_public_readout_state (Epub:=Epub)
    public_register_state EA xi + bb84_vf_history_public_readout_state (Epub:=Epub) public_register_state EA xi.
Proof. rewrite /bb84_pe_pass_history_public_readout_state /bb84_pass_history_public_readout_state /bb84_vf_history_public_readout_state. rewrite -big_split /=; apply: eq_bigr => s _. rewrite -big_split /=; apply: eq_bigr => h _. by rewrite -scalerDl -realcD -mulrDl addrC subrK. Qed.

Fact bb84_source_pass_prob_nonneg (EA : adv) (xi : @cq_state R L HL (bb84_cvar M) V) : (forall i, @BVa M i != @BVy M i) -> (forall i, @BVP
    M != @BVa M i) -> (forall i, @BVP M != @BVy M i) -> (forall i, @BVP M != @BVb M i) -> (forall i, @BVP M != @BVy' M i) -> (forall i, @BVP
    M != @BVd M i) -> @BVP M != @BVX M -> @BVP M != @BVZ M -> @BVP M != @BVabort M -> (forall i, bb84_wf_round i) -> bb84_wf_pe ->
    bb84_wf_ec -> bb84_wf_pa -> (forall s, xi s \is psdlf) -> 0 <= bb84_source_pass_prob EA xi.
Proof.
  move=> Hay HPa HPy HPb HPy' HPd HPX HPZ HPabort Hround Hpe Hec Hpa Hxi.
  have Hrun_nn : 0 <= bb84_run_pass_prob EA xi.
  { rewrite /bb84_run_pass_prob; apply: run_event_prob_nonneg. exact: (bb84_eval_scheme_state_psd EA Hround Hpe Hec Hpa Hxi). } have Hdom := bb84_run_pass_prob_le_source EA Hay HPa HPy HPb HPy' HPd HPX HPZ HPabort Hxi.
  exact: (le_trans Hrun_nn Hdom). Qed.

Fact bb84_source_pass_prob_le1 (EA : adv) (xi : @cq_state R L HL (bb84_cvar M) V) : (forall i, @BVa M i != @BVy M i) -> (forall i, @BVP M
    != @BVa M i) -> (forall i, @BVP M != @BVy M i) -> (forall i, @BVP M != @BVb M i) -> (forall i, @BVP M != @BVy' M i) -> (forall i, @BVP M
    != @BVd M i) -> @BVP M != @BVX M -> @BVP M != @BVZ M -> @BVP M != @BVabort M -> (forall i, bb84_wf_round i) -> bb84_wf_pe -> bb84_wf_ec
    -> bb84_wf_pa -> cq_wf xi -> bb84_source_pass_prob EA xi <= 1.
Proof.
  move=> Hay HPa HPy HPb HPy' HPd HPX HPZ HPabort Hround Hpe Hec Hpa Hxi.
  have Hxi_psd : forall s, xi s \is psdlf by case: Hxi.
  have HRe_realM : forall (r : R) (z : @hermitian.C R), @complex.Re R (r%:C * z) = r * @complex.Re R z.
  { move=> r z. by case: z => zr zi /=; rewrite mul0r subr0. } have HmassE : @cq_mass R L HL (bb84_cvar M) V (bb84_eval_scheme_state EA xi) = \sum_s \sum_(h : hist) @complex.Re R (\Tr ((bb84_history_post_weight h s)%:C *: bb84_history_source_state EA h (xi s))).
  { transitivity (@run_event_prob R L HL (bb84_cvar M) V xpredT (bb84_eval_scheme_state EA xi)).
    { by rewrite /run_event_prob /cq_mass. } rewrite {1}/bb84_eval_scheme_state ((bb84_scheme_args (@denote_run_decomp)) EA xi Hay HPa HPy HPb HPy' HPd HPX HPZ HPabort).
    rewrite run_event_prob_sum; apply: eq_bigr => s _.
    rewrite /history_sum run_event_prob_sum; apply: eq_bigr => h _.
    rewrite run_event_prob_history_branch mul1r.
    congr (@complex.Re R _); congr (\Tr _).
    rewrite hist_wt_split -/(bb84_start_store s) -/(bb84_history_post_weight h s).
    set post := bb84_history_post_weight h s.
    set samples := @round_samples_weight R (bb84_cvar M) V (bb84_n P) (bb84_k P) M vX vZ bitV h (bb84_start_store s).
    set Hso := @hist_so R L HL V M (@bb84_signal_regs M LE LB) empty_transcript (bb84_device_dev_rho) (bb84_device_dev_meas) (bb84_eve_reg M LE LB) EA h (xi s).
    rewrite [samples * post]mulrC rmorphM /= -scalerA.
    by rewrite [samples%:C *: Hso] (bb84_hist_weighted_so_source_or_zero EA h (bb84_start_store s) (xi s)). } have Hmass1 : @cq_mass R L HL (bb84_cvar M) V (bb84_eval_scheme_state EA xi) = 1.
  { rewrite /bb84_eval_scheme_state.
    exact: ((bb84_scheme_args (@bb84_eval_mass1)) EA xi Hround Hpe Hec Hpa Hxi). } rewrite -Hmass1 HmassE /bb84_source_pass_prob /bb84_pass_history_source_state.
  rewrite [X in @complex.Re R X <= _]linear_sum /= raddf_sum /=; apply: ler_sum => s _.
  rewrite [X in @complex.Re R X <= _]linear_sum /= raddf_sum /=; apply: ler_sum => h _.
  have Hpost_ge0 : 0 <= bb84_history_post_weight h s.
  { bb84_post_wt_nonneg. } have HT_ge0 : 0 <= @complex.Re R (\Tr (bb84_history_source_state EA h (xi s))).
  { have := psdlf_trlf (bb84_history_source_state_psd EA h (Hxi_psd s)). by rewrite lecE /= => /andP[]. } rewrite !linearZ /= !HRe_realM; apply: ler_wpM2r; first exact: HT_ge0.
  rewrite -{2}(mul1r (bb84_history_post_weight h s)); apply: ler_wpM2r; first exact: Hpost_ge0.
  by case: (bb84_pe_pass_indic h s); rewrite ?ler01. Qed.

Local Close Scope lfun_scope.

End CertifiedPreparation.
