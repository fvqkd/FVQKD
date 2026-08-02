(* example.v -- Protocol-facing BB84 theorem layer                      *)
(* Module: qkd.example.example                                          *)
(* Culmination of the protocol layer: the security corollary            *)
(* bb84_secure_protocol for the denotational run of bb84_program.       *)
From HB Require Import structures.
From mathcomp.classical Require Import boolp classical_sets.
From mathcomp Require Import all_boot all_order all_algebra fingroup perm.
From mathcomp.reals Require Import reals.
From mathcomp.analysis.topology_theory Require Import topology.
From mathcomp.analysis Require Import exp.
From mathcomp.real_closed Require Import mxtens.
From quantum.external Require Import spectral complex.
From quantum Require Import mcextra mcaextra notation hermitian quantum cpo mxpred extnum ctopology svd mxnorm hspace inhabited.
From quantum.dirac Require Import hstensor.

Import Order.TTheory GRing.Theory Num.Theory Num.Def MxLownerOrder.
Import VectorInternalTheory.

From utils Require Import bitstr exports.
From utils.mx Require Import prop.
From entropy Require Import def.
From eur Require Import def prop.
From lhl Require Import def prop construction post_hash dephase util.
From qkd.bb84 Require Import def model prop bb84.
From qkd.protocol Require Import syntax semantics qkd_cmd.
From qkd.example Require Import device program run stat.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Local Open Scope lfun_scope.
Local Open Scope qkd_scope.
Ltac cvinr := apply: bb84_cvar_inr_neq; rewrite -val_eqE /= !inordK.
Ltac cvun := rewrite ?/BVa ?/BVy ?/BVb ?/BVy' ?/BVd ?/BVX ?/BVZ ?/BVK ?/BVXA ?/BVXB ?/BVZA ?/BVZB ?/BVlam ?/BVpec ?/BVXhat ?/BVg
  ?/BVtA ?/BVtB ?/BVf ?/BVS ?/BVSh ?/BVabort ?/BVP.
Ltac cvne := cvun; try rewrite /=; cvinr.
Lemma disjoint_setDUl (T : finType) (A B : {set T}) : [disjoint A & [set: T] :\: (A :|: B)].
Proof. by rewrite mathcomp.boot.finset.setTD mathcomp.boot.finset.disjoints_subset mathcomp.boot.finset.setCK mathcomp.boot.finset.subsetUl. Qed.

Lemma disjoint_setDUr (T : finType) (A B : {set T}) : [disjoint B & [set: T] :\: (A :|: B)].
Proof. by rewrite mathcomp.boot.finset.setTD mathcomp.boot.finset.disjoints_subset mathcomp.boot.finset.setCK mathcomp.boot.finset.subsetUr. Qed.

Section RegisterAllocation.
Variable R : realType.
Notation chsType := (@chsType R).
Variables (P : @bb84_protocol R) (q : R) (dev : bb84_certified_device P q) (LE : finType) (HE : LE -> chsType).
Definition fin_hilbert_of_dim (d : nat) (Hd : (0 < d)%N) : ihbFinType := FinInhabited.Pack (FinInhabited.Class (Choice.on 'I_d)
    (Countable.on 'I_d) (Finite.on 'I_d) (isPointed.Build 'I_d (Ordinal Hd))).
Definition bb84_register_index := 'I_8.
Definition bb84_reg_S : bb84_register_index := Ordinal (isT : (0 < 8)%N).
Definition bb84_reg_E : bb84_register_index := Ordinal (isT : (1 < 8)%N).
Definition bb84_reg_Zkey : bb84_register_index := Ordinal (isT : (2 < 8)%N).
Definition bb84_reg_Bq : bb84_register_index := Ordinal (isT : (3 < 8)%N).
Definition bb84_reg_Zp : bb84_register_index := Ordinal (isT : (4 < 8)%N).
Definition bb84_reg_Fl : bb84_register_index := Ordinal (isT : (5 < 8)%N).
Definition bb84_reg_Zl : bb84_register_index := Ordinal (isT : (6 < 8)%N).
Definition bb84_reg_Ppub : bb84_register_index := Ordinal (isT : (7 < 8)%N).
Definition bb84_register_dim (r : bb84_register_index) : nat := match val r with | 0 => 2 ^ bb84_n P
  | 1 => #|{: bb84_eur_public (bb84_round_limit P) (cd_vseed_count dev)}| | 2 => 2 ^ bb84_n P | 3 => 2 ^ bb84_n P | 4 => 2 ^ bb84_n P
  | 5 => cd_paseed_count dev | 6 => 2 ^ bb84_l P | 7 => (2 ^ cd_ir_bits dev) * cd_tag_count dev | _ => 1 end.
Fact bb84_register_dim_pos (r : bb84_register_index) : (0 < bb84_register_dim r)%N.
Proof. rewrite /bb84_register_dim; case: r => m Hm /=. case: m Hm => [|m] Hm; first by rewrite expn_gt0. case: m Hm => [|m] Hm;
  first by apply/card_gt0P; exists ([ffun _ : 'I_(bb84_round_limit P) => None], ([set i : 'I_(bb84_round_limit P) | false] : {set 'I_(bb84_round_limit P)}), ([ffun _ : 'I_(bb84_round_limit P) => None] : bb84_partial_bits (bb84_round_limit P)), ([ffun _ : 'I_(bb84_round_limit P) => None] : bb84_partial_bits (bb84_round_limit P)), (None : option 'I_(cd_vseed_count dev))); rewrite inE.
  case: m Hm => [|m] Hm; first by rewrite expn_gt0. case: m Hm => [|m] Hm; first by rewrite expn_gt0. case: m Hm => [|m] Hm; first by rewrite expn_gt0. case: m Hm => [|m] Hm; first exact: cd_paseed_pos. case: m Hm => [|m] Hm; first by rewrite expn_gt0.
  case: m Hm => [|m] Hm; first by rewrite muln_gt0 expn_gt0 cd_tag_pos. by []. Qed.

Definition bb84_register_space (r : bb84_register_index) : chsType := 'Hs (fin_hilbert_of_dim (bb84_register_dim_pos r)).
Notation M := (bb84_round_limit P).
Notation L := (bb84_label M LE bb84_register_index).
Notation HL := (bb84_label_space HE bb84_register_space).
Notation ec_bits := (cd_ir_bits dev).
Notation vseed_count := (cd_vseed_count dev).
Notation tag_count := (cd_tag_count dev).
Notation paseed_count := (cd_paseed_count dev).
Notation V := (bb84_val M (bb84_n P) (bb84_l P) ec_bits vseed_count tag_count paseed_count).
Local Notation dev_final_args F h s := (F R (bb84_cvar M) V (bb84_n P) (bb84_k P) (bb84_l P) (cd_ir_bits dev) M (bb84_Qtol P)
  (@BVa M) (@BVy M) (@BVb M) (@BVy' M) (@BVd M) (@BVX M) (@BVZ M) (@BVK M) (@BVXA M) (@BVXB M)
  (@BVZA M) (@BVZB M) (@BVlam M) (@BVpec M) (@BVXhat M) (@BVg M) (@BVtA M) (@BVtB M) (@BVf M)
  (@BVS M) (@BVSh M) (@BVabort M) (@BVP M) (bb84_basis_value dev BasisX) (bb84_basis_value dev BasisZ)
  (bb84_outcome_val None) bb84_bot_val bb84_empty_transcript_val bb84_bool_val bb84_set_val bb84_set_of
  bb84_error_val bb84_tr_app_rounds bb84_tr_app_pe bb84_tr_app_ec bb84_tr_app_pa bb84_bits_on_val
  bb84_partial_bits_on_val bb84_err_count_val bb84_error_of (bb84_ir_pub_val (@cd_ir_pub R P q dev))
  (bb84_ir_dec_val (@cd_ir_dec R P q dev)) (bb84_verify_hash_val (@cd_vh R P q dev))
  (bb84_privacy_hash_val (@cd_pa R P q dev)) h s) (only parsing).
Local Notation dev_weight_args F h s := (F R (bb84_cvar M) V (bb84_n P) (bb84_k P) (bb84_l P) (cd_ir_bits dev) M (bb84_Qtol P)
  (@BVa M) (@BVy M) (@BVb M) (@BVy' M) (@BVd M) (@BVX M) (@BVZ M) (@BVK M) (@BVXA M) (@BVXB M)
  (@BVZA M) (@BVZB M) (@BVlam M) (@BVpec M) (@BVXhat M) (@BVg M) (@BVtA M) (@BVtB M) (@BVf M)
  (@BVS M) (@BVSh M) (@BVabort M) (@BVP M) (bb84_basis_value dev BasisX) (bb84_basis_value dev BasisZ)
  (bb84_outcome_val None) bb84_bot_val bb84_empty_transcript_val bb84_bool_val bb84_set_val bb84_set_of
  bb84_error_val bb84_tr_app_rounds bb84_tr_app_pe bb84_tr_app_ec bb84_tr_app_pa bb84_bits_on_val
  bb84_partial_bits_on_val bb84_err_count_val bb84_error_of bb84_unif_nsubset_mass
  (bb84_ir_pub_val (@cd_ir_pub R P q dev)) (bb84_ir_dec_val (@cd_ir_dec R P q dev))
  bb84_unif_vseed_mass (bb84_verify_hash_val (@cd_vh R P q dev)) bb84_unif_pseed_mass
  (bb84_privacy_hash_val (@cd_pa R P q dev)) h s) (only parsing).
Local Notation dev_sann h s := (@announce_store (bb84_cvar M) V M (@BVa M) (@BVb M) (@BVd M) (@BVP M) bb84_tr_app_rounds
  (@rounds_store (bb84_cvar M) V M (@BVa M) (@BVy M) (@BVb M) (@BVy' M) (@BVd M) (@BVX M) (@BVZ M)
    (bb84_basis_value dev BasisX) (bb84_basis_value dev BasisZ) (bb84_outcome_val None) bb84_bool_val bb84_set_val h
    (@start_store (bb84_cvar M) V M (@BVX M) (@BVZ M) (@BVabort M) (@BVP M) bb84_empty_transcript_val bb84_bool_val bb84_set_val s)))
  (only parsing).
Local Notation dev_sfin h s := (@paramest_store (bb84_cvar M) V M (@BVy M) (@BVy' M) (@BVZ M) (@BVK M) (@BVXA M)
  (@BVXB M) (@BVZA M) (@BVZB M) (@BVlam M) (@BVP M) bb84_set_of bb84_error_val bb84_tr_app_pe bb84_bits_on_val
  bb84_partial_bits_on_val bb84_err_count_val h (dev_sann h s)) (only parsing).
Definition bb84_history_errcorr_store (h : @run_history V M) (s : @store (bb84_cvar M) V) : @store (bb84_cvar M) V :=
  @history_errcorr_store (bb84_cvar M) V ec_bits M (@BVa M) (@BVy M) (@BVb M) (@BVy' M) (@BVd M) (@BVX M) (@BVZ M) (@BVK M) (@BVXA M)
    (@BVXB M) (@BVZA M) (@BVZB M) (@BVlam M) (@BVpec M) (@BVXhat M) (@BVg M) (@BVtA M) (@BVtB M) (@BVabort M) (@BVP M)
    (bb84_basis_value dev BasisX) (bb84_basis_value dev BasisZ) (bb84_outcome_val None) bb84_empty_transcript_val
    bb84_bool_val bb84_set_val bb84_set_of bb84_error_val bb84_tr_app_rounds bb84_tr_app_pe bb84_tr_app_ec
    bb84_bits_on_val bb84_partial_bits_on_val bb84_err_count_val (bb84_ir_pub_val (@cd_ir_pub R P q dev))
    (bb84_ir_dec_val (@cd_ir_dec R P q dev)) (bb84_verify_hash_val (@cd_vh R P q dev)) h s.
Definition bb84_history_pass_weight (h : @run_history V M) (s : @store (bb84_cvar M) V) : R := @history_pass_weight R (bb84_cvar M) V
    (bb84_n P) (bb84_k P) (bb84_l P) ec_bits M (bb84_Qtol P) (@BVa M) (@BVy M) (@BVb M) (@BVy' M) (@BVd M)
    (@BVX M) (@BVZ M) (@BVK M) (@BVXA M) (@BVXB M) (@BVZA M) (@BVZB M) (@BVlam M) (@BVpec M) (@BVXhat M) (@BVg M) (@BVtA M) (@BVtB M)
    (@BVf M) (@BVS M) (@BVSh M) (@BVabort M) (@BVP M) (bb84_basis_value dev BasisX) (bb84_basis_value dev BasisZ)
    (bb84_outcome_val None) bb84_bot_val bb84_empty_transcript_val bb84_bool_val bb84_set_val bb84_set_of bb84_error_val
    bb84_tr_app_rounds bb84_tr_app_pe bb84_tr_app_ec bb84_tr_app_pa bb84_bits_on_val bb84_partial_bits_on_val bb84_err_count_val
    bb84_error_of bb84_unif_nsubset_mass (bb84_ir_pub_val (@cd_ir_pub R P q dev)) (bb84_ir_dec_val (@cd_ir_dec R P q dev))
    bb84_unif_vseed_mass (bb84_verify_hash_val (@cd_vh R P q dev)) bb84_unif_pseed_mass (bb84_privacy_hash_val (@cd_pa R P q dev)) h s.
Definition bb84_history_pass_prefix_weight (h : @run_history V M) (s : @store (bb84_cvar M) V) : R :=
  @history_pass_prefix_weight R (bb84_cvar M) V (bb84_n P) (bb84_k P) (bb84_l P) ec_bits M (bb84_Qtol P)
    (@BVa M) (@BVy M) (@BVb M) (@BVy' M) (@BVd M) (@BVX M) (@BVZ M) (@BVK M) (@BVXA M) (@BVXB M) (@BVZA M) (@BVZB M) (@BVlam M) (@BVpec M)
    (@BVXhat M) (@BVg M) (@BVtA M) (@BVtB M) (@BVf M) (@BVS M) (@BVSh M) (@BVabort M) (@BVP M)
    (bb84_basis_value dev BasisX) (bb84_basis_value dev BasisZ) (bb84_outcome_val None) bb84_bot_val bb84_empty_transcript_val
    bb84_bool_val bb84_set_val bb84_set_of bb84_error_val bb84_tr_app_rounds bb84_tr_app_pe bb84_tr_app_ec bb84_tr_app_pa
    bb84_bits_on_val bb84_partial_bits_on_val bb84_err_count_val bb84_error_of bb84_unif_nsubset_mass
    (bb84_ir_pub_val (@cd_ir_pub R P q dev)) (bb84_ir_dec_val (@cd_ir_dec R P q dev))
    bb84_unif_vseed_mass (bb84_verify_hash_val (@cd_vh R P q dev)) (bb84_privacy_hash_val (@cd_pa R P q dev)) h s.
Definition bb84_prefix_errcorr_store (p : @run_prefix V M) (f : V) (s : @store (bb84_cvar M) V) : @store (bb84_cvar M) V :=
  bb84_history_errcorr_store (prefix_history p f) s.
Definition bb84_prefix_pass_weight (p : @run_prefix V M) (f : V) (s : @store (bb84_cvar M) V) : R :=
  bb84_history_pass_weight (prefix_history p f) s.
Definition bb84_prefix_pass_base (p : @run_prefix V M) (s : @store (bb84_cvar M) V) : R := bb84_history_pass_prefix_weight
    (prefix_history p bb84_bot_val) s.
Definition bb84_reg (r : bb84_register_index) : {set L} := bb84_bridge_reg r.
Definition bb84_S : {set L} := bb84_reg bb84_reg_S.
Definition bb84_Eve : {set L} := bb84_eve_reg M LE bb84_register_index.
Definition bb84_Epub : {set L} := bb84_reg bb84_reg_E.
Definition bb84_E : {set L} := bb84_Eve :|: bb84_Epub.
Definition bb84_Zkey : {set L} := bb84_reg bb84_reg_Zkey.
Definition bb84_Bq : {set L} := bb84_reg bb84_reg_Bq.
Definition bb84_Zp : {set L} := bb84_reg bb84_reg_Zp.
Definition bb84_Fl : {set L} := bb84_reg bb84_reg_Fl.
Definition bb84_Zl : {set L} := bb84_reg bb84_reg_Zl.
Definition bb84_Ppub : {set L} := bb84_reg bb84_reg_Ppub.
Lemma bb84_bridge_reg_disjoint (a b : bb84_register_index) : a != b -> [disjoint bb84_reg a & bb84_reg b].
Proof. move=> Hab; rewrite /bb84_reg /bb84_bridge_reg disjoint1X !inE; rewrite /bb84_bridge_label. apply/negP=> /eqP H.
  have Hab_eq : a = b by case: H. by move: Hab; rewrite Hab_eq eqxx. Qed.

Lemma bb84_bridge_qmem_disjoint (a : bb84_register_index) : [disjoint bb84_reg a & bb84_Eve].
Proof. by rewrite /bb84_reg /bb84_bridge_reg /bb84_Eve /bb84_eve_reg disjoint1X inE /bb84_bridge_label. Qed.

Fact bb84_bridge_E_disjoint (a : bb84_register_index) : a != bb84_reg_E -> [disjoint bb84_reg a & bb84_E].
Proof. by move=> Ha; rewrite /bb84_E disjointXU bb84_bridge_qmem_disjoint bb84_bridge_reg_disjoint. Qed.

Lemma bb84_E_bridge_disjoint (a : bb84_register_index) : a != bb84_reg_E -> [disjoint bb84_E & bb84_reg a].
Proof. by move=> Ha; rewrite disjoint_sym bb84_bridge_E_disjoint. Qed.

Lemma dim_bb84_reg (r : bb84_register_index) : dim ('H[HL]_(bb84_reg r)) = bb84_register_dim r.
Proof. have dim_fin_hilbert_of_dim : forall (d : nat) (Hd : (0 < d)%N), dim ('Hs (fin_hilbert_of_dim Hd) : chsType) = d.
  { move=> d Hd. by rewrite /fin_hilbert_of_dim -(@ihb_dim_cast R _) card_ord. }
have dim_bb84_register_space : forall (r : bb84_register_index), dim (bb84_register_space r) = bb84_register_dim r.
{ clear r; move=> r. exact: dim_fin_hilbert_of_dim. } by rewrite /bb84_reg /bb84_bridge_reg dim_setten big_set1 /bb84_label_space /bb84_bridge_label dim_bb84_register_space. Qed.

Fact bb84_dim_Epub : dim ('H[HL]_bb84_Epub) = #|{: bb84_eur_public (bb84_round_limit P) (cd_vseed_count dev)}|.
Proof. by rewrite /bb84_Epub dim_bb84_reg /bb84_register_dim. Qed.

Definition bb84_public_idx (p : bb84_eur_public (bb84_round_limit P) (cd_vseed_count dev)) : 'Idx[HL]_bb84_Epub :=
  n2i (cast_ord (esym bb84_dim_Epub) (enum_rank p)).
Definition bb84_public_projector (p : bb84_eur_public (bb84_round_limit P) (cd_vseed_count dev)) : 'F[HL]_bb84_Epub :=
  [> deltav (bb84_public_idx p); deltav (bb84_public_idx p) <].
Definition bb84_public_register_state (s : @store (bb84_cvar M) V) : 'F[HL]_bb84_Epub := bb84_public_projector (bb84_eur_public_of_store s).
Lemma bb84_public_register_state_den1lf (s : @store (bb84_cvar M) V) : bb84_public_register_state s \is den1lf.
Proof. have bb84_public_projector_den1lf : forall (p : bb84_eur_public (bb84_round_limit P) (cd_vseed_count dev)), bb84_public_projector p
  \is den1lf.
  { move=> p; apply/den1lfP; split; first exact: outp_psd. by rewrite /bb84_public_projector outp_trlf dv_dot eqxx. }
exact: bb84_public_projector_den1lf. Qed.

Lemma bb84_disSE : [disjoint bb84_S & bb84_E].
Proof. exact: bb84_bridge_E_disjoint. Qed.

Lemma bb84_disS_Epub : [disjoint bb84_S & bb84_Epub].
Proof. exact: bb84_bridge_reg_disjoint. Qed.

Fact bb84_disSZ : [disjoint bb84_S & bb84_Zkey].
Proof. exact: bb84_bridge_reg_disjoint. Qed.

Fact bb84_disSBq : [disjoint bb84_S & bb84_Bq].
Proof. exact: bb84_bridge_reg_disjoint. Qed.

Lemma bb84_disSF : [disjoint bb84_S & bb84_Fl].
Proof. exact: bb84_bridge_reg_disjoint. Qed.

Lemma bb84_disSZl : [disjoint bb84_S & bb84_Zl].
Proof. exact: bb84_bridge_reg_disjoint. Qed.

Fact bb84_disEZ : [disjoint bb84_E & bb84_Zkey].
Proof. exact: bb84_E_bridge_disjoint. Qed.

Fact bb84_disEBq : [disjoint bb84_E & bb84_Bq].
Proof. exact: bb84_E_bridge_disjoint. Qed.

Fact bb84_disEZl : [disjoint bb84_E & bb84_Zl].
Proof. exact: bb84_E_bridge_disjoint. Qed.

Lemma bb84_disZBq : [disjoint bb84_Zkey & bb84_Bq].
Proof. exact: bb84_bridge_reg_disjoint. Qed.

Lemma bb84_disFZl : [disjoint bb84_Fl & bb84_Zl].
Proof. exact: bb84_bridge_reg_disjoint. Qed.

Lemma bb84_disSP : [disjoint bb84_S & bb84_Ppub].
Proof. exact: bb84_bridge_reg_disjoint. Qed.

Lemma bb84_disEP : [disjoint bb84_E & bb84_Ppub].
Proof. exact: bb84_E_bridge_disjoint. Qed.

Lemma bb84_disPSE : [disjoint bb84_Ppub & (bb84_S :|: bb84_E)].
Proof. by rewrite disjointXU (disjoint_sym bb84_Ppub bb84_S) bb84_disSP (disjoint_sym bb84_Ppub bb84_E) bb84_disEP. Qed.

Lemma bb84_disSEpub : [disjoint bb84_S & bb84_E :|: bb84_Ppub].
Proof. by rewrite disjointXU bb84_disSE bb84_disSP. Qed.

Lemma bb84_disP_SEpub : [disjoint bb84_Ppub & bb84_S :|: bb84_Epub].
Proof. have HPS : [disjoint bb84_Ppub & bb84_S] by rewrite disjoint_sym bb84_disSP. have HPEpub : [disjoint bb84_Ppub & bb84_Epub] by exact:
  bb84_bridge_reg_disjoint. by rewrite disjointXU HPS HPEpub. Qed.

Lemma bb84_disEpubF : [disjoint bb84_E :|: bb84_Ppub & bb84_Fl].
Proof. have bb84_disEF : [disjoint bb84_E & bb84_Fl] by exact: bb84_E_bridge_disjoint. have HPF : [disjoint bb84_Ppub & bb84_Fl] by exact:
  bb84_bridge_reg_disjoint. by rewrite disjointUX bb84_disEF HPF. Qed.

Lemma bb84_disEpubZl : [disjoint bb84_E :|: bb84_Ppub & bb84_Zl].
Proof. have HPZl : [disjoint bb84_Ppub & bb84_Zl] by exact: bb84_bridge_reg_disjoint. by rewrite disjointUX bb84_disEZl HPZl. Qed.

Lemma bb84_disZl_FEpub : [disjoint bb84_Zl & (bb84_Fl :|: (bb84_E :|: bb84_Ppub))].
Proof. have HZF : [disjoint bb84_Zl & bb84_Fl] by rewrite disjoint_sym bb84_disFZl. have HZE : [disjoint bb84_Zl & bb84_E] by rewrite
  disjoint_sym bb84_disEZl. have HZP : [disjoint bb84_Zl & bb84_Ppub] by exact: bb84_bridge_reg_disjoint.
  by rewrite disjointXU HZF disjointXU HZE HZP. Qed.

Lemma bb84_dim_S : (2 ^ bb84_n P)%N = dim ('H[HL]_bb84_S).
Proof. by rewrite dim_bb84_reg. Qed.

Lemma bb84_dim_Zkey : (2 ^ bb84_n P)%N = dim ('H[HL]_bb84_Zkey).
Proof. by rewrite dim_bb84_reg. Qed.

Lemma bb84_dim_Bq : (2 ^ bb84_n P)%N = dim ('H[HL]_bb84_Bq).
Proof. by rewrite dim_bb84_reg. Qed.

Lemma bb84_dim_Fl : cd_paseed_count dev = dim ('H[HL]_bb84_Fl).
Proof. by rewrite dim_bb84_reg. Qed.

Lemma bb84_dim_Zl : dim ('H[HL]_bb84_Zl) = (2 ^ bb84_l P)%N.
Proof. by rewrite dim_bb84_reg. Qed.

Fact bb84_dim_Ppub : dim ('H[HL]_bb84_Ppub) = ((2 ^ cd_ir_bits dev) * cd_tag_count dev)%N.
Proof. by rewrite dim_bb84_reg. Qed.

Lemma bb84_round_cmd_wf (i : 'I_M) : cmd_wf bb84_Eve (@Round R L HL (bb84_cvar M) V (bb84_n P) (bb84_k P) M (@BVa M) (@BVy M)
      (@BVb M) (@BVy' M) (@BVd M) (@bb84_signal_regs M LE bb84_register_index) (@BVX M) (@BVZ M)
      (bb84_basis_value dev BasisX) (bb84_basis_value dev BasisZ) (bb84_outcome_val None) bb84_bool_val bb84_bit_val
      bb84_set_val (bb84_device_dev_rho HE bb84_register_space) (bb84_device_dev_meas HE bb84_register_space) i).
Proof. have bb84_signal_Eve_disjoint : forall (i : 'I_M), [disjoint @bb84_signal_regs M LE bb84_register_index i & bb84_Eve].
{ clear i; move=> i. by rewrite /bb84_signal_regs /bb84_signal_reg /bb84_Eve /bb84_eve_reg disjoint1X inE /bb84_signal_label. }
apply: Round_wf.
  - move=> s; split.
    + move=> v; rewrite /mu_basis /pX /bb84_basis_value; apply: bb84_basis_bool_mass_nonneg.
      * by rewrite invr_ge0 addr_ge0 ?ler01 ?sqrtr_ge0.
      * by rewrite invf_le1; [rewrite lerDl sqrtr_ge0 | rewrite ltr_wpDr ?ltr01 ?sqrtr_ge0].
    + by rewrite /mu_basis /pX /bb84_basis_value bb84_basis_bool_mass_sum1.
  - move=> s; split.
    + by move=> v; rewrite /mu_bit; exact: bb84_bit_mass_nonneg.
    + by rewrite /mu_bit bb84_bit_mass_sum1.
  - exact: bb84_signal_Eve_disjoint.
  - by move=> s; exact: bb84_device_dev_rho_den1.
  - by move=> s; exact: bb84_device_dev_meas_complete_any. Qed.

Lemma bb84_paramest_cmd_wf : cmd_wf bb84_Eve (@ParamEst R L HL (bb84_cvar M) V (bb84_n P) M (@BVy M) (@BVy' M) (@BVX M) (@BVZ M) (@BVK M)
      (@BVXA M) (@BVXB M) (@BVZA M) (@BVZB M) (@BVlam M) (@BVP M) bb84_bot_val bb84_set_of bb84_error_val
      bb84_tr_app_pe bb84_bits_on_val bb84_partial_bits_on_val bb84_err_count_val bb84_unif_nsubset_mass).
Proof. apply: ParamEst_wf => s; split.
  - move=> v; rewrite /paramest_K_mu /has_key_sample; case: ifP => Hkey.
    + exact: bb84_unif_nsubset_mass_nonneg.
    + by rewrite ler0n.
  - rewrite /paramest_K_mu /has_key_sample; case Hkey: (bb84_n P <= #|bb84_set_of (s (@BVX M))|)%N.
    + by apply: bb84_unif_nsubset_mass_sum1; exact: bb84_nsubset_count_pos.
    + rewrite (bigD1 bb84_bot_val) //=. by rewrite [X in _ + X]big1 ?addr0 // => v Hv; rewrite (negbTE Hv). Qed.

Lemma bb84_errcorr_cmd_wf : cmd_wf bb84_Eve (@ErrCorr R L HL (bb84_cvar M) V (cd_ir_bits dev)
      (@BVXA M) (@BVXB M) (@BVpec M) (@BVXhat M) (@BVg M) (@BVtA M) (@BVtB M) (@BVP M) bb84_tr_app_ec
      (bb84_ir_pub_val (@cd_ir_pub R P q dev)) (bb84_ir_dec_val (@cd_ir_dec R P q dev))
      bb84_unif_vseed_mass (bb84_verify_hash_val (@cd_vh R P q dev))).
Proof. apply: ErrCorr_wf => s; split.
  - exact: bb84_unif_vseed_mass_nonneg.
  - exact: (bb84_unif_vseed_mass_sum1 s (cd_vseed_pos dev)). Qed.

Lemma bb84_privamp_cmd_wf : cmd_wf bb84_Eve (@PrivAmp R L HL (bb84_cvar M) V (bb84_l P) (@BVXA M) (@BVXhat M) (@BVf M) (@BVS M) (@BVSh M)
      (@BVP M) bb84_tr_app_pa bb84_unif_pseed_mass (bb84_privacy_hash_val (@cd_pa R P q dev))).
Proof. apply: PrivAmp_wf => s; split.
  - exact: bb84_unif_pseed_mass_nonneg.
  - exact: (bb84_unif_pseed_mass_sum1 s (cd_paseed_pos dev)). Qed.

Local Ltac abpart := by [assumption | exact: bb84_bool_val_neq | exact: bb84_abort_neq_P | exact: bb84_abort_neq_f | exact:
  bb84_abort_neq_S | exact: bb84_abort_neq_Sh | exact: bb84_round_cmd_wf | exact: bb84_paramest_cmd_wf | exact: bb84_errcorr_cmd_wf |
  exact: bb84_privamp_cmd_wf | rewrite eq_sym bb84_abort_neq_P | move=> ?; cvun | cvne].
Lemma bb84_eval_scheme_abort_pass_partition (EA : @adversary R L HL V bb84_Eve) (xi : @cq_state R L HL (bb84_cvar M) V) :
  cq_wf xi -> @run_abort_prob R L HL (bb84_cvar M) V (@BVabort M) bb84_bool_val (bb84_eval_scheme_state EA xi) +
  @run_pass_prob R L HL (bb84_cvar M) V (@BVabort M) bb84_bool_val (bb84_eval_scheme_state EA xi) = 1.
Proof. move=> Hxi; rewrite /bb84_eval_scheme_state. apply: run_mass_from_abort_support. 1-4: abpart. 1-4: abpart. 1-4: abpart. 1-4: abpart.
  1-4: abpart. 1-4: abpart. 1-4: abpart. 1-4: abpart. 1-4: abpart. all: abpart. Qed.

Definition bb84_Fl_index (f : 'I_(cd_paseed_count dev)) : 'Idx[HL]_bb84_Fl := n2i (cast_ord bb84_dim_Fl f).
Definition bb84_pa_seed_ord (f : 'Idx[HL]_bb84_Fl) : 'I_(cd_paseed_count dev) := cast_ord (esym bb84_dim_Fl) (i2n f).
Definition bb84_pa_input_ord (x : 'Idx[HL]_bb84_S) : 'I_(2 ^ bb84_n P) := cast_ord (esym bb84_dim_S) (i2n x).
Definition bb84_pa_output_idx (z : 'I_(2 ^ bb84_l P)) : 'Idx[HL]_bb84_Zl := n2i (cast_ord (esym bb84_dim_Zl) z).
Definition bb84_pa_hash_index (f : 'Idx[HL]_bb84_Fl) (x : 'Idx[HL]_bb84_S) : 'Idx[HL]_bb84_Zl := bb84_pa_output_idx
    (@cd_pa R P q dev (bb84_pa_seed_ord f) (bb84_pa_input_ord x)).
Fact bb84_pa_hash_index_two_univ : @two_univ R _ _ _ bb84_pa_hash_index.
Proof. rewrite /bb84_pa_hash_index /bb84_pa_seed_ord /bb84_pa_input_ord /bb84_pa_output_idx.
  apply: (@two_univ_transport R 'I_(cd_paseed_count dev) 'Idx[HL]_bb84_Fl 'I_(2 ^ bb84_n P) 'Idx[HL]_bb84_S 'I_(2 ^ bb84_l P) 'Idx[HL]_bb84_Zl (@cd_pa R P q dev) (fun f => cast_ord (esym bb84_dim_Fl) (i2n f)) (fun x => cast_ord (esym bb84_dim_S) (i2n x)) (fun z => n2i (cast_ord (esym bb84_dim_Zl) z))).
  - exists (fun f => n2i (cast_ord bb84_dim_Fl f)).
    + by move=> f; apply: i2n_inj; rewrite n2iK cast_ordKV.
    + by move=> f; rewrite n2iK cast_ordK.
  - by move=> x y Hxy; apply: i2n_inj; apply: cast_ord_inj Hxy.
  - exists (fun z => cast_ord bb84_dim_Zl (i2n z)).
    + by move=> z; rewrite n2iK cast_ordKV.
    + by move=> z; apply: i2n_inj; rewrite n2iK cast_ordK.
  - exact: cd_pa_two_univ. Qed.

Lemma bb84_cq_block_projector_public (x0 x : 'Idx[HL]_bb84_S) (rho : 'F[HL]_(bb84_E :|: bb84_Ppub)) : cq_block bb84_disSEpub x
    (([> deltav x0 ; deltav x0 <] \O rho) : 'F[HL]_(bb84_S :|: (bb84_E :|: bb84_Ppub))) = if x == x0 then rho else 0.
Proof. rewrite /cq_block. set K := (([> deltav x ; deltav x <] \O (\1 : 'F[HL]_(bb84_E :|: bb84_Ppub))) : 'F[HL]_(bb84_S :|: (bb84_E :|:
  bb84_Ppub))). set rho0 := (([> deltav x0 ; deltav x0 <] \O rho) : 'F[HL]_(bb84_S :|: (bb84_E :|: bb84_Ppub))). case Hx: (x == x0).
  - move/eqP: Hx => Hx. have Hproj : K \o rho0 \o K = rho0.
    { have HK : K = [> deltav x0 ; deltav x0 <] \⊗ (\1 : 'F[HL]_(bb84_E :|: bb84_Ppub)).
      { by apply: to_Fnd_inj; rewrite /K Hx (sdotFT _ _ bb84_disSEpub) to_Fnd_tenE. } have Hrho0 : rho0 = [> deltav x0 ; deltav x0 <] \⊗ rho. { by apply: to_Fnd_inj; rewrite (sdotFT _ _ bb84_disSEpub) to_Fnd_tenE. } rewrite HK Hrho0; rewrite -tenf_comp; last exact: bb84_disSEpub. rewrite comp_lfun1l outp_comp dv_dot eqxx scale1r; rewrite -tenf_comp; last exact: bb84_disSEpub.
        by rewrite comp_lfun1r outp_comp dv_dot eqxx scale1r. } by rewrite Hproj ptrace_castl_sdot_trace_l outp_trlf dv_dot eqxx scale1r.
  - have Hproj : K \o rho0 \o K = 0.
    { have HK : K = [> deltav x ; deltav x <] \⊗ (\1 : 'F[HL]_(bb84_E :|: bb84_Ppub)).
      { by apply: to_Fnd_inj; rewrite (sdotFT _ _ bb84_disSEpub) to_Fnd_tenE. } have Hrho0 : rho0 = [> deltav x0 ; deltav x0 <] \⊗ rho.
      { by apply: to_Fnd_inj; rewrite (sdotFT _ _ bb84_disSEpub) to_Fnd_tenE. } rewrite HK Hrho0; rewrite -tenf_comp; last exact: bb84_disSEpub. rewrite comp_lfun1l outp_comp dv_dot. by rewrite Hx /= scale0r ten0f comp_lfun0l. }
by rewrite Hproj /ptrace_castl /ptrace_cast_gen linear0 linear0. Qed.

Fact bb84_post_hash_projector_public (x0 : 'Idx[HL]_bb84_S) (rho : 'F[HL]_(bb84_E :|: bb84_Ppub)) :
  let eqZFE := esym (finset.setUA bb84_Zl bb84_Fl (bb84_E :|: bb84_Ppub)) in post_hash_state bb84_disSEpub bb84_pa_hash_index
    (([> deltav x0 ; deltav x0 <] \O rho) : 'F[HL]_(bb84_S :|: (bb84_E :|: bb84_Ppub))) = castlf (eqZFE, eqZFE)
    ((dim 'H[HL]_bb84_Fl)%:R^-1 *: \sum_(f : 'Idx[HL]_bb84_Fl) ([> deltav (bb84_pa_hash_index f x0) ; deltav (bb84_pa_hash_index f x0) <] \O
          [> deltav f ; deltav f <] \O rho)).
Proof. rewrite /post_hash_state /=; congr (castlf (_, _) _); congr (_ *: _). apply: eq_bigr => f _; set z0 := bb84_pa_hash_index f x0.
  have Hxsum (z : 'Idx[HL]_bb84_Zl) : \sum_(x : 'Idx[HL]_bb84_S | bb84_pa_hash_index f x == z) cq_block bb84_disSEpub x (([> deltav x0 ; deltav x0 <] \O rho) : 'F[HL]_(bb84_S :|: (bb84_E :|: bb84_Ppub))) = if z == z0 then rho else 0.
  { case Hz: (z == z0).
    - move/eqP: Hz => Hz. rewrite (bigD1 x0); last by rewrite Hz /z0 eqxx. rewrite /= bb84_cq_block_projector_public eqxx.
      rewrite [X in _ + X]big1 ?addr0 // => x Hx. move/andP: Hx => [_ Hxx0]; by rewrite bb84_cq_block_projector_public (negbTE Hxx0).
    - apply: big1 => x Hhash; rewrite bb84_cq_block_projector_public. case Hxx0: (x == x0); last by []. move/eqP: Hxx0 => Hxx0; move: Hhash; rewrite Hxx0 /z0 => /eqP Hbad. by move: Hz; rewrite -Hbad eqxx. } rewrite (bigD1 z0) //= Hxsum eqxx.
      rewrite [X in _ + X]big1 ?addr0 // => z Hz. rewrite Hxsum; have Hz0 : z == z0 = false by move: Hz; case: (z == z0).
      by rewrite Hz0 sdotf0. Qed.

Fact bb84_post_hash_projector_public_paseed (x0 : 'Idx[HL]_bb84_S) (rho : 'F[HL]_(bb84_E :|: bb84_Ppub)) :
  post_hash_state bb84_disSEpub bb84_pa_hash_index (([> deltav x0 ; deltav x0 <] \O rho) : 'F[HL]_(bb84_S :|: (bb84_E :|: bb84_Ppub))) =
  (((cd_paseed_count dev)%:R)^-1)%:C *: \sum_(f : 'I_(cd_paseed_count dev)) ([> deltav (bb84_pa_hash_index (bb84_Fl_index f) x0) ;
          deltav (bb84_pa_hash_index (bb84_Fl_index f) x0) <] \⊗ ([> deltav (bb84_Fl_index f) ; deltav (bb84_Fl_index f) <] \⊗ rho)).
Proof. set eqZFE := esym (finset.setUA bb84_Zl bb84_Fl (bb84_E :|: bb84_Ppub)); rewrite bb84_post_hash_projector_public linearZ /=
  -bb84_dim_Fl. congr (_ *: _).
  - by rewrite -natrC -fmorphV.
  - rewrite raddf_sum /=. rewrite [in LHS](reindex_onto bb84_Fl_index bb84_pa_seed_ord).
    + apply: eq_big => f.
      * by rewrite /= /bb84_pa_seed_ord /bb84_Fl_index n2iK cast_ordK eqxx.
      * move=> _; apply: to_Fnd_inj; rewrite Fnd_cast !to_Fnd_sdotE !to_Fnd_tenE. have HZF : [disjoint bb84_Zl & bb84_Fl] by rewrite disjoint_sym bb84_disFZl. have HZF_Epub : [disjoint bb84_Zl :|: bb84_Fl & bb84_E :|: bb84_Ppub].
        { have HZEpub : [disjoint bb84_Zl & bb84_E :|: bb84_Ppub] by rewrite disjoint_sym bb84_disEpubZl.
          have HFEpub : [disjoint bb84_Fl & bb84_E :|: bb84_Ppub] by rewrite disjoint_sym bb84_disEpubF.
          by rewrite disjointUX HZEpub HFEpub. } rewrite [X in (X \· _)%FND]dotFT; last exact: HZF. rewrite dotFT; last exact: HZF_Epub.
          by rewrite tenFA.
    + by move=> f _; apply: i2n_inj; rewrite /bb84_pa_seed_ord /bb84_Fl_index n2iK cast_ordKV. Qed.

Fact bb84_post_hash_projector_public_pseed_val (x0 : 'Idx[HL]_bb84_S) (rho : 'F[HL]_(bb84_E :|: bb84_Ppub)) (s : @store (bb84_cvar M) V) :
  let branch := fun fval => match bb84_paseed_of fval with | Some f => ([> deltav (bb84_pa_hash_index (bb84_Fl_index f) x0) ;
          deltav (bb84_pa_hash_index (bb84_Fl_index f) x0) <] \⊗ ([> deltav (bb84_Fl_index f) ; deltav (bb84_Fl_index f) <] \⊗ rho))
    | None => 0 end in post_hash_state bb84_disSEpub bb84_pa_hash_index (([> deltav x0 ; deltav x0 <] \O rho) :
      'F[HL]_(bb84_S :|: (bb84_E :|: bb84_Ppub))) = \sum_f ((bb84_unif_pseed_mass s f)%:C *: branch f).
Proof. rewrite bb84_post_hash_projector_public_paseed. pose branch : V -> 'F[HL]_(bb84_Zl :|: (bb84_Fl :|: (bb84_E :|: bb84_Ppub))) := fun
  fval => match bb84_paseed_of fval with | Some f => ([> deltav (bb84_pa_hash_index (bb84_Fl_index f) x0) ; deltav (bb84_pa_hash_index (bb84_Fl_index f) x0) <] \⊗ ([> deltav (bb84_Fl_index f) ; deltav (bb84_Fl_index f) <] \⊗ rho)) | None => 0 end. transitivity (\sum_(f : 'I_(cd_paseed_count dev)) (((cd_paseed_count dev)%:R)^-1)%:C *: branch (bb84_paseed_val (Some f))).
  - rewrite scaler_sumr. apply: eq_bigr => f _. by rewrite /branch bb84_paseed_of_val.
  - rewrite -(@bb84_unif_pseed_val_support_sum R M (bb84_n P) (bb84_l P) (cd_ir_bits dev) (cd_vseed_count dev) (cd_tag_count dev) (cd_paseed_count dev) _ s branch). by apply: eq_bigr => f _. Qed.

Lemma bb84_dim_SEB : (((2 ^ bb84_n P) * dim ('H[HL]_bb84_E)) * (2 ^ bb84_n P))%N = dim ('H[HL]_((bb84_S :|: bb84_E) :|: bb84_Bq)).
Proof. have bb84_disSE_Bq : [disjoint bb84_S :|: bb84_E & bb84_Bq] by rewrite disjointUX bb84_disSBq bb84_disEBq.
  by rewrite (tenv_dim bb84_disSE_Bq) (tenv_dim bb84_disSE) -bb84_dim_S -bb84_dim_Bq. Qed.

Section BB84ZSrcProgScaffold.
Variable rhofull : @adversary R L HL V bb84_Eve -> @cq_state R L HL (bb84_cvar M) V ->
  'M[(@hermitian.C R)]_(bb84_full_string_count P * dim ('H[HL]_bb84_E) * bb84_full_string_count P).
Hypothesis Hrhofull_den1 : forall (EA : @adversary R L HL V bb84_Eve) (xi : @cq_state R L HL (bb84_cvar M) V), rhofull EA xi \is den1mx.
Definition bb84_zsrc_prog (EA : @adversary R L HL V bb84_Eve) (xi : @cq_state R L HL (bb84_cvar M) V) : bb84_zsource P :=
  @BB84ZSource R P (dim ('H[HL]_bb84_E)) (rhofull EA xi) (Hrhofull_den1 EA xi).
End BB84ZSrcProgScaffold.
Fact bb84_low_pass_nonabort_le (eps ebar eps_s p_abort p_pass : R) :
  0 < eps -> 0 < ebar -> eps + ebar <= eps_s -> bb84_pass_prob_le p_abort p_pass -> p_pass <= eps ^+ 2 -> 1 - p_abort <= eps_s.
Proof. move=> eps_pos ebar_pos Hbudget Hpass_le Hpass_case. have Hnonabort_le_pass := bb84_pass_prob_le_bound Hpass_le;
  have Habort_ge0 := bb84_pass_prob_le_abort_ge0 Hpass_le. have Hnonabort_le1 : 1 - p_abort <= 1 by rewrite lerBlDr lerDl.
  case: (lerP eps 1) => [Heps_le1 | Hone_lt_eps].
  - have Heps2_le_eps : eps ^+ 2 <= eps.
    { rewrite expr2; have Htmp : eps * eps <= eps * 1 by exact: (ler_pM (ltW eps_pos) (ltW eps_pos) (lexx eps) Heps_le1).
      by rewrite mulr1 in Htmp. } have Heps_le_sum : eps <= eps + ebar by rewrite lerDl ltW.
      exact: le_trans Hnonabort_le_pass (le_trans Hpass_case (le_trans Heps2_le_eps (le_trans Heps_le_sum Hbudget))).
  - have Hone_le_eps_s : 1 <= eps_s.
    { have Heps_lt_sum : eps < eps + ebar by rewrite ltrDl. exact: ltW (lt_le_trans (lt_trans Hone_lt_eps Heps_lt_sum) Hbudget). }
exact: le_trans Hnonabort_le1 Hone_le_eps_s. Qed.

Definition bb84_key_default : 'I_(2 ^ bb84_n P).
Proof. exact: Ordinal (expn_gt0 2 (bb84_n P)). Defined.
Definition bb84_raw_key_index (v : V) : 'I_(2 ^ bb84_n P) := odflt bb84_key_default (bb84_raw_key_of v).
Definition bb84_ec_default : 'I_(2 ^ cd_ir_bits dev).
Proof. exact: Ordinal (expn_gt0 2 (cd_ir_bits dev)). Defined.
Definition bb84_ec_index (v : V) : 'I_(2 ^ cd_ir_bits dev) := odflt bb84_ec_default (bb84_ec_of v).
Definition bb84_tag_default : 'I_(cd_tag_count dev).
Proof. exact: Ordinal (cd_tag_pos dev). Defined.
Definition bb84_tag_index (v : V) : 'I_(cd_tag_count dev) := odflt bb84_tag_default (bb84_tag_of v).
Definition bb84_paseed_default : 'I_(cd_paseed_count dev).
Proof. exact: Ordinal (cd_paseed_pos dev). Defined.
Definition bb84_paseed_index (v : V) : 'I_(cd_paseed_count dev) := odflt bb84_paseed_default (bb84_paseed_of v).
Definition bb84_final_key_default : 'I_(2 ^ bb84_l P).
Proof. exact: Ordinal (expn_gt0 2 (bb84_l P)). Defined.
Definition bb84_final_key_index (v : V) : 'I_(2 ^ bb84_l P) := odflt bb84_final_key_default (bb84_final_key_of v).
Fact bb84_final_store_raw_key_of (h : @run_history V M) (s : @store (bb84_cvar M) V) :
  #|bb84_set_of (@hist_K V M h)| = bb84_n P -> @bb84_raw_key_of M (bb84_n P) (bb84_l P) (cd_ir_bits dev)
    (cd_vseed_count dev) (cd_tag_count dev) (cd_paseed_count dev) (dev_final_args (@final_store) h s (@BVXA M)) = Some (bitstring_to_ord
      (fun j => match bb84_selected_index (bb84_set_of (@hist_K V M h)) j with | Some i =>
        if bb84_read_bit (dev_sann h s (@BVy M i)) is Some b then b else false | None => false end)).
Proof. move=> Hcard. set fs := dev_final_args (@final_store) h s. set bits := fun i : 'I_M => dev_sann h s (@BVy M i).
  have Hstore : fs (@BVXA M) = bb84_bits_on_val (bb84_set_of (@hist_K V M h)) bits.
  { rewrite /fs /bits; apply: final_store_XA_bits_on; by [move=> ?; cvun | cvne]. } by rewrite Hstore bb84_raw_key_of_bits_on_val Hcard eqxx. Qed.

Fact bb84_final_store_Sv_hash_value (h : @run_history V M) (s : @store (bb84_cvar M) V) : let fs := dev_final_args (@final_store) h s in
  fs (@BVabort M) == bb84_bool_val false -> @bb84_final_key_of M (bb84_n P) (bb84_l P) (cd_ir_bits dev)
    (cd_vseed_count dev) (cd_tag_count dev) (cd_paseed_count dev) (fs (@BVS M)) = match
    @bb84_paseed_of M (bb84_n P) (bb84_l P) (cd_ir_bits dev) (cd_vseed_count dev) (cd_tag_count dev) (cd_paseed_count dev) (@hist_f V M h),
    @bb84_raw_key_of M (bb84_n P) (bb84_l P) (cd_ir_bits dev) (cd_vseed_count dev) (cd_tag_count dev) (cd_paseed_count dev) (fs (@BVXA M))
  with | Some f, Some x => Some (@cd_pa R P q dev f x) | _, _ => None end.
Proof. move=> fs Hpass. set spe := dev_sfin h s. set sec := @errcorr_store (bb84_cvar M) V (cd_ir_bits dev) M (@BVXA M) (@BVXB M) (@BVpec M)
  (@BVXhat M) (@BVg M) (@BVtA M) (@BVtB M) (@BVP M) bb84_tr_app_ec (bb84_ir_pub_val (@cd_ir_pub R P q dev)) (bb84_ir_dec_val (@cd_ir_dec R P q dev)) (bb84_verify_hash_val (@cd_vh R P q dev)) h spe. have HSv : fs (@BVS M) = bb84_privacy_hash_val (@cd_pa R P q dev) (bb84_l P) (@hist_f V M h) (sec (@BVXA M)).
  { rewrite /fs; apply: final_store_Sv; by [exact: Hpass | rewrite /bb84_bool_val | cvne]. } have HsecXA : sec (@BVXA M) = spe (@BVXA M) by rewrite /sec; apply: errcorr_store_XA; cvne. have HfsXA : fs (@BVXA M) = spe (@BVXA M) by rewrite /fs /spe; apply: final_store_XA; cvne.
    rewrite HSv HsecXA -HfsXA /bb84_privacy_hash_val. case: (bb84_paseed_of (@hist_f V M h)) => [f|]; case: (bb84_raw_key_of (fs (@BVXA M))) => [x|]; by rewrite bb84_final_key_of_val. Qed.

Fact bb84_final_store_pa_seed_index (h : @run_history V M) (s : @store (bb84_cvar M) V) : let fs := dev_final_args (@final_store) h s in
  fs (@BVabort M) == bb84_bool_val false -> bb84_paseed_index (fs (@BVf M)) = bb84_paseed_index (@hist_f V M h).
Proof. move=> fs Hpass. rewrite /fs. rewrite (dev_final_args (@final_store_fv) h s); by [exact: Hpass | rewrite /bb84_bool_val | cvne |
  done]. Qed.

Fact bb84_final_store_public_register_state (h : @run_history V M) (s : @store (bb84_cvar M) V) : let fs := dev_final_args (@final_store) h
  s in
  let spe := dev_sfin h s in
  let sec := @errcorr_store (bb84_cvar M) V (cd_ir_bits dev) M (@BVXA M) (@BVXB M) (@BVpec M) (@BVXhat M) (@BVg M)
      (@BVtA M) (@BVtB M) (@BVP M) bb84_tr_app_ec (bb84_ir_pub_val (@cd_ir_pub R P q dev)) (bb84_ir_dec_val (@cd_ir_dec R P q dev))
      (bb84_verify_hash_val (@cd_vh R P q dev)) h spe in
  fs (@BVabort M) == bb84_bool_val false -> bb84_public_register_state fs = bb84_public_register_state sec.
Proof. have bb84_public_register_state_privamp_store : forall (h : @run_history V M) (s : @store (bb84_cvar M) V),
  bb84_public_register_state (@privamp_store (bb84_cvar M) V (bb84_l P) M (@BVXA M) (@BVXhat M) (@BVf M) (@BVS M) (@BVSh M) (@BVP M) bb84_tr_app_pa (bb84_privacy_hash_val (@cd_pa R P q dev)) h s) = bb84_public_register_state s.
  { move=> {}h {}s. rewrite /bb84_public_register_state /bb84_eur_public_of_store /privamp_store.
    set s1 := store_set s (@BVf M) (@hist_f V M h). set s2 := store_set s1 (@BVS M) (bb84_privacy_hash_val (@cd_pa R P q dev) (bb84_l P) (s1 (@BVf M)) (s1 (@BVXA M))). set s3 := store_set s2 (@BVSh M) (bb84_privacy_hash_val (@cd_pa R P q dev) (bb84_l P) (s2 (@BVf M)) (s2 (@BVXhat M))). rewrite store_set_same bb84_eur_public_of_tr_app_pa /s3 store_set_other; last by cvne. rewrite /s2 store_set_other; last by cvne. by rewrite /s1 store_set_other //; cvne. } move=> fs spe sec Hpass. have HAB_S : @BVabort M != @BVS M by cvne.
    have HAB_Sh : @BVabort M != @BVSh M by cvne. have Hpe := final_store_pass_pe_ok (h := h) (s := s) bb84_bool_val_neq HAB_S HAB_Sh Hpass; rewrite -/spe in Hpe. have Hverify : ~~ (sec (@BVtA M) != sec (@BVtB M)).
  { move: Hpass; rewrite /fs /final_store -/spe (negbTE Hpe) -/sec. case Hbad: (sec (@BVtA M) != sec (@BVtB M)); last by [].
    by rewrite abort_store_not_pass. } by rewrite /fs /final_store -/spe (negbTE Hpe) -/sec (negbTE Hverify); exact: bb84_public_register_state_privamp_store. Qed.

Definition bb84_S_index (x : 'I_(2 ^ bb84_n P)) : 'Idx[HL]_bb84_S := n2i (cast_ord bb84_dim_S x).
Definition bb84_Zl_index (z : 'I_(2 ^ bb84_l P)) : 'Idx[HL]_bb84_Zl := bb84_pa_output_idx z.
Fact bb84_dim_Ppub_pair : #|{: ('I_(2 ^ cd_ir_bits dev) * 'I_(cd_tag_count dev))%type}| = dim ('H[HL]_bb84_Ppub).
Proof. by rewrite card_prod !card_ord bb84_dim_Ppub. Qed.

Definition bb84_Ppub_index (p : ('I_(2 ^ cd_ir_bits dev) * 'I_(cd_tag_count dev))%type) : 'Idx[HL]_bb84_Ppub :=
  n2i (cast_ord bb84_dim_Ppub_pair (enum_rank p)).
Definition bb84_S_projector (x : 'I_(2 ^ bb84_n P)) : 'F[HL]_bb84_S := [> deltav (bb84_S_index x); deltav (bb84_S_index x) <].
Definition bb84_Fl_projector (f : 'I_(cd_paseed_count dev)) : 'F[HL]_bb84_Fl := [> deltav (bb84_Fl_index f); deltav (bb84_Fl_index f) <].
Definition bb84_Zl_projector (z : 'I_(2 ^ bb84_l P)) : 'F[HL]_bb84_Zl := [> deltav (bb84_Zl_index z); deltav (bb84_Zl_index z) <].
Definition bb84_Ppub_projector (p : ('I_(2 ^ cd_ir_bits dev) * 'I_(cd_tag_count dev))%type) : 'F[HL]_bb84_Ppub :=
  [> deltav (bb84_Ppub_index p); deltav (bb84_Ppub_index p) <].
Fact bb84_S_projector_den1lf (x : 'I_(2 ^ bb84_n P)) : bb84_S_projector x \is den1lf.
Proof. by apply/den1lfP; split; first exact: outp_psd; rewrite /bb84_S_projector outp_trlf dv_dot eqxx. Qed.

Fact bb84_Fl_projector_den1lf (f : 'I_(cd_paseed_count dev)) : bb84_Fl_projector f \is den1lf.
Proof. by apply/den1lfP; split; first exact: outp_psd; rewrite /bb84_Fl_projector outp_trlf dv_dot eqxx. Qed.

Fact bb84_Zl_projector_den1lf (z : 'I_(2 ^ bb84_l P)) : bb84_Zl_projector z \is den1lf.
Proof. by apply/den1lfP; split; first exact: outp_psd; rewrite /bb84_Zl_projector outp_trlf dv_dot eqxx. Qed.

Definition bb84_alice_key_register_state (s : @store (bb84_cvar M) V) : 'F[HL]_bb84_S :=
  bb84_S_projector (bb84_raw_key_index (s (@BVXA M))).
Fact bb84_alice_key_register_state_den1lf (s : @store (bb84_cvar M) V) : bb84_alice_key_register_state s \is den1lf.
Proof. exact: bb84_S_projector_den1lf. Qed.

Definition bb84_key_public_register_state (s : @store (bb84_cvar M) V) : 'F[HL]_(bb84_S :|: bb84_Epub) :=
  bb84_alice_key_register_state s \⊗ bb84_public_register_state s.
Definition bb84_leakage_register_state (s : @store (bb84_cvar M) V) : 'F[HL]_bb84_Ppub := bb84_Ppub_projector
    (bb84_ec_index (s (@BVpec M)), bb84_tag_index (s (@BVtA M))).
Fact bb84_leakage_register_state_privamp_store (h : @run_history V M) (s : @store (bb84_cvar M) V) : bb84_leakage_register_state
    (@privamp_store (bb84_cvar M) V (bb84_l P) M (@BVXA M) (@BVXhat M) (@BVf M) (@BVS M) (@BVSh M) (@BVP M) bb84_tr_app_pa
      (bb84_privacy_hash_val (@cd_pa R P q dev)) h s) = bb84_leakage_register_state s.
Proof. by rewrite /bb84_leakage_register_state /privamp_store; rewrite !store_set_other //; cvinr. Qed.

Definition bb84_pa_public_register_state (s : @store (bb84_cvar M) V) : 'F[HL]_(bb84_Zl :|: (bb84_Fl :|: (bb84_Epub :|: bb84_Ppub))) :=
  bb84_Zl_projector (bb84_final_key_index (s (@BVS M))) \⊗ (bb84_Fl_projector (bb84_paseed_index (s (@BVf M))) \⊗
      (bb84_public_register_state s \⊗ bb84_leakage_register_state s)).
Definition bb84_leakage_public_register_state (s : @store (bb84_cvar M) V) : 'F[HL]_(bb84_Ppub :|: (bb84_S :|: bb84_Epub)) :=
  bb84_leakage_register_state s \⊗ (bb84_alice_key_register_state s \⊗ bb84_public_register_state s).
Lemma bb84_leakage_register_state_den1lf (s : @store (bb84_cvar M) V) : bb84_leakage_register_state s \is den1lf.
Proof. have bb84_Ppub_projector_den1lf : forall (p : ('I_(2 ^ cd_ir_bits dev) * 'I_(cd_tag_count dev))%type), bb84_Ppub_projector p \is
  den1lf.
  { move=> p; apply/den1lfP; split; first exact: outp_psd. by rewrite /bb84_Ppub_projector outp_trlf dv_dot eqxx. }
exact: bb84_Ppub_projector_den1lf. Qed.

Fact bb84_pa_public_register_state_den1lf (s : @store (bb84_cvar M) V) : bb84_pa_public_register_state s \is den1lf.
Proof. have HZFEpubP : [disjoint bb84_Zl & bb84_Fl :|: (bb84_Epub :|: bb84_Ppub)].
  { have HZF : [disjoint bb84_Zl & bb84_Fl] by rewrite disjoint_sym bb84_disFZl. have HZEpub : [disjoint bb84_Zl & bb84_Epub] by exact: bb84_bridge_reg_disjoint. have HZP : [disjoint bb84_Zl & bb84_Ppub] by exact: bb84_bridge_reg_disjoint.
    by rewrite disjointXU HZF disjointXU HZEpub HZP. } have HFEpubP : [disjoint bb84_Fl & bb84_Epub :|: bb84_Ppub].
  { have HFEpub : [disjoint bb84_Fl & bb84_Epub] by exact: bb84_bridge_reg_disjoint. have HFP : [disjoint bb84_Fl & bb84_Ppub] by exact: bb84_bridge_reg_disjoint. by rewrite disjointXU HFEpub HFP. } have HEpubP : [disjoint bb84_Epub & bb84_Ppub] by exact: bb84_bridge_reg_disjoint. apply/den1lfP; split.
  - rewrite /bb84_pa_public_register_state psdlfE. apply: tenf_ge0; first exact: HZFEpubP.
    + by move: (den1lf_psd (bb84_Zl_projector_den1lf (bb84_final_key_index (s (@BVS M))))); rewrite psdlfE.
    + apply: tenf_ge0; first exact: HFEpubP.
      * by move: (den1lf_psd (bb84_Fl_projector_den1lf (bb84_paseed_index (s (@BVf M))))); rewrite psdlfE.
      * apply: tenf_ge0; first exact: HEpubP.
        -- by move: (den1lf_psd (bb84_public_register_state_den1lf s)); rewrite psdlfE.
        -- by move: (den1lf_psd (bb84_leakage_register_state_den1lf s)); rewrite psdlfE.
  - rewrite /bb84_pa_public_register_state. rewrite (lftrace_tenf _ _ HZFEpubP) (lftrace_tenf _ _ HFEpubP) (lftrace_tenf _ _ HEpubP).
    rewrite (den1lf_trlf (bb84_Zl_projector_den1lf (bb84_final_key_index (s (@BVS M))))). rewrite (den1lf_trlf (bb84_Fl_projector_den1lf (bb84_paseed_index (s (@BVf M))))). by rewrite (den1lf_trlf (bb84_public_register_state_den1lf s)); rewrite (den1lf_trlf (bb84_leakage_register_state_den1lf s)) !mul1r. Qed.

Lemma bb84_key_public_register_state_den1lf (s : @store (bb84_cvar M) V) : bb84_key_public_register_state s \is den1lf.
Proof. apply/den1lfP; split.
  - rewrite /bb84_key_public_register_state psdlfE. apply: tenf_ge0; first exact: bb84_disS_Epub.
    + by move: (den1lf_psd (bb84_alice_key_register_state_den1lf s)); rewrite psdlfE.
    + by move: (den1lf_psd (bb84_public_register_state_den1lf s)); rewrite psdlfE.
  - rewrite /bb84_key_public_register_state. by rewrite (lftrace_tenf _ _ bb84_disS_Epub) (den1lf_trlf (bb84_alice_key_register_state_den1lf s)) (den1lf_trlf (bb84_public_register_state_den1lf s)) mul1r. Qed.

Fact bb84_key_public_register_state_cq (s : @store (bb84_cvar M) V) : @is_cq_state R L HL bb84_S bb84_Epub
    (bb84_key_public_register_state s).
Proof. rewrite /is_cq_state; apply/forallP => x; apply/forallP => x'; apply/implyP => Hx'x. apply/eqP. have Hleft : ([> deltav x ;
  deltav x <] \O (\1 : 'F[HL]_bb84_Epub) : 'F[HL]_(bb84_S :|: bb84_Epub)) = [> deltav x ; deltav x <] \⊗ (\1 : 'F[HL]_bb84_Epub).
  { by apply: to_Fnd_inj; rewrite (sdotFT _ _ bb84_disS_Epub) to_Fnd_tenE. } have Hright : ([> deltav x' ; deltav x' <] \O (\1 : 'F[HL]_bb84_Epub) : 'F[HL]_(bb84_S :|: bb84_Epub)) = [> deltav x' ; deltav x' <] \⊗ (\1 : 'F[HL]_bb84_Epub).
  { by apply: to_Fnd_inj; rewrite (sdotFT _ _ bb84_disS_Epub) to_Fnd_tenE. } rewrite Hleft Hright /bb84_key_public_register_state.
    rewrite -[([> deltav x ; deltav x <] \⊗ _) \o (bb84_alice_key_register_state s \⊗ bb84_public_register_state s)] tenf_comp; last exact: bb84_disS_Epub. rewrite comp_lfun1l. rewrite -[((([> deltav x ; deltav x <] \o bb84_alice_key_register_state s) \⊗ _) \o ([> deltav x' ; deltav x' <] \⊗ _))]tenf_comp; last exact: bb84_disS_Epub. rewrite comp_lfun1r /bb84_alice_key_register_state /bb84_S_projector. set idxS := bb84_S_index (bb84_raw_key_index _). have Hxx' : [> deltav x ; deltav x <] \o [> deltav idxS ; deltav idxS <] \o [> deltav x' ; deltav x' <] = 0.
  { case: (eqVneq x idxS) => [Hxidx | Hxidx].
    - rewrite Hxidx. move: Hx'x; rewrite Hxidx => Hx'idx. have Hidxx' : idxS != x' by rewrite eq_sym.
      by rewrite outp_comp dv_dot eqxx scale1r outp_comp dv_dot; rewrite ?(negbTE Hx'idx) ?(negbTE Hidxx') /= scale0r.
    - have Hidxx : idxS != x by rewrite eq_sym. rewrite outp_comp dv_dot. by rewrite ?(negbTE Hxidx) ?(negbTE Hidxx) /= scale0r comp_lfun0l. }
by rewrite Hxx' ten0f. Qed.

Lemma bb84_leakage_public_register_state_den1lf (s : @store (bb84_cvar M) V) : bb84_leakage_public_register_state s \is den1lf.
Proof. have HPS_Epub := bb84_disP_SEpub. apply/den1lfP; split.
  - rewrite /bb84_leakage_public_register_state psdlfE. apply: tenf_ge0; first exact: HPS_Epub.
    + by move: (den1lf_psd (bb84_leakage_register_state_den1lf s)); rewrite psdlfE.
    + by move: (den1lf_psd (bb84_key_public_register_state_den1lf s)); rewrite psdlfE.
  - rewrite /bb84_leakage_public_register_state. by rewrite (lftrace_tenf _ _ HPS_Epub) (den1lf_trlf (bb84_leakage_register_state_den1lf s)) (den1lf_trlf (bb84_key_public_register_state_den1lf s)) mul1r. Qed.

Fact bb84_leakage_public_register_state_reassoc (s : @store (bb84_cvar M) V) :
  let eq_pub_assoc := bb84_public_assoc bb84_S bb84_Epub bb84_Ppub in castlf (eq_pub_assoc, eq_pub_assoc)
    (bb84_leakage_public_register_state s) = ((bb84_alice_key_register_state s) \O
    (bb84_public_register_state s \O bb84_leakage_register_state s) : 'F[HL]_(bb84_S :|: (bb84_Epub :|: bb84_Ppub))).
Proof. move=> /=; have HPS_Epub := bb84_disP_SEpub. set p := (bb84_ec_index (s (@BVpec M)), bb84_tag_index (s (@BVtA M))).
  rewrite /bb84_leakage_public_register_state /bb84_leakage_register_state /bb84_Ppub_projector -/p.
  rewrite -[([> deltav (bb84_Ppub_index p); deltav (bb84_Ppub_index p) <] \⊗ (bb84_alice_key_register_state s \⊗ bb84_public_register_state s))] (sdotF_to_tenF HPS_Epub). rewrite -[bb84_alice_key_register_state s \⊗ bb84_public_register_state s] (sdotF_to_tenF bb84_disS_Epub); apply: to_Fnd_inj. rewrite !Fnd_cast !to_Fnd_sdotE dotFA. rewrite (@dotFC R L HL (to_Fnd [> deltav (bb84_Ppub_index p); deltav (bb84_Ppub_index p) <]) (to_Fnd (bb84_alice_key_register_state s))).
  - rewrite -!dotFA; congr (_ \· _)%FND. rewrite (@dotFC R L HL (to_Fnd [> deltav (bb84_Ppub_index p); deltav (bb84_Ppub_index p) <]) (to_Fnd (bb84_public_register_state s))).
    + by [].
    + by exact: bb84_bridge_reg_disjoint.
  - by exact: bb84_bridge_reg_disjoint. Unshelve. all: by exact: bb84_bridge_reg_disjoint. Qed.

Local Lemma castlf_esymK (S T : {set L}) (e : S = T) (X : 'F[HL]_T) : castlf (e, e) (castlf (esym e, esym e) X) = X.
Proof. by rewrite castlf_comp (eq_irrelevance (etrans (esym e) e) erefl) castlf_id. Qed.

Fact bb84_leakage_public_replaceso_target_marginal (s : @store (bb84_cvar M) V) (rho : 'F[HL]_(setTfor L)) :
  ptrace_cast_gen (bb84_setT_diff_complement (bb84_S :|: bb84_E)) (@replaceso R L HL (bb84_Ppub :|: (bb84_S :|: bb84_Epub))
      (bb84_leakage_public_register_state s) rho) = ptrace_cast_gen (bb84_setT_diff_complement (bb84_S :|: bb84_E))
    (@replaceso R L HL (bb84_S :|: bb84_Epub) (bb84_key_public_register_state s) rho).
Proof. set A := bb84_Ppub; set B := bb84_S :|: bb84_Epub; set C0 := ([set: L] : {set L}) :\: (A :|: B).
  have HPS_Epub : [disjoint A & B] := bb84_disP_SEpub. have HA_C0 : [disjoint A & C0] := disjoint_setDUl A B.
  have HB_C0 : [disjoint B & C0] := disjoint_setDUr A B. have HAB_C0 : [disjoint A :|: B & C0]. { by rewrite disjointUX HA_C0 HB_C0. }
have eqABC : A :|: B :|: C0 = ([set: L] : {set L}). { by rewrite /C0 setUD_sub. } apply/eqP/trlf_intror => g.
  rewrite !(ptrace_cast_gen_setC_liftf_lf_tr (bb84_setT_diff_complement (bb84_S :|: bb84_E))). have HSE_A : bb84_S :|: bb84_E :<=: ~: A.
  { by rewrite /A -disjointX_subset disjoint_sym bb84_disPSE. } set gA := lift_lf HSE_A g; set gA0 := castlf (esym (@mathcomp.boot.finset.setTD L A), esym (@mathcomp.boot.finset.setTD L A)) gA.
  have Hg : liftf_lf g = liftf_lf gA0. { by rewrite /gA0 liftf_lf_cast /gA liftf_lf2. } rewrite Hg -(@ptraceso_liftf_lf_tr R L HL A (@replaceso R L HL (A :|: B) (bb84_leakage_public_register_state s) rho) gA0). rewrite -(@ptraceso_liftf_lf_tr R L HL A (@replaceso R L HL B (bb84_key_public_register_state s) rho) gA0). rewrite !replacesoE /bb84_leakage_public_register_state.
  rewrite -[bb84_leakage_register_state s \⊗ _](sdotF_to_tenF HPS_Epub) -/bb84_key_public_register_state.
  set eqC := etrans (esym (setDU_l HAB_C0)) (f_equal (fun S => S :\: (A :|: B)) eqABC). set xC := castlf (esym eqC, esym eqC) (\Tr_(A :|: B) rho). have HxC : \Tr_(A :|: B) rho = castlf (eqC, eqC) xC by rewrite /xC castlf_esymK. rewrite HxC.
  rewrite (@ptraceso_appendso_union_l_den1 R L HL A B C0 HPS_Epub HA_C0 HB_C0 HAB_C0 eqABC (bb84_leakage_register_state s) (bb84_key_public_register_state s) xC (bb84_leakage_register_state_den1lf s)). have HBA : [disjoint B & A] by rewrite disjoint_sym HPS_Epub. have eqBAC : B :|: A :|: C0 = ([set: L] : {set L}).
  { rewrite -eqABC; apply/setP=> x. rewrite /A /B /C0 /bb84_Ppub /bb84_S /bb84_Epub /bb84_reg !inE.
    case HPx : (x == bb84_bridge_label bb84_reg_Ppub); case HSx : (x == bb84_bridge_label bb84_reg_S); case HEx : (x == bb84_bridge_label bb84_reg_E); by rewrite ?HPx ?HSx ?HEx. } set eqAC := etrans (esym (setDU3_A HBA HB_C0)) (f_equal (fun S => S :\: B) eqBAC); set yAC := castlf (esym eqAC, esym eqAC) (\Tr_(B) rho). have HyAC : \Tr_(B) rho = castlf (eqAC, eqAC) yAC by rewrite /yAC castlf_esymK. rewrite HyAC (@ptraceso_appendso_complement R L HL B A C0 HBA HB_C0 HA_C0 eqBAC (bb84_key_public_register_state s) yAC). have Htail : ptrace_castl HA_C0 yAC = xC.
  { rewrite /ptrace_castl /ptrace_cast_gen /yAC /xC. rewrite (ptracelf_castlf_eq (esym eqAC) (f_equal (fun S => S :\: A) (esym eqAC))).
    have Hcomp_trace := congr1 (fun F : 'SO[HL]_(setTfor L, ((setTfor L :\: B) :\: A)) => F rho) (@ptraceso_comp R L HL A B (setTfor L)).
    move: Hcomp_trace; rewrite comp_soE castsoE /= castlf_id => Hcomp_trace; rewrite Hcomp_trace.
    have Htrace_comm : \Tr_(B :|: A) rho = castlf (esym (f_equal (fun S => ([set: L] : {set L}) :\: S) (finset.setUC B A)), esym (f_equal (fun S => ([set: L] : {set L}) :\: S) (finset.setUC B A))) (\Tr_(A :|: B) rho).
    { by case: _ / (finset.setUC B A); rewrite castlf_id. } rewrite Htrace_comm !castlf_comp. by congr (castlf (_, _) _); exact: eq_irrelevance. } by rewrite Htail; congr (\Tr (_ \o gA0)); congr (castlf (_, _) _); exact: eq_irrelevance. Qed.

Fact bb84_leakage_public_register_state_pa_cq (s : @store (bb84_cvar M) V) :
  let eq_pub_assoc := bb84_public_assoc bb84_S bb84_Epub bb84_Ppub in @is_cq_state R L HL bb84_S (bb84_Epub :|: bb84_Ppub)
    (castlf (eq_pub_assoc, eq_pub_assoc) (bb84_leakage_public_register_state s)).
Proof. have HPS_Epub := bb84_disP_SEpub. set p := (bb84_ec_index (s (@BVpec M)), bb84_tag_index (s (@BVtA M))).
  rewrite /bb84_leakage_public_register_state /bb84_leakage_register_state /bb84_Ppub_projector -/p.
  rewrite -[([> deltav (bb84_Ppub_index p); deltav (bb84_Ppub_index p) <] \⊗ (bb84_alice_key_register_state s \⊗ bb84_public_register_state s))] (sdotF_to_tenF HPS_Epub). rewrite (@bb84_public_deterministic_state_right R L HL bb84_S bb84_Epub bb84_Ppub HPS_Epub (bb84_Ppub_index p) (bb84_key_public_register_state s)). apply: bb84_public_right_append_cq.
  - exact: bb84_disSP.
  - by exact: bb84_bridge_reg_disjoint.
  - exact: bb84_key_public_register_state_cq. Qed.

Fact bb84_leakage_public_replaceso_pa_cq (s : @store (bb84_cvar M) V) (rho : 'F[HL]_(setTfor L)) (x x' : 'Idx[HL]_bb84_S) :
  x' != x -> ((liftf_lf (([> deltav x ; deltav x <] \O (\1 : 'F[HL]_(bb84_Epub :|: bb84_Ppub))) :
        'F[HL]_(bb84_S :|: (bb84_Epub :|: bb84_Ppub))) \o @replaceso R L HL (bb84_Ppub :|: (bb84_S :|: bb84_Epub))
      (bb84_leakage_public_register_state s) rho) \o liftf_lf (([> deltav x' ; deltav x' <] \O (\1 : 'F[HL]_(bb84_Epub :|: bb84_Ppub))) :
        'F[HL]_(bb84_S :|: (bb84_Epub :|: bb84_Ppub)))) = 0.
Proof. move=> Hx'x; set eq_pub_assoc := bb84_public_assoc bb84_S bb84_Epub bb84_Ppub. set Kx := (([> deltav x ;
  deltav x <] \O (\1 : 'F[HL]_(bb84_Epub :|: bb84_Ppub))) : 'F[HL]_(bb84_S :|: (bb84_Epub :|: bb84_Ppub))). set Kx' := (([> deltav x' ; deltav x' <] \O (\1 : 'F[HL]_(bb84_Epub :|: bb84_Ppub))) : 'F[HL]_(bb84_S :|: (bb84_Epub :|: bb84_Ppub))).
  set A := castlf (esym eq_pub_assoc, esym eq_pub_assoc) Kx; set B := castlf (esym eq_pub_assoc, esym eq_pub_assoc) Kx'.
  have HliftA : liftf_lf Kx = liftf_lf A by rewrite /A liftf_lf_cast. have HliftB : liftf_lf Kx' = liftf_lf B by rewrite /B liftf_lf_cast.
  rewrite HliftA HliftB replacesoE appendso_comp_keep. have Hblock : A \o bb84_leakage_public_register_state s \o B = 0.
  { move: (bb84_leakage_public_register_state_pa_cq s); rewrite /is_cq_state -/eq_pub_assoc => /forallP Hcq.
    move: (Hcq x) => /forallP /(_ x') /implyP Hcqxx'; move/eqP: (Hcqxx' Hx'x) => Hcq0. apply/eqP; rewrite -(@castlf_eq0 R L HL _ _ _ _ (eq_pub_assoc, eq_pub_assoc) (A \o bb84_leakage_public_register_state s \o B)).
    rewrite (castlf_complf eq_pub_assoc eq_pub_assoc eq_pub_assoc). rewrite [castlf _ (A \o _)](castlf_complf eq_pub_assoc eq_pub_assoc eq_pub_assoc) /A /B !castlf_comp !castlf_id. by rewrite Hcq0 eqxx. } by rewrite Hblock appendsoE ten0f linear0. Qed.

Fact bb84_leakage_public_replaceso_classical (s : @store (bb84_cvar M) V) (rho : 'F[HL]_(setTfor L)) (p p' : 'Idx[HL]_bb84_Ppub) :
  p' != p -> ((liftf_lf (([> deltav p ; deltav p <] \O (\1 : 'F[HL]_(bb84_S :|: bb84_Epub))) :
        'F[HL]_(bb84_Ppub :|: (bb84_S :|: bb84_Epub))) \o @replaceso R L HL (bb84_Ppub :|: (bb84_S :|: bb84_Epub))
      (bb84_leakage_public_register_state s) rho) \o liftf_lf (([> deltav p' ; deltav p' <] \O (\1 : 'F[HL]_(bb84_S :|: bb84_Epub))) :
        'F[HL]_(bb84_Ppub :|: (bb84_S :|: bb84_Epub)))) = 0.
Proof. have bb84_leakage_public_register_state_classical : forall (s : @store (bb84_cvar M) V) (p p' : 'Idx[HL]_bb84_Ppub), p' != p -> (([>
  deltav p ; deltav p <] \O (\1 : 'F[HL]_(bb84_S :|: bb84_Epub))) \o bb84_leakage_public_register_state s \o ([> deltav p' ; deltav p' <] \O (\1 : 'F[HL]_(bb84_S :|: bb84_Epub)))) = 0.
  { move=> {}s {}p {}p' Hp'p; have HPS_Epub := bb84_disP_SEpub. have Hleft : ([> deltav p ; deltav p <] \O (\1 : 'F[HL]_(bb84_S :|: bb84_Epub)) : 'F[HL]_(bb84_Ppub :|: (bb84_S :|: bb84_Epub))) = [> deltav p ; deltav p <] \⊗ (\1 : 'F[HL]_(bb84_S :|: bb84_Epub)).
    { by apply: to_Fnd_inj; rewrite (sdotFT _ _ HPS_Epub) to_Fnd_tenE. } have Hright : ([> deltav p' ; deltav p' <] \O (\1 : 'F[HL]_(bb84_S :|: bb84_Epub)) : 'F[HL]_(bb84_Ppub :|: (bb84_S :|: bb84_Epub))) = [> deltav p' ; deltav p' <] \⊗ (\1 : 'F[HL]_(bb84_S :|: bb84_Epub)).
    { by apply: to_Fnd_inj; rewrite (sdotFT _ _ HPS_Epub) to_Fnd_tenE. } rewrite Hleft Hright /bb84_leakage_public_register_state -tenf_comp // comp_lfun1l. rewrite -tenf_comp // comp_lfun1r /bb84_leakage_register_state /bb84_Ppub_projector. set idx := bb84_Ppub_index _.
      have Hpp' : [> deltav p ; deltav p <] \o [> deltav idx ; deltav idx <] \o [> deltav p' ; deltav p' <] = 0.
    { case: (eqVneq p idx) => [Hpidx | Hpidx].
      - rewrite Hpidx. move: Hp'p; rewrite Hpidx => Hp'idx. have Hidxp' : idx != p' by rewrite eq_sym.
        rewrite outp_comp dv_dot eqxx scale1r outp_comp dv_dot. by rewrite ?(negbTE Hp'idx) ?(negbTE Hidxp') /= scale0r.
      - have Hidxp : idx != p by rewrite eq_sym. rewrite outp_comp dv_dot. by rewrite ?(negbTE Hpidx) ?(negbTE Hidxp) /= scale0r comp_lfun0l. } by rewrite Hpp' ten0f. } move=> Hp'p; rewrite replacesoE appendso_comp_keep.
        by rewrite (bb84_leakage_public_register_state_classical s _ _ Hp'p); rewrite appendsoE ten0f linear0. Qed.

Definition bb84_pass_key_public_readout_state (EA : @adversary R L HL V bb84_Eve) (xi : @cq_state R L HL (bb84_cvar M) V) :=
  @bb84_pass_history_public_readout_state R P q dev LE HE bb84_register_index bb84_register_space (bb84_S :|: bb84_Epub)
    bb84_key_public_register_state EA xi.
Definition bb84_pe_pass_key_public_readout_state (EA : @adversary R L HL V bb84_Eve) (xi : @cq_state R L HL (bb84_cvar M) V) :=
  @bb84_pe_pass_history_public_readout_state R P q dev LE HE bb84_register_index bb84_register_space (bb84_S :|: bb84_Epub)
    bb84_key_public_register_state EA xi.
Definition bb84_pass_key_public_source_state (EA : @adversary R L HL V bb84_Eve) (xi : @cq_state R L HL (bb84_cvar M) V) :=
  @bb84_pass_history_public_source_state R P q dev LE HE bb84_register_index bb84_register_space (bb84_S :|: bb84_Epub)
    bb84_key_public_register_state EA xi.
Fact bb84_pass_key_public_readout_source_ptraceso_all_sources (EA : @adversary R L HL V bb84_Eve) (xi : @cq_state R L HL (bb84_cvar M) V) :
  ptraceso [set x : L | if x is inr (inl _) then true else false] (bb84_pass_key_public_readout_state EA xi) =
  ptraceso [set x : L | if x is inr (inl _) then true else false] (bb84_pass_key_public_source_state EA xi).
Proof. rewrite /bb84_pass_key_public_readout_state /bb84_pass_key_public_source_state /bb84_pass_history_public_readout_state
  /bb84_pass_history_public_source_state. rewrite [in LHS]linear_sum /=. rewrite [in RHS]linear_sum /=. apply: eq_bigr => s _.
  rewrite [in LHS]linear_sum /=. rewrite [in RHS]linear_sum /=. apply: eq_bigr => h _. rewrite [in LHS]linearZ /=. rewrite [in RHS]linearZ /=.
  set Qpub := bb84_S :|: bb84_Epub; set Qsrc := [set x : L | if x is inr (inl _) then true else false].
  set C0 := ([set: L] : {set L}) :\: (Qpub :|: Qsrc). have Hpub_src : [disjoint Qpub & Qsrc].
  { apply/disjointP=> x Hx_pub. apply/negP=> Hx_src. move: Hx_pub; rewrite /Qpub /Qsrc /bb84_S /bb84_Epub /bb84_reg /bb84_bridge_reg !inE.
    by case/orP=> /eqP Hx; move: Hx_src; rewrite /Qsrc inE Hx. } have Hpub_C : [disjoint Qpub & C0] := disjoint_setDUl Qpub Qsrc.
    have Hsrc_C : [disjoint Qsrc & C0] := disjoint_setDUr Qpub Qsrc. have Heq : Qpub :|: Qsrc :|: C0 = ([set: L] : {set L}) by rewrite /C0 setUD_sub. set pub := bb84_key_public_register_state _. have Hbranch : ptraceso Qsrc (@replaceso R L HL Qpub pub (bb84_history_readout_state EA h (xi s))) = ptraceso Qsrc (@replaceso R L HL Qpub pub (bb84_history_source_state EA h (xi s))).
  { apply: (@ptraceso_replaceso_disjoint_eq R L HL Qpub Qsrc C0 Hpub_src Hpub_C Hsrc_C Heq). case Hdecoded: (bb84_history_decoded h).
    - rewrite (bb84_history_readout_source_ptraceso_all_sources (h := h) EA (xi s)); first by []. by rewrite Hdecoded.
    - by rewrite /bb84_history_readout_state /bb84_history_source_state /bb84_trace_source_state -bb84_history_decoded_traceE Hdecoded !linear0. } by rewrite Hbranch. Qed.

Definition bb84_pe_pass_key_public_source_state (EA : @adversary R L HL V bb84_Eve) (xi : @cq_state R L HL (bb84_cvar M) V) :=
  @bb84_pe_pass_history_public_source_state R P q dev LE HE bb84_register_index bb84_register_space (bb84_S :|: bb84_Epub)
    bb84_key_public_register_state EA xi.
Definition bb84_key_public_source_pass_prob (EA : @adversary R L HL V bb84_Eve) (xi : @cq_state R L HL (bb84_cvar M) V) : R :=
  @complex.Re R (\Tr (bb84_pass_key_public_source_state EA xi)).
Fact bb84_key_public_source_pass_prob_runE (EA : @adversary R L HL V bb84_Eve) (xi : @cq_state R L HL (bb84_cvar M) V) :
  (forall i, @BVa M i != @BVy M i) -> (forall i, @BVP M != @BVa M i) -> (forall i, @BVP M != @BVy M i) ->
  (forall i, @BVP M != @BVb M i) -> (forall i, @BVP M != @BVy' M i) -> (forall i, @BVP M != @BVd M i) ->
  @BVP M != @BVX M -> @BVP M != @BVZ M -> @BVP M != @BVabort M -> bb84_key_public_source_pass_prob EA xi =
  @bb84_run_pass_prob R P q dev LE HE bb84_register_index bb84_register_space EA xi.
Proof. move=> Hay HPa HPy HPb HPy' HPd HPX HPZ HPabort; rewrite /bb84_key_public_source_pass_prob.
  transitivity (@complex.Re R (\Tr (@bb84_run_pass_history_state R P q dev LE HE bb84_register_index bb84_register_space EA xi))).
  { congr (@complex.Re R _). rewrite (@bb84_run_pass_history_state_fullE R P q dev LE HE bb84_register_index bb84_register_space EA xi).
    rewrite /bb84_pass_key_public_source_state /bb84_pass_history_public_source_state [in LHS]linear_sum /=. rewrite [in RHS]linear_sum /=; apply: eq_bigr => s _. rewrite [in LHS]linear_sum /=. rewrite [in RHS]linear_sum /=. apply: eq_bigr => h _.
    rewrite [in LHS]linearZ /=. rewrite [in RHS]linearZ /=. by rewrite replaceso_trlf_den1 ?bb84_key_public_register_state_den1lf. }
exact: (@bb84_run_pass_history_state_traceE R P q dev LE HE bb84_register_index bb84_register_space EA xi Hay HPa HPy HPb HPy' HPd HPX HPZ HPabort). Qed.

Definition bb84_pass_leakage_public_readout_state (EA : @adversary R L HL V bb84_Eve) (xi : @cq_state R L HL (bb84_cvar M) V) :=
  @bb84_pass_history_public_readout_state R P q dev LE HE bb84_register_index bb84_register_space (bb84_Ppub :|: (bb84_S :|: bb84_Epub))
    bb84_leakage_public_register_state EA xi.
Fact bb84_pass_history_leakage_public_readout_source_readoutE (EA : @adversary R L HL V bb84_Eve) (xi : @cq_state R L HL (bb84_cvar M) V) :
  bb84_pass_leakage_public_readout_state EA xi = \sum_s \sum_(t : @round_trace V M) \sum_K \sum_g \sum_f
    let h : @run_history V M := (t, ((K, g), f)) in let s4 := bb84_history_errcorr_store h s in let pass := bb84_history_pass_weight h s in
    ((pass)%:C *: @replaceso R L HL (bb84_Ppub :|: (bb84_S :|: bb84_Epub)) (bb84_leakage_register_state s4 \⊗
          (bb84_alice_key_register_state s4 \⊗ bb84_public_register_state s4)) (bb84_history_readout_state EA h (xi s))).
Proof. rewrite /bb84_pass_leakage_public_readout_state /bb84_pass_history_public_readout_state; apply: eq_bigr => s _.
  rewrite -run_history_sum_split_history; apply: eq_bigr => t _. apply: eq_bigr => K _; apply: eq_bigr => g _; apply: eq_bigr => fseed _.
  set h : @run_history V M := (t, ((K, g), fseed)). set fs := dev_final_args (@final_store) h s.
  set s0 := @start_store (bb84_cvar M) V M (@BVX M) (@BVZ M) (@BVabort M) (@BVP M) bb84_empty_transcript_val bb84_bool_val bb84_set_val s.
  set s1 := @rounds_store (bb84_cvar M) V M (@BVa M) (@BVy M) (@BVb M) (@BVy' M) (@BVd M) (@BVX M) (@BVZ M) (bb84_basis_value dev BasisX) (bb84_basis_value dev BasisZ) (bb84_outcome_val None) bb84_bool_val bb84_set_val h s0. set s2 := @announce_store (bb84_cvar M) V M (@BVa M) (@BVb M) (@BVd M) (@BVP M) bb84_tr_app_rounds s1. set s3 := @paramest_store (bb84_cvar M) V M (@BVy M) (@BVy' M) (@BVZ M) (@BVK M) (@BVXA M) (@BVXB M) (@BVZA M) (@BVZB M) (@BVlam M) (@BVP M) bb84_set_of bb84_error_val bb84_tr_app_pe bb84_bits_on_val bb84_partial_bits_on_val bb84_err_count_val h s2. set s4 := @errcorr_store (bb84_cvar M) V (cd_ir_bits dev) M (@BVXA M) (@BVXB M) (@BVpec M) (@BVXhat M) (@BVg M) (@BVtA M) (@BVtB M) (@BVP M) bb84_tr_app_ec (bb84_ir_pub_val (@cd_ir_pub R P q dev)) (bb84_ir_dec_val (@cd_ir_dec R P q dev)) (bb84_verify_hash_val (@cd_vh R P q dev)) h s3. set old_post := history_post_weight (R:=R) (Cv:=bb84_cvar M) (V:=V) (M:=M) (bb84_n P) (bb84_k P) (cd_ir_bits dev) (bb84_Qtol P) (@BVa M) (@BVy M) (@BVb M) (@BVy' M) (@BVd M) (@BVX M) (@BVZ M) (@BVK M) (@BVXA M) (@BVXB M) (@BVZA M) (@BVZB M) (@BVlam M) (@BVpec M) (@BVXhat M) (@BVg M) (@BVtA M) (@BVtB M) (@BVabort M) (@BVP M) (bb84_basis_value dev BasisX) (bb84_basis_value dev BasisZ) (bb84_outcome_val None) bb84_bot_val bb84_empty_transcript_val bb84_bool_val bb84_set_val bb84_set_of bb84_error_val bb84_tr_app_rounds bb84_tr_app_pe bb84_tr_app_ec bb84_bits_on_val bb84_partial_bits_on_val bb84_err_count_val bb84_error_of bb84_unif_nsubset_mass (bb84_ir_pub_val (@cd_ir_pub R P q dev)) (bb84_ir_dec_val (@cd_ir_dec R P q dev)) bb84_unif_vseed_mass (bb84_verify_hash_val (@cd_vh R P q dev)) bb84_unif_pseed_mass h s. set post := @key_sample_mass R (bb84_cvar M) V (bb84_n P) M (@BVX M) bb84_bot_val bb84_set_of bb84_unif_nsubset_mass s2 (@hist_K V M h) * (bb84_unif_vseed_mass (@errcorr_seed_store (bb84_cvar M) V (cd_ir_bits dev) (@BVXA M) (@BVXB M) (@BVpec M) (@BVXhat M) (bb84_ir_pub_val (@cd_ir_pub R P q dev)) (bb84_ir_dec_val (@cd_ir_dec R P q dev)) s3) (@hist_g V M h) * bb84_unif_pseed_mass s4 (@hist_f V M h)).
  rewrite /bb84_history_pass_weight /bb84_history_errcorr_store /history_pass_weight /history_errcorr_store /history_privamp_weight /history_paramest_store /history_announce_store. rewrite -/fs -/s0 -/s1 -/s2 -/s3 -/s4 -/post. have HAB_S : @BVabort M != @BVS M.
  { rewrite /BVabort /BVS /=; have Hord : (inord 17 : 'I_18) != inord 15 by rewrite -val_eqE /= !inordK. by rewrite Hord. }
have HAB_Sh : @BVabort M != @BVSh M.
  { rewrite /BVabort /BVSh /=; have Hord : (inord 17 : 'I_18) != inord 16 by rewrite -val_eqE /= !inordK. by rewrite Hord. }
have Hold_post_pass : fs (@BVabort M) == bb84_bool_val false -> old_post = post.
  { move=> Hpass; rewrite /old_post /post. rewrite (dev_weight_args (@history_post_weight_final_pass) h s bb84_bool_val_neq HAB_S HAB_Sh Hpass). by rewrite -/s0 -/s1 -/s2 -/s3 -/s4. }
set coef := (fs (@BVabort M) == bb84_bool_val false)%:R * post; case Hcoef: (coef == 0).
  - move/eqP: Hcoef => Hcoef0. have Hold_coef0 : (fs (@BVabort M) == bb84_bool_val false)%:R * old_post = 0.
    { case Hpass: (fs (@BVabort M) == bb84_bool_val false).
      - have Hpost0 : post = 0 by move: Hcoef0; rewrite /coef Hpass mul1r. by rewrite (Hold_post_pass Hpass) Hpost0 mulr0.
      - by rewrite mul0r. } by rewrite -/fs -/old_post Hold_coef0 -/coef Hcoef0 !scale0r.
  - have Hcoef_neq : (fs (@BVabort M) == bb84_bool_val false)%:R * post != 0 by rewrite -/coef Hcoef.
    have Hpass : fs (@BVabort M) == bb84_bool_val false.
    { move: Hcoef_neq; rewrite /coef. case: (fs (@BVabort M) == bb84_bool_val false) => //. by rewrite mul0r eqxx. }
have Hold_post := Hold_post_pass Hpass. have Hkey_s4 : bb84_alice_key_register_state fs = bb84_alice_key_register_state s4.
    { rewrite /bb84_alice_key_register_state; congr bb84_S_projector; congr bb84_raw_key_index.
      have HfsXA : fs (@BVXA M) = s3 (@BVXA M) by rewrite /fs /s3; apply: final_store_XA; cvne.
      have Hs4XA : s4 (@BVXA M) = s3 (@BVXA M) by rewrite /s4; apply: errcorr_store_XA; cvne. exact: (etrans HfsXA (esym Hs4XA)). }
have Hpublic_s4 : bb84_public_register_state fs = bb84_public_register_state s4.
    { rewrite (@bb84_final_store_public_register_state h s Hpass). by rewrite -/s0 -/s1 -/s2 -/s3 -/s4. }
have Hleak_s4 : bb84_leakage_register_state fs = bb84_leakage_register_state s4.
    { have Hpe := final_store_pass_pe_ok (h := h) (s := s) bb84_bool_val_neq HAB_S HAB_Sh Hpass; rewrite -/s3 in Hpe.
      have Hverify : ~~ (s4 (@BVtA M) != s4 (@BVtB M)).
      { move: Hpass; rewrite /fs /final_store -/s0 -/s1 -/s2 -/s3 (negbTE Hpe) -/s4. case Hbad: (s4 (@BVtA M) != s4 (@BVtB M)); last by [].
        by rewrite abort_store_not_pass. } rewrite /fs /final_store -/s0 -/s1 -/s2 -/s3 (negbTE Hpe) -/s4 (negbTE Hverify).
        exact: bb84_leakage_register_state_privamp_store. } by rewrite /bb84_leakage_public_register_state Hkey_s4 Hpublic_s4 Hleak_s4 /stat.bb84_final_store /stat.bb84_history_post_weight -/fs -/old_post Hold_post -/post -/coef -/s0 -/s1 -/s2. Qed.

Definition rhoXE_readout_pass_prog (EA : @adversary R L HL V bb84_Eve) (xi : @cq_state R L HL (bb84_cvar M) V) :
    'F[HL]_(bb84_S :|: bb84_E) := let st := bb84_pe_pass_key_public_readout_state EA xi in
  ptrace_cast_gen (bb84_setT_diff_complement (bb84_S :|: bb84_E)) (((@complex.Re R (\Tr st))^-1)%:C *: st).
Lemma bb84_pe_pass_key_public_readout_traceRe (EA : @adversary R L HL V bb84_Eve) (xi : @cq_state R L HL (bb84_cvar M) V) :
  @complex.Re R (\Tr (bb84_pe_pass_key_public_readout_state EA xi)) = bb84_source_pass_prob EA xi.
Proof. have bb84_pe_pass_key_public_readout_trace_source : forall (EA : @adversary R L HL V bb84_Eve) (xi : @cq_state R L HL (bb84_cvar M)
  V), \Tr (bb84_pe_pass_key_public_readout_state EA xi) = \Tr (bb84_pe_pass_key_public_source_state EA xi).
{ clear xi EA; move=> EA xi. have bb84_pe_pass_key_public_readout_source_ptraceso_all_sources : forall (EA : @adversary R L HL V bb84_Eve) (xi : @cq_state R L HL (bb84_cvar M) V), ptraceso [set x : L | if x is inr (inl _) then true else false] (bb84_pe_pass_key_public_readout_state EA xi) = ptraceso [set x : L | if x is inr (inl _) then true else false] (bb84_pe_pass_key_public_source_state EA xi).
{ clear xi EA; move=> EA xi. rewrite /bb84_pe_pass_key_public_readout_state /bb84_pe_pass_key_public_source_state /bb84_pe_pass_history_public_readout_state /bb84_pe_pass_history_public_source_state. rewrite [in LHS]linear_sum /=. rewrite [in RHS]linear_sum /=. apply: eq_bigr => s _. rewrite [in LHS]linear_sum /=. rewrite [in RHS]linear_sum /=. apply: eq_bigr => h _.
  rewrite [in LHS]linearZ /=. rewrite [in RHS]linearZ /=. set Qpub := bb84_S :|: bb84_Epub; set Qsrc := [set x : L | if x is inr (inl _) then true else false]. set C0 := ([set: L] : {set L}) :\: (Qpub :|: Qsrc). have Hpub_src : [disjoint Qpub & Qsrc].
  { apply/disjointP=> x Hx_pub. apply/negP=> Hx_src. move: Hx_pub; rewrite /Qpub /Qsrc /bb84_S /bb84_Epub /bb84_reg /bb84_bridge_reg !inE.
    by case/orP=> /eqP Hx; move: Hx_src; rewrite /Qsrc inE Hx. } have Hpub_C : [disjoint Qpub & C0] := disjoint_setDUl Qpub Qsrc.
    have Hsrc_C : [disjoint Qsrc & C0] := disjoint_setDUr Qpub Qsrc. have Heq : Qpub :|: Qsrc :|: C0 = ([set: L] : {set L}) by rewrite /C0 setUD_sub. set pub := bb84_key_public_register_state _. have Hbranch : ptraceso Qsrc (@replaceso R L HL Qpub pub (bb84_history_readout_state EA h (xi s))) = ptraceso Qsrc (@replaceso R L HL Qpub pub (bb84_history_source_state EA h (xi s))).
  { apply: (@ptraceso_replaceso_disjoint_eq R L HL Qpub Qsrc C0 Hpub_src Hpub_C Hsrc_C Heq). case Hdecoded: (bb84_history_decoded h).
    - rewrite (bb84_history_readout_source_ptraceso_all_sources (h := h) EA (xi s)); first by []. by rewrite Hdecoded.
    - by rewrite /bb84_history_readout_state /bb84_history_source_state /bb84_trace_source_state -bb84_history_decoded_traceE Hdecoded !linear0. } by rewrite Hbranch. } have /cptpP [_ /tpmapP Htp] := @ptraceso_qc R L HL [set x : L | if x is inr (inl _) then true else false] (setTfor L). rewrite -(Htp (bb84_pe_pass_key_public_readout_state EA xi)) -(Htp (bb84_pe_pass_key_public_source_state EA xi)). by rewrite bb84_pe_pass_key_public_readout_source_ptraceso_all_sources. }
have bb84_pe_pass_key_public_source_traceE : forall (EA : @adversary R L HL V bb84_Eve) (xi : @cq_state R L HL (bb84_cvar M) V), \Tr (bb84_pe_pass_key_public_source_state EA xi) = \Tr (@bb84_pass_history_source_state R P q dev LE HE bb84_register_index bb84_register_space EA xi).
{ clear xi EA; move=> EA xi. rewrite /bb84_pe_pass_key_public_source_state /bb84_pe_pass_history_public_source_state /bb84_pass_history_source_state. rewrite [in LHS]linear_sum /=. rewrite [in RHS]linear_sum /=. apply: eq_bigr => s _.
  rewrite [in LHS]linear_sum /=. rewrite [in RHS]linear_sum /=. apply: eq_bigr => h _. rewrite [in LHS]linearZ /=. rewrite [in RHS]linearZ /=.
  by rewrite replaceso_trlf_den1 ?bb84_key_public_register_state_den1lf. } rewrite /bb84_source_pass_prob. by congr (@complex.Re R _); rewrite bb84_pe_pass_key_public_readout_trace_source; exact: bb84_pe_pass_key_public_source_traceE. Qed.

Definition bb84_pe_pass_leakage_public_readout_state (EA : @adversary R L HL V bb84_Eve) (xi : @cq_state R L HL (bb84_cvar M) V) :=
  @bb84_pe_pass_history_public_readout_state R P q dev LE HE bb84_register_index bb84_register_space (bb84_Ppub :|: (bb84_S :|: bb84_Epub))
    bb84_leakage_public_register_state EA xi.
Lemma bb84_pe_pass_leakage_public_readout_trace_key_public (EA : @adversary R L HL V bb84_Eve) (xi : @cq_state R L HL (bb84_cvar M) V) :
  \Tr (bb84_pe_pass_leakage_public_readout_state EA xi) = \Tr (bb84_pe_pass_key_public_readout_state EA xi).
Proof. rewrite /bb84_pe_pass_leakage_public_readout_state /bb84_pe_pass_key_public_readout_state /bb84_pe_pass_history_public_readout_state.
  rewrite [in LHS]linear_sum /=. rewrite [in RHS]linear_sum /=. apply: eq_bigr => s _. rewrite [in LHS]linear_sum /=. rewrite [in RHS]linear_sum /=. apply: eq_bigr => h _. rewrite [in LHS]linearZ /=. rewrite [in RHS]linearZ /=.
  by rewrite !replaceso_trlf_den1 ?bb84_leakage_public_register_state_den1lf ?bb84_key_public_register_state_den1lf. Qed.

Fact bb84_pe_pass_leakage_public_readout_state_marginal (EA : @adversary R L HL V bb84_Eve) (xi : @cq_state R L HL (bb84_cvar M) V) :
  ptrace_cast_gen (bb84_setT_diff_complement (bb84_S :|: bb84_E)) (bb84_pe_pass_leakage_public_readout_state EA xi) =
  ptrace_cast_gen (bb84_setT_diff_complement (bb84_S :|: bb84_E)) (bb84_pe_pass_key_public_readout_state EA xi).
Proof. rewrite /bb84_pe_pass_leakage_public_readout_state /bb84_pe_pass_key_public_readout_state /bb84_pe_pass_history_public_readout_state.
  rewrite /ptrace_cast_gen [\Tr_(~: (bb84_S :|: bb84_E)) _]raddf_sum /= [\Tr_(~: (bb84_S :|: bb84_E)) _]raddf_sum /= raddf_sum /=.
  rewrite raddf_sum /=; apply: eq_bigr => s _. rewrite [\Tr_(~: (bb84_S :|: bb84_E)) _]raddf_sum /= [\Tr_(~: (bb84_S :|: bb84_E)) _]raddf_sum /= raddf_sum /=. rewrite raddf_sum /=; apply: eq_bigr => h _. rewrite [in LHS]linearZ /= [in LHS]linearZ /=.
  rewrite [in RHS]linearZ /= [in RHS]linearZ /=; congr (_ *: _). set fs := (X in bb84_leakage_public_register_state X).
  change (ptrace_cast_gen (bb84_setT_diff_complement (bb84_S :|: bb84_E)) (@replaceso R L HL (bb84_Ppub :|: (bb84_S :|: bb84_Epub)) (bb84_leakage_public_register_state fs) (bb84_history_readout_state EA h (xi s))) = ptrace_cast_gen (bb84_setT_diff_complement (bb84_S :|: bb84_E)) (@replaceso R L HL (bb84_S :|: bb84_Epub) (bb84_key_public_register_state fs) (bb84_history_readout_state EA h (xi s)))).
  exact: bb84_leakage_public_replaceso_target_marginal. Qed.

Fact bb84_pe_pass_leakage_public_readout_state_pa_cq_Epub (EA : @adversary R L HL V bb84_Eve) (xi : @cq_state R L HL (bb84_cvar M) V)
    (x x' : 'Idx[HL]_bb84_S) : x' != x -> ((liftf_lf (([> deltav x ; deltav x <] \O (\1 : 'F[HL]_(bb84_Epub :|: bb84_Ppub))) :
        'F[HL]_(bb84_S :|: (bb84_Epub :|: bb84_Ppub))) \o bb84_pe_pass_leakage_public_readout_state EA xi) \o liftf_lf
      (([> deltav x' ; deltav x' <] \O (\1 : 'F[HL]_(bb84_Epub :|: bb84_Ppub))) : 'F[HL]_(bb84_S :|: (bb84_Epub :|: bb84_Ppub)))) = 0.
Proof. move=> Hx'x; rewrite /bb84_pe_pass_leakage_public_readout_state /bb84_pe_pass_history_public_readout_state.
  rewrite [X in X \o _ = _]linear_sumr /= linear_sumlz /=. apply: big1 => s _. rewrite [X in X \o _ = _]linear_sumr /= linear_sumlz /=.
  apply: big1 => h _. by rewrite [X in X \o _ = _]linearZr /= linearZl /=; rewrite bb84_leakage_public_replaceso_pa_cq //; rewrite scaler0. Qed.

Fact bb84_pe_pass_leakage_public_readout_state_classical_E (EA : @adversary R L HL V bb84_Eve) (xi : @cq_state R L HL (bb84_cvar M) V)
    (p p' : 'Idx[HL]_bb84_Ppub) : p' != p -> ((liftf_lf (([> deltav p ; deltav p <] \O (\1 : 'F[HL]_(bb84_S :|: bb84_E))) :
        'F[HL]_(bb84_Ppub :|: (bb84_S :|: bb84_E))) \o bb84_pe_pass_leakage_public_readout_state EA xi) \o liftf_lf
      (([> deltav p' ; deltav p' <] \O (\1 : 'F[HL]_(bb84_S :|: bb84_E))) : 'F[HL]_(bb84_Ppub :|: (bb84_S :|: bb84_E)))) = 0.
Proof. have bb84_pe_pass_leakage_public_readout_state_classical : forall (EA : @adversary R L HL V bb84_Eve) (xi : @cq_state R L HL
  (bb84_cvar M) V) (p p' : 'Idx[HL]_bb84_Ppub), p' != p -> ((liftf_lf (([> deltav p ; deltav p <] \O (\1 : 'F[HL]_(bb84_S :|: bb84_Epub))) : 'F[HL]_(bb84_Ppub :|: (bb84_S :|: bb84_Epub))) \o bb84_pe_pass_leakage_public_readout_state EA xi) \o liftf_lf (([> deltav p' ; deltav p' <] \O (\1 : 'F[HL]_(bb84_S :|: bb84_Epub))) : 'F[HL]_(bb84_Ppub :|: (bb84_S :|: bb84_Epub)))) = 0.
{ clear p' p xi EA; move=> EA xi p p'. move=> Hp'p. rewrite /bb84_pe_pass_leakage_public_readout_state /bb84_pe_pass_history_public_readout_state. rewrite [X in X \o _ = _]linear_sumr /= linear_sumlz /=. apply: big1 => s _.
  rewrite [X in X \o _ = _]linear_sumr /= linear_sumlz /=. apply: big1 => h _. rewrite [X in X \o _ = _]linearZr /= linearZl /=.
  rewrite bb84_leakage_public_replaceso_classical //. by rewrite scaler0. } move=> Hp'p; have HPS_Epub := bb84_disP_SEpub.
  have Hlift : forall p0 : 'Idx[HL]_bb84_Ppub, liftf_lf (([> deltav p0 ; deltav p0 <] \O (\1 : 'F[HL]_(bb84_S :|: bb84_E))) : 'F[HL]_(bb84_Ppub :|: (bb84_S :|: bb84_E))) = liftf_lf (([> deltav p0 ; deltav p0 <] \O (\1 : 'F[HL]_(bb84_S :|: bb84_Epub))) : 'F[HL]_(bb84_Ppub :|: (bb84_S :|: bb84_Epub))).
  { move=> p0. have Hleft : (([> deltav p0 ; deltav p0 <] \O (\1 : 'F[HL]_(bb84_S :|: bb84_E))) : 'F[HL]_(bb84_Ppub :|: (bb84_S :|: bb84_E))) = [> deltav p0 ; deltav p0 <] \⊗ (\1 : 'F[HL]_(bb84_S :|: bb84_E)).
    { by apply: to_Fnd_inj; rewrite (sdotFT _ _ bb84_disPSE) to_Fnd_tenE. } have Hright : (([> deltav p0 ; deltav p0 <] \O (\1 : 'F[HL]_(bb84_S :|: bb84_Epub))) : 'F[HL]_(bb84_Ppub :|: (bb84_S :|: bb84_Epub))) = [> deltav p0 ; deltav p0 <] \⊗ (\1 : 'F[HL]_(bb84_S :|: bb84_Epub)).
    { by apply: to_Fnd_inj; rewrite (sdotFT _ _ HPS_Epub) to_Fnd_tenE. } rewrite Hleft Hright.
      by rewrite !liftf_lf_tenf1r ?bb84_disPSE ?HPS_Epub. } by rewrite (Hlift p) (Hlift p'); exact: bb84_pe_pass_leakage_public_readout_state_classical. Qed.

Definition rhoPSE_readout_pass_prog (EA : @adversary R L HL V bb84_Eve) (xi : @cq_state R L HL (bb84_cvar M) V) :
    'F[HL]_(bb84_Ppub :|: (bb84_S :|: bb84_E)) := let st := bb84_pe_pass_leakage_public_readout_state EA xi in
  ptrace_cast_gen (bb84_setT_diff_complement (bb84_Ppub :|: (bb84_S :|: bb84_E))) (((@complex.Re R (\Tr st))^-1)%:C *: st).
Lemma rhoPSE_readout_pass_prog_trace1 (EA : @adversary R L HL V bb84_Eve) (xi : @cq_state R L HL (bb84_cvar M) V) :
  let st := bb84_pe_pass_leakage_public_readout_state EA xi in
  0 < @complex.Re R (\Tr st) -> @complex.Re R (\Tr (rhoPSE_readout_pass_prog EA xi)) = 1.
Proof. rewrite /rhoPSE_readout_pass_prog. set st := bb84_pe_pass_leakage_public_readout_state EA xi; move=> Hpass;
  rewrite /ptrace_cast_gen castlf_trlfE. have /cptpP [_ /tpmapP Htp] := @ptraceso_qc R L HL (mathcomp.boot.finset.setC (bb84_Ppub :|: (bb84_S :|: bb84_E))) (setTfor L). rewrite Htp linearZ /=. have HRe_realM : forall (r : R) (z : C), @complex.Re R (r%:C * z) = r * @complex.Re R z.
  { move=> r z. by case: z => zr zi /=; rewrite mul0r subr0. } by rewrite HRe_realM; rewrite mulVf ?lt0r_neq0. Qed.

Lemma rhoPSE_readout_pass_prog_tr_le1 (EA : @adversary R L HL V bb84_Eve) (xi : @cq_state R L HL (bb84_cvar M) V) :
  (forall s, xi s \is psdlf) -> @complex.Re R (\Tr (rhoPSE_readout_pass_prog EA xi)) <= 1.
Proof. set st := bb84_pe_pass_leakage_public_readout_state EA xi; move=> Hxi; have Hst_psd : st \is psdlf.
  { rewrite /st /bb84_pe_pass_leakage_public_readout_state. apply: (@bb84_pe_pass_history_public_readout_state_psd R P q dev LE HE bb84_register_index bb84_register_space (bb84_Ppub :|: (bb84_S :|: bb84_Epub)) bb84_leakage_public_register_state EA xi).
    - exact: bb84_leakage_public_register_state_den1lf.
    - exact: Hxi. } have Hst_ge0 : 0 <= @complex.Re R (\Tr st) by have := psdlf_trlf Hst_psd; rewrite lecE /= => /andP[].
      have [Hpass|Hpass] := boolP (0 < @complex.Re R (\Tr st)).
  - by rewrite (rhoPSE_readout_pass_prog_trace1 (EA := EA) (xi := xi) Hpass).
  - have Hst_le0 : @complex.Re R (\Tr st) <= 0 by move: Hpass; rewrite -leNgt. have Hst0 : @complex.Re R (\Tr st) = 0 by apply/eqP; rewrite eq_le Hst_ge0 Hst_le0. rewrite /rhoPSE_readout_pass_prog -/st /ptrace_cast_gen castlf_trlfE.
    have /cptpP [_ /tpmapP Htp] := @ptraceso_qc R L HL (mathcomp.boot.finset.setC (bb84_Ppub :|: (bb84_S :|: bb84_E))) (setTfor L).
    rewrite Htp linearZ /=. have HRe_realM : forall (r : R) (z : C), @complex.Re R (r%:C * z) = r * @complex.Re R z.
    { move=> r z. by case: z => zr zi /=; rewrite mul0r subr0. } by rewrite HRe_realM Hst0 mulr0 ler01. Qed.

Fact rhoPSE_readout_pass_prog_classical (EA : @adversary R L HL V bb84_Eve) (xi : @cq_state R L HL (bb84_cvar M) V)
    (p p' : 'Idx[HL]_bb84_Ppub) : p' != p -> ((([> deltav p ; deltav p <] \O (\1 : 'F[HL]_(bb84_S :|: bb84_E))) \o
    rhoPSE_readout_pass_prog EA xi) \o ([> deltav p' ; deltav p' <] \O (\1 : 'F[HL]_(bb84_S :|: bb84_E)))) = 0.
Proof. move=> Hp'p; rewrite /rhoPSE_readout_pass_prog. set st := bb84_pe_pass_leakage_public_readout_state EA xi;
  set c := ((@complex.Re R (\Tr st))^-1)%:C. set Pp := (([> deltav p ; deltav p <] \O (\1 : 'F[HL]_(bb84_S :|: bb84_E))) : 'F[HL]_(bb84_Ppub :|: (bb84_S :|: bb84_E))). set Pp' := (([> deltav p' ; deltav p' <] \O (\1 : 'F[HL]_(bb84_S :|: bb84_E))) : 'F[HL]_(bb84_Ppub :|: (bb84_S :|: bb84_E))). apply/eqP/trlf_intror => g. rewrite comp_lfun0l -!comp_lfunA lftraceC -comp_lfunA.
  rewrite (ptrace_cast_gen_setC_liftf_lf_tr (bb84_setT_diff_complement (bb84_Ppub :|: (bb84_S :|: bb84_E))) (c *: st) (Pp' \o g \o Pp)).
  rewrite -comp_lfunZl linearZ /= !liftf_lf_comp. rewrite !comp_lfunA lftraceC -!comp_lfunA !comp_lfunA (bb84_pe_pass_leakage_public_readout_state_classical_E EA xi Hp'p) comp_lfun0l. have Htr0 : \Tr (0 : 'F[HL]_(bb84_Ppub :|: (bb84_S :|: bb84_E))) = 0 by rewrite linear0. have Htr0_full : \Tr (0 : 'F[HL]_(setTfor L)) = 0. { by rewrite linear0. } by rewrite Htr0_full Htr0; rewrite mulr0. Qed.

Fact rhoPSE_readout_pass_prog_pa_cq (EA : @adversary R L HL V bb84_Eve) (xi : @cq_state R L HL (bb84_cvar M) V) :
  let eq_pub_assoc := bb84_public_assoc bb84_S bb84_E bb84_Ppub in @is_cq_state R L HL bb84_S (bb84_E :|: bb84_Ppub)
    (castlf (eq_pub_assoc, eq_pub_assoc) (rhoPSE_readout_pass_prog EA xi)).
Proof. have rhoPSE_readout_pass_prog_key_cq : forall (EA : @adversary R L HL V bb84_Eve) (xi : @cq_state R L HL (bb84_cvar M) V) (x x' :
  'Idx[HL]_bb84_S), x' != x -> (((\1 : 'F[HL]_bb84_Ppub) \O (([> deltav x ; deltav x <] \O (\1 : 'F[HL]_bb84_E)) : 'F[HL]_(bb84_S :|: bb84_E)) \o rhoPSE_readout_pass_prog EA xi) \o ((\1 : 'F[HL]_bb84_Ppub) \O (([> deltav x' ; deltav x' <] \O (\1 : 'F[HL]_bb84_E)) : 'F[HL]_(bb84_S :|: bb84_E)))) = 0.
{ clear xi EA; move=> EA xi x x'. move=> Hx'x; rewrite /rhoPSE_readout_pass_prog. set st := bb84_pe_pass_leakage_public_readout_state EA xi; set c := ((@complex.Re R (\Tr st))^-1)%:C. set KxE := (([> deltav x ; deltav x <] \O (\1 : 'F[HL]_bb84_E)) : 'F[HL]_(bb84_S :|: bb84_E)).
  set KxE' := (([> deltav x' ; deltav x' <] \O (\1 : 'F[HL]_bb84_E)) : 'F[HL]_(bb84_S :|: bb84_E)).
  set KxPSE := ((\1 : 'F[HL]_bb84_Ppub) \O KxE : 'F[HL]_(bb84_Ppub :|: (bb84_S :|: bb84_E))). set KxPSE' := ((\1 : 'F[HL]_bb84_Ppub) \O KxE' : 'F[HL]_(bb84_Ppub :|: (bb84_S :|: bb84_E))). have Hlift : forall x0 : 'Idx[HL]_bb84_S, liftf_lf (((\1 : 'F[HL]_bb84_Ppub) \O (([> deltav x0 ; deltav x0 <] \O (\1 : 'F[HL]_bb84_E)) : 'F[HL]_(bb84_S :|: bb84_E))) : 'F[HL]_(bb84_Ppub :|: (bb84_S :|: bb84_E))) = liftf_lf (([> deltav x0 ; deltav x0 <] \O (\1 : 'F[HL]_(bb84_Epub :|: bb84_Ppub))) : 'F[HL]_(bb84_S :|: (bb84_Epub :|: bb84_Ppub))).
  { move=> x0; have HdisS_EpubP : [disjoint bb84_S & bb84_Epub :|: bb84_Ppub]. { by rewrite disjointXU bb84_disS_Epub bb84_disSP. }
set KxE0 := (([> deltav x0 ; deltav x0 <] \O (\1 : 'F[HL]_bb84_E)) : 'F[HL]_(bb84_S :|: bb84_E)).
    have Hleft : (((\1 : 'F[HL]_bb84_Ppub) \O KxE0) : 'F[HL]_(bb84_Ppub :|: (bb84_S :|: bb84_E))) = (\1 : 'F[HL]_bb84_Ppub) \⊗ KxE0.
    { by apply: to_Fnd_inj; rewrite (sdotFT _ _ bb84_disPSE) to_Fnd_tenE. } have HkeyE : KxE0 = [> deltav x0 ; deltav x0 <] \⊗ (\1 : 'F[HL]_bb84_E).
    { by apply: to_Fnd_inj; rewrite (sdotFT _ _ bb84_disSE) to_Fnd_tenE. } have Hright : (([> deltav x0 ; deltav x0 <] \O (\1 : 'F[HL]_(bb84_Epub :|: bb84_Ppub))) : 'F[HL]_(bb84_S :|: (bb84_Epub :|: bb84_Ppub))) = [> deltav x0 ; deltav x0 <] \⊗ (\1 : 'F[HL]_(bb84_Epub :|: bb84_Ppub)).
    { by apply: to_Fnd_inj; rewrite (sdotFT _ _ HdisS_EpubP) to_Fnd_tenE. } rewrite Hleft HkeyE Hright (liftf_lf_tenf1l _ bb84_disPSE) (liftf_lf_tenf1r _ bb84_disSE). by rewrite (liftf_lf_tenf1r _ HdisS_EpubP). } apply/eqP/trlf_intror => g.
      rewrite comp_lfun0l -!comp_lfunA lftraceC -comp_lfunA. rewrite (ptrace_cast_gen_setC_liftf_lf_tr (bb84_setT_diff_complement (bb84_Ppub :|: (bb84_S :|: bb84_E))) (c *: st) (KxPSE' \o g \o KxPSE)). rewrite -comp_lfunZl linearZ /= !liftf_lf_comp.
      rewrite !comp_lfunA lftraceC -!comp_lfunA !comp_lfunA (Hlift x) (Hlift x').
      rewrite (bb84_pe_pass_leakage_public_readout_state_pa_cq_Epub EA xi Hx'x) comp_lfun0l.
      have Htr0 : \Tr (0 : 'F[HL]_(bb84_Ppub :|: (bb84_S :|: bb84_E))) = 0 by rewrite linear0. have Htr0_full : \Tr (0 : 'F[HL]_(setTfor L)) = 0. { by rewrite linear0. } rewrite Htr0_full Htr0. by rewrite mulr0. } set eq_pub_assoc := bb84_public_assoc bb84_S bb84_E bb84_Ppub; rewrite /is_cq_state. apply/forallP => x; apply/forallP => x'; apply/implyP => Hx'x. apply/eqP. set KxEP := (([> deltav x ; deltav x <] \O (\1 : 'F[HL]_(bb84_E :|: bb84_Ppub))) : 'F[HL]_(bb84_S :|: (bb84_E :|: bb84_Ppub))). set KxEP' := (([> deltav x' ; deltav x' <] \O (\1 : 'F[HL]_(bb84_E :|: bb84_Ppub))) : 'F[HL]_(bb84_S :|: (bb84_E :|: bb84_Ppub))). set KxE := (([> deltav x ; deltav x <] \O (\1 : 'F[HL]_bb84_E)) : 'F[HL]_(bb84_S :|: bb84_E)). set KxE' := (([> deltav x' ; deltav x' <] \O (\1 : 'F[HL]_bb84_E)) : 'F[HL]_(bb84_S :|: bb84_E)). set KxPSE := ((\1 : 'F[HL]_bb84_Ppub) \O KxE : 'F[HL]_(bb84_Ppub :|: (bb84_S :|: bb84_E))). set KxPSE' := ((\1 : 'F[HL]_bb84_Ppub) \O KxE' : 'F[HL]_(bb84_Ppub :|: (bb84_S :|: bb84_E))).
      have HdisP_SEdiff : [disjoint bb84_Ppub & (bb84_S :|: bb84_E) :\: bb84_S].
  { apply/disjointP => a HP. move/disjointP: bb84_disPSE => HPSE; apply/negP => Hdiff. move: Hdiff; rewrite inE => /andP [_ HSE].
    by move: (HPSE a HP); rewrite HSE. } have HdisP_Ediff : [disjoint bb84_Ppub & bb84_E :\: bb84_S].
  { apply/disjointP => a HP. have HPE : [disjoint bb84_Ppub & bb84_E] by rewrite disjoint_sym bb84_disEP. move/disjointP: HPE => HPE; apply/negP => Hdiff. move: Hdiff; rewrite inE => /andP [_ HEin]. by move: (HPE a HP); rewrite HEin. }
have HdisP_S_Ediff : [disjoint bb84_Ppub & bb84_S :|: bb84_E :\: bb84_S].
  { have HPS : [disjoint bb84_Ppub & bb84_S] by rewrite disjoint_sym bb84_disSP. by rewrite disjointXU HPS HdisP_Ediff. }
have HdisP_E_Sdiff : [disjoint bb84_Ppub & bb84_E :|: bb84_S :\: bb84_E].
  { apply/disjointP => a HP. move/disjointP: bb84_disPSE => HPSE; apply/negP => Hmem. have HSE : a \in bb84_S :|: bb84_E.
    { move: Hmem; rewrite inE => /orP [HEin | HSdiff].
      - by rewrite inE HEin orbT.
      - move: HSdiff; rewrite inE => /andP [_ HSin]. by rewrite inE HSin. } by move: (HPSE a HP); rewrite HSE. }
have Hleft : KxEP = castlf (eq_pub_assoc, eq_pub_assoc) KxPSE.
  { have HIEP : (\1 : 'F[HL]_(bb84_E :|: bb84_Ppub)) = (\1 : 'F[HL]_bb84_E) \O (\1 : 'F[HL]_bb84_Ppub).
    { by rewrite sdotf11. } apply: to_Fnd_inj. rewrite /KxEP /KxPSE /KxE HIEP Fnd_cast !to_Fnd_sdotE !dotFA -[RHS]dotFA [RHS]dotFC.
    - by [].
    - by rewrite /= HdisP_S_Ediff.
    - by rewrite /= HdisP_E_Sdiff. } have Hright : KxEP' = castlf (eq_pub_assoc, eq_pub_assoc) KxPSE'.
  { have HIEP : (\1 : 'F[HL]_(bb84_E :|: bb84_Ppub)) = (\1 : 'F[HL]_bb84_E) \O (\1 : 'F[HL]_bb84_Ppub).
    { by rewrite sdotf11. } apply: to_Fnd_inj. rewrite /KxEP' /KxPSE' /KxE' HIEP Fnd_cast !to_Fnd_sdotE !dotFA -[RHS]dotFA [RHS]dotFC.
    - by [].
    - by rewrite /= HdisP_S_Ediff.
    - by rewrite /= HdisP_E_Sdiff. } rewrite Hleft Hright -!(castlf_complf eq_pub_assoc eq_pub_assoc eq_pub_assoc); apply/eqP.
      rewrite (@castlf_eq0 R L HL _ _ _ _ (eq_pub_assoc, eq_pub_assoc) (KxPSE \o rhoPSE_readout_pass_prog EA xi \o KxPSE')). by apply/eqP; rewrite rhoPSE_readout_pass_prog_key_cq. Qed.

Fact rhoPSE_readout_pass_prog_marginal (EA : @adversary R L HL V bb84_Eve) (xi : @cq_state R L HL (bb84_cvar M) V) :
  ptrace_castl bb84_disPSE (rhoPSE_readout_pass_prog EA xi) = rhoXE_readout_pass_prog EA xi.
Proof. apply/eqP/trlf_intror => g. rewrite -(@trlf_lift_partial R L HL bb84_Ppub (bb84_S :|: bb84_E) bb84_disPSE (rhoPSE_readout_pass_prog
  EA xi) g). rewrite /rhoPSE_readout_pass_prog /rhoXE_readout_pass_prog. set stP := bb84_pe_pass_leakage_public_readout_state EA xi; set stX := bb84_pe_pass_key_public_readout_state EA xi. set cP := ((@complex.Re R (\Tr stP))^-1)%:C; set cX := ((@complex.Re R (\Tr stX))^-1)%:C. rewrite (ptrace_cast_gen_setC_liftf_lf_tr (bb84_setT_diff_complement (bb84_Ppub :|: (bb84_S :|: bb84_E))) (cP *: stP) (((\1 : 'F[HL]_bb84_Ppub) \O g) : 'F[HL]_(bb84_Ppub :|: (bb84_S :|: bb84_E)))).
  rewrite (ptrace_cast_gen_setC_liftf_lf_tr (bb84_setT_diff_complement (bb84_S :|: bb84_E)) (cX *: stX) g).
  rewrite -[in LHS]comp_lfunZl [in LHS]linearZ /= -[in RHS]comp_lfunZl [in RHS]linearZ /=.
  have Htr : \Tr stP = \Tr stX by rewrite /stP /stX; exact: bb84_pe_pass_leakage_public_readout_trace_key_public. rewrite /cP /cX Htr; congr (_ * _). have Hlift : liftf_lf (((\1 : 'F[HL]_bb84_Ppub) \O g) : 'F[HL]_(bb84_Ppub :|: (bb84_S :|: bb84_E))) = liftf_lf g.
  { have Hten : (((\1 : 'F[HL]_bb84_Ppub) \O g) : 'F[HL]_(bb84_Ppub :|: (bb84_S :|: bb84_E))) = (\1 : 'F[HL]_bb84_Ppub) \⊗ g.
    { by apply: to_Fnd_inj; rewrite (sdotFT _ _ bb84_disPSE) to_Fnd_tenE. } by rewrite Hten liftf_lf_tenf1l ?bb84_disPSE. } rewrite Hlift; move: (bb84_pe_pass_leakage_public_readout_state_marginal EA xi); move=> Hmarg. move: (congr1 (fun z => \Tr (z \o g)) Hmarg); by rewrite !ptrace_cast_gen_setC_liftf_lf_tr. Qed.

Fact bb84_post_hash_public_ptrace_linear : linear (fun rho : 'F[HL]_(setTfor L) => post_hash_state bb84_disSEpub bb84_pa_hash_index
      (castlf (bb84_public_assoc bb84_S bb84_E bb84_Ppub, bb84_public_assoc bb84_S bb84_E bb84_Ppub) (ptrace_cast_gen
          (bb84_setT_diff_complement (bb84_Ppub :|: (bb84_S :|: bb84_E))) rho))).
Proof. move=> a rho tau; rewrite /ptrace_cast_gen; rewrite [\Tr_(~: (bb84_Ppub :|: (bb84_S :|: bb84_E))) (a *: rho + tau)]linearP /=.
  rewrite [castlf (bb84_setT_diff_complement (bb84_Ppub :|: (bb84_S :|: bb84_E)), bb84_setT_diff_complement (bb84_Ppub :|: (bb84_S :|: bb84_E))) (_ + _)]linearD /=. rewrite [castlf (bb84_setT_diff_complement (bb84_Ppub :|: (bb84_S :|: bb84_E)), bb84_setT_diff_complement (bb84_Ppub :|: (bb84_S :|: bb84_E))) (a *: _)]linearZ /=. rewrite [castlf (bb84_public_assoc bb84_S bb84_E bb84_Ppub, bb84_public_assoc bb84_S bb84_E bb84_Ppub) (_ + _)]linearD /=. rewrite [castlf (bb84_public_assoc bb84_S bb84_E bb84_Ppub, bb84_public_assoc bb84_S bb84_E bb84_Ppub) (a *: _)]linearZ /=. set X := castlf (bb84_public_assoc bb84_S bb84_E bb84_Ppub, bb84_public_assoc bb84_S bb84_E bb84_Ppub) (castlf (bb84_setT_diff_complement (bb84_Ppub :|: (bb84_S :|: bb84_E)), bb84_setT_diff_complement (bb84_Ppub :|: (bb84_S :|: bb84_E))) (\Tr_(~: (bb84_Ppub :|: (bb84_S :|: bb84_E))) rho)). set Y := castlf (bb84_public_assoc bb84_S bb84_E bb84_Ppub, bb84_public_assoc bb84_S bb84_E bb84_Ppub) (castlf (bb84_setT_diff_complement (bb84_Ppub :|: (bb84_S :|: bb84_E)), bb84_setT_diff_complement (bb84_Ppub :|: (bb84_S :|: bb84_E))) (\Tr_(~: (bb84_Ppub :|: (bb84_S :|: bb84_E))) tau)). change (post_hash_state bb84_disSEpub bb84_pa_hash_index (a *: X + Y) = a *: post_hash_state bb84_disSEpub bb84_pa_hash_index X + post_hash_state bb84_disSEpub bb84_pa_hash_index Y).
  exact: (@post_hash_state_linear R L HL bb84_S (bb84_E :|: bb84_Ppub) bb84_Fl bb84_Zl bb84_disSEpub bb84_pa_hash_index a X Y). Qed.

Definition bb84_pa_public_branch_ptrace (s : @store (bb84_cvar M) V) (fidx : 'I_(cd_paseed_count dev)) (rho : 'F[HL]_(setTfor L)) :
    'F[HL]_(bb84_Zl :|: (bb84_Fl :|: (bb84_E :|: bb84_Ppub))) := ptrace_cast_gen (bb84_setT_diff_complement
      (bb84_Zl :|: (bb84_Fl :|: (bb84_E :|: bb84_Ppub)))) (@replaceso R L HL (bb84_Zl :|: (bb84_Fl :|: (bb84_Epub :|: bb84_Ppub)))
      ([> deltav (bb84_pa_hash_index (bb84_Fl_index fidx) (bb84_S_index (bb84_raw_key_index (s (@BVXA M)))) ) ;
        deltav (bb84_pa_hash_index (bb84_Fl_index fidx) (bb84_S_index (bb84_raw_key_index (s (@BVXA M)))) ) <] \⊗
        ([> deltav (bb84_Fl_index fidx) ; deltav (bb84_Fl_index fidx) <] \⊗ (bb84_public_register_state s \⊗
            bb84_leakage_register_state s))) rho).
Fact bb84_pa_public_pseed_branch_ptrace (c : C) (fval : V) (s : @store (bb84_cvar M) V) (rho : 'F[HL]_(setTfor L)) : ptrace_cast_gen
    (bb84_setT_diff_complement (bb84_Zl :|: (bb84_Fl :|: (bb84_E :|: bb84_Ppub)))) (match bb84_paseed_of fval with | Some fidx => c *:
        @replaceso R L HL (bb84_Zl :|: (bb84_Fl :|: (bb84_Epub :|: bb84_Ppub))) ([> deltav (bb84_pa_hash_index (bb84_Fl_index fidx)
              (bb84_S_index (bb84_raw_key_index (s (@BVXA M)))) ) ; deltav (bb84_pa_hash_index (bb84_Fl_index fidx)
              (bb84_S_index (bb84_raw_key_index (s (@BVXA M)))) ) <] \⊗ ([> deltav (bb84_Fl_index fidx) ; deltav (bb84_Fl_index fidx) <] \⊗
              (bb84_public_register_state s \⊗ bb84_leakage_register_state s))) rho | None => 0 end) = c *: match bb84_paseed_of fval with
    | Some fidx => bb84_pa_public_branch_ptrace s fidx rho | None => 0 end.
Proof. case: (bb84_paseed_of fval) => [fidx|].
  - by rewrite ptrace_cast_gen_scale /bb84_pa_public_branch_ptrace.
  - by rewrite ptrace_cast_gen0 scaler0. Qed.

Fact bb84_leakage_public_replaceso_branch_ptrace (s : @store (bb84_cvar M) V) (rho : 'F[HL]_(setTfor L)) : castlf
    (bb84_public_assoc bb84_S bb84_E bb84_Ppub, bb84_public_assoc bb84_S bb84_E bb84_Ppub) (ptrace_cast_gen
      (bb84_setT_diff_complement (bb84_Ppub :|: (bb84_S :|: bb84_E))) (@replaceso R L HL (bb84_Ppub :|: (bb84_S :|: bb84_Epub))
        (bb84_leakage_public_register_state s) rho)) = (bb84_alice_key_register_state s \O ptrace_cast_gen
      (bb84_setT_diff_complement (bb84_E :|: bb84_Ppub)) (@replaceso R L HL (bb84_Epub :|: bb84_Ppub)
        (bb84_public_register_state s \⊗ bb84_leakage_register_state s) rho) : 'F[HL]_(bb84_S :|: (bb84_E :|: bb84_Ppub))).
Proof. set T := bb84_Ppub :|: (bb84_S :|: bb84_E); set A := bb84_Ppub :|: (bb84_S :|: bb84_Epub). set B := mathcomp.boot.finset.setC T;
  set C0 := bb84_Eve. set T0 := bb84_E :|: bb84_Ppub; set A0 := bb84_Epub :|: bb84_Ppub. set B0 := mathcomp.boot.finset.setC T0; set payload := bb84_public_register_state s \⊗ bb84_leakage_register_state s. have HAB : [disjoint A & B].
  { apply/disjointP => x HxA; apply/negP => HxB. have HxT : x \in T.
    { move: HxA; rewrite /A /T !inE => /orP [HP | /orP [HS | HEpub]].
      - by rewrite HP.
      - by rewrite HS orbT.
      - by rewrite HEpub !orbT. } by move: HxB; rewrite /B inE HxT. } have HAC : [disjoint A & C0]. { rewrite /A /C0 !disjointUX.
        by rewrite !bb84_bridge_qmem_disjoint. } have HBC : [disjoint B & C0].
  { apply/disjointP => x HxB; apply/negP => HxC. have HxT : x \in T.
    { move: HxC; rewrite /C0 /bb84_Eve /bb84_eve_reg inE => HxEve. rewrite /T !inE /bb84_E; apply/orP; right; apply/orP; right.
      by apply/orP; left; rewrite HxEve. } by move: HxB; rewrite /B inE HxT. } have eqABC : A :|: B :|: C0 = ([set: L] : {set L}).
  { apply/setP=> x. rewrite /A /B /T /C0 !inE /bb84_E /bb84_Eve /bb84_eve_reg. case: (x == bb84_bridge_label bb84_reg_Ppub); first by [].
    case: (x == bb84_bridge_label bb84_reg_S); first by []. case: (match x with inr (inr (inl _)) => true | _ => false end); first by rewrite orbT. case: (x == bb84_bridge_label bb84_reg_E); by []. } have HA0B0 : [disjoint A0 & B0].
  { apply/disjointP => x HxA; apply/negP => HxB. have HxT : x \in T0.
    { move: HxA; rewrite /A0 /T0 !inE /bb84_E => /orP [HEpub | HP]. - by rewrite HEpub !orbT. - by rewrite HP !orbT. } by move: HxB; rewrite /B0 inE HxT. } have HA0C : [disjoint A0 & C0]. { rewrite /A0 /C0 disjointUX. by rewrite !bb84_bridge_qmem_disjoint. }
have HB0C : [disjoint B0 & C0].
  { apply/disjointP => x HxB; apply/negP => HxC. have HxT : x \in T0.
    { move: HxC; rewrite /C0 /bb84_Eve /bb84_eve_reg inE => HxEve. rewrite /T0 !inE /bb84_E; apply/orP; left. by apply/orP; left; rewrite HxEve. } by move: HxB; rewrite /B0 inE HxT. } have eqA0B0C : A0 :|: B0 :|: C0 = ([set: L] : {set L}).
  { apply/setP=> x. rewrite /A0 /B0 /T0 /C0 !inE /bb84_E /bb84_Eve /bb84_eve_reg. case: (match x with inr (inr (inl _)) => true | _ => false end); first by rewrite !orbT. case: (x == bb84_bridge_label bb84_reg_E); first by []. case: (x == bb84_bridge_label bb84_reg_Ppub); by []. } set eqBC := etrans (esym (setDU3_A HAB HAC)) (f_equal (fun S => S :\: A) eqABC); set yBC := castlf (esym eqBC, esym eqBC) (\Tr_(A) rho). have HyBC : \Tr_(A) rho = castlf (eqBC, eqBC) yBC by rewrite /yBC castlf_esymK.
    set eqB0C := etrans (esym (setDU3_A HA0B0 HA0C)) (f_equal (fun S => S :\: A0) eqA0B0C).
    set yB0C := castlf (esym eqB0C, esym eqB0C) (\Tr_(A0) rho). have HyB0C : \Tr_(A0) rho = castlf (eqB0C, eqB0C) yB0C by rewrite /yB0C castlf_esymK. have Hmarg : ptrace_castl HBC yBC = ptrace_castl HB0C yB0C.
  { rewrite /ptrace_castl /ptrace_cast_gen /yBC /yB0C (ptracelf_castlf_eq (esym eqBC) (f_equal (fun S => S :\: B) (esym eqBC))).
    rewrite (ptracelf_castlf_eq (esym eqB0C) (f_equal (fun S => S :\: B0) (esym eqB0C))).
    have Hcomp_left := congr1 (fun F : 'SO[HL]_(setTfor L, ((setTfor L :\: A) :\: B)) => F rho) (@ptraceso_comp R L HL B A (setTfor L)).
    move: Hcomp_left; rewrite comp_soE castsoE /= castlf_id => Hcomp_left; rewrite Hcomp_left.
    have Hcomp_right := congr1 (fun F : 'SO[HL]_(setTfor L, ((setTfor L :\: A0) :\: B0)) => F rho) (@ptraceso_comp R L HL B0 A0 (setTfor L)). move: Hcomp_right; rewrite comp_soE castsoE /= castlf_id => Hcomp_right; rewrite Hcomp_right.
    have Htrace_set : A :|: B = A0 :|: B0.
    { have HAB_C : [disjoint A :|: B & C0] by rewrite disjointUX HAC HBC. have HA0B0_C : [disjoint A0 :|: B0 & C0] by rewrite disjointUX HA0C HB0C. have Hleft : A :|: B = ([set: L] : {set L}) :\: C0. { by rewrite -(setDU_r HAB_C) eqABC. }
have Hright : A0 :|: B0 = ([set: L] : {set L}) :\: C0. { by rewrite -(setDU_r HA0B0_C) eqA0B0C. } by rewrite Hleft Hright. }
by apply: to_Fnd_inj; rewrite !Fnd_cast; case: _ / Htrace_set. } rewrite /ptrace_cast_gen !replacesoE HyBC.
      rewrite (@ptraceso_appendso_complement R L HL A B C0 HAB HAC HBC eqABC (bb84_leakage_public_register_state s) yBC) HyB0C.
      rewrite (@ptraceso_appendso_complement R L HL A0 B0 C0 HA0B0 HA0C HB0C eqA0B0C payload yB0C) Hmarg.
      have HEpubP : [disjoint bb84_Epub & bb84_Ppub] by exact: bb84_bridge_reg_disjoint.
      have Hreassoc := congr1 (@to_Fnd R L HL _ _) (bb84_leakage_public_register_state_reassoc s). move: Hreassoc; rewrite Fnd_cast !to_Fnd_sdotE /payload; rewrite [X in (_ = (_ \· X)%FND)]dotFT; last exact: HEpubP. move=> Hreassoc; apply: to_Fnd_inj; rewrite !Fnd_cast !to_Fnd_sdotE Hreassoc. by rewrite !Fnd_cast !to_Fnd_sdotE !to_Fnd_tenE /ptrace_castl /ptrace_cast_gen !Fnd_cast; rewrite !dotFA. Qed.

Fact bb84_leakage_public_replaceso_post_hash_pseed (s : @store (bb84_cvar M) V) (rho : 'F[HL]_(setTfor L)) :
  post_hash_state bb84_disSEpub bb84_pa_hash_index (castlf (bb84_public_assoc bb84_S bb84_E bb84_Ppub,
       bb84_public_assoc bb84_S bb84_E bb84_Ppub) (ptrace_cast_gen (bb84_setT_diff_complement (bb84_Ppub :|: (bb84_S :|: bb84_E)))
        (@replaceso R L HL (bb84_Ppub :|: (bb84_S :|: bb84_Epub)) (bb84_leakage_public_register_state s) rho))) =
  \sum_f ((bb84_unif_pseed_mass s f)%:C *: match bb84_paseed_of f with | Some fidx => bb84_pa_public_branch_ptrace s fidx rho | None => 0
    end).
Proof. have bb84_pa_public_replaceso_branch_ptrace : forall (z : 'Idx[HL]_bb84_Zl) (f : 'Idx[HL]_bb84_Fl) (payload : 'F[HL]_(bb84_Epub :|:
  bb84_Ppub)) (rho : 'F[HL]_(setTfor L)), ptrace_cast_gen (bb84_setT_diff_complement (bb84_Zl :|: (bb84_Fl :|: (bb84_E :|: bb84_Ppub)))) (@replaceso R L HL (bb84_Zl :|: (bb84_Fl :|: (bb84_Epub :|: bb84_Ppub))) ([> deltav z ; deltav z <] \⊗ ([> deltav f ; deltav f <] \⊗ payload)) rho) = ([> deltav z ; deltav z <] \⊗ ([> deltav f ; deltav f <] \⊗ ptrace_cast_gen (bb84_setT_diff_complement (bb84_E :|: bb84_Ppub)) (@replaceso R L HL (bb84_Epub :|: bb84_Ppub) payload rho))).
{ clear rho s; move=> z f payload rho. set T := bb84_Zl :|: (bb84_Fl :|: (bb84_E :|: bb84_Ppub)).
  set A := bb84_Zl :|: (bb84_Fl :|: (bb84_Epub :|: bb84_Ppub)); set B := mathcomp.boot.finset.setC T. set C0 := bb84_Eve; set T0 := bb84_E :|: bb84_Ppub. set A0 := bb84_Epub :|: bb84_Ppub; set B0 := mathcomp.boot.finset.setC T0. have HAB : [disjoint A & B].
  { apply/disjointP => x HxA; apply/negP => HxB. have HxT : x \in T.
    { move: HxA; rewrite /A /T !inE => /orP [Hz | /orP [Hf | /orP [HEpub | HP]]].
      - by rewrite Hz.
      - by rewrite Hf orbT.
      - by rewrite HEpub !orbT.
      - by rewrite HP !orbT. } by move: HxB; rewrite /B inE HxT. } have HAC : [disjoint A & C0]. { rewrite /A /C0 !disjointUX.
        by rewrite !bb84_bridge_qmem_disjoint. } have HBC : [disjoint B & C0].
  { apply/disjointP => x HxB; apply/negP => HxC. have HxT : x \in T.
    { move: HxC; rewrite /C0 /bb84_Eve /bb84_eve_reg inE => HxEve. rewrite /T !inE /bb84_E; apply/orP; right; apply/orP; right.
      by apply/orP; left; rewrite HxEve. } by move: HxB; rewrite /B inE HxT. } have eqABC : A :|: B :|: C0 = ([set: L] : {set L}).
  { apply/setP=> x. rewrite /A /B /T /C0 !inE /bb84_E /bb84_Eve /bb84_eve_reg. case: (x == bb84_bridge_label bb84_reg_Zl); first by [].
    case: (x == bb84_bridge_label bb84_reg_Fl); first by []. case: (match x with inr (inr (inl _)) => true | _ => false end); first by rewrite orbT. case: (x == bb84_bridge_label bb84_reg_E); first by []. case: (x == bb84_bridge_label bb84_reg_Ppub); by []. }
have HA0B0 : [disjoint A0 & B0].
  { apply/disjointP => x HxA; apply/negP => HxB. have HxT : x \in T0.
    { move: HxA; rewrite /A0 /T0 !inE /bb84_E => /orP [HEpub | HP]. - by rewrite HEpub !orbT. - by rewrite HP !orbT. } by move: HxB; rewrite /B0 inE HxT. } have HA0C : [disjoint A0 & C0]. { rewrite /A0 /C0 disjointUX. by rewrite !bb84_bridge_qmem_disjoint. }
have HB0C : [disjoint B0 & C0].
  { apply/disjointP => x HxB; apply/negP => HxC. have HxT : x \in T0.
    { move: HxC; rewrite /C0 /bb84_Eve /bb84_eve_reg inE => HxEve. rewrite /T0 !inE /bb84_E; apply/orP; left. by apply/orP; left; rewrite HxEve. } by move: HxB; rewrite /B0 inE HxT. } have eqA0B0C : A0 :|: B0 :|: C0 = ([set: L] : {set L}).
  { apply/setP=> x. rewrite /A0 /B0 /T0 /C0 !inE /bb84_E /bb84_Eve /bb84_eve_reg. case: (match x with inr (inr (inl _)) => true | _ => false end); first by rewrite !orbT. case: (x == bb84_bridge_label bb84_reg_E); first by []. case: (x == bb84_bridge_label bb84_reg_Ppub); by []. } set eqBC := etrans (esym (setDU3_A HAB HAC)) (f_equal (fun S => S :\: A) eqABC); set yBC := castlf (esym eqBC, esym eqBC) (\Tr_(A) rho). have HyBC : \Tr_(A) rho = castlf (eqBC, eqBC) yBC by rewrite /yBC castlf_esymK.
    set eqB0C := etrans (esym (setDU3_A HA0B0 HA0C)) (f_equal (fun S => S :\: A0) eqA0B0C).
    set yB0C := castlf (esym eqB0C, esym eqB0C) (\Tr_(A0) rho). have HyB0C : \Tr_(A0) rho = castlf (eqB0C, eqB0C) yB0C by rewrite /yB0C castlf_esymK. have Hmarg : ptrace_castl HBC yBC = ptrace_castl HB0C yB0C.
  { rewrite /ptrace_castl /ptrace_cast_gen /yBC /yB0C (ptracelf_castlf_eq (esym eqBC) (f_equal (fun S => S :\: B) (esym eqBC))).
    rewrite (ptracelf_castlf_eq (esym eqB0C) (f_equal (fun S => S :\: B0) (esym eqB0C))).
    have Hcomp_left := congr1 (fun F : 'SO[HL]_(setTfor L, ((setTfor L :\: A) :\: B)) => F rho) (@ptraceso_comp R L HL B A (setTfor L)).
    move: Hcomp_left; rewrite comp_soE castsoE /= castlf_id => Hcomp_left; rewrite Hcomp_left.
    have Hcomp_right := congr1 (fun F : 'SO[HL]_(setTfor L, ((setTfor L :\: A0) :\: B0)) => F rho) (@ptraceso_comp R L HL B0 A0 (setTfor L)). move: Hcomp_right; rewrite comp_soE castsoE /= castlf_id => Hcomp_right; rewrite Hcomp_right.
    have Htrace_set : A :|: B = A0 :|: B0.
    { have HAB_C : [disjoint A :|: B & C0] by rewrite disjointUX HAC HBC. have HA0B0_C : [disjoint A0 :|: B0 & C0] by rewrite disjointUX HA0C HB0C. have Hleft : A :|: B = ([set: L] : {set L}) :\: C0. { by rewrite -(setDU_r HAB_C) eqABC. }
have Hright : A0 :|: B0 = ([set: L] : {set L}) :\: C0. { by rewrite -(setDU_r HA0B0_C) eqA0B0C. } by rewrite Hleft Hright. }
by apply: to_Fnd_inj; rewrite !Fnd_cast; case: _ / Htrace_set. } rewrite /ptrace_cast_gen !replacesoE HyBC.
      rewrite (@ptraceso_appendso_complement R L HL A B C0 HAB HAC HBC eqABC ([> deltav z ; deltav z <] \⊗ ([> deltav f ; deltav f <] \⊗ payload)) yBC). rewrite HyB0C (@ptraceso_appendso_complement R L HL A0 B0 C0 HA0B0 HA0C HB0C eqA0B0C payload yB0C).
      rewrite Hmarg; apply: to_Fnd_inj. rewrite !Fnd_cast !to_Fnd_sdotE !to_Fnd_tenE; rewrite dotFT; last exact: HAC.
      rewrite [X in (_ = (_ \⊗ (_ \⊗ X))%FND)]Fnd_cast. rewrite [X in (_ = (_ \⊗ (_ \⊗ X))%FND)]Fnd_cast.
      rewrite [X in (_ = (_ \⊗ (_ \⊗ X))%FND)]to_Fnd_sdotE. rewrite [X in (_ = (_ \⊗ (_ \⊗ X))%FND)]dotFT; last exact: HA0C.
      by rewrite !tenFA. } rewrite bb84_leakage_public_replaceso_branch_ptrace /bb84_alice_key_register_state /bb84_S_projector.
      rewrite (bb84_post_hash_projector_public_pseed_val _ _ s); apply: eq_bigr => fval _. by case: (bb84_paseed_of fval) => [fidx|] //=; rewrite /bb84_pa_public_branch_ptrace -bb84_pa_public_replaceso_branch_ptrace. Qed.

Fact bb84_leakage_public_replaceso_post_hash_pseed_weighted (s : @store (bb84_cvar M) V) (rho : 'F[HL]_(setTfor L)) (base : R) :
  \sum_f ((base * bb84_unif_pseed_mass s f)%:C *: post_hash_state bb84_disSEpub bb84_pa_hash_index (castlf
        (bb84_public_assoc bb84_S bb84_E bb84_Ppub, bb84_public_assoc bb84_S bb84_E bb84_Ppub) (ptrace_cast_gen
          (bb84_setT_diff_complement (bb84_Ppub :|: (bb84_S :|: bb84_E))) (@replaceso R L HL (bb84_Ppub :|: (bb84_S :|: bb84_Epub))
            (bb84_leakage_public_register_state s) rho)))) = \sum_f ((base * bb84_unif_pseed_mass s f)%:C *: match bb84_paseed_of f with
    | Some fidx => bb84_pa_public_branch_ptrace s fidx rho | None => 0 end).
Proof. rewrite bb84_leakage_public_replaceso_post_hash_pseed -scaler_suml. have -> : \sum_f (base * bb84_unif_pseed_mass s f)%:C = base%:C.
  { rewrite -rmorph_sum /= -mulr_sumr. by rewrite bb84_unif_pseed_mass_sum1 ?mulr1 ?cd_paseed_pos. } by rewrite scaler_sumr; apply: eq_bigr => f _; rewrite scalerA -rmorphM. Qed.

Fact bb84_leakage_public_replaceso_post_hash_pseed_weighted_linear (s : @store (bb84_cvar M) V) (rho : 'F[HL]_(setTfor L)) (base : R) :
  \sum_f post_hash_state bb84_disSEpub bb84_pa_hash_index (castlf (bb84_public_assoc bb84_S bb84_E bb84_Ppub,
         bb84_public_assoc bb84_S bb84_E bb84_Ppub) (ptrace_cast_gen (bb84_setT_diff_complement (bb84_Ppub :|: (bb84_S :|: bb84_E)))
          ((base * bb84_unif_pseed_mass s f)%:C *: @replaceso R L HL (bb84_Ppub :|: (bb84_S :|: bb84_Epub))
              (bb84_leakage_public_register_state s) rho))) = \sum_f ((base * bb84_unif_pseed_mass s f)%:C *: match bb84_paseed_of f with
    | Some fidx => bb84_pa_public_branch_ptrace s fidx rho | None => 0 end).
Proof. rewrite -bb84_leakage_public_replaceso_post_hash_pseed_weighted; apply: eq_bigr => f _.
  move: (bb84_post_hash_public_ptrace_linear (base * bb84_unif_pseed_mass s f)%:C (@replaceso R L HL (bb84_Ppub :|: (bb84_S :|: bb84_Epub)) (bb84_leakage_public_register_state s) rho) 0); rewrite addr0. have Hzero : post_hash_state bb84_disSEpub bb84_pa_hash_index (castlf (bb84_public_assoc bb84_S bb84_E bb84_Ppub, bb84_public_assoc bb84_S bb84_E bb84_Ppub) (ptrace_cast_gen (bb84_setT_diff_complement (bb84_Ppub :|: (bb84_S :|: bb84_E))) 0)) = 0.
  { rewrite ptrace_cast_gen0 linear0 /post_hash_state. rewrite [\sum_(_ : 'Idx[HL]_bb84_Fl) _]big1 ?scale0r ?linear0 //. move=> fidx _; rewrite [\sum_(_ : 'Idx[HL]_bb84_Zl) _]big1 // => z _. rewrite [\sum_(_ : 'Idx[HL]_bb84_S | _) _]big1 ?sdotf0 // => x _.
    by rewrite /cq_block comp_lfun0r comp_lfun0l /ptrace_castl /ptrace_cast_gen !linear0. } by rewrite Hzero addr0. Qed.

Fact bb84_pa_public_readout_replaceso_state_trace_eq (EA : @adversary R L HL V bb84_Eve) (rho : 'F[HL]_(setTfor L))
    (s s' : @store (bb84_cvar M) V) (h h' : @run_history V M) (fidx : 'I_(cd_paseed_count dev)) :
  s = s' -> h.1 = h'.1 -> bb84_pa_public_branch_ptrace s fidx (bb84_history_readout_state EA h rho) = bb84_pa_public_branch_ptrace s' fidx
    (bb84_history_readout_state EA h' rho).
Proof. move=> -> Htrace. have Hread := @bb84_history_readout_state_trace_eq R P q dev LE HE bb84_register_index bb84_register_space EA h h'
  rho Htrace. by rewrite /bb84_pa_public_branch_ptrace Hread. Qed.

Fact bb84_pa_public_readout_branch_sum_post_hash_eq (EA : @adversary R L HL V bb84_Eve) (rho : 'F[HL]_(setTfor L))
    (s s' : @store (bb84_cvar M) V) (h h' : @run_history V M) (base : R) :
  s = s' -> h.1 = h'.1 -> \sum_f ((base * bb84_unif_pseed_mass s f)%:C *: match bb84_paseed_of f with | Some fidx =>
        bb84_pa_public_branch_ptrace s fidx (bb84_history_readout_state EA h rho) | None => 0 end) = \sum_f
    post_hash_state bb84_disSEpub bb84_pa_hash_index (castlf (bb84_public_assoc bb84_S bb84_E bb84_Ppub,
         bb84_public_assoc bb84_S bb84_E bb84_Ppub) (ptrace_cast_gen (bb84_setT_diff_complement (bb84_Ppub :|: (bb84_S :|: bb84_E)))
          ((base * bb84_unif_pseed_mass s' f)%:C *: @replaceso R L HL (bb84_Ppub :|: (bb84_S :|: bb84_Epub))
              (bb84_leakage_public_register_state s') (bb84_history_readout_state EA h' rho)))).
Proof. move=> -> Htrace. transitivity (\sum_f ((base * bb84_unif_pseed_mass s' f)%:C *: match bb84_paseed_of f with | Some fidx =>
  bb84_pa_public_branch_ptrace s' fidx (bb84_history_readout_state EA h' rho) | None => 0 end)).
  - apply: eq_bigr => f _. case Hf: (bb84_paseed_of f) => [fidx|].
    + exact: (f_equal (fun x => (base * bb84_unif_pseed_mass s' f)%:C *: x) (@bb84_pa_public_readout_replaceso_state_trace_eq EA rho s' s' h h' fidx erefl Htrace)).
    + by [].
  - by rewrite -bb84_leakage_public_replaceso_post_hash_pseed_weighted_linear. Qed.

Fact bb84_pa_public_readout_branch_sum_normalize (EA : @adversary R L HL V bb84_Eve) (rho : 'F[HL]_(setTfor L))
    (coef : V -> R) (branch_store : V -> @store (bb84_cvar M) V) (branch_history : V -> @run_history V M)
    (base : R) (s0 : @store (bb84_cvar M) V) (h0 : @run_history V M) :
  (forall f, coef f = base * bb84_unif_pseed_mass s0 f) -> (forall f, branch_store f = s0) ->
  (forall f, (branch_history f).1 = h0.1) -> \sum_f ((coef f)%:C *: match bb84_paseed_of f with | Some fidx =>
        bb84_pa_public_branch_ptrace (branch_store f) fidx (bb84_history_readout_state EA (branch_history f) rho) | None => 0 end) =
  \sum_f ((base * bb84_unif_pseed_mass s0 f)%:C *: match bb84_paseed_of f with | Some fidx => bb84_pa_public_branch_ptrace s0 fidx
          (bb84_history_readout_state EA h0 rho) | None => 0 end).
Proof. move=> Hcoef Hstore Htrace; apply: eq_bigr => f _; rewrite Hcoef. case Hf: (bb84_paseed_of f) => [fidx|].
  - exact: (f_equal (fun x => (base * bb84_unif_pseed_mass s0 f)%:C *: x) (@bb84_pa_public_readout_replaceso_state_trace_eq EA rho (branch_store f) s0 (branch_history f) h0 fidx (Hstore f) (Htrace f))).
  - by []. Qed.

Fact bb84_pa_public_readout_seed_sum_endpoint (EA : @adversary R L HL V bb84_Eve) (rho : 'F[HL]_(setTfor L))
    (coef : V -> R) (branch_store : V -> @store (bb84_cvar M) V) (branch_history : V -> @run_history V M)
    (base : R) (s0 : @store (bb84_cvar M) V) (h0 : @run_history V M) :
  (forall f, coef f = base * bb84_unif_pseed_mass s0 f) -> (forall f, branch_store f = s0) ->
  (forall f, (branch_history f).1 = h0.1) -> \sum_f ((coef f)%:C *: match bb84_paseed_of f with | Some fidx =>
        bb84_pa_public_branch_ptrace (branch_store f) fidx (bb84_history_readout_state EA (branch_history f) rho) | None => 0 end) = \sum_f
    post_hash_state bb84_disSEpub bb84_pa_hash_index (castlf (bb84_public_assoc bb84_S bb84_E bb84_Ppub,
         bb84_public_assoc bb84_S bb84_E bb84_Ppub) (ptrace_cast_gen (bb84_setT_diff_complement (bb84_Ppub :|: (bb84_S :|: bb84_E)))
          ((coef f)%:C *: @replaceso R L HL (bb84_Ppub :|: (bb84_S :|: bb84_Epub)) (bb84_leakage_public_register_state (branch_store f))
              (bb84_history_readout_state EA (branch_history f) rho)))).
Proof. move=> Hcoef Hstore Htrace. transitivity (\sum_f ((base * bb84_unif_pseed_mass s0 f)%:C *: match bb84_paseed_of f with | Some fidx =>
  bb84_pa_public_branch_ptrace s0 fidx (bb84_history_readout_state EA h0 rho) | None => 0 end)).
  - exact: (@bb84_pa_public_readout_branch_sum_normalize EA rho coef branch_store branch_history base s0 h0 Hcoef Hstore Htrace).
    transitivity (\sum_f post_hash_state bb84_disSEpub bb84_pa_hash_index (castlf (bb84_public_assoc bb84_S bb84_E bb84_Ppub, bb84_public_assoc bb84_S bb84_E bb84_Ppub) (ptrace_cast_gen (bb84_setT_diff_complement (bb84_Ppub :|: (bb84_S :|: bb84_E))) ((base * bb84_unif_pseed_mass s0 f)%:C *: @replaceso R L HL (bb84_Ppub :|: (bb84_S :|: bb84_Epub)) (bb84_leakage_public_register_state s0) (bb84_history_readout_state EA h0 rho))))).
  - exact: (@bb84_pa_public_readout_branch_sum_post_hash_eq EA rho s0 s0 h0 h0 base erefl erefl).
  - apply/esym. apply: eq_bigr => f _. rewrite Hcoef. have Hread := @bb84_history_readout_state_trace_eq R P q dev LE HE bb84_register_index bb84_register_space EA (branch_history f) h0 rho (Htrace f). by rewrite (Hstore f) Hread. Qed.

Fact bb84_prefix_pa_public_readout_seed_sum_endpoint (EA : @adversary R L HL V bb84_Eve) (xi : @cq_state R L HL (bb84_cvar M) V)
    (s : @store (bb84_cvar M) V) (p : @run_prefix V M) : \sum_f ((bb84_prefix_pass_weight p f s)%:C *: match bb84_paseed_of f with
    | Some fidx => bb84_pa_public_branch_ptrace (bb84_prefix_errcorr_store p f s) fidx (bb84_history_readout_state EA
            (prefix_history p f) (xi s)) | None => 0 end) = \sum_f post_hash_state bb84_disSEpub bb84_pa_hash_index (castlf
        (bb84_public_assoc bb84_S bb84_E bb84_Ppub, bb84_public_assoc bb84_S bb84_E bb84_Ppub) (ptrace_cast_gen
          (bb84_setT_diff_complement (bb84_Ppub :|: (bb84_S :|: bb84_E))) ((bb84_prefix_pass_weight p f s)%:C *:
            @replaceso R L HL (bb84_Ppub :|: (bb84_S :|: bb84_Epub)) (bb84_leakage_public_register_state (bb84_prefix_errcorr_store p f s))
              (bb84_history_readout_state EA (prefix_history p f) (xi s))))).
Proof. case: p => t [K g]. eapply (@bb84_pa_public_readout_seed_sum_endpoint EA (xi s) (fun f => bb84_prefix_pass_weight (t, (K, g)) f s)
  (fun f => bb84_prefix_errcorr_store (t, (K, g)) f s) (prefix_history (t, (K, g))) (bb84_prefix_pass_base (t, (K, g)) s) (bb84_prefix_errcorr_store (t, (K, g)) bb84_bot_val s) (prefix_history (t, (K, g)) bb84_bot_val)).
  - move=> f. exact: (history_post_coeff_f_irrel t K g f bb84_bot_val s (@bb84_abort_neq_f M) (@bb84_abort_neq_S M) (@bb84_abort_neq_Sh M) (@bb84_abort_neq_P M)).
  - by move=> f; exact: (history_post_store_f_irrel t K g f bb84_bot_val s).
  - by move=> f. Qed.

Definition bb84_pass_pa_public_readout_state (EA : @adversary R L HL V bb84_Eve) (xi : @cq_state R L HL (bb84_cvar M) V) :=
  @bb84_pass_history_public_readout_state R P q dev LE HE bb84_register_index bb84_register_space
    (bb84_Zl :|: (bb84_Fl :|: (bb84_Epub :|: bb84_Ppub))) bb84_pa_public_register_state EA xi.
Fact bb84_pa_public_readout_trace_leakage_public (EA : @adversary R L HL V bb84_Eve) (xi : @cq_state R L HL (bb84_cvar M) V) :
  \Tr (bb84_pass_pa_public_readout_state EA xi) = \Tr (bb84_pass_leakage_public_readout_state EA xi).
Proof. rewrite /bb84_pass_pa_public_readout_state /bb84_pass_leakage_public_readout_state /bb84_pass_history_public_readout_state.
  rewrite [in LHS]linear_sum /=. rewrite [in RHS]linear_sum /=. apply: eq_bigr => s _. rewrite [in LHS]linear_sum /=. rewrite [in RHS]linear_sum /=. apply: eq_bigr => h _. rewrite [in LHS]linearZ /=. rewrite [in RHS]linearZ /=.
  by rewrite !replaceso_trlf_den1 ?bb84_pa_public_register_state_den1lf ?bb84_leakage_public_register_state_den1lf. Qed.

Fact bb84_pass_history_pa_public_readout_hash_readoutE (EA : @adversary R L HL V bb84_Eve) (xi : @cq_state R L HL (bb84_cvar M) V) :
  bb84_pass_pa_public_readout_state EA xi = \sum_s \sum_(t : @round_trace V M) \sum_K \sum_g \sum_f
    let h : @run_history V M := (t, ((K, g), f)) in let fs := dev_final_args (@final_store) h s in
    let s0 := @start_store (bb84_cvar M) V M (@BVX M) (@BVZ M) (@BVabort M) (@BVP M) bb84_empty_transcript_val
      bb84_bool_val bb84_set_val s in let s1 := @rounds_store (bb84_cvar M) V M (@BVa M) (@BVy M)
      (@BVb M) (@BVy' M) (@BVd M) (@BVX M) (@BVZ M) (bb84_basis_value dev BasisX) (bb84_basis_value dev BasisZ)
      (bb84_outcome_val None) bb84_bool_val bb84_set_val h s0 in let s2 := @announce_store (bb84_cvar M) V M (@BVa M) (@BVb M)
      (@BVd M) (@BVP M) bb84_tr_app_rounds s1 in let s3 := @paramest_store (bb84_cvar M) V M (@BVy M) (@BVy' M) (@BVZ M) (@BVK M) (@BVXA M)
      (@BVXB M) (@BVZA M) (@BVZB M) (@BVlam M) (@BVP M) bb84_set_of bb84_error_val bb84_tr_app_pe bb84_bits_on_val
      bb84_partial_bits_on_val bb84_err_count_val h s2 in let s4 := @errcorr_store (bb84_cvar M) V (cd_ir_bits dev) M
      (@BVXA M) (@BVXB M) (@BVpec M) (@BVXhat M) (@BVg M) (@BVtA M) (@BVtB M) (@BVP M) bb84_tr_app_ec
      (bb84_ir_pub_val (@cd_ir_pub R P q dev)) (bb84_ir_dec_val (@cd_ir_dec R P q dev)) (bb84_verify_hash_val (@cd_vh R P q dev)) h s3 in
    let post := @key_sample_mass R (bb84_cvar M) V (bb84_n P) M (@BVX M) bb84_bot_val bb84_set_of bb84_unif_nsubset_mass
        s2 (@hist_K V M h) * (bb84_unif_vseed_mass (@errcorr_seed_store (bb84_cvar M) V (cd_ir_bits dev)
          (@BVXA M) (@BVXB M) (@BVpec M) (@BVXhat M) (bb84_ir_pub_val (@cd_ir_pub R P q dev))
          (bb84_ir_dec_val (@cd_ir_dec R P q dev)) s3) (@hist_g V M h) * bb84_unif_pseed_mass s4 (@hist_f V M h)) in
    let xidx := bb84_raw_key_index (s4 (@BVXA M)) in match bb84_paseed_of (@hist_f V M h) with | Some f =>
      let zidx := bb84_pa_hash_index (bb84_Fl_index f) (bb84_S_index xidx) in ((((fs (@BVabort M) == bb84_bool_val false)%:R) * post)%:C *:
          @replaceso R L HL (bb84_Zl :|: (bb84_Fl :|: (bb84_Epub :|: bb84_Ppub))) ([> deltav zidx ; deltav zidx <] \⊗
              ([> deltav (bb84_Fl_index f) ; deltav (bb84_Fl_index f) <] \⊗ (bb84_public_register_state s4 \⊗
                  bb84_leakage_register_state s4))) (bb84_history_readout_state EA h (xi s))) | None => 0 end.
Proof. rewrite /bb84_pass_pa_public_readout_state /bb84_pass_history_public_readout_state; apply: eq_bigr => s _.
  rewrite -run_history_sum_split_history; apply: eq_bigr => t _. apply: eq_bigr => K _; apply: eq_bigr => g _; apply: eq_bigr => fseed _.
  set h : @run_history V M := (t, ((K, g), fseed)). set fs := dev_final_args (@final_store) h s.
  set s0 := @start_store (bb84_cvar M) V M (@BVX M) (@BVZ M) (@BVabort M) (@BVP M) bb84_empty_transcript_val bb84_bool_val bb84_set_val s.
  set s1 := @rounds_store (bb84_cvar M) V M (@BVa M) (@BVy M) (@BVb M) (@BVy' M) (@BVd M) (@BVX M) (@BVZ M) (bb84_basis_value dev BasisX) (bb84_basis_value dev BasisZ) (bb84_outcome_val None) bb84_bool_val bb84_set_val h s0. set s2 := @announce_store (bb84_cvar M) V M (@BVa M) (@BVb M) (@BVd M) (@BVP M) bb84_tr_app_rounds s1. set s3 := @paramest_store (bb84_cvar M) V M (@BVy M) (@BVy' M) (@BVZ M) (@BVK M) (@BVXA M) (@BVXB M) (@BVZA M) (@BVZB M) (@BVlam M) (@BVP M) bb84_set_of bb84_error_val bb84_tr_app_pe bb84_bits_on_val bb84_partial_bits_on_val bb84_err_count_val h s2. set s4 := @errcorr_store (bb84_cvar M) V (cd_ir_bits dev) M (@BVXA M) (@BVXB M) (@BVpec M) (@BVXhat M) (@BVg M) (@BVtA M) (@BVtB M) (@BVP M) bb84_tr_app_ec (bb84_ir_pub_val (@cd_ir_pub R P q dev)) (bb84_ir_dec_val (@cd_ir_dec R P q dev)) (bb84_verify_hash_val (@cd_vh R P q dev)) h s3. set old_post := history_post_weight (R:=R) (Cv:=bb84_cvar M) (V:=V) (M:=M) (bb84_n P) (bb84_k P) (cd_ir_bits dev) (bb84_Qtol P) (@BVa M) (@BVy M) (@BVb M) (@BVy' M) (@BVd M) (@BVX M) (@BVZ M) (@BVK M) (@BVXA M) (@BVXB M) (@BVZA M) (@BVZB M) (@BVlam M) (@BVpec M) (@BVXhat M) (@BVg M) (@BVtA M) (@BVtB M) (@BVabort M) (@BVP M) (bb84_basis_value dev BasisX) (bb84_basis_value dev BasisZ) (bb84_outcome_val None) bb84_bot_val bb84_empty_transcript_val bb84_bool_val bb84_set_val bb84_set_of bb84_error_val bb84_tr_app_rounds bb84_tr_app_pe bb84_tr_app_ec bb84_bits_on_val bb84_partial_bits_on_val bb84_err_count_val bb84_error_of bb84_unif_nsubset_mass (bb84_ir_pub_val (@cd_ir_pub R P q dev)) (bb84_ir_dec_val (@cd_ir_dec R P q dev)) bb84_unif_vseed_mass (bb84_verify_hash_val (@cd_vh R P q dev)) bb84_unif_pseed_mass h s. set post := @key_sample_mass R (bb84_cvar M) V (bb84_n P) M (@BVX M) bb84_bot_val bb84_set_of bb84_unif_nsubset_mass s2 (@hist_K V M h) * (bb84_unif_vseed_mass (@errcorr_seed_store (bb84_cvar M) V (cd_ir_bits dev) (@BVXA M) (@BVXB M) (@BVpec M) (@BVXhat M) (bb84_ir_pub_val (@cd_ir_pub R P q dev)) (bb84_ir_dec_val (@cd_ir_dec R P q dev)) s3) (@hist_g V M h) * bb84_unif_pseed_mass s4 (@hist_f V M h)). have HAB_S : @BVabort M != @BVS M.
  { rewrite /BVabort /BVS /=; have Hord : (inord 17 : 'I_18) != inord 15 by rewrite -val_eqE /= !inordK. by rewrite Hord. }
have HAB_Sh : @BVabort M != @BVSh M.
  { rewrite /BVabort /BVSh /=; have Hord : (inord 17 : 'I_18) != inord 16 by rewrite -val_eqE /= !inordK. by rewrite Hord. }
have Hold_post_pass : fs (@BVabort M) == bb84_bool_val false -> old_post = post.
  { move=> Hpass; rewrite /old_post /post. rewrite (dev_weight_args (@history_post_weight_final_pass) h s bb84_bool_val_neq HAB_S HAB_Sh Hpass). by rewrite -/s0 -/s1 -/s2 -/s3 -/s4. }
set coef := (fs (@BVabort M) == bb84_bool_val false)%:R * post; case Hcoef: (coef == 0).
  - move/eqP: Hcoef => Hcoef0. have Hold_coef0 : (fs (@BVabort M) == bb84_bool_val false)%:R * old_post = 0.
    { case Hpass: (fs (@BVabort M) == bb84_bool_val false).
      - have Hpost0 : post = 0 by move: Hcoef0; rewrite /coef Hpass mul1r. by rewrite (Hold_post_pass Hpass) Hpost0 mulr0.
      - by rewrite mul0r. } case: (bb84_paseed_of (@hist_f V M h)) => [f|].
    + by rewrite -/fs -/old_post Hold_coef0 -/coef Hcoef0 !scale0r.
    + by rewrite -/fs -/old_post Hold_coef0 scale0r.
  - have Hcoef_neq : (fs (@BVabort M) == bb84_bool_val false)%:R * post != 0 by rewrite -/coef Hcoef.
    have Hpass : fs (@BVabort M) == bb84_bool_val false.
    { move: Hcoef_neq; rewrite /coef. case: (fs (@BVabort M) == bb84_bool_val false) => //. by rewrite mul0r eqxx. }
have Hold_post := Hold_post_pass Hpass. have Hold_coef_neq : (fs (@BVabort M) == bb84_bool_val false)%:R * old_post != 0 by rewrite Hold_post. have [Hcard _] := bb84_pass_history_key_sample_support (h := h) Hold_coef_neq. have HfsXA_s4 : fs (@BVXA M) = s4 (@BVXA M).
    { have HfsXA : fs (@BVXA M) = s3 (@BVXA M) by rewrite /fs /s3; apply: final_store_XA; cvne.
      have Hs4XA : s4 (@BVXA M) = s3 (@BVXA M) by rewrite /s4; apply: errcorr_store_XA; cvne. exact: (etrans HfsXA (esym Hs4XA)). }
have Hraw_s4 : @bb84_raw_key_of M (bb84_n P) (bb84_l P) (cd_ir_bits dev) (cd_vseed_count dev) (cd_tag_count dev) (cd_paseed_count dev) (s4 (@BVXA M)) = Some (bitstring_to_ord (fun j => match bb84_selected_index (bb84_set_of (@hist_K V M h)) j with | Some i => if bb84_read_bit (dev_sann h s (@BVy M i)) is Some b then b else false | None => false end)).
    { move: (bb84_final_store_raw_key_of (h := h) s Hcard); by rewrite HfsXA_s4. } have Hkey_ord : bb84_final_key_index (fs (@BVS M)) = match bb84_paseed_of (@hist_f V M h) with | Some f => @cd_pa R P q dev f (bb84_raw_key_index (s4 (@BVXA M))) | None => bb84_final_key_default end.
    { rewrite /bb84_final_key_index (bb84_final_store_Sv_hash_value (h := h) (s := s) Hpass). rewrite /bb84_privacy_hash_val HfsXA_s4; case: (bb84_paseed_of (@hist_f V M h)) => [f|].
      - by rewrite Hraw_s4 /bb84_raw_key_index Hraw_s4.
      - by []. } have Hkey : bb84_Zl_projector (bb84_final_key_index (fs (@BVS M))) = match bb84_paseed_of (@hist_f V M h) with | Some f => let zidx := bb84_pa_hash_index (bb84_Fl_index f) (bb84_S_index (bb84_raw_key_index (s4 (@BVXA M)))) in [> deltav zidx ; deltav zidx <] | None => bb84_Zl_projector bb84_final_key_default end.
    { rewrite Hkey_ord. case: (bb84_paseed_of (@hist_f V M h)) => [f|] //. rewrite /bb84_Zl_projector /bb84_Zl_index /bb84_pa_hash_index /bb84_pa_output_idx /bb84_pa_seed_ord /bb84_pa_input_ord /bb84_Fl_index /bb84_S_index. congr ([> deltav _; deltav _ <]); apply: i2n_inj; by rewrite !n2iK !cast_ordK. } have Hseed : bb84_Fl_projector (bb84_paseed_index (fs (@BVf M))) = match bb84_paseed_of (@hist_f V M h) with | Some f => [> deltav (bb84_Fl_index f) ; deltav (bb84_Fl_index f) <] | None => bb84_Fl_projector bb84_paseed_default end.
    { rewrite (bb84_final_store_pa_seed_index (h := h) (s := s) Hpass). rewrite /bb84_Fl_projector /bb84_paseed_index.
      by case: (bb84_paseed_of (@hist_f V M h)). } have Hpublic_s4 : bb84_public_register_state fs = bb84_public_register_state s4.
    { rewrite (@bb84_final_store_public_register_state h s Hpass). by rewrite -/s0 -/s1 -/s2 -/s3 -/s4. }
have Hleak_s4 : bb84_leakage_register_state fs = bb84_leakage_register_state s4.
    { have Hpe := final_store_pass_pe_ok (h := h) (s := s) bb84_bool_val_neq HAB_S HAB_Sh Hpass; rewrite -/s3 in Hpe.
      have Hverify : ~~ (s4 (@BVtA M) != s4 (@BVtB M)).
      { move: Hpass; rewrite /fs /final_store -/s0 -/s1 -/s2 -/s3 (negbTE Hpe) -/s4. case Hbad: (s4 (@BVtA M) != s4 (@BVtB M)); last by [].
        by rewrite abort_store_not_pass. } rewrite /fs /final_store -/s0 -/s1 -/s2 -/s3 (negbTE Hpe) -/s4 (negbTE Hverify).
        exact: bb84_leakage_register_state_privamp_store. } rewrite /bb84_pa_public_register_state Hkey Hseed Hpublic_s4 Hleak_s4; case Hf: (bb84_paseed_of (@hist_f V M h)) => [f|].
    - by rewrite /stat.bb84_final_store /stat.bb84_history_post_weight -/fs -/old_post Hold_post -/post -/coef -/s0 -/s1 -/s2.
      have Hpost0 : post = 0.
    { rewrite /post /bb84_unif_pseed_mass. rewrite big1 ?mulr0 // => f0 _. case: ifP => [/eqP Hsame | _]; last by [].
      have Hnone : Some f0 = None by move: Hf; rewrite Hsame bb84_paseed_of_val. by discriminate. }
by rewrite /stat.bb84_final_store /stat.bb84_history_post_weight -/fs -/old_post Hold_post Hpost0 mulr0 scale0r. Qed.

Fact bb84_pa_public_readout_post_hashE (EA : @adversary R L HL V bb84_Eve) (xi : @cq_state R L HL (bb84_cvar M) V) :
  let eq_pub_assoc := bb84_public_assoc bb84_S bb84_E bb84_Ppub in ptrace_cast_gen (bb84_setT_diff_complement
      (bb84_Zl :|: (bb84_Fl :|: (bb84_E :|: bb84_Ppub)))) (bb84_pass_pa_public_readout_state EA xi) =
  post_hash_state bb84_disSEpub bb84_pa_hash_index (castlf (eq_pub_assoc, eq_pub_assoc) (ptrace_cast_gen
        (bb84_setT_diff_complement (bb84_Ppub :|: (bb84_S :|: bb84_E))) (bb84_pass_leakage_public_readout_state EA xi))).
Proof. have bb84_pass_history_pa_public_readout_hash_ptraceE : forall (EA : @adversary R L HL V bb84_Eve) (xi : @cq_state R L HL (bb84_cvar
  M) V), ptrace_cast_gen (bb84_setT_diff_complement (bb84_Zl :|: (bb84_Fl :|: (bb84_E :|: bb84_Ppub)))) (bb84_pass_pa_public_readout_state EA xi) = \sum_s \sum_(t : @round_trace V M) \sum_K \sum_g \sum_f let h : @run_history V M := (t, ((K, g), f)) in let s4 := bb84_history_errcorr_store h s in let pass := bb84_history_pass_weight h s in ((pass)%:C *: match bb84_paseed_of (@hist_f V M h) with | Some fidx => bb84_pa_public_branch_ptrace s4 fidx (bb84_history_readout_state EA h (xi s)) | None => 0 end).
{ clear xi EA; move=> EA xi. rewrite bb84_pass_history_pa_public_readout_hash_readoutE ptrace_cast_gen_sum. apply: eq_bigr => s _.
  rewrite ptrace_cast_gen_sum; apply: eq_bigr => t _. rewrite ptrace_cast_gen_sum; apply: eq_bigr => K _. rewrite ptrace_cast_gen_sum; apply: eq_bigr => g _. rewrite ptrace_cast_gen_sum; apply: eq_bigr => f _. rewrite /bb84_history_pass_weight /bb84_history_errcorr_store /history_pass_weight /history_errcorr_store /history_privamp_weight /history_paramest_store /history_announce_store.
  exact: bb84_pa_public_pseed_branch_ptrace. } have bb84_pass_history_leakage_public_readout_post_hashE : forall (EA : @adversary R L HL V bb84_Eve) (xi : @cq_state R L HL (bb84_cvar M) V), let eq_pub_assoc := bb84_public_assoc bb84_S bb84_E bb84_Ppub in post_hash_state bb84_disSEpub bb84_pa_hash_index (castlf (eq_pub_assoc, eq_pub_assoc) (ptrace_cast_gen (bb84_setT_diff_complement (bb84_Ppub :|: (bb84_S :|: bb84_E))) (bb84_pass_leakage_public_readout_state EA xi))) = \sum_s \sum_(t : @round_trace V M) \sum_K \sum_g \sum_f let h : @run_history V M := (t, ((K, g), f)) in let s4 := bb84_history_errcorr_store h s in let pass := bb84_history_pass_weight h s in post_hash_state bb84_disSEpub bb84_pa_hash_index (castlf (eq_pub_assoc, eq_pub_assoc) (ptrace_cast_gen (bb84_setT_diff_complement (bb84_Ppub :|: (bb84_S :|: bb84_E))) ((pass)%:C *: @replaceso R L HL (bb84_Ppub :|: (bb84_S :|: bb84_Epub)) (bb84_leakage_register_state s4 \⊗ (bb84_alice_key_register_state s4 \⊗ bb84_public_register_state s4)) (bb84_history_readout_state EA h (xi s))))).
{ clear xi EA; move=> EA xi. pose Fraw := fun rho : 'F[HL]_(setTfor L) => post_hash_state bb84_disSEpub bb84_pa_hash_index (castlf (bb84_public_assoc bb84_S bb84_E bb84_Ppub, bb84_public_assoc bb84_S bb84_E bb84_Ppub) (ptrace_cast_gen (bb84_setT_diff_complement (bb84_Ppub :|: (bb84_S :|: bb84_E))) rho)). have Fraw_linear : linear Fraw by exact: bb84_post_hash_public_ptrace_linear.
  pose F : {linear 'F[HL]_(setTfor L) -> 'F[HL]_(bb84_Zl :|: (bb84_Fl :|: (bb84_E :|: bb84_Ppub)))} := HB.pack Fraw (GRing.isLinear.Build C _ _ *:%R _ Fraw_linear). have F_eq rho : F rho = Fraw rho by [].
      transitivity (F (bb84_pass_leakage_public_readout_state EA xi)).
  - by rewrite F_eq. rewrite bb84_pass_history_leakage_public_readout_source_readoutE (@linear_sum _ _ _ _ F); apply: eq_bigr => s _.
    rewrite (@linear_sum _ _ _ _ F); apply: eq_bigr => t _. rewrite (@linear_sum _ _ _ _ F); apply: eq_bigr => K _.
    rewrite (@linear_sum _ _ _ _ F); apply: eq_bigr => g _. rewrite (@linear_sum _ _ _ _ F). by apply: eq_bigr => f _; rewrite F_eq. }
symmetry. rewrite bb84_pass_history_leakage_public_readout_post_hashE; symmetry.
    rewrite bb84_pass_history_pa_public_readout_hash_ptraceE; apply: eq_bigr => s _. pose left := fun (p : @run_prefix V M) (f : V) => ((bb84_prefix_pass_weight p f s)%:C *: match bb84_paseed_of f with | Some fidx => bb84_pa_public_branch_ptrace (bb84_prefix_errcorr_store p f s) fidx (bb84_history_readout_state EA (prefix_history p f) (xi s)) | None => 0 end).
    pose right := fun (p : @run_prefix V M) (f : V) => post_hash_state bb84_disSEpub bb84_pa_hash_index (castlf (bb84_public_assoc bb84_S bb84_E bb84_Ppub, bb84_public_assoc bb84_S bb84_E bb84_Ppub) (ptrace_cast_gen (bb84_setT_diff_complement (bb84_Ppub :|: (bb84_S :|: bb84_E))) ((bb84_prefix_pass_weight p f s)%:C *: @replaceso R L HL (bb84_Ppub :|: (bb84_S :|: bb84_Epub)) (bb84_leakage_public_register_state (bb84_prefix_errcorr_store p f s)) (bb84_history_readout_state EA (prefix_history p f) (xi s))))).
    change (\sum_(t : @round_trace V M) \sum_K \sum_g \sum_f left (t, (K, g)) f = \sum_(t : @round_trace V M) \sum_K \sum_g \sum_f right (t, (K, g)) f). rewrite (run_prefix_sum_split left) (run_prefix_sum_split right); apply: eq_bigr => p _.
    change (\sum_f ((bb84_prefix_pass_weight p f s)%:C *: match bb84_paseed_of f with | Some fidx => bb84_pa_public_branch_ptrace (bb84_prefix_errcorr_store p f s) fidx (bb84_history_readout_state EA (prefix_history p f) (xi s)) | None => 0 end) = \sum_f post_hash_state bb84_disSEpub bb84_pa_hash_index (castlf (bb84_public_assoc bb84_S bb84_E bb84_Ppub, bb84_public_assoc bb84_S bb84_E bb84_Ppub) (ptrace_cast_gen (bb84_setT_diff_complement (bb84_Ppub :|: (bb84_S :|: bb84_E))) ((bb84_prefix_pass_weight p f s)%:C *: @replaceso R L HL (bb84_Ppub :|: (bb84_S :|: bb84_Epub)) (bb84_leakage_public_register_state (bb84_prefix_errcorr_store p f s)) (bb84_history_readout_state EA (prefix_history p f) (xi s)))))). exact: bb84_prefix_pa_public_readout_seed_sum_endpoint. Qed.

Definition rhoZFEpub_readout_prog (EA : @adversary R L HL V bb84_Eve) (xi : @cq_state R L HL (bb84_cvar M) V) :
    'F[HL]_(bb84_Zl :|: (bb84_Fl :|: (bb84_E :|: bb84_Ppub))) := let st := bb84_pass_pa_public_readout_state EA xi in
  let norm := bb84_pass_leakage_public_readout_state EA xi in ptrace_cast_gen (bb84_setT_diff_complement
      (bb84_Zl :|: (bb84_Fl :|: (bb84_E :|: bb84_Ppub)))) (((@complex.Re R (\Tr norm))^-1)%:C *: st).
Lemma rhoZFEpub_readout_prog_psd (EA : @adversary R L HL V bb84_Eve) (xi : @cq_state R L HL (bb84_cvar M) V) :
  (forall s, xi s \is psdlf) -> rhoZFEpub_readout_prog EA xi \is psdlf.
Proof. rewrite /rhoZFEpub_readout_prog. set st := bb84_pass_pa_public_readout_state EA xi;
  set norm := bb84_pass_leakage_public_readout_state EA xi. move=> Hxi; have Hnorm_psd : norm \is psdlf.
  { rewrite /norm /bb84_pass_leakage_public_readout_state. apply: (@bb84_pass_history_public_readout_state_psd R P q dev LE HE bb84_register_index bb84_register_space (bb84_Ppub :|: (bb84_S :|: bb84_Epub)) bb84_leakage_public_register_state EA xi).
    - exact: bb84_leakage_public_register_state_den1lf.
    - exact: Hxi. } have Hnorm_ge0 : 0 <= @complex.Re R (\Tr norm) by have := psdlf_trlf Hnorm_psd; rewrite lecE /= => /andP[].
      have Hst_psd : st \is psdlf.
  { rewrite /st /bb84_pass_pa_public_readout_state. apply: (@bb84_pass_history_public_readout_state_psd R P q dev LE HE bb84_register_index bb84_register_space (bb84_Zl :|: (bb84_Fl :|: (bb84_Epub :|: bb84_Ppub))) bb84_pa_public_register_state EA xi).
    - exact: bb84_pa_public_register_state_den1lf.
    - exact: Hxi. } by apply: ptrace_cast_gen_psdlf; apply: psdlfZ; last exact: Hst_psd; rewrite lecR invr_ge0. Qed.

Lemma rhoZFEpub_readout_prog_tr_le1 (EA : @adversary R L HL V bb84_Eve) (xi : @cq_state R L HL (bb84_cvar M) V) :
  (forall s, xi s \is psdlf) -> @complex.Re R (\Tr (rhoZFEpub_readout_prog EA xi)) <= 1.
Proof. have rhoZFEpub_readout_prog_trace1 : forall (EA : @adversary R L HL V bb84_Eve) (xi : @cq_state R L HL (bb84_cvar M) V), let norm :=
  bb84_pass_leakage_public_readout_state EA xi in 0 < @complex.Re R (\Tr norm) -> @complex.Re R (\Tr (rhoZFEpub_readout_prog EA xi)) = 1.
  { move=> {}EA {}xi. rewrite /rhoZFEpub_readout_prog. set st := bb84_pass_pa_public_readout_state EA xi.
    set norm := bb84_pass_leakage_public_readout_state EA xi. move=> Hpass; rewrite /ptrace_cast_gen castlf_trlfE.
    have /cptpP [_ /tpmapP Htp] := @ptraceso_qc R L HL (mathcomp.boot.finset.setC (bb84_Zl :|: (bb84_Fl :|: (bb84_E :|: bb84_Ppub)))) (setTfor L). rewrite Htp linearZ /=. have HRe_realM : forall (r : R) (z : C), @complex.Re R (r%:C * z) = r * @complex.Re R z.
  { move=> r z. by case: z => zr zi /=; rewrite mul0r subr0. }
rewrite HRe_realM (bb84_pa_public_readout_trace_leakage_public EA xi). by rewrite mulVf ?lt0r_neq0. }
set norm := bb84_pass_leakage_public_readout_state EA xi; move=> Hxi; have Hnorm_psd : norm \is psdlf.
  { rewrite /norm /bb84_pass_leakage_public_readout_state. apply: (@bb84_pass_history_public_readout_state_psd R P q dev LE HE bb84_register_index bb84_register_space (bb84_Ppub :|: (bb84_S :|: bb84_Epub)) bb84_leakage_public_register_state EA xi).
    - exact: bb84_leakage_public_register_state_den1lf.
    - exact: Hxi. } have Hnorm_ge0 : 0 <= @complex.Re R (\Tr norm) by have := psdlf_trlf Hnorm_psd; rewrite lecE /= => /andP[].
      have [Hpass|Hpass] := boolP (0 < @complex.Re R (\Tr norm)).
  - by rewrite (rhoZFEpub_readout_prog_trace1 EA xi Hpass).
  - have Hnorm_le0 : @complex.Re R (\Tr norm) <= 0 by move: Hpass; rewrite -leNgt. have Hnorm0 : @complex.Re R (\Tr norm) = 0 by apply/eqP; rewrite eq_le Hnorm_ge0 Hnorm_le0. rewrite /rhoZFEpub_readout_prog -/norm. set st := bb84_pass_pa_public_readout_state EA xi; rewrite /ptrace_cast_gen castlf_trlfE. have /cptpP [_ /tpmapP Htp] := @ptraceso_qc R L HL (mathcomp.boot.finset.setC (bb84_Zl :|: (bb84_Fl :|: (bb84_E :|: bb84_Ppub)))) (setTfor L). rewrite Htp linearZ /=. have HRe_realM : forall (r : R) (z : C), @complex.Re R (r%:C
    * z) = r * @complex.Re R z.
    { move=> r z. by case: z => zr zi /=; rewrite mul0r subr0. } by rewrite HRe_realM /st (bb84_pa_public_readout_trace_leakage_public EA xi); rewrite -/norm Hnorm0 mulr0 ler01. Qed.

Definition bb84_vf_leakage_public_readout_state (EA : @adversary R L HL V bb84_Eve) (xi : @cq_state R L HL (bb84_cvar M) V) :=
  @bb84_vf_history_public_readout_state R P q dev LE HE bb84_register_index bb84_register_space (bb84_Ppub :|: (bb84_S :|: bb84_Epub))
    bb84_leakage_public_register_state EA xi.
Fact rhoZFEpub_readout_progE (EA : @adversary R L HL V bb84_Eve) (xi : @cq_state R L HL (bb84_cvar M) V) :
  let st := bb84_pass_pa_public_readout_state EA xi in let norm := bb84_pass_leakage_public_readout_state EA xi in
  rhoZFEpub_readout_prog EA xi = ((@complex.Re R (\Tr norm))^-1)%:C *: ptrace_cast_gen (bb84_setT_diff_complement
        (bb84_Zl :|: (bb84_Fl :|: (bb84_E :|: bb84_Ppub)))) st.
Proof. rewrite /rhoZFEpub_readout_prog /ptrace_cast_gen /=. set st := bb84_pass_pa_public_readout_state EA xi;
  set norm := bb84_pass_leakage_public_readout_state EA xi. set c := ((@complex.Re R (\Tr norm))^-1)%:C.
  by rewrite [\Tr_(~: (bb84_Zl :|: (bb84_Fl :|: (bb84_E :|: bb84_Ppub)))) (c *: st)]linearZ /=; rewrite [castlf _ (c *: _)]linearZ. Qed.

Fact bb84_vf_leakage_public_readout_state_psd (EA : @adversary R L HL V bb84_Eve) (xi : @cq_state R L HL (bb84_cvar M) V) :
  (forall s, xi s \is psdlf) -> bb84_vf_leakage_public_readout_state EA xi \is psdlf.
Proof. move=> Hxi; rewrite /bb84_vf_leakage_public_readout_state. apply: (@bb84_vf_history_public_readout_state_psd R P q dev LE HE
  bb84_register_index bb84_register_space (bb84_Ppub :|: (bb84_S :|: bb84_Epub)) bb84_leakage_public_register_state EA xi).
  - exact: bb84_leakage_public_register_state_den1lf.
  - exact: Hxi. Qed.

Fact bb84_pe_pass_leakage_public_readout_state_split (EA : @adversary R L HL V bb84_Eve) (xi : @cq_state R L HL (bb84_cvar M) V) :
  bb84_pe_pass_leakage_public_readout_state EA xi = bb84_pass_leakage_public_readout_state EA xi +
  bb84_vf_leakage_public_readout_state EA xi.
Proof. rewrite /bb84_pe_pass_leakage_public_readout_state /bb84_pass_leakage_public_readout_state /bb84_vf_leakage_public_readout_state.
  exact: (@bb84_pe_pass_history_public_readout_state_split R P q dev LE HE bb84_register_index bb84_register_space (bb84_Ppub :|: (bb84_S :|: bb84_Epub)) bb84_leakage_public_register_state EA xi). Qed.

Fact bb84_pass_leakage_public_readout_state_pa_cq_Epub (EA : @adversary R L HL V bb84_Eve) (xi : @cq_state R L HL (bb84_cvar M) V)
    (x x' : 'Idx[HL]_bb84_S) : x' != x -> ((liftf_lf (([> deltav x ; deltav x <] \O (\1 : 'F[HL]_(bb84_Epub :|: bb84_Ppub))) :
        'F[HL]_(bb84_S :|: (bb84_Epub :|: bb84_Ppub))) \o bb84_pass_leakage_public_readout_state EA xi) \o liftf_lf
      (([> deltav x' ; deltav x' <] \O (\1 : 'F[HL]_(bb84_Epub :|: bb84_Ppub))) : 'F[HL]_(bb84_S :|: (bb84_Epub :|: bb84_Ppub)))) = 0.
Proof. move=> Hx'x; rewrite /bb84_pass_leakage_public_readout_state /bb84_pass_history_public_readout_state.
  rewrite [X in X \o _ = _]linear_sumr /= linear_sumlz /=. apply: big1 => s _. rewrite [X in X \o _ = _]linear_sumr /= linear_sumlz /=.
  apply: big1 => h _. by rewrite [X in X \o _ = _]linearZr /= linearZl /=; rewrite bb84_leakage_public_replaceso_pa_cq //; rewrite scaler0. Qed.

Fact bb84_pass_leakage_public_readout_state_classical_E (EA : @adversary R L HL V bb84_Eve) (xi : @cq_state R L HL (bb84_cvar M) V)
    (p p' : 'Idx[HL]_bb84_Ppub) : p' != p -> ((liftf_lf (([> deltav p ; deltav p <] \O (\1 : 'F[HL]_(bb84_S :|: bb84_E))) :
        'F[HL]_(bb84_Ppub :|: (bb84_S :|: bb84_E))) \o bb84_pass_leakage_public_readout_state EA xi) \o liftf_lf
      (([> deltav p' ; deltav p' <] \O (\1 : 'F[HL]_(bb84_S :|: bb84_E))) : 'F[HL]_(bb84_Ppub :|: (bb84_S :|: bb84_E)))) = 0.
Proof. have bb84_pass_leakage_public_readout_state_classical : forall (EA : @adversary R L HL V bb84_Eve) (xi : @cq_state R L HL (bb84_cvar
  M) V) (p p' : 'Idx[HL]_bb84_Ppub), p' != p -> ((liftf_lf (([> deltav p ; deltav p <] \O (\1 : 'F[HL]_(bb84_S :|: bb84_Epub))) : 'F[HL]_(bb84_Ppub :|: (bb84_S :|: bb84_Epub))) \o bb84_pass_leakage_public_readout_state EA xi) \o liftf_lf (([> deltav p' ; deltav p' <] \O (\1 : 'F[HL]_(bb84_S :|: bb84_Epub))) : 'F[HL]_(bb84_Ppub :|: (bb84_S :|: bb84_Epub)))) = 0.
{ clear p' p xi EA; move=> EA xi p p'. move=> Hp'p. rewrite /bb84_pass_leakage_public_readout_state /bb84_pass_history_public_readout_state.
  rewrite [X in X \o _ = _]linear_sumr /= linear_sumlz /=. apply: big1 => s _. rewrite [X in X \o _ = _]linear_sumr /= linear_sumlz /=.
  apply: big1 => h _. rewrite [X in X \o _ = _]linearZr /= linearZl /=. rewrite bb84_leakage_public_replaceso_classical //.
  by rewrite scaler0. } move=> Hp'p; have HPS_Epub := bb84_disP_SEpub. have Hlift : forall p0 : 'Idx[HL]_bb84_Ppub, liftf_lf (([> deltav p0 ; deltav p0 <] \O (\1 : 'F[HL]_(bb84_S :|: bb84_E))) : 'F[HL]_(bb84_Ppub :|: (bb84_S :|: bb84_E))) = liftf_lf (([> deltav p0 ; deltav p0 <] \O (\1 : 'F[HL]_(bb84_S :|: bb84_Epub))) : 'F[HL]_(bb84_Ppub :|: (bb84_S :|: bb84_Epub))).
  { move=> p0. have Hleft : (([> deltav p0 ; deltav p0 <] \O (\1 : 'F[HL]_(bb84_S :|: bb84_E))) : 'F[HL]_(bb84_Ppub :|: (bb84_S :|: bb84_E))) = [> deltav p0 ; deltav p0 <] \⊗ (\1 : 'F[HL]_(bb84_S :|: bb84_E)).
    { by apply: to_Fnd_inj; rewrite (sdotFT _ _ bb84_disPSE) to_Fnd_tenE. } have Hright : (([> deltav p0 ; deltav p0 <] \O (\1 : 'F[HL]_(bb84_S :|: bb84_Epub))) : 'F[HL]_(bb84_Ppub :|: (bb84_S :|: bb84_Epub))) = [> deltav p0 ; deltav p0 <] \⊗ (\1 : 'F[HL]_(bb84_S :|: bb84_Epub)).
    { by apply: to_Fnd_inj; rewrite (sdotFT _ _ HPS_Epub) to_Fnd_tenE. } rewrite Hleft Hright.
      by rewrite !liftf_lf_tenf1r ?bb84_disPSE ?HPS_Epub. } by rewrite (Hlift p) (Hlift p'); exact: bb84_pass_leakage_public_readout_state_classical. Qed.
End RegisterAllocation.
Section CorrectnessReadout.
Variable R : realType.
Notation chsType := (@chsType R).
Variables (L : finType) (HL : L -> chsType).
Variables n k l leakEC M ec_bits vseed_count tag_count paseed_count : nat.
Variable Qtol eps_c : R.
Notation Cv := (bb84_cvar M).
Notation V := (bb84_val M n l ec_bits vseed_count tag_count paseed_count).
Variables basisX basisZ outEmpty empty_transcript : V.
Variable vrat : nat -> nat -> V.
Variables (Q : 'I_M -> {set L}) (dev_rho : forall i : 'I_M, V -> V -> 'F[HL]_(Q i)) (dev_meas : forall i : 'I_M, V -> V -> 'F[HL]_(Q i)).
Variables (tr_app_rounds : ('I_M -> V * V * V) -> V -> V) (tr_app_pe : V -> V -> V -> V -> V) (tr_app_ec : V -> V -> V -> V -> V).
Variables (tr_app_pa : V -> V -> V).
Variables (err_count : V -> V -> nat) (err_of : V -> nat) (unif_nsubset_mass : nat -> {set 'I_M} -> V -> R).
Variables (ir_pub : 'I_(2 ^ n) -> 'I_(2 ^ n) -> 'I_(2 ^ ec_bits)) (ir_dec : 'I_(2 ^ ec_bits) -> 'I_(2 ^ n) -> 'I_(2 ^ n)) (verify_hash : 'I_vseed_count -> 'I_(2 ^ n) -> 'I_tag_count) (privacy_hash : nat -> V -> V -> V).
Local Notation a_ := (@BVa M).
Local Notation y_ := (@BVy M).
Local Notation b_ := (@BVb M).
Local Notation y'_ := (@BVy' M).
Local Notation d_ := (@BVd M).
Local Notation Xv := (@BVX M).
Local Notation Zv := (@BVZ M).
Local Notation Kv := (@BVK M).
Local Notation XA := (@BVXA M).
Local Notation XB := (@BVXB M).
Local Notation ZA := (@BVZA M).
Local Notation ZB := (@BVZB M).
Local Notation lamv := (@BVlam M).
Local Notation pECv := (@BVpec M).
Local Notation Xhatv := (@BVXhat M).
Local Notation gv := (@BVg M).
Local Notation tAv := (@BVtA M).
Local Notation tBv := (@BVtB M).
Local Notation fv := (@BVf M).
Local Notation Sv := (@BVS M).
Local Notation Shv := (@BVSh M).
Local Notation abortv := (@BVabort M).
Local Notation Pvar := (@BVP M).
Local Notation bot := (@bb84_bot_val M n l ec_bits vseed_count tag_count paseed_count).
Local Notation vbool := (@bb84_bool_val M n l ec_bits vseed_count tag_count paseed_count).
Local Notation vbit := (@bb84_bit_val M n l ec_bits vseed_count tag_count paseed_count).
Local Notation vset := (@bb84_set_val M n l ec_bits vseed_count tag_count paseed_count).
Local Notation vset_of := (@bb84_set_of M n l ec_bits vseed_count tag_count paseed_count).
Local Notation bits_on := (@bb84_bits_on_val M n l ec_bits vseed_count tag_count paseed_count).
Local Notation test_bits_on := (@bb84_partial_bits_on_val M n l ec_bits vseed_count tag_count paseed_count).
Local Notation key_of := (@bb84_raw_key_of M n l ec_bits vseed_count tag_count paseed_count).
Local Notation raw_val := (@bb84_raw_key_val M n l ec_bits vseed_count tag_count paseed_count).
Local Notation unif_vseed := (@bb84_unif_vseed_mass R M n l ec_bits vseed_count tag_count paseed_count).
Local Notation unif_pseed := (@bb84_unif_pseed_mass R M n l ec_bits vseed_count tag_count paseed_count).
Local Notation ir_pub_val := (@bb84_ir_pub_val M n l ec_bits vseed_count tag_count paseed_count ir_pub).
Local Notation ir_dec_val := (@bb84_ir_dec_val M n l ec_bits vseed_count tag_count paseed_count ir_dec).
Local Notation verify_hash_val := (@bb84_verify_hash_val M n l ec_bits vseed_count tag_count paseed_count verify_hash).
Local Notation corr_prob := (@corr_prob_prog R L HL Cv V n k leakEC M Qtol a_ y_ b_ y'_ d_ Q Xv Zv Kv XA XB ZA ZB lamv pECv Xhatv
    gv tAv tBv Sv Shv abortv Pvar basisX basisZ outEmpty bot empty_transcript vbool vbit vset vset_of vrat dev_rho dev_meas
    tr_app_rounds tr_app_pe tr_app_ec bits_on test_bits_on err_count err_of unif_nsubset_mass
    ir_pub_val ir_dec_val unif_vseed verify_hash_val (2 ^ n) key_of).
Local Notation output_mismatch_prob := (@run_output_mismatch_prob R L HL Cv V Sv Shv abortv vbool).
Fact correctness_readout (qA : {set L}) (EA : @adversary R L HL V qA) (xi : @cq_state R L HL Cv V) :
  (0 < vseed_count)%N -> (0 < tag_count)%N -> (0 < paseed_count)%N -> @two_univ R _ _ _ verify_hash ->
  ((tag_count%:R : R)^-1 <= eps_c)%R -> abortv != Sv -> abortv != Shv -> (forall i, a_ i != y_ i) ->
  (forall i, Pvar != a_ i) -> (forall i, Pvar != y_ i) -> (forall i, Pvar != b_ i) ->
  (forall i, Pvar != y'_ i) -> (forall i, Pvar != d_ i) -> Pvar != Xv -> Pvar != Zv -> Pvar != abortv ->
  (forall i, abortv != a_ i) -> (forall i, abortv != y_ i) -> (forall i, abortv != b_ i) ->
  (forall i, abortv != y'_ i) -> (forall i, abortv != d_ i) ->
  abortv != Xv -> abortv != Zv -> abortv != Pvar -> abortv != Kv -> abortv != XA -> abortv != XB ->
  abortv != ZA -> abortv != ZB -> abortv != lamv -> abortv != pECv -> abortv != Xhatv -> abortv != gv ->
  abortv != tAv -> abortv != tBv -> XA != fv -> Xhatv != fv -> fv != Sv -> Xhatv != Sv ->
  Sv != Shv -> Sv != Pvar -> Shv != Pvar -> gv != tAv -> gv != tBv ->
  tAv != tBv -> tAv != Pvar -> tBv != Pvar -> XA != XB -> XA != ZA -> XA != ZB -> XA != Pvar -> XA != lamv ->
  XA != pECv -> XA != Xhatv -> XA != gv -> XA != tAv -> XA != tBv -> XB != pECv ->
  Xhatv != gv -> Xhatv != tAv -> Xhatv != tBv -> Xhatv != Pvar -> (forall i, cmd_wf qA (@Round R L HL Cv V n k M a_ y_ b_ y'_ d_ Q Xv Zv
      basisX basisZ outEmpty vbool vbit vset dev_rho dev_meas i)) -> cmd_wf qA (@ParamEst R L HL Cv V n M y_ y'_ Xv Zv Kv XA XB ZA ZB lamv
      Pvar bot vset_of vrat tr_app_pe bits_on test_bits_on err_count unif_nsubset_mass) -> cmd_wf qA
    (@ErrCorr R L HL Cv V leakEC XA XB pECv Xhatv gv tAv tBv
      Pvar tr_app_ec ir_pub_val ir_dec_val unif_vseed verify_hash_val) -> cq_wf xi -> @eps_correct R (output_mismatch_prob
      (@bb84_eval_scheme R L HL Cv V n k l leakEC M Qtol a_ y_ b_ y'_ d_ Q Xv Zv Kv XA XB ZA ZB lamv pECv Xhatv
        gv tAv tBv fv Sv Shv abortv Pvar basisX basisZ outEmpty bot empty_transcript vbool vbit vset vset_of vrat dev_rho dev_meas
        tr_app_rounds tr_app_pe tr_app_ec tr_app_pa bits_on test_bits_on err_count err_of unif_nsubset_mass
        ir_pub_val ir_dec_val unif_vseed verify_hash_val unif_pseed privacy_hash qA EA xi)) eps_c.
Proof. move=> Hvseed Htag Hpaseed H2u Htag_le HAS HAH Hay HPa HPy HPb HPy' HPd HPX HPZ HPabort Ha Hy Hb Hy' Hd HX HZ HP HK HXA HXB HZA HZB
  Hlam HpEC HXhat Hg HtA HtB HXAf HXhatf HfS HXhatS HSS HSP HShP HgtA HgtB HtAtB HtAP HtBP HXAXB HXAZA HXAZB HXAP HXAlam HXAp HXAXhat HXAg HXAtA HXAtB HXBp HXhatg HXhattA HXhattB HXhatP Hround Hpe Hec Hxi. have Hxi_psd : forall s, xi s \is psdlf by case: Hxi.
  rewrite /eps_correct. have Hbb84_correct := bb84_correct Htag H2u (@corr_prob_prog_nonneg R L HL Cv V n k leakEC M Qtol a_ y_ b_ y'_ d_ Q Xv Zv Kv XA XB ZA ZB lamv pECv Xhatv gv tAv tBv Sv Shv abortv Pvar basisX basisZ outEmpty bot empty_transcript vbool vbit vset vset_of vrat dev_rho dev_meas tr_app_rounds tr_app_pe tr_app_ec bits_on test_bits_on err_count err_of unif_nsubset_mass ir_pub_val ir_dec_val unif_vseed verify_hash_val (2 ^ n) key_of qA EA xi Hround Hpe Hec Hxi_psd) (@corr_prob_prog_mismatch_mass_le1 R L HL Cv V n k leakEC M Qtol a_ y_ b_ y'_ d_ Q Xv Zv Kv XA XB ZA ZB lamv pECv Xhatv gv tAv tBv Sv Shv abortv Pvar basisX basisZ outEmpty bot empty_transcript vbool vbit vset vset_of vrat dev_rho dev_meas tr_app_rounds tr_app_pe tr_app_ec bits_on test_bits_on err_count err_of unif_nsubset_mass ir_pub_val ir_dec_val unif_vseed verify_hash_val (2 ^ n) key_of qA EA xi Hround Hpe Hec Hxi) Htag_le.
  rewrite /eps_correct in Hbb84_correct; apply: (le_trans _ Hbb84_correct). rewrite /p_mismatch; apply: (@run_output_mismatch_prob_le_collision_sum_from_paramest R L HL Cv V n k l leakEC M Qtol a_ y_ b_ y'_ d_ Q Xv Zv Kv XA XB ZA ZB lamv pECv Xhatv gv tAv tBv fv Sv Shv abortv Pvar basisX basisZ outEmpty bot empty_transcript vbool vbit vset vset_of vrat dev_rho dev_meas tr_app_rounds tr_app_pe tr_app_ec tr_app_pa bits_on test_bits_on err_count err_of unif_nsubset_mass ir_pub_val ir_dec_val unif_vseed verify_hash_val unif_pseed privacy_hash (2 ^ n) key_of raw_val (@verification_collision_prob R (2 ^ n) vseed_count tag_count verify_hash) qA EA xi). all: try by [assumption | exact: bb84_bool_val_neq | exact: bb84_bits_on_val_raw_key | move=> s; split; [exact: bb84_unif_pseed_mass_nonneg | exact: (bb84_unif_pseed_mass_sum1 s Hpaseed)]]. move=> seed_store ok raw bob Hraw; rewrite /verification_collision_prob. by rewrite (@bb84_verify_hash_errcorr_mismatch_guard_seed_sumE R M n l ec_bits vseed_count tag_count paseed_count seed_store verify_hash ir_pub ir_dec leakEC ok raw bob Hvseed Hraw). Qed.
End CorrectnessReadout.
Section ProtocolSecurity.
Variable R : realType.
Notation chsType := (@chsType R).
Variables (P : @bb84_protocol R) (q : R) (dev : bb84_certified_device P q) (LE : finType) (HE : LE -> chsType).
Notation M := (bb84_round_limit P).
Notation HB := (@bb84_register_space R P q dev).
Notation L := (bb84_label M LE bb84_register_index).
Notation HL := (bb84_label_space HE HB).
Notation V := (bb84_val M (bb84_n P) (bb84_l P) (cd_ir_bits dev) (cd_vseed_count dev) (cd_tag_count dev) (cd_paseed_count dev)).
Notation store := (@store (bb84_cvar M) V).
Notation state := (@cq_state R L HL (bb84_cvar M) V).
Notation Eve := (@bb84_Eve R P LE).
Notation Sreg := (@bb84_S R P LE).
Notation Ereg := (@bb84_E R P LE).
Notation Zkey := (@bb84_Zkey R P LE).
Notation Bq := (@bb84_Bq R P LE).
Notation Zp := (@bb84_Zp R P LE).
Notation Fl := (@bb84_Fl R P LE).
Notation Zl := (@bb84_Zl R P LE).
Notation Ppub := (@bb84_Ppub R P LE).
Definition bb84_branch_shape (h : @run_history V M) (s : store) : Prop := let fs := @final_store R (bb84_cvar M) V
      (bb84_n P) (bb84_k P) (bb84_l P) (cd_ir_bits dev) M (bb84_Qtol P) (@BVa M) (@BVy M) (@BVb M) (@BVy' M) (@BVd M)
      (@BVX M) (@BVZ M) (@BVK M) (@BVXA M) (@BVXB M) (@BVZA M) (@BVZB M) (@BVlam M) (@BVpec M) (@BVXhat M)
      (@BVg M) (@BVtA M) (@BVtB M) (@BVf M) (@BVS M) (@BVSh M) (@BVabort M) (@BVP M)
      (bb84_basis_value dev BasisX) (bb84_basis_value dev BasisZ) (bb84_outcome_val None) bb84_bot_val bb84_empty_transcript_val
      bb84_bool_val bb84_set_val bb84_set_of bb84_error_val bb84_tr_app_rounds bb84_tr_app_pe bb84_tr_app_ec bb84_tr_app_pa
      bb84_bits_on_val bb84_partial_bits_on_val bb84_err_count_val bb84_error_of (bb84_ir_pub_val (@cd_ir_pub R P q dev))
      (bb84_ir_dec_val (@cd_ir_dec R P q dev)) (bb84_verify_hash_val (@cd_vh R P q dev)) (bb84_privacy_hash_val (@cd_pa R P q dev)) h s in
  let spe := @paramest_store (bb84_cvar M) V M (@BVy M) (@BVy' M) (@BVZ M) (@BVK M) (@BVXA M)
      (@BVXB M) (@BVZA M) (@BVZB M) (@BVlam M) (@BVP M) bb84_set_of bb84_error_val bb84_tr_app_pe bb84_bits_on_val
      bb84_partial_bits_on_val bb84_err_count_val h (@announce_store (bb84_cvar M) V M (@BVa M) (@BVb M)
        (@BVd M) (@BVP M) bb84_tr_app_rounds (@rounds_store (bb84_cvar M) V M (@BVa M) (@BVy M)
          (@BVb M) (@BVy' M) (@BVd M) (@BVX M) (@BVZ M) (bb84_basis_value dev BasisX) (bb84_basis_value dev BasisZ)
          (bb84_outcome_val None) bb84_bool_val bb84_set_val h (@start_store (bb84_cvar M) V M (@BVX M) (@BVZ M)
            (@BVabort M) (@BVP M) bb84_empty_transcript_val bb84_bool_val bb84_set_val s))) in
  let sec := @errcorr_store (bb84_cvar M) V (cd_ir_bits dev) M (@BVXA M) (@BVXB M) (@BVpec M) (@BVXhat M) (@BVg M)
      (@BVtA M) (@BVtB M) (@BVP M) bb84_tr_app_ec (bb84_ir_pub_val (@cd_ir_pub R P q dev)) (bb84_ir_dec_val (@cd_ir_dec R P q dev))
      (bb84_verify_hash_val (@cd_vh R P q dev)) h spe in (fs (@BVabort M) = bb84_bool_val true /\
   fs (@BVS M) = bb84_bot_val /\ fs (@BVSh M) = bb84_bot_val) \/ (fs (@BVabort M) = bb84_bool_val false /\ fs (@BVS M) =
     bb84_privacy_hash_val (@cd_pa R P q dev) (bb84_l P) (@hist_f V M h) (sec (@BVXA M)) /\ fs (@BVSh M) =
     bb84_privacy_hash_val (@cd_pa R P q dev) (bb84_l P) (@hist_f V M h) (sec (@BVXhat M))).
Fact bb84_final_store_branch_shape (h : @run_history V M) (s : store) : bb84_branch_shape h s.
Proof. rewrite /bb84_branch_shape; apply: final_store_branch_shape; by [exact: bb84_abort_neq_P | rewrite /bb84_bool_val | move=> ?;
  cvun | cvne]. Qed.

Corollary bb84_partition_protocol : forall (EA : @adversary R L HL V Eve) (xi_init : state),
  cq_wf xi_init -> let xi_out := @bb84_eval R P q LE HE bb84_register_index HB dev Eve EA xi_init in let p_abort :=
    @run_abort_prob R L HL (bb84_cvar M) V (@BVabort M) bb84_bool_val xi_out in let p_pass :=
    @run_pass_prob R L HL (bb84_cvar M) V (@BVabort M) bb84_bool_val xi_out in p_abort + p_pass = 1.
Proof. move=> EA xi_init Hxi /=. have evalE : @bb84_eval R P q LE HE bb84_register_index HB dev Eve EA xi_init = bb84_eval_scheme_state EA
  xi_init.
  { by rewrite /bb84_eval /bb84_program /bb84_eval_scheme_state /bb84_eval_scheme /bb84_program_scheme /bb84_program_device_rho /bb84_device_dev_rho /bb84_program_device_meas /bb84_device_dev_meas /bb84_program_basis_value /bb84_basis_value /bb84_program_basis_of_value /bb84_basis_of_value. } by rewrite evalE; exact: bb84_eval_scheme_abort_pass_partition. Qed.

Local Ltac crpart := by [assumption | exact: cd_vseed_pos | exact: cd_tag_pos | exact: cd_paseed_pos | exact: cd_vh_two_univ | exact:
  cd_tag_le | exact: bb84_abort_neq_S | exact: bb84_abort_neq_Sh | exact: bb84_abort_neq_P | rewrite eq_sym bb84_abort_neq_P | move=> ?;
  cvun | cvne].
Corollary bb84_correct_protocol : forall (EA : @adversary R L HL V Eve) (xi_init : state),
  cq_wf xi_init -> let xi_out := @bb84_eval R P q LE HE bb84_register_index HB dev Eve EA xi_init in let p_mismatch :=
    @run_output_mismatch_prob R L HL (bb84_cvar M) V (@BVS M) (@BVSh M) (@BVabort M) bb84_bool_val xi_out in
  @eps_correct R p_mismatch (bb84_eps_c P).
Proof. have bb84_eval_scheme_correct : forall (EA : @adversary R L HL V Eve) (xi_init : state), cq_wf xi_init -> @eps_correct R
  (@run_output_mismatch_prob R L HL (bb84_cvar M) V (@BVS M) (@BVSh M) (@BVabort M) bb84_bool_val (bb84_eval_scheme_state EA xi_init)) (bb84_eps_c P).
{ move=> EA xi_init. move=> Hxi; have Hround_wf := @bb84_round_cmd_wf R P q dev LE HE. have Hpe_wf := @bb84_paramest_cmd_wf R P q dev LE HE; have Hec_wf := @bb84_errcorr_cmd_wf R P q dev LE HE. apply: correctness_readout.
  1-3: crpart. 1-3: crpart. 1-3: crpart. 1-3: crpart. 1-3: crpart. 1-3: crpart. 1-3: crpart. 1-3: crpart. 1-3: crpart. 1-3: crpart. 1-3: crpart. 1-3: crpart. 1-3: crpart. 1-3: crpart. 1-3: crpart. 1-3: crpart. 1-3: crpart. 1-3: crpart. 1-3: crpart. 1-3: crpart. 1-3: crpart.
  all: crpart. } move=> EA xi_init Hxi /=.
  have evalE : @bb84_eval R P q LE HE bb84_register_index HB dev Eve EA xi_init = bb84_eval_scheme_state EA xi_init.
  { by rewrite /bb84_eval /bb84_program /bb84_eval_scheme_state /bb84_eval_scheme /bb84_program_scheme /bb84_program_device_rho /bb84_device_dev_rho /bb84_program_device_meas /bb84_device_dev_meas /bb84_program_basis_value /bb84_basis_value /bb84_program_basis_of_value /bb84_basis_of_value. } by rewrite evalE; exact: bb84_eval_scheme_correct. Qed.
End ProtocolSecurity.
Import Order.TTheory GRing.Theory Num.Theory Num.Def MxLownerOrder.
Import VectorInternalTheory.
Local Close Scope qkd_scope.
Local Close Scope classical_set_scope.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Local Open Scope lfun_scope.
Section BiprodExtra.
Variable R : realType.
Notation C := (@hermitian.C R).
Variables (L : finType) (H : L -> @chsType R).
Fact biprod_mx_one (A B : {set L}) (disAB : [disjoint A & B]) : biprod_mx disAB (\1 : 'F[H]_(A :|: B)) = 1%:M.
Proof. rewrite /biprod_mx h2mx1. set Q : 'M[C]_(dim 'H[H]_A * dim 'H[H]_B) := castmx (tenv_dim disAB, erefl) (@tenv_mxU R L H A B).
  have HQ_t : Q^*t = castmx (erefl, tenv_dim disAB) (@tenv_mxU R L H A B)^*t.
  { rewrite /Q. exact: (@castmx_mx_mxT _ _ (@adjmx _) _ _ _ _ (tenv_dim disAB, erefl) (@tenv_mxU R L H A B)). }
have HQtQ : Q^*t *m Q = 1%:M.
  { rewrite /Q HQ_t mcextra.castmx_mul. have HU : (@tenv_mxU R L H A B)^*t *m (@tenv_mxU R L H A B) = 1%:M.
    { have := unitarymxK (@tenv_mxU_adj_unitarymx R L H A B disAB). by rewrite adjmxK. } rewrite HU. by case: _ / (tenv_dim disAB); rewrite castmx_id. } have -> : castmx (tenv_dim disAB, tenv_dim disAB) (1%:M : 'M[C]_(dim 'H[H]_(A :|: B))) = 1%:M.
  { by case: _ / (tenv_dim disAB); rewrite castmx_id. } by rewrite mulmx1 HQtQ. Qed.

Lemma biprod_mx_adj (A B : {set L}) (disAB : [disjoint A & B]) (f : 'F[H]_(A :|: B)) : biprod_mx disAB f^A = (biprod_mx disAB f)^*t.
Proof. rewrite /biprod_mx h2mx_adj. set Q : 'M[C]_(dim 'H[H]_A * dim 'H[H]_B) := castmx (tenv_dim disAB, erefl) (@tenv_mxU R L H A B).
  have Hcast_adj : castmx (tenv_dim disAB, tenv_dim disAB) (h2mx f)^*t = (castmx (tenv_dim disAB, tenv_dim disAB) (h2mx f))^*t.
  { by rewrite (@castmx_mx_mxT _ _ (@adjmx _) _ _ _ _ (tenv_dim disAB, tenv_dim disAB) (h2mx f)). }
by rewrite Hcast_adj adjmxM adjmxM adjmxK; rewrite !mulmxA. Qed.

Fact biprod_of_mx_trace (A B : {set L}) (disAB : [disjoint A & B]) (m : 'M[C]_(dim ('H[H]_A) * dim ('H[H]_B))) :
  \Tr (biprod_of_mx disAB m) = \tr m.
Proof. by rewrite -{2}(biprod_mxK disAB m) biprod_mx_trace. Qed.

Fact biprod_of_mx_den1 (A B : {set L}) (disAB : [disjoint A & B]) (m : 'M[C]_(dim ('H[H]_A) * dim ('H[H]_B))) :
  m \is den1mx -> biprod_of_mx disAB m \is den1lf.
Proof. move=> /den1mxP [Hpsd /eqP Htr]. by apply/den1lfP; split; first exact: biprod_of_mx_psd; rewrite biprod_of_mx_trace Htr. Qed.

Fact biprod_of_mx_unitary (A B : {set L}) (disAB : [disjoint A & B]) (m : 'M[C]_(dim ('H[H]_A) * dim ('H[H]_B))) :
  m \is unitarymx -> biprod_of_mx disAB m \is unitarylf.
Proof. move=> Hm; apply/unitarylfP. have Hmx : biprod_mx disAB ((biprod_of_mx disAB m)^A \o biprod_of_mx disAB m) = biprod_mx disAB (\1 :
  'F[H]_(A :|: B)).
  { rewrite biprod_mx_comp biprod_mx_adj biprod_mxK biprod_mx_one. exact: unitarymxKV. } exact: (biprod_mx_inj Hmx). Qed.
End BiprodExtra.
Section BitAddress.
Definition upd_str {d : nat} (s : bitstr d) (j : 'I_d) (b : bool) : bitstr d := fun k => if k == j then b else s k.
Definition bit_of_ord {d : nat} (x : 'I_(2 ^ d)) (j : 'I_d) : bool := ord_to_bitstring x j.
Definition upd_bit {d : nat} (x : 'I_(2 ^ d)) (j : 'I_d) (b : bool) : 'I_(2 ^ d) := bitstring_to_ord (upd_str (ord_to_bitstring x) j b).
Lemma bit_of_upd_bit {d : nat} (x : 'I_(2 ^ d)) (j : 'I_d) (b : bool) : bit_of_ord (upd_bit x j b) j = b.
Proof. by rewrite /bit_of_ord /upd_bit ord_to_bitstringK /upd_str eqxx. Qed.
End BitAddress.
Section BitswapPerm.
Variable R : realType.
Notation C := (@hermitian.C R).
Variables a b : nat.
Variables (jA : 'I_a) (jB : 'I_b).
Definition bitswap_pairfun (z : 'I_(2 ^ a) * 'I_(2 ^ b)) : 'I_(2 ^ a) * 'I_(2 ^ b) := (upd_bit z.1 jA (bit_of_ord z.2 jB),
   upd_bit z.2 jB (bit_of_ord z.1 jA)).
Fact bitswap_pairfunK : involutive bitswap_pairfun.
Proof. have upd_bit_upd_bit : forall (d : nat) (x : 'I_(2 ^ d)) (j : 'I_d) (bb c : bool), upd_bit (upd_bit x j bb) j c = upd_bit x j c.
  { move=> d x j bb c. rewrite /upd_bit ord_to_bitstringK. congr bitstring_to_ord. apply/funext=> k. by rewrite /upd_str; case: (k == j). }
have upd_bit_id : forall (d : nat) (x : 'I_(2 ^ d)) (j : 'I_d), upd_bit x j (bit_of_ord x j) = x.
  { move=> d x j. rewrite /upd_bit /bit_of_ord. have -> : upd_str (ord_to_bitstring x) j (ord_to_bitstring x j) = ord_to_bitstring x.
  { by apply/funext=> k; rewrite /upd_str; case: eqP => [->|]. }
exact: bitstring_to_ordK. }
by move=> [x y]; rewrite /bitswap_pairfun /=; rewrite !bit_of_upd_bit !upd_bit_upd_bit !upd_bit_id. Qed.

Definition bitswap_ordfun (z : 'I_(2 ^ a * 2 ^ b)) : 'I_(2 ^ a * 2 ^ b) := mxtens_index (bitswap_pairfun (mxtens_unindex z)).
Lemma bitswap_ordfunK : involutive bitswap_ordfun.
Proof. move=> z. by rewrite /bitswap_ordfun mxtens_indexK bitswap_pairfunK mxtens_unindexK. Qed.

Definition bitswap_perm : 'S_(2 ^ a * 2 ^ b) := perm (inv_inj bitswap_ordfunK).
Definition bitswap_mx : 'M[C]_(2 ^ a * 2 ^ b) := perm_mx bitswap_perm.
Fact bitswap_mx_unitary : bitswap_mx \is unitarymx.
Proof. exact: perm_mx_unitary. Qed.
End BitswapPerm.
Section BitswapLabelled.
Variable R : realType.
Notation C := (@hermitian.C R).
Variables (L : finType) (H : L -> @chsType R).
Variables A B : {set L}.
Variable disAB : [disjoint A & B].
Variables a b : nat.
Variables (dimA : dim ('H[H]_A) = (2 ^ a)%N) (dimB : dim ('H[H]_B) = (2 ^ b)%N).
Let dimAB : (dim ('H[H]_A) * dim ('H[H]_B))%N = (2 ^ a * 2 ^ b)%N := f_equal2 muln dimA dimB.
Definition bitswap_lf (jA : 'I_a) (jB : 'I_b) : 'F[H]_(A :|: B) := biprod_of_mx disAB
    (castmx (esym dimAB, esym dimAB) (@bitswap_mx R a b jA jB)).
Fact bitswap_lf_unitary (jA : 'I_a) (jB : 'I_b) : bitswap_lf jA jB \is unitarylf.
Proof. apply: biprod_of_mx_unitary. apply: castmx_unitarymx. exact: bitswap_mx_unitary. Qed.

Fact bitswap_lf_lift_unitary (jA : 'I_a) (jB : 'I_b) : liftf_lf (bitswap_lf jA jB) \is unitarylf.
Proof. by rewrite -liftf_lf_unitaryE bitswap_lf_unitary. Qed.

Definition bitswap_so (jA : 'I_a) (jB : 'I_b) : 'SO[H]_setT := formso (liftf_lf (bitswap_lf jA jB)).
Fact bitswap_so_cptp (jA : 'I_a) (jB : 'I_b) : bitswap_so jA jB \is cptp.
Proof. apply/cpmap_tpmap_cptp; first exact: formso_cp. apply/tpmapP => x. rewrite formsoE lftraceC comp_lfunA.
  move/unitarylfP: (bitswap_lf_lift_unitary jA jB) => ->; by rewrite comp_lfun1l. Qed.

Lemma bitswap_so_trlf (jA : 'I_a) (jB : 'I_b) (x : 'F[H]_setT) : \Tr (bitswap_so jA jB x) = \Tr x.
Proof. by move: (bitswap_so_cptp jA jB) => /cptpP [_ /tpmapP ->]. Qed.

Lemma bitswap_so_psd (jA : 'I_a) (jB : 'I_b) (x : 'F[H]_setT) : x \is psdlf -> bitswap_so jA jB x \is psdlf.
Proof. exact: cp_psdP. Qed.

Lemma bitswap_so_formso_compC (T : {set L}) (disT : [disjoint T & A :|: B]) (f : 'F[H]_T) (jA : 'I_a) (jB : 'I_b) :
  bitswap_so jA jB :o formso (liftf_lf f) = formso (liftf_lf f) :o bitswap_so jA jB.
Proof. rewrite /bitswap_so -!liftfso_formso. apply: liftfso_compC. by rewrite disjoint_sym. Qed.
End BitswapLabelled.
Section EBZPointerBasis.
Variable R : realType.
Notation C := (@hermitian.C R).
Definition bb84_eb_z_sign (zbit : bool) : C := if zbit then -1 else 1.
Definition bb84_prep_source_z_ket (zbit : bool) : 'cV[C]_4 := (sqrtC (2%:R : C))^-1 *:
    ((delta_mx (bb84_prep_index BasisX false) (0 : 'I_1) : 'cV[C]_4)
      + bb84_eb_z_sign zbit *: (delta_mx (bb84_prep_index BasisX true) (0 : 'I_1) : 'cV[C]_4)).
Definition bb84_prep_source_z_projector (zbit : bool) : 'M[C]_(4 * 2) := (bb84_prep_source_z_ket zbit *m (bb84_prep_source_z_ket zbit)^*t)
    *t (1%:M : 'M[C]_2).
Fact bb84_eb_z_sign_conj (zbit : bool) : (bb84_eb_z_sign zbit)^* = bb84_eb_z_sign zbit.
Proof. by case: zbit; rewrite /bb84_eb_z_sign ?rmorphN rmorph1. Qed.
End EBZPointerBasis.
Section CollectBB84.
Variable R : realType.
Notation chsType := (@chsType R).
Notation C := (@hermitian.C R).
Variables (P : @bb84_protocol R) (q : R) (dev : bb84_certified_device P q) (LE : finType) (HE : LE -> chsType).
Notation M := (bb84_round_limit P).
Notation LB := bb84_register_index.
Notation HB := (@bb84_register_space R P q dev).
Notation L := (bb84_label M LE LB).
Notation HL := (bb84_label_space HE HB).
Notation V := (bb84_val M (bb84_n P) (bb84_l P) (cd_ir_bits dev) (cd_vseed_count dev) (cd_tag_count dev) (cd_paseed_count dev)).
Notation Eve := (bb84_eve_reg M LE LB).
Notation Sreg := (bb84_S P LE).
Notation Bqreg := (bb84_Bq P LE).
Notation nkey := (bb84_n P).
Lemma bb84_collect_disS_source (i : 'I_M) : [disjoint Sreg & @bb84_source_reg M LE LB i].
Proof. by rewrite /bb84_S /bb84_reg /bb84_bridge_reg /bb84_source_reg disjoint1X inE /bb84_bridge_label /bb84_source_label. Qed.

Lemma bb84_collect_disBq_signal (i : 'I_M) : [disjoint Bqreg & @bb84_signal_reg M LE LB i].
Proof. by rewrite /bb84_Bq /bb84_reg /bb84_bridge_reg /bb84_signal_reg disjoint1X inE /bb84_bridge_label /bb84_signal_label. Qed.

Lemma bb84_dim_S_pow2 : dim ('H[HL]_Sreg) = (2 ^ nkey)%N.
Proof. exact: esym (@bb84_dim_S R P q dev LE HE). Qed.

Lemma bb84_dim_Bq_pow2 : dim ('H[HL]_Bqreg) = (2 ^ nkey)%N.
Proof. exact: esym (@bb84_dim_Bq R P q dev LE HE). Qed.

Lemma bb84_dim_source_pow2 (i : 'I_M) : dim ('H[HL]_(@bb84_source_reg M LE LB i)) = (2 ^ 2)%N.
Proof. by rewrite (bb84_source_reg_dim HE HB i). Qed.

Lemma bb84_dim_signal_pow2 (i : 'I_M) : dim ('H[HL]_(@bb84_signal_reg M LE LB i)) = (2 ^ 1)%N.
Proof. by rewrite (bb84_signal_reg_dim HE HB i). Qed.

Definition bb84_src_ptr_slot : 'I_2 := Ordinal (isT : (1 < 2)%N).
Definition bb84_swap_S_so (j : 'I_nkey) (i : 'I_M) : 'SO[HL]_setT := bitswap_so (bb84_collect_disS_source i)
    bb84_dim_S_pow2 (bb84_dim_source_pow2 i) j bb84_src_ptr_slot.
Definition bb84_swap_Bq_so (j : 'I_nkey) (i : 'I_M) : 'SO[HL]_setT := bitswap_so (bb84_collect_disBq_signal i)
    bb84_dim_Bq_pow2 (bb84_dim_signal_pow2 i) j ord0.
Fact bb84_swap_Bq_so_psd (j : 'I_nkey) (i : 'I_M) (x : 'F[HL]_setT) : x \is psdlf -> bb84_swap_Bq_so j i x \is psdlf.
Proof. exact: bitswap_so_psd. Qed.

Local Lemma bb84_collect_castmx_den1 (m n : nat) (e : m = n) (A : 'M[C]_m) : A \is den1mx -> castmx (e, e) A \is den1mx.
Proof. move=> /den1mxP [Hpsd Htr]. apply/den1mxP; split; first exact: castmx_sq_psdmx. by rewrite mxtrace_castmx_sq; exact: Htr. Qed.

Lemma bb84_collect_source_signal_lfun_den1 (i : 'I_M) (m : 'M[C]_(4 * 2)) : m \is den1mx -> bb84_source_signal_lfun HE HB i m \is den1lf.
Proof. move=> Hm; rewrite /bb84_source_signal_lfun. apply: biprod_of_mx_den1. exact: bb84_collect_castmx_den1. Qed.

Definition bb84_eb_pair_x_branch_ok (pair : 'M[C]_(4 * 2)) : Prop := forall bit : bool, bb84_prep_source_projector R BasisX bit *m pair *m
      bb84_prep_source_projector R BasisX bit = ((2%:R)^-1)%:C *: ((delta_mx (bb84_prep_index BasisX bit)
          (bb84_prep_index BasisX bit) : 'M[C]_4) *t cd_rho dev BasisX bit).
Definition bb84_key_set (h : @run_history V M) : {set 'I_M} := bb84_set_of (@hist_K V M h).
Definition bb84_eb_round_so (EA : @adversary R L HL V Eve) (h : @run_history V M) (K : {set 'I_M}) (pair : 'M[C]_(4 * 2))
    (i : 'I_M) : 'SO[HL]_setT := if i \in K then (bb84_prep_basis_prob P (bb84_history_bob_basis h i) *
     bb84_prep_basis_prob P (bb84_history_alice_basis h i))%:C *: (liftfso (EA (bb84_signal_reg i) (empty_transcript dev)) :o
       replaceso (bb84_source_signal_lfun HE HB i pair)) else (bb84_prep_basis_prob P (bb84_history_bob_basis h i))%:C *:
      (formso (liftf_lf (bb84_round_readout_lf dev HE HB i (bb84_history_bob_basis h i) (bb84_history_bob_outcome h i))) :o
       (liftfso (EA (bb84_signal_reg i) (empty_transcript dev)) :o replaceso (bb84_signal_lfun HE HB i (bb84_prep_source_branch dev
            (bb84_history_alice_basis h i) (bb84_history_alice_bit h i))))).
Definition bb84_eb_implant_so (K : {set 'I_M}) (j : 'I_nkey) : 'SO[HL]_setT := if bb84_selected_index K j is Some i then
    bb84_swap_S_so j i :o bb84_swap_Bq_so j i else \:1.
Definition bb84_eb_history_state (EA : @adversary R L HL V Eve) (pair : 'M[C]_(4 * 2))
    (h : @run_history V M) (rho : 'F[HL]_setT) : 'F[HL]_setT := if bb84_history_decoded h && (#|bb84_key_set h| == nkey) then
    (\compr_(j <- enum 'I_nkey) bb84_eb_implant_so (bb84_key_set h) j) ((\compr_(i <- enum 'I_M)
          bb84_eb_round_so EA h (bb84_key_set h) pair i) rho) else 0.
Definition bb84_collect_post_weight (h : @run_history V M) (s : @store (bb84_cvar M) V) : R := history_post_weight
    (R:=R) (Cv:=bb84_cvar M) (V:=V) (M:=M) (bb84_n P) (bb84_k P) (cd_ir_bits dev) (bb84_Qtol P)
    (@BVa M) (@BVy M) (@BVb M) (@BVy' M) (@BVd M) (@BVX M) (@BVZ M) (@BVK M) (@BVXA M) (@BVXB M)
    (@BVZA M) (@BVZB M) (@BVlam M) (@BVpec M) (@BVXhat M) (@BVg M) (@BVtA M) (@BVtB M) (@BVabort M) (@BVP M)
    (bb84_basis_value dev BasisX) (bb84_basis_value dev BasisZ) (bb84_outcome_val None) bb84_bot_val bb84_empty_transcript_val
    bb84_bool_val bb84_set_val bb84_set_of bb84_error_val bb84_tr_app_rounds bb84_tr_app_pe bb84_tr_app_ec
    bb84_bits_on_val bb84_partial_bits_on_val bb84_err_count_val bb84_error_of bb84_unif_nsubset_mass
    (bb84_ir_pub_val (@cd_ir_pub R P q dev)) (bb84_ir_dec_val (@cd_ir_dec R P q dev))
    bb84_unif_vseed_mass (bb84_verify_hash_val (@cd_vh R P q dev)) bb84_unif_pseed_mass h s.
Definition bb84_collect_key_sample_mass (h : @run_history V M) (s : @store (bb84_cvar M) V) : R :=
  @key_sample_mass R (bb84_cvar M) V (bb84_n P) M (@BVX M) bb84_bot_val bb84_set_of (@bb84_unif_nsubset_mass R M (bb84_n P) (bb84_l P)
      (cd_ir_bits dev) (cd_vseed_count dev) (cd_tag_count dev) (cd_paseed_count dev)) (@announce_store (bb84_cvar M) V M (@BVa M) (@BVb M)
      (@BVd M) (@BVP M) bb84_tr_app_rounds (@rounds_store (bb84_cvar M) V M (@BVa M) (@BVy M) (@BVb M) (@BVy' M) (@BVd M) (@BVX M) (@BVZ M)
        (bb84_basis_value dev BasisX) (bb84_basis_value dev BasisZ) (bb84_outcome_val None) bb84_bool_val bb84_set_val h
        (@start_store (bb84_cvar M) V M (@BVX M) (@BVZ M) (@BVabort M) (@BVP M) bb84_empty_transcript_val bb84_bool_val bb84_set_val s)))
    (@hist_K V M h).
Definition bb84_collect_pe_pass_indic (h : @run_history V M) (s : @store (bb84_cvar M) V) : bool :=
  ~~ @pe_failed R (bb84_cvar M) V (bb84_n P) (bb84_k P) M (bb84_Qtol P) (@BVX M) (@BVZ M) (@BVlam M) bb84_set_of bb84_error_of
       (@paramest_store (bb84_cvar M) V M (@BVy M) (@BVy' M) (@BVZ M) (@BVK M) (@BVXA M) (@BVXB M) (@BVZA M) (@BVZB M) (@BVlam M) (@BVP M)
          bb84_set_of bb84_error_val bb84_tr_app_pe bb84_bits_on_val bb84_partial_bits_on_val bb84_err_count_val h
          (@announce_store (bb84_cvar M) V M (@BVa M) (@BVb M) (@BVd M) (@BVP M) bb84_tr_app_rounds
            (@rounds_store (bb84_cvar M) V M (@BVa M) (@BVy M) (@BVb M) (@BVy' M) (@BVd M) (@BVX M) (@BVZ M)
              (bb84_basis_value dev BasisX) (bb84_basis_value dev BasisZ) (bb84_outcome_val None) bb84_bool_val bb84_set_val h
              (@start_store (bb84_cvar M) V M (@BVX M) (@BVZ M) (@BVabort M) (@BVP M) bb84_empty_transcript_val
                bb84_bool_val bb84_set_val s)))).
Fact bb84_eb_round_so_psd (EA : @adversary R L HL V Eve) (h : @run_history V M) (K : {set 'I_M}) (pair : 'M[C]_(4 * 2))
    (i : 'I_M) (rho : 'F[HL]_setT) : pair \is den1mx -> rho \is psdlf -> bb84_eb_round_so EA h K pair i rho \is psdlf.
Proof. move=> Hpair Hrho; rewrite /bb84_eb_round_so; case: (i \in K).
  - rewrite scale_soE; apply: psdlfZ.
    + by rewrite lecR mulr_ge0 ?bb84_prep_basis_prob_nonneg.
    + rewrite comp_soE; apply: cp_psdP; apply: replaceso_psd; last exact: Hrho. exact: den1lf_psd (bb84_collect_source_signal_lfun_den1 i Hpair).
  - rewrite scale_soE; apply: psdlfZ.
    + by rewrite lecR bb84_prep_basis_prob_nonneg.
    + rewrite comp_soE; apply: cp_psdP. rewrite comp_soE; apply: cp_psdP; apply: replaceso_psd; last exact: Hrho.
      exact: bb84_signal_lfun_prep_source_branch_psd. Qed.

Fact bb84_eb_implant_so_trlf (K : {set 'I_M}) (j : 'I_nkey) (x : 'F[HL]_setT) : \Tr (bb84_eb_implant_so K j x) = \Tr x.
Proof. have bb84_swap_S_so_trlf : forall (j : 'I_nkey) (i : 'I_M) (x : 'F[HL]_setT), \Tr (bb84_swap_S_so j i x) = \Tr x.
  { move=> {}j i {}x. exact: bitswap_so_trlf. } have bb84_swap_Bq_so_trlf : forall (j : 'I_nkey) (i : 'I_M) (x : 'F[HL]_setT), \Tr (bb84_swap_Bq_so j i x) = \Tr x.
{ clear x j K; move=> j i x. exact: bitswap_so_trlf. } rewrite /bb84_eb_implant_so. case: (bb84_selected_index K j) => [i|]; last by rewrite id_soE. by rewrite comp_soE bb84_swap_S_so_trlf bb84_swap_Bq_so_trlf. Qed.

Fact bb84_eb_implant_so_psd (K : {set 'I_M}) (j : 'I_nkey) (x : 'F[HL]_setT) : x \is psdlf -> bb84_eb_implant_so K j x \is psdlf.
Proof. have bb84_swap_S_so_psd : forall (j : 'I_nkey) (i : 'I_M) (x : 'F[HL]_setT), x \is psdlf -> bb84_swap_S_so j i x \is psdlf.
  { move=> {}j i {}x. exact: bitswap_so_psd. } move=> Hx; rewrite /bb84_eb_implant_so. case: (bb84_selected_index K j) => [i|]; last by rewrite id_soE. by rewrite comp_soE; exact: (bb84_swap_S_so_psd _ _ _ (bb84_swap_Bq_so_psd j i Hx)). Qed.

Local Lemma bb84_eb_round_seq_psd (EA : @adversary R L HL V Eve) (h : @run_history V M) (K : {set 'I_M}) (pair : 'M[C]_(4 * 2))
    (r : seq 'I_M) (rho : 'F[HL]_setT) : pair \is den1mx -> rho \is psdlf -> (\compr_(i <- r) bb84_eb_round_so EA h K pair i) rho \is psdlf.
Proof. move=> Hpair; elim: r rho => [|i r IHr] rho Hrho.
  - by rewrite big_nil id_soE.
  - by rewrite big_cons comp_sorE; apply: IHr; exact: bb84_eb_round_so_psd. Qed.

Local Lemma bb84_eb_implant_seq_psd (K : {set 'I_M}) (r : seq 'I_nkey) (rho : 'F[HL]_setT) :
  rho \is psdlf -> (\compr_(j <- r) bb84_eb_implant_so K j) rho \is psdlf.
Proof. elim: r rho => [|j r IHr] rho Hrho.
  - by rewrite big_nil id_soE.
  - by rewrite big_cons comp_sorE; apply: IHr; exact: bb84_eb_implant_so_psd. Qed.

Local Lemma bb84_eb_implant_seq_trlf (K : {set 'I_M}) (r : seq 'I_nkey) (rho : 'F[HL]_setT) :
  \Tr ((\compr_(j <- r) bb84_eb_implant_so K j) rho) = \Tr rho.
Proof. elim: r rho => [|j r IHr] rho.
  - by rewrite big_nil id_soE.
  - by rewrite big_cons comp_sorE IHr bb84_eb_implant_so_trlf. Qed.

Lemma bb84_collect_prep_basis_prob_le1 (basis : bb84_basis) : bb84_prep_basis_prob P basis <= 1.
Proof. rewrite /bb84_prep_basis_prob; case: basis.
  - by rewrite invf_le1; [rewrite lerDl sqrtr_ge0 | rewrite ltr_wpDr ?ltr01 ?sqrtr_ge0].
  - by rewrite gerBl invr_ge0 addr_ge0 ?ler01 ?sqrtr_ge0. Qed.

Local Lemma bb84_eb_readout_lf_bound1 (i : 'I_M) (basis : bb84_basis) (outcome : option bool) :
  bb84_round_readout_lf dev HE HB i basis outcome \is bound1lf.
Proof. by rewrite /bb84_round_readout_lf -bb84_device_dev_meas_case; exact: bb84_device_dev_meas_any_bound1. Qed.

Local Lemma bb84_eb_readout_so_tr_le (i : 'I_M) (basis : bb84_basis) (outcome : option bool) (x : 'F[HL]_setT) : x \is psdlf -> \Tr (formso
    (liftf_lf (bb84_round_readout_lf dev HE HB i basis outcome)) x) <= \Tr x.
Proof. move=> Hx; have Hbound : liftf_lf (bb84_round_readout_lf dev HE HB i basis outcome) \is bound1lf by rewrite -liftf_lf_bound1E;
  exact: bb84_eb_readout_lf_bound1. have Hcptn : formso (liftf_lf (bb84_round_readout_lf dev HE HB i basis outcome)) \is cptn by rewrite (Bound1Lf_BuildE Hbound) qualifE formso_cp formso_tn. by have /cp_isqoP Htr := Hcptn; exact: Htr. Qed.

Local Lemma bb84_collect_replaceso_trlf (Q : {set L}) (rho' : 'F[HL]_Q) (x : 'F[HL]_setT) : \Tr (replaceso rho' x) = \Tr rho' * \Tr x.
Proof. by rewrite replacesoE appendso_trlf; congr (_ * _); case/cptpP: (@ptraceso_qc R L HL Q (setTfor L)) => _ /tpmapP ->. Qed.

Fact bb84_eb_round_so_tr_le (EA : @adversary R L HL V Eve) (h : @run_history V M) (K : {set 'I_M}) (pair : 'M[C]_(4 * 2))
    (i : 'I_M) (rho : 'F[HL]_setT) : pair \is den1mx -> rho \is psdlf -> \Tr (bb84_eb_round_so EA h K pair i rho) <= \Tr rho.
Proof. have bb84_collect_prep_branch_prob_le1 : forall (basis : bb84_basis), bb84_prep_branch_prob P basis <= 1.
{ clear rho i pair K h EA; move=> basis; rewrite /bb84_prep_branch_prob; apply: mulr_ile1.
  - exact: bb84_prep_basis_prob_nonneg.
  - by rewrite invr_ge0 ler0n.
  - exact: bb84_collect_prep_basis_prob_le1.
  - by rewrite invf_le1 ?ltr0n // ler1n. } move=> Hpair Hrho; rewrite /bb84_eb_round_so. case: (i \in K).
  - rewrite scale_soE linearZ /=. have -> : \Tr ((liftfso (EA (bb84_signal_reg i) (empty_transcript dev)) :o replaceso (bb84_source_signal_lfun HE HB i pair)) rho) = \Tr rho.
    { rewrite comp_soE. have /tpmapP Htp : liftfso (EA (bb84_signal_reg i) (empty_transcript dev)) \is tpmap by apply: liftso_tp.
      by rewrite Htp; exact: replaceso_trlf_den1 (bb84_collect_source_signal_lfun_den1 i Hpair). } apply: ler_piMl; first exact: psdlf_trlf.
      rewrite lecR; apply: mulr_ile1. 1,2: exact: bb84_prep_basis_prob_nonneg. 1,2: exact: bb84_collect_prep_basis_prob_le1.
  - rewrite scale_soE linearZ /= comp_soE; set Y := (liftfso _ :o replaceso _) rho. have HY_psd : Y \is psdlf.
    { rewrite /Y comp_soE; apply: cp_psdP; apply: replaceso_psd; last exact: Hrho. exact: bb84_signal_lfun_prep_source_branch_psd. }
have HY_tr : \Tr Y = (bb84_prep_branch_prob P (bb84_history_alice_basis h i))%:C * \Tr rho.
    { rewrite /Y comp_soE. have /tpmapP Htp : liftfso (EA (bb84_signal_reg i) (empty_transcript dev)) \is tpmap by apply: liftso_tp.
      by rewrite Htp bb84_collect_replaceso_trlf bb84_signal_lfun_prep_source_branch_tr. }
have Hstep : \Tr (formso (liftf_lf (bb84_round_readout_lf dev HE HB i (bb84_history_bob_basis h i) (bb84_history_bob_outcome h i))) Y) <= \Tr Y by exact: bb84_eb_readout_so_tr_le. apply: (@le_trans _ _ ((bb84_prep_basis_prob P (bb84_history_bob_basis h i))%:C * \Tr Y)).
    + by apply: ler_wpM2l; [rewrite lecR bb84_prep_basis_prob_nonneg | exact: Hstep].
    + rewrite HY_tr mulrA; apply: ler_piMl; first exact: psdlf_trlf. rewrite -rmorphM /= lecR. apply: mulr_ile1.
      * exact: bb84_prep_basis_prob_nonneg.
      * exact: bb84_prep_branch_prob_nonneg.
      * exact: bb84_collect_prep_basis_prob_le1.
      * exact: bb84_collect_prep_branch_prob_le1. Qed.

Local Lemma bb84_eb_round_seq_tr_le (EA : @adversary R L HL V Eve) (h : @run_history V M) (K : {set 'I_M}) (pair : 'M[C]_(4 * 2))
    (r : seq 'I_M) (rho : 'F[HL]_setT) : pair \is den1mx -> rho \is psdlf -> \Tr ((\compr_(i <- r) bb84_eb_round_so EA h K pair i) rho) <=
  \Tr rho.
Proof. move=> Hpair; elim: r rho => [|i r IHr] rho Hrho.
  - by rewrite big_nil id_soE lexx.
  - rewrite big_cons comp_sorE; apply: le_trans (bb84_eb_round_so_tr_le EA h K i Hpair Hrho). by apply: IHr; exact: bb84_eb_round_so_psd. Qed.

Definition bb84_eb_full_round_so (EA : @adversary R L HL V Eve) (h : @run_history V M) (pair : 'M[C]_(4 * 2)) (i : 'I_M) : 'SO[HL]_setT :=
  (bb84_prep_basis_prob P (bb84_history_bob_basis h i) * bb84_prep_basis_prob P (bb84_history_alice_basis h i))%:C *:
    (liftfso (EA (bb84_signal_reg i) (empty_transcript dev)) :o replaceso (bb84_source_signal_lfun HE HB i pair)).
Fact bb84_eb_full_round_so_psd (EA : @adversary R L HL V Eve) (h : @run_history V M) (pair : 'M[C]_(4 * 2))
    (i : 'I_M) (rho : 'F[HL]_setT) : pair \is den1mx -> rho \is psdlf -> bb84_eb_full_round_so EA h pair i rho \is psdlf.
Proof. move=> Hpair Hrho; rewrite /bb84_eb_full_round_so scale_soE; apply: psdlfZ.
  - by rewrite lecR mulr_ge0 ?bb84_prep_basis_prob_nonneg.
  - rewrite comp_soE; apply: cp_psdP; apply: replaceso_psd; last exact: Hrho. exact: den1lf_psd (bb84_collect_source_signal_lfun_den1 i Hpair). Qed.

Fact bb84_eb_full_round_so_tr_le (EA : @adversary R L HL V Eve) (h : @run_history V M) (pair : 'M[C]_(4 * 2))
    (i : 'I_M) (rho : 'F[HL]_setT) : pair \is den1mx -> rho \is psdlf -> \Tr (bb84_eb_full_round_so EA h pair i rho) <= \Tr rho.
Proof. have bb84_eb_full_round_so_trace : forall (EA : @adversary R L HL V Eve) (h : @run_history V M) (pair : 'M[C]_(4 * 2)) (i : 'I_M)
  (rho : 'F[HL]_setT), pair \is den1mx -> \Tr (bb84_eb_full_round_so EA h pair i rho) = (bb84_prep_basis_prob P (bb84_history_bob_basis h i)
  * bb84_prep_basis_prob P (bb84_history_alice_basis h i))%:C * \Tr rho.
{ clear rho i pair h EA; move=> EA h pair i rho. move=> Hpair; rewrite /bb84_eb_full_round_so scale_soE linearZ /=. congr (_ * _); rewrite comp_soE. have /tpmapP Htp : liftfso (EA (bb84_signal_reg i) (empty_transcript dev)) \is tpmap by apply: liftso_tp.
  by rewrite Htp; exact: replaceso_trlf_den1 (bb84_collect_source_signal_lfun_den1 i Hpair). } move=> Hpair Hrho; rewrite bb84_eb_full_round_so_trace//. apply: ler_piMl; first exact: psdlf_trlf. rewrite lecR; apply: mulr_ile1.
  1,2: exact: bb84_prep_basis_prob_nonneg. 1,2: exact: bb84_collect_prep_basis_prob_le1. Qed.
Local Lemma bb84_eb_full_round_seq_psd (EA : @adversary R L HL V Eve) (h : @run_history V M) (pair : 'M[C]_(4 * 2))
    (r : seq 'I_M) (rho : 'F[HL]_setT) :
  pair \is den1mx -> rho \is psdlf -> (\compr_(i <- r) bb84_eb_full_round_so EA h pair i) rho \is psdlf.
Proof. move=> Hpair; elim: r rho => [|i r IHr] rho Hrho.
  - by rewrite big_nil id_soE.
  - by rewrite big_cons comp_sorE; apply: IHr; exact: bb84_eb_full_round_so_psd. Qed.
Local Lemma bb84_eb_full_round_seq_tr_le (EA : @adversary R L HL V Eve) (h : @run_history V M) (pair : 'M[C]_(4 * 2))
    (r : seq 'I_M) (rho : 'F[HL]_setT) : pair \is den1mx -> rho \is psdlf ->
  \Tr ((\compr_(i <- r) bb84_eb_full_round_so EA h pair i) rho) <= \Tr rho.
Proof. move=> Hpair; elim: r rho => [|i r IHr] rho Hrho.
  - by rewrite big_nil id_soE lexx.
  - rewrite big_cons comp_sorE. have Hinner : bb84_eb_full_round_so EA h pair i rho \is psdlf by exact: bb84_eb_full_round_so_psd.
    apply: (le_trans (IHr _ Hinner)). exact: bb84_eb_full_round_so_tr_le. Qed.
End CollectBB84.
Section EBPairOfPure.
Variable R : realType.
Notation C := (@hermitian.C R).
Local Notation pidx b := (bb84_prep_index BasisX b).
Local Lemma eb_prep_index_neq : pidx false != pidx true.
Proof. apply/eqP => Heq. have := bb84_prep_bit_of_indexK BasisX false. by rewrite Heq bb84_prep_bit_of_indexK; []. Qed.
Local Lemma eb_sqrt2_sq : ((sqrtC (2%:R : C))^-1)^* * ((sqrtC (2%:R : C))^-1) = ((2%:R)^-1)%:C.
Proof. by rewrite geC0_conj ?invr_ge0 ?sqrtC_ge0 ?ler0n//; rewrite -expr2 exprVn sqrtCK; rewrite fmorphV rmorph_nat. Qed.
Local Lemma eb_sqrt2_sq' : (sqrtC (2%:R : C))^-1 * ((sqrtC (2%:R : C))^-1)^* = ((2%:R)^-1)%:C.
Proof. by rewrite mulrC eb_sqrt2_sq. Qed.
Local Lemma eb_prep_index_neq' : pidx true != pidx false.
Proof. by rewrite eq_sym eb_prep_index_neq. Qed.
Local Lemma eb_tens_mx11 (X : 'M[C]_1) : (delta_mx (0 : 'I_1) (0 : 'I_1) : 'M[C]_1) *t X = X.
Proof. apply/matrixP=> i j. have ei : i = mxtens_index (0 : 'I_1, 0 : 'I_1) by apply/val_inj; rewrite /= ord1.
  have ej : j = mxtens_index (0 : 'I_1, 0 : 'I_1) by apply/val_inj; rewrite /= ord1. by rewrite ei ej tensmxE mxE !eqxx /= mul1r; congr (X _ _); apply/val_inj. Qed.
Local Lemma eb_pair_component_dot (v w : 'cV[C]_2) (b b' : bool) : ((delta_mx (pidx b) (0 : 'I_1) : 'cV[C]_4) *t v)^*t *m
  ((delta_mx (pidx b') (0 : 'I_1) : 'cV[C]_4) *t w) = if pidx b == pidx b' then v^*t *m w else 0.
Proof. rewrite adjmx_tens adjmx_delta tensmx_mul mul_delta_mx_cond; case: eqP => _.
  - by rewrite mulr1n eb_tens_mx11.
  - by rewrite mulr0n tens0mx. Qed.
Local Lemma eb_pair_component_outer (v w : 'cV[C]_2) (b b' : bool) : ((delta_mx (pidx b) (0 : 'I_1) : 'cV[C]_4) *t v) *m
  ((delta_mx (pidx b') (0 : 'I_1) : 'cV[C]_4) *t w)^*t = (delta_mx (pidx b) (pidx b') : 'M[C]_4) *t (v *m w^*t).
Proof. by rewrite adjmx_tens adjmx_delta tensmx_mul mul_delta_mx. Qed.
Local Lemma eb_proj_outer (b b1 b2 : bool) (X : 'M[C]_2) : ((delta_mx (pidx b) (pidx b) : 'M[C]_4) *t (1%:M : 'M[C]_2)) *m
  ((delta_mx (pidx b1) (pidx b2) : 'M[C]_4) *t X) *m ((delta_mx (pidx b) (pidx b) : 'M[C]_4) *t (1%:M : 'M[C]_2)) =
  if (b == b1) && (b2 == b) then (delta_mx (pidx b) (pidx b) : 'M[C]_4) *t X else 0.
Proof. rewrite !tensmx_mul !mul1mx !mulmx1; case: b; case: b1; case: b2 => /=.
  - by rewrite !mul_delta_mx.
  - by rewrite mul_delta_mx (mul_delta_mx_0 _ _ _ eb_prep_index_neq) tens0mx.
  - by rewrite (mul_delta_mx_0 _ _ _ eb_prep_index_neq') mul0mx tens0mx.
  - by rewrite (mul_delta_mx_0 _ _ _ eb_prep_index_neq') mul0mx tens0mx.
  - by rewrite (mul_delta_mx_0 _ _ _ eb_prep_index_neq) mul0mx tens0mx.
  - by rewrite (mul_delta_mx_0 _ _ _ eb_prep_index_neq) mul0mx tens0mx.
  - by rewrite mul_delta_mx (mul_delta_mx_0 _ _ _ eb_prep_index_neq') tens0mx.
  - by rewrite !mul_delta_mx. Qed.
Local Lemma eb_pidx_eq (b b' : bool) : (pidx b == pidx b') = (b == b').
Proof. apply/idP/idP.
  - move=> /eqP H; apply/eqP. by rewrite -(bb84_prep_bit_of_indexK BasisX b) -(bb84_prep_bit_of_indexK BasisX b') H.
  - by move=> /eqP ->. Qed.
Local Lemma eb_proj_matL (b b1 b2 : bool) (X : 'M[C]_2) : ((delta_mx (pidx b) (pidx b) : 'M[C]_4) *t (1%:M : 'M[C]_2)) *m
  ((delta_mx (pidx b1) (pidx b2) : 'M[C]_4) *t X) = if b == b1 then (delta_mx (pidx b) (pidx b2) : 'M[C]_4) *t X else 0.
Proof. rewrite tensmx_mul mul1mx; case: (b =P b1) => [Heq | Hne].
  - by rewrite Heq mul_delta_mx.
  - have Hp : pidx b != pidx b1 by rewrite eb_pidx_eq; apply/eqP. by rewrite (mul_delta_mx_0 _ _ _ Hp) tens0mx. Qed.
Local Lemma eb_proj_matR (a c b : bool) (X : 'M[C]_2) : ((delta_mx (pidx a) (pidx c) : 'M[C]_4) *t X) *m
  ((delta_mx (pidx b) (pidx b) : 'M[C]_4) *t (1%:M : 'M[C]_2)) = if c == b then (delta_mx (pidx a) (pidx b) : 'M[C]_4) *t X else 0.
Proof. rewrite tensmx_mul mulmx1; case: (c =P b) => [Heq | Hne].
  - by rewrite Heq mul_delta_mx.
  - have Hp : pidx c != pidx b by rewrite eb_pidx_eq; apply/eqP. by rewrite (mul_delta_mx_0 _ _ _ Hp) tens0mx. Qed.
Local Lemma eb_delta11 : (delta_mx (0 : 'I_1) (0 : 'I_1) : 'M[C]_1) = 1%:M.
Proof. by apply/matrixP => i j; rewrite !mxE !ord1 !eqxx. Qed.
Local Lemma eb_half_conj : (((2%:R)^-1)%:C : C)^* = ((2%:R)^-1)%:C.
Proof. exact: conjc_real _. Qed.
Local Lemma eb_z_ket_adj_low (zbit : bool) : (bb84_prep_source_z_ket R zbit)^*t *m (delta_mx (pidx false) (0 : 'I_1) : 'cV[C]_4) =
  ((sqrtC (2%:R : C))^-1)^* *: (1%:M : 'M[C]_1).
Proof. rewrite /bb84_prep_source_z_ket adjmxZ -scalemxAl adjmxD mulmxDl adjmxZ -scalemxAl.
  by rewrite !adjmx_delta mul_delta_mx (mul_delta_mx_0 _ _ _ eb_prep_index_neq'); rewrite scaler0 addr0 eb_delta11. Qed.
Local Lemma eb_z_ket_adj_high (zbit : bool) : (bb84_prep_source_z_ket R zbit)^*t *m (delta_mx (pidx true) (0 : 'I_1) : 'cV[C]_4) =
  (((sqrtC (2%:R : C))^-1)^* * bb84_eb_z_sign R zbit) *: (1%:M : 'M[C]_1).
Proof. rewrite /bb84_prep_source_z_ket adjmxZ -scalemxAl adjmxD mulmxDl adjmxZ -scalemxAl. by rewrite !adjmx_delta (mul_delta_mx_0 _ _ _
  eb_prep_index_neq) mul_delta_mx; rewrite add0r eb_delta11 scalerA bb84_eb_z_sign_conj. Qed.
Local Lemma eb_z_proj_ket_low (zbit : bool) : (bb84_prep_source_z_ket R zbit *m (bb84_prep_source_z_ket R zbit)^*t) *m
    (delta_mx (pidx false) (0 : 'I_1) : 'cV[C]_4) = ((sqrtC (2%:R : C))^-1)^* *: bb84_prep_source_z_ket R zbit.
Proof. by rewrite -mulmxA eb_z_ket_adj_low -scalemxAr mulmx1. Qed.
Local Lemma eb_z_proj_ket_high (zbit : bool) : (bb84_prep_source_z_ket R zbit *m (bb84_prep_source_z_ket R zbit)^*t) *m
    (delta_mx (pidx true) (0 : 'I_1) : 'cV[C]_4) = (((sqrtC (2%:R : C))^-1)^* * bb84_eb_z_sign R zbit) *: bb84_prep_source_z_ket R zbit.
Proof. by rewrite -mulmxA eb_z_ket_adj_high -scalemxAr mulmx1. Qed.
Local Lemma eb_tensZr (k : C) (a : 'M[C]_4) (b : 'M[C]_2) : a *t (k *: b) = k *: (a *t b).
Proof. by rewrite -[k *: b]addr0 (linear_tensmx a) tensmx0 !addr0. Qed.
Local Lemma eb_outer_tens (a : 'cV[C]_4) (b : 'cV[C]_2) : (a *t b) *m (a *t b)^*t = (a *m a^*t) *t (b *m b^*t).
Proof. by rewrite adjmx_tens tensmx_mul. Qed.
Local Lemma eb_z_tens_combine (a : 'cV[C]_4) (u w : 'cV[C]_2) (k : C) : a *t u + k *: (a *t w) = a *t (u + k *: w).
Proof. rewrite [u + k *: w]addrC (linear_tensmx a). by rewrite addrC. Qed.
Local Lemma eb_z_proj_tblock_low (v : 'cV[C]_2) (zbit : bool) : bb84_prep_source_z_projector R zbit *m
    ((delta_mx (pidx false) (0 : 'I_1) : 'cV[C]_4) *t v) = ((sqrtC (2%:R : C))^-1)^* *: (bb84_prep_source_z_ket R zbit *t v).
Proof. by rewrite /bb84_prep_source_z_projector mxtens.tensmx_mul mul1mx; rewrite eb_z_proj_ket_low tensmxZl. Qed.
Local Lemma eb_z_proj_tblock_high (v : 'cV[C]_2) (zbit : bool) : bb84_prep_source_z_projector R zbit *m
    ((delta_mx (pidx true) (0 : 'I_1) : 'cV[C]_4) *t v) = (((sqrtC (2%:R : C))^-1)^* * bb84_eb_z_sign R zbit) *:
    (bb84_prep_source_z_ket R zbit *t v).
Proof. by rewrite /bb84_prep_source_z_projector mxtens.tensmx_mul mul1mx; rewrite eb_z_proj_ket_high tensmxZl. Qed.
Local Lemma eb_z_projector_adj (zbit : bool) : (bb84_prep_source_z_projector R zbit)^*t = bb84_prep_source_z_projector R zbit.
Proof. rewrite /bb84_prep_source_z_projector adjmx_tens adjmx1. by rewrite adjmxM adjmxK. Qed.
End EBPairOfPure.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Local Open Scope lfun_scope.
Section BitAddressExtra.
Definition bito (b : bool) : 'I_2 := if b then Ordinal (isT : (1 < 2)%N) else Ordinal (isT : (0 < 2)%N).
Lemma bito_eq (b c : bool) : (bito b == bito c) = (b == c).
Proof. by case: b; case: c. Qed.
Lemma bit_of_ord_upd_bit {d : nat} (x : 'I_(2 ^ d)) (j k : 'I_d) (b : bool) :
  bit_of_ord (upd_bit x j b) k = if k == j then b else bit_of_ord x k.
Proof. by rewrite /bit_of_ord /upd_bit ord_to_bitstringK /upd_str. Qed.
Lemma bit_of_bitstring {d : nat} (s : bitstr d) (j : 'I_d) : bit_of_ord (bitstring_to_ord s) j = s j.
Proof. by rewrite /bit_of_ord ord_to_bitstringK. Qed.
Lemma eq_from_bit_of_ord {d : nat} (x y : 'I_(2 ^ d)) : (forall j, bit_of_ord x j = bit_of_ord y j) -> x = y.
Proof. move=> Hxy; rewrite -(bitstring_to_ordK x) -(bitstring_to_ordK y). by congr bitstring_to_ord; exact/funext. Qed.
Lemma eq_bits_ord {d : nat} (z : 'I_(2 ^ d)) (s : bitstr d) : [forall j, bit_of_ord z j == s j] = (z == bitstring_to_ord s).
Proof. apply/forallP/eqP => [Hall | -> j].
  - by apply: eq_from_bit_of_ord => j; rewrite bit_of_bitstring; exact/eqP/(Hall j).
  - by rewrite bit_of_bitstring. Qed.
Fact bito_bts1 (s : bitstr 1) : bito (s ord0) = bitstring_to_ord s.
Proof. apply: (can_inj (@bitstring_to_ordK 1)). rewrite ord_to_bitstringK; apply/funext => k; rewrite (ord1 k). by move: (s ord0) => c;
  rewrite /ord_to_bitstring /=; case: c. Qed.
Fact bito_bit0 (z : 'I_(2 ^ 1)) : bito (bit_of_ord z ord0) = z.
Proof. by rewrite /bit_of_ord bito_bts1 bitstring_to_ordK. Qed.
End BitAddressExtra.
Section SumHelpers.
Variable V : nmodType.
Fact sum_ord2 (f : 'I_2 -> V) : \sum_(k < 2) f k = f (bito false) + f (bito true).
Proof. rewrite big_ord_recl big_ord_recl big_ord0 addr0. by congr (f _ + f _); exact/val_inj. Qed.
End SumHelpers.
Fact prod_ord2 (T : comNzRingType) (f : 'I_2 -> T) : \prod_(k < 2) f k = f ord0 * f (bito true).
Proof. by rewrite big_ord_recl big_ord1; have -> : lift ord0 ord0 = bito true by apply: val_inj. Qed.
Section BitProdMx.
Variable R : realType.
Notation C := (@hermitian.C R).
Variable d : nat.
Definition bitprod_mx (F : 'I_d -> 'M[C]_2) : 'M[C]_(2 ^ d) := \matrix_(z, z')
    \prod_(j < d) F j (bito (bit_of_ord z j)) (bito (bit_of_ord z' j)).
Lemma bitprod_mxE (F : 'I_d -> 'M[C]_2) (z z' : 'I_(2 ^ d)) : bitprod_mx F z z' =
  \prod_(j < d) F j (bito (bit_of_ord z j)) (bito (bit_of_ord z' j)).
Proof. by rewrite mxE. Qed.
Lemma prodr_ind (P : 'I_d -> bool) : \prod_(j < d) ((P j)%:R : C) = ([forall j, P j])%:R.
Proof. case: (boolP [forall j, P j]) => [/forallP Hall | Hnot].
  - by rewrite big1 => [|j _]; [rewrite mulr1n | rewrite Hall].
  - have [j Hj] : exists j, ~~ P j by move: Hnot; rewrite negb_forall => /existsP. by rewrite (bigD1 j) //= (negbTE Hj) !mulr0n mul0r. Qed.
Lemma bitprod_mx_adj (F : 'I_d -> 'M[C]_2) : (bitprod_mx F)^*t = bitprod_mx (fun j => (F j)^*t).
Proof. by apply/matrixP=> z z'; rewrite adjmxE !mxE rmorph_prod /=; apply: eq_bigr => j _; rewrite adjmxE !mxE. Qed.
Lemma bitprod_mx_mul (F G : 'I_d -> 'M[C]_2) : bitprod_mx F *m bitprod_mx G = bitprod_mx (fun j => F j *m G j).
Proof. have sum_ord2_bool : forall (V : nmodType) (f : 'I_2 -> V), \sum_(k < 2) f k = \sum_(b : bool) f (bito b).
  { move=> V f. by rewrite sum_ord2 big_bool addrC. } apply/matrixP=> z z''; rewrite !mxE. under [RHS]eq_bigr do rewrite mxE sum_ord2_bool.
    rewrite bigA_distr_bigA /=. pose h (w : {ffun 'I_d -> bool}) : 'I_(2 ^ d) := bitstring_to_ord (fun j => w j).
    have hK : forall w j, bit_of_ord (h w) j = w j by move=> w j; rewrite /h bit_of_bitstring. have hbij : bijective h.
  { exists (fun z' => [ffun j => bit_of_ord z' j]).
    - by move=> w; apply/ffunP=> j; rewrite ffunE hK.
    - move=> z'; rewrite /h. have -> : (fun j => [ffun j0 => bit_of_ord z' j0] j) = ord_to_bitstring z' by apply/funext=> j; rewrite ffunE.
      exact: bitstring_to_ordK. } rewrite (reindex h); last exact: onW_bij. by apply: eq_bigr => w _; rewrite !mxE -big_split /=; apply: eq_bigr => j _; rewrite hK. Qed.
Lemma bitprod_mx1 : bitprod_mx (fun _ => 1%:M) = 1%:M.
Proof. apply/matrixP=> z z'; rewrite !mxE. under eq_bigr do rewrite mxE bito_eq. rewrite prodr_ind.
  have -> : [forall j, bit_of_ord z j == bit_of_ord z' j] = (z == z') by rewrite (eq_bits_ord z (ord_to_bitstring z')) bitstring_to_ordK.
  by []. Qed.
Fact bitprod_mx_delta (s t : bitstr d) : bitprod_mx (fun j => delta_mx (bito (s j)) (bito (t j))) =
  delta_mx (bitstring_to_ord s) (bitstring_to_ord t).
Proof. apply/matrixP=> z z'; rewrite !mxE. under eq_bigr do rewrite mxE !bito_eq. rewrite prodr_ind.
  have -> : [forall j, (bit_of_ord z j == s j) && (bit_of_ord z' j == t j)] = ((z == bitstring_to_ord s) && (z' == bitstring_to_ord t)).
  { rewrite -eq_bits_ord -(eq_bits_ord z' t); apply/forallP/andP => [Hall | [/forallP Hs /forallP Ht] j].
    - by split; apply/forallP=> j; case/andP: (Hall j).
    - by rewrite Hs Ht. } by []. Qed.
Lemma bitprod_mx_sum (O : finType) (N : 'I_d -> O -> 'M[C]_2) : \sum_(w : {ffun 'I_d -> O}) bitprod_mx (fun j => N j (w j)) =
  bitprod_mx (fun j => \sum_(o : O) N j o).
Proof. apply/matrixP=> z z'; rewrite summxE !mxE. under [RHS]eq_bigr do rewrite summxE. by rewrite bigA_distr_bigA /=;
  apply: eq_bigr => w _; rewrite mxE. Qed.
Definition bitlift_mx (j : 'I_d) (A : 'M[C]_2) : 'M[C]_(2 ^ d) := bitprod_mx (fun k => if k == j then A else 1%:M).
End BitProdMx.
Fact bitprod_mx_ord1 (R : realType) (F : 'I_1 -> 'M[@hermitian.C R]_2) : bitprod_mx F = F ord0.
Proof. apply/matrixP=> z z'. by rewrite bitprod_mxE big_ord1 !bito_bit0. Qed.
Definition slotupd {T : Type} {d : nat} (F : 'I_d -> T) (j : 'I_d) (A : T) : 'I_d -> T := fun k => if k == j then A else F k.
Fact bitprod_slotupd_ord1 (R : realType) (A : 'M[@hermitian.C R]_2) : bitprod_mx (slotupd (fun _ : 'I_1 => 1%:M) ord0 A) = A.
Proof. by rewrite bitprod_mx_ord1 /slotupd eqxx. Qed.
Section BitswapConj.
Variable R : realType.
Notation C := (@hermitian.C R).
Variables a b : nat.
Variables (jA : 'I_a) (jB : 'I_b).
Lemma bitswap_permE (z : 'I_(2 ^ a * 2 ^ b)) : bitswap_perm jA jB z = bitswap_ordfun jA jB z.
Proof. by rewrite permE. Qed.
Fact bitswap_mx_bitprod_conj (F : 'I_a -> 'M[C]_2) (G : 'I_b -> 'M[C]_2) : bitswap_mx R jA jB *m (bitprod_mx F *t bitprod_mx G) *m
    bitswap_mx R jA jB = bitprod_mx (slotupd F jA (G jB)) *t bitprod_mx (slotupd G jB (F jA)).
Proof. have bitswap_mx_conjE : forall (m : 'M[C]_(2 ^ a * 2 ^ b)) (z z' : 'I_(2 ^ a * 2 ^ b)), (bitswap_mx R jA jB *m m *m bitswap_mx R jA
  jB) z z' = m (bitswap_perm jA jB z) (bitswap_perm jA jB z').
{ clear G F; move=> m z z'. have bitswap_permV : ((bitswap_perm jA jB)^-1)%g = bitswap_perm jA jB.
{ clear z' z m; have Hinv : forall z, bitswap_perm jA jB (bitswap_perm jA jB z) = z.
  { by move=> z; rewrite !bitswap_permE bitswap_ordfunK. } by apply/permP=> z; rewrite -{1}(Hinv z) permK. } rewrite /bitswap_mx -row_permE.
    have -> : row_perm (bitswap_perm jA jB) m *m perm_mx (bitswap_perm jA jB) = col_perm ((bitswap_perm jA jB)^-1)%g (row_perm (bitswap_perm jA jB) m) by rewrite col_permE invgK. by rewrite !mxE bitswap_permV. } apply/matrixP=> z z'; rewrite bitswap_mx_conjE -(mxtens_unindexK z) -(mxtens_unindexK z'). set p := mxtens_unindex z; set p' := mxtens_unindex z'.
    have swapE : forall q : 'I_(2 ^ a) * 'I_(2 ^ b), bitswap_perm jA jB (mxtens_index q) = mxtens_index (bitswap_pairfun jA jB q).
  { by move=> q; rewrite bitswap_permE /bitswap_ordfun mxtens_indexK. } rewrite !swapE !tensmxE !mxE /bitswap_pairfun /= [\prod_(j < a) F j _ _](bigD1 jA) //=. rewrite [\prod_(j < b) G j _ _](bigD1 jB) //= [in RHS](bigD1 jA) //= [in RHS](bigD1 jB) //=.
    rewrite /slotupd !eqxx !bit_of_upd_bit. have -> : \prod_(j < a | j != jA) F j (bito (bit_of_ord (upd_bit p.1 jA (bit_of_ord p.2 jB)) j)) (bito (bit_of_ord (upd_bit p'.1 jA (bit_of_ord p'.2 jB)) j)) = \prod_(j < a | j != jA) F j (bito (bit_of_ord p.1 j)) (bito (bit_of_ord p'.1 j)). { by apply: eq_bigr => j /negbTE Hj; rewrite !bit_of_ord_upd_bit Hj. } have -> : \prod_(j < b | j != jB) G j (bito (bit_of_ord (upd_bit p.2 jB (bit_of_ord p.1 jA)) j)) (bito (bit_of_ord (upd_bit p'.2 jB (bit_of_ord p'.1 jA)) j)) = \prod_(j < b | j != jB) G j (bito (bit_of_ord p.2 j)) (bito (bit_of_ord p'.2 j)). { by apply: eq_bigr => j /negbTE Hj; rewrite !bit_of_ord_upd_bit Hj. }
have -> : \prod_(j < a | j != jA) (if j == jA then G jB else F j) (bito (bit_of_ord p.1 j)) (bito (bit_of_ord p'.1 j)) = \prod_(j < a | j != jA) F j (bito (bit_of_ord p.1 j)) (bito (bit_of_ord p'.1 j)). { by apply: eq_bigr => j /negbTE Hj; rewrite Hj. }
have -> : \prod_(j < b | j != jB) (if j == jB then F jA else G j) (bito (bit_of_ord p.2 j)) (bito (bit_of_ord p'.2 j)) = \prod_(j < b | j != jB) G j (bito (bit_of_ord p.2 j)) (bito (bit_of_ord p'.2 j)).
  { by apply: eq_bigr => j /negbTE Hj; rewrite Hj. } by rewrite mulrACA [in RHS]mulrACA [X in X * _ = _]mulrC. Qed.
End BitswapConj.
Section RegMxLfun.
Variable R : realType.
Notation C := (@hermitian.C R).
Variables (L : finType) (H : L -> @chsType R) (A : {set L}) (d : nat) (dimA : dim ('H[H]_A) = (2 ^ d)%N).
Definition regmx_lf (m : 'M[C]_(2 ^ d)) : 'F[H]_A := mx2h (castmx (esym dimA, esym dimA) m).
Lemma regmx_lf_comp (m m' : 'M[C]_(2 ^ d)) : regmx_lf m \o regmx_lf m' = regmx_lf (m *m m').
Proof. apply/h2mx_inj. by rewrite h2mx_comp !mx2hK castmx_mul. Qed.
Lemma regmx_lf_adj (m : 'M[C]_(2 ^ d)) : (regmx_lf m)^A = regmx_lf (m^*t).
Proof. by apply/h2mx_inj; rewrite h2mx_adj !mx2hK; rewrite (@castmx_mx_mxT _ _ (@adjmx _) _ _ _ _ (esym dimA, esym dimA) m). Qed.
Lemma regmx_lf1 : regmx_lf 1%:M = \1.
Proof. apply/h2mx_inj. rewrite h2mx1 mx2hK. by case: _ / (esym dimA); rewrite castmx_id. Qed.
Lemma regmx_lf_sum (I : finType) (P : pred I) (f : I -> 'M[C]_(2 ^ d)) : regmx_lf (\sum_(i | P i) f i) = \sum_(i | P i) regmx_lf (f i).
Proof. by rewrite /regmx_lf !linear_sum. Qed.
End RegMxLfun.
Section DeferredBB84.
Variable R : realType.
Notation chsType := (@chsType R).
Notation C := (@hermitian.C R).
Variables (P : @bb84_protocol R) (q : R) (dev : bb84_certified_device P q) (LE : finType) (HE : LE -> chsType).
Notation M := (bb84_round_limit P).
Notation LB := bb84_register_index.
Notation HB := (@bb84_register_space R P q dev).
Notation L := (bb84_label M LE LB).
Notation HL := (bb84_label_space HE HB).
Notation V := (bb84_val M (bb84_n P) (bb84_l P) (cd_ir_bits dev) (cd_vseed_count dev) (cd_tag_count dev) (cd_paseed_count dev)).
Notation Eve := (bb84_eve_reg M LE LB).
Notation Sreg := (bb84_S P LE).
Notation Bqreg := (bb84_Bq P LE).
Notation nkey := (bb84_n P).
Notation dimS := (@bb84_dim_S_pow2 R P q dev LE HE).
Notation dimBq := (@bb84_dim_Bq_pow2 R P q dev LE HE).
Notation bobout := {ffun 'I_nkey -> option bool}.
Definition bb84_deferred_alice_lf (x : 'I_(2 ^ nkey)) : 'F[HL]_Sreg := regmx_lf dimS (delta_mx x x).
Definition bb84_deferred_bob_mx (w : bobout) : 'M[C]_(2 ^ nkey) := bitprod_mx (fun j => cd_meas dev BasisX (w j)).
Definition bb84_deferred_bob_lf (w : bobout) : 'F[HL]_Bqreg := regmx_lf dimBq (bb84_deferred_bob_mx w).
Definition bb84_deferred_readout_so (x : 'I_(2 ^ nkey)) (w : bobout) : 'SO[HL]_setT := formso (liftf_lf (bb84_deferred_alice_lf x)) :o
  formso (liftf_lf (bb84_deferred_bob_lf w)).
Fact bb84_deferred_alice_complete : \sum_(x : 'I_(2 ^ nkey)) ((bb84_deferred_alice_lf x)^A \o bb84_deferred_alice_lf x) =
  (\1 : 'F[HL]_Sreg).
Proof. have sum_delta_mx_diag : forall (n : nat), \sum_(x : 'I_n) delta_mx x x = (1%:M : 'M[C]_n).
  { move=> n. apply/matrixP=> i j. rewrite summxE (bigD1 i) //= !mxE eqxx /=. rewrite big1 => [|x Hx]; last first.
  { by rewrite mxE eq_sym (negbTE Hx). }
by rewrite addr0 eq_sym. }
have step : forall x : 'I_(2 ^ nkey), (bb84_deferred_alice_lf x)^A \o bb84_deferred_alice_lf x = regmx_lf dimS (delta_mx x x).
  { move=> x. by rewrite /bb84_deferred_alice_lf regmx_lf_adj regmx_lf_comp adjmx_delta mul_delta_mx. } under eq_bigr do rewrite step.
    by rewrite -regmx_lf_sum sum_delta_mx_diag regmx_lf1. Qed.
Fact bb84_deferred_bob_complete : \sum_(w : bobout) ((bb84_deferred_bob_lf w)^A \o bb84_deferred_bob_lf w) = (\1 : 'F[HL]_Bqreg).
Proof. have sum_option_bool : forall (V : nmodType) (f : option bool -> V), \sum_(o : option bool) f o = f None + (f (Some false) + f (Some
  true)).
  { move=> V f. rewrite (bigD1 None) //=. congr (_ + _). rewrite (reindex_onto some (odflt false)); last by case=> [b|].
    rewrite (eq_bigl xpredT) => [|b]; last by rewrite eqxx. by rewrite big_bool addrC. }
have step : forall w : bobout, (bb84_deferred_bob_lf w)^A \o bb84_deferred_bob_lf w = regmx_lf dimBq (bitprod_mx (fun j => (cd_meas dev BasisX (w j))^*t *m cd_meas dev BasisX (w j))).
  { move=> w. rewrite /bb84_deferred_bob_lf regmx_lf_adj regmx_lf_comp. by rewrite /bb84_deferred_bob_mx bitprod_mx_adj bitprod_mx_mul. }
under eq_bigr do rewrite step. rewrite -regmx_lf_sum. rewrite (bitprod_mx_sum (fun (j : 'I_nkey) (o : option bool) => (cd_meas dev BasisX o)^*t *m cd_meas dev BasisX o)). have -> : (fun j : 'I_nkey => \sum_(o : option bool) (cd_meas dev BasisX o)^*t *m cd_meas dev BasisX o) = (fun _ : 'I_nkey => 1%:M : 'M[C]_2).
  { apply/funext=> j. rewrite sum_option_bool addrA. exact: (cd_meas_complete dev BasisX). } by rewrite bitprod_mx1 regmx_lf1. Qed.
Local Lemma bb84_deferred_alice_lift_complete : \sum_(x : 'I_(2 ^ nkey)) ((liftf_lf (bb84_deferred_alice_lf x))^A \o
     liftf_lf (bb84_deferred_alice_lf x)) = (\1 : 'F[HL]_setT).
Proof. under eq_bigr do rewrite -liftf_lf_adj -liftf_lf_comp. by rewrite -linear_sum /= bb84_deferred_alice_complete liftf_lf1. Qed.
Local Lemma bb84_deferred_bob_lift_complete : \sum_(w : bobout) ((liftf_lf (bb84_deferred_bob_lf w))^A \o
     liftf_lf (bb84_deferred_bob_lf w)) = (\1 : 'F[HL]_setT).
Proof. under eq_bigr do rewrite -liftf_lf_adj -liftf_lf_comp. by rewrite -linear_sum /= bb84_deferred_bob_complete liftf_lf1. Qed.
Fact bb84_outcome_of_inv (v : V) (o : option bool) : bb84_outcome_of v = Some o -> v = bb84_outcome_val o.
Proof. by case: v => [|[|[|[o'|]]]] //= [->]. Qed.
Definition bb84_reround_choice (c : @round_choice V) (yb : bool) (o : option bool) : ((V * V) * (V * V))%type :=
  ((choice_a c, bb84_bit_val yb), (choice_b c, bb84_outcome_val o)).
Definition bb84_key_reround (h : @run_history V M) (x : 'I_(2 ^ nkey)) (w : bobout) : @run_history V M :=
  ([ffun i => if i \in bb84_key_set h then (if (insub (index i (enum (bb84_key_set h))) : option 'I_nkey) is Some j then
         bb84_reround_choice (h.1 i) (bit_of_ord x j) (w j) else h.1 i) else h.1 i], h.2).
Lemma bb84_key_reroundE (h : @run_history V M) (x : 'I_(2 ^ nkey)) (w : bobout) (i : 'I_M) : (bb84_key_reround h x w).1 i =
  (if i \in bb84_key_set h then (if (insub (index i (enum (bb84_key_set h))) : option 'I_nkey) is Some j then
        bb84_reround_choice (h.1 i) (bit_of_ord x j) (w j) else h.1 i) else h.1 i).
Proof. exact: ffunE. Qed.
Lemma bb84_key_reround_key_set (h : @run_history V M) (x : 'I_(2 ^ nkey)) (w : bobout) :
  bb84_key_set (bb84_key_reround h x w) = bb84_key_set h.
Proof. by []. Qed.
Lemma bb84_key_reround_notin (h : @run_history V M) (x : 'I_(2 ^ nkey)) (w : bobout) (i : 'I_M) :
  i \notin bb84_key_set h -> (bb84_key_reround h x w).1 i = h.1 i.
Proof. by move=> Hi; rewrite bb84_key_reroundE (negbTE Hi). Qed.
Fact bb84_key_slot_lt (K : {set 'I_M}) (i : 'I_M) : #|K| = nkey -> i \in K -> (index i (enum K) < nkey)%N.
Proof. move=> HK Hi; by rewrite -HK cardE index_mem mem_enum. Qed.
Fact bb84_selected_index_index (K : {set 'I_M}) (i : 'I_M) (j : 'I_nkey) :
  #|K| = nkey -> i \in K -> index i (enum K) = j -> bb84_selected_index K j = Some i.
Proof. move=> HK Hi Hj; rewrite /bb84_selected_index (nth_map i); last first.
  { by rewrite -Hj -cardE HK bb84_key_slot_lt. } by rewrite -Hj nth_index // mem_enum. Qed.
Lemma bb84_selected_index_inv (K : {set 'I_M}) (i : 'I_M) (j : 'I_nkey) :
  #|K| = nkey -> bb84_selected_index K j = Some i -> index i (enum K) = j.
Proof. move=> HK; rewrite /bb84_selected_index (nth_map i); last first.
  { by rewrite -cardE HK ltn_ord. } move=> [Hnth]; by rewrite -Hnth index_uniq -?cardE ?HK ?ltn_ord ?enum_uniq. Qed.
Fact bb84_key_reround_y (h : @run_history V M) (x : 'I_(2 ^ nkey)) (w : bobout) (i : 'I_M) (j : 'I_nkey) :
  #|bb84_key_set h| = nkey -> i \in bb84_key_set h -> index i (enum (bb84_key_set h)) = j -> hist_y (bb84_key_reround h x w) i =
    (bb84_bit_val (bit_of_ord x j) : V) /\ hist_y' (bb84_key_reround h x w) i = (bb84_outcome_val (w j) : V).
Proof. move=> HK Hi Hj; rewrite /hist_y /hist_y' /hist_choice bb84_key_reroundE Hi. case: insubP => [u _ Hu | ]; last first.
  { by rewrite Hj ltn_ord. } have -> : u = j by apply/val_inj; rewrite Hu Hj. by split. Qed.
Fact bb84_key_reround_reround (h : @run_history V M) (x x' : 'I_(2 ^ nkey)) (w w' : bobout) :
  bb84_key_reround (bb84_key_reround h x w) x' w' = bb84_key_reround h x' w'.
Proof. congr (_ , _). by apply/ffunP=> i; rewrite !ffunE bb84_key_reround_key_set; case HiK: (i \in bb84_key_set h) => //; case: insubP. Qed.
Definition bb84_key_data_x (h : @run_history V M) : 'I_(2 ^ nkey) := bitstring_to_ord (fun j =>
    if bb84_selected_index (bb84_key_set h) j is Some i then bb84_history_alice_bit h i else false).
Definition bb84_key_data_w (h : @run_history V M) : bobout := [ffun j => if bb84_selected_index (bb84_key_set h) j is Some i
    then bb84_history_bob_outcome h i else None].
Lemma bb84_key_data_xE (h : @run_history V M) (j : 'I_nkey) : bit_of_ord (bb84_key_data_x h) j =
  (if bb84_selected_index (bb84_key_set h) j is Some i then bb84_history_alice_bit h i else false).
Proof. exact: bit_of_bitstring. Qed.
Lemma bb84_key_data_wE (h : @run_history V M) (j : 'I_nkey) : bb84_key_data_w h j = (if bb84_selected_index (bb84_key_set h) j is Some i
   then bb84_history_bob_outcome h i else None).
Proof. exact: ffunE. Qed.
Fact bb84_key_reroundK (h : @run_history V M) : bb84_history_decoded h -> #|bb84_key_set h| = nkey ->
  bb84_key_reround h (bb84_key_data_x h) (bb84_key_data_w h) = h.
Proof. have bb84_bit_of_inv : forall (v : V) (b : bool), bb84_bit_of v = Some b -> v = bb84_bit_val b.
  { move=> v b. by case: v => [|[|[c|]]] //= [->]. } move=> Hdec HK; rewrite [in RHS](surjective_pairing h); congr (_ , _). apply/ffunP=> i; rewrite ffunE. case HiK: (i \in bb84_key_set h); last by []. case: insubP => [j _ Hj | ]; last by [].
    have Hidx : index i (enum (bb84_key_set h)) = j by rewrite -Hj. have Hsel : bb84_selected_index (bb84_key_set h) j = Some i by apply: bb84_selected_index_index. rewrite bb84_key_data_xE bb84_key_data_wE Hsel. have Hround : bb84_history_round_decoded h i by move/forallP: Hdec; exact. case/and4P: Hround => _ Hy _ Hy'. have Hyc : choice_y (h.1 i) = (bb84_bit_val (bb84_history_alice_bit h i) : V).
  { apply: bb84_bit_of_inv. rewrite /bb84_history_alice_bit. exact: (bb84_bit_of_decoded Hy). }
have Hy'c : choice_y' (h.1 i) = (bb84_outcome_val (bb84_history_bob_outcome h i) : V).
  { apply: bb84_outcome_of_inv. rewrite /bb84_history_bob_outcome. exact: (bb84_outcome_of_decoded Hy'). } by move: Hyc Hy'c; case: (h.1 i) => [[a y] [b y']]; rewrite /choice_y /choice_y' /= => -> ->; []. Qed.
Fact bb84_history_round_decoded_reround2 (h : @run_history V M) (x x' : 'I_(2 ^ nkey)) (w w' : bobout) (i : 'I_M) :
  bb84_history_round_decoded (bb84_key_reround h x w) i = bb84_history_round_decoded (bb84_key_reround h x' w') i.
Proof. rewrite /bb84_history_round_decoded /hist_a /hist_y /hist_b /hist_y' /hist_choice !bb84_key_reroundE.
  by case: (i \in bb84_key_set h) => //; case: insubP. Qed.
Fact bb84_history_decoded_reround2 (h : @run_history V M) (x x' : 'I_(2 ^ nkey)) (w w' : bobout) :
  bb84_history_decoded (bb84_key_reround h x w) = bb84_history_decoded (bb84_key_reround h x' w').
Proof. apply/eq_forallb=> i. exact: bb84_history_round_decoded_reround2. Qed.
Fact bb84_eb_history_state_reround (EA : @adversary R L HL V Eve) (pair : 'M[C]_(4 * 2))
    (h : @run_history V M) (x x' : 'I_(2 ^ nkey)) (w w' : bobout) (rho : 'F[HL]_setT) :
  bb84_eb_history_state EA pair (bb84_key_reround h x w) rho = bb84_eb_history_state EA pair (bb84_key_reround h x' w') rho.
Proof. have bb84_eb_round_so_reround : forall (EA : @adversary R L HL V Eve) (h : @run_history V M) (x x' : 'I_(2 ^ nkey)) (w w' : bobout)
  (pair : 'M[C]_(4 * 2)) (i : 'I_M), bb84_eb_round_so EA (bb84_key_reround h x w) (bb84_key_set h) pair i = bb84_eb_round_so EA (bb84_key_reround h x' w') (bb84_key_set h) pair i.
{ clear rho w' w x' x h pair EA; move=> EA h x x' w w' pair i. have bb84_key_reround_a : forall (h : @run_history V M) (x : 'I_(2 ^ nkey)) (w : bobout) (i : 'I_M), hist_a (bb84_key_reround h x w) i = hist_a h i.
{ clear i pair w' w x' x h EA; move=> h x w i. rewrite /hist_a /hist_choice bb84_key_reroundE. by case: (i \in bb84_key_set h) => //; case: insubP. } have bb84_key_reround_b : forall (h : @run_history V M) (x : 'I_(2 ^ nkey)) (w : bobout) (i : 'I_M), hist_b (bb84_key_reround h x w) i = hist_b h i.
{ clear i pair w' w x' x h EA; move=> h x w i. rewrite /hist_b /hist_choice bb84_key_reroundE. by case: (i \in bb84_key_set h) => //; case: insubP. } rewrite /bb84_eb_round_so; case HiK: (i \in bb84_key_set h).
  - by rewrite /bb84_history_bob_basis /bb84_history_alice_basis !bb84_key_reround_a !bb84_key_reround_b.
  - rewrite /bb84_history_bob_basis /bb84_history_alice_basis /bb84_history_bob_outcome /bb84_history_alice_bit /hist_a /hist_b /hist_y /hist_y' /hist_choice. by rewrite !(bb84_key_reround_notin _ _ (negbT HiK)). } rewrite /bb84_eb_history_state !bb84_key_reround_key_set (bb84_history_decoded_reround2 h x x' w w'). case: (bb84_history_decoded (bb84_key_reround h x' w') && (#|bb84_key_set h| == nkey)); last by []. have Hcomp : (\compr_(i <- enum 'I_M) bb84_eb_round_so EA (bb84_key_reround h x w) (bb84_key_set h) pair i) = (\compr_(i <- enum 'I_M) bb84_eb_round_so EA (bb84_key_reround h x' w') (bb84_key_set h) pair i).
  { apply: eq_bigr => i _. exact: bb84_eb_round_so_reround. } have Happ := congr1 (fun E : 'SO[HL]_setT => E rho) Hcomp.
    exact: (congr1 (fun t : 'F[HL]_setT => (\compr_(j <- enum 'I_nkey) bb84_eb_implant_so dev HE (bb84_key_set h) j) t) Happ). Qed.
Definition bb84_mixed_round_so (EA : @adversary R L HL V Eve) (h : @run_history V M) (K : {set 'I_M}) (i : 'I_M) : 'SO[HL]_setT :=
  if i \in K then (bb84_prep_basis_prob P (bb84_history_bob_basis h i))%:C *: (formso (liftf_lf (bb84_round_readout_lf dev HE HB i
          (bb84_history_bob_basis h i) (bb84_history_bob_outcome h i))) :o bb84_round_source_update_so EA h i) else
    (bb84_prep_basis_prob P (bb84_history_bob_basis h i))%:C *: (formso (liftf_lf (bb84_round_readout_lf dev HE HB i
          (bb84_history_bob_basis h i) (bb84_history_bob_outcome h i))) :o (liftfso (EA (bb84_signal_reg i) (empty_transcript dev)) :o
        replaceso (bb84_signal_lfun HE HB i (bb84_prep_source_branch dev (bb84_history_alice_basis h i) (bb84_history_alice_bit h i))))).
Definition bb84_mixed_history_state (EA : @adversary R L HL V Eve) (h : @run_history V M) (rho : 'F[HL]_setT) : 'F[HL]_setT :=
  if bb84_history_decoded h && (#|bb84_key_set h| == nkey) then (\compr_(i <- enum 'I_M) bb84_mixed_round_so EA h (bb84_key_set h) i) rho
  else 0.
End DeferredBB84.
Section PtrSupport.
Variable R : realType.
Notation C := (@hermitian.C R).
Definition bb84_src_low_proj (b : bool) : 'M[C]_4 := delta_mx (bb84_prep_index BasisX b) (bb84_prep_index BasisX b) +
  delta_mx (bb84_prep_index BasisZ b) (bb84_prep_index BasisZ b).
Definition bb84_src_x_span : 'M[C]_4 := delta_mx (bb84_prep_index BasisX false) (bb84_prep_index BasisX false) +
  delta_mx (bb84_prep_index BasisX true) (bb84_prep_index BasisX true).
Definition bb84_eb_pair_ptr_ok (pair : 'M[C]_(4 * 2)) : Prop := (bb84_src_x_span *t (1%:M : 'M[C]_2)) *m pair *m
    (bb84_src_x_span *t (1%:M : 'M[C]_2)) = pair.
Lemma bb84_prep_index_XX (b b' : bool) : (bb84_prep_index BasisX b == bb84_prep_index BasisX b') = (b == b').
Proof. by case: b; case: b'; rewrite /bb84_prep_index -val_eqE /= !inordK. Qed.
Fact bb84_prep_index_valX (b : bool) : val (bb84_prep_index BasisX b) = nat_of_bool b.
Proof. by case: b; rewrite /bb84_prep_index /= inordK. Qed.
Fact bb84_prep_index_valZ (b : bool) : val (bb84_prep_index BasisZ b) = (2 + nat_of_bool b)%N.
Proof. by case: b; rewrite /bb84_prep_index /= inordK. Qed.
Fact bb84_src_low_proj_bitlift (b : bool) : bitlift_mx bb84_src_ptr_slot (delta_mx (bito b) (bito b)) = bb84_src_low_proj b.
Proof. apply/matrixP => i j; rewrite /bitlift_mx bitprod_mxE prod_ord2. have -> : (if ord0 == bb84_src_ptr_slot then delta_mx (bito b) (bito
  b) else 1%:M) = (1%:M : 'M[C]_2) by []. have -> : (if bito true == bb84_src_ptr_slot then delta_mx (bito b) (bito b) else 1%:M) = delta_mx (bito b) (bito b) by []. rewrite /bb84_src_low_proj !mxE !bito_eq -!val_eqE. rewrite !bb84_prep_index_valX !bb84_prep_index_valZ /bit_of_ord !ord_to_bitstring_valE; case: i => vi Hi; case: j => vj Hj; move: Hi Hj. case: vi => [|[|[|[|vi']]]] Hi.
  all: case: vj => [|[|[|[|vj']]]] Hj. all: case: b. all: rewrite /= ?mulr1n ?mulr0n ?mul0r ?mul1r ?mulr0 ?mulr1 ?add0r ?addr0. all: by []. Qed.
Fact bb84_src_low_proj_adj (b : bool) : (bb84_src_low_proj b)^*t = bb84_src_low_proj b.
Proof. by rewrite /bb84_src_low_proj adjmxD !adjmx_delta. Qed.
Fact bb84_src_x_span_deltaL (b b' : bool) : bb84_src_x_span *m delta_mx (bb84_prep_index BasisX b) (bb84_prep_index BasisX b') =
  delta_mx (bb84_prep_index BasisX b) (bb84_prep_index BasisX b').
Proof. by rewrite /bb84_src_x_span mulmxDl !mul_delta_mx_cond !bb84_prep_index_XX; case: b; rewrite /= mulr1n mulr0n ?addr0 ?add0r. Qed.
Fact bb84_src_x_span_deltaR (b b' : bool) : delta_mx (bb84_prep_index BasisX b) (bb84_prep_index BasisX b') *m bb84_src_x_span =
  delta_mx (bb84_prep_index BasisX b) (bb84_prep_index BasisX b').
Proof. by rewrite /bb84_src_x_span mulmxDr !mul_delta_mx_cond !bb84_prep_index_XX; case: b'; rewrite /= mulr1n mulr0n ?addr0 ?add0r. Qed.
Fact bb84_src_low_span (b : bool) : bb84_src_low_proj b *m bb84_src_x_span =
  delta_mx (bb84_prep_index BasisX b) (bb84_prep_index BasisX b).
Proof. have bb84_prep_index_ZX : forall (b b' : bool), (bb84_prep_index BasisZ b == bb84_prep_index BasisX b') = false.
  { move=> {}b b'. by case: b; case: b'; rewrite /bb84_prep_index -val_eqE /= !inordK. }
rewrite /bb84_src_low_proj mulmxDl bb84_src_x_span_deltaR. by rewrite /bb84_src_x_span mulmxDr !mul_delta_mx_cond !bb84_prep_index_ZX; rewrite !mulr0n !addr0. Qed.
Fact bb84_src_span_low (b : bool) : bb84_src_x_span *m bb84_src_low_proj b =
  delta_mx (bb84_prep_index BasisX b) (bb84_prep_index BasisX b).
Proof. have bb84_src_x_span_adj : bb84_src_x_span^*t = bb84_src_x_span. { clear b; by rewrite /bb84_src_x_span adjmxD !adjmx_delta. }
by rewrite -[LHS]adjmxK adjmxM bb84_src_low_proj_adj bb84_src_x_span_adj; rewrite bb84_src_low_span adjmx_delta. Qed.
Fact bb84_src_x_span_conj_delta (b b' : bool) (Y : 'M[C]_2) : (bb84_src_x_span *t (1%:M : 'M[C]_2)) *m
    ((delta_mx (bb84_prep_index BasisX b) (bb84_prep_index BasisX b') : 'M[C]_4) *t Y) *m (bb84_src_x_span *t (1%:M : 'M[C]_2)) =
  (delta_mx (bb84_prep_index BasisX b) (bb84_prep_index BasisX b') : 'M[C]_4) *t Y.
Proof. by rewrite !tensmx_mul !mul1mx mulmx1; rewrite bb84_src_x_span_deltaL bb84_src_x_span_deltaR. Qed.
End PtrSupport.
Section DeferredKeyRoundCollapse.
Variable R : realType.
Notation chsType := (@chsType R).
Notation C := (@hermitian.C R).
Variables (P : @bb84_protocol R) (q : R) (dev : bb84_certified_device P q) (LE : finType) (HE : LE -> chsType).
Notation M := (bb84_round_limit P).
Notation LB := bb84_register_index.
Notation HB := (@bb84_register_space R P q dev).
Notation L := (bb84_label M LE LB).
Notation HL := (bb84_label_space HE HB).
Notation V := (bb84_val M (bb84_n P) (bb84_l P) (cd_ir_bits dev) (cd_vseed_count dev) (cd_tag_count dev) (cd_paseed_count dev)).
Notation Eve := (bb84_eve_reg M LE LB).
Notation nkey := (bb84_n P).
Fact bb84_eb_pair_low_proj_branch (pair : 'M[C]_(4 * 2)) (b : bool) : bb84_eb_pair_ptr_ok pair -> bb84_eb_pair_x_branch_ok dev pair ->
  (bb84_src_low_proj R b *t (1%:M : 'M[C]_2)) *m pair *m (bb84_src_low_proj R b *t (1%:M : 'M[C]_2)) = ((2%:R)^-1)%:C *:
    ((delta_mx (bb84_prep_index BasisX b) (bb84_prep_index BasisX b) : 'M[C]_4) *t cd_rho dev BasisX b).
Proof. move=> Hptr Hbr. have Hls : (bb84_src_low_proj R b *t (1%:M : 'M[C]_2)) *m (bb84_src_x_span R *t (1%:M : 'M[C]_2)) = (delta_mx
  (bb84_prep_index BasisX b) (bb84_prep_index BasisX b) : 'M[C]_4) *t (1%:M : 'M[C]_2).
  { by rewrite tensmx_mul mulmx1 bb84_src_low_span. } have Hsl : (bb84_src_x_span R *t (1%:M : 'M[C]_2)) *m (bb84_src_low_proj R b *t (1%:M : 'M[C]_2)) = (delta_mx (bb84_prep_index BasisX b) (bb84_prep_index BasisX b) : 'M[C]_4) *t (1%:M : 'M[C]_2).
  { by rewrite tensmx_mul mulmx1 bb84_src_span_low. } by rewrite -{1}Hptr !mulmxA Hls; rewrite -[X in X = _]mulmxA Hsl; exact: (Hbr b). Qed.
Local Lemma bb84_ss_lfun_comp (i : 'I_M) (m m' : 'M[C]_(4 * 2)) : bb84_source_signal_lfun HE HB i m \o bb84_source_signal_lfun HE HB i m' =
  bb84_source_signal_lfun HE HB i (m *m m').
Proof. apply: (@biprod_mx_inj R L HL _ _ (bb84_source_signal_disjoint LE LB i)). rewrite biprod_mx_comp /bb84_source_signal_lfun (biprod_mxK
  (bb84_source_signal_disjoint LE LB i)). by rewrite !(biprod_mxK (bb84_source_signal_disjoint LE LB i)) castmx_mul. Qed.
Local Lemma bb84_ss_lfun_adj (i : 'I_M) (m : 'M[C]_(4 * 2)) : (bb84_source_signal_lfun HE HB i m)^A =
  bb84_source_signal_lfun HE HB i (m^*t).
Proof. apply: (@biprod_mx_inj R L HL _ _ (bb84_source_signal_disjoint LE LB i)). rewrite biprod_mx_adj /bb84_source_signal_lfun !biprod_mxK.
  by rewrite (@castmx_mx_mxT _ _ (@adjmx _) _ _ _ _ (esym (f_equal2 muln (bb84_source_reg_dim HE HB i) (bb84_signal_reg_dim HE HB i)), esym (f_equal2 muln (bb84_source_reg_dim HE HB i) (bb84_signal_reg_dim HE HB i))) m). Qed.
Local Lemma bb84_ss_lfunZ (i : 'I_M) (c : C) (m : 'M[C]_(4 * 2)) : bb84_source_signal_lfun HE HB i (c *: m) =
  c *: bb84_source_signal_lfun HE HB i m.
Proof. rewrite /bb84_source_signal_lfun linearZ /=. by rewrite biprod_of_mxZ. Qed.
Local Lemma bb84_signal_lfun_one (i : 'I_M) : bb84_signal_lfun HE HB i (1%:M : 'M[C]_2) = \1.
Proof. by apply/h2mx_inj; rewrite h2mx1 /bb84_signal_lfun mx2hK; case: _ / (esym (bb84_signal_reg_dim HE HB i)); rewrite castmx_id. Qed.
Local Lemma bb84_source_lift_ss (i : 'I_M) (A : 'M[C]_4) : liftf_lf (bb84_source_lfun HE HB i A) =
  liftf_lf (bb84_source_signal_lfun HE HB i (A *t (1%:M : 'M[C]_2))).
Proof. by rewrite bb84_source_signal_lfun_tens liftf_lf_sdot; rewrite bb84_signal_lfun_one liftf_lf1 comp_lfun1r. Qed.
Local Lemma bb84_replacesoZ_so (Q : {set L}) (a : C) (rho : 'F[HL]_Q) : replaceso (a *: rho) = a *: replaceso rho.
Proof. apply/superopP => x. by rewrite replacesoZ scale_soE. Qed.
Local Lemma formso_liftf_replaceso (Q : {set L}) (f g : 'F[HL]_Q) : formso (liftf_lf f) :o replaceso g = replaceso ((f \o g \o f^A)%VF).
Proof. by apply/superopP => x; rewrite comp_soE replacesoE formsoE -liftf_lf_adj appendso_comp_keep; rewrite -replacesoE. Qed.
Local Lemma bb84_ss_formso_replaceso (i : 'I_M) (m r : 'M[C]_(4 * 2)) : formso (liftf_lf (bb84_source_signal_lfun HE HB i m)) :o
    replaceso (bb84_source_signal_lfun HE HB i r) = replaceso (bb84_source_signal_lfun HE HB i (m *m r *m m^*t)).
Proof. rewrite formso_liftf_replaceso bb84_ss_lfun_adj !bb84_ss_lfun_comp. by []. Qed.
Fact bb84_collect_attack_dis_source (i i' : 'I_M) : [disjoint @bb84_signal_reg M LE LB i' :|: Eve & @bb84_source_reg M LE LB i].
Proof. rewrite disjointUX /bb84_source_reg /bb84_signal_reg /bb84_eve_reg disjoint1X disjointX1 !inE /bb84_source_label /bb84_signal_label.
  by []. Qed.
Fact bb84_eb_key_round_collapse (EA : @adversary R L HL V Eve) (h : @run_history V M) (K : {set 'I_M}) (pair : 'M[C]_(4 * 2)) (i : 'I_M) :
  bb84_eb_pair_ptr_ok pair -> bb84_eb_pair_x_branch_ok dev pair -> i \in K ->
  bb84_history_alice_basis h i = BasisX -> bb84_history_bob_basis h i = BasisX -> formso (liftf_lf (bb84_signal_lfun HE HB i
      (cd_meas dev BasisX (bb84_history_bob_outcome h i)))) :o (formso (liftf_lf (bb84_source_lfun HE HB i
      (bb84_src_low_proj R (bb84_history_alice_bit h i)))) :o bb84_eb_round_so EA h K pair i) = bb84_mixed_round_so EA h K i.
Proof. have bb84_source_formso_attack_compC : forall (EA : @adversary R L HL V Eve) (i i' : 'I_M) (v : V) (f : 'F[HL]_(@bb84_source_reg M LE
  LB i)), formso (liftf_lf f) :o liftfso (EA (bb84_signal_reg i') v) = liftfso (EA (bb84_signal_reg i') v) :o formso (liftf_lf f).
{ clear i pair K h EA; move=> EA i i' v f. rewrite -liftfso_formso. by apply: liftfso_compC; rewrite disjoint_sym; exact: bb84_collect_attack_dis_source. } move=> Hptr Hbr HiK Ha Hb; rewrite /bb84_eb_round_so /bb84_mixed_round_so HiK Ha Hb; rewrite /bb84_round_source_update_so Ha. have -> : bb84_round_readout_lf dev HE HB i BasisX (bb84_history_bob_outcome h i) = bb84_signal_lfun HE HB i (cd_meas dev BasisX (bb84_history_bob_outcome h i)).
  { by rewrite /bb84_round_readout_lf; case: (bb84_history_bob_outcome h i). } rewrite !comp_soZr.
    set meas := formso (liftf_lf (bb84_signal_lfun HE HB i (cd_meas dev BasisX (bb84_history_bob_outcome h i)))).
    set proj := formso (liftf_lf (bb84_source_lfun HE HB i (bb84_src_low_proj R (bb84_history_alice_bit h i)))).
    set att := liftfso (EA (bb84_signal_reg i) (empty_transcript dev)). have Hcore : proj :o (att :o replaceso (bb84_source_signal_lfun HE HB i pair)) = ((2%:R)^-1)%:C *: (att :o replaceso (bb84_source_signal_lfun HE HB i ((delta_mx (bb84_prep_index BasisX (bb84_history_alice_bit h i)) (bb84_prep_index BasisX (bb84_history_alice_bit h i)) : 'M[C]_4) *t cd_rho dev BasisX (bb84_history_alice_bit h i)))).
  { rewrite comp_soA /proj bb84_source_formso_attack_compC -comp_soA. rewrite bb84_source_lift_ss bb84_ss_formso_replaceso adjmx_tens bb84_src_low_proj_adj adjmx1 (bb84_eb_pair_low_proj_branch _ Hptr Hbr). by rewrite bb84_ss_lfunZ bb84_replacesoZ_so comp_soZr. }
rewrite Hcore bb84_prep_source_signal_branchE bb84_ss_lfunZ bb84_replacesoZ_so !comp_soZr !scalerA; congr (_ *: _).
    by rewrite -!rmorphM /=; congr ((_)%:C); rewrite /bb84_prep_branch_prob mulrA. Qed.
Fact bb84_eb_nonkey_round_collapse (EA : @adversary R L HL V Eve) (h : @run_history V M) (K : {set 'I_M})
    (pair : 'M[C]_(4 * 2)) (i : 'I_M) : i \notin K -> bb84_eb_round_so EA h K pair i = bb84_mixed_round_so EA h K i.
Proof. move=> HiK; by rewrite /bb84_eb_round_so /bb84_mixed_round_so (negbTE HiK). Qed.
End DeferredKeyRoundCollapse.
Section BitswapIntertwine.
Variable R : realType.
Notation C := (@hermitian.C R).
Variables a b : nat.
Variables (jA : 'I_a) (jB : 'I_b).
Lemma bitswap_mx_intertwineL (F : 'I_a -> 'M[C]_2) : (bitprod_mx F *t (1%:M : 'M[C]_(2 ^ b))) *m bitswap_mx R jA jB = bitswap_mx R jA jB *m
  (bitprod_mx (slotupd F jA (1%:M : 'M[C]_2)) *t bitprod_mx (slotupd (fun _ : 'I_b => (1%:M : 'M[C]_2)) jB (F jA))).
Proof. have bitswap_mx_invol : bitswap_mx R jA jB *m bitswap_mx R jA jB = 1%:M.
  { rewrite /bitswap_mx -perm_mxM. have -> : (bitswap_perm jA jB * bitswap_perm jA jB)%g = 1%g.
  { apply/permP=> z. by rewrite permM !bitswap_permE bitswap_ordfunK perm1. }
by rewrite perm_mx1. }
have Hconj := bitswap_mx_bitprod_conj jA jB F (fun _ : 'I_b => (1%:M : 'M[C]_2)). rewrite bitprod_mx1 in Hconj.
    rewrite -Hconj !mulmxA bitswap_mx_invol mul1mx. by []. Qed.
End BitswapIntertwine.
Section DeferredSwapTransport.
Variable R : realType.
Notation chsType := (@chsType R).
Notation C := (@hermitian.C R).
Variables (P : @bb84_protocol R) (q : R) (dev : bb84_certified_device P q) (LE : finType) (HE : LE -> chsType).
Notation M := (bb84_round_limit P).
Notation LB := bb84_register_index.
Notation HB := (@bb84_register_space R P q dev).
Notation L := (bb84_label M LE LB).
Notation HL := (@bb84_label_space R M LE LB HE HB).
Notation V := (bb84_val M (bb84_n P) (bb84_l P) (cd_ir_bits dev) (cd_vseed_count dev) (cd_tag_count dev) (cd_paseed_count dev)).
Notation Eve := (bb84_eve_reg M LE LB).
Notation Sreg := (bb84_S P LE).
Notation Bqreg := (bb84_Bq P LE).
Notation nkey := (bb84_n P).
Notation dimS := (@bb84_dim_S_pow2 R P q dev LE HE).
Notation dimBq := (@bb84_dim_Bq_pow2 R P q dev LE HE).
Definition bb84_Ssrc_lfun (i : 'I_M) (m : 'M[C]_(2 ^ nkey * 2 ^ 2)) : 'F[HL]_(Sreg :|: @bb84_source_reg M LE LB i) :=
  biprod_of_mx (bb84_collect_disS_source LE i) (castmx (esym (f_equal2 muln dimS (bb84_dim_source_pow2 dev HE i)),
        esym (f_equal2 muln dimS (bb84_dim_source_pow2 dev HE i))) m).
Local Lemma bb84_Ssrc_lfun_comp (i : 'I_M) (m m' : 'M[C]_(2 ^ nkey * 2 ^ 2)) : bb84_Ssrc_lfun i m \o bb84_Ssrc_lfun i m' =
  bb84_Ssrc_lfun i (m *m m').
Proof. apply: (@biprod_mx_inj R L HL _ _ (bb84_collect_disS_source LE i)). rewrite biprod_mx_comp /bb84_Ssrc_lfun (biprod_mxK
  (bb84_collect_disS_source LE i)). by rewrite (biprod_mxK (bb84_collect_disS_source LE i)) (biprod_mxK (bb84_collect_disS_source LE i)); rewrite castmx_mul. Qed.
Local Lemma bb84_Ssrc_lfun_tens (i : 'I_M) (A : 'M[C]_(2 ^ nkey)) (B : 'M[C]_(2 ^ 2)) : bb84_Ssrc_lfun i (A *t B) =
  (sdot_lfun (regmx_lf dimS A) (bb84_source_lfun HE HB i B) : 'F[HL]_(Sreg :|: @bb84_source_reg M LE LB i)).
Proof. apply: (@biprod_mx_inj R L HL _ _ (bb84_collect_disS_source LE i)). rewrite biprod_mxK biprod_mx_sdot /bb84_Ssrc_lfun /regmx_lf
  /bb84_source_lfun !mx2hK. rewrite -(@castmx_tensmx R _ _ _ _ _ _ _ _ (esym dimS) (esym dimS) (esym (bb84_source_reg_dim HE HB i)) (esym (bb84_source_reg_dim HE HB i)) A B). by congr (castmx (_, _) _); exact: eq_irrelevance. Qed.
Local Lemma bb84_source_lfun_one (i : 'I_M) : bb84_source_lfun HE HB i (1%:M : 'M[C]_4) = \1.
Proof. by apply/h2mx_inj; rewrite h2mx1 /bb84_source_lfun mx2hK; case: _ / (esym (bb84_source_reg_dim HE HB i)); rewrite castmx_id. Qed.
Local Lemma bb84_S_lift_Ssrc (i : 'I_M) (A : 'M[C]_(2 ^ nkey)) : liftf_lf (regmx_lf dimS A) =
  liftf_lf (bb84_Ssrc_lfun i (A *t (1%:M : 'M[C]_(2 ^ 2)))).
Proof. by rewrite bb84_Ssrc_lfun_tens liftf_lf_sdot bb84_source_lfun_one; rewrite liftf_lf1 comp_lfun1r. Qed.
Local Lemma bb84_source_lift_Ssrc (i : 'I_M) (B : 'M[C]_(2 ^ 2)) : liftf_lf (bb84_source_lfun HE HB i B) =
  liftf_lf (bb84_Ssrc_lfun i ((1%:M : 'M[C]_(2 ^ nkey)) *t B)).
Proof. rewrite bb84_Ssrc_lfun_tens liftf_lf_sdot regmx_lf1. by rewrite liftf_lf1 comp_lfun1l. Qed.
Local Lemma liftf_lf_comp_transport (S : {set L}) (a b c d e : 'F[HL]_S) : a \o b = c \o (d \o e) -> liftf_lf a \o liftf_lf b =
  liftf_lf c \o (liftf_lf d \o liftf_lf e).
Proof. by move=> H; rewrite -!liftf_lf_comp H. Qed.
Local Lemma bb84_Ssrc_lfun_comp_transport (i : 'I_M)
    (A B C D E : 'M[C]_(2 ^ nkey * 2 ^ 2)) :
  A *m B = C *m (D *m E) -> bb84_Ssrc_lfun i A \o bb84_Ssrc_lfun i B =
  bb84_Ssrc_lfun i C \o (bb84_Ssrc_lfun i D \o bb84_Ssrc_lfun i E).
Proof.
  move=> H; rewrite bb84_Ssrc_lfun_comp.
  rewrite bb84_Ssrc_lfun_comp bb84_Ssrc_lfun_comp.
  by rewrite H.
Qed.
Fact bb84_swap_S_transport (j : 'I_nkey) (i : 'I_M) (F : 'I_nkey -> 'M[C]_2) : formso (liftf_lf (regmx_lf dimS (bitprod_mx F))) :o
    bb84_swap_S_so dev HE j i = bb84_swap_S_so dev HE j i :o (formso (liftf_lf (regmx_lf dimS
      (bitprod_mx (slotupd F j (1%:M : 'M[C]_2))))) :o formso (liftf_lf (bb84_source_lfun HE HB i
      (bitprod_mx (slotupd (fun _ : 'I_2 => (1%:M : 'M[C]_2)) bb84_src_ptr_slot (F j)))))).
Proof. have bb84_swap_S_soE : forall (j : 'I_nkey) (i : 'I_M), bb84_swap_S_so dev HE j i = formso (liftf_lf (bb84_Ssrc_lfun i (bitswap_mx R
  j bb84_src_ptr_slot))).
{ clear F i j; move=> j i. by []. } rewrite bb84_swap_S_soE !formso_comp; congr formso. rewrite !(bb84_S_lift_Ssrc i) (bb84_source_lift_Ssrc i); apply: liftf_lf_comp_transport. by apply: bb84_Ssrc_lfun_comp_transport; rewrite tensmx_mul mul1mx mulmx1; exact: bitswap_mx_intertwineL. Qed.
Definition bb84_Bqsig_lfun (i : 'I_M) (m : 'M[C]_(2 ^ nkey * 2 ^ 1)) : 'F[HL]_(Bqreg :|: @bb84_signal_reg M LE LB i) :=
  biprod_of_mx (bb84_collect_disBq_signal LE i) (castmx (esym (f_equal2 muln dimBq (bb84_dim_signal_pow2 dev HE i)),
        esym (f_equal2 muln dimBq (bb84_dim_signal_pow2 dev HE i))) m).
Local Lemma bb84_Bqsig_lfun_comp (i : 'I_M) (m m' : 'M[C]_(2 ^ nkey * 2 ^ 1)) : bb84_Bqsig_lfun i m \o bb84_Bqsig_lfun i m' =
  bb84_Bqsig_lfun i (m *m m').
Proof. apply: (@biprod_mx_inj R L HL _ _ (bb84_collect_disBq_signal LE i)). rewrite biprod_mx_comp /bb84_Bqsig_lfun (biprod_mxK
  (bb84_collect_disBq_signal LE i)). by rewrite (biprod_mxK (bb84_collect_disBq_signal LE i)) (biprod_mxK (bb84_collect_disBq_signal LE i)); rewrite castmx_mul. Qed.
Local Lemma bb84_Bqsig_lfun_tens (i : 'I_M) (A : 'M[C]_(2 ^ nkey)) (B : 'M[C]_(2 ^ 1)) : bb84_Bqsig_lfun i (A *t B) =
  (sdot_lfun (regmx_lf dimBq A) (bb84_signal_lfun HE HB i B) : 'F[HL]_(Bqreg :|: @bb84_signal_reg M LE LB i)).
Proof. apply: (@biprod_mx_inj R L HL _ _ (bb84_collect_disBq_signal LE i)). rewrite biprod_mxK biprod_mx_sdot /bb84_Bqsig_lfun /regmx_lf
  /bb84_signal_lfun !mx2hK. rewrite -(@castmx_tensmx R _ _ _ _ _ _ _ _ (esym dimBq) (esym dimBq) (esym (bb84_signal_reg_dim HE HB i)) (esym (bb84_signal_reg_dim HE HB i)) A B). by congr (castmx (_, _) _); exact: eq_irrelevance. Qed.
Local Lemma bb84_signal_lfun_one1 (i : 'I_M) : bb84_signal_lfun HE HB i (1%:M : 'M[C]_2) = \1.
Proof. by apply/h2mx_inj; rewrite h2mx1 /bb84_signal_lfun mx2hK; case: _ / (esym (bb84_signal_reg_dim HE HB i)); rewrite castmx_id. Qed.
Local Lemma bb84_Bq_lift_Bqsig (i : 'I_M) (A : 'M[C]_(2 ^ nkey)) : liftf_lf (regmx_lf dimBq A) =
  liftf_lf (bb84_Bqsig_lfun i (A *t (1%:M : 'M[C]_(2 ^ 1)))).
Proof. by rewrite bb84_Bqsig_lfun_tens liftf_lf_sdot bb84_signal_lfun_one1; rewrite liftf_lf1 comp_lfun1r. Qed.
Local Lemma bb84_signal_lift_Bqsig (i : 'I_M) (B : 'M[C]_(2 ^ 1)) : liftf_lf (bb84_signal_lfun HE HB i B) =
  liftf_lf (bb84_Bqsig_lfun i ((1%:M : 'M[C]_(2 ^ nkey)) *t B)).
Proof. rewrite bb84_Bqsig_lfun_tens liftf_lf_sdot regmx_lf1. by rewrite liftf_lf1 comp_lfun1l. Qed.
Local Lemma bb84_Bqsig_lfun_comp_transport (i : 'I_M)
    (A B C D E : 'M[C]_(2 ^ nkey * 2 ^ 1)) :
  A *m B = C *m (D *m E) -> bb84_Bqsig_lfun i A \o bb84_Bqsig_lfun i B =
  bb84_Bqsig_lfun i C \o (bb84_Bqsig_lfun i D \o bb84_Bqsig_lfun i E).
Proof.
  move=> H; rewrite bb84_Bqsig_lfun_comp.
  rewrite bb84_Bqsig_lfun_comp bb84_Bqsig_lfun_comp.
  by rewrite H.
Qed.
Fact bb84_swap_Bq_transport (j : 'I_nkey) (i : 'I_M) (G : 'I_nkey -> 'M[C]_2) : formso (liftf_lf (regmx_lf dimBq (bitprod_mx G))) :o
    bb84_swap_Bq_so dev HE j i = bb84_swap_Bq_so dev HE j i :o (formso (liftf_lf (regmx_lf dimBq
      (bitprod_mx (slotupd G j (1%:M : 'M[C]_2))))) :o formso (liftf_lf (bb84_signal_lfun HE HB i (G j)))).
Proof. have bb84_swap_Bq_soE : forall (j : 'I_nkey) (i : 'I_M), bb84_swap_Bq_so dev HE j i = formso (liftf_lf (bb84_Bqsig_lfun i (bitswap_mx
  R j ord0))).
{ clear G i j; move=> j i. by []. } rewrite bb84_swap_Bq_soE !formso_comp; congr formso.
  rewrite !(bb84_Bq_lift_Bqsig i) -[G j]bitprod_slotupd_ord1 (bb84_signal_lift_Bqsig i); apply: liftf_lf_comp_transport.
  by apply: bb84_Bqsig_lfun_comp_transport; rewrite tensmx_mul mul1mx mulmx1; exact: bitswap_mx_intertwineL. Qed.
Lemma bitprod_mx_eq (d : nat) (F1 F2 : 'I_d -> 'M[C]_2) : F1 =1 F2 -> bitprod_mx F1 = bitprod_mx F2.
Proof. move=> H; apply/matrixP=> z z'; rewrite !mxE. by apply: eq_bigr=> j _; rewrite H. Qed.
Lemma comp_so_comprC (X : 'SO[HL]_setT) (Y : 'I_nkey -> 'SO[HL]_setT) (l : seq 'I_nkey) :
  (forall j, j \in l -> X :o Y j = Y j :o X) -> X :o (\compr_(j <- l) Y j) = (\compr_(j <- l) Y j) :o X.
Proof. elim: l => [|j0 l' IH] Hc.
  - by rewrite big_nil comp_so1r comp_so1l.
  - rewrite big_cons comp_soErl comp_soA. rewrite IH; last by move=> j Hj; apply: Hc; rewrite in_cons Hj orbT.
    by rewrite -comp_soA Hc ?in_cons ?eqxx //; rewrite comp_soA. Qed.
Fact comp_so_compr_comprC (X Y : 'I_nkey -> 'SO[HL]_setT) (l : seq 'I_nkey) :
  (forall j j', X j :o Y j' = Y j' :o X j) -> (\compr_(j <- l) X j) :o (\compr_(j <- l) Y j)
  = (\compr_(j <- l) Y j) :o (\compr_(j <- l) X j).
Proof. move=> H; apply/esym; rewrite comp_so_comprC.
  - by [].
  - move=> j Hj; apply/esym; rewrite comp_so_comprC.
    + by [].
    + by move=> j' _; rewrite H. Qed.
Section PeelGen.
Variables (rd : ('I_nkey -> 'M[C]_2) -> 'SO[HL]_setT) (impl : 'I_nkey -> 'SO[HL]_setT)
          (em : ('I_nkey -> 'M[C]_2) -> 'I_nkey -> 'SO[HL]_setT) (F : 'I_nkey -> 'M[C]_2).
Hypotheses (Hext : forall F1 F2, F1 =1 F2 -> rd F1 = rd F2) (Hemloc : forall F1 F2 j, F1 j = F2 j -> em F1 j = em F2 j).
Hypothesis Hpeel : forall (F0 : 'I_nkey -> 'M[C]_2) (j : 'I_nkey), rd F0 :o impl j = impl j :o (rd (slotupd F0 j (1%:M)) :o em F0 j).
Hypotheses (Hcomm1 : forall j j' : 'I_nkey, j != j' -> impl j :o em F j' = em F j' :o impl j).
Hypotheses (Hcomm2 : forall j j' : 'I_nkey, j != j' -> em F j :o em F j' = em F j' :o em F j).
Lemma peel_gen (l : seq 'I_nkey) : uniq l -> rd F :o (\compr_(j <- l) impl j) = (\compr_(j <- l) impl j)
    :o (rd (fun k => if k \in l then (1%:M) else F k) :o (\compr_(j <- l) em F j)).
Proof. elim: l => [|j0 l' IH].
  - by move=> _; rewrite !big_nil comp_so1l !comp_so1r; apply: Hext => k /=.
  - move=> /= /andP[Hj0 Hun]. rewrite !big_cons !comp_soErl. rewrite [X in X = _]comp_soA (IH Hun). set CI := (\compr_(j <- l') impl j); set CE := (\compr_(j <- l') em F j). set A0 := (rd (fun k => if k \in l' then 1%:M else F k)); set A1 := (rd (fun k => if k \in j0 :: l' then 1%:M else F k)). have Hc1 : impl j0 :o CE = CE :o impl j0.
    { rewrite /CE; apply: comp_so_comprC => j Hj. by apply: Hcomm1; apply/eqP => e; rewrite e Hj in Hj0. }
have Hc2 : em F j0 :o CE = CE :o em F j0.
    { rewrite /CE; apply: comp_so_comprC => j Hj. by apply: Hcomm2; apply/eqP => e; rewrite e Hj in Hj0. }
have HrdeF : rd (slotupd (fun k => if k \in l' then 1%:M else F k) j0 (1%:M)) = A1.
    { rewrite /A1; apply: Hext => k; rewrite /slotupd in_cons. by case: (k == j0). } have HemeF : em (fun k => if k \in l' then 1%:M else F k) j0 = em F j0 by apply: Hemloc; rewrite (negbTE Hj0).
    rewrite -[(CI :o (A0 :o CE)) :o impl j0]comp_soA -[(A0 :o CE) :o impl j0]comp_soA. rewrite -Hc1 [A0 :o (impl j0 :o CE)]comp_soA /A0 Hpeel HrdeF HemeF -[(impl j0 :o (A1 :o em F j0)) :o CE]comp_soA. by rewrite -[(A1 :o em F j0) :o CE]comp_soA Hc2; rewrite -[(CI :o impl j0) :o (A1 :o (CE :o em F j0))]comp_soA. Qed.
End PeelGen.
Fact pk_dis_source_Bqsignal (i' i : 'I_M) : [disjoint @bb84_source_reg M LE LB i' & Bqreg :|: @bb84_signal_reg M LE LB i].
Proof. rewrite disjointXU /bb84_Bq /bb84_reg /bb84_bridge_reg /bb84_source_reg /bb84_signal_reg !disjoint1X !inE /bb84_bridge_label
  /bb84_source_label /bb84_signal_label. by []. Qed.
Fact pk_dis_Sreg_Bqsignal (i : 'I_M) : [disjoint Sreg & Bqreg :|: @bb84_signal_reg M LE LB i].
Proof. rewrite disjointXU /bb84_S /bb84_Bq /bb84_reg /bb84_bridge_reg /bb84_signal_reg !disjoint1X !inE /bb84_bridge_label
  /bb84_signal_label. by []. Qed.
Fact pk_dis_source_Ssource {i' i : 'I_M} (Hii : i' != i) : [disjoint @bb84_source_reg M LE LB i' & Sreg :|: @bb84_source_reg M LE LB i].
Proof. rewrite disjointXU /bb84_S /bb84_reg /bb84_bridge_reg /bb84_source_reg !disjoint1X !inE /bb84_bridge_label /bb84_source_label.
  by rewrite !(inj_eq (@inr_inj _ _)) !(inj_eq (@inl_inj _ _)) Hii. Qed.
Lemma pk_dis_source_source (i i' : 'I_M) : i' != i -> [disjoint @bb84_source_reg M LE LB i' & @bb84_source_reg M LE LB i].
Proof. move=> Hii; rewrite /bb84_source_reg disjoint1X !inE /bb84_source_label. by rewrite !(inj_eq (@inr_inj _ _)) !(inj_eq (@inl_inj _
  _)). Qed.
Fact pk_dis_Bqreg_Ssource (i : 'I_M) : [disjoint Bqreg & Sreg :|: @bb84_source_reg M LE LB i].
Proof. rewrite disjointXU /bb84_S /bb84_Bq /bb84_reg /bb84_bridge_reg /bb84_source_reg !disjoint1X !inE /bb84_bridge_label
  /bb84_source_label. by []. Qed.
Fact pk_dis_signal_Bqsignal {i' i : 'I_M} (Hii : i' != i) : [disjoint @bb84_signal_reg M LE LB i' & Bqreg :|: @bb84_signal_reg M LE LB i].
Proof. rewrite disjointXU /bb84_Bq /bb84_reg /bb84_bridge_reg /bb84_signal_reg !disjoint1X !inE /bb84_bridge_label /bb84_signal_label.
  by rewrite !(inj_eq (@inl_inj _ _)) Hii. Qed.
Fact pk_dis_signal_Ssource (i' i : 'I_M) : [disjoint @bb84_signal_reg M LE LB i' & Sreg :|: @bb84_source_reg M LE LB i].
Proof. rewrite disjointXU /bb84_S /bb84_reg /bb84_bridge_reg /bb84_source_reg /bb84_signal_reg !disjoint1X !inE /bb84_bridge_label
  /bb84_source_label /bb84_signal_label. by []. Qed.
Lemma pk_dis_signal_signal (i i' : 'I_M) : i' != i -> [disjoint @bb84_signal_reg M LE LB i' & @bb84_signal_reg M LE LB i].
Proof. by move=> Hii; rewrite /bb84_signal_reg disjoint1X !inE /bb84_signal_label; rewrite !(inj_eq (@inl_inj _ _)). Qed.
Lemma pk_dis_source_signal (i i' : 'I_M) : [disjoint @bb84_source_reg M LE LB i & @bb84_signal_reg M LE LB i'].
Proof. by rewrite /bb84_source_reg /bb84_signal_reg disjoint1X !inE /bb84_source_label /bb84_signal_label; []. Qed.
Lemma pk_swapBq_source {i' i : 'I_M} (j : 'I_nkey) (f : 'F[HL]_(@bb84_source_reg M LE LB i')) :
  bb84_swap_Bq_so dev HE j i :o formso (liftf_lf f) = formso (liftf_lf f) :o bb84_swap_Bq_so dev HE j i.
Proof. apply: bitswap_so_formso_compC; exact: (pk_dis_source_Bqsignal i' i). Qed.
Fact pk_swapS_source {i' i : 'I_M} (Hii : i' != i) (j : 'I_nkey) (f : 'F[HL]_(@bb84_source_reg M LE LB i')) :
  bb84_swap_S_so dev HE j i :o formso (liftf_lf f) = formso (liftf_lf f) :o bb84_swap_S_so dev HE j i.
Proof. apply: bitswap_so_formso_compC; exact: (pk_dis_source_Ssource Hii). Qed.
Fact pk_swapBq_signal {i' i : 'I_M} (Hii : i' != i) (j : 'I_nkey) (f : 'F[HL]_(@bb84_signal_reg M LE LB i')) :
  bb84_swap_Bq_so dev HE j i :o formso (liftf_lf f) = formso (liftf_lf f) :o bb84_swap_Bq_so dev HE j i.
Proof. apply: bitswap_so_formso_compC; exact: (pk_dis_signal_Bqsignal Hii). Qed.
Lemma pk_formso_compC (S T : {set L}) (f : 'F[HL]_S) (g : 'F[HL]_T) : [disjoint S & T] -> formso (liftf_lf f) :o formso (liftf_lf g)
  = formso (liftf_lf g) :o formso (liftf_lf f).
Proof. by move=> dis; rewrite !formso_comp liftf_lf_compC. Qed.
Lemma pk_sel_inj (K : {set 'I_M}) (j j' : 'I_nkey) (i i' : 'I_M) :
  #|K| = nkey -> j != j' -> bb84_selected_index K j = Some i -> bb84_selected_index K j' = Some i' -> i' != i.
Proof. move=> HK Hjj Hi Hi'; have E1 := bb84_selected_index_inv HK Hi. have E2 := bb84_selected_index_inv HK Hi'. apply/eqP => e;
  move: Hjj => /eqP; apply; apply: ord_inj. by rewrite -E1 -E2 e. Qed.
Definition bb84_src_emit (K : {set 'I_M}) (F0 : 'I_nkey -> 'M[C]_2) (j : 'I_nkey) : 'SO[HL]_setT :=
  if bb84_selected_index K j is Some i then formso (liftf_lf (bb84_source_lfun HE HB i
      (bitprod_mx (slotupd (fun _ : 'I_2 => (1%:M : 'M[C]_2)) bb84_src_ptr_slot (F0 j))))) else \:1.
Definition bb84_sig_emit (K : {set 'I_M}) (G0 : 'I_nkey -> 'M[C]_2) (j : 'I_nkey) : 'SO[HL]_setT :=
  if bb84_selected_index K j is Some i then formso (liftf_lf (bb84_signal_lfun HE HB i (G0 j))) else \:1.
Definition bb84_S_readout (F0 : 'I_nkey -> 'M[C]_2) : 'SO[HL]_setT := formso (liftf_lf (regmx_lf dimS (bitprod_mx F0))).
Definition bb84_Bq_readout (G0 : 'I_nkey -> 'M[C]_2) : 'SO[HL]_setT := formso (liftf_lf (regmx_lf dimBq (bitprod_mx G0))).
Fact bb84_readout_peelS (K : {set 'I_M}) (F : 'I_nkey -> 'M[C]_2) :
  #|K| = nkey -> bb84_S_readout F :o (\compr_(j <- enum 'I_nkey) bb84_eb_implant_so dev HE K j)
  = (\compr_(j <- enum 'I_nkey) bb84_eb_implant_so dev HE K j) :o (\compr_(j <- enum 'I_nkey) bb84_src_emit K F j).
Proof. have pk_swapBq_Sreg : forall (i : 'I_M) (j : 'I_nkey) (f : 'F[HL]_Sreg), bb84_swap_Bq_so dev HE j i :o formso (liftf_lf f) = formso
  (liftf_lf f) :o bb84_swap_Bq_so dev HE j i.
{ clear F K; move=> i j f. apply: bitswap_so_formso_compC; exact: (pk_dis_Sreg_Bqsignal i). } move=> HK.
  have Hext : forall F1 F2 : 'I_nkey -> 'M[C]_2, F1 =1 F2 -> bb84_S_readout F1 = bb84_S_readout F2.
  { move=> F1 F2 H; rewrite /bb84_S_readout. by rewrite (bitprod_mx_eq H). } have Hemloc : forall (F1 F2 : 'I_nkey -> 'M[C]_2) (j : 'I_nkey), F1 j = F2 j -> bb84_src_emit K F1 j = bb84_src_emit K F2 j.
  { move=> F1 F2 j Hj; rewrite /bb84_src_emit. by case: (bb84_selected_index K j) => // i; rewrite Hj. }
have Hpeel : forall (F0 : 'I_nkey -> 'M[C]_2) (j : 'I_nkey), bb84_S_readout F0 :o bb84_eb_implant_so dev HE K j = bb84_eb_implant_so dev HE K j :o (bb84_S_readout (slotupd F0 j (1%:M)) :o bb84_src_emit K F0 j).
  { move=> F0 j. have [i Hi] := bb84_selected_index_some (esym HK) j. rewrite /bb84_eb_implant_so /bb84_src_emit Hi /bb84_S_readout.
    rewrite [X in X = _]comp_soA bb84_swap_S_transport. set SS := (bb84_swap_S_so dev HE j i). set SB := (bb84_swap_Bq_so dev HE j i).
    set RA' := (formso (liftf_lf (regmx_lf dimS (bitprod_mx (slotupd F0 j (1%:M)))))). set SRC := (formso (liftf_lf (bb84_source_lfun HE HB i (bitprod_mx (slotupd (fun _ : 'I_2 => (1%:M : 'M[C]_2)) bb84_src_ptr_slot (F0 j)))))). rewrite -[(SS :o (RA' :o SRC)) :o SB]comp_soA -[(RA' :o SRC) :o SB]comp_soA. rewrite -pk_swapBq_source [RA' :o (SB :o SRC)]comp_soA -pk_swapBq_Sreg -[(SB :o RA') :o SRC]comp_soA.
    by rewrite comp_soA. } have Hcomm1 : forall j j' : 'I_nkey, j != j' -> bb84_eb_implant_so dev HE K j :o bb84_src_emit K F j' = bb84_src_emit K F j' :o bb84_eb_implant_so dev HE K j.
  { move=> j j' Hjj. rewrite /bb84_eb_implant_so /bb84_src_emit. case Hj: (bb84_selected_index K j) => [i|]; last by rewrite comp_so1l comp_so1r. case Hj': (bb84_selected_index K j') => [i'|]; last by rewrite comp_so1r comp_so1l.
    have Hii : i' != i := pk_sel_inj HK Hjj Hj Hj'. set SS := (bb84_swap_S_so dev HE j i). set SB := (bb84_swap_Bq_so dev HE j i).
    set SRC' := (formso (liftf_lf (bb84_source_lfun HE HB i' (bitprod_mx (slotupd (fun _ : 'I_2 => (1%:M : 'M[C]_2)) bb84_src_ptr_slot (F j')))))). rewrite -[(SS :o SB) :o SRC']comp_soA pk_swapBq_source [SS :o (SRC' :o SB)]comp_soA (pk_swapS_source Hii).
    by rewrite -comp_soA. } have Hcomm2 : forall j j' : 'I_nkey, j != j' -> bb84_src_emit K F j :o bb84_src_emit K F j' = bb84_src_emit K F j' :o bb84_src_emit K F j.
  { move=> j j' Hjj. rewrite /bb84_src_emit. case Hj: (bb84_selected_index K j) => [i|]; last by rewrite comp_so1l comp_so1r.
    case Hj': (bb84_selected_index K j') => [i'|]; last by rewrite comp_so1r comp_so1l. have Hii : i' != i := pk_sel_inj HK Hjj Hj Hj'.
    apply: pk_formso_compC; apply: pk_dis_source_source. by rewrite eq_sym. } have Hpg := peel_gen Hext Hemloc Hpeel Hcomm1 Hcomm2 (enum_uniq _). rewrite Hpg. have He1 : (fun k : 'I_nkey => if k \in enum 'I_nkey then (1%:M : 'M[C]_2) else F k) = (fun _ => (1%:M : 'M[C]_2)).
  { by apply/funext => k; rewrite mem_enum. } by rewrite He1 /bb84_S_readout bitprod_mx1 regmx_lf1 liftf_lf1 formso1 comp_so1l. Qed.
Fact bb84_readout_peelBq (K : {set 'I_M}) (G : 'I_nkey -> 'M[C]_2) :
  #|K| = nkey -> bb84_Bq_readout G :o (\compr_(j <- enum 'I_nkey) bb84_eb_implant_so dev HE K j)
  = (\compr_(j <- enum 'I_nkey) bb84_eb_implant_so dev HE K j) :o (\compr_(j <- enum 'I_nkey) bb84_sig_emit K G j).
Proof. have pk_swapS_Bqreg : forall (i : 'I_M) (j : 'I_nkey) (f : 'F[HL]_Bqreg), bb84_swap_S_so dev HE j i :o formso (liftf_lf f) = formso
  (liftf_lf f) :o bb84_swap_S_so dev HE j i.
{ clear G K; move=> i j f. apply: bitswap_so_formso_compC; exact: (pk_dis_Bqreg_Ssource i). } have pk_swapS_signal : forall (i' i : 'I_M) (j : 'I_nkey) (f : 'F[HL]_(@bb84_signal_reg M LE LB i')), bb84_swap_S_so dev HE j i :o formso (liftf_lf f) = formso (liftf_lf f) :o bb84_swap_S_so dev HE j i.
{ clear G K; move=> i' i j f. apply: bitswap_so_formso_compC; exact: (pk_dis_signal_Ssource i' i). } move=> HK.
  have Hext : forall G1 G2 : 'I_nkey -> 'M[C]_2, G1 =1 G2 -> bb84_Bq_readout G1 = bb84_Bq_readout G2.
  { move=> G1 G2 H; rewrite /bb84_Bq_readout. by rewrite (bitprod_mx_eq H). } have Hemloc : forall (G1 G2 : 'I_nkey -> 'M[C]_2) (j : 'I_nkey), G1 j = G2 j -> bb84_sig_emit K G1 j = bb84_sig_emit K G2 j.
  { move=> G1 G2 j Hj; rewrite /bb84_sig_emit. by case: (bb84_selected_index K j) => // i; rewrite Hj. }
have Hpeel : forall (G0 : 'I_nkey -> 'M[C]_2) (j : 'I_nkey), bb84_Bq_readout G0 :o bb84_eb_implant_so dev HE K j = bb84_eb_implant_so dev HE K j :o (bb84_Bq_readout (slotupd G0 j (1%:M)) :o bb84_sig_emit K G0 j).
  { move=> G0 j. have [i Hi] := bb84_selected_index_some (esym HK) j. rewrite /bb84_eb_implant_so /bb84_sig_emit Hi /bb84_Bq_readout.
    set SS := (bb84_swap_S_so dev HE j i). set SB := (bb84_swap_Bq_so dev HE j i). set RB := (formso (liftf_lf (regmx_lf dimBq (bitprod_mx G0)))). set RB' := (formso (liftf_lf (regmx_lf dimBq (bitprod_mx (slotupd G0 j (1%:M)))))).
    set SIG := (formso (liftf_lf (bb84_signal_lfun HE HB i (G0 j)))). rewrite [X in X = _]comp_soA.
    rewrite -pk_swapS_Bqreg -[(SS :o RB) :o SB]comp_soA bb84_swap_Bq_transport. by rewrite comp_soA. }
have Hcomm1 : forall j j' : 'I_nkey, j != j' -> bb84_eb_implant_so dev HE K j :o bb84_sig_emit K G j' = bb84_sig_emit K G j' :o bb84_eb_implant_so dev HE K j.
  { move=> j j' Hjj. rewrite /bb84_eb_implant_so /bb84_sig_emit. case Hj: (bb84_selected_index K j) => [i|]; last by rewrite comp_so1l comp_so1r. case Hj': (bb84_selected_index K j') => [i'|]; last by rewrite comp_so1r comp_so1l.
    have Hii : i' != i := pk_sel_inj HK Hjj Hj Hj'. set SS := (bb84_swap_S_so dev HE j i). set SB := (bb84_swap_Bq_so dev HE j i).
    set SIG' := (formso (liftf_lf (bb84_signal_lfun HE HB i' (G j')))). rewrite -[(SS :o SB) :o SIG']comp_soA (pk_swapBq_signal Hii) [SS :o (SIG' :o SB)]comp_soA pk_swapS_signal. by rewrite -comp_soA. } have Hcomm2 : forall j j' : 'I_nkey, j != j' -> bb84_sig_emit K G j :o bb84_sig_emit K G j' = bb84_sig_emit K G j' :o bb84_sig_emit K G j.
  { move=> j j' Hjj. rewrite /bb84_sig_emit. case Hj: (bb84_selected_index K j) => [i|]; last by rewrite comp_so1l comp_so1r.
    case Hj': (bb84_selected_index K j') => [i'|]; last by rewrite comp_so1r comp_so1l. have Hii : i' != i := pk_sel_inj HK Hjj Hj Hj'.
    apply: pk_formso_compC; apply: pk_dis_signal_signal. by rewrite eq_sym. } have Hpg := peel_gen Hext Hemloc Hpeel Hcomm1 Hcomm2 (enum_uniq _). rewrite Hpg. have He1 : (fun k : 'I_nkey => if k \in enum 'I_nkey then (1%:M : 'M[C]_2) else G k) = (fun _ => (1%:M : 'M[C]_2)).
  { by apply/funext => k; rewrite mem_enum. } by rewrite He1 /bb84_Bq_readout bitprod_mx1 regmx_lf1 liftf_lf1 formso1 comp_so1l. Qed.
Fact bb84_readout_peel (K : {set 'I_M}) (FA FG : 'I_nkey -> 'M[C]_2) : #|K| = nkey -> (bb84_S_readout FA :o bb84_Bq_readout FG)
    :o (\compr_(j <- enum 'I_nkey) bb84_eb_implant_so dev HE K j) = (\compr_(j <- enum 'I_nkey) bb84_eb_implant_so dev HE K j)
    :o ((\compr_(j <- enum 'I_nkey) bb84_sig_emit K FG j) :o (\compr_(j <- enum 'I_nkey) bb84_src_emit K FA j)).
Proof. have pk_src_sig_C : forall (K : {set 'I_M}) (FA FG : 'I_nkey -> 'M[C]_2) (j j' : 'I_nkey), bb84_src_emit K FA j :o bb84_sig_emit K FG
  j' = bb84_sig_emit K FG j' :o bb84_src_emit K FA j.
{ clear FG FA K; move=> K FA FG j j'. rewrite /bb84_src_emit /bb84_sig_emit. case: (bb84_selected_index K j) => [i|]; last by rewrite comp_so1l comp_so1r. case: (bb84_selected_index K j') => [i'|]; last by rewrite comp_so1r comp_so1l.
  apply: pk_formso_compC; exact: (pk_dis_source_signal i i'). } move=> HK; rewrite -comp_soA (bb84_readout_peelBq FG HK) comp_soA; rewrite (bb84_readout_peelS FA HK) -comp_soA. congr (_ :o _). apply: comp_so_compr_comprC => j j'. exact: pk_src_sig_C. Qed.
End DeferredSwapTransport.
Section SuperopFoldTools.
Variables (R : realType) (W : @chsType R).
Fact bb84_compr_drop_id (T : eqType) (f : T -> 'SO(W,W)) (Q : pred T) (l : seq T) :
  (forall i, ~~ Q i -> f i = \:1) -> \compr_(i <- l) f i = \compr_(i <- [seq i <- l | Q i]) f i.
Proof. move=> Hid. elim: l => [|a l IH]; first by rewrite !big_nil. rewrite big_cons /=; case Ha: (Q a).
  - by rewrite big_cons IH.
  - by rewrite comp_soErl (Hid a) ?Ha // comp_so1r IH. Qed.
Fact bb84_so_gmerge {T : eqType} {a g : T -> 'SO(W,W)} {l : seq T} : uniq l -> (forall i i', i != i' -> a i :o g i' = g i' :o a i) ->
  (\compr_(i <- l) a i) :o (\compr_(i <- l) g i) = \compr_(i <- l) (a i :o g i).
Proof. have bb84_so_gcomprC : forall (Tc : eqType) (X : 'SO(W,W)) (Y : Tc -> 'SO(W,W)) (l : seq Tc), (forall j, j \in l -> X :o Y j = Y j :o
  X) -> X :o (\compr_(j <- l) Y j) = (\compr_(j <- l) Y j) :o X.
  { move=> Tc X Y {}l. elim: l => [|j0 l' IH] Hc.
  - by rewrite big_nil comp_so1r comp_so1l.
  - rewrite big_cons comp_soErl comp_soA. rewrite IH; last by move=> j Hj; apply: Hc; rewrite in_cons Hj orbT.
    rewrite -comp_soA Hc ?in_cons ?eqxx //. by rewrite comp_soA. }
move=> Hun Hcomm; elim: l Hun => [|i0 l' IH] Hun.
  - by rewrite !big_nil comp_so1l.
  - move: Hun => /= /andP[Hi0 Hun]. rewrite !big_cons !comp_soErl. set CA := (\compr_(i <- l') a i); set CG := (\compr_(i <- l') g i).
    have Hac : a i0 :o CG = CG :o a i0.
    { rewrite /CG; apply: bb84_so_gcomprC => j Hj. by apply: Hcomm; apply/eqP => e; rewrite e Hj in Hi0. }
rewrite -[(CA :o a i0) :o (CG :o g i0)]comp_soA [a i0 :o (CG :o g i0)]comp_soA Hac. by rewrite -[(CG :o a i0) :o g i0]comp_soA [CA :o (CG :o (a i0 :o g i0))]comp_soA; rewrite /CA /CG (IH Hun). Qed.
End SuperopFoldTools.
Section GenericOrbitReindex.
Unset Implicit Arguments.
Variable R : realType.
Notation C := (@hermitian.C R).
Variables (V : finType) (M : nat).
Notation RH := (@run_history V M).
Variables (IX W : finType).
Variables (botv : V) (reround : RH -> IX -> W -> RH).
Variables (kdx : RH -> IX) (kdw : RH -> W).
Variables (decoded full : pred RH).
Variable det : pred W.
Variables (pe ksm pw : RH -> R).
Variable T : IX -> W -> RH -> C.
Variables (x0 : IX) (w0 : W).
Notation canon h := ((kdx h == x0) && (kdw h == w0)).
Notation seedp h := ((@hist_g V M h == botv) && (@hist_f V M h == botv)).
Notation Gsum h := ((pe h * ksm h)%:C * T (kdx h) (kdw h) h).
Notation Acond h := ((canon h && seedp h) && (decoded h && full h)).
Hypotheses (Hkdx_rr : forall h x w, full h -> kdx (reround h x w) = x) (Hkdw_rr : forall h x w, full h -> kdw (reround h x w) = w).
Hypotheses (HreroundK : forall h, decoded h -> full h -> reround h (kdx h) (kdw h) = h) (Hrr_rr : forall h x w x' w', reround (reround h x w) x' w' = reround h x' w') (Hfull_rr : forall h x w, full (reround h x w) = full h) (Hhistg_rr : forall h x w, @hist_g V M (reround h x w) = @hist_g V M h) (Hhistf_rr : forall h x w, @hist_f V M (reround h x w) = @hist_f V M h) (Hdec_rr : forall h x w x' w', decoded (reround h x w) = decoded (reround h x' w')).
Hypotheses (Hpe_rr : forall h x w, (kdx h == x0) && (kdw h == w0) -> decoded h -> full h -> det w -> ksm h != 0 -> pe (reround h x w) = pe h) (Hksm_rr : forall h x w x' w', det w -> det w' -> ksm (reround h x w) = ksm (reround h x' w')) (Hw0 : det w0) (HT_rr : forall x w h x1 w1 x2 w2, T x w (reround h x1 w1) = T x w (reround h x2 w2)) (HT0 : forall x w h, ~~ (decoded h && full h) -> T x w h = 0).
Hypotheses (Hksm0 : forall h, decoded h -> full h -> ~~ det (kdw h) -> ksm h = 0) (Hpe_si : forall t K g f, pe (t, ((K, g), f)) = pe (t, ((K, botv), botv))).
Hypothesis HT_si : forall t K g f, T (kdx (t, ((K, g), f))) (kdw (t, ((K, g), f))) (t, ((K, g), f)) =
  T (kdx (t, ((K, botv), botv))) (kdw (t, ((K, botv), botv))) (t, ((K, botv), botv)).
Hypothesis Hpw_seed : forall t K, \sum_(g : V) \sum_(f : V) pw (t, ((K, g), f)) = ksm (t, ((K, botv), botv)).
Fact abs_RHS_MID : \sum_(h : RH) (pe h * pw h)%:C * T (kdx h) (kdw h) h = \sum_(h : RH | seedp h) (pe h * ksm h)%:C * T (kdx h) (kdw h) h.
Proof. transitivity (\sum_(t : @round_trace V M) \sum_(K : V) (pe (t, ((K, botv), botv)) * ksm (t, ((K, botv), botv)))%:C * T (kdx (t, ((K,
  botv), botv))) (kdw (t, ((K, botv), botv))) (t, ((K, botv), botv))).
- rewrite -[LHS](run_history_sum_split_history (fun h => (pe h * pw h)%:C * T (kdx h) (kdw h) h)). apply: eq_bigr => t _; apply: eq_bigr => K _. under eq_bigr => g _ do under eq_bigr => f _ do rewrite Hpe_si HT_si. under eq_bigr => g _ do rewrite -mulr_suml.
  rewrite -mulr_suml; congr (_ * _). under eq_bigr => g _ do under eq_bigr => f _ do rewrite rmorphM /=.
  under eq_bigr => g _ do rewrite -mulr_sumr. rewrite -mulr_sumr. under eq_bigr => g _ do rewrite -rmorph_sum.
  by rewrite -rmorph_sum Hpw_seed rmorphM.
- rewrite [RHS]big_mkcond. rewrite -[RHS](run_history_sum_split_history (fun h => if seedp h then (pe h * ksm h)%:C * T (kdx h) (kdw h) h else 0)). apply: eq_bigr => t _; apply: eq_bigr => K _. rewrite (bigD1 botv) //=. rewrite [X in _ = _ + X]big1; last first.
  { move=> g Hg. apply: big1 => f _. by rewrite /hist_g /hist_f /= (negbTE Hg) andFb. } rewrite addr0 (bigD1 botv) //=.
    rewrite [X in _ = _ + X]big1; last first.
  { move=> f Hf. by rewrite /hist_g /hist_f /= eqxx (negbTE Hf) andbF. } by rewrite addr0 /hist_g /hist_f /= !eqxx. Qed.
Fact abs_MIDR_MID : \sum_(h : RH | seedp h && (decoded h && full h && det (kdw h))) Gsum h = \sum_(h : RH | seedp h) Gsum h.
Proof. rewrite [RHS](bigID (fun h => decoded h && full h && det (kdw h))) /=. rewrite [X in _ + X]big1 ?addr0 // => h /andP[_ Hn].
  have [Hdf|Hdf] := boolP (decoded h && full h).
- have /andP[Hd Hf] := Hdf. have Hnd : ~~ det (kdw h) by apply: contra Hn => Hkw; rewrite Hd Hf Hkw.
  by rewrite (Hksm0 h Hd Hf Hnd) mulr0 rmorph0 mul0r.
- by rewrite (HT0 (kdx h) (kdw h) h Hdf) mulr0. Qed.
Fact abs_LHS_MIDR : \sum_(h : RH) (pe h * ksm h * (canon h && seedp h)%:R)%:C * (\sum_(x : IX) \sum_(w : W | det w) T x w h) =
  \sum_(h : RH | seedp h && (decoded h && full h && det (kdw h))) Gsum h.
Proof. have Hsummand : forall h x w, (kdx h == x0) && (kdw h == w0) -> decoded h -> full h -> det w -> (pe h * ksm h)%:C * T x w h = (pe
  (reround h x w) * ksm (reround h x w))%:C * T (kdx (reround h x w)) (kdw (reround h x w)) (reround h x w).
{ move=> h x w Hcanon Hdec Hfull Hdw. have Hdkw : det (kdw h) by move: Hcanon => /andP[_ /eqP ->]; exact: Hw0.
  rewrite (Hkdx_rr h x w Hfull) (Hkdw_rr h x w Hfull) (Hksm_rr h x w (kdx h) (kdw h) Hdw Hdkw).
  rewrite (HT_rr x w h x w (kdx h) (kdw h)) (HreroundK h Hdec Hfull). have [Hksmz|Hksmn0] := eqVneq (ksm h) 0.
  - by rewrite Hksmz !mulr0 !rmorph0 !mul0r.
  - by rewrite (Hpe_rr h x w Hcanon Hdec Hfull Hdw Hksmn0). } have Hcond : forall (a : RH) (x : IX) (w : W), ((seedp (reround a x w) && ((decoded (reround a x w) && full (reround a x w)) && det (kdw (reround a x w)))) && ((reround (reround a x w) x0 w0 == a) && ((kdx (reround a x w) == x) && (kdw (reround a x w) == w)))) = ((((kdx a == x0) && (kdw a == w0)) && seedp a) && (decoded a && full a)) && det w.
{ move=> a x w. apply/idP/idP.
  - move=> /andP[/andP[Hsr /andP[/andP[Hdr Hfr] Hkwr]] /andP[/eqP Hrep /andP[/eqP Hkxr /eqP Hkwr']]].
    have Hfa : full a by rewrite -(Hfull_rr a x w). have Hdw : det w by rewrite -Hkwr'. have Hrepa : reround a x0 w0 = a by move: Hrep; rewrite (Hrr_rr a x w x0 w0). have Hkxa : kdx a = x0 by rewrite -(Hkdx_rr a x0 w0 Hfa); rewrite Hrepa.
    have Hkwa : kdw a = w0 by rewrite -(Hkdw_rr a x0 w0 Hfa); rewrite Hrepa. have Hsa : seedp a by move: Hsr; rewrite Hhistg_rr Hhistf_rr.
    have Hda : decoded a by move: Hdr; rewrite (Hdec_rr a x w x0 w0) Hrepa. by rewrite Hkxa Hkwa Hsa Hda Hfa Hdw !eqxx.
  - move=> /andP[/andP[/andP[/andP[/eqP Hkxa /eqP Hkwa] Hsa] /andP[Hda Hfa]] Hdw]. have Hfr : full (reround a x w) by rewrite (Hfull_rr a x w). have Hsr : seedp (reround a x w) by rewrite Hhistg_rr Hhistf_rr. have Hrepa : reround a x0 w0 = a by rewrite -{2}(HreroundK a Hda Hfa) Hkxa Hkwa. have Hkxr : kdx (reround a x w) == x by rewrite (Hkdx_rr a x w Hfa) eqxx.
    have Hkwr' : kdw (reround a x w) == w by rewrite (Hkdw_rr a x w Hfa) eqxx. have Hdr : decoded (reround a x w) by rewrite (Hdec_rr a x w x0 w0) Hrepa. have Hdkwr : det (kdw (reround a x w)) by rewrite (Hkdw_rr a x w Hfa). have Hrepr : reround (reround a x w) x0 w0 == a by rewrite (Hrr_rr a x w x0 w0) Hrepa eqxx. by rewrite Hsr Hdr Hfr Hdkwr Hrepr Hkxr Hkwr'. }
rewrite (eq_bigr (fun h => if (canon h && seedp h) then (pe h * ksm h)%:C * (\sum_(x : IX) \sum_(w : W | det w) T x w h) else 0)); last first.
{ move=> h _. case: (canon h && seedp h); [by rewrite mulr1 | by rewrite mulr0 rmorph0 mul0r]. } rewrite -big_mkcond /=.
  rewrite (bigID (fun h => decoded h && full h)) /=. rewrite [X in _ + X]big1 ?addr0; last first.
{ move=> h /andP[_ Hn]. suff -> : (\sum_(x : IX) \sum_(w : W | det w) T x w h) = 0 by rewrite mulr0. by apply: big1 => x _; apply: big1 => w _; exact: (HT0 x w h Hn). } under eq_bigr => h _ do (rewrite mulr_sumr; under eq_bigr => x _ do rewrite mulr_sumr).
  transitivity (\sum_(p : RH * (IX * W) | Acond p.1 && det p.2.2) ((pe p.1 * ksm p.1)%:C * T p.2.1 p.2.2 p.1)).
- under eq_bigr => h _ do rewrite pair_big /=. by rewrite pair_big /=; apply: eq_bigl => p; rewrite andbA.
- symmetry. rewrite (reindex_onto (fun p : RH * (IX * W) => reround p.1 p.2.1 p.2.2) (fun h' : RH => (reround h' x0 w0, (kdx h', kdw h')))) /=; last first.
  { move=> h' /andP[_ /andP[/andP[Hdec Hfull] _]]. by rewrite Hrr_rr (HreroundK h' Hdec Hfull). } apply: eq_big => [p | p Hp].
  + exact: (Hcond p.1 p.2.1 p.2.2).
  + have Hp2 : Acond p.1 && det p.2.2 by rewrite -(Hcond p.1 p.2.1 p.2.2). by move: Hp2 => /andP[/andP[/andP[Hcanon Hseed] /andP[Hdec Hfull]] Hdw]; rewrite /= (Hsummand p.1 p.2.1 p.2.2 Hcanon Hdec Hfull Hdw). Qed.
Fact abs_orbit_reindex : \sum_(h : RH) (pe h * ksm h * (canon h && seedp h)%:R)%:C * (\sum_(x : IX) \sum_(w : W | det w) T x w h) =
  \sum_(h : RH) (pe h * pw h)%:C * T (kdx h) (kdw h) h.
Proof. rewrite abs_LHS_MIDR abs_MIDR_MID. by symmetry; exact: abs_RHS_MID. Qed.
Set Implicit Arguments.
End GenericOrbitReindex.
Section AbstractValOrbitReindex.
Unset Implicit Arguments.
Variable R : realType.
Notation C := (@hermitian.C R).
Variables (Cv V : finType) (M : nat).
Notation store := (@syntax.store Cv V).
Notation RH := (@run_history V M).
Variables n k leakEC : nat.
Variable Qtol : R.
Variables (a_ y_ b_ y'_ d_ : 'I_M -> Cv).
Variables Xv Zv Kv XA XB ZA ZB lamv pECv Xhatv gv tAv tBv abortv Pvar : Cv.
Variables basisX basisZ outEmpty bot empty_transcript : V.
Variables (vbool : bool -> V) (vset : {set 'I_M} -> V) (vset_of : V -> {set 'I_M}) (vrat : nat -> nat -> V).
Variables (tr_app_rounds : ('I_M -> V * V * V) -> V -> V).
Variables tr_app_pe tr_app_ec : V -> V -> V -> V -> V.
Variables bits_on test_bits_on : {set 'I_M} -> ('I_M -> V) -> V.
Variables (err_count : V -> V -> nat) (err_of : V -> nat) (unif_nsubset_mass : nat -> {set 'I_M} -> V -> R) (ir_pub : nat -> V -> V -> V).
Variables (ir_dec : V -> V -> V) (unif_vseed : @syntax.dexpr R Cv V) (verify_hash : V -> V -> V) (unif_pseed : @syntax.dexpr R Cv V).
Variable s : store.
Local Notation av_pw h := (@history_post_weight R Cv V n k leakEC M Qtol a_ y_ b_ y'_ d_
     Xv Zv Kv XA XB ZA ZB lamv pECv Xhatv gv tAv tBv abortv Pvar basisX basisZ outEmpty bot empty_transcript vbool vset vset_of vrat
     tr_app_rounds tr_app_pe tr_app_ec bits_on test_bits_on err_count err_of
     unif_nsubset_mass ir_pub ir_dec unif_vseed verify_hash unif_pseed h s).
Local Notation av_ksm h := (@key_sample_mass R Cv V n M Xv bot vset_of unif_nsubset_mass (@announce_store Cv V M a_ b_ d_ Pvar tr_app_rounds
        (@rounds_store Cv V M a_ y_ b_ y'_ d_ Xv Zv basisX basisZ outEmpty vbool vset h
           (@start_store Cv V M Xv Zv abortv Pvar empty_transcript vbool vset s))) (@hist_K V M h)).
Variables IX W : finType.
Variable reround : RH -> IX -> W -> RH.
Variables (kdx : RH -> IX) (kdw : RH -> W).
Variables (decoded full : pred RH).
Variables (det : pred W) (pe : RH -> R) (T : IX -> W -> RH -> C).
Variables (x0 : IX) (w0 : W).
Notation canon h := ((kdx h == x0) && (kdw h == w0)).
Notation seedp h := ((@hist_g V M h == bot) && (@hist_f V M h == bot)).
Hypotheses (Hkdx_rr : forall h x w, full h -> kdx (reround h x w) = x) (Hkdw_rr : forall h x w, full h -> kdw (reround h x w) = w).
Hypotheses (HreroundK : forall h, decoded h -> full h -> reround h (kdx h) (kdw h) = h) (Hrr_rr : forall h x w x' w', reround (reround h x w) x' w' = reround h x' w') (Hfull_rr : forall h x w, full (reround h x w) = full h) (Hhistg_rr : forall h x w, @hist_g V M (reround h x w) = @hist_g V M h) (Hhistf_rr : forall h x w, @hist_f V M (reround h x w) = @hist_f V M h) (Hdec_rr : forall h x w x' w', decoded (reround h x w) = decoded (reround h x' w')).
Hypothesis Hpe_rr : forall h x w, (kdx h == x0) && (kdw h == w0) -> decoded h -> full h -> det w ->
  av_ksm h != 0%R -> pe (reround h x w) = pe h.
Hypotheses (Hksm_rr : forall h x w x' w', det w -> det w' -> av_ksm (reround h x w) = av_ksm (reround h x' w')) (Hw0 : det w0) (HT_rr : forall x w h x1 w1 x2 w2, T x w (reround h x1 w1) = T x w (reround h x2 w2)).
Hypotheses (HT0 : forall x w h, ~~ (decoded h && full h) -> T x w h = 0%R).
Hypotheses (Hksm0 : forall h, decoded h -> full h -> ~~ det (kdw h) -> av_ksm h = 0%R).
Hypotheses (Hpe_ext : forall h h', h.1 = h'.1 -> @hist_K V M h = @hist_K V M h' -> pe h = pe h').
Hypothesis HT_ext : forall h h', h.1 = h'.1 -> @hist_K V M h = @hist_K V M h' -> T (kdx h) (kdw h) h = T (kdx h') (kdw h') h'.
Hypotheses (HV : forall s' : store, (\sum_(v : V) unif_vseed s' v)%R = 1%R) (HP : forall s' : store, (\sum_(v : V) unif_pseed s' v)%R =
  1%R).
Fact av_orbit_reindex : \sum_(h : RH) (pe h * av_ksm h * (canon h && seedp h)%:R)%:C * (\sum_(x : IX) \sum_(w : W | det w) T x w h) =
  \sum_(h : RH) (pe h * av_pw h)%:C * T (kdx h) (kdw h) h.
Proof. apply: (@abs_orbit_reindex R V M IX W bot reround kdx kdw decoded full det pe (fun h => av_ksm h) (fun h => av_pw h) T x0 w0).
  all: try by [assumption | move=> t K g f; apply: Hpe_ext | move=> t K g f; apply: HT_ext]. move=> t K; exact: (@history_post_weight_seed_collapse R Cv V n k leakEC M Qtol a_ y_ b_ y'_ d_ Xv Zv Kv XA XB ZA ZB lamv pECv Xhatv gv tAv tBv abortv Pvar basisX basisZ outEmpty bot empty_transcript vbool vset vset_of vrat tr_app_rounds tr_app_pe tr_app_ec bits_on test_bits_on err_count err_of unif_nsubset_mass ir_pub ir_dec unif_vseed verify_hash unif_pseed t K s HV HP). Qed.
Set Implicit Arguments.
End AbstractValOrbitReindex.
Section DeferredHistoryCollapse.
Variable R : realType.
Notation chsType := (@chsType R).
Notation C := (@hermitian.C R).
Variables (P : @bb84_protocol R) (q : R) (dev : bb84_certified_device P q) (LE : finType) (HE : LE -> chsType).
Notation M := (bb84_round_limit P).
Notation LB := bb84_register_index.
Notation HB := (@bb84_register_space R P q dev).
Notation L := (bb84_label M LE LB).
Notation HL := (@bb84_label_space R M LE LB HE HB).
Notation V := (bb84_val M (bb84_n P) (bb84_l P) (cd_ir_bits dev) (cd_vseed_count dev) (cd_tag_count dev) (cd_paseed_count dev)).
Notation Eve := (bb84_eve_reg M LE LB).
Notation Sreg := (bb84_S P LE).
Notation Bqreg := (bb84_Bq P LE).
Notation nkey := (bb84_n P).
Notation dimS := (@bb84_dim_S_pow2 R P q dev LE HE).
Notation dimBq := (@bb84_dim_Bq_pow2 R P q dev LE HE).
Lemma bb84_so_commute_comp (X Y Z : 'SO[HL]_setT) : Z :o X = X :o Z -> Z :o Y = Y :o Z -> Z :o (X :o Y) = (X :o Y) :o Z.
Proof. by move=> HX HY; rewrite comp_soA HX -comp_soA HY comp_soA. Qed.
Fact bb84_formso_formso_compC {A B : {set L}} (f : 'F[HL]_A) (g : 'F[HL]_B) :
  [disjoint A & B] -> formso (liftf_lf f) :o formso (liftf_lf g) = formso (liftf_lf g) :o formso (liftf_lf f).
Proof. by move=> dis; rewrite !formso_comp liftf_lf_compC. Qed.
Fact bb84_formso_attack_compC {A : {set L}} (f : 'F[HL]_A) (EA : @adversary R L HL V Eve) (i' : 'I_M) (v : V) :
  [disjoint A & @bb84_signal_reg M LE LB i' :|: Eve] -> formso (liftf_lf f) :o liftfso (EA (bb84_signal_reg i') v) =
  liftfso (EA (bb84_signal_reg i') v) :o formso (liftf_lf f).
Proof. move=> dis; rewrite -liftfso_formso. by apply: liftfso_compC. Qed.
Fact bb84_formso_eb_round_compC {A : {set L}} (f : 'F[HL]_A) (EA : @adversary R L HL V Eve) (h : @run_history V M)
    (K : {set 'I_M}) (pair : 'M[C]_(4 * 2)) (i' : 'I_M) : [disjoint A &
    (@bb84_source_reg M LE LB i' :|: @bb84_signal_reg M LE LB i') :|: Eve] -> formso (liftf_lf f) :o bb84_eb_round_so EA h K pair i'
  = bb84_eb_round_so EA h K pair i' :o formso (liftf_lf f).
Proof. move=> dis. have disSS : [disjoint A & @bb84_source_reg M LE LB i' :|: @bb84_signal_reg M LE LB i'] by apply: (disjointWr _ dis);
  exact: subsetUl. have disSigE : [disjoint A & @bb84_signal_reg M LE LB i' :|: Eve]. by apply: (disjointWr _ dis); apply: setUSS; [exact: subsetUr | exact: subxx]. have disSig1 : [disjoint A & @bb84_signal_reg M LE LB i'] by apply: (disjointWr _ disSS); exact: subsetUr. have subSS : A :<=: setT :\: (@bb84_source_reg M LE LB i' :|: @bb84_signal_reg M LE LB i') by rewrite setTD -disjoints_subset. have subSig : A :<=: setT :\: (@bb84_signal_reg M LE LB i') by rewrite setTD -disjoints_subset.
  rewrite /bb84_eb_round_so; case: (i' \in K).
  - rewrite comp_soZr comp_soZl; congr (_ *: _). apply: bb84_so_commute_comp.
    + exact: (@bb84_formso_attack_compC A f EA i' (empty_transcript dev) disSigE).
    + exact: (replaceso_formso_compC subSS f (bb84_source_signal_lfun HE HB i' pair)).
  - rewrite comp_soZr comp_soZl; congr (_ *: _). apply: bb84_so_commute_comp.
    + exact: (bb84_formso_formso_compC f (bb84_round_readout_lf dev HE HB i' (bb84_history_bob_basis h i') (bb84_history_bob_outcome h i')) disSig1).
    + apply: bb84_so_commute_comp.
      * exact: (@bb84_formso_attack_compC A f EA i' (empty_transcript dev) disSigE).
      * exact: (replaceso_formso_compC subSig f (bb84_signal_lfun HE HB i' (bb84_prep_source_branch dev (bb84_history_alice_basis h i') (bb84_history_alice_bit h i')))). Qed.
Fact bb84_emit_reindex (K : {set 'I_M}) (e : 'I_nkey -> 'SO[HL]_setT) (er : 'I_M -> 'SO[HL]_setT) :
  #|K| = nkey -> (forall i, i \notin K -> er i = \:1) -> (forall (j : 'I_nkey) (i : 'I_M),
     bb84_selected_index K j = Some i -> er i = e j) -> \compr_(j <- enum 'I_nkey) e j = \compr_(i <- enum 'I_M) er i.
Proof. have bb84_enum_filter_memE : forall (K : {set 'I_M}), [seq i <- enum 'I_M | i \in K] = enum K by move=> {}K; rewrite enumT.
  have bb84_enum_set_valE : forall (K : {set 'I_M}), enum K = [seq enum_val j | j <- enum 'I_#|K|].
  { move=> {}K. have Hsz : size (enum K) = size [seq enum_val j | j <- enum 'I_#|K|]. by rewrite size_map -cardE size_enum_ord.
    case: (set_0Vmem K) => [->|[x0 _]].
  - rewrite enum_set0; apply/esym/size0nil. by rewrite size_map size_enum_ord cards0.
  - apply: (eq_from_nth (x0 := x0)) => // i Hi. have Hik : (i < #|K|)%N by rewrite -cardE in Hi. rewrite (nth_map (Ordinal Hik)); last by rewrite size_enum_ord. rewrite (nth_ord_enum (Ordinal Hik) (Ordinal Hik)). apply/esym; exact: (@enum_val_nth _ K x0 (Ordinal Hik)). }
have bb84_map_cast_ord_enumE : forall (n m : nat) (E : n = m), [seq cast_ord E j | j <- enum 'I_n] = enum 'I_m.
  { move=> n m E. apply: (inj_map val_inj). rewrite -map_comp (@eq_map _ _ (val \o cast_ord E) val); last by move=> j /=.
    by rewrite !val_enum_ord E. }
move=> HK Hoff Hon; symmetry; rewrite (bb84_compr_drop_id (Q := fun i => i \in K)); last exact: Hoff.
    rewrite bb84_enum_filter_memE (bb84_enum_set_valE K) big_map -(bb84_map_cast_ord_enumE _ _ (esym HK)) big_map; apply: eq_bigr => j _.
    apply: (Hon j). exact: (bb84_selected_index_enum_val (cast_ord (esym HK) j)). Qed.
Definition bb84_src_round (h : @run_history V M) (K : {set 'I_M}) (i : 'I_M) : 'SO[HL]_setT := if i \in K then
    formso (liftf_lf (bb84_source_lfun HE HB i (bb84_src_low_proj R (bb84_history_alice_bit h i)))) else \:1.
Definition bb84_sig_round (h : @run_history V M) (K : {set 'I_M}) (i : 'I_M) : 'SO[HL]_setT := if i \in K then
    formso (liftf_lf (bb84_signal_lfun HE HB i (cd_meas dev BasisX (bb84_history_bob_outcome h i)))) else \:1.
Fact bb84_src_round_eb_compC (h : @run_history V M) (K : {set 'I_M}) (EA : @adversary R L HL V Eve) (pair : 'M[C]_(4 * 2)) (i i' : 'I_M) :
  i != i' -> bb84_src_round h K i :o bb84_eb_round_so EA h K pair i' = bb84_eb_round_so EA h K pair i' :o bb84_src_round h K i.
Proof. have bb84_dis_source_round : forall (i i' : 'I_M), i != i' -> [disjoint @bb84_source_reg M LE LB i & (@bb84_source_reg M LE LB i' :|:
  @bb84_signal_reg M LE LB i') :|: Eve].
{ clear i' i pair EA K h; move=> i i'. move=> Hii; rewrite -setUA disjointXU. apply/andP; split.
  - exact: (pk_dis_source_source LE Hii).
  - rewrite disjoint_sym; exact: (bb84_collect_attack_dis_source LE i i'). } move=> Hii; rewrite /bb84_src_round. case: (i \in K); last by rewrite comp_so1l comp_so1r. apply: bb84_formso_eb_round_compC; exact: bb84_dis_source_round. Qed.
Fact bb84_sig_round_eb_compC (h : @run_history V M) (K : {set 'I_M}) (EA : @adversary R L HL V Eve) (pair : 'M[C]_(4 * 2)) (i i' : 'I_M) :
  i != i' -> bb84_sig_round h K i :o bb84_eb_round_so EA h K pair i' = bb84_eb_round_so EA h K pair i' :o bb84_sig_round h K i.
Proof. have bb84_dis_signal_round : forall (i i' : 'I_M), i != i' -> [disjoint @bb84_signal_reg M LE LB i & (@bb84_source_reg M LE LB i' :|:
  @bb84_signal_reg M LE LB i') :|: Eve].
{ clear i' i pair EA K h; move=> i i'. have bb84_dis_signal_eve : forall (i : 'I_M), [disjoint @bb84_signal_reg M LE LB i & Eve].
{ clear i' i; move=> i. rewrite /bb84_signal_reg /bb84_eve_reg disjoint1X inE /bb84_signal_label. by []. } move=> Hii; rewrite -setUA disjointXU. apply/andP; split.
  - rewrite disjoint_sym; exact: (pk_dis_source_signal LE i' i).
  - rewrite disjointXU. apply/andP; split.
    + exact: (pk_dis_signal_signal LE Hii).
    + exact: bb84_dis_signal_eve. } move=> Hii; rewrite /bb84_sig_round. case: (i \in K); last by rewrite comp_so1l comp_so1r.
      apply: bb84_formso_eb_round_compC; exact: bb84_dis_signal_round. Qed.
Fact bb84_sig_round_src_round_compC (h : @run_history V M) (K : {set 'I_M}) (i i' : 'I_M) : bb84_sig_round h K i :o bb84_src_round h K i'
  = bb84_src_round h K i' :o bb84_sig_round h K i.
Proof. rewrite /bb84_sig_round /bb84_src_round. case: (i \in K); last by rewrite comp_so1l comp_so1r. case: (i' \in K);
  last by rewrite comp_so1r comp_so1l. apply: bb84_formso_formso_compC. rewrite disjoint_sym; exact: (pk_dis_source_signal LE i' i). Qed.
Fact bb84_src_emit_reindexE (h : @run_history V M) :
  #|bb84_key_set h| = nkey -> \compr_(j <- enum 'I_nkey) bb84_src_emit dev HE (bb84_key_set h)
    (fun j => delta_mx (bito (bit_of_ord (bb84_key_data_x h) j)) (bito (bit_of_ord (bb84_key_data_x h) j))) j
  = \compr_(i <- enum 'I_M) bb84_src_round h (bb84_key_set h) i.
Proof. move=> HK; apply: (@bb84_emit_reindex (bb84_key_set h) _ _ HK).
  - by move=> i HiK; rewrite /bb84_src_round (negbTE HiK).
  - move=> j i Hsel. rewrite /bb84_src_emit/= Hsel /bb84_src_round (bb84_selected_index_mem Hsel); congr (formso (liftf_lf (bb84_source_lfun HE HB i _))). rewrite (_ : bitprod_mx (slotupd (fun _ : 'I_2 => (1%:M : 'M[C]_2)) bb84_src_ptr_slot _) = bb84_src_low_proj R (bit_of_ord (bb84_key_data_x h) j)); last exact: bb84_src_low_proj_bitlift.
    by rewrite bb84_key_data_xE Hsel. Qed.
Fact bb84_selected_index_onto (K : {set 'I_M}) (i : 'I_M) : #|K| = nkey -> i \in K -> exists j : 'I_nkey, bb84_selected_index K j = Some i.
Proof. by move=> HK HiK; have Hlt := bb84_key_slot_lt HK HiK; exists (Ordinal Hlt); apply: (bb84_selected_index_index HK HiK). Qed.
Fact bb84_deferred_history_collapse (EA : @adversary R L HL V Eve) (pair : 'M[C]_(4 * 2)) (h : @run_history V M) (rho : 'F[HL]_setT) :
  bb84_history_decoded h -> #|bb84_key_set h| = nkey -> bb84_eb_pair_ptr_ok pair ->
  bb84_eb_pair_x_branch_ok dev pair -> (forall (j : 'I_nkey) (i : 'I_M),
     bb84_selected_index (bb84_key_set h) j = Some i -> bb84_history_alice_basis h i = BasisX) -> (forall (j : 'I_nkey) (i : 'I_M),
     bb84_selected_index (bb84_key_set h) j = Some i -> bb84_history_bob_basis h i = BasisX) ->
  bb84_deferred_readout_so dev HE (bb84_key_data_x h) (bb84_key_data_w h) (bb84_eb_history_state EA pair h rho)
  = (\compr_(j <- enum 'I_nkey) bb84_eb_implant_so dev HE (bb84_key_set h) j) (bb84_mixed_history_state EA h rho).
Proof. have bb84_sig_emit_reindexE : forall (h : @run_history V M), #|bb84_key_set h| = nkey -> \compr_(j <- enum 'I_nkey) bb84_sig_emit dev
  HE (bb84_key_set h) (fun j => cd_meas dev BasisX (bb84_key_data_w h j)) j = \compr_(i <- enum 'I_M) bb84_sig_round h (bb84_key_set h) i.
  { move=> {}h. move=> HK; apply: (@bb84_emit_reindex (bb84_key_set h) _ _ HK).
  - by move=> i HiK; rewrite /bb84_sig_round (negbTE HiK).
  - move=> j i Hsel. rewrite /bb84_sig_emit/= Hsel /bb84_sig_round (bb84_selected_index_mem Hsel).
    congr (formso (liftf_lf (bb84_signal_lfun HE HB i (cd_meas dev BasisX _)))). by rewrite bb84_key_data_wE Hsel. }
have bb84_deferred_readout_peelform : forall (x : 'I_(2 ^ nkey)) (w : {ffun 'I_nkey -> option bool}), bb84_deferred_readout_so dev HE x w = bb84_S_readout dev HE (fun j => delta_mx (bito (bit_of_ord x j)) (bito (bit_of_ord x j))) :o bb84_Bq_readout dev HE (fun j => cd_meas dev BasisX (w j)).
{ clear rho h pair EA; move=> x w. rewrite /bb84_deferred_readout_so /bb84_deferred_alice_lf /bb84_deferred_bob_lf /bb84_deferred_bob_mx /bb84_S_readout /bb84_Bq_readout. congr (_ :o _). congr (formso (liftf_lf (regmx_lf dimS _))).
  by rewrite bitprod_mx_delta /bit_of_ord bitstring_to_ordK. } move=> Hdec HK Hptr Hbr Hba Hbb.
  have Hround : ((\compr_(i <- enum 'I_M) bb84_sig_round h (bb84_key_set h) i) :o (\compr_(i <- enum 'I_M) bb84_src_round h (bb84_key_set h) i)) :o (\compr_(i <- enum 'I_M) bb84_eb_round_so EA h (bb84_key_set h) pair i) = \compr_(i <- enum 'I_M) bb84_mixed_round_so EA h (bb84_key_set h) i.
  { rewrite -comp_soA. rewrite (bb84_so_gmerge (enum_uniq _) (fun i i' Hii => bb84_src_round_eb_compC h (bb84_key_set h) EA pair Hii)).
    rewrite (bb84_so_gmerge (enum_uniq _) (fun i i' Hii => bb84_so_commute_comp (bb84_sig_round_src_round_compC h (bb84_key_set h) i i') (bb84_sig_round_eb_compC h (bb84_key_set h) EA pair Hii))). apply: eq_bigr => i _. case HiK: (i \in bb84_key_set h).
    - have [j Hj] := bb84_selected_index_onto HK HiK. by rewrite /bb84_sig_round /bb84_src_round HiK; exact: (bb84_eb_key_round_collapse EA Hptr Hbr HiK (Hba j i Hj) (Hbb j i Hj)).
    - rewrite /bb84_sig_round /bb84_src_round HiK !comp_so1l. exact: (bb84_eb_nonkey_round_collapse EA h pair (negbT HiK)). }
have Hg : bb84_history_decoded h && (#|bb84_key_set h| == nkey) by rewrite Hdec HK eqxx.
      have Hif : forall X Y : 'F[HL]_setT, (if bb84_history_decoded h && (#|bb84_key_set h| == nkey) then X else Y) = X by move=> X Y; rewrite Hg. rewrite bb84_deferred_readout_peelform /bb84_eb_history_state /bb84_mixed_history_state !Hif -comp_soE.
      rewrite (bb84_readout_peel dev HE (fun j => delta_mx (bito (bit_of_ord (bb84_key_data_x h) j)) (bito (bit_of_ord (bb84_key_data_x h) j))) (fun j => cd_meas dev BasisX (bb84_key_data_w h j)) HK). rewrite comp_soE; congr ((\compr_(j <- enum 'I_nkey) bb84_eb_implant_so dev HE (bb84_key_set h) j) _). by rewrite (bb84_sig_emit_reindexE _ HK) (bb84_src_emit_reindexE HK); rewrite -comp_soE Hround. Qed.
Definition bb84_eb_readout_pass_state (EA : @adversary R L HL V Eve) (pair : 'M[C]_(4 * 2))
    (xi : @cq_state R L HL (bb84_cvar M) V) : 'F[HL]_setT := \sum_s \sum_(h : @run_history V M) ((((bb84_collect_pe_pass_indic h s)%:R) *
      bb84_collect_post_weight h s)%:C *: bb84_deferred_readout_so dev HE (bb84_key_data_x h) (bb84_key_data_w h)
        (bb84_eb_history_state EA pair h (xi s))).
Definition bb84_mixed_implant_pass_state (EA : @adversary R L HL V Eve) (xi : @cq_state R L HL (bb84_cvar M) V) : 'F[HL]_setT :=
  \sum_s \sum_(h : @run_history V M) ((((bb84_collect_pe_pass_indic h s)%:R) * bb84_collect_post_weight h s)%:C *:
      (\compr_(j <- enum 'I_nkey) bb84_eb_implant_so dev HE (bb84_key_set h) j) (bb84_mixed_history_state EA h (xi s))).
Fact bb84_mixed_history_source_ptraceso (EA : @adversary R L HL V Eve) (h : @run_history V M) (rho : 'F[HL]_setT) :
  bb84_history_decoded h -> #|bb84_key_set h| = nkey -> ptraceso [set x : L | if x is inr (inl _) then true else false]
    (bb84_mixed_history_state EA h rho) = ptraceso [set x : L | if x is inr (inl _) then true else false]
    (bb84_history_source_state EA h rho).
Proof. have bb84_ptraceso_compr_seq_eq : forall (F G : 'I_M -> 'SO[HL]_setT) (r : seq 'I_M) (rho : 'F[HL]_setT), (forall (i : 'I_M) (x :
  'F[HL]_setT), ptraceso [set x0 : L | if x0 is inr (inl _) then true else false] (F i x) = ptraceso [set x0 : L | if x0 is inr (inl _) then true else false] (G i x)) -> (forall (r' : seq 'I_M) (x y : 'F[HL]_setT), ptraceso [set x0 : L | if x0 is inr (inl _) then true else false] x = ptraceso [set x0 : L | if x0 is inr (inl _) then true else false] y -> ptraceso [set x0 : L | if x0 is inr (inl _) then true else false] ((\compr_(i <- r') G i) x) = ptraceso [set x0 : L | if x0 is inr (inl _) then true else false] ((\compr_(i <- r') G i) y)) -> ptraceso [set x0 : L | if x0 is inr (inl _) then true else false] ((\compr_(i <- r) F i) rho) = ptraceso [set x0 : L | if x0 is inr (inl _) then true else false] ((\compr_(i <- r) G i) rho).
{ clear rho h EA; move=> F G r rho. move=> HFG HGprop; elim: r rho => [|i r IHr] rho.
  - by rewrite !big_nil !id_soE.
  - rewrite !big_cons !comp_sorE. rewrite IHr. apply: (HGprop r). exact: (HFG i rho). } move=> Hdec HK.
    have bb84_mixed_history_state_case : bb84_mixed_history_state EA h rho = (\compr_(i <- enum 'I_M) bb84_mixed_round_so EA h (bb84_key_set h) i) rho.
  { rewrite /bb84_mixed_history_state. by have -> : (bb84_history_decoded h && (#|bb84_key_set h| == nkey)) = true by rewrite HK eqxx andbT. }
rewrite bb84_mixed_history_state_case. rewrite (bb84_history_source_state_case (h := h) EA rho Hdec).
    apply: bb84_ptraceso_compr_seq_eq.
  - move=> i x. case Hik: (i \in bb84_key_set h).
    + rewrite /bb84_mixed_round_so Hik. set a := (bb84_prep_basis_prob P (bb84_history_bob_basis h i))%:C. rewrite !scale_soE.
      rewrite [in X in X = _]comp_soE. rewrite [in X in _ = X]comp_soE [in X in _ = X]comp_soE. rewrite ![ptraceso _ (a *: _)]linearZ.
      congr (a *: _). exact: bb84_round_source_update_so_formso_ptraceso_all_sources.
    + by rewrite /bb84_mixed_round_so Hik.
  - move=> r' x y Hxy. apply: bb84_source_readout_seq_ptraceso_eq. exact: Hxy. Qed.
Fact bb84_eb_readout_pass_state_traceRe (EA : @adversary R L HL V Eve) (pair : 'M[C]_(4 * 2)) (xi : @cq_state R L HL (bb84_cvar M) V) :
  bb84_eb_pair_ptr_ok pair -> bb84_eb_pair_x_branch_ok dev pair -> @complex.Re R (\Tr (bb84_eb_readout_pass_state EA pair xi)) =
  bb84_source_pass_prob EA xi.
Proof. have bb84_eb_readout_pass_source_traceE : forall (EA : @adversary R L HL V Eve) (pair : 'M[C]_(4 * 2)) (xi : @cq_state R L HL
  (bb84_cvar M) V), bb84_eb_pair_ptr_ok pair -> bb84_eb_pair_x_branch_ok dev pair -> \Tr (bb84_eb_readout_pass_state EA pair xi) = \Tr (bb84_pass_history_source_state EA xi).
{ clear xi pair EA; move=> EA pair xi. have bb84_eb_readout_pass_traceE : forall (EA : @adversary R L HL V Eve) (pair : 'M[C]_(4 * 2)) (xi : @cq_state R L HL (bb84_cvar M) V), bb84_eb_pair_ptr_ok pair -> bb84_eb_pair_x_branch_ok dev pair -> \Tr (bb84_eb_readout_pass_state EA pair xi) = \sum_s \sum_(h : @run_history V M) (((bb84_collect_pe_pass_indic h s)%:R * bb84_collect_post_weight h s)%:C * \Tr (bb84_mixed_history_state EA h (xi s))).
{ clear xi pair EA; move=> EA pair xi. have bb84_eb_implant_fold_trlf : forall (K : {set 'I_M}) (x : 'F[HL]_setT), \Tr ((\compr_(j <- enum 'I_nkey) bb84_eb_implant_so dev HE K j) x) = \Tr x.
{ clear xi pair EA; move=> K x. have gen : forall (r : seq 'I_nkey) (y : 'F[HL]_setT), \Tr ((\compr_(j <- r) bb84_eb_implant_so dev HE K j) y) = \Tr y.
  { elim => [|j r IHr] y.
    - by rewrite big_nil id_soE.
    - by rewrite big_cons comp_sorE IHr bb84_eb_implant_so_trlf. } exact: gen. } have bb84_eb_readout_pass_collapse_gen : forall (EA : @adversary R L HL V Eve) (pair : 'M[C]_(4 * 2)) (xi : @cq_state R L HL (bb84_cvar M) V), bb84_eb_pair_ptr_ok pair -> bb84_eb_pair_x_branch_ok dev pair -> (forall (h : @run_history V M) (s : @store (bb84_cvar M) V) (j : 'I_nkey) (i : 'I_M), (bb84_collect_pe_pass_indic h s)%:R * bb84_collect_post_weight h s != 0 -> bb84_selected_index (bb84_key_set h) j = Some i -> bb84_history_alice_basis h i = BasisX /\ bb84_history_bob_basis h i = BasisX) -> bb84_eb_readout_pass_state EA pair xi = bb84_mixed_implant_pass_state EA xi.
{ clear xi pair EA; move=> EA pair xi. move=> Hptr Hbr Hbasis; rewrite /bb84_eb_readout_pass_state /bb84_mixed_implant_pass_state.
  apply: eq_bigr => s _; apply: eq_bigr => h _. case Hw: (((bb84_collect_pe_pass_indic h s)%:R * bb84_collect_post_weight h s) == 0).
  - by rewrite (eqP Hw) rmorph0 !scale0r.
  - congr (_ *: _). case Hdec: (bb84_history_decoded h && (#|bb84_key_set h| == nkey)).
    + case/andP: Hdec => Hdec1 /eqP HK. apply: bb84_deferred_history_collapse; by [assumption | move=> j i Hsel; have [Ha _] := Hbasis h s j i (negbT Hw) Hsel | move=> j i Hsel; have [_ Hb] := Hbasis h s j i (negbT Hw) Hsel].
    + have Heb0 : bb84_eb_history_state EA pair h (xi s) = 0 by rewrite /bb84_eb_history_state Hdec.
      have Hmx0 : bb84_mixed_history_state EA h (xi s) = 0 by rewrite /bb84_mixed_history_state Hdec.
      by rewrite Heb0 Hmx0 /fun_of_superof !linear0. } move=> Hptr Hbr. have bb84_eb_readout_pass_collapse : bb84_eb_readout_pass_state EA pair xi = bb84_mixed_implant_pass_state EA xi.
  { apply: bb84_eb_readout_pass_collapse_gen => // h s j i Hw Hsel. exact: (bb84_pe_pass_history_selected_key_basis Hw Hsel). }
rewrite bb84_eb_readout_pass_collapse /bb84_mixed_implant_pass_state linear_sum /=; apply: eq_bigr => s _. rewrite linear_sum /=; apply: eq_bigr => h _. by rewrite linearZ /= bb84_eb_implant_fold_trlf. } have bb84_mixed_history_source_traceE : forall (EA : @adversary R L HL V Eve) (h : @run_history V M) (rho : 'F[HL]_setT), #|bb84_key_set h| = nkey -> \Tr (bb84_mixed_history_state EA h rho) = \Tr (bb84_history_source_state EA h rho).
{ clear xi pair EA; move=> EA h rho. move=> HK. case Hdec: (bb84_history_decoded h); last first.
  - have Hm0 : bb84_mixed_history_state EA h rho = 0 by rewrite /bb84_mixed_history_state Hdec.
    have Hs0 : bb84_history_source_state EA h rho = 0.
    { rewrite /bb84_history_source_state /bb84_trace_source_state -bb84_history_decoded_traceE Hdec. by []. } by rewrite Hm0 Hs0.
  - have /cptpP [_ /tpmapP Htp] := @ptraceso_qc R L HL [set x : L | if x is inr (inl _) then true else false] (setTfor L).
    rewrite -(Htp (bb84_mixed_history_state EA h rho)) -(Htp (bb84_history_source_state EA h rho)).
    by rewrite (bb84_mixed_history_source_ptraceso EA rho Hdec HK). } move=> Hptr Hbr; rewrite bb84_eb_readout_pass_traceE //.
    rewrite /bb84_pass_history_source_state linear_sum /=; apply: eq_bigr => s _. rewrite linear_sum /=; apply: eq_bigr => h _.
    rewrite linearZ /=. transitivity (((bb84_collect_pe_pass_indic h s)%:R * bb84_collect_post_weight h s)%:C * \Tr (bb84_history_source_state EA h (xi s))).
  - case Hw: (((bb84_collect_pe_pass_indic h s)%:R * bb84_collect_post_weight h s) == 0).
    + by rewrite (eqP Hw) rmorph0 !mul0r.
    + congr (_ * _). apply: bb84_mixed_history_source_traceE. by have [Hcard _] := bb84_pe_pass_history_key_sample_support (h := h) (s := s) (negbT Hw); exact: Hcard.
  - by []. } move=> Hptr Hbr; by rewrite bb84_eb_readout_pass_source_traceE // /bb84_source_pass_prob. Qed.
Notation Ereg := (bb84_E P LE).
Notation Zreg := (bb84_Zkey P LE).
Definition bb84_eb_canon (h : @run_history V M) : bool := (bb84_key_data_x h == bitstring_to_ord (fun _ : 'I_nkey => false)) &&
  (bb84_key_data_w h == [ffun _ : 'I_nkey => Some false]).
Definition bb84_seed_unused_hist (h : @run_history V M) : bool := (hist_g h == bb84_bot_val) && (hist_f h == bb84_bot_val).
Local Notation bobout := {ffun 'I_nkey -> option bool}.
Definition bb84_M_click : 'M[C]_2 := 1%:M - (cd_meas dev BasisX None)^*t *m cd_meas dev BasisX None.
Fact bb84_M_click_click : bb84_M_click = (cd_meas dev BasisX (Some false))^*t *m cd_meas dev BasisX (Some false)
  + (cd_meas dev BasisX (Some true))^*t *m cd_meas dev BasisX (Some true).
Proof. rewrite /bb84_M_click; apply/eqP; rewrite subr_eq; apply/eqP. by rewrite -(cd_meas_complete dev BasisX) [in RHS]addrC [in RHS]addrA. Qed.
Fact bb84_M_click_psd : bb84_M_click \is psdmx.
Proof. rewrite bb84_M_click_click. exact: psdmxD (formV_psd _) (formV_psd _). Qed.
Definition bb84_M_click_sqrt : 'M[C]_2 := mapf_mx sqrtC bb84_M_click.
Definition bb84_M_click_total_lf : 'F[HL]_Bqreg := regmx_lf dimBq (bitprod_mx (fun _ : 'I_nkey => bb84_M_click)).
Definition bb84_click_bob_lf : 'F[HL]_Bqreg := regmx_lf dimBq (bitprod_mx (fun _ : 'I_nkey => bb84_M_click_sqrt)).
Definition bb84_detect_so : 'SO[HL]_setT := formso (liftf_lf bb84_click_bob_lf).
Definition bb84_eb_class_det_state (EA : @adversary R L HL V Eve) (pair : 'M[C]_(4 * 2))
    (xi : @cq_state R L HL (bb84_cvar M) V) : 'F[HL]_setT := \sum_s \sum_(h : @run_history V M) (((bb84_collect_pe_pass_indic h s)%:R *
      bb84_collect_key_sample_mass h s * (bb84_eb_canon h && bb84_seed_unused_hist h)%:R)%:C *:
      bb84_detect_so (bb84_eb_history_state EA pair h (xi s))).
Fact bb84_eb_class_det_state_psd (EA : @adversary R L HL V Eve) (pair : 'M[C]_(4 * 2)) (xi : @cq_state R L HL (bb84_cvar M) V) :
  pair \is den1mx -> (forall s, xi s \is psdlf) -> bb84_eb_class_det_state EA pair xi \is psdlf.
Proof. have bb84_detect_so_psd : forall (rho : 'F[HL]_setT), rho \is psdlf -> bb84_detect_so rho \is psdlf.
{ clear xi pair EA; move=> rho. move=> Hrho; rewrite /bb84_detect_so; exact: cp_psdP. } move=> Hpair Hxi.
  have bb84_collect_key_sample_mass_nonneg : forall (h0 : @run_history V M) (s0 : @store (bb84_cvar M) V), 0 <= bb84_collect_key_sample_mass h0 s0.
  { move=> h0 s0; rewrite /bb84_collect_key_sample_mass. apply: key_sample_mass_nonneg => m X v0. exact: bb84_unif_nsubset_mass_nonneg. }
have bb84_eb_history_state_psd : forall (EA0 : @adversary R L HL V Eve) (pair0 : 'M[C]_(4 * 2)) (h0 : @run_history V M) (rho0 : 'F[HL]_setT), pair0 \is den1mx -> rho0 \is psdlf -> bb84_eb_history_state EA0 pair0 h0 rho0 \is psdlf.
  { move=> EA0 pair0 h0 rho0 Hpair0 Hrho0; rewrite /bb84_eb_history_state. case: (_ && _); last exact: is_psdlf.
    apply: bb84_eb_implant_seq_psd. exact: bb84_eb_round_seq_psd. } rewrite /bb84_eb_class_det_state; apply: psdlf_sum => s _.
    apply: psdlf_sum => h _. have Hcoef : 0 <= (bb84_collect_pe_pass_indic h s)%:R * bb84_collect_key_sample_mass h s * (bb84_eb_canon h && bb84_seed_unused_hist h)%:R.
  { apply: mulr_ge0; last by case: (bb84_eb_canon h && bb84_seed_unused_hist h). apply: mulr_ge0; first by case: (bb84_collect_pe_pass_indic h s). exact: bb84_collect_key_sample_mass_nonneg. } apply: psdlfZ; first by rewrite lecR.
    apply: bb84_detect_so_psd. apply: bb84_eb_history_state_psd.
  - exact: Hpair.
  - exact: (Hxi s). Qed.
Fact bb84_deferred_bob_detected_complete : \sum_(w : bobout | [forall j, w j != None])
    ((bb84_deferred_bob_lf dev HE w)^A \o bb84_deferred_bob_lf dev HE w) = bb84_M_click_total_lf.
Proof. have bb84_detected_reindex : forall (V' : zmodType) (G : bobout -> V'), \sum_(w : bobout | [forall j, w j != None]) G w = \sum_(b :
  {ffun 'I_nkey -> bool}) G [ffun j => Some (b j)].
  { move=> V' G. rewrite (reindex_onto (fun b : {ffun 'I_nkey -> bool} => [ffun j => Some (b j)]) (fun w : bobout => [ffun j => odflt false (w j)])); last first.
  { move=> w /forallP Hw; apply/ffunP => j; rewrite !ffunE. have Hj := Hw j; case E: (w j) Hj => [c|] Hj //. }
apply: eq_bigl => b; apply/andP; split.
  - by apply/forallP => j; rewrite ffunE.
  - by apply/eqP/ffunP => j; rewrite !ffunE. }
have step : forall w : bobout, (bb84_deferred_bob_lf dev HE w)^A \o bb84_deferred_bob_lf dev HE w = regmx_lf dimBq (bitprod_mx (fun j => (cd_meas dev BasisX (w j))^*t *m cd_meas dev BasisX (w j))).
  { move=> w. rewrite /bb84_deferred_bob_lf regmx_lf_adj regmx_lf_comp. by rewrite /bb84_deferred_bob_mx bitprod_mx_adj bitprod_mx_mul. }
under eq_bigr do rewrite step. rewrite -regmx_lf_sum /bb84_M_click_total_lf; congr (regmx_lf dimBq _).
    rewrite (bb84_detected_reindex _ (fun w => bitprod_mx (fun j => (cd_meas dev BasisX (w j))^*t *m cd_meas dev BasisX (w j)))).
    have Hre : forall b : {ffun 'I_nkey -> bool}, bitprod_mx (fun j => (cd_meas dev BasisX ([ffun j0 => Some (b j0)] j))^*t *m cd_meas dev BasisX ([ffun j0 => Some (b j0)] j)) = bitprod_mx (fun j => (cd_meas dev BasisX (Some (b j)))^*t *m cd_meas dev BasisX (Some (b j))).
  { by move=> b; apply: bitprod_mx_eq => j; rewrite ffunE. } under eq_bigr do rewrite Hre. rewrite (bitprod_mx_sum (fun (j : 'I_nkey) (c : bool) => (cd_meas dev BasisX (Some c))^*t *m cd_meas dev BasisX (Some c))). congr (bitprod_mx _); apply/funext => j.
    rewrite big_bool bb84_M_click_click; exact: addrC. Qed.
Local Lemma bb84_alice_lift_complete_loc : \sum_(x : 'I_(2 ^ nkey)) ((liftf_lf (bb84_deferred_alice_lf dev HE x))^A \o
     liftf_lf (bb84_deferred_alice_lf dev HE x)) = (\1 : 'F[HL]_setT).
Proof. under eq_bigr do rewrite -liftf_lf_adj -liftf_lf_comp. by rewrite -linear_sum /= bb84_deferred_alice_complete liftf_lf1. Qed.
Local Lemma bb84_bob_detected_lift_complete_loc : \sum_(w : bobout | [forall j, w j != None])
    ((liftf_lf (bb84_deferred_bob_lf dev HE w))^A \o liftf_lf (bb84_deferred_bob_lf dev HE w)) = liftf_lf bb84_M_click_total_lf.
Proof. under eq_bigr do rewrite -liftf_lf_adj -liftf_lf_comp. by rewrite -linear_sum /= bb84_deferred_bob_detected_complete. Qed.
Lemma bb84_outcome_val_detected_neq (o : option bool) : o != None -> (bb84_outcome_val o : V) != bb84_outcome_val None.
Proof. apply: contra => /eqP Heq; move: Heq. by rewrite /bb84_outcome_val => -[->]. Qed.
Fact bb84_choice_a_reround (c : @round_choice V) (yb : bool) (o : option bool) : choice_a (bb84_reround_choice c yb o) = choice_a c.
Proof. by []. Qed.
Fact bb84_choice_b_reround (c : @round_choice V) (yb : bool) (o : option bool) : choice_b (bb84_reround_choice c yb o) = choice_b c.
Proof. by []. Qed.
Fact bb84_choice_y'_reround (c : @round_choice V) (yb : bool) (o : option bool) :
  choice_y' (bb84_reround_choice c yb o) = bb84_outcome_val o.
Proof. by []. Qed.
Fact bb84_trace_key_round_detected_reround (bX : V) (rep : @run_history V M) (x x' : 'I_(2 ^ nkey)) (w w' : bobout) (i : 'I_M) :
  [forall j, w j != None] -> [forall j, w' j != None] -> @trace_key_round V M bX (bb84_outcome_val None) (bb84_key_reround rep x w).1 i =
  @trace_key_round V M bX (bb84_outcome_val None) (bb84_key_reround rep x' w').1 i.
Proof. move=> /forallP Hw /forallP Hw'; rewrite /trace_key_round /trace_detected !bb84_key_reroundE. case HiK: (i \in bb84_key_set rep);
  last by []. case: insubP => [j _ _ | _]; last by []. rewrite !bb84_choice_a_reround !bb84_choice_b_reround !bb84_choice_y'_reround.
  by rewrite (bb84_outcome_val_detected_neq (Hw j)) (bb84_outcome_val_detected_neq (Hw' j)). Qed.
Fact bb84_trace_key_set_detected_reround (bX : V) (rep : @run_history V M) (x x' : 'I_(2 ^ nkey)) (w w' : bobout) :
  [forall j, w j != None] -> [forall j, w' j != None] -> @trace_key_set V M bX (bb84_outcome_val None) (bb84_key_reround rep x w).1 =
  @trace_key_set V M bX (bb84_outcome_val None) (bb84_key_reround rep x' w').1.
Proof. move=> Hw Hw'; apply/setP => i; rewrite !inE. exact: (@bb84_trace_key_round_detected_reround bX rep x x' w w' i Hw Hw'). Qed.
Lemma bb84_basis_value_program (b : bb84_basis) : bb84_basis_value dev b = @bb84_program_basis_value R P q dev b.
Proof. by case: b. Qed.
Fact bb84_collect_key_sample_mass_key_set_eq (h h' : @run_history V M) (s : @store (bb84_cvar M) V) :
  (0 < M)%N -> @trace_key_set V M (@bb84_program_basis_value R P q dev BasisX) (bb84_outcome_val None) h.1 =
  @trace_key_set V M (@bb84_program_basis_value R P q dev BasisX) (bb84_outcome_val None) h'.1 -> hist_K h = hist_K h' ->
  bb84_collect_key_sample_mass h s = bb84_collect_key_sample_mass h' s.
Proof. move=> HM Hset HK; rewrite /bb84_collect_key_sample_mass /key_sample_mass; cbv beta; rewrite !bb84_basis_value_program.
  by rewrite [in X in X = _](announce_trace_key_set h.1 s HM); rewrite [in X in _ = X](announce_trace_key_set h'.1 s HM); rewrite Hset HK. Qed.
Fact bb84_key_sample_mass_detected_reround_const (rep : @run_history V M) (s : @store (bb84_cvar M) V)
    (x x' : 'I_(2 ^ nkey)) (w w' : bobout) : (0 < M)%N -> [forall j, w j != None] -> [forall j, w' j != None] ->
  bb84_collect_key_sample_mass (bb84_key_reround rep x w) s = bb84_collect_key_sample_mass (bb84_key_reround rep x' w') s.
Proof. move=> HM Hw Hw'. apply: (bb84_collect_key_sample_mass_key_set_eq _ HM); last by [].
  exact: (@bb84_trace_key_set_detected_reround (@bb84_program_basis_value R P q dev BasisX) rep x x' w w' Hw Hw'). Qed.
Definition rhoSrc_SEB_sigdet_lf (EA : @adversary R L HL V Eve) (pair : 'M[C]_(4 * 2)) (xi : @cq_state R L HL (bb84_cvar M) V) :
    'F[HL]_((Sreg :|: Ereg) :|: Bqreg) := ptrace_cast_gen (bb84_setT_diff_complement ((Sreg :|: Ereg) :|: Bqreg))
    (bb84_eb_class_det_state EA pair xi).
Fact rhoSrc_SEB_sigdet_lf_psd (EA : @adversary R L HL V Eve) (pair : 'M[C]_(4 * 2)) (xi : @cq_state R L HL (bb84_cvar M) V) :
  pair \is den1mx -> (forall s, xi s \is psdlf) -> rhoSrc_SEB_sigdet_lf EA pair xi \is psdlf.
Proof. move=> Hpair Hxi; rewrite /rhoSrc_SEB_sigdet_lf. apply: ptrace_cast_gen_psdlf. exact: (bb84_eb_class_det_state_psd EA Hpair Hxi). Qed.
Fact bb84_key_setE_loc (h : @run_history V M) : bb84_key_set h = bb84_set_of (@hist_K V M h).
Proof. by []. Qed.
Lemma bb84_key_set_ext (h h' : @run_history V M) : @hist_K V M h = @hist_K V M h' -> bb84_key_set h = bb84_key_set h'.
Proof. by move=> HK; rewrite !bb84_key_setE_loc HK. Qed.
Fact bb84_key_data_x_ext (h h' : @run_history V M) :
  h.1 = h'.1 -> @hist_K V M h = @hist_K V M h' -> bb84_key_data_x h = bb84_key_data_x h'.
Proof. move=> H1 HK; apply: eq_from_bit_of_ord => j; rewrite !bb84_key_data_xE (bb84_key_set_ext HK).
  case: (bb84_selected_index _ j) => [i|]; last by []. by rewrite /bb84_history_alice_bit /hist_y /hist_choice H1. Qed.
Fact bb84_key_data_w_ext (h h' : @run_history V M) :
  h.1 = h'.1 -> @hist_K V M h = @hist_K V M h' -> bb84_key_data_w h = bb84_key_data_w h'.
Proof. move=> H1 HK; apply/ffunP => j; rewrite !bb84_key_data_wE (bb84_key_set_ext HK). case: (bb84_selected_index _ j) => [i|]; last by [].
  by rewrite /bb84_history_bob_outcome /hist_y' /hist_choice H1. Qed.
Fact bb84_eb_history_state_ext (EA : @adversary R L HL V Eve) (pair : 'M[C]_(4 * 2)) (h h' : @run_history V M) (rho : 'F[HL]_setT) :
  h.1 = h'.1 -> @hist_K V M h = @hist_K V M h' -> bb84_eb_history_state EA pair h rho = bb84_eb_history_state EA pair h' rho.
Proof. move=> H1 HK; have Hkey : bb84_key_set h = bb84_key_set h' by apply: bb84_key_set_ext.
  have Hdec : bb84_history_decoded h = bb84_history_decoded h'.
  { apply/eq_forallb => i. by rewrite /bb84_history_round_decoded /hist_a /hist_y /hist_b /hist_y' /hist_choice H1. }
rewrite /bb84_eb_history_state Hkey Hdec. case: (bb84_history_decoded h' && (#|bb84_key_set h'| == nkey)); last by [].
    have Hcomp : (\compr_(i <- enum 'I_M) bb84_eb_round_so EA h (bb84_key_set h') pair i)%VF = (\compr_(i <- enum 'I_M) bb84_eb_round_so EA h' (bb84_key_set h') pair i)%VF.
  { apply: eq_bigr => i _. rewrite /bb84_eb_round_so. case: (i \in bb84_key_set h').
    - by rewrite /bb84_history_bob_basis /bb84_history_alice_basis /hist_a /hist_b /hist_choice H1.
    - by rewrite /bb84_history_bob_basis /bb84_history_alice_basis /bb84_history_bob_outcome /bb84_history_alice_bit /hist_a /hist_b /hist_y /hist_y' /hist_choice H1. } have Happ := congr1 (fun E : 'SO[HL]_setT => E rho) Hcomp.
      exact: (congr1 (fun t : 'F[HL]_setT => (\compr_(j <- enum 'I_nkey) bb84_eb_implant_so dev HE (bb84_key_set h') j)%VF t) Happ). Qed.
Fact bb84_readout_trace_ext (EA : @adversary R L HL V Eve) (pair : 'M[C]_(4 * 2)) (rho : 'F[HL]_setT) (h h' : @run_history V M) :
  h.1 = h'.1 -> @hist_K V M h = @hist_K V M h' -> \Tr (bb84_deferred_readout_so dev HE (bb84_key_data_x h) (bb84_key_data_w h)
        (bb84_eb_history_state EA pair h rho)) = \Tr (bb84_deferred_readout_so dev HE (bb84_key_data_x h') (bb84_key_data_w h')
        (bb84_eb_history_state EA pair h' rho)).
Proof. move=> H1 HK; rewrite (bb84_key_data_x_ext H1 HK). by rewrite (bb84_key_data_w_ext H1 HK);
  rewrite (bb84_eb_history_state_ext EA pair rho H1 HK). Qed.
Fact pe_pass_indic_hist_ext (h h' : @run_history V M) (s : @store (bb84_cvar M) V) : h.1 = h'.1 -> @hist_K V M h = @hist_K V M h' ->
  bb84_collect_pe_pass_indic h s = bb84_collect_pe_pass_indic h' s.
Proof. move=> H1 HK; rewrite /bb84_collect_pe_pass_indic; rewrite /rounds_store !rounds_store_seqE H1.
  congr (~~ (@pe_failed R (bb84_cvar M) V nkey (bb84_k P) M (bb84_Qtol P) (@BVX M) (@BVZ M) (@BVlam M) bb84_set_of bb84_error_of _)).
  rewrite [in LHS](surjective_pairing h) [in LHS](surjective_pairing h.2) [in LHS](surjective_pairing h.2.1).
  rewrite [in RHS](surjective_pairing h') [in RHS](surjective_pairing h'.2) [in RHS](surjective_pairing h'.2.1). by move: HK; rewrite /hist_K => HK; rewrite H1 HK; exact: paramest_store_future_irrel. Qed.
Fact undetected_notin_trace_key_set (h : @run_history V M) (i : 'I_M) : bb84_history_decoded h -> bb84_history_bob_outcome h i = None ->
  i \notin @trace_key_set V M (bb84_program_basis_value dev BasisX) (bb84_outcome_val None) h.1.
Proof. move=> Hdec Hbo. have Hround : bb84_history_round_decoded h i by move/forallP: Hdec; exact. case/and4P: Hround => _ _ _ Hy'.
  have Hoc : bb84_outcome_of (hist_y' h i) = Some None.
{ move: Hbo; rewrite /bb84_history_bob_outcome. by rewrite (bb84_outcome_of_decoded Hy'); case: (bb84_outcome_of _) => [[b|]|] //=. }
have Hyv : hist_y' h i = bb84_outcome_val None by apply: bb84_outcome_of_inv. by rewrite !inE /trace_key_round /trace_detected; apply/negP => /andP[_]; rewrite /hist_y' /hist_choice in Hyv; rewrite Hyv eqxx. Qed.
Fact key_sample_mass_undetected_zero (h : @run_history V M) (s : @store (bb84_cvar M) V) :
  bb84_history_decoded h -> #|bb84_key_set h| == nkey -> ~~ [forall j, bb84_key_data_w h j != None] -> bb84_collect_key_sample_mass h s = 0.
Proof. move=> Hdec /eqP HK; rewrite negb_forall => /existsP[j0]; rewrite negbK => /eqP Hj0. have HMpos : (0 < M)%N.
{ have [i _] := bb84_selected_index_some (esym HK) j0. exact: (leq_ltn_trans (leq0n i) (ltn_ord i)). }
have [i0 Hsel] := bb84_selected_index_some (esym HK) j0. have Hi0K : i0 \in bb84_key_set h := bb84_selected_index_mem Hsel.
  have Hbo : bb84_history_bob_outcome h i0 = None by move: Hj0; rewrite bb84_key_data_wE Hsel.
  have Hi0X := undetected_notin_trace_key_set Hdec Hbo. rewrite /bb84_collect_key_sample_mass /key_sample_mass; cbv beta.
  rewrite !bb84_basis_value_program (announce_trace_key_set h.1 s HMpos); case: ifP => _; last first.
{ have Hn1 : (0 < #|bb84_key_set h|)%N. by rewrite HK (leq_ltn_trans (leq0n j0) (ltn_ord j0)).
  have Hne : (@hist_K V M h == bb84_bot_val) = false.
  { apply/negbTE; apply/eqP => Hbot; move: Hn1. rewrite /bb84_key_set Hbot. by rewrite (_ : bb84_set_of bb84_bot_val = set0) ?cards0 //. }
by rewrite Hne. } apply: bb84_unif_nsubset_mass_outside. apply/nandP; right. by apply/negP => Hsub; move/subsetP: Hsub => Hsub; move: Hi0X; rewrite (Hsub i0 Hi0K). Qed.
Section HpeBridge.
Notation Cv := (bb84_cvar M).
Notation store := (@syntax.store Cv V).
Notation set_of := (@bb84_set_of M (bb84_n P) (bb84_l P) (cd_ir_bits dev) (cd_vseed_count dev) (cd_tag_count dev) (cd_paseed_count dev)).
Notation trace_key_set_of := (@trace_key_set V M (bb84_program_basis_value dev BasisX) (bb84_outcome_val None)).
Notation trace_test_set_of := (@trace_test_set V M (bb84_program_basis_value dev BasisZ) (bb84_outcome_val None)).
Notation start_dev s := (@start_store Cv V M (@BVX M) (@BVZ M) (@BVabort M) (@BVP M) bb84_empty_transcript_val bb84_bool_val
  bb84_set_val s).
Notation rounds_dev g s := (@rounds_store Cv V M (@BVa M) (@BVy M) (@BVb M) (@BVy' M) (@BVd M) (@BVX M) (@BVZ M)
  (bb84_basis_value dev BasisX) (bb84_basis_value dev BasisZ) (bb84_outcome_val None) bb84_bool_val bb84_set_val g (start_dev s)).
Notation announce_dev X := (@announce_store Cv V M (@BVa M) (@BVb M) (@BVd M) (@BVP M) bb84_tr_app_rounds X).
Notation paramest_dev g X := (@paramest_store Cv V M (@BVy M) (@BVy' M) (@BVZ M) (@BVK M) (@BVXA M) (@BVXB M)
  (@BVZA M) (@BVZB M) (@BVlam M) (@BVP M) bb84_set_of bb84_error_val bb84_tr_app_pe bb84_bits_on_val bb84_partial_bits_on_val
  bb84_err_count_val g X).
Notation sfin g s := (paramest_dev g (announce_dev (rounds_dev g s))).
Notation sann g s := (announce_dev (rounds_dev g s)).
Notation pe_failed_dev := (@pe_failed R Cv V nkey (bb84_k P) M (bb84_Qtol P) (@BVX M) (@BVZ M) (@BVlam M) bb84_set_of bb84_error_of).
Fact pe_pass_indicE (g : @run_history V M) (s : store) : bb84_collect_pe_pass_indic g s = ~~ pe_failed_dev (sfin g s).
Proof. by []. Qed.
Lemma sfin_Xv (g : @run_history V M) (s : store) : (0 < M)%N -> set_of (sfin g s (@BVX M)) = trace_key_set_of g.1.
Proof. move=> HM; have Hp : paramest_dev g (sann g s) (@BVX M) = sann g s (@BVX M).
{ by apply: paramest_store_other; cvne. } by rewrite Hp !bb84_basis_value_program; exact: (announce_trace_key_set g.1 s HM). Qed.
Lemma sfin_Zv (g : @run_history V M) (s : store) : (0 < M)%N -> set_of (sfin g s (@BVZ M)) = trace_test_set_of g.1.
Proof. move=> HM; have Hp : paramest_dev g (sann g s) (@BVZ M) = sann g s (@BVZ M).
{ by apply: paramest_store_other; cvne. } by rewrite Hp !bb84_basis_value_program; exact: (announce_trace_test_set g.1 s HM). Qed.
Lemma partial_bits_on_val_eq (K : {set 'I_M}) (f g : 'I_M -> V) :
  (forall i, i \in K -> f i = g i) -> bb84_partial_bits_on_val K f = bb84_partial_bits_on_val K g.
Proof. move=> Hfg; rewrite /bb84_partial_bits_on_val; congr bb84_partial_bits_val. apply/ffunP => i; rewrite !ffunE; case Hi: (i \in K);
  last by []. by rewrite Hfg. Qed.
Lemma sfin_lamv (g : @run_history V M) (s : store) : (0 < M)%N -> sfin g s (@BVlam M) = bb84_error_val (bb84_err_count_val
      (bb84_partial_bits_on_val (trace_test_set_of g.1) (fun i => hist_y g i))
      (bb84_partial_bits_on_val (trace_test_set_of g.1) (fun i => hist_y' g i))) #|trace_test_set_of g.1|.
Proof. have sann_y : forall (g : @run_history V M) (s : store) (i : 'I_M), sann g s (@BVy M i) = hist_y g i.
  { move=> {}g {}s i. rewrite announce_store_other; last by []. apply: rounds_store_y.
  - by move=> j _.
  - by move=> j.
  - by move=> j Hji; rewrite eq_sym.
  - by move=> j.
  - by move=> j.
  - by [].
  - by []. }
have sann_y' : forall (g : @run_history V M) (s : store) (i : 'I_M), sann g s (@BVy' M i) = hist_y' g i.
  { move=> {}g {}s i. rewrite announce_store_other; last by []. apply: rounds_store_y'.
  - by move=> j.
  - by move=> j.
  - by move=> j.
  - by move=> j Hji; rewrite eq_sym.
  - by move=> j.
  - by [].
  - by []. }
have paramest_lamv : forall (g : @run_history V M) (s' : store), paramest_dev g s' (@BVlam M) = bb84_error_val (bb84_err_count_val (bb84_partial_bits_on_val (bb84_set_of (s' (@BVZ M))) (fun i => s' (@BVy M i))) (bb84_partial_bits_on_val (bb84_set_of (s' (@BVZ M))) (fun i => s' (@BVy' M i)))) #|bb84_set_of (s' (@BVZ M))|.
{ clear s g; move=> g s'. rewrite /paramest_store. set s1 := store_set s' (@BVK M) (@hist_K V M g); set s2 := store_set s1 (@BVXA M) _.
  set s3 := store_set s2 (@BVXB M) _; set s4 := store_set s3 (@BVZA M) _. set s5 := store_set s4 (@BVZB M) _; set s6 := store_set s5 (@BVP M) _. rewrite store_set_same. have Hs3Zv : s3 (@BVZ M) = s' (@BVZ M).
{ rewrite /s3 store_set_other; last by rewrite /BVXB /BVZ; cvinr. rewrite /s2 store_set_other; last by rewrite /BVXA /BVZ; cvinr.
  by rewrite /s1 store_set_other // /BVK /BVZ; cvinr. } have Hs4Zv : s4 (@BVZ M) = s' (@BVZ M) by rewrite /s4 store_set_other; [rewrite Hs3Zv | rewrite /BVZA /BVZ; cvinr]. have Hs6Zv : s6 (@BVZ M) = s' (@BVZ M).
{ rewrite /s6 store_set_other; last by rewrite /BVP /BVZ; cvinr. rewrite /s5 store_set_other; last by rewrite /BVZB /BVZ; cvinr.
  by rewrite Hs4Zv. } have Hs3y : forall i, s3 (@BVy M i) = s' (@BVy M i).
{ move=> i; rewrite /s3 store_set_other // /s2 store_set_other // /s1 store_set_other //. }
have Hs4y' : forall i, s4 (@BVy' M i) = s' (@BVy' M i).
{ move=> i; rewrite /s4 store_set_other // /s3 store_set_other // /s2 store_set_other // /s1 store_set_other //. }
have Hs6ZA : s6 (@BVZA M) = bb84_partial_bits_on_val (bb84_set_of (s' (@BVZ M))) (fun i => s' (@BVy M i)).
{ rewrite /s6 store_set_other; last by rewrite /BVP /BVZA; cvinr. rewrite /s5 store_set_other; last by rewrite /BVZB /BVZA; cvinr.
  rewrite /s4 store_set_same Hs3Zv; congr (bb84_partial_bits_on_val _ _). by apply: funext => i; rewrite Hs3y. }
have Hs6ZB : s6 (@BVZB M) = bb84_partial_bits_on_val (bb84_set_of (s' (@BVZ M))) (fun i => s' (@BVy' M i)).
{ rewrite /s6 store_set_other; last by rewrite /BVP /BVZB; cvinr. rewrite /s5 store_set_same Hs4Zv; congr (bb84_partial_bits_on_val _ _).
  by apply: funext => i; rewrite Hs4y'. } by rewrite Hs6ZA Hs6ZB Hs6Zv. } move=> HM; rewrite paramest_lamv.
  have HZ : bb84_set_of (sann g s (@BVZ M)) = trace_test_set_of g.1.
{ rewrite !bb84_basis_value_program; exact: (announce_trace_test_set g.1 s HM). } rewrite HZ.
  have Hy : (fun i => sann g s (@BVy M i)) = (fun i => hist_y g i) by apply: funext => i; rewrite sann_y.
  have Hy' : (fun i => sann g s (@BVy' M i)) = (fun i => hist_y' g i) by apply: funext => i; rewrite sann_y'. by rewrite Hy Hy'. Qed.
Fact ksm_nonzero_key_sub (g : @run_history V M) (s : store) :
  (0 < M)%N -> bb84_collect_key_sample_mass g s != 0 -> bb84_key_set g \subset trace_key_set_of g.1.
Proof. move=> HM; rewrite /bb84_collect_key_sample_mass /key_sample_mass; cbv beta.
  rewrite !bb84_basis_value_program (announce_trace_key_set g.1 s HM); case: ifP => Hle.
- by move=> Hnz; move: (bb84_unif_nsubset_mass_support Hnz) => /andP[_ Hsub].
- move=> Hnz. have Hb : @hist_K V M g == bb84_bot_val. { move: Hnz; rewrite pnatr_eq0. by case: (@hist_K V M g == bb84_bot_val). }
by rewrite /bb84_key_set (eqP Hb); rewrite (_ : set_of bb84_bot_val = set0) ?sub0set //. Qed.
Lemma bb84_key_reround_M0 (h : @run_history V M) (x : 'I_(2 ^ nkey)) (w : bobout) : M = 0%N -> bb84_key_reround h x w = h.
Proof. move=> HM0; rewrite /bb84_key_reround [in RHS](surjective_pairing h). congr (_ , _). apply/ffunP => i; exfalso. by move: i;
  rewrite HM0 => j; move: (ltn_ord j); rewrite ltn0. Qed.
Fact bb84_trace_test_round_detected_reround (bZ : V) (rep : @run_history V M) (x x' : 'I_(2 ^ nkey)) (w w' : bobout) (i : 'I_M) :
  [forall j, w j != None] -> [forall j, w' j != None] -> @trace_test_round V M bZ (bb84_outcome_val None) (bb84_key_reround rep x w).1 i =
  @trace_test_round V M bZ (bb84_outcome_val None) (bb84_key_reround rep x' w').1 i.
Proof. move=> /forallP Hw /forallP Hw'; rewrite /trace_test_round /trace_detected !bb84_key_reroundE. case HiK: (i \in bb84_key_set rep);
  last by []. case: insubP => [j _ _ | _]; last by []. rewrite !bb84_choice_a_reround !bb84_choice_b_reround !bb84_choice_y'_reround.
  by rewrite (bb84_outcome_val_detected_neq (Hw j)) (bb84_outcome_val_detected_neq (Hw' j)). Qed.
Fact bb84_trace_test_set_detected_reround (bZ : V) (rep : @run_history V M) (x x' : 'I_(2 ^ nkey)) (w w' : bobout) :
  [forall j, w j != None] -> [forall j, w' j != None] -> @trace_test_set V M bZ (bb84_outcome_val None) (bb84_key_reround rep x w).1 =
  @trace_test_set V M bZ (bb84_outcome_val None) (bb84_key_reround rep x' w').1.
Proof. move=> Hw Hw'; apply/setP => i; rewrite !inE. exact: (@bb84_trace_test_round_detected_reround bZ rep x x' w w' i Hw Hw'). Qed.
Fact bb84_pe_pass_indic_detected_reround (h : @run_history V M) (s : store) (x x' : 'I_(2 ^ nkey)) (w w' : bobout) :
  (0 < M)%N -> [forall j, w j != None] -> [forall j, w' j != None] ->
  bb84_key_set h \subset trace_key_set_of h.1 -> bb84_collect_pe_pass_indic (bb84_key_reround h x w) s =
  bb84_collect_pe_pass_indic (bb84_key_reround h x' w') s.
Proof. have pe_failed_read_eq : forall (s1 s2 : store), set_of (s1 (@BVX M)) = set_of (s2 (@BVX M)) -> set_of (s1 (@BVZ M)) = set_of (s2
  (@BVZ M)) -> bb84_error_of (s1 (@BVlam M)) = bb84_error_of (s2 (@BVlam M)) -> pe_failed_dev s1 = pe_failed_dev s2.
{ clear w' w x' x s h; move=> s1 s2. move=> HX HZ Hl; rewrite /pe_failed /replay_pe_fail /replay_sift_ok /replay_pe_error_high.
  by rewrite HX HZ Hl. } move=> HM Hw Hw' Hsub; rewrite !pe_pass_indicE. suff Heq : pe_failed_dev (sfin (bb84_key_reround h x w) s) = pe_failed_dev (sfin (bb84_key_reround h x' w') s) by exact: (congr1 negb Heq). apply: pe_failed_read_eq.
- exact: (etrans (sfin_Xv (bb84_key_reround h x w) s HM) (etrans (@bb84_trace_key_set_detected_reround (bb84_program_basis_value dev BasisX) h x x' w w' Hw Hw') (esym (sfin_Xv (bb84_key_reround h x' w') s HM)))).
- exact: (etrans (sfin_Zv (bb84_key_reround h x w) s HM) (etrans (@bb84_trace_test_set_detected_reround (bb84_program_basis_value dev BasisZ) h x x' w w' Hw Hw') (esym (sfin_Zv (bb84_key_reround h x' w') s HM)))).
- have HZtr : trace_test_set_of (bb84_key_reround h x w).1 = trace_test_set_of (bb84_key_reround h x' w').1 by exact: (@bb84_trace_test_set_detected_reround (bb84_program_basis_value dev BasisZ) h x x' w w' Hw Hw').
  have Hdisj : forall i, i \in trace_test_set_of (bb84_key_reround h x' w').1 -> i \notin bb84_key_set h.
  { move=> i Hi. apply/negP => HiK. have HiX : i \in trace_key_set_of h.1 by move/subsetP: Hsub; apply. move: HiX; rewrite !inE /trace_key_round => /andP[/andP[/eqP HaX _] _]. move: Hi; rewrite !inE /trace_test_round => /andP[/andP[/eqP HaZ _] _].
    have Hae : choice_a ((bb84_key_reround h x' w').1 i) = choice_a (h.1 i).
    { rewrite bb84_key_reroundE. case: (i \in bb84_key_set h) => //. by case: insubP. } have Hneq : bb84_program_basis_value dev BasisX != bb84_program_basis_value dev BasisZ.
    { by rewrite /bb84_program_basis_value; exact: bb84_basis_bool_val_neq. } by move: Hneq; rewrite -HaX -Hae HaZ eqxx. }
have Herr : bb84_error_val (bb84_err_count_val (bb84_partial_bits_on_val (trace_test_set_of (bb84_key_reround h x w).1) (fun i => hist_y (bb84_key_reround h x w) i)) (bb84_partial_bits_on_val (trace_test_set_of (bb84_key_reround h x w).1) (fun i => hist_y' (bb84_key_reround h x w) i))) #|trace_test_set_of (bb84_key_reround h x w).1| = bb84_error_val (bb84_err_count_val (bb84_partial_bits_on_val (trace_test_set_of (bb84_key_reround h x' w').1) (fun i => hist_y (bb84_key_reround h x' w') i)) (bb84_partial_bits_on_val (trace_test_set_of (bb84_key_reround h x' w').1) (fun i => hist_y' (bb84_key_reround h x' w') i))) #|trace_test_set_of (bb84_key_reround h x' w').1|.
  { have Ey : bb84_partial_bits_on_val (trace_test_set_of (bb84_key_reround h x w).1) (fun i => hist_y (bb84_key_reround h x w) i) = bb84_partial_bits_on_val (trace_test_set_of (bb84_key_reround h x' w').1) (fun i => hist_y (bb84_key_reround h x' w') i).
    { rewrite HZtr; apply: partial_bits_on_val_eq => i Hi. have HiK := Hdisj i Hi. by rewrite /hist_y /hist_choice !(bb84_key_reround_notin _ _ HiK). } have Ey' : bb84_partial_bits_on_val (trace_test_set_of (bb84_key_reround h x w).1) (fun i => hist_y' (bb84_key_reround h x w) i) = bb84_partial_bits_on_val (trace_test_set_of (bb84_key_reround h x' w').1) (fun i => hist_y' (bb84_key_reround h x' w') i).
    { rewrite HZtr; apply: partial_bits_on_val_eq => i Hi. have HiK := Hdisj i Hi. by rewrite /hist_y' /hist_choice !(bb84_key_reround_notin _ _ HiK). } by rewrite Ey Ey' HZtr. } have Hlam : sfin (bb84_key_reround h x w) s (@BVlam M) = sfin (bb84_key_reround h x' w') s (@BVlam M).
  { apply: (etrans (sfin_lamv (bb84_key_reround h x w) s HM)). rewrite Herr. exact: (esym (sfin_lamv (bb84_key_reround h x' w') s HM)). }
exact: (congr1 bb84_error_of Hlam). Qed.
Fact bb84_pe_pass_indic_reround (h : @run_history V M) (s : store) (x : 'I_(2 ^ nkey)) (w : bobout) :
  bb84_history_decoded h -> #|bb84_key_set h| = nkey -> [forall j, w j != None] ->
  [forall j, bb84_key_data_w h j != None] -> bb84_collect_key_sample_mass h s != 0 ->
  bb84_collect_pe_pass_indic (bb84_key_reround h x w) s = bb84_collect_pe_pass_indic h s.
Proof. move=> Hdec Hfull Hdet Hdetw Hksm; case: (posnP M) => [HM0 | HM].
- by rewrite (bb84_key_reround_M0 h x w HM0).
- have Hsub := ksm_nonzero_key_sub HM Hksm. transitivity (bb84_collect_pe_pass_indic (bb84_key_reround h (bb84_key_data_x h) (bb84_key_data_w h)) s).
  + exact: (@bb84_pe_pass_indic_detected_reround h s x (bb84_key_data_x h) w (bb84_key_data_w h) HM Hdet Hdetw Hsub).
  + by rewrite (bb84_key_reroundK Hdec Hfull). Qed.
End HpeBridge.
Fact bb84_eb_class_det_state_traceRe (EA : @adversary R L HL V Eve) (pair : 'M[C]_(4 * 2)) (xi : @cq_state R L HL (bb84_cvar M) V) :
  bb84_eb_pair_ptr_ok pair -> bb84_eb_pair_x_branch_ok dev pair -> @complex.Re R (\Tr (bb84_eb_class_det_state EA pair xi)) =
  bb84_source_pass_prob EA xi.
Proof. have bb84_key_data_x_reround : forall (h : @run_history V M) (x : 'I_(2 ^ nkey)) (w : bobout), #|bb84_key_set h| = nkey ->
  bb84_key_data_x (bb84_key_reround h x w) = x.
  { move=> h x w. move=> HK; apply: eq_from_bit_of_ord => j. rewrite bb84_key_data_xE bb84_key_reround_key_set.
    have [i Hsel] := bb84_selected_index_some (esym HK) j. rewrite Hsel. have HiK : i \in bb84_key_set h := bb84_selected_index_mem Hsel.
    have Hidx : index i (enum (bb84_key_set h)) = j by apply: bb84_selected_index_inv. have [Hy _] := bb84_key_reround_y x w HK HiK Hidx.
    by rewrite /bb84_history_alice_bit Hy bb84_bit_of_val. }
have bb84_key_data_w_reround : forall (h : @run_history V M) (x : 'I_(2 ^ nkey)) (w : bobout), #|bb84_key_set h| = nkey -> bb84_key_data_w (bb84_key_reround h x w) = w.
  { move=> h x w. have bb84_outcome_of_val : forall (o : option bool), bb84_outcome_of (bb84_outcome_val o : V) = Some o.
  { clear w x h; move=> o. by []. }
move=> HK; apply/ffunP=> j. rewrite bb84_key_data_wE bb84_key_reround_key_set. have [i Hsel] := bb84_selected_index_some (esym HK) j.
    rewrite Hsel. have HiK : i \in bb84_key_set h := bb84_selected_index_mem Hsel. have Hidx : index i (enum (bb84_key_set h)) = j by apply: bb84_selected_index_inv. have [_ Hy'] := bb84_key_reround_y x w HK HiK Hidx.
    by rewrite /bb84_history_bob_outcome Hy' bb84_outcome_of_val. }
have bb84_eb_class_det_state_traceE_pass : forall (EA : @adversary R L HL V Eve) (pair : 'M[C]_(4 * 2)) (xi : @cq_state R L HL (bb84_cvar M) V), \Tr (bb84_eb_class_det_state EA pair xi) = \Tr (bb84_eb_readout_pass_state EA pair xi).
{ clear xi pair EA; move=> EA pair xi. have bb84_eb_class_det_state_traceE : forall (EA : @adversary R L HL V Eve) (pair : 'M[C]_(4 * 2)) (xi : @cq_state R L HL (bb84_cvar M) V), \Tr (bb84_eb_class_det_state EA pair xi) = \sum_s \sum_(h : @run_history V M) (((bb84_collect_pe_pass_indic h s)%:R * bb84_collect_key_sample_mass h s * (bb84_eb_canon h && bb84_seed_unused_hist h)%:R)%:C * (\sum_(x : 'I_(2 ^ nkey)) \sum_(w : bobout | [forall j, w j != None]) \Tr (bb84_deferred_readout_so dev HE x w (bb84_eb_history_state EA pair h (xi s))))).
{ clear xi pair EA; move=> EA pair xi. have bb84_detect_so_traceE : forall (st : 'F[HL]_setT), \Tr (bb84_detect_so st) = \sum_(x : 'I_(2 ^ nkey)) \sum_(w : bobout | [forall j, w j != None]) \Tr (bb84_deferred_readout_so dev HE x w st).
{ clear xi pair EA; move=> st. have bb84_M_click_sqrt_psd : bb84_M_click_sqrt \is psdmx.
{ clear st; apply: mapf_mx_psdP; first exact: bb84_M_click_psd. by move=> x Hx; rewrite sqrtC_ge0. }
have bb84_click_bob_lf_total : (bb84_click_bob_lf)^A \o bb84_click_bob_lf = bb84_M_click_total_lf.
  { have bb84_M_click_sqrtK : (bb84_M_click_sqrt)^*t *m bb84_M_click_sqrt = bb84_M_click.
    { have /hermmxP HadjE := psdmx_herm bb84_M_click_sqrt_psd. rewrite -{1}HadjE /bb84_M_click_sqrt.
      exact: (mapf_mx_sqrt (hermmx_normal (psdmx_herm bb84_M_click_psd))). } rewrite /bb84_click_bob_lf /bb84_M_click_total_lf regmx_lf_adj regmx_lf_comp bitprod_mx_adj bitprod_mx_mul. congr (regmx_lf dimBq (bitprod_mx _)). by apply/funext => j; exact: bb84_M_click_sqrtK. }
transitivity (\Tr (liftf_lf bb84_M_click_total_lf \o st)).
  { rewrite /bb84_detect_so formsoE lftraceC comp_lfunA. by rewrite -liftf_lf_adj -liftf_lf_comp bb84_click_bob_lf_total. }
have branch_tr : forall (x : 'I_(2 ^ nkey)) (w : bobout), \Tr (bb84_deferred_readout_so dev HE x w st) = \Tr (((liftf_lf (bb84_deferred_alice_lf dev HE x))^A \o liftf_lf (bb84_deferred_alice_lf dev HE x)) \o (liftf_lf (bb84_deferred_bob_lf dev HE w) \o st \o (liftf_lf (bb84_deferred_bob_lf dev HE w))^A)).
  { move=> x w. rewrite /bb84_deferred_readout_so comp_soE !formsoE. by rewrite lftraceC !comp_lfunA. }
under eq_bigr do under eq_bigr do rewrite branch_tr. rewrite exchange_big /=. have inner : forall w : bobout, \sum_(x : 'I_(2 ^ nkey)) \Tr (((liftf_lf (bb84_deferred_alice_lf dev HE x))^A \o liftf_lf (bb84_deferred_alice_lf dev HE x)) \o (liftf_lf (bb84_deferred_bob_lf dev HE w) \o st \o (liftf_lf (bb84_deferred_bob_lf dev HE w))^A)) = \Tr (liftf_lf (bb84_deferred_bob_lf dev HE w) \o st \o (liftf_lf (bb84_deferred_bob_lf dev HE w))^A).
  { move=> w. rewrite -linear_sum /= -linear_sumlz /=. by rewrite bb84_alice_lift_complete_loc comp_lfun1l. }
under eq_bigr do rewrite inner. have bob_tr : forall w : bobout, \Tr (liftf_lf (bb84_deferred_bob_lf dev HE w) \o st \o (liftf_lf (bb84_deferred_bob_lf dev HE w))^A) = \Tr (((liftf_lf (bb84_deferred_bob_lf dev HE w))^A \o liftf_lf (bb84_deferred_bob_lf dev HE w)) \o st).
  { by move=> w; rewrite lftraceC !comp_lfunA. } under eq_bigr do rewrite bob_tr. rewrite -linear_sum /= -linear_sumlz /=.
    by rewrite bb84_bob_detected_lift_complete_loc. } rewrite /bb84_eb_class_det_state linear_sum /=; apply: eq_bigr => s _.
    rewrite linear_sum /=; apply: eq_bigr => h _. rewrite linearZ /=. by rewrite bb84_detect_so_traceE. }
rewrite bb84_eb_class_det_state_traceE /bb84_eb_readout_pass_state linear_sum /=; apply: eq_bigr => s _. rewrite linear_sum /=.
    under [X in _ = X]eq_bigr => h _ do rewrite linearZ /=. rewrite /bb84_eb_canon /bb84_seed_unused_hist.
    apply: (@av_orbit_reindex R (bb84_cvar M) V M (bb84_n P) (bb84_k P) (cd_ir_bits dev) (bb84_Qtol P) (@BVa M) (@BVy M) (@BVb M) (@BVy' M) (@BVd M) (@BVX M) (@BVZ M) (@BVK M) (@BVXA M) (@BVXB M) (@BVZA M) (@BVZB M) (@BVlam M) (@BVpec M) (@BVXhat M) (@BVg M) (@BVtA M) (@BVtB M) (@BVabort M) (@BVP M) (bb84_basis_value dev BasisX) (bb84_basis_value dev BasisZ) (bb84_outcome_val None) bb84_bot_val bb84_empty_transcript_val bb84_bool_val bb84_set_val bb84_set_of bb84_error_val bb84_tr_app_rounds bb84_tr_app_pe bb84_tr_app_ec bb84_bits_on_val bb84_partial_bits_on_val bb84_err_count_val bb84_error_of bb84_unif_nsubset_mass (bb84_ir_pub_val (@cd_ir_pub R P q dev)) (bb84_ir_dec_val (@cd_ir_dec R P q dev)) bb84_unif_vseed_mass (bb84_verify_hash_val (@cd_vh R P q dev)) bb84_unif_pseed_mass s ('I_(2 ^ nkey)) _ (@bb84_key_reround R P q dev) _ _ (@bb84_history_decoded R P q dev) (fun h => #|bb84_key_set h| == bb84_n P) _ _ _ _ _).
- by move=> h x w /eqP HK; exact: bb84_key_data_x_reround.
- by move=> h x w /eqP HK; exact: bb84_key_data_w_reround.
- by move=> h Hd /eqP HK; exact: bb84_key_reroundK.
- by move=> h x w x' w'; exact: bb84_key_reround_reround.
- by move=> h x w; rewrite bb84_key_reround_key_set. 1,2: by [].
- by move=> h x w x' w'; exact: bb84_history_decoded_reround2.
- move=> h x w Hcanon Hdec /eqP Hfull Hdet Hksm. have Hkdw : [forall j, bb84_key_data_w h j != None] by case/andP: Hcanon => _ /eqP ->; apply/forallP => j; rewrite ffunE. apply: (congr1 (fun b : bool => (b%:R : R))). exact: (@bb84_pe_pass_indic_reround h s x w Hdec Hfull Hdet Hkdw Hksm).
- move=> h x w x' w' Hw Hw'. case: (posnP M) => [HM0 | HM].
  + by rewrite (bb84_key_reround_M0 h x w HM0) (bb84_key_reround_M0 h x' w' HM0).
  + exact: (@bb84_key_sample_mass_detected_reround_const h s x x' w w' HM Hw Hw').
- by apply/forallP => j; rewrite ffunE.
- by move=> x w h x1 w1 x2 w2; rewrite (bb84_eb_history_state_reround EA pair h x1 x2 w1 w2 (xi s)).
- move=> x w h Hn. rewrite (_ : bb84_eb_history_state EA pair h (xi s) = 0) ?/fun_of_superof ?linear0 //.
  by rewrite /bb84_eb_history_state (negbTE Hn).
- by move=> h Hd Hf Hn; exact: (@key_sample_mass_undetected_zero h s Hd Hf Hn).
- move=> h h' H1 HK. apply: (congr1 (fun b : bool => (b%:R : R))). exact: (@pe_pass_indic_hist_ext h h' s H1 HK).
- by move=> h h' H1 HK; exact: (bb84_readout_trace_ext EA pair (xi s) H1 HK).
- by move=> s'; exact: (bb84_unif_vseed_mass_sum1 s' (cd_vseed_pos dev)).
- by move=> s'; exact: (bb84_unif_pseed_mass_sum1 s' (cd_paseed_pos dev)). } by move=> Hptr Hbr; rewrite bb84_eb_class_det_state_traceE_pass bb84_eb_readout_pass_state_traceRe. Qed.
Definition rhoSrc_SEB_sigdet (EA : @adversary R L HL V Eve) (pair : 'M[C]_(4 * 2)) (xi : @cq_state R L HL (bb84_cvar M) V) :
    'M[C]_(((2 ^ nkey) * dim ('H[HL]_Ereg)) * (2 ^ nkey)) := castmx (esym (@bb84_dim_SEB R P q dev LE HE),
          esym (@bb84_dim_SEB R P q dev LE HE)) (h2mx (((bb84_source_pass_prob EA xi)^-1)%:C *: rhoSrc_SEB_sigdet_lf EA pair xi)).
Definition rhoXE_sigdet (EA : @adversary R L HL V Eve) (pair : 'M[C]_(4 * 2)) (xi : @cq_state R L HL (bb84_cvar M) V)
    (nx : nat) (Mx : 'I_nx -> 'M[C]_(2 ^ nkey)) (dim_X : nx = dim ('H[HL]_Sreg)) : 'F[HL]_(Sreg :|: Ereg) :=
  eur_rho_XB (bb84_disSE P LE) (rhoSrc_SEB_sigdet EA pair xi) Mx (bb84_register_pair_dim (bb84_disSE P LE) dim_X erefl).
Definition rhoZB_sigdet (EA : @adversary R L HL V Eve) (pair : 'M[C]_(4 * 2)) (xi : @cq_state R L HL (bb84_cvar M) V) :
    'F[HL]_(Zreg :|: Bqreg) := eur_rho_ZC (bb84_disZBq P LE) (rhoSrc_SEB_sigdet EA pair xi) (@std_projective_povm R (2 ^ nkey))
    (bb84_register_pair_dim (bb84_disZBq P LE) (@bb84_dim_Zkey R P q dev LE HE) (@bb84_dim_Bq R P q dev LE HE)).
Lemma rhoSrc_SEB_sigdet_lf_traceRe (EA : @adversary R L HL V Eve) (pair : 'M[C]_(4 * 2)) (xi : @cq_state R L HL (bb84_cvar M) V) :
  bb84_eb_pair_ptr_ok pair -> bb84_eb_pair_x_branch_ok dev pair -> @complex.Re R (\Tr (rhoSrc_SEB_sigdet_lf EA pair xi)) =
  bb84_source_pass_prob EA xi.
Proof. move=> Hptr Hbr; rewrite /rhoSrc_SEB_sigdet_lf /ptrace_cast_gen castlf_trlfE. have /cptpP [_ /tpmapP Htp] := @ptraceso_qc R L HL
  (mathcomp.boot.finset.setC ((Sreg :|: Ereg) :|: Bqreg)) (setTfor L). by rewrite Htp; rewrite bb84_eb_class_det_state_traceRe. Qed.
Lemma rhoSrc_SEB_sigdet_den1mx (EA : @adversary R L HL V Eve) (pair : 'M[C]_(4 * 2)) (xi : @cq_state R L HL (bb84_cvar M) V) :
  pair \is den1mx -> bb84_eb_pair_ptr_ok pair -> bb84_eb_pair_x_branch_ok dev pair ->
  0 < bb84_source_pass_prob EA xi -> (forall s, xi s \is psdlf) -> rhoSrc_SEB_sigdet EA pair xi \is den1mx.
Proof. have rhoSrc_SEB_sigdet_norm_lf_den1lf : forall (EA : @adversary R L HL V Eve) (pair : 'M[C]_(4 * 2)) (xi : @cq_state R L HL
  (bb84_cvar M) V), pair \is den1mx -> bb84_eb_pair_ptr_ok pair -> bb84_eb_pair_x_branch_ok dev pair -> 0 < bb84_source_pass_prob EA xi -> (forall s, xi s \is psdlf) -> ((bb84_source_pass_prob EA xi)^-1)%:C *: rhoSrc_SEB_sigdet_lf EA pair xi \is den1lf.
{ clear xi pair EA; move=> EA pair xi. have rhoSrc_SEB_sigdet_norm_lf_traceRe1 : forall (EA : @adversary R L HL V Eve) (pair : 'M[C]_(4 * 2)) (xi : @cq_state R L HL (bb84_cvar M) V), bb84_eb_pair_ptr_ok pair -> bb84_eb_pair_x_branch_ok dev pair -> 0 < bb84_source_pass_prob EA xi -> @complex.Re R (\Tr (((bb84_source_pass_prob EA xi)^-1)%:C *: rhoSrc_SEB_sigdet_lf EA pair xi)) = 1.
{ clear xi pair EA; move=> EA pair xi. move=> Hptr Hbr Hpos; rewrite linearZ /=. have HRe_realM : forall (r : R) (z : C), @complex.Re R (r%:C * z) = r * @complex.Re R z.
  { move=> r z. by case: z => zr zi /=; rewrite mul0r subr0. } rewrite HRe_realM rhoSrc_SEB_sigdet_lf_traceRe //.
    by rewrite mulVf ?lt0r_neq0. } move=> Hpair Hptr Hbr Hpos Hxi. have Hpsd : ((bb84_source_pass_prob EA xi)^-1)%:C *: rhoSrc_SEB_sigdet_lf EA pair xi \is psdlf.
  { apply: psdlfZ.
    - rewrite lecR invr_ge0. exact: ltW Hpos.
    - exact: (rhoSrc_SEB_sigdet_lf_psd EA Hpair Hxi). } apply/den1lfP; split; first exact: Hpsd.
      have Hreal : \Tr (((bb84_source_pass_prob EA xi)^-1)%:C *: rhoSrc_SEB_sigdet_lf EA pair xi) \is Num.real := ger0_real (psdlf_trlf Hpsd). by rewrite -(RRe_real Hreal) rhoSrc_SEB_sigdet_norm_lf_traceRe1. } move=> Hpair Hptr Hbr Hpos Hxi.
      have Hden1 : ((bb84_source_pass_prob EA xi)^-1)%:C *: rhoSrc_SEB_sigdet_lf EA pair xi \is den1lf.
  { by apply: rhoSrc_SEB_sigdet_norm_lf_den1lf; assumption. } move/den1lfP: Hden1 => [Hpsd Htr]. apply/den1mxP; split.
  - rewrite /rhoSrc_SEB_sigdet. apply: castmx_sq_psdmx. by move: Hpsd; rewrite qualifE.
  - apply/eqP. by rewrite /rhoSrc_SEB_sigdet mxtrace_castmx_sq -/(\Tr (((bb84_source_pass_prob EA xi)^-1)%:C *: rhoSrc_SEB_sigdet_lf EA pair xi)) Htr. Qed.
Fact rhoZB_sigdet_psd (EA : @adversary R L HL V Eve) (pair : 'M[C]_(4 * 2)) (xi : @cq_state R L HL (bb84_cvar M) V) :
  pair \is den1mx -> bb84_eb_pair_ptr_ok pair -> bb84_eb_pair_x_branch_ok dev pair ->
  0 < bb84_source_pass_prob EA xi -> (forall s, xi s \is psdlf) -> rhoZB_sigdet EA pair xi \is psdlf.
Proof. move=> Hpair Hptr Hbr Hpos Hxi; have Hden1 : rhoSrc_SEB_sigdet EA pair xi \is den1mx.
  { by apply: rhoSrc_SEB_sigdet_den1mx; assumption. }
rewrite /rhoZB_sigdet. apply: eur_rho_ZC_psd; [exact: std_projective_povm_is_povm | exact: Hden1]. Qed.
Fact bb84_program_uncertainty_sigdet (EA : @adversary R L HL V Eve) (pair : 'M[C]_(4 * 2)) (xi : @cq_state R L HL (bb84_cvar M) V)
    (eps' : R) : (0 < nkey)%N -> rhoSrc_SEB_sigdet EA pair xi \is denmx -> 0 <= eps' ->
  eps' < Num.sqrt (@complex.Re R (\tr (rhoSrc_SEB_sigdet EA pair xi))) -> smooth_hmin Ereg eps' (@rhoXE_sigdet EA pair xi (2 ^ nkey)
      (@bb84_source_x_povm R P q (@cd_src R P q dev) (@cd_src_dim_A R P q dev) (@cd_src_dim_X R P q dev)) (@bb84_dim_S R P q dev LE HE)) +
  smooth_hmax Bqreg eps' (rhoZB_sigdet EA pair xi) >= nkey%:R * q.
Proof. move=> Hn Hden Heps0 Heps_lt; rewrite /rhoXE_sigdet /rhoZB_sigdet. have HM : is_povm_mx (@bb84_source_x_povm R P q (@cd_src R P q
  dev) (@cd_src_dim_A R P q dev) (@cd_src_dim_X R P q dev)).
  { exact: (@bb84_source_x_povm_is_povm R P q (@cd_src R P q dev) (@cd_src_dim_A R P q dev) (@cd_src_dim_X R P q dev)). }
have Hoverlap : nkey%:R * q <= q_of_mx (@bb84_source_x_povm R P q (@cd_src R P q dev) (@cd_src_dim_A R P q dev) (@cd_src_dim_X R P q dev)) (@std_projective_povm R (2 ^ nkey)). { exact: (@cd_src_overlap_standard_z R P q dev). }
have HN : is_povm_mx (@std_projective_povm R (2 ^ nkey)) := @std_projective_povm_is_povm R _.
    have Heur := @entropic_uncertainty_relation_bb84 R L HL Sreg Ereg Zreg Bqreg (bb84_disSE P LE) (bb84_disSZ P LE) (bb84_disSBq P LE) (bb84_disEZ P LE) (bb84_disEBq P LE) (bb84_disZBq P LE) nkey eps' q (2 ^ nkey) (dim ('H[HL]_Ereg)) (2 ^ nkey) (2 ^ nkey) (2 ^ nkey) (rhoSrc_SEB_sigdet EA pair xi) (@bb84_source_x_povm R P q (@cd_src R P q dev) (@cd_src_dim_A R P q dev) (@cd_src_dim_X R P q dev)) (@std_projective_povm R (2 ^ nkey)) (bb84_register_pair_dim (bb84_disSE P LE) (@bb84_dim_S R P q dev LE HE) erefl) (bb84_register_pair_dim (bb84_disZBq P LE) (@bb84_dim_Zkey R P q dev LE HE) (@bb84_dim_Bq R P q dev LE HE)) (@bb84_dim_S R P q dev LE HE) erefl (@bb84_dim_Zkey R P q dev LE HE) (@bb84_dim_Bq R P q dev LE HE) Hn Hden Heps0 Heps_lt HM HN Hoverlap. exact: Heur. Qed.
End DeferredHistoryCollapse.
Section BB84ProgramHmaxGeneric.
Variable (R : realType).
Notation C := (@hermitian.C R).
Notation chsType := (@chsType R).
Variable (L : finType) (HL : L -> chsType).
Variables (Zkey Bq Zp : {set L}).
Hypotheses (disZBq : [disjoint Zkey & Bq]) (disZZp : [disjoint Zkey & Zp]).
Variable (Aux : @bb84_aux_regs R L HL Zkey Bq Zp).
Variables (P : @bb84_protocol R) (G : @bb84_zsource R P) (eps : R).
Hypotheses (dim_Zk_key : (2 ^ bb84_n P)%N = dim ('H[HL]_Zkey)) (dim_Bq_key : (2 ^ bb84_n P)%N = dim ('H[HL]_Bq)).
Hypotheses (dim_Zp_key : (2 ^ bb84_n P)%N = dim ('H[HL]_Zp)).
Definition prog_hmax_dimZBq := bb84_register_pair_dim disZBq dim_Zk_key dim_Bq_key.
Definition prog_hmax_rhoZB : 'F[HL]_(Zkey :|: Bq) := eur_rho_ZC disZBq (bb84_cond_rho G)
    (@std_projective_povm R (2 ^ bb84_n P)) prog_hmax_dimZBq.
Fact bb84_program_hmax_mx_from_zsource : (0 < bb84_n P)%N -> (0 < bb84_k P)%N -> 0 < eps -> 0 < bb84_p_pass_tot G ->
  eps / Num.sqrt (bb84_p_pass_tot G) < 1 -> smooth_hmax_mx (eps / Num.sqrt (bb84_p_pass_tot G)) (biprod_mx disZBq prog_hmax_rhoZB)
    <= (bb84_n P)%:R * bb84_h_trunc (bb84_Qtol P + bb84_mu (bb84_n P) (bb84_k P) eps).
Proof. have bb84_program_hmax_from_zsource : (0 < bb84_n P)%N -> (0 < bb84_k P)%N -> 0 < eps -> 0 < bb84_p_pass_tot G -> eps / Num.sqrt
  (bb84_p_pass_tot G) < 1 -> smooth_hmax Bq (eps / Num.sqrt (bb84_p_pass_tot G)) prog_hmax_rhoZB <= (bb84_n P)%:R * bb84_h_trunc (bb84_Qtol P + bb84_mu (bb84_n P) (bb84_k P) eps).
{ move=> Hn_pos Hk_pos Heps_pos Hpass_pos Heps'_lt1; set eps' := eps / Num.sqrt (bb84_p_pass_tot G). set rhoZB := prog_hmax_rhoZB; pose rhoZZp := bb84_rhoZZ_pass_mixH disZZp G dim_Zk_key dim_Zp_key. have rho_den1 : bb84_cond_rho G \is den1mx := bb84_cond_rho_den1 Hpass_pos. have Heps'_nn : 0 <= eps' by rewrite /eps'; apply: divr_ge0; [exact: ltW | exact: sqrtr_ge0]. have HtrZB_eq1 : \Tr rhoZB = 1.
  { rewrite /rhoZB /prog_hmax_rhoZB. exact: (eur_rho_ZC_tr1 disZBq prog_hmax_dimZBq (@std_projective_povm_is_povm R (2 ^ bb84_n P)) rho_den1). } have HrhoZB_tr1R : @complex.Re R (\Tr rhoZB) = 1 by rewrite HtrZB_eq1 re_realid.
    have Heps'_lt_TrZB : eps' < Num.sqrt (@complex.Re R (\Tr rhoZB)) by rewrite HrhoZB_tr1R sqrtr1.
    have HrhoZZp_psd : rhoZZp \is psdlf by rewrite /rhoZZp; exact: (@bb84_rhoZZ_pass_mixH_psd R L HL Zkey Zp disZZp P G dim_Zk_key dim_Zp_key Hpass_pos). have Htransport : smooth_hmax Bq eps' rhoZB <= smooth_hmax Zp eps' rhoZZp.
  { set dim_BqZp := etrans (esym dim_Bq_key) dim_Zp_key. pose BobZ := bob_z_basis_qchannel (bob_z_canonical_readout dim_BqZp).
    have Hreadout := @bb84_delayed_measurement_of_zsource R L HL Zkey Bq Zp disZBq disZZp P G Hpass_pos dim_Zk_key dim_Bq_key dim_Zp_key.
    exact: (@bb84_delayed_measurement_hmax R L HL Zkey Bq Zp disZBq disZZp Aux eps' BobZ _ _ Heps'_nn Heps'_lt_TrZB Hreadout). }
apply: le_trans Htransport _. have Hstruct_mix := @bb84_rhoZZ_pass_mixH_biprod R L HL Zkey Zp disZZp P G dim_Zk_key dim_Zp_key.
    exact: (@qkd.bb84.prop.stat_mix R L HL Zkey Zp disZZp P G eps rhoZZp dim_Zk_key dim_Zp_key Hn_pos Hk_pos Heps_pos HrhoZZp_psd Hpass_pos Heps'_lt1 Hstruct_mix). } move=> Hn_pos Hk_pos Heps_pos Hpass_pos Heps'_lt1; have Hpsd : prog_hmax_rhoZB \is psdlf.
  { rewrite /prog_hmax_rhoZB. exact: (eur_rho_ZC_psd disZBq prog_hmax_dimZBq (@std_projective_povm_is_povm R (2 ^ bb84_n P)) (bb84_cond_rho_den1 Hpass_pos)). } by rewrite -(entropy.prop.smooth_hmax_labelled_mx disZBq _ Hpsd); exact: bb84_program_hmax_from_zsource. Qed.
End BB84ProgramHmaxGeneric.
Section BB84GapTWitness.
Variable (R : realType).
Notation chsType := (@chsType R).
Variable (P : @bb84_protocol R).
Local Notation dn := (2 ^ bb84_n P)%N.
Definition gapt_d (i : 'I_10) : nat := match val i with | 0 => dn | 1 => dn | 2 => dn | 3 => dn * dn | 4 => dn * dn
  | 5 => (dn * (dn * dn)) * (dn * (dn * dn)) | 6 => dn | 7 => ((dn * (dn * dn)) * (dn * (dn * dn))) * dn | 8 => dn * (dn * dn)
  | _ => ((dn * (dn * dn)) * (dn * (dn * dn))) * (dn * (dn * dn)) end.
Fact gapt_d_gt0 (i : 'I_10) : (0 < gapt_d i)%N.
Proof. rewrite /gapt_d; case: (val i) => [|[|[|[|[|[|[|[|[|?]]]]]]]]] //=; by rewrite ?muln_gt0 expn_gt0. Qed.
Definition gapt_HL (i : 'I_10) : chsType := @inhabited.ihb_chsType R 'I_((gapt_d i).-1.+1).
Lemma gapt_reg_dim (i : 'I_10) : dim 'H[gapt_HL]_[set i] = gapt_d i.
Proof. by rewrite dim_setten big_set1 /gapt_HL -inhabited.ihb_dim_cast card_ord (prednK (gapt_d_gt0 i)). Qed.
Local Notation gZk  := [set (@Ordinal 10 0 isT)].
Local Notation gBq  := [set (@Ordinal 10 1 isT)].
Local Notation gZp  := [set (@Ordinal 10 2 isT)].
Local Notation gapp := [set (@Ordinal 10 3 isT)].
Local Notation gbpp := [set (@Ordinal 10 4 isT)].
Local Notation gciso := [set (@Ordinal 10 5 isT)].
Local Notation gcp_src := [set (@Ordinal 10 6 isT)].
Local Notation gcpp_src := [set (@Ordinal 10 7 isT)].
Local Notation gcp_tgt := [set (@Ordinal 10 8 isT)].
Local Notation gcpp_tgt := [set (@Ordinal 10 9 isT)].
Local Ltac gdisj := apply/disjointP => x; rewrite !inE; (move=> /eqP -> || move=> /orP[] /eqP ->); rewrite ?inE.
Definition gapt_Aux : @bb84_aux_regs R 'I_10 gapt_HL gZk gBq gZp.
Proof. have dZkBq : [disjoint gZk & gBq] by gdisj. have dZkApp : [disjoint gZk & gapp] by gdisj.
  have dZpBpp : [disjoint gZp & gbpp] by gdisj. have dZAppZpBpp : [disjoint gZk :|: gapp & gZp :|: gbpp] by gdisj.
  have eZk : dim 'H[gapt_HL]_gZk = dn by rewrite gapt_reg_dim. have eBq : dim 'H[gapt_HL]_gBq = dn by rewrite gapt_reg_dim.
  have eZp : dim 'H[gapt_HL]_gZp = dn by rewrite gapt_reg_dim. have eApp : dim 'H[gapt_HL]_gapp = (dn * dn)%N by rewrite gapt_reg_dim.
  have eBpp : dim 'H[gapt_HL]_gbpp = (dn * dn)%N by rewrite gapt_reg_dim. have eCiso : dim 'H[gapt_HL]_gciso = ((dn * (dn * dn)) * (dn * (dn
  * dn)))%N by rewrite gapt_reg_dim. have eCpSrc : dim 'H[gapt_HL]_gcp_src = dn by rewrite gapt_reg_dim.
  have eCppSrc : dim 'H[gapt_HL]_gcpp_src = (((dn * (dn * dn)) * (dn * (dn * dn))) * dn)%N by rewrite gapt_reg_dim.
  have eCpTgt : dim 'H[gapt_HL]_gcp_tgt = (dn * (dn * dn))%N by rewrite gapt_reg_dim. have eCppTgt : dim 'H[gapt_HL]_gcpp_tgt = (((dn * (dn
  * dn)) * (dn * (dn * dn))) * (dn * (dn * dn)))%N by rewrite gapt_reg_dim. have Hdn : (0 < dn)%N by rewrite expn_gt0.
  have Hdn2 : (0 < dn * dn)%N by rewrite muln_gt0 !expn_gt0. have HD5 : (0 < (dn * (dn * dn)) * (dn * (dn * dn)))%N by rewrite !muln_gt0 !expn_gt0. have HdnLe : (dn <= dn * (dn * dn))%N by apply: leq_pmulr; exact: Hdn2. refine (@BB84AuxRegs R 'I_10 gapt_HL gZk gBq gZp gapp gbpp gciso gcp_src gcpp_src gcp_tgt gcpp_tgt _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _). all: try (by gdisj).
  all: rewrite ?(tenv_dim dZAppZpBpp) ?(tenv_dim dZkBq) ?(tenv_dim dZkApp) ?(tenv_dim dZpBpp) ?eZk ?eBq ?eZp ?eApp ?eBpp ?eCiso ?eCpSrc ?eCppSrc ?eCpTgt ?eCppTgt. 1,2: exact: leqnn.
  - exact: (leq_mul HdnLe HdnLe).
  - exact: leqnn.
  - by [].
  - exact: leqnn.
  - apply: leq_pmull; exact: HD5.
  - by [].
  - exact: leqnn.
  - apply: leq_pmull; exact: HD5. Qed.
Definition gapt_dim_Zk : (2 ^ bb84_n P)%N = dim 'H[gapt_HL]_gZk.
Proof. by rewrite gapt_reg_dim. Defined.
Definition gapt_dim_Bq : (2 ^ bb84_n P)%N = dim 'H[gapt_HL]_gBq.
Proof. by rewrite gapt_reg_dim. Defined.
Definition gapt_dim_Zp : (2 ^ bb84_n P)%N = dim 'H[gapt_HL]_gZp.
Proof. by rewrite gapt_reg_dim. Defined.
Lemma gapt_disZBq : [disjoint gZk & gBq]. Proof. by gdisj. Qed.
Fact gapt_disZZp : [disjoint gZk & gZp]. Proof. by gdisj. Qed.
End BB84GapTWitness.
Section BB84ProgramHmaxWitness.
Variable (R : realType).
Fact bb84_program_hmax_bound_witness_mx (P : @bb84_protocol R) (G : @bb84_zsource R P) (eps : R) :
  (0 < bb84_n P)%N -> (0 < bb84_k P)%N -> 0 < eps -> 0 < bb84_p_pass_tot G ->
  eps / Num.sqrt (bb84_p_pass_tot G) < 1 -> smooth_hmax_mx (eps / Num.sqrt (bb84_p_pass_tot G)) (biprod_mx gapt_disZBq
       (prog_hmax_rhoZB gapt_disZBq G (@gapt_dim_Zk R P) (@gapt_dim_Bq R P))) <= (bb84_n P)%:R *
       bb84_h_trunc (bb84_Qtol P + bb84_mu (bb84_n P) (bb84_k P) eps).
Proof. exact: (@bb84_program_hmax_mx_from_zsource R 'I_10 (gapt_HL P) _ _ _ gapt_disZBq gapt_disZZp (@gapt_Aux R P) P G eps (@gapt_dim_Zk R
  P) (@gapt_dim_Bq R P) (@gapt_dim_Zp R P)). Qed.
End BB84ProgramHmaxWitness.
Section BB84ProgramHmaxBoundSigdet.
Variable R : realType.
Notation chsType := (@chsType R).
Notation C := (@hermitian.C R).
Variables (P : @bb84_protocol R) (q : R) (dev : bb84_certified_device P q) (LE : finType) (HE : LE -> chsType).
Notation M := (bb84_round_limit P).
Notation LB := bb84_register_index.
Notation HB := (@bb84_register_space R P q dev).
Notation L := (bb84_label M LE LB).
Notation HL := (@bb84_label_space R M LE LB HE HB).
Notation V := (bb84_val M (bb84_n P) (bb84_l P) (cd_ir_bits dev) (cd_vseed_count dev) (cd_tag_count dev) (cd_paseed_count dev)).
Notation Eve := (bb84_Eve P LE).
Notation Sreg := (bb84_S P LE).
Notation Ereg := (bb84_E P LE).
Notation Zreg := (bb84_Zkey P LE).
Notation Bqreg := (bb84_Bq P LE).
Notation nkey := (bb84_n P).
Variable rhofull : forall (EA : @adversary R L HL V Eve) (xi : @cq_state R L HL (bb84_cvar M) V),
    'M[C]_(bb84_full_string_count P * dim ('H[HL]_Ereg) * bb84_full_string_count P).
Hypothesis Hden1 : forall (EA : @adversary R L HL V Eve) (xi : @cq_state R L HL (bb84_cvar M) V), rhofull EA xi \is den1mx.
Definition sigdet_correspondence : Prop := forall (EA : @adversary R L HL V Eve) (pair : 'M[C]_(4 * 2))
         (xi : @cq_state R L HL (bb84_cvar M) V),
    cq_wf xi -> pair \is den1mx -> bb84_eb_pair_ptr_ok pair -> bb84_eb_pair_x_branch_ok dev pair ->
    castmx (esym (@bb84_dim_SEB R P q dev LE HE), esym (@bb84_dim_SEB R P q dev LE HE)) (h2mx (rhoSrc_SEB_sigdet_lf EA pair xi))
    = bb84_cond_rho_raw (@bb84_zsrc_prog R P q dev LE HE rhofull Hden1 EA xi).
Lemma bb84_program_hmax_bound_sigdet : sigdet_correspondence -> (0 < bb84_n P)%N -> (0 < bb84_k P)%N ->
  forall (EA : @adversary R L HL V Eve) (pair : 'M[C]_(4 * 2)) (xi : @cq_state R L HL (bb84_cvar M) V) (eps : R),
    cq_wf xi -> pair \is den1mx -> bb84_eb_pair_ptr_ok pair -> bb84_eb_pair_x_branch_ok dev pair ->
    0 < bb84_source_pass_prob EA xi -> 0 < eps -> eps < 1 ->
    0 <= eps / Num.sqrt (bb84_source_pass_prob EA xi) -> eps / Num.sqrt (bb84_source_pass_prob EA xi) <
      Num.sqrt (@complex.Re R (\tr (rhoSrc_SEB_sigdet EA pair xi))) -> smooth_hmax Bqreg (eps / Num.sqrt (bb84_source_pass_prob EA xi))
      (rhoZB_sigdet EA pair xi) <= (bb84_n P)%:R * bb84_h_trunc (bb84_Qtol P + bb84_mu (bb84_n P) (bb84_k P) eps).
Proof. move=> Hcorr Hn Hk EA pair xi eps Hwf Hpair Hptr Hbr Hpos Heps_pos Heps_lt1 Heps'_nn Heps'_lt.
  have Hxi_psd : forall s, xi s \is psdlf by case: Hwf. set G := @bb84_zsrc_prog R P q dev LE HE rhofull Hden1 EA xi.
  have Hpre := Hcorr EA pair xi Hwf Hpair Hptr Hbr. have Hbp : bb84_source_pass_prob EA xi = bb84_p_pass_tot G.
  { have Htr : @complex.Re R (\tr (castmx (esym (@bb84_dim_SEB R P q dev LE HE), esym (@bb84_dim_SEB R P q dev LE HE)) (h2mx (rhoSrc_SEB_sigdet_lf EA pair xi)))) = @complex.Re R (\tr (bb84_cond_rho_raw G)) by rewrite Hpre. move: Htr; rewrite mxtrace_castmx_sq -/(\Tr (rhoSrc_SEB_sigdet_lf EA pair xi)). rewrite (@rhoSrc_SEB_sigdet_lf_traceRe R P q dev LE HE EA pair xi Hptr Hbr) bb84_cond_rho_raw_trace1 re_realid. by []. } have Hbn : rhoSrc_SEB_sigdet EA pair xi = bb84_cond_rho G.
  { rewrite /rhoSrc_SEB_sigdet /bb84_cond_rho -Hbp. rewrite h2mxZ_lf [castmx _ (_ *: _)]linearZ; congr (_ *: _). exact: Hpre. }
have Hpsd_zb : rhoZB_sigdet EA pair xi \is psdlf by exact: (@rhoZB_sigdet_psd R P q dev LE HE EA pair xi Hpair Hptr Hbr Hpos Hxi_psd).
    have Htr1 : \tr (rhoSrc_SEB_sigdet EA pair xi) = 1.
  { have Hd := @rhoSrc_SEB_sigdet_den1mx R P q dev LE HE EA pair xi Hpair Hptr Hbr Hpos Hxi_psd. by move/den1mxP: Hd => [_ /eqP ->]. }
have HRe1 : @complex.Re R (\tr (rhoSrc_SEB_sigdet EA pair xi)) = 1 by rewrite Htr1 re_realid.
    have Hpass_pos_G : 0 < bb84_p_pass_tot G by rewrite -Hbp. have Heps'1 : eps / Num.sqrt (bb84_p_pass_tot G) < 1.
  { rewrite -Hbp. move: Heps'_lt. by rewrite HRe1 sqrtr1. } have Hwit := @bb84_program_hmax_bound_witness_mx R P G eps Hn Hk Heps_pos Hpass_pos_G Heps'1. move: Hwit; rewrite /prog_hmax_rhoZB. rewrite (eur_rho_ZC_biprod_mx gapt_disZBq (bb84_cond_rho G) (@std_projective_povm R (2 ^ bb84_n P)) _ (@gapt_dim_Zk R P) (@gapt_dim_Bq R P)). rewrite entropy.prop.smooth_hmax_mx_cast_bipartite.
    move=> Hwit; rewrite (entropy.prop.smooth_hmax_labelled_mx (bb84_disZBq P LE) _ Hpsd_zb) /rhoZB_sigdet.
    rewrite (eur_rho_ZC_biprod_mx (bb84_disZBq P LE) (rhoSrc_SEB_sigdet EA pair xi) (@std_projective_povm R (2 ^ nkey)) _ (@bb84_dim_Zkey R P q dev LE HE) (@bb84_dim_Bq R P q dev LE HE)). by rewrite entropy.prop.smooth_hmax_mx_cast_bipartite Hbn Hbp; exact: Hwit. Qed.
Definition delayed_measurement_hmin_sigdet : Prop := forall (EA : @adversary R L HL V Eve) (pair : 'M[C]_(4 * 2))
         (xi : @cq_state R L HL (bb84_cvar M) V) (eps : R),
    cq_wf xi -> pair \is den1mx -> bb84_eb_pair_ptr_ok pair -> bb84_eb_pair_x_branch_ok dev pair ->
    0 < bb84_source_pass_prob EA xi -> 0 < eps -> eps < 1 ->
    0 <= eps / Num.sqrt (bb84_source_pass_prob EA xi) -> eps / Num.sqrt (bb84_source_pass_prob EA xi) <
      Num.sqrt (@complex.Re R (\tr (rhoSrc_SEB_sigdet EA pair xi))) -> smooth_hmin Ereg (eps / Num.sqrt (bb84_source_pass_prob EA xi))
      (@rhoXE_sigdet R P q dev LE HE EA pair xi (2 ^ nkey) (@bb84_source_x_povm R P q (@cd_src R P q dev)
          (@cd_src_dim_A R P q dev) (@cd_src_dim_X R P q dev)) (@bb84_dim_S R P q dev LE HE)) <=
    smooth_hmin Ereg (eps / Num.sqrt (bb84_source_pass_prob EA xi)) (rhoXE_readout_pass_prog EA xi).
Fact bb84_pe_pass_hmin_sigdet : sigdet_correspondence -> delayed_measurement_hmin_sigdet ->
  (0 < bb84_n P)%N -> (0 < bb84_k P)%N -> forall (EA : @adversary R L HL V Eve) (pair : 'M[C]_(4 * 2))
         (xi : @cq_state R L HL (bb84_cvar M) V) (eps : R),
    cq_wf xi -> pair \is den1mx -> bb84_eb_pair_ptr_ok pair -> bb84_eb_pair_x_branch_ok dev pair ->
    0 < bb84_source_pass_prob EA xi -> 0 < eps -> eps < 1 ->
    0 <= eps / Num.sqrt (bb84_source_pass_prob EA xi) -> eps / Num.sqrt (bb84_source_pass_prob EA xi) <
      Num.sqrt (@complex.Re R (\tr (rhoSrc_SEB_sigdet EA pair xi))) -> (bb84_n P)%:R *
      (q - bb84_h_trunc (bb84_Qtol P + bb84_mu (bb84_n P) (bb84_k P) eps)) <=
    smooth_hmin Ereg (eps / Num.sqrt (bb84_source_pass_prob EA xi)) (rhoXE_readout_pass_prog EA xi).
Proof. move=> Hcorr Hdm Hn Hk EA pair xi eps Hwf Hpair Hptr Hbr Hpos Heps_pos Heps_lt1 Heps'_nn Heps'_lt.
  have Hxi_psd : forall s, xi s \is psdlf by case: Hwf. set eps' := eps / Num.sqrt (bb84_source_pass_prob EA xi).
  have Hsrc_den1 : rhoSrc_SEB_sigdet EA pair xi \is den1mx.
  { exact: (@rhoSrc_SEB_sigdet_den1mx R P q dev LE HE EA pair xi Hpair Hptr Hbr Hpos Hxi_psd). }
have Hsrc_den : rhoSrc_SEB_sigdet EA pair xi \is denmx := den1mx_den Hsrc_den1. have Hucr := @bb84_program_uncertainty_sigdet R P q dev LE HE EA pair xi eps' Hn Hsrc_den Heps'_nn Heps'_lt. set h_trunc := bb84_h_trunc (bb84_Qtol P + bb84_mu (bb84_n P) (bb84_k P) eps).
    have HstatB := @bb84_program_hmax_bound_sigdet Hcorr Hn Hk EA pair xi eps Hwf Hpair Hptr Hbr Hpos Heps_pos Heps_lt1 Heps'_nn Heps'_lt.
    have Hmin_sig : (bb84_n P)%:R * (q - h_trunc) <= smooth_hmin Ereg eps' (@rhoXE_sigdet R P q dev LE HE EA pair xi (2 ^ nkey) (@bb84_source_x_povm R P q (@cd_src R P q dev) (@cd_src_dim_A R P q dev) (@cd_src_dim_X R P q dev)) (@bb84_dim_S R P q dev LE HE)).
  { have Hcomb : (bb84_n P)%:R * q <= smooth_hmin Ereg eps' (@rhoXE_sigdet R P q dev LE HE EA pair xi (2 ^ nkey) (@bb84_source_x_povm R P q (@cd_src R P q dev) (@cd_src_dim_A R P q dev) (@cd_src_dim_X R P q dev)) (@bb84_dim_S R P q dev LE HE)) + (bb84_n P)%:R * h_trunc.
    { apply: le_trans Hucr _. by rewrite lerD2l; exact: HstatB. } rewrite mulrBr. by rewrite lerBlDr. } apply: le_trans Hmin_sig _.
      exact: (Hdm EA pair xi eps Hwf Hpair Hptr Hbr Hpos Heps_pos Heps_lt1 Heps'_nn Heps'_lt). Qed.
End BB84ProgramHmaxBoundSigdet.
Section BB84FlagBlock.
Variable (R : realType).
Notation C := (@hermitian.C R).
Notation chsType := (@chsType R).
Variable (L : finType) (HL : L -> chsType).
Variable (Fbit E : {set L}).
Hypothesis disFE : [disjoint Fbit & E].
Fact bb84_flag_cq_block_projector (x0 x : 'Idx[HL]_Fbit) (rho : 'F[HL]_E) : cq_block disFE x
    (([> deltav x0 ; deltav x0 <] \O rho) : 'F[HL]_(Fbit :|: E)) = if x == x0 then rho else 0.
Proof. rewrite /cq_block. set K := (([> deltav x ; deltav x <] \O (\1 : 'F[HL]_E)) : 'F[HL]_(Fbit :|: E)). set rho0 := (([> deltav x0 ;
  deltav x0 <] \O rho) : 'F[HL]_(Fbit :|: E)). case Hx: (x == x0).
  - move/eqP: Hx => Hx. have Hproj : K \o rho0 \o K = rho0.
    { have HK : K = [> deltav x0 ; deltav x0 <] \⊗ (\1 : 'F[HL]_E). by apply: to_Fnd_inj; rewrite /K Hx (sdotFT _ _ disFE) to_Fnd_tenE.
      have Hrho0 : rho0 = [> deltav x0 ; deltav x0 <] \⊗ rho. by apply: to_Fnd_inj; rewrite (sdotFT _ _ disFE) to_Fnd_tenE.
      rewrite HK Hrho0; rewrite -tenf_comp; last exact: disFE. rewrite comp_lfun1l outp_comp dv_dot eqxx scale1r; rewrite -tenf_comp; last exact: disFE. by rewrite comp_lfun1r outp_comp dv_dot eqxx scale1r. } by rewrite Hproj ptrace_castl_sdot_trace_l outp_trlf dv_dot eqxx scale1r.
  - have Hproj : K \o rho0 \o K = 0.
    { have HK : K = [> deltav x ; deltav x <] \⊗ (\1 : 'F[HL]_E). by apply: to_Fnd_inj; rewrite (sdotFT _ _ disFE) to_Fnd_tenE.
      have Hrho0 : rho0 = [> deltav x0 ; deltav x0 <] \⊗ rho. by apply: to_Fnd_inj; rewrite (sdotFT _ _ disFE) to_Fnd_tenE.
      rewrite HK Hrho0; rewrite -tenf_comp; last exact: disFE. rewrite comp_lfun1l outp_comp dv_dot.
      by rewrite Hx /= scale0r ten0f comp_lfun0l. } by rewrite Hproj /ptrace_castl /ptrace_cast_gen linear0 linear0. Qed.
Fact bb84_flag_cq_blockD (x : 'Idx[HL]_Fbit) (X Y : 'F[HL]_(Fbit :|: E)) :
  cq_block disFE x (X + Y) = cq_block disFE x X + cq_block disFE x Y.
Proof. have Hlin : forall (X' Y' : 'F[HL]_(Fbit :|: E)), cq_block disFE x (1 *: X' + Y') = 1 *: cq_block disFE x X' + cq_block disFE x Y'.
  { move=> X' Y'; rewrite /cq_block. rewrite linearPr /= linearPl /= /ptrace_castl /ptrace_cast_gen. rewrite linearP /=.
    by rewrite linearP /=. } by move: (Hlin X Y); rewrite !scale1r. Qed.
Variable (acc rej : 'Idx[HL]_Fbit).
Hypothesis Hnr : acc != rej.
Definition bb84_flag_pair (A B : 'F[HL]_E) : 'F[HL]_(Fbit :|: E) :=
  ([> deltav acc ; deltav acc <] \O A) + ([> deltav rej ; deltav rej <] \O B).
Lemma bb84_flag_pair_psd (A B : 'F[HL]_E) : A \is psdlf -> B \is psdlf -> bb84_flag_pair A B \is psdlf.
Proof. move=> HA HB. have Hsummand : forall (i : 'Idx[HL]_Fbit) (X : 'F[HL]_E), X \is psdlf -> (([> deltav i ;
  deltav i <] \O X) : 'F[HL]_(Fbit :|: E)) \is psdlf.
  { move=> i X HX. have -> : (([> deltav i ; deltav i <] \O X) : 'F[HL]_(Fbit :|: E)) = [> deltav i ; deltav i <] \⊗ X.
    by apply: to_Fnd_inj; rewrite (sdotFT _ _ disFE) to_Fnd_tenE. rewrite psdlfE. apply: tenf_ge0.
    - exact: disFE.
    - exact: outp_ge0.
    - by rewrite -psdlfE. } rewrite /bb84_flag_pair. by apply: psdlfD; apply: Hsummand. Qed.
Lemma bb84_flag_pair_trace (A B : 'F[HL]_E) : \Tr (bb84_flag_pair A B) = \Tr A + \Tr B.
Proof. by rewrite /bb84_flag_pair linearD /= !(lftrace_sdot_disj _ _ disFE); rewrite !outp_trlf !dv_dot !eqxx !mul1r. Qed.
Fact bb84_flag_pair_cq_acc (A B : 'F[HL]_E) : cq_block disFE acc (bb84_flag_pair A B) = A.
Proof. by rewrite /bb84_flag_pair bb84_flag_cq_blockD bb84_flag_cq_block_projector eqxx bb84_flag_cq_block_projector;
  rewrite (negbTE Hnr) addr0. Qed.
Fact bb84_flag_pair_ptrace (A B : 'F[HL]_E) : ptrace_castl disFE (bb84_flag_pair A B) = A + B.
Proof. have bb84_flag_ptrace_castlD : forall (X Y : 'F[HL]_(Fbit :|: E)), ptrace_castl disFE (X + Y) = ptrace_castl disFE X + ptrace_castl
  disFE Y.
{ clear B A; move=> X Y. rewrite /ptrace_castl /ptrace_cast_gen. by rewrite linearD /= linearD /=. }
by rewrite /bb84_flag_pair bb84_flag_ptrace_castlD !ptrace_castl_sdot_trace_l; rewrite !outp_trlf !dv_dot !eqxx !scale1r. Qed.
End BB84FlagBlock.
Section BB84DistGenWitness.
Variable (R : realType).
Notation C := (@hermitian.C R).
Notation chsType := (@chsType R).
Variable (L : finType) (H : L -> chsType) (A B : {set L}).
Hypothesis disAB : [disjoint A & B].
Fact dist_uniform_gen_witness (rhoAB : 'F[H]_(A :|: B)) (sigmaB : 'F[H]_B) :
  rhoAB \is psdlf -> sigmaB \is psdlf -> 2%:R * dist_from_uniform rhoAB <= trnormH (rhoAB - (dim 'H[H]_A)%:R^-1 *: ((\1 : 'F_A) \O sigmaB))
    + `| @complex.Re R (\Tr sigmaB) - @complex.Re R (\Tr rhoAB) |.
Proof. move=> Hrho Hsig; set m := @complex.Re R (\Tr rhoAB). set s := @complex.Re R (\Tr sigmaB);
  set N := trnormH (rhoAB - (dim 'H[H]_A)%:R^-1 *: ((\1 : 'F_A) \O sigmaB)). have Hm_ge0 : 0 <= m by move: (psdlf_trlf Hrho); rewrite lecE/= => /andP[_]. have Hs_ge0 : 0 <= s by move: (psdlf_trlf Hsig); rewrite lecE/= => /andP[_].
  have Hrho_Tr_real : \Tr rhoAB \is Num.real := ger0_real (psdlf_trlf Hrho). have Hsig_Tr_real : \Tr sigmaB \is Num.real := ger0_real (psdlf_trlf Hsig). have Htr_ptrace_rho : \Tr (\Tr_(A) rhoAB) = \Tr rhoAB by case/cptpP: (@ptraceso_qc R L H A (A :|: B)) => _ /tpmapP ->.
  have Hdim_A_ne0_R : ((dim 'H[H]_A)%:R : R) != 0 by rewrite pnatr_eq0 -lt0n dim_proper. pose invd : R := @GRing.inv R ((dim 'H[H]_A)%:R).
  have Hinv_eq : @GRing.inv C ((dim 'H[H]_A)%:R) = invd%:C by rewrite /invd -natrC -fmorphV.
  have Hinv_ge0 : 0 <= invd by rewrite /invd invr_ge0 ler0n. have Hinvd_dim : invd * ((dim 'H[H]_A)%:R) = 1 by rewrite /invd mulVf.
  case: (ltrP 0 s) => Hs_case; last first.
  - have Hs0 : s = 0 by apply/le_anti; rewrite Hs_case Hs_ge0. have Hsig0 : sigmaB = 0. apply/eqP/trlf0_eq0; split; first by move: Hsig; rewrite psdlfE. by rewrite -(RRe_real Hsig_Tr_real) -/s Hs0. have HN : N = m by rewrite /N Hsig0 sdotf0 scaler0 subr0; rewrite /m (trnormH_psd Hrho). rewrite HN Hs0 sub0r normrN (ger0_norm Hm_ge0). have Hdist := dist_uniform_le_trace disAB Hrho.
    rewrite -/m in Hdist. have H2 : 2%:R * dist_from_uniform rhoAB <= 2%:R * m by rewrite ler_pM2l ?ltr0n. apply: le_trans H2 _.
    by rewrite mulr2n mulrDl mul1r lexx.
  - set c : R := m / s. have Hc_ge0 : 0 <= c by rewrite /c divr_ge0. pose tau : 'F[H]_B := c%:C *: sigmaB.
    have Htau_psd : tau \is psdlf by rewrite /tau; apply: psdlfZ; [rewrite lecR | ]. have Htau_Tr : \Tr tau = \Tr (\Tr_(A) rhoAB).
    rewrite Htr_ptrace_rho /tau linearZ /= -(RRe_real Hsig_Tr_real) -(RRe_real Hrho_Tr_real) -/s -/m -realcM /c -mulrA mulVf ?mulr1 //.
    by rewrite gt_eqF. have Hwb : 2%:R * dist_from_uniform rhoAB <= trnormH (rhoAB - (dim 'H[H]_A)%:R^-1 *: ((\1 : 'F_A) \O tau)).
    exact: dist_uniform_witness_bound Htau_psd Htau_Tr. apply: le_trans Hwb _. have Hsplit : rhoAB - (dim 'H[H]_A)%:R^-1 *: ((\1 : 'F_A) \O tau) = (rhoAB - (dim 'H[H]_A)%:R^-1 *: ((\1 : 'F_A) \O sigmaB)) - ((dim 'H[H]_A)%:R^-1 *: ((\1 : 'F_A) \O tau) - (dim 'H[H]_A)%:R^-1 *: ((\1 : 'F_A) \O sigmaB)). by rewrite opprB addrA addrNK. rewrite Hsplit; apply: le_trans (trnormH_triangleB _ _) _. rewrite -/N lerD2l.
    have Hdiff : (dim 'H[H]_A)%:R^-1 *: ((\1 : 'F_A) \O tau) - (dim 'H[H]_A)%:R^-1 *: ((\1 : 'F_A) \O sigmaB) = (c - 1)%:C *: ((dim 'H[H]_A)%:R^-1 *: ((\1 : 'F_A) \O sigmaB)). rewrite -scalerBr -sdotfBr. have Htau_sig : tau - sigmaB = (c - 1)%:C *: sigmaB by rewrite /tau -{2}(scale1r sigmaB) -scalerBl; rewrite raddfB /= rmorph1. by rewrite Htau_sig sdotfZr scalerA mulrC -scalerA; [].
    rewrite Hdiff trnormH_scaleZ Hinv_eq trnormH_scaleZ (trnormH_lift_I_psd disAB Hsig) (trnormH_psd Hsig).
    rewrite -/s (ger0_norm Hinv_ge0) [invd * (_ * _)]mulrA Hinvd_dim mul1r. have Halg : (c - 1) * s = m - s by rewrite mulrBl mul1r /c divfK ?gt_eqF. by rewrite -{1}(ger0_norm (ltW Hs_case)) -normrM Halg distrC; exact: lexx. Qed.
End BB84DistGenWitness.
Section BB84FlagContract.
Variable (R : realType).
Notation C := (@hermitian.C R).
Notation chsType := (@chsType R).
Variable (L : finType) (HL : L -> chsType) (Fbit E : {set L}).
Hypothesis disFE : [disjoint Fbit & E].
Fact trnormH_dephase_le (Y : 'F[HL]_(Fbit :|: E)) : trnormH ((@dephase_X_so R L HL Fbit E) Y) <= trnormH Y.
Proof. have Hit := itnormP (@dephase_X_so R L HL Fbit E) Y. have Hqc : `|(@dephase_X_so R L HL Fbit E) : 'SO| = 1.
  { apply: itnorm_qcP; exact: (@dephase_X_cptp R L HL Fbit E disFE). } rewrite Hqc mul1r in Hit. rewrite /trnormH.
    have Hre1 : trnorm (h2mx ((@dephase_X_so R L HL Fbit E) Y)) \is Num.real by exact: ger0_real (trnorm_ge0 _).
    have Hre2 : trnorm (h2mx Y) \is Num.real by exact: ger0_real (trnorm_ge0 _). move: Hit; rewrite /Num.norm /= /trfnorm /=.
    by rewrite -(RRe_real Hre1) -(RRe_real Hre2) lecR. Qed.
End BB84FlagContract.
Section LfunTrNormDual.
Variable (R : realType).
Notation C := (@hermitian.C R).
Notation chsType := (@chsType R).
Lemma trfnorm_aligned_witness (U : chsType) (f : 'End(U)) : exists2 g : 'End(U), (i2fnorm g <= 1) & (\Tr (f \o g) = `|f|).
Proof. have [B PB1 PB2] := trfnorm_existsr f; set a := \Tr (f \o B). have Ha : `|a| = `|f| by rewrite /a -PB2.
  case: (eqVneq a 0) => [Ha0 | Han0].
  - exists B; first by rewrite PB1. by rewrite -/a Ha0 -Ha Ha0 normr0.
  - pose u : C := `|a| / a. have Hune0 : `|a| != 0 by rewrite normr_eq0. exists (u *: B).
    + by rewrite i2fnormZ PB1 mulr1 /u normrM normrV ?unitfE// normr_id divff.
    + by rewrite -comp_lfunZr linearZ /= -/a /u; rewrite (divfK Han0) Ha. Qed.
End LfunTrNormDual.
Section BB84FlagAdditivity.
Variable (R : realType).
Notation C := (@hermitian.C R).
Notation chsType := (@chsType R).
Variable (L : finType) (HL : L -> chsType) (Fbit E : {set L}).
Hypothesis disFE : [disjoint Fbit & E].
Variable (acc rej : 'Idx[HL]_Fbit).
Hypothesis Hnr : acc != rej.
Local Notation Pacc := ([> deltav acc ; deltav acc <] : 'F[HL]_Fbit).
Local Notation Prej := ([> deltav rej ; deltav rej <] : 'F[HL]_Fbit).
Lemma sdot_compFE (a c : 'F[HL]_Fbit) (b d : 'F[HL]_E) : ((a \O b : 'F[HL]_(Fbit :|: E)) \o (c \O d)) = (a \o c) \O (b \o d).
Proof. rewrite (sdotF_to_tenF disFE a b) (sdotF_to_tenF disFE c d). by rewrite -tenf_comp; last exact: disFE;
  rewrite -(sdotF_to_tenF disFE (a \o c) (b \o d)). Qed.
Lemma sdot_adjFE (a : 'F[HL]_Fbit) (b : 'F[HL]_E) : ((a \O b : 'F[HL]_(Fbit :|: E))^A) = a^A \O b^A.
Proof. rewrite (sdotF_to_tenF disFE a b) tenf_adj. by rewrite -(sdotF_to_tenF disFE a^A b^A). Qed.
Fact trnormH_flag_add (X Y : 'F[HL]_E) : trnormH ((Pacc \O X + Prej \O Y) : 'F[HL]_(Fbit :|: E)) = trnormH X + trnormH Y.
Proof. have trnormH_flag_factor : forall (v : 'Idx[HL]_Fbit) (f : 'F[HL]_E), trnormH (([> deltav v ;
  deltav v <] \O f) : 'F[HL]_(Fbit :|: E)) = trnormH f.
{ clear Y X; move=> v f. have Hten : (([> deltav v ; deltav v <] \O f) : 'F[HL]_(Fbit :|: E)) = [> deltav v ; deltav v <] \⊗ f.
  by apply: to_Fnd_inj; rewrite (sdotFT _ _ disFE) to_Fnd_tenE. rewrite Hten /trnormH h2mx_tenf. rewrite trnormUr; first last.
  { by apply: tenv_mxU_adj_unitarymx; exact: disFE. } rewrite trnormUl_cond; first last.
  { by apply: tenv_mxU_adj_unitarymx; exact: disFE. } rewrite trnorm_tens. have HP : trnorm (h2mx ([> deltav v ; deltav v <] : 'F[HL]_Fbit)) = 1.
  { have Hpsd : ([> deltav v ; deltav v <] : 'F[HL]_Fbit) \is psdlf by rewrite psdlfE; exact: outp_ge0. rewrite psdmx_trnorm; last by move: Hpsd; rewrite qualifE. have -> : \tr (h2mx ([> deltav v ; deltav v <] : 'F[HL]_Fbit)) = \Tr ([> deltav v ; deltav v <] : 'F[HL]_Fbit) by []. by rewrite outp_trlf dv_dot eqxx. } by rewrite HP mul1r. }
have flag_proj_le1 : (Pacc + Prej : 'F[HL]_Fbit) ⊑ \1.
{ clear Y X; have H1 : (\1 : 'F[HL]_Fbit) = \sum_(i : 'Idx[HL]_Fbit) [> deltav i ; deltav i <]. by rewrite sumonb_out. rewrite -subv_ge0.
  have -> : (\1 : 'F[HL]_Fbit) - (Pacc + Prej) = \sum_(i : 'Idx[HL]_Fbit | (i != acc) && (i != rej)) [> deltav i ; deltav i <].
  { rewrite {1}H1 (bigD1 acc) //=. rewrite (bigD1 rej) //=; last by rewrite eq_sym. by rewrite addrA [X in X - _]addrC addrK. }
by apply: sumv_ge0 => i _; exact: outp_ge0. } set Z := (Pacc \O X + Prej \O Y : 'F[HL]_(Fbit :|: E)).
    have HtrE : forall (S : {set L}) (f : 'F[HL]_S), trnormH f = @complex.Re R `|f| by move=> S f; rewrite /trnormH /Num.norm /= /trfnorm.
    apply/le_anti/andP; split.
  - rewrite /Z. apply: le_trans (trnormH_triangle _ _) _. by rewrite !trnormH_flag_factor.
  - have [gX HgX1 HgX2] := trfnorm_aligned_witness X. have [gY HgY1 HgY2] := trfnorm_aligned_witness Y.
    set W := (Pacc \O gX + Prej \O gY : 'F[HL]_(Fbit :|: E)). have HPP : Pacc \o Pacc = Pacc by rewrite outp_comp dv_dot eqxx scale1r.
    have HQQ : Prej \o Prej = Prej by rewrite outp_comp dv_dot eqxx scale1r. have HPQ : Pacc \o Prej = 0 by rewrite outp_comp dv_dot (negbTE Hnr) scale0r. have HQP : Prej \o Pacc = 0 by rewrite outp_comp dv_dot eq_sym (negbTE Hnr) scale0r.
    have HgXform : gX^A \o gX ⊑ \1 by rewrite -bound1lf_form_le1 bound1lf_i2fnormE.
    have HgYform : gY^A \o gY ⊑ \1 by rewrite -bound1lf_form_le1 bound1lf_i2fnormE. have HWAW : W^A \o W = Pacc \O (gX^A \o gX) + Prej \O (gY^A \o gY).
    { rewrite /W raddfD /= !sdot_adjFE !adj_outp. rewrite comp_lfunDl !comp_lfunDr !sdot_compFE HPP HPQ HQP HQQ.
      by rewrite !sdot0f addr0 add0r. } have Hobs : (W^A \o W) \is obslf.
    { rewrite HWAW obslfE; apply/andP; split.
      - apply: addv_ge0.
        + rewrite (sdotF_to_tenF disFE Pacc); apply: tenf_ge0; [exact: disFE | exact: outp_ge0 | exact: form_gef0].
        + rewrite (sdotF_to_tenF disFE Prej); apply: tenf_ge0; [exact: disFE | exact: outp_ge0 | exact: form_gef0].
      - have Hstep1 : Pacc \O (gX^A \o gX) + Prej \O (gY^A \o gY) ⊑ Pacc \O (\1 : 'F[HL]_E) + Prej \O \1. apply: levD.
          + apply: (lef_sdotfr disFE); [exact: outp_ge0 | exact: HgXform].
          + apply: (lef_sdotfr disFE); [exact: outp_ge0 | exact: HgYform]. apply: le_trans Hstep1 _. rewrite -sdotfDl.
            have Hone : (\1 : 'F[HL]_(Fbit :|: E)) = (\1 : 'F[HL]_Fbit) \O \1. by apply: to_Fnd_inj; rewrite (sdotFT _ _ disFE) -!to_FndEV tenf11. rewrite Hone (sdotF_to_tenF disFE (Pacc + Prej)) (sdotF_to_tenF disFE (\1 : 'F[HL]_Fbit)). apply: (lef_tenfl disFE); [exact: lef01 | exact: flag_proj_le1]. } have HW1 : i2fnorm W <= 1.
    { rewrite -bound1lf_i2fnormE qualifE. have <- : h2mx (W^A \o W) = (h2mx W)^*t *m h2mx W by rewrite h2mx_comp h2mx_adj. by move: Hobs; rewrite qualifE. } have HZW : \Tr (Z \o W) = `|X| + `|Y|.
    { rewrite /Z /W comp_lfunDl !comp_lfunDr !sdot_compFE. rewrite HPP HPQ HQP HQQ !sdot0f !addr0 add0r linearD /= !(lftrace_sdot_disj _ _ disFE). rewrite !outp_trlf !dv_dot !eqxx !mul1r. by rewrite HgX2 HgY2. } have Hkey : (`|X| + `|Y| : C) <= `|Z|.
    { rewrite -[`|X| + `|Y|]ger0_norm; last by apply: addr_ge0; apply: normr_ge0. rewrite -HZW; apply: le_trans (trlf_trfnorm _) _.
      apply: le_trans (trfnormMl Z W) _. rewrite -{2}(mulr1 (`|Z|)). apply: ler_wpM2l; [exact: normr_ge0 | exact: HW1]. }
by rewrite !HtrE -raddfD /=; move: Hkey; rewrite lecE => /andP[_ H]; exact: H. Qed.
End BB84FlagAdditivity.
Section BB84FlagPinch.
Variable (R : realType).
Notation C := (@hermitian.C R).
Notation chsType := (@chsType R).
Variable (L : finType) (HL : L -> chsType) (Fbit E : {set L}).
Hypothesis disFE : [disjoint Fbit & E].
Variable (acc rej : 'Idx[HL]_Fbit).
Hypotheses (Hnr : acc != rej) (Hcard2 : #|'Idx[HL]_Fbit| = 2).
Local Notation Pacc := ([> deltav acc ; deltav acc <] : 'F[HL]_Fbit).
Local Notation Prej := ([> deltav rej ; deltav rej <] : 'F[HL]_Fbit).
Fact flag_two_valued (x : 'Idx[HL]_Fbit) : (x == acc) || (x == rej).
Proof. have HeqT : [set acc; rej] == [set: 'Idx[HL]_Fbit]. by rewrite eqEcard subsetT /= cardsT Hcard2 cards2 Hnr. have Hx : x \in [set acc;
  rej] by rewrite (eqP HeqT) in_setT. by move: Hx; rewrite !inE. Qed.
Lemma dephase_two_block (D : 'F[HL]_(Fbit :|: E)) : (@dephase_X_so R L HL Fbit E) D =
  Pacc \O cq_block disFE acc D + Prej \O cq_block disFE rej D.
Proof. rewrite /dephase_X_so kraussoE. transitivity (\sum_(x : 'Idx[HL]_Fbit) ([> deltav x ;
  deltav x <] \O cq_block disFE x D : 'F[HL]_(Fbit :|: E))).
  { apply: eq_bigr => x _. have HKadj : (([> deltav x ; deltav x <] \O (\1 : 'F[HL]_E) : 'F[HL]_(Fbit :|: E)))^A = [> deltav x ; deltav x <] \O (\1 : 'F[HL]_E). by rewrite (sdot_adjFE disFE) adj_outp adjf1. rewrite HKadj. exact: (Kbox_cq_decomp disFE). }
rewrite (bigD1 acc) //= (bigD1 rej) //=; last by rewrite eq_sym. rewrite big1.
  - by rewrite !addr0.
  - by move=> x /andP[Hxa Hxr]; move: (flag_two_valued x); rewrite (negbTE Hxa) (negbTE Hxr). Qed.
Fact trnormH_flag_pinch (D : 'F[HL]_(Fbit :|: E)) : trnormH (cq_block disFE acc D) + trnormH (cq_block disFE rej D) <= trnormH D.
Proof. rewrite -(trnormH_flag_add disFE Hnr (cq_block disFE acc D) (cq_block disFE rej D)). by rewrite -dephase_two_block;
  exact: (trnormH_dephase_le disFE). Qed.
End BB84FlagPinch.
Section BB84OmegaCommute.
Variable (R : realType).
Notation chsType := (@chsType R).
Variable (L : finType) (HL : L -> chsType).
Variable (Fbit Akey Brest : {set L}).
Hypotheses (disFA : [disjoint Fbit & Akey]) (disFB : [disjoint Fbit & Brest]) (disAB : [disjoint Akey & Brest]).
Local Notation E := (Akey :|: Brest).
Let disFE : [disjoint Fbit & E].
Proof. by rewrite disjointXU disFA disFB. Defined.
Let disAFB : [disjoint Akey & (Fbit :|: Brest)].
Proof. by rewrite disjointXU disjoint_sym disFA disAB. Defined.
Let Hre : Akey :|: (Fbit :|: Brest) = Fbit :|: (Akey :|: Brest) := setUCA Akey Fbit Brest.
Lemma sdot_comp_gen (X Y : {set L}) (dXY : [disjoint X & Y]) (a c : 'F[HL]_X) (b d : 'F[HL]_Y) :
  ((a \O b : 'F[HL]_(X :|: Y)) \o (c \O d)) = (a \o c) \O (b \o d).
Proof. rewrite (sdotF_to_tenF dXY a b) (sdotF_to_tenF dXY c d). by rewrite -tenf_comp; last exact: dXY;
  rewrite -(sdotF_to_tenF dXY (a \o c) (b \o d)). Qed.
Lemma sdot_reassoc_FAB (a : 'F[HL]_Fbit) (x : 'F[HL]_Akey) (b : 'F[HL]_Brest) :
  castlf (Hre, Hre) ((x \O (a \O b)) : 'F[HL]_(Akey :|: (Fbit :|: Brest))) = ((a \O (x \O b)) : 'F[HL]_(Fbit :|: (Akey :|: Brest))).
Proof. apply: to_Fnd_inj. rewrite Fnd_cast (sdotFT _ _ disAFB) (sdotFT _ _ disFB) (sdotFT _ _ disFE) (sdotFT _ _ disAB).
  by rewrite tenFA (tenFC (to_Fnd x) (to_Fnd a)) -tenFA. Qed.
Lemma cq_block_omega_commute (v : 'Idx[HL]_Fbit) (om : 'F[HL]_Akey) (sig : 'F[HL]_(Fbit :|: Brest)) :
  cq_block disFE v (castlf (Hre, Hre) ((om \O sig) : 'F[HL]_(Akey :|: (Fbit :|: Brest)))) = om \O cq_block disFB v sig.
Proof. have castlf_Hre_mult : forall (f g : 'F[HL]_(Akey :|: (Fbit :|: Brest))), (castlf (Hre, Hre) f \o castlf (Hre, Hre) g) = castlf (Hre,
  Hre) (f \o g).
{ clear sig om v; move=> f g. by rewrite (castlf_complf Hre Hre Hre). } have one_E_split : (\1 : 'F[HL]_E) = ((\1 : 'F[HL]_Akey) \O (\1 : 'F[HL]_Brest) : 'F[HL]_E).
{ clear sig om v; by apply: to_Fnd_inj; rewrite (sdotFT _ _ disAB) tenF11. } set Pv := ([> deltav v ; deltav v <] : 'F[HL]_Fbit).
  set sB := cq_block disFB v sig; set P' := (Pv \O (\1 : 'F[HL]_Brest) : 'F[HL]_(Fbit :|: Brest)).
  set Kv := (Pv \O (\1 : 'F[HL]_E) : 'F[HL]_(Fbit :|: E)); set Kv' := ((\1 : 'F[HL]_Akey) \O P' : 'F[HL]_(Akey :|: (Fbit :|: Brest))).
  have HKv : Kv = castlf (Hre, Hre) Kv'.
  { rewrite /Kv /Kv' /P'. rewrite (sdot_reassoc_FAB Pv (\1 : 'F[HL]_Akey) (\1 : 'F[HL]_Brest)). by rewrite one_E_split. }
rewrite /cq_block -/Pv -/Kv HKv !castlf_Hre_mult. have Hsand : Kv' \o ((om \O sig) : 'F[HL]_(Akey :|: (Fbit :|: Brest))) \o Kv' = (om \O (P' \o sig \o P')).
  { rewrite /Kv'. rewrite (sdot_comp_gen disAFB (\1 : 'F[HL]_Akey) om P' sig) (sdot_comp_gen disAFB (\1 \o om) (\1 : 'F[HL]_Akey) (P' \o sig) P'). by rewrite comp_lfun1l comp_lfun1r. } rewrite Hsand. have HP'sig : P' \o sig \o P' = Pv \O sB by rewrite /P' /sB (Kbox_cq_decomp disFB). by rewrite HP'sig (sdot_reassoc_FAB Pv om sB); rewrite ptrace_castl_sdot_trace_l outp_trlf dv_dot eqxx scale1r. Qed.
End BB84OmegaCommute.
Section BB84DaggerHelpers.
Variable (R : realType).
Notation C := (@hermitian.C R).
Notation chsType := (@chsType R).
Variable (L : finType) (HL : L -> chsType).
Fact Re_lftrace_le_trnormH (S : {set L}) (X : 'F[HL]_S) : `| @complex.Re R (\Tr X) | <= trnormH X.
Proof. rewrite -lecR /trnormH. have Hreal : trnorm (h2mx X) \is Num.real := ger0_real (trnorm_ge0 _). by rewrite (RRe_real Hreal);
  apply: le_trans (normc_ge_Re (\Tr X)) _; rewrite /lftrace; exact: trnorm_ge_tr _. Qed.
Lemma trlf_scale_id_sdot (S T : {set L}) (dST : [disjoint S & T]) (g : 'F[HL]_T) :
  \Tr ((dim 'H[HL]_S)%:R^-1 *: ((\1 : 'F[HL]_S) \O g) : 'F[HL]_(S :|: T)) = \Tr g.
Proof. have trlf_id : forall (Sr : {set L}), \Tr (\1 : 'F[HL]_Sr) = (dim 'H[HL]_Sr)%:R.
  { move=> Sr. rewrite lftrace_baseE. under eq_bigr do rewrite lfunE/= ns_dot. by rewrite sumr_const card_ord. }
by rewrite linearZ /= (lftrace_sdot_disj _ _ dST) trlf_id mulrA mulVf ?mul1r //; rewrite pnatr_eq0 -lt0n dim_proper. Qed.
End BB84DaggerHelpers.
Section BB84CqBlockLin.
Variable (R : realType).
Notation C := (@hermitian.C R).
Notation chsType := (@chsType R).
Variable (L : finType) (HL : L -> chsType) (Fbit E : {set L}).
Hypothesis disFE : [disjoint Fbit & E].
Lemma cq_block_psd (v : 'Idx[HL]_Fbit) (X : 'F[HL]_(Fbit :|: E)) : X \is psdlf -> cq_block disFE v X \is psdlf.
Proof. move=> HX; rewrite /cq_block; apply: ptrace_castl_psdlf; rewrite psdlfE. have HP_eq : (([> deltav v;
  deltav v <] \O (\1 : 'F[HL]_E)) : 'F[HL]_(Fbit :|: E)) = [> deltav v; deltav v <] \⊗ (\1 : 'F[HL]_E). by apply: to_Fnd_inj; rewrite (sdotFT _ _ disFE) to_Fnd_tenE. have Hadj : (([> deltav v; deltav v <] \O (\1 : 'F[HL]_E)) : 'F[HL]_(Fbit :|: E))^A = [> deltav v; deltav v <] \O (\1 : 'F[HL]_E). by rewrite HP_eq tenf_adj adj_outp adjf1 -HP_eq. rewrite -{2}Hadj; apply: gef0_formfV; by rewrite -psdlfE. Qed.
End BB84CqBlockLin.
Section BB84DaggerAssembly.
Variable (R : realType).
Notation C := (@hermitian.C R).
Notation chsType := (@chsType R).
Variable (L : finType) (HL : L -> chsType).
Variable (Fbit Akey Brest : {set L}).
Hypotheses (disFA : [disjoint Fbit & Akey]) (disFB : [disjoint Fbit & Brest]) (disAB : [disjoint Akey & Brest]).
Variable (acc rej : 'Idx[HL]_Fbit).
Hypotheses (Hnr : acc != rej) (Hcard2 : #|'Idx[HL]_Fbit| = 2).
Local Notation E := (Akey :|: Brest).
Let disFE : [disjoint Fbit & E].
Proof. by rewrite disjointXU disFA disFB. Defined.
Let disAFB : [disjoint Akey & (Fbit :|: Brest)].
Proof. by rewrite disjointXU disjoint_sym disFA disAB. Defined.
Let Hre : Akey :|: (Fbit :|: Brest) = Fbit :|: (Akey :|: Brest) := setUCA Akey Fbit Brest.
Fact bb84_dagger_dist_le (Omega : 'F[HL]_(Fbit :|: E)) : Omega \is psdlf -> dist_from_uniform (cq_block disFE acc Omega)
    <= dist_from_uniform (castlf (esym Hre, esym Hre) Omega).
Proof. have cq_block_subD : forall (v : 'Idx[HL]_Fbit) (X Y : 'F[HL]_(Fbit :|: E)), cq_block disFE v (X - Y) = cq_block disFE v X - cq_block
  disFE v Y.
  { move=> v X Y. have H := bb84_flag_cq_blockD disFE v (X - Y) Y. rewrite subrK in H. by rewrite H addrK. }
have cq_block_scale : forall (v : 'Idx[HL]_Fbit) (c : C) (X : 'F[HL]_(Fbit :|: E)), cq_block disFE v (c *: X) = c *: cq_block disFE v X.
  { move=> v c X. rewrite /cq_block -comp_lfunZr -comp_lfunZl. by rewrite ptrace_castl_linearZ. } move=> HOmega; set W := castlf (esym Hre, esym Hre) Omega. have HW_psd : W \is psdlf by rewrite /W castlf_psdlfE.
    have Hcast_trn : forall (SA SB : {set L}) (eq : SA = SB) (g : 'F[HL]_SA), trnormH (castlf (eq, eq) g) = trnormH g.
  { move=> SA SB eq g. by case: SB / eq; rewrite castlf_id. } apply: (dist_uniform_glb disAFB HW_psd).
    move=> v [sigma [Hsig_psd [Hsig_tr Hv]]]; set sigma_a := cq_block disFB acc sigma. set Wsig := ((dim 'H[HL]_Akey)%:R^-1 *: ((\1 : 'F[HL]_Akey) \O sigma) : 'F[HL]_(Akey :|: (Fbit :|: Brest))). set D := castlf (Hre, Hre) (W - Wsig).
    have HD : D = Omega - (dim 'H[HL]_Akey)%:R^-1 *: castlf (Hre, Hre) ((\1 : 'F[HL]_Akey) \O sigma).
  { rewrite /D /Wsig. Timeout 15 (rewrite [castlf _ (_ - _)]linearB /=). congr (_ - _).
    - by rewrite /W castlfKV.
    - by rewrite linearZ /=. } have HcqaccD : cq_block disFE acc D = cq_block disFE acc Omega - (dim 'H[HL]_Akey)%:R^-1 *: ((\1 : 'F[HL]_Akey) \O sigma_a).
  { rewrite HD cq_block_subD; congr (_ - _). rewrite cq_block_scale; congr (_ *: _). by rewrite (cq_block_omega_commute disFA disFB disAB acc (\1 : 'F[HL]_Akey) sigma). } have Htrconserv : \Tr (cq_block disFE acc D) + \Tr (cq_block disFE rej D) = \Tr D.
  { have Hsum : \Tr ((@dephase_X_so R L HL Fbit E) D) = \Tr (cq_block disFE acc D) + \Tr (cq_block disFE rej D).
    { rewrite (dephase_two_block disFE Hnr Hcard2 D) linearD /=. rewrite !(lftrace_sdot_disj _ _ disFE).
      by rewrite !outp_trlf !dv_dot !eqxx !mul1r. } have Htp : \Tr ((@dephase_X_so R L HL Fbit E) D) = \Tr D.
    { by have /cptpP [_ /tpmapP H] := @dephase_X_cptp R L HL Fbit E disFE; exact: H. } by rewrite -Hsum Htp. } have HtrD0 : \Tr D = 0.
  { rewrite /D -castlf_trlf. have -> : \Tr (W - Wsig) = \Tr W - \Tr Wsig by apply: raddfB.
    have HtrWsig : \Tr Wsig = \Tr sigma := trlf_scale_id_sdot disAFB sigma. have Hptr : \Tr (\Tr_(Akey) W) = \Tr W.
    { by have /cptpP [_ /tpmapP H] := @ptraceso_qc R L HL Akey (Akey :|: (Fbit :|: Brest)); exact: H. }
by rewrite HtrWsig Hsig_tr Hptr subrr. } have HtrAcc : \Tr (cq_block disFE acc D) = \Tr (cq_block disFE acc Omega) - \Tr sigma_a.
  { rewrite HcqaccD. Timeout 15 (rewrite [X in X = _]linearB). congr (_ - _). exact: (trlf_scale_id_sdot disAB sigma_a). }
have HtrRej : \Tr (cq_block disFE rej D) = \Tr sigma_a - \Tr (cq_block disFE acc Omega).
  { have H := Htrconserv. rewrite HtrAcc HtrD0 in H. move/eqP: H; rewrite addrC addr_eq0 => /eqP H. by rewrite H opprB. }
have Hcorr : `| @complex.Re R (\Tr sigma_a) - @complex.Re R (\Tr (cq_block disFE acc Omega)) | = `| @complex.Re R (\Tr (cq_block disFE rej D)) |.
  { by rewrite HtrRej [@complex.Re R (_ - _)]raddfB /=. } have HA_psd : cq_block disFE acc Omega \is psdlf := cq_block_psd disFE acc HOmega.
    have Hsiga_psd : sigma_a \is psdlf := cq_block_psd disFB acc Hsig_psd. have Hgw := dist_uniform_gen_witness disAB HA_psd Hsiga_psd.
    rewrite -HcqaccD Hcorr in Hgw. have Hpinch := trnormH_flag_pinch disFE Hnr Hcard2 D. have Hcorr_le : `| @complex.Re R (\Tr (cq_block disFE rej D)) | <= trnormH (cq_block disFE rej D) := Re_lftrace_le_trnormH _. have Hchain : 2%:R * dist_from_uniform (cq_block disFE acc Omega) <= trnormH D.
  { apply: le_trans Hgw _. apply: le_trans (lerD (lexx _) Hcorr_le) _. exact: Hpinch. } have HtrnD : trnormH D = trnormH (W - Wsig).
  { rewrite /D. exact: (Hcast_trn _ _ Hre (W - Wsig)). } rewrite HtrnD in Hchain. rewrite Hv. have H2 : (0 : R) <= ((2%:R)^-1)%R by rewrite invr_ge0 ler0n. have Hfin := ler_wpM2l H2 Hchain. rewrite mulrA mulVf ?pnatr_eq0 // mul1r in Hfin. exact: Hfin. Qed.
End BB84DaggerAssembly.
Section BB84PublicLeakageFlagAugment.
Variable R : realType.
Notation chsType := (@chsType R).
Variables (P : @bb84_protocol R) (q : R) (dev : bb84_certified_device P q) (LE : finType) (HE : LE -> chsType).
Notation M := (bb84_round_limit P).
Notation LB := bb84_register_index.
Notation HB := (@bb84_register_space R P q dev).
Notation L := (bb84_label M LE LB).
Notation HL := (@bb84_label_space R M LE LB HE HB).
Notation V := (bb84_val M (bb84_n P) (bb84_l P) (cd_ir_bits dev) (cd_vseed_count dev) (cd_tag_count dev) (cd_paseed_count dev)).
Notation bb84_Eve := (@bb84_Eve R P LE).
Notation bb84_S := (@bb84_S R P LE).
Notation bb84_E := (@bb84_E R P LE).
Notation bb84_Ppub := (@bb84_Ppub R P LE).
Notation bb84_Epub := (@bb84_Epub R P LE).
Lemma bb84_flag_public_cast_eq (Fbit : {set L}) : Fbit :|: (bb84_Ppub :|: (bb84_S :|: bb84_E))
  = (bb84_Ppub :|: Fbit) :|: (bb84_S :|: bb84_E).
Proof. by rewrite finset.setUA (finset.setUC Fbit). Qed.
Fact bb84_public_leakage_readout_pass_prog_flagged (EA : @adversary R L HL V bb84_Eve) (xi : @cq_state R L HL (bb84_cvar M) V)
    (Hxi : forall s, xi s \is psdlf) (Fbit : {set L}) (disFS : [disjoint Fbit & bb84_S]) (disFE : [disjoint Fbit & bb84_E])
    (disFP : [disjoint Fbit & bb84_Ppub]) (acc rej : 'Idx[HL]_Fbit) (Hnr : acc != rej) (Hdim2 : dim ('H[HL]_Fbit) = 2) (k : nat)
    (Heps_c : bb84_eps_c P = (((2 ^ k)%:R : R)^-1)%R) (Htag : cd_tag_count dev = (2 ^ k)%N)
    (A B : 'F[HL]_(bb84_Ppub :|: (bb84_S :|: bb84_E))) (HApsd : A \is psdlf) (HBpsd : B \is psdlf)
    (Hsum : A + B = rhoPSE_readout_pass_prog EA xi) (HAcl : forall x x' : 'Idx[HL]_bb84_Ppub, x' != x ->
       (([> deltav x; deltav x <] \O (\1 : 'F[HL]_(bb84_S :|: bb84_E))) \o A \o
        ([> deltav x'; deltav x' <] \O (\1 : 'F[HL]_(bb84_S :|: bb84_E)))) = 0) (HBcl : forall x x' : 'Idx[HL]_bb84_Ppub, x' != x ->
       (([> deltav x; deltav x <] \O (\1 : 'F[HL]_(bb84_S :|: bb84_E))) \o B \o
        ([> deltav x'; deltav x' <] \O (\1 : 'F[HL]_(bb84_S :|: bb84_E)))) = 0) (HAcq : @is_cq_state R L HL bb84_S (bb84_E :|: bb84_Ppub)
       (castlf (bb84_public_assoc bb84_S bb84_E bb84_Ppub, bb84_public_assoc bb84_S bb84_E bb84_Ppub) A))
    (HBcq : @is_cq_state R L HL bb84_S (bb84_E :|: bb84_Ppub) (castlf (bb84_public_assoc bb84_S bb84_E bb84_Ppub,
                bb84_public_assoc bb84_S bb84_E bb84_Ppub) B)) : bb84_public_leakage (bb84_Ppub :|: Fbit) (rhoXE_readout_pass_prog EA xi)
    (bb84_leak_EC P + log2 (2%:R / bb84_eps_c P)).
Proof. refine ( let disF_PSE : [disjoint Fbit & (bb84_Ppub :|: (bb84_S :|: bb84_E))] := ltac:(by rewrite disjointXU disFP disjointXU disFS
  disFE) in let disSP' : [disjoint bb84_S & (bb84_Ppub :|: Fbit)] := ltac:(by rewrite disjointXU bb84_disSP disjoint_sym disFS) in let disEP' : [disjoint bb84_E & (bb84_Ppub :|: Fbit)] := ltac:(by rewrite disjointXU bb84_disEP disjoint_sym disFE) in let disP'_SE : [disjoint (bb84_Ppub :|: Fbit) & (bb84_S :|: bb84_E)] := ltac:(by rewrite disjointUX bb84_disPSE disjointXU disFS disFE) in let disPF : [disjoint bb84_Ppub & Fbit] := ltac:(by rewrite disjoint_sym disFP) in let Hcast : Fbit :|: (bb84_Ppub :|: (bb84_S :|: bb84_E)) = (bb84_Ppub :|: Fbit) :|: (bb84_S :|: bb84_E) := bb84_flag_public_cast_eq Fbit in {| bb84_public_disSP := disSP'; bb84_public_disEP := disEP'; bb84_public_disP_SE := disP'_SE; bb84_public_state := castlf (Hcast, Hcast) (bb84_flag_pair acc rej A B); bb84_public_leak_bound := _ |}).
  - apply: castlf_psdlf. exact: (@bb84_flag_pair_psd R L HL Fbit _ disF_PSE acc rej A B HApsd HBpsd).
  - rewrite castlf_trlfE (@bb84_flag_pair_trace R L HL Fbit _ disF_PSE acc rej A B).
      have Htr : \Tr A + \Tr B = \Tr (rhoPSE_readout_pass_prog EA xi) by rewrite -Hsum linearD. by rewrite Htr; exact: rhoPSE_readout_pass_prog_tr_le1.
  - move=> x x' Hx'x. have Htr : forall (y : 'Idx[HL]_(bb84_Ppub :|: Fbit)), (([> deltav y; deltav y <] \O (\1 : 'F[HL]_(bb84_S :|: bb84_E))) : 'F[HL]_((bb84_Ppub :|: Fbit) :|: (bb84_S :|: bb84_E))) = castlf (Hcast, Hcast) (([> deltav (idxSr y); deltav (idxSr y) <] \O (([> deltav (idxSl y); deltav (idxSl y) <] \O (\1 : 'F[HL]_(bb84_S :|: bb84_E))) : 'F[HL]_(bb84_Ppub :|: (bb84_S :|: bb84_E)))) : 'F[HL]_(Fbit :|: (bb84_Ppub :|: (bb84_S :|: bb84_E)))).
    { move=> y. apply: to_Fnd_inj. rewrite Fnd_cast (dv_split y) -tenf_outp (sdotFT _ _ disP'_SE) to_Fnd_tenE (sdotFT _ _ disF_PSE) (sdotFT _ _ (bb84_disPSE P LE)). by rewrite tenFA (tenFC (to_Fnd [> deltav (idxSr y); deltav (idxSr y) <]) (to_Fnd [> deltav (idxSl y); deltav (idxSl y) <])). } rewrite !Htr -!castlf_complf; apply/eqP; rewrite castlf_eq0; apply/eqP. set XA := (([> deltav (idxSl x); deltav (idxSl x) <] \O (\1 : 'F[HL]_(bb84_S :|: bb84_E))) : 'F[HL]_(bb84_Ppub :|: (bb84_S :|: bb84_E))).
      set XA' := (([> deltav (idxSl x'); deltav (idxSl x') <] \O (\1 : 'F[HL]_(bb84_S :|: bb84_E))) : 'F[HL]_(bb84_Ppub :|: (bb84_S :|: bb84_E))). have HOtoT : forall (a : 'F[HL]_Fbit) (b : 'F[HL]_(bb84_Ppub :|: (bb84_S :|: bb84_E))), ((a \O b) : 'F[HL]_(Fbit :|: (bb84_Ppub :|: (bb84_S :|: bb84_E)))) = a \⊗ b.
    { move=> a b. by apply: to_Fnd_inj; rewrite (sdotFT _ _ disF_PSE) to_Fnd_tenE. } have Hcomp : forall (fl : 'Idx[HL]_Fbit) (F : 'F[HL]_(bb84_Ppub :|: (bb84_S :|: bb84_E))), (([> deltav (idxSr x); deltav (idxSr x) <] \O XA) \o (([> deltav fl; deltav fl <] \O F) : 'F[HL]_(Fbit :|: (bb84_Ppub :|: (bb84_S :|: bb84_E)))) \o ([> deltav (idxSr x'); deltav (idxSr x') <] \O XA')) = (([> deltav (idxSr x); deltav (idxSr x) <] \o [> deltav fl; deltav fl <] \o [> deltav (idxSr x'); deltav (idxSr x') <]) \⊗ (XA \o F \o XA')).
    { move=> fl F. rewrite !HOtoT; rewrite -tenf_comp; last exact: disF_PSE. rewrite -tenf_comp; last exact: disF_PSE. by []. }
have Hxx : forall a b : 'Idx[HL]_(bb84_Ppub :|: Fbit), idxSl a = idxSl b -> idxSr a = idxSr b -> a = b.
    { move=> a b Ha Hb. apply/eqP. by rewrite -idxBE Ha Hb !eqxx. } rewrite /bb84_flag_pair comp_lfunDr comp_lfunDl !Hcomp.
      have [Hfr|Hfr] := eqVneq (idxSr x) (idxSr x').
    - have Hpl : idxSl x' != idxSl x.
      { apply/negP => /eqP Habs; move/negP: Hx'x; apply; apply/eqP. by apply: Hxx; [exact: Habs | exact: esym Hfr]. }
by rewrite /XA /XA' (HAcl _ _ Hpl) (HBcl _ _ Hpl); rewrite !tenf0 addr0.
    - have Hfl0 : forall fl : 'Idx[HL]_Fbit, ([> deltav (idxSr x); deltav (idxSr x) <] \o [> deltav fl; deltav fl <] \o [> deltav (idxSr x'); deltav (idxSr x') <]) = 0.
      { move=> fl. have [Hf|Hf] := eqVneq (idxSr x) fl.
        - by rewrite -Hf outp_comp dv_dot eqxx scale1r outp_comp dv_dot; rewrite (negbTE Hfr) scale0r.
        - rewrite outp_comp dv_dot (negbTE Hf) scale0r comp_lfun0l. by []. } by rewrite !Hfl0 !ten0f addr0.
  - have HrhoXE : ptrace_castl (bb84_disPSE P LE) (A + B) = rhoXE_readout_pass_prog EA xi. by rewrite Hsum; exact: rhoPSE_readout_pass_prog_marginal. have Hmove : forall (F : 'F[HL]_(Fbit :|: (bb84_Ppub :|: (bb84_S :|: bb84_E)))) (G : 'F[HL]_((bb84_Ppub :|: Fbit) :|: (bb84_S :|: bb84_E))), \Tr (castlf (Hcast, Hcast) F \o G) = \Tr (F \o castlf (esym Hcast, esym Hcast) G).
    { move=> F G. by rewrite -{1}(castlfKV Hcast Hcast G) -castlf_complf castlf_trlfE. } apply/eqP/trlf_intror => g.
      have HG' : castlf (esym Hcast, esym Hcast) (((\1 : 'F[HL]_(bb84_Ppub :|: Fbit)) \O g) : 'F[HL]_((bb84_Ppub :|: Fbit) :|: (bb84_S :|: bb84_E))) = (((\1 : 'F[HL]_Fbit) \O (((\1 : 'F[HL]_bb84_Ppub) \O g) : 'F[HL]_(bb84_Ppub :|: (bb84_S :|: bb84_E)))) : 'F[HL]_(Fbit :|: (bb84_Ppub :|: (bb84_S :|: bb84_E)))).
    { rewrite -[(\1 : 'F[HL]_(bb84_Ppub :|: Fbit))]sdotf11. apply: to_Fnd_inj. rewrite Fnd_cast !to_Fnd_sdotE !dotFA.
      rewrite (dotFC (x1 := to_Fnd (\1 : 'F[HL]_Fbit)) (x2 := to_Fnd (\1 : 'F[HL]_bb84_Ppub))) //=. }
rewrite -HrhoXE -(trlf_lift_partial (bb84_disPSE P LE) (A + B) g). rewrite -(trlf_lift_partial disP'_SE (castlf (Hcast, Hcast) (bb84_flag_pair acc rej A B)) g) Hmove HG'. rewrite (trlf_lift_partial disF_PSE (bb84_flag_pair acc rej A B) (((\1 : 'F[HL]_bb84_Ppub) \O g) : 'F[HL]_(bb84_Ppub :|: (bb84_S :|: bb84_E)))). by rewrite (@bb84_flag_pair_ptrace R L HL Fbit _ disF_PSE acc rej A B).
  - cbv zeta. have disS_EPF : [disjoint bb84_S & (bb84_E :|: (bb84_Ppub :|: Fbit))] by rewrite disjointXU bb84_disSE disjointXU bb84_disSP disjoint_sym disFS. have tenFCA : forall (a b c : @Fnd R L HL), (a \⊗ (b \⊗ c))%FND = (b \⊗ (a \⊗ c))%FND by move=> a b c; rewrite Monoid.mulmCA. rewrite castlf_comp. set Ecombo := (etrans _ _). have Htr : forall (y : 'Idx[HL]_bb84_S), (([> deltav y; deltav y <] \O (\1 : 'F[HL]_(bb84_E :|: (bb84_Ppub :|: Fbit)))) : 'F[HL]_(bb84_S :|: (bb84_E :|: (bb84_Ppub :|: Fbit)))) = castlf (Ecombo, Ecombo) ((\1 : 'F[HL]_Fbit) \O ((\1 : 'F[HL]_bb84_Ppub) \O (([> deltav y; deltav y <] \O (\1 : 'F[HL]_bb84_E)) : 'F[HL]_(bb84_S :|: bb84_E)) : 'F[HL]_(bb84_Ppub :|: (bb84_S :|: bb84_E))) : 'F[HL]_(Fbit :|: (bb84_Ppub :|: (bb84_S :|: bb84_E)))).
    { move=> y. apply: to_Fnd_inj. rewrite Fnd_cast. rewrite (sdotFT _ _ disS_EPF) (sdotFT _ _ disF_PSE) (sdotFT _ _ (@bb84_disPSE R P LE)) (sdotFT _ _ (@bb84_disSE R P LE)). rewrite [X in _ = X]tenFCA. rewrite [X in _ = Fnd_ten _ X]tenFCA. rewrite [X in _ = X]tenFCA.
      rewrite [X in _ = Fnd_ten _ (Fnd_ten _ X)]tenFC. rewrite [X in _ = Fnd_ten _ X]tenFCA. rewrite (tenF11 HL bb84_Ppub Fbit) (tenF11 HL bb84_E (bb84_Ppub :|: Fbit)). by []. } pose assoc_P := bb84_public_assoc bb84_S bb84_E bb84_Ppub.
      have Hpa_cast : forall (w : 'Idx[HL]_bb84_S), castlf (assoc_P, assoc_P) (((\1 : 'F[HL]_bb84_Ppub) \O (([> deltav w; deltav w <] \O (\1 : 'F[HL]_bb84_E)) : 'F[HL]_(bb84_S :|: bb84_E))) : 'F[HL]_(bb84_Ppub :|: (bb84_S :|: bb84_E))) = (([> deltav w; deltav w <] \O (\1 : 'F[HL]_(bb84_E :|: bb84_Ppub))) : 'F[HL]_(bb84_S :|: (bb84_E :|: bb84_Ppub))).
    { move=> w. apply: to_Fnd_inj. rewrite Fnd_cast. rewrite (sdotFT _ _ (@bb84_disSEpub R P LE)) (sdotFT _ _ (@bb84_disPSE R P LE)) (sdotFT _ _ (@bb84_disSE R P LE)). rewrite [X in X = _]tenFCA. rewrite [X in Fnd_ten _ X = _]tenFC. rewrite (tenF11 HL bb84_E bb84_Ppub).
      by []. } have HOtoT : forall (a : 'F[HL]_Fbit) (b : 'F[HL]_(bb84_Ppub :|: (bb84_S :|: bb84_E))), ((a \O b) : 'F[HL]_(Fbit :|: (bb84_Ppub :|: (bb84_S :|: bb84_E)))) = a \⊗ b.
    { move=> a b. by apply: to_Fnd_inj; rewrite (sdotFT _ _ disF_PSE) to_Fnd_tenE. } apply/forallP=> x; apply/forallP=> x'; apply/implyP=> Hx'x; apply/eqP. have Hblk : forall (X : 'F[HL]_(bb84_Ppub :|: (bb84_S :|: bb84_E))), @is_cq_state R L HL bb84_S (bb84_E :|: bb84_Ppub) (castlf (assoc_P, assoc_P) X) -> (((\1 : 'F[HL]_bb84_Ppub) \O (([> deltav x; deltav x <] \O (\1 : 'F[HL]_bb84_E)) : 'F[HL]_(bb84_S :|: bb84_E))) \o X \o ((\1 : 'F[HL]_bb84_Ppub) \O (([> deltav x'; deltav x' <] \O (\1 : 'F[HL]_bb84_E)) : 'F[HL]_(bb84_S :|: bb84_E)))) = 0.
    { move=> X HX. move: HX => /forallP/(_ x)/forallP/(_ x')/implyP/(_ Hx'x)/eqP HXi.
      have Hc0 : castlf (assoc_P, assoc_P) (((\1 : 'F[HL]_bb84_Ppub) \O (([> deltav x; deltav x <] \O (\1 : 'F[HL]_bb84_E)) : 'F[HL]_(bb84_S :|: bb84_E))) \o X \o ((\1 : 'F[HL]_bb84_Ppub) \O (([> deltav x'; deltav x' <] \O (\1 : 'F[HL]_bb84_E)) : 'F[HL]_(bb84_S :|: bb84_E)))) = 0.
      { by rewrite -HXi -(Hpa_cast x) -(Hpa_cast x') -!castlf_complf. } by move/eqP: Hc0; rewrite castlf_eq0 => /eqP. }
rewrite !Htr -!castlf_complf; apply/eqP; rewrite castlf_eq0; apply/eqP. have Hcomp : forall (fl : 'Idx[HL]_Fbit) (F : 'F[HL]_(bb84_Ppub :|: (bb84_S :|: bb84_E))), (((\1 : 'F[HL]_Fbit) \O ((\1 : 'F[HL]_bb84_Ppub) \O (([> deltav x; deltav x <] \O (\1 : 'F[HL]_bb84_E)) : 'F[HL]_(bb84_S :|: bb84_E)))) \o (([> deltav fl; deltav fl <] \O F) : 'F[HL]_(Fbit :|: (bb84_Ppub :|: (bb84_S :|: bb84_E)))) \o ((\1 : 'F[HL]_Fbit) \O ((\1 : 'F[HL]_bb84_Ppub) \O (([> deltav x'; deltav x' <] \O (\1 : 'F[HL]_bb84_E)) : 'F[HL]_(bb84_S :|: bb84_E))))) = (((\1 : 'F[HL]_Fbit) \o [> deltav fl; deltav fl <] \o (\1 : 'F[HL]_Fbit)) \⊗ (((\1 : 'F[HL]_bb84_Ppub) \O (([> deltav x; deltav x <] \O (\1 : 'F[HL]_bb84_E)) : 'F[HL]_(bb84_S :|: bb84_E))) \o F \o ((\1 : 'F[HL]_bb84_Ppub) \O (([> deltav x'; deltav x' <] \O (\1 : 'F[HL]_bb84_E)) : 'F[HL]_(bb84_S :|: bb84_E))))).
    { move=> fl F. rewrite !HOtoT. rewrite -tenf_comp; last exact: disF_PSE. rewrite -tenf_comp; last exact: disF_PSE. by []. }
by rewrite /bb84_flag_pair comp_lfunDr comp_lfunDl !Hcomp (Hblk A HAcq) (Hblk B HBcq); rewrite !tenf0 addr0.
  -  by rewrite (tenv_dim disPF) bb84_dim_Ppub Hdim2; exact: (bb84_ec_tag_leak_bound_flagged Heps_c Htag). Defined.
Definition bb84_pass_block_readout_pass_prog (EA : @adversary R L HL V bb84_Eve) (xi : @cq_state R L HL (bb84_cvar M) V) :
    'F[HL]_(bb84_Ppub :|: (bb84_S :|: bb84_E)) := ptrace_cast_gen (bb84_setT_diff_complement (bb84_Ppub :|: (bb84_S :|: bb84_E)))
    (((@complex.Re R (\Tr (bb84_pe_pass_leakage_public_readout_state EA xi)))^-1)%:C *: bb84_pass_leakage_public_readout_state EA xi).
Definition bb84_vf_block_readout_pass_prog (EA : @adversary R L HL V bb84_Eve) (xi : @cq_state R L HL (bb84_cvar M) V) :
    'F[HL]_(bb84_Ppub :|: (bb84_S :|: bb84_E)) := ptrace_cast_gen (bb84_setT_diff_complement (bb84_Ppub :|: (bb84_S :|: bb84_E)))
    (((@complex.Re R (\Tr (bb84_pe_pass_leakage_public_readout_state EA xi)))^-1)%:C *: bb84_vf_leakage_public_readout_state EA xi).
Lemma bb84_pass_vf_block_sum (EA : @adversary R L HL V bb84_Eve) (xi : @cq_state R L HL (bb84_cvar M) V) :
  bb84_pass_block_readout_pass_prog EA xi + bb84_vf_block_readout_pass_prog EA xi = rhoPSE_readout_pass_prog EA xi.
Proof. have ptrace_cast_gen_add : forall (S T B : {set L}) (eq : S :\: B = T) (x y : 'F[HL]_S), ptrace_cast_gen eq (x + y) = ptrace_cast_gen
  eq x
    + ptrace_cast_gen eq y.
  { move=> S T B eq x y. by rewrite /ptrace_cast_gen linearD /= linearD. }
rewrite /bb84_pass_block_readout_pass_prog /bb84_vf_block_readout_pass_prog /rhoPSE_readout_pass_prog /=.
    by rewrite !ptrace_cast_gen_scale -scalerDr -ptrace_cast_gen_add; rewrite -(bb84_pe_pass_leakage_public_readout_state_split EA xi). Qed.
Lemma bb84_pass_block_readout_pass_prog_psd (EA : @adversary R L HL V bb84_Eve) (xi : @cq_state R L HL (bb84_cvar M) V) :
  (forall s, xi s \is psdlf) -> bb84_pass_block_readout_pass_prog EA xi \is psdlf.
Proof. move=> Hxi; rewrite /bb84_pass_block_readout_pass_prog. have Hstp_psd : bb84_pe_pass_leakage_public_readout_state EA xi \is psdlf.
  { rewrite /bb84_pe_pass_leakage_public_readout_state. apply: bb84_pe_pass_history_public_readout_state_psd.
    - exact: bb84_leakage_public_register_state_den1lf.
    - exact: Hxi. } have Hst_psd : bb84_pass_leakage_public_readout_state EA xi \is psdlf.
  { rewrite /bb84_pass_leakage_public_readout_state. apply: bb84_pass_history_public_readout_state_psd.
    - exact: bb84_leakage_public_register_state_den1lf.
    - exact: Hxi. } have Hstp_ge0 : 0 <= @complex.Re R (\Tr (bb84_pe_pass_leakage_public_readout_state EA xi)).
      by have := psdlf_trlf Hstp_psd; rewrite lecE /= => /andP[]. by apply: ptrace_cast_gen_psdlf; apply: psdlfZ; last exact: Hst_psd; rewrite lecR invr_ge0. Qed.
Lemma bb84_vf_block_readout_pass_prog_psd (EA : @adversary R L HL V bb84_Eve) (xi : @cq_state R L HL (bb84_cvar M) V) :
  (forall s, xi s \is psdlf) -> bb84_vf_block_readout_pass_prog EA xi \is psdlf.
Proof. move=> Hxi; rewrite /bb84_vf_block_readout_pass_prog. have Hstp_psd : bb84_pe_pass_leakage_public_readout_state EA xi \is psdlf.
  { rewrite /bb84_pe_pass_leakage_public_readout_state. apply: bb84_pe_pass_history_public_readout_state_psd.
    - exact: bb84_leakage_public_register_state_den1lf.
    - exact: Hxi. } have Hstp_ge0 : 0 <= @complex.Re R (\Tr (bb84_pe_pass_leakage_public_readout_state EA xi)).
      by have := psdlf_trlf Hstp_psd; rewrite lecE /= => /andP[]. have Hst_psd : bb84_vf_leakage_public_readout_state EA xi \is psdlf by apply: bb84_vf_leakage_public_readout_state_psd; exact: Hxi. by apply: ptrace_cast_gen_psdlf; apply: psdlfZ; last exact: Hst_psd; rewrite lecR invr_ge0. Qed.
Lemma bb84_pass_block_readout_pass_prog_classical (EA : @adversary R L HL V bb84_Eve) (xi : @cq_state R L HL (bb84_cvar M) V)
    (p p' : 'Idx[HL]_bb84_Ppub) : p' != p -> ((([> deltav p ; deltav p <] \O (\1 : 'F[HL]_(bb84_S :|: bb84_E))) \o
    bb84_pass_block_readout_pass_prog EA xi) \o ([> deltav p' ; deltav p' <] \O (\1 : 'F[HL]_(bb84_S :|: bb84_E)))) = 0.
Proof. move=> Hp'p; rewrite /bb84_pass_block_readout_pass_prog. set st := bb84_pass_leakage_public_readout_state EA xi.
  set c := ((@complex.Re R (\Tr (bb84_pe_pass_leakage_public_readout_state EA xi)))^-1)%:C. set Pp := (([> deltav p ; deltav p <] \O (\1 : 'F[HL]_(bb84_S :|: bb84_E))) : 'F[HL]_(bb84_Ppub :|: (bb84_S :|: bb84_E))). set Pp' := (([> deltav p' ; deltav p' <] \O (\1 : 'F[HL]_(bb84_S :|: bb84_E))) : 'F[HL]_(bb84_Ppub :|: (bb84_S :|: bb84_E))). apply/eqP/trlf_intror => g.
  rewrite comp_lfun0l -!comp_lfunA lftraceC -comp_lfunA. rewrite (ptrace_cast_gen_setC_liftf_lf_tr (bb84_setT_diff_complement (bb84_Ppub :|: (bb84_S :|: bb84_E))) (c *: st) (Pp' \o g \o Pp)). rewrite -comp_lfunZl linearZ /= !liftf_lf_comp.
  rewrite !comp_lfunA lftraceC -!comp_lfunA !comp_lfunA (bb84_pass_leakage_public_readout_state_classical_E EA xi Hp'p) comp_lfun0l.
  have Htr0 : \Tr (0 : 'F[HL]_(bb84_Ppub :|: (bb84_S :|: bb84_E))) = 0 by rewrite linear0. have Htr0_full : \Tr (0 : 'F[HL]_(setTfor L)) = 0 by rewrite linear0. by rewrite Htr0_full Htr0; rewrite mulr0. Qed.
Lemma bb84_pass_block_readout_pass_prog_pa_cq (EA : @adversary R L HL V bb84_Eve) (xi : @cq_state R L HL (bb84_cvar M) V) :
  let eq_pub_assoc := bb84_public_assoc bb84_S bb84_E bb84_Ppub in @is_cq_state R L HL bb84_S (bb84_E :|: bb84_Ppub)
    (castlf (eq_pub_assoc, eq_pub_assoc) (bb84_pass_block_readout_pass_prog EA xi)).
Proof. have bb84_pass_block_readout_pass_prog_key_cq : forall (EA : @adversary R L HL V bb84_Eve) (xi : @cq_state R L HL (bb84_cvar M) V) (x
  x' : 'Idx[HL]_bb84_S), x' != x -> (((\1 : 'F[HL]_bb84_Ppub) \O (([> deltav x ; deltav x <] \O (\1 : 'F[HL]_bb84_E)) : 'F[HL]_(bb84_S :|: bb84_E)) \o bb84_pass_block_readout_pass_prog EA xi) \o ((\1 : 'F[HL]_bb84_Ppub) \O (([> deltav x' ; deltav x' <] \O (\1 : 'F[HL]_bb84_E)) : 'F[HL]_(bb84_S :|: bb84_E)))) = 0.
{ clear xi EA; move=> EA xi x x'. move=> Hx'x; rewrite /bb84_pass_block_readout_pass_prog. set st := bb84_pass_leakage_public_readout_state EA xi. set c := ((@complex.Re R (\Tr (bb84_pe_pass_leakage_public_readout_state EA xi)))^-1)%:C. set KxE := (([> deltav x ; deltav x <] \O (\1 : 'F[HL]_bb84_E)) : 'F[HL]_(bb84_S :|: bb84_E)). set KxE' := (([> deltav x' ; deltav x' <] \O (\1 : 'F[HL]_bb84_E)) : 'F[HL]_(bb84_S :|: bb84_E)). set KxPSE := ((\1 : 'F[HL]_bb84_Ppub) \O KxE : 'F[HL]_(bb84_Ppub :|: (bb84_S :|: bb84_E))). set KxPSE' := ((\1 : 'F[HL]_bb84_Ppub) \O KxE' : 'F[HL]_(bb84_Ppub :|: (bb84_S :|: bb84_E))).
  have Hlift : forall x0 : 'Idx[HL]_bb84_S, liftf_lf (((\1 : 'F[HL]_bb84_Ppub) \O (([> deltav x0 ; deltav x0 <] \O (\1 : 'F[HL]_bb84_E)) : 'F[HL]_(bb84_S :|: bb84_E))) : 'F[HL]_(bb84_Ppub :|: (bb84_S :|: bb84_E))) = liftf_lf (([> deltav x0 ; deltav x0 <] \O (\1 : 'F[HL]_(bb84_Epub :|: bb84_Ppub))) : 'F[HL]_(bb84_S :|: (bb84_Epub :|: bb84_Ppub))).
  { move=> x0. have HdisS_EpubP : [disjoint bb84_S & bb84_Epub :|: bb84_Ppub] by rewrite disjointXU (@bb84_disS_Epub R P LE) (@bb84_disSP R P LE). set KxE0 := (([> deltav x0 ; deltav x0 <] \O (\1 : 'F[HL]_bb84_E)) : 'F[HL]_(bb84_S :|: bb84_E)).
    have Hleft : (((\1 : 'F[HL]_bb84_Ppub) \O KxE0) : 'F[HL]_(bb84_Ppub :|: (bb84_S :|: bb84_E))) = (\1 : 'F[HL]_bb84_Ppub) \⊗ KxE0.
    { by apply: to_Fnd_inj; rewrite (sdotFT _ _ (@bb84_disPSE R P LE)) to_Fnd_tenE. } have HkeyE : KxE0 = [> deltav x0 ; deltav x0 <] \⊗ (\1 : 'F[HL]_bb84_E).
    { by apply: to_Fnd_inj; rewrite (sdotFT _ _ (@bb84_disSE R P LE)) to_Fnd_tenE. } have Hright : (([> deltav x0 ; deltav x0 <] \O (\1 : 'F[HL]_(bb84_Epub :|: bb84_Ppub))) : 'F[HL]_(bb84_S :|: (bb84_Epub :|: bb84_Ppub))) = [> deltav x0 ; deltav x0 <] \⊗ (\1 : 'F[HL]_(bb84_Epub :|: bb84_Ppub)).
    { by apply: to_Fnd_inj; rewrite (sdotFT _ _ HdisS_EpubP) to_Fnd_tenE. } rewrite Hleft HkeyE Hright (liftf_lf_tenf1l _ (@bb84_disPSE R P LE)) (liftf_lf_tenf1r _ (@bb84_disSE R P LE)). by rewrite (liftf_lf_tenf1r _ HdisS_EpubP). } apply/eqP/trlf_intror => g.
      rewrite comp_lfun0l -!comp_lfunA lftraceC -comp_lfunA. rewrite (ptrace_cast_gen_setC_liftf_lf_tr (bb84_setT_diff_complement (bb84_Ppub :|: (bb84_S :|: bb84_E))) (c *: st) (KxPSE' \o g \o KxPSE)). rewrite -comp_lfunZl linearZ /= !liftf_lf_comp.
      rewrite !comp_lfunA lftraceC -!comp_lfunA !comp_lfunA (Hlift x) (Hlift x'). rewrite (bb84_pass_leakage_public_readout_state_pa_cq_Epub EA xi Hx'x) comp_lfun0l. have Htr0 : \Tr (0 : 'F[HL]_(bb84_Ppub :|: (bb84_S :|: bb84_E))) = 0 by rewrite linear0.
      have Htr0_full : \Tr (0 : 'F[HL]_(setTfor L)) = 0 by rewrite linear0. rewrite Htr0_full Htr0. by rewrite mulr0. }
set eq_pub_assoc := bb84_public_assoc bb84_S bb84_E bb84_Ppub; rewrite /is_cq_state. apply/forallP => x; apply/forallP => x'; apply/implyP => Hx'x. apply/eqP. set KxEP := (([> deltav x ; deltav x <] \O (\1 : 'F[HL]_(bb84_E :|: bb84_Ppub))) : 'F[HL]_(bb84_S :|: (bb84_E :|: bb84_Ppub))). set KxEP' := (([> deltav x' ; deltav x' <] \O (\1 : 'F[HL]_(bb84_E :|: bb84_Ppub))) : 'F[HL]_(bb84_S :|: (bb84_E :|: bb84_Ppub))). set KxE := (([> deltav x ; deltav x <] \O (\1 : 'F[HL]_bb84_E)) : 'F[HL]_(bb84_S :|: bb84_E)).
      set KxE' := (([> deltav x' ; deltav x' <] \O (\1 : 'F[HL]_bb84_E)) : 'F[HL]_(bb84_S :|: bb84_E)).
      set KxPSE := ((\1 : 'F[HL]_bb84_Ppub) \O KxE : 'F[HL]_(bb84_Ppub :|: (bb84_S :|: bb84_E))).
      set KxPSE' := ((\1 : 'F[HL]_bb84_Ppub) \O KxE' : 'F[HL]_(bb84_Ppub :|: (bb84_S :|: bb84_E))).
      have HdisP_SEdiff : [disjoint bb84_Ppub & (bb84_S :|: bb84_E) :\: bb84_S].
  { apply/disjointP => a HP. move/disjointP: (@bb84_disPSE R P LE) => HPSE; apply/negP => Hdiff. move: Hdiff; rewrite inE => /andP [_ HSE].
    by move: (HPSE a HP); rewrite HSE. } have HdisP_Ediff : [disjoint bb84_Ppub & bb84_E :\: bb84_S].
  { apply/disjointP => a HP. have HPE : [disjoint bb84_Ppub & bb84_E] by rewrite disjoint_sym (@bb84_disEP R P LE).
    move/disjointP: HPE => HPE; apply/negP => Hdiff. move: Hdiff; rewrite inE => /andP [_ HEin]. by move: (HPE a HP); rewrite HEin. }
have HdisP_S_Ediff : [disjoint bb84_Ppub & bb84_S :|: bb84_E :\: bb84_S].
  { have HPS : [disjoint bb84_Ppub & bb84_S] by rewrite disjoint_sym (@bb84_disSP R P LE). by rewrite disjointXU HPS HdisP_Ediff. }
have HdisP_E_Sdiff : [disjoint bb84_Ppub & bb84_E :|: bb84_S :\: bb84_E].
  { apply/disjointP => a HP. move/disjointP: (@bb84_disPSE R P LE) => HPSE; apply/negP => Hmem. have HSE : a \in bb84_S :|: bb84_E.
    { move: Hmem; rewrite inE => /orP [HEin | HSdiff].
      - by rewrite inE HEin orbT.
      - move: HSdiff; rewrite inE => /andP [_ HSin]. by rewrite inE HSin. } by move: (HPSE a HP); rewrite HSE. }
have Hleft : KxEP = castlf (eq_pub_assoc, eq_pub_assoc) KxPSE.
  { have HIEP : (\1 : 'F[HL]_(bb84_E :|: bb84_Ppub)) = (\1 : 'F[HL]_bb84_E) \O (\1 : 'F[HL]_bb84_Ppub).
    { by rewrite sdotf11. } apply: to_Fnd_inj. rewrite /KxEP /KxPSE /KxE HIEP Fnd_cast !to_Fnd_sdotE !dotFA -[RHS]dotFA [RHS]dotFC.
    - by [].
    - by rewrite /= HdisP_S_Ediff.
    - by rewrite /= HdisP_E_Sdiff. } have Hright : KxEP' = castlf (eq_pub_assoc, eq_pub_assoc) KxPSE'.
  { have HIEP : (\1 : 'F[HL]_(bb84_E :|: bb84_Ppub)) = (\1 : 'F[HL]_bb84_E) \O (\1 : 'F[HL]_bb84_Ppub).
    { by rewrite sdotf11. } apply: to_Fnd_inj. rewrite /KxEP' /KxPSE' /KxE' HIEP Fnd_cast !to_Fnd_sdotE !dotFA -[RHS]dotFA [RHS]dotFC.
    - by [].
    - by rewrite /= HdisP_S_Ediff.
    - by rewrite /= HdisP_E_Sdiff. } rewrite Hleft Hright -!(castlf_complf eq_pub_assoc eq_pub_assoc eq_pub_assoc); apply/eqP.
      rewrite (@castlf_eq0 R L HL _ _ _ _ (eq_pub_assoc, eq_pub_assoc) (KxPSE \o bb84_pass_block_readout_pass_prog EA xi \o KxPSE')).
      by apply/eqP; rewrite bb84_pass_block_readout_pass_prog_key_cq. Qed.
Lemma bb84_vf_block_readout_pass_prog_classical (EA : @adversary R L HL V bb84_Eve) (xi : @cq_state R L HL (bb84_cvar M) V)
    (p p' : 'Idx[HL]_bb84_Ppub) : p' != p -> ((([> deltav p ; deltav p <] \O (\1 : 'F[HL]_(bb84_S :|: bb84_E))) \o
    bb84_vf_block_readout_pass_prog EA xi) \o ([> deltav p' ; deltav p' <] \O (\1 : 'F[HL]_(bb84_S :|: bb84_E)))) = 0.
Proof. move=> Hp'p; have HA := bb84_pass_block_readout_pass_prog_classical EA xi Hp'p. have Hrho := rhoPSE_readout_pass_prog_classical EA xi
  Hp'p. have HB : bb84_vf_block_readout_pass_prog EA xi = rhoPSE_readout_pass_prog EA xi - bb84_pass_block_readout_pass_prog EA xi.
  by rewrite -(bb84_pass_vf_block_sum EA xi) addrAC subrr add0r. rewrite HB comp_lfunDr comp_lfunNr comp_lfunDl comp_lfunNl Hrho HA subrr //. Qed.
Lemma bb84_vf_block_readout_pass_prog_pa_cq (EA : @adversary R L HL V bb84_Eve) (xi : @cq_state R L HL (bb84_cvar M) V) :
  let eq_pub_assoc := bb84_public_assoc bb84_S bb84_E bb84_Ppub in @is_cq_state R L HL bb84_S (bb84_E :|: bb84_Ppub)
    (castlf (eq_pub_assoc, eq_pub_assoc) (bb84_vf_block_readout_pass_prog EA xi)).
Proof. set eq_pub_assoc := bb84_public_assoc bb84_S bb84_E bb84_Ppub; rewrite /is_cq_state. apply/forallP => x; apply/forallP => x';
  apply/implyP => Hx'x. apply/eqP. have HA := bb84_pass_block_readout_pass_prog_pa_cq EA xi. have Hrho := rhoPSE_readout_pass_prog_pa_cq EA xi. move: HA; rewrite /is_cq_state => /forallP/(_ x)/forallP/(_ x')/implyP/(_ Hx'x)/eqP HA. move: Hrho; rewrite /is_cq_state => /forallP/(_ x)/forallP/(_ x')/implyP/(_ Hx'x)/eqP Hrho. have Hvf : bb84_vf_block_readout_pass_prog EA xi = rhoPSE_readout_pass_prog EA xi - bb84_pass_block_readout_pass_prog EA xi. by rewrite -(bb84_pass_vf_block_sum EA xi) addrAC subrr add0r.
  have HB : castlf (eq_pub_assoc, eq_pub_assoc) (bb84_vf_block_readout_pass_prog EA xi) = castlf (eq_pub_assoc, eq_pub_assoc) (rhoPSE_readout_pass_prog EA xi) - castlf (eq_pub_assoc, eq_pub_assoc) (bb84_pass_block_readout_pass_prog EA xi). by rewrite Hvf linearB.
  rewrite HB comp_lfunDr comp_lfunNr comp_lfunDl comp_lfunNl Hrho HA subrr //. Qed.
End BB84PublicLeakageFlagAugment.
Section BB84PostHashFlagSpectator.
Variable (R : realType).
Notation chsType := (@chsType R).
Variable (L : finType) (HL : L -> chsType).
Variable (S E Fl Zl Fbit : {set L}).
Hypotheses (disSE : [disjoint S & E]) (disSFl : [disjoint S & Fl]) (disSZl : [disjoint S & Zl]) (disEFl : [disjoint E & Fl]).
Hypotheses (disEZl : [disjoint E & Zl]) (disFlZl : [disjoint Fl & Zl]) (disFbS : [disjoint Fbit & S]) (disFbE : [disjoint Fbit & E]).
Hypotheses (disFbFl : [disjoint Fbit & Fl]) (disFbZl : [disjoint Fbit & Zl]).
Let disSFb : [disjoint S & Fbit].
Proof. by rewrite disjoint_sym disFbS. Defined.
Let disS_FE : [disjoint S & (Fbit :|: E)].
Proof. by rewrite disjointXU disSFb disSE. Defined.
Let disZlFb : [disjoint Zl & Fbit].
Proof. by rewrite disjoint_sym disFbZl. Defined.
Let disFlFb : [disjoint Fl & Fbit].
Proof. by rewrite disjoint_sym disFbFl. Defined.
Let disZlE : [disjoint Zl & E].
Proof. by rewrite disjoint_sym disEZl. Defined.
Let disFlE : [disjoint Fl & E].
Proof. by rewrite disjoint_sym disEFl. Defined.
Let dZF_E : [disjoint (Zl :|: Fl) & E].
Proof. by rewrite disjointUX disZlE disFlE. Defined.
Let dZF_FbE : [disjoint (Zl :|: Fl) & (Fbit :|: E)].
Proof. by rewrite disjointUX !disjointXU disZlFb disZlE disFlFb disFlE. Defined.
Let dFb_ZFE : [disjoint Fbit & ((Zl :|: Fl) :|: E)].
Proof. by rewrite !disjointXU disFbZl disFbFl disFbE. Defined.
Let dFb_ZFlE : [disjoint Fbit & (Zl :|: (Fl :|: E))].
Proof. by rewrite !disjointXU disFbZl disFbFl disFbE. Defined.
Let Hin := finset.setUCA Fbit S E.
Let GEOM := etrans (finset.setUCA Fbit Zl (finset.setU Fl E)) (congr1 (finset.setU Zl) (finset.setUCA Fbit Fl E)).
Fact post_hash_flag_spectator (Fh : 'Idx[HL]_Fl -> 'Idx[HL]_S -> 'Idx[HL]_Zl) (w : 'Idx[HL]_Fbit) (rho : 'F[HL]_(S :|: E)) :
  post_hash_state disS_FE Fh (castlf (Hin, Hin) (([> deltav w ; deltav w <] \O rho) : 'F[HL]_(Fbit :|: (S :|: E)))) = castlf (GEOM, GEOM)
    (([> deltav w ; deltav w <] \O post_hash_state disSE Fh rho) : 'F[HL]_(Fbit :|: (Zl :|: (Fl :|: E)))).
Proof. have cq_block_irrel : forall (X Y : {set L}) (d d' : [disjoint X & Y]) (x : 'Idx[HL]_X) (r : 'F[HL]_(X :|: Y)), cq_block d x r =
  cq_block d' x r.
  { move=> X Y d d' x r. by rewrite (bool_irrelevance d d'). } have sdot_castlf_r : forall (Y : 'F[HL]_((Zl :|: Fl) :|: E)) (w : 'F[HL]_Fbit) (e : (Zl :|: Fl) :|: E = Zl :|: (Fl :|: E)), (w \O (castlf (e, e) Y) : 'F[HL]_(Fbit :|: (Zl :|: (Fl :|: E)))) = castlf (congr1 (finset.setU Fbit) e, congr1 (finset.setU Fbit) e) ((w \O Y) : 'F[HL]_(Fbit :|: ((Zl :|: Fl) :|: E))).
  { move=> Y {}w e. apply: to_Fnd_inj. rewrite (sdotFT _ _ dFb_ZFlE) Fnd_cast Fnd_cast (sdotFT _ _ dFb_ZFE). by []. }
have sdot_flag_term_reorder : forall (p : 'F[HL]_(Zl :|: Fl)) (w : 'F[HL]_Fbit) (g : 'F[HL]_E) (c1 : (Zl :|: Fl) :|: (Fbit :|: E) = Zl :|: (Fl :|: (Fbit :|: E))) (c2 : Fbit :|: ((Zl :|: Fl) :|: E) = Zl :|: (Fl :|: (Fbit :|: E))), castlf (c1, c1) ((p \O (w \O g)) : 'F[HL]_((Zl :|: Fl) :|: (Fbit :|: E))) = castlf (c2, c2) ((w \O (p \O g)) : 'F[HL]_(Fbit :|: ((Zl :|: Fl) :|: E))).
{ clear rho w Fh; move=> p w g c1 c2. apply: to_Fnd_inj. rewrite !Fnd_cast (sdotFT _ _ dZF_FbE) (sdotFT _ _ disFbE) (sdotFT _ _ dFb_ZFE) (sdotFT _ _ dZF_E). by rewrite tenFA (tenFC (to_Fnd p) (to_Fnd w)) -tenFA. } set Pw := ([> deltav w ; deltav w <] : 'F[HL]_Fbit).
  have Hcqx : forall x : 'Idx[HL]_S, cq_block disS_FE x (castlf (Hin, Hin) ((Pw \O rho) : 'F[HL]_(Fbit :|: (S :|: E)))) = Pw \O cq_block disSE x rho.
  { move=> x; have H := cq_block_omega_commute disSFb disSE disFbE x Pw rho. rewrite -H; exact: cq_block_irrel. }
have Hsumx : forall (f : 'Idx[HL]_Fl) (z : 'Idx[HL]_Zl), (\sum_(x : 'Idx[HL]_S | Fh f x == z) cq_block disS_FE x (castlf (Hin, Hin) ((Pw \O rho) : 'F[HL]_(Fbit :|: (S :|: E))))) = Pw \O (\sum_(x : 'Idx[HL]_S | Fh f x == z) cq_block disSE x rho).
  { move=> f z. under eq_bigr => x _ do rewrite Hcqx. by rewrite -linear_sumr. } rewrite /post_hash_state sdot_castlf_r castlf_comp.
    rewrite [X in X = _]linearZ /=. rewrite [X in _ *: X = _]linear_sum /=. under [X in _ *: X = _] eq_bigr => f _ do rewrite linear_sum /=.
    under [X in _ *: X = _] eq_bigr => f _. under eq_bigr => z _ do rewrite Hsumx. over. rewrite [X in _ = castlf _ X]linearZr /=.
    rewrite [X in _ = X]linearZ /=. rewrite [X in _ = _ *: castlf _ X]linear_sumr /=. rewrite [X in _ = _ *: X]linear_sum /=.
    under [X in _ = _ *: X] eq_bigr => f _ do rewrite linear_sumr /= linear_sum /=. congr (_ *: _); apply: eq_bigr => f _; apply: eq_bigr => z _. exact: sdot_flag_term_reorder. Qed.
Fact post_hash_flag_pair_dist (Fh : 'Idx[HL]_Fl -> 'Idx[HL]_S -> 'Idx[HL]_Zl) (acc rej : 'Idx[HL]_Fbit) (A B : 'F[HL]_(S :|: E)) :
  post_hash_state disS_FE Fh (castlf (Hin, Hin) ((bb84_flag_pair acc rej A B) : 'F[HL]_(Fbit :|: (S :|: E)))) = castlf (GEOM, GEOM)
    ((bb84_flag_pair acc rej (post_hash_state disSE Fh A) (post_hash_state disSE Fh B)) : 'F[HL]_(Fbit :|: (Zl :|: (Fl :|: E)))).
Proof. have PHadd : forall X Y : 'F[HL]_(S :|: (Fbit :|: E)), post_hash_state disS_FE Fh (X + Y) = post_hash_state disS_FE Fh X +
  post_hash_state disS_FE Fh Y.
  { move=> X Y. have := post_hash_state_linear disS_FE Fh 1 X Y. by rewrite !scale1r. } by rewrite /bb84_flag_pair linearD /= PHadd !post_hash_flag_spectator; rewrite -linearD. Qed.
End BB84PostHashFlagSpectator.
Section BB84PostHashCastE.
Variable (R : realType).
Notation chsType := (@chsType R).
Variable (L : finType) (HL : L -> chsType).
Fact post_hash_state_cast_E (X E1 E2 Fl Zl : {set L}) (disXE1 : [disjoint X & E1]) (disXE2 : [disjoint X & E2])
    (Fh : 'Idx[HL]_Fl -> 'Idx[HL]_X -> 'Idx[HL]_Zl) (eqE : E1 = E2) (cin : (X :|: E1) = (X :|: E2))
    (cout : (Zl :|: (Fl :|: E1)) = (Zl :|: (Fl :|: E2))) (rho : 'F[HL]_(X :|: E1)) : post_hash_state disXE2 Fh (castlf (cin, cin) rho)
  = castlf (cout, cout) (post_hash_state disXE1 Fh rho).
Proof. by case: E2 / eqE in disXE2 cin cout *; rewrite !castlf_id (bool_irrelevance disXE2 disXE1). Qed.
Lemma dist_from_uniform_side_cast (A B1 B2 : {set L}) (eqB : B1 = B2) (cAB : (A :|: B1) = (A :|: B2)) (rho : 'F[HL]_(A :|: B1)) :
  dist_from_uniform (castlf (cAB, cAB) rho) = dist_from_uniform rho.
Proof. case: B2 / eqB in cAB *. by rewrite castlf_id. Qed.
Fact bb84_flag_pair_cast_side (Fbit E1 E2 : {set L}) (acc rej : 'Idx[HL]_Fbit) (eqE : E1 = E2) (cE : E1 = E2)
    (cFbitE : (Fbit :|: E1) = (Fbit :|: E2)) (A B : 'F[HL]_E1) : castlf (cFbitE, cFbitE) (@bb84_flag_pair R L HL Fbit E1 acc rej A B)
  = @bb84_flag_pair R L HL Fbit E2 acc rej (castlf (cE, cE) A) (castlf (cE, cE) B).
Proof. case: E2 / eqE in cE cFbitE *. by rewrite !castlf_id. Qed.
End BB84PostHashCastE.
Section BB84DistScaleUb.
Variable (R : realType).
Notation chsType := (@chsType R).
Variable (L : finType) (H : L -> chsType) (A B : {set L}).
Hypothesis disAB : [disjoint A & B].
Lemma dist_uniform_scale_ub (rhoAB : 'F[H]_(A :|: B)) (c : R) :
  rhoAB \is psdlf -> 0 <= c -> dist_from_uniform (c%:C *: rhoAB) <= c * dist_from_uniform rhoAB.
Proof. move=> Hrho Hc; case: (eqVneq c 0) => [-> | Hc0].
  - rewrite mul0r rmorph0 scale0r. apply: dist_uniform_lb. exists 0; split; first by rewrite qualifE h2mx0 psdmx0. split; first by rewrite !linear0. by rewrite sdotf0 scaler0 subr0 /trnormH h2mx0 trnorm0 mulr0.
  - have Hcpos : 0 < c by rewrite lt_def Hc0 Hc. have Hpsd_scaled : (c%:C *: rhoAB) \is psdlf by apply: psdlfZ; [rewrite lecR Hc | exact: Hrho]. have Hc_inv_nn : (0 : R) <= (c^-1)%R by rewrite invr_ge0 Hc.
    have Hge := @dist_uniform_scale_le R L H A B disAB (c%:C *: rhoAB) ((c^-1)%R) Hpsd_scaled Hc_inv_nn.
    have Hsimpl : (c^-1)%:C *: (c%:C *: rhoAB) = rhoAB.
    { rewrite scalerA fmorphV mulVf ?scale1r //. by rewrite realc_eq0. } rewrite Hsimpl in Hge. have := ler_wpM2l (ltW Hcpos) Hge.
      by rewrite mulrA mulfV ?mul1r //. Qed.
End BB84DistScaleUb.
Section BB84FlaggedRecognize.
Variable R : realType.
Notation chsType := (@chsType R).
Variables (P : @bb84_protocol R) (q : R) (dev : bb84_certified_device P q) (LE : finType) (HE : LE -> chsType).
Notation M := (bb84_round_limit P).
Notation LB := bb84_register_index.
Notation HB := (@bb84_register_space R P q dev).
Notation L := (bb84_label M LE LB).
Notation HL := (@bb84_label_space R M LE LB HE HB).
Notation V := (bb84_val M (bb84_n P) (bb84_l P) (cd_ir_bits dev) (cd_vseed_count dev) (cd_tag_count dev) (cd_paseed_count dev)).
Notation bb84_Eve := (@bb84_Eve R P LE).
Notation bb84_S := (@bb84_S R P LE).
Notation bb84_E := (@bb84_E R P LE).
Notation bb84_Ppub := (@bb84_Ppub R P LE).
Notation bb84_Zl := (@bb84_Zl R P LE).
Notation bb84_Fl := (@bb84_Fl R P LE).
Notation bb84_disSEpub := (@bb84_disSEpub R P LE).
Notation bb84_pa_hash_index := (@bb84_pa_hash_index R P q dev LE HE).
Definition bb84_PHpass (EA : @adversary R L HL V bb84_Eve) (xi : @cq_state R L HL (bb84_cvar M) V) :
    'F[HL]_(bb84_Zl :|: (bb84_Fl :|: (bb84_E :|: bb84_Ppub))) := post_hash_state bb84_disSEpub bb84_pa_hash_index
    (castlf (bb84_public_assoc bb84_S bb84_E bb84_Ppub, bb84_public_assoc bb84_S bb84_E bb84_Ppub)
      (bb84_pass_block_readout_pass_prog EA xi)).
Definition bb84_PHvf (EA : @adversary R L HL V bb84_Eve) (xi : @cq_state R L HL (bb84_cvar M) V) :
    'F[HL]_(bb84_Zl :|: (bb84_Fl :|: (bb84_E :|: bb84_Ppub))) := post_hash_state bb84_disSEpub bb84_pa_hash_index
    (castlf (bb84_public_assoc bb84_S bb84_E bb84_Ppub, bb84_public_assoc bb84_S bb84_E bb84_Ppub) (bb84_vf_block_readout_pass_prog EA xi)).
Fact bb84_rhoZFEpub_kappa_PHpass (EA : @adversary R L HL V bb84_Eve) (xi : @cq_state R L HL (bb84_cvar M) V) :
  @complex.Re R (\Tr (bb84_pe_pass_leakage_public_readout_state EA xi)) != 0 -> rhoZFEpub_readout_prog EA xi =
    (((@complex.Re R (\Tr (bb84_pass_leakage_public_readout_state EA xi)))^-1)
      * (@complex.Re R (\Tr (bb84_pe_pass_leakage_public_readout_state EA xi))))%:C *: bb84_PHpass EA xi.
Proof. have bb84_post_hash_stateZ : forall (a : @hermitian.C R) (X : 'F[HL]_(bb84_S :|: (bb84_E :|: bb84_Ppub))), post_hash_state
  bb84_disSEpub bb84_pa_hash_index (a *: X) = a *: post_hash_state bb84_disSEpub bb84_pa_hash_index X.
  { move=> a X. have Hpl := post_hash_state_linear bb84_disSEpub bb84_pa_hash_index.
    have Hp0 : post_hash_state bb84_disSEpub bb84_pa_hash_index 0 = 0.
  { have E := Hpl 1 0 0. move: E; rewrite !scale1r !addr0 => E. by apply: (addrI (post_hash_state bb84_disSEpub bb84_pa_hash_index 0)); rewrite addr0 -E. }
have := Hpl a X 0. by rewrite addr0 Hp0 addr0. }
move=> Hpe; set pass := @complex.Re R (\Tr (bb84_pass_leakage_public_readout_state EA xi)).
    set pe := @complex.Re R (\Tr (bb84_pe_pass_leakage_public_readout_state EA xi)). have HPHpass : bb84_PHpass EA xi = (pe^-1)%:C *: ptrace_cast_gen (bb84_setT_diff_complement (bb84_Zl :|: (bb84_Fl :|: (bb84_E :|: bb84_Ppub)))) (bb84_pass_pa_public_readout_state EA xi).
  { rewrite /bb84_PHpass /bb84_pass_block_readout_pass_prog -/pe. rewrite ptrace_cast_gen_scale linearZ /= bb84_post_hash_stateZ.
    by rewrite -(bb84_pa_public_readout_post_hashE EA xi). } by rewrite HPHpass (rhoZFEpub_readout_progE EA xi) /= -/pass scalerA -rmorphM; congr (_ %:C *: _); rewrite -mulrA (mulfV Hpe) mulr1. Qed.
Lemma castlf_irrel (S T : {set L}) (e1 e2 : S = T) (X : 'F[HL]_S) : castlf (e1, e1) X = castlf (e2, e2) X.
Proof. by rewrite (eq_irrelevance e1 e2). Qed.
Fact post_hash_state_irrel (X E Fl Zl : {set L}) (d d' : [disjoint X & E]) (Fh : 'Idx[HL]_Fl -> 'Idx[HL]_X -> 'Idx[HL]_Zl)
    (rho : 'F[HL]_(X :|: E)) : post_hash_state d Fh rho = post_hash_state d' Fh rho.
Proof. by rewrite (bool_irrelevance d d'). Qed.
Fact bb84_flagged_post_hash_recognize (EA : @adversary R L HL V bb84_Eve) (xi : @cq_state R L HL (bb84_cvar M) V) (Fbit : {set L})
    (disFS : [disjoint Fbit & bb84_S]) (disFbE : [disjoint Fbit & bb84_E])
    (disFP : [disjoint Fbit & bb84_Ppub]) (disFbZl : [disjoint Fbit & bb84_Zl]) (disFbFl : [disjoint Fbit & bb84_Fl])
    (acc rej : 'Idx[HL]_Fbit) (disSEPF : [disjoint bb84_S & (bb84_E :|: (bb84_Ppub :|: Fbit))])
    (bigcast : Fbit :|: (bb84_Ppub :|: (bb84_S :|: bb84_E)) = bb84_S :|: (bb84_E :|: (bb84_Ppub :|: Fbit)))
    (outcast : Fbit :|: (bb84_Zl :|: (bb84_Fl :|: (bb84_E :|: bb84_Ppub))) = bb84_Zl :|: (bb84_Fl :|: (bb84_E :|: (bb84_Ppub :|: Fbit)))) :
  post_hash_state disSEPF bb84_pa_hash_index (castlf (bigcast, bigcast) (bb84_flag_pair acc rej (bb84_pass_block_readout_pass_prog EA xi)
        (bb84_vf_block_readout_pass_prog EA xi))) = castlf (outcast, outcast)
      (bb84_flag_pair acc rej (bb84_PHpass EA xi) (bb84_PHvf EA xi)).
Proof. pose pa := bb84_public_assoc bb84_S bb84_E bb84_Ppub; set A := bb84_pass_block_readout_pass_prog EA xi.
  set B := bb84_vf_block_readout_pass_prog EA xi. have disFbEP : [disjoint Fbit & (bb84_E :|: bb84_Ppub)] by rewrite disjointXU disFbE disFP. have eqEside : (bb84_E :|: (bb84_Ppub :|: Fbit)) = (Fbit :|: (bb84_E :|: bb84_Ppub)).
  { by rewrite finset.setUA (finset.setUC (bb84_E :|: bb84_Ppub) Fbit). } pose cin := congr1 (finset.setU bb84_S) eqEside; pose cout := congr1 (finset.setU bb84_Zl) (congr1 (finset.setU bb84_Fl) eqEside). pose cFbitP := congr1 (finset.setU Fbit) pa.
    have disS_FE : [disjoint bb84_S & (Fbit :|: (bb84_E :|: bb84_Ppub))] by rewrite disjointXU bb84_disSEpub andbT disjoint_sym; exact: disFS. have Hphd := post_hash_flag_pair_dist (S := bb84_S) (E := bb84_E :|: bb84_Ppub) (Fl := bb84_Fl) (Zl := bb84_Zl) (Fbit := Fbit) bb84_disSEpub (@bb84_disEpubF R P LE) (@bb84_disEpubZl R P LE) disFS disFbEP disFbFl disFbZl bb84_pa_hash_index acc rej (castlf (pa, pa) A) (castlf (pa, pa) B). rewrite -(@bb84_flag_pair_cast_side R L HL Fbit (bb84_Ppub :|: (bb84_S :|: bb84_E)) (bb84_S :|: (bb84_E :|: bb84_Ppub)) acc rej pa pa cFbitP A B) in Hphd. rewrite castlf_comp in Hphd. rewrite (post_hash_state_irrel _ disS_FE) in Hphd.
    rewrite (castlf_irrel _ (etrans bigcast cin)) in Hphd. apply: (can_inj (castlfK cout cout)).
    rewrite -(@post_hash_state_cast_E R L HL bb84_S (bb84_E :|: (bb84_Ppub :|: Fbit)) (Fbit :|: (bb84_E :|: bb84_Ppub)) bb84_Fl bb84_Zl disSEPF disS_FE bb84_pa_hash_index eqEside cin cout (castlf (bigcast, bigcast) (bb84_flag_pair acc rej A B))). rewrite castlf_comp Hphd.
    by rewrite [X in _ = X]castlf_comp; rewrite /pa /A /B -/(bb84_PHpass EA xi) -/(bb84_PHvf EA xi); exact: castlf_irrel. Qed.
End BB84FlaggedRecognize.
Section BB84XDiagPair.
Variable R : realType.
Notation C := (@hermitian.C R).
Variables (P : @bb84_protocol R) (q : R) (dev : bb84_certified_device P q).
Definition bb84_x_diag_pair : 'M[C]_(4 * 2) := \sum_(bit : bool) ((2%:R)^-1)%:C *:
    ((delta_mx (bb84_prep_index BasisX bit) (bb84_prep_index BasisX bit) : 'M[C]_4) *t cd_rho dev BasisX bit).
Lemma bb84_x_diag_pair_ptr_ok : bb84_eb_pair_ptr_ok bb84_x_diag_pair.
Proof. rewrite /bb84_eb_pair_ptr_ok /bb84_x_diag_pair mulmx_sumr mulmx_suml; apply: eq_bigr => bit _. rewrite -scalemxAr -scalemxAl;
  congr (_ *: _). exact: bb84_src_x_span_conj_delta. Qed.
Lemma bb84_x_diag_pair_x_branch_ok : bb84_eb_pair_x_branch_ok dev bb84_x_diag_pair.
Proof. move=> bit; rewrite /bb84_x_diag_pair /bb84_prep_source_projector; rewrite mulmx_sumr mulmx_suml (bigD1 bit) //= big1 ?addr0.
  - rewrite -scalemxAr -scalemxAl; congr (_ *: _). by rewrite !tensmx_mul !mul_delta_mx !mul1mx mulmx1.
  - move=> c Hc. have Hneq : bb84_prep_index BasisX bit != bb84_prep_index BasisX c by rewrite bb84_prep_index_XX eq_sym.
    by rewrite -scalemxAr -scalemxAl tensmx_mul (mul_delta_mx_0 _ _ _ Hneq); rewrite tens0mx mul0mx scaler0. Qed.
Lemma bb84_x_diag_pair_den1 : bb84_x_diag_pair \is den1mx.
Proof. apply/den1mxP; split.
  - rewrite /bb84_x_diag_pair; apply: psdmx_sum => bit _. apply: psdmxZ; first by rewrite lec0R invr_ge0 ler0n. apply: psdmx_tens; first exact: delta_mx_psdmx. exact: (denmx_psd (den1mx_den (cd_rho_den1 dev BasisX bit))).
  - rewrite /bb84_x_diag_pair raddf_sum /=. under eq_bigr => bit _.
    { rewrite linearZ /= mxtrace_tens mxtrace_delta eqxx. have /den1mxP [_ /eqP ->] := cd_rho_den1 dev BasisX bit. rewrite mulr1 mulr1.
      over. } by rewrite sumr_const card_bool; apply/eqP; rewrite -rmorphMn /= -mulr_natr mulVf ?pnatr_eq0 // rmorph1. Qed.
End BB84XDiagPair.
Section BB84FlaggedPHpassBound.
Variable R : realType.
Notation chsType := (@chsType R).
Variables (P : @bb84_protocol R) (q : R) (dev : bb84_certified_device P q) (LE : finType) (HE : LE -> chsType).
Notation M := (bb84_round_limit P).
Notation LB := bb84_register_index.
Notation HB := (@bb84_register_space R P q dev).
Notation L := (bb84_label M LE LB).
Notation HL := (@bb84_label_space R M LE LB HE HB).
Notation V := (bb84_val M (bb84_n P) (bb84_l P) (cd_ir_bits dev) (cd_vseed_count dev) (cd_tag_count dev) (cd_paseed_count dev)).
Notation Eve := (@bb84_Eve R P LE).
Notation Sreg := (@bb84_S R P LE).
Notation Ereg := (@bb84_E R P LE).
Notation Zl := (@bb84_Zl R P LE).
Notation Fl := (@bb84_Fl R P LE).
Notation Ppub := (@bb84_Ppub R P LE).
Notation C := (@hermitian.C R).
Variable rhofull : forall (EA : @adversary R L HL V Eve) (xi : @cq_state R L HL (bb84_cvar M) V),
    'M[C]_(bb84_full_string_count P * dim ('H[HL]_Ereg) * bb84_full_string_count P).
Variable Hden1 : forall (EA : @adversary R L HL V Eve) (xi : @cq_state R L HL (bb84_cvar M) V), rhofull EA xi \is den1mx.
Hypotheses (Hcorr : @sigdet_correspondence R P q dev LE HE rhofull Hden1) (Hdm : @delayed_measurement_hmin_sigdet R P q dev LE HE).
Hypotheses (Hn : (0 < bb84_n P)%N) (Hk : (0 < bb84_k P)%N).
Variables (i0 : 'I_M) (kk : nat).
Hypotheses (Heps_c : bb84_eps_c P = (((2 ^ kk)%:R : R)^-1)%R) (Htag : cd_tag_count dev = (2 ^ kk)%N).
Fact bb84_flagged_PHpass_dist_bound (EA : @adversary R L HL V Eve) (xi : @cq_state R L HL (bb84_cvar M) V) (Hxi : cq_wf xi)
    (eps ebar : R) (eps_pos : 0 < eps) (eps_lt1 : eps < 1) (ebar_pos : 0 < ebar) (Hpass_case : eps ^+ 2 < bb84_source_pass_prob EA xi)
    (Heps'_lt1_h : eps / Num.sqrt (bb84_source_pass_prob EA xi) < 1) (Hlen_public : log2 (dim 'H[HL]_Zl)%:R <= (bb84_n P)%:R *
          (q - bb84_h_trunc (bb84_Qtol P + bb84_mu (bb84_n P) (bb84_k P) eps))
        + 2%:R * log2 (2%:R * ebar)
        - (bb84_leak_EC P + log2 (2%:R / bb84_eps_c P))) : dist_from_uniform (bb84_PHpass EA xi)
    <= eps / Num.sqrt (bb84_source_pass_prob EA xi) + ebar.
Proof. have Hxi_psd : forall s, xi s \is psdlf by case: Hxi. set p_source := bb84_source_pass_prob EA xi.
  have p_source_pos : 0 < p_source := lt_trans (exprn_gt0 2 eps_pos) Hpass_case. set eps' := eps / Num.sqrt p_source.
  have Hsqrt_pos : 0 < Num.sqrt p_source by rewrite sqrtr_gt0. have Heps'_nn : 0 <= eps' by rewrite divr_ge0 // ltW.
  have Heps'_lt1 : eps' < 1 by rewrite /eps'; exact: Heps'_lt1_h. pose Fbit := (bb84_signal_reg i0 : {set L}).
  have disFS : [disjoint Fbit & Sreg]. by rewrite /Fbit /bb84_signal_reg disjoint1X /bb84_S /bb84_reg /bb84_bridge_reg inE; rewrite /bb84_signal_label /bb84_bridge_label. have disFP : [disjoint Fbit & Ppub].
  by rewrite /Fbit /bb84_signal_reg disjoint1X /bb84_Ppub /bb84_reg /bb84_bridge_reg inE; rewrite /bb84_signal_label /bb84_bridge_label.
  have disFE : [disjoint Fbit & Ereg]. rewrite /Fbit /bb84_E disjointXU; apply/andP; split.
    - by rewrite /bb84_signal_reg disjoint1X /bb84_Eve /bb84_eve_reg inE; rewrite /bb84_signal_label.
    - by rewrite /bb84_signal_reg disjoint1X /bb84_Epub /bb84_reg /bb84_bridge_reg inE; rewrite /bb84_signal_label /bb84_bridge_label.
      have disFZl : [disjoint Fbit & Zl]. by rewrite /Fbit /bb84_signal_reg disjoint1X /bb84_Zl /bb84_reg /bb84_bridge_reg inE; rewrite /bb84_signal_label /bb84_bridge_label. have disFFl : [disjoint Fbit & Fl].
      by rewrite /Fbit /bb84_signal_reg disjoint1X /bb84_Fl /bb84_reg /bb84_bridge_reg inE; rewrite /bb84_signal_label /bb84_bridge_label.
      have Hdim2 : dim ('H[HL]_Fbit) = 2%N by exact: (bb84_signal_reg_dim HE HB i0). have Hcard2 : #|'Idx[HL]_Fbit| = 2%N by rewrite card_idx -dim_setten (bb84_signal_reg_dim HE HB i0). have Hgt1 : (1 < #|'Idx[HL]_Fbit|)%N by rewrite Hcard2.
      have Hex : exists xy : 'Idx[HL]_Fbit * 'Idx[HL]_Fbit, xy.1 != xy.2 by move: Hgt1 => /card_gt1P [a [b [_ _ ab]]]; exists (a, b).
      have [[acc rej] /= Hnr] := cid Hex. pose A := bb84_pass_block_readout_pass_prog EA xi; pose B := bb84_vf_block_readout_pass_prog EA xi. pose pub := @bb84_public_leakage_readout_pass_prog_flagged R P q dev LE HE EA xi Hxi_psd Fbit disFS disFE disFP acc rej Hnr Hdim2 kk Heps_c Htag A B (@bb84_pass_block_readout_pass_prog_psd R P q dev LE HE EA xi Hxi_psd) (@bb84_vf_block_readout_pass_prog_psd R P q dev LE HE EA xi Hxi_psd) (@bb84_pass_vf_block_sum R P q dev LE HE EA xi) (@bb84_pass_block_readout_pass_prog_classical R P q dev LE HE EA xi) (@bb84_vf_block_readout_pass_prog_classical R P q dev LE HE EA xi) (@bb84_pass_block_readout_pass_prog_pa_cq R P q dev LE HE EA xi) (@bb84_vf_block_readout_pass_prog_pa_cq R P q dev LE HE EA xi).
      have HstateE : bb84_public_state pub = castlf (@bb84_flag_public_cast_eq R P LE Fbit, @bb84_flag_public_cast_eq R P LE Fbit) (bb84_flag_pair acc rej A B).
  { reflexivity. } have Hpe_re : @complex.Re R (\Tr (bb84_pe_pass_leakage_public_readout_state EA xi)) = p_source.
  { rewrite bb84_pe_pass_leakage_public_readout_trace_key_public. exact: bb84_pe_pass_key_public_readout_traceRe. }
have Hpe_pos : 0 < @complex.Re R (\Tr (bb84_pe_pass_leakage_public_readout_state EA xi)) by rewrite Hpe_re.
    have disFb_PSE : [disjoint Fbit & (Ppub :|: (Sreg :|: Ereg))] by rewrite disjointXU disFP disjointXU disFS disFE; [].
    have Hstate_tr1 : @complex.Re R (\Tr (bb84_public_state pub)) = 1.
  { rewrite HstateE castlf_trlfE. rewrite (@bb84_flag_pair_trace R L HL Fbit (Ppub :|: (Sreg :|: Ereg)) disFb_PSE acc rej A B).
    rewrite -raddfD /A /B (bb84_pass_vf_block_sum EA xi). exact: rhoPSE_readout_pass_prog_trace1. } set eps'v := eps / Num.sqrt p_source.
    have Heps_state : 0 <= eps'v < Num.sqrt (@complex.Re R (\Tr (bb84_public_state pub))).
  { by rewrite Hstate_tr1 sqrtr1 -/eps'v Heps'_nn Heps'_lt1. } have Hbase_sig : (bb84_n P)%:R * (q - bb84_h_trunc (bb84_Qtol P + bb84_mu (bb84_n P) (bb84_k P) eps)) <= smooth_hmin Ereg eps'v (rhoXE_readout_pass_prog EA xi).
  { apply: (@bb84_pe_pass_hmin_sigdet R P q dev LE HE rhofull Hden1 Hcorr Hdm Hn Hk EA (@bb84_x_diag_pair R P q dev) xi eps Hxi (@bb84_x_diag_pair_den1 R P q dev) (@bb84_x_diag_pair_ptr_ok R P q dev) (@bb84_x_diag_pair_x_branch_ok R P q dev) p_source_pos eps_pos eps_lt1 Heps'_nn). rewrite (_ : @complex.Re R (\tr (rhoSrc_SEB_sigdet EA (@bb84_x_diag_pair R P q dev) xi)) = 1).
    - by rewrite sqrtr1.
    - have Hd := @rhoSrc_SEB_sigdet_den1mx R P q dev LE HE EA (@bb84_x_diag_pair R P q dev) xi (@bb84_x_diag_pair_den1 R P q dev) (@bb84_x_diag_pair_ptr_ok R P q dev) (@bb84_x_diag_pair_x_branch_ok R P q dev) p_source_pos Hxi_psd.
      by move/den1mxP: Hd => [_ /eqP ->]; rewrite re_realid. } have dSFb : [disjoint Sreg & Fbit] by rewrite disjoint_sym disFS.
      have dEF : [disjoint Ereg & Fl] by move: (@bb84_disEpubF R P LE); rewrite disjointUX => /andP[].
      have dPF : [disjoint Ppub & Fl] by move: (@bb84_disEpubF R P LE); rewrite disjointUX => /andP[_].
      have dEZl : [disjoint Ereg & Zl] by move: (@bb84_disEpubZl R P LE); rewrite disjointUX => /andP[].
      have dPZl : [disjoint Ppub & Zl] by move: (@bb84_disEpubZl R P LE); rewrite disjointUX => /andP[_].
      have dZlFl : [disjoint Zl & Fl] by rewrite disjoint_sym bb84_disFZl. have dZlE : [disjoint Zl & Ereg] by rewrite disjoint_sym dEZl.
      have dZlP : [disjoint Zl & Ppub] by rewrite disjoint_sym dPZl. have dZlFb : [disjoint Zl & Fbit] by rewrite disjoint_sym disFZl.
      have disSEpub' : [disjoint Sreg & Ereg :|: (Ppub :|: Fbit)].
  { rewrite disjointXU; apply/andP; split; first exact: bb84_disSE. rewrite disjointXU; apply/andP; split; [exact: bb84_disSP | exact: dSFb]. } have disEpubF' : [disjoint Ereg :|: (Ppub :|: Fbit) & Fl].
  { rewrite disjointUX; apply/andP; split; first exact: dEF. rewrite disjointUX; apply/andP; split; [exact: dPF | exact: disFFl]. }
have disEpubZl' : [disjoint Ereg :|: (Ppub :|: Fbit) & Zl].
  { rewrite disjointUX; apply/andP; split; first exact: dEZl. rewrite disjointUX; apply/andP; split; [exact: dPZl | exact: disFZl]. }
have disZlFEpub' : [disjoint Zl & Fl :|: (Ereg :|: (Ppub :|: Fbit))].
  { rewrite disjointXU; apply/andP; split; first exact: dZlFl. rewrite disjointXU; apply/andP; split; first exact: dZlE. rewrite disjointXU; apply/andP; split; [exact: dZlP | exact: dZlFb]. } have Hdelta := @bb84_delta_from_public_leakage R L HL Sreg Ereg Fl Zl (@bb84_disSE R P LE) (@bb84_disSF R P LE) (@bb84_disSZl R P LE) (@bb84_disFZl R P LE) (Ppub :|: Fbit) (rhoXE_readout_pass_prog EA xi) (bb84_leak_EC P + log2 (2%:R / bb84_eps_c P)) eps'v ebar ((bb84_n P)%:R * (q - bb84_h_trunc (bb84_Qtol P + bb84_mu (bb84_n P) (bb84_k P) eps))) pub disSEpub' disEpubF' disEpubZl' disZlFEpub' (@bb84_pa_hash_index R P q dev LE HE) Heps_state Hbase_sig Hlen_public (@bb84_pa_hash_index_two_univ R P q dev LE HE) ebar_pos. rewrite /delta_secret HstateE castlf_comp /A /B in Hdelta.
    have Eoutcast : Fbit :|: (Zl :|: (Fl :|: (Ereg :|: Ppub))) = Zl :|: (Fl :|: (Ereg :|: (Ppub :|: Fbit))).
  { by rewrite (finset.setUCA Fbit Zl (Fl :|: (Ereg :|: Ppub))) (finset.setUCA Fbit Fl (Ereg :|: Ppub)) (finset.setUCA Fbit Ereg Ppub) (finset.setUC Fbit Ppub). } rewrite (@bb84_flagged_post_hash_recognize R P q dev LE HE EA xi Fbit disFS disFE disFP disFZl disFFl acc rej disSEpub' _ Eoutcast) in Hdelta. set Omega := bb84_flag_pair acc rej (bb84_PHpass EA xi) (bb84_PHvf EA xi).
    have HPHpass_psd : bb84_PHpass EA xi \is psdlf.
  { rewrite /bb84_PHpass. apply: (@post_hash_psdlf R L HL Sreg (Ereg :|: Ppub) Fl Zl (@bb84_disSEpub R P LE) (@bb84_disSF R P LE) (@bb84_disSZl R P LE) (@bb84_disEpubF R P LE) (@bb84_disEpubZl R P LE) (@bb84_disFZl R P LE) (@bb84_pa_hash_index R P q dev LE HE)).
    rewrite castlf_psdlfE. exact: (@bb84_pass_block_readout_pass_prog_psd R P q dev LE HE EA xi Hxi_psd). }
have HPHvf_psd : bb84_PHvf EA xi \is psdlf.
  { rewrite /bb84_PHvf. apply: (@post_hash_psdlf R L HL Sreg (Ereg :|: Ppub) Fl Zl (@bb84_disSEpub R P LE) (@bb84_disSF R P LE) (@bb84_disSZl R P LE) (@bb84_disEpubF R P LE) (@bb84_disEpubZl R P LE) (@bb84_disFZl R P LE) (@bb84_pa_hash_index R P q dev LE HE)).
    rewrite castlf_psdlfE. exact: (@bb84_vf_block_readout_pass_prog_psd R P q dev LE HE EA xi Hxi_psd). }
have disF_ZFEP : [disjoint Fbit & (Zl :|: (Fl :|: (Ereg :|: Ppub)))].
  { rewrite disjointXU disFZl disjointXU disFFl disjointXU disFE disFP. by []. } have HOmega_psd : Omega \is psdlf by apply: (@bb84_flag_pair_psd R L HL Fbit _ disF_ZFEP acc rej); [exact: HPHpass_psd | exact: HPHvf_psd].
    have dZl_FEP : [disjoint Zl & (Fl :|: (Ereg :|: Ppub))] by rewrite disjointXU dZlFl disjointXU dZlE dZlP; [].
    have disF_FEP : [disjoint Fbit & (Fl :|: (Ereg :|: Ppub))] by rewrite disjointXU disFFl disjointXU disFE disFP; [].
    have Hdag := @bb84_dagger_dist_le R L HL Fbit Zl (Fl :|: (Ereg :|: Ppub)) disFZl disF_FEP dZl_FEP acc rej Hnr Hcard2 Omega HOmega_psd.
    rewrite (bb84_flag_pair_cq_acc _ Hnr) in Hdag. have eqB : Fbit :|: (Fl :|: (Ereg :|: Ppub)) = Fl :|: (Ereg :|: (Ppub :|: Fbit)).
  { by rewrite (finset.setUCA Fbit Fl (Ereg :|: Ppub)) (finset.setUCA Fbit Ereg Ppub) (finset.setUC Fbit Ppub). }
pose cAB := congr1 (finset.setU Zl) eqB. have Hside : dist_from_uniform (castlf (Eoutcast, Eoutcast) Omega) = dist_from_uniform (castlf (esym (finset.setUCA Zl Fbit (Fl :|: (Ereg :|: Ppub))), esym (finset.setUCA Zl Fbit (Fl :|: (Ereg :|: Ppub)))) Omega).
  { have -> : castlf (Eoutcast, Eoutcast) Omega = castlf (cAB, cAB) (castlf (esym (finset.setUCA Zl Fbit (Fl :|: (Ereg :|: Ppub))), esym (finset.setUCA Zl Fbit (Fl :|: (Ereg :|: Ppub)))) Omega). { rewrite castlf_comp. exact: castlf_irrel. }
exact: (@dist_from_uniform_side_cast R L HL Zl (Fbit :|: (Fl :|: (Ereg :|: Ppub))) (Fl :|: (Ereg :|: (Ppub :|: Fbit))) eqB cAB (castlf (esym (finset.setUCA Zl Fbit (Fl :|: (Ereg :|: Ppub))), esym (finset.setUCA Zl Fbit (Fl :|: (Ereg :|: Ppub)))) Omega)). }
by apply: le_trans Hdag _; rewrite -Hside; exact: Hdelta. Qed.
Fact bb84_pass_leakage_public_readout_traceRe (EA : @adversary R L HL V Eve) (xi : @cq_state R L HL (bb84_cvar M) V) :
  @complex.Re R (\Tr (@bb84_pass_leakage_public_readout_state R P q dev LE HE EA xi)) =
  @bb84_key_public_source_pass_prob R P q dev LE HE EA xi.
Proof. have bb84_pass_leakage_public_readout_trace_key_public : forall (EA : @adversary R L HL V Eve) (xi : @cq_state R L HL (bb84_cvar M)
  V), \Tr (@bb84_pass_leakage_public_readout_state R P q dev LE HE EA xi) = \Tr (@bb84_pass_key_public_readout_state R P q dev LE HE EA xi).
{ clear xi EA; move=> EA xi. rewrite /bb84_pass_leakage_public_readout_state /bb84_pass_key_public_readout_state /bb84_pass_history_public_readout_state. rewrite [in LHS]linear_sum /=. rewrite [in RHS]linear_sum /=. apply: eq_bigr => s _.
  rewrite [in LHS]linear_sum /=. rewrite [in RHS]linear_sum /=. apply: eq_bigr => h _. rewrite [in LHS]linearZ /=. rewrite [in RHS]linearZ /=.
  by rewrite !replaceso_trlf_den1 ?bb84_leakage_public_register_state_den1lf ?bb84_key_public_register_state_den1lf. }
have bb84_pass_key_public_readout_trace_source : forall (EA : @adversary R L HL V Eve) (xi : @cq_state R L HL (bb84_cvar M) V), \Tr (@bb84_pass_key_public_readout_state R P q dev LE HE EA xi) = \Tr (@bb84_pass_key_public_source_state R P q dev LE HE EA xi).
{ clear xi EA; move=> EA xi. have /cptpP [_ /tpmapP Htp] := @ptraceso_qc R L HL [set x : L | if x is inr (inl _) then true else false] (setTfor L). rewrite -(Htp (@bb84_pass_key_public_readout_state R P q dev LE HE EA xi)) -(Htp (@bb84_pass_key_public_source_state R P q dev LE HE EA xi)). by rewrite bb84_pass_key_public_readout_source_ptraceso_all_sources. }
rewrite /bb84_key_public_source_pass_prob; congr (@complex.Re R _). by rewrite bb84_pass_leakage_public_readout_trace_key_public; exact: bb84_pass_key_public_readout_trace_source. Qed.
Fact bb84_flagged_eps_secret (EA : @adversary R L HL V Eve) (xi_init : @cq_state R L HL (bb84_cvar M) V) (Hxi : cq_wf xi_init)
    (eps_s : R) (eps_s_pos : 0 < eps_s) (eps_s_le1 : eps_s <= 1) (Hlen_sup : (bb84_l P)%:R <= sup (fun m : R => exists eps ebar : R,
        0 < eps /\ eps < 1 /\ 0 < ebar /\ eps + ebar <= eps_s /\ m = ((floor (bb84_key_length_ub (bb84_n P) (bb84_k P) q
          (bb84_Qtol P) eps ebar (bb84_leak_EC P) (bb84_eps_c P)))%:~R : R))) : @eps_secret R L HL Zl (Fl :|: (Ereg :|: Ppub))
    (rhoZFEpub_readout_prog EA xi_init) eps_s (@run_abort_prob R L HL (bb84_cvar M) V (@BVabort M) bb84_bool_val
       (bb84_eval_scheme_state EA xi_init)).
Proof. have Hxi_psd : forall s, xi_init s \is psdlf by case: Hxi. set xi_out := bb84_eval_scheme_state EA xi_init;
  set p_abort := @run_abort_prob R L HL (bb84_cvar M) V (@BVabort M) bb84_bool_val xi_out. set p_pass := @run_pass_prob R L HL (bb84_cvar M) V (@BVabort M) bb84_bool_val xi_out. have Hpart : p_abort + p_pass = 1 by rewrite /p_abort /p_pass /xi_out; exact: bb84_eval_scheme_abort_pass_partition. have Hay : forall i, @BVa M i != @BVy M i by move=> i; rewrite /BVa /BVy.
  have HPa : forall i, @BVP M != @BVa M i by move=> i; rewrite /BVP /BVa. have HPy : forall i, @BVP M != @BVy M i by move=> i; rewrite /BVP /BVy. have HPb : forall i, @BVP M != @BVb M i by move=> i; rewrite /BVP /BVb.
  have HPy' : forall i, @BVP M != @BVy' M i by move=> i; rewrite /BVP /BVy'. have HPd : forall i, @BVP M != @BVd M i by move=> i; rewrite /BVP /BVd. have HPX : @BVP M != @BVX M by rewrite /BVP /BVX /=; apply: bb84_cvar_inr_neq; rewrite -val_eqE /= !inordK.
  have HPZ : @BVP M != @BVZ M by rewrite /BVP /BVZ /=; apply: bb84_cvar_inr_neq; rewrite -val_eqE /= !inordK.
  have HPabort : @BVP M != @BVabort M by rewrite eq_sym bb84_abort_neq_P. have Hround_wf := @bb84_round_cmd_wf R P q dev LE HE; have Hpe_wf := @bb84_paramest_cmd_wf R P q dev LE HE. have Hec_wf := @bb84_errcorr_cmd_wf R P q dev LE HE; have Hpa_wf := @bb84_privamp_cmd_wf R P q dev LE HE. have Hout_psd : forall s, xi_out s \is psdlf.
  { rewrite /xi_out. exact: (bb84_eval_scheme_state_psd EA Hround_wf Hpe_wf Hec_wf Hpa_wf Hxi_psd). }
have p_source_nonneg : 0 <= bb84_source_pass_prob EA xi_init.
  { exact: (@bb84_source_pass_prob_nonneg R P q dev LE HE bb84_register_index HB EA xi_init Hay HPa HPy HPb HPy' HPd HPX HPZ HPabort Hround_wf Hpe_wf Hec_wf Hpa_wf Hxi_psd). } have p_source_le1_all : bb84_source_pass_prob EA xi_init <= 1.
  { exact: (@bb84_source_pass_prob_le1 R P q dev LE HE bb84_register_index HB EA xi_init Hay HPa HPy HPb HPy' HPd HPX HPZ HPabort Hround_wf Hpe_wf Hec_wf Hpa_wf Hxi). } have HnonabortE : 1 - p_abort = p_pass by move: Hpart => <-; rewrite addrAC subrr add0r.
    have Habort_nn : 0 <= p_abort by rewrite /p_abort /run_abort_prob; apply: run_event_prob_nonneg; exact: Hout_psd.
    have Hpass_nn : 0 <= p_pass by rewrite /p_pass /run_pass_prob; apply: run_event_prob_nonneg; exact: Hout_psd.
    have Hpass_le1 : p_pass <= 1 by rewrite -Hpart lerDr. have Habort_le1 : p_abort <= 1 by rewrite -Hpart lerDl.
    have Hpass_le : bb84_pass_prob_le p_abort (bb84_source_pass_prob EA xi_init).
  { split=> //; split=> //; rewrite HnonabortE /p_pass /xi_out. exact: (bb84_run_pass_prob_le_source EA Hay HPa HPy HPb HPy' HPd HPX HPZ HPabort Hxi_psd). } have Hlen_int : (bb84_l P)%:R \is a int_num := @intr_nat R ((bb84_l P)%:R) (@natr_nat R (bb84_l P)).
    have [eps [ebar [eps_pos [eps_lt1 [ebar_pos [Hbudget Hlen]]]]]] := @bb84_key_length_sup_witness R P q eps_s (bb84_l P)%:R eps_s_pos eps_s_le1 Hlen_int Hlen_sup. set p_source := bb84_source_pass_prob EA xi_init. have eps_nn : 0 <= eps := ltW eps_pos.
    have ebar_nn : 0 <= ebar := ltW ebar_pos. case: (ltrP (eps ^+ 2) p_source) => Hpass_case.
  - case: (ltrP 0 (1 - p_abort)) => Hfull_case; last first.
    { exists 1; split.
      - rewrite /delta_secret. have Hdist := dist_uniform_le_trace (@bb84_disZl_FEpub R P LE) (@rhoZFEpub_readout_prog_psd R P q dev LE HE EA xi_init Hxi_psd). by have Htr := @rhoZFEpub_readout_prog_tr_le1 R P q dev LE HE EA xi_init Hxi_psd; exact: (le_trans Hdist Htr).
      - by rewrite mulr1; exact: (le_trans Hfull_case (ltW eps_s_pos)). } have p_source_pos : 0 < p_source := lt_trans (exprn_gt0 2 eps_pos) Hpass_case. have p_source_le1 : p_source <= 1 := p_source_le1_all. have Hsqrt_p_source_pos : 0 < Num.sqrt p_source by rewrite sqrtr_gt0. set eps' := eps / Num.sqrt p_source. have Heps'_nn : 0 <= eps' by rewrite divr_ge0 // ltW. have Heps'_lt1 : eps' < 1.
    { rewrite /eps' ltr_pdivrMr // mul1r; have Hdomain : bb84_entropy_domain eps p_source.
      { split=> //; have Heps_sqrt : Num.sqrt (eps ^+ 2) = eps by rewrite sqrtr_sqr ger0_norm // ltW. rewrite -Heps_sqrt ltr_sqrt; first exact: Hpass_case. exact: lt_trans (exprn_gt0 2 eps_pos) Hpass_case. } exact: bb84_eps_lt_sqrt_pass Hdomain. }
have Hlen_real : (bb84_l P)%:R <= bb84_key_length_ub (bb84_n P) (bb84_k P) q (bb84_Qtol P) eps ebar (bb84_leak_EC P) (bb84_eps_c P).
    { exact: (le_trans Hlen (@Rfloor_le R _)). } have Hlog2_dim : @log2 R ((dim 'H[HL]_Zl)%:R : R) = ((bb84_l P)%:R : R) by rewrite bb84_dim_Zl; exact: (@log2_pow2_nat R (bb84_l P)). have H2ebar_pos : 0 < 2%:R * ebar :> R by rewrite mulr_gt0 // ltr0n.
      have Hlog2_inv_ebar : log2 ((2%:R * ebar)^-1) = - log2 (2%:R * ebar) by rewrite /log2 lnV // mulNr.
      have Hlen_public : log2 (dim 'H[HL]_Zl)%:R <= (bb84_n P)%:R * (q - bb84_h_trunc (bb84_Qtol P + bb84_mu (bb84_n P) (bb84_k P) eps))
        + 2%:R * log2 (2%:R * ebar)
        - (bb84_leak_EC P + log2 (2%:R / bb84_eps_c P)).
    { rewrite Hlog2_dim. have Hlen_rewr : (bb84_l P)%:R <= (bb84_n P)%:R * (q - bb84_h_trunc (bb84_Qtol P + bb84_mu (bb84_n P) (bb84_k P) eps))
        + 2%:R * log2 (2%:R * ebar)
        - bb84_leak_EC P - log2 (2%:R / bb84_eps_c P).
      { move: Hlen_real. by rewrite /bb84_key_length_ub Hlog2_inv_ebar mulrN opprK. } by apply: le_trans Hlen_rewr _; rewrite opprD addrA. }
have HdistPH := @bb84_flagged_PHpass_dist_bound EA xi_init Hxi eps ebar eps_pos eps_lt1 ebar_pos Hpass_case Heps'_lt1 Hlen_public.
        set pass := @complex.Re R (\Tr (@bb84_pass_leakage_public_readout_state R P q dev LE HE EA xi_init)).
        set pe := @complex.Re R (\Tr (@bb84_pe_pass_leakage_public_readout_state R P q dev LE HE EA xi_init)). have Hpe_re : pe = p_source.
    { by rewrite /pe bb84_pe_pass_leakage_public_readout_trace_key_public; exact: bb84_pe_pass_key_public_readout_traceRe. }
have Hpe_neq : pe != 0 by rewrite Hpe_re lt0r_neq0. have HkappaE := @bb84_rhoZFEpub_kappa_PHpass R P q dev LE HE EA xi_init Hpe_neq.
      have Hpass_eq : pass = 1 - p_abort.
    { rewrite /pass bb84_pass_leakage_public_readout_traceRe. rewrite (bb84_key_public_source_pass_prob_runE EA xi_init Hay HPa HPy HPb HPy' HPd HPX HPZ HPabort). by rewrite /bb84_run_pass_prob -/xi_out -/p_pass HnonabortE. } have HPHpass_psd : @bb84_PHpass R P q dev LE HE EA xi_init \is psdlf.
    { rewrite /bb84_PHpass. apply: (@post_hash_psdlf R L HL Sreg (Ereg :|: Ppub) Fl Zl (@bb84_disSEpub R P LE) (@bb84_disSF R P LE) (@bb84_disSZl R P LE) (@bb84_disEpubF R P LE) (@bb84_disEpubZl R P LE) (@bb84_disFZl R P LE) (@bb84_pa_hash_index R P q dev LE HE)).
      by rewrite castlf_psdlfE; exact: (@bb84_pass_block_readout_pass_prog_psd R P q dev LE HE EA xi_init Hxi_psd). }
have Hkappa_nn : 0 <= pass^-1 * pe. { rewrite Hpass_eq Hpe_re. apply: mulr_ge0. - by rewrite invr_ge0 ltW.
      - exact: ltW p_source_pos. } exists (pass^-1 * pe * (eps' + ebar)); split.
    + rewrite /delta_secret HkappaE. apply: le_trans (@dist_uniform_scale_ub R L HL Zl (Fl :|: (Ereg :|: Ppub)) (@bb84_disZl_FEpub R P LE) (@bb84_PHpass R P q dev LE HE EA xi_init) (pass^-1 * pe) HPHpass_psd Hkappa_nn) _. by apply: (ler_wpM2l Hkappa_nn); exact: HdistPH.
    + rewrite Hpass_eq Hpe_re. have Hne : (1 - p_abort) != 0 by rewrite lt0r_neq0. have Hsqrt_ne : Num.sqrt p_source != 0 by rewrite lt0r_neq0. rewrite mulrA mulrA (mulfV Hne) mul1r mulrDr. have Hpe' : p_source * eps' = Num.sqrt p_source * eps.
      { rewrite /eps' -{1}(sqr_sqrtr (ltW p_source_pos)) expr2 -!mulrA. congr (_ * _). by rewrite mulrCA divff // mulr1. } rewrite Hpe'.
        have Hsqrt_le1 : Num.sqrt p_source <= 1 by rewrite -sqrtr1 ler_wsqrtr. apply: le_trans (_ : eps + ebar <= eps_s); last exact: Hbudget. apply: lerD.
      * by rewrite -{2}(mul1r eps) ler_wpM2r.
      * by rewrite -{2}(mul1r ebar) ler_wpM2r.
  - have Hnonabort_le_eps_s : 1 - p_abort <= eps_s by exact: (bb84_low_pass_nonabort_le eps_pos ebar_pos Hbudget Hpass_le Hpass_case).
    exists 1; split.
    + rewrite /delta_secret. have Hdist := dist_uniform_le_trace (@bb84_disZl_FEpub R P LE) (@rhoZFEpub_readout_prog_psd R P q dev LE HE EA xi_init Hxi_psd). by have Htr := @rhoZFEpub_readout_prog_tr_le1 R P q dev LE HE EA xi_init Hxi_psd; exact: (le_trans Hdist Htr).
    + by rewrite mulr1. Qed.
Fact bb84_flagged_dist_bound_flag_in_view (EA : @adversary R L HL V Eve) (xi : @cq_state R L HL (bb84_cvar M) V) (Hxi : cq_wf xi)
    (Fbit : {set L}) (disFS : [disjoint Fbit & Sreg]) (disFE : [disjoint Fbit & Ereg])
    (disFP : [disjoint Fbit & Ppub]) (disFZl : [disjoint Fbit & Zl]) (disFFl : [disjoint Fbit & Fl]) (Hdim2 : dim ('H[HL]_Fbit) = 2%N)
    (acc rej : 'Idx[HL]_Fbit) (Hnr : acc != rej) (eps ebar : R) (eps_pos : 0 < eps) (eps_lt1 : eps < 1) (ebar_pos : 0 < ebar)
    (Hpass_case : eps ^+ 2 < bb84_source_pass_prob EA xi) (Heps'_lt1_h : eps / Num.sqrt (bb84_source_pass_prob EA xi) < 1) (Hlen_public :
      log2 (dim 'H[HL]_Zl)%:R <= (bb84_n P)%:R * (q - bb84_h_trunc (bb84_Qtol P + bb84_mu (bb84_n P) (bb84_k P) eps))
        + 2%:R * log2 (2%:R * ebar)
        - (bb84_leak_EC P + log2 (2%:R / bb84_eps_c P))) : dist_from_uniform (castlf (esym (finset.setUCA Zl Fbit (Fl :|: (Ereg :|: Ppub))),
             esym (finset.setUCA Zl Fbit (Fl :|: (Ereg :|: Ppub)))) (bb84_flag_pair acc rej (bb84_PHpass EA xi) (bb84_PHvf EA xi)))
    <= eps / Num.sqrt (bb84_source_pass_prob EA xi) + ebar.
Proof. have Hxi_psd : forall s, xi s \is psdlf by case: Hxi. set p_source := bb84_source_pass_prob EA xi.
  have p_source_pos : 0 < p_source := lt_trans (exprn_gt0 2 eps_pos) Hpass_case. set eps' := eps / Num.sqrt p_source.
  have Hsqrt_pos : 0 < Num.sqrt p_source by rewrite sqrtr_gt0. have Heps'_nn : 0 <= eps' by rewrite divr_ge0 // ltW.
  have Heps'_lt1 : eps' < 1 by rewrite /eps'; exact: Heps'_lt1_h. pose A := bb84_pass_block_readout_pass_prog EA xi; pose B := bb84_vf_block_readout_pass_prog EA xi. pose pub := @bb84_public_leakage_readout_pass_prog_flagged R P q dev LE HE EA xi Hxi_psd Fbit disFS disFE disFP acc rej Hnr Hdim2 kk Heps_c Htag A B (@bb84_pass_block_readout_pass_prog_psd R P q dev LE HE EA xi Hxi_psd) (@bb84_vf_block_readout_pass_prog_psd R P q dev LE HE EA xi Hxi_psd) (@bb84_pass_vf_block_sum R P q dev LE HE EA xi) (@bb84_pass_block_readout_pass_prog_classical R P q dev LE HE EA xi) (@bb84_vf_block_readout_pass_prog_classical R P q dev LE HE EA xi) (@bb84_pass_block_readout_pass_prog_pa_cq R P q dev LE HE EA xi) (@bb84_vf_block_readout_pass_prog_pa_cq R P q dev LE HE EA xi).
  have HstateE : bb84_public_state pub = castlf (@bb84_flag_public_cast_eq R P LE Fbit, @bb84_flag_public_cast_eq R P LE Fbit) (bb84_flag_pair acc rej A B).
  { reflexivity. } have Hpe_re : @complex.Re R (\Tr (bb84_pe_pass_leakage_public_readout_state EA xi)) = p_source.
  { rewrite bb84_pe_pass_leakage_public_readout_trace_key_public. exact: bb84_pe_pass_key_public_readout_traceRe. }
have Hpe_pos : 0 < @complex.Re R (\Tr (bb84_pe_pass_leakage_public_readout_state EA xi)) by rewrite Hpe_re.
    have disFb_PSE : [disjoint Fbit & (Ppub :|: (Sreg :|: Ereg))] by rewrite disjointXU disFP disjointXU disFS disFE; [].
    have Hstate_tr1 : @complex.Re R (\Tr (bb84_public_state pub)) = 1.
  { rewrite HstateE castlf_trlfE. rewrite (@bb84_flag_pair_trace R L HL Fbit (Ppub :|: (Sreg :|: Ereg)) disFb_PSE acc rej A B).
    rewrite -raddfD /A /B (bb84_pass_vf_block_sum EA xi). exact: rhoPSE_readout_pass_prog_trace1. } set eps'v := eps / Num.sqrt p_source.
    have Heps_state : 0 <= eps'v < Num.sqrt (@complex.Re R (\Tr (bb84_public_state pub))).
  { by rewrite Hstate_tr1 sqrtr1 -/eps'v Heps'_nn Heps'_lt1. } have Hbase_sig : (bb84_n P)%:R * (q - bb84_h_trunc (bb84_Qtol P + bb84_mu (bb84_n P) (bb84_k P) eps)) <= smooth_hmin Ereg eps'v (rhoXE_readout_pass_prog EA xi).
  { apply: (@bb84_pe_pass_hmin_sigdet R P q dev LE HE rhofull Hden1 Hcorr Hdm Hn Hk EA (@bb84_x_diag_pair R P q dev) xi eps Hxi (@bb84_x_diag_pair_den1 R P q dev) (@bb84_x_diag_pair_ptr_ok R P q dev) (@bb84_x_diag_pair_x_branch_ok R P q dev) p_source_pos eps_pos eps_lt1 Heps'_nn). rewrite (_ : @complex.Re R (\tr (rhoSrc_SEB_sigdet EA (@bb84_x_diag_pair R P q dev) xi)) = 1).
    - by rewrite sqrtr1.
    - have Hd := @rhoSrc_SEB_sigdet_den1mx R P q dev LE HE EA (@bb84_x_diag_pair R P q dev) xi (@bb84_x_diag_pair_den1 R P q dev) (@bb84_x_diag_pair_ptr_ok R P q dev) (@bb84_x_diag_pair_x_branch_ok R P q dev) p_source_pos Hxi_psd.
      by move/den1mxP: Hd => [_ /eqP ->]; rewrite re_realid. } have dSFb : [disjoint Sreg & Fbit] by rewrite disjoint_sym disFS.
      have dEF : [disjoint Ereg & Fl] by move: (@bb84_disEpubF R P LE); rewrite disjointUX => /andP[].
      have dPF : [disjoint Ppub & Fl] by move: (@bb84_disEpubF R P LE); rewrite disjointUX => /andP[_].
      have dEZl : [disjoint Ereg & Zl] by move: (@bb84_disEpubZl R P LE); rewrite disjointUX => /andP[].
      have dPZl : [disjoint Ppub & Zl] by move: (@bb84_disEpubZl R P LE); rewrite disjointUX => /andP[_].
      have dZlFl : [disjoint Zl & Fl] by rewrite disjoint_sym bb84_disFZl. have dZlE : [disjoint Zl & Ereg] by rewrite disjoint_sym dEZl.
      have dZlP : [disjoint Zl & Ppub] by rewrite disjoint_sym dPZl. have dZlFb : [disjoint Zl & Fbit] by rewrite disjoint_sym disFZl.
      have disSEpub' : [disjoint Sreg & Ereg :|: (Ppub :|: Fbit)].
  { rewrite disjointXU; apply/andP; split; first exact: bb84_disSE. rewrite disjointXU; apply/andP; split; [exact: bb84_disSP | exact: dSFb]. } have disEpubF' : [disjoint Ereg :|: (Ppub :|: Fbit) & Fl].
  { rewrite disjointUX; apply/andP; split; first exact: dEF. rewrite disjointUX; apply/andP; split; [exact: dPF | exact: disFFl]. }
have disEpubZl' : [disjoint Ereg :|: (Ppub :|: Fbit) & Zl].
  { rewrite disjointUX; apply/andP; split; first exact: dEZl. rewrite disjointUX; apply/andP; split; [exact: dPZl | exact: disFZl]. }
have disZlFEpub' : [disjoint Zl & Fl :|: (Ereg :|: (Ppub :|: Fbit))].
  { rewrite disjointXU; apply/andP; split; first exact: dZlFl. rewrite disjointXU; apply/andP; split; first exact: dZlE. rewrite disjointXU; apply/andP; split; [exact: dZlP | exact: dZlFb]. } have Hdelta := @bb84_delta_from_public_leakage R L HL Sreg Ereg Fl Zl (@bb84_disSE R P LE) (@bb84_disSF R P LE) (@bb84_disSZl R P LE) (@bb84_disFZl R P LE) (Ppub :|: Fbit) (rhoXE_readout_pass_prog EA xi) (bb84_leak_EC P + log2 (2%:R / bb84_eps_c P)) eps'v ebar ((bb84_n P)%:R * (q - bb84_h_trunc (bb84_Qtol P + bb84_mu (bb84_n P) (bb84_k P) eps))) pub disSEpub' disEpubF' disEpubZl' disZlFEpub' (@bb84_pa_hash_index R P q dev LE HE) Heps_state Hbase_sig Hlen_public (@bb84_pa_hash_index_two_univ R P q dev LE HE) ebar_pos. rewrite /delta_secret HstateE castlf_comp /A /B in Hdelta.
    have Eoutcast : Fbit :|: (Zl :|: (Fl :|: (Ereg :|: Ppub))) = Zl :|: (Fl :|: (Ereg :|: (Ppub :|: Fbit))).
  { by rewrite (finset.setUCA Fbit Zl (Fl :|: (Ereg :|: Ppub))) (finset.setUCA Fbit Fl (Ereg :|: Ppub)) (finset.setUCA Fbit Ereg Ppub) (finset.setUC Fbit Ppub). } rewrite (@bb84_flagged_post_hash_recognize R P q dev LE HE EA xi Fbit disFS disFE disFP disFZl disFFl acc rej disSEpub' _ Eoutcast) in Hdelta. set Omega := bb84_flag_pair acc rej (bb84_PHpass EA xi) (bb84_PHvf EA xi).
    have eqB : Fbit :|: (Fl :|: (Ereg :|: Ppub)) = Fl :|: (Ereg :|: (Ppub :|: Fbit)).
  { by rewrite (finset.setUCA Fbit Fl (Ereg :|: Ppub)) (finset.setUCA Fbit Ereg Ppub) (finset.setUC Fbit Ppub). }
pose cAB := congr1 (finset.setU Zl) eqB. have Hside : dist_from_uniform (castlf (Eoutcast, Eoutcast) Omega) = dist_from_uniform (castlf (esym (finset.setUCA Zl Fbit (Fl :|: (Ereg :|: Ppub))), esym (finset.setUCA Zl Fbit (Fl :|: (Ereg :|: Ppub)))) Omega).
  { have -> : castlf (Eoutcast, Eoutcast) Omega = castlf (cAB, cAB) (castlf (esym (finset.setUCA Zl Fbit (Fl :|: (Ereg :|: Ppub))), esym (finset.setUCA Zl Fbit (Fl :|: (Ereg :|: Ppub)))) Omega). { rewrite castlf_comp. exact: castlf_irrel. }
exact: (@dist_from_uniform_side_cast R L HL Zl (Fbit :|: (Fl :|: (Ereg :|: Ppub))) (Fl :|: (Ereg :|: (Ppub :|: Fbit))) eqB cAB (castlf (esym (finset.setUCA Zl Fbit (Fl :|: (Ereg :|: Ppub))), esym (finset.setUCA Zl Fbit (Fl :|: (Ereg :|: Ppub)))) Omega)). }
by rewrite -Hside; exact: Hdelta. Qed.
Definition bb84_rhoZFbEpub_readout_prog (EA : @adversary R L HL V Eve) (xi : @cq_state R L HL (bb84_cvar M) V)
    (Fbit : {set L}) (acc rej : 'Idx[HL]_Fbit) : 'F[HL]_(Zl :|: (Fbit :|: (Fl :|: (Ereg :|: Ppub)))) :=
  (((@complex.Re R (\Tr (bb84_pass_leakage_public_readout_state EA xi)))^-1
    * (@complex.Re R (\Tr (bb84_pe_pass_leakage_public_readout_state EA xi))))%:C) *:
    castlf (esym (finset.setUCA Zl Fbit (Fl :|: (Ereg :|: Ppub))), esym (finset.setUCA Zl Fbit (Fl :|: (Ereg :|: Ppub))))
      (bb84_flag_pair acc rej (bb84_PHpass EA xi) (bb84_PHvf EA xi)).
Fact bb84_flagged_eps_secret_flag_in_view (EA : @adversary R L HL V Eve) (xi_init : @cq_state R L HL (bb84_cvar M) V) (Hxi : cq_wf xi_init)
    (Fbit : {set L}) (disFS : [disjoint Fbit & Sreg]) (disFE : [disjoint Fbit & Ereg])
    (disFP : [disjoint Fbit & Ppub]) (disFZl : [disjoint Fbit & Zl]) (disFFl : [disjoint Fbit & Fl]) (Hdim2 : dim ('H[HL]_Fbit) = 2%N)
    (acc rej : 'Idx[HL]_Fbit) (Hnr : acc != rej) (eps_s : R) (eps_s_pos : 0 < eps_s) (eps_s_le1 : eps_s <= 1) (Hlen_sup : (bb84_l P)%:R <=
      sup (fun m : R => exists eps ebar : R, 0 < eps /\ eps < 1 /\ 0 < ebar /\ eps + ebar <= eps_s /\
        m = ((floor (bb84_key_length_ub (bb84_n P) (bb84_k P) q (bb84_Qtol P) eps ebar (bb84_leak_EC P) (bb84_eps_c P)))%:~R : R))) :
  @eps_secret R L HL Zl (Fbit :|: (Fl :|: (Ereg :|: Ppub))) (@bb84_rhoZFbEpub_readout_prog EA xi_init Fbit acc rej) eps_s
    (@run_abort_prob R L HL (bb84_cvar M) V (@BVabort M) bb84_bool_val (bb84_eval_scheme_state EA xi_init)).
Proof. have Hxi_psd : forall s, xi_init s \is psdlf by case: Hxi. set xi_out := bb84_eval_scheme_state EA xi_init;
  set p_abort := @run_abort_prob R L HL (bb84_cvar M) V (@BVabort M) bb84_bool_val xi_out. set p_pass := @run_pass_prob R L HL (bb84_cvar M) V (@BVabort M) bb84_bool_val xi_out. have Hpart : p_abort + p_pass = 1 by rewrite /p_abort /p_pass /xi_out; exact: bb84_eval_scheme_abort_pass_partition. have Hay : forall i, @BVa M i != @BVy M i by move=> i; rewrite /BVa /BVy.
  have HPa : forall i, @BVP M != @BVa M i by move=> i; rewrite /BVP /BVa. have HPy : forall i, @BVP M != @BVy M i by move=> i; rewrite /BVP /BVy. have HPb : forall i, @BVP M != @BVb M i by move=> i; rewrite /BVP /BVb.
  have HPy' : forall i, @BVP M != @BVy' M i by move=> i; rewrite /BVP /BVy'. have HPd : forall i, @BVP M != @BVd M i by move=> i; rewrite /BVP /BVd. have HPX : @BVP M != @BVX M by rewrite /BVP /BVX /=; apply: bb84_cvar_inr_neq; rewrite -val_eqE /= !inordK.
  have HPZ : @BVP M != @BVZ M by rewrite /BVP /BVZ /=; apply: bb84_cvar_inr_neq; rewrite -val_eqE /= !inordK.
  have HPabort : @BVP M != @BVabort M by rewrite eq_sym bb84_abort_neq_P. have Hround_wf := @bb84_round_cmd_wf R P q dev LE HE; have Hpe_wf := @bb84_paramest_cmd_wf R P q dev LE HE. have Hec_wf := @bb84_errcorr_cmd_wf R P q dev LE HE; have Hpa_wf := @bb84_privamp_cmd_wf R P q dev LE HE. have Hout_psd : forall s, xi_out s \is psdlf.
  { rewrite /xi_out. exact: (bb84_eval_scheme_state_psd EA Hround_wf Hpe_wf Hec_wf Hpa_wf Hxi_psd). }
have p_source_nonneg : 0 <= bb84_source_pass_prob EA xi_init.
  { exact: (@bb84_source_pass_prob_nonneg R P q dev LE HE bb84_register_index HB EA xi_init Hay HPa HPy HPb HPy' HPd HPX HPZ HPabort Hround_wf Hpe_wf Hec_wf Hpa_wf Hxi_psd). } have p_source_le1_all : bb84_source_pass_prob EA xi_init <= 1.
  { exact: (@bb84_source_pass_prob_le1 R P q dev LE HE bb84_register_index HB EA xi_init Hay HPa HPy HPb HPy' HPd HPX HPZ HPabort Hround_wf Hpe_wf Hec_wf Hpa_wf Hxi). } have HnonabortE : 1 - p_abort = p_pass by move: Hpart => <-; rewrite addrAC subrr add0r.
    have Habort_nn : 0 <= p_abort by rewrite /p_abort /run_abort_prob; apply: run_event_prob_nonneg; exact: Hout_psd.
    have Hpass_nn : 0 <= p_pass by rewrite /p_pass /run_pass_prob; apply: run_event_prob_nonneg; exact: Hout_psd.
    have Hpass_le1 : p_pass <= 1 by rewrite -Hpart lerDr. have Habort_le1 : p_abort <= 1 by rewrite -Hpart lerDl.
    have Hpass_le : bb84_pass_prob_le p_abort (bb84_source_pass_prob EA xi_init).
  { split=> //; split=> //; rewrite HnonabortE /p_pass /xi_out. exact: (bb84_run_pass_prob_le_source EA Hay HPa HPy HPb HPy' HPd HPX HPZ HPabort Hxi_psd). } have Hlen_int : (bb84_l P)%:R \is a int_num := @intr_nat R ((bb84_l P)%:R) (@natr_nat R (bb84_l P)).
    have [eps [ebar [eps_pos [eps_lt1 [ebar_pos [Hbudget Hlen]]]]]] := @bb84_key_length_sup_witness R P q eps_s (bb84_l P)%:R eps_s_pos eps_s_le1 Hlen_int Hlen_sup. set p_source := bb84_source_pass_prob EA xi_init. have eps_nn : 0 <= eps := ltW eps_pos.
    have ebar_nn : 0 <= ebar := ltW ebar_pos. set pass := @complex.Re R (\Tr (@bb84_pass_leakage_public_readout_state R P q dev LE HE EA xi_init)). set pe := @complex.Re R (\Tr (@bb84_pe_pass_leakage_public_readout_state R P q dev LE HE EA xi_init)).
    have Hpass_psd : @bb84_pass_leakage_public_readout_state R P q dev LE HE EA xi_init \is psdlf.
  { rewrite /bb84_pass_leakage_public_readout_state. apply: bb84_pass_history_public_readout_state_psd.
    - exact: bb84_leakage_public_register_state_den1lf.
    - exact: Hxi_psd. } have Hpe_psd : @bb84_pe_pass_leakage_public_readout_state R P q dev LE HE EA xi_init \is psdlf.
  { rewrite /bb84_pe_pass_leakage_public_readout_state. apply: bb84_pe_pass_history_public_readout_state_psd.
    - exact: bb84_leakage_public_register_state_den1lf.
    - exact: Hxi_psd. } have Hpass_ge0 : 0 <= pass by rewrite /pass; have := psdlf_trlf Hpass_psd; rewrite lecE /= => /andP[].
      have Hpe_ge0 : 0 <= pe by rewrite /pe; have := psdlf_trlf Hpe_psd; rewrite lecE /= => /andP[].
      have Hkappa_nn : 0 <= pass^-1 * pe by apply: mulr_ge0; [rewrite invr_ge0 | ]; assumption. have Hpe_re : pe = p_source.
  { rewrite /pe bb84_pe_pass_leakage_public_readout_trace_key_public. exact: bb84_pe_pass_key_public_readout_traceRe. }
have Hpass_eq : pass = 1 - p_abort.
  { rewrite /pass bb84_pass_leakage_public_readout_traceRe. rewrite (bb84_key_public_source_pass_prob_runE EA xi_init Hay HPa HPy HPb HPy' HPd HPX HPZ HPabort). rewrite /bb84_run_pass_prob -/xi_out -/p_pass. by rewrite HnonabortE. }
have disFbE_comb : [disjoint Fbit & (Zl :|: (Fl :|: (Ereg :|: Ppub)))].
  { rewrite disjointXU disFZl disjointXU disFFl disjointXU disFE disFP. by []. } have HPHpass_psd : @bb84_PHpass R P q dev LE HE EA xi_init \is psdlf.
  { rewrite /bb84_PHpass. apply: (@post_hash_psdlf R L HL Sreg (Ereg :|: Ppub) Fl Zl (@bb84_disSEpub R P LE) (@bb84_disSF R P LE) (@bb84_disSZl R P LE) (@bb84_disEpubF R P LE) (@bb84_disEpubZl R P LE) (@bb84_disFZl R P LE) (@bb84_pa_hash_index R P q dev LE HE)).
    rewrite castlf_psdlfE. exact: (@bb84_pass_block_readout_pass_prog_psd R P q dev LE HE EA xi_init Hxi_psd). }
have HPHvf_psd : @bb84_PHvf R P q dev LE HE EA xi_init \is psdlf.
  { rewrite /bb84_PHvf. apply: (@post_hash_psdlf R L HL Sreg (Ereg :|: Ppub) Fl Zl (@bb84_disSEpub R P LE) (@bb84_disSF R P LE) (@bb84_disSZl R P LE) (@bb84_disEpubF R P LE) (@bb84_disEpubZl R P LE) (@bb84_disFZl R P LE) (@bb84_pa_hash_index R P q dev LE HE)).
    rewrite castlf_psdlfE. exact: (@bb84_vf_block_readout_pass_prog_psd R P q dev LE HE EA xi_init Hxi_psd). }
have Hfp_psd : bb84_flag_pair acc rej (@bb84_PHpass R P q dev LE HE EA xi_init) (@bb84_PHvf R P q dev LE HE EA xi_init) \is psdlf.
  { apply: (@bb84_flag_pair_psd R L HL Fbit _ disFbE_comb acc rej); [exact: HPHpass_psd | exact: HPHvf_psd]. }
have Hfc_psd : castlf (esym (finset.setUCA Zl Fbit (Fl :|: (Ereg :|: Ppub))), esym (finset.setUCA Zl Fbit (Fl :|: (Ereg :|: Ppub)))) (bb84_flag_pair acc rej (@bb84_PHpass R P q dev LE HE EA xi_init) (@bb84_PHvf R P q dev LE HE EA xi_init)) \is psdlf by rewrite castlf_psdlfE. have HtrPHpass : \Tr (@bb84_PHpass R P q dev LE HE EA xi_init) = \Tr (bb84_pass_block_readout_pass_prog EA xi_init).
  { rewrite /bb84_PHpass. rewrite (@post_hash_trace_preserve R L HL Sreg (Ereg :|: Ppub) Fl Zl (@bb84_disSEpub R P LE) (@bb84_disSF R P LE) (@bb84_disSZl R P LE) (@bb84_disEpubF R P LE) (@bb84_disEpubZl R P LE) (@bb84_disFZl R P LE) (@bb84_pa_hash_index R P q dev LE HE) _).
    - by rewrite castlf_trlfE.
    - rewrite castlf_psdlfE. exact: (@bb84_pass_block_readout_pass_prog_psd R P q dev LE HE EA xi_init Hxi_psd). }
have HtrPHvf : \Tr (@bb84_PHvf R P q dev LE HE EA xi_init) = \Tr (bb84_vf_block_readout_pass_prog EA xi_init).
  { rewrite /bb84_PHvf. rewrite (@post_hash_trace_preserve R L HL Sreg (Ereg :|: Ppub) Fl Zl (@bb84_disSEpub R P LE) (@bb84_disSF R P LE) (@bb84_disSZl R P LE) (@bb84_disEpubF R P LE) (@bb84_disEpubZl R P LE) (@bb84_disFZl R P LE) (@bb84_pa_hash_index R P q dev LE HE) _).
    - by rewrite castlf_trlfE.
    - rewrite castlf_psdlfE. exact: (@bb84_vf_block_readout_pass_prog_psd R P q dev LE HE EA xi_init Hxi_psd). }
have Hfc_tr_le1 : @complex.Re R (\Tr (castlf (esym (finset.setUCA Zl Fbit (Fl :|: (Ereg :|: Ppub))), esym (finset.setUCA Zl Fbit (Fl :|: (Ereg :|: Ppub)))) (bb84_flag_pair acc rej (@bb84_PHpass R P q dev LE HE EA xi_init) (@bb84_PHvf R P q dev LE HE EA xi_init)))) <= 1.
  { rewrite castlf_trlfE. rewrite (@bb84_flag_pair_trace R L HL Fbit _ disFbE_comb acc rej) HtrPHpass HtrPHvf -raddfD (bb84_pass_vf_block_sum EA xi_init). exact: (@rhoPSE_readout_pass_prog_tr_le1 R P q dev LE HE EA xi_init Hxi_psd). }
have disZl_FbFEP : [disjoint Zl & (Fbit :|: (Fl :|: (Ereg :|: Ppub)))].
  { rewrite disjointXU; apply/andP; split; [by rewrite disjoint_sym | exact: (@bb84_disZl_FEpub R P LE)]. }
have Hstate_psd : @bb84_rhoZFbEpub_readout_prog EA xi_init Fbit acc rej \is psdlf.
  { rewrite /bb84_rhoZFbEpub_readout_prog -/pass -/pe. apply: psdlfZ; [by rewrite lecR | exact: Hfc_psd]. }
have HRe_realM : forall (r : R) (z : C), @complex.Re R (r%:C * z) = r * @complex.Re R z by move=> r z; case: z => zr zi /=; rewrite mul0r subr0. have Hstate_tr : @complex.Re R (\Tr (@bb84_rhoZFbEpub_readout_prog EA xi_init Fbit acc rej)) = (pass^-1 * pe) * @complex.Re R (\Tr (castlf (esym (finset.setUCA Zl Fbit (Fl :|: (Ereg :|: Ppub))), esym (finset.setUCA Zl Fbit (Fl :|: (Ereg :|: Ppub)))) (bb84_flag_pair acc rej (@bb84_PHpass R P q dev LE HE EA xi_init) (@bb84_PHvf R P q dev LE HE EA xi_init)))).
  { rewrite /bb84_rhoZFbEpub_readout_prog -/pass -/pe. by rewrite linearZ /= HRe_realM. } have Htr_state_nn : 0 <= @complex.Re R (\Tr (@bb84_rhoZFbEpub_readout_prog EA xi_init Fbit acc rej)).
  { by have := psdlf_trlf Hstate_psd; rewrite lecE /= => /andP[]. } case: (ltrP (eps ^+ 2) p_source) => Hpass_case.
  - have p_source_pos : 0 < p_source := lt_trans (exprn_gt0 2 eps_pos) Hpass_case. have p_source_le1 : p_source <= 1 := p_source_le1_all.
      have Hsqrt_p_source_pos : 0 < Num.sqrt p_source by rewrite sqrtr_gt0. set eps' := eps / Num.sqrt p_source.
      have Heps'_nn : 0 <= eps' by rewrite divr_ge0 // ltW. have Heps'_lt1 : eps' < 1.
    { rewrite /eps' ltr_pdivrMr // mul1r; have Hdomain : bb84_entropy_domain eps p_source.
      { split=> //; have Heps_sqrt : Num.sqrt (eps ^+ 2) = eps by rewrite sqrtr_sqr ger0_norm // ltW. rewrite -Heps_sqrt ltr_sqrt; first exact: Hpass_case. exact: lt_trans (exprn_gt0 2 eps_pos) Hpass_case. } exact: bb84_eps_lt_sqrt_pass Hdomain. }
have Hlen_real : (bb84_l P)%:R <= bb84_key_length_ub (bb84_n P) (bb84_k P) q (bb84_Qtol P) eps ebar (bb84_leak_EC P) (bb84_eps_c P).
    { exact: (le_trans Hlen (@Rfloor_le R _)). } have Hlog2_dim : @log2 R ((dim 'H[HL]_Zl)%:R : R) = ((bb84_l P)%:R : R) by rewrite bb84_dim_Zl; exact: (@log2_pow2_nat R (bb84_l P)). have H2ebar_pos : 0 < 2%:R * ebar :> R by rewrite mulr_gt0 // ltr0n.
      have Hlog2_inv_ebar : log2 ((2%:R * ebar)^-1) = - log2 (2%:R * ebar) by rewrite /log2 lnV // mulNr.
      have Hlen_public : log2 (dim 'H[HL]_Zl)%:R <= (bb84_n P)%:R * (q - bb84_h_trunc (bb84_Qtol P + bb84_mu (bb84_n P) (bb84_k P) eps))
        + 2%:R * log2 (2%:R * ebar)
        - (bb84_leak_EC P + log2 (2%:R / bb84_eps_c P)).
    { rewrite Hlog2_dim. have Hlen_rewr : (bb84_l P)%:R <= (bb84_n P)%:R * (q - bb84_h_trunc (bb84_Qtol P + bb84_mu (bb84_n P) (bb84_k P) eps))
        + 2%:R * log2 (2%:R * ebar)
        - bb84_leak_EC P - log2 (2%:R / bb84_eps_c P).
      { move: Hlen_real. by rewrite /bb84_key_length_ub Hlog2_inv_ebar mulrN opprK. } by apply: le_trans Hlen_rewr _; rewrite opprD addrA. }
have HdistFb := @bb84_flagged_dist_bound_flag_in_view EA xi_init Hxi Fbit disFS disFE disFP disFZl disFFl Hdim2 acc rej Hnr eps ebar eps_pos eps_lt1 ebar_pos Hpass_case Heps'_lt1 Hlen_public. exists (pass^-1 * pe * (eps' + ebar)); split.
    + rewrite /delta_secret /bb84_rhoZFbEpub_readout_prog -/pass -/pe. apply: le_trans (@dist_uniform_scale_ub R L HL Zl (Fbit :|: (Fl :|: (Ereg :|: Ppub))) disZl_FbFEP (castlf (esym (finset.setUCA Zl Fbit (Fl :|: (Ereg :|: Ppub))), esym (finset.setUCA Zl Fbit (Fl :|: (Ereg :|: Ppub)))) (bb84_flag_pair acc rej (@bb84_PHpass R P q dev LE HE EA xi_init) (@bb84_PHvf R P q dev LE HE EA xi_init))) (pass^-1 * pe) Hfc_psd Hkappa_nn) _. by apply: (ler_wpM2l Hkappa_nn); exact: HdistFb.
    + case: (ltrP 0 (1 - p_abort)) => Hfull_case; last first.
      * apply: le_trans (_ : (1 - p_abort) * (pass^-1 * pe * (eps' + ebar)) <= 0) (ltW eps_s_pos). apply: mulr_le0_ge0; first exact: Hfull_case. apply: mulr_ge0; first exact: Hkappa_nn. by apply: addr_ge0; [exact: Heps'_nn | exact: ebar_nn].
      * rewrite Hpass_eq Hpe_re. have Hne : (1 - p_abort) != 0 by rewrite lt0r_neq0. have Hsqrt_ne : Num.sqrt p_source != 0 by rewrite lt0r_neq0. rewrite mulrA mulrA (mulfV Hne) mul1r mulrDr. have Hpe' : p_source * eps' = Num.sqrt p_source * eps.
        { rewrite /eps' -{1}(sqr_sqrtr (ltW p_source_pos)) expr2 -!mulrA. congr (_ * _). by rewrite mulrCA divff // mulr1. } rewrite Hpe'.
          have Hsqrt_le1 : Num.sqrt p_source <= 1 by rewrite -sqrtr1 ler_wsqrtr. apply: le_trans (_ : eps + ebar <= eps_s); last exact: Hbudget. apply: lerD.
        -- by rewrite -{2}(mul1r eps) ler_wpM2r.
        -- by rewrite -{2}(mul1r ebar) ler_wpM2r.
  - have Heps2_lt_eps_s : eps ^+ 2 < eps_s.
    { apply: (@le_lt_trans _ _ eps).
      - by rewrite expr2 -[X in _ <= X]mulr1; apply: (ler_wpM2l (ltW eps_pos)); exact: ltW eps_lt1.
      - apply: (@lt_le_trans _ _ (eps + ebar)); last exact: Hbudget. by rewrite -{1}(addr0 eps) ltrD2l. }
have Hp_source_lt_eps_s : p_source < eps_s := le_lt_trans Hpass_case Heps2_lt_eps_s.
        exists (@complex.Re R (\Tr (@bb84_rhoZFbEpub_readout_prog EA xi_init Fbit acc rej))); split.
    + by rewrite /delta_secret; exact: (dist_uniform_le_trace disZl_FbFEP Hstate_psd).
    + rewrite Hstate_tr; case: (ltrP 0 (1 - p_abort)) => Hfull_case.
      * apply: (@le_trans _ _ p_source); last exact: ltW Hp_source_lt_eps_s. rewrite mulrA; have Hstep : (1 - p_abort) * (pass^-1 * pe) = pe.
        { rewrite -Hpass_eq mulrA mulfV ?mul1r //. by rewrite Hpass_eq lt0r_neq0. } rewrite Hstep Hpe_re; apply: le_trans (ler_wpM2l p_source_nonneg Hfc_tr_le1) _. by rewrite mulr1.
      * apply: le_trans (_ : (1 - p_abort) * ((pass^-1 * pe) * @complex.Re R (\Tr (castlf (esym (finset.setUCA Zl Fbit (Fl :|: (Ereg :|: Ppub))), esym (finset.setUCA Zl Fbit (Fl :|: (Ereg :|: Ppub)))) (bb84_flag_pair acc rej (@bb84_PHpass R P q dev LE HE EA xi_init) (@bb84_PHvf R P q dev LE HE EA xi_init))))) <= 0) (ltW eps_s_pos). apply: mulr_le0_ge0; first exact: Hfull_case. by apply: mulr_ge0; first exact: Hkappa_nn; have := psdlf_trlf Hfc_psd; rewrite lecE /= => /andP[]. Qed.
Lemma bb84_secure_protocol_pow2 (eps_s eps_tot : R) : bb84_eps_c P + eps_s <= eps_tot -> (0 < eps_s) && (eps_s <= 1) -> (bb84_l P)%:R <=
    sup (fun m : R => exists eps ebar : R, 0 < eps /\ eps < 1 /\ 0 < ebar /\ eps + ebar <= eps_s /\
        m = ((floor (bb84_key_length_ub (bb84_n P) (bb84_k P) q (bb84_Qtol P) eps ebar (bb84_leak_EC P) (bb84_eps_c P)))%:~R : R)) ->
  forall (EA : @adversary R L HL V Eve) (xi_init : @cq_state R L HL (bb84_cvar M) V),
  cq_wf xi_init -> let xi_out := @bb84_eval R P q LE HE bb84_register_index HB dev Eve EA xi_init in let p_abort :=
    @run_abort_prob R L HL (bb84_cvar M) V (@BVabort M) bb84_bool_val xi_out in let p_pass :=
    @run_pass_prob R L HL (bb84_cvar M) V (@BVabort M) bb84_bool_val xi_out in let p_mismatch :=
    @run_output_mismatch_prob R L HL (bb84_cvar M) V (@BVS M) (@BVSh M) (@BVabort M) bb84_bool_val xi_out in
  forall (acc rej : 'Idx[HL]_(bb84_signal_reg i0)), acc != rej ->
  [/\ (forall (h : @run_history V M) (s : @store (bb84_cvar M) V), bb84_branch_shape h s), p_abort + p_pass = 1
    & @eps_secure R L HL Zl (bb84_signal_reg i0 :|: (Fl :|: (Ereg :|: Ppub))) p_mismatch (bb84_eps_c P)
        (bb84_rhoZFbEpub_readout_prog EA xi_init acc rej) eps_s p_abort eps_tot].
Proof. move=> Htot_budget /andP [eps_s_pos eps_s_le1] Hlen_sup EA xi_init Hxi /=; move=> acc rej Hnr.
  have Hpart := @bb84_partition_protocol R P q dev LE HE EA xi_init Hxi. have Hcorrect := @bb84_correct_protocol R P q dev LE HE EA xi_init Hxi; move: Hpart Hcorrect => /=. set xi_out := @bb84_eval R P q LE HE bb84_register_index HB dev Eve EA xi_init; move=> Hpart Hcorrect.
  have disFS : [disjoint bb84_signal_reg i0 & Sreg]. by rewrite /bb84_signal_reg disjoint1X /bb84_S /bb84_reg /bb84_bridge_reg inE; rewrite /bb84_signal_label /bb84_bridge_label. have disFP : [disjoint bb84_signal_reg i0 & Ppub].
  by rewrite /bb84_signal_reg disjoint1X /bb84_Ppub /bb84_reg /bb84_bridge_reg inE; rewrite /bb84_signal_label /bb84_bridge_label.
  have disFE : [disjoint bb84_signal_reg i0 & Ereg]. rewrite /bb84_E disjointXU; apply/andP; split.
    - by rewrite /bb84_signal_reg disjoint1X /bb84_Eve /bb84_eve_reg inE; rewrite /bb84_signal_label.
    - by rewrite /bb84_signal_reg disjoint1X /bb84_Epub /bb84_reg /bb84_bridge_reg inE; rewrite /bb84_signal_label /bb84_bridge_label.
      have disFZl : [disjoint bb84_signal_reg i0 & Zl]. by rewrite /bb84_signal_reg disjoint1X /bb84_Zl /bb84_reg /bb84_bridge_reg inE; rewrite /bb84_signal_label /bb84_bridge_label. have disFFl : [disjoint bb84_signal_reg i0 & Fl].
      by rewrite /bb84_signal_reg disjoint1X /bb84_Fl /bb84_reg /bb84_bridge_reg inE; rewrite /bb84_signal_label /bb84_bridge_label.
      have Hdim2 : dim ('H[HL]_(bb84_signal_reg i0)) = 2%N by exact: (bb84_signal_reg_dim HE HB i0).
      have Hsecret_scheme := @bb84_flagged_eps_secret_flag_in_view EA xi_init Hxi (bb84_signal_reg i0) disFS disFE disFP disFZl disFFl Hdim2 acc rej Hnr eps_s eps_s_pos eps_s_le1 Hlen_sup. have evalE : @bb84_eval R P q LE HE bb84_register_index HB dev Eve EA xi_init = bb84_eval_scheme_state EA xi_init.
  { by rewrite /bb84_eval /bb84_program /bb84_eval_scheme_state /bb84_eval_scheme /bb84_program_scheme /bb84_program_device_rho /bb84_device_dev_rho /bb84_program_device_meas /bb84_device_dev_meas /bb84_program_basis_value /bb84_basis_value /bb84_program_basis_of_value /bb84_basis_of_value. } have Hsecret : @eps_secret R L HL Zl (bb84_signal_reg i0 :|: (Fl :|: (Ereg :|: Ppub))) (bb84_rhoZFbEpub_readout_prog EA xi_init acc rej) eps_s (@run_abort_prob R L HL (bb84_cvar M) V (@BVabort M) bb84_bool_val xi_out). { rewrite /xi_out evalE. exact: Hsecret_scheme. } have Hsecure : @eps_secure R L HL Zl (bb84_signal_reg i0 :|: (Fl :|: (Ereg :|: Ppub))) (@run_output_mismatch_prob R L HL (bb84_cvar M) V (@BVS M) (@BVSh M) (@BVabort M) bb84_bool_val xi_out) (bb84_eps_c P) (bb84_rhoZFbEpub_readout_prog EA xi_init acc rej) eps_s (@run_abort_prob R L HL (bb84_cvar M) V (@BVabort M) bb84_bool_val xi_out) eps_tot.
  { split; first exact: Hcorrect. split; first exact: Hsecret. exact: Htot_budget. } split.
  - move=> h s; exact: bb84_final_store_branch_shape.
  - exact: Hpart.
  - exact: Hsecure. Qed.
Fact pow2_inv_le_of_log2_inv_le (x : R) (m : nat) : 0 < x -> log2 (x^-1)%R <= m%:R -> (((2 ^ m)%:R : R)^-1)%R <= x.
Proof. move=> Hx Hlog; have Hxinv_pos : (0 < (x^-1)%R) by rewrite invr_gt0. have Hpow_pos : (0:R) < (2^m)%:R by rewrite ltr0n expn_gt0.
  have Hle2 : log2 (x^-1)%R <= log2 ((2^m)%:R : R) by rewrite log2_pow2_nat. have Hxinv_le : ((x^-1)%R <= ((2^m)%:R : R)). move: Hle2; rewrite /log2 ler_pM2r; last by rewrite invr_gt0 ln2_gt0. by rewrite ler_ln. by rewrite -(invrK x) lef_pV2 ?inE ?posrE ?invr_gt0. Qed.
Corollary bb84_secure_protocol (ec eps_s eps_tot : R) (Hec_pos : 0 < ec) (Hec_le1 : ec <= 1) (Hround : bb84_ceil_log_inv_eps ec kk) :
  ec + eps_s <= eps_tot -> (0 < eps_s) && (eps_s <= 1) -> (bb84_l P)%:R <= sup (fun m : R => exists eps ebar : R,
        0 < eps /\ eps < 1 /\ 0 < ebar /\ eps + ebar <= eps_s /\ m = ((floor (bb84_key_length_ub (bb84_n P) (bb84_k P) q
          (bb84_Qtol P) eps ebar (bb84_leak_EC P) (bb84_eps_c P)))%:~R : R)) -> forall (EA : @adversary R L HL V Eve)
    (xi_init : @cq_state R L HL (bb84_cvar M) V), cq_wf xi_init -> let xi_out := @bb84_eval R P q LE HE bb84_register_index HB dev
    Eve EA xi_init in let p_abort := @run_abort_prob R L HL (bb84_cvar M) V (@BVabort M) bb84_bool_val xi_out in let p_pass :=
    @run_pass_prob R L HL (bb84_cvar M) V (@BVabort M) bb84_bool_val xi_out in let p_mismatch :=
    @run_output_mismatch_prob R L HL (bb84_cvar M) V (@BVS M) (@BVSh M) (@BVabort M) bb84_bool_val xi_out in
  forall (acc rej : 'Idx[HL]_(bb84_signal_reg i0)), acc != rej ->
  [/\ (forall (h : @run_history V M) (s : @store (bb84_cvar M) V), bb84_branch_shape h s), p_abort + p_pass = 1
    & @eps_secure R L HL Zl (bb84_signal_reg i0 :|: (Fl :|: (Ereg :|: Ppub))) p_mismatch ec
        (bb84_rhoZFbEpub_readout_prog EA xi_init acc rej) eps_s p_abort eps_tot].
Proof. move=> Htot_budget Hrange Hlen_sup EA xi_init Hxi /=; move=> acc rej Hnr. have Hecp_le : bb84_eps_c P <= ec.
  { rewrite Heps_c. case: Hround => Hlog _. exact: pow2_inv_le_of_log2_inv_le Hec_pos Hlog. } have Hbase_budget : bb84_eps_c P + eps_s <= eps_tot by apply: le_trans Htot_budget; rewrite lerD2r.
  have Hbase := @bb84_secure_protocol_pow2 eps_s eps_tot Hbase_budget Hrange Hlen_sup EA xi_init Hxi acc rej Hnr.
    move: Hbase => /= [Hbranch Hpart Hsecure_ec'].
  have [Hcorr_ec' [Hsecret _]] := Hsecure_ec'. have Hcorr_ec : @eps_correct R (@run_output_mismatch_prob R L HL (bb84_cvar M) V (@BVS M) (@BVSh M) (@BVabort M) bb84_bool_val (@bb84_eval R P q LE HE bb84_register_index HB dev Eve EA xi_init)) ec by exact: le_trans Hcorr_ec' Hecp_le. split.
  - exact: Hbranch.
  - exact: Hpart.
  - split; first exact: Hcorr_ec. by split; [exact: Hsecret | exact: Htot_budget]. Qed.
End BB84FlaggedPHpassBound.
