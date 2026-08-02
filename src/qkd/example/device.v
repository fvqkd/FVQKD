(* device.v -- BB84 device interface                                    *)
(* Module: qkd.example.device                                           *)
(* The record `bb84_certified_device` packages the source model, the    *)
(* per-qubit preparation and measurement operators, and the classical   *)
(* post-processing primitives with their numeric bounds, for the        *)
(* protocol theorem layer.                                              *)

From mathcomp Require Import all_boot all_order all_algebra.
From mathcomp.reals Require Import reals.
From quantum.external Require Import spectral complex.
From quantum Require Import mcextra mcaextra notation hermitian quantum cpo mxpred extnum ctopology svd mxnorm hspace.
From quantum.dirac Require Import hstensor.

Import Order.TTheory GRing.Theory Num.Theory Num.Def MxLownerOrder.
Import VectorInternalTheory.

From utils Require Import arith.
From eur Require Import def prop.
From lhl Require Import def.
From qkd.bb84 Require Import def model.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Open Scope ring_scope.
Local Open Scope lfun_scope.

Section CertifiedDevice.
Variable R : realType.
Notation C := (@hermitian.C R).
Notation bb84_protocol := (@bb84_protocol R).

Definition bb84_source_x_povm (P : bb84_protocol) (q : R) (src : bb84_source_model P q) (dim_A : bb84_src_na src = (2 ^ bb84_n P)%N)
    (dim_X : bb84_src_nx src = (2 ^ bb84_n P)%N) : 'I_(2 ^ bb84_n P) -> 'M[C]_(2 ^ bb84_n P) := cast_square_povm_mx (esym dim_X)
    (fun x : 'I_(bb84_src_nx src) => castmx (etrans dim_A (esym dim_X), etrans dim_A (esym dim_X)) (@bb84_src_M R P q src x)).

Fact bb84_source_x_povm_is_povm (P : bb84_protocol) (q : R) (src : bb84_source_model P q) (dim_A : bb84_src_na src = (2 ^ bb84_n P)%N)
    (dim_X : bb84_src_nx src = (2 ^ bb84_n P)%N) : is_povm_mx (bb84_source_x_povm dim_A dim_X).
Proof.
have cast_povm_mx_is_povm : forall (nx n m : nat) (e : n = m) (M : 'I_nx -> 'M[C]_n), is_povm_mx M -> is_povm_mx (fun x => castmx (e, e) (M x)).
{ clear dim_X dim_A src q P; move=> nx n m e M. case: m / e M => M HM.
  apply/is_povm_mxP; split.
  - move=> x.
    rewrite castmx_id.
    exact: is_povm_mx_psd HM.
  - under eq_bigr do rewrite castmx_id.
    exact: is_povm_mx_sum HM. } rewrite /bb84_source_x_povm.
  apply: cast_square_povm_mx_is_povm.
  apply: cast_povm_mx_is_povm.
  exact: (@bb84_src_M_povm R P q src). Qed.

Record bb84_certified_device (P : bb84_protocol) (q : R)
  := BB84CertifiedDevice {
  cd_src : bb84_source_model P q;
  cd_src_dim_A : bb84_src_na cd_src = (2 ^ bb84_n P)%N;
  cd_src_dim_X : bb84_src_nx cd_src = (2 ^ bb84_n P)%N;
  cd_src_nb_pos : (0 < bb84_src_nb cd_src)%N;
  cd_src_overlap_standard_z :
    (bb84_n P)%:R * q <= q_of_mx
      (bb84_source_x_povm cd_src_dim_A cd_src_dim_X)
      (@std_projective_povm R (2 ^ bb84_n P));

  cd_rho : bb84_basis -> bool -> 'M[C]_2;
  cd_rho_den1 : forall basis bit, cd_rho basis bit \is den1mx;

  cd_meas : bb84_basis -> option bool -> 'M[C]_2;
  cd_meas_complete : forall basis,
    (cd_meas basis None)^*t *m cd_meas basis None +
    (cd_meas basis (Some false))^*t *m cd_meas basis (Some false) +
    (cd_meas basis (Some true))^*t *m cd_meas basis (Some true) = 1%:M;
  cd_detect_basis_indep :
    cd_meas BasisX None = cd_meas BasisZ None;

  cd_ir_bits : nat;
  cd_ir_pub :
    'I_(2 ^ bb84_n P) -> 'I_(2 ^ bb84_n P) -> 'I_(2 ^ cd_ir_bits);
  cd_ir_dec :
    'I_(2 ^ cd_ir_bits) -> 'I_(2 ^ bb84_n P) -> 'I_(2 ^ bb84_n P);
  cd_ir_leak : (cd_ir_bits)%:R <= bb84_leak_EC P;

  cd_vseed_count : nat;
  cd_vseed_pos : (0 < cd_vseed_count)%N;
  cd_tag_count : nat;
  cd_vh :
    'I_cd_vseed_count -> 'I_(2 ^ bb84_n P) -> 'I_cd_tag_count;
  cd_vh_two_univ : @two_univ R _ _ _ cd_vh;
  cd_tag_pos : (0 < cd_tag_count)%N;
  cd_tag_le : ((cd_tag_count%:R : R)^-1 <= bb84_eps_c P)%R;
  cd_tag_bits :
    log2 (cd_tag_count%:R : R) <= log2 (2%:R / bb84_eps_c P);

  cd_paseed_count : nat;
  cd_paseed_pos : (0 < cd_paseed_count)%N;
  cd_pa :
    'I_cd_paseed_count -> 'I_(2 ^ bb84_n P) -> 'I_(2 ^ bb84_l P);
  cd_pa_two_univ : @two_univ R _ _ _ cd_pa; }
.

End CertifiedDevice.

Arguments bb84_certified_device {R} P q.

Local Open Scope ring_scope.

Section LeakageBounds.
Variables (R : realType) (P : @bb84_protocol R) (q : R) (dev : bb84_certified_device P q).

Fact bb84_ec_tag_leak_bound : log2 ((((2 ^ cd_ir_bits dev) * cd_tag_count dev)%:R : R)) <= bb84_leak_EC P + log2 (2%:R / bb84_eps_c P).
Proof. rewrite natrM log2_mul ?log2_pow2_nat; [|by rewrite ltr0n expn_gt0|by rewrite ltr0n cd_tag_pos]. by exact: lerD (cd_ir_leak dev) (cd_tag_bits dev). Qed.

Fact bb84_ec_tag_leak_bound_flagged (k : nat) (Heps_c : bb84_eps_c P = ((2 ^ k)%:R : R)^-1) (Htag : cd_tag_count dev = (2 ^ k)%N) :
  log2 ((((2 ^ cd_ir_bits dev) * cd_tag_count dev * 2)%:R : R)) <= bb84_leak_EC P + log2 (2%:R / bb84_eps_c P).
Proof.
  have Hlhs : (2 ^ cd_ir_bits dev * 2 ^ k * 2)%N = (2 ^ (cd_ir_bits dev + k + 1))%N by rewrite addn1 expnSr expnD.
  rewrite Htag Heps_c Hlhs log2_pow2_nat.
  have Hrhs : (2%:R / ((2 ^ k)%:R : R)^-1) = ((2 ^ (k + 1))%:R : R).
  { rewrite invrK -natrM; congr (_%:R). by rewrite -{1}(expn1 2) -expnD add1n addn1. } by rewrite Hrhs log2_pow2_nat -addnA natrD; apply: lerD; [exact: cd_ir_leak dev | exact: lexx]. Qed.

End LeakageBounds.
