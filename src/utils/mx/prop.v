(* -------------------------------------------------------------------- *)
(* prop.v — Matrix-level lemmas and properties                           *)
(* -------------------------------------------------------------------- *)
(* Module: utils.mx.prop                                  *)
(* TeX source: none (library utility)                                    *)
(* TeX labels: none                                                      *)
(* -------------------------------------------------------------------- *)
(* Owns all matrix-level LEMMAS (computations, identities, qualifier-   *)
(* preservations). Pure matrix-level — no lfun-level, no labeled-system.*)
(* Contents: sqrtmx algebra (psd/K/herm/0/1/mapfE/Z_nn/tens),            *)
(* psdmx_le_tr_id,                                                      *)
(* castmx_sq_*, max_mixed_denmx, tensmx_*, tuple_tensmx_*,              *)
(* trace_tensmx, ptrace_tensmx, trnorm_unitarymx, trnorm_psdmx,          *)
(* sqrtmx_block_diag, trnorm_block_diag, mxtrace_abaaba_collapse,        *)
(* sigma23K, mxswap23K, ptrace1/2_denmx/psdmx, setDU_r/l,               *)
(* setDU3_A/B/C, setUC_swap3.                                            *)
(* -------------------------------------------------------------------- *)

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
From quantum Require Import mcextra mcaextra notation hermitian quantum
  cpo mxpred extnum ctopology svd mxnorm hspace.

Import Order.TTheory GRing.Theory Num.Theory Num.Def MxLownerOrder.
Import VectorInternalTheory.

(* --- FVQKD imports --- *)
From utils.mx Require Import def.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Open Scope ring_scope.

Section FvqkdReal.
Variable R : realType.
Notation C := (@hermitian.C R).
Notation chsType := (@chsType R).

(* ================================================================== *)
(* sqrtmx algebra (qualifier preservation, composition, scaling)       *)
(* ================================================================== *)

(* sqrtmx_psd *)
(* infra: no tex label — fundamental & reusable (mathcomp-style) *)
(* consumer: sqrtmx_psd is used downstream by the BB84 secrecy proof. *)
(* path: utils:sqrtmx_psd -> entropy:smooth_hmax_attained -> *)
(*   entropy:smooth_hmaxE_EFin -> *)
(*   bb84:bb84_secret *)
Lemma sqrtmx_psd {n : nat} (M : 'M[C]_n) : M \is psdmx -> sqrtmx M \is psdmx.
Proof.
  move=> _; rewrite /sqrtmx.
  rewrite -[X in _ *m _ *m X]adjmxK.
  apply/psdmx_bimap_closed_gen/diagmx_nnegmx_psd.
  apply/nnegmxP=> i j; rewrite !mxE nnegrE.
  by rewrite lecR sqrtr_ge0.
Qed.

(* sqrtmxK *)
(* infra: no tex label — fundamental & reusable (mathcomp-style) *)
(* consumer: sqrtmxK is used downstream by the BB84 secrecy proof. *)
(* path: utils:sqrtmxK -> bb84:stat -> bb84:bb84_secret *)
Lemma sqrtmxK {n : nat} (M : 'M[C]_n) : M \is psdmx -> sqrtmx M *m sqrtmx M = M.
Proof.
  move=> PM.
  rewrite /sqrtmx.
  set U := spectralmx M. set sp := spectral_diag M.
  set sq : 'rV[C]_n := \row_i (Num.sqrt (@complex.Re R (sp 0 i)))%:C.
  have UU : U \is unitarymx by apply: spectral_unitarymx.
  have UUt : U *m U^*t = 1%:M by apply: unitarymxK.
  have Pnneg : sp \is a nnegmx by case/psdmxP: PM.
  have collapse : U^*t *m diag_mx sq *m U *m (U^*t *m diag_mx sq *m U)
                = U^*t *m (diag_mx sq *m diag_mx sq) *m U.
    transitivity (U^*t *m diag_mx sq *m (U *m U^*t) *m diag_mx sq *m U).
      by rewrite !mulmxA.
    rewrite UUt mulmx1; congr (_ *m U); by rewrite mulmxA.
  rewrite collapse mulmx_diag.
  have sqsq : \row_j (sq 0 j * sq 0 j) = sp :> 'rV[C]_n.
    apply/matrixP=> i j; rewrite !mxE.
    rewrite (ord1 i).
    have Hnn : 0 <= sp 0 j.
      by move/nnegmxP: Pnneg=>/(_ 0 j); rewrite nnegrE.
    move: Hnn; case E : (sp 0 j) => [a b] /=.
    rewrite lecE /= => /andP[/eqP Hb Ha].
    by rewrite -rmorphM/= -expr2 sqr_sqrtr// Hb.
  rewrite sqsq.
  have PNormal : M \is normalmx by apply/hermmx_normal/psdmx_herm.
  by move/eigen_dec: PNormal; rewrite /eigenmx -/U -/sp adjmxK=> <-.
Qed.

(* sqrtmx_herm *)
(* infra: no tex label — fundamental & reusable (mathcomp-style) *)
(* consumer: sqrtmx_herm is used downstream by the BB84 secrecy proof. *)
(* path: utils:sqrtmx_herm -> eur:rho_XB_subden -> eur:eur_rho_XB_psd -> *)
(*   bb84:bb84_secret *)
Lemma sqrtmx_herm {n : nat} (M : 'M[C]_n) : M \is hermmx -> sqrtmx M \is hermmx.
Proof.
  move=> _; apply/hermmxP.
  rewrite /sqrtmx !adjmxM adjmxK diag_mx_adj mulmxA; congr (_ *m _ *m _).
  apply/matrixP=> i j; rewrite !mxE.
  case: (i == j); last by [].
  by apply/eqP; rewrite eq_complex/= eqxx oppr0 eqxx.
Qed.

(* sqrtmx0 *)
(* infra: no tex label — fundamental & reusable (mathcomp-style) *)
(* consumer: sqrtmx0 is used downstream by the BB84 secrecy proof. *)
(* path: utils:sqrtmx0 -> bb84:privacy_amplification -> *)
(*   bb84:bb84_secret *)
Lemma sqrtmx0 {n : nat} : sqrtmx (0 : 'M[C]_n) = 0.
Proof.
  rewrite /sqrtmx spectral_diag0.
  rewrite (_ : \row_i _ = 0); last first.
    by apply/matrixP=> i j; rewrite !mxE /= sqrtr0 raddf0.
  by rewrite linear0 mulmx0 mul0mx.
Qed.

(* sqrtmx1 *)
(* infra: no tex label — fundamental & reusable (mathcomp-style) *)
(* consumer: sqrtmx1 is used downstream by the BB84 secrecy proof. *)
(* path: utils:sqrtmx1 -> utils:sqrtH1 -> entropy:min_koenig -> *)
(*   entropy:min_omni -> entropy:minmax_dual -> entropy:smooth_iso_hmax -> *)
(*   entropy:entropy_data_proc -> *)
(*   bb84:bb84_secret *)
Lemma sqrtmx1 {n : nat} : sqrtmx (1%:M : 'M[C]_n) = 1%:M.
Proof.
  rewrite /sqrtmx spectral_diag1.
  have eq1 : \row_i (Num.sqrt (@complex.Re R ((const_mx 1 : 'rV[C]_n) 0 i)))%:C
           = (const_mx 1 : 'rV[C]_n).
    apply/matrixP=> i j; rewrite !mxE.
    have -> : @complex.Re R (1 : C) = 1 by [].
    by rewrite sqrtr1.
  by rewrite eq1 diag_const_mx mulmx1 unitarymxKV.
Qed.

(* Bridge: sqrtmx = mapf_mx (λ z, sqrt(Re z)%:C) *)
(* sqrtmx_mapfE *)
(* infra: no tex label — fundamental & reusable (mathcomp-style) *)
(* consumer: sqrtmx_mapfE is used downstream by the BB84 secrecy proof. *)
(* path: utils:sqrtmx_mapfE -> utils:sqrtmxZ_nn -> bb84:stat -> *)
(*   bb84:bb84_secret *)
Lemma sqrtmx_mapfE {n : nat} (A : 'M[C]_n) :
  sqrtmx A = mapf_mx (fun z : C => (Num.sqrt (@complex.Re R z))%:C) A.
Proof.
  rewrite /sqrtmx mapf_mx.unlock.
  have rowE :
      \row_i (Num.sqrt (@complex.Re R (spectral_diag A 0 i)))%:C =
      map_mx (fun z : C => (Num.sqrt (@complex.Re R z))%:C)
        (spectral_diag A).
    by apply/matrixP=> i j; rewrite !mxE (ord1 i).
  by rewrite rowE.
Qed.

(* Scalar rule: nonnegative real scaling on PSD matrices.              *)
(* sqrtmxZ_nn *)
(* infra: no tex label — fundamental & reusable (mathcomp-style) *)
(* consumer: sqrtmxZ_nn is used downstream by the BB84 secrecy proof. *)
(* path: utils:sqrtmxZ_nn -> bb84:stat -> bb84:bb84_secret *)
Lemma sqrtmxZ_nn {n : nat} (c : R) (M : 'M[C]_n) :
  0 <= c -> M \is psdmx ->
  sqrtmx ((c%:C) *: M) = (Num.sqrt c)%:C *: sqrtmx M.
Proof.
  move=> c_ge0 PM.
  set P := spectralmx M. set sp := spectral_diag M.
  have PU : P \is unitarymx by apply: spectral_unitarymx.
  have PM_normal : M \is normalmx by apply/hermmx_normal/psdmx_herm.
  have decM : P^*t *m diag_mx sp *m P = M.
    by move/eigen_dec: PM_normal; rewrite /eigenmx -/P -/sp adjmxK => <-.
  have spnneg : sp \is a nnegmx by case/psdmxP: PM.
  pose f (z : C) : C := (Num.sqrt (@complex.Re R z))%:C.
  have sqrtM_eq : sqrtmx M = P^*t *m diag_mx (map_mx f sp) *m P.
    by rewrite sqrtmx_mapfE -(mapf_mx_unique f PU decM).
  have deccM : P^*t *m diag_mx ((c%:C) *: sp) *m P = (c%:C) *: M.
    by rewrite linearZ/= -scalemxAr -scalemxAl decM.
  have sqrtcM_eq : sqrtmx ((c%:C) *: M)
                 = P^*t *m diag_mx (map_mx f ((c%:C) *: sp)) *m P.
    by rewrite sqrtmx_mapfE -(mapf_mx_unique f PU deccM).
  have scale_eq : map_mx f ((c%:C) *: sp) = (Num.sqrt c)%:C *: map_mx f sp.
    apply/matrixP=> i j; rewrite !mxE /f.
    have Hz : 0 <= sp i j by move/nnegmxP: spnneg => /(_ i j); rewrite nnegrE.
    have Hz_real : sp i j \is Num.real := ger0_real Hz.
    have HRe_nn : 0 <= @complex.Re R (sp i j).
      by move: Hz; rewrite lecE/= => /andP[_].
    rewrite -{1}(RRe_real Hz_real) -realcM re_realid.
    by rewrite sqrtrM// realcM.
  rewrite sqrtcM_eq sqrtM_eq scale_eq.
  by rewrite [diag_mx _]linearZ/= -scalemxAr -scalemxAl.
Qed.

(* For PSD P, sqrtmx(P*P) = P.                                                 *)
(* sqrtmx_psd_square *)
(* infra: no tex label — fundamental & reusable (mathcomp-style) *)
(* consumer: sqrtmx_psd_square is used downstream by the BB84 secrecy proof. *)
(* path: utils:sqrtmx_psd_square -> entropy:smooth_hmax_attained -> *)
(*   entropy:smooth_hmaxE_EFin -> *)
(*   bb84:bb84_secret *)
Lemma sqrtmx_psd_square {n : nat} (P : 'M[C]_n) :
  P \is psdmx -> sqrtmx (P *m P) = P.
Proof.
  move=> HP.
  have Hnorm : P \is normalmx by apply/hermmx_normal/psdmx_herm.
  set U := spectralmx P. set sp := spectral_diag P.
  have HU : U \is unitarymx by apply: spectral_unitarymx.
  have /eigen_dec HPspec := Hnorm.
  have Hspec : P = U^*t *m diag_mx sp *m U
    by move: HPspec; rewrite /eigenmx -/U -/sp adjmxK=> <-.
  have /unitarymxP HUU : U \is unitarymx by exact: HU.
  have Hsqspec : P *m P = U^*t *m diag_mx (sp .* sp) *m U.
    rewrite Hspec -!mulmxA (mulmxA U U^*t) HUU mul1mx !mulmxA mulmxACA.
    by rewrite diag_mx_dmul.
  set f := fun x : C => (Num.sqrt (@complex.Re R x))%:C.
  have /realmxP Hsp_real := hermitian_spectral_diag_real (psdmx_herm HP).
  have Hf_sp : map_mx f (sp .* sp) = sp.
    apply/matrixP=> i j.
    have -> : i = ord0 by exact: ord1.
    rewrite !mxE /f.
    have Hreal := Hsp_real ord0 j.
    have Hge := psdmx_eigen_ge0 j HP.
    have Hspj : sp ord0 j = (@complex.Re R (sp ord0 j))%:C
      by exact: (esym (RRe_real Hreal)).
    rewrite [sp ord0 j]Hspj /=.
    congr (_%:C).
    move: Hge; rewrite lecE/= => /andP[_ Hre].
    by rewrite !mul0r subr0 -expr2 sqrtr_sqr ger0_norm.
  by rewrite sqrtmx_mapfE -(mapf_mx_unique f HU (esym Hsqspec)) Hf_sp -Hspec.
Qed.

(* sqrtmx commutes with unitary conjugation on PSD matrices. *)
(* sqrtmx_unitary_conj *)
(* infra: no tex label — fundamental & reusable (mathcomp-style) *)
(* consumer: sqrtmx_unitary_conj is used downstream by the BB84 secrecy proof. *)
(* path: utils:sqrtmx_unitary_conj -> utils:fid_unitary_conj_mx -> *)
(*   utils:fid_ptr_mono -> entropy:entropy_data_proc -> *)
(*   bb84:bb84_secret *)
Lemma sqrtmx_unitary_conj {n : nat} (U A : 'M[C]_n) :
  U \is unitarymx -> A \is psdmx ->
  sqrtmx (U *m A *m U^*t) = U *m sqrtmx A *m U^*t.
Proof.
  move=> HU HA.
  set f := fun x : C => (Num.sqrt (@complex.Re R x))%:C.
  have /hermmx_normal/eigen_dec Hspec := psdmx_herm HA.
  have HAeig : A = (spectralmx A)^*t *m diag_mx (spectral_diag A) *m spectralmx A
    by move: Hspec; rewrite /eigenmx adjmxK.
  have HVu := spectral_unitarymx A.
  set Ut := U^*t.
  set W := spectralmx A *m Ut.
  have HUt : Ut \is unitarymx by rewrite /Ut; exact: adjmx_unitaryP HU.
  have HWu : W \is unitarymx by rewrite /W; exact: mul_unitarymx HVu HUt.
  have Hmap : sqrtmx A =
      (spectralmx A)^*t *m diag_mx (map_mx f (spectral_diag A)) *m spectralmx A.
    by rewrite sqrtmx_mapfE mapf_mx.unlock.
  have Hspec2 : W^*t *m diag_mx (spectral_diag A) *m W = U *m A *m Ut.
    have -> : U *m A *m Ut =
      U *m ((spectralmx A)^*t *m diag_mx (spectral_diag A) *m spectralmx A) *m Ut
      by rewrite -HAeig.
    by rewrite /W adjmxM /Ut adjmxK !mulmxA.
  have Hkey := mapf_mx_unique f HWu Hspec2.
  have Hkey2 : W^*t *m diag_mx (map_mx f (spectral_diag A)) *m W
             = U *m sqrtmx A *m Ut.
    by rewrite /W adjmxM /Ut adjmxK Hmap !mulmxA.
  by rewrite sqrtmx_mapfE -Hkey Hkey2.
Qed.

(* Uhlmann/Gram route: mxswap preserves PSD.              *)
(* Needed for `sqrtmx_mxswap` + `uhlmann_fidelity_ptrace1_monotonicity`.            *)
(* mxswap_psdmx *)
(* infra: no tex label — fundamental & reusable matrix permutation fact. *)
(* path: utils:mxswap_psdmx -> eur:ucr_pure_smooth -> *)
(*   eur:entropic_uncertainty_relation -> *)
(*   eur:entropic_uncertainty_relation -> *)
(*   bb84:entropic_uncertainty_relation_bb84 -> bb84:bb84_secret *)
Lemma mxswap_psdmx {m n : nat} (A : 'M[C]_(m * n)) :
  A \is psdmx -> mxswap A \is psdmx.
Proof.
  move=> /psdmx_form [B ->].
  by rewrite -mxswap_mul -mxswap_adj form_psd.
Qed.

(* mxswap_denmx *)
(* infra: no tex label — fundamental & reusable matrix permutation fact. *)
(* path: utils:mxswap_denmx -> eur:ucr_pure_smooth -> *)
(*   eur:entropic_uncertainty_relation -> *)
(*   eur:entropic_uncertainty_relation -> *)
(*   bb84:entropic_uncertainty_relation_bb84 -> bb84:bb84_secret *)
Lemma mxswap_denmx {m n : nat} (A : 'M[C]_(m * n)) :
  A \is denmx -> mxswap A \is denmx.
Proof.
  move=> /denmxP[HA Htr].
  apply/denmxP; split.
  - exact: mxswap_psdmx.
  - by rewrite mxswap_trace.
Qed.

(* denmx_psd_re_tr_le *)
(* infra: no tex label — package the matrix subnormalized-state predicate. *)
(* path: utils:denmx_psd_re_tr_le -> bb84:stat -> bb84:bb84_secret *)
Lemma denmx_psd_re_tr_le {n : nat} (rho : 'M[C]_n) :
  rho \is psdmx -> @complex.Re R (\tr rho) <= 1 -> rho \is denmx.
Proof.
  move=> Hpsd Htr.
  apply/denmxP; split; first exact: Hpsd.
  have Hreal : \tr rho \is Num.real := ger0_real (psdmx_trace Hpsd).
  by rewrite -(RRe_real Hreal) lecR1.
Qed.

(* mxswap_den1mx *)
(* infra: no tex label — fundamental & reusable matrix permutation fact. *)
(* path: utils:mxswap_den1mx -> entropy:smooth_hmax_labelled_mx -> *)
(*   bb84:stat -> bb84:bb84_secret *)
Lemma mxswap_den1mx {m n : nat} (A : 'M[C]_(m * n)) :
  A \is den1mx -> mxswap A \is den1mx.
Proof.
  move=> /den1mxP[HA /eqP Htr].
  apply/den1mxP; split.
  - exact: mxswap_psdmx.
  - by rewrite mxswap_trace Htr.
Qed.

(* sqrtmx commutes with mxswap on PSD matrices. Proven via uniqueness: for PSD A, *)
(* P := mxswap(sqrtmx A) is PSD and P*P = mxswap(sqrtmx A * sqrtmx A) = mxswap A, *)
(* so by `sqrtmx_psd_square`, sqrtmx(P*P) = P, i.e., sqrtmx(mxswap A) = P.          *)

(* ================================================================== *)
(* PSD bounded above by trace times identity                            *)
(* ================================================================== *)

(* ================================================================== *)
(* castmx_sq lemmas                                                     *)
(* ================================================================== *)

(* path: utils:mxtrace_castmx_sq -> eur:eur_rho_XB_tr1 -> bb84:bb84_secret *)
Lemma mxtrace_castmx_sq {n n' : nat} (eq_n : n = n') (A : 'M[C]_n) :
  \tr (castmx_sq eq_n A) = \tr A.
Proof.
  by subst n'; rewrite /castmx_sq castmx_id.
Qed.

(* path: utils:castmx_sq_psdmx -> bb84:bb84_rhoZZ_passH_psd -> *)
(*   bb84:bb84_secret *)
Lemma castmx_sq_psdmx {n n' : nat} (eq_n : n = n') (A : 'M[C]_n) :
  A \is psdmx -> castmx_sq eq_n A \is psdmx.
Proof.
  by subst n'; rewrite /castmx_sq castmx_id.
Qed.

(* path: utils:castmx_unitarymx -> utils:castmx_sq_psdmx -> *)
(*   bb84:bb84_rhoZZ_passH_psd -> bb84:bb84_secret *)
Lemma castmx_unitarymx {n n' : nat} (eq_n : n = n') (A : 'M[C]_n) :
  A \is unitarymx -> castmx (eq_n, eq_n) A \is unitarymx.
Proof.
  by subst n'; rewrite castmx_id.
Qed.

(* ================================================================== *)
(* Tensor product factoring identities                                  *)
(* ================================================================== *)

Section TensorFactor.
Variable (m n p q : nat).

(* (A ⊗ B)(C ⊗ D) = (AC) ⊗ (BD) *)
(* tensmx_mul *)
(* infra: no tex label — fundamental & reusable (mathcomp-style) *)
(* consumer: tensmx_mul is used downstream by the BB84 secrecy proof. *)
(* path: utils:tensmx_mul -> bb84:stat -> bb84:bb84_secret *)
Lemma tensmx_mul (A : 'M[C]_(m, n)) (B : 'M[C]_(p, q))
    (E : 'M[C]_(n, m)) (F : 'M[C]_(q, p)) :
  (A *t B) *m (E *t F) = (A *m E) *t (B *m F).
Proof. exact: mxtens.tensmx_mul. Qed.

(* (A ⊗ B)† = A† ⊗ B† *)
(* tensmx_adj *)
(* infra: no tex label — fundamental & reusable (mathcomp-style) *)
(* consumer: tensmx_adj is used downstream by the BB84 secrecy proof. *)
(* path: utils:tensmx_adj -> utils:castmx_sq_psdmx -> *)
(*   bb84:bb84_rhoZZ_passH_psd -> bb84:bb84_secret *)
Lemma tensmx_adj (A : 'M[C]_(m, n)) (B : 'M[C]_(p, q)) :
  (A *t B)^*t = A^*t *t B^*t.
Proof. exact: adjmx_tens. Qed.

(* castmx distributes through tensor products. *)
(* castmx_tensmx *)
(* infra: no tex label — fundamental raw tensor-coordinate cast fact. *)
(* path: utils:castmx_tensmx -> bb84:eur_rho_XB_cq -> bb84:bb84_secret *)
Lemma castmx_tensmx {m1 m2 n1 n2 p1 p2 q1 q2 : nat}
    (hm : m1 = m2) (hn : n1 = n2) (hp : p1 = p2) (hq : q1 = q2)
    (A : 'M[C]_(m1, n1)) (B : 'M[C]_(p1, q1)) :
  castmx (f_equal2 muln hm hp, f_equal2 muln hn hq) (A *t B) =
  castmx (hm, hn) A *t castmx (hp, hq) B.
Proof.
  by case: m2 / hm; case: n2 / hn; case: p2 / hp; case: q2 / hq;
    rewrite !castmx_id.
Qed.

(* (kA) ⊗ B = k(A ⊗ B) *)
(* tensmxZl *)
(* infra: no tex label — fundamental & reusable (mathcomp-style) *)
(* consumer: tensmxZl is used downstream by the BB84 secrecy proof. *)
(* path: utils:tensmxZl -> entropy:hmax_mx_projected_A_app_le -> *)
(*   entropy:entropy_data_proc -> *)
(*   bb84:bb84_secret *)
Lemma tensmxZl (k : C) (A : 'M[C]_(m, n)) (B : 'M[C]_(p, q)) :
  (k *: A) *t B = k *: (A *t B).
Proof.
  by rewrite -[k *: A]addr0 (linear_tensmxr B) linear0l addr0.
Qed.

(* tr(A ⊗ B) = tr(A) * tr(B) *)
(* trace_tensmx *)
(* infra: no tex label — fundamental & reusable (mathcomp-style) *)
(* consumer: trace_tensmx is used downstream by the BB84 secrecy proof. *)
(* path: utils:trace_tensmx -> entropy:smooth_hmax_labelled_mx -> bb84:stat -> *)
(*   bb84:bb84_secret *)
Lemma trace_tensmx (A : 'M[C]_m) (B : 'M[C]_p) :
  \tr (A *t B) = \tr A * \tr B.
Proof. exact: mxtrace_tens. Qed.

End TensorFactor.

(* tuple_tensmx preserves normalized density. *)
(* tuple_tensmx_den1 *)
(* infra: no tex label -- raw matrix-level variable product-state lemma. *)
(* path: utils:tuple_tensmx_den1 -> entropy:smooth_hmax_labelled_mx -> *)
(*   bb84:stat -> bb84:bb84_secret *)
Lemma tuple_tensmx_den1 {d n : nat} (t : n.-tuple 'M[C]_d) :
  (forall i : 'I_n, tnth t i \is den1mx) ->
  tuple_tensmx t \is den1mx.
Proof.
  elim: n t => [t _|n IH t Hden].
  - apply/den1mxP; split; first exact: psdmx1.
    by apply/eqP; rewrite mxtrace1.
  - case/tupleNP: t Hden => x t Hden.
    rewrite /=.
    have Hfirst : tfirst_tuple [tuple of rcons t x] = t.
    { by apply/val_inj=> /=; rewrite tfirst_rcons. }
    rewrite Hfirst /tlast tnthN.
    have Ht_den : forall i : 'I_n, tnth t i \is den1mx.
    {
      move=> i.
      move: (Hden (widen_ord (leqnSn n) i)).
      by rewrite tnthNS.
    }
    have Hx_den : x \is den1mx.
    { by move: (Hden ord_max); rewrite tnthN. }
    have Hprod_den : tuple_tensmx t *t x \is den1mx.
    { exact: den1mx_tens (IH t Ht_den) Hx_den. }
    apply/den1mxP; split.
    + apply: castmx_sq_psdmx.
      by have /den1mxP [Hpsd _] := Hprod_den.
    + apply/eqP.
      rewrite mxtrace_castmx_sq.
      by have /den1mxP [_ /eqP ->] := Hprod_den.
Qed.

(* tuple_tensmx respects pointwise matrix multiplication. *)
(* tuple_tensmx_mul *)
(* infra: no tex label -- raw matrix-level variable product algebra. *)
(* path: utils:tuple_tensmx_mul -> entropy:smooth_hmax_labelled_mx -> *)
(*   bb84:stat -> bb84:bb84_secret *)
Lemma tuple_tensmx_mul {d n : nat} (A B : n.-tuple 'M[C]_d) :
  tuple_tensmx A *m tuple_tensmx B =
  tuple_tensmx [tuple tnth A i *m tnth B i | i < n].
Proof.
  elim: n A B => [A B|n IH A B].
  - by rewrite /= mul1mx.
  - case/tupleNP: A => a A.
    case/tupleNP: B => b B.
    pose AB := [tuple tnth A i *m tnth B i | i < n].
    have Hpoint :
        [tuple
          tnth [tuple of rcons A a] i *m
            tnth [tuple of rcons B b] i | i < n.+1] =
        [tuple of rcons AB (a *m b)].
    {
      apply: eq_from_tnth => i.
      case: (widenP i) => [|j].
      - by rewrite tnth_mktuple !tnthN.
      - rewrite tnth_mktuple.
        rewrite !tnthNS.
        by rewrite /AB tnth_mktuple.
    }
    rewrite /= Hpoint.
    have HfirstA : tfirst_tuple [tuple of rcons A a] = A.
    { by apply/val_inj=> /=; rewrite tfirst_rcons. }
    have HfirstB : tfirst_tuple [tuple of rcons B b] = B.
    { by apply/val_inj=> /=; rewrite tfirst_rcons. }
    have HfirstAB : tfirst_tuple [tuple of rcons AB (a *m b)] = AB.
    { by apply/val_inj=> /=; rewrite tfirst_rcons. }
    rewrite HfirstA HfirstB HfirstAB /tlast !tnthN.
    rewrite /castmx_sq mcextra.castmx_mul tensmx_mul IH.
    by [].
Qed.

(* path: utils:bigten_unitary -> entropy:smooth_hmax_labelled_mx -> *)
(*   bb84:stat -> bb84:bb84_secret *)
Lemma bigten_unitary {n : nat} (A : 'M[C]_n) (k : nat) :
  A \is unitarymx -> bigten A k \is unitarymx.
Proof.
  move=> HA.
  elim: k => [|k IH] /=.
  - exact: unitarymx1.
  - apply: castmx_unitarymx.
    apply: unitarymx_tens; first exact: IH.
    exact: HA.
Qed.

(* path: utils:bigten_entry_norm -> entropy:smooth_hmax_labelled_mx -> *)
(*   bb84:stat -> bb84:bb84_secret *)
Lemma bigten_entry_norm {n : nat} (A : 'M[C]_n) (k : nat) (c : R) :
  (forall i j, `|A i j| = c%:C) ->
  forall i j, `|bigten A k i j| = (c ^+ k)%:C.
Proof.
  move=> HA.
  elim: k => [|k IH] i j /=.
  - rewrite (ord1 i) (ord1 j) mxE eqxx normr1 expr0.
    by rewrite rmorph1.
  - rewrite castmxE /= esymK.
    case: (mxtens_indexP (cast_ord (expnSr n k) i)) => i0 i1.
    case: (mxtens_indexP (cast_ord (expnSr n k) j)) => j0 j1.
    rewrite tensmxE normrM IH HA.
    have -> : (c ^+ k)%:C * c%:C = (c ^+ k * c)%:C
      by rewrite rmorphM.
    by rewrite exprSr.
Qed.

(* ================================================================== *)
(* Partial trace computation helpers                                    *)
(* ================================================================== *)

Section PartialTraceComp.
Variable (m n : nat).

(* tr_A(A ⊗ B) = tr(A) * B *)
(* ptrace1_tensmx *)
(* infra: no tex label — fundamental & reusable (mathcomp-style) *)
(* consumer: ptrace1_tensmx is used downstream by the BB84 secrecy proof. *)
(* path: utils:ptrace1_tensmx -> bb84:stat -> bb84:bb84_secret *)
Lemma ptrace1_tensmx (A : 'M[C]_m) (B : 'M[C]_n) :
  ptrace1 (A *t B) = \tr A *: B.
Proof.
  apply/matrixP=> i j; rewrite mxE ptrace1E.
  under eq_bigr do rewrite tensmxE.
  by rewrite -mulr_suml.
Qed.

(* tr_B(A ⊗ B) = tr(B) * A *)
(* path: utils:ptrace_tensmx -> bb84:stat -> bb84:bb84_secret *)
Lemma ptrace_tensmx (A : 'M[C]_m) (B : 'M[C]_n) :
  ptrace2 (A *t B) = \tr B *: A.
Proof.
  apply/matrixP=> i j; rewrite mxE ptrace2E1 mxswap_tens ptrace1E.
  under eq_bigr do rewrite tensmxE.
  by rewrite -mulr_suml.
Qed.

End PartialTraceComp.

(* Helper used by ptrace2_compose and ptrace2_castmx_tensmx_assoc. *)
(* mxtens_cast_assoc *)
(* infra: no tex label — fundamental & reusable (mathcomp-style) *)
(* consumer: mxtens_cast_assoc is used downstream by the BB84 secrecy proof. *)
(* path: utils:mxtens_cast_assoc -> utils:ptrace2_compose -> *)
(*   utils:gfid_cast_mx -> entropy:entropy_data_proc -> *)
(*   bb84:bb84_secret *)
Local Lemma mxtens_cast_assoc {m n p : nat}
    (a : 'I_m) (b : 'I_n) (c : 'I_p) :
  cast_ord (mulnA m n p) (mxtens_index (a, mxtens_index (b, c))) =
  mxtens_index (mxtens_index (a, b), c).
Proof.
  apply/val_inj => /=.
  by rewrite mulnDl mulnA addnA.
Qed.

(* Tracing out the right-most factor of 'M_((m*n)*p) by first         *)
(* reshape-to-(m*(n*p))-then-ptrace2 equals ptrace2∘ptrace2.           *)
(* ptrace2_compose *)
(* infra: no tex label — fundamental & reusable (mathcomp-style) *)
(* consumer: ptrace2_compose is used downstream by the BB84 secrecy proof. *)
(* path: utils:ptrace2_compose -> utils:gfid_cast_mx -> *)
(*   entropy:entropy_data_proc -> *)
(*   bb84:bb84_secret *)
Lemma ptrace2_compose {m n p : nat} (A : 'M[C]_((m * n) * p)) :
  ptrace2 (castmx (esym (mulnA m n p), esym (mulnA m n p)) A)
  = ptrace2 (ptrace2 A).
Proof.
  have ptrace2E : forall s t (B : 'M[C]_(s * t)) r1 r2,
    (ptrace2 B) r1 r2 = \sum_k B (mxtens_index (r1, k)) (mxtens_index (r2, k)).
  { move=> s t B r1 r2; rewrite ptrace2E1 ptrace1E.
    by apply: eq_bigr => k _; rewrite mxE !mxtens_indexK. }
  apply/matrixP => i j.
  rewrite ptrace2E.
  transitivity (\sum_(k : 'I_n) \sum_(k2 : 'I_p)
    A (mxtens_index (mxtens_index (i, k), k2))
      (mxtens_index (mxtens_index (j, k), k2))).
  { rewrite (reindex (@mxtens_index n p)) /=.
    2:{ exists (@mxtens_unindex n p) => k /=;
        by rewrite ?(mxtens_indexK, mxtens_unindexK) -?surjective_pairing. }
    rewrite pair_bigV /=.
    apply: eq_bigr => k1 _; apply: eq_bigr => k2 _.
    by rewrite castmxE /= esymK !mxtens_cast_assoc. }
  rewrite ptrace2E.
  by apply: eq_bigr => k1 _; rewrite ptrace2E.
Qed.

(* ptrace1 and ptrace2 on disjoint registers commute up to an             *)
(* associativity castmx reshape. Used by rho_ZC_slot_purif_ptrace2_mx.    *)
(* ptrace2_ptrace1_commute *)
(* infra: no tex label — fundamental & reusable (mathcomp-style) *)
(* consumer: ptrace2_ptrace1_commute is used downstream by the BB84 secrecy proof. *)
(* path: utils:ptrace2_ptrace1_commute -> *)
(*   utils:rho_ZC_slot_purif_ptrace2_mx -> *)
(*   eur:smooth_hmax_mx_rho_ZC_purif_dpi -> *)
(*   eur:entropic_uncertainty_relation -> *)
(*   eur:entropic_uncertainty_relation -> *)
(*   bb84:entropic_uncertainty_relation_bb84 -> bb84:bb84_secret *)
Lemma ptrace2_ptrace1_commute {a b c d : nat}
    (X : 'M[C]_((a * b) * (c * d)))
    (e : ((a * b) * (c * d) = (a * b) * c * d)%N) :
  ptrace2 (ptrace1 X) = ptrace1 (ptrace2 (castmx (e, e) X)).
Proof.
  have ptrace2E : forall s t (B : 'M[C]_(s * t)) r1 r2,
    (ptrace2 B) r1 r2 = \sum_k0 B (mxtens_index (r1, k0)) (mxtens_index (r2, k0)).
  { move=> s t B r1 r2; rewrite ptrace2E1 ptrace1E.
    by apply: eq_bigr => k0 _; rewrite mxE !mxtens_indexK. }
  have He : e = mulnA (a*b) c d by apply: eq_irrelevance.
  apply/matrixP => i j.
  rewrite ptrace2E ptrace1E.
  under eq_bigr do rewrite ptrace1E.
  rewrite exchange_big /=.
  apply: eq_bigr => k _.
  rewrite ptrace2E.
  apply: eq_bigr => r _.
  rewrite castmxE /=.
  rewrite -[mxtens_index (mxtens_index (k, i), r)]mxtens_cast_assoc.
  rewrite -[mxtens_index (mxtens_index (k, j), r)]mxtens_cast_assoc.
  by rewrite He !cast_ordK.
Qed.

(* castmx(mulnA m p q) (A1 *t 1_(p*q)) = (A1 *t 1_p) *t 1_q.              *)
(* tensmx_1_assoc *)
(* infra: no tex label — fundamental & reusable (mathcomp-style) *)
(* consumer: tensmx_1_assoc is used downstream by the BB84 secrecy proof. *)
(* path: utils:tensmx_1_assoc -> utils:rho_ZC_slot_purif_ptrace2_mx -> *)
(*   eur:smooth_hmax_mx_rho_ZC_purif_dpi -> *)
(*   eur:entropic_uncertainty_relation -> *)
(*   eur:entropic_uncertainty_relation -> *)
(*   bb84:entropic_uncertainty_relation_bb84 -> bb84:bb84_secret *)
Lemma tensmx_1_assoc {m n p q : nat} (A : 'M[C]_(m, n)) :
  castmx (mulnA m p q, mulnA n p q) (A *t (1%:M : 'M[C]_(p * q)))
  = (A *t (1%:M : 'M[C]_p)) *t (1%:M : 'M[C]_q).
Proof.
  apply/matrixP => i j.
  case: (mxtens_indexP i) => i12 i3.
  case: (mxtens_indexP j) => j12 j3.
  rewrite tensmxE.
  case: (mxtens_indexP i12) => i1 i2.
  case: (mxtens_indexP j12) => j1 j2.
  rewrite tensmxE !mxE castmxE.
  have Hcast_row : cast_ord (esym (mulnA m p q))
      (mxtens_index (mxtens_index (i1, i2), i3))
      = mxtens_index (i1, mxtens_index (i2, i3)).
  { by apply: val_inj => /=; rewrite mulnDl mulnA addnA. }
  have Hcast_col : cast_ord (esym (mulnA n p q))
      (mxtens_index (mxtens_index (j1, j2), j3))
      = mxtens_index (j1, mxtens_index (j2, j3)).
  { by apply: val_inj => /=; rewrite mulnDl mulnA addnA. }
  rewrite Hcast_row Hcast_col tensmxE mxE.
  rewrite (inj_eq (can_inj (@mxtens_indexK _ _))) -pair_eqE /=.
  by case: (i2 == j2); case: (i3 == j3);
    rewrite ?andbT ?andbF ?mulr0 ?mulr1.
Qed.

(* castmx(mulnA m p r) (A *t (B *t C)) = (A *t B) *t C. *)
(* tensmx_assoc *)
(* infra: no tex label — raw tensor-coordinate associativity. *)
(* path: utils:tensmx_assoc -> entropy:smooth_hmax_labelled_mx -> bb84:stat -> *)
(*   bb84:bb84_secret *)
Lemma tensmx_assoc {m n p q r s : nat}
    (A : 'M[C]_(m, n)) (B : 'M[C]_(p, q)) (D : 'M[C]_(r, s)) :
  castmx (mulnA m p r, mulnA n q s) (A *t (B *t D)) =
  (A *t B) *t D.
Proof.
  apply/matrixP => i j.
  case: (mxtens_indexP i) => i12 i3.
  case: (mxtens_indexP j) => j12 j3.
  rewrite tensmxE.
  case: (mxtens_indexP i12) => i1 i2.
  case: (mxtens_indexP j12) => j1 j2.
  rewrite tensmxE castmxE.
  have Hcast_row : cast_ord (esym (mulnA m p r))
      (mxtens_index (mxtens_index (i1, i2), i3))
      = mxtens_index (i1, mxtens_index (i2, i3)).
  { by apply: val_inj => /=; rewrite mulnDl mulnA addnA. }
  have Hcast_col : cast_ord (esym (mulnA n q s))
      (mxtens_index (mxtens_index (j1, j2), j3))
      = mxtens_index (j1, mxtens_index (j2, j3)).
  { by apply: val_inj => /=; rewrite mulnDl mulnA addnA. }
  by rewrite Hcast_row Hcast_col !tensmxE mulrA.
Qed.

(* Multiplication distributes componentwise over left-associated triple
   tensor products. *)
(* tensmx3_mul *)
(* infra: no tex label — raw tensor-coordinate multiplication utility. *)
Lemma tensmx3_mul {m1 n1 p1 m2 n2 p2 m3 n3 p3 : nat}
    (A1 : 'M[C]_(m1, n1)) (A2 : 'M[C]_(m2, n2))
    (A3 : 'M[C]_(m3, n3))
    (B1 : 'M[C]_(n1, p1)) (B2 : 'M[C]_(n2, p2))
    (B3 : 'M[C]_(n3, p3)) :
  ((A1 *t A2) *t A3) *m ((B1 *t B2) *t B3) =
  ((A1 *m B1) *t (A2 *m B2)) *t (A3 *m B3).
Proof.
  apply/matrixP => i j.
  case: (mxtens_indexP i) => i12 i3.
  case: (mxtens_indexP j) => j12 j3.
  case: (mxtens_indexP i12) => i1 i2.
  case: (mxtens_indexP j12) => j1 j2.
  transitivity
    (\sum_(k1 : 'I_n1) \sum_(k2 : 'I_n2) \sum_(k3 : 'I_n3)
      (((A1 i1 k1 * A2 i2 k2) * A3 i3 k3) *
       ((B1 k1 j1 * B2 k2 j2) * B3 k3 j3))).
  {
    rewrite !mxE.
    rewrite (reindex (@mxtens_index (n1 * n2) n3)) /=.
    2:{ exists (@mxtens_unindex (n1 * n2) n3) => k /=;
        by rewrite ?(mxtens_indexK, mxtens_unindexK)
          -?surjective_pairing. }
    rewrite pair_bigV /=.
    rewrite (reindex (@mxtens_index n1 n2)) /=.
    2:{ exists (@mxtens_unindex n1 n2) => k /=;
        by rewrite ?(mxtens_indexK, mxtens_unindexK)
          -?surjective_pairing. }
    rewrite pair_bigV /=.
    apply: eq_bigr => k1 _.
    apply: eq_bigr => k2 _.
    apply: eq_bigr => k3 _.
    by rewrite !tensmxE.
  }
  rewrite !mxE ?tensmxE !mxtens_indexK /=.
  rewrite [X in _ = X * _]mulr_suml.
  rewrite mulr_suml.
  apply: eq_bigr => k1 _.
  rewrite [X in _ = X * _]mulr_sumr.
  rewrite mulr_suml.
  apply: eq_bigr => k2 _.
  rewrite mulr_sumr.
  apply: eq_bigr => k3 _.
  have Hmul (a b c d e f : C) :
      a * (b * (c * (d * (e * f)))) =
      a * (d * (b * (e * (c * f)))).
  {
    rewrite [c * (d * _)]mulrCA.
    rewrite [b * (d * _)]mulrCA.
    rewrite [c * (e * _)]mulrCA.
    by [].
  }
  rewrite -!mulrA.
  exact: Hmul.
Qed.

(* Distribute castmx through a triple matrix product. *)
(* castmx_mulmx3 *)
(* infra: no tex label — fundamental & reusable (mathcomp-style) *)
(* consumer: castmx_mulmx3 is used downstream by the BB84 secrecy proof. *)
(* path: utils:castmx_mulmx3 -> bb84:eur_rho_XB_cq -> bb84:bb84_secret *)
Lemma castmx_mulmx3 {m1 m2 n1 n2 : nat} (hm : m1 = m2) (hn : n1 = n2)
    (A : 'M[C]_(m1, n1)) (B : 'M[C]_n1) (D : 'M[C]_(n1, m1)) :
  castmx (hm, hm) (A *m B *m D) =
  castmx (hm, hn) A *m castmx (hn, hn) B *m castmx (hn, hm) D.
Proof.
  by case: m2 / hm; case: n2 / hn; rewrite !castmx_id.
Qed.

(* tensmx_sumr *)
(* infra: no tex label -- tensor product distributes over finite sums *)
(* path: utils:tensmx_sumr -> utils:castmx_mulmx3 -> bb84:eur_rho_XB_cq -> *)
(*   bb84:bb84_secret *)
Lemma tensmx_sumr {m n p q : nat} {I : finType}
    (A : 'M[C]_(m, n)) (P : pred I) (B : I -> 'M[C]_(p, q)) :
  A *t (\sum_(i | P i) B i) = \sum_(i | P i) (A *t B i).
Proof.
  apply/matrixP => i j.
  case: (mxtens_indexP i) => i1 i2.
  case: (mxtens_indexP j) => j1 j2.
  rewrite !tensmxE.
  rewrite [RHS]summxE.
  under [RHS]eq_bigr do rewrite tensmxE.
  by rewrite summxE mulr_sumr.
Qed.

Lemma tensmx_suml {m n p q : nat} {I : finType}
    (P : pred I) (A : I -> 'M[C]_(m, n)) (B : 'M[C]_(p, q)) :
  (\sum_(i | P i) A i) *t B = \sum_(i | P i) (A i *t B).
Proof.
  apply/matrixP => i j.
  case: (mxtens_indexP i) => i1 i2.
  case: (mxtens_indexP j) => j1 j2.
  rewrite !tensmxE.
  rewrite [RHS]summxE.
  under [RHS]eq_bigr do rewrite tensmxE.
  by rewrite summxE mulr_suml.
Qed.

(* `delta_mx i i` is PSD via form_psd on the standard basis column.      *)
(* delta_mx_ii_psdmx *)
(* infra: no tex label — fundamental & reusable (mathcomp-style) *)
(* consumer: delta_mx_ii_psdmx is used downstream by the BB84 secrecy proof. *)
(* path: utils:delta_mx_ii_psdmx -> bb84:stat -> bb84:bb84_secret *)
Lemma delta_mx_ii_psdmx {n : nat} (i : 'I_n) :
  (delta_mx i i : 'M[C]_n) \is psdmx.
Proof.
  have := form_psd (delta_mx i (0 : 'I_1) : 'M[C]_(n, 1)).
  by rewrite adjmx_delta mul_delta_mx.
Qed.

(* sqrt(delta_mx i i) = delta_mx i i for computational-basis projectors. *)
(* sqrtmx_delta_mx_ii *)
(* infra: no tex label -- fundamental & reusable (mathcomp-style) *)
(* path: utils:sqrtmx_delta_mx_ii -> entropy:smooth_hmax_labelled_mx -> *)
(*   bb84:stat -> bb84:bb84_secret *)
Lemma sqrtmx_delta_mx_ii {n : nat} (i : 'I_n) :
  sqrtmx (delta_mx i i : 'M[C]_n) = delta_mx i i.
Proof.
  have Hsq :
      (delta_mx i i : 'M[C]_n) *m delta_mx i i = delta_mx i i.
  { exact: (@mul_delta_mx C n n n i i i). }
  by rewrite -Hsq sqrtmx_psd_square ?delta_mx_ii_psdmx.
Qed.

(* Sandwiching any matrix between basis projectors keeps one entry. *)
(* delta_mx_sandwich *)
(* infra: no tex label -- fundamental and reusable basis algebra. *)
(* path: utils:delta_mx_sandwich -> entropy:smooth_hmax_labelled_mx -> *)
(*   bb84:stat -> bb84:bb84_secret *)
Lemma delta_mx_sandwich {n : nat} (A : 'M[C]_n) (x z : 'I_n) :
  delta_mx x x *m A *m delta_mx z z = A x z *: delta_mx x z.
Proof.
  rewrite -mulmxA.
  apply/matrixP=> i j.
  rewrite !mcextra.delta_mx_mulEr !mcextra.delta_mx_mulEl !mxE.
  rewrite (eq_sym x i) (eq_sym z j).
  by case: (i == x); case: (j == z); simpc.
Qed.

(* Tensoring matrix units gives the matrix unit at the tensor index. *)
(* delta_mx_tens *)
(* infra: no tex label -- fundamental and reusable basis algebra. *)
(* path: utils:delta_mx_tens -> entropy:smooth_hmax_labelled_mx -> *)
(*   bb84:stat -> bb84:bb84_secret *)
Lemma delta_mx_tens {m n : nat}
    (i k : 'I_m) (j l : 'I_n) :
  (delta_mx i k : 'M[C]_m) *t (delta_mx j l : 'M[C]_n) =
  delta_mx (mxtens_index (i, j)) (mxtens_index (k, l)).
Proof.
  apply/matrix_tenP=> a b c d.
  rewrite tensmxE !mxE.
  rewrite !(inj_eq (@mxtens_index_inj _ _)).
  rewrite -!pair_eqE /=.
  by do ! case: eqP; rewrite ?mulr0 ?mulr1 ?mul0r ?mul1r.
Qed.

Lemma mx_delta_basis {m n : nat} (A : 'M[C]_(m, n)) :
  A = \sum_(i : 'I_m) \sum_(j : 'I_n) A i j *: delta_mx i j.
Proof.
  apply/matrixP => i j.
  rewrite summxE (bigD1 i) //=.
  rewrite [X in _ + X]big1; last first.
  {
    move=> i' Hi'.
    rewrite summxE.
    apply: big1 => j' _.
    have Hii' : i != i' by rewrite eq_sym.
    by rewrite !mxE (negbTE Hii') andFb mulr0.
  }
  rewrite addr0 summxE (bigD1 j) //=.
  rewrite [X in _ + X]big1; last first.
  {
    move=> j' Hj'.
    have Hjj' : j != j' by rewrite eq_sym.
    by rewrite !mxE eqxx (negbTE Hjj') andbF mulr0.
  }
  by rewrite addr0 /delta_mx !mxE !eqxx /= ?mul1r ?mulr1.
Qed.

(* path: utils:unitary_delta_projector_psdmx -> *)
(*   entropy:smooth_hmax_labelled_mx -> bb84:stat -> bb84:bb84_secret *)
Lemma unitary_delta_projector_psdmx {n : nat} (U : 'M[C]_n)
    (x : 'I_n) :
  U^*t *m delta_mx x x *m U \is psdmx.
Proof.
  have Hpsd := @psdmx_bimap_closed_gen _ _ (delta_mx x x) _ U^*t
    (delta_mx_ii_psdmx x).
  by move: Hpsd; rewrite adjmxK.
Qed.

(* path: utils:unitary_delta_projector_idem -> *)
(*   entropy:smooth_hmax_labelled_mx -> bb84:stat -> bb84:bb84_secret *)
Lemma unitary_delta_projector_idem {n : nat} (U : 'M[C]_n) (x : 'I_n) :
  U \is unitarymx ->
  (U^*t *m delta_mx x x *m U) *m
    (U^*t *m delta_mx x x *m U) =
  U^*t *m delta_mx x x *m U.
Proof.
  move=> HU.
  rewrite -!mulmxA.
  rewrite [U *m (U^*t *m _)]mulmxA.
  rewrite (unitarymxK HU) mul1mx.
  rewrite [delta_mx x x *m (delta_mx x x *m U)]mulmxA.
  by rewrite mul_delta_mx.
Qed.

(* path: utils:sqrtmx_unitary_delta_projector -> *)
(*   entropy:smooth_hmax_labelled_mx -> bb84:stat -> bb84:bb84_secret *)
Lemma sqrtmx_unitary_delta_projector {n : nat} (U : 'M[C]_n)
    (x : 'I_n) :
  U \is unitarymx ->
  sqrtmx (U^*t *m delta_mx x x *m U) =
  U^*t *m delta_mx x x *m U.
Proof.
  move=> HU.
  have Hsq := unitary_delta_projector_idem x HU.
  by rewrite -Hsq sqrtmx_psd_square ?unitary_delta_projector_psdmx.
Qed.

(* \tr (delta_mx i i) = 1.                                                 *)
(* tr_delta_mx_ii *)
(* infra: no tex label — fundamental & reusable (mathcomp-style) *)
(* consumer: tr_delta_mx_ii is used downstream by the BB84 secrecy proof. *)
(* path: utils:tr_delta_mx_ii -> eur:rho_XB_subden -> eur:eur_rho_XB_psd -> *)
(*   bb84:bb84_secret *)
Lemma tr_delta_mx_ii {n : nat} (i : 'I_n) :
  \tr (delta_mx i i : 'M[C]_n) = 1.
Proof.
  rewrite /mxtrace (bigD1 i)//= mxE eqxx/= big1 ?addr0//=.
  by move=> j Hij; rewrite mxE (negbTE Hij).
Qed.

(* ptrace2_castmx_tensmx_assoc *)
(* infra: no tex label — fundamental & reusable (mathcomp-style) *)
(* consumer: ptrace2_castmx_tensmx_assoc is used downstream by the BB84 secrecy proof. *)
(* path: utils:ptrace2_castmx_tensmx_assoc -> eur:ucr_pure_smooth -> *)
(*   eur:entropic_uncertainty_relation -> *)
(*   eur:entropic_uncertainty_relation -> *)
(*   bb84:entropic_uncertainty_relation_bb84 -> bb84:bb84_secret *)
Lemma ptrace2_castmx_tensmx_assoc
    {k n p : nat} (M : 'M[C]_k) (Y : 'M[C]_(n * p)) :
  ptrace2 (castmx (mulnA k n p, mulnA k n p) (M *t Y)) = M *t ptrace2 Y.
Proof.
  have ptrace2E : forall s t (B : 'M[C]_(s * t)) r1 r2,
    (ptrace2 B) r1 r2 = \sum_k0 B (mxtens_index (r1, k0)) (mxtens_index (r2, k0)).
  { move=> s t B r1 r2; rewrite ptrace2E1 ptrace1E.
    by apply: eq_bigr => k0 _; rewrite mxE !mxtens_indexK. }
  apply/matrixP => i j.
  case: (mxtens_indexP i) => im in_.
  case: (mxtens_indexP j) => jm jn.
  rewrite ptrace2E tensmxE ptrace2E mulr_sumr.
  apply: eq_bigr => r _.
  rewrite castmxE /=.
  rewrite -[X in (M *t Y) (cast_ord _ X) _]mxtens_cast_assoc.
  rewrite -[X in (M *t Y) _ (cast_ord _ X)]mxtens_cast_assoc.
  by rewrite !cast_ordK tensmxE.
Qed.

(* Partial-trace qualifier preservation. *)
(* path: utils:ptrace2_denmx -> eur:ucr_pure_smooth -> *)
(*   eur:entropic_uncertainty_relation -> *)
(*   eur:entropic_uncertainty_relation -> *)
(*   bb84:entropic_uncertainty_relation_bb84 -> bb84:bb84_secret *)
Lemma ptrace2_denmx {n m : nat} (M : 'M[C]_(n * m)) :
  M \is denmx -> ptrace2 M \is denmx.
Proof.
  by move=>/denmxP [P Ptr]; apply/denmxP;
     split; [exact: ptrace2_psd|rewrite -tr_ptrace2].
Qed.

(* ptrace1_denmx *)
(* infra: no tex label — fundamental & reusable (mathcomp-style) *)
(* path: utils:ptrace1_denmx -> entropy:smooth_hmax_labelled_mx -> *)
(*   bb84:stat -> bb84:bb84_secret *)
Lemma ptrace1_denmx {n m : nat} (M : 'M[C]_(n * m)) :
  M \is denmx -> ptrace1 M \is denmx.
Proof.
  by move=>/denmxP [P Ptr]; apply/denmxP;
     split; [exact: ptrace1_psd|rewrite -tr_ptrace1].
Qed.

(* trnorm(M) = tr(M) for PSD M *)

(* ================================================================== *)
(* Trace cyclic collapse for the 6-fold ABAABA pattern.                *)
(* math: \tr(A·B·A·A·B·A) = \tr((A·A)·B·(A·A)·B).                      *)
(* Consumers (≥2): uniform_to_collision Hhoelder, privacy_amp          *)
(* (symmetric cyclic collapse on collision-entropy expansion).         *)
(* ================================================================== *)

(* mxtrace_abaaba_collapse *)
(* infra: no tex label — fundamental & reusable (mathcomp-style) *)
(* consumer: mxtrace_abaaba_collapse is used downstream by the BB84 secrecy proof. *)
(* path: utils:mxtrace_abaaba_collapse -> lhl:uniform_collision_bound -> *)
(*   bb84:privacy_amplification -> bb84:bb84_secret *)
Lemma mxtrace_abaaba_collapse (n : nat) (A B : 'M[C]_n) :
  \tr (A *m B *m A *m A *m B *m A) =
  \tr ((A *m A) *m B *m (A *m A) *m B).
Proof.
  rewrite mxtrace_mulC.
  by rewrite !mulmxA.
Qed.

(* ================================================================== *)
(* System swap: sigma23 cancellation and mxswap23 involution           *)
(* ================================================================== *)

(* sigma23K *)
(* infra: no tex label — fundamental & reusable (mathcomp-style) *)
(* path: utils:sigma23K -> utils:fid_mxswap23 -> *)
(*   utils:fid_ptr_mono_mxswap23 -> entropy:hmax_mx_projected_A_app_le -> *)
(*   entropy:entropy_data_proc -> *)
(*   bb84:bb84_secret *)
Lemma sigma23K {a b c : nat} : cancel (@sigma23 a b c) (@sigma23 a c b).
Proof.
  move=> i; rewrite /sigma23 !mxtens_indexK.
  by rewrite -surjective_pairing mxtens_unindexK
    -surjective_pairing mxtens_unindexK.
Qed.

(* sigma23_inj *)
(* infra: no tex label — fundamental & reusable (mathcomp-style) *)
(* path: utils:sigma23_inj -> entropy:smooth_hmax_labelled_mx -> bb84:stat -> *)
(*   bb84:bb84_secret *)
Lemma sigma23_inj {a b c : nat} : injective (@sigma23 a b c).
Proof. exact: (can_inj sigma23K). Qed.

(* sigma23_tens *)
(* infra: no tex label — fundamental & reusable (mathcomp-style) *)
(* path: utils:sigma23_tens -> utils:ptr2_mxswap23_tens_mx -> *)
(*   entropy:hmax_mx_projected_A_app_le -> entropy:entropy_data_proc -> *)
(*   bb84:bb84_secret *)
Lemma sigma23_tens {a b c : nat} (i1 : 'I_a) (i2 : 'I_c) (i3 : 'I_b) :
  @sigma23 a b c (mxtens_index (mxtens_index (i1, i2), i3)) =
  mxtens_index (mxtens_index (i1, i3), i2).
Proof.
  by rewrite /sigma23 !mxtens_indexK.
Qed.

(* mxswap23E *)
(* infra: no tex label — fundamental & reusable (mathcomp-style) *)
(* path: utils:mxswap23E -> utils:mxswap23_psdmx -> *)
(*   entropy:hmax_mx_projected_A_app_le -> entropy:entropy_data_proc -> *)
(*   bb84:bb84_secret *)
Lemma mxswap23E {a b c : nat}
    (rho : 'M[C]_((a * b) * c)) (i j : 'I_((a * c) * b)) :
  mxswap23 rho i j = rho (sigma23 i) (sigma23 j).
Proof.
  by rewrite /mxswap23 mxE.
Qed.

(* mxswap23_trace *)
(* infra: no tex label — fundamental & reusable (mathcomp-style) *)
(* path: utils:mxswap23_trace -> eur:ucr_pure_smooth -> *)
(*   eur:entropic_uncertainty_relation -> *)
(*   eur:entropic_uncertainty_relation -> *)
(*   bb84:entropic_uncertainty_relation_bb84 -> bb84:bb84_secret *)
Lemma mxswap23_trace {a b c : nat} (rho : 'M[C]_((a * b) * c)) :
  \tr (mxswap23 rho) = \tr rho.
Proof.
  rewrite /mxtrace (reindex (@sigma23 a b c)).
  - by apply: eq_bigr=> i _; rewrite mxswap23E.
  - exists (@sigma23 a c b)=> i _; exact: sigma23K.
Qed.

(* mxswap23_psdmx *)
(* infra: no tex label — fundamental & reusable (mathcomp-style) *)
(* path: utils:mxswap23_psdmx -> entropy:hmax_mx_projected_A_app_le -> *)
(*   entropy:entropy_data_proc -> *)
(*   bb84:bb84_secret *)
Lemma mxswap23_psdmx {a b c : nat} (rho : 'M[C]_((a * b) * c)) :
  rho \is psdmx -> mxswap23 rho \is psdmx.
Proof.
  move/psdmx_form=> [B ->].
  set D := \matrix_(i, k) B (@sigma23 a b c i) k :
    'M[C]_((a * c) * b, _).
  suff -> : mxswap23 (B *m B^*t) = D *m D^*t by exact: form_psd.
  apply/matrixP=> i j; rewrite mxswap23E !mxE.
  by apply: eq_bigr=> k _; rewrite !mxE.
Qed.

(* mxswap23_denmx *)
(* infra: no tex label — fundamental & reusable (mathcomp-style) *)
(* path: utils:mxswap23_denmx -> eur:ucr_pure_smooth -> *)
(*   eur:entropic_uncertainty_relation -> *)
(*   eur:entropic_uncertainty_relation -> *)
(*   bb84:entropic_uncertainty_relation_bb84 -> bb84:bb84_secret *)
Lemma mxswap23_denmx {a b c : nat} (rho : 'M[C]_((a * b) * c)) :
  rho \is denmx -> mxswap23 rho \is denmx.
Proof.
  move/denmxP=> [Hpsd Htr]; apply/denmxP; split.
  - exact: mxswap23_psdmx.
  - by rewrite mxswap23_trace.
Qed.

(* mxswap23_den1mx *)
(* infra: no tex label — fundamental & reusable (mathcomp-style) *)
(* path: utils:mxswap23_den1mx -> entropy:smooth_hmax_labelled_mx -> *)
(*   bb84:stat -> bb84:bb84_secret *)
Lemma mxswap23_den1mx {a b c : nat} (rho : 'M[C]_((a * b) * c)) :
  rho \is den1mx -> mxswap23 rho \is den1mx.
Proof.
  move/den1mxP=> [Hpsd /eqP Htr]; apply/den1mxP; split.
  - exact: mxswap23_psdmx.
  - by rewrite mxswap23_trace Htr.
Qed.

(* mxswap23 applied twice recovers the original matrix *)
(* mxswap23K *)
(* infra: no tex label — fundamental & reusable (mathcomp-style) *)
(* path: utils:mxswap23K -> entropy:smooth_hmax_labelled_mx -> bb84:stat -> *)
(*   bb84:bb84_secret *)
Lemma mxswap23K {a b c : nat} (rho : 'M[C]_((a * b) * c)) :
  mxswap23 (mxswap23 rho) = rho.
Proof.
  apply/matrixP=> i j.
  by rewrite mxswap23E mxswap23E !sigma23K.
Qed.

(* ptr2_mxswap23_tens_mx *)
(* infra: no tex label — fundamental matrix middle-register trace identity *)
(* math: Tr_B(swap_{BC}(M_AB ⊗ S_C)) = Tr_B(M_AB) ⊗ S_C. *)
(* path: utils:ptr2_mxswap23_tens_mx -> entropy:hmax_mx_projected_A_app_le -> *)
(*   entropy:entropy_data_proc -> *)
(*   bb84:bb84_secret *)
Lemma ptr2_mxswap23_tens_mx {a b c : nat}
    (M : 'M[C]_(a * b)) (S : 'M[C]_c) :
  ptrace2 (mxswap23 (M *t S)) = ptrace2 M *t S.
Proof.
  have ptrace2E' :
      forall s t (X : 'M[C]_(s * t)) r1 r2,
        ptrace2 X r1 r2 =
        \sum_k X (mxtens_index (r1, k)) (mxtens_index (r2, k)).
  { move=> s t X r1 r2; rewrite ptrace2E1 ptrace1E.
    by apply: eq_bigr=> k _; rewrite mxE !mxtens_indexK. }
  apply/matrixP=> i j.
  case: (mxtens_indexP i)=> ia ic.
  case: (mxtens_indexP j)=> ja jc.
  rewrite ptrace2E' tensmxE.
  under eq_bigr=> k _ do rewrite mxswap23E !sigma23_tens tensmxE.
  rewrite -mulr_suml.
  by rewrite (ptrace2E' a b M ia ja).
Qed.

(* setDU_r *)
(* infra: no tex label — fundamental & reusable (mathcomp-style) *)
(* consumer: setDU_r is used downstream by the BB84 secrecy proof. *)
(* path: utils:setDU_r -> entropy:entropy_data_proc -> *)
(*   bb84:bb84_secret *)
Lemma setDU_r (L : finType) (A B : {set L}) :
  [disjoint A & B] -> (A :|: B) :\: B = A.
Proof.
  move=> disAB; apply/setP=> x; rewrite !inE.
  case Bx: (x \in B); rewrite ?andbF ?andbT.
    apply/esym/negP=> Ax; move/disjoint_setI0/setP/(_ x): disAB.
    by rewrite !inE Ax Bx.
  by rewrite orbF.
Qed.

(* setDU_l *)
(* infra: no tex label — fundamental & reusable (mathcomp-style) *)
(* consumer: setDU_l is used downstream by the BB84 secrecy proof. *)
(* path: utils:setDU_l -> lhl:min_coll_bound -> *)
(*   bb84:privacy_amplification -> bb84:bb84_secret *)
Lemma setDU_l (L : finType) (A B : {set L}) :
  [disjoint A & B] -> (A :|: B) :\: A = B.
Proof.
  move=> disAB; apply/setP=> x; rewrite !inE.
  case Ax: (x \in A); rewrite ?andbF ?andbT.
    apply/esym/negP=> Bx; move/disjoint_setI0/setP/(_ x): disAB.
    by rewrite !inE Ax Bx.
  by [].
Qed.

(* setDU3_C *)
(* infra: no tex label — fundamental & reusable (mathcomp-style) *)
(* consumer: setDU3_C is used downstream by the BB84 secrecy proof. *)
(* path: utils:setDU3_C -> utils:ptrace_cast3C_sdot_right -> *)
(*   entropy:entropy_data_proc -> *)
(*   bb84:bb84_secret *)
Lemma setDU3_C (L : finType) (A B C : {set L}) :
  [disjoint A & C] -> [disjoint B & C] ->
  (A :|: B :|: C) :\: C = A :|: B.
Proof.
  move=> disAC disBC; apply/setP=> x; rewrite !inE.
  case Cx: (x \in C); rewrite ?andbF ?andbT.
    apply/esym/negP=> /orP[Ax|Bx].
      by move/disjoint_setI0/setP/(_ x): disAC; rewrite !inE Ax Cx.
    by move/disjoint_setI0/setP/(_ x): disBC; rewrite !inE Bx Cx.
  by rewrite orbF.
Qed.

(* setDU3_B *)
(* infra: no tex label — fundamental & reusable (mathcomp-style) *)
(* consumer: setDU3_B is used downstream by the BB84 secrecy proof. *)
(* path: utils:setDU3_B -> utils:ptrace_cast3B_B_proj_le -> *)
(*   entropy:smoothing_support_hmax -> entropy:smooth_iso_hmax -> *)
(*   entropy:entropy_data_proc -> *)
(*   bb84:bb84_secret *)
Lemma setDU3_B (L : finType) (A B C : {set L}) :
  [disjoint A & B] -> [disjoint B & C] ->
  (A :|: B :|: C) :\: B = A :|: C.
Proof.
  move=> disAB disBC; apply/setP=> x; rewrite !inE.
  case Bx: (x \in B); rewrite ?andbF ?andbT.
    apply/esym/negP=> /orP[Ax|Cx].
      by move/disjoint_setI0/setP/(_ x): disAB; rewrite !inE Ax Bx.
    by move/disjoint_setI0/setP/(_ x): disBC; rewrite !inE Bx Cx.
  by rewrite orbF.
Qed.

(* setDU3_A *)
(* infra: no tex label — fundamental & reusable (mathcomp-style) *)
(* consumer: setDU3_A is used downstream by the BB84 secrecy proof. *)
(* path: utils:setDU3_A -> entropy:smooth_hmax_labelled_mx -> bb84:stat -> *)
(*   bb84:bb84_secret *)
Lemma setDU3_A (L : finType) (A B C : {set L}) :
  [disjoint A & B] -> [disjoint A & C] ->
  (A :|: B :|: C) :\: A = B :|: C.
Proof.
  move=> disAB disAC; apply/setP=> x; rewrite !inE.
  case Ax: (x \in A); rewrite ?andbF ?andbT.
    apply/esym/negP=> /orP[Bx|Cx].
      by move/disjoint_setI0/setP/(_ x): disAB; rewrite !inE Ax Bx.
    by move/disjoint_setI0/setP/(_ x): disAC; rewrite !inE Ax Cx.
  by rewrite -orbA.
Qed.

(* setUC_swap3 *)
(* infra: no tex label — fundamental & reusable (mathcomp-style) *)
(* consumer: setUC_swap3 is used downstream by the BB84 secrecy proof. *)
(* path: utils:setUC_swap3 -> entropy:entropy_data_proc -> *)
(*   bb84:bb84_secret *)
Lemma setUC_swap3 (L : finType) (A B C : {set L}) :
  A :|: B :|: C = A :|: C :|: B.
Proof.
  by rewrite -finset.setUA (finset.setUC B) finset.setUA.
Qed.

(* Helper: index in allpairs for pairs. *)
(* index_allpairs_pair *)
(* infra: no tex label — fundamental & reusable (mathcomp-style) *)
(* consumer: index_allpairs_pair is used downstream by the BB84 secrecy proof. *)
(* path: utils:index_allpairs_pair -> utils:setUC_swap3 -> *)
(*   entropy:entropy_data_proc -> *)
(*   bb84:bb84_secret *)
Lemma index_allpairs_pair (S T : eqType) (s : seq S) (t : seq T) (x : S) (y : T) :
  uniq s -> x \in s -> y \in t ->
  index (x, y) [seq (a, b) | a <- s, b <- t] =
  index x s * size t + index y t.
Proof.
  elim: s => [//|a s' IH] /andP[Ha Hs].
  rewrite in_cons => /orP[/eqP -> Hy | Hx Hy].
    rewrite /= eqxx index_cat.
    have Hinj : injective (pair a : T -> S * T).
      by move=> u1 u2 /(congr1 snd).
    by rewrite (@mem_map _ _ _ Hinj) Hy /= (@index_map _ _ _ Hinj).
  have Hne : x != a by apply/eqP => E; rewrite E (negPf Ha) in Hx.
  rewrite allpairs_cons index_cat.
  have -> : (x, y) \in [seq (a, b0) | b0 <- t] = false.
    apply/negP => /mapP [b0 _ /(congr1 fst) /= Hax].
    by rewrite Hax eqxx in Hne.
  rewrite size_map IH //.
  by rewrite -[a :: s']cat1s index_cat mem_seq1 (negPf Hne) /= addnA.
Qed.

(* Helper: mxvec_index and mxtens_index yield the same ordinal. *)
(* mxvec_mxtens_index *)
(* infra: no tex label — fundamental & reusable (mathcomp-style) *)
(* consumer: mxvec_mxtens_index is used downstream by the BB84 secrecy proof. *)
(* path: utils:mxvec_mxtens_index -> utils:ptrace2_outerM -> *)
(*   utils:purification_exists_in_dim -> utils:pd_gtd_bar_lb -> *)
(*   bb84:privacy_amplification -> bb84:bb84_secret *)
Lemma mxvec_mxtens_index (m n : nat) (i : 'I_m) (j : 'I_n) :
  mxvec_index i j = mxtens_index (i, j).
Proof.
  apply: val_inj => /=.
  rewrite /enum_rank enum_rank_in.unlock val_insubd.
  rewrite ifT; last by rewrite cardE index_mem mem_enum.
  rewrite enumT unlock /= index_allpairs_pair ?enum_uniq ?mem_enum //.
  by rewrite size_enum_ord !index_enum_ord.
Qed.

(* Partial trace of outer product: ptrace2(v*v^*t) = A*A^*t where A = vec_mx(v^T). *)
(* ptrace2_outerM *)
(* infra: no tex label — fundamental & reusable (mathcomp-style) *)
(* consumer: ptrace2_outerM is used downstream by the BB84 secrecy proof. *)
(* path: utils:ptrace2_outerM -> utils:purification_exists_in_dim -> *)
(*   utils:pd_gtd_bar_lb -> bb84:privacy_amplification -> *)
(*   bb84:bb84_secret *)
Lemma ptrace2_outerM {m n : nat} (v : 'cV[C]_(m * n)) :
  ptrace2 (v *m v^*t) = vec_mx (v^T) *m (vec_mx (v^T))^*t.
Proof.
  set A := vec_mx (v^T).
  rewrite ptrace2E1.
  apply/matrixP => i j; rewrite mxE /ptrace1 /= castmxE /= !mxtens_1index summxE.
  apply eq_bigr => k _.
  rewrite -mulmxA.
  rewrite tens_delta_mx1_mulEl eqxx mul1r.
  rewrite tens_delta_mx1_mulEr eqxx mul1r.
  rewrite mxE !mxtens_indexK /=.
  rewrite mxE big_ord1.
  have Hv: forall a b, v (mxtens_index (a, b)) ord0 =
    (vec_mx (v^T) : 'M_(m,n)) a b.
  { move=> a b. rewrite /vec_mx mxE /= mxE.
    by rewrite mxvec_mxtens_index. }
  rewrite Hv; congr (_ * _).
  rewrite adjmxE !mxE /= mxvec_mxtens_index //.
Qed.

(* Conjugation by contraction preserves denmx. *)
(* denmx_conj_contraction *)
(* infra: no tex label — fundamental & reusable (mathcomp-style) *)
(* consumer: denmx_conj_contraction is used downstream by the BB84 secrecy proof. *)
(* path: utils:denmx_conj_contraction -> eur:ucr_pure_smooth -> *)
(*   eur:entropic_uncertainty_relation -> *)
(*   eur:entropic_uncertainty_relation -> *)
(*   bb84:entropic_uncertainty_relation_bb84 -> bb84:bb84_secret *)
Lemma denmx_conj_contraction {m n : nat} (W : 'M[C]_(m, n))
    (rho : 'M[C]_n) :
  W^*t *m W <= 1%:M ->
  rho \is denmx -> W *m rho *m W^*t \is denmx.
Proof.
  move=> /le_lownerE_psdtr Hmon /denmxP [Hpsd Htr]; apply/denmxP; split.
  - exact: form_psdmx _ Hpsd.
  - apply: (le_trans _ Htr).
    rewrite mxtrace_mulC mulmxA.
    by move: (Hmon _ Hpsd); rewrite mul1mx.
Qed.

(* ================================================================== *)
(* Rank-1 decompositions.    *)
(* Consumer: uhlmann_environment_unitary_witness.                       *)
(* ================================================================== *)

(* Rank-1 den1mx matrices decompose as v *m v^*t. *)
(* rank1_form *)
(* infra: no tex label — fundamental & reusable (mathcomp-style) *)
(* consumer: rank1_form is used downstream by the BB84 secrecy proof. *)
(* path: utils:rank1_form -> utils:pd_metric_triangle -> lhl:cq_smoothing -> *)
(*   bb84:privacy_amplification -> bb84:bb84_secret *)
Lemma rank1_form {n : nat} (M : 'M[C]_n) :
  M \is den1mx -> \rank M = 1%N ->
  exists v : 'cV[C]_n, M = v *m v^*t.
Proof.
  move=> Hden1 Hrank.
  have /den1mxP [Hpsd /eqP Htr1] := Hden1.
  have Hnorm : M \is hermmx by exact: psdmx_herm Hpsd.
  have Hhermnorm : M \is normalmx by exact: hermmx_normal Hnorm.
  have Hproj1 : M \is proj1mx.
  { apply/proj1mxP; split; last by rewrite Hrank.
    apply/projmxP; split=> //.
    have /psdmxP [_ /nnegmxP Hnneg] := Hpsd.
    rewrite trace_spectral_diag // mxtrace_diag in Htr1.
    have /sum_nat_eq1 [i0 Pi0] :
        (\sum_(k : 'I_n) (spectral_diag M ord0 k != 0%R))%N = 1%N.
    { by rewrite -rank_diag_mx -(normalmx_rank Hhermnorm). }
    have Hzero : forall k, k != i0 -> spectral_diag M ord0 k = 0.
    { move=> k Hk; apply/eqP/negPn.
      have := Pi0 k; rewrite [i0 == k]eq_sym (negPf Hk).
      by case: (_ != _). }
    have Hi0_val : spectral_diag M ord0 i0 = 1.
    { move: Htr1; rewrite (bigD1 i0) //=.
      suff -> : \sum_(k | k != i0) spectral_diag M ord0 k = 0 by rewrite addr0.
      apply: big1 => k Hk; exact: Hzero _ Hk. }
    apply/boolmxP=> i j; rewrite (ord1 i).
    case: (j =P i0) => [->|/eqP ni].
    - by apply/orP; right; rewrite Hi0_val eqxx.
    - by apply/orP; left; rewrite Hzero //; apply/negP. }
  move: Hproj1 => /proj1mx_diagP [i0 Hi0].
  set U := eigenmx M.
  exists (col i0 U).
  move: Hhermnorm => /eigen_dec ->.
  rewrite -/U Hi0.
  set d := delta_mx (0 : 'I_1) i0.
  rewrite mulmx_colrow (bigD1 i0) //= big1; last first.
  { move=> j Hj.
    rewrite col_diag_mul.
    have -> : d ord0 j = 0 by rewrite /d mxE eqxx /= (negPf Hj).
    by rewrite scale0r mul0mx. }
  rewrite addr0 col_diag_mul.
  have -> : d ord0 i0 = 1 by rewrite /d mxE !eqxx.
  by rewrite scale1r -adj_col.
Qed.

(* Fixed-environment purification: any denmx sigma_A with rank ≤ b admits a    *)
(* rank-1 purification theta on A⊗B.                                           *)
(* purification_exists_in_dim *)
(* infra: no tex label — fundamental & reusable (mathcomp-style) *)
(* consumer: purification_exists_in_dim is used downstream by the BB84 secrecy proof. *)
(* path: utils:purification_exists_in_dim -> utils:pd_gtd_bar_lb -> *)
(*   bb84:privacy_amplification -> bb84:bb84_secret *)
Lemma purification_exists_in_dim {a b : nat} (sigma_A : 'M[C]_a) :
  sigma_A \is denmx ->
  sigma_A != 0 ->
  (\rank sigma_A <= b)%N ->
  exists theta0 : 'M[C]_(a * b),
    theta0 \is denmx /\ \rank theta0 = 1%N /\ ptrace2 theta0 = sigma_A.
Proof.
  move=> Hsigma_den Hsigma_nz Hrank_sigma_b.
  have Hsigma_psd : sigma_A \is psdmx by exact: denmx_psd.
  have [B HB] := psdmx_form Hsigma_psd.
  pose r := \rank B.
  have Hr_le_b : (r <= b)%N by rewrite /r -rank_form -HB.
  pose RB := row_base B.
  pose S := RB *m RB^*t.
  have HS_psd : S \is psdmx by exact: form_psd.
  have /hermmxP HT_herm := sqrtmx_herm (psdmx_herm HS_psd).
  pose T := sqrtmx S.
  pose A0 := col_base B *m T.
  pose Apad : 'M[C]_(a, r + (b - r)) := row_mx A0 (0 : 'M[C]_(a, b - r)).
  pose A' : 'M[C]_(a, b) := castmx (erefl a, subnKC Hr_le_b) Apad.
  pose v : 'cV[C]_(a * b) := (mxvec A')^T.
  have HA0 : A0 *m A0^*t = sigma_A.
  { rewrite /A0 /T adjmxM -HT_herm.
    have -> :
        (col_base B *m sqrtmx S) *m (sqrtmx S *m (col_base B)^*t) =
        col_base B *m (sqrtmx S *m sqrtmx S) *m (col_base B)^*t.
    {
      rewrite -[LHS]mulmxA.
      rewrite [sqrtmx S *m (sqrtmx S *m (col_base B)^*t)]mulmxA.
      by rewrite [LHS]mulmxA.
    }
    rewrite (sqrtmxK HS_psd).
    rewrite /S /RB.
    have -> :
        col_base B *m (row_base B *m (row_base B)^*t) *m (col_base B)^*t =
        (col_base B *m row_base B) *m ((row_base B)^*t *m (col_base B)^*t).
    {
      rewrite -[LHS]mulmxA.
      rewrite -[row_base B *m (row_base B)^*t *m (col_base B)^*t]mulmxA.
      by rewrite [LHS]mulmxA.
    }
    by rewrite -adjmxM mulmx_base HB. }
  have HApad : Apad *m Apad^*t = sigma_A.
  { have HApad_adj :
        Apad^*t = col_mx A0^*t (0 : 'M[C]_(b - r, a)).
    { rewrite /Apad adjmxE tr_row_mx trmx0 map_col_mx map_mx0 -adjmxE //. }
    by rewrite HApad_adj /Apad mul_row_col mul0mx addr0. }
  have HA : A' *m A'^*t = sigma_A.
  { have HAcadj : A'^*t = castmx (subnKC Hr_le_b, erefl a) (Apad^*t).
    { rewrite /A'. by rewrite adjmx_castV. }
    have -> : A' *m A'^*t = castmx (erefl a, erefl a) (Apad *m Apad^*t).
    { rewrite /A' HAcadj castmx_mul //. }
    by rewrite castmx_id HApad. }
  have Hvm : vec_mx (v^T) = A' by rewrite /v trmxK mxvecK.
  have Hptrace : ptrace2 (v *m v^*t) = sigma_A.
  { by rewrite ptrace2_outerM Hvm HA. }
  exists (v *m v^*t); split; last split.
  - apply/denmxP; split; first exact: form_psd.
    move/denmxP: Hsigma_den => [_ Htr_sigma].
    by rewrite tr_ptrace2 Hptrace.
  - apply/eqP; rewrite eqn_leq; apply/andP; split.
    + apply: leq_trans (mxrankM_maxl _ _) (rank_leq_col _).
    + rewrite lt0n mxrank_eq0.
      apply/eqP => Hvv0.
      have Hsigma0 : sigma_A = 0.
      { by rewrite -Hptrace Hvv0 linear0. }
      by move/negP: Hsigma_nz; apply; rewrite Hsigma0.
  - exact: Hptrace.
Qed.

(* PSD rank-1 matrices are outer products of column vectors. Uses scaling  *)
(* to reduce to rank1_form.                                                 *)
(* psdmx_rank1_form *)
(* infra: no tex label — fundamental & reusable (mathcomp-style) *)
(* consumer: psdmx_rank1_form is used downstream by the BB84 secrecy proof. *)
(* path: utils:psdmx_rank1_form -> utils:pd_ext -> utils:ptrace_cast_psdlf -> *)
(*   lhl:min_coll_bound -> bb84:privacy_amplification -> *)
(*   bb84:bb84_secret *)
Lemma psdmx_rank1_form {n : nat} (M : 'M[C]_n) :
  M \is psdmx -> \rank M = 1%N ->
  exists w : 'cV[C]_n, M = w *m w^*t.
Proof.
  move=> Hpsd Hrank.
  have HM_nz : M != 0.
  { by apply/negP => /eqP HM0; rewrite HM0 mxrank0 in Hrank. }
  have Htr_nz : \tr M != 0.
  { by rewrite (psdmx_trace_eq0 Hpsd). }
  set t := @complex.Re R (\tr M).
  have Htr_real : (\tr M : C) = t%:C.
  { by rewrite /t RRe_real // ger0_real // psdmx_trace. }
  have Ht_ne0 : t%:C != (0 : C) by rewrite -Htr_real.
  have Ht_ne0R : t != 0 by move: Ht_ne0; rewrite fmorph_eq0.
  have Ht_gt0 : 0 < t.
  { rewrite lt_def Ht_ne0R /=.
    have := psdmx_trace Hpsd. by rewrite Htr_real lecR. }
  set M' := t^-1%:C *: M.
  have HM'_psd : M' \is psdmx.
  { apply: psdmxZ; last exact: Hpsd.
    by rewrite lecR invr_ge0 ltW. }
  have HM'_tr1 : \tr M' = 1.
  { rewrite /M' linearZ /= Htr_real.
    by rewrite -rmorphM /= mulVf // rmorph1. }
  have HM'_den1 : M' \is den1mx by apply/den1mxP; split=> //; rewrite HM'_tr1.
  have HM'_rank : \rank M' = 1%N.
  { have Hne0 : t^-1%:C != (0 : C) by rewrite fmorph_eq0 invr_eq0.
    have /eqmxP Heq := eqmx_scale M Hne0.
    by rewrite /M' (eqmx_rank Heq). }
  have [v Hv] := rank1_form HM'_den1 HM'_rank.
  exists ((Num.sqrt t)%:C *: v).
  rewrite -scalemxAl adjmxZ -scalemxAr scalerA.
  rewrite geC0_conj; last by rewrite lecR sqrtr_ge0.
  rewrite -rmorphM /= -expr2 sqr_sqrtr; last exact: ltW Ht_gt0.
  rewrite -Hv /M' scalerA -rmorphM /= mulfV //.
  by rewrite rmorph1 scale1r.
Qed.

(* ================================================================== *)
(* Purification ptrace primitives — single-slot ptrace identities for  *)
(* UCR purification-reshape arguments.                                 *)
(* Consumers: eur/def.v (rho_XB/rho_ZC closures).                      *)
(* ================================================================== *)

Section PurificationPtracePrimitives.
Variable (na nb nc nd : nat).

(* Primitive 1 — single-slot ptrace1 ∘ ptrace2 identity under         *)
(* A-sandwich + castmx reshape (used by rho_XB closure).               *)
(* Reduces to: ptrace2 commutes with mulnA-castmx up to ptrace         *)
(* composition, and (A *t 1 *t 1) sandwich passes through ptrace1.    *)
(* ptrace12_sandwich_purif_slot_mx *)
(* infra: no tex label — fundamental & reusable (mathcomp-style) *)
(* consumer: ptrace12_sandwich_purif_slot_mx is used downstream by the BB84 secrecy proof. *)
(* path: utils:ptrace12_sandwich_purif_slot_mx -> eur:purif_reshape_rank -> *)
(*   eur:entropic_uncertainty_relation -> *)
(*   eur:entropic_uncertainty_relation -> *)
(*   bb84:entropic_uncertainty_relation_bb84 -> bb84:bb84_secret *)
Lemma ptrace12_sandwich_purif_slot_mx
    (e : (na * nb * nc * nd = na * nb * (nc * nd))%N)
    (A : 'M[C]_na)
    (rhoABC : 'M[C]_(na * nb * nc))
    (rhoABCD : 'M[C]_(na * nb * nc * nd)) :
  ptrace2 rhoABCD = rhoABC ->
  ptrace1 (ptrace2
    ((A *t 1%:M *t 1%:M) *m castmx (e, e) rhoABCD
       *m (A *t 1%:M *t 1%:M)))
  = ptrace1 (ptrace2
    ((A *t 1%:M *t 1%:M) *m rhoABC
       *m (A *t 1%:M *t 1%:M))).
Proof.
  move=> Hext; congr ptrace1.
  rewrite !ptrace2_mulmxI !ptrace2_mulImx.
  congr (_ *m _ *m _).
  have He : e = esym (mulnA (na * nb) nc nd) by apply: eq_irrelevance.
  by rewrite He ptrace2_compose Hext.
Qed.

(* Primitive 2 — single-slot conditioning-ptrace identity for the   *)
(* per-z term of rho_ZC on a purification reshape. This relates a    *)
(* single term (delta_mx z z *t ptrace1 (sandwich with cast rhoABCD))*)
(* on the full CD conditioning block to a single term of rho_ZC on   *)
(* rhoABC by tracing out D via ptrace2+castmx. Genuine per-slot      *)
(* reduction of the sum-over-z consumer in eur/def.v.                *)
(* rho_ZC_slot_purif_ptrace2_mx *)
(* infra: no tex label — fundamental & reusable (mathcomp-style) *)
(* consumer: rho_ZC_slot_purif_ptrace2_mx is used downstream by the BB84 secrecy proof. *)
(* path: utils:rho_ZC_slot_purif_ptrace2_mx -> *)
(*   eur:smooth_hmax_mx_rho_ZC_purif_dpi -> *)
(*   eur:entropic_uncertainty_relation -> *)
(*   eur:entropic_uncertainty_relation -> *)
(*   bb84:entropic_uncertainty_relation_bb84 -> bb84:bb84_secret *)
Lemma rho_ZC_slot_purif_ptrace2_mx
    (nz : nat) (z : 'I_nz)
    (e : (nz * (nc * nd) = nz * nc * nd)%N)
    (e' : (na * nb * nc * nd = na * nb * (nc * nd))%N)
    (A : 'M[C]_na)
    (rhoABC : 'M[C]_(na * nb * nc))
    (rhoABCD : 'M[C]_(na * nb * nc * nd)) :
  ptrace2 rhoABCD = rhoABC ->
  ptrace2 (castmx (e, e)
    (delta_mx z z *t ptrace1
      ((A *t 1%:M *t 1%:M) *m castmx (e', e') rhoABCD
         *m (A *t 1%:M *t 1%:M))))
  = delta_mx z z *t ptrace1
      ((A *t 1%:M *t 1%:M) *m rhoABC *m (A *t 1%:M *t 1%:M)).
Proof.
  move=> Hext.
  have He : e = mulnA nz nc nd by apply: eq_irrelevance.
  rewrite He ptrace2_castmx_tensmx_assoc.
  congr (_ *t _).
  rewrite (ptrace2_ptrace1_commute _ (mulnA (na*nb) nc nd)).
  congr ptrace1.
  rewrite (castmx_mulmx3 (mulnA (na*nb) nc nd) (mulnA (na*nb) nc nd)).
  rewrite castmx_comp.
  have Hmid : etrans e' (mulnA (na*nb) nc nd) = erefl _
    by apply: eq_irrelevance.
  rewrite Hmid castmx_id.
  rewrite !tensmx_1_assoc.
  rewrite ptrace2_mulmxI ptrace2_mulImx.
  by rewrite Hext.
Qed.

End PurificationPtracePrimitives.

(* ================================================================== *)
(* Foundational pinvmx_ helpers.                                        *)
(* mathcomp-CoqQ's pinvmx_ has 3 of 4 MP conditions in hspace.v;        *)
(* this section completes the characterization with the missing 4th    *)
(* condition (`pinvmx_MP_cond2`) and MP-uniqueness, then provides       *)
(* spectral form for psd matrices.                                      *)
(* Consumers (≥4 each): pinvlf_psdlf, pinvlfZ_nn, pinvlf_sqrtH_pow2,   *)
(* pinvlf_sdot_I (in lf.v and lift.v), and related pinvlf usages.      *)
(* ================================================================== *)

Section PinvmxFoundations.

(* The 4th MP condition for (pinvmx_ M)^*t: it is a "reflexive g-inverse" *)
(* satisfying X M X = X.                                                *)
(* Standalone justification: foundational MP pseudoinverse identity      *)
(* (Penrose 1955 §1, Stewart-Sun §3.1).                                 *)
(* path: utils:pinvmx_MP_cond2 -> utils:pinvlfZ_nn -> lhl:min_coll_bound -> *)
(*   bb84:privacy_amplification -> bb84:bb84_secret *)
Lemma pinvmx_MP_cond2 (n : nat) (M : 'M[C]_n) :
  (pinvmx_ M)^*t *m M *m (pinvmx_ M)^*t = (pinvmx_ M)^*t.
Proof.
  rewrite {2}(svdE M) /pinvmx_ !adjmxM !adjmxK !mulmxA.
  do 2 (rewrite mulmxKtV ?svd_pE//).
  f_equal; rewrite -!mulmxA; f_equal.
  rewrite mulmxA cdiag_mx_mulr svd_d_invC svd_d_exdr_mul -boolmx_of_inv.
  apply: adjmx_inj; rewrite adjmxM diag_mx_adj adjmxK.
  rewrite -svd_d_exdr_conj boolmx_of_conj cdiag_diag_mul; f_equal.
  apply/matrixP=>i j; rewrite !mxE.
  have [->|_] := eqVneq ((svd_d M) i j) 0.
    by rewrite invr0 mul0r.
  by rewrite /= mulr1.
Qed.

(* MP-uniqueness from the 4 conditions.                                 *)
(* Standalone justification: textbook MP-uniqueness (Penrose 1955).    *)
(* path: utils:pinvmx_uniq_MP -> utils:pinvlfZ_nn -> lhl:min_coll_bound -> *)
(*   bb84:privacy_amplification -> bb84:bb84_secret *)
Lemma pinvmx_uniq_MP (n : nat) (M Y : 'M[C]_n) :
  M *m Y *m M = M ->
  Y *m M *m Y = Y ->
  (M *m Y)^*t = M *m Y ->
  (Y *m M)^*t = Y *m M ->
  Y = (pinvmx_ M)^*t.
Proof.
  move=> H1 H2 H3 H4.
  set Y' : 'M[C]_n := (pinvmx_ M)^*t.
  have HY'1 : M *m Y' *m M = M.
    have := cosuppmx_id M.
    by rewrite /cosuppmx -/Y'.
  have HY'2 : Y' *m M *m Y' = Y' by exact: pinvmx_MP_cond2.
  have HY'3 : (M *m Y')^*t = M *m Y'.
    have /hermmxP HCH := cosuppmx_herm M.
    by move: HCH; rewrite /cosuppmx -/Y'.
  have HY'4 : (Y' *m M)^*t = Y' *m M.
    have /hermmxP HSH := suppmx_herm M.
    by move: HSH; rewrite /suppmx -/Y'.
  (* M *m Y = M *m Y'. *)
  have step1 : M *m Y *m M *m Y' = M *m Y' by rewrite H1.
  have step2 : M *m Y' *m M *m Y = M *m Y by rewrite HY'1.
  have HMY' : M *m Y = M *m Y'.
    (* Compare the two projections by multiplying against each other and
       taking adjoints.  The equations `step1` and `step2` collapse the two
       products, while `H3` and `HY'3` identify the relevant adjoints. *)
    have a : M *m Y *m (M *m Y') = M *m Y'.
      by rewrite mulmxA step1.
    have b : M *m Y' *m (M *m Y) = M *m Y.
      by rewrite mulmxA step2.
    have c : (M *m Y *m (M *m Y'))^*t = M *m Y' *m (M *m Y).
      by rewrite adjmxM HY'3 H3.
    by rewrite -b -c a.
  (* Y *m M = Y' *m M (symmetric). *)
  have rebracket : forall AA BB CC : 'M[C]_n,
    AA *m M *m (BB *m CC) = AA *m (M *m BB *m CC).
    by move=> AA BB CC; rewrite !mulmxA.
  have HYM' : Y *m M = Y' *m M.
    have a : Y *m M *m (Y' *m M) = Y *m M
      by rewrite rebracket HY'1.
    have b : Y' *m M *m (Y *m M) = Y' *m M
      by rewrite rebracket H1.
    have c : (Y *m M *m (Y' *m M))^*t = Y' *m M *m (Y *m M)
      by rewrite adjmxM HY'4 H4.
    by rewrite -b -c a.
  (* Y = Y M Y = Y' M Y = Y' M Y' = Y'. *)
  rewrite -H2 HYM' -mulmxA HMY' mulmxA.
  exact: HY'2.
Qed.

(* svds_d of M^2 for psd M = (svds_d M)^+ 2 entry-wise.                 *)
(* Standalone justification: spectral mapping theorem; for psd M with  *)
(* eigendecomp M = U^*t D U, M^2 = U^*t D^2 U so eigenvalues of M^2     *)
(* are squares of eigenvalues of M.                                     *)
(* path: utils:svds_d_psdmx_sqr -> utils:schnorm4_lift_quarter_pow4 -> *)
(*   lhl:uniform_collision_bound -> *)
(*   bb84:privacy_amplification -> bb84:bb84_secret *)
Lemma svds_d_psdmx_sqr (n : nat) (M : 'M[C]_n) :
  M \is psdmx ->
  svds_d (M *m M) = (svds_d M).^+ 2.
Proof.
  move=> PM.
  case: (psdmx_svd PM) => -[U D] /and3P [HU HD /eqP HM].
  have HUKV : U^*t *m U = 1%:M := unitarymxKV HU.
  have HUK  : U *m U^*t = 1%:M := unitarymxK HU.
  have HUadj : U^*t \is unitarymx by rewrite adjmx_unitary.
  have HD_nneg j : 0 <= D 0 j by exact: svd_diag_ge0.
  (* svds_d M = D via uniqueness (M = (U^*t) * diag D * (U^*t)^*t). *)
  have HsM : svds_d M = D.
    apply: esym; apply: (svds_d_unique HUadj HUadj HD).
    by rewrite adjmxK.
  (* M^2 = U^*t * diag (D .* D) * U via cancellation. *)
  have HM2 : M *m M = U^*t *m diag_mx (D .* D) *m U.
    rewrite HM.
    rewrite -!mulmxA.
    rewrite [U *m (U^*t *m _)]mulmxA HUK mul1mx.
    rewrite [diag_mx D *m _]mulmxA.
    rewrite diag_mx_dmul.
    by rewrite mulmxA.
  (* D .* D \is svd_diag (nneg + sorted decreasing, by squaring nneg-monotonic). *)
  have HDD_sd : D .* D \is svd_diag.
    apply/svd_diagP => i; split.
      rewrite mxE; apply: mulr_ge0; exact: HD_nneg.
    move=> j Hij; rewrite !mxE.
    have Hle : D 0 j <= D 0 i.
      have /svd_diagP/(_ i)[_ /(_ j Hij)] := HD.
      done.
    by apply: ler_pM => //; exact: HD_nneg.
  have HsM2 : svds_d (M *m M) = D .* D.
    apply: esym; apply: (svds_d_unique HUadj HUadj HDD_sd).
    by rewrite HM2 adjmxK.
  rewrite HsM2 HsM.
  apply/matrixP=> i j; rewrite !mxE.
  by rewrite expr2.
Qed.

(* Pseudoinverse of a psd matrix in SVD form.                            *)
(* If M = U^*t *m diag(D) *m U with U unitary and D nneg svd_diag,       *)
(* then pinvmx_ M = U^*t *m diag(D.^-1) *m U.                            *)
(* Standalone justification: the candidate Y' = U^*t *m diag(D.^-1) *m U *)
(* is hermitian and satisfies the 4 MP conditions, so MP-uniqueness     *)
(* yields Y' = (pinvmx_ M)^*t = pinvmx_ M.                              *)
(* Consumers (≥2): pinvlf_psdlf, pinvlf_sqrtH_pow2 in lf.v.             *)
(* path: utils:pinvmx_psdmx_svd_form -> utils:pinvlf_psdlf -> *)
(*   lhl:min_coll_bound -> bb84:privacy_amplification -> *)
(*   bb84:bb84_secret *)
Lemma pinvmx_psdmx_svd_form (n : nat) (M : 'M[C]_n) (U : 'M[C]_n) (D : 'rV[C]_n) :
  U \is unitarymx -> D \is a nnegmx ->
  M = U^*t *m diag_mx D *m U ->
  pinvmx_ M = U^*t *m diag_mx D.^-1 *m U.
Proof.
  move=> HU HD HM.
  set Y' : 'M[C]_n := U^*t *m diag_mx D.^-1 *m U.
  have HUKV : U^*t *m U = 1%:M by exact: unitarymxKV.
  have HUK  : U *m U^*t = 1%:M by exact: unitarymxK.
  have HDnn : forall j, 0 <= D 0 j.
    by move=> j; have /nnegmxP/(_ 0 j) := HD; rewrite nnegrE.
  (* Pointwise identities over D and D.^-1. *)
  have HD_DDinv : (D .* D.^-1) .* D = D.
    apply/matrixP=> i j; rewrite !mxE.
    rewrite (ord1 i).
    case: (eqVneq (D 0 j) 0) => [-> | Hne].
      by rewrite mul0r mul0r.
    by rewrite mulfV// mul1r.
  have HD_DinvD_Dinv : (D.^-1 .* D) .* D.^-1 = D.^-1.
    apply/matrixP=> i j; rewrite !mxE.
    rewrite (ord1 i).
    case: (eqVneq (D 0 j) 0) => [-> | Hne].
      by rewrite invr0 !mul0r.
    by rewrite mulVf// mul1r.
  have Hsym : D .* D.^-1 = D.^-1 .* D by exact: dmulmxC.
  (* Simplifications of M*Y' and Y'*M. *)
  have HMY : M *m Y' = U^*t *m diag_mx (D .* D.^-1) *m U.
    rewrite HM /Y'.
    rewrite -!mulmxA.
    rewrite [U *m (U^*t *m _)]mulmxA HUK mul1mx.
    rewrite [diag_mx D *m _]mulmxA.
    rewrite diag_mx_dmul.
    reflexivity.
  have HYM : Y' *m M = U^*t *m diag_mx (D.^-1 .* D) *m U.
    rewrite HM /Y'.
    rewrite -!mulmxA.
    rewrite [U *m (U^*t *m _)]mulmxA HUK mul1mx.
    rewrite [diag_mx D.^-1 *m _]mulmxA.
    rewrite diag_mx_dmul.
    reflexivity.
  have HMP1 : M *m Y' *m M = M.
    rewrite HMY HM.
    rewrite -!mulmxA.
    rewrite [U *m (U^*t *m _)]mulmxA HUK mul1mx.
    rewrite [diag_mx (D .* D.^-1) *m _]mulmxA.
    rewrite diag_mx_dmul HD_DDinv.
    reflexivity.
  have HMP2 : Y' *m M *m Y' = Y'.
    rewrite HYM /Y'.
    rewrite -!mulmxA.
    rewrite [U *m (U^*t *m _)]mulmxA HUK mul1mx.
    rewrite [diag_mx (D.^-1 .* D) *m _]mulmxA.
    rewrite diag_mx_dmul HD_DinvD_Dinv.
    reflexivity.
  have Hdiag_herm : forall (E : 'rV[C]_n),
    E^*m = E -> (diag_mx E)^*t = diag_mx E.
    by move=> E HE; rewrite diag_mx_adj HE.
  have HDinv_real : (D.^-1)^*m = D.^-1.
    apply/matrixP=> i j; rewrite !mxE.
    rewrite (ord1 i).
    apply: geC0_conj.
    by rewrite invr_ge0.
  have HDD_real : (D .* D.^-1)^*m = D .* D.^-1.
    apply/matrixP=> i j; rewrite !mxE.
    rewrite (ord1 i).
    apply: geC0_conj.
    apply: mulr_ge0.
      exact: (HDnn j).
    by rewrite invr_ge0.
  have HMP3 : (M *m Y')^*t = M *m Y'.
    rewrite HMY !adjmxM !adjmxK.
    rewrite (Hdiag_herm _ HDD_real).
    rewrite [LHS]mulmxA.
    reflexivity.
  have HDinvD_real : (D.^-1 .* D)^*m = D.^-1 .* D.
    by rewrite -Hsym HDD_real.
  have HMP4 : (Y' *m M)^*t = Y' *m M.
    rewrite HYM !adjmxM !adjmxK.
    rewrite (Hdiag_herm _ HDinvD_real).
    rewrite [LHS]mulmxA.
    reflexivity.
  have HY'_eq : Y' = (pinvmx_ M)^*t by exact: pinvmx_uniq_MP HMP1 HMP2 HMP3 HMP4.
  have HY'_herm : Y'^*t = Y'.
    rewrite /Y' !adjmxM !adjmxK.
    rewrite (Hdiag_herm _ HDinv_real).
    rewrite [LHS]mulmxA.
    reflexivity.
  rewrite -[LHS]adjmxK.
  rewrite -HY'_eq.
  exact: HY'_herm.
Qed.

(* Pseudoinverse is preserved under unitary conjugation:                    *)
(*   U unitary => pinvmx_ (U *m M *m U^*t) = U *m pinvmx_ M *m U^*t.        *)
(* Standalone justification: candidate U *m (pinvmx_ M)^*t *m U^*t           *)
(* satisfies 4 MP conditions w.r.t. U *m M *m U^*t (unitarymx cancellations  *)
(* + cosuppmx_id + pinvmx_MP_cond2 + cosuppmx_herm + suppmx_herm).            *)
(* Consumers (≥1): pinvlf_sdot_I via tenv_mxU conjugation.                   *)
(* path: utils:pinvmx_unitary_conj -> entropy:smooth_hmax_labelled_mx -> *)
(*   bb84:stat -> bb84:bb84_secret *)
Lemma pinvmx_unitary_conj (n : nat) (U M : 'M[C]_n) :
  U \is unitarymx ->
  pinvmx_ (U *m M *m U^*t) = U *m pinvmx_ M *m U^*t.
Proof.
  move=> HU.
  have HUKV : U^*t *m U = 1%:M by exact: unitarymxKV.
  have HUK  : U *m U^*t = 1%:M by exact: unitarymxK.
  set M' := U *m M *m U^*t.
  set Y' : 'M[C]_n := U *m (pinvmx_ M)^*t *m U^*t.
  (* Conjugation collapses: (U A U^*t) *m (U B U^*t) = U (A B) U^*t when U^*t U = 1. *)
  have collapse : forall A B : 'M[C]_n,
    (U *m A *m U^*t) *m (U *m B *m U^*t) = U *m (A *m B) *m U^*t.
    move=> A0 B0.
    rewrite -mulmxA -mulmxA -mulmxA.
    rewrite [U^*t *m (U *m _)]mulmxA HUKV mul1mx.
    by rewrite !mulmxA.
  have HMP1 : M' *m Y' *m M' = M'.
    rewrite /M' /Y'.
    rewrite collapse.
    rewrite collapse.
    by rewrite -/(cosuppmx M) cosuppmx_id.
  have HMP2 : Y' *m M' *m Y' = Y'.
    rewrite /M' /Y'.
    rewrite collapse.
    rewrite collapse.
    by rewrite pinvmx_MP_cond2.
  have HCH : (M *m (pinvmx_ M)^*t)^*t = M *m (pinvmx_ M)^*t.
    by have/hermmxP/esym := cosuppmx_herm M; rewrite /cosuppmx.
  have HSH : ((pinvmx_ M)^*t *m M)^*t = (pinvmx_ M)^*t *m M.
    by have/hermmxP/esym := suppmx_herm M; rewrite /suppmx.
  (* Conjugating a hermitian matrix preserves hermiticity. *)
  have herm_conj : forall X : 'M[C]_n,
    X^*t = X -> (U *m X *m U^*t)^*t = U *m X *m U^*t.
    move=> X HX.
    rewrite !adjmxM !adjmxK HX.
    by rewrite -mulmxA.
  have HMP3 : (M' *m Y')^*t = M' *m Y'.
    rewrite /M' /Y' collapse.
    by apply: herm_conj.
  have HMP4 : (Y' *m M')^*t = Y' *m M'.
    rewrite /M' /Y' collapse.
    by apply: herm_conj.
  have HY'_eq : Y' = (pinvmx_ M')^*t by exact: pinvmx_uniq_MP HMP1 HMP2 HMP3 HMP4.
  have ->: pinvmx_ M' = Y'^*t by rewrite HY'_eq adjmxK.
  rewrite /Y' !adjmxM !adjmxK.
  by rewrite mulmxA.
Qed.

(* Pseudoinverse on identity-tensor: pinvmx_ (1%:M *t M) = 1%:M *t pinvmx_ M.   *)
(* Standalone justification: candidate Y' = 1 *t (pinvmx_ M)^*t satisfies the   *)
(* 4 MP conditions w.r.t. M' = 1 *t M (using tensmx_mul + cosuppmx_id +         *)
(* pinvmx_MP_cond2 + cosuppmx_herm + suppmx_herm), so MP-uniqueness yields      *)
(* Y' = (pinvmx_ M')^*t. Take adjoint: pinvmx_ M' = Y'^*t = 1 *t pinvmx_ M.     *)
(* Consumers (≥1): pinvlf_sdot_I in lift.v.                                     *)
(* path: utils:pinvmx_tenmx_one_left -> utils:suppmx_tenmx_one_left -> *)
(*   utils:ptrace_supph_lift -> lhl:uniform_collision_bound -> *)
(*   bb84:privacy_amplification -> bb84:bb84_secret *)
Lemma pinvmx_tenmx_one_left (m n : nat) (M : 'M[C]_n) :
  pinvmx_ ((1%:M : 'M[C]_m) *t M) = (1%:M : 'M[C]_m) *t pinvmx_ M.
Proof.
  set M' := (1%:M : 'M[C]_m) *t M.
  set Y' : 'M[C]_(m * n) := (1%:M : 'M[C]_m) *t (pinvmx_ M)^*t.
  have HMP1 : M' *m Y' *m M' = M'.
    rewrite /M' /Y' !tensmx_mul !mul1mx.
    by rewrite -/(cosuppmx M) cosuppmx_id.
  have HMP2 : Y' *m M' *m Y' = Y'.
    rewrite /M' /Y' !tensmx_mul !mul1mx.
    by rewrite pinvmx_MP_cond2.
  have HMP3 : (M' *m Y')^*t = M' *m Y'.
    rewrite /M' /Y' tensmx_mul mul1mx -/(cosuppmx M).
    rewrite adjmx_tens adjmx1.
    congr (_ *t _).
    by have /hermmxP := cosuppmx_herm M.
  have HMP4 : (Y' *m M')^*t = Y' *m M'.
    rewrite /M' /Y' tensmx_mul mul1mx -/(suppmx M).
    rewrite adjmx_tens adjmx1.
    congr (_ *t _).
    by have /hermmxP := suppmx_herm M.
  have HY'_eq : Y' = (pinvmx_ M')^*t by exact: pinvmx_uniq_MP HMP1 HMP2 HMP3 HMP4.
  have ->: pinvmx_ M' = Y'^*t by rewrite HY'_eq adjmxK.
  by rewrite /Y' adjmx_tens adjmx1 adjmxK.
Qed.

End PinvmxFoundations.

(* ================================================================== *)
(* Partial-trace support inclusion for psd matrices.                    *)
(* For psd rho : 'M[C]_(m * n), suppmx rho ⊑ (1%:M *t suppmx ptrace1).  *)
(* Foundational quantum-info partial-trace identity                     *)
(* (Renner Lemma `lem:tensprodimage`, support-projector form).          *)
(* ================================================================== *)

(* Helper: if A *m P = A and P is a projector, then suppmx A ≤ P.      *)
(* Standalone justification: foundational projector partial order      *)
(* (Halmos §32, Bhatia §IV.1).                                          *)
(* path: utils:suppmx_le_proj -> utils:suppmx_ptrace1_tens -> *)
(*   utils:ptrace_supph_lift -> lhl:uniform_collision_bound -> *)
(*   bb84:privacy_amplification -> bb84:bb84_secret *)
Lemma suppmx_le_proj {n : nat} (A P : 'M[C]_n) :
  P \is projmx -> A *m P = A -> suppmx A ⊑ P.
Proof.
  move=> Pproj AP.
  have /projmxP_id[/hermmxP hP PP] := Pproj.
  have Sproj : suppmx A \is projmx by exact: suppmx_proj A.
  have /projmxP_id[/hermmxP hS SS] := Sproj.
  have SP : suppmx A *m P = suppmx A by rewrite /suppmx -mulmxA AP.
  have PS : P *m suppmx A = suppmx A.
    apply: adjmx_inj.
    by rewrite adjmxM -hS -hP SP.
  have diff_proj : (P - suppmx A) \is projmx.
    apply/projmxP_id; split.
    - by apply/hermmxP; rewrite linearB/= -hP -hS.
    - by rewrite !mulmxBr !mulmxBl PP PS SP SS subrr subr0.
  by rewrite le_lownerE; exact: obsmx_psd (projmx_obs diff_proj).
Qed.

(* pinvmx_ commutes with rectangular unitary conjugation (both UU^*t = 1     *)
(* and U^*t U = 1 needed). Foundational helper: lifts pinvmx_unitary_conj    *)
(* from square U to rectangular U (full rank, two-sided unitary).            *)
(* path: utils:pinvmx_rect_unitary_conj -> utils:suppmx_rect_unitary_conj -> *)
(*   utils:ptrace_supph_lift -> lhl:uniform_collision_bound -> *)
(*   bb84:privacy_amplification -> bb84:bb84_secret *)
Lemma pinvmx_rect_unitary_conj (p q : nat) (U : 'M[C]_(p, q)) (M : 'M[C]_q) :
  U \is unitarymx -> U^*t \is unitarymx ->
  pinvmx_ (U *m M *m U^*t) = U *m pinvmx_ M *m U^*t.
Proof.
  move=> HU HUt.
  have HUKV : U^*t *m U = 1%:M by have := unitarymxK HUt; rewrite adjmxK.
  have HUK : U *m U^*t = 1%:M by exact: unitarymxK.
  set M' := U *m M *m U^*t.
  set Y' : 'M[C]_p := U *m (pinvmx_ M)^*t *m U^*t.
  have collapse : forall A B : 'M[C]_q,
      (U *m A *m U^*t) *m (U *m B *m U^*t) = U *m (A *m B) *m U^*t.
    move=> A0 B0.
    by rewrite -!mulmxA [U^*t *m (U *m _)]mulmxA HUKV mul1mx !mulmxA.
  have HMP1 : M' *m Y' *m M' = M'.
    rewrite /M' /Y' collapse collapse.
    by rewrite -/(cosuppmx M) cosuppmx_id.
  have HMP2 : Y' *m M' *m Y' = Y'.
    rewrite /M' /Y' collapse collapse.
    by rewrite pinvmx_MP_cond2.
  have herm_conj : forall X : 'M[C]_q,
      X^*t = X -> (U *m X *m U^*t)^*t = U *m X *m U^*t.
    by move=> X HX; rewrite !adjmxM !adjmxK HX -mulmxA.
  have HMP3 : (M' *m Y')^*t = M' *m Y'.
    rewrite /M' /Y' collapse; apply: herm_conj.
    by have/hermmxP/esym := cosuppmx_herm M; rewrite /cosuppmx.
  have HMP4 : (Y' *m M')^*t = Y' *m M'.
    rewrite /M' /Y' collapse; apply: herm_conj.
    by have/hermmxP/esym := suppmx_herm M; rewrite /suppmx.
  have HY'_eq : Y' = (pinvmx_ M')^*t by exact: pinvmx_uniq_MP HMP1 HMP2 HMP3 HMP4.
  have ->: pinvmx_ M' = Y'^*t by rewrite HY'_eq adjmxK.
  by rewrite /Y' !adjmxM !adjmxK mulmxA.
Qed.

(* suppmx commutes with rectangular unitary conjugation. Direct corollary    *)
(* of pinvmx_rect_unitary_conj.                                              *)
(* path: utils:suppmx_rect_unitary_conj -> utils:ptrace_supph_lift -> *)
(*   lhl:uniform_collision_bound -> *)
(*   bb84:privacy_amplification -> bb84:bb84_secret *)
Lemma suppmx_rect_unitary_conj (p q : nat) (U : 'M[C]_(p, q)) (M : 'M[C]_q) :
  U \is unitarymx -> U^*t \is unitarymx ->
  suppmx (U *m M *m U^*t) = U *m suppmx M *m U^*t.
Proof.
  move=> HU HUt.
  have HUKV : U^*t *m U = 1%:M by have := unitarymxK HUt; rewrite adjmxK.
  rewrite /suppmx (pinvmx_rect_unitary_conj _ HU HUt).
  rewrite !adjmxM !adjmxK.
  set P := (pinvmx_ M)^*t.
  rewrite -[LHS]mulmxA.
  rewrite -[RHS]mulmxA.
  congr (U *m _).
  rewrite -[LHS]mulmxA.
  rewrite -[U *m M *m U^*t]mulmxA.
  rewrite (mulmxA U^*t U) HUKV mul1mx.
  rewrite [LHS]mulmxA.
  reflexivity.
Qed.

(* suppmx absorbs tensor-with-one on the left.                                *)
(* path: utils:suppmx_tenmx_one_left -> utils:ptrace_supph_lift -> *)
(*   lhl:uniform_collision_bound -> *)
(*   bb84:privacy_amplification -> bb84:bb84_secret *)
Lemma suppmx_tenmx_one_left (m n : nat) (Y : 'M[C]_n) :
  suppmx ((1%:M : 'M[C]_m) *t Y) = (1%:M : 'M[C]_m) *t suppmx Y.
Proof.
  rewrite /suppmx pinvmx_tenmx_one_left.
  rewrite adjmx_tens adjmx1.
  by rewrite tensmx_mul mul1mx.
Qed.

(* path: utils:suppmx_ptrace1_tens -> utils:ptrace_supph_lift -> *)
(*   lhl:uniform_collision_bound -> *)
(*   bb84:privacy_amplification -> bb84:bb84_secret *)
Lemma suppmx_ptrace1_tens (m n : nat) (rho : 'M[C]_(m * n)) :
  rho \is psdmx ->
  (suppmx rho ⊑ ((1%:M : 'M[C]_m) *t suppmx (ptrace1 rho))).
Proof.
  move=> Hrho.
  set Q := suppmx (ptrace1 rho).
  have Qproj := suppmx_proj (ptrace1 rho).
  have /projmxP_id [/hermmxP Qherm Qidem] := Qproj.
  have proj1m : (1%:M : 'M[C]_m) \is projmx
    by apply/projmxP_id; split; [apply/hermmxP; rewrite adjmx1 | rewrite mulmx1].
  apply: suppmx_le_proj.
  - exact: projmx_tens proj1m Qproj.
  - set Q' := (1%:M : 'M[C]_n) - Q.
    have Q'idem : Q' *m Q' = Q'.
      by rewrite /Q' !mulmxBr !mulmxBl !mulmx1 !mul1mx Qidem subrr subr0.
    have Q'herm : Q' = Q'^*t.
      by rewrite /Q' linearB/= adjmx1 -Qherm.
    suff HrhoQ' : rho *m ((1%:M : 'M[C]_m) *t Q') = 0.
      have tens_distrib : forall (X : 'M[C]_m) (Y Z : 'M[C]_n),
          X *t (Y + Z) = X *t Y + X *t Z.
        move=> X Y Z; apply/matrixP=> i j.
        case: (mxtens_indexP i)=> i1 i2; case: (mxtens_indexP j)=> j1 j2.
        by rewrite [in RHS]mxE !tensmxE mxE mulrDr.
      rewrite -(addr0 (rho *m ((1%:M : 'M[C]_m) *t Q))) -{1}HrhoQ'.
      rewrite -mulmxDr -tens_distrib /Q' addrC addrNK tensmx11.
      by rewrite mulmx1.
    have [B defRho] := psdmx_formV Hrho.
    suff HBQ' : B *m ((1%:M : 'M[C]_m) *t Q') = 0.
      by rewrite defRho -mulmxA HBQ' mulmx0.
    apply: formV_tr_eq0.
    rewrite adjmxM adjmx_tens adjmx1 -Q'herm.
    rewrite mulmxA -(mulmxA ((1%:M : 'M[C]_m) *t _)) -defRho.
    rewrite mxtrace_mulC mulmxA tensmx_mul Q'idem mul1mx.
    rewrite mxtrace_mulC tr_ptrace1 ptrace1_mulmxI.
    by rewrite /Q' mulmxBr mulmx1 suppmx_id subrr linear0.
Qed.

End FvqkdReal.
