(* -------------------------------------------------------------------- *)
(* fid.v — Fidelity F(ρ,τ) and generalized fidelity F̄(ρ,τ)             *)
(* -------------------------------------------------------------------- *)
(* Module: utils.dist.fid                                 *)
(* Paper: Tomamichel, 'A Framework for Non-Asymptotic Quantum           *)
(*   Information Theory' (PhD thesis, arXiv:1203.2142), Chapter 3.       *)
(* TeX labels: df:gfid (Def 3.2), lm:alt-gfid (Lem 3.1),               *)
(*   tb:fid (Table 3.1)                                                 *)
(* -------------------------------------------------------------------- *)
(* Fidelity and generalized fidelity are shared distance primitives.      *)
(* This file contains their matrix-level definitions and reusable algebra *)
(* used by purified distance (`pd_uhl`, `pd_ext`,                         *)
(* `purified_monotonicity`) and the BB84 secrecy proof.                   *)
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
From quantum.dirac Require Import hstensor.

Import Order.TTheory GRing.Theory Num.Theory Num.Def MxLownerOrder.
Import VectorInternalTheory.

(* --- FVQKD imports --- *)
From utils.mx Require Import def prop.
From utils.labelled Require Import op sys lift.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Open Scope ring_scope.
Local Open Scope lfun_scope.

Section FvqkdReal.
Variable R : realType.
Notation C := (@hermitian.C R).
Notation chsType := (@chsType R).

(* ================================================================== *)
(* Fidelity F(ρ,τ) = ||√ρ √τ||₁                                        *)
(* ================================================================== *)

Section FidelityMxDef.
Variable (n : nat).

(* tex: df:gfid — Tomamichel, 'A Framework for Non-Asymptotic Quantum   *)
(*   Information Theory' (PhD thesis, arXiv:1203.2142), Definition 3.2  *)
(*   — fidelity sub-definition                                          *)
(* Matrix core: F(ρ, τ) = ||√ρ √τ||₁.                                  *)
Definition fidelity_mx (rho tau : 'M[C]_n) : R :=
  @complex.Re R (trnorm (sqrtmx rho *m sqrtmx tau)).

End FidelityMxDef.

Section FidelitySetDef.
Variables (L : finType) (H : L -> chsType) (S : {set L}).

(* fidelity *)
(* infra: no tex label — fundamental & reusable ambient set-labelled utility *)
(* consumer: fidelity is used downstream by the BB84 secrecy proof. *)
Definition fidelity (rho tau : 'F[H]_S) : R :=
  @complex.Re R (trnorm (h2mx (sqrtH rho \o sqrtH tau))).

End FidelitySetDef.

Arguments fidelity {L H S} rho tau.

Section MatrixFidelityCore.
Variable (n : nat).

(* ================================================================== *)
(* tex: tb:fid item (i) — Tomamichel, 'A Framework for Non-Asymptotic   *)
(*   Quantum Information Theory' (PhD thesis, arXiv:1203.2142),         *)
(*   Table 3.1, item (i): fidelity is symmetric                         *)
(* math: F(rho, tau) = F(tau, rho) for rho, tau in Pos(H).             *)
(* ================================================================== *)
(* path: utils:fid_i_sym_mx -> entropy:entropy_data_proc -> *)
(*   bb84:bb84_secret *)
Lemma fid_i_sym_mx (rho tau : 'M[C]_n) :
  rho \is psdmx -> tau \is psdmx ->
  @complex.Re R (trnorm (sqrtmx rho *m sqrtmx tau)) =
  @complex.Re R (trnorm (sqrtmx tau *m sqrtmx rho)).
Proof.
  move=> Prho Ptau.
  have Hr : sqrtmx rho = (sqrtmx rho)^*t.
    apply/hermmxP.
    exact: sqrtmx_herm (psdmx_herm Prho).
  have Ht : sqrtmx tau = (sqrtmx tau)^*t.
    apply/hermmxP.
    exact: sqrtmx_herm (psdmx_herm Ptau).
  by rewrite {1}Hr {1}Ht -adjmxM trnorm_adjmx.
Qed.

(* fid_le_tr_mx: Cauchy-Schwarz-style bound F(rho,tau) ≤ sqrt Tr rho  *)
(* · sqrt Tr tau. Reusable infra used in tb:fid item (ii) upper bound.   *)
(* path: utils:fid_le_tr_mx -> entropy:min_omni -> entropy:minmax_dual -> *)
(*   entropy:smooth_iso_hmax -> entropy:entropy_data_proc -> *)
(*   bb84:bb84_secret *)
Lemma fid_le_tr_mx (rho tau : 'M[C]_n) :
  rho \is psdmx -> tau \is psdmx ->
  @complex.Re R (trnorm (sqrtmx rho *m sqrtmx tau)) <=
    Num.sqrt (@complex.Re R (\tr rho)) * Num.sqrt (@complex.Re R (\tr tau)).
Proof.
  move=> Prho Ptau.
  set a := sqrtmx rho; set b := sqrtmx tau.
  have Ha_herm : a^*t = a.
    apply/esym/hermmxP.
    exact: sqrtmx_herm (psdmx_herm Prho).
  have Hb_herm : b^*t = b.
    apply/esym/hermmxP.
    exact: sqrtmx_herm (psdmx_herm Ptau).
  have Haa : a^*t *m a = rho.
    by rewrite Ha_herm /a sqrtmxK.
  have Hbb : b^*t *m b = tau.
    by rewrite Hb_herm /b sqrtmxK.
  set ta := \tr (a^*t *m a).
  set tb := \tr (b^*t *m b).
  have Hta : (0 : C) <= ta by rewrite /ta mxtrace_mulC; exact: form_tr_ge0.
  have Htb : (0 : C) <= tb by rewrite /tb mxtrace_mulC; exact: form_tr_ge0.
  have Hta_R : (0 : R) <= @complex.Re R ta.
    by move: Hta; rewrite lecE/= => /andP[_].
  have Htb_R : (0 : R) <= @complex.Re R tb.
    by move: Htb; rewrite lecE/= => /andP[_].
  have Hlhs : (0 : C) <= trnorm (a *m b) := trnorm_ge0 _.
  have Hlhs_R : (0 : R) <= @complex.Re R (trnorm (a *m b)).
    by move: Hlhs; rewrite lecE/= => /andP[_].
  have Hsch : trnorm (a *m b) <= l2norm a * l2norm b.
    rewrite l2norm_fbnorm.
    apply: schnorm_hoelder_gen; rewrite ?ler0n ?lexx ?orbT //.
    by rewrite invr1 split21.
  have HlN : 0 <= l2norm a * l2norm b by apply: mulr_ge0; apply: l2norm_ge0.
  have Hsq : (trnorm (a *m b)) ^+ 2 <= ta * tb.
    apply: (le_trans (y := (l2norm a * l2norm b) ^+ 2)).
      by apply: lerXn2r; rewrite ?nnegrE ?trnorm_ge0.
    have Ha2 : (l2norm a) ^+ 2 = ta.
      rewrite /ta l2norm_dotV.
      exact: sqrtCK.
    have Hb2 : (l2norm b) ^+ 2 = tb.
      rewrite /tb l2norm_dotV.
      exact: sqrtCK.
    by rewrite exprMn Ha2 Hb2.
  have HlR := ger0_real Hlhs.
  have HtaR := ger0_real Hta.
  have HtbR := ger0_real Htb.
  have Hsq2ge0 : (0 : C) <= trnorm (a *m b) ^+ 2.
    by rewrite expr2; apply: mulr_ge0; exact: Hlhs.
  have Htatb_ge0 : (0 : C) <= ta * tb := mulr_ge0 Hta Htb.
  have Hsq_R : (@complex.Re R (trnorm (a *m b))) ^+ 2
               <= @complex.Re R ta * @complex.Re R tb.
    have E1 : (@complex.Re R (trnorm (a *m b))) ^+ 2
              = @complex.Re R (trnorm (a *m b) ^+ 2).
      by rewrite -(RRe_real HlR) -rmorphXn re_realid.
    have E2 : @complex.Re R ta * @complex.Re R tb
              = @complex.Re R (ta * tb).
      have HtaC : (@complex.Re R ta)%:C = ta := RRe_real HtaR.
      have HtbC : (@complex.Re R tb)%:C = tb := RRe_real HtbR.
      rewrite -[LHS](re_realid (@complex.Re R ta * @complex.Re R tb)).
      congr (@complex.Re R _).
      transitivity ((@complex.Re R ta)%:C * (@complex.Re R tb)%:C).
        exact: realcM.
      exact: (congr2 (fun x y => x * y) HtaC HtbC).
    rewrite E1 E2.
    move: Hsq.
    rewrite -(RRe_real (ger0_real Hsq2ge0)).
    rewrite -(RRe_real (ger0_real Htatb_ge0)).
    by rewrite lecR.
  have Hge0_rho : 0 <= @complex.Re R (\tr rho).
    by rewrite -Haa; exact: Hta_R.
  rewrite -[leLHS]ger0_norm // -sqrtr_sqr -(sqrtrM _ Hge0_rho).
  apply: ler_wsqrtr.
  rewrite -Haa -Hbb -/ta -/tb.
  exact: Hsq_R.
Qed.

End MatrixFidelityCore.

(* ================================================================== *)
(* Generalized fidelity F̄(ρ,τ)                                         *)
(*   F̄(ρ,τ) = F(ρ̂,τ̂) = F(ρ,τ) + sqrt((1-Tr ρ)(1-Tr τ))              *)
(*   where ρ̂ = ρ ⊕ (1-Tr ρ)                                           *)
(* ================================================================== *)

(* tex: df:gfid — Tomamichel, 'A Framework for Non-Asymptotic Quantum   *)
(*   Information Theory' (PhD thesis, arXiv:1203.2142), Definition 3.2  *)

Section GFidelity.
Variable (n : nat).

(* Block diagonal embedding: ρ̂ = block_diag(ρ, (1-tr ρ)) ∈ 'M[C]_(n+1) *)
Definition embed_subnorm (rho : 'M[C]_n) : 'M[C]_(n + 1) :=
  block_mx rho 0 0 ((1 - \tr rho) *: 1%:M).

(* Generalized fidelity (matrix level, used by gfid):
   F̄(ρ,τ) = F(ρ̂,τ̂) *)
Definition gfidelity (rho tau : 'M[C]_n) : R :=
  @complex.Re R (trnorm (sqrtmx (embed_subnorm rho) *m sqrtmx (embed_subnorm tau))).

(* sqrtmx distributes over block-diagonal (A ⊕ scalar_1x1) when A is PSD and   *)
(* the 1×1 scalar block is nonneg-real. Derived via `mapf_mx_unique` applied to  *)
(* U = block_mx (spectralmx A) 0 0 1%:M and D = row_mx (spectral_diag A)         *)
(* (\row_i (a%:C)); sqrtmx of the scalar block uses `sqrtmxZ_nn` + `sqrtmx1`.    *)
(* The statement does not need a separate `0 <= a` hypothesis. For `a < 0`,       *)
(* `Num.sqrt a = 0` by MathComp's truncated-square-root convention                *)
(* (`ler0_sqrtr`), so the scalar block on the right is `0`, matching the          *)
(* spectral decomposition's treatment of the negative eigenvalue. This form        *)
(* is used by `sqrtmx_embed_subnorm_gen` and the generalized-fidelity             *)
(* Cauchy-Schwarz argument.                                                       *)
(* sqrtmx_block_diag_scalar *)
(* infra: no tex label — fundamental & reusable (mathcomp-style) *)
(* consumer: sqrtmx_block_diag_scalar is used downstream by the BB84 secrecy proof. *)
(* path: utils:sqrtmx_block_diag_scalar -> utils:sqrtmx_embed_subnorm -> *)
(*   utils:alt_gfid_gen -> bb84:privacy_amplification -> *)
(*   bb84:bb84_secret *)
Lemma sqrtmx_block_diag_scalar (rho : 'M[C]_n) (a : R) :
  rho \is psdmx ->
  sqrtmx (block_mx rho (0 : 'M[C]_(n,1)) (0 : 'M[C]_(1,n))
           ((a%:C) *: (1%:M : 'M[C]_1))) =
  block_mx (sqrtmx rho) (0 : 'M[C]_(n,1)) (0 : 'M[C]_(1,n))
           ((Num.sqrt a)%:C *: (1%:M : 'M[C]_1)).
Proof.
  move=> Prho.
  set f : C -> C := fun z => (Num.sqrt (@complex.Re R z))%:C.
  pose U := block_mx (spectralmx rho) (0 : 'M[C]_(n,1))
                     (0 : 'M[C]_(1,n)) (1%:M : 'M[C]_1).
  pose D := row_mx (spectral_diag rho) (\row_i (a%:C) : 'rV[C]_1).
  have HU : U \is unitarymx.
    by apply: mxdiag_unitary; [exact: spectral_unitarymx|exact: unitarymx1].
  have Hrho_spec :
      rho = (spectralmx rho)^*t *m diag_mx (spectral_diag rho) *m spectralmx rho.
    by move: (psdmx_herm Prho) => /hermmx_normal/eigen_dec; rewrite /eigenmx adjmxK.
  have scalar_diag : (a%:C) *: (1%:M : 'M[C]_1) = diag_mx (\row_i (a%:C) : 'rV[C]_1).
    rewrite scalemx1 -diag_const_mx; congr (diag_mx _).
    by apply/matrixP=> i j; rewrite !mxE.
  have Hdecomp :
      U^*t *m diag_mx D *m U =
      block_mx rho (0 : 'M[C]_(n,1)) (0 : 'M[C]_(1,n))
               ((a%:C) *: (1%:M : 'M[C]_1)).
    rewrite /U /D diag_mx_row adj_block_mx.
    rewrite !linear0 mulmx_block !mulmx0 !mul0mx !addr0 add0r.
    rewrite mulmx_block !mulmx0 !mul0mx !addr0 add0r.
    by rewrite -Hrho_spec adjmx1 mul1mx mulmx1 scalar_diag.
  have Hmap := mapf_mx_unique f HU Hdecomp.
  have sqrtE : sqrtmx (block_mx rho (0 : 'M[C]_(n,1)) (0 : 'M[C]_(1,n))
                                 ((a%:C) *: (1%:M : 'M[C]_1)))
             = mapf_mx f (block_mx rho (0 : 'M[C]_(n,1)) (0 : 'M[C]_(1,n))
                                    ((a%:C) *: (1%:M : 'M[C]_1))).
    by rewrite sqrtmx_mapfE.
  rewrite sqrtE -Hmap /U /D map_row_mx diag_mx_row adj_block_mx.
  rewrite !linear0 mulmx_block !mulmx0 !mul0mx !addr0 add0r.
  rewrite mulmx_block !mulmx0 !mul0mx !addr0 add0r.
  have Hul : (spectralmx rho)^*t
              *m diag_mx (map_mx f (spectral_diag rho))
              *m spectralmx rho = sqrtmx rho.
    by rewrite sqrtmx_mapfE mapf_mx.unlock.
  have Hlr : (1%:M : 'M[C]_1)^*t
              *m diag_mx (map_mx f (\row_i (a%:C) : 'rV[C]_1))
              *m (1%:M : 'M[C]_1)
             = (Num.sqrt a)%:C *: (1%:M : 'M[C]_1).
    rewrite adjmx1 mul1mx mulmx1.
    have map_scalar : map_mx f (\row_i (a%:C) : 'rV[C]_1)
                    = \row_i ((Num.sqrt a)%:C) :> 'rV[C]_1.
      apply/matrixP=> i j; rewrite !mxE /f.
      by rewrite re_realid.
    rewrite map_scalar.
    rewrite [in RHS]scalemx1 -[in RHS]diag_const_mx; congr (diag_mx _).
    by apply/matrixP=> i j; rewrite !mxE.
  by rewrite Hul Hlr.
Qed.

(* sqrtmx of the embedded subnormalized state (matrix form):                    *)
(*   √(ρ ⊕ (1 - tr ρ))  = √ρ ⊕ √(1 - tr ρ).                                     *)
(* This form does not require `Tr ρ <= 1`. When `Tr ρ > 1`, the scalar            *)
(* `1 - Tr ρ` is negative and `Num.sqrt` truncates to 0, so the embedded          *)
(* scalar block is 0. The unconstrained statement is used by the                  *)
(* generalized-fidelity Cauchy-Schwarz argument on non-subnormalized inputs.      *)
(* sqrtmx_embed_subnorm *)
(* infra: no tex label — fundamental & reusable (mathcomp-style) *)
(* consumer: sqrtmx_embed_subnorm is used downstream by the BB84 secrecy proof. *)
(* path: utils:sqrtmx_embed_subnorm -> utils:alt_gfid_gen -> *)
(*   bb84:privacy_amplification -> bb84:bb84_secret *)
Lemma sqrtmx_embed_subnorm (rho : 'M[C]_n) :
  rho \is psdmx ->
  sqrtmx (embed_subnorm rho) =
    block_mx (sqrtmx rho) (0 : 'M[C]_(n,1)) (0 : 'M[C]_(1,n))
      ((Num.sqrt (@complex.Re R (1 - \tr rho)))%:C *: (1%:M : 'M[C]_1)).
Proof.
  move=> Prho.
  pose c := @complex.Re R (1 - \tr rho).
  have trR : (\tr rho) \is Num.real by apply: ger0_real; apply: psdmx_trace.
  have cR : (1 - \tr rho) \is Num.real by apply: realB; [apply: real1|exact: trR].
  have c_eq : 1 - \tr rho = c%:C by rewrite /c RRe_real.
  rewrite /embed_subnorm c_eq.
  exact: (sqrtmx_block_diag_scalar _ Prho).
Qed.

(* tex: lm:alt-gfid — Tomamichel, "A Framework for Non-Asymptotic
   Quantum Information Theory" (PhD thesis, arXiv:1203.2142), Lemma 3.1
   math: F̄(ρ,τ) = F(ρ,τ) + sqrt((1-tr ρ)(1-tr τ)) *)

(* Generalized alt_gfid (Tier 4b for framework hmax upper bound).                   *)
(* Drops both sub-norm hypotheses; uses product-of-sqrts form.                  *)
(* When either cr or ct is negative (non-sub-norm arg), Num.sqrt truncates to 0 *)
(* by `ler0_sqrtr`, so the correction term vanishes and gfidelity = fidelity.    *)
(* alt_gfid_gen *)
(* infra: no tex label — fundamental & reusable (mathcomp-style) *)
(* consumer: alt_gfid_gen is used downstream by the BB84 secrecy proof. *)
(* path: utils:alt_gfid_gen -> bb84:privacy_amplification -> *)
(*   bb84:bb84_secret *)
Lemma alt_gfid_gen (rho tau : 'M[C]_n) :
  rho \is psdmx -> tau \is psdmx ->
  gfidelity rho tau =
    @complex.Re R (trnorm (sqrtmx rho *m sqrtmx tau)) +
    Num.sqrt (@complex.Re R (1 - \tr rho)) *
    Num.sqrt (@complex.Re R (1 - \tr tau)).
Proof.
  move=> Prho Ptau.
  pose cr := @complex.Re R (1 - \tr rho).
  pose ct := @complex.Re R (1 - \tr tau).
  have sqcr_nn : 0 <= Num.sqrt cr by apply: sqrtr_ge0.
  have sqct_nn : 0 <= Num.sqrt ct by apply: sqrtr_ge0.
  have prod_nn : 0 <= Num.sqrt cr * Num.sqrt ct by apply: mulr_ge0.
  rewrite /gfidelity (sqrtmx_embed_subnorm Prho) (sqrtmx_embed_subnorm Ptau).
  rewrite mulmx_block !mulmx0 !mul0mx !addr0 add0r.
  rewrite -scalemxAl -scalemxAr mulmx1 scalerA -rmorphM/=.
  rewrite (schnorm_mxdiag 1
     (sqrtmx rho *m sqrtmx tau)
     ((Num.sqrt cr * Num.sqrt ct)%:C *: (1%:M : 'M[C]_1))).
  rewrite l1normE !big_ord1 big_split_ord /=.
  under eq_bigr => j _.
    rewrite row_mxEl ger0_norm; last by apply: svd_d_ge0.
    over.
  rewrite big_ord1 row_mxEr ger0_norm; last by apply: svd_d_ge0.
  rewrite -trnorm_svdE.
  set c : C := (Num.sqrt cr * Num.sqrt ct)%:C.
  have c_nn_C : (0 : C) <= c by rewrite /c lecE /= eqxx /= prod_nn.
  have svd_d_scal1 : svd_d (c *: (1%:M : 'M[C]_1)) 0 ord0 = c.
    have trM_svd : trnorm (c *: (1%:M : 'M[C]_1))
                 = svd_d (c *: (1%:M : 'M[C]_1)) 0 ord0.
      by rewrite trnorm_svdE big_ord1.
    have trM_val : trnorm (c *: (1%:M : 'M[C]_1)) = c.
      by rewrite scalemx1 trnorm_scale mul1r ger0_norm.
    by rewrite -trM_svd trM_val.
  rewrite svd_d_scal1.
  by rewrite raddfD/= /c/=.
Qed.

(* gfid_ge0_mx *)
(* infra: no tex label — fundamental & reusable (mathcomp-style) *)
(* consumer: gfid_ge0_mx is used downstream by the BB84 secrecy proof. *)
(* path: utils:gfid_ge0_mx -> bb84:stat -> bb84:bb84_secret *)
Lemma gfid_ge0_mx (rho tau : 'M[C]_n) :
  rho \is psdmx -> tau \is psdmx ->
  0 <= gfidelity rho tau.
Proof.
  move=> _ _; rewrite /gfidelity.
  by have /= := trnorm_ge0 (sqrtmx (embed_subnorm rho) *m sqrtmx (embed_subnorm tau));
     rewrite lecE/= => /andP[_].
Qed.

(* Matrix-level Cauchy-Schwarz: trnorm(√ρ √τ) ≤ √(Tr ρ) · √(Tr τ) for PSD ρ,τ. *)
(* Direct port of fid_le_tr_mx's proof to 'M[C]_m via schnorm_hoelder_gen      *)
(* with p=1, q=r=2 (Hölder at the Hilbert-Schmidt endpoint).                     *)
(* trnorm_sqrt_cs *)
(* infra: no tex label — fundamental & reusable (mathcomp-style) *)
(* consumer: trnorm_sqrt_cs is used downstream by the BB84 secrecy proof. *)
(* path: utils:trnorm_sqrt_cs -> bb84:stat -> bb84:bb84_secret *)
Lemma trnorm_sqrt_cs {m : nat} (rhoM tauM : 'M[C]_m) :
  rhoM \is psdmx -> tauM \is psdmx ->
  @complex.Re R (trnorm (sqrtmx rhoM *m sqrtmx tauM))
    <= Num.sqrt (@complex.Re R (\tr rhoM)) * Num.sqrt (@complex.Re R (\tr tauM)).
Proof.
  move=> PrhoM PtauM.
  set a := sqrtmx rhoM; set b := sqrtmx tauM.
  have Ha_herm : a^*t = a.
    by apply/esym/hermmxP; exact: (sqrtmx_herm (psdmx_herm PrhoM)).
  have Hb_herm : b^*t = b.
    by apply/esym/hermmxP; exact: (sqrtmx_herm (psdmx_herm PtauM)).
  have Haa : a^*t *m a = rhoM by rewrite Ha_herm /a (sqrtmxK PrhoM).
  have Hbb : b^*t *m b = tauM by rewrite Hb_herm /b (sqrtmxK PtauM).
  set ta := \tr (a^*t *m a).
  set tb := \tr (b^*t *m b).
  have Hta : (0 : C) <= ta by rewrite /ta mxtrace_mulC; exact: form_tr_ge0.
  have Htb : (0 : C) <= tb by rewrite /tb mxtrace_mulC; exact: form_tr_ge0.
  have Hta_R : (0 : R) <= @complex.Re R ta.
    by move: Hta; rewrite lecE/= => /andP[_].
  have Htb_R : (0 : R) <= @complex.Re R tb.
    by move: Htb; rewrite lecE/= => /andP[_].
  have Hlhs : (0 : C) <= trnorm (a *m b) := trnorm_ge0 _.
  have Hlhs_R : (0 : R) <= @complex.Re R (trnorm (a *m b)).
    by move: Hlhs; rewrite lecE/= => /andP[_].
  have Hsch : trnorm (a *m b) <= l2norm a * l2norm b.
    rewrite l2norm_fbnorm.
    apply: schnorm_hoelder_gen; rewrite ?ler0n ?lexx ?orbT //.
    by rewrite invr1 split21.
  have HlN : 0 <= l2norm a * l2norm b by apply: mulr_ge0; apply: l2norm_ge0.
  have Hsq : (trnorm (a *m b)) ^+ 2 <= ta * tb.
    apply: (le_trans (y := (l2norm a * l2norm b) ^+ 2)).
      by apply: lerXn2r; rewrite ?nnegrE ?trnorm_ge0.
    have Ha2 : (l2norm a) ^+ 2 = ta.
      rewrite /ta l2norm_dotV.
      exact: sqrtCK.
    have Hb2 : (l2norm b) ^+ 2 = tb.
      rewrite /tb l2norm_dotV.
      exact: sqrtCK.
    by rewrite exprMn Ha2 Hb2.
  have HlR := ger0_real Hlhs.
  have HtaR := ger0_real Hta.
  have HtbR := ger0_real Htb.
  have Hsq2ge0 : (0 : C) <= trnorm (a *m b) ^+ 2.
    by rewrite expr2; apply: mulr_ge0; exact: Hlhs.
  have Htatb_ge0 : (0 : C) <= ta * tb := mulr_ge0 Hta Htb.
  have Hsq_R : (@complex.Re R (trnorm (a *m b))) ^+ 2
               <= @complex.Re R ta * @complex.Re R tb.
    have E1 : (@complex.Re R (trnorm (a *m b))) ^+ 2
              = @complex.Re R (trnorm (a *m b) ^+ 2).
      by rewrite -(RRe_real HlR) -rmorphXn re_realid.
    have E2 : @complex.Re R ta * @complex.Re R tb
              = @complex.Re R (ta * tb).
      have HtaC : (@complex.Re R ta)%:C = ta := RRe_real HtaR.
      have HtbC : (@complex.Re R tb)%:C = tb := RRe_real HtbR.
      rewrite -[LHS](re_realid (@complex.Re R ta * @complex.Re R tb)).
      congr (@complex.Re R _).
      transitivity ((@complex.Re R ta)%:C * (@complex.Re R tb)%:C).
        exact: realcM.
      exact: (congr2 (fun x y => x * y) HtaC HtbC).
    rewrite E1 E2.
    move: Hsq.
    rewrite -(RRe_real (ger0_real Hsq2ge0)).
    rewrite -(RRe_real (ger0_real Htatb_ge0)).
    by rewrite lecR.
  have Hge0_rho : 0 <= @complex.Re R (\tr rhoM).
    by rewrite -Haa; exact: Hta_R.
  rewrite -[leLHS]ger0_norm // -sqrtr_sqr -(sqrtrM _ Hge0_rho).
  apply: ler_wsqrtr.
  rewrite -Haa -Hbb -/ta -/tb.
  exact: Hsq_R.
Qed.

(* Under sub-normalization (Re(\tr ρ) ≤ 1), the block-diagonal embedding is PSD: *)
(*   ρ̂ = block_mx ρ 0 0 ((1-\tr ρ) *: 1%:M₁), factored as B*B^*t with             *)
(*   B = block_mx (sqrtmx ρ) 0 0 ((√(1-Re(\tr ρ)))%:C *: 1%:M).                  *)
(* embed_subnorm_psdmx *)
(* infra: no tex label — fundamental & reusable (mathcomp-style) *)
(* consumer: embed_subnorm_psdmx is used downstream by the BB84 secrecy proof. *)
(* path: utils:embed_subnorm_psdmx -> utils:pd_gtd_bar_lb -> *)
(*   bb84:privacy_amplification -> bb84:bb84_secret *)
Lemma embed_subnorm_psdmx (rho : 'M[C]_n) :
  rho \is denmx ->
  embed_subnorm rho \is psdmx.
Proof.
  move=> Hrho_den.
  have /denmxP [Prho HsnC] := Hrho_den.
  have Hsn : @complex.Re R (\tr rho) <= 1
    by move: HsnC; rewrite lecE /= => /andP [_].
  have tr_real : \tr rho \is Num.real by apply: ger0_real; exact: psdmx_trace.
  set c : R := 1 - @complex.Re R (\tr rho).
  have c_ge0 : 0 <= c by rewrite /c subr_ge0.
  have eq_1minus : 1 - \tr rho = c%:C.
    by rewrite -(RRe_real tr_real) /c rmorphB.
  pose Brho : 'M[C]_n := sqrtmx rho.
  pose Bscal : 'M[C]_1 := (Num.sqrt c)%:C *: 1%:M.
  pose F : 'M[C]_(n+1) := block_mx Brho (0 : 'M[C]_(n,1)) (0 : 'M[C]_(1,n)) Bscal.
  have Brho_herm : Brho^*t = Brho.
    by apply/esym/hermmxP; exact: (sqrtmx_herm (psdmx_herm Prho)).
  have Bscal_herm : Bscal^*t = Bscal.
    by rewrite /Bscal adjmxZ adjmx1 conjCc conjc_real.
  have BrhoK : Brho *m Brho^*t = rho.
    by rewrite Brho_herm /Brho (sqrtmxK Prho).
  have BscalK : Bscal *m Bscal^*t = (1 - \tr rho) *: 1%:M.
    rewrite Bscal_herm /Bscal eq_1minus.
    rewrite -scalemxAl -scalemxAr mulmx1 scalerA -rmorphM -expr2.
    by rewrite sqr_sqrtr.
  have -> : embed_subnorm rho = F *m F^*t.
    rewrite /embed_subnorm /F adj_block_mx !linear0 mulmx_block.
    rewrite BrhoK !mulmx0 !mul0mx !addr0 add0r BscalK.
    by [].
  exact: form_psd.
Qed.

(* Re(\tr (embed_subnorm ρ)) = 1 whenever ρ is PSD and sub-normalized. The       *)
(* scalar block carries exactly the "missing mass" 1 - \tr ρ.                    *)
(* embed_subnorm_tr_eq1 *)
(* infra: no tex label — fundamental & reusable (mathcomp-style) *)
(* consumer: embed_subnorm_tr_eq1 is used downstream by the BB84 secrecy proof. *)
(* path: utils:embed_subnorm_tr_eq1 -> utils:pd_gtd_bar_lb -> *)
(*   bb84:privacy_amplification -> bb84:bb84_secret *)
Lemma embed_subnorm_tr_eq1 (rho : 'M[C]_n) :
  rho \is denmx ->
  @complex.Re R (\tr (embed_subnorm rho)) = 1.
Proof.
  move=> _.
  rewrite /embed_subnorm mxtrace_block linearZ/= mxtrace1 mulr1.
  have ->: \tr rho + (1 - \tr rho) = (1 : C) by rewrite addrC subrK.
  by [].
Qed.

(* gfid_le1_mx *)
(* infra: no tex label — fundamental & reusable (mathcomp-style) *)
(* consumer: gfid_le1_mx is used downstream by the BB84 secrecy proof. *)
(* path: utils:gfid_le1_mx -> entropy:hminE_EFin -> *)
(*   bb84:privacy_amplification -> bb84:bb84_secret *)
Lemma gfid_le1_mx (rho tau : 'M[C]_n) :
  rho \is denmx -> tau \is denmx ->
  gfidelity rho tau <= 1.
Proof.
  move=> Hrho_den Htau_den.
  rewrite /gfidelity.
  apply: le_trans (trnorm_sqrt_cs (embed_subnorm_psdmx Hrho_den)
                                  (embed_subnorm_psdmx Htau_den)) _.
  rewrite (embed_subnorm_tr_eq1 Hrho_den) (embed_subnorm_tr_eq1 Htau_den).
  by rewrite sqrtr1 mulr1 lexx.
Qed.

(* Tier 4b — Cauchy-Schwarz bound on gfidelity² for non-sub-norm 2nd argument.   *)
(* Unlocks framework `hmax_ub`, `hmax_ub_log_gfid`, `hmax_ub_log` whose              *)
(* `hmax_feasible` exposes `I ⊗ σ` with trace `d · Tr σ > 1` when `d > 1`.        *)
(* Proof by case split: Tr σ ≤ 1 uses `gfid_le1_mx`; Tr σ > 1 uses             *)
(* `alt_gfid_gen` (correction term vanishes via `ler0_sqrtr`) + `trnorm_sqrt_cs`.*)
(* gfid_sq_le_max_mx *)
(* infra: no tex label — fundamental & reusable (mathcomp-style) *)
(* consumer: gfid_sq_le_max_mx is used downstream by the BB84 secrecy proof. *)
(* path: utils:gfid_sq_le_max_mx -> bb84:stat -> bb84:bb84_secret *)
Lemma gfid_sq_le_max_mx (rho sigma : 'M[C]_n) :
  rho \is denmx -> sigma \is psdmx ->
  (gfidelity rho sigma) ^+ 2 <= maxr 1 (@complex.Re R (\tr sigma)).
Proof.
  move=> Hrho_den Psig.
  have /denmxP [Prho Htr_rhoC] := Hrho_den.
  have Htr_rho : @complex.Re R (\tr rho) <= 1
    by move: Htr_rhoC; rewrite lecE /= => /andP [_].
  have Hgfid_ge0 : 0 <= gfidelity rho sigma := gfid_ge0_mx Prho Psig.
  case: (lerP (@complex.Re R (\tr sigma)) 1) => [Htr_sig | Htr_sig].
  - have Hsig_den : sigma \is denmx.
    { exact: denmx_psd_re_tr_le Psig Htr_sig. }
    have Hle1 : gfidelity rho sigma <= 1 :=
      gfid_le1_mx Hrho_den Hsig_den.
    have Hsq_le1 : (gfidelity rho sigma) ^+ 2 <= 1.
      by rewrite -[leRHS]mulr1; apply: ler_pM=> //; rewrite expr2 mulrC.
    by apply: (le_trans Hsq_le1).
  - have Htr_sig_neg : @complex.Re R (1 - \tr sigma) <= 0.
      by rewrite raddfB/= subr_le0 ltW.
    have Hsqrt_ct : Num.sqrt (@complex.Re R (1 - \tr sigma)) = 0
      by apply: ler0_sqrtr.
    have Hgfid_eq : gfidelity rho sigma =
      @complex.Re R (trnorm (sqrtmx rho *m sqrtmx sigma)).
      by rewrite (alt_gfid_gen Prho Psig) Hsqrt_ct mulr0 addr0.
    have Hfid_cs : @complex.Re R (trnorm (sqrtmx rho *m sqrtmx sigma))
                   <= Num.sqrt (@complex.Re R (\tr rho))
                      * Num.sqrt (@complex.Re R (\tr sigma))
      := trnorm_sqrt_cs Prho Psig.
    have Hgfid_cs : gfidelity rho sigma <=
      Num.sqrt (@complex.Re R (\tr rho)) * Num.sqrt (@complex.Re R (\tr sigma))
      by rewrite Hgfid_eq.
    have Htr_rho_ge0 : 0 <= @complex.Re R (\tr rho).
      by have /= := psdmx_trace Prho; rewrite lecE/= => /andP[_].
    have Htr_sig_ge0 : 0 <= @complex.Re R (\tr sigma).
      by have /= := psdmx_trace Psig; rewrite lecE/= => /andP[_].
    have Hsqrt_rho_nn : 0 <= Num.sqrt (@complex.Re R (\tr rho)) := sqrtr_ge0 _.
    have Hsqrt_sig_nn : 0 <= Num.sqrt (@complex.Re R (\tr sigma)) := sqrtr_ge0 _.
    have Hprod_nn : 0 <= Num.sqrt (@complex.Re R (\tr rho)) *
                         Num.sqrt (@complex.Re R (\tr sigma))
      by apply: mulr_ge0.
    have Hsq : (gfidelity rho sigma) ^+ 2 <=
      (Num.sqrt (@complex.Re R (\tr rho)) *
       Num.sqrt (@complex.Re R (\tr sigma))) ^+ 2
      by apply: lerXn2r; rewrite ?nnegrE.
    apply: (le_trans Hsq).
    rewrite exprMn !sqr_sqrtr//.
    apply: (le_trans (y := 1 * @complex.Re R (\tr sigma))).
      by apply: ler_pM.
    by rewrite mul1r.
Qed.

(* Reflexivity: for a PSD sub-normalized state ρ, the embedded matrix           *)
(* embed_subnorm ρ has trace exactly 1, and its sqrt squared is itself.         *)
(* Hence gfidelity ρ ρ = Re(trnorm(embed_subnorm ρ)) = 1 via psdmx_trnorm.      *)
(* gfid_refl_mx *)
(* infra: no tex label — fundamental & reusable (mathcomp-style) *)
(* consumer: gfid_refl_mx is used downstream by the BB84 secrecy proof. *)
(* path: utils:gfid_refl_mx -> utils:pur_dist_refl -> *)
(*   bb84:privacy_amplification -> bb84:bb84_secret *)
Lemma gfid_refl_mx (rho : 'M[C]_n) :
  rho \is denmx ->
  gfidelity rho rho = 1.
Proof.
  move=> Hrho_den.
  rewrite /gfidelity.
  have Pe : embed_subnorm rho \is psdmx := embed_subnorm_psdmx Hrho_den.
  by rewrite (sqrtmxK Pe) psdmx_trnorm// (embed_subnorm_tr_eq1 Hrho_den).
Qed.

(* gfid_sym_mx *)
(* infra: no tex label — fundamental & reusable (mathcomp-style) *)
(* consumer: gfid_sym_mx is used downstream by the BB84 secrecy proof. *)
(* path: utils:gfid_sym_mx -> bb84:privacy_amplification -> *)
(*   bb84:bb84_secret *)
Lemma gfid_sym_mx (rho tau : 'M[C]_n) :
  rho \is psdmx -> tau \is psdmx ->
  gfidelity rho tau = gfidelity tau rho.
Proof.
  move=> Prho Ptau.
  have embed_herm : forall sig : 'M[C]_n, sig \is psdmx ->
      embed_subnorm sig = (embed_subnorm sig)^*t.
    move=> sig Psig.
    rewrite /embed_subnorm adj_block_mx !linear0 adjmxZ adjmx1.
    have trR : (1 - \tr sig)^* = 1 - \tr sig.
      apply: conj_Creal; apply: rpredB; first by apply: real1.
      by apply: ger0_real; apply: psdmx_trace.
    rewrite trR.
    by move: Psig => /psdmx_herm /hermmxP <-.
  have Hr : sqrtmx (embed_subnorm rho) = (sqrtmx (embed_subnorm rho))^*t.
    apply/hermmxP; apply: sqrtmx_herm.
    by apply/hermmxP; apply: embed_herm.
  have Ht : sqrtmx (embed_subnorm tau) = (sqrtmx (embed_subnorm tau))^*t.
    apply/hermmxP; apply: sqrtmx_herm.
    by apply/hermmxP; apply: embed_herm.
  rewrite /gfidelity.
  by rewrite {1}Hr {1}Ht -adjmxM trnorm_adjmx.
Qed.

(* ================================================================== *)
(* Bridges between gfidelity and bare-matrix fidelity.                  *)
(* When tr rho = 1 (and Re tr tau <= 1), gfidelity reduces to the bare  *)
(* trnorm form trnorm(sqrtmx rho *m sqrtmx tau). Bridge 2 is the       *)
(* trivial zero-edge case used by consumers of hmax_mx-style proofs.   *)
(* ================================================================== *)

(* Bridge 1: when tr(rho) = 1, the embed-subnorm correction vanishes. *)
(* Math: alt_gfid_gen gives                                            *)
(*   gfid rho tau = Re(trnorm(sqrtmx rho * sqrtmx tau))                *)
(*               + sqrt(Re(1 - tr rho)) * sqrt(Re(1 - tr tau))         *)
(* tr rho = 1 ==> 1 - tr rho = 0 in C ==> Re(0) = 0 ==> sqrt 0 = 0,    *)
(* killing the correction-product factor.                              *)
(* gfid_eq_fid_tr1_mx *)
(* infra: no tex label - generalized-fidelity utility bridge *)
(* path: utils:gfid_eq_fid_tr1_mx -> entropy:entropy_data_proc -> *)
(*   bb84:bb84_secret *)
Lemma gfid_eq_fid_tr1_mx (rho tau : 'M[C]_n) :
  rho \is psdmx -> tau \is psdmx ->
  \tr rho = 1 -> @complex.Re R (\tr tau) <= 1 ->
  gfidelity rho tau =
    @complex.Re R (trnorm (sqrtmx rho *m sqrtmx tau)).
Proof.
  move=> Prho Ptau Htr1 _.
  (* Bridge1.1: invoke alt_gfid_gen to expand gfidelity. *)
  rewrite (alt_gfid_gen Prho Ptau).
  (* Bridge1.2: 1 - tr rho = 0 in C using tr rho = 1. *)
  have Hzero_C : (1 : C) - \tr rho = 0 by rewrite Htr1 subrr.
  (* Bridge1.3: Re(1 - tr rho) = 0 by linearity of Re at 0. *)
  have HRe_zero : @complex.Re R (1 - \tr rho) = 0.
    by rewrite Hzero_C linear0.
  (* Bridge1.4: sqrt 0 = 0 kills the correction factor; addr0 closes. *)
  by rewrite HRe_zero sqrtr0 mul0r addr0.
Qed.

(* Bridge 2: trivial trnorm zero case.                                 *)
(* Math: sqrtmx 0 = 0, then 0 *m _ = 0, trnorm 0 = 0, Re 0 = 0.        *)
(* Re_trnorm_sqrtmx_zero_left *)
(* infra: no tex label - generalized-fidelity utility bridge *)
(* path: utils:Re_trnorm_sqrtmx_zero_left -> utils:pd_mono -> *)
(*   entropy:entropy_data_proc -> *)
(*   bb84:bb84_secret *)
Lemma Re_trnorm_sqrtmx_zero_left (tau : 'M[C]_n) :
  @complex.Re R (trnorm (sqrtmx (0 : 'M[C]_n) *m sqrtmx tau)) = 0.
Proof.
  by rewrite sqrtmx0 mul0mx trnorm0 linear0.
Qed.

End GFidelity.

(* ================================================================== *)
(* Uhlmann/Gram route: Gram formulation of fidelity                     *)
(* ================================================================== *)

Section GramFidelity.

(* Gram form for (m ≤ n): fidelity of A A^† and B B^† equals ||A^† B||_1.      *)
(* Proof: polar decomp A = P_A U_A, B = P_B U_B. Then √(A A^†) = P_A, √(B B^†)   *)
(* = P_B via sqrtmx_psd_square. A^† B = U_A^† P_A P_B U_B; unitary invariance    *)
(* of trnorm absorbs U_A^†, U_B.                                                 *)
(* fid_gramE_mx *)
(* infra: no tex label — fundamental & reusable (mathcomp-style) *)
(* consumer: fid_gramE_mx is used downstream by the BB84 secrecy proof. *)
(* path: utils:fid_gramE_mx -> utils:fid_gram_general_mx -> *)
(*   utils:fid_iv_proj_mx -> bb84:stat -> bb84:bb84_secret *)
Lemma fid_gramE_mx {m n : nat} (A B : 'M[C]_(m, n)) :
  (m <= n)%N ->
  @complex.Re R (trnorm (sqrtmx (A *m A^*t) *m sqrtmx (B *m B^*t)))
    = @complex.Re R (trnorm (A^*t *m B)).
Proof.
  move=> Hmn.
  have [P [U [HPpsd [HPsq [HU HA]]]]] := polar_PU A Hmn.
  have [Q [V [HQpsd [HQsq [HV HB]]]]] := polar_PU B Hmn.
  have /hermmxP HPherm := psdmx_herm HPpsd.
  rewrite -HPsq -HQsq (sqrtmx_psd_square HPpsd) (sqrtmx_psd_square HQpsd).
  have -> : A^*t *m B = U^*t *m P *m Q *m V.
    rewrite HA HB.
    have -> : (P *m U)^*t = U^*t *m P by rewrite adjmxM -HPherm.
    by rewrite !mulmxA.
  congr (@complex.Re R _).
  rewrite -!mulmxA.
  rewrite (trnormUl_cond (U := U^*t) (P *m (Q *m V))); last by rewrite adjmxK; exact: HU.
  by rewrite mulmxA (trnormUr _ HV).
Qed.

(* General Gram form (no dim constraint): via zero-padding A, B to (m, n+m).     *)
(* fid_gram_general_mx *)
(* infra: no tex label — fundamental & reusable (mathcomp-style) *)
(* consumer: fid_gram_general_mx is used downstream by the BB84 secrecy proof. *)
(* General matrix Gram identity used by fidelity/purified-distance consumers. *)
(* path: utils:fid_gram_general_mx -> utils:fid_iv_proj_mx -> bb84:stat -> *)
(*   bb84:bb84_secret *)
Lemma fid_gram_general_mx {m n : nat} (A B : 'M[C]_(m, n)) :
  @complex.Re R (trnorm (sqrtmx (A *m A^*t) *m sqrtmx (B *m B^*t)))
    = @complex.Re R (trnorm (A^*t *m B)).
Proof.
  pose A' := row_mx A (0 : 'M[C]_(m, m)).
  pose B' := row_mx B (0 : 'M[C]_(m, m)).
  have HA' : A' *m A'^*t = A *m A^*t.
  { rewrite /A' adjmxE tr_row_mx map_col_mx -!adjmxE !raddf0.
    by rewrite mul_row_col !mul0mx addr0. }
  have HB' : B' *m B'^*t = B *m B^*t.
  { rewrite /B' adjmxE tr_row_mx map_col_mx -!adjmxE !raddf0.
    by rewrite mul_row_col !mul0mx addr0. }
  have HAB : A'^*t *m B' = block_mx (A^*t *m B) 0 0 (0 : 'M[C]_m).
  { rewrite /A' /B'.
    have -> : (row_mx A (0 : 'M[C]_(m, m)))^*t =
              col_mx A^*t (0 : 'M[C]_(m, m)).
    { by rewrite adjmxE tr_row_mx map_col_mx -!adjmxE !raddf0. }
    by rewrite mul_col_row !mulmx0 !mul0mx. }
  have Hdim : (m <= n + m)%N by exact: leq_addl.
  rewrite -HA' -HB' (fid_gramE_mx A' B' Hdim) HAB.
  by rewrite schnorm_block_mx000.
Qed.

(* Regroup factor: reshape (m*n, k) → (m, n*k) by folding second axis of the     *)
(* codomain back onto the domain's second axis.                                   *)
(* regroup_factor *)
(* infra: no tex label — fundamental & reusable (mathcomp-style) *)
(* consumer: regroup_factor is used downstream by the BB84 secrecy proof. *)
Definition regroup_factor {m n k : nat} (A : 'M[C]_((m * n), k)) :
  'M[C]_(m, n * k) :=
  \matrix_(i, j)
    let: (j1, j2) := mxtens_unindex j in
    A (mxtens_index (i, j1)) j2.

(* Trace identity for `regroup_factor` with (1⊗V). Used by the Uhlmann            *)
(* environment-unitary witness.                                                   *)
(* trace_regroup_tens1 *)
(* infra: no tex label — fundamental & reusable (mathcomp-style) *)
(* consumer: trace_regroup_tens1 is used downstream by the BB84 secrecy proof. *)
(* path: utils:trace_regroup_tens1 -> utils:pd_ext -> *)
(*   utils:ptrace_cast_psdlf -> lhl:min_coll_bound -> *)
(*   bb84:privacy_amplification -> bb84:bb84_secret *)
Lemma trace_regroup_tens1 {a b : nat} (V : 'M[C]_b) (v w : 'cV[C]_(a * b)) :
  let RA := castmx (erefl a, muln1 b) (regroup_factor v) in
  let RB := castmx (erefl a, muln1 b) (regroup_factor w) in
  \tr (v^*t *m ((1%:M : 'M[C]_a) *t V) *m w) =
  \tr (RA^*t *m RB *m V^T).
Proof.
  move=> RA RB.
  rewrite -mulmxA trace_mx11.
  transitivity
    (\sum_(s : 'I_a) \sum_(j : 'I_b)
      (v^*t) 0 (mxtens_index (s, j)) *
      (((1%:M : 'M[C]_a) *t V *m w) (mxtens_index (s, j)) 0)).
  { rewrite mxE (reindex_mxtens_index
      (fun l => (v^*t) 0 l * ((1%:M *t V *m w) l 0))).
    by rewrite pair_bigV. }
  transitivity
    (\sum_(s : 'I_a) \sum_(j : 'I_b)
      (v^*t) 0 (mxtens_index (s, j)) *
      (\sum_(k : 'I_b) V j k * w (mxtens_index (s, k)) 0)).
  { apply: eq_bigr => s _; apply: eq_bigr => j _.
    congr (_ * _).
    rewrite (tensmxE_mid ((1%:M : 'M[C]_a) *t V) w
      (mxtens_index (s, j)) 0).
    transitivity
      (\sum_(i1 : 'I_a)
        (s == i1)%:R *
        \sum_(i2 : 'I_b) V j i2 * w (mxtens_index (i1, i2)) 0).
    { apply: eq_bigr => i1 _; rewrite mulr_sumr.
      apply: eq_bigr => i2 _.
      by rewrite tensmxE mxE -mulrA. }
    rewrite (bigD1 s) //=.
    rewrite eqxx mul1r.
    rewrite [X in _ + X]big1 ?addr0 //.
    by move=> i1 Hi1; rewrite eq_sym (negPf Hi1) mul0r. }
  symmetry.
  transitivity
    (\sum_(l : 'I_b) \sum_(m0 : 'I_b)
      (\sum_(i : 'I_a) (v (mxtens_index (i, l)) 0)^* *
        w (mxtens_index (i, m0)) 0) * V l m0).
  { apply: eq_bigr => l _.
    rewrite mxE.
    apply: eq_bigr => m0 _ .
    congr (_ * _).
    { rewrite mxE.
      apply: eq_bigr => i _.
      rewrite !mxE.
      congr (_ * _).
      - rewrite /RA castmxE cast_ord_id mxtens_index1 /regroup_factor mxE.
        by rewrite mxtens_indexK.
      - rewrite /RB castmxE cast_ord_id mxtens_index1 /regroup_factor mxE.
        by rewrite mxtens_indexK. }
    { by rewrite mxE. } }
  under eq_bigr do under eq_bigr do rewrite mulr_suml.
  under eq_bigr do rewrite exchange_big /=.
  rewrite exchange_big /=.
  apply: eq_bigr => s _.
  apply: eq_bigr => j _.
  under eq_bigr do rewrite -mulrA.
  rewrite -mulr_sumr.
  have -> : (v (mxtens_index (s, j)) 0)^* = (v^*t) 0 (mxtens_index (s, j))
    by rewrite !mxE.
  congr (_ * _).
  apply: eq_bigr => k _.
  by rewrite mulrC.
Qed.

(* Key regroup identity: partial trace over second factor = regrouped Gram       *)
(* product.                                                                       *)
(* ptrace2_gram_regroup *)
(* infra: no tex label — fundamental & reusable (mathcomp-style) *)
(* consumer: ptrace2_gram_regroup is used downstream by the BB84 secrecy proof. *)
(* path: utils:ptrace2_gram_regroup -> utils:fid_ptr_mono_mx -> *)
(*   utils:gfid_ptr_mono_mx -> bb84:stat -> bb84:bb84_secret *)
Lemma ptrace2_gram_regroup {m n k : nat} (A : 'M[C]_((m * n), k)) :
  ptrace2 (A *m A^*t) =
  regroup_factor A *m (regroup_factor A)^*t.
Proof.
  have ptrace2E' : forall s t (B : 'M[C]_(s * t)) r1 r2,
    (ptrace2 B) r1 r2 = \sum_l B (mxtens_index (r1, l)) (mxtens_index (r2, l)).
    move=> s t B r1 r2; rewrite ptrace2E1 ptrace1E.
    by apply eq_bigr=> l _; rewrite mxE !mxtens_indexK.
  apply/matrixP=> i j.
  rewrite ptrace2E'.
  transitivity (\sum_(b : 'I_n) \sum_(c : 'I_k)
    A (mxtens_index (i, b)) c * (A^*t) c (mxtens_index (j, b))).
    apply: eq_bigr=> b _.
    by rewrite mxE.
  rewrite mxE.
  rewrite (reindex_mxtens_index
    (P := predT)
    (fun l : 'I_(n * k) =>
      regroup_factor A i l * (regroup_factor A)^*t l j)).
  rewrite pair_bigV /=.
  apply: eq_bigr=> b _.
  apply: eq_bigr=> c _.
  by rewrite adjmxE !mxE mxtens_indexK.
Qed.

(* Uhlmann environment-unitary witness. For pure states ρ_AB, θ₀ with             *)
(* marginals ρ_A, σ_A, there exists a unitary U on B such that the conjugated     *)
(* θ₀ has the same fidelity with ρ_AB as ρ_A has with σ_A.                         *)
(* Key ingredients: psdmx_rank1_form + polar_PU_UQ + trace_regroup_tens1 +        *)
(* fid_gram_general_mx + schnorm11 (1x1 trnorm = | entry |).                    *)
(* uhlmann_environment_unitary_witness *)
(* infra: no tex label — fundamental & reusable (mathcomp-style) *)
(* consumer: uhlmann_environment_unitary_witness is used downstream by the BB84 secrecy proof. *)
(* path: utils:uhlmann_environment_unitary_witness -> *)
(*   utils:uhlmann_fid_pure_witness_mx -> utils:fid_iii_uhl_mx -> *)
(*   utils:pd_gtd_bar_lb -> bb84:privacy_amplification -> *)
(*   bb84:bb84_secret *)
Lemma uhlmann_environment_unitary_witness {a b : nat}
    {rho_AB theta0 : 'M[C]_(a * b)} {rho_A sigma_A : 'M[C]_a} :
  rho_AB \is denmx ->
  \rank rho_AB = 1%N ->
  ptrace2 rho_AB = rho_A ->
  theta0 \is denmx ->
  \rank theta0 = 1%N ->
  ptrace2 theta0 = sigma_A ->
  exists U : 'M[C]_b,
    U \is unitarymx /\
    @complex.Re R (trnorm (sqrtmx rho_AB *m
      sqrtmx (((1%:M : 'M[C]_a) *t U) *m theta0
        *m (((1%:M : 'M[C]_a) *t U)^*t)))) =
    @complex.Re R (trnorm (sqrtmx rho_A *m sqrtmx sigma_A)).
Proof.
  move=> Hrho_den Hrho_rank Hptr_rho Htheta_den Htheta_rank Hptr_theta.
  have Hrho_psd : rho_AB \is psdmx by exact: denmx_psd.
  have Htheta_psd : theta0 \is psdmx by exact: denmx_psd.
  have [v Hv] := psdmx_rank1_form Hrho_psd Hrho_rank.
  have [w Hw] := psdmx_rank1_form Htheta_psd Htheta_rank.
  set RA := castmx (erefl a, muln1 b) (regroup_factor v).
  set RB := castmx (erefl a, muln1 b) (regroup_factor w).
  have HRA_AAt : RA *m RA^*t = regroup_factor v *m (regroup_factor v)^*t.
  { by rewrite /RA -(adjmx_castV (muln1 b, erefl a))
               (castmx_mul (muln1 b)) castmx_id. }
  have HRB_AAt : RB *m RB^*t = regroup_factor w *m (regroup_factor w)^*t.
  { by rewrite /RB -(adjmx_castV (muln1 b, erefl a))
               (castmx_mul (muln1 b)) castmx_id. }
  have HrhoA : rho_A = RA *m RA^*t.
  { by rewrite HRA_AAt -Hptr_rho Hv ptrace2_gram_regroup. }
  have HsigA : sigma_A = RB *m RB^*t.
  { by rewrite HRB_AAt -Hptr_theta Hw ptrace2_gram_regroup. }
  have [P [Q [U0 [HP [HQ [HPsq [HQsq [HU0 [Hleft Hright]]]]]]]]] :=
    polar_PU_UQ (RA^*t *m RB).
  exists (conjmx U0).
  have HcU0 : conjmx U0 \is unitarymx by rewrite conjmx_unitary.
  split; first exact HcU0.
  pose W := ((1%:M : 'M[C]_a) *t conjmx U0).
  have HW : W \is unitarymx.
  { by apply: unitarymx_tens; [exact: unitarymx1 | exact: HcU0]. }
  have Hconj_theta : W *m theta0 *m W^*t = (W *m w) *m (W *m w)^*t.
  { by rewrite Hw !mulmxA -(mulmxA (W *m w)) -adjmxM. }
  rewrite Hv Hconj_theta fid_gram_general_mx.
  have -> : v^*t *m (W *m w) = v^*t *m W *m w by rewrite mulmxA.
  rewrite HrhoA HsigA fid_gram_general_mx.
  have Hentry : (v^*t *m ((1%:M : 'M[C]_a) *t conjmx U0) *m w) 0 0 =
    \tr (RA^*t *m RB *m U0^*t).
  { rewrite -(trace_mx11 (v^*t *m ((1%:M : 'M[C]_a) *t conjmx U0) *m w)).
    rewrite (trace_regroup_tens1 (conjmx U0) v w) /=.
    by rewrite conjmxAT trmxK. }
  rewrite (schnorm11 1) Hentry.
  rewrite Hleft -mulmxA (unitarymxK HU0) mulmx1.
  have HP_nneg : 0 <= \tr P by exact: psdmx_trace.
  by rewrite (ger0_norm HP_nneg) (trnormUr _ HU0) (psdmx_trnorm HP).
Qed.

(* ptrace2 is invariant under right-tensor-unitary conjugation.                   *)
(* ptrace2_conj_tens_right *)
(* infra: no tex label — fundamental & reusable (mathcomp-style) *)
(* consumer: ptrace2_conj_tens_right is used downstream by the BB84 secrecy proof. *)
(* path: utils:ptrace2_conj_tens_right -> utils:pd_ext -> *)
(*   utils:ptrace_cast_psdlf -> lhl:min_coll_bound -> *)
(*   bb84:privacy_amplification -> bb84:bb84_secret *)
Lemma ptrace2_conj_tens_right {a b : nat} (U : 'M[C]_b) (A : 'M[C]_(a * b)) :
  U \is unitarymx ->
  ptrace2 (((1%:M : 'M[C]_a) *t U) *m A *m (((1%:M : 'M[C]_a) *t U)^*t)) =
  ptrace2 A.
Proof.
  move=> HU.
  have ptrace2E' : forall s t (B' : 'M[C]_(s * t)) r1 r2,
    (ptrace2 B') r1 r2 = \sum_l B' (mxtens_index (r1, l)) (mxtens_index (r2, l)).
  { move=> s t B' r1 r2.
    rewrite ptrace2E1 ptrace1E.
    by apply: eq_bigr => l _; rewrite mxE !mxtens_indexK. }
  apply/matrixP => i j.
  rewrite !ptrace2E'.
  pose Rt := (((1%:M : 'M[C]_a) *t U)^*t).
  have HleftMul : forall (B' : 'M[C]_(a * b)) (k : 'I_b) (t : 'I_(a * b)),
      (((1%:M : 'M[C]_a) *t U) *m B') (mxtens_index (i, k)) t =
      \sum_(k1 : 'I_b) U k k1 * B' (mxtens_index (i, k1)) t.
  { move=> B' k t.
    rewrite (tensmxE_mid (((1%:M : 'M[C]_a) *t U)) B' (mxtens_index (i, k)) t).
    transitivity
      (\sum_(i1 : 'I_a) \sum_(k1 : 'I_b)
        ((i == i1)%:R * U k k1) * B' (mxtens_index (i1, k1)) t).
    { apply: eq_bigr => i1 _.
      apply: eq_bigr => k1 _.
      by rewrite tensmxE !mxE -mulrA. }
    transitivity
      (\sum_(i1 : 'I_a)
        (i == i1)%:R *
        \sum_(k1 : 'I_b) U k k1 * B' (mxtens_index (i1, k1)) t).
    { apply: eq_bigr => i1 _.
      rewrite mulr_sumr.
      by apply: eq_bigr => k1 _; rewrite -mulrA. }
    rewrite (bigD1 i) //= eqxx mul1r.
    rewrite [X in _ + X]big1 ?addr0 //.
    by move=> i1 Hi1; rewrite eq_sym (negPf Hi1) mul0r. }
  have HrightMul : forall (k1 k : 'I_b),
      (A *m Rt) (mxtens_index (i, k1)) (mxtens_index (j, k)) =
      \sum_(k2 : 'I_b) A (mxtens_index (i, k1)) (mxtens_index (j, k2)) *
                         (U^*t) k2 k.
  { move=> k1 k.
    rewrite /Rt.
    rewrite (tensmxE_mid A (((1%:M : 'M[C]_a) *t U)^*t)
      (mxtens_index (i, k1)) (mxtens_index (j, k))).
    transitivity
      (\sum_(j1 : 'I_a) \sum_(k2 : 'I_b)
        ((j == j1)%:R * A (mxtens_index (i, k1)) (mxtens_index (j1, k2))) *
        (U^*t) k2 k).
    { apply: eq_bigr => j1 _.
      apply: eq_bigr => k2 _.
      rewrite /Rt adjmx_tens adjmx1.
      rewrite tensmxE !mxE eq_sym mulrA.
      rewrite [A _ _ * _]mulrC -mulrA //. }
    transitivity
      (\sum_(j1 : 'I_a)
        (j == j1)%:R *
        \sum_(k2 : 'I_b)
          A (mxtens_index (i, k1)) (mxtens_index (j1, k2)) * (U^*t) k2 k).
    { apply: eq_bigr => j1 _.
      rewrite mulr_sumr.
      by apply: eq_bigr => k2 _; rewrite -mulrA. }
    rewrite (bigD1 j) //= eqxx mul1r.
    rewrite [X in _ + X]big1 ?addr0 //.
    by move=> j1 Hj1; rewrite eq_sym (negPf Hj1) mul0r. }
  transitivity
    (\sum_(k : 'I_b) \sum_(k1 : 'I_b)
      U k k1 * (A *m Rt) (mxtens_index (i, k1)) (mxtens_index (j, k))).
  { apply: eq_bigr => k _.
    by rewrite -mulmxA HleftMul. }
  rewrite exchange_big /=.
  transitivity
    (\sum_(k1 : 'I_b) \sum_(k2 : 'I_b)
      A (mxtens_index (i, k1)) (mxtens_index (j, k2)) *
      \sum_(k : 'I_b) (U^*t) k2 k * U k k1).
  { apply: eq_bigr => k1 _.
    transitivity
      (\sum_(k : 'I_b) \sum_(k2 : 'I_b)
        A (mxtens_index (i, k1)) (mxtens_index (j, k2)) *
        ((U^*t) k2 k * U k k1)).
    - apply: eq_bigr => k _.
      rewrite HrightMul mulr_sumr.
      apply: eq_bigr => k2 _.
      rewrite mulrA [U k k1 * _]mulrC -mulrA.
      by rewrite [(U k k1) * _]mulrC.
    - rewrite exchange_big /=.
      apply: eq_bigr => k2 _.
      by rewrite -mulr_sumr. }
  transitivity
    (\sum_(k1 : 'I_b) \sum_(k2 : 'I_b)
      A (mxtens_index (i, k1)) (mxtens_index (j, k2)) * ((U^*t *m U) k2 k1)).
  { apply: eq_bigr => k1 _.
    by apply: eq_bigr => k2 _; rewrite mxE. }
  rewrite (unitarymxKV HU).
  transitivity
    (\sum_(k1 : 'I_b) A (mxtens_index (i, k1)) (mxtens_index (j, k1))).
  { apply: eq_bigr => k1 _.
    rewrite (bigD1 k1) //= mxE !eqxx /= mulr1.
    rewrite big1 ?addr0 //.
    move=> k2 Hk2; rewrite mxE.
    have -> : (k2 == k1) = false by rewrite (negPf Hk2).
    by rewrite /= mulr0. }
  by [].
Qed.

(* Uhlmann's theorem for pure states, relative to a given purification θ₀ of σ_A. *)
(* Given: ρ_AB rank-1 purifying ρ_A, and θ₀ any rank-1 purification of σ_A,        *)
(* construct θ purifying σ_A with matrix-fidelity equal to F(ρ_A, σ_A).            *)
(* uhlmann_fid_pure_witness_mx *)
(* infra: no tex label — fundamental & reusable (mathcomp-style) *)
(* consumer: uhlmann_fid_pure_witness_mx is used downstream by the BB84 secrecy proof. *)
(* path: utils:uhlmann_fid_pure_witness_mx -> utils:fid_iii_uhl_mx -> *)
(*   utils:pd_gtd_bar_lb -> bb84:privacy_amplification -> *)
(*   bb84:bb84_secret *)
Lemma uhlmann_fid_pure_witness_mx {a b : nat}
    {rho_AB theta0 : 'M[C]_(a * b)} {rho_A sigma_A : 'M[C]_a} :
  rho_AB \is denmx ->
  \rank rho_AB = 1%N ->
  ptrace2 rho_AB = rho_A ->
  theta0 \is denmx ->
  \rank theta0 = 1%N ->
  ptrace2 theta0 = sigma_A ->
  exists theta : 'M[C]_(a * b),
    theta \is denmx /\ \rank theta = 1%N /\
    ptrace2 theta = sigma_A /\
    @complex.Re R (trnorm (sqrtmx rho_AB *m sqrtmx theta))
      = @complex.Re R (trnorm (sqrtmx rho_A *m sqrtmx sigma_A)).
Proof.
  move=> Hrho_den Hrho_rank1 Hptrace_rho Htheta0_den Htheta0_rank Hptrace_theta0.
  have [U [HU Hfid]] :=
    uhlmann_environment_unitary_witness Hrho_den Hrho_rank1 Hptrace_rho
      Htheta0_den Htheta0_rank Hptrace_theta0.
  pose W := ((1%:M : 'M[C]_a) *t U).
  pose theta := W *m theta0 *m W^*t.
  have HW : W \is unitarymx by apply: unitarymx_tens; [exact: unitarymx1 | exact: HU].
  have HWle : W^*t *m W <= 1%:M by rewrite (unitarymxKV HW); apply: lexx.
  exists theta; split; last split; last split.
  - exact: denmx_conj_contraction HWle Htheta0_den.
  - by rewrite /theta mxrank_mulmxUC ?mxrank_mulUmx ?HW ?Htheta0_rank.
  - by rewrite /theta ptrace2_conj_tens_right ?HU.
  - exact Hfid.
Qed.

(* Matrix-level fidelity invariance under unitary conjugation. Forward-infra for *)
(* the ptrace-DPI route labelled `pd_mono_ptrace`: consumer is the `tenv_mxU`     *)
(* permutation step bridging `h2mx (\Tr_([set B]) rho)` to matrix-level           *)
(* `ptrace1/2 (h2mx rho)`.                                                        *)
(* fid_unitary_conj_mx *)
(* infra: no tex label — fundamental & reusable (mathcomp-style) *)
(* consumer: fid_unitary_conj_mx is used downstream by the BB84 secrecy proof. *)
(* path: utils:fid_unitary_conj_mx -> utils:fid_ptr_mono -> *)
(*   entropy:entropy_data_proc -> *)
(*   bb84:bb84_secret *)
Lemma fid_unitary_conj_mx {n : nat} (U : 'M[C]_n) (rho sigma : 'M[C]_n) :
  U \is unitarymx ->
  rho \is psdmx ->
  sigma \is psdmx ->
  @complex.Re R (trnorm (sqrtmx (U *m rho *m U^*t)
                          *m sqrtmx (U *m sigma *m U^*t))) =
  @complex.Re R (trnorm (sqrtmx rho *m sqrtmx sigma)).
Proof.
  move=> HU Hrho Hsigma.
  rewrite !sqrtmx_unitary_conj//.
  have -> :
      (U *m sqrtmx rho *m U^*t) *m (U *m sqrtmx sigma *m U^*t) =
      U *m (sqrtmx rho *m sqrtmx sigma) *m U^*t.
    rewrite !mulmxA -(mulmxA _ U^*t U).
    by rewrite (unitarymxKV HU) mulmx1.
  have HU_adj : U^*t \is unitarymx by rewrite adjmx_unitary HU.
  by rewrite (trnormUr _ HU_adj) (trnormUl _ HU).
Qed.

(* Matrix-level Uhlmann's theorem for pure states (fidelity form). When          *)
(* rho_AB is rank-1 and purifies rho_A, any denmx sigma_A with rank ≤ dim B      *)
(* admits a rank-1 purification theta with the same matrix-fidelity.             *)
(* fid_iii_uhl_mx *)
(* infra: no tex label — fundamental & reusable (mathcomp-style) *)
(* consumer: fid_iii_uhl_mx is used downstream by the BB84 secrecy proof. *)
(* path: utils:fid_iii_uhl_mx -> utils:pd_gtd_bar_lb -> *)
(*   bb84:privacy_amplification -> bb84:bb84_secret *)
Lemma fid_iii_uhl_mx {a b : nat}
    {rho_AB : 'M[C]_(a * b)} {rho_A sigma_A : 'M[C]_a} :
  rho_AB \is denmx ->
  \rank rho_AB = 1%N ->
  ptrace2 rho_AB = rho_A ->
  sigma_A \is denmx ->
  sigma_A != 0 ->
  (\rank sigma_A <= b)%N ->
  exists theta : 'M[C]_(a * b),
    theta \is denmx /\ \rank theta = 1%N /\
    ptrace2 theta = sigma_A /\
    @complex.Re R (trnorm (sqrtmx rho_AB *m sqrtmx theta))
      = @complex.Re R (trnorm (sqrtmx rho_A *m sqrtmx sigma_A)).
Proof.
  move=> Hrho_den Hrho_rank1 Hptrace Hsigma_den Hsigma_nz Hsigma_rank.
  have [theta0 [Htheta0_den [Htheta0_rank Htheta0_ptrace]]] :=
    purification_exists_in_dim Hsigma_den Hsigma_nz Hsigma_rank.
  exact: uhlmann_fid_pure_witness_mx Hrho_den Hrho_rank1 Hptrace
    Htheta0_den Htheta0_rank Htheta0_ptrace.
Qed.

Section Uhlmann.
Variable (L : finType) (HL : L -> chsType) (A B : {set L}).
Hypothesis disAB : [disjoint A & B].
Hypothesis dimAB : dim 'H[HL]_A = dim 'H[HL]_B.
Notation S_AB := (A :|: B).

(* tex: lemma:uhlmann-pure (LHL arXiv:1002.2436, Uhlmann pure-state form).  Re-statement: phi must  *)
(* be a PURE purification (rank 1 + den1lf trace-1), tau sub-normalized        *)
(* non-zero with rank <= dim H_B.  Matches Tomamichel: rho tau in S_leq(H), H iso   *)
(* H, phi in H tensor H purification of rho.                                   *)
(* Proof route: h2mx bridge to matrix-level fid_iii_uhl_mx + tenv_mxU        *)
(* unitary conjugation.  Deferred: dim unification between h2mx phi on        *)
(* dim H_S_AB and matrix-level M_phi on dim H_A * dim H_B requires castmx.    *)
(* fid_iii_uhl *)
(* infra: no tex label — fundamental & reusable (mathcomp-style) *)
(* Labelled-level Uhlmann surface. Matrix-level consumers may use          *)
(* `fid_iii_uhl_mx` directly; this theorem keeps the set-labelled API      *)
(* available for modules that state purified-distance facts over labels.   *)
Lemma fid_iii_uhl (phi : 'F[HL]_S_AB) (tau : 'F[HL]_A) :
  phi \is den1lf -> \Rank phi = 1%N ->
  tau \is denlf -> h2mx tau != 0 ->
  (\Rank tau <= dim 'H[HL]_B)%N ->
  exists (psi : 'F[HL]_S_AB),
    psi \is denlf /\ \Rank psi = 1%N /\
    ptrace_cast disAB psi = tau /\
    fidelity phi psi = fidelity (ptrace_cast disAB phi) tau.
Proof.
  move=> Hphi_den1 Hphi_rank Htau_den Htau_mx_nz Htau_rankB.
  (* Preserve API compatibility: ensure section discharge generalizes over   *)
  (* dimAB.  (Original version was generalized over all section              *)
  (* hypotheses; downstream consumers like pd_uhl pass dimAB as 6th arg.)    *)
  have _ : dim 'H[HL]_A = dim 'H[HL]_B := dimAB.
  (* Matrix bridge setup: U conjugates h2mx phi (on dim 'H_S_AB) to *)
  (* 'M_(dim 'H_A * dim 'H_B) where matrix-level Uhlmann lives. *)
  pose U := @tenv_mxU R L HL A B.
  have HU : U \is unitarymx := tenv_mxU_unitarymx _ _.
  have HUadj : U^*t \is unitarymx := tenv_mxU_adj_unitarymx disAB.
  have U_mul_Uadj : U *m U^*t = 1%:M := unitarymxK HU.
  have Uadj_mul_U : U^*t *m U = 1%:M.
  { by have := unitarymxK HUadj; rewrite adjmxK. }
  (* Matrix images of phi and tau. *)
  have Hphi_psd : phi \is psdlf := den1lf_psd Hphi_den1.
  have Hphi_mx_psd : h2mx phi \is psdmx by move: Hphi_psd; rewrite qualifE.
  have Htau_psd : tau \is psdlf := denlf_psd Htau_den.
  have Htau_mx_psd : h2mx tau \is psdmx by move: Htau_psd; rewrite qualifE.
  have Htau_mx_den : h2mx tau \is denmx by move: Htau_den; rewrite qualifE.
  pose rho_AB := U^*t *m h2mx phi *m U.
  pose sigma_A := h2mx tau.
  (* Matrix-level rho_AB is den1mx and rank 1. *)
  have Hphi_mx_den1 : h2mx phi \is den1mx by move: Hphi_den1; rewrite qualifE.
  have HrhoAB_psd : rho_AB \is psdmx.
  { rewrite /rho_AB -[U in _ *m _ *m U]adjmxK.
    exact: psdmx_bimap_closed_gen Hphi_mx_psd. }
  have HrhoAB_tr1 : \tr rho_AB = 1.
  { rewrite /rho_AB mxtrace_mulC mulmxA U_mul_Uadj mul1mx.
    by have /den1mxP [_ /eqP] := Hphi_mx_den1. }
  have HrhoAB_den1 : rho_AB \is den1mx by apply/den1mxP; split=> //; rewrite HrhoAB_tr1.
  have HrhoAB_rank : \rank rho_AB = 1%N.
  { rewrite /rho_AB (mxrank_mulmxU _ HU) (mxrank_mulUCmx _ HU).
    by rewrite -/(\Rank phi) Hphi_rank. }
  (* sigma_A is denmx, nonzero, and rank ≤ dim 'H_B. *)
  have Hsigma_den : sigma_A \is denmx by [].
  have Hsigma_nz : sigma_A != 0 by [].
  have Hsigma_rank : (\rank sigma_A <= dim 'H[HL]_B)%N by [].
  (* Matrix-level ptrace identity: ptrace2 rho_AB = h2mx (ptrace_cast phi). *)
  have Hptr_mx : ptrace2 rho_AB = h2mx (ptrace_cast disAB phi).
  { by rewrite /rho_AB -(h2mx_ptrace_cast_ptrace2 disAB phi). }
  (* Apply matrix-level Uhlmann's theorem to obtain theta. *)
  have [theta [Htheta_den [Htheta_rank [Htheta_ptrace Htheta_fid]]]] :=
    fid_iii_uhl_mx (den1mx_den HrhoAB_den1) HrhoAB_rank Hptr_mx
      Hsigma_den Hsigma_nz Hsigma_rank.
  (* Lift theta back to 'F[HL]_S_AB via U *m _ *m U^*t and mx2h. *)
  pose psi : 'F[HL]_S_AB := mx2h (U *m theta *m U^*t).
  have Htheta_psd : theta \is psdmx by move/denmxP: Htheta_den => [].
  have Hpsi_h2mx : h2mx psi = U *m theta *m U^*t by rewrite /psi mx2hK.
  have Hpsi_mx_psd : h2mx psi \is psdmx.
  { by rewrite Hpsi_h2mx; exact: psdmx_bimap_closed_gen. }
  have Hpsi_psd : psi \is psdlf by rewrite qualifE Hpsi_mx_psd.
  (* Trace of psi = trace of theta ≤ 1. *)
  have Hpsi_tr_eq : \tr (h2mx psi) = \tr theta.
  { rewrite Hpsi_h2mx mxtrace_mulC mulmxA Uadj_mul_U mul1mx.
    by []. }
  have Hpsi_tr_le1 : \tr (h2mx psi) <= 1.
  { rewrite Hpsi_tr_eq.
    by have /denmxP [_] := Htheta_den. }
  have Hpsi_den : psi \is denlf.
  { rewrite qualifE.
    apply/denmxP; split.
    - exact: Hpsi_mx_psd.
    - exact: Hpsi_tr_le1. }
  (* Rank of psi = rank of theta = 1. *)
  have Hpsi_rank : \Rank psi = 1%N.
  { rewrite /lfrank Hpsi_h2mx.
    rewrite (mxrank_mulmxU _ HUadj).
    rewrite -[U]adjmxK (mxrank_mulUCmx _ HUadj).
    by rewrite Htheta_rank. }
  (* Matrix relation: U^*t *m h2mx psi *m U = theta. *)
  have HM_psi_theta : U^*t *m h2mx psi *m U = theta.
  { rewrite Hpsi_h2mx !mulmxA Uadj_mul_U mul1mx -mulmxA Uadj_mul_U mulmx1.
    by []. }
  (* ptrace_cast disAB psi = tau via h2mx-injectivity. *)
  have Hpsi_ptr : ptrace_cast disAB psi = tau.
  { apply/h2mx_inj.
    rewrite (h2mx_ptrace_cast_ptrace2 disAB psi) -/U HM_psi_theta.
    exact: Htheta_ptrace. }
  (* Fidelity equation: lift the matrix-level identity via                   *)
  (* fid_unitary_conj_mx.  Uses the `tenv_dim disAB` cast trick (cf.    *)
  (* gfid_tenv_mxU_conj_eq_mx, fid.v:1238-1243) to make U square.          *)
  have Hfid_eq : fidelity phi psi = fidelity (ptrace_cast disAB phi) tau.
  { rewrite /fidelity !h2mx_comp !sqrtH_h2mx.
    (* Express h2mx phi = U *m rho_AB *m U^*t. *)
    have HphiE : h2mx phi = U *m rho_AB *m U^*t.
    { transitivity (U *m U^*t *m h2mx phi *m U *m U^*t).
      { by rewrite U_mul_Uadj mul1mx -mulmxA U_mul_Uadj mulmx1. }
      by rewrite /rho_AB !mulmxA. }
    rewrite HphiE Hpsi_h2mx.
    (* Note: sigma_A = h2mx tau, so the RHS already has the form expected.   *)
    (* Apply Htheta_fid first to rewrite the RHS, then fid_unitary_conj_mx.*)
    rewrite -/sigma_A -Htheta_fid.
    (* Goal: Re(trnorm (sqrtmx (U *m rho_AB *m U^*t)                          *)
    (*                  *m sqrtmx (U *m theta *m U^*t)))                      *)
    (*     = Re(trnorm (sqrtmx rho_AB *m sqrtmx theta))                       *)
    (* This is fid_unitary_conj_mx after dim-cast.                       *)
    (* Clear psi-related items first, since psi depends on theta.            *)
    clearbody psi.
    clear Hpsi_h2mx Hpsi_ptr Hpsi_rank HM_psi_theta
          Hpsi_tr_eq Hpsi_tr_le1 Hpsi_den Hpsi_psd Hpsi_mx_psd psi.
    clear U_mul_Uadj Uadj_mul_U HphiE.
    (* Now generalize U, rho_AB, theta into abstract square matrices.        *)
    move: HU HrhoAB_psd Htheta_psd.
    move: rho_AB theta {HrhoAB_den1 HrhoAB_tr1 HrhoAB_rank
                        Htheta_den Htheta_rank Htheta_ptrace
                        Hphi_mx_den1 Hptr_mx Htheta_fid}.
    move: U HUadj.
    case: _ / (esym (tenv_dim disAB)) => U HUadj rho_AB theta HU HrhoAB_psd
      Htheta_psd.
    exact: fid_unitary_conj_mx HU HrhoAB_psd Htheta_psd. }
  exists psi; do !split=> //.
Qed.

End Uhlmann.

(* ================================================================== *)
(* path: utils:fid_iv_proj_mx -> bb84:stat -> bb84:bb84_secret *)
Lemma fid_iv_proj_mx {n : nat}
    (P rho tau : 'M[C]_n) :
  P \is projmx ->
  rho \is psdmx ->
  tau \is psdmx ->
  let rhoP := P *m rho *m P in
  let tauP := P *m tau *m P in
  [/\ @complex.Re R (trnorm (sqrtmx rhoP *m sqrtmx tau))
        = @complex.Re R (trnorm (sqrtmx rhoP *m sqrtmx tauP)) &
      @complex.Re R (trnorm (sqrtmx rhoP *m sqrtmx tauP))
        = @complex.Re R (trnorm (sqrtmx rho *m sqrtmx tauP))].
Proof.
  move=> Pproj Prho Ptau.
  pose rhoP := P *m rho *m P.
  pose tauP := P *m tau *m P.
  have /projmxP_id [/hermmxP HPherm HPid] := Pproj.
  have HrhoP : rhoP \is psdmx.
  { have -> : rhoP = P *m rho *m P^*t.
    { rewrite /rhoP. by rewrite [P in _ *m _ *m P]HPherm. }
    exact: psdmx_bimap_closed_gen Prho. }
  have HtauP : tauP \is psdmx.
  { have -> : tauP = P *m tau *m P^*t.
    { rewrite /tauP. by rewrite [P in _ *m _ *m P]HPherm. }
    exact: psdmx_bimap_closed_gen Ptau. }
  have Hproj_left :
      @complex.Re R (trnorm (sqrtmx rhoP *m sqrtmx tau))
        = @complex.Re R (trnorm (sqrtmx rhoP *m sqrtmx tauP)).
  { pose S := P *m sqrtmx rho.
    pose T := sqrtmx tau.
    pose Tp := P *m sqrtmx tau.
    have /hermmxP HSrho_herm : sqrtmx rho \is hermmx
      by exact: sqrtmx_herm (psdmx_herm Prho).
    have /hermmxP HStau_herm : sqrtmx tau \is hermmx
      by exact: sqrtmx_herm (psdmx_herm Ptau).
    have HSrho_sq : sqrtmx rho *m sqrtmx rho = rho := sqrtmxK Prho.
    have HStau_sq : sqrtmx tau *m sqrtmx tau = tau := sqrtmxK Ptau.
    have HSrho_form : sqrtmx rho *m (sqrtmx rho)^*t = rho.
      by rewrite -HSrho_herm HSrho_sq.
    have HStau_form : sqrtmx tau *m (sqrtmx tau)^*t = tau.
      by rewrite -HStau_herm HStau_sq.
    have HS : rhoP = S *m S^*t.
    { rewrite /rhoP.
      have -> : S *m S^*t = P *m rho *m P.
      { have -> : S *m S^*t = P *m (sqrtmx rho *m (sqrtmx rho)^*t) *m P.
          by rewrite /S adjmxM -HPherm -!mulmxA.
        by rewrite HSrho_form. }
      by []. }
    have HT : tau = T *m T^*t by rewrite /T HStau_form.
    have HTp : tauP = Tp *m Tp^*t.
    { rewrite /tauP.
      have -> : Tp *m Tp^*t = P *m tau *m P.
      { have -> : Tp *m Tp^*t = P *m (sqrtmx tau *m (sqrtmx tau)^*t) *m P.
          by rewrite /Tp adjmxM -HPherm -!mulmxA.
        by rewrite HStau_form. }
      by []. }
    rewrite HS HT HTp.
    rewrite (fid_gram_general_mx S T).
    rewrite (fid_gram_general_mx S Tp).
    have -> : S^*t *m T = (sqrtmx rho)^*t *m P *m sqrtmx tau.
      by rewrite /S /T adjmxM -HPherm mulmxA.
    have -> : S^*t *m Tp = (sqrtmx rho)^*t *m P *m sqrtmx tau.
    { rewrite /S /Tp adjmxM -HPherm.
      have -> :
          (sqrtmx rho)^*t *m P *m (P *m sqrtmx tau) =
          (sqrtmx rho)^*t *m (P *m P) *m sqrtmx tau
        by rewrite !mulmxA.
      by rewrite HPid. }
    by []. }
  have Hproj_right :
      @complex.Re R (trnorm (sqrtmx rhoP *m sqrtmx tauP))
        = @complex.Re R (trnorm (sqrtmx rho *m sqrtmx tauP)).
  { pose S := sqrtmx rho.
    pose Sp := P *m sqrtmx rho.
    pose T := P *m sqrtmx tau.
    have /hermmxP HSrho_herm : sqrtmx rho \is hermmx
      by exact: sqrtmx_herm (psdmx_herm Prho).
    have /hermmxP HStau_herm : sqrtmx tau \is hermmx
      by exact: sqrtmx_herm (psdmx_herm Ptau).
    have HSrho_sq : sqrtmx rho *m sqrtmx rho = rho := sqrtmxK Prho.
    have HStau_sq : sqrtmx tau *m sqrtmx tau = tau := sqrtmxK Ptau.
    have HSrho_form : sqrtmx rho *m (sqrtmx rho)^*t = rho.
      by rewrite -HSrho_herm HSrho_sq.
    have HStau_form : sqrtmx tau *m (sqrtmx tau)^*t = tau.
      by rewrite -HStau_herm HStau_sq.
    have HS : rho = S *m S^*t by rewrite /S HSrho_form.
    have HSp : rhoP = Sp *m Sp^*t.
    { rewrite /rhoP.
      have -> : Sp *m Sp^*t = P *m rho *m P.
      { have -> : Sp *m Sp^*t = P *m (sqrtmx rho *m (sqrtmx rho)^*t) *m P.
          by rewrite /Sp adjmxM -HPherm -!mulmxA.
        by rewrite HSrho_form. }
      by []. }
    have HT : tauP = T *m T^*t.
    { rewrite /tauP.
      have -> : T *m T^*t = P *m tau *m P.
      { have -> : T *m T^*t = P *m (sqrtmx tau *m (sqrtmx tau)^*t) *m P.
          by rewrite /T adjmxM -HPherm -!mulmxA.
        by rewrite HStau_form. }
      by []. }
    rewrite HS HSp HT.
    rewrite (fid_gram_general_mx Sp T).
    rewrite (fid_gram_general_mx S T).
    have -> : Sp^*t *m T = (sqrtmx rho)^*t *m P *m sqrtmx tau.
    { rewrite /Sp /T adjmxM -!HPherm.
      have -> :
          (sqrtmx rho)^*t *m P *m (P *m sqrtmx tau) =
          (sqrtmx rho)^*t *m (P *m P) *m sqrtmx tau
        by rewrite !mulmxA.
      by rewrite HPid. }
    have -> : S^*t *m T = (sqrtmx rho)^*t *m P *m sqrtmx tau
      by rewrite /S /T mulmxA.
    reflexivity. }
  by split.
Qed.

(* ================================================================== *)
(* path: utils:fid_v_mono_r_psd_mx -> entropy:entropy_data_proc -> *)
(*   bb84:bb84_secret *)
Lemma fid_v_mono_r_psd_mx {n : nat}
    (rho sigma tau : 'M[C]_n) :
  rho \is psdmx ->
  sigma \is psdmx ->
  tau \is psdmx ->
  sigma <= tau ->
  @complex.Re R (trnorm (sqrtmx rho *m sqrtmx sigma)) <=
  @complex.Re R (trnorm (sqrtmx rho *m sqrtmx tau)).
Proof.
  move=> Hrho Hsigma Htau Hle.
  have Hdiff_psd : (tau - sigma) \is psdmx.
  { by move: Hle; rewrite le_lownerE. }
  have [P HP] := psdmx_form Hrho.
  have [Q HQ] := psdmx_form Hsigma.
  have [W HW] := psdmx_form Hdiff_psd.
  pose E := row_mx Q W.
  have Hadj_row :
      forall k1 k2 (A : 'M[C]_(n, k1)) (B : 'M[C]_(n, k2)),
        (row_mx A B)^*t = col_mx A^*t B^*t.
  { by move=> k1 k2 A B; rewrite /adjmx tr_row_mx map_col_mx. }
  have Hadj0 : forall k1 k2, (0 : 'M[C]_(k1, k2))^*t = 0.
  { by move=> k1 k2; rewrite /adjmx trmx0 map_mx0. }
  have HE : tau = E *m E^*t.
  { rewrite /E Hadj_row mul_row_col -HQ -HW addrC subrK. reflexivity. }
  pose P' := row_mx P (0 : 'M[C]_(n, n)).
  have HP' : rho = P' *m P'^*t.
  { rewrite /P' Hadj_row mul_row_col Hadj0 mulmx0 addr0. exact: HP. }
  have Hf_sigma :
      @complex.Re R (trnorm (sqrtmx rho *m sqrtmx sigma))
        = @complex.Re R (trnorm (P^*t *m Q)).
  { by rewrite HP HQ fid_gram_general_mx. }
  have Hf_tau :
      @complex.Re R (trnorm (sqrtmx rho *m sqrtmx tau))
        = @complex.Re R (trnorm (P'^*t *m E)).
  { by rewrite HP' HE fid_gram_general_mx. }
  rewrite Hf_sigma Hf_tau.
  suff Hcle : \tr| P^*t *m Q | <= \tr| P'^*t *m E |.
  { have Hr1 : \tr| P^*t *m Q | \is Num.real by exact: schnorm_real.
    have Hr2 : \tr| P'^*t *m E | \is Num.real by exact: schnorm_real.
    by move: Hcle; rewrite -(RRe_real Hr1) -(RRe_real Hr2) lecR. }
  have Hprod : P'^*t *m E =
      block_mx (P^*t *m Q) (P^*t *m W) (0 : 'M[C]_(n, n)) (0 : 'M[C]_(n, n)).
  { rewrite /P' /E Hadj_row mul_col_row Hadj0 !mul0mx. reflexivity. }
  rewrite Hprod /block_mx row_mx0 schnorm_col_mx0.
  have Hfactor :
      P^*t *m Q =
      row_mx (P^*t *m Q) (P^*t *m W) *m
      col_mx (1%:M : 'M[C]_n) (0 : 'M[C]_n).
  { by rewrite mul_row_col mulmx1 mulmx0 addr0. }
  set M := row_mx (P^*t *m Q) (P^*t *m W).
  set V := col_mx (1%:M : 'M[C]_n) (0 : 'M[C]_(n, n)).
  have Hunitary_row :
      (row_mx (1%:M : 'M[C]_n) (0 : 'M[C]_(n, n))) \is unitarymx.
    exact: (row_mx0_unitarymx _ (unitarymx1 _ _)).
  have Hi2_V : i2norm V = (n != 0)%:R.
  { rewrite /V -i2norm_adjmx.
    rewrite adjmxE tr_col_mx map_row_mx -!adjmxE adjmx1 linear0.
    exact: i2norm_unitary Hunitary_row. }
  rewrite Hfactor.
  apply: (le_trans (schnormMl 1 M V)).
  rewrite Hi2_V.
  case: (boolP (n != 0)%N) => Hn.
  - by rewrite mulr1.
  - move/negPn/eqP: Hn => Hn0.
    subst n.
    by rewrite /M !mx_dim0E schnorm0.
Qed.

(* ================================================================== *)
(* path: utils:fid_vi_block_diag_mx -> utils:pd_mono -> *)
(*   entropy:entropy_data_proc -> *)
(*   bb84:bb84_secret *)
Lemma fid_vi_block_diag_mx {m k : nat}
    (rho1 tau1 : 'M[C]_m) (rho2 tau2 : 'M[C]_k) :
  rho1 \is psdmx -> tau1 \is psdmx ->
  rho2 \is psdmx -> tau2 \is psdmx ->
  @complex.Re R (trnorm (sqrtmx (block_mx rho1 0 0 rho2)
                         *m sqrtmx (block_mx tau1 0 0 tau2))) =
  @complex.Re R (trnorm (sqrtmx rho1 *m sqrtmx tau1)) +
  @complex.Re R (trnorm (sqrtmx rho2 *m sqrtmx tau2)).
Proof.
  move=> Hrho1 Htau1 Hrho2 Htau2.
  (* Inline sqrtmx_block_diag: sqrt of block-diag PSD is block-diag of sqrts *)
  have Hsqrt_bd : forall (m0 k0 : nat) (A : 'M[C]_m0) (B : 'M[C]_k0),
      A \is psdmx -> B \is psdmx ->
      sqrtmx (block_mx A 0 0 B) = block_mx (sqrtmx A) 0 0 (sqrtmx B).
  { move=> m0 k0 A B PA PB.
    set UA := spectralmx A. set UB := spectralmx B.
    set DA := spectral_diag A. set DB := spectral_diag B.
    pose U : 'M[C]_(m0 + k0) := block_mx UA 0 0 UB.
    pose D : 'rV[C]_(m0 + k0) := row_mx DA DB.
    pose f (z : C) : C := (Num.sqrt (@complex.Re R z))%:C.
    have HUA : UA \is unitarymx by apply: spectral_unitarymx.
    have HUB : UB \is unitarymx by apply: spectral_unitarymx.
    have HU : U \is unitarymx by apply: mxdiag_unitary.
    have A_normal : A \is normalmx by apply/hermmx_normal/psdmx_herm.
    have B_normal : B \is normalmx by apply/hermmx_normal/psdmx_herm.
    have decA : UA^*t *m diag_mx DA *m UA = A.
      by move/eigen_dec: A_normal; rewrite /eigenmx -/UA -/DA adjmxK => <-.
    have decB : UB^*t *m diag_mx DB *m UB = B.
      by move/eigen_dec: B_normal; rewrite /eigenmx -/UB -/DB adjmxK => <-.
    have decAB : U^*t *m diag_mx D *m U = block_mx A 0 0 B.
      rewrite /U /D diag_mx_row adj_block_mx !linear0.
      rewrite mulmx_block !mulmx0 !mul0mx !addr0 !add0r.
      by rewrite mulmx_block !mulmx0 !mul0mx !addr0 !add0r decA decB.
    have Hmap := mapf_mx_unique f HU decAB.
    have sqrtA_eq : sqrtmx A = UA^*t *m diag_mx (map_mx f DA) *m UA.
      by rewrite sqrtmx_mapfE (mapf_mx_unique f HUA decA).
    have sqrtB_eq : sqrtmx B = UB^*t *m diag_mx (map_mx f DB) *m UB.
      by rewrite sqrtmx_mapfE (mapf_mx_unique f HUB decB).
    rewrite sqrtmx_mapfE -Hmap /U /D map_row_mx diag_mx_row adj_block_mx !linear0.
    rewrite mulmx_block !mulmx0 !mul0mx !addr0 !add0r.
    rewrite mulmx_block !mulmx0 !mul0mx !addr0 !add0r.
    by rewrite -sqrtA_eq -sqrtB_eq. }
  (* Inline trnorm_block_diag *)
  have Htrnorm_bd : forall (m1 n1 k1 l1 : nat)
      (A : 'M[C]_(m1, n1)) (B : 'M[C]_(k1, l1)),
      trnorm (block_mx A 0 0 B) = trnorm A + trnorm B.
  { move=> m1 n1 k1 l1 A B.
    rewrite [LHS](_ : _ = lpnorm 1 (row_mx (svd_d A) (svd_d B)));
      last exact: schnorm_mxdiag.
    rewrite l1normE big_ord1 big_split_ord/=.
    rewrite !trnorm_svdE; congr (_ + _).
    - by apply: eq_bigr => i _; rewrite row_mxEl ger0_norm// svd_d_ge0.
    - by apply: eq_bigr => i _; rewrite row_mxEr ger0_norm// svd_d_ge0. }
  rewrite (Hsqrt_bd _ _ _ _ Hrho1 Hrho2) (Hsqrt_bd _ _ _ _ Htau1 Htau2).
  have -> :
      block_mx (sqrtmx rho1) 0 0 (sqrtmx rho2) *m
      block_mx (sqrtmx tau1) 0 0 (sqrtmx tau2) =
      block_mx (sqrtmx rho1 *m sqrtmx tau1) 0 0
               (sqrtmx rho2 *m sqrtmx tau2).
  { by rewrite mulmx_block !mulmx0 !mul0mx !addr0 !add0r. }
  by rewrite Htrnorm_bd raddfD.
Qed.

(* Matrix ordinary fidelity invariance under a rectangular isometry. *)
(* infra: no tex label — reusable plain-fidelity isometry bridge      *)
(* path: utils:fid_isometry_conj_mx -> utils:pd_mono -> *)
(*   entropy:entropy_data_proc -> *)
(*   bb84:bb84_secret *)
Lemma fid_isometry_conj_mx {m n : nat}
    (W : 'M[C]_(m, n)) (rho sigma : 'M[C]_m) :
  W \is unitarymx ->
  rho \is psdmx ->
  sigma \is psdmx ->
  @complex.Re R
    (trnorm (sqrtmx (W^*t *m rho *m W) *m
             sqrtmx (W^*t *m sigma *m W))) =
  @complex.Re R (trnorm (sqrtmx rho *m sqrtmx sigma)).
Proof.
  move=> HW Hrho Hsigma.
  have Hadj_row :
      forall k1 k2 (A0 : 'M[C]_(n, k1)) (B0 : 'M[C]_(n, k2)),
        (row_mx A0 B0)^*t = col_mx A0^*t B0^*t.
  {
    by move=> k1 k2 A0 B0; rewrite /adjmx tr_row_mx map_col_mx.
  }
  have Hmn : (m <= n)%N by exact: unitary_dim HW.
  have Emn : (m + (n - m) = n)%N by exact: subnKC Hmn.
  pose Uc0 := castmx (Emn, erefl n)
              (schmidt (col_mx W (0 : 'M[C]_(n - m, n)))).
  pose Uc := Uc0^*t.
  pose Ucview := castmx (erefl n, esym Emn) Uc.
  pose rho0 := block_mx rho (0 : 'M[C]_(m, n - m))
                        (0 : 'M[C]_(n - m, m)) (0 : 'M[C]_(n - m)).
  pose sigma0 := block_mx sigma (0 : 'M[C]_(m, n - m))
                          (0 : 'M[C]_(n - m, m)) (0 : 'M[C]_(n - m)).
  pose rho0sq := castmx (Emn, Emn) rho0.
  pose sigma0sq := castmx (Emn, Emn) sigma0.
  have HUc0 : Uc0 \is unitarymx.
  {
    rewrite /Uc0 castmx_funE.
    by apply/schmidt_unitarymx; rewrite subnKC.
  }
  have HUc : Uc \is unitarymx.
  {
    rewrite /Uc.
    exact: adjmx_unitaryP HUc0.
  }
  have HWl : lsubmx Ucview = W^*t.
  {
    have -> :
        Ucview =
        (schmidt (col_mx W (0 : 'M[C]_(n - m, n))))^*t.
    {
      apply/adjmx_inj.
      rewrite /Ucview /Uc /Uc0 adjmx_castV.
      by rewrite castmx_comp /= etrans_esym castmx_id.
    }
    have -> :
        lsubmx
          ((schmidt (col_mx W (0 : 'M[C]_(n - m, n))))^*t) =
        (usubmx (schmidt (col_mx W (0 : 'M[C]_(n - m, n)))))^*t.
    {
      apply/matrixP=> i j.
      by rewrite !mxE.
    }
    apply/adjmx_inj.
    rewrite adjmxK.
    rewrite adjmxK.
    symmetry.
    exact: unitary_ext HW.
  }
  have Hrho0 : rho0 \is psdmx.
  {
    pose R0 := col_mx (sqrtmx rho) (0 : 'M[C]_(n - m, m)).
    have /hermmxP HSrho_herm : sqrtmx rho \is hermmx
      by exact: sqrtmx_herm (psdmx_herm Hrho).
    have H0adj : (0 : 'M[C]_(n - m, m))^*t = (0 : 'M[C]_(m, n - m)).
    {
      apply/matrixP=> i j.
      by rewrite !mxE conjC0.
    }
    have -> : rho0 = R0 *m R0^*t.
    {
      rewrite /rho0 /R0 adjmxE tr_col_mx map_row_mx -!adjmxE H0adj.
      rewrite mul_col_row ?mulmx0 ?mul0mx ?add0r ?addr0.
      by rewrite -HSrho_herm (sqrtmxK Hrho).
    }
    exact: form_psd.
  }
  have Hsigma0 : sigma0 \is psdmx.
  {
    pose S0 := col_mx (sqrtmx sigma) (0 : 'M[C]_(n - m, m)).
    have /hermmxP HSsigma_herm : sqrtmx sigma \is hermmx
      by exact: sqrtmx_herm (psdmx_herm Hsigma).
    have H0adj : (0 : 'M[C]_(n - m, m))^*t = (0 : 'M[C]_(m, n - m)).
    {
      apply/matrixP=> i j.
      by rewrite !mxE conjC0.
    }
    have -> : sigma0 = S0 *m S0^*t.
    {
      rewrite /sigma0 /S0 adjmxE tr_col_mx map_row_mx -!adjmxE H0adj.
      rewrite mul_col_row ?mulmx0 ?mul0mx ?add0r ?addr0.
      by rewrite -HSsigma_herm (sqrtmxK Hsigma).
    }
    exact: form_psd.
  }
  have Hrho0sq : rho0sq \is psdmx.
  {
    rewrite /rho0sq /castmx_sq.
    exact: castmx_sq_psdmx Hrho0.
  }
  have Hsigma0sq : sigma0sq \is psdmx.
  {
    rewrite /sigma0sq /castmx_sq.
    exact: castmx_sq_psdmx Hsigma0.
  }
  have HUcview_adj : Ucview^*t = castmx (esym Emn, erefl n) Uc^*t.
    by rewrite /Ucview adjmx_castV.
  have Hrho_sq :
      Ucview *m rho0 *m Ucview^*t = Uc *m rho0sq *m Uc^*t.
  {
    have -> : rho0 = castmx (esym Emn, esym Emn) rho0sq.
      by rewrite /rho0sq castmxK.
    by rewrite HUcview_adj /Ucview -!mulmxA !castmx_mul castmx_id.
  }
  have Hsigma_sq :
      Ucview *m sigma0 *m Ucview^*t = Uc *m sigma0sq *m Uc^*t.
  {
    have -> : sigma0 = castmx (esym Emn, esym Emn) sigma0sq.
      by rewrite /sigma0sq castmxK.
    by rewrite HUcview_adj /Ucview -!mulmxA !castmx_mul castmx_id.
  }
  have Hrho_embed_view :
      Ucview *m rho0 *m Ucview^*t = W^*t *m rho *m W.
  {
    rewrite /rho0 -[Ucview]hsubmxK HWl /block_mx row_mx0.
    have Hrow_adj :
        (row_mx W^*t (rsubmx Ucview))^*t =
        col_mx W (rsubmx Ucview)^*t.
    {
      rewrite (Hadj_row _ _ W^*t (rsubmx Ucview)).
      by rewrite adjmxK.
    }
    rewrite Hrow_adj.
    rewrite mul_row_col ?mulmx0 ?addr0.
    rewrite mul_mx_row ?mulmx0.
    by rewrite mul_row_col ?mul0mx ?addr0.
  }
  have Hsigma_embed_view :
      Ucview *m sigma0 *m Ucview^*t = W^*t *m sigma *m W.
  {
    rewrite /sigma0 -[Ucview]hsubmxK HWl /block_mx row_mx0.
    have Hrow_adj :
        (row_mx W^*t (rsubmx Ucview))^*t =
        col_mx W (rsubmx Ucview)^*t.
    {
      rewrite (Hadj_row _ _ W^*t (rsubmx Ucview)).
      by rewrite adjmxK.
    }
    rewrite Hrow_adj.
    rewrite mul_row_col ?mulmx0 ?addr0.
    rewrite mul_mx_row ?mulmx0.
    by rewrite mul_row_col ?mul0mx ?addr0.
  }
  have Hrho_embed : Uc *m rho0sq *m Uc^*t = W^*t *m rho *m W.
    by rewrite -Hrho_sq Hrho_embed_view.
  have Hsigma_embed : Uc *m sigma0sq *m Uc^*t = W^*t *m sigma *m W.
    by rewrite -Hsigma_sq Hsigma_embed_view.
  rewrite -Hrho_embed -Hsigma_embed.
  rewrite (fid_unitary_conj_mx HUc Hrho0sq Hsigma0sq).
  clear Hrho0sq Hsigma0sq Hrho_sq Hsigma_sq
    Hrho_embed_view Hsigma_embed_view Hrho_embed Hsigma_embed.
  rewrite /rho0sq /sigma0sq /castmx_sq.
  have Hcast :
      @complex.Re R
        (trnorm (sqrtmx (castmx (Emn, Emn) rho0) *m
                 sqrtmx (castmx (Emn, Emn) sigma0))) =
      @complex.Re R (trnorm (sqrtmx rho0 *m sqrtmx sigma0)).
  {
    have Hcast_gen :
        forall n' (e : (m + (n - m))%N = n')
               (A0 B0 : 'M[C]_(m + (n - m))),
          @complex.Re R
            (trnorm (sqrtmx (castmx (e, e) A0) *m
                     sqrtmx (castmx (e, e) B0))) =
          @complex.Re R (trnorm (sqrtmx A0 *m sqrtmx B0)).
    {
      move=> n' e A0 B0.
      subst n'.
      by rewrite !castmx_id.
    }
    exact: (Hcast_gen n Emn rho0 sigma0).
  }
  rewrite Hcast.
  pose R0 := col_mx (sqrtmx rho) (0 : 'M[C]_(n - m, m)).
  pose S0 := col_mx (sqrtmx sigma) (0 : 'M[C]_(n - m, m)).
  have Hrho0_form : rho0 = R0 *m R0^*t.
  {
    have /hermmxP HSrho_herm : sqrtmx rho \is hermmx
      by exact: sqrtmx_herm (psdmx_herm Hrho).
    have H0adj : (0 : 'M[C]_(n - m, m))^*t = (0 : 'M[C]_(m, n - m)).
    {
      apply/matrixP=> i j.
      by rewrite !mxE conjC0.
    }
    rewrite /rho0 /R0 adjmxE tr_col_mx map_row_mx -!adjmxE H0adj.
    rewrite mul_col_row ?mulmx0 ?mul0mx ?add0r ?addr0.
    by rewrite -HSrho_herm (sqrtmxK Hrho).
  }
  have Hsigma0_form : sigma0 = S0 *m S0^*t.
  {
    have /hermmxP HSsigma_herm : sqrtmx sigma \is hermmx
      by exact: sqrtmx_herm (psdmx_herm Hsigma).
    have H0adj : (0 : 'M[C]_(n - m, m))^*t = (0 : 'M[C]_(m, n - m)).
    {
      apply/matrixP=> i j.
      by rewrite !mxE conjC0.
    }
    rewrite /sigma0 /S0 adjmxE tr_col_mx map_row_mx -!adjmxE H0adj.
    rewrite mul_col_row ?mulmx0 ?mul0mx ?add0r ?addr0.
    by rewrite -HSsigma_herm (sqrtmxK Hsigma).
  }
  rewrite [rho0]Hrho0_form [sigma0]Hsigma0_form.
  rewrite (fid_gram_general_mx R0 S0).
  have /hermmxP HSrho_herm : sqrtmx rho \is hermmx
    by exact: sqrtmx_herm (psdmx_herm Hrho).
  rewrite /R0 /S0 adjmxE tr_col_mx map_row_mx -!adjmxE.
  rewrite mul_row_col ?mulmx0 ?mul0mx ?add0r ?addr0.
  by rewrite -HSrho_herm.
Qed.

(* Generalized fidelity invariance under unitary conjugation. Lifts           *)
(* `fid_unitary_conj_mx` to `gfidelity` via `embed_subnorm`.             *)
(* Consumer: pd_unitary_conj_OV (utils/dist/pd.v).                            *)
(* Key algebraic identity: embed_subnorm (U ρ U^†) = block_diag(U, 1%:M)      *)
(* × embed_subnorm ρ × block_diag(U, 1%:M)^†, using trace invariance          *)
(* (Tr (U ρ U^†) = Tr ρ) and block multiplication.                            *)
(* gfid_unitary_conj_mx *)
(* infra: no tex label — fundamental & reusable (mathcomp-style) *)
(* consumer: gfid_unitary_conj_mx is used downstream by the BB84 secrecy proof. *)
(* path: utils:gfid_unitary_conj_mx -> utils:pd_mono -> *)
(*   entropy:entropy_data_proc -> *)
(*   bb84:bb84_secret *)
Lemma gfid_unitary_conj_mx {n : nat}
    (U : 'M[C]_n) (rho sigma : 'M[C]_n) :
  U \is unitarymx ->
  rho \is denmx -> sigma \is denmx ->
  gfidelity (U *m rho *m U^*t) (U *m sigma *m U^*t) = gfidelity rho sigma.
Proof.
  move=> HU Hrho_den Hsigma_den.
  rewrite /gfidelity.
  pose M : 'M[C]_(n+1) := block_mx U (0 : 'M_(n,1)) (0 : 'M_(1,n)) (1%:M : 'M[C]_1).
  have HM : M \is unitarymx.
  { rewrite /M.
    have H1 : (1%:M : 'M[C]_1) \is unitarymx := @unitarymx1 C 1%N.
    by have := mxdiag_unitary HU H1; apply. }
  have HtrU : \tr (U *m rho *m U^*t) = \tr rho.
  { by rewrite mxtrace_mulC mulmxA (unitarymxKV HU) mul1mx. }
  have HtrU' : \tr (U *m sigma *m U^*t) = \tr sigma.
  { by rewrite mxtrace_mulC mulmxA (unitarymxKV HU) mul1mx. }
  have Heq : forall (tau : 'M[C]_n), \tr (U *m tau *m U^*t) = \tr tau ->
    embed_subnorm (U *m tau *m U^*t) = M *m embed_subnorm tau *m M^*t.
  { move=> tau Htr_tau; rewrite /embed_subnorm /M Htr_tau.
    rewrite adj_block_mx !raddf0 adjmx1.
    rewrite mulmx_block !(mulmx0, mul0mx, addr0, add0r, mulmx1, mul1mx).
    rewrite mulmx_block !(mulmx0, mul0mx, addr0, add0r, mulmx1, mul1mx).
    by []. }
  rewrite (Heq _ HtrU) (Heq _ HtrU').
  exact: fid_unitary_conj_mx HM
    (embed_subnorm_psdmx Hrho_den)
    (embed_subnorm_psdmx Hsigma_den).
Qed.

(* Sub-norm matrix isometry-conjugation invariance for `gfidelity`. Generalizes  *)
(* `gfid_unitary_conj_mx` from square unitary U to a rectangular column-     *)
(* isometry V : 'M[C]_(m, n) (V^*t is unitarymx, equivalently V^*t mul V = 1,    *)
(* i.e. V has orthonormal columns). The proof reduces to two pieces:             *)
(*   (i)  trace cycling: tr (V . rho . V^*t) = tr rho                            *)
(*        (using V^*t . V = 1 to absorb V from the right via mxtrace_mulC),      *)
(*   (ii) Gram-form trnorm identity:                                             *)
(*        Re(trnorm(sqrtmx (V . rho . V^*t) . sqrtmx (V . sigma . V^*t)))        *)
(*           = Re(trnorm(sqrtmx rho . sqrtmx sigma))                              *)
(*        via `fid_gram_general_mx` applied to A := V . sqrtmx rho and B :=    *)
(*        V . sqrtmx sigma, plus V^*t . V = 1 to cancel the V-sandwich           *)
(*        inside A^*t . B.                                                        *)
(* The two pieces combine through `alt_gfid_gen`: the correction term            *)
(* sqrt(1 - tr) . sqrt(1 - tr) is preserved by (i) and the trnorm term by (ii).  *)
(* tex: df:gfid invariance — Tomamichel, 'A Framework for Non-Asymptotic         *)
(*   Quantum Information Theory' (PhD thesis, arXiv:1203.2142), Definition 3.2 + *)
(* standard Uhlmann-style sub-norm isometry invariance used implicitly in        *)
(* pd_mono / Stinespring proofs.                                                  *)
(* Reusable infra for any lift-state-through-Stinespring-isometry-then-operate-  *)
(* then-descend argument and for the matrix sub-norm Uhlmann family of lemmas.   *)
(* gfid_isometry_conj_psd_mx *)
(* infra: no tex label — fundamental & reusable (mathcomp-style) *)
(* path: utils:gfid_isometry_conj_psd_mx -> utils:gfid_isometry_conj_mx -> *)
(*   utils:subnorm_matrix_uhlmann_in_image -> utils:gfid_cast_mx -> *)
(*   entropy:entropy_data_proc -> *)
(*   bb84:bb84_secret *)
Lemma gfid_isometry_conj_psd_mx {m n : nat}
    (V : 'M[C]_(m, n)) (rho sigma : 'M[C]_n) :
  V^*t \is unitarymx ->
  rho \is psdmx -> sigma \is psdmx ->
  gfidelity (V *m rho *m V^*t) (V *m sigma *m V^*t) = gfidelity rho sigma.
Proof.
  move=> HVi Hrho Hsigma.
  (* trace preservation via cyclicity + V^*t . V = 1. *)
  have HVtV : V^*t *m V = 1%:M.
    have := unitarymxK HVi. by rewrite adjmxK.
  have HtrV : forall (tau : 'M[C]_n), \tr (V *m tau *m V^*t) = \tr tau.
    move=> tau.
    rewrite mxtrace_mulC mulmxA HVtV.
    by rewrite mul1mx.
  (* PSD preservation under V . _ . V^*t (via form_psdmx). *)
  have HVrV_psd : V *m rho *m V^*t \is psdmx := form_psdmx V Hrho.
  have HVsV_psd : V *m sigma *m V^*t \is psdmx := form_psdmx V Hsigma.
  (* apply alt_gfid_gen on both sides. *)
  rewrite (alt_gfid_gen HVrV_psd HVsV_psd) (alt_gfid_gen Hrho Hsigma).
  (* Correction terms match by trace preservation. *)
  rewrite !HtrV.
  congr (_ + _).
  (* Gram-form trnorm identity using fid_gram_general_mx. *)
  have HSr_herm : (sqrtmx rho)^*t = sqrtmx rho.
    by apply/esym/hermmxP; apply: sqrtmx_herm; exact: psdmx_herm Hrho.
  have HSs_herm : (sqrtmx sigma)^*t = sqrtmx sigma.
    by apply/esym/hermmxP; apply: sqrtmx_herm; exact: psdmx_herm Hsigma.
  set A : 'M[C]_(m, n) := V *m sqrtmx rho.
  set B : 'M[C]_(m, n) := V *m sqrtmx sigma.
  have HAA : A *m A^*t = V *m rho *m V^*t.
    rewrite /A adjmxM HSr_herm -mulmxA -mulmxA.
    by rewrite (mulmxA (sqrtmx rho)) (sqrtmxK Hrho) mulmxA.
  have HBB : B *m B^*t = V *m sigma *m V^*t.
    rewrite /B adjmxM HSs_herm -mulmxA -mulmxA.
    by rewrite (mulmxA (sqrtmx sigma)) (sqrtmxK Hsigma) mulmxA.
  have HAB : A^*t *m B = sqrtmx rho *m sqrtmx sigma.
    rewrite /A /B adjmxM HSr_herm.
    rewrite -mulmxA (mulmxA V^*t V) HVtV mul1mx.
    by [].
  have Hgram_LHS := fid_gram_general_mx A B.
  rewrite HAA HBB HAB in Hgram_LHS.
  (* RHS sqrtmx . sqrtmx is itself in gram form via square A' = sqrtmx rho. *)
  set A' : 'M[C]_n := sqrtmx rho.
  set B' : 'M[C]_n := sqrtmx sigma.
  have HA'A' : A' *m A'^*t = rho.
    rewrite /A' HSr_herm. exact: sqrtmxK Hrho.
  have HB'B' : B' *m B'^*t = sigma.
    rewrite /B' HSs_herm. exact: sqrtmxK Hsigma.
  have HA'B' : A'^*t *m B' = sqrtmx rho *m sqrtmx sigma.
    by rewrite /A' /B' HSr_herm.
  have Hgram_RHS := fid_gram_general_mx A' B'.
  rewrite HA'A' HB'B' HA'B' in Hgram_RHS.
  by rewrite Hgram_LHS -Hgram_RHS.
Qed.

(* gfid_isometry_conj_mx *)
(* infra: no tex label — wrapper for subnormalized gfidelity call sites. *)
(* consumer: gfid_isometry_conj_mx is used downstream by the BB84 secrecy proof. *)
(* path: utils:gfid_isometry_conj_mx -> *)
(*   utils:subnorm_matrix_uhlmann_in_image -> utils:gfid_cast_mx -> *)
(*   entropy:entropy_data_proc -> *)
(*   bb84:bb84_secret *)
Lemma gfid_isometry_conj_mx {m n : nat}
    (V : 'M[C]_(m, n)) (rho sigma : 'M[C]_n) :
  V^*t \is unitarymx ->
  rho \is psdmx -> sigma \is psdmx ->
  @complex.Re R (\tr rho) <= 1 -> @complex.Re R (\tr sigma) <= 1 ->
  gfidelity (V *m rho *m V^*t) (V *m sigma *m V^*t) = gfidelity rho sigma.
Proof. by move=> HVi Hrho Hsigma _ _; exact: gfid_isometry_conj_psd_mx HVi Hrho Hsigma. Qed.

(* Sub-norm matrix Uhlmann theorem (gfidelity form). Generalizes              *)
(* `fid_iii_uhl_mx` from den1mx (rank-1, trace-1) to PSD                    *)
(* sub-normalized states using the generalized fidelity `gfidelity`.           *)
(*                                                                             *)
(* Setup: psi_rho is a sub-normalized PSD matrix with rank ≤ 1 (i.e. either    *)
(* zero or rank-1) on `'M_(n*k)`, purifying rho := ptrace2 psi_rho on `'M_n`.  *)
(* sigma is any PSD sub-normalized state on `'M_n` whose rank does not exceed  *)
(* the environment dimension k.  The conclusion produces a sub-normalized      *)
(* PSD purification psi_sigma of sigma on `'M_(n*k)` with                      *)
(*   gfidelity psi_rho psi_sigma = gfidelity rho sigma.                         *)
(*                                                                             *)
(* Strategy (scaling reduction).  Set α := Re(Tr ρ) = Re(Tr ψ_ρ).              *)
(*   - Edge case σ = 0: choose ψ_σ := 0; both gfidelities collapse to the       *)
(*     trace-correction sqrt(1 - α) coming from `alt_gfid_gen` (the main term  *)
(*     vanishes since `sqrtmx 0 = 0`).                                         *)
(*   - Edge case σ ≠ 0 but α = 0 (so ρ = 0 and ψ_ρ = 0): use                  *)
(*     `purification_exists_in_dim` to obtain any rank-1 purification of σ;    *)
(*     gfidelity 0 _ = sqrt(1 - Tr σ) on both sides.                            *)
(*   - Generic case σ ≠ 0 and α > 0: rescale ψ_ρ' := α^(-1) *: ψ_ρ to a        *)
(*     den1mx rank-1 purification of α^(-1) *: ρ; apply `fid_iii_uhl_mx`     *)
(*     to obtain θ : denmx, rank-1, ptrace2 θ = σ, and the FIDELITY identity   *)
(*     Re(trnorm(√ψ_ρ' √θ)) = Re(trnorm(√(α^(-1)·ρ) √σ)).  Multiplying by      *)
(*     sqrt(α) and using `sqrtmxZ_nn`/`trnormZ` upgrades both sides to the     *)
(*     unscaled Re(trnorm(√ψ_ρ √θ)) = Re(trnorm(√ρ √σ)).  The trace            *)
(*     correction `sqrt(1-Tr ψ_ρ) · sqrt(1-Tr θ)` matches `sqrt(1-Tr ρ) ·      *)
(*     sqrt(1-Tr σ)` via `tr_ptrace2`.                                          *)
(*                                                                             *)
(* tex: Tomamichel, 'A Framework for Non-Asymptotic Quantum Information         *)
(*   Theory' (PhD thesis, arXiv:1203.2142) — sub-norm Uhlmann (th:pd-uhl,       *)
(*   Thm 3.5; lemma:uhlmann-pure variant) + df:gfid (Def 3.2) trace-correction  *)
(*   term, and the Uhlmann argument used in th:data-proc (Theorem 5.7).         *)
(* This is a reusable helper for the                                            *)
(* smooth-entropy Uhlmann bridge; `gfid_isometry_conj_mx` is the companion     *)
(* isometry invariance lemma immediately above.                                *)
(* subnorm_matrix_uhlmann *)
(* infra: no tex label — fundamental & reusable (mathcomp-style) *)
(* consumer: subnorm_matrix_uhlmann is used downstream by the BB84 secrecy proof. *)
(* path: utils:subnorm_matrix_uhlmann -> utils:gfid_cast_mx -> *)
(*   entropy:entropy_data_proc -> *)
(*   bb84:bb84_secret *)
Lemma subnorm_matrix_uhlmann {a b : nat}
    (psi_rho : 'M[C]_(a * b)) (rho sigma : 'M[C]_a) :
  psi_rho \is psdmx ->
  (\rank psi_rho <= 1)%N ->
  @complex.Re R (\tr psi_rho) <= 1 ->
  ptrace2 psi_rho = rho ->
  sigma \is psdmx ->
  @complex.Re R (\tr sigma) <= 1 ->
  (\rank sigma <= b)%N ->
  exists psi_sigma : 'M[C]_(a * b),
    [/\ psi_sigma \is psdmx,
        (\rank psi_sigma <= 1)%N,
        @complex.Re R (\tr psi_sigma) <= 1,
        ptrace2 psi_sigma = sigma &
        gfidelity psi_rho psi_sigma = gfidelity rho sigma].
Proof.
  move=> Hpsi_psd Hpsi_rank Hpsi_tr Hpsi_ptr Hsigma_psd Hsigma_tr Hsigma_rank.
  (* Derived facts about rho. *)
  have Hrho_psd : rho \is psdmx.
    by rewrite -Hpsi_ptr; apply: ptrace2_psd.
  have Htr_psi_rho : \tr psi_rho = \tr rho.
    by rewrite -Hpsi_ptr -tr_ptrace2.
  have Hrho_tr : @complex.Re R (\tr rho) <= 1.
    by rewrite -Htr_psi_rho.
  (* Trace is real and non-negative. *)
  have Htr_psi_real : \tr psi_rho \is Num.real
    by apply: ger0_real; exact: psdmx_trace.
  have Htr_psi_ge0 : 0 <= @complex.Re R (\tr psi_rho).
    have := psdmx_trace Hpsi_psd. by rewrite lecE/= => /andP[_].
  (* Case split on whether sigma is zero. *)
  case: (sigma =P 0) => [Hsig0|/eqP Hsig_nz].
  { (* CASE A: sigma = 0.  Choose psi_sigma := 0.                              *)
    exists 0; split.
    - exact: psdmx0.
    - by rewrite mxrank0.
    - by rewrite mxtrace0 raddf0/= ler01.
    - by rewrite linear0 Hsig0.
    - (* Both sides reduce to the correction term sqrt(1 - Tr) * 1. *)
      rewrite Hsig0.
      rewrite (alt_gfid_gen Hpsi_psd (@psdmx0 _ (a*b)%N)).
      rewrite (alt_gfid_gen Hrho_psd (@psdmx0 _ a)).
      rewrite !sqrtmx0 !mulmx0 !trnorm0.
      have HRe0 : @complex.Re R (0 : C) = 0 by rewrite raddf0.
      rewrite HRe0 !add0r !mxtrace0.
      by rewrite Htr_psi_rho. }
  (* CASE B/C: sigma != 0.  Need a real number for trace inverse. *)
  set alpha : R := @complex.Re R (\tr psi_rho).
  have Halpha_eq : \tr psi_rho = alpha%:C
    by rewrite /alpha (RRe_real Htr_psi_real).
  have Halpha_eq_rho : \tr rho = alpha%:C by rewrite -Htr_psi_rho.
  case: (alpha =P 0) => [Halpha0|/eqP Halpha_nz].
  { (* CASE B: alpha = 0, i.e. Tr psi_rho = 0, so psi_rho = 0 (and rho = 0).   *)
    have Hpsi_tr0 : \tr psi_rho == 0 by rewrite Halpha_eq Halpha0 raddf0.
    have Hpsi_zero : psi_rho = 0
      by apply/eqP; rewrite -(psdmx_trace_eq0 Hpsi_psd).
    have Hrho_zero : rho = 0 by rewrite -Hpsi_ptr Hpsi_zero linear0.
    (* Build a rank-1 purification of sigma using `purification_exists_in_dim`. *)
    have Hsigma_den : sigma \is denmx.
      apply/denmxP; split; first exact: Hsigma_psd.
      have Htr_sig_real : \tr sigma \is Num.real.
        apply: ger0_real. exact: (psdmx_trace Hsigma_psd).
      rewrite -(RRe_real Htr_sig_real) -[1]/(1%:C : C) lecR.
      exact: Hsigma_tr.
    have [theta [Htheta_den [Htheta_rank Htheta_ptr]]] :=
      purification_exists_in_dim Hsigma_den Hsig_nz Hsigma_rank.
    exists theta.
    have Htheta_psd : theta \is psdmx := denmx_psd Htheta_den.
    have Htheta_tr_le : @complex.Re R (\tr theta) <= 1.
      have /denmxP[_ Htr_theta] := Htheta_den.
      have Htr_th_real : \tr theta \is Num.real
        by apply: ger0_real; apply: psdmx_trace; exact: denmx_psd Htheta_den.
      by move: Htr_theta; rewrite -(RRe_real Htr_th_real) -[1]/(1%:C : C) lecR.
    split.
    - exact: Htheta_psd.
    - by rewrite Htheta_rank.
    - exact: Htheta_tr_le.
    - exact: Htheta_ptr.
    - rewrite Hpsi_zero Hrho_zero.
      (* gfidelity 0 X for X psdmx sub-norm: trace correction only. *)
      rewrite (alt_gfid_gen (@psdmx0 _ (a*b)%N) Htheta_psd).
      rewrite (alt_gfid_gen (@psdmx0 _ a) Hsigma_psd).
      rewrite !sqrtmx0 !mul0mx !trnorm0.
      have HRe0 : @complex.Re R (0 : C) = 0 by rewrite raddf0.
      rewrite HRe0 !add0r !mxtrace0.
      have Htr_theta_sigma : \tr theta = \tr sigma.
        by rewrite -Htheta_ptr -tr_ptrace2.
      by rewrite Htr_theta_sigma. }
  (* CASE C: alpha > 0.  Scaling reduction. *)
  have Halpha_gt0 : 0 < alpha by rewrite lt_def Halpha_nz Htr_psi_ge0.
  have Halpha_C_ne0 : alpha%:C != 0 :> C.
    apply/negP=> /eqP H; move/eqP: Halpha_nz; apply.
    by apply/(@complexI R); rewrite H rmorph0.
  set alphaC : C := alpha%:C.
  set inv_alpha : R := (alpha^-1)%R.
  have Hinv_ge0 : 0 <= inv_alpha by rewrite /inv_alpha invr_ge0 ltW.
  have Hinv_alphaC : inv_alpha%:C = (alphaC^-1)%R
    by rewrite /inv_alpha /alphaC -fmorphV.
  have Halpha_unit : alphaC \is a GRing.unit
    by rewrite /alphaC unitfE.
  (* Rescaled purification psi_rho' := inv_alpha *: psi_rho. *)
  set psi_rho' : 'M[C]_(a * b) := inv_alpha%:C *: psi_rho.
  set rho' : 'M[C]_a := inv_alpha%:C *: rho.
  have Hpsi'_psd : psi_rho' \is psdmx.
    rewrite /psi_rho'.
    apply: psdmxZ=> //.
    by rewrite lecE/= eqxx/= Hinv_ge0.
  have Hpsi'_ptr : ptrace2 psi_rho' = rho'.
    by rewrite /psi_rho' /rho' linearZ/= Hpsi_ptr.
  have Hpsi'_tr : \tr psi_rho' = 1.
    rewrite /psi_rho' linearZ/= Halpha_eq Hinv_alphaC -/alphaC.
    by rewrite mulVf//.
  have Hpsi'_den1 : psi_rho' \is den1mx
    by apply/den1mxP; split=> //; apply/eqP.
  have Hinv_C_ne0 : inv_alpha%:C != 0 :> C
    by rewrite Hinv_alphaC invr_eq0.
  have Hpsi'_rank_eq : (\rank psi_rho' = \rank psi_rho)%N.
    rewrite /psi_rho'.
    by have := eqmx_scale psi_rho Hinv_C_ne0; case=> -> _.
  have Hpsi_rank_pos : (0 < \rank psi_rho)%N.
    rewrite lt0n mxrank_eq0; apply/negP=> /eqP Hpsi0.
    move/eqP: Halpha_nz; apply; rewrite /alpha Hpsi0.
    by rewrite mxtrace0 raddf0.
  have Hpsi'_rank : \rank psi_rho' = 1%N.
    rewrite Hpsi'_rank_eq.
    by apply/eqP; rewrite eqn_leq Hpsi_rank Hpsi_rank_pos.
  (* sigma_A := sigma; need denmx + nz + rank ≤ b — already have. *)
  have Hsigma_den : sigma \is denmx.
    apply/denmxP; split; first exact: Hsigma_psd.
    have Htr_sig_real : \tr sigma \is Num.real.
      apply: ger0_real. exact: (psdmx_trace Hsigma_psd).
    rewrite -(RRe_real Htr_sig_real) -[1]/(1%:C : C) lecR.
    exact: Hsigma_tr.
  (* Apply fid_iii_uhl_mx. *)
  have [theta [Htheta_den [Htheta_rank [Htheta_ptr Htheta_fid]]]] :=
    fid_iii_uhl_mx (den1mx_den Hpsi'_den1) Hpsi'_rank Hpsi'_ptr
      Hsigma_den Hsig_nz Hsigma_rank.
  exists theta.
  have Htheta_psd : theta \is psdmx := denmx_psd Htheta_den.
  have Htr_theta_sigma : \tr theta = \tr sigma
    by rewrite -Htheta_ptr -tr_ptrace2.
  have Htheta_tr_le : @complex.Re R (\tr theta) <= 1
    by rewrite Htr_theta_sigma.
  split.
  - exact: Htheta_psd.
  - by rewrite Htheta_rank.
  - exact: Htheta_tr_le.
  - exact: Htheta_ptr.
  (* Final fidelity equation. *)
  rewrite (alt_gfid_gen Hpsi_psd Htheta_psd) (alt_gfid_gen Hrho_psd Hsigma_psd).
  (* The trace-correction terms match: Tr psi_rho = Tr rho, Tr theta = Tr sigma. *)
  rewrite Htr_psi_rho Htr_theta_sigma.
  congr (_ + _).
  (* Main term: psi_rho = alpha *: psi_rho', rho = alpha *: rho'. *)
  have Hpsi_eq : psi_rho = alphaC *: psi_rho'.
    rewrite /psi_rho' scalerA Hinv_alphaC -/alphaC.
    by rewrite divff// scale1r.
  have Hrho_eq : rho = alphaC *: rho'.
    rewrite /rho' scalerA Hinv_alphaC -/alphaC.
    by rewrite divff// scale1r.
  (* sqrtmx (alpha *: X) = sqrt(alpha) *: sqrtmx X. *)
  have Hrho'_psd : rho' \is psdmx.
    rewrite /rho'.
    by apply: psdmxZ=> //; rewrite lecE/= eqxx/= Hinv_ge0.
  have Hsqrt_psi : sqrtmx psi_rho = (Num.sqrt alpha)%:C *: sqrtmx psi_rho'.
    by rewrite Hpsi_eq /alphaC sqrtmxZ_nn// ltW.
  have Hsqrt_rho : sqrtmx rho = (Num.sqrt alpha)%:C *: sqrtmx rho'.
    by rewrite Hrho_eq /alphaC sqrtmxZ_nn// ltW.
  rewrite Hsqrt_psi Hsqrt_rho.
  rewrite -!scalemxAl !trnormZ.
  set sqα_C : C := (Num.sqrt alpha)%:C.
  have Hsqα_ge0_C : (0 : C) <= sqα_C
    by rewrite /sqα_C lecE /= eqxx /= sqrtr_ge0.
  rewrite !(ger0_norm Hsqα_ge0_C).
  (* Re(sqα_C * T) = Num.sqrt alpha * Re T (since sqα_C is real). *)
  have HReM : forall T : C,
      @complex.Re R (sqα_C * T) = Num.sqrt alpha * @complex.Re R T.
    move=> [c d] /=.
    by rewrite mul0r subr0.
  rewrite !HReM.
  congr (_ * _).
  exact: Htheta_fid.
Qed.

(* Column-isometry generalization of `ptrace2_conj_tens_right`.                  *)
(* That earlier lemma requires `U \is unitarymx` (square unitary on the env       *)
(* dimension `b`).  Here we generalize the env factor to a rectangular            *)
(* column-isometry `W : 'M[C]_(b', b)` satisfying `W^*t *m W = 1%:M`, exactly the *)
(* shape produced by Stinespring dilation `W : 'M[C]_(nB*z, nB)`.                 *)
(*                                                                                *)
(* Statement: for any `M : 'M[C]_(a * b)`, the dilated state                       *)
(*   M_dil := ((1_a) *t W) *m M *m ((1_a) *t W)^*t : 'M[C]_(a * b')                *)
(* has the same partial-trace marginal as M:                                      *)
(*   ptrace2 M_dil = ptrace2 M.                                                    *)
(*                                                                                *)
(* This is the structural bridge for the embedding strategy used by smooth-       *)
(* entropy Uhlmann arguments: the standard sub-norm matrix Uhlmann lemma          *)
(* produces a witness in the small space `'M_(a*b)`; embedding it as              *)
(* `(1_a) *t W *m psi *m (1_a) *t W^*t` lifts it to the dilated env space         *)
(* `'M_(a*b')` with image-support `Pi *m _ = _` (Pi := V V^*t with              *)
(* V := (1_a) *t W) and ptrace2 marginal preserved by this lemma.                 *)
(*                                                                                *)
(* The proof is direct entry-by-entry expansion via `tensmxE_mid` / `mxtens_index` *)
(* / cancellation of `W^*t W = 1` (column-iso).  Same proof structure as the      *)
(* unitary version, with rectangular `W : 'M[C]_(b', b)`.                        *)
(*                                                                                *)
(* tex: Tomamichel, 'A Framework for Non-Asymptotic Quantum Information          *)
(*   Theory' (PhD thesis, arXiv:1203.2142) — Stinespring purification embedding *)
(*   (lm:stinespring, Lemma 2.4) plus the image-support Uhlmann argument in      *)
(*   th:data-proc (Theorem 5.7, Generalized Data Processing).                    *)
(* ptrace2_conj_tens_right_iso *)
(* infra: no tex label - fundamental & reusable (mathcomp-style) *)
(* consumer: ptrace2_conj_tens_right_iso is used downstream by the BB84 secrecy proof. *)
(* path: utils:ptrace2_conj_tens_right_iso -> entropy:entropy_data_proc -> *)
(*   bb84:bb84_secret *)
Lemma ptrace2_conj_tens_right_iso {a b b' : nat}
    (W : 'M[C]_(b', b)) (M : 'M[C]_(a * b)) :
  W^*t *m W = 1%:M ->
  ptrace2 ((((1%:M : 'M[C]_a) *t W) *m M) *m
           (((1%:M : 'M[C]_a) *t W)^*t)) = ptrace2 M.
Proof.
  move=> HW.
  have ptrace2E' : forall s t (N : 'M[C]_(s * t)) r1 r2,
      (ptrace2 N) r1 r2 =
      \sum_l N (mxtens_index (r1, l)) (mxtens_index (r2, l)).
  { move=> s t N r1 r2.
    rewrite ptrace2E1 ptrace1E.
    by apply: eq_bigr => l _; rewrite mxE !mxtens_indexK. }
  apply/matrixP => i j.
  rewrite !ptrace2E'.
  pose RR := (((1%:M : 'M[C]_a) *t W)^*t).
  have HleftMul :
      forall (N : 'M[C]_(a * b, a * b'))
             (k : 'I_b') (t : 'I_(a * b')),
        ((((1%:M : 'M[C]_a) *t W) *m N)
           (mxtens_index (i, k)) t) =
        \sum_(k1 : 'I_b) W k k1 * N (mxtens_index (i, k1)) t.
  { move=> N k t.
    rewrite (tensmxE_mid (((1%:M : 'M[C]_a) *t W)) N
      (mxtens_index (i, k)) t).
    transitivity
      (\sum_(i1 : 'I_a) \sum_(k1 : 'I_b)
        ((i == i1)%:R * W k k1) *
        N (mxtens_index (i1, k1)) t).
    { apply: eq_bigr => i1 _.
      apply: eq_bigr => k1 _.
      by rewrite tensmxE !mxE -mulrA. }
    transitivity
      (\sum_(i1 : 'I_a)
        (i == i1)%:R *
        \sum_(k1 : 'I_b) W k k1 * N (mxtens_index (i1, k1)) t).
    { apply: eq_bigr => i1 _.
      rewrite mulr_sumr.
      by apply: eq_bigr => k1 _; rewrite -mulrA. }
    rewrite (bigD1 i) //= eqxx mul1r.
    rewrite [X in _ + X]big1 ?addr0 //.
    by move=> i1 Hi1; rewrite eq_sym (negPf Hi1) mul0r. }
  have HrightMul :
      forall (k1 : 'I_b) (k : 'I_b'),
        (M *m RR) (mxtens_index (i, k1)) (mxtens_index (j, k)) =
        \sum_(k2 : 'I_b)
          M (mxtens_index (i, k1)) (mxtens_index (j, k2)) *
          (W^*t) k2 k.
  { move=> k1 k.
    rewrite /RR.
    rewrite (tensmxE_mid M (((1%:M : 'M[C]_a) *t W)^*t)
      (mxtens_index (i, k1)) (mxtens_index (j, k))).
    transitivity
      (\sum_(j1 : 'I_a) \sum_(k2 : 'I_b)
        ((j == j1)%:R *
          M (mxtens_index (i, k1)) (mxtens_index (j1, k2))) *
        (W^*t) k2 k).
    { apply: eq_bigr => j1 _.
      apply: eq_bigr => k2 _.
      rewrite /RR adjmx_tens adjmx1.
      rewrite tensmxE !mxE eq_sym.
      rewrite -mulrA.
      by rewrite mulrCA. }
    transitivity
      (\sum_(j1 : 'I_a)
        (j == j1)%:R *
        \sum_(k2 : 'I_b)
          M (mxtens_index (i, k1)) (mxtens_index (j1, k2)) *
          (W^*t) k2 k).
    { apply: eq_bigr => j1 _.
      rewrite mulr_sumr.
      by apply: eq_bigr => k2 _; rewrite -mulrA. }
    rewrite (bigD1 j) //= eqxx mul1r.
    rewrite [X in _ + X]big1 ?addr0 //.
    by move=> j1 Hj1; rewrite eq_sym (negPf Hj1) mul0r. }
  transitivity
    (\sum_(k : 'I_b') \sum_(k1 : 'I_b)
      W k k1 * (M *m RR) (mxtens_index (i, k1)) (mxtens_index (j, k))).
  { apply: eq_bigr => k _.
    by rewrite -mulmxA HleftMul. }
  rewrite exchange_big /=.
  transitivity
    (\sum_(k1 : 'I_b) \sum_(k2 : 'I_b)
      M (mxtens_index (i, k1)) (mxtens_index (j, k2)) *
      \sum_(k : 'I_b') (W^*t) k2 k * W k k1).
  { apply: eq_bigr => k1 _.
    transitivity
      (\sum_(k : 'I_b') \sum_(k2 : 'I_b)
        M (mxtens_index (i, k1)) (mxtens_index (j, k2)) *
        ((W^*t) k2 k * W k k1)).
    - apply: eq_bigr => k _.
      rewrite HrightMul mulr_sumr.
      apply: eq_bigr => k2 _.
      rewrite mulrA [W k k1 * _]mulrC -mulrA.
      by rewrite [(W k k1) * _]mulrC.
    - rewrite exchange_big /=.
      apply: eq_bigr => k2 _.
      by rewrite -mulr_sumr. }
  transitivity
    (\sum_(k1 : 'I_b) \sum_(k2 : 'I_b)
      M (mxtens_index (i, k1)) (mxtens_index (j, k2)) *
      ((W^*t *m W) k2 k1)).
  { apply: eq_bigr => k1 _.
    by apply: eq_bigr => k2 _; rewrite mxE. }
  rewrite HW.
  transitivity
    (\sum_(k1 : 'I_b)
      M (mxtens_index (i, k1)) (mxtens_index (j, k1))).
  { apply: eq_bigr => k1 _.
    rewrite (bigD1 k1) //= mxE !eqxx /= mulr1.
    rewrite big1 ?addr0 //.
    move=> k2 Hk2; rewrite mxE.
    have -> : (k2 == k1) = false by rewrite (negPf Hk2).
    by rewrite /= mulr0. }
  by [].
Qed.

(* Uhlmann fixed-target witness with a larger environment.                    *)
(* fid_iii_uhl_iso_mx *)
(* infra: no tex label — fundamental matrix Uhlmann embedding bridge. *)
(* math: if c can contain b, varying the source purification by an   *)
(*       isometry b -> c realizes the fidelity to a fixed c-env       *)
(*       purification of sigma_A.                                     *)
(* path: utils:fid_iii_uhl_iso_mx -> entropy:minmax_dual -> *)
(*   entropy:smooth_iso_hmax -> entropy:entropy_data_proc -> *)
(*   bb84:bb84_secret *)
Lemma fid_iii_uhl_iso_mx {a b c : nat}
    {rho_AB : 'M[C]_(a * b)} {theta_AC : 'M[C]_(a * c)}
    {rho_A sigma_A : 'M[C]_a} :
  (b <= c)%N ->
  rho_AB \is denmx ->
  \rank rho_AB = 1%N ->
  ptrace2 rho_AB = rho_A ->
  theta_AC \is denmx ->
  \rank theta_AC = 1%N ->
  ptrace2 theta_AC = sigma_A ->
  exists V : 'M[C]_(c, b),
    V^*t *m V = 1%:M /\
    @complex.Re R
      (trnorm (sqrtmx ((((1%:M : 'M[C]_a) *t V) *m rho_AB) *m
        (((1%:M : 'M[C]_a) *t V)^*t)) *m sqrtmx theta_AC)) =
    @complex.Re R (trnorm (sqrtmx rho_A *m sqrtmx sigma_A)).
Proof.
  move=> Hbc Hrho_den Hrho_rank Hptr_rho Htheta_den Htheta_rank Hptr_theta.
  pose R0 : 'M[C]_(b, b + (c - b)) :=
    row_mx (1%:M : 'M[C]_b) (0 : 'M[C]_(b, c - b)).
  pose RR : 'M[C]_(b, c) := castmx (erefl b, subnKC Hbc) R0.
  have HRR_unit : RR \is unitarymx.
  { rewrite /RR castmx_funE.
    exact: (row_mx0_unitarymx _ (unitarymx1 _ _)). }
  pose J : 'M[C]_(c, b) := RR^*t.
  have HJ : J^*t *m J = 1%:M.
  { rewrite /J adjmxK.
    exact: unitarymxK HRR_unit. }
  pose WJ : 'M[C]_(a * c, a * b) := (1%:M : 'M[C]_a) *t J.
  have HWJ : WJ^*t *m WJ = 1%:M.
  { by rewrite /WJ tensmx_adj adjmx1 tensmx_mul mul1mx HJ tensmx11. }
  pose rho_AC : 'M[C]_(a * c) := WJ *m rho_AB *m WJ^*t.
  have Hrho_psd : rho_AB \is psdmx := denmx_psd Hrho_den.
  have Htheta_psd : theta_AC \is psdmx := denmx_psd Htheta_den.
  have Hrho_AC_psd : rho_AC \is psdmx.
  { rewrite /rho_AC.
    exact: psdmx_bimap_closed_gen Hrho_psd. }
  have Hrho_AC_tr : \tr rho_AC = \tr rho_AB.
  { by rewrite /rho_AC mxtrace_mulC mulmxA HWJ mul1mx. }
  have Hrho_AC_den : rho_AC \is denmx.
  { apply/denmxP; split=> //.
    by rewrite Hrho_AC_tr; have /denmxP[_] := Hrho_den. }
  have Hrho_AC_rank_le : (\rank rho_AC <= 1)%N.
  { rewrite /rho_AC.
    have Hstep1 :
        (\rank (WJ *m rho_AB *m WJ^*t) <= \rank (WJ *m rho_AB))%N
      by exact: mxrankM_maxl.
    have Hstep2 : (\rank (WJ *m rho_AB) <= \rank rho_AB)%N
      by exact: mxrankM_maxr.
    have Hstep3 : (\rank rho_AB <= 1)%N by rewrite Hrho_rank.
    exact: leq_trans Hstep1 (leq_trans Hstep2 Hstep3). }
  have Hrho_AB_nz : rho_AB != 0.
  { by rewrite -mxrank_eq0 Hrho_rank. }
  have Hrho_AC_nz : rho_AC != 0.
  { apply/eqP=> Hrho_AC0.
    have Hrho_AB_tr0 : \tr rho_AB = 0
      by rewrite -Hrho_AC_tr Hrho_AC0 mxtrace0.
    have Hrho_AB0 : rho_AB = 0.
    { by apply/eqP; rewrite -(psdmx_trace_eq0 Hrho_psd) Hrho_AB_tr0. }
    by move/eqP: Hrho_AB_nz; rewrite Hrho_AB0. }
  have Hrho_AC_rank : \rank rho_AC = 1%N.
  { by apply/eqP; rewrite eqn_leq Hrho_AC_rank_le lt0n mxrank_eq0. }
  have Hptr_rho_AC : ptrace2 rho_AC = rho_A.
  { by rewrite /rho_AC /WJ
      (@ptrace2_conj_tens_right_iso a b c J rho_AB HJ). }
  have [U [HU Hfid]] :=
    uhlmann_environment_unitary_witness Hrho_AC_den Hrho_AC_rank
      Hptr_rho_AC Htheta_den Htheta_rank Hptr_theta.
  pose Uadj : 'M[C]_c := U^*t.
  pose V : 'M[C]_(c, b) := Uadj *m J.
  have HV : V^*t *m V = 1%:M.
  { transitivity (J^*t *m (U *m U^*t) *m J).
    - by rewrite /V /Uadj adjmxM adjmxK !mulmxA.
    - by rewrite (unitarymxK HU) mulmx1 HJ. }
  exists V; split.
  - exact: HV.
  pose WU : 'M[C]_(a * c) := (1%:M : 'M[C]_a) *t U.
  have HWU : WU \is unitarymx.
  { by apply: unitarymx_tens; [exact: unitarymx1 | exact: HU]. }
  have HWUadj : WU^*t \is unitarymx by rewrite adjmx_unitary.
  have Hsource :
      (((1%:M : 'M[C]_a) *t V) *m rho_AB) *m
        (((1%:M : 'M[C]_a) *t V)^*t) =
      WU^*t *m rho_AC *m WU.
  { have HtV : ((1%:M : 'M[C]_a) *t V) = WU^*t *m WJ.
    { rewrite /V /Uadj.
      symmetry.
      have Hmul_tens :
          (((1%:M : 'M[C]_a) *t U^*t) *m
            ((1%:M : 'M[C]_a) *t J)) =
          ((1%:M : 'M[C]_a) *t (U^*t *m J)).
      { pose Ustar : 'M[C]_c := U^*t.
        change ((((1%:M : 'M[C]_a) *t Ustar) *m
            ((1%:M : 'M[C]_a) *t J)) =
          ((1%:M : 'M[C]_a) *t (Ustar *m J))).
        by rewrite mxtens.tensmx_mul mul1mx. }
      rewrite /WU /WJ.
      rewrite [((1%:M : 'M[C]_a) *t U)^*t]tensmx_adj adjmx1.
      exact: Hmul_tens. }
    by rewrite HtV /rho_AC adjmxM adjmxK !mulmxA. }
  have Htarget :
      WU^*t *m
        (((1%:M : 'M[C]_a) *t U) *m theta_AC *m
          (((1%:M : 'M[C]_a) *t U)^*t)) *m WU =
      theta_AC.
  { by rewrite /WU !mulmxA (unitarymxKV HWU) mul1mx
      -mulmxA (unitarymxKV HWU) mulmx1. }
  have Htheta_conj_psd :
      (((1%:M : 'M[C]_a) *t U) *m theta_AC *m
        (((1%:M : 'M[C]_a) *t U)^*t)) \is psdmx.
  { exact: psdmx_bimap_closed_gen Htheta_psd. }
  have Hconj := fid_unitary_conj_mx HWUadj Hrho_AC_psd Htheta_conj_psd.
  rewrite !adjmxK in Hconj.
  rewrite Htarget in Hconj.
  rewrite Hsource.
  rewrite Hconj.
  exact: Hfid.
Qed.

(* Image-supported sub-norm matrix Uhlmann (gfidelity form). Specialization of   *)
(* `subnorm_matrix_uhlmann` where `psi_rho` is already supported on               *)
(* the image of the projector `Pi := (1_a) ⊗ (W *m W^*t)` (with `W` a column-     *)
(* isometry on the env factor: `W^*t *m W = 1`).  The output `psi_sigma`          *)
(* automatically also lives in the image of `Pi` (it is built as `V K' V^*t` for *)
(* `V := (1_a) ⊗ W`), preserving the marginal `ptrace2 psi_sigma = sigma`.         *)
(*                                                                                *)
(* Strategy.  Image-support `V V^*t *m psi_rho = psi_rho` plus PSD-derived        *)
(* hermiticity yields `psi_rho = V K V^*t` with `K := V^*t *m psi_rho *m V`        *)
(* (column-isometry compression).  `K` inherits PSD (`formV_psdmx`), rank ≤ 1     *)
(* (`mxrankM_max`), trace ≤ 1 (cyclic + image-support), and purifies              *)
(* `rho := ptrace2 psi_rho` on the small env (`ptrace2_conj_tens_right_iso`).     *)
(* Apply `subnorm_matrix_uhlmann` to `K` and `sigma` on the small space `'M_(a*b)`*)
(* obtaining a sub-norm purification `psi_sigma_b` of `sigma` with                 *)
(* `gfidelity K psi_sigma_b = gfidelity rho sigma`.  Embed                         *)
(* `psi_sigma := V *m psi_sigma_b *m V^*t` on `'M_(a*b')`.  PSD via `form_psdmx`,  *)
(* trace ≤ 1 by cyclic + `V^*t V = 1`, ptrace2 marginal preserved by              *)
(* `ptrace2_conj_tens_right_iso`, image-support `V V^*t *m psi_sigma = psi_sigma` *)
(* directly from `V V^*t *m V = V`, and gfidelity equality via                    *)
(* `gfid_isometry_conj_mx` (preliminary 1, applied with V column-iso) chained   *)
(* with `gfidelity K psi_sigma_b = gfidelity rho sigma`.                          *)
(*                                                                                *)
(* tex: Tomamichel, 'A Framework for Non-Asymptotic Quantum Information           *)
(*   Theory' (PhD thesis, arXiv:1203.2142) — sub-normalized Uhlmann (th:pd-uhl,  *)
(*   Theorem 3.5) plus the image-support Uhlmann argument in th:data-proc         *)
(*   (Theorem 5.7). This combines                                                 *)
(* `gfid_isometry_conj_mx`, `subnorm_matrix_uhlmann`, and the column-isometry     *)
(* `ptrace2_conj_tens_right_iso` above.                                           *)
(* subnorm_matrix_uhlmann_in_image *)
(* infra: no tex label — fundamental & reusable (mathcomp-style) *)
(* consumer: subnorm_matrix_uhlmann_in_image is used downstream by the BB84 secrecy proof. *)
(* path: utils:subnorm_matrix_uhlmann_in_image -> utils:gfid_cast_mx -> *)
(*   entropy:entropy_data_proc -> *)
(*   bb84:bb84_secret *)
Lemma subnorm_matrix_uhlmann_in_image {a b b' : nat}
    (W : 'M[C]_(b', b))
    (psi_rho : 'M[C]_(a * b')) (rho sigma : 'M[C]_a) :
  W^*t *m W = 1%:M ->
  ((1%:M : 'M[C]_a) *t W) *m ((1%:M : 'M[C]_a) *t W)^*t *m psi_rho = psi_rho ->
  psi_rho \is psdmx ->
  (\rank psi_rho <= 1)%N ->
  @complex.Re R (\tr psi_rho) <= 1 ->
  ptrace2 psi_rho = rho ->
  sigma \is psdmx ->
  @complex.Re R (\tr sigma) <= 1 ->
  (\rank sigma <= b)%N ->
  exists psi_sigma : 'M[C]_(a * b'),
    [/\ psi_sigma \is psdmx,
        @complex.Re R (\tr psi_sigma) <= 1,
        ptrace2 psi_sigma = sigma,
        ((1%:M : 'M[C]_a) *t W) *m ((1%:M : 'M[C]_a) *t W)^*t *m psi_sigma = psi_sigma &
        gfidelity psi_rho psi_sigma = gfidelity rho sigma].
Proof.
  move=> HW Himg Hpsi_psd Hpsi_rank Hpsi_tr Hpsi_ptr Hsigma_psd Hsigma_tr Hsigma_rank.
  set V : 'M[C]_(a * b', a * b) := (1%:M : 'M[C]_a) *t W.
  (* V is a column-isometry: V^*t *m V = 1. *)
  have HVtV : V^*t *m V = 1%:M.
  { rewrite /V adjmx_tens adjmx1 tensmx_mul mul1mx HW tensmx11. by []. }
  (* Image-support of psi_rho written via V V^*t. *)
  have Himg_V : V *m V^*t *m psi_rho = psi_rho by exact: Himg.
  (* Right-side image-support via hermiticity (psi_rho is psd hence hermitian). *)
  have Hpsi_herm : psi_rho^*t = psi_rho.
  { have Hh : psi_rho \is hermmx := psdmx_herm Hpsi_psd.
    by symmetry; apply/hermmxP. }
  have HVVt_herm : (V *m V^*t)^*t = V *m V^*t
    by rewrite adjmxM adjmxK.
  have Himg_R : psi_rho *m (V *m V^*t) = psi_rho.
  { have Hadj : (V *m V^*t *m psi_rho)^*t = psi_rho^*t by rewrite Himg_V.
    move: Hadj; rewrite adjmxM HVVt_herm Hpsi_herm => Hadj.
    exact: Hadj. }
  (* K := V^*t *m psi_rho *m V is the "compression" of psi_rho to small space. *)
  set K : 'M[C]_(a * b) := V^*t *m psi_rho *m V.
  (* Sandwich identity: psi_rho = V *m K *m V^*t (uses both image-support sides). *)
  have Hpsi_eq : psi_rho = V *m K *m V^*t.
  { rewrite /K.
    have step : V *m (V^*t *m psi_rho *m V) *m V^*t =
                (V *m V^*t) *m psi_rho *m (V *m V^*t)
      by rewrite !mulmxA.
    rewrite step Himg_V Himg_R. by []. }
  (* K is PSD via formV_psdmx. *)
  have HK_psd : K \is psdmx := formV_psdmx V Hpsi_psd.
  (* rank K <= rank psi_rho <= 1 via mxrankM_maxl/maxr chain. *)
  have HK_rank : (\rank K <= 1)%N.
  { rewrite /K.
    apply: leq_trans Hpsi_rank.
    have step1 : (\rank (V^*t *m psi_rho *m V) <= \rank (V^*t *m psi_rho))%N
      by exact: mxrankM_maxl.
    have step2 : (\rank (V^*t *m psi_rho) <= \rank psi_rho)%N
      by exact: mxrankM_maxr.
    exact: leq_trans step1 step2. }
  (* Trace identities: tr K = tr (V V^*t psi_rho) = tr psi_rho (image-support). *)
  have HK_tr_eq : \tr K = \tr psi_rho.
  { rewrite /K.
    rewrite mxtrace_mulC mulmxA.
    by rewrite Himg_V. }
  have HK_tr : @complex.Re R (\tr K) <= 1 by rewrite HK_tr_eq.
  (* ptrace2 K = rho via Hpsi_eq + ptrace2_conj_tens_right_iso. *)
  have Hpt_iso : ptrace2 (V *m K *m V^*t) = ptrace2 K.
  { rewrite /V. exact: (@ptrace2_conj_tens_right_iso a b b' W K HW). }
  have HK_ptr : ptrace2 K = rho.
  { rewrite -Hpsi_ptr Hpsi_eq.
    by rewrite Hpt_iso. }
  (* Apply preliminary 2 to (K, rho, sigma) on small space 'M_(a*b). *)
  have [psi_sigma_b [Hpb_psd Hpb_rank Hpb_tr Hpb_ptr Hpb_fid]] :=
    subnorm_matrix_uhlmann HK_psd HK_rank HK_tr HK_ptr Hsigma_psd Hsigma_tr Hsigma_rank.
  (* Build psi_sigma := V *m psi_sigma_b *m V^*t. *)
  set psi_sigma : 'M[C]_(a * b') := V *m psi_sigma_b *m V^*t.
  exists psi_sigma; split.
  (* (1) psi_sigma psd via form_psdmx. *)
  - rewrite /psi_sigma. apply: form_psdmx. exact: Hpb_psd.
  (* (2) Re(tr psi_sigma) <= 1 via cyclic + V^*t V = 1. *)
  - have Htr_eq : \tr psi_sigma = \tr psi_sigma_b.
    { rewrite /psi_sigma.
      rewrite mxtrace_mulC mulmxA.
      by rewrite HVtV mul1mx. }
    by rewrite Htr_eq.
  (* (3) ptrace2 psi_sigma = sigma via ptrace2_conj_tens_right_iso. *)
  - rewrite /psi_sigma /V (@ptrace2_conj_tens_right_iso a b b' W psi_sigma_b HW).
    exact: Hpb_ptr.
  (* (4) image-support: V V^*t *m psi_sigma = psi_sigma via V V^*t V = V. *)
  - rewrite /psi_sigma.
    have HVVtV : V *m V^*t *m V = V.
    { have step : V *m V^*t *m V = V *m (V^*t *m V) by rewrite mulmxA.
      by rewrite step HVtV mulmx1. }
    have step2 : V *m V^*t *m (V *m psi_sigma_b *m V^*t) =
                 (V *m V^*t *m V) *m psi_sigma_b *m V^*t
      by rewrite !mulmxA.
    rewrite step2 HVVtV. by [].
  (* (5) gfidelity psi_rho psi_sigma = gfidelity rho sigma.                       *)
  (*     LHS = gfidelity (V K V^*t) (V psi_sigma_b V^*t)                          *)
  (*         = gfidelity K psi_sigma_b           (gfid_isometry_conj_mx on V)   *)
  (*         = gfidelity rho sigma                (preliminary 2 conclusion).      *)
  - rewrite Hpsi_eq /psi_sigma -/V.
    have HVi : V^*t \is unitarymx.
    { apply/unitarymxP.
      rewrite -adjmxE adjmxK. exact: HVtV. }
    rewrite (gfid_isometry_conj_mx HVi HK_psd Hpb_psd HK_tr Hpb_tr).
    exact: Hpb_fid.
Qed.

(* Trace preservation under regroup. *)
(* trace_adj_regroup *)
(* infra: no tex label — fundamental & reusable (mathcomp-style) *)
(* consumer: trace_adj_regroup is used downstream by the BB84 secrecy proof. *)
(* path: utils:trace_adj_regroup -> utils:fid_ptr_mono_mx -> *)
(*   utils:gfid_ptr_mono_mx -> bb84:stat -> bb84:bb84_secret *)
Lemma trace_adj_regroup {m n k : nat} (A B : 'M[C]_((m * n), k)) :
  \tr ((regroup_factor A)^*t *m regroup_factor B) =
  \tr (A^*t *m B).
Proof.
  rewrite mxtrace_mulC [\tr (A^*t *m B)]mxtrace_mulC.
  pose S := \sum_(i : 'I_m) \sum_(b : 'I_n) \sum_(c : 'I_k)
    B (mxtens_index (i, b)) c * (A^*t) c (mxtens_index (i, b)).
  have Hleft : \tr (regroup_factor B *m (regroup_factor A)^*t) = S.
    apply: eq_bigr=> i _.
    rewrite mxE.
    rewrite (reindex_mxtens_index
      (P := predT)
      (fun l : 'I_(n * k) =>
        regroup_factor B i l * (regroup_factor A)^*t l i)).
    rewrite pair_bigV /=.
    apply: eq_bigr=> b _.
    apply: eq_bigr=> c _.
    by rewrite adjmxE !mxE mxtens_indexK.
  have Hright : \tr (B *m A^*t) = S.
    rewrite /mxtrace.
    rewrite (reindex_mxtens_index
      (P := predT)
      (fun l : 'I_(m * n) => (B *m A^*t) l l)).
    rewrite pair_bigV /=.
    apply: eq_bigr=> i _.
    apply: eq_bigr=> b _.
    rewrite mxE.
    apply: eq_bigr=> c _.
    by rewrite adjmxE !mxE.
  by rewrite Hleft Hright.
Qed.

(* Optimal fidelity factorization: given PSD rho, sigma, there exist factors      *)
(* A, B with A A^† = rho, B B^† = sigma, and Re|tr(A^† B)| = F(rho, sigma).        *)
(* Key building block for DPI proofs.                                              *)
(* optimal_fid_factors_mx *)
(* infra: no tex label — fundamental & reusable (mathcomp-style) *)
(* consumer: optimal_fid_factors_mx is used downstream by the BB84 secrecy proof. *)
(* path: utils:optimal_fid_factors_mx -> utils:fid_ptr_mono_mx -> *)
(*   utils:gfid_ptr_mono_mx -> bb84:stat -> bb84:bb84_secret *)
Lemma optimal_fid_factors_mx {n : nat} (rho sigma : 'M[C]_n) :
  rho \is psdmx -> sigma \is psdmx ->
  exists A B : 'M[C]_n,
    A *m A^*t = rho /\
    B *m B^*t = sigma /\
    @complex.Re R (Num.norm (\tr (A^*t *m B))) =
    @complex.Re R (trnorm (sqrtmx rho *m sqrtmx sigma)).
Proof.
  move=> Hrho_psd Hsigma_psd.
  have /hermmxP HSr_herm : sqrtmx rho \is hermmx
    by exact: sqrtmx_herm (psdmx_herm Hrho_psd).
  have /hermmxP HSs_herm : sqrtmx sigma \is hermmx
    by exact: sqrtmx_herm (psdmx_herm Hsigma_psd).
  pose Sr := sqrtmx rho.
  pose Ss := sqrtmx sigma.
  pose M := Sr *m Ss.
  have [P [U [HPpsd [HPsq [HU HM]]]]] := polar_UP M (leqnn n).
  have HUu : U \is unitarymx by move: HU; rewrite adjmx_unitary.
  exists (Sr *m U), Ss; split.
  - rewrite adjmxM -HSr_herm mulmxA.
    have HSUU : Sr *m U *m U^*t = Sr *m (U *m U^*t).
      by rewrite [RHS]mulmxA.
    rewrite HSUU.
    by rewrite (unitarymxK HUu) mulmx1 (sqrtmxK Hrho_psd).
  split; first by rewrite -HSs_herm (sqrtmxK Hsigma_psd).
  have HAB : (Sr *m U)^*t *m Ss = P.
    rewrite adjmxM -HSr_herm.
    have HUSs : U^*t *m sqrtmx rho *m Ss = U^*t *m (sqrtmx rho *m Ss).
      by rewrite [RHS]mulmxA.
    rewrite HUSs.
    have HSrSs : sqrtmx rho *m Ss = M by rewrite /M.
    rewrite HSrSs.
    rewrite HM.
    have HUUP : U^*t *m (U *m P) = (U^*t *m U) *m P.
      by rewrite [LHS]mulmxA.
    rewrite HUUP.
    by rewrite (unitarymxKV HUu) mul1mx.
  rewrite HAB.
  have -> : Sr *m Ss = M by rewrite /M.
  rewrite HM (trnormUl _ HUu).
  have -> : \tr| P | = \tr P by exact: psdmx_trnorm HPpsd.
  have HPtr_ge0 := psdmx_trace HPpsd.
  have -> : @complex.Re R (Num.norm (\tr P)) = @complex.Re R (\tr P)
    by rewrite ger0_norm.
  by [].
Qed.

(* Fidelity DPI for partial trace over 2nd factor (ptrace2 monotonicity).         *)
(* Uses fid_gramE_mx + ptrace2_gram_regroup + trace_adj_regroup +                  *)
(* optimal_fidelity_factors. PSD sub-normalized hypothesis suffices.              *)
(* fid_ptr_mono_mx *)
(* infra: no tex label — fundamental & reusable (mathcomp-style) *)
(* consumer: fid_ptr_mono_mx is used downstream by the BB84 secrecy proof. *)
(* path: utils:fid_ptr_mono_mx -> utils:gfid_ptr_mono_mx -> bb84:stat -> *)
(*   bb84:bb84_secret *)
Lemma fid_ptr_mono_mx {m n : nat} (rho sigma : 'M[C]_(m * n)) :
  (0 < n)%N ->
  rho \is psdmx ->
  sigma \is psdmx ->
  @complex.Re R (trnorm (sqrtmx rho *m sqrtmx sigma)) <=
  @complex.Re R (trnorm (sqrtmx (ptrace2 rho) *m sqrtmx (ptrace2 sigma))).
Proof.
  move=> Hn0 Hrho Hsigma.
  have [A [B [HA [HB Hopt]]]] := optimal_fid_factors_mx Hrho Hsigma.
  have Hn1 : (1 <= n)%N by exact: Hn0.
  have Hmn : (m <= m * n)%N
    by rewrite -{1}(muln1 m); exact: leq_mul (leqnn m) Hn1.
  have Hdim : (m <= n * (m * n))%N
    by rewrite -{1}(mul1n m); exact: leq_mul Hn1 Hmn.
  pose RA := regroup_factor A.
  pose RB := regroup_factor B.
  have Hptr_rho : ptrace2 rho = RA *m RA^*t
    by rewrite /RA -HA ptrace2_gram_regroup.
  have Hptr_sigma : ptrace2 sigma = RB *m RB^*t
    by rewrite /RB -HB ptrace2_gram_regroup.
  have Hnorm_real : (Num.norm (\tr (A^*t *m B))) \is Num.real
    by exact: normr_real.
  have Hgram := fid_gramE_mx RA RB Hdim.
  have Hgram' :
      @complex.Re R (trnorm (sqrtmx (ptrace2 rho) *m sqrtmx (ptrace2 sigma))) =
      @complex.Re R (trnorm (RA^*t *m RB))
    by rewrite Hptr_rho Hptr_sigma.
  have Hle := trnorm_ge_tr (RA^*t *m RB).
  rewrite (trace_adj_regroup A B) in Hle.
  have Htrnorm_real : (trnorm (RA^*t *m RB)) \is Num.real
    by exact: ger0_real (trnorm_ge0 _).
  move: Hle.
  rewrite -(RRe_real Hnorm_real) -(RRe_real Htrnorm_real) lecR.
  by rewrite Hopt -Hgram'.
Qed.

(* Fidelity is invariant under the matrix swap of the middle and right
   tensor factors. *)
(* path: utils:fid_mxswap23 -> utils:fid_ptr_mono_mxswap23 -> *)
(*   entropy:hmax_mx_projected_A_app_le -> entropy:entropy_data_proc -> *)
(*   bb84:bb84_secret *)
Lemma fid_mxswap23 {a b c : nat} (rho sigma : 'M[C]_((a * b) * c)) :
  rho \is psdmx -> sigma \is psdmx ->
  @complex.Re R (trnorm (sqrtmx (mxswap23 rho) *m sqrtmx (mxswap23 sigma))) =
  @complex.Re R (trnorm (sqrtmx rho *m sqrtmx sigma)).
Proof.
  move=> /psdmx_form [Rt ->] /psdmx_form [S ->].
  pose Rsw : 'M[C]_((a * c) * b, (a * b) * c) :=
    \matrix_(i, k) Rt (sigma23 i) k.
  pose Ssw : 'M[C]_((a * c) * b, (a * b) * c) :=
    \matrix_(i, k) S (sigma23 i) k.
  have HRsw :
      mxswap23 (Rt *m Rt^*t) = Rsw *m Rsw^*t.
  {
    apply/matrixP=> i j.
    rewrite mxswap23E !mxE.
    by apply: eq_bigr=> k _; rewrite !mxE.
  }
  have HSsw :
      mxswap23 (S *m S^*t) = Ssw *m Ssw^*t.
  {
    apply/matrixP=> i j.
    rewrite mxswap23E !mxE.
    by apply: eq_bigr=> k _; rewrite !mxE.
  }
  have Hcross : Rsw^*t *m Ssw = Rt^*t *m S.
  {
    apply/matrixP=> i j.
    rewrite !mxE.
    rewrite (reindex (@sigma23 a b c)).
    - by apply: eq_bigr=> k _; rewrite !mxE.
    - exists (@sigma23 a c b)=> k _; exact: sigma23K.
  }
  by rewrite HRsw HSsw !fid_gram_general_mx Hcross.
Qed.

(* Fidelity DPI for tracing the middle tensor factor of A x B x C. *)
(* path: utils:fid_ptr_mono_mxswap23 -> entropy:hmax_mx_projected_A_app_le -> *)
(*   entropy:entropy_data_proc -> *)
(*   bb84:bb84_secret *)
Lemma fid_ptr_mono_mxswap23 {a b c : nat}
    (rho sigma : 'M[C]_((a * b) * c)) :
  (0 < b)%N ->
  rho \is psdmx ->
  sigma \is psdmx ->
  @complex.Re R (trnorm (sqrtmx rho *m sqrtmx sigma)) <=
  @complex.Re R
    (trnorm (sqrtmx (ptrace2 (mxswap23 rho)) *m
             sqrtmx (ptrace2 (mxswap23 sigma)))).
Proof.
  move=> Hb_pos Hrho Hsigma.
  have Hrho_sw : mxswap23 rho \is psdmx := mxswap23_psdmx Hrho.
  have Hsigma_sw : mxswap23 sigma \is psdmx := mxswap23_psdmx Hsigma.
  have Hswap := fid_mxswap23 Hrho Hsigma.
  rewrite -Hswap.
  exact: fid_ptr_mono_mx.
Qed.

(* tb:fid item (ii) — matrix form: fidelity does not decrease under a       *)
(* channel given in Stinespring form (conjugate by an isometry W, then      *)
(* trace out the ancilla).  Matrix twin of `fid_ii_cptp_bounds`: composes   *)
(* `fid_isometry_conj_mx` (isometry invariance) with `fid_ptr_mono_mx`      *)
(* (partial-trace monotonicity).                                            *)
(* path: utils:fid_ii_cptp_bounds_mx -> utils:pd_mono -> *)
(*   entropy:entropy_data_proc -> bb84:bb84_secret *)
Lemma fid_ii_cptp_bounds_mx {dout din b : nat} (W : 'M[C]_(dout * b, din))
    (rho sigma : 'M[C]_din) :
  (0 < b)%N -> W^*t *m W = 1%:M ->
  rho \is psdmx -> sigma \is psdmx ->
  @complex.Re R (trnorm (sqrtmx rho *m sqrtmx sigma)) <=
  @complex.Re R (trnorm (sqrtmx (ptrace2 (W *m rho *m W^*t)) *m
                         sqrtmx (ptrace2 (W *m sigma *m W^*t)))).
Proof.
  move=> Hb HW Prho Psig.
  have HW0uni : W^*t \is unitarymx.
  { apply/unitarymxP. rewrite -adjmxE adjmxK. exact: HW. }
  have Hiso := fid_isometry_conj_mx HW0uni Prho Psig.
  rewrite !adjmxK in Hiso.
  have HWrho_psd : W *m rho *m W^*t \is psdmx.
    exact: psdmx_bimap_closed_gen Prho.
  have HWsig_psd : W *m sigma *m W^*t \is psdmx.
    exact: psdmx_bimap_closed_gen Psig.
  have Hdpi := fid_ptr_mono_mx Hb HWrho_psd HWsig_psd.
  rewrite -Hiso. exact: Hdpi.
Qed.

Section FidelityPtraceMono.
Variable (L : finType) (HL : L -> chsType) (A B : {set L}).
Hypothesis disAB : [disjoint A & B].
Notation S_AB := (A :|: B).

(* Labeled ordinary-fidelity DPI under partial trace. *)
(* fid_ptr_mono *)
(* infra: no tex label — labeled analog of matrix fid_ptr_mono_mx *)
(* consumer: fid_ptr_mono is used downstream by the BB84 secrecy proof. *)
(* path: utils:fid_ptr_mono -> entropy:entropy_data_proc -> *)
(*   bb84:bb84_secret *)
Lemma fid_ptr_mono (rho sigma : 'F[HL]_S_AB) :
  rho \is psdlf -> sigma \is psdlf ->
  (0 < dim 'H[HL]_B)%N ->
  fidelity rho sigma <=
  fidelity (ptrace_cast disAB rho) (ptrace_cast disAB sigma).
Proof.
  move=> Prho Psig HB.
  rewrite /fidelity !h2mx_comp !sqrtH_h2mx.
  rewrite !(h2mx_ptrace_cast_ptrace2 disAB).
  have Hrho_mx : h2mx rho \is psdmx by move: Prho; rewrite qualifE.
  have Hsig_mx : h2mx sigma \is psdmx by move: Psig; rewrite qualifE.
  pose U := @tenv_mxU R L HL A B.
  have HUadj : U^*t \is unitarymx := tenv_mxU_adj_unitarymx disAB.
  have HUrho_psd : U^*t *m h2mx rho *m U \is psdmx.
  { rewrite -[U in _ *m _ *m U]adjmxK.
    exact: psdmx_bimap_closed_gen Hrho_mx. }
  have HUsig_psd : U^*t *m h2mx sigma *m U \is psdmx.
  { rewrite -[U in _ *m _ *m U]adjmxK.
    exact: psdmx_bimap_closed_gen Hsig_mx. }
  have Hmat_eq :
      @complex.Re R (trnorm (sqrtmx (U^*t *m h2mx rho *m U) *m
                              sqrtmx (U^*t *m h2mx sigma *m U))) =
      @complex.Re R (trnorm (sqrtmx (h2mx rho) *m sqrtmx (h2mx sigma))).
  { clearbody U.
    move: U HUadj HUrho_psd HUsig_psd.
    case: _ / (tenv_dim disAB) => U HUadj HUrho_psd HUsig_psd.
    have := fid_unitary_conj_mx HUadj Hrho_mx Hsig_mx.
    by rewrite !adjmxK. }
  rewrite -Hmat_eq.
  exact: (fid_ptr_mono_mx HB HUrho_psd HUsig_psd).
Qed.

End FidelityPtraceMono.

(* Fidelity DPI for partial trace over 1st factor (ptrace1 monotonicity).         *)
(* Derived from ptrace2 DPI via mxswap: ptrace1 A = ptrace2(mxswap A).             *)
(* This is the labeled pd_mono_ptrace (ptrace-DPI route) prerequisite.            *)

(* ================================================================== *)
(* Generalized fidelity, ambient set-labelled wrapper.                 *)
(* ================================================================== *)

Section GeneralizedFidelityLfunSet.
Variables (L : finType) (H : L -> chsType) (S : {set L}).

(* gfid *)
(* infra: no tex label — fundamental & reusable ambient set-labelled utility *)
(* consumer: gfid is used downstream by the BB84 secrecy proof. *)
Definition gfid (rho sigma : 'F[H]_S) : R :=
  gfidelity (h2mx rho) (h2mx sigma).

End GeneralizedFidelityLfunSet.

Arguments gfid {L H S} rho sigma.

(* Generalized fidelity DPI for partial trace (ptrace2 version).                   *)
(* Derives from matrix fidelity DPI via `alt_gfid_gen` + trace preservation        *)
(* (`tr_ptrace2`). Direct consumer of `fid_ptr_mono_mx`.              *)
(* This is the matrix-level analog of Tomamichel's `th:pd-mono` at the gfidelity level.  *)
(* gfid_ptr_mono_mx *)
(* infra: no tex label — fundamental & reusable (mathcomp-style) *)
(* consumer: gfid_ptr_mono_mx is used downstream by the BB84 secrecy proof. *)
(* path: utils:gfid_ptr_mono_mx -> bb84:stat -> bb84:bb84_secret *)
Lemma gfid_ptr_mono_mx {m n : nat} (rho sigma : 'M[C]_(m * n)) :
  (0 < n)%N ->
  rho \is psdmx -> sigma \is psdmx ->
  gfidelity rho sigma <= gfidelity (ptrace2 rho) (ptrace2 sigma).
Proof.
  move=> Hn0 Hrho Hsigma.
  have Hp_rho := ptrace2_psd Hrho.
  have Hp_sigma := ptrace2_psd Hsigma.
  rewrite (alt_gfid_gen Hrho Hsigma) (alt_gfid_gen Hp_rho Hp_sigma).
  rewrite !tr_ptrace2.
  apply: lerD; last exact: lexx.
  exact: fid_ptr_mono_mx.
Qed.

Section GeneralizedFidelityPtraceMono.
Variable (L : finType) (HL : L -> chsType) (A B : {set L}).
Hypothesis disAB : [disjoint A & B].

(* Set-level labelled generalized-fidelity DPI under partial trace. *)
(* gfid_ptr_mono *)
(* infra: no tex label — fundamental & reusable (mathcomp-style) *)
(* path: utils:gfid_ptr_mono -> entropy:entropy_data_proc -> *)
(*   bb84:bb84_secret *)
Lemma gfid_ptr_mono (rho sigma : 'F[HL]_(A :|: B)) :
  rho \is psdlf -> sigma \is psdlf ->
  (0 < dim 'H[HL]_B)%N ->
  gfid rho sigma <=
  gfid (ptrace_cast disAB rho) (ptrace_cast disAB sigma).
Proof.
  move=> Prho Psigma HdB.
  rewrite /gfid !(h2mx_ptrace_cast_ptrace2 disAB).
  have Hrho_mx : h2mx rho \is psdmx by move: Prho; rewrite qualifE.
  have Hsigma_mx : h2mx sigma \is psdmx by move: Psigma; rewrite qualifE.
  pose U := @tenv_mxU R L HL A B.
  have HU : U \is unitarymx := tenv_mxU_unitarymx A B.
  have HUadj : U^*t \is unitarymx := tenv_mxU_adj_unitarymx disAB.
  have HUrho_psd : U^*t *m h2mx rho *m U \is psdmx.
  { rewrite -[U in _ *m _ *m U]adjmxK.
    exact: psdmx_bimap_closed_gen Hrho_mx. }
  have HUsigma_psd : U^*t *m h2mx sigma *m U \is psdmx.
  { rewrite -[U in _ *m _ *m U]adjmxK.
    exact: psdmx_bimap_closed_gen Hsigma_mx. }
  have Hmat_eq :
      gfidelity (h2mx rho) (h2mx sigma) =
      gfidelity (U^*t *m h2mx rho *m U)
                (U^*t *m h2mx sigma *m U).
  { rewrite (alt_gfid_gen Hrho_mx Hsigma_mx).
    rewrite (alt_gfid_gen HUrho_psd HUsigma_psd).
    have Htr_preserve : forall X : 'M[C]_(dim 'H[HL]_(A :|: B)),
      \tr (U^*t *m X *m U) = \tr X.
    { move=> X; rewrite mxtrace_mulC mulmxA.
      have /unitarymxP-> : U \is unitarymx := HU.
      by rewrite mul1mx. }
    rewrite !Htr_preserve.
    congr (_ + _).
    clearbody U.
    clear Htr_preserve HU.
    move: U HUadj HUrho_psd HUsigma_psd.
    case: _ / (tenv_dim disAB) => U HUadj HUrho_psd HUsigma_psd.
    have := fid_unitary_conj_mx HUadj Hrho_mx Hsigma_mx.
    move=> Hfid.
    rewrite !adjmxK in Hfid.
    by symmetry. }
  rewrite Hmat_eq.
  exact: (gfid_ptr_mono_mx HdB HUrho_psd HUsigma_psd).
Qed.

End GeneralizedFidelityPtraceMono.

(* Generalized fidelity DPI for partial trace (ptrace1 version).                   *)
(* Same structure as gfid_ptr_mono_mx, using ptrace1 variants.               *)

(* gfidelity invariance under simultaneous castmx. *)
(* path: utils:gfid_cast_mx -> entropy:entropy_data_proc -> *)
(*   bb84:bb84_secret *)
Lemma gfid_cast_mx {n m : nat} (eq : n = m) (rho tau : 'M[C]_n) :
  gfidelity (castmx (eq, eq) rho) (castmx (eq, eq) tau) = gfidelity rho tau.
Proof.
  by case: m / eq; rewrite !castmx_id.
Qed.
(* ================================================================== *)
(* Sub-norm matrix Uhlmann (gfidelity form), arbitrary rank.            *)
(* Generalizes `subnorm_matrix_uhlmann` by dropping the                  *)
(* `\rank psi_rho <= 1` hypothesis.                                     *)
(*                                                                      *)
(* Proof structure:                                                      *)
(*  Step D.1 Degenerate cases.                                          *)
(*    - sigma = 0 -> psi_sigma := 0 works (no rank constraint needed).   *)
(*    - alpha := Re(\tr psi_rho) = 0 -> psi_rho = 0 = rho; build rank-1 *)
(*      purification of sigma via `purification_exists_in_dim`.         *)
(*  Step D.2 Generic case (sigma != 0, alpha > 0).  Two routes:          *)
(*    (a) Spectral.  Diagonalise psi_rho = sum_i lambda_i |phi_i><phi_i|*)
(*        (PSD), apply rank-1 `subnorm_matrix_uhlmann` per eigenvector. *)
(*        Recombine using a common env unitary supplied by Layer C      *)
(*        (`purifications_iso_related`).                                *)
(*    (b) Lift.  Rescale psi_rho' := alpha^-1 *: psi_rho (den1mx),      *)
(*        purify to a rank-1 Phi : 'M_((a*b)*(a*b)) via                 *)
(*        `purification_mx_exists`.  View Phi as living on              *)
(*        'M_(a * (b * (a*b))).  Apply rank-1 `subnorm_matrix_uhlmann`  *)
(*        on Phi with sigma (env dim b * (a*b) >= b >= rank sigma).     *)
(*        Compress the resulting rank-1 purification of sigma back to   *)
(*        'M_(a*b) using Layer C / iso-relation arguments.              *)
(*  Step D.3 Verify all five conjuncts on the recombined witness.       *)
(*                                                                      *)
(* The degenerate, generic, and witness-verification cases are all       *)
(* handled by the lift construction above.  Environment compression and *)
(* the fidelity bridge are closed inline                                *)
(* using `gfid_cast_mx`, two applications of `gfid_ptr_mono_mx` *)
(* (DPI sandwich + antisymmetry), and the alpha-rescale algebra mirror  *)
(* of the rank-1 lemma.  Companion `_in_image` variant remains          *)
(* routed (mirrors rank-1 `subnorm_matrix_uhlmann_in_image`).            *)
(* ================================================================== *)
(* subnorm_matrix_uhlmann_arbitrary_rank *)
(* infra: no tex label - fundamental & reusable (mathcomp-style)        *)
(* consumer: subnorm_matrix_uhlmann_arbitrary_rank is used downstream by the BB84 secrecy proof. *)
(* path: utils:subnorm_matrix_uhlmann_arbitrary_rank -> utils:gfid_cast_mx -> *)
(*   entropy:entropy_data_proc -> *)
(*   bb84:bb84_secret *)
Lemma subnorm_matrix_uhlmann_arbitrary_rank {a b : nat}
    (psi_rho : 'M[C]_(a * b)) (rho sigma : 'M[C]_a) :
  psi_rho \is psdmx ->
  @complex.Re R (\tr psi_rho) <= 1 ->
  ptrace2 psi_rho = rho ->
  sigma \is psdmx ->
  @complex.Re R (\tr sigma) <= 1 ->
  (\rank sigma <= b)%N ->
  exists psi_sigma : 'M[C]_(a * b),
    [/\ psi_sigma \is psdmx,
        @complex.Re R (\tr psi_sigma) <= 1,
        ptrace2 psi_sigma = sigma &
        gfidelity psi_rho psi_sigma = gfidelity rho sigma].
Proof.
  move=> Hpsi_psd Hpsi_tr Hpsi_ptr Hsigma_psd Hsigma_tr Hsigma_rank.
  (* Derived facts about rho. *)
  have Hrho_psd : rho \is psdmx.
    by rewrite -Hpsi_ptr; apply: ptrace2_psd.
  have Htr_psi_rho : \tr psi_rho = \tr rho.
    by rewrite -Hpsi_ptr -tr_ptrace2.
  have Hrho_tr : @complex.Re R (\tr rho) <= 1.
    by rewrite -Htr_psi_rho.
  have Htr_psi_real : \tr psi_rho \is Num.real
    by apply: ger0_real; exact: psdmx_trace.
  have Htr_psi_ge0 : 0 <= @complex.Re R (\tr psi_rho).
    have := psdmx_trace Hpsi_psd. by rewrite lecE/= => /andP[_].
  (* Step D.1a: sigma = 0 branch (no rank constraint on psi_rho needed). *)
  case: (sigma =P 0) => [Hsig0|/eqP Hsig_nz].
  { exists 0; split.
    - exact: psdmx0.
    - by rewrite mxtrace0 raddf0/= ler01.
    - by rewrite linear0 Hsig0.
    - rewrite Hsig0.
      rewrite (alt_gfid_gen Hpsi_psd (@psdmx0 _ (a*b)%N)).
      rewrite (alt_gfid_gen Hrho_psd (@psdmx0 _ a)).
      rewrite !sqrtmx0 !mulmx0 !trnorm0.
      have HRe0 : @complex.Re R (0 : C) = 0 by rewrite raddf0.
      rewrite HRe0 !add0r !mxtrace0.
      by rewrite Htr_psi_rho. }
  (* Step D.1b: alpha = 0 branch -> psi_rho = 0 = rho. *)
  set alpha : R := @complex.Re R (\tr psi_rho).
  have Halpha_eq : \tr psi_rho = alpha%:C
    by rewrite /alpha (RRe_real Htr_psi_real).
  case: (alpha =P 0) => [Halpha0|/eqP Halpha_nz].
  { have Hpsi_tr0 : \tr psi_rho == 0 by rewrite Halpha_eq Halpha0 raddf0.
    have Hpsi_zero : psi_rho = 0
      by apply/eqP; rewrite -(psdmx_trace_eq0 Hpsi_psd).
    have Hrho_zero : rho = 0 by rewrite -Hpsi_ptr Hpsi_zero linear0.
    have Hsigma_den : sigma \is denmx.
      apply/denmxP; split; first exact: Hsigma_psd.
      have Htr_sig_real : \tr sigma \is Num.real.
        apply: ger0_real. exact: (psdmx_trace Hsigma_psd).
      rewrite -(RRe_real Htr_sig_real) -[1]/(1%:C : C) lecR.
      exact: Hsigma_tr.
    have [theta [Htheta_den [Htheta_rank Htheta_ptr]]] :=
      purification_exists_in_dim Hsigma_den Hsig_nz Hsigma_rank.
    exists theta.
    have Htheta_psd : theta \is psdmx := denmx_psd Htheta_den.
    have Htheta_tr_le : @complex.Re R (\tr theta) <= 1.
      have /denmxP[_ Htr_theta] := Htheta_den.
      have Htr_th_real : \tr theta \is Num.real
        by apply: ger0_real; apply: psdmx_trace; exact: denmx_psd Htheta_den.
      by move: Htr_theta; rewrite -(RRe_real Htr_th_real) -[1]/(1%:C : C) lecR.
    split.
    - exact: Htheta_psd.
    - exact: Htheta_tr_le.
    - exact: Htheta_ptr.
    - rewrite Hpsi_zero Hrho_zero.
      rewrite (alt_gfid_gen (@psdmx0 _ (a*b)%N) Htheta_psd).
      rewrite (alt_gfid_gen (@psdmx0 _ a) Hsigma_psd).
      rewrite !sqrtmx0 !mul0mx !trnorm0.
      have HRe0 : @complex.Re R (0 : C) = 0 by rewrite raddf0.
      rewrite HRe0 !add0r !mxtrace0.
      have Htr_theta_sigma : \tr theta = \tr sigma.
        by rewrite -Htheta_ptr -tr_ptrace2.
      by rewrite Htr_theta_sigma. }
  (* Step D.2: Generic case sigma != 0, alpha > 0.                       *)
  (* Lift route (b): rescale -> purify -> lift via rank-1 lemma.          *)
  (* Step D.2.1: rescale psi_rho' := alpha^-1 *: psi_rho (den1mx).        *)
  have Halpha_gt0 : 0 < alpha by rewrite lt_def Halpha_nz Htr_psi_ge0.
  have Halpha_C_ne0 : alpha%:C != 0 :> C.
    apply/negP=> /eqP H; move/eqP: Halpha_nz; apply.
    by apply/(@complexI R); rewrite H rmorph0.
  set alphaC : C := alpha%:C.
  set inv_alpha : R := (alpha^-1)%R.
  have Hinv_ge0 : 0 <= inv_alpha by rewrite /inv_alpha invr_ge0 ltW.
  have Hinv_alphaC : inv_alpha%:C = (alphaC^-1)%R
    by rewrite /inv_alpha /alphaC -fmorphV.
  have Halpha_unit : alphaC \is a GRing.unit
    by rewrite /alphaC unitfE.
  set psi_rho' : 'M[C]_(a * b) := inv_alpha%:C *: psi_rho.
  set rho' : 'M[C]_a := inv_alpha%:C *: rho.
  have Hpsi'_psd : psi_rho' \is psdmx.
    rewrite /psi_rho'.
    apply: psdmxZ=> //.
    by rewrite lecE/= eqxx/= Hinv_ge0.
  have Hpsi'_ptr : ptrace2 psi_rho' = rho'.
    by rewrite /psi_rho' /rho' linearZ/= Hpsi_ptr.
  have Hpsi'_tr : \tr psi_rho' = 1.
    rewrite /psi_rho' linearZ/= Halpha_eq Hinv_alphaC -/alphaC.
    by rewrite mulVf//.
  have Hpsi'_den1 : psi_rho' \is den1mx
    by apply/den1mxP; split=> //; apply/eqP.
  have Hpsi'_den : psi_rho' \is denmx by exact: den1mx_den.
  have Hpsi'_nz : psi_rho' != 0.
    apply/negP=> /eqP Hpz; move/eqP: Halpha_nz; apply.
    have : \tr psi_rho' = 0 by rewrite Hpz linear0.
    by rewrite Hpsi'_tr => /eqP; rewrite oner_eq0.
  (* Step D.2.2: build rank-1 purification Phi of psi_rho' on env (a*b). *)
  (* Use purification_exists_in_dim (from utils/mx/prop.v) since           *)
  (* purification_mx_exists lives downstream in pur.v which imports fid.v. *)
  have Hpsi'_rank_le : (\rank psi_rho' <= a * b)%N by exact: rank_leq_row.
  have [Phi [HPhi_den [HPhi_rk HPhi_ptr]]] :=
    purification_exists_in_dim Hpsi'_den Hpsi'_nz Hpsi'_rank_le.
  have HPhi_psd : Phi \is psdmx := denmx_psd HPhi_den.
  have HPhi_tr_le : @complex.Re R (\tr Phi) <= 1.
    have /denmxP[_ Htr_phi] := HPhi_den.
    have Htr_ph_real : \tr Phi \is Num.real
      by apply: ger0_real; exact: psdmx_trace HPhi_psd.
    by move: Htr_phi; rewrite -(RRe_real Htr_ph_real) -[1]/(1%:C : C) lecR.
  (* Step D.2.3: Cast Phi to view it on 'M_(a * (b * (a*b))).             *)
  (* Use mulnA: (a*b)*(a*b) = a*(b*(a*b)).  Apply esym to flip direction. *)
  set eAB : ((a * b) * (a * b) = a * (b * (a * b)))%N
    := esym (mulnA a b (a * b)).
  set Phi_cast : 'M[C]_(a * (b * (a * b))) := castmx (eAB, eAB) Phi.
  have HPhi_cast_psd : Phi_cast \is psdmx.
    by rewrite /Phi_cast /castmx_sq -[castmx _ _]/(castmx_sq eAB Phi);
       exact: castmx_sq_psdmx HPhi_psd.
  have HPhi_cast_tr : \tr Phi_cast = \tr Phi.
    by rewrite /Phi_cast -[castmx _ _]/(castmx_sq eAB Phi);
       exact: mxtrace_castmx_sq.
  have HPhi_cast_tr_le : @complex.Re R (\tr Phi_cast) <= 1
    by rewrite HPhi_cast_tr.
  have HPhi_cast_rank : (\rank Phi_cast <= 1)%N.
    rewrite /Phi_cast.
    have Hrk_eq : \rank (castmx (eAB, eAB) Phi) = \rank Phi
      by rewrite mxrank_cast.
    by rewrite Hrk_eq HPhi_rk.
  (* ptrace2 of Phi_cast = ptrace2 (ptrace2 Phi) = ptrace2 psi_rho' = rho'. *)
  have HPhi_cast_ptr : ptrace2 Phi_cast = rho'.
    rewrite /Phi_cast /eAB ptrace2_compose HPhi_ptr.
    exact: Hpsi'_ptr.
  (* Step D.2.4: apply rank-1 subnorm_matrix_uhlmann to (Phi_cast, rho',  *)
  (* sigma) on ambient (a, b*(a*b)).  Need rank sigma <= b*(a*b).          *)
  have Hsigma_rank_pos : (0 < \rank sigma)%N.
    rewrite lt0n mxrank_eq0; apply/eqP=> Hsig0.
    by move/eqP: Hsig_nz; apply.
  have Hb_pos : (0 < b)%N
    by exact: leq_trans Hsigma_rank_pos Hsigma_rank.
  have Hab_pos : (0 < a * b)%N.
    have Ha_pos : (0 < a)%N.
      have : (\rank sigma <= a)%N by exact: rank_leq_row.
      by move/(leq_trans Hsigma_rank_pos).
    by rewrite muln_gt0 Ha_pos Hb_pos.
  have Hsigma_rank_big : (\rank sigma <= b * (a * b))%N.
    by apply: leq_trans Hsigma_rank _; rewrite leq_pmulr.
  have [psi_sigma_big [Hpsb_psd Hpsb_rk Hpsb_tr Hpsb_ptr Hpsb_fid]] :=
    subnorm_matrix_uhlmann HPhi_cast_psd HPhi_cast_rank HPhi_cast_tr_le
                           HPhi_cast_ptr Hsigma_psd Hsigma_tr Hsigma_rank_big.
  (* Step D.2.5: env compression. *)
  (* Step D.2.5.1: reshape psi_sigma_big to psi_flat on (a*b)*(a*b) via mulnA.    *)
  set eAB' : (a * (b * (a * b)) = (a * b) * (a * b))%N := mulnA a b (a * b).
  set psi_flat : 'M[C]_((a * b) * (a * b)) := castmx (eAB', eAB') psi_sigma_big.
  have Hpsi_flat_psd : psi_flat \is psdmx
    by rewrite /psi_flat -[castmx _ _]/(castmx_sq eAB' psi_sigma_big);
       exact: castmx_sq_psdmx Hpsb_psd.
  have Hpsi_flat_tr : \tr psi_flat = \tr psi_sigma_big
    by rewrite /psi_flat -[castmx _ _]/(castmx_sq eAB' psi_sigma_big);
       exact: mxtrace_castmx_sq.
  have Hpsi_flat_rk : (\rank psi_flat <= 1)%N.
  { rewrite /psi_flat.
    have Hrk_eq : \rank (castmx (eAB', eAB') psi_sigma_big) = \rank psi_sigma_big
      by rewrite mxrank_cast.
    by rewrite Hrk_eq. }
  (* Step D.2.5.2: ptrace2 psi_flat = ptrace2 psi_sigma_big = sigma.              *)
  (* Use ptrace2_compose: castmx (esym mulnA) of an ((a*b)*(a*b)) matrix has     *)
  (* ptrace2 = ptrace2 (ptrace2 of original).  Going the other direction:        *)
  (* psi_flat = castmx (mulnA, mulnA) psi_sigma_big, so psi_sigma_big =          *)
  (* castmx (esym mulnA, esym mulnA) psi_flat.                                    *)
  have Hpt_flat_eq : ptrace2 (ptrace2 psi_flat) = ptrace2 psi_sigma_big.
  { have Hcast_eq : psi_sigma_big = castmx (esym eAB', esym eAB') psi_flat.
    { rewrite /psi_flat castmxK //. }
    rewrite Hcast_eq /eAB' ptrace2_compose //. }
  (* Step D.2.5.3: define candidate psi_sigma := ptrace2 psi_flat : 'M_(a*b).    *)
  set psi_sigma : 'M[C]_(a * b) := ptrace2 psi_flat.
  exists psi_sigma; split.
  (* Step D.2.5.4: PSD via ptrace2_psd.                                          *)
  - by apply: ptrace2_psd.
  (* Step D.2.5.5: Re(\tr psi_sigma) <= 1 via tr_ptrace2 chain.                  *)
  - have Htr_psi_eq : \tr psi_sigma = \tr psi_sigma_big
      by rewrite /psi_sigma -tr_ptrace2 Hpsi_flat_tr.
    by rewrite Htr_psi_eq.
  (* Step D.2.5.6: ptrace2 psi_sigma = sigma via Hpt_flat_eq + Hpsb_ptr.         *)
  - by rewrite /psi_sigma Hpt_flat_eq Hpsb_ptr.
  (* Step D.2.6: gfidelity equation.                                              *)
  (* Math route:                                                                  *)
  (*   D.2.6.1: gfidelity Phi_cast psi_sigma_big = gfidelity Phi psi_flat         *)
  (*           via gfid_cast_mx (eAB' = mulnA, eAB = esym mulnA cancels).       *)
  (*   D.2.6.2: gfidelity Phi psi_flat <= gfidelity psi_rho' psi_sigma            *)
  (*           via gfid_ptr_mono_mx (ptrace2 Phi = psi_rho',                *)
  (*           ptrace2 psi_flat = psi_sigma).                                     *)
  (*   D.2.6.3: gfidelity psi_rho' psi_sigma <= gfidelity rho' sigma              *)
  (*           via gfid_ptr_mono_mx (ptrace2 psi_rho' = rho',               *)
  (*           ptrace2 psi_sigma = sigma).                                        *)
  (*   Antisymmetry: chain returns to gfidelity rho' sigma (D.2.4 + D.2.6.1), so  *)
  (*           gfidelity psi_rho' psi_sigma = gfidelity rho' sigma.               *)
  (*   D.2.6.4: alpha-rescale to lift to unscaled (psi_rho, psi_sigma) vs         *)
  (*           (rho, sigma); correction terms match via tr equalities.            *)
  - (* Step D.2.6.A: trace identities used throughout.                             *)
    have Htr_psi_sigma_big_eq : \tr psi_sigma_big = \tr sigma.
    { by rewrite -Hpsb_ptr -tr_ptrace2. }
    have Htr_psi_flat_eq : \tr psi_flat = \tr sigma.
    { by rewrite Hpsi_flat_tr Htr_psi_sigma_big_eq. }
    have Htr_psi_sigma_eq : \tr psi_sigma = \tr sigma.
    { by rewrite /psi_sigma -tr_ptrace2 Htr_psi_flat_eq. }
    have HPhi_psi_rho'_tr : \tr Phi = \tr psi_rho'.
    { by rewrite -HPhi_ptr -tr_ptrace2. }
    (* Step D.2.6.1: gfidelity Phi_cast psi_sigma_big = gfidelity Phi psi_flat. *)
    (* Phi_cast = castmx (eAB,eAB) Phi; psi_flat = castmx (eAB',eAB') psi_sigma_big. *)
    (* Note eAB : (a*b)*(a*b) = a*(b*(a*b)), eAB' : a*(b*(a*b)) = (a*b)*(a*b).      *)
    (* The forward direction: gfid_cast_mx pushes castmx (eAB',eAB') across        *)
    (* gfidelity, identifying both sides on 'M_(a*(b*(a*b))).                        *)
    have HD261 : gfidelity Phi_cast psi_sigma_big = gfidelity Phi psi_flat.
    { rewrite -(gfid_cast_mx eAB' Phi_cast psi_sigma_big).
      rewrite -[castmx (eAB', eAB') psi_sigma_big]/psi_flat.
      have HPhi_id : castmx (eAB', eAB') Phi_cast = Phi.
      { rewrite /Phi_cast castmx_comp.
        rewrite (eq_irrelevance (etrans eAB eAB') (erefl _)).
        by rewrite castmx_id. }
      by rewrite HPhi_id. }
    (* Step D.2.6.2: gfidelity Phi psi_flat <= gfidelity psi_rho' psi_sigma. *)
    (* via gfid_ptr_mono_mx with (m,n) = (a*b, a*b) and Hab_pos.       *)
    have HptPhi : ptrace2 Phi = psi_rho' by exact: HPhi_ptr.
    have Hpt_psi_flat : ptrace2 psi_flat = psi_sigma by [].
    have HD262 :
      gfidelity Phi psi_flat <= gfidelity psi_rho' psi_sigma.
    { have Hmono := gfid_ptr_mono_mx Hab_pos HPhi_psd Hpsi_flat_psd.
      by rewrite HptPhi /psi_sigma in Hmono. }
    (* Step D.2.6.3: gfidelity psi_rho' psi_sigma <= gfidelity rho' sigma. *)
    have Hpt_psi_sigma : ptrace2 psi_sigma = sigma.
    { by rewrite /psi_sigma Hpt_flat_eq Hpsb_ptr. }
    have Hpsi_sigma_psd : psi_sigma \is psdmx by exact: ptrace2_psd Hpsi_flat_psd.
    have HD263 :
      gfidelity psi_rho' psi_sigma <= gfidelity rho' sigma.
    { have Hmono := gfid_ptr_mono_mx Hb_pos Hpsi'_psd Hpsi_sigma_psd.
      by rewrite Hpsi'_ptr Hpt_psi_sigma in Hmono. }
    (* Antisymmetry: chain.                                                  *)
    have HEq_scaled : gfidelity psi_rho' psi_sigma = gfidelity rho' sigma.
    { apply: le_anti.
      apply/andP; split; first exact: HD263.
      have Hchain : gfidelity rho' sigma <= gfidelity psi_rho' psi_sigma.
      { by rewrite -Hpsb_fid HD261. }
      exact: Hchain. }
    (* Step D.2.6.4: alpha-rescale.  Mirror the rank-1 proof's algebra at the *)
    (* main-term level; correction terms match because tr psi_rho = tr rho   *)
    (* and tr psi_sigma = tr sigma.                                          *)
    rewrite (alt_gfid_gen Hpsi_psd Hpsi_sigma_psd)
            (alt_gfid_gen Hrho_psd Hsigma_psd).
    rewrite Htr_psi_rho Htr_psi_sigma_eq.
    congr (_ + _).
    (* Reduce both trace-norm correction terms by using                         *)
    (* psi_rho = alpha *: psi_rho' and                                          *)
    (* rho = alpha *: rho' to push sqrt(alpha) through.                          *)
    have Hpsi_eq : psi_rho = alphaC *: psi_rho'.
    { rewrite /psi_rho' scalerA Hinv_alphaC -/alphaC.
      by rewrite divff// scale1r. }
    have Hrho_eq : rho = alphaC *: rho'.
    { rewrite /rho' scalerA Hinv_alphaC -/alphaC.
      by rewrite divff// scale1r. }
    have Hrho'_psd : rho' \is psdmx.
    { rewrite /rho'.
      by apply: psdmxZ=> //; rewrite lecE/= eqxx/= Hinv_ge0. }
    have Hsqrt_psi : sqrtmx psi_rho = (Num.sqrt alpha)%:C *: sqrtmx psi_rho'.
    { by rewrite Hpsi_eq /alphaC sqrtmxZ_nn// ltW. }
    have Hsqrt_rho : sqrtmx rho = (Num.sqrt alpha)%:C *: sqrtmx rho'.
    { by rewrite Hrho_eq /alphaC sqrtmxZ_nn// ltW. }
    rewrite Hsqrt_psi Hsqrt_rho.
    rewrite -!scalemxAl !trnormZ.
    set sqalpha_C : C := (Num.sqrt alpha)%:C.
    have Hsqalpha_ge0_C : (0 : C) <= sqalpha_C
      by rewrite /sqalpha_C lecE /= eqxx /= sqrtr_ge0.
    rewrite !(ger0_norm Hsqalpha_ge0_C).
    have HReM : forall T : C,
        @complex.Re R (sqalpha_C * T) = Num.sqrt alpha * @complex.Re R T.
    { move=> [c d] /=. by rewrite mul0r subr0. }
    rewrite !HReM.
    congr (_ * _).
    (* Reduce to gfidelity-level equality on rescaled states.  Use HEq_scaled. *)
    (* HEq_scaled : gfidelity psi_rho' psi_sigma = gfidelity rho' sigma.       *)
    (* Apply alt_gfid_gen on both sides; correction terms vanish since         *)
    (* tr psi_rho' = 1 and tr rho' = 1 give 1 - tr = 0, sqrt 0 = 0.           *)
    have Halpha_eq_rho : \tr rho = alpha%:C by rewrite -Htr_psi_rho.
    have Htr_rho'_one : \tr rho' = 1.
    { rewrite /rho' linearZ/= Halpha_eq_rho Hinv_alphaC -/alphaC.
      by rewrite mulVf//. }
    have HRe_zero_psi' : @complex.Re R (1 - \tr psi_rho') = 0.
    { by rewrite Hpsi'_tr subrr linear0. }
    have HRe_zero_rho' : @complex.Re R (1 - \tr rho') = 0.
    { by rewrite Htr_rho'_one subrr linear0. }
    move: HEq_scaled.
    rewrite (alt_gfid_gen Hpsi'_psd Hpsi_sigma_psd)
            (alt_gfid_gen Hrho'_psd Hsigma_psd).
    rewrite HRe_zero_psi' HRe_zero_rho' !sqrtr0 !mul0r !addr0.
    by [].
Qed.

(* Image-supported sub-norm matrix Uhlmann, arbitrary rank.              *)
(* Drops the `\rank psi_rho <= 1` hypothesis from                        *)
(* `subnorm_matrix_uhlmann_in_image`.  The proof mirrors the rank-1      *)
(* image variant: compress psi_rho to K := V^*t psi_rho V on            *)
(* the small space 'M_(a*b) (V := 1_a *t W column-iso), apply           *)
(* `subnorm_matrix_uhlmann_arbitrary_rank` to (K, rho, sigma), then      *)
(* embed psi_sigma := V *m psi_sigma_b *m V^*t back to 'M_(a*b').        *)
(* Arbitrary-rank image variant, proved by compression into the small space. *)
(* subnorm_matrix_uhlmann_arbitrary_rank_in_image *)
(* infra: no tex label - fundamental & reusable (mathcomp-style)        *)
(* consumer: subnorm_matrix_uhlmann_arbitrary_rank_in_image is used downstream by the BB84 secrecy proof. *)
(* path: utils:subnorm_matrix_uhlmann_arbitrary_rank_in_image -> *)
(*   utils:pd_mono -> entropy:entropy_data_proc -> *)
(*   bb84:bb84_secret *)
Lemma subnorm_matrix_uhlmann_arbitrary_rank_in_image {a b b' : nat}
    (W : 'M[C]_(b', b))
    (psi_rho : 'M[C]_(a * b')) (rho sigma : 'M[C]_a) :
  W^*t *m W = 1%:M ->
  ((1%:M : 'M[C]_a) *t W) *m ((1%:M : 'M[C]_a) *t W)^*t *m psi_rho = psi_rho ->
  psi_rho \is psdmx ->
  @complex.Re R (\tr psi_rho) <= 1 ->
  ptrace2 psi_rho = rho ->
  sigma \is psdmx ->
  @complex.Re R (\tr sigma) <= 1 ->
  (\rank sigma <= b)%N ->
  exists psi_sigma : 'M[C]_(a * b'),
    [/\ psi_sigma \is psdmx,
        @complex.Re R (\tr psi_sigma) <= 1,
        ptrace2 psi_sigma = sigma,
        ((1%:M : 'M[C]_a) *t W) *m ((1%:M : 'M[C]_a) *t W)^*t *m psi_sigma = psi_sigma &
        gfidelity psi_rho psi_sigma = gfidelity rho sigma].
Proof.
  move=> HW Himg Hpsi_psd Hpsi_tr Hpsi_ptr Hsigma_psd Hsigma_tr Hsigma_rank.
  set V : 'M[C]_(a * b', a * b) := (1%:M : 'M[C]_a) *t W.
  (* V is a column-isometry: V^*t *m V = 1. *)
  have HVtV : V^*t *m V = 1%:M.
  { rewrite /V adjmx_tens adjmx1 tensmx_mul mul1mx HW tensmx11. by []. }
  (* Image-support of psi_rho written via V V^*t. *)
  have Himg_V : V *m V^*t *m psi_rho = psi_rho by exact: Himg.
  have Hpsi_herm : psi_rho^*t = psi_rho.
  { have Hh : psi_rho \is hermmx := psdmx_herm Hpsi_psd.
    by symmetry; apply/hermmxP. }
  have HVVt_herm : (V *m V^*t)^*t = V *m V^*t
    by rewrite adjmxM adjmxK.
  have Himg_R : psi_rho *m (V *m V^*t) = psi_rho.
  { have Hadj : (V *m V^*t *m psi_rho)^*t = psi_rho^*t by rewrite Himg_V.
    move: Hadj; rewrite adjmxM HVVt_herm Hpsi_herm => Hadj.
    exact: Hadj. }
  set K : 'M[C]_(a * b) := V^*t *m psi_rho *m V.
  have Hpsi_eq : psi_rho = V *m K *m V^*t.
  { rewrite /K.
    have step : V *m (V^*t *m psi_rho *m V) *m V^*t =
                (V *m V^*t) *m psi_rho *m (V *m V^*t)
      by rewrite !mulmxA.
    rewrite step Himg_V Himg_R. by []. }
  have HK_psd : K \is psdmx := formV_psdmx V Hpsi_psd.
  have HK_tr_eq : \tr K = \tr psi_rho.
  { rewrite /K.
    rewrite mxtrace_mulC mulmxA.
    by rewrite Himg_V. }
  have HK_tr : @complex.Re R (\tr K) <= 1 by rewrite HK_tr_eq.
  have Hpt_iso : ptrace2 (V *m K *m V^*t) = ptrace2 K.
  { rewrite /V. exact: (@ptrace2_conj_tens_right_iso a b b' W K HW). }
  have HK_ptr : ptrace2 K = rho.
  { rewrite -Hpsi_ptr Hpsi_eq.
    by rewrite Hpt_iso. }
  (* Apply the arbitrary-rank version on the small space 'M_(a*b). *)
  have [psi_sigma_b [Hpb_psd Hpb_tr Hpb_ptr Hpb_fid]] :=
    subnorm_matrix_uhlmann_arbitrary_rank HK_psd HK_tr HK_ptr Hsigma_psd Hsigma_tr Hsigma_rank.
  set psi_sigma : 'M[C]_(a * b') := V *m psi_sigma_b *m V^*t.
  exists psi_sigma; split.
  - rewrite /psi_sigma. apply: form_psdmx. exact: Hpb_psd.
  - have Htr_eq : \tr psi_sigma = \tr psi_sigma_b.
    { rewrite /psi_sigma.
      rewrite mxtrace_mulC mulmxA.
      by rewrite HVtV mul1mx. }
    by rewrite Htr_eq.
  - rewrite /psi_sigma /V (@ptrace2_conj_tens_right_iso a b b' W psi_sigma_b HW).
    exact: Hpb_ptr.
  - rewrite /psi_sigma.
    have HVVtV : V *m V^*t *m V = V.
    { have step : V *m V^*t *m V = V *m (V^*t *m V) by rewrite mulmxA.
      by rewrite step HVtV mulmx1. }
    have step2 : V *m V^*t *m (V *m psi_sigma_b *m V^*t) =
                 (V *m V^*t *m V) *m psi_sigma_b *m V^*t
      by rewrite !mulmxA.
    rewrite step2 HVVtV. by [].
  - rewrite Hpsi_eq /psi_sigma -/V.
    have HVi : V^*t \is unitarymx.
    { apply/unitarymxP.
      rewrite -adjmxE adjmxK. exact: HVtV. }
    rewrite (gfid_isometry_conj_mx HVi HK_psd Hpb_psd HK_tr Hpb_tr).
    exact: Hpb_fid.
Qed.

(* Matrix-level fidelity invariance under mxswap. Needed to derive ptrace1 DPI    *)
(* from ptrace2 DPI.                                                              *)

Section gfid_tenv_mxU_conj.
Variable (L : finType) (HL : L -> chsType) (A B : {set L}).
Hypothesis disAB : [disjoint A & B].

Let nAB := (dim 'H[HL]_(A :|: B)).

(* path: utils:gfid_tenv_mxU_conj_eq_mx -> entropy:smooth_hmax_labelled_mx -> *)
(*   bb84:stat -> bb84:bb84_secret *)
Lemma gfid_tenv_mxU_conj_eq_mx
    (rho tau : 'M[C]_nAB) :
  rho \is psdmx -> tau \is psdmx ->
  gfidelity rho tau =
  gfidelity ((@tenv_mxU R L HL A B)^*t *m rho *m (@tenv_mxU R L HL A B))
            ((@tenv_mxU R L HL A B)^*t *m tau *m (@tenv_mxU R L HL A B)).
Proof.
  move=> Hrho Htau.
  pose U := @tenv_mxU R L HL A B.
  have HU : U \is unitarymx := tenv_mxU_unitarymx A B.
  have HUadj : U^*t \is unitarymx := tenv_mxU_adj_unitarymx disAB.
  have HUrho : U^*t *m rho *m U \is psdmx.
  { rewrite -[U in _ *m _ *m U]adjmxK.
    exact: psdmx_bimap_closed_gen Hrho. }
  have HUtau : U^*t *m tau *m U \is psdmx.
  { rewrite -[U in _ *m _ *m U]adjmxK.
    exact: psdmx_bimap_closed_gen Htau. }
  rewrite (alt_gfid_gen Hrho Htau).
  rewrite (alt_gfid_gen HUrho HUtau).
  have Htr_preserve : forall (X : 'M[C]_nAB), \tr (U^*t *m X *m U) = \tr X.
  { move=> X.
    rewrite mxtrace_mulC mulmxA.
    have /unitarymxP-> : U \is unitarymx := HU.
    by rewrite mul1mx. }
  rewrite !Htr_preserve.
  congr (_ + _).
  clearbody U.
  clear Htr_preserve HU.
  move: U HUadj HUrho HUtau.
  case: _ / (tenv_dim disAB) => U HUadj HUrho HUtau.
  have := fid_unitary_conj_mx HUadj Hrho Htau.
  move=> Hfid.
  rewrite !adjmxK in Hfid.
  by symmetry.
Qed.

End gfid_tenv_mxU_conj.

(* ================================================================== *)
(* tex: tb:fid item (vi) — Tomamichel, 'A Framework for Non-Asymptotic  *)
(*   Quantum Information Theory' (PhD thesis, arXiv:1203.2142),         *)
(*   Table 3.1, item (vi): fidelity additive on block-diagonal states   *)
(* math: F(ρ₁⊕ρ₂, τ₁⊕τ₂) = F(ρ₁,τ₁) + F(ρ₂,τ₂)                       *)
(* ================================================================== *)
(* tex: tb:fid item (v) — Tomamichel, 'A Framework for Non-Asymptotic   *)
(*   Quantum Information Theory' (PhD thesis, arXiv:1203.2142),         *)
(*   Table 3.1, item (v): fidelity monotone in right argument under ≥  *)
(* math: σ ≥ ρ ⇒ F(σ,τ) ≥ F(ρ,τ)                                     *)
(* Stated in right-arg form (as in CoqQ-2): rho ≤ sigma raises F in the *)
(* "second" slot; symmetry of fidelity gives the tex (first-slot) form. *)
(* ================================================================== *)
(* tex: tb:fid item (iv) — Tomamichel, 'A Framework for Non-Asymptotic  *)
(*   Quantum Information Theory' (PhD thesis, arXiv:1203.2142),         *)
(*   Table 3.1, item (iv): fidelity under projection conjugation        *)
(* math: F(ΠρΠ, τ) = F(ΠρΠ, ΠτΠ) = F(ρ, ΠτΠ)                          *)
End GramFidelity.

(* ================================================================== *)
(* sqrt(1 - x^2) anti-monotonicity helpers + gfidelity CPTN Kraus DPI.  *)
(* ================================================================== *)

(* sqrt_1msq_antimono *)
(* infra: no tex label — fundamental & reusable (mathcomp-style) *)
(* consumer: sqrt_1msq_antimono is used downstream by the BB84 secrecy proof. *)
(* path: utils:sqrt_1msq_antimono -> utils:sqrt_1msq_antimono_gen -> *)
(*   bb84:stat -> bb84:bb84_secret *)
Lemma sqrt_1msq_antimono (a b : R) :
  0 <= a -> a <= 1 -> 0 <= b -> b <= 1 ->
  a <= b ->
  Num.sqrt (1 - b ^+ 2) <= Num.sqrt (1 - a ^+ 2).
Proof.
  move=> Ha0 Ha1 Hb0 Hb1 Hab.
  have Hb2_le1 : b ^+ 2 <= 1.
  { have := @lerXn2r R 2 b 1 Hb0 ler01 Hb1.
    by rewrite expr1n. }
  have H1b2 : 0 <= 1 - b ^+ 2 by rewrite subr_ge0.
  have H1a2 : 1 - b ^+ 2 <= 1 - a ^+ 2.
  { rewrite lerD2l lerN2.
    by apply: (@lerXn2r R 2 a b). }
  by rewrite ler_sqrt //; apply: le_trans H1b2 H1a2.
Qed.

(* path: utils:sqrt_1msq_antimono_gen -> bb84:stat -> bb84:bb84_secret *)
Lemma sqrt_1msq_antimono_gen (a b : R) :
  0 <= a -> a <= 1 -> 0 <= b ->
  a <= b ->
  Num.sqrt (1 - b ^+ 2) <= Num.sqrt (1 - a ^+ 2).
Proof.
  move=> Ha0 Ha1 Hb0 Hab.
  case: (lerP b 1) => Hb1.
  - exact: sqrt_1msq_antimono.
  - rewrite ler0_sqrtr ?sqrtr_ge0// subr_le0.
    have := @lerXn2r R 2 1 b ler01 Hb0 (ltW Hb1).
    by rewrite expr1n.
Qed.

(* Generalized fidelity DPI under a CPTN Kraus channel.                 *)
(* tex: tb:fid monotonicity/DPI support — Tomamichel, 'A Framework for  *)
(*   Non-Asymptotic Quantum Information Theory' (PhD thesis,            *)
(*   arXiv:1203.2142), Table 3.1 (items (ii), (v))                      *)
(* Consumer: pur_dist_mx_cptn_kraus_contract in pd.v.                   *)

End FvqkdReal.

Arguments fidelity {R L H S} rho tau.
Arguments gfid {R L H S} rho sigma.
