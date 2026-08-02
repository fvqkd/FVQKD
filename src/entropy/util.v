(* -------------------------------------------------------------------- *)
(* util.v — class-entangled-max + op-bound                              *)
(* -------------------------------------------------------------------- *)
(* Module: entropy.util                             *)
(* Source: Tomamichel, 'A Framework for Non-Asymptotic Quantum          *)
(*   Information Theory' (PhD thesis, arXiv:1203.2142), Lemma A.2        *)
(*   (tex lm:op-bound) and Lemma A.4                                    *)
(*   (tex lm:smmoth/class/class-entangled-max).                         *)
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
From quantum.dirac Require Import hstensor setdec.

Import Order.TTheory GRing.Theory Num.Theory Num.Def MxLownerOrder.
Import VectorInternalTheory.

(* --- FVQKD imports --- *)
From utils Require Import exports.
From entropy Require Import def prop.

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
(* Tomamichel thesis (arXiv:1203.2142), Lemma A.2 — tex lm:op-bound.    *)
(* math: M ∈ Pos(ℋ ⊗ ℋ') ⇒ M ≤ dim(ℋ') · (Tr_{ℋ'} M) ⊗ I_{ℋ'}.         *)
(* consumer: op_ineq is used downstream by the BB84 secrecy proof. *)
(* ================================================================== *)

Section OpBound.
Variable (L : finType) (HL : L -> chsType) (A B : {set L}).
Hypothesis disAB : [disjoint A & B].
Notation S_AB := (A :|: B).

(* path: entropy:op_bound -> lhl:min_coll_bound -> *)
(*   bb84:privacy_amplification -> bb84:bb84_secret *)
Lemma op_bound (M : 'F[HL]_S_AB) :
  M \is psdlf ->
  (M : 'F[HL]_S_AB) <=
    (dim 'H[HL]_B)%:R *: (ptrace_cast disAB M \⊗ (\1 : 'F[HL]_B)).
Proof.
  move=> HM.
  pose a := dim 'H[HL]_A.
  pose b := dim 'H[HL]_B.
  pose U := @tenv_mxU R L HL A B.
  have HU : U \is unitarymx := tenv_mxU_unitarymx _ _.
  have HUadj : U^*t \is unitarymx := tenv_mxU_adj_unitarymx disAB.
  have U_mul_Uadj : U *m U^*t = 1%:M := unitarymxK HU.
  pose N : 'M[C]_(a * b) := U^*t *m h2mx M *m U.
  have HN_psd : N \is psdmx.
  { rewrite /N -[U in _ *m _ *m U]adjmxK.
    move: HM; rewrite qualifE.
    exact: psdmx_bimap_closed_gen. }
  have HN_bound : N <= b%:R *: (ptrace2 N *t (1%:M : 'M[C]_b)).
  {
    rewrite le_lownerE.
    pose E (i j : 'I_b) : 'M[C]_(a * b) :=
      (1%:M : 'M[C]_a) *t (delta_mx i j : 'M[C]_b).
    pose D := \sum_j E j j *m N *m E j j.
    have HEadj : forall i j, (E i j)^*t = E j i.
    { by move=> i j; rewrite /E adjmx_tens adjmx1 adjmx_delta. }
    have HEcomplete : \sum_j E j j = 1%:M :> 'M[C]_(a * b).
    {
      rewrite /E.
      transitivity ((1%:M : 'M[C]_a) *t
        (\sum_(j : 'I_b) (delta_mx j j : 'M[C]_b))).
      { by rewrite linear_sumr. }
      by rewrite -mx1_sum_delta tensmx11.
    }
    have delta_sumR : forall (T : finType) (f : T -> C) (j : T),
      \sum_i (i == j)%:R * f i = f j.
    {
      move=> T f j; rewrite (bigD1 j) //= eqxx mul1r big1 ?addr0 //.
      by move=> i /negPf ->; rewrite mul0r.
    }
    have ptrace2E' : forall s t (B0 : 'M[C]_(s * t)) r1 r2,
      (ptrace2 B0) r1 r2 =
      \sum_k0 B0 (mxtens_index (r1, k0)) (mxtens_index (r2, k0)).
    {
      move=> s t B0 r1 r2; rewrite ptrace2E1 ptrace1E.
      by apply: eq_bigr => k0 _; rewrite mxE !mxtens_indexK.
    }
    have Hkey : ptrace2 N *t (1%:M : 'M[C]_b) =
      \sum_(i : 'I_b) \sum_(j : 'I_b) E j i *m N *m E i j.
    {
      apply/matrixP => r s.
      case: (mxtens_indexP r) => r1 r2.
      case: (mxtens_indexP s) => s1 s2.
      rewrite [LHS]tensmxE ptrace2E'.
      rewrite [in RHS]summxE.
      under [RHS]eq_bigr => i0 _ do rewrite summxE.
      transitivity (
        \sum_i \sum_j (j == r2)%:R * (j == s2)%:R *
          N (mxtens_index (r1, i)) (mxtens_index (s1, i))); last first.
      {
        apply: eq_bigr => i0 _; apply: eq_bigr => j0 _.
        set X := E j0 i0 *m N *m E i0 j0.
        have -> : X (mxtens_index (r1, r2)) (mxtens_index (s1, s2)) =
          (mxswap X) (mxtens_index (r2, r1)) (mxtens_index (s2, s1)).
        { by rewrite /mxswap mxE !mxtens_indexK. }
        rewrite /X -!(mxswap_mul (m:=a) (n:=a) (p:=b) (q:=b) (r:=a) (s:=b)).
        rewrite /E !(mxswap_tens (m:=a) (n:=a) (p:=b) (q:=b)).
        rewrite tens_delta_mx1_mulEr tens_delta_mx1_mulEl.
        rewrite /mxswap mxE !mxtens_indexK /=.
        by rewrite mulrA [X in X * _]mulrC.
      }
      rewrite [1%:M _ _]mxE mulrC mulr_sumr.
      apply: eq_bigr => i0 _.
      have Hj : \sum_(j0 : 'I_b) (j0 == r2)%:R * ((j0 == s2)%:R *
        N (mxtens_index (r1, i0)) (mxtens_index (s1, i0))) =
        (r2 == s2)%:R * N (mxtens_index (r1, i0)) (mxtens_index (s1, i0)).
      { exact: delta_sumR. }
      rewrite -Hj.
      by apply: eq_bigr => j0 _; rewrite mulrA.
    }
    have Hsplit : b%:R *: (ptrace2 N *t (1%:M : 'M[C]_b)) - N =
      b%:R *: (\sum_i \sum_(j | j != i) E j i *m N *m E i j) +
      (b%:R *: D - N).
    {
      have Hsum_split : \sum_i \sum_j E j i *m N *m E i j =
        D + \sum_i \sum_(j | j != i) E j i *m N *m E i j.
      {
        rewrite /D.
        transitivity (\sum_i (E i i *m N *m E i i +
                              \sum_(j | j != i) E j i *m N *m E i j)).
        { apply: eq_bigr => i _.
          by rewrite (bigD1 i). }
        by rewrite big_split.
      }
      rewrite Hkey Hsum_split scalerDr.
      by rewrite addrAC addrC.
    }
    rewrite Hsplit.
    apply: psdmxD.
    - apply: psdmxZ; first by rewrite ler0n.
      apply: psdmx_sum => i _; apply: psdmx_sum => j _.
      rewrite -HEadj.
      exact: formV_psdmx HN_psd.
    - set X := b%:R *: D - N.
      suff HX2 : X *+ 2 \is psdmx.
      { have -> : X = 2%:R^-1 *: (X *+ 2).
        { by rewrite -scaler_nat scalerA mulVf ?scale1r // pnatr_eq0. }
        by apply: psdmxZ => //; rewrite invr_ge0 ler0n. }
      rewrite -scaler_nat /X scalerBr.
      have HN_expand : N = \sum_j \sum_k E j j *m N *m E k k.
      {
        transitivity ((\sum_j E j j) *m N *m (\sum_k E k k)).
        { by rewrite HEcomplete mul1mx mulmx1. }
        rewrite -mulmxA mulmx_suml.
        by under eq_bigr do rewrite mulmxA mulmx_sumr.
      }
      have HbD : b%:R *: D =
        \sum_j \sum_(k : 'I_b) E j j *m N *m E j j.
      {
        rewrite /D scaler_sumr; apply: eq_bigr => j _.
        by rewrite sumr_const card_ord scaler_nat.
      }
      rewrite -scalerBr HbD [in X in _ - X]HN_expand.
      suff -> : 2 *: (\sum_j \sum_(k : 'I_b) E j j *m N *m E j j -
                \sum_j \sum_k E j j *m N *m E k k) =
        \sum_j \sum_(k : 'I_b)
          (E j j - E k k) *m N *m (E j j - E k k).
      {
        apply: psdmx_sum => j _; apply: psdmx_sum => k _.
        have Hself : (E j j - E k k)^*t = E j j - E k k.
        { by rewrite linearB /= !HEadj. }
        rewrite -[X in X *m _ *m _]Hself.
        exact: formV_psdmx HN_psd.
      }
      under [RHS]eq_bigr => j _ do
        under eq_bigr => k _ do
          rewrite mulmxBr !mulmxBl opprB addrACA.
        under [RHS]eq_bigr => j _ do
          rewrite !big_split /=.
        rewrite !big_split /=.
        pose A0 := \sum_(i < b) \sum_(i0 < b) E i i *m N *m E i i.
        pose A1 := \sum_(i < b) \sum_(i0 < b) E i0 i0 *m N *m E i0 i0.
        pose nB := \sum_(i < b) \sum_(i0 < b) - (E i i *m N *m E i0 i0).
        pose nB1 := \sum_(i < b) \sum_(i0 < b) - (E i0 i0 *m N *m E i i).
        pose B0 := \sum_(j < b) \sum_(k < b) E j j *m N *m E k k.
        change (2 *: (A0 - B0) = A0 + A1 + (nB1 + nB)).
        have HA1 : A1 = A0.
        { by rewrite /A1 /A0 exchange_big. }
        have HnB1 : nB1 = nB.
        { by rewrite /nB1 /nB exchange_big. }
        rewrite HA1 HnB1.
        have HnB : nB = - B0.
        {
          rewrite /nB /B0 -sumrN; apply: eq_bigr => j0 _.
          by rewrite -sumrN.
        }
        rewrite HnB.
        rewrite scalerBr.
      have -> : (2 : C) *: A0 = A0 + A0.
      { by rewrite -mulr2n scaler_nat. }
      have -> : (2 : C) *: B0 = B0 + B0.
      { by rewrite -mulr2n scaler_nat. }
      by rewrite opprD.
  }
  rewrite lef_h2mx.
  have Hleft : h2mx M = U *m N *m U^*t.
  { by rewrite /N !mulmxA U_mul_Uadj mul1mx -mulmxA U_mul_Uadj mulmx1. }
  have Hright :
      h2mx ((dim 'H[HL]_B)%:R *:
        (ptrace_cast disAB M \⊗ (\1 : 'F[HL]_B))) =
      U *m (b%:R *: (ptrace2 N *t (1%:M : 'M[C]_b))) *m U^*t.
  {
    have Hscale :
        h2mx ((dim 'H[HL]_B)%:R *:
          (ptrace_cast disAB M \⊗ (\1 : 'F[HL]_B))) =
        (dim 'H[HL]_B)%:R *:
          h2mx (ptrace_cast disAB M \⊗ (\1 : 'F[HL]_B)).
    {
      by rewrite h2mxZ_lf.
    }
    rewrite Hscale h2mx_tenf h2mx1 (h2mx_ptrace_cast_ptrace2 disAB M) /N.
    by rewrite scalemxAl scalemxAr.
  }
  rewrite Hleft Hright le_lownerE -mulmxBl -mulmxBr.
  by move: HN_bound; rewrite le_lownerE; exact: psdmx_bimap_closed_gen.
Qed.

End OpBound.

(* ================================================================== *)
(* Tomamichel thesis (arXiv:1203.2142), Lemma A.4 — tex lm:smmoth/class/class-entangled-max. *)
(* math: For ρ ∈ S_≤(ℋ_{XX'AB}) coherent classical between X and X',   *)
(*   H_max(XA|X'B)_ρ ≤ H_max(A|XX'B)_ρ.                                 *)
(* consumer: lm_emx is used downstream by the BB84 secrecy proof. *)
(* Formal statement: canonical-copy-projector form.        *)
(* We assume `dim H_X = dim H_X'`, build the coherent-classical          *)
(* projector Π_XX' = Σ_x |x><x|_X ⊗ |x><x|_{X'}, require sub-normalized  *)
(* `rhoXX'AB`, and assume `rhoXX'AB = Π rhoXX'AB Π`.                    *)
(* ================================================================== *)
Section ClassEntangledMax.
Variable (L : finType) (H : L -> chsType).
Variables (X X' A B : {set L}).
Hypothesis disXX' : [disjoint X & X'].
Hypothesis disXA : [disjoint X & A].
Hypothesis disXB : [disjoint X & B].
Hypothesis disX'A : [disjoint X' & A].
Hypothesis disX'B : [disjoint X' & B].
Hypothesis disAB : [disjoint A & B].
Hypothesis dimXX' : dim 'H[H]_X = dim 'H[H]_(X').
Notation S_XX' := (X :|: X').
Notation S_AB := (A :|: B).
Notation S_X'B := (X' :|: B).
Notation S_XX'B := (S_XX' :|: B).
Notation S_XX'AB := (S_XX' :|: S_AB).
Let eqXX' : dim 'H[H]_X = dim 'H[H]_(X') := dimXX'.

Let cc_idx (x : 'Idx[H]_X) : 'Idx[H]_(X') :=
  n2i (cast_ord eqXX' (i2n x)).

Let cc_pair (x : 'Idx[H]_X) : 'H[H]_S_XX' :=
  deltav x ⊗v deltav (cc_idx x).

Let cc_proj_xx : 'F[H]_S_XX' :=
  sumoutp (fun=>1) cc_pair cc_pair.

(* Classical entangled max-entropy bound. This labelled statement is kept  *)
(* as a reusable companion to the min-entropy class bounds, even when a    *)
(* downstream proof chooses a direct min-entropy route.                    *)
Lemma class_entangled_max (rhoXX'AB : 'F[H]_S_XX'AB) :
  rhoXX'AB \is denlf ->
  0 < @complex.Re R (\Tr rhoXX'AB) ->
  (* ρ is coherent classical between X and X': Π_XX' ρ Π_XX' = ρ *)
  rhoXX'AB =
    (lift_lf (@finset.subsetUl _ S_XX' S_AB) cc_proj_xx) \o
      rhoXX'AB \o
    (lift_lf (@finset.subsetUl _ S_XX' S_AB) cc_proj_xx) ->
  (hmaxE S_X'B rhoXX'AB <= hmaxE S_XX'B rhoXX'AB)%E.
Proof.
  move=> Hrho_den Hrho_pos Hcoh.
  have Prho : rhoXX'AB \is psdlf := denlf_psd Hrho_den.
  have Hrhon : @complex.Re R (\Tr rhoXX'AB) <= 1.
  {
    have Hreal : \Tr rhoXX'AB \is Num.real :=
      ger0_real (psdlf_trlf Prho).
    by move: (denlf_trlf Hrho_den); rewrite -(RRe_real Hreal) lecR.
  }
  have disX_X'B : [disjoint X & S_X'B].
  {
    move: disXX' disXB.
    setdec.
  }
  have disXX'_B : [disjoint S_XX' & B].
  {
    move: disXB disX'B.
    setdec.
  }
  have disA_XX'B : [disjoint A & S_XX'B].
  {
    move: disXA disX'A disAB.
    setdec.
  }
  have eqA_XX'B : (A :|: S_XX'B) = S_XX'AB.
  {
    setdec.
  }
  have eqX_X'B : (X :|: S_X'B) = S_XX'B.
  {
    setdec.
  }
  pose Px (x : 'Idx[H]_X) := [> deltav x ; deltav x <].
  pose Qx (x : 'Idx[H]_X) := [> deltav (cc_idx x) ; deltav (cc_idx x) <].
  pose QxB (x : 'Idx[H]_X) : 'F[H]_S_X'B := Qx x \O (\1 : 'F_B).
  pose PxxB : 'F[H]_S_XX'B :=
    lift_lf (@finset.subsetUl _ S_XX' B) cc_proj_xx.
  pose Pfull : 'F[H]_S_XX'AB :=
    lift_lf (@finset.subsetUl _ S_XX' S_AB) cc_proj_xx.
  have HQxB_ten (x : 'Idx[H]_X) :
      QxB x = (Qx x \⊗ (\1 : 'F_B) : 'F[H]_S_X'B).
  {
    apply: to_Fnd_inj.
    by rewrite /QxB (sdotFT _ _ disX'B) to_Fnd_tenE.
  }
  have cc_idxK :
      cancel cc_idx (fun x' : 'Idx[H]_(X') =>
        n2i (cast_ord (esym eqXX') (i2n x'))).
  {
    move=> x.
    apply: i2n_inj.
    rewrite /cc_idx !n2iK cast_ord_comp cast_ord_id.
    by [].
  }
  have cc_idxKV :
      cancel (fun x' : 'Idx[H]_(X') =>
                n2i (cast_ord (esym eqXX') (i2n x'))) cc_idx.
  {
    move=> x'.
    apply: i2n_inj.
    rewrite /cc_idx !n2iK cast_ord_comp cast_ord_id.
    by [].
  }
  have cc_idx_bij : {on [pred x | true], bijective cc_idx}.
  {
    exists (fun x' : 'Idx[H]_(X') =>
      n2i (cast_ord (esym eqXX') (i2n x'))).
    - by move=> x _; apply: cc_idxK.
    - by move=> x' _; apply: cc_idxKV.
  }
  have cc_pair_dot (x y : 'Idx[H]_X) :
      [< cc_pair x ; cc_pair y >] = (x == y)%:R.
  {
    rewrite /cc_pair tenv_dot //.
    case: (boolP (x == y)) => [/eqP ->|Hxy].
    - by rewrite !dv_dot !eqxx mul1r.
    - rewrite dv_dot.
      by move/negPf: Hxy => ->; rewrite mul0r.
  }
  pose cc_pair_ponb : 'PONB('Idx[H]_X; 'H[H]_S_XX') :=
    PONB.Pack
      (PONB.Class
        (isPONB.Build R 'H[H]_S_XX' 'Idx[H]_X cc_pair cc_pair_dot)).
  have cc_proj_xx_proj : cc_proj_xx \is projlf.
  {
    rewrite /cc_proj_xx.
    change (sumoutp (fun=> 1) cc_pair_ponb cc_pair_ponb \is projlf).
    exact: sumoutp_proj.
  }
  have PxxB_proj : PxxB \is projlf.
  {
    by rewrite /PxxB -lift_lf_projE cc_proj_xx_proj.
  }
  have Pfull_proj : Pfull \is projlf.
  {
    by rewrite /Pfull -lift_lf_projE cc_proj_xx_proj.
  }
  rewrite (@hmaxE_EFin R L H S_XX'AB S_X'B rhoXX'AB Prho Hrhon Hrho_pos).
  rewrite (@hmaxE_EFin R L H S_XX'AB S_XX'B rhoXX'AB Prho Hrhon Hrho_pos).
  rewrite lee_fin.
  apply: hmax_lub.
  - exact: hmax_has_sup Prho Hrhon Hrho_pos.
  - move=> v.
  rewrite /hmax_feasible.
  move=> [sigma [Psig_den Hv]].
  have Psig_psd : sigma \is psdlf := den1lf_psd Psig_den.
  have Hsig_tr1 : \Tr sigma = 1 := den1lf_trlf Psig_den.
  have Hsig_tr : @complex.Re R (\Tr sigma) <= 1.
  {
    by rewrite Hsig_tr1.
  }
  pose tau0_raw :=
    fun e1 e2 : (S_XX'AB :\: S_X'B) :|: (S_XX'AB :&: S_X'B) = S_XX'AB =>
      castlf (e1, e2) ((\1 : 'F[H]_(S_XX'AB :\: S_X'B)) \O sigma).
  have eq_sig : (S_XX'AB :&: S_X'B) = S_X'B.
  {
    setdec.
  }
  pose sigmaX'B : 'F[H]_S_X'B := castlf (eq_sig, eq_sig) sigma.
  have sub_X'B_XX'B : S_X'B :<=: S_XX'B.
  {
    setdec.
  }
  have sub_XX'B_full : S_XX'B :<=: S_XX'AB.
  {
    setdec.
  }
  have sub_X'B_full : S_X'B :<=: S_XX'AB.
  {
    setdec.
  }
  have Hsigma_small_lift0 :
      castlf (eqX_X'B, eqX_X'B) ((\1 : 'F_X) \O sigmaX'B) =
      lift_lf sub_X'B_XX'B sigmaX'B.
  {
    have sub_X_XX'B : X :<=: S_XX'B.
    {
      setdec.
    }
    have sub_eqX : (X :|: S_X'B) :<=: S_XX'B.
    {
      setdec.
    }
    have Hcast :
        lift_lf sub_eqX
          ((\1 : 'F_X) \O sigmaX'B) =
        castlf (eqX_X'B, eqX_X'B) ((\1 : 'F_X) \O sigmaX'B).
    {
      case: _ / eqX_X'B in sub_eqX *.
      by rewrite castlf_id lift_lf_id.
    }
    have Hlift :
        lift_lf sub_eqX
          ((\1 : 'F_X) \O sigmaX'B) =
        lift_lf sub_X'B_XX'B sigmaX'B.
    {
      rewrite (eq_irrelevance sub_eqX
        (subUsetPP sub_X_XX'B sub_X'B_XX'B)).
      rewrite lift_lf_sdot lift_lf1 comp_lfun1l.
      done.
    }
    by rewrite -Hcast Hlift.
  }
  pose sigma_small : 'F[H]_S_XX'B :=
    castlf (eqX_X'B, eqX_X'B) ((\1 : 'F_X) \O sigmaX'B).
  pose tau_small : 'F[H]_S_XX'AB := lift_lf sub_XX'B_full sigma_small.
  have PsigmaX'B : sigmaX'B \is psdlf.
  {
    by rewrite /sigmaX'B castlf_psdlfE.
  }
  have Psigma_small : sigma_small \is psdlf.
  {
    rewrite /sigma_small castlf_psdlfE.
    have -> :
        ((\1 : 'F_X) \O sigmaX'B : 'F[H]_(X :|: S_X'B)) =
        (\1 : 'F_X) \⊗ sigmaX'B.
    {
      by apply: to_Fnd_inj; rewrite (sdotFT _ _ disX_X'B) to_Fnd_tenE.
    }
    rewrite psdlfE.
    apply: tenf_ge0; first exact: disX_X'B.
    - by rewrite -psdlfE psdlfE; exact: lef01.
    - by rewrite -psdlfE.
  }
  have Ptau_small : tau_small \is psdlf.
  {
    by rewrite /tau_small -lift_lf_psdE.
  }
  have /projlfP [HPxxB_herm HPxxB_id] := PxxB_proj.
  pose sigma_big : 'F[H]_S_XX'B := PxxB \o sigma_small \o PxxB.
  pose tau_big : 'F[H]_S_XX'AB := lift_lf sub_XX'B_full sigma_big.
  have Psigma_big : sigma_big \is psdlf.
  {
    rewrite /sigma_big psdlfE -{2}HPxxB_herm.
    apply: gef0_formfV.
    by rewrite -psdlfE.
  }
  have Ptau_big : tau_big \is psdlf.
  {
    by rewrite /tau_big -lift_lf_psdE.
  }
  have HPxxB_le1 : PxxB ⊑ (\1 : 'F[H]_S_XX'B).
  {
    exact: obslf_le1 (projlf_obs PxxB_proj).
  }
  have Htr_sigma_big_le : \Tr sigma_big <= \Tr sigma_small.
  {
    rewrite /sigma_big [\Tr (_ \o PxxB)]lftraceC comp_lfunA HPxxB_id.
    move/lef_psdtr: HPxxB_le1.
    move=> /(_ sigma_small Psigma_small).
    by rewrite comp_lfun1l.
  }
  have Htr_sigma_small_real : \Tr sigma_small \is Num.real.
  {
    exact: ger0_real (psdlf_trlf Psigma_small).
  }
  have Htr_sigma_big_real : \Tr sigma_big \is Num.real.
  {
    exact: ger0_real (psdlf_trlf Psigma_big).
  }
  have Htr_sigma_big_leR :
      @complex.Re R (\Tr sigma_big) <= @complex.Re R (\Tr sigma_small).
  {
    move: Htr_sigma_big_le.
    rewrite -(RRe_real Htr_sigma_big_real) -(RRe_real Htr_sigma_small_real).
    by rewrite lecR.
  }
  have HPfull_lift :
      lift_lf sub_XX'B_full PxxB = Pfull.
  {
    rewrite /Pfull /PxxB lift_lf2.
    congr (lift_lf _ cc_proj_xx).
    apply: eq_irrelevance.
  }
  have Hcc_outp (x : 'Idx[H]_X) :
      [> cc_pair x ; cc_pair x <] = Px x \O Qx x.
  {
    apply: to_Fnd_inj.
    rewrite /Px /Qx /cc_pair -tenf_outp.
    by rewrite (sdotFT _ _ disXX') to_Fnd_tenE.
  }
  have HPxxB_term (x : 'Idx[H]_X) :
      lift_lf (@finset.subsetUl _ S_XX' B) [> cc_pair x ; cc_pair x <] =
      castlf (eqX_X'B, eqX_X'B) (Px x \O QxB x).
  {
    rewrite (lift_lfEl [> cc_pair x ; cc_pair x <] disXX'_B) Hcc_outp /QxB.
    have -> :
        (((Px x \O Qx x) : 'F[H]_S_XX') \⊗ (\1 : 'F_B)) =
        ((Px x \O Qx x) \O (\1 : 'F_B)).
    {
      by apply: to_Fnd_inj; rewrite (sdotFT _ _ disXX'_B) to_Fnd_tenE.
    }
    have -> :
        ((Px x \O Qx x) \O (\1 : 'F_B)) =
        castlf (eqX_X'B, eqX_X'B) (Px x \O (Qx x \O (\1 : 'F_B))).
    {
      apply: to_Fnd_inj.
      by rewrite Fnd_cast !to_Fnd_sdotE dotFsA.
    }
    done.
  }
  have HPxxB_sum :
      PxxB =
      \sum_(x : 'Idx[H]_X)
        castlf (eqX_X'B, eqX_X'B) (Px x \O QxB x).
  {
    rewrite /PxxB /cc_proj_xx sumoutpE raddf_sum /=.
    apply: eq_bigr => x _.
    by rewrite /= scale1r HPxxB_term.
  }
  have HsumQx :
      \sum_(x : 'Idx[H]_X) Qx x = (\1 : 'F[H]_(X')).
  {
    rewrite /Qx.
    set inv_cc := fun x' : 'Idx[H]_(X') =>
      n2i (cast_ord (esym eqXX') (i2n x')).
    transitivity (\sum_(x' : 'Idx[H]_(X')) [> deltav x' ; deltav x' <]).
    - rewrite (reindex inv_cc) /=.
      2: {
        exists cc_idx => x _.
        - exact: cc_idxKV.
        - exact: cc_idxK.
      }
      apply: eq_bigr => x' _.
      by rewrite /inv_cc cc_idxKV.
    - exact: sumonb_out.
  }
  have HsumQxB :
      \sum_(x : 'Idx[H]_X) QxB x = (\1 : 'F[H]_S_X'B).
  {
    transitivity (\sum_(x : 'Idx[H]_X)
      (Qx x \⊗ (\1 : 'F_B) : 'F[H]_S_X'B)).
    - apply: eq_bigr => x _.
      by rewrite HQxB_ten.
    - by rewrite -tenf_suml HsumQx tenf11.
  }
  have Hsigma_small_ten :
      sigma_small =
      castlf (eqX_X'B, eqX_X'B) ((\1 : 'F_X) \O sigmaX'B).
  {
    by rewrite /sigma_small.
  }
  have Hsigma_small_lift :
      sigma_small = lift_lf sub_X'B_XX'B sigmaX'B.
  {
    rewrite Hsigma_small_ten.
    exact: Hsigma_small_lift0.
  }
  have Htau_small_lift :
      tau_small = lift_lf sub_X'B_full sigmaX'B.
  {
    rewrite /tau_small Hsigma_small_lift.
    have sub_eq :
        fintype.subset_trans sub_X'B_XX'B sub_XX'B_full = sub_X'B_full.
    {
      apply: eq_irrelevance.
    }
    by rewrite lift_lf2 sub_eq.
  }
  have Htr_sigma_big_eq : \Tr sigma_big = \Tr sigma.
  {
    rewrite /sigma_big [\Tr (PxxB \o sigma_small \o PxxB)]lftraceC comp_lfunA HPxxB_id.
    rewrite HPxxB_sum ?linear_sumr ?linear_sumlz /= linear_sum/=.
    under eq_bigr => x _.
      rewrite Hsigma_small_ten -castlf_complf castlf_trlfE.
      have Hten_sigma :
          ((\1 : 'F_X) \O sigmaX'B : 'F[H]_(X :|: S_X'B)) =
          (\1 : 'F_X) \⊗ sigmaX'B.
      {
        by apply: to_Fnd_inj; rewrite (sdotFT _ _ disX_X'B) to_Fnd_tenE.
      }
      have Hten_Q :
          (Px x \O QxB x : 'F[H]_(X :|: S_X'B)) =
          Px x \⊗ QxB x.
      {
        by apply: to_Fnd_inj; rewrite (sdotFT _ _ disX_X'B) to_Fnd_tenE.
      }
      rewrite Hten_sigma Hten_Q -tenf_comp // comp_lfun1r.
      rewrite (lftrace_tenf _ _ disX_X'B) outp_trlf dv_dot eqxx mul1r.
    over.
    rewrite -linear_sum/= -linear_sumlz/= HsumQxB comp_lfun1l.
    by rewrite /sigmaX'B castlf_trlfE.
  }
  have Hsigbig_tr : @complex.Re R (\Tr sigma_big) <= 1.
  {
    rewrite Htr_sigma_big_eq.
    exact: Hsig_tr.
  }
  have Htau_ten (sig : 'F[H]_S_XX'B) :
      lift_lf sub_XX'B_full sig =
      castlf (eqA_XX'B, eqA_XX'B) ((\1 : 'F_A) \O sig).
  {
    have sub_A_full : A :<=: S_XX'AB.
    {
      setdec.
    }
    have sub_eqA : (A :|: S_XX'B) :<=: S_XX'AB.
    {
      setdec.
    }
    have Hcast :
        lift_lf sub_eqA ((\1 : 'F_A) \O sig) =
        castlf (eqA_XX'B, eqA_XX'B) ((\1 : 'F_A) \O sig).
    {
      case: _ / eqA_XX'B in sub_eqA *.
      by rewrite castlf_id lift_lf_id.
    }
    have Hlift :
        lift_lf sub_eqA ((\1 : 'F_A) \O sig) = lift_lf sub_XX'B_full sig.
    {
      rewrite (eq_irrelevance sub_eqA
        (subUsetPP sub_A_full sub_XX'B_full)).
      rewrite lift_lf_sdot lift_lf1 comp_lfun1l.
      done.
    }
    by rewrite -Hlift Hcast.
  }
  have Htau_small_ten :
      tau_small =
      castlf (eqA_XX'B, eqA_XX'B) ((\1 : 'F_A) \O sigma_small).
  {
    exact: Htau_ten.
  }
  have Htau_big_ten :
      tau_big =
      castlf (eqA_XX'B, eqA_XX'B) ((\1 : 'F_A) \O sigma_big).
  {
    exact: Htau_ten.
  }
  have Htau_big_proj :
      tau_big = Pfull \o tau_small \o Pfull.
  {
    rewrite /tau_big /sigma_big lift_lf_comp lift_lf_comp.
    by rewrite HPfull_lift.
  }
  have Htr_tau_small_real : \Tr tau_small \is Num.real.
  {
    exact: ger0_real (psdlf_trlf Ptau_small).
  }
  have Htr_tau_big_real : \Tr tau_big \is Num.real.
  {
    exact: ger0_real (psdlf_trlf Ptau_big).
  }
  have Htr_tau_big_leR :
      @complex.Re R (\Tr tau_big) <= @complex.Re R (\Tr tau_small).
  {
    rewrite /tau_big /tau_small !castlf_trlfE.
    rewrite !lftrace_tenf ?disjointXD //.
    set Irem := (\1 : 'F[H]_(S_XX'AB :\: S_XX'B)).
    have PIrem : Irem \is psdlf.
    {
      exact: (projlf_psd (@projlf1 R 'H[H]_(S_XX'AB :\: S_XX'B))).
    }
    have HIrem_ge0 : 0 <= \Tr Irem := psdlf_trlf PIrem.
    have HIrem_real : \Tr Irem \is Num.real := ger0_real HIrem_ge0.
    rewrite -(RRe_real Htr_sigma_big_real) -(RRe_real Htr_sigma_small_real).
    rewrite -(RRe_real HIrem_real) -!realcM.
    have HIrem_ge0R : 0 <= @complex.Re R (\Tr Irem).
    {
      move: HIrem_ge0.
      rewrite -(RRe_real HIrem_real).
      by rewrite lecR.
    }
    by apply: ler_wpM2r.
  }
  have Htau_small_trR :
      @complex.Re R (\Tr tau_small) =
      (dim 'H[H]_A)%:R * @complex.Re R (\Tr sigma_small).
  {
    have Htmp :
        \Tr tau_small = (dim 'H[H]_A)%:R * \Tr sigma_small :> C.
    {
      by rewrite Htau_small_ten castlf_trlfE (trlf_lift_I disA_XX'B sigma_small).
    }
    move: (congr1 (fun z : C => @complex.Re R z) Htmp).
    rewrite -(RRe_real Htr_sigma_small_real) -natrC -realcM re_realid.
    done.
  }
  have Htau_big_trR :
      @complex.Re R (\Tr tau_big) =
      (dim 'H[H]_A)%:R * @complex.Re R (\Tr sigma_big).
  {
    have Htmp :
        \Tr tau_big = (dim 'H[H]_A)%:R * \Tr sigma_big :> C.
    {
      by rewrite Htau_big_ten castlf_trlfE (trlf_lift_I disA_XX'B sigma_big).
    }
    move: (congr1 (fun z : C => @complex.Re R z) Htmp).
    rewrite -(RRe_real Htr_sigma_big_real) -natrC -realcM re_realid.
    done.
  }
  have Hsigma_small_trR :
      @complex.Re R (\Tr sigma_small) =
      (dim 'H[H]_X)%:R * @complex.Re R (\Tr sigma).
  {
    have Htmp :
        \Tr sigma_small = (dim 'H[H]_X)%:R * \Tr sigma :> C.
    {
      by rewrite /sigma_small castlf_trlfE (trlf_lift_I disX_X'B sigmaX'B)
        /sigmaX'B castlf_trlfE.
    }
    have Htr_sigma_real : \Tr sigma \is Num.real := ger0_real (psdlf_trlf Psig_psd).
    move: (congr1 (fun z : C => @complex.Re R z) Htmp).
    rewrite -(RRe_real Htr_sigma_real) -natrC -realcM.
    by rewrite re_realid.
  }
  have Htau_small_trR_sigma :
      @complex.Re R (\Tr tau_small) =
      (dim 'H[H]_A)%:R * (dim 'H[H]_X)%:R * @complex.Re R (\Tr sigma).
  {
    rewrite Htau_small_trR Hsigma_small_trR.
    by rewrite mulrA.
  }
  have Htau_big_trR_sigma :
      @complex.Re R (\Tr tau_big) =
      (dim 'H[H]_A)%:R * @complex.Re R (\Tr sigma).
  {
    rewrite Htau_big_trR Htr_sigma_big_eq.
    have Htr_sigma_real : \Tr sigma \is Num.real := ger0_real (psdlf_trlf Psig_psd).
    by rewrite -(RRe_real Htr_sigma_real).
  }
  pose dXX'B : R := (dim 'H[H]_S_XX'B)%:R.
  pose omega : 'F[H]_S_XX'B := (dXX'B^-1)%:C *: (\1 : 'F[H]_S_XX'B).
  have HdXX'B_gt0 : 0 < dXX'B.
  {
    rewrite /dXX'B.
    by rewrite ltr0n dim_proper.
  }
  have HdXX'B_neq0 : dXX'B != 0.
  {
    exact: lt0r_neq0 HdXX'B_gt0.
  }
  have Pomega : omega \is psdlf.
  {
    rewrite /omega.
    apply: psdlfZ.
    - by rewrite lecR invr_ge0 ltW.
    - exact: (projlf_psd (@projlf1 R 'H[H]_S_XX'B)).
  }
  have Homega_tr1 : @complex.Re R (\Tr omega) = 1.
  {
    rewrite /omega linearZ /= /lftrace h2mx1 mxtrace1.
    by rewrite /dXX'B -natrC -realcM re_realid mulrC mulfV.
  }
  have eqST_left :
      (S_XX'AB :\: S_X'B) :|: (S_XX'AB :&: S_X'B) = S_XX'AB.
  {
    by rewrite finset.setUC finset.setID.
  }
  pose Aleft := (S_XX'AB :\: S_X'B).
  have eqAleft_sig :
      Aleft :|: (S_XX'AB :&: S_X'B) = Aleft :|: S_X'B.
  {
    rewrite /Aleft.
    setdec.
  }
  have eqAleft_full : Aleft :|: S_X'B = S_XX'AB.
  {
    rewrite /Aleft.
    setdec.
  }
  pose tau0 : 'F[H]_S_XX'AB := tau0_raw eqST_left eqST_left.
  have Htau0_small : tau0 = tau_small.
  {
    have sub_Aleft_full : Aleft :<=: S_XX'AB.
    {
      rewrite /Aleft.
      setdec.
    }
    have sub_eqAleft : Aleft :|: S_X'B :<=: S_XX'AB.
    {
      rewrite /Aleft.
      setdec.
    }
    have Hcast :
        lift_lf sub_eqAleft
          ((\1 : 'F[H]_Aleft) \O sigmaX'B) =
        castlf (eqAleft_full, eqAleft_full)
          ((\1 : 'F[H]_Aleft) \O sigmaX'B).
    {
      case: _ / eqAleft_full in sub_eqAleft *.
      by rewrite castlf_id lift_lf_id.
    }
    have Hlift :
        lift_lf sub_eqAleft
          ((\1 : 'F[H]_Aleft) \O sigmaX'B) =
        lift_lf sub_X'B_full sigmaX'B.
    {
      rewrite (eq_irrelevance sub_eqAleft
        (subUsetPP sub_Aleft_full sub_X'B_full)).
      rewrite lift_lf_sdot lift_lf1 comp_lfun1l.
      done.
    }
    have Htau0_cast :
        tau0 = castlf (eqAleft_full, eqAleft_full)
          ((\1 : 'F[H]_Aleft) \O sigmaX'B).
    {
      rewrite /tau0 /tau0_raw.
      have -> :
          eqST_left = etrans eqAleft_sig eqAleft_full.
      {
        apply: eq_irrelevance.
      }
      rewrite -castlf_comp.
      rewrite (@sdotIf_cast_r R _ _ Aleft
        (S_XX'AB :&: S_X'B) S_X'B eq_sig eqAleft_sig sigma).
      done.
    }
    rewrite Htau0_cast -Hcast Hlift.
    exact: (esym Htau_small_lift).
  }
  have Hold_witness_tau0
      (p : (S_XX'AB :\: S_X'B) :|: (S_XX'AB :&: S_X'B) = S_XX'AB) :
      castlf (p, p) ((\1 : 'F[H]_(S_XX'AB :\: S_X'B)) \O sigma) = tau0.
  {
    have Hp : p = eqST_left by apply: eq_irrelevance.
    rewrite /tau0 /tau0_raw.
    by rewrite Hp.
  }
  have fid_eq (rho tau : 'F[H]_S_XX'AB) :
      rho \is psdlf -> tau \is psdlf ->
      fidelity rho tau =
        @complex.Re R (trnorm (sqrtmx (h2mx rho) *m sqrtmx (h2mx tau))).
  {
    move=> Pr Ps.
    by rewrite /fidelity h2mx_comp !sqrtH_h2mx.
  }
  have HPfull_mx_proj : h2mx Pfull \is projmx.
  {
    by move: Pfull_proj; rewrite qualifE.
  }
  have Hfid_small_big :
      fidelity rhoXX'AB tau_small = fidelity rhoXX'AB tau_big.
  {
    pose Pm := h2mx Pfull.
    pose rhoM := h2mx rhoXX'AB.
    pose tauM := h2mx tau_small.
    have HPm_proj : Pm \is projmx.
    {
      by rewrite /Pm.
    }
    have HrhoM_psd : rhoM \is psdmx.
    {
      by move: Prho; rewrite /rhoM qualifE.
    }
    have HtauM_psd : tauM \is psdmx.
    {
      by move: Ptau_small; rewrite /tauM qualifE.
    }
    have [Hfid _] :=
      fid_iv_proj_mx
        (P := Pm) (rho := rhoM) (tau := tauM)
        HPm_proj HrhoM_psd HtauM_psd.
    rewrite (fid_eq rhoXX'AB tau_small Prho Ptau_small).
    rewrite (fid_eq rhoXX'AB tau_big Prho Ptau_big).
    move: Hfid.
    rewrite /Pm /rhoM /tauM.
    by rewrite -!h2mx_comp -Hcoh -Htau_big_proj.
  }
  have Hfid_tau0_big :
      fidelity rhoXX'AB tau0 = fidelity rhoXX'AB tau_big.
  {
    by rewrite Htau0_small Hfid_small_big.
  }
  have eq_big_cond : (S_XX'AB :&: S_XX'B) = S_XX'B.
  {
    rewrite -eqA_XX'B.
    setdec.
  }
  have eq_big_diff : (S_XX'AB :\: S_XX'B) = A.
  {
    rewrite -eqA_XX'B.
    exact: setDU_r disA_XX'B.
  }
  have eq_big_union :
      (S_XX'AB :\: S_XX'B) :|: (S_XX'AB :&: S_XX'B) = S_XX'AB.
  {
    by rewrite finset.setUC finset.setID.
  }
  have eq_big_union_sig :
      (S_XX'AB :\: S_XX'B) :|: (S_XX'AB :&: S_XX'B) =
      (S_XX'AB :\: S_XX'B) :|: S_XX'B.
  {
    setdec.
  }
  have eq_big_union_cast :
      (S_XX'AB :\: S_XX'B) :|: S_XX'B = A :|: S_XX'B.
  {
    rewrite eq_big_diff.
    done.
  }
  have Hbig_witness_castI
      (sigc : 'F[H]_(S_XX'AB :&: S_XX'B)) :
      castlf (eq_big_union, eq_big_union)
        ((\1 : 'F[H]_(S_XX'AB :\: S_XX'B)) \O sigc) =
      castlf (eqA_XX'B, eqA_XX'B)
        ((\1 : 'F_A) \O (castlf (eq_big_cond, eq_big_cond) sigc)).
  {
    have -> :
        eq_big_union = etrans eq_big_union_sig (etrans eq_big_union_cast eqA_XX'B).
    {
      apply: eq_irrelevance.
    }
    rewrite -castlf_comp.
    rewrite (@sdotIf_cast_r R _ _ (S_XX'AB :\: S_XX'B)
      (S_XX'AB :&: S_XX'B) S_XX'B
      eq_big_cond eq_big_union_sig sigc).
    rewrite -castlf_comp.
    rewrite (@sdotIf_cast_l R _ _ (S_XX'AB :\: S_XX'B)
      A S_XX'B
      eq_big_diff eq_big_union_cast
      (\1 : 'F[H]_(S_XX'AB :\: S_XX'B))
      (castlf (eq_big_cond, eq_big_cond) sigc)).
    have -> :
        castlf (eq_big_diff, eq_big_diff)
          (\1 : 'F[H]_(S_XX'AB :\: S_XX'B)) =
        (\1 : 'F_A).
    {
      exact: castlf1 eq_big_diff.
    }
    done.
  }
  have Hbig_witness_lift
      (p : (S_XX'AB :\: S_XX'B) :|: (S_XX'AB :&: S_XX'B) = S_XX'AB)
      (sig : 'F[H]_S_XX'B) :
      castlf (p, p)
        ((\1 : 'F[H]_(S_XX'AB :\: S_XX'B)) \O
         (castlf (esym eq_big_cond, esym eq_big_cond) sig)) =
      lift_lf sub_XX'B_full sig.
  {
    have Hp : p = eq_big_union by apply: eq_irrelevance.
    rewrite Hp Hbig_witness_castI.
    rewrite (castlfKV eq_big_cond eq_big_cond sig).
    exact: (esym (Htau_ten sig)).
  }
  pose dL : R := (dim 'H[H]_(S_XX'AB :\: S_X'B))%:R.
  pose dR : R := (dim 'H[H]_(S_XX'AB :\: S_XX'B))%:R.
  pose tau_left : 'F[H]_S_XX'AB := (dL^-1)%:C *: tau_small.
  pose tau_right : 'F[H]_S_XX'AB := (dR^-1)%:C *: tau_big.
  have HdL_gt0 : 0 < dL by rewrite /dL ltr0n dim_proper.
  have HdR_gt0 : 0 < dR by rewrite /dR ltr0n dim_proper.
  have HdL_neq0 : dL != 0 := lt0r_neq0 HdL_gt0.
  have HdR_neq0 : dR != 0 := lt0r_neq0 HdR_gt0.
  have HdR_eq : dR = (dim 'H[H]_A)%:R.
  {
    by rewrite /dR eq_big_diff.
  }
  have Ptau_left : tau_left \is psdlf.
  {
    rewrite /tau_left.
    apply: psdlfZ.
    - by rewrite lecR invr_ge0 ltW.
    - exact: Ptau_small.
  }
  have Ptau_right : tau_right \is psdlf.
  {
    rewrite /tau_right.
    apply: psdlfZ.
    - by rewrite lecR invr_ge0 ltW.
    - exact: Ptau_big.
  }
  have dis_left : [disjoint S_XX'AB :\: S_X'B & S_XX'AB :&: S_X'B].
  {
    setdec.
  }
  have Htau_small_trR_dL :
      @complex.Re R (\Tr tau_small) = dL * @complex.Re R (\Tr sigma).
  {
    have Htmp : \Tr tau_small = dL%:C * \Tr sigma :> C.
    {
      rewrite -Htau0_small /tau0 /tau0_raw castlf_trlfE.
      by rewrite (trlf_lift_I dis_left sigma) /dL -natrC.
    }
    have Htr_sigma_real : \Tr sigma \is Num.real :=
      ger0_real (psdlf_trlf Psig_psd).
    move: (congr1 (fun z : C => @complex.Re R z) Htmp).
    rewrite -(RRe_real Htr_sigma_real) -realcM.
    by rewrite re_realid.
  }
  have Hleft_tr1 : @complex.Re R (\Tr tau_left) = 1.
  {
    rewrite /tau_left linearZ /=.
    rewrite -(RRe_real Htr_tau_small_real) -realcM re_realid.
    rewrite Htau_small_trR_dL Hsig_tr1 /=.
    by rewrite mulr1 mulVf.
  }
  have Hright_tr1 : @complex.Re R (\Tr tau_right) = 1.
  {
    rewrite /tau_right linearZ /=.
    rewrite -(RRe_real Htr_tau_big_real) -realcM re_realid.
    rewrite Htau_big_trR_sigma Hsig_tr1 /=.
    by rewrite -HdR_eq mulr1 mulVf.
  }
  have Hleft_target
      (p : (S_XX'AB :\: S_X'B) :|: (S_XX'AB :&: S_X'B) = S_XX'AB) :
      castlf (p, p)
        ((dL^-1)%:C *:
          ((\1 : 'F[H]_(S_XX'AB :\: S_X'B)) \O sigma)) =
      tau_left.
  {
    by rewrite /tau_left linearZ /= (Hold_witness_tau0 p) Htau0_small.
  }
  have Hright_target
      (p : (S_XX'AB :\: S_XX'B) :|: (S_XX'AB :&: S_XX'B) = S_XX'AB) :
      castlf (p, p)
        ((dR^-1)%:C *:
          ((\1 : 'F[H]_(S_XX'AB :\: S_XX'B)) \O
            castlf (esym eq_big_cond, esym eq_big_cond) sigma_big)) =
      tau_right.
  {
    by rewrite /tau_right linearZ /= Hbig_witness_lift.
  }
  have Hgfid_eq_fid (tau : 'F[H]_S_XX'AB) :
      tau \is psdlf ->
      @complex.Re R (\Tr tau) = 1 ->
      gfid rhoXX'AB tau = fidelity rhoXX'AB tau.
  {
    move=> Ptau Htau_tr.
    rewrite /gfid.
    have Prho_mx : h2mx rhoXX'AB \is psdmx by move: Prho; rewrite qualifE.
    have Ptau_mx : h2mx tau \is psdmx by move: Ptau; rewrite qualifE.
    rewrite (alt_gfid_gen Prho_mx Ptau_mx).
    rewrite /fidelity !h2mx_comp !sqrtH_h2mx.
    have -> : @complex.Re R (1 - \tr (h2mx tau)) = 0.
      {
        by rewrite raddfB /= /lftrace Htau_tr subrr.
      }
    by rewrite sqrtr0 mulr0 addr0.
  }
  have Hfid_scale_right (c : R) (tau : 'F[H]_S_XX'AB) :
      0 <= c ->
      tau \is psdlf ->
      fidelity rhoXX'AB (c%:C *: tau) =
        Num.sqrt c * fidelity rhoXX'AB tau.
  {
    move=> Hc Ptau.
    rewrite /fidelity (@sqrtHZ_nn R L H S_XX'AB c tau Hc Ptau).
    rewrite -comp_lfunZr.
    change (trnormH ((Num.sqrt c)%:C *:
              (sqrtH rhoXX'AB \o sqrtH tau)) =
            Num.sqrt c * fidelity rhoXX'AB tau).
    rewrite (@trnormH_scaleZ R L H S_XX'AB (Num.sqrt c)).
    rewrite ger0_norm ?sqrtr_ge0 //.
  }
  have Hfid_left :
      fidelity rhoXX'AB tau_left =
      Num.sqrt (dL^-1) * fidelity rhoXX'AB tau_big.
  {
    rewrite /tau_left Hfid_scale_right ?invr_ge0 ?ltW //.
    by rewrite Hfid_small_big.
  }
  have Hfid_right :
      fidelity rhoXX'AB tau_right =
      Num.sqrt (dR^-1) * fidelity rhoXX'AB tau_big.
  {
    by rewrite /tau_right Hfid_scale_right ?invr_ge0 ?ltW.
  }
  have Hleft_arg :
      dL * (gfid rhoXX'AB tau_left)^+2 =
      (fidelity rhoXX'AB tau_big)^+2.
  {
    rewrite (Hgfid_eq_fid tau_left Ptau_left Hleft_tr1) Hfid_left.
    by rewrite exprMn sqr_sqrtr ?invr_ge0 ?ltW // mulrA mulfV ?mul1r.
  }
  have Hright_arg :
      dR * (gfid rhoXX'AB tau_right)^+2 =
      (fidelity rhoXX'AB tau_big)^+2.
  {
    rewrite (Hgfid_eq_fid tau_right Ptau_right Hright_tr1) Hfid_right.
    by rewrite exprMn sqr_sqrtr ?invr_ge0 ?ltW // mulrA mulfV ?mul1r.
  }
  have Harg_eq :
      dL * (gfid rhoXX'AB tau_left)^+2 =
      dR * (gfid rhoXX'AB tau_right)^+2.
  {
    by rewrite Hleft_arg Hright_arg.
  }
  have Hleft_eq_v :
      elog2 (dL * (gfid rhoXX'AB tau_left)^+2) = v%:E.
  {
    rewrite -Hv /dL.
    by rewrite Hleft_target.
  }
  apply: hmax_ub.
  - exact: hmax_has_sup Prho Hrhon Hrho_pos.
  - exists (castlf (esym eq_big_cond, esym eq_big_cond) sigma_big); split.
    + apply/den1lfP; split.
      * exact: castlf_psdlf Psigma_big.
      * by rewrite castlf_trlfE Htr_sigma_big_eq Hsig_tr1.
    + rewrite -Hleft_eq_v /dR.
      rewrite Hright_target -/dR.
      by rewrite -Harg_eq.
Qed.

End ClassEntangledMax.

End FvqkdReal.
