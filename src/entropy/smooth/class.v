(* -------------------------------------------------------------------- *)
(* class.v — Classical smooth entropy bounds                            *)
(* -------------------------------------------------------------------- *)
(* Module: entropy.smooth.class                     *)
(* Source: Tomamichel, 'A Framework for Non-Asymptotic Quantum          *)
(*   Information Theory' (PhD thesis, arXiv:1203.2142), Proposition 5.9  *)
(*   (tex pr:class/bounds-1, min-left) and Proposition 5.10             *)
(*   (tex pr:class/bounds-2, min-right).                                *)
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
From entropy.smooth Require Import prop.

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
(* Classical smooth entropy bounds (pr:class/bounds-1, bounds-2)        *)
(* ================================================================== *)

Section ClassBounds.
Variable (L : finType) (H : L -> chsType) (X A B : {set L}).
Hypothesis disXA : [disjoint X & A].
Hypothesis disXB : [disjoint X & B].
Hypothesis disAB : [disjoint A & B].
Hypothesis disXAB : [disjoint X & (A :|: B)].
Notation S_AB := (A :|: B).
Notation S_XAB := (X :|: S_AB).

(* Inline "ρ is classical on X" — parse-time sugar, not a Definition.    *)
Local Notation classical_on_X rho :=
  (forall (x x' : 'Idx[H]_X), x' != x ->
    (([> deltav x ; deltav x <] \O (\1 : 'F_S_AB)) \o rho \o
     ([> deltav x' ; deltav x' <] \O (\1 : 'F_S_AB))) = 0).

(* Entropy of classical information: first inequality of min half         *)
(* Tomamichel thesis (arXiv:1203.2142), Proposition 5.9 — tex pr:class/bounds-1, *)
(*   eqn §[class/bounds-1/min], first inequality.                          *)
(* math: For ρ ∈ S_≤(ℋ_{XAB}) classical on X and 0 ≤ ε < 1,                *)
(*   H^ε_min(A|B)_ρ ≤ H^ε_min(XA|B)_ρ.                                     *)
(* Coq ball-side premise: `0 ≤ ε < sqrt(Re Tr rhoXAB)` (the formal         *)
(* constraint under which smoothing_support_hmin / pr:smoothing/support    *)
(* apply; matches the established `smooth_iso_hmin` surface pattern).      *)
(* path: entropy:class_bounds_1_min_upper -> *)
(*   entropy:class_bounds_2_min_lower -> bb84:bb84_secret *)
Lemma class_bounds_1_min_upper (eps : R) (rhoXAB : 'F[H]_S_XAB) :
  rhoXAB \is denlf ->
  classical_on_X rhoXAB ->
  0 <= eps < Num.sqrt (@complex.Re R (\Tr rhoXAB)) ->
  (smooth_hminE B eps (ptrace_castl disXAB rhoXAB) <=
    smooth_hminE B eps rhoXAB)%E.
Proof.
  (* Tex route (pr:class/bounds-1, §[class/bounds-1/min], first inequality).
     Coq realisation: sup-le reduction + Petz-recovery inline extension.    *)
  move=> Hrho_den Hclass /andP [Heps0 Hrange].
  have Prho : rhoXAB \is psdlf := denlf_psd Hrho_den.
  have Hrho_tr : @complex.Re R (\Tr rhoXAB) <= 1.
  { have Hreal : \Tr rhoXAB \is Num.real := ger0_real (psdlf_trlf Prho).
    by move: (denlf_trlf Hrho_den); rewrite -(RRe_real Hreal) lecR. }
  (* === Setup: rhoAB := Tr_X rhoXAB, PSD + sub-normalised trace. === *)
  pose rhoAB := ptrace_castl disXAB rhoXAB.
  have PrhoAB : rhoAB \is psdlf.
    exact: ptrace_castl_psdlf.
  have Htr_eq : \Tr rhoAB = \Tr rhoXAB.
    exact: trlf_ptrace_castl.
  have Hrho_tr_AB : @complex.Re R (\Tr rhoAB) <= 1.
  { by rewrite /rhoAB Htr_eq. }
  have Hsqrt_eq : Num.sqrt (@complex.Re R (\Tr rhoAB)) =
                  Num.sqrt (@complex.Re R (\Tr rhoXAB)).
  { by rewrite /rhoAB Htr_eq. }
  (* === Strict range eps < sqrt(Tr rhoXAB) supplied by hypothesis. === *)
  rewrite {1}/smooth_hminE.
  apply: ge_ereal_sup => v [tauAB [HtauAB Hv]].
    (* === Petz-recovery extension: build tauXAB ∈ B^ε(rhoXAB) with
       hminE B tauXAB ≥ hminE B tauAB.                              *)
    have [tauXAB [Htau_ball Hhmin_mono]] :
      exists tauXAB : 'F[H]_S_XAB,
        eps_ball eps rhoXAB tauXAB /\
        (hminE B tauAB <= hminE B tauXAB)%E.
    {
      apply: (@classical_X_hmin_lift R L H X A B disAB disXAB
        rhoXAB eps tauAB) => //.
      by rewrite Heps0 Hrange. }
    subst v.
    apply: le_trans Hhmin_mono _.
    (* Close by the generic ball-ge lemma on S_XAB with T = B. *)
    apply: (@smooth_hmin_ball_ge_gen R L H S_XAB B) => //.
    by rewrite Heps0 Hrange.
Qed.

(* Right inequality of the min-entropy half of pr:class/bounds-2.         *)
(* Tomamichel thesis (arXiv:1203.2142), Proposition 5.10 — tex pr:class/bounds-2, *)
(*   specifically the right inequality of the min half.                   *)
(* math: For ρ ∈ S_≤(ℋ_{XAB}) classical on X and 0 ≤ ε < 1,                *)
(*   H^ε_min(A|BX)_ρ ≥ H^ε_min(A|B)_ρ - log d_X.                          *)
(* path: entropy:class_bounds_2_min_lower -> bb84:bb84_secret *)
Lemma class_bounds_2_min_lower (eps : R) (rhoXAB : 'F[H]_S_XAB) :
  rhoXAB \is denlf ->
  classical_on_X rhoXAB ->
  0 <= eps < Num.sqrt (@complex.Re R (\Tr rhoXAB)) ->
  (smooth_hminE B eps (ptrace_castl disXAB rhoXAB) -
      (log2 (dim 'H[H]_X)%:R)%:E <=
    smooth_hminE (B :|: X) eps rhoXAB)%E.
Proof.
  (* Tex route (pr:class/bounds-2, §[class/bounds-2/min], second inequality):
     two-step chain
       (1) smooth_hmin(A|BX)_ρ ≥ smooth_hmin(XA|B)_ρ - log d_X
       (2) smooth_hmin(XA|B)_ρ ≥ smooth_hmin(A|B)_{Tr_X ρ}
     with (2) supplied by the previously proved class_bounds_1_min_upper.  *)
  move=> Hrho_den Hclass /andP [Heps0 Hrange].
  have Prho : rhoXAB \is psdlf := denlf_psd Hrho_den.
  have Hrho_tr : @complex.Re R (\Tr rhoXAB) <= 1.
  { have Hreal : \Tr rhoXAB \is Num.real := ger0_real (psdlf_trlf Prho).
    by move: (denlf_trlf Hrho_den); rewrite -(RRe_real Hreal) lecR. }
  (* Step (2): apply class_bounds_1_min_upper. *)
  have Hstep2 :
      (smooth_hminE B eps (ptrace_castl disXAB rhoXAB) <=
      smooth_hminE B eps rhoXAB)%E.
  { apply: class_bounds_1_min_upper => //.
    by rewrite Heps0 Hrange. }
  (* === Step (1): the cascade inequality
       smooth_hmin S_BX ρ ≥ smooth_hmin [B] ρ - log d_X.                    *)
  have Hstep1 :
      (smooth_hminE B eps rhoXAB <=
       smooth_hminE (B :|: X) eps rhoXAB +
         (log2 (dim 'H[H]_X)%:R)%:E)%E.
  {
    (* (B1) Pointwise phi_min scaling: for every PSD τ,
           phi_min ([B]∪[X]) τ ≤ d_X · phi_min [B] τ.
       Witness rule: σ_B feasible for phi_min [B] τ
                     ⟹ σ' := I_X ⊗ σ_B feasible for phi_min ([B]∪[X]) τ.   *)
    have Hphi_pt :
      forall tau : 'F[H]_S_XAB,
        tau \is psdlf -> @complex.Re R (\Tr tau) <= 1 ->
        phi_min (B :|: X) tau <=
        (dim 'H[H]_X)%:R * phi_min B tau.
    {
      move=> tau Ptau PtrTauLe1.
      pose dX : R := (dim 'H[H]_X)%:R.
      have HdX_pos : 0 < dX by rewrite ltr0n dim_proper.
      have HdX_ne0 : dX != 0 by exact: lt0r_neq0.
      (* Generic set facts for phi_min: (S :\: T) :|: (S :&: T) = S,
         disjoint (S :\: T) (S :&: T).                                    *)
      have eqST_B : (S_XAB :\: B) :|: (S_XAB :&: B) = S_XAB.
        by rewrite finset.setUC finset.setID.
      have eqST_BX : (S_XAB :\: (B :|: X)) :|:
                     (S_XAB :&: (B :|: X)) = S_XAB.
        by rewrite finset.setUC finset.setID.
      have disB_int_diff :
          [disjoint (S_XAB :\: B) & (S_XAB :&: B)].
      { setdec. }
      (* Lift witness: for σ feasible for phi_min [B] τ with Tr σ = v,
         σ' := castlf ((\1 : 'F[H]_[X]) \O σ_cast) works with Tr σ' = dX*v. *)
      (* Key set equalities. *)
      have eqB_int : S_XAB :&: B = B.
      { by setdec. }
      have eqBX_int : S_XAB :&: (B :|: X) = X :|: B.
      { by setdec. }
      have Hwit : forall v : R,
        phi_min_feasible B tau v ->
        phi_min_feasible (B :|: X) tau (dX * v).
      {
        move=> v [sigma [Psigma [Hfeas Hv]]].
        (* Build σ' := castlf (\1_X \O castlf sigma) living in S_XAB :&: ([B]∪[X]). *)
        pose sigma_B : 'F[H]_B := castlf (eqB_int, eqB_int) sigma.
        have Psigma_B : sigma_B \is psdlf.
          by rewrite /sigma_B castlf_psdlfE.
        pose sigma_XB : 'F[H]_(X :|: B) :=
          (\1 : 'F[H]_X) \O sigma_B.
        have Psigma_XB : sigma_XB \is psdlf.
        { rewrite /sigma_XB psdlfE.
          have Heq : (\1 : 'F[H]_X) \O sigma_B =
                     (\1 : 'F[H]_X) \⊗ sigma_B.
          { by apply/to_Fnd_inj; rewrite (sdotFT _ _ disXB) to_Fnd_tenE. }
          rewrite Heq.
          have HI_psd : (0 : 'F[H]_X) ⊑ (\1 : 'F[H]_X).
          { by rewrite -psdlfE; rewrite qualifE h2mx1; apply: psdmx1. }
          have Hsig_psd : (0 : 'F[H]_B) ⊑ sigma_B.
          { by rewrite -psdlfE. }
          exact: tenf_ge0 disXB HI_psd Hsig_psd. }
        pose sigma' : 'F[H]_(S_XAB :&: (B :|: X)) :=
          castlf (esym eqBX_int, esym eqBX_int) sigma_XB.
        exists sigma'.
        split; first by rewrite /sigma' castlf_psdlfE.
        split.
        { (* Feasibility: reduce to Hfeas via cast algebra.                   *)
          (* Goal: castlf (eqST_BX, eqST_BX)
                   ((\1 : 'F_(S_XAB :\: ([B]:|:[X]))) \O sigma') - tau \is psdlf.
             Strategy: rewrite this expression to equal
                   castlf (eqST_B, eqST_B)
                     ((\1 : 'F_(S_XAB :\: [B])) \O sigma) - tau, then apply Hfeas. *)
          have Hkey :
            forall (e1 : (S_XAB :\: (B :|: X)) :|:
                         (S_XAB :&: (B :|: X)) = S_XAB)
                   (e2 : (S_XAB :\: B) :|:
                         (S_XAB :&: B) = S_XAB),
              castlf (e1, e1)
                ((\1 : 'F[H]_(S_XAB :\: (B :|: X))) \O sigma') =
              castlf (e2, e2)
                ((\1 : 'F[H]_(S_XAB :\: B)) \O sigma).
          { move=> e1 e2.
            apply/to_Fnd_inj.
            rewrite !Fnd_cast.
            (* LHS: unfold sigma' through castlf, then sdotFT. *)
            rewrite /sigma'.
            (* The outer \O against \1_(S_XAB :\: ([B]∪[X])) with sigma' in
               S_XAB :&: ([B]∪[X]). Disjointness is inherited from set
               difference. *)
            have disL1 :
                [disjoint (S_XAB :\: (B :|: X)) &
                          (S_XAB :&: (B :|: X))].
            { setdec. }
            rewrite (sdotFT _ _ disL1).
            (* now LHS Fnd is \1 \⊗ (castlf sigma_XB). *)
            rewrite Fnd_cast.
            (* expand sigma_XB: \1_[X] \O sigma_B *)
            rewrite /sigma_XB.
            rewrite (sdotFT _ _ disXB).
            (* sigma_B = castlf sigma *)
            rewrite /sigma_B Fnd_cast.
            (* RHS side *)
            have disR :
                [disjoint (S_XAB :\: B) & (S_XAB :&: B)].
            { setdec. }
            rewrite (sdotFT _ _ disR).
            (* Goal: \1_(S_XAB:\:([B]∪[X])) ⊗ (\1_[X] ⊗ sigma)
                    = \1_(S_XAB:\:[B]) ⊗ sigma. *)
            rewrite tenFA.
            (* \1 ⊗ \1 = \1_(union) *)
            rewrite tenF11.
            (* Need (S_XAB :\: ([B]∪[X])) :|: [X] = S_XAB :\: [B]. *)
            have HsetEq :
                (S_XAB :\: (B :|: X)) :|: X =
                S_XAB :\: B.
            {
              apply/setP=> z.
              rewrite /S_XAB /S_AB !inE.
              have XnotB : z \in X -> (z \in B) = false.
              { move=> HzX. apply/negP=> HzB.
                by move/disjointP: disXB => /(_ _ HzX); rewrite HzB. }
              have XnotA : z \in X -> (z \in A) = false.
              { move=> HzX. apply/negP=> HzA.
                by move/disjointP: disXA => /(_ _ HzX); rewrite HzA. }
              have AnotB : z \in A -> (z \in B) = false.
              { move=> HzA. apply/negP=> HzB.
                by move/disjointP: disAB => /(_ _ HzA); rewrite HzB. }
              case HXz : (z \in X); case HAz : (z \in A); case HBz : (z \in B);
                rewrite ?HXz ?HAz ?HBz //=;
                try by move: (XnotB HXz); rewrite HBz;
                try by move: (XnotA HXz); rewrite HAz;
                try by move: (AnotB HAz); rewrite HBz.
            }
            f_equal; exact: Fnd_eq1 HsetEq. }
          rewrite (Hkey _
            (eq_ind_r (eq^~ S_XAB)
               (eq_ind_r (eq^~ S_XAB) (erefl S_XAB)
                 (finset.setID S_XAB B))
               (finset.setUC (S_XAB :\: B)
                 (S_XAB :&: B)))).
          exact: Hfeas. }
        (* Trace: Re Tr sigma' = dX * v. *)
        rewrite /sigma' castlf_trlfE /sigma_XB.
        rewrite (trlf_lift_I disXB) /sigma_B castlf_trlfE.
        have Htr_sigma_real : \Tr sigma \is Num.real
          := ger0_real (psdlf_trlf Psigma).
        rewrite Hv /dX.
        have HtrE : (\Tr sigma : C) = (@complex.Re R (\Tr sigma))%:C.
          by rewrite RRe_real.
        rewrite HtrE.
        by rewrite -natrC -rmorphM /=.
      }
      (* Non-emptiness witness for phi_min [B] tau (same \1 witness as Hphi_pos). *)
      have Hne_B : exists v : R, phi_min_feasible B tau v.
      { exists (@complex.Re R (\Tr (\1 : 'F[H]_(S_XAB :&: B)))).
        rewrite /phi_min_feasible.
        exists (\1 : 'F[H]_(S_XAB :&: B)); split.
        { by rewrite qualifE h2mx1; apply: psdmx1. }
        split; last by [].
        rewrite sdotf11 castlf1.
        have Htau_le1 : tau ⊑ (\1 : 'F[H]_S_XAB).
        { have Htau_den : tau \is denlf.
          { apply/denlfP; split=> //.
            have Hreal : \Tr tau \is Num.real
              := ger0_real (psdlf_trlf Ptau).
            by rewrite -(RRe_real Hreal) lecR. }
          exact: denf_le1 (DenLf_Build Htau_den). }
        by move: Htau_le1; rewrite lefE. }
      (* Has lower bound for phi_min ([B]∪[X]) tau: 0 is a trivial lb. *)
      have Hlb_BX : has_lbound [set v : R |
          phi_min_feasible (B :|: X) tau v].
      { exists 0. move=> v [sigma [Psigma [_ ->]]].
        have := psdlf_trlf Psigma.
        have Htr_real : (\Tr sigma : C) = (@complex.Re R (\Tr sigma))%:C.
          by rewrite RRe_real // ger0_real // psdlf_trlf.
        by rewrite Htr_real lecR. }
      (* Main inf inequality: inf ([B]∪[X]-feas) ≤ dX · inf ([B]-feas). *)
      rewrite /phi_min.
      rewrite mulrC -ler_pdivrMr //.
      apply: lb_le_inf; first exact: Hne_B.
      move=> v HvB.
      rewrite ler_pdivrMr // mulrC.
      apply: ge_inf; first exact: Hlb_BX.
      exact: Hwit v HvB.
    }
    (* (B2) -log of (B1): hmin [B] τ - log d_X ≤ hmin ([B]∪[X]) τ via
       log2_le_pos on Hphi_pt.  Requires phi_min positivity for τ ∈ ball;
       for τ ∈ B^ε(ρXAB) with eps < sqrt(Tr ρXAB), Tr τ > 0 hence τ ≠ 0
       hence phi_min T τ > 0 for any T.                                    *)
    have Hhmin_pt :
      forall tau : 'F[H]_S_XAB, eps_ball eps rhoXAB tau ->
        (hminE B tau <=
         hminE (B :|: X) tau + (log2 (dim 'H[H]_X)%:R)%:E)%E.
      {
        move=> tau Htau.
        have Ptau : tau \is psdlf := eps_ball_psdlf Htau.
        have PtrTau : @complex.Re R (\Tr tau) <= 1 := eps_ball_trlf Htau.
        pose dX : R := (dim 'H[H]_X)%:R.
        have HdX_pos : 0 < dX by rewrite ltr0n dim_proper.
        have HdX_ne0 : dX != 0 by exact: lt0r_neq0.
        have HtauTr_pos : 0 < @complex.Re R (\Tr tau).
          exact: eps_ball_trlf_gt0 Htau.
      have Htau_ne0 : tau != 0.
      { apply/eqP=> Htau0.
        by move: HtauTr_pos; rewrite Htau0 raddf0 raddf0 ltxx. }
      (* phi_min positive for nonzero PSD tau. *)
      have Hphi_pos : forall (T : {set L}), 0 < phi_min T tau.
      {
        move=> T.
        (* Set fact: [disjoint (S_XAB :\: T) & (S_XAB :&: T)]. *)
        have eqST_gen : (S_XAB :\: T) :|: (S_XAB :&: T) = S_XAB.
          by rewrite finset.setUC finset.setID.
        have disSplit_gen :
            [disjoint (S_XAB :\: T) & (S_XAB :&: T)].
        { apply/disjointP=> z; rewrite !inE.
          by case: (z \in T); rewrite ?andbF ?andbT. }
        pose dT : R := (dim 'H[H]_(S_XAB :\: T))%:R.
        have HdT_pos : 0 < dT by rewrite /dT ltr0n dim_proper.
        (* For every feasible σ with value v := Re Tr σ, v ≥ Re Tr τ / dT. *)
        rewrite /phi_min.
        apply: (@lt_le_trans _ _ ((@complex.Re R (\Tr tau)) / dT)).
        - by apply: divr_gt0.
        - apply: lb_le_inf.
          + (* Non-emptiness: witness σ := \1_(S_XAB :&: T). *)
            pose sigma1 : 'F[H]_(S_XAB :&: T) := \1.
            pose v1 : R := @complex.Re R (\Tr sigma1).
            exists v1.
            rewrite /phi_min_feasible.
            exists sigma1; split.
            { by rewrite qualifE h2mx1; apply: psdmx1. }
            split; last by [].
            (* feasibility: the castlf argument evaluates to \1 via sdotf11/castlf1. *)
            rewrite sdotf11 castlf1.
            have Htau_le1 : tau ⊑ (\1 : 'F[H]_S_XAB).
            { have Htau_den : tau \is denlf.
              { apply/denlfP; split=> //.
                have : (\Tr tau : C) = (@complex.Re R (\Tr tau))%:C.
                  by rewrite RRe_real // ger0_real // psdlf_trlf.
                move=> ->. by rewrite lecR. }
              exact: denf_le1 (DenLf_Build Htau_den). }
            by move: Htau_le1; rewrite lefE.
          + move=> v [sigma [Psigma [Hfeas ->]]].
            have Htr_sigma_real :
                (\Tr sigma : C) = (@complex.Re R (\Tr sigma))%:C.
              by rewrite RRe_real // ger0_real // psdlf_trlf.
            have Htau_leR :
                @complex.Re R (\Tr tau) <=
                (dim 'H[H]_(S_XAB :\: T))%:R * @complex.Re R (\Tr sigma).
            { pose Hgap := psdlf_trlf Hfeas.
              have Htau_leC :
                  \Tr tau <=
                  (dim 'H[H]_(S_XAB :\: T))%:R * \Tr sigma.
              { move: Hgap.
                rewrite raddfB /= castlf_trlfE (trlf_lift_I disSplit_gen).
                by rewrite subr_ge0. }
              move: Htau_leC.
              have Htau_tr_real : (\Tr tau : C) = (@complex.Re R (\Tr tau))%:C.
                by rewrite RRe_real // ger0_real // psdlf_trlf.
              rewrite Htau_tr_real Htr_sigma_real.
              by rewrite -natrC -rmorphM /= lecR. }
            rewrite ler_pdivrMr //.
            by rewrite mulrC.
      }
      have HpB_pos : 0 < phi_min B tau := Hphi_pos _.
      have HpBX_pos : 0 < phi_min (B :|: X) tau := Hphi_pos _.
      have HdXpB_pos : 0 < dX * phi_min B tau by apply: mulr_gt0.
      have Hscale : phi_min (B :|: X) tau <=
                    dX * phi_min B tau := Hphi_pt tau Ptau PtrTau.
      have Hlog_ineq : log2 (phi_min (B :|: X) tau) <=
                       log2 (dX * phi_min B tau).
      { exact: log2_le_pos HpBX_pos Hscale. }
      have Hlog_prod : log2 (dX * phi_min B tau) =
                       log2 dX + log2 (phi_min B tau).
      { by rewrite /log2 lnM //= mulrDl. }
      rewrite Hlog_prod in Hlog_ineq.
      have Hneg := Hlog_ineq.
      rewrite -lerN2 in Hneg.
      rewrite opprD in Hneg.
      rewrite addrC in Hneg.
      have Hshift :
          hmin B tau <= hmin (B :|: X) tau + log2 (dim 'H[H]_X)%:R.
      { by rewrite -lerBlDr. }
      rewrite (@hminE_EFin R L H S_XAB B tau HpB_pos).
      rewrite (@hminE_EFin R L H S_XAB (B :|: X) tau HpBX_pos).
      by rewrite -EFinD lee_fin.
    }
    (* (B3) Sup-shift: from the pointwise bound on τ ∈ ball(rhoXAB), conclude
        smooth_hmin [B] ρ - log d_X ≤ smooth_hmin ([B]∪[X]) ρ.               *)
    rewrite {1}/smooth_hminE.
    apply: ge_ereal_sup => v [tauS [HtauS ->]].
      have Hptw := Hhmin_pt tauS HtauS.
      apply: le_trans Hptw _.
      apply: leeD; last exact: lexx.
      apply: (@smooth_hmin_ball_ge_gen R L H S_XAB (B :|: X)) => //.
      by rewrite Heps0 Hrange.
  }
  (* === Compose (1) and (2). === *)
  have Hplus :
      (smooth_hminE B eps (ptrace_castl disXAB rhoXAB) <=
       smooth_hminE (B :|: X) eps rhoXAB +
         (log2 (dim 'H[H]_X)%:R)%:E)%E
    := le_trans Hstep2 Hstep1.
  have Hlog_fin :
      ((log2 (dim 'H[H]_X)%:R)%:E : extended R) \is a fin_num.
  { by rewrite fin_numE. }
  move: Hplus.
  by rewrite leeBlDr.
Qed.

End ClassBounds.

End FvqkdReal.
