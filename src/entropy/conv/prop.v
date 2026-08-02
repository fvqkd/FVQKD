(* -------------------------------------------------------------------- *)
(* prop.v — Properties i–viii of Phi functional                          *)
(* -------------------------------------------------------------------- *)
(* Module: entropy.conv.prop                        *)
(* Source: Tomamichel, 'A Framework for Non-Asymptotic Quantum          *)
(*   Information Theory' (PhD thesis, arXiv:1203.2142), Sec. 4.5,        *)
(*   Table 4.1 (Properties of Φ), properties i–viii — tex tb:Phi.       *)
(*   phi_min_iii_subadd, phi_min_iv_convex, phi_min_v_iso_inv,          *)
(*   phi_min_vi_data_proc, phi_min_vii_data_proc_ext, phi_min_viii_tens) *)
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
  cpo mxpred extnum ctopology svd mxnorm hspace hspace_extra.
From quantum.dirac Require Import setdec hstensor.

Import Order.TTheory GRing.Theory Num.Theory Num.Def MxLownerOrder.
Import VectorInternalTheory.

(* --- FVQKD imports --- *)
From utils Require Import exports.
From entropy Require Import def prop util.

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
(* Table 4.1 (Properties of Φ), properties i–viii — tex tb:Phi.         *)
(* ================================================================== *)

(* Property i, set-level form (Scaling, Table 4.1 item i):             *)
(* For lambda >= 0, Phi_T(lambda rho_S) = lambda Phi_T(rho_S).          *)
Section PhiMinScaling.
Variable (L : finType) (H : L -> chsType) (S T : {set L}).

(* path: entropy:phi_min_i_scale -> entropy:entropy_data_proc -> *)
(*   bb84:bb84_secret *)
Lemma phi_min_i_scale (rhoS : 'F[H]_S) (lambda : R) :
  rhoS \is psdlf ->
  0 <= lambda ->
  phi_min T (lambda%:C *: rhoS) =
    lambda * phi_min T rhoS.
Proof.
  move=> Prho Hlambda_ge0.
  case: (eqVneq lambda 0) => [->|Hlambda_nz]; last first.
  - have Hlambda_pos : 0 < lambda
      by rewrite lt_neqAle Hlambda_ge0 andbT eq_sym.
    pose ilambda : R := GRing.inv lambda.
    have Hlambda_inv_ge0 : (0 : R) <= ilambda.
      by rewrite /ilambda invr_ge0.
    have Plrho : (lambda%:C *: rhoS) \is psdlf.
    {
      apply: psdlfZ.
      - by rewrite lecR.
      - exact: Prho.
    }
    have Hscale_up : forall v,
        phi_min_feasible T rhoS v ->
        phi_min_feasible T (lambda%:C *: rhoS) (lambda * v).
    {
      move=> v [sigma [Psigma [Hsigma ->]]].
      exists (lambda%:C *: sigma).
      split.
      - apply: psdlfZ.
        + by rewrite lecR.
        + exact: Psigma.
      - split.
        + set Dsigma := (X in (X - rhoS) \is psdlf) in Hsigma.
          set Dsigma_l := (X in (X - lambda%:C *: rhoS) \is psdlf).
          have Hcast : Dsigma_l = lambda%:C *: Dsigma.
          {
            by rewrite /Dsigma_l /Dsigma !linearZ /=.
          }
          have Hord : rhoS <= Dsigma.
          {
            by move: Hsigma; rewrite /Dsigma -lefE.
          }
          have Hord' : lambda%:C *: rhoS <= lambda%:C *: Dsigma.
          {
            apply: lef_pscale2lP Hord.
            by rewrite ltc0R.
          }
          move: Hord'.
          by rewrite -Hcast /Dsigma_l lefE.
        + have Htr_sigma_real : \Tr sigma \is Num.real
            := ger0_real (psdlf_trlf Psigma).
          rewrite linearZ /= -(RRe_real Htr_sigma_real) -realcM.
          by rewrite re_realid.
    }
    have Hscale_down : forall v,
        phi_min_feasible T (lambda%:C *: rhoS) v ->
        phi_min_feasible T rhoS (ilambda * v).
    {
      move=> v [sigma [Psigma [Hsigma ->]]].
      exists (ilambda%:C *: sigma).
      split.
      - apply: psdlfZ.
        + by rewrite lecR /ilambda invr_ge0.
        + exact: Psigma.
      - split.
        + set Dsigma := (X in (X - lambda%:C *: rhoS) \is psdlf) in Hsigma.
          set Dsigma_i := (X in (X - rhoS) \is psdlf).
          have Hcast : Dsigma_i = ilambda%:C *: Dsigma.
          {
            by rewrite /Dsigma_i /Dsigma !linearZ /=.
          }
          have Hord : lambda%:C *: rhoS <= Dsigma.
          {
            by move: Hsigma; rewrite /Dsigma -lefE.
          }
          have Hord' :
              ilambda%:C *: (lambda%:C *: rhoS) <=
              ilambda%:C *: Dsigma.
          {
            apply: lef_pscale2lP Hord.
            by rewrite ltc0R /ilambda invr_gt0.
          }
          move: Hord'.
          have -> : ilambda%:C *: (lambda%:C *: rhoS) = rhoS.
          {
            by rewrite scalerA -rmorphM /= /ilambda mulVf ?rmorph1 ?scale1r.
          }
          by rewrite -Hcast /Dsigma_i lefE.
        + have Htr_sigma_real : \Tr sigma \is Num.real
            := ger0_real (psdlf_trlf Psigma).
          rewrite linearZ /= -(RRe_real Htr_sigma_real) -realcM.
          by rewrite re_realid.
    }
    apply/eqP; rewrite eq_le; apply/andP; split.
    + have Hdiv_le :
          ilambda * phi_min T (lambda%:C *: rhoS) <=
          phi_min T rhoS.
      {
        rewrite /phi_min.
        apply: lb_le_inf.
        - by have [Hne _] := @phi_min_feasible_has_inf R L H S T rhoS Prho.
        - move=> v Hv.
          have Hscaled_le :
              phi_min T (lambda%:C *: rhoS) <= lambda * v.
          {
            apply: ge_inf.
            - by have [_ Hlb] :=
                @phi_min_feasible_has_inf R L H S T _ Plrho.
            - exact: Hscale_up Hv.
          }
          have Hscaled_div :
              phi_min T (lambda%:C *: rhoS) / lambda <= v.
          {
            rewrite ler_pdivrMr // mulrC.
            exact: Hscaled_le.
          }
          by rewrite mulrC in Hscaled_div.
      }
      have Hup :
          lambda * (ilambda * phi_min T (lambda%:C *: rhoS)) <=
          lambda * phi_min T rhoS
        := ler_wpM2l Hlambda_ge0 Hdiv_le.
      have Hlhs :
          lambda * (ilambda * phi_min T (lambda%:C *: rhoS)) =
          phi_min T (lambda%:C *: rhoS).
      {
        by rewrite mulrA /ilambda mulfV ?mul1r // lt0r_neq0.
      }
      by move: Hup; rewrite Hlhs.
    + rewrite /phi_min.
      apply: lb_le_inf.
      * by have [Hne _] := @phi_min_feasible_has_inf R L H S T _ Plrho.
      * move=> v Hv.
        have Hrho_le : phi_min T rhoS <= ilambda * v.
        {
          apply: ge_inf.
          - by have [_ Hlb] := @phi_min_feasible_has_inf R L H S T rhoS Prho.
          - exact: Hscale_down Hv.
        }
        have Hmul : lambda * phi_min T rhoS <= lambda * (ilambda * v)
          := ler_wpM2l Hlambda_ge0 Hrho_le.
        move: Hmul.
        by rewrite mulrA /ilambda mulfV ?mul1r // lt0r_neq0.
  - have P0 : (0 : 'F[H]_S) \is psdlf by rewrite psdlfE lexx.
    rewrite scale0r mul0r.
    apply/eqP; rewrite eq_le; apply/andP; split.
    + rewrite /phi_min.
      apply: ge_inf.
      * by have [_ Hlb] :=
          @phi_min_feasible_has_inf R L H S T (0 : 'F[H]_S) P0.
      * exists (0 : 'F[H]_(S :&: T)).
        split.
        - by rewrite psdlfE lexx.
        - split.
          + by rewrite sdotf0 linear0 subrr.
          + by rewrite linear0.
    + rewrite /phi_min.
      apply: lb_le_inf.
      * by have [Hne _] :=
          @phi_min_feasible_has_inf R L H S T (0 : 'F[H]_S) P0.
      * move=> v [sigma [Psigma [_ ->]]].
        by have := psdlf_trlf Psigma; rewrite lecE /= => /andP[_].
Qed.

End PhiMinScaling.

(* Property ii, set-level form (Monotonicity, Table 4.1 item ii):       *)
(* If ρ_S ≤ τ_S then Φ_T(ρ_S) ≤ Φ_T(τ_S).                               *)
Section PhiMinMonotonicity.
Variable (L : finType) (H : L -> chsType) (S T : {set L}).

(* path: entropy:phi_min_ii_mono -> entropy:entropy_data_proc -> *)
(*   bb84:bb84_secret *)
Lemma phi_min_ii_mono (rhoS tauS : 'F[H]_S) :
  rhoS \is psdlf ->
  tauS \is psdlf ->
  rhoS <= tauS ->
  phi_min T rhoS <= phi_min T tauS.
Proof.
  move=> Prho Ptau Hrt.
  have psdlf_le_tr_id_local :
      forall (S0 : {set L}) (f : 'F[H]_S0),
        f \is psdlf ->
        f <= (@complex.Re R (\Tr f))%:C *: (\1 : 'F[H]_S0).
  {
    move=> S0 f Pf.
    have Htr_real : \Tr f \is Num.real := ger0_real (psdlf_trlf Pf).
    rewrite lef_h2mx.
    have -> :
        h2mx ((@complex.Re R (\Tr f))%:C *: (\1 : 'F[H]_S0)) =
        (\tr (h2mx f))%:M.
    {
      rewrite h2mxZ_lf h2mx1 /lftrace (RRe_real Htr_real) scalemx1.
      done.
    }
    apply: lemx_psd_ub.
    by rewrite qualifE.
  }
  have Hhas_inf : forall (x : 'F[H]_S),
      x \is psdlf -> has_inf [set v : R | phi_min_feasible T x v].
  {
    move=> x Px; split.
    - pose c := @complex.Re R (\Tr x).
      pose sigma0 : 'F[H]_(S :&: T) := c%:C *: (\1 : 'F[H]_(S :&: T)).
      have Htr_x_real : (\Tr x : C) = c%:C.
      {
        by rewrite /c RRe_real // ger0_real // psdlf_trlf.
      }
      have Psigma0 : sigma0 \is psdlf.
      {
        rewrite /sigma0.
        apply: psdlfZ.
        - by move: (psdlf_trlf Px); rewrite Htr_x_real lecR.
        - by rewrite qualifE h2mx1; apply: psdmx1.
      }
      exists (@complex.Re R (\Tr sigma0)).
      exists sigma0; split; first exact: Psigma0.
      split; last reflexivity.
      move: (psdlf_le_tr_id_local S x Px).
      rewrite /sigma0 sdotfZr sdotf11 linearZ /= castlf1.
      done.
    - exists 0 => v [sigma [Psigma [_ ->]]].
      by have := psdlf_trlf Psigma; rewrite lecE /= => /andP[_].
  }
  rewrite /phi_min.
  apply: lb_le_inf.
  - by have [Hne _] := Hhas_inf tauS Ptau.
  - move=> v [sigma [Psigma [Htau ->]]].
    apply: ge_inf.
    + by have [_ Hlb] := Hhas_inf rhoS Prho.
    exists sigma.
    split.
    + exact: Psigma.
    + split; last reflexivity.
      move: Htau; rewrite -lefE => Htau_le.
      have Hrho_le := le_trans Hrt Htau_le.
      by move: Hrho_le; rewrite lefE.
Qed.

Fact hminE_mono_lowner (rhoS tauS : 'F[H]_S) :
  rhoS \is psdlf ->
  tauS \is psdlf ->
  @complex.Re R (\Tr rhoS) <= 1 ->
  0 < @complex.Re R (\Tr rhoS) ->
  rhoS <= tauS ->
  (hminE T tauS <= hminE T rhoS)%E.
Proof.
  move=> Prho Ptau Hrho_tr Hrho_pos Hrt.
  have Hphi_le := phi_min_ii_mono Prho Ptau Hrt.
  have Hphi_pos := phi_min_pos_trace T Prho Hrho_tr Hrho_pos.
  by rewrite /hminE leeN2; exact: elog2_le _ _ Hphi_pos Hphi_le.
Qed.

End PhiMinMonotonicity.

(* Property iii, set-level form (Sub-additivity, Table 4.1 item iii):   *)
(* Phi_T(rho_S + tau_S) <= Phi_T(rho_S) + Phi_T(tau_S).                 *)
Section PhiMinSubadditivity.
Variable (L : finType) (H : L -> chsType) (S T : {set L}).

(* path: entropy:phi_min_iii_subadd -> entropy:entropy_data_proc -> *)
(*   bb84:bb84_secret *)
Lemma phi_min_iii_subadd (rhoS tauS : 'F[H]_S) :
  rhoS \is psdlf ->
  tauS \is psdlf ->
  phi_min T (rhoS + tauS) <= phi_min T rhoS + phi_min T tauS.
Proof.
  move=> Prho Ptau.
  pose Erho : set R := fun v : R => phi_min_feasible T rhoS v.
  pose Etau : set R := fun v : R => phi_min_feasible T tauS v.
  pose Esum : set R := fun v : R => exists x y, Erho x /\ Etau y /\ v = x + y.
  have Psum : (rhoS + tauS) \is psdlf by exact: psdlfD.
  have Hsubset :
      forall v : R, Esum v -> phi_min_feasible T (rhoS + tauS) v.
  {
    move=> v [x [y [Hx [Hy ->]]]].
    move: Hx => [sigma [Psigma [Hsigma ->]]].
    move: Hy => [tau [Ptau' [Htau ->]]].
    exists (sigma + tau).
    split.
    - exact: psdlfD Psigma Ptau'.
    - split.
      + set Dsigma := (X in (X - rhoS) \is psdlf) in Hsigma.
        set Dtau := (X in (X - tauS) \is psdlf) in Htau.
        set Dsum := (X in (X - (rhoS + tauS)) \is psdlf).
        have -> :
            Dsum - (rhoS + tauS) =
            (Dsigma - rhoS) + (Dtau - tauS).
        {
          have Hadd :
              forall a b c d : 'F[H]_S,
                a + b - (c + d) = (a - c) + (b - d).
          {
            move=> a b c d.
            rewrite opprD -!addrA.
            rewrite [b + (- c + - d)]addrCA.
            by rewrite !addrA.
          }
          have Hadd' :
              forall a b c d : 'F[H]_S,
                a + b + (- c - d) = (a - c) + (b - d).
          {
            move=> a b c d.
            rewrite -!addrA.
            rewrite [b + (- c - d)]addrCA.
            by rewrite !addrA.
          }
          rewrite /Dsum /Dsigma /Dtau !linearD /=.
          exact: (Hadd' _ _ _ _).
        }
        exact: psdlfD Hsigma Htau.
      + by rewrite !linearD /=.
  }
  have HEsum_nonempty : nonempty Esum.
  {
    have [Hx _] := @phi_min_feasible_has_inf R L H S T rhoS Prho.
    have [Hy _] := @phi_min_feasible_has_inf R L H S T tauS Ptau.
    case: Hx => x Hx.
    case: Hy => y Hy.
    exact: (ex_intro _ (x + y) (ex_intro _ x (ex_intro _ y
      (conj Hx (conj Hy erefl))))).
  }
  have Hsum_lb : lbound Esum (inf Erho + inf Etau).
  {
    move=> v [x [y [Hx [Hy ->]]]].
    apply: lerD.
    - have [_ Hlb] := @phi_min_feasible_has_inf R L H S T rhoS Prho.
      have Hlb' : lbound Erho (inf Erho).
      {
        by rewrite /Erho; exact: ge_inf Hlb.
      }
      exact: Hlb' _ Hx.
    - have [_ Hlb] := @phi_min_feasible_has_inf R L H S T tauS Ptau.
      have Hlb' : lbound Etau (inf Etau).
      {
        by rewrite /Etau; exact: ge_inf Hlb.
      }
      exact: Hlb' _ Hy.
  }
  have HEsum_has_inf : has_inf Esum.
  {
    split; first exact: HEsum_nonempty.
    exists (inf Erho + inf Etau).
    exact: Hsum_lb.
  }
  have Hsum_inf : inf Esum = inf Erho + inf Etau.
  {
    apply/eqP; rewrite eq_le; apply/andP; split.
    - rewrite leNgt; apply/negP => Hgt.
      pose eps := inf Esum - (inf Erho + inf Etau).
      have Heps_pos : 0 < eps by rewrite /eps subr_gt0.
      have He2pos : 0 < eps / 2%:R.
      {
        by rewrite divr_gt0 // ltr0n.
      }
      have [x Hx Hxlt] :=
        inf_adherent He2pos (@phi_min_feasible_has_inf R L H S T rhoS Prho).
      have [y Hy Hylt] :=
        inf_adherent He2pos (@phi_min_feasible_has_inf R L H S T tauS Ptau).
      have Hz : Esum (x + y).
      {
        exact: (ex_intro _ x (ex_intro _ y (conj Hx (conj Hy erefl)))).
      }
      have Hinf_lb : inf Esum <= x + y.
      {
        have Hlb' : lbound Esum (inf Esum).
        {
          exact: ge_inf HEsum_has_inf.2.
        }
        exact: Hlb' _ Hz.
      }
      have Heps_split : eps / 2%:R + eps / 2%:R = eps.
      {
        by rewrite -splitr.
      }
      have Hxy_lt : x + y < inf Esum.
      {
        have Hlt := ltrD Hxlt Hylt.
        move: Hlt.
        have Hadd2 : forall a b e : R, (a + e) + (b + e) = a + b + (e + e).
        {
          by move=> a b e; rewrite addrACA.
        }
        have -> :
            (inf Erho + eps / 2%:R) + (inf Etau + eps / 2%:R) =
            inf Erho + inf Etau + eps.
        {
          rewrite (Hadd2 (inf Erho) (inf Etau) (eps / 2%:R)).
          by rewrite Heps_split.
        }
        rewrite /eps.
        have -> :
            inf Erho + inf Etau + (inf Esum - (inf Erho + inf Etau)) =
            inf Esum.
        {
          by rewrite addrC subrK.
        }
        done.
      }
      have := lt_le_trans Hxy_lt Hinf_lb.
      by rewrite ltxx.
    - exact: (lb_le_inf HEsum_nonempty Hsum_lb).
  }
  rewrite /phi_min.
  apply: (le_trans _ _).
  - apply: lb_le_inf.
    + exact: HEsum_nonempty.
    + move=> v Hv.
      have Hlb' :
          lbound [set w : R | phi_min_feasible T (rhoS + tauS) w]
            (phi_min T (rhoS + tauS)).
      {
        have [_ Hlb] := @phi_min_feasible_has_inf R L H S T (rhoS + tauS) Psum.
        exact: ge_inf Hlb.
      }
      exact: (Hlb' _ (Hsubset _ Hv)).
  - by rewrite Hsum_inf /Erho /Etau.
Qed.

End PhiMinSubadditivity.

(* Property iv, set-level form (Convexity, Table 4.1 item iv):          *)
(* Phi_T(lambda rho + (1-lambda) tau) <=                                *)
(*   lambda Phi_T(rho) + (1-lambda) Phi_T(tau).                         *)
Section PhiMinConvexity.
Variable (L : finType) (H : L -> chsType) (S T : {set L}).

(* path: entropy:phi_min_iv_convex -> entropy:entropy_data_proc -> *)
(*   bb84:bb84_secret *)
Lemma phi_min_iv_convex (rhoS tauS : 'F[H]_S) (lambda : R) :
  rhoS \is psdlf ->
  tauS \is psdlf ->
  0 <= lambda <= 1 ->
  phi_min T (lambda%:C *: rhoS + (1 - lambda)%:C *: tauS) <=
    lambda * phi_min T rhoS + (1 - lambda) * phi_min T tauS.
Proof.
  move=> Prho Ptau /andP[Hlambda_ge0 Hlambda_le1].
  have H1ml_ge0 : 0 <= 1 - lambda by rewrite subr_ge0.
  have Plrho : (lambda%:C *: rhoS) \is psdlf.
  {
    apply: psdlfZ.
    - by rewrite lecR.
    - exact: Prho.
  }
  have Pmtau : ((1 - lambda)%:C *: tauS) \is psdlf.
  {
    apply: psdlfZ.
    - by rewrite lecR.
    - exact: Ptau.
  }
  have Hsub := @phi_min_iii_subadd L H S T
    (lambda%:C *: rhoS) ((1 - lambda)%:C *: tauS) Plrho Pmtau.
  apply: (le_trans Hsub).
  by rewrite !phi_min_i_scale.
Qed.

End PhiMinConvexity.

(* Property v, set-level form (Local isometry invariance, Table 4.1 item v). *)
Section PhiMinIsometryInvariance.
Variable (L : finType) (H : L -> chsType) (A A' B B' : {set L}).
Hypothesis disAB : [disjoint A & B].
Hypothesis disA'B' : [disjoint A' & B'].
Hypothesis disA'B : [disjoint A' & B].
Hypothesis disAB' : [disjoint A & B'].

(* path: entropy:phi_min_v_iso_inv -> entropy:entropy_data_proc -> *)
(*   bb84:bb84_secret *)
Lemma phi_min_v_iso_inv (rhoAB : 'F[H]_(A :|: B))
    (U : 'FI[H]_(A, A')) (V : 'FI[H]_(B, B')) :
  rhoAB \is psdlf ->
  phi_min B' ((U \⊗ V) \o rhoAB \o (U \⊗ V)^A) =
    phi_min B rhoAB.
Proof.
  move=> Prho.
  pose W := U \⊗ V.
  pose rho' : 'F[H]_(A' :|: B') := W \o rhoAB \o W^A.
  have W_iso : W \is isolf.
  {
    apply/isolfP.
    by rewrite tenf_adj -tenf_comp ?disAB // isofE isofE tenf11.
  }
  pose Wi := IsoLf_Build W_iso.
  have HWi : W = Wi by exact: IsoLf_BuildE W_iso.
  have HWi_cptp : formso Wi \is cptp by apply: is_cptp.
  have Hrho'E : rho' = formso Wi rhoAB by rewrite /rho' HWi formsoE.
  have Prho' : rho' \is psdlf.
  {
    rewrite Hrho'E (CPMap_BuildE (cptp_cpmap HWi_cptp)).
    exact: cp_psdP Prho.
  }
  have -> : ((U \⊗ V) \o rhoAB \o (U \⊗ V)^A) = rho' by [].
  pose S_AB := A :|: B.
  pose S_A'B' := A' :|: B'.
  have Wa_b1 : W^A \is bound1lf.
    by rewrite bound1lf_adj; exact: isolf_bound1 W_iso.
  pose Wa := Bound1Lf_Build Wa_b1.
  have HWa : W^A = Wa by exact: Bound1Lf_BuildE Wa_b1.
  have eqA : S_AB :\: B = A by rewrite /S_AB setDU_r.
  have eqB : S_AB :&: B = B by rewrite /S_AB; setdec.
  have eqA' : S_A'B' :\: B' = A' by rewrite /S_A'B' setDU_r.
  have eqB' : S_A'B' :&: B' = B' by rewrite /S_A'B'; setdec.
  have Hphi_cf_src :
      forall (tau : 'F[H]_S_AB) (v : R),
        phi_min_feasible B tau v <->
        exists sigma : 'F[H]_B,
          sigma \is psdlf /\
          (((\1 : 'F[H]_A) \O sigma) - tau) \is psdlf /\
          v = @complex.Re R (\Tr sigma).
  {
    have Hcast_src_lift :
        forall (eqST1 : (S_AB :\: B) :|: (S_AB :&: B) = S_AB)
               (eqB0 : S_AB :&: B = B)
               (sigma0 : 'F[H]_(S_AB :&: B)),
          castlf (eqST1, eqST1)
            ((\1 : 'F[H]_(S_AB :\: B)) \O sigma0) =
          ((\1 : 'F[H]_A) \O castlf (eqB0, eqB0) sigma0 : 'F[H]_S_AB).
    {
      move=> eqST1 eqB0 sigma0.
      have eqU1 :
          (S_AB :\: B) :|: (S_AB :&: B) = A :|: (S_AB :&: B).
        by rewrite eqA.
      have eqU2 : A :|: (S_AB :&: B) = S_AB.
        by rewrite eqB /S_AB.
      transitivity
        (castlf (etrans eqU1 eqU2, etrans eqU1 eqU2)
          ((\1 : 'F[H]_(S_AB :\: B)) \O sigma0)).
      {
        by rewrite (eq_irrelevance (etrans eqU1 eqU2) eqST1).
      }
      rewrite -(castlf_comp eqU1 eqU1 eqU2 eqU2).
      rewrite (sdotIf_cast_l eqA eqU1) castlf1.
      rewrite (sdotIf_cast_r eqB0 eqU2).
      by [].
    }
    have Hcast_src_lift_inv :
        forall (eqST1 : (S_AB :\: B) :|: (S_AB :&: B) = S_AB)
               (sigma : 'F[H]_B),
          castlf (eqST1, eqST1)
            ((\1 : 'F[H]_(S_AB :\: B)) \O
              castlf (esym eqB, esym eqB) sigma) =
          ((\1 : 'F[H]_A) \O sigma : 'F[H]_S_AB).
    {
      move=> eqST1 sigma.
      rewrite (Hcast_src_lift eqST1 eqB).
      by rewrite castlfKV.
    }
    move=> tau v; rewrite /phi_min_feasible; split.
    - move=> [sigma0 [Psigma0 [Hdom0 Hv]]].
      exists (castlf (eqB, eqB) sigma0); split.
      + by rewrite castlf_psdlfE.
      + split.
        * have Hdom1 :
              (((\1 : 'F[H]_A) \O castlf (eqB, eqB) sigma0) - tau)
                \is psdlf.
          {
            have Haux :
                forall eqST1 : (S_AB :\: B) :|: (S_AB :&: B) = S_AB,
                  (castlf (eqST1, eqST1)
                    ((\1 : 'F[H]_(S_AB :\: B)) \O sigma0) - tau)
                    \is psdlf ->
                  (((\1 : 'F[H]_A) \O castlf (eqB, eqB) sigma0) - tau)
                    \is psdlf.
            {
              move=> eqST1 Hpsd.
              have Hcore :
                  ((\1 : 'F[H]_A) \O castlf (eqB, eqB) sigma0) =
                  castlf (eqST1, eqST1)
                    ((\1 : 'F[H]_(S_AB :\: B)) \O sigma0).
                exact: (esym (Hcast_src_lift eqST1 eqB sigma0)).
              by rewrite Hcore.
            }
            exact: (Haux _ Hdom0).
          }
          exact: Hdom1.
        * by rewrite castlf_trlfE Hv.
    - move=> [sigma [Psigma [Hdom Hv]]].
      exists (castlf (esym eqB, esym eqB) sigma); split.
      + by rewrite castlf_psdlfE.
      + split.
        * by rewrite (Hcast_src_lift_inv _ sigma).
        * by rewrite castlf_trlfE Hv.
  }
  have Hphi_cf_tgt :
      forall (tau : 'F[H]_S_A'B') (v : R),
        phi_min_feasible B' tau v <->
        exists sigma : 'F[H]_B',
          sigma \is psdlf /\
          (((\1 : 'F[H]_A') \O sigma) - tau) \is psdlf /\
          v = @complex.Re R (\Tr sigma).
  {
    have Hcast_tgt_lift :
        forall (eqST1 : (S_A'B' :\: B') :|: (S_A'B' :&: B') = S_A'B')
               (eqB0 : S_A'B' :&: B' = B')
               (sigma0 : 'F[H]_(S_A'B' :&: B')),
          castlf (eqST1, eqST1)
            ((\1 : 'F[H]_(S_A'B' :\: B')) \O sigma0) =
          ((\1 : 'F[H]_A') \O castlf (eqB0, eqB0) sigma0 : 'F[H]_S_A'B').
    {
      move=> eqST1 eqB0 sigma0.
      have eqU1 :
          (S_A'B' :\: B') :|: (S_A'B' :&: B') =
          A' :|: (S_A'B' :&: B').
        by rewrite eqA'.
      have eqU2 : A' :|: (S_A'B' :&: B') = S_A'B'.
        by rewrite eqB' /S_A'B'.
      transitivity
        (castlf (etrans eqU1 eqU2, etrans eqU1 eqU2)
          ((\1 : 'F[H]_(S_A'B' :\: B')) \O sigma0)).
      {
        by rewrite (eq_irrelevance (etrans eqU1 eqU2) eqST1).
      }
      rewrite -(castlf_comp eqU1 eqU1 eqU2 eqU2).
      rewrite (sdotIf_cast_l eqA' eqU1) castlf1.
      rewrite (sdotIf_cast_r eqB0 eqU2).
      by [].
    }
    have Hcast_tgt_lift_inv :
        forall (eqST1 : (S_A'B' :\: B') :|: (S_A'B' :&: B') = S_A'B')
               (sigma : 'F[H]_B'),
          castlf (eqST1, eqST1)
            ((\1 : 'F[H]_(S_A'B' :\: B')) \O
              castlf (esym eqB', esym eqB') sigma) =
          ((\1 : 'F[H]_A') \O sigma : 'F[H]_S_A'B').
    {
      move=> eqST1 sigma.
      rewrite (Hcast_tgt_lift eqST1 eqB').
      by rewrite castlfKV.
    }
    move=> tau v; rewrite /phi_min_feasible; split.
    - move=> [sigma0 [Psigma0 [Hdom0 Hv]]].
      exists (castlf (eqB', eqB') sigma0); split.
      + by rewrite castlf_psdlfE.
      + split.
        * have Hdom1 :
              (((\1 : 'F[H]_A') \O castlf (eqB', eqB') sigma0) - tau)
                \is psdlf.
          {
            have Haux :
                forall eqST1 :
                    (S_A'B' :\: B') :|: (S_A'B' :&: B') = S_A'B',
                  (castlf (eqST1, eqST1)
                    ((\1 : 'F[H]_(S_A'B' :\: B')) \O sigma0) - tau)
                    \is psdlf ->
                  (((\1 : 'F[H]_A') \O castlf (eqB', eqB') sigma0) - tau)
                    \is psdlf.
            {
              move=> eqST1 Hpsd.
              have Hcore :
                  ((\1 : 'F[H]_A') \O castlf (eqB', eqB') sigma0) =
                  castlf (eqST1, eqST1)
                    ((\1 : 'F[H]_(S_A'B' :\: B')) \O sigma0).
                exact: (esym (Hcast_tgt_lift eqST1 eqB' sigma0)).
              by rewrite Hcore.
            }
            exact: (Haux _ Hdom0).
          }
          exact: Hdom1.
        * by rewrite castlf_trlfE Hv.
    - move=> [sigma [Psigma [Hdom Hv]]].
      exists (castlf (esym eqB', esym eqB') sigma); split.
      + by rewrite castlf_psdlfE.
      + split.
        * by rewrite (Hcast_tgt_lift_inv _ sigma).
        * by rewrite castlf_trlfE Hv.
  }
  have Hphi_tgt_le_src : phi_min B' rho' <= phi_min B rhoAB.
  {
    rewrite /phi_min.
    apply: lb_le_inf.
    - by have [Hne _] := @phi_min_feasible_has_inf R L H S_AB B rhoAB Prho.
    - move=> v Hv.
      move/(proj1 (Hphi_cf_src rhoAB v)): Hv
        => [sigma [Psigma [Hdom Hv]]].
      pose sigma' := V \o sigma \o V^A.
      have Psigma' : sigma' \is psdlf.
      {
        apply/psdlfP=> x.
        rewrite /sigma' !comp_lfunE /= -adj_dotEl.
        by move/psdlfP: Psigma.
      }
      have Htrace_sigma' :
          @complex.Re R (\Tr sigma') = @complex.Re R (\Tr sigma).
      {
        rewrite /sigma' lftraceC comp_lfunA isofE comp_lfun1l.
        reflexivity.
      }
      have Hgap_psd :
          ((((\1 : 'F[H]_A') - (U \o U^A)) \O sigma') :
              'F[H]_S_A'B') \is psdlf.
      {
        have HgapA : ((\1 : 'F[H]_A') - (U \o U^A)) \is psdlf.
          by rewrite -lefE; exact: isofEr_le1 U.
        have Hten :
            ((((\1 : 'F[H]_A') - (U \o U^A)) \O sigma') :
                'F[H]_S_A'B') =
            (((\1 : 'F[H]_A') - (U \o U^A)) \⊗ sigma').
          by apply: to_Fnd_inj; rewrite (sdotFT _ _ disA'B') to_Fnd_tenE.
        rewrite Hten psdlfE.
        apply: tenf_ge0; first exact: disA'B'.
        - by move: HgapA; rewrite psdlfE.
        - by move: Psigma'; rewrite psdlfE.
      }
      have Hlift_conj :
          W \o ((\1 : 'F[H]_A) \O sigma) \o W^A =
          ((U \o U^A) \O sigma' : 'F[H]_S_A'B').
      {
        have Hsrc_ten :
            (((\1 : 'F[H]_A) \O sigma) : 'F[H]_S_AB) =
            ((\1 : 'F[H]_A) \⊗ sigma).
          by apply: to_Fnd_inj; rewrite (sdotFT _ _ disAB) to_Fnd_tenE.
        have Htgt_ten :
            (((U \o U^A) \O sigma') : 'F[H]_S_A'B') =
            ((U \o U^A) \⊗ sigma').
          by apply: to_Fnd_inj; rewrite (sdotFT _ _ disA'B') to_Fnd_tenE.
        rewrite Hsrc_ten Htgt_ten /W /sigma' tenf_adj.
        rewrite -!tenf_comp ?disAB ?disA'B' //.
        by rewrite !comp_lfun1r.
      }
      have Hconj_psd :
          (W \o ((((\1 : 'F[H]_A) \O sigma) - rhoAB)) \o W^A) \is psdlf.
      {
        have HWi_cp : formso Wi \is cpmap by exact: formso_cp.
        have HformE :
            W \o ((((\1 : 'F[H]_A) \O sigma) - rhoAB)) \o W^A =
            formso Wi ((((\1 : 'F[H]_A) \O sigma) - rhoAB)).
          by rewrite formsoE -HWi.
        rewrite HformE (CPMap_BuildE HWi_cp).
        exact: cp_psdP Hdom.
      }
      have Hdom' : (((\1 : 'F[H]_A') \O sigma') - rho') \is psdlf.
      {
        have -> :
            (((\1 : 'F[H]_A') \O sigma') - rho') =
            ((((\1 : 'F[H]_A') - (U \o U^A)) \O sigma') +
             (W \o ((((\1 : 'F[H]_A) \O sigma) - rhoAB)) \o W^A)).
        {
          have Hconj_diff :
              (W \o ((((\1 : 'F[H]_A) \O sigma) - rhoAB)) \o W^A) =
              (W \o ((\1 : 'F[H]_A) \O sigma) \o W^A) - rho'.
          {
            rewrite /rho' comp_lfunDr comp_lfunNr comp_lfunDl comp_lfunNl.
            by rewrite -!comp_lfunA.
          }
          rewrite Hconj_diff Hlift_conj.
          rewrite addrA.
          congr (_ - _).
          rewrite -sdotfDl.
          by rewrite subrK.
        }
        exact: psdlfD Hgap_psd Hconj_psd.
      }
      have Hfeas' : phi_min_feasible B' rho' v.
      {
        apply/(proj2 (Hphi_cf_tgt rho' v)).
        by exists sigma'; repeat split=> //; rewrite Hv Htrace_sigma'.
      }
      apply: ge_inf.
      + by have [_ Hlb] := @phi_min_feasible_has_inf R L H S_A'B' B' rho' Prho'.
      + exact: Hfeas'.
  }
  have Va_b1 : V^A \is bound1lf.
    by rewrite bound1lf_adj; exact: (isolf_bound1 (is_isolf V)).
  pose Va := Bound1Lf_Build Va_b1.
  have HVa : V^A = Va by exact: Bound1Lf_BuildE Va_b1.
  have HVa_cptn : formso Va \is cptn.
    by rewrite qualifE formso_cp formso_tn.
  have Hphi_src_le_tgt : phi_min B rhoAB <= phi_min B' rho'.
  {
    rewrite /phi_min.
    apply: lb_le_inf.
    - by have [Hne _] := @phi_min_feasible_has_inf R L H S_A'B' B' rho' Prho'.
    - move=> v Hv.
      move/(proj1 (Hphi_cf_tgt rho' v)): Hv
        => [sigma' [Psigma' [Hdom' Hv]]].
      pose sigma := V^A \o sigma' \o V.
      have Psigma : sigma \is psdlf.
      {
        have HVa_cp : formso Va \is cpmap by exact: formso_cp.
        have HsigmaE : sigma = formso Va sigma'
          by rewrite /sigma formsoE -HVa adjfK.
        rewrite HsigmaE (CPMap_BuildE HVa_cp).
        exact: cp_psdP Psigma'.
      }
      have Htrace_sigma_le :
          @complex.Re R (\Tr sigma) <= @complex.Re R (\Tr sigma').
      {
        have HsigmaE : sigma = formso Va sigma'
          by rewrite /sigma HVa formsoE adjfK.
        have Hsoa : ((QOperation_Build HVa_cptn) : 'SO(_, _)) = formso Va
          by exact: QOperation_BuildE.
        have Hle' := qo_trlfE (QOperation_Build HVa_cptn) Psigma'.
        rewrite Hsoa -HsigmaE in Hle'.
        have Htr_sigma_real :
            (\Tr sigma : C) = (@complex.Re R (\Tr sigma))%:C.
          by rewrite RRe_real // ger0_real // psdlf_trlf.
        have Htr_sigma'_real :
            (\Tr sigma' : C) = (@complex.Re R (\Tr sigma'))%:C.
          by rewrite RRe_real // ger0_real // psdlf_trlf.
        by move: Hle'; rewrite Htr_sigma_real Htr_sigma'_real !lecR.
      }
      have Hlift_compress :
          W^A \o ((\1 : 'F[H]_A') \O sigma') \o W =
          ((\1 : 'F[H]_A) \O sigma : 'F[H]_S_AB).
      {
        have Hsrc_ten :
            (((\1 : 'F[H]_A') \O sigma') : 'F[H]_S_A'B') =
            ((\1 : 'F[H]_A') \⊗ sigma').
          by apply: to_Fnd_inj; rewrite (sdotFT _ _ disA'B') to_Fnd_tenE.
        have Htgt_ten :
            (((\1 : 'F[H]_A) \O sigma) : 'F[H]_S_AB) =
            ((\1 : 'F[H]_A) \⊗ sigma).
          by apply: to_Fnd_inj; rewrite (sdotFT _ _ disAB) to_Fnd_tenE.
        rewrite Hsrc_ten Htgt_ten /W /sigma tenf_adj.
        rewrite -!tenf_comp ?disA'B' ?disAB //.
        by rewrite !comp_lfun1r isofE.
      }
      have Hconj_back_psd :
          (W^A \o ((((\1 : 'F[H]_A') \O sigma') - rho')) \o W) \is psdlf.
      {
        have HWa_cp : formso Wa \is cpmap by exact: formso_cp.
        have HformE :
            W^A \o ((((\1 : 'F[H]_A') \O sigma') - rho')) \o W =
            formso Wa ((((\1 : 'F[H]_A') \O sigma') - rho')).
          by rewrite formsoE -HWa adjfK.
        rewrite HformE (CPMap_BuildE HWa_cp).
        exact: cp_psdP Hdom'.
      }
      have Hdom : (((\1 : 'F[H]_A) \O sigma) - rhoAB) \is psdlf.
      {
        have Hrho_back : W^A \o rho' \o W = rhoAB.
        {
          have HWiA : W^A = Wi^A by rewrite HWi.
          rewrite /rho' HWiA HWi -!comp_lfunA.
          rewrite [Wi^A \o Wi]isofE comp_lfun1r.
          by rewrite comp_lfunA [Wi^A \o Wi]isofE comp_lfun1l.
        }
        have Hconj_back_diff :
            W^A \o ((((\1 : 'F[H]_A') \O sigma') - rho')) \o W =
            (W^A \o ((\1 : 'F[H]_A') \O sigma') \o W) - rhoAB.
        {
          rewrite /rho' comp_lfunDr comp_lfunNr comp_lfunDl comp_lfunNl.
          by rewrite Hrho_back.
        }
        have Hback_eq :
            W^A \o ((((\1 : 'F[H]_A') \O sigma') - rho')) \o W =
            (((\1 : 'F[H]_A) \O sigma) - rhoAB).
        {
          rewrite Hconj_back_diff Hlift_compress.
          reflexivity.
        }
        by rewrite -Hback_eq.
      }
      have Hfeas_src :
          phi_min_feasible B rhoAB (@complex.Re R (\Tr sigma)).
      {
        apply/(proj2 (Hphi_cf_src rhoAB (@complex.Re R (\Tr sigma)))).
        exists sigma; split.
        - exact: Psigma.
        - split.
          + exact: Hdom.
          + reflexivity.
      }
      have Hphi_le_sigma :
          phi_min B rhoAB <= @complex.Re R (\Tr sigma).
      {
        apply: ge_inf.
        - by have [_ Hlb] := @phi_min_feasible_has_inf R L H S_AB B rhoAB Prho.
        - exact: Hfeas_src.
      }
      apply: le_trans Hphi_le_sigma _.
      by rewrite Hv.
  }
  apply/eqP.
  by rewrite eq_le Hphi_tgt_le_src Hphi_src_le_tgt.
Qed.

End PhiMinIsometryInvariance.

(* ================================================================== *)
(* Property vi.B, set-level form (Data Processing on B-system).          *)
(* Tomamichel thesis (arXiv:1203.2142), Table 4.1 item vi — tex tb:Phi. *)
(* math: for TNI CPM E : B -> B',                                       *)
(*   Phi_{A|B'}((id_A \otimes E)[rho_AB]) <= Phi_{A|B}(rho_AB).         *)
(* ================================================================== *)

Section PhiDataProcBSet.
Variable (L : finType) (H : L -> chsType) (A B B' : {set L}).
Hypothesis disAB : [disjoint A & B].
Hypothesis disAB' : [disjoint A & B'].

Notation S_AB := (A :|: B).
Notation S_AB' := (A :|: B').

Let eqAB_diff : S_AB :\: B = A.
Proof.
  exact: setDU_r disAB.
Defined.

Let eqAB_cond : S_AB :&: B = B.
Proof.
  setdec.
Defined.

Let eqAB_lift : (S_AB :\: B) :|: B = S_AB.
Proof.
  by rewrite eqAB_diff.
Defined.

Let eqAB_lift_sig :
    (S_AB :\: B) :|: (S_AB :&: B) = (S_AB :\: B) :|: B.
Proof.
  by rewrite eqAB_cond.
Defined.

Let eqAB_phi : (S_AB :\: B) :|: (S_AB :&: B) = S_AB.
Proof.
  by rewrite finset.setUC finset.setID.
Defined.

Let eqAB'_diff : S_AB' :\: B' = A.
Proof.
  exact: setDU_r disAB'.
Defined.

Let eqAB'_cond : S_AB' :&: B' = B'.
Proof.
  setdec.
Defined.

Let eqAB'_lift : (S_AB' :\: B') :|: B' = S_AB'.
Proof.
  by rewrite eqAB'_diff.
Defined.

Let eqAB'_lift_sig :
    (S_AB' :\: B') :|: (S_AB' :&: B') = (S_AB' :\: B') :|: B'.
Proof.
  by rewrite eqAB'_cond.
Defined.

Let eqAB'_phi : (S_AB' :\: B') :|: (S_AB' :&: B') = S_AB'.
Proof.
  by rewrite finset.setUC finset.setID.
Defined.

Let phi_lift_term_B (sigmaB : 'F[H]_B) :
    castlf (eqAB_phi, eqAB_phi)
      ((\1 : 'F[H]_(S_AB :\: B)) \O
        castlf (esym eqAB_cond, esym eqAB_cond) sigmaB) =
    (\1 : 'F[H]_A) \O sigmaB.
Proof.
  have -> : eqAB_phi = etrans eqAB_lift_sig eqAB_lift
    by apply: eq_irrelevance.
  rewrite -castlf_comp.
  rewrite (@sdotIf_cast_r R _ _ (S_AB :\: B) (S_AB :&: B) B
    eqAB_cond eqAB_lift_sig
    (castlf (esym eqAB_cond, esym eqAB_cond) sigmaB)).
  rewrite castlfKV.
  rewrite (@sdotIf_cast_l R _ _ (S_AB :\: B) A B eqAB_diff eqAB_lift
    (\1 : 'F[H]_(S_AB :\: B)) sigmaB).
  by rewrite castlf1.
Defined.

Let phi_lift_term_B' (sigmaB' : 'F[H]_B') :
    castlf (eqAB'_phi, eqAB'_phi)
      ((\1 : 'F[H]_(S_AB' :\: B')) \O
        castlf (esym eqAB'_cond, esym eqAB'_cond) sigmaB') =
    (\1 : 'F[H]_A) \O sigmaB'.
Proof.
  have -> : eqAB'_phi = etrans eqAB'_lift_sig eqAB'_lift
    by apply: eq_irrelevance.
  rewrite -castlf_comp.
  rewrite (@sdotIf_cast_r R _ _ (S_AB' :\: B') (S_AB' :&: B') B'
    eqAB'_cond eqAB'_lift_sig
    (castlf (esym eqAB'_cond, esym eqAB'_cond) sigmaB')).
  rewrite castlfKV.
  rewrite (@sdotIf_cast_l R _ _ (S_AB' :\: B') A B' eqAB'_diff eqAB'_lift
    (\1 : 'F[H]_(S_AB' :\: B')) sigmaB').
  by rewrite castlf1.
Defined.

(* path: entropy:phi_min_data_proc_B -> entropy:entropy_data_proc -> *)
(*   bb84:bb84_secret *)
Lemma phi_min_data_proc_B (rhoAB : 'F[H]_S_AB)
    (E : 'QO[H]_(B, B')) :
  rhoAB \is psdlf ->
  phi_min B' (((\:1 : 'SO[H]_A) :⊗ E) rhoAB) <=
    phi_min B rhoAB.
Proof.
  move=> Prho.
  pose rhoAB' : 'F[H]_S_AB' := (((\:1 : 'SO[H]_A) :⊗ E) rhoAB).
  have PidE : ((\:1 : 'SO[H]_A) :⊗ E) \is cpmap.
  {
    exact: (@tenso_cp R L H A A B B' disAB
      (\:1 : 'CP[H]_A) (E : 'CP[H]_(B, B'))).
  }
  have Ptarget : rhoAB' \is psdlf.
  {
    rewrite /rhoAB' (CPMap_BuildE PidE).
    exact: cp_psdP Prho.
  }
  have psdlf_le_tr_id_local :
      forall (S : {set L}) (f : 'F[H]_S),
        f \is psdlf ->
        f <= (@complex.Re R (\Tr f))%:C *: (\1 : 'F[H]_S).
  {
    move=> S f Pf.
    have Htr_real : \Tr f \is Num.real := ger0_real (psdlf_trlf Pf).
    rewrite lef_h2mx.
    have -> :
        h2mx ((@complex.Re R (\Tr f))%:C *: (\1 : 'F[H]_S)) =
        (\tr (h2mx f))%:M.
    {
      rewrite h2mxZ_lf h2mx1 /lftrace (RRe_real Htr_real) scalemx1.
      done.
    }
    apply: lemx_psd_ub.
    by rewrite qualifE.
  }
  rewrite /phi_min.
  apply: lb_le_inf.
  - pose c := @complex.Re R (\Tr rhoAB).
    pose sigma0B : 'F[H]_B := c%:C *: (\1 : 'F[H]_B).
    pose sigma0 : 'F[H]_(S_AB :&: B) :=
      castlf (esym eqAB_cond, esym eqAB_cond) sigma0B.
    have Pc : 0 <= c.
    {
      have Htr_real : (\Tr rhoAB : C) = c%:C
        by rewrite /c RRe_real // ger0_real // psdlf_trlf.
      by move: (psdlf_trlf Prho); rewrite Htr_real lecR.
    }
    have Psigma0 : sigma0 \is psdlf.
    {
      rewrite /sigma0 /sigma0B castlf_psdlfE.
      apply: psdlfZ; first by rewrite lecR.
      by rewrite qualifE h2mx1; apply: psdmx1.
    }
    exists (@complex.Re R (\Tr sigma0)).
    exists sigma0; split; first exact: Psigma0.
    split; last reflexivity.
    have -> :
        sigma0 = castlf (esym eqAB_cond, esym eqAB_cond) sigma0B
      by [].
    rewrite phi_lift_term_B /sigma0B sdotfZr sdotf11.
    exact: psdlf_le_tr_id_local Prho.
  - move=> v [sigma [Psigma [Hsigma Hv]]].
    pose sigmaB : 'F[H]_B := castlf (eqAB_cond, eqAB_cond) sigma.
    pose sigmaB' : 'F[H]_B' := E sigmaB.
    pose sigma' : 'F[H]_(S_AB' :&: B') :=
      castlf (esym eqAB'_cond, esym eqAB'_cond) sigmaB'.
    have PsigmaB : sigmaB \is psdlf by rewrite /sigmaB castlf_psdlfE.
    have PsigmaB' : sigmaB' \is psdlf.
    {
      rewrite /sigmaB' (CPMap_BuildE (cptn_cpmap (is_cptn E))).
      exact: cp_psdP PsigmaB.
    }
    have Psigma' : sigma' \is psdlf by rewrite /sigma' castlf_psdlfE.
    have HsigmaB :
        ((\1 : 'F[H]_A) \O sigmaB - rhoAB) \is psdlf.
    {
      move: Hsigma.
      have -> :
          sigma = castlf (esym eqAB_cond, esym eqAB_cond) sigmaB
        by rewrite /sigmaB castlfK.
      by rewrite phi_lift_term_B.
    }
    have Hmap_id :
        (((\:1 : 'SO[H]_A) :⊗ E) ((\1 : 'F[H]_A) \O sigmaB)) =
        (\1 : 'F[H]_A) \O sigmaB'.
    {
      have Hten :
          ((\1 : 'F[H]_A) \O sigmaB) =
          ((\1 : 'F[H]_A) \⊗ sigmaB : 'F[H]_S_AB).
      {
        apply: to_Fnd_inj.
        by rewrite (sdotFT _ _ disAB) to_Fnd_tenE.
      }
      have Hten' :
          ((\1 : 'F[H]_A) \O sigmaB') =
          ((\1 : 'F[H]_A) \⊗ sigmaB' : 'F[H]_S_AB').
      {
        apply: to_Fnd_inj.
        by rewrite (sdotFT _ _ disAB') to_Fnd_tenE.
      }
      rewrite Hten Hten' /sigmaB'.
      have Hten_map :
          ((\:1 : 'SO[H]_A) (\1 : 'F[H]_A)) \⊗ (E sigmaB) =
          (((\:1 : 'SO[H]_A) :⊗ E)
            ((\1 : 'F[H]_A) \⊗ sigmaB)).
      {
        exact: (tenso_correct (\:1 : 'SO[H]_A) E disAB
          (\1 : 'F[H]_A) sigmaB).
      }
      rewrite soE in Hten_map.
      symmetry.
      exact: Hten_map.
    }
    have Htarget_feas_psd :
        ((\1 : 'F[H]_A) \O sigmaB' - rhoAB') \is psdlf.
    {
      have Hord : rhoAB <= ((\1 : 'F[H]_A) \O sigmaB)
        by move: HsigmaB; rewrite -lefE.
      have Hord' :
          (((\:1 : 'SO[H]_A) :⊗ E) rhoAB) <=
          (((\:1 : 'SO[H]_A) :⊗ E) ((\1 : 'F[H]_A) \O sigmaB)).
      {
        rewrite (CPMap_BuildE PidE).
        exact: cp_preserve_order Hord.
      }
      move: Hord'.
      rewrite /rhoAB' Hmap_id -lefE.
      done.
    }
    have Hfeas' :
        phi_min_feasible B' rhoAB' (@complex.Re R (\Tr sigma')).
    {
      exists sigma'; split; first exact: Psigma'.
      split; last reflexivity.
      have -> :
          sigma' = castlf (esym eqAB'_cond, esym eqAB'_cond) sigmaB'
        by [].
      rewrite phi_lift_term_B'.
      exact: Htarget_feas_psd.
    }
    have Hhas_inf' :
        has_inf [set w : R | phi_min_feasible B' rhoAB' w].
    {
      split.
      - by exists (@complex.Re R (\Tr sigma')).
      - exists 0 => w [tau [Ptau [_ ->]]].
        by have := psdlf_trlf Ptau; rewrite lecE /= => /andP[_].
    }
    have Htr_le :
        @complex.Re R (\Tr sigma') <= v.
    {
      have Htr_sigma_eq : \Tr sigma = \Tr sigmaB
        by rewrite /sigmaB castlf_trlfE.
      have Htr_sigma'_eq : \Tr sigma' = \Tr sigmaB'
        by rewrite /sigma' castlf_trlfE.
      have Htr_sigmaB_real :
          (\Tr sigmaB : C) = (@complex.Re R (\Tr sigmaB))%:C
        by rewrite RRe_real // ger0_real // psdlf_trlf.
      have Htr_sigmaB'_real :
          (\Tr sigmaB' : C) = (@complex.Re R (\Tr sigmaB'))%:C
        by rewrite RRe_real // ger0_real // psdlf_trlf.
      have Htr_leC : \Tr sigmaB' <= \Tr sigmaB.
      {
        rewrite /sigmaB' (QOperation_BuildE (is_cptn E)).
        exact: qo_trlfE PsigmaB.
      }
      have Hre_le :
          @complex.Re R (\Tr sigmaB') <= @complex.Re R (\Tr sigmaB)
        by move: Htr_leC; rewrite Htr_sigmaB_real Htr_sigmaB'_real lecR.
      rewrite Hv Htr_sigma'_eq Htr_sigma_eq.
      exact: Hre_le.
    }
    exact: le_trans (ge_inf Hhas_inf'.2 Hfeas') Htr_le.
Qed.

End PhiDataProcBSet.

(* Property vi.A (Data Processing on A-system, Table 4.1 item vi):      *)
(* If E is sub-unital CP, applying E to the non-conditioned register     *)
(* cannot increase Phi_min.                                             *)
Section PhiDataProcASet.
Variable (L : finType) (H : L -> chsType) (A A' B : {set L}).
Hypothesis disAB : [disjoint A & B].
Hypothesis disA'B : [disjoint A' & B].

Notation S_AB := (A :|: B).
Notation S_A'B := (A' :|: B).

Let eqAB_diff : S_AB :\: B = A.
Proof.
  exact: setDU_r.
Defined.

Let eqAB_cond : S_AB :&: B = B.
Proof.
  setdec.
Defined.

Let eqAB_lift :
    (S_AB :\: B) :|: B = S_AB.
Proof.
  by rewrite eqAB_diff.
Defined.

Let eqAB_lift_sig :
    (S_AB :\: B) :|: (S_AB :&: B) =
    (S_AB :\: B) :|: B.
Proof.
  by rewrite eqAB_cond.
Defined.

Let eqAB_phi :
    (S_AB :\: B) :|: (S_AB :&: B) = S_AB.
Proof.
  by rewrite finset.setUC finset.setID.
Defined.

Let eqA'B_diff : S_A'B :\: B = A'.
Proof.
  exact: setDU_r.
Defined.

Let eqA'B_cond : S_A'B :&: B = B.
Proof.
  setdec.
Defined.

Let eqA'B_lift :
    (S_A'B :\: B) :|: B = S_A'B.
Proof.
  by rewrite eqA'B_diff.
Defined.

Let eqA'B_lift_sig :
    (S_A'B :\: B) :|: (S_A'B :&: B) =
    (S_A'B :\: B) :|: B.
Proof.
  by rewrite eqA'B_cond.
Defined.

Let eqA'B_phi :
    (S_A'B :\: B) :|: (S_A'B :&: B) = S_A'B.
Proof.
  by rewrite finset.setUC finset.setID.
Defined.

Let phi_lift_term_A (sigmaB : 'F[H]_B) :
    castlf (eqAB_phi, eqAB_phi)
      ((\1 : 'F[H]_(S_AB :\: B)) \O
        castlf (esym eqAB_cond, esym eqAB_cond) sigmaB) =
    (\1 : 'F[H]_A) \O sigmaB.
Proof.
  have -> : eqAB_phi = etrans eqAB_lift_sig eqAB_lift.
  {
    apply: eq_irrelevance.
  }
  rewrite -castlf_comp.
  rewrite (@sdotIf_cast_r R _ _ (S_AB :\: B)
    (S_AB :&: B) B eqAB_cond eqAB_lift_sig
    (castlf (esym eqAB_cond, esym eqAB_cond) sigmaB)).
  have -> :
      castlf (eqAB_cond, eqAB_cond)
        (castlf (esym eqAB_cond, esym eqAB_cond) sigmaB) = sigmaB.
  {
    exact: castlfKV.
  }
  rewrite (@sdotIf_cast_l R _ _ (S_AB :\: B) A B
    eqAB_diff eqAB_lift
    (\1 : 'F[H]_(S_AB :\: B)) sigmaB).
  have -> :
      castlf (eqAB_diff, eqAB_diff)
        (\1 : 'F[H]_(S_AB :\: B)) =
      (\1 : 'F[H]_A).
  {
    exact: castlf1.
  }
  done.
Defined.

Let phi_lift_term_A' (sigmaB : 'F[H]_B) :
    castlf (eqA'B_phi, eqA'B_phi)
      ((\1 : 'F[H]_(S_A'B :\: B)) \O
        castlf (esym eqA'B_cond, esym eqA'B_cond) sigmaB) =
    (\1 : 'F[H]_A') \O sigmaB.
Proof.
  have -> : eqA'B_phi = etrans eqA'B_lift_sig eqA'B_lift.
  {
    apply: eq_irrelevance.
  }
  rewrite -castlf_comp.
  rewrite (@sdotIf_cast_r R _ _ (S_A'B :\: B)
    (S_A'B :&: B) B eqA'B_cond eqA'B_lift_sig
    (castlf (esym eqA'B_cond, esym eqA'B_cond) sigmaB)).
  have -> :
      castlf (eqA'B_cond, eqA'B_cond)
        (castlf (esym eqA'B_cond, esym eqA'B_cond) sigmaB) = sigmaB.
  {
    exact: castlfKV.
  }
  rewrite (@sdotIf_cast_l R _ _ (S_A'B :\: B) A' B
    eqA'B_diff eqA'B_lift
    (\1 : 'F[H]_(S_A'B :\: B)) sigmaB).
  have -> :
      castlf (eqA'B_diff, eqA'B_diff)
        (\1 : 'F[H]_(S_A'B :\: B)) =
      (\1 : 'F[H]_A').
  {
    exact: castlf1.
  }
  done.
Defined.

(* path: entropy:phi_min_data_proc_A -> entropy:entropy_data_proc -> *)
(*   bb84:bb84_secret *)
Lemma phi_min_data_proc_A (rhoAB : 'F[H]_S_AB)
    (E : 'SO[H]_(A, A')) :
  rhoAB \is psdlf ->
  E \is cpmap ->
  E^*o \is tnmap ->
  phi_min B ((E :⊗ (\:1 : 'SO[H]_B)) rhoAB) <=
    phi_min B rhoAB.
Proof.
  move=> Prho HEcp HEdualtn.
  pose rhoAB' : 'F[H]_S_A'B := ((E :⊗ (\:1 : 'SO[H]_B)) rhoAB).
  have PEid : (E :⊗ (\:1 : 'SO[H]_B)) \is cpmap.
  {
    rewrite (CPMap_BuildE HEcp).
    exact: (@tenso_cp R L H A A' B B disAB
      (CPMap_Build HEcp) (\:1 : 'CP[H]_B)).
  }
  have Ptarget : rhoAB' \is psdlf.
  {
    rewrite /rhoAB' (CPMap_BuildE PEid).
    exact: cp_psdP Prho.
  }
    have HEsub : E (\1 : 'F[H]_A) <= (\1 : 'F[H]_A').
    {
      rewrite (CPMap_BuildE HEcp).
      rewrite -(@cp_isdualtnE R _ _ (CPMap_Build HEcp)).
      by rewrite -(CPMap_BuildE HEcp).
    }
  have psdlf_le_tr_id_local :
      forall (S : {set L}) (f : 'F[H]_S),
        f \is psdlf ->
        f <= (@complex.Re R (\Tr f))%:C *: (\1 : 'F[H]_S).
  {
    move=> S f Pf.
    have Htr_real : \Tr f \is Num.real := ger0_real (psdlf_trlf Pf).
    rewrite lef_h2mx.
    have -> :
        h2mx ((@complex.Re R (\Tr f))%:C *: (\1 : 'F[H]_S)) =
        (\tr (h2mx f))%:M.
    {
      rewrite h2mxZ_lf h2mx1 /lftrace (RRe_real Htr_real) scalemx1.
      done.
    }
    apply: lemx_psd_ub.
    by rewrite qualifE.
  }
  rewrite /phi_min.
  apply: lb_le_inf.
  - pose c := @complex.Re R (\Tr rhoAB).
    pose sigma0B : 'F[H]_B := c%:C *: (\1 : 'F[H]_B).
    pose sigma0 : 'F[H]_(S_AB :&: B) :=
      castlf (esym eqAB_cond, esym eqAB_cond) sigma0B.
    have Pc : 0 <= c.
    {
      have Htr_real : (\Tr rhoAB : C) = c%:C
        by rewrite /c RRe_real // ger0_real // psdlf_trlf.
      by move: (psdlf_trlf Prho); rewrite Htr_real lecR.
    }
    have Psigma0 : sigma0 \is psdlf.
    {
      rewrite /sigma0 /sigma0B castlf_psdlfE.
      apply: psdlfZ; first by rewrite lecR.
      by rewrite qualifE h2mx1; apply: psdmx1.
    }
    exists (@complex.Re R (\Tr sigma0)).
    exists sigma0; split; first exact: Psigma0.
    split; last reflexivity.
    have -> :
        sigma0 = castlf (esym eqAB_cond, esym eqAB_cond) sigma0B
      by [].
    rewrite phi_lift_term_A /sigma0B sdotfZr sdotf11.
    exact: psdlf_le_tr_id_local Prho.
  - move=> v [sigma [Psigma [Hsigma Hv]]].
    pose sigmaB : 'F[H]_B := castlf (eqAB_cond, eqAB_cond) sigma.
    pose sigma' : 'F[H]_(S_A'B :&: B) :=
      castlf (esym eqA'B_cond, esym eqA'B_cond) sigmaB.
    have PsigmaB : sigmaB \is psdlf by rewrite /sigmaB castlf_psdlfE.
    have Psigma' : sigma' \is psdlf by rewrite /sigma' castlf_psdlfE.
    have HsigmaB :
        ((\1 : 'F[H]_A) \O sigmaB - rhoAB) \is psdlf.
    {
      move: Hsigma.
      have -> :
          sigma = castlf (esym eqAB_cond, esym eqAB_cond) sigmaB
        by rewrite /sigmaB castlfK.
      by rewrite phi_lift_term_A.
    }
    have Hmap_id :
        ((E :⊗ (\:1 : 'SO[H]_B)) ((\1 : 'F[H]_A) \O sigmaB)) =
        (E (\1 : 'F[H]_A)) \O sigmaB.
    {
      have Hten :
          ((\1 : 'F[H]_A) \O sigmaB) =
          ((\1 : 'F[H]_A) \⊗ sigmaB : 'F[H]_S_AB).
      {
        apply: to_Fnd_inj.
        by rewrite (sdotFT _ _ disAB) to_Fnd_tenE.
      }
      have Hten' :
          ((E (\1 : 'F[H]_A)) \O sigmaB) =
          ((E (\1 : 'F[H]_A)) \⊗ sigmaB : 'F[H]_S_A'B).
      {
        apply: to_Fnd_inj.
        by rewrite (sdotFT _ _ disA'B) to_Fnd_tenE.
      }
      rewrite Hten Hten'.
      have Hten_map :
          (E (\1 : 'F[H]_A)) \⊗
            ((\:1 : 'SO[H]_B) sigmaB) =
          ((E :⊗ (\:1 : 'SO[H]_B))
            ((\1 : 'F[H]_A) \⊗ sigmaB)).
      {
        exact: (tenso_correct E (\:1 : 'SO[H]_B) disAB
          (\1 : 'F[H]_A) sigmaB).
      }
      rewrite soE in Hten_map.
      symmetry.
      exact: Hten_map.
    }
    have Htarget_feas_psd :
        ((\1 : 'F[H]_A') \O sigmaB - rhoAB') \is psdlf.
    {
      have Hord : rhoAB <= ((\1 : 'F[H]_A) \O sigmaB)
        by move: HsigmaB; rewrite -lefE.
      have Hord' :
          ((E :⊗ (\:1 : 'SO[H]_B)) rhoAB) <=
          ((E :⊗ (\:1 : 'SO[H]_B)) ((\1 : 'F[H]_A) \O sigmaB)).
      {
        rewrite (CPMap_BuildE PEid).
        exact: cp_preserve_order Hord.
      }
      have Hmap_le :
          ((E :⊗ (\:1 : 'SO[H]_B)) ((\1 : 'F[H]_A) \O sigmaB)) <=
          (\1 : 'F[H]_A') \O sigmaB.
      {
        rewrite Hmap_id.
        have Hten_le :
            (E (\1 : 'F[H]_A)) \⊗ sigmaB <=
            (\1 : 'F[H]_A') \⊗ sigmaB.
        {
          apply: (lef_tenfl disA'B).
          - exact: psdlf_ge0 PsigmaB.
          - exact: HEsub.
        }
        move: Hten_le.
        have -> :
            (E (\1 : 'F[H]_A)) \⊗ sigmaB =
            (E (\1 : 'F[H]_A)) \O sigmaB.
        {
          apply: to_Fnd_inj.
          by rewrite (sdotFT _ _ disA'B) to_Fnd_tenE.
        }
        have -> :
            (\1 : 'F[H]_A') \⊗ sigmaB =
            (\1 : 'F[H]_A') \O sigmaB.
        {
          apply: to_Fnd_inj.
          by rewrite (sdotFT _ _ disA'B) to_Fnd_tenE.
        }
        done.
      }
      have Hord_final :
          rhoAB' <= (\1 : 'F[H]_A') \O sigmaB.
      {
        exact: le_trans Hord' Hmap_le.
      }
      by move: Hord_final; rewrite -lefE.
    }
    have Hfeas' : phi_min_feasible B rhoAB' v.
    {
      exists sigma'; split; first exact: Psigma'.
      split.
      - have -> :
            sigma' = castlf (esym eqA'B_cond, esym eqA'B_cond) sigmaB
          by [].
        rewrite phi_lift_term_A'.
        exact: Htarget_feas_psd.
      - rewrite Hv /sigma' castlf_trlfE /sigmaB castlf_trlfE.
        reflexivity.
    }
    have Hhas_inf' :
        has_inf [set w : R | phi_min_feasible B rhoAB' w].
    {
      split.
      - by exists v.
      - exists 0 => w [tau [Ptau [_ ->]]].
        by have := psdlf_trlf Ptau; rewrite lecE /= => /andP[_].
    }
    rewrite -/rhoAB'.
    exact: (ge_inf Hhas_inf'.2 Hfeas').
Qed.

End PhiDataProcASet.

(* Property vi, set-level form (Data processing, Table 4.1 item vi):    *)
(* TNI processing on the conditioning system and sub-unital processing   *)
(* on the witnessed system cannot increase Phi.                         *)
Section PhiMinDataProcessing.
Variable (L : finType) (H : L -> chsType) (A A' B B' : {set L}).
Hypothesis disAB : [disjoint A & B].
Hypothesis disAB' : [disjoint A & B'].
Hypothesis disA'B : [disjoint A' & B].

(* path: entropy:phi_min_vi_data_proc -> entropy:entropy_data_proc -> *)
(*   bb84:bb84_secret *)
Lemma phi_min_vi_data_proc (rhoAB : 'F[H]_(A :|: B))
    (E_B : 'QO[H]_(B, B')) (E_A : 'SO[H]_(A, A')) :
  rhoAB \is psdlf ->
  E_A \is cpmap ->
  E_A^*o \is tnmap ->
  phi_min B' (((\:1 : 'SO[H]_A) :⊗ E_B) rhoAB) <= phi_min B rhoAB /\
  phi_min B ((E_A :⊗ (\:1 : 'SO[H]_B)) rhoAB) <= phi_min B rhoAB.
Proof.
  move=> Prho HEA_cp HEA_dual_tn.
  split.
  - exact: (@phi_min_data_proc_B L H A B B'
      disAB disAB' rhoAB E_B Prho).
  - exact: (@phi_min_data_proc_A L H A A' B
      disAB disA'B rhoAB E_A Prho HEA_cp HEA_dual_tn).
Qed.

End PhiMinDataProcessing.

(* Property vii (Extension by an uncorrelated/processed C-system),        *)
(* set-level form used by th:data-proc.                                  *)
Section PhiDataProcExtSet.
Variable (L : finType) (H : L -> chsType) (A B C C' : {set L}).
Hypothesis disAB : [disjoint A & B].
Hypothesis disAC : [disjoint A & C].
Hypothesis disBC : [disjoint B & C].
Hypothesis disAC' : [disjoint A & C'].
Hypothesis disBC' : [disjoint B & C'].

Notation S_BC := (B :|: C).
Notation S_BC' := (B :|: C').
Notation S_ABC := (A :|: S_BC).
Notation S_ABC' := (A :|: S_BC').

Let disA_BC : [disjoint A & S_BC].
Proof.
  by rewrite /S_BC disjointXU disAB disAC.
Defined.

Let disA_BC' : [disjoint A & S_BC'].
Proof.
  by rewrite /S_BC' disjointXU disAB disAC'.
Defined.

(* path: entropy:phi_min_data_proc_conditioning_ext -> *)
(*   entropy:entropy_data_proc -> *)
(*   bb84:bb84_secret *)
Lemma phi_min_data_proc_conditioning_ext
    (rhoABC : 'F[H]_S_ABC) (E : 'QO[H]_(C, C')) :
  rhoABC \is psdlf ->
  phi_min S_BC'
      (((\:1 : 'SO[H]_A) :⊗
         ((\:1 : 'SO[H]_B) :⊗ E)) rhoABC) <=
    phi_min S_BC rhoABC.
Proof.
  move=> Prho.
  pose EBCso : 'SO[H]_(S_BC, S_BC') :=
    ((\:1 : 'SO[H]_B) :⊗ E).
  have HEBC : EBCso \is cptn.
  {
    rewrite /EBCso.
    exact: (@tenso_qo R L H B B C C'
      disBC disBC' (\:1 : 'QO[H]_B) E).
  }
  have Hle :=
    @phi_min_data_proc_B L H A S_BC S_BC'
      disA_BC disA_BC' rhoABC (QOperation_Build HEBC) Prho.
  rewrite -(QOperation_BuildE HEBC) /EBCso in Hle.
  exact: Hle.
Qed.

End PhiDataProcExtSet.

(* Property vii (Data Processing on Extension), set-level form.         *)
(* Tomamichel thesis (arXiv:1203.2142), Table 4.1 item vii — tex tb:Phi. *)
(* math: For TNI CPM E : B -> B' with B an EXTENSION register (neither  *)
(* the witness nor the conditioning), Phi_C((id_A ⊗ E ⊗ id_C)[rho])     *)
(*   <= Phi_C(rho).                                                     *)
Section PhiDataProcExtensionSet.
Variable (L : finType) (H : L -> chsType) (A B B' C : {set L}).
Hypothesis disAB : [disjoint A & B].
Hypothesis disAB' : [disjoint A & B'].
Hypothesis disAC : [disjoint A & C].
Hypothesis disBC : [disjoint B & C].
Hypothesis disB'C : [disjoint B' & C].

Notation S_AB := (A :|: B).
Notation S_AB' := (A :|: B').
Notation S_ABC := (S_AB :|: C).
Notation S_ABC' := (S_AB' :|: C).

Let disS_ABC : [disjoint S_AB & C].
Proof.
  by rewrite /S_AB disjointUX disAC disBC.
Defined.

Let disS_AB'C : [disjoint S_AB' & C].
Proof.
  by rewrite /S_AB' disjointUX disAC disB'C.
Defined.

(* Extended Phi-vii data-processing statement. Some consumers inline the   *)
(* marginal bound and `phi_min_ii_mono`; this theorem provides the same    *)
(* argument as a reusable labelled API surface.                            *)
Lemma phi_min_vii_data_proc_ext
    (rhoABC : 'F[H]_S_ABC) (E : 'SO[H]_(B, B')) :
  rhoABC \is psdlf ->
  E \is cpmap ->
  E^*o \is tnmap ->
  phi_min C ((((\:1 : 'SO[H]_A) :⊗ E) :⊗ (\:1 : 'SO[H]_C)) rhoABC) <=
    phi_min C rhoABC.
Proof.
  move=> Prho HEcp HEdualtn.
  pose Eab : 'SO[H]_(S_AB, S_AB') := (\:1 : 'SO[H]_A) :⊗ E.
  have HEab_cp : Eab \is cpmap.
  {
    rewrite /Eab.
    exact: (@tenso_cp R L H A A B B' disAB
      (\:1 : 'CP[H]_A) (CPMap_Build HEcp)).
  }
  have HEab_dualtn : Eab^*o \is tnmap.
  {
      have HEsub : E (\1 : 'F[H]_B) <= (\1 : 'F[H]_B').
      {
        rewrite (CPMap_BuildE HEcp).
        rewrite -(@cp_isdualtnE R _ _ (CPMap_Build HEcp)).
        by rewrite -(CPMap_BuildE HEcp).
      }
    rewrite (CPMap_BuildE HEab_cp) cp_isdualtnE -(CPMap_BuildE HEab_cp) /Eab.
    have H1AB : (\1 : 'F[H]_S_AB) = (\1 : 'F[H]_A) \⊗ (\1 : 'F[H]_B)
      by rewrite tenf11.
    rewrite H1AB.
    have Hmap :
        ((\:1 : 'SO[H]_A) :⊗ E)
          ((\1 : 'F[H]_A) \⊗ (\1 : 'F[H]_B)) =
        (\1 : 'F[H]_A) \⊗ (E (\1 : 'F[H]_B)).
    {
      have := tenso_correct (\:1 : 'SO[H]_A) E disAB
        (\1 : 'F[H]_A) (\1 : 'F[H]_B).
      rewrite soE => <-.
      reflexivity.
    }
    rewrite Hmap.
    have H1AB' : (\1 : 'F[H]_S_AB') = (\1 : 'F[H]_A) \⊗ (\1 : 'F[H]_B')
      by rewrite tenf11.
    rewrite H1AB'.
    apply: (lef_tenfr disAB').
    - exact: lef01.
    - exact: HEsub.
  }
  have Hassoc :
      (((\:1 : 'SO[H]_A) :⊗ E) :⊗ (\:1 : 'SO[H]_C)) =
      (Eab :⊗ (\:1 : 'SO[H]_C)) :> 'SO[H]_(S_ABC, S_ABC')
    by [].
  rewrite Hassoc.
  exact: (@phi_min_data_proc_A L H S_AB S_AB' C
    disS_ABC disS_AB'C rhoABC Eab Prho HEab_cp HEab_dualtn).
Qed.

End PhiDataProcExtensionSet.

(* Property viii, set-level form (Tensor product, Table 4.1 item viii): *)
(* Phi_{A1A2|B1B2}(rho1 tensor rho2) = Phi_{A1|B1}(rho1) Phi_{A2|B2}(rho2). *)
Section PhiMinTensorProduct.
Variable (L : finType) (H : L -> chsType).
Variable (A1 B1 A2 B2 : {set L}).

Notation S1 := (A1 :|: B1).
Notation S2 := (A2 :|: B2).

Hypothesis disA1B1 : [disjoint A1 & B1].
Hypothesis disA2B2 : [disjoint A2 & B2].
Hypothesis disS1S2 : [disjoint S1 & S2].

(* path: entropy:phi_min_viii_tens -> entropy:entropy_data_proc -> *)
(*   bb84:bb84_secret *)
Lemma phi_min_viii_tens (rho1 : 'F[H]_S1) (rho2 : 'F[H]_S2) :
  rho1 \is psdlf ->
  rho2 \is psdlf ->
  phi_min (B1 :|: B2) (rho1 \⊗ rho2) =
    phi_min B1 rho1 * phi_min B2 rho2.
Proof.
  move=> Prho1 Prho2.
  pose Phi1 := phi_min B1 rho1.
  pose Phi2 := phi_min B2 rho2.
  pose Phi12 := phi_min (B1 :|: B2) (rho1 \⊗ rho2).
  have Pprod : (rho1 \⊗ rho2) \is psdlf.
  {
    rewrite psdlfE.
    apply: tenf_ge0; first exact: disS1S2.
    - by move: Prho1; rewrite psdlfE.
    - by move: Prho2; rewrite psdlfE.
  }
  have HPhi1_ge0 : 0 <= Phi1.
  {
    rewrite /Phi1 /phi_min.
    apply: lb_le_inf.
    - by have [Hne _] :=
        @phi_min_feasible_has_inf R L H S1 B1 rho1 Prho1.
    - move=> v [sigma [Psigma [_ ->]]].
      by have := psdlf_trlf Psigma; rewrite lecE /= => /andP[_].
  }
  have HPhi2_ge0 : 0 <= Phi2.
  {
    rewrite /Phi2 /phi_min.
    apply: lb_le_inf.
    - by have [Hne _] :=
        @phi_min_feasible_has_inf R L H S2 B2 rho2 Prho2.
    - move=> v [sigma [Psigma [_ ->]]].
      by have := psdlf_trlf Psigma; rewrite lecE /= => /andP[_].
  }
  have HPhi12_ge0 : 0 <= Phi12.
  {
    rewrite /Phi12 /phi_min.
    apply: lb_le_inf.
    - by have [Hne _] :=
        @phi_min_feasible_has_inf R L H (S1 :|: S2) (B1 :|: B2)
          (rho1 \⊗ rho2) Pprod.
    - move=> v [sigma [Psigma [_ ->]]].
      by have := psdlf_trlf Psigma; rewrite lecE /= => /andP[_].
  }
  have Htensor_primal_witness :
      forall x y : R,
        phi_min_feasible B1 rho1 x ->
        phi_min_feasible B2 rho2 y ->
        phi_min_feasible (B1 :|: B2) (rho1 \⊗ rho2) (x * y).
  {
    move=> x y Hx Hy.
    move: Hx => [sigma1 [Psigma1 [Hdom1 ->]]].
    move: Hy => [sigma2 [Psigma2 [Hdom2 ->]]].
    have eqB1 : S1 :&: B1 = B1.
    {
      change ((A1 :|: B1) :&: B1 = B1).
      by rewrite finset.setUC finset.setUK.
    }
    have eqB2 : S2 :&: B2 = B2.
    {
      change ((A2 :|: B2) :&: B2 = B2).
      by rewrite finset.setUC finset.setUK.
    }
    have eqB12 : ((S1 :|: S2) :&: (B1 :|: B2)) = (B1 :|: B2).
    {
      apply/setP=> z.
      rewrite /S1 /S2 !inE.
      by case: (z \in B1); case: (z \in B2);
        rewrite ?orbT ?orbF ?andbT ?andbF.
    }
    have disB1B2 : [disjoint B1 & B2].
    {
      move: disS1S2.
      change ([disjoint (A1 :|: B1) & (A2 :|: B2)] ->
        [disjoint B1 & B2]).
      setdec.
    }
    pose sigmaB1 : 'F[H]_B1 := castlf (eqB1, eqB1) sigma1.
    pose sigmaB2 : 'F[H]_B2 := castlf (eqB2, eqB2) sigma2.
    pose sigma12 : 'F[H]_((S1 :|: S2) :&: (B1 :|: B2)) :=
      castlf (esym eqB12, esym eqB12) (sigmaB1 \⊗ sigmaB2).
    exists sigma12.
    split.
      - rewrite /sigma12 castlf_psdlfE psdlfE.
        apply: tenf_ge0; first exact: disB1B2.
        + by rewrite -psdlfE /sigmaB1 castlf_psdlfE.
        + by rewrite -psdlfE /sigmaB2 castlf_psdlfE.
    - split.
      + set D1 := (X in (X - rho1) \is psdlf) in Hdom1.
        set D2 := (X in (X - rho2) \is psdlf) in Hdom2.
        set D12 := (X in (X - (rho1 \⊗ rho2)) \is psdlf).
          have HD12 : D12 = D1 \⊗ D2.
          {
            have eqA1 : S1 :\: B1 = A1 by rewrite /S1 setDU_r.
            have eqA2 : S2 :\: B2 = A2 by rewrite /S2 setDU_r.
            have eqU11 :
                (S1 :\: B1) :|: (S1 :&: B1) =
                A1 :|: (S1 :&: B1) by rewrite eqA1.
            have eqU12 : A1 :|: (S1 :&: B1) = S1
              by rewrite eqB1 /S1.
            have eqU21 :
                (S2 :\: B2) :|: (S2 :&: B2) =
                A2 :|: (S2 :&: B2) by rewrite eqA2.
            have eqU22 : A2 :|: (S2 :&: B2) = S2
              by rewrite eqB2 /S2.
            have Hlift1 :
                D1 = ((\1 : 'F[H]_A1) \O sigmaB1 : 'F[H]_S1).
            {
              rewrite /D1 /sigmaB1.
              transitivity
                (castlf (etrans eqU11 eqU12, etrans eqU11 eqU12)
                  ((\1 : 'F[H]_(S1 :\: B1)) \O sigma1)).
              {
                by rewrite (eq_irrelevance
                  (eq_ind_r (eq^~ S1)
                    (eq_ind_r (eq^~ S1) (erefl S1) (setID S1 B1))
                    (finset.setUC (S1 :\: B1) (S1 :&: B1)))
                  (etrans eqU11 eqU12)).
              }
              rewrite -(castlf_comp eqU11 eqU11 eqU12 eqU12).
              rewrite (sdotIf_cast_l eqA1 eqU11) castlf1.
              rewrite (sdotIf_cast_r eqB1 eqU12).
              done.
            }
              have Hlift2 :
                  D2 = ((\1 : 'F[H]_A2) \O sigmaB2 : 'F[H]_S2).
              {
              rewrite /D2 /sigmaB2.
              transitivity
                (castlf (etrans eqU21 eqU22, etrans eqU21 eqU22)
                  ((\1 : 'F[H]_(S2 :\: B2)) \O sigma2)).
              {
                by rewrite (eq_irrelevance
                  (eq_ind_r (eq^~ S2)
                    (eq_ind_r (eq^~ S2) (erefl S2) (setID S2 B2))
                    (finset.setUC (S2 :\: B2) (S2 :&: B2)))
                  (etrans eqU21 eqU22)).
              }
              rewrite -(castlf_comp eqU21 eqU21 eqU22 eqU22).
              rewrite (sdotIf_cast_l eqA2 eqU21) castlf1.
                rewrite (sdotIf_cast_r eqB2 eqU22).
                done.
              }
              have eqA12 :
                  (S1 :|: S2) :\: (B1 :|: B2) = A1 :|: A2.
              {
                apply/setP=> z.
                rewrite /S1 /S2 !inE.
                have A1notB1 : z \in A1 -> (z \in B1) = false.
                { move=> HzA1; apply/negP=> HzB1.
                  by move/disjointP: disA1B1 => /(_ _ HzA1);
                    rewrite HzB1. }
                have A2notB2 : z \in A2 -> (z \in B2) = false.
                { move=> HzA2; apply/negP=> HzB2.
                  by move/disjointP: disA2B2 => /(_ _ HzA2);
                    rewrite HzB2. }
                have A1notB2 : z \in A1 -> (z \in B2) = false.
                { move=> HzA1; apply/negP=> HzB2.
                  have HzS1 : z \in S1 by rewrite /S1 !inE HzA1.
                  by move/disjointP: disS1S2 => /(_ _ HzS1);
                    rewrite /S2 !inE HzB2 orbT. }
                have A2notB1 : z \in A2 -> (z \in B1) = false.
                { move=> HzA2; apply/negP=> HzB1.
                  have HzS1 : z \in S1 by rewrite /S1 !inE HzB1 orbT.
                  by move/disjointP: disS1S2 => /(_ _ HzS1);
                    rewrite /S2 !inE HzA2. }
                case HA1 : (z \in A1); case HB1 : (z \in B1);
                  case HA2 : (z \in A2); case HB2 : (z \in B2);
                  rewrite ?HA1 ?HB1 ?HA2 ?HB2 //=.
                all: try by move: (A1notB1 HA1); rewrite HB1.
                all: try by move: (A2notB2 HA2); rewrite HB2.
                all: try by move: (A1notB2 HA1); rewrite HB2.
                all: try by move: (A2notB1 HA2); rewrite HB1.
              }
              have eqS12 : (A1 :|: A2) :|: (B1 :|: B2) = S1 :|: S2.
              {
                apply/setP=> z.
                rewrite /S1 /S2 !inE.
                by case: (z \in A1); case: (z \in A2);
                  case: (z \in B1); case: (z \in B2).
              }
            have eqU121 :
                ((S1 :|: S2) :\: (B1 :|: B2)) :|:
                  ((S1 :|: S2) :&: (B1 :|: B2)) =
                (A1 :|: A2) :|:
                  ((S1 :|: S2) :&: (B1 :|: B2))
              by rewrite eqA12.
              have eqU122 :
                  (A1 :|: A2) :|:
                    ((S1 :|: S2) :&: (B1 :|: B2)) =
                  (A1 :|: A2) :|: (B1 :|: B2)
                by rewrite eqB12.
              have Hlift12 :
                  D12 =
                  castlf (eqS12, eqS12)
                    (((\1 : 'F[H]_(A1 :|: A2)) \O
                    (sigmaB1 \⊗ sigmaB2))).
            {
                rewrite /D12 /sigma12.
                transitivity
                  (castlf
                    (etrans (etrans eqU121 eqU122) eqS12,
                     etrans (etrans eqU121 eqU122) eqS12)
                    ((\1 : 'F[H]_((S1 :|: S2) :\: (B1 :|: B2))) \O
                      castlf (esym eqB12, esym eqB12)
                        (sigmaB1 \⊗ sigmaB2))).
              {
                by rewrite (eq_irrelevance
                  (eq_ind_r (eq^~ (S1 :|: S2))
                    (eq_ind_r (eq^~ (S1 :|: S2)) (erefl (S1 :|: S2))
                      (setID (S1 :|: S2) (B1 :|: B2)))
                      (finset.setUC ((S1 :|: S2) :\: (B1 :|: B2))
                        ((S1 :|: S2) :&: (B1 :|: B2))))
                    (etrans (etrans eqU121 eqU122) eqS12)).
                }
                rewrite -(castlf_comp (etrans eqU121 eqU122)
                  (etrans eqU121 eqU122) eqS12 eqS12).
                rewrite -(castlf_comp eqU121 eqU121 eqU122 eqU122).
                rewrite (sdotIf_cast_l eqA12 eqU121) castlf1.
                rewrite (sdotIf_cast_r eqB12 eqU122) castlfKV.
                done.
              }
            have Hregroup :
                castlf (eqS12, eqS12)
                  (((\1 : 'F[H]_(A1 :|: A2)) \O
                    (sigmaB1 \⊗ sigmaB2))) =
                (((\1 : 'F[H]_A1) \O sigmaB1 : 'F[H]_S1) \⊗
                  ((\1 : 'F[H]_A2) \O sigmaB2 : 'F[H]_S2)).
              {
                have disA12B12 : [disjoint A1 :|: A2 & B1 :|: B2].
                {
                  apply/disjointP=> z.
                  rewrite !inE.
                  have A1notB1 : z \in A1 -> (z \in B1) = false.
                  { move=> HzA1; apply/negP=> HzB1.
                    by move/disjointP: disA1B1 => /(_ _ HzA1);
                      rewrite HzB1. }
                  have A2notB2 : z \in A2 -> (z \in B2) = false.
                  { move=> HzA2; apply/negP=> HzB2.
                    by move/disjointP: disA2B2 => /(_ _ HzA2);
                      rewrite HzB2. }
                  have A1notB2 : z \in A1 -> (z \in B2) = false.
                  { move=> HzA1; apply/negP=> HzB2.
                    have HzS1 : z \in S1 by rewrite /S1 !inE HzA1.
                    by move/disjointP: disS1S2 => /(_ _ HzS1);
                      rewrite /S2 !inE HzB2 orbT. }
                  have A2notB1 : z \in A2 -> (z \in B1) = false.
                  { move=> HzA2; apply/negP=> HzB1.
                    have HzS1 : z \in S1 by rewrite /S1 !inE HzB1 orbT.
                    by move/disjointP: disS1S2 => /(_ _ HzS1);
                      rewrite /S2 !inE HzA2. }
                  case HA1 : (z \in A1); case HA2 : (z \in A2);
                    case HB1 : (z \in B1); case HB2 : (z \in B2);
                    rewrite ?HA1 ?HA2 ?HB1 ?HB2 //=.
                  all: try by move: (A1notB1 HA1); rewrite HB1.
                  all: try by move: (A2notB2 HA2); rewrite HB2.
                  all: try by move: (A1notB2 HA1); rewrite HB2.
                  all: try by move: (A2notB1 HA2); rewrite HB1.
                }
                rewrite (sdotF_to_tenF disA12B12
                  (\1 : 'F[H]_(A1 :|: A2)) (sigmaB1 \⊗ sigmaB2)).
                rewrite (sdotF_to_tenF disA1B1
                  (\1 : 'F[H]_A1) sigmaB1).
                rewrite (sdotF_to_tenF disA2B2
                  (\1 : 'F[H]_A2) sigmaB2).
                apply/to_Fnd_inj.
                rewrite Fnd_cast !to_Fnd_tenE.
                rewrite -tenF11.
                rewrite -tenFA.
                rewrite [(\1 \⊗ (sigmaB1 \⊗ sigmaB2))%FND]tenFA.
                rewrite [((to_Fnd (\1 : 'F[H]_A2)) \⊗
                  (to_Fnd sigmaB1))%FND]tenFC.
                by rewrite -tenFA tenFA.
              }
            by rewrite Hlift12 Hlift1 Hlift2.
          }
          have PD1 : D1 \is psdlf.
          {
            have -> : D1 = (D1 - rho1) + rho1 by rewrite subrK.
            exact: psdlfD Hdom1 Prho1.
          }
          have PD2 : D2 \is psdlf.
          {
            have -> : D2 = (D2 - rho2) + rho2 by rewrite subrK.
            exact: psdlfD Hdom2 Prho2.
          }
        have Hle1 : rho1 <= D1 by move: Hdom1; rewrite /D1 -lefE.
        have Hle2 : rho2 <= D2 by move: Hdom2; rewrite /D2 -lefE.
        rewrite HD12 -lefE.
        apply: (le_trans (lef_tenfl disS1S2 (psdlf_ge0 Prho2) Hle1)).
        exact: (lef_tenfr disS1S2 (psdlf_ge0 PD1) Hle2).
        + rewrite /sigma12 castlf_trlfE lftrace_tenf //.
          rewrite /sigmaB1 /sigmaB2 !castlf_trlfE.
          have Htr1_real : \Tr sigma1 \is Num.real :=
            ger0_real (psdlf_trlf Psigma1).
          have Htr2_real : \Tr sigma2 \is Num.real :=
            ger0_real (psdlf_trlf Psigma2).
          rewrite -(RRe_real Htr1_real) -(RRe_real Htr2_real) -realcM.
          by rewrite re_realid.
  }
    have Hupper : Phi12 <= Phi1 * Phi2.
    {
      have Hopt1 : phi_min_feasible B1 rho1 Phi1.
      {
        rewrite /Phi1.
        exact: (@phi_min_primal_attained R L H A1 B1 disA1B1 rho1 Prho1).
      }
      have Hopt2 : phi_min_feasible B2 rho2 Phi2.
      {
        rewrite /Phi2.
        exact: (@phi_min_primal_attained R L H A2 B2 disA2B2 rho2 Prho2).
      }
      have Hprod_feas :
          phi_min_feasible (B1 :|: B2) (rho1 \⊗ rho2) (Phi1 * Phi2).
      {
        exact: Htensor_primal_witness Hopt1 Hopt2.
      }
      rewrite /Phi12 /phi_min.
      have [_ Hlb] :=
        @phi_min_feasible_has_inf R L H (S1 :|: S2) (B1 :|: B2)
          (rho1 \⊗ rho2) Pprod.
      have Hlb' :
          lbound [set w : R |
            phi_min_feasible (B1 :|: B2) (rho1 \⊗ rho2) w]
            (inf [set w : R |
              phi_min_feasible (B1 :|: B2) (rho1 \⊗ rho2) w]).
      {
        exact: ge_inf Hlb.
      }
      exact: Hlb' _ Hprod_feas.
    }
    have Hlower : Phi1 * Phi2 <= Phi12.
    {
      pose D1 : set R := [set v : R | exists Y : 'F[H]_S1,
        [/\ Y \is psdlf,
            ptrace_castl disA1B1 Y <= (\1 : 'F[H]_B1) &
            v = @complex.Re R (\Tr (rho1 \o Y))]]%classic.
      pose D2 : set R := [set v : R | exists Y : 'F[H]_S2,
        [/\ Y \is psdlf,
            ptrace_castl disA2B2 Y <= (\1 : 'F[H]_B2) &
            v = @complex.Re R (\Tr (rho2 \o Y))]]%classic.
      have Hdual1 : Phi1 = sup D1.
      {
        rewrite /Phi1 /D1.
        exact: (@phi_min_dual R L H A1 B1 disA1B1 rho1 Prho1).
      }
      have Hdual2 : Phi2 = sup D2.
      {
        rewrite /Phi2 /D2.
        exact: (@phi_min_dual R L H A2 B2 disA2B2 rho2 Prho2).
      }
      have HD1_has_sup : has_sup D1.
      {
        split.
        - exists 0.
          exists (0 : 'F[H]_S1).
          split.
          + by rewrite psdlfE lexx.
          + rewrite /ptrace_castl /ptrace_cast_gen linear0 /= linear0.
            rewrite lefE subr0.
            by rewrite psdlfE; exact: lef01.
          + by rewrite comp_lfun0r linear0 raddf0.
        - exists Phi1 => v [Y [PY HY ->]].
          exact: (@phi_min_dual_feasible_ub R L H A1 B1 disA1B1
            rho1 Y Prho1 PY HY).
      }
      have HD2_has_sup : has_sup D2.
      {
        split.
        - exists 0.
          exists (0 : 'F[H]_S2).
          split.
          + by rewrite psdlfE lexx.
          + rewrite /ptrace_castl /ptrace_cast_gen linear0 /= linear0.
            rewrite lefE subr0.
            by rewrite psdlfE; exact: lef01.
          + by rewrite comp_lfun0r linear0 raddf0.
        - exists Phi2 => v [Y [PY HY ->]].
          exact: (@phi_min_dual_feasible_ub R L H A2 B2 disA2B2
            rho2 Y Prho2 PY HY).
      }
      have Hproduct_dual_bound :
          forall x y : R, D1 x -> D2 y -> x * y <= Phi12.
        {
          move=> x y [Y1 [PY1 HY1 ->]] [Y2 [PY2 HY2 ->]].
          pose Y12 : 'F[H]_(S1 :|: S2) := Y1 \⊗ Y2.
          have PY12 : Y12 \is psdlf.
          {
            rewrite /Y12 psdlfE.
            apply: tenf_ge0; first exact: disS1S2.
            - by move: PY1; rewrite psdlfE.
            - by move: PY2; rewrite psdlfE.
          }
          have eqSplit :
              ((S1 :|: S2) :\: (B1 :|: B2)) :|:
                ((S1 :|: S2) :&: (B1 :|: B2)) =
              S1 :|: S2
            by rewrite finset.setUC finset.setID.
          have disSplit :
              [disjoint ((S1 :|: S2) :\: (B1 :|: B2)) &
                ((S1 :|: S2) :&: (B1 :|: B2))].
          {
            setdec.
          }
          pose Y12s : 'F[H]_(((S1 :|: S2) :\: (B1 :|: B2)) :|:
              ((S1 :|: S2) :&: (B1 :|: B2))) :=
            castlf (esym eqSplit, esym eqSplit) Y12.
          have PY12s : Y12s \is psdlf
            by rewrite /Y12s castlf_psdlfE.
          have HptrY12 :
              ptrace_castl disSplit Y12s <=
                (\1 : 'F[H]_((S1 :|: S2) :&: (B1 :|: B2))).
          {
            have eqB12 :
                ((S1 :|: S2) :&: (B1 :|: B2)) = (B1 :|: B2).
            {
              apply/setP=> z.
              rewrite /S1 /S2 !inE.
              by case: (z \in B1); case: (z \in B2);
                rewrite ?orbT ?orbF ?andbT ?andbF.
            }
            have disB1B2 : [disjoint B1 & B2].
            {
              move: disS1S2.
              change ([disjoint (A1 :|: B1) & (A2 :|: B2)] ->
                [disjoint B1 & B2]).
              setdec.
            }
            have Hptr_prod :
                ptrace_castl disSplit Y12s =
                castlf (esym eqB12, esym eqB12)
                  (ptrace_castl disA1B1 Y1 \⊗
                    ptrace_castl disA2B2 Y2).
            {
              have eqA12 :
                  ((S1 :|: S2) :\: (B1 :|: B2)) = A1 :|: A2.
              {
                apply/setP=> z.
                rewrite /S1 /S2 !inE.
                have A1notB1 : z \in A1 -> (z \in B1) = false.
                { move=> HzA1; apply/negP=> HzB1.
                  by move/disjointP: disA1B1 => /(_ _ HzA1);
                    rewrite HzB1. }
                have A2notB2 : z \in A2 -> (z \in B2) = false.
                { move=> HzA2; apply/negP=> HzB2.
                  by move/disjointP: disA2B2 => /(_ _ HzA2);
                    rewrite HzB2. }
                have A1notB2 : z \in A1 -> (z \in B2) = false.
                { move=> HzA1; apply/negP=> HzB2.
                  have HzS1 : z \in S1 by rewrite /S1 !inE HzA1.
                  by move/disjointP: disS1S2 => /(_ _ HzS1);
                    rewrite /S2 !inE HzB2 orbT. }
                have A2notB1 : z \in A2 -> (z \in B1) = false.
                { move=> HzA2; apply/negP=> HzB1.
                  have HzS1 : z \in S1 by rewrite /S1 !inE HzB1 orbT.
                  by move/disjointP: disS1S2 => /(_ _ HzS1);
                    rewrite /S2 !inE HzA2. }
                case HA1 : (z \in A1); case HB1 : (z \in B1);
                  case HA2 : (z \in A2); case HB2 : (z \in B2);
                  rewrite ?HA1 ?HB1 ?HA2 ?HB2 //=.
                all: try by move: (A1notB1 HA1); rewrite HB1.
                all: try by move: (A2notB2 HA2); rewrite HB2.
                all: try by move: (A1notB2 HA1); rewrite HB2.
                all: try by move: (A2notB1 HA2); rewrite HB1.
              }
              have disA1A2 : [disjoint A1 & A2].
              {
                move: disS1S2.
                change ([disjoint (A1 :|: B1) & (A2 :|: B2)] ->
                  [disjoint A1 & A2]).
                setdec.
              }
              have disB1A2 : [disjoint B1 & A2].
              {
                move: disS1S2.
                change ([disjoint (A1 :|: B1) & (A2 :|: B2)] ->
                  [disjoint B1 & A2]).
                setdec.
              }
              have disA12B12 : [disjoint A1 :|: A2 & B1 :|: B2].
              {
                apply/disjointP=> z.
                rewrite !inE.
                have A1notB1 : z \in A1 -> (z \in B1) = false.
                { move=> HzA1; apply/negP=> HzB1.
                  by move/disjointP: disA1B1 => /(_ _ HzA1);
                    rewrite HzB1. }
                have A2notB2 : z \in A2 -> (z \in B2) = false.
                { move=> HzA2; apply/negP=> HzB2.
                  by move/disjointP: disA2B2 => /(_ _ HzA2);
                    rewrite HzB2. }
                have A1notB2 : z \in A1 -> (z \in B2) = false.
                { move=> HzA1; apply/negP=> HzB2.
                  have HzS1 : z \in S1 by rewrite /S1 !inE HzA1.
                  by move/disjointP: disS1S2 => /(_ _ HzS1);
                    rewrite /S2 !inE HzB2 orbT. }
                have A2notB1 : z \in A2 -> (z \in B1) = false.
                { move=> HzA2; apply/negP=> HzB1.
                  have HzS1 : z \in S1 by rewrite /S1 !inE HzB1 orbT.
                  by move/disjointP: disS1S2 => /(_ _ HzS1);
                    rewrite /S2 !inE HzA2. }
                case HA1 : (z \in A1); case HA2 : (z \in A2);
                  case HB1 : (z \in B1); case HB2 : (z \in B2);
                  rewrite ?HA1 ?HA2 ?HB1 ?HB2 //=.
                all: try by move: (A1notB1 HA1); rewrite HB1.
                all: try by move: (A2notB2 HA2); rewrite HB2.
                all: try by move: (A1notB2 HA1); rewrite HB2.
                all: try by move: (A2notB1 HA2); rewrite HB1.
              }
              have eqSplitAB :
                  ((S1 :|: S2) :\: (B1 :|: B2)) :|:
                    ((S1 :|: S2) :&: (B1 :|: B2)) =
                  (A1 :|: A2) :|: (B1 :|: B2)
                by rewrite eqA12 eqB12.
              rewrite /Y12s /Y12.
              clear PY12s Y12s PY12 Y12.
              rewrite -[Y1 \⊗ Y2](sdotF_to_tenF disS1S2 Y1 Y2).
              rewrite -[(ptrace_castl disA1B1 Y1 \⊗
                ptrace_castl disA2B2 Y2)]
                (sdotF_to_tenF disB1B2).
              have Hbasis (i j : 'Idx[H]_S1) (k l : 'Idx[H]_S2) :
                  ptrace_castl disSplit
                    (castlf (esym eqSplit, esym eqSplit)
                      (([> deltav i ; deltav j <] \O
                        [> deltav k ; deltav l <]) :
                        'F[H]_(S1 :|: S2))) =
                  castlf (esym eqB12, esym eqB12)
                    (ptrace_castl disA1B1 [> deltav i ; deltav j <] \O
                      ptrace_castl disA2B2 [> deltav k ; deltav l <]).
              {
                pose xA1 : 'F[H]_A1 :=
                  [> deltav (idxSl i) ; deltav (idxSl j) <].
                pose xB1 : 'F[H]_B1 :=
                  [> deltav (idxSr i) ; deltav (idxSr j) <].
                pose xA2 : 'F[H]_A2 :=
                  [> deltav (idxSl k) ; deltav (idxSl l) <].
                pose xB2 : 'F[H]_B2 :=
                  [> deltav (idxSr k) ; deltav (idxSr l) <].
                have HY1_split :
                    [> deltav i ; deltav j <] =
                    (xA1 \O xB1 : 'F[H]_S1).
                {
                  apply: to_Fnd_inj.
                  by rewrite /xA1 /xB1 !dv_split -tenf_outp
                    to_Fnd_tenE (sdotFT _ _ disA1B1).
                }
                have HY2_split :
                    [> deltav k ; deltav l <] =
                    (xA2 \O xB2 : 'F[H]_S2).
                {
                  apply: to_Fnd_inj.
                  by rewrite /xA2 /xB2 !dv_split -tenf_outp
                    to_Fnd_tenE (sdotFT _ _ disA2B2).
                }
                case: ((S1 :|: S2) :\: (B1 :|: B2)) / (esym eqA12)
                  in disSplit eqSplit eqSplitAB *.
                have Hregroup :
                    castlf (esym eqSplit, esym eqSplit)
                      (((xA1 \O xB1) \O (xA2 \O xB2)) :
                        'F[H]_(S1 :|: S2)) =
                    castlf (esym eqSplitAB, esym eqSplitAB)
                      (((xA1 \O xA2) \O (xB1 \O xB2)) :
                        'F[H]_((A1 :|: A2) :|: (B1 :|: B2))).
                {
                  rewrite (sdotF_to_tenF disS1S2
                    (xA1 \O xB1) (xA2 \O xB2)).
                  rewrite (sdotF_to_tenF disA1B1 xA1 xB1).
                  rewrite (sdotF_to_tenF disA2B2 xA2 xB2).
                  rewrite (sdotF_to_tenF disA12B12
                    (xA1 \O xA2) (xB1 \O xB2)).
                  rewrite (sdotF_to_tenF disA1A2 xA1 xA2).
                  rewrite (sdotF_to_tenF disB1B2 xB1 xB2).
                  apply: to_Fnd_inj.
                  rewrite !Fnd_cast !to_Fnd_tenE.
                  rewrite -[in RHS]tenFA.
                  rewrite [((to_Fnd xA2) \⊗
                    ((to_Fnd xB1) \⊗ (to_Fnd xB2)))%FND]tenFA.
                  rewrite [((to_Fnd xA2) \⊗ (to_Fnd xB1))%FND]tenFC.
                  rewrite -[in RHS]tenFA.
                  by rewrite [in RHS]tenFA.
                }
                rewrite HY1_split HY2_split Hregroup; clear Hregroup.
                case: ((S1 :|: S2) :&: (B1 :|: B2)) / (esym eqB12)
                  in disSplit eqSplitAB *.
                rewrite (eq_irrelevance eqSplitAB erefl) castlf_id.
                rewrite (eq_irrelevance disSplit disA12B12).
                rewrite ptrace_castl_sdot_trace_l.
                rewrite ptrace_castl_sdot_trace_l.
                  rewrite ptrace_castl_sdot_trace_l.
                  rewrite lftrace_sdot_disj //.
                  by rewrite sdotfZl sdotfZr scalerA.
                }
                have Hleft_suml (I0 : finType) (P : pred I0)
                    (F : I0 -> 'F[H]_S1) (Z : 'F[H]_S2) :
                    ptrace_castl disSplit
                      (castlf (esym eqSplit, esym eqSplit)
                        (((\sum_(i | P i) F i) \O Z) :
                          'F[H]_(S1 :|: S2))) =
                    \sum_(i | P i)
                      ptrace_castl disSplit
                        (castlf (esym eqSplit, esym eqSplit)
                          (F i \O Z : 'F[H]_(S1 :|: S2))).
                {
                  rewrite sdotf_suml /ptrace_castl /ptrace_cast_gen.
                    by rewrite raddf_sum /= raddf_sum /= raddf_sum.
                }
                have Hleft_sumr (I0 : finType) (P : pred I0)
                    (X : 'F[H]_S1) (F : I0 -> 'F[H]_S2) :
                    ptrace_castl disSplit
                      (castlf (esym eqSplit, esym eqSplit)
                        (X \O (\sum_(i | P i) F i) :
                          'F[H]_(S1 :|: S2))) =
                    \sum_(i | P i)
                      ptrace_castl disSplit
                        (castlf (esym eqSplit, esym eqSplit)
                          (X \O F i : 'F[H]_(S1 :|: S2))).
                {
                  rewrite sdotf_sumr /ptrace_castl /ptrace_cast_gen.
                    by rewrite raddf_sum /= raddf_sum /= raddf_sum.
                }
                have Hright_suml (I0 : finType) (P : pred I0)
                    (F : I0 -> 'F[H]_S1) (Z : 'F[H]_B2) :
                    castlf (esym eqB12, esym eqB12)
                      (ptrace_castl disA1B1 (\sum_(i | P i) F i) \O Z) =
                    \sum_(i | P i)
                      castlf (esym eqB12, esym eqB12)
                        (ptrace_castl disA1B1 (F i) \O Z).
                {
                  rewrite /ptrace_castl /ptrace_cast_gen.
                  rewrite raddf_sum /= linear_sum /=.
                  by rewrite sdotf_suml linear_sum.
                }
                have Hright_sumr (I0 : finType) (P : pred I0)
                    (Z : 'F[H]_B1) (F : I0 -> 'F[H]_S2) :
                    castlf (esym eqB12, esym eqB12)
                      (Z \O ptrace_castl disA2B2 (\sum_(i | P i) F i)) =
                    \sum_(i | P i)
                      castlf (esym eqB12, esym eqB12)
                        (Z \O ptrace_castl disA2B2 (F i)).
                {
                  rewrite /ptrace_castl /ptrace_cast_gen.
                  rewrite raddf_sum /= linear_sum /=.
                  by rewrite sdotf_sumr linear_sum.
                }
                have Hleft_Zl (c : C) (X : 'F[H]_S1) (Z : 'F[H]_S2) :
                    ptrace_castl disSplit
                      (castlf (esym eqSplit, esym eqSplit)
                        ((c *: X) \O Z : 'F[H]_(S1 :|: S2))) =
                    c *: ptrace_castl disSplit
                      (castlf (esym eqSplit, esym eqSplit)
                        (X \O Z : 'F[H]_(S1 :|: S2))).
                {
                    rewrite sdotfZl /ptrace_castl /ptrace_cast_gen.
                    rewrite [castlf (esym eqSplit, esym eqSplit) (c *: _)]linearZ /=.
                    rewrite [\Tr_((S1 :|: S2) :\: (B1 :|: B2)) (c *: _)]linearZ /=.
                    by rewrite linearZ.
                }
                have Hleft_Zr (c : C) (X : 'F[H]_S1) (Z : 'F[H]_S2) :
                    ptrace_castl disSplit
                      (castlf (esym eqSplit, esym eqSplit)
                        (X \O (c *: Z) : 'F[H]_(S1 :|: S2))) =
                    c *: ptrace_castl disSplit
                      (castlf (esym eqSplit, esym eqSplit)
                        (X \O Z : 'F[H]_(S1 :|: S2))).
                {
                    rewrite sdotfZr /ptrace_castl /ptrace_cast_gen.
                    rewrite [castlf (esym eqSplit, esym eqSplit) (c *: _)]linearZ /=.
                    rewrite [\Tr_((S1 :|: S2) :\: (B1 :|: B2)) (c *: _)]linearZ /=.
                    by rewrite linearZ.
                }
                have Hright_Zl (c : C) (X : 'F[H]_S1) (Z : 'F[H]_B2) :
                    castlf (esym eqB12, esym eqB12)
                      (ptrace_castl disA1B1 (c *: X) \O Z) =
                    c *: castlf (esym eqB12, esym eqB12)
                      (ptrace_castl disA1B1 X \O Z).
                {
                  case: ((S1 :|: S2) :&: (B1 :|: B2)) / (esym eqB12).
                  rewrite !castlf_id.
                  rewrite /ptrace_castl /ptrace_cast_gen.
                  rewrite [\Tr_(A1) (c *: _)]linearZ /=.
                  rewrite [castlf _ (c *: _)]linearZ /=.
                  by rewrite sdotfZl.
                }
                have Hright_Zr (c : C) (Z : 'F[H]_B1) (X : 'F[H]_S2) :
                    castlf (esym eqB12, esym eqB12)
                      (Z \O ptrace_castl disA2B2 (c *: X)) =
                    c *: castlf (esym eqB12, esym eqB12)
                      (Z \O ptrace_castl disA2B2 X).
                {
                  case: ((S1 :|: S2) :&: (B1 :|: B2)) / (esym eqB12).
                  rewrite !castlf_id.
                  rewrite /ptrace_castl /ptrace_cast_gen.
                  rewrite [\Tr_(A2) (c *: _)]linearZ /=.
                  rewrite [castlf _ (c *: _)]linearZ /=.
                  by rewrite sdotfZr.
                }
                rewrite (onb_lfun2id deltav Y1) (onb_lfun2id deltav Y2).
                rewrite Hleft_suml Hright_suml.
                apply: eq_bigr=> i _.
                rewrite Hleft_suml Hright_suml.
                apply: eq_bigr=> j _.
                rewrite Hleft_Zl Hright_Zl.
                congr (_ *: _).
                rewrite Hleft_sumr Hright_sumr.
                apply: eq_bigr=> k _.
                rewrite Hleft_sumr Hright_sumr.
                apply: eq_bigr=> l _.
                by rewrite Hleft_Zr Hright_Zr Hbasis.
            }
            rewrite Hptr_prod.
            have HId_cast :
                (\1 : 'F[H]_((S1 :|: S2) :&: (B1 :|: B2))) =
                castlf (esym eqB12, esym eqB12)
                  ((\1 : 'F[H]_B1) \⊗ (\1 : 'F[H]_B2)).
            {
              by rewrite tenf11 castlf1.
            }
            rewrite HId_cast lefE -castlf_sub castlf_psdlfE -lefE.
            apply: (le_trans (lef_tenfl disB1B2
              (psdlf_ge0 (ptrace_castl_psdlf disA2B2 PY2)) HY1)).
            apply: (lef_tenfr disB1B2 _ HY2).
            exact: lef01.
          }
          rewrite /Phi12 /phi_min.
          apply: lb_le_inf.
          - by have [Hne _] :=
              @phi_min_feasible_has_inf R L H (S1 :|: S2) (B1 :|: B2)
                (rho1 \⊗ rho2) Pprod.
          - move=> v [sigma [Psigma [Hgap ->]]].
          have Hrho_le_lift :
              rho1 \⊗ rho2 <=
              castlf (eqSplit, eqSplit)
                ((\1 : 'F[H]_((S1 :|: S2) :\: (B1 :|: B2))) \O sigma).
          {
            move: Hgap; rewrite lefE.
            by rewrite (eq_irrelevance
              (eq_ind_r (eq^~ (S1 :|: S2))
                (eq_ind_r (eq^~ (S1 :|: S2)) (erefl (S1 :|: S2))
                  (setID (S1 :|: S2) (B1 :|: B2)))
                (finset.setUC ((S1 :|: S2) :\: (B1 :|: B2))
                  ((S1 :|: S2) :&: (B1 :|: B2))))
              eqSplit).
          }
          have HrhoY_le : \Tr ((rho1 \⊗ rho2) \o Y12) <=
              \Tr ((castlf (eqSplit, eqSplit)
                ((\1 : 'F[H]_((S1 :|: S2) :\: (B1 :|: B2))) \O sigma))
                \o Y12).
          {
            move/lef_psdtr: Hrho_le_lift => /(_ Y12 PY12).
            exact.
          }
          have Hlift_trace :
              \Tr ((castlf (eqSplit, eqSplit)
                ((\1 : 'F[H]_((S1 :|: S2) :\: (B1 :|: B2))) \O sigma))
                \o Y12) =
              \Tr ((ptrace_castl disSplit Y12s) \o sigma).
          {
            rewrite lftraceC.
            have HY12_cast : castlf (eqSplit, eqSplit) Y12s = Y12.
            { by rewrite /Y12s castlfKV. }
            rewrite -HY12_cast.
            rewrite -castlf_complf castlf_trlfE.
            by rewrite trlf_lift_partial.
          }
          have Hptr_le : \Tr ((ptrace_castl disSplit Y12s) \o sigma) <=
              \Tr ((\1 : 'F[H]_((S1 :|: S2) :&: (B1 :|: B2))) \o sigma).
          {
            move/lef_psdtr: HptrY12 => /(_ sigma Psigma).
            exact.
          }
          have Hbound :
              @complex.Re R (\Tr ((rho1 \⊗ rho2) \o Y12)) <=
              @complex.Re R (\Tr sigma).
          {
            have HrhoY_leR :
                @complex.Re R (\Tr ((rho1 \⊗ rho2) \o Y12)) <=
                @complex.Re R (\Tr ((castlf (eqSplit, eqSplit)
                  ((\1 : 'F[H]_((S1 :|: S2) :\: (B1 :|: B2))) \O sigma))
                  \o Y12)).
            {
              move: HrhoY_le.
              rewrite lecE /= => /andP[_].
              exact.
            }
            have Hptr_leR :
                @complex.Re R (\Tr ((ptrace_castl disSplit Y12s) \o sigma)) <=
                @complex.Re R (\Tr sigma).
            {
              move: Hptr_le.
              rewrite comp_lfun1l lecE /= => /andP[_].
              exact.
            }
            apply: (le_trans HrhoY_leR).
            by rewrite Hlift_trace.
          }
          have Htr_prod :
              \Tr ((rho1 \⊗ rho2) \o (Y1 \⊗ Y2)) =
              \Tr (rho1 \o Y1) * \Tr (rho2 \o Y2).
          {
            by rewrite -tenf_comp ?disS1S2 // lftrace_tenf.
          }
          have Htr1_real : \Tr (rho1 \o Y1) \is Num.real :=
            ger0_real (psdlf_TrM Prho1 PY1).
          have Htr2_real : \Tr (rho2 \o Y2) \is Num.real :=
            ger0_real (psdlf_TrM Prho2 PY2).
          have Hobj_factor :
              @complex.Re R (\Tr ((rho1 \⊗ rho2) \o Y12)) =
              @complex.Re R (\Tr (rho1 \o Y1)) *
                @complex.Re R (\Tr (rho2 \o Y2)).
          {
            rewrite /Y12 Htr_prod.
            rewrite -(RRe_real Htr1_real) -(RRe_real Htr2_real) -realcM.
            by rewrite re_realid.
          }
          by rewrite -Hobj_factor.
        }
      have Hsup_product : sup D1 * sup D2 <= Phi12.
      {
        have HsupD2_ge0 : 0 <= sup D2 by rewrite -Hdual2.
        case: (eqVneq (sup D2) 0) => [HsupD2_eq0|HsupD2_neq0].
        - by rewrite HsupD2_eq0 mulr0.
        - have HsupD2_pos : 0 < sup D2.
          {
            rewrite lt_def HsupD2_ge0 andbT.
            by apply/negP=> /eqP H0; move: HsupD2_neq0; rewrite H0 eqxx.
          }
          rewrite -(@ler_pdivlMr R (sup D2) (sup D1) Phi12) //.
          apply: ExtNumTopology.sup_least_ubound; first exact: HD1_has_sup.
          apply/ubP=> x Hx.
          case: (leP x 0) => [Hx_le0|Hx_pos].
          + apply: le_trans Hx_le0 _.
            by rewrite divr_ge0 // ltW.
          + rewrite leNgt.
            apply/negP=> Hx_gt.
              have Heps_pos : 0 < sup D2 - Phi12 / x.
              {
                have HPhi_lt_xsup : Phi12 < x * sup D2.
                {
                  by move: Hx_gt; rewrite ltr_pdivrMr // mulrC.
                }
                rewrite subr_gt0.
                rewrite ltr_pdivrMr // mulrC.
                exact: HPhi_lt_xsup.
              }
              have [y Hy Hy_gt] := sup_adherent Heps_pos HD2_has_sup.
              rewrite subKr in Hy_gt.
              have HPhi_lt_xy : Phi12 < x * y.
              {
                move: Hy_gt.
                rewrite ltr_pdivrMr //.
                by rewrite mulrC.
              }
            move: (Hproduct_dual_bound x y Hx Hy).
            by rewrite leNgt HPhi_lt_xy.
      }
      by rewrite -Hdual1 -Hdual2 in Hsup_product.
    }
  apply/eqP; rewrite eq_le.
  exact/andP.
Qed.

End PhiMinTensorProduct.

End FvqkdReal.
