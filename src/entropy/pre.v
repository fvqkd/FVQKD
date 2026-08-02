(* -------------------------------------------------------------------- *)
(* pre.v — Stinespring dilation + purification existence                 *)
(* -------------------------------------------------------------------- *)
(* Module: entropy.pre                              *)
(* Source: Tomamichel, 'A Framework for Non-Asymptotic Quantum          *)
(*   Information Theory' (PhD thesis, arXiv:1203.2142).                  *)
(*   Lemma 2.4 (Stinespring Dilation) — tex lm:stinespring;             *)
(*   purification existence (Sec. 2.2.2, unnumbered para) — tex "purification". *)
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
  cpo mxpred extnum ctopology svd mxnorm hspace autonat.
From quantum.dirac Require Import hstensor.

Import Order.TTheory GRing.Theory Num.Theory Num.Def MxLownerOrder.
Import VectorInternalTheory.

(* --- FVQKD imports --- *)
From utils Require Import exports.
From entropy Require Import def.

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
(* Purification existence. Tomamichel, 'A Framework for Non-Asymptotic *)
(*   Quantum Information Theory' (PhD thesis, arXiv:1203.2142), Sec.    *)
(*   2.2.2 (unnumbered paragraph) — tex "purification".                *)
(* math: For any state ρ_A of a system A, there exists a purification  *)
(*   |ρ⟩ ∈ ℋ_{AA'} of the joint system AA' with Tr_{A'}(|ρ⟩⟨ρ|) = ρ_A. *)
(*   The auxiliary system A' is taken isomorphic to A.                  *)
(* Formal statement (labeled operator form): for disjoint labels A, A', *)
(*   any normalized state ρ_A has a pure normalized extension           *)
(*   phi ∈ 'F_{A ∪ A'} with ptrace_cast giving back ρ_A, assuming       *)
(*   dim(H_A) = dim(H_A').                                              *)
(* ================================================================== *)

Section PurificationExists.
Variable (L : finType) (HL : L -> chsType) (A A' : L).
Hypothesis disAA' : [disjoint [set A] & [set A']].
Notation S_AA' := ([set A] :|: [set A']).

(* path: entropy:purification_exists -> entropy:entropy_data_proc -> *)
(*   bb84:bb84_secret *)
Lemma purification_exists (rho : 'F[HL]_[set A]) :
  rho \is den1lf ->
  dim (HL A) = dim (HL A') ->
  exists (phi : 'F[HL]_S_AA'),
    phi \is den1lf /\
    \Rank phi = 1%N /\
    ptrace_cast disAA' phi = rho.
Proof.
  move=> Hrho_den1 HdimAA'.
  have HdimAA'_set : dim 'H[HL]_[set A] = dim 'H[HL]_[set A'] :=
    etrans (esym (@dim_set1 R L HL A)) (etrans HdimAA' (@dim_set1 R L HL A')).
  have Hrho_mx_den1 : h2mx rho \is den1mx by move: Hrho_den1; rewrite qualifE.
  have Hrho_mx_den : h2mx rho \is denmx := den1mx_den Hrho_mx_den1.
  have Hrho_mx_nz : h2mx rho != 0.
  {
    apply/eqP => Hrho0.
    by move/den1mxP: Hrho_mx_den1 => [_ /eqP];
      rewrite Hrho0 linear0 => /eqP; rewrite eq_sym oner_eq0.
  }
  have Hrho_rankA' : (\rank (h2mx rho) <= dim 'H[HL]_[set A'])%N.
  {
    rewrite -HdimAA'_set.
    exact: rank_leq_row.
  }
  have [theta0 [Htheta0_den [Htheta0_rank Htheta0_ptrace]]] :=
    purification_exists_in_dim Hrho_mx_den Hrho_mx_nz Hrho_rankA'.
  have Htheta0_den1 : theta0 \is den1mx.
  {
    apply/den1mxP; split.
    - exact: denmx_psd Htheta0_den.
    - apply/eqP.
      rewrite tr_ptrace2 Htheta0_ptrace.
      by case/den1mxP: Hrho_mx_den1 => _ /eqP ->.
  }
  pose U := @tenv_mxU R _ HL [set A] [set A'].
  have HU : U \is unitarymx := tenv_mxU_unitarymx _ _.
  have HUadj : U^*t \is unitarymx := tenv_mxU_adj_unitarymx disAA'.
  have Uadj_mul_U : U^*t *m U = 1%:M.
  { by have := unitarymxK HUadj; rewrite adjmxK. }
  pose phi : 'F[HL]_([set A] :|: [set A']) := mx2h (U *m theta0 *m U^*t).
  have Htheta0_psd : theta0 \is psdmx by move/denmxP: Htheta0_den => [].
  have Hphi_h2mx : h2mx phi = U *m theta0 *m U^*t
    by rewrite /phi mx2hK.
  have Hphi_mx_psd : h2mx phi \is psdmx.
  { by rewrite Hphi_h2mx; exact: psdmx_bimap_closed_gen Htheta0_psd. }
  have Hphi_den1 : phi \is den1lf.
  {
    apply/den1lfP; split.
    - by move: Hphi_mx_psd; rewrite qualifE.
    - apply/eqP.
      rewrite /lftrace /= Hphi_h2mx mxtrace_mulC mulmxA Uadj_mul_U mul1mx.
      by case/den1mxP: Htheta0_den1 => _ /eqP ->.
  }
  have Hphi_rank : \Rank phi = 1%N.
  {
    rewrite /lfrank Hphi_h2mx mxrank_mulmxU // -[U]adjmxK.
    by rewrite mxrank_mulUCmx // Htheta0_rank.
  }
  have Hphi_ptrace : ptrace_cast disAA' phi = rho.
  {
    apply/h2mx_inj.
    rewrite (h2mx_ptrace_cast_ptrace2 disAA' phi).
    rewrite Hphi_h2mx !mulmxA Uadj_mul_U mul1mx -mulmxA Uadj_mul_U mulmx1.
    exact: Htheta0_ptrace.
  }
  by exists phi; repeat split.
Qed.

End PurificationExists.

(* Stinespring dilation (lm:stinespring) and fidelity monotonicity under   *)
(* TP-CPMs (tb:fid item ii) are provided by utils.dist.dilation as     *)
(* generic matrix-level quantum-channel primitives, and are visible        *)
(* here via `utils Require Import exports`.                             *)

(* ================================================================== *)
(* SDP strong duality, primal Slater branch                            *)
(* Tomamichel, 'A Framework for Non-Asymptotic Quantum Information     *)
(*   Theory' (PhD thesis, arXiv:1203.2142), Theorem 2.6 (Strong        *)
(*   Duality), first formula — tex th:sdp/strong.                      *)
(* Tex statement: if α is finite and there exists Y > 0 with Ψ†[Y] < A, *)
(*   then α = β and there exists a primal feasible X attaining α.      *)
(* In the live Coq surface, α and β are the etinf / etsup of the       *)
(* primal / dual feasible-value sets below, and "α is finite" is       *)
(* recorded by `has_inf sdp_primal_set`.                               *)
(* Tomamichel's SDP definition also assumes that Ψ preserves Hermiticity;   *)
(* we expose that as a theorem premise below.                          *)
(* The strict witness condition is encoded as                           *)
(*   `Y \is pdmx /\ (A - Ψ†[Y]) \is pdmx`,                              *)
(* i.e. Y > 0 and A - Ψ†[Y] > 0 in the positive-definite sense.         *)
(* ================================================================== *)

Section SDPStrongPrimal.

Variables (U V : chsType).
Variables (A : 'M[C]_(dim U)) (B : 'M[C]_(dim V)).
Variable (Psi : 'SO(U, V)).

Local Notation sdp_primal_set := (@sdp_primal_set R U V A B Psi).
Local Notation sdp_dual_set := (@sdp_dual_set R U V A B Psi).

(* Reusable finite-dimensional conic Farkas/separation theorem for the
   primal SDP epigraph cone.  This is the only abstract convex-analysis
   input needed by `sdp_strong_primal`; the rest of the strong-duality
   proof below is matrix algebra, weak duality, and compactness. *)
(* path: entropy:sdp_primal_farkas_separator -> entropy:sdp_strong_primal -> *)
(*   entropy:min_koenig -> entropy:min_omni -> entropy:minmax_dual -> *)
(*   entropy:smooth_iso_hmax -> entropy:entropy_data_proc -> *)
(*   bb84:bb84_secret *)
Lemma sdp_primal_farkas_separator (gamma : R) :
  A \is hermmx ->
  B \is hermmx ->
  (forall X : 'M[C]_(dim U),
      X \is hermmx -> h2mx (Psi (mx2h X)) \is hermmx) ->
  (exists Y0 : 'M[C]_(dim V),
      Y0 \is pdmx /\ (A - h2mx (Psi^*o (mx2h Y0))) \is pdmx) ->
  (~ exists X : 'M[C]_(dim U),
      [/\ X \is psdmx,
          h2mx (Psi (mx2h X)) >= B &
          @complex.Re R (\tr (A *m X)) <= gamma]) ->
  exists (Z : 'M[C]_(dim U)) (Y : 'M[C]_(dim V)) (t : R),
    [/\ 0 < t,
        Z \is psdmx,
        Y \is psdmx,
        t%:C *: A =
          h2mx (Psi^*o (mx2h Y)) + Z &
        t * gamma < @complex.Re R (\tr (B *m Y))].
Proof.
  move=> HA HB HPsi_herm [Y0 [HY0pd HS0pd]] Hprimal_infeasible.

  (* Block 1: encode the primal epigraph cone whose excluded point is
     `(B, gamma)`. *)
  pose cone_member (w : 'M[C]_(dim V) * R) :=
    exists (X : 'M[C]_(dim U)) (S : 'M[C]_(dim V)) (r : R),
      [/\ X \is psdmx,
          S \is psdmx,
          0 <= r,
          w.1 = h2mx (Psi (mx2h X)) - S &
          w.2 = @complex.Re R (\tr (A *m X)) + r].
  pose p : 'M[C]_(dim V) * R := (B, gamma).

  (* Block 2: the hypothesis says exactly that the point `(B, gamma)` is
     outside the cone. *)
  have Hp_not_cone : ~ cone_member p.
  {
    move=> [X [S [r [PX PS Hr Hp1 Hp2]]]].
    apply: Hprimal_infeasible.
    exists X.
    split.
    - exact: PX.
    - rewrite le_lownerE.
      have Hgap : h2mx (Psi (mx2h X)) - B = S.
      {
        move: Hp1.
        rewrite /p /= => Hp1.
        by rewrite Hp1 subKr.
      }
      by rewrite Hgap.
    - move: Hp2.
      rewrite /p /= => Hgamma.
      rewrite Hgamma.
      by rewrite lerDl.
  }

  (* Block 3: finite-dimensional closed conic separation.  This is the
     only non-elementary convex-analysis step: closedness uses the strict
     Slater witness `Y0 > 0` and `A - Psi^*[Y0] > 0` to bound escaping
     primal directions. *)
  have Hseparator :
      exists (Z : 'M[C]_(dim U)) (Y : 'M[C]_(dim V)) (t : R),
        [/\ 0 < t,
            Z \is psdmx,
            Y \is psdmx,
            t%:C *: A =
              h2mx (Psi^*o (mx2h Y)) + Z &
            t * gamma < @complex.Re R (\tr (B *m Y))].
  {
    (* First separate the cone with a nonnegative scalar.  The remaining
       code in this block turns the nonnegative scalar into a positive one
       using the strict Slater witness. *)
    have Hraw_separator :
        exists (Z : 'M[C]_(dim U)) (Y : 'M[C]_(dim V)) (t : R),
          [/\ 0 <= t,
              Z \is psdmx,
              Y \is psdmx,
              t%:C *: A =
                h2mx (Psi^*o (mx2h Y)) + Z &
              t * gamma < @complex.Re R (\tr (B *m Y))].
    {
      have Hself_dual :
          forall n (M : 'M[C]_n),
            M \is hermmx ->
            (forall H : 'M[C]_n, H \is psdmx ->
              0 <= @complex.Re R (\tr (H *m M))) ->
            M \is psdmx.
      {
        move=> n M HM Hpos.
        have Hle : (0 : 'M[C]_n) <= M.
        {
          apply/le_lownerE_psdtr => X PX.
          rewrite mul0mx mxtrace0 mxtrace_mulC.
          have Hreal : \tr (X *m M) \is Num.real.
          {
            apply/CrealP.
            rewrite -mxtrace_adj adjmxM.
            have /hermmxP ME := HM.
            have /hermmxP XE := psdmx_herm PX.
            by rewrite -ME -XE mxtrace_mulC.
          }
          have HposX : 0 <= @complex.Re R (\tr (X *m M)) := Hpos X PX.
          have HposC : (0 : C) <= (@complex.Re R (\tr (X *m M)))%:C.
          {
            by rewrite ler0c.
          }
          by rewrite -(RRe_real Hreal).
        }
        by move: Hle; rewrite le_lownerE subr0.
      }
      pose Zlin (Y : 'M[C]_(dim V)) (t : R) :=
        t%:C *: A - h2mx (Psi^*o (mx2h Y)).
      pose dual_nonneg (Y : 'M[C]_(dim V)) :=
        forall S : 'M[C]_(dim V), S \is psdmx ->
          0 <= @complex.Re R (\tr (S *m Y)).
      pose station_nonneg (Y : 'M[C]_(dim V)) (t : R) :=
        forall X : 'M[C]_(dim U), X \is psdmx ->
          0 <= @complex.Re R (\tr (X *m Zlin Y t)).
      have HPsi_dual_herm :
          forall Y : 'M[C]_(dim V),
            Y \is hermmx ->
            h2mx (Psi^*o (mx2h Y)) \is hermmx.
      {
        move=> Y HY.
        apply/hermmx_dot=> u.
        pose X := u *m u^*t.
        have HXpsd : X \is psdmx.
        {
          exact: form_psd.
        }
        have HpsiX_herm : h2mx (Psi (mx2h X)) \is hermmx.
        {
          exact: HPsi_herm (psdmx_herm HXpsd).
        }
        have Hpair :
            \tr (h2mx (Psi^*o (mx2h Y)) *m X) =
            \tr (h2mx (Psi (mx2h X)) *m Y).
        {
          move: (dualso_trlfEV Psi (mx2h X) (mx2h Y)).
          rewrite /lftrace !h2mx_comp !mx2hK mxtrace_mulC.
          by [].
        }
        have Hquad :
            \tr (u^*t *m h2mx (Psi^*o (mx2h Y)) *m u) =
            \tr (h2mx (Psi (mx2h X)) *m Y).
        {
          rewrite -mulmxA mxtrace_mulC.
          by rewrite -mulmxA -/X Hpair.
        }
        rewrite Hquad.
        apply/CrealP.
        rewrite -mxtrace_adj adjmxM.
        have /hermmxP YE := HY.
        have /hermmxP PE := HpsiX_herm.
        by rewrite -YE -PE mxtrace_mulC.
      }
      have Hlinear_separator :
          exists (Y : 'M[C]_(dim V)) (t : R),
            [/\ 0 <= t,
                Y \is hermmx,
                Zlin Y t \is hermmx,
                dual_nonneg Y &
                [/\ station_nonneg Y t &
                    t * gamma < @complex.Re R (\tr (B *m Y))]].
      {
        have Hconic_separation :
            exists (Y : 'M[C]_(dim V)) (t : R),
              [/\ Y \is hermmx,
                  Zlin Y t \is hermmx,
                  (forall w : 'M[C]_(dim V) * R, cone_member w ->
                    @complex.Re R (\tr (Y *m w.1)) - t * w.2 <= 0) &
                  0 < @complex.Re R (\tr (Y *m B)) - t * gamma].
        {
          (* Cone algebra: zero, addition, and nonnegative real scaling. *)
          have HRe_realM : forall (c : R) (z : C),
              @complex.Re R (c%:C * z) = c * @complex.Re R z.
          {
            move=> c z.
            case: z => a b /=.
            by rewrite mul0r subr0.
          }
          have Hcone0 : cone_member (0, 0).
          {
            exists 0, 0, 0.
            split.
            - exact: psdmx0.
            - exact: psdmx0.
            - exact: lexx.
            - have HPsi0 : Psi 0 = 0 by rewrite linear0.
              by rewrite mx2h0 HPsi0 h2mx0 subr0.
            - by rewrite mulmx0 mxtrace0 addr0.
          }
          have HconeD :
              forall u v : 'M[C]_(dim V) * R,
                cone_member u -> cone_member v ->
                cone_member (u.1 + v.1, u.2 + v.2).
          {
            move=> u v [Xu [Su [ru [PXu PSu Hru Hu1 Hu2]]]]
                       [Xv [Sv [rv [PXv PSv Hrv Hv1 Hv2]]]].
            exists (Xu + Xv), (Su + Sv), (ru + rv).
            split.
            - exact: psdmxD PXu PXv.
            - exact: psdmxD PSu PSv.
            - exact: addr_ge0 Hru Hrv.
            - rewrite Hu1 Hv1.
              have HpsiD :
                  h2mx (Psi (mx2h (Xu + Xv))) =
                  h2mx (Psi (mx2h Xu)) + h2mx (Psi (mx2h Xv)).
              {
                have Hmx2hD : mx2h (Xu + Xv) = mx2h Xu + mx2h Xv
                  by rewrite linearD.
                have HPsiD :
                    Psi (mx2h (Xu + Xv)) =
                    Psi (mx2h Xu) + Psi (mx2h Xv).
                { rewrite Hmx2hD. exact: linearD. }
                have Hh2mxD :
                    h2mx (Psi (mx2h Xu) + Psi (mx2h Xv)) =
                    h2mx (Psi (mx2h Xu)) + h2mx (Psi (mx2h Xv)).
                { by rewrite raddfD. }
                by rewrite HPsiD Hh2mxD.
              }
              rewrite HpsiD.
              have Hadd :
                  forall a b c d : 'M[C]_(dim V),
                    (a - c) + (b - d) = a + b - (c + d).
              {
                move=> a b c d.
                rewrite opprD -!addrA.
                rewrite [b + (- c + - d)]addrCA.
                by rewrite !addrA.
              }
              by rewrite Hadd.
            - rewrite mulmxDr linearD /= raddfD /= Hu2 Hv2.
              by rewrite addrACA.
          }
          have HconeZ :
              forall (c : R) (u : 'M[C]_(dim V) * R),
                0 <= c -> cone_member u ->
                cone_member (c%:C *: u.1, c * u.2).
          {
            move=> c u Hc [X [S [r [PX PS Hr Hu1 Hu2]]]].
            exists (c%:C *: X), (c%:C *: S), (c * r).
            split.
            - apply: psdmxZ; last exact: PX.
              by rewrite lecR Hc.
            - apply: psdmxZ; last exact: PS.
              by rewrite lecR Hc.
            - exact: mulr_ge0 Hc Hr.
            - rewrite Hu1 scalerBr.
              have HpsiZ :
                  h2mx (Psi (mx2h (c%:C *: X))) =
                  c%:C *: h2mx (Psi (mx2h X)).
              {
                have Hmx2hZ : mx2h (c%:C *: X) = c%:C *: mx2h X
                  by rewrite linearZ.
                have HPsiZ :
                    Psi (mx2h (c%:C *: X)) = c%:C *: Psi (mx2h X).
                { rewrite Hmx2hZ. exact: linearZ. }
                have Hh2mxZ :
                    h2mx (c%:C *: Psi (mx2h X)) =
                    c%:C *: h2mx (Psi (mx2h X)).
                {
                  move: (h2mxP c%:C (Psi (mx2h X)) 0).
                  by rewrite h2mx0 !addr0.
                }
                by rewrite HPsiZ Hh2mxZ.
              }
              by rewrite HpsiZ.
            - rewrite -scalemxAr linearZ /= Hu2.
              by rewrite HRe_realM mulrDr.
          }
          have Hcone_conv :
              forall (a : R) (u v : 'M[C]_(dim V) * R),
                0 <= a -> a <= 1 ->
                cone_member u -> cone_member v ->
                cone_member
                  (a%:C *: u.1 + (1 - a)%:C *: v.1,
                   a * u.2 + (1 - a) * v.2).
          {
            move=> a u v Ha Ha1 Hu Hv.
            have Hu' : cone_member (a%:C *: u.1, a * u.2) :=
              HconeZ a u Ha Hu.
            have Hv' : cone_member ((1 - a)%:C *: v.1, (1 - a) * v.2).
            {
              apply: HconeZ; last exact: Hv.
              by rewrite subr_ge0.
            }
            exact: (HconeD _ _ Hu' Hv').
          }
          (* Slater gap identity: this is the boundedness estimate used by
             the closedness proof for the cone image. *)
          pose S0_slater := A - h2mx (Psi^*o (mx2h Y0)).
          have Hslater_gap :
              forall (w : 'M[C]_(dim V) * R)
                (X : 'M[C]_(dim U)) (S : 'M[C]_(dim V)) (r : R),
                X \is psdmx -> S \is psdmx -> 0 <= r ->
                w.1 = h2mx (Psi (mx2h X)) - S ->
                w.2 = @complex.Re R (\tr (A *m X)) + r ->
                w.2 - @complex.Re R (\tr (Y0 *m w.1)) =
                  @complex.Re R (\tr (S0_slater *m X)) +
                  @complex.Re R (\tr (Y0 *m S)) + r.
          {
            move=> w X S r PX PS Hr Hw1 Hw2.
            have Hpair :
                \tr (Y0 *m h2mx (Psi (mx2h X))) =
                \tr (h2mx (Psi^*o (mx2h Y0)) *m X).
            {
              move: (dualso_trlfEV Psi (mx2h X) (mx2h Y0)).
              rewrite /lftrace !h2mx_comp !mx2hK mxtrace_mulC.
              by move=> ->; rewrite mxtrace_mulC.
            }
            rewrite Hw2 Hw1 mulmxBr linearB /= raddfB /= Hpair /S0_slater.
            have HS0E :
                @complex.Re R
                  (\tr ((A - h2mx (Psi^*o (mx2h Y0))) *m X)) =
                @complex.Re R
                  (\tr (A *m X) -
                   \tr (h2mx (Psi^*o (mx2h Y0)) *m X)).
            {
              rewrite mulmxBl.
              have HtrB :
                  \tr (A *m X - h2mx (Psi^*o (mx2h Y0)) *m X) =
                  \tr (A *m X) -
                  \tr (h2mx (Psi^*o (mx2h Y0)) *m X).
              { by rewrite linearB. }
              by rewrite HtrB raddfB.
            }
            rewrite HS0E.
            set ax := @complex.Re R (\tr (A *m X)).
            set px := @complex.Re R (\tr (h2mx (Psi^*o (mx2h Y0)) *m X)).
            set ys := @complex.Re R (\tr (Y0 *m S)).
            have HReB :
                @complex.Re R
                  (\tr (A *m X) - \tr (h2mx (Psi^*o (mx2h Y0)) *m X)) =
                ax - px.
            {
              by rewrite /ax /px raddfB.
            }
            rewrite HReB.
            have Halg : (ax + r) - (px - ys) = (ax - px) + ys + r.
            {
              rewrite opprB.
              rewrite [ys - px]addrC.
              rewrite -[LHS]addrA.
              rewrite [r + (- px + ys)]addrCA.
              rewrite [r + ys]addrC.
              by rewrite !addrA.
            }
            exact: Halg.
          }
          have HS0_slater_psd : S0_slater \is psdmx := pdmx_psdmx HS0pd.
          have HY0_slater_psd : Y0 \is psdmx := pdmx_psdmx HY0pd.
          have Hslater_gap_terms_ge0 :
              forall (X : 'M[C]_(dim U)) (S : 'M[C]_(dim V)),
                X \is psdmx -> S \is psdmx ->
                0 <= @complex.Re R (\tr (S0_slater *m X)) /\
                0 <= @complex.Re R (\tr (Y0 *m S)).
          {
            move=> X S PX PS.
            split.
            - have Hle0 : (0 : 'M[C]_(dim U)) <= S0_slater.
              {
                rewrite le_lownerE.
                have -> : S0_slater - 0 = S0_slater.
                {
                  apply/matrixP=> i j.
                  by rewrite !mxE subr0.
                }
                exact: HS0_slater_psd.
              }
              have Htr : 0 <= \tr (S0_slater *m X).
              {
                move/le_lownerE_psdtr: Hle0 => /(_ X PX).
                by rewrite mul0mx mxtrace0.
              }
              have Hreal : \tr (S0_slater *m X) \is Num.real :=
                ger0_real Htr.
              have HtrC :
                  (0 : C) <=
                    (@complex.Re R (\tr (S0_slater *m X)))%:C.
              {
                by rewrite RRe_real.
              }
              by move: HtrC; rewrite ler0c.
            - have Hle0 : (0 : 'M[C]_(dim V)) <= Y0.
              {
                rewrite le_lownerE.
                have -> : Y0 - 0 = Y0.
                {
                  apply/matrixP=> i j.
                  by rewrite !mxE subr0.
                }
                exact: HY0_slater_psd.
              }
              have Htr : 0 <= \tr (Y0 *m S).
              {
                move/le_lownerE_psdtr: Hle0 => /(_ S PS).
                by rewrite mul0mx mxtrace0.
              }
              have Hreal : \tr (Y0 *m S) \is Num.real :=
                ger0_real Htr.
              have HtrC :
                  (0 : C) <= (@complex.Re R (\tr (Y0 *m S)))%:C.
              {
                by rewrite RRe_real.
              }
              by move: HtrC; rewrite ler0c.
          }
          have Hslater_gap_bounds :
              forall (w : 'M[C]_(dim V) * R)
                (X : 'M[C]_(dim U)) (S : 'M[C]_(dim V)) (r : R),
                X \is psdmx -> S \is psdmx -> 0 <= r ->
                w.1 = h2mx (Psi (mx2h X)) - S ->
                w.2 = @complex.Re R (\tr (A *m X)) + r ->
                let gap :=
                  w.2 - @complex.Re R (\tr (Y0 *m w.1)) in
                [/\ 0 <= gap,
                    @complex.Re R (\tr (S0_slater *m X)) <= gap,
                    @complex.Re R (\tr (Y0 *m S)) <= gap &
                    r <= gap].
          {
            move=> w X S r PX PS Hr Hw1 Hw2 /=.
            have [HS0X_ge0 HY0S_ge0] := Hslater_gap_terms_ge0 X S PX PS.
            have Hgap := Hslater_gap w X S r PX PS Hr Hw1 Hw2.
            rewrite Hgap.
            split.
            - exact: addr_ge0 (addr_ge0 HS0X_ge0 HY0S_ge0) Hr.
            - by rewrite -addrA lerDl addr_ge0.
            - rewrite [@complex.Re R (\tr (S0_slater *m X)) + _]addrC.
              by rewrite -addrA lerDl addr_ge0.
            - set sx := @complex.Re R (\tr (S0_slater *m X)).
              set sy := @complex.Re R (\tr (Y0 *m S)).
              change (r <= sx + sy + r).
              rewrite addrC.
              by rewrite lerDl addr_ge0.
          }
          (* Closed conic separation: still the finite-dimensional
             compactness/nearest-point step to fill below. *)
          have Hclosed_conic_separator :
              exists (Y : 'M[C]_(dim V)) (t : R),
                [/\ Y \is hermmx,
                    Zlin Y t \is hermmx,
                    (forall w : 'M[C]_(dim V) * R, cone_member w ->
                      @complex.Re R (\tr (Y *m w.1)) - t * w.2 <= 0) &
                    0 < @complex.Re R (\tr (Y *m B)) - t * gamma].
          {
            (* Strict positivity gives a trace functional that bounds
               PSD witnesses in the ambient matrix norm. *)
            have Hpd_trace_norm_bound :
                forall n (P : 'M[C]_n),
                  (0 < n)%N ->
                  P \is pdmx ->
                  exists cm : C,
                    0 < cm /\
                    forall X : 'M[C]_n,
                      X \is psdmx ->
                      mx_norm X <=
                        cm *
                        ((@complex.Re R (\tr (P *m X)))%:C).
            {
              move=> n P Hdim_pos HPpd.
              pose c0 := \sum_i (spectral_diag P 0 i)^-1.
              have /pdmxP [HPherm /posmxP HPpos] := HPpd.
              have Hc0_pos : 0 < c0.
              {
                pose i0 : 'I_n := Ordinal Hdim_pos.
                rewrite /c0 (bigD1 i0) //.
                have Hterm_pos : 0 < GRing.inv (spectral_diag P 0 i0).
                {
                  move: (HPpos 0 i0).
                  by rewrite posrE invr_gt0.
                }
                have Hrest_ge0 : 0 <= \sum_(i | i != i0)
                    GRing.inv (spectral_diag P 0 i).
                {
                  apply: sumr_ge0 => i _.
                  move: (HPpos 0 i).
                  by rewrite posrE => /ltW; rewrite invr_ge0.
                }
                apply: (lt_le_trans Hterm_pos).
                by rewrite lerDl.
              }
              pose c0R := @c2r R C c0.
              have Hc0R_pos : 0 < c0R.
              {
                by rewrite /c0R; exact: ExtNumTopology.c2r_gt0.
              }
              have Hc0E : c0 = c0R%:C.
              {
                rewrite /c0R c2rK //.
                exact: gtr0_real Hc0_pos.
              }
              have HId_le_cP : (1%:M : 'M[C]_n) <= c0 *: P.
              {
                pose P0 := eigenmx P.
                pose d0 := spectral_diag P.
                have HP0u : P0 \is unitarymx := eigen_unitarymx P.
                have HPdec : P = P0 *m diag_mx d0 *m P0^*t.
                {
                  move: (hermitian_normalmx HPherm).
                  by rewrite -/P0 -/d0; move/eigen_dec.
                }
                have Hdiag_psd : (c0 *: diag_mx d0 - 1%:M) \is psdmx.
                {
                  have -> : c0 *: diag_mx d0 - 1%:M =
                      diag_mx (\row_i (c0 * d0 0 i - 1)).
                  {
                    apply/matrixP=> i j.
                    have [Hij|Hij] := eqVneq i j.
                    - by move: Hij => ->; rewrite !mxE eqxx.
                    - by rewrite !mxE (negbTE Hij) mulr0 subrr.
                  }
                  apply/diagmx_nnegmx_psd/nnegmxP=> i j.
                  rewrite !mxE nnegrE subr_ge0.
                  have Hd0j_pos : 0 < d0 0 j.
                  {
                    move: (HPpos 0 j).
                    by rewrite posrE.
                  }
                  have Hinv_le : ((d0 0 j)^-1)%R <= c0.
                  {
                    rewrite /c0 (bigD1 j) //.
                    rewrite lerDl.
                    apply: sumr_ge0 => k _.
                    have Hd0k_pos : 0 < d0 0 k.
                    {
                      move: (HPpos 0 k).
                      by rewrite posrE.
                    }
                    by rewrite invr_ge0 (ltW Hd0k_pos).
                  }
                  have Htmp : ((d0 0 j)^-1)%R * d0 0 j <= c0 * d0 0 j.
                  {
                    by rewrite (ler_pM2r Hd0j_pos).
                  }
                  move: Htmp.
                  by rewrite mulVf ?lt0r_neq0.
                }
                rewrite le_lownerE.
                have HcP : P0 *m (c0 *: diag_mx d0) *m P0^*t = c0 *: P.
                {
                  rewrite HPdec.
                  by rewrite -scalemxAr -scalemxAl.
                }
                have Hconj :
                    c0 *: P - 1%:M =
                    P0 *m (c0 *: diag_mx d0 - 1%:M) *m P0^*t.
                {
                  rewrite mulmxBr mulmxBl HcP.
                  have -> : P0 *m 1%:M *m P0^*t = 1%:M.
                    by rewrite mulmx1 unitarymxK.
                  by [].
                }
                rewrite Hconj.
                exact: psdmx_bimap_closed_gen Hdiag_psd.
              }
              have [cm Hcm_pos Hcm_bound] :
                  exists2 cm : C, 0 < cm &
                    forall X : 'M[C]_n, mx_norm X <= cm * trnorm X.
              {
                exact: cmnorm_bounded.
              }
              exists (cm * c0R%:C).
              split.
              - by rewrite mulr_gt0 // ltcR.
              - move=> X PX.
                have HtrX_real : \tr X \is Num.real.
                {
                  exact: ger0_real (psdmx_trace PX).
                }
                have HPX_real : \tr (P *m X) \is Num.real.
                {
                  apply/CrealP.
                  rewrite -mxtrace_adj adjmxM.
                  have /hermmxP PE := HPherm.
                  have /hermmxP XE := psdmx_herm PX.
                  by rewrite -PE -XE mxtrace_mulC.
                }
                have HtrX_le :
                    @complex.Re R (\tr X) <=
                    c0R * @complex.Re R (\tr (P *m X)).
                {
                  move/le_lownerE_psdtr: HId_le_cP => /(_ X PX).
                  rewrite mul1mx -scalemxAl linearZ /= Hc0E.
                  by rewrite -(RRe_real HtrX_real) -(RRe_real HPX_real)
                             -realcM re_realid lecR.
                }
                apply: (le_trans (Hcm_bound X)).
                rewrite (psdmx_trnorm PX).
                have -> : \tr X = (@complex.Re R (\tr X))%:C.
                {
                  exact: esym (RRe_real HtrX_real).
                }
                rewrite -mulrA.
                rewrite ler_pM2l //.
                rewrite -rmorphM lecR.
                exact: HtrX_le.
            }
            (* Block packing: identify a product point `(W,r)` with a
               block-diagonal matrix so the Frobenius nearest-point normal
               can later be read back as a trace-linear pair `(Y,t)`. *)
            pose pack (w : 'M[C]_(dim V) * R) : 'M[C]_(dim V + 1) :=
              block_mx w.1 0 0 ((w.2)%:C%:M : 'M[C]_1).
            pose normal_pack (Y : 'M[C]_(dim V)) (t : R) :
                'M[C]_(dim V + 1) :=
              block_mx Y 0 0 (((- t)%:C)%:M : 'M[C]_1).
            have Hpack_pairing :
                forall (Y : 'M[C]_(dim V)) (t : R)
                  (w : 'M[C]_(dim V) * R),
                  @complex.Re R (\tr (normal_pack Y t *m pack w)) =
                  @complex.Re R (\tr (Y *m w.1)) - t * w.2.
            {
              move=> Y t w.
              rewrite /normal_pack /pack.
              rewrite mulmx_block !mulmx0 !mul0mx !addr0 !add0r.
              rewrite mxtrace_block linearD /=.
              rewrite mul_mx_scalar.
              have HRe_realM_pack : forall (c : R) (z : C),
                  @complex.Re R (c%:C * z) = c * @complex.Re R z.
              {
                move=> c z.
                case: z => a b /=.
                by rewrite mul0r subr0.
              }
              rewrite linearZ /= mxtrace_scalar.
              rewrite HRe_realM_pack.
              have -> : w.2 * - t = - (t * w.2) by rewrite mulrN mulrC.
              by [].
            }
            (* Easy Slater branch: the strict dual witness itself separates
               `(B,gamma)` whenever its objective already beats `gamma`. *)
            pose d0_sep := @complex.Re R (\tr (Y0 *m B)).
            case: (ltP gamma d0_sep) => HgammaY0.
            - exists Y0, 1.
              have HY0herm : Y0 \is hermmx := psdmx_herm HY0_slater_psd.
              have HZ_Y0 : Zlin Y0 1 \is hermmx.
              {
                have -> : Zlin Y0 1 = S0_slater.
                  by rewrite /Zlin /S0_slater scale1r.
                exact: psdmx_herm HS0_slater_psd.
              }
              split=> //.
              + move=> w [X [S [r [PX PS Hr Hw1 Hw2]]]].
                have [Hgap_ge0 _ _ _] :=
                  Hslater_gap_bounds w X S r PX PS Hr Hw1 Hw2.
                rewrite mul1r subr_le0.
                by move: Hgap_ge0; rewrite subr_ge0.
              + rewrite mul1r subr_gt0.
                exact: HgammaY0.
            -
            (* Hilbert separation core: the missing point is now isolated as
               a block-matrix nearest-point separator for the closed cone. *)
            have Hblock_separator :
                exists (Y : 'M[C]_(dim V)) (t : R),
                  [/\ Y \is hermmx,
                      Zlin Y t \is hermmx,
                      (forall w : 'M[C]_(dim V) * R, cone_member w ->
                        @complex.Re R (\tr (normal_pack Y t *m pack w)) <= 0) &
                      0 <
                        @complex.Re R
                          (\tr (normal_pack Y t *m pack p))].
            {
              (* Nearest-point normal: this is the remaining analytic core.
                 A minimizer `q` of the block Frobenius distance from `p`
                 gives the outward normal `pack p - pack q`. *)
              have Hnearest_normal :
                  exists q : 'M[C]_(dim V) * R,
                    [/\ cone_member q,
                        (forall w : 'M[C]_(dim V) * R, cone_member w ->
                          @complex.Re R
                            (\tr (normal_pack (p.1 - q.1) (q.2 - p.2)
                                      *m pack w)) <= 0) &
                        0 <
                          @complex.Re R
                            (\tr (normal_pack (p.1 - q.1) (q.2 - p.2)
                                    *m pack p))].
              {
                have Hnormal_packE :
                    forall q : 'M[C]_(dim V) * R,
                      normal_pack (p.1 - q.1) (q.2 - p.2) =
                      pack p - pack q.
                {
                  move=> q.
                  rewrite /normal_pack /pack /p /=.
                  rewrite opp_block_mx add_block_mx !subrr.
                  congr (block_mx _ _ _ _); try by [].
                  rewrite opprB.
                  by rewrite -raddfB /= rmorphB.
                }
                have Hpack_inj : injective pack.
                {
                  move=> u v Huv.
                  case: u Huv => Wu ru /= Huv.
                  case: v Huv => Wv rv /= Huv.
                  have HW : Wu = Wv.
                  {
                    move: (congr1 ulsubmx Huv).
                    by rewrite !block_mxKul.
                  }
                  have Hr : ru = rv.
                  {
                    move: (congr1 drsubmx Huv).
                    rewrite !block_mxKdr => Hrv.
                    move: (congr1 (fun M : 'M[C]_1 => M ord0 ord0) Hrv).
                    rewrite !mxE => Hscalar.
                    apply/eqP.
                    rewrite -eqcR.
                    by apply/eqP.
                  }
                  by rewrite HW Hr.
                }
                (* Nearest point: closedness under Slater plus compactness
                   gives a block-Frobenius minimizer in the cone. *)
                have Hnearest_point :
                    exists q : 'M[C]_(dim V) * R,
                      [/\ cone_member q,
                          (forall w : 'M[C]_(dim V) * R, cone_member w ->
                            fbnorm (pack p - pack q) <=
                            fbnorm (pack p - pack w)) &
                          p != q].
                {
                  pose PackCone (Q : 'M[C]_(dim V + 1)) :=
                    exists w : 'M[C]_(dim V) * R,
                      cone_member w /\ Q = pack w.
                  have Hpack_nearest :
                      exists Q : 'M[C]_(dim V + 1),
                        [/\ PackCone Q,
                            (forall Q' : 'M[C]_(dim V + 1), PackCone Q' ->
                              fbnorm (pack p - Q) <= fbnorm (pack p - Q')) &
                              Q != pack p].
                    {
                      (* Minimize the real Frobenius distance over the
                         bounded witness slice; compactness is isolated
                         in `HDist_compact` below. *)
                      pose distR (Q : 'M[C]_(dim V + 1)) : R :=
                        @complex.Re R (fbnorm (pack p - Q)).
                      pose coneQ
                        (z : ('M[C]_(dim U) * 'M[C]_(dim V)) * R) :
                        'M[C]_(dim V + 1) :=
                        pack (h2mx (Psi (mx2h z.1.1)) - z.1.2,
                          @complex.Re R (\tr (A *m z.1.1)) + z.2).
                      pose Witness
                        (z : ('M[C]_(dim U) * 'M[C]_(dim V)) * R) :=
                        [/\ z.1.1 \is psdmx,
                            z.1.2 \is psdmx,
                            0 <= z.2 &
                            distR (coneQ z) <= distR 0].
                      pose DistSet : set R :=
                        [set d : R | exists z :
                          ('M[C]_(dim U) * 'M[C]_(dim V)) * R,
                          Witness z /\ d = distR (coneQ z)]%classic.
                      have Hpack0_local : pack (0, 0) = 0.
                      {
                        by rewrite /pack /= scalemx0 block_mx0.
                      }
                      pose z0 : ('M[C]_(dim U) * 'M[C]_(dim V)) * R :=
                        ((0, 0), 0).
                      have HconeQ0 : coneQ z0 = 0.
                      {
                        have HPsi0 : Psi 0 = 0 by rewrite linear0.
                        rewrite /coneQ /z0 /= mx2h0 HPsi0 subr0
                          mulmx0 mxtrace0 addr0.
                        by rewrite h2mx0 raddf0 Hpack0_local.
                      }
                      have Hz0 : Witness z0.
                      {
                        split.
                        - exact: psdmx0.
                        - exact: psdmx0.
                        - exact: lexx.
                        - by rewrite HconeQ0.
                      }
                      have HDist_ne : (DistSet !=set0)%classic.
                      {
                        exists (distR (coneQ z0)).
                        by exists z0.
                      }
                      have HdistR_leC :
                          forall Q1 Q2 : 'M[C]_(dim V + 1),
                            distR Q1 <= distR Q2 ->
                            fbnorm (pack p - Q1) <= fbnorm (pack p - Q2).
                      {
                        move=> Q1 Q2 Hle.
                        have H1real :
                            fbnorm (pack p - Q1) \is Num.real :=
                          schnorm_real 2 (pack p - Q1).
                        have H2real :
                            fbnorm (pack p - Q2) \is Num.real :=
                          schnorm_real 2 (pack p - Q2).
                        by rewrite -(RRe_real H1real) -(RRe_real H2real) lecR.
                      }
                      have HDist_compact : compact (DistSet : set R^o).
                      {
                        pose WType :=
                          (('M[C]_(dim U) * 'M[C]_(dim V)) * R^o)%type.
                        pose distW
                          (z : WType) : R^o :=
                            distR (coneQ z).
                            pose WSet : set WType := Witness.
                            have HdistW_cont : continuous distW.
                            {
                              (* The distance is a continuous norm after
                                 the affine packed-cone map. *)
                              have HdistR_cont :
                                  continuous (fun Q : 'M[C]_(dim V + 1) =>
                                    (distR Q : R^o)).
                              {
                                (* Subtracting from the fixed packed point,
                                   then taking Frobenius norm and real part,
                                   is continuous. *)
                                have Hsub_cont :
                                    continuous (fun Q : 'M[C]_(dim V + 1) =>
                                      pack p - Q).
                                {
                                  have -> :
                                      (fun Q : 'M[C]_(dim V + 1) => pack p - Q) =
                                      ((fun Q : 'M[C]_(dim V + 1) => pack p + Q) \o
                                       (fun Q : 'M[C]_(dim V + 1) => - Q))%FUN.
                                  {
                                    by apply/funext=> Q.
                                  }
                                  apply: (@continuous_comp_simp _ _ _
                                    (fun Q : 'M[C]_(dim V + 1) => - Q)
                                    (fun Q : 'M[C]_(dim V + 1) => pack p + Q)).
                                  - exact: (@cmxopp_continuous R (dim V + 1) (dim V + 1)).
                                  - exact: (@cmxaddr_continuous R (dim V + 1) (dim V + 1) (pack p)).
                                }
                                have Hnorm_cont :
                                    continuous (fun Q : 'M[C]_(dim V + 1) =>
                                      fbnorm (pack p - Q)).
                                {
                                  apply: (@continuous_comp_simp _ _ _
                                    (fun Q : 'M[C]_(dim V + 1) => pack p - Q)
                                    (fun M : 'M[C]_(dim V + 1) => fbnorm M)).
                                  - exact: Hsub_cont.
                                  - exact: schnorm_continuous.
                                }
                                rewrite /distR.
                                apply: (@continuous_comp_simp _ _ _
                                  (fun Q : 'M[C]_(dim V + 1) => fbnorm (pack p - Q))
                                  (fun x : C => (@complex.Re R x : R^o))).
                                - exact: Hnorm_cont.
                                - exact: continuous_c2rC.
                              }
                              have HconeQ_cont :
                                  continuous (fun z : WType => coneQ z).
                              {
                                have HprojX_cont :
                                    continuous (fun z : WType => z.1.1).
                                {
                                  move=> z.
                                  exact: (@cvg_comp _ _ _
                                    (fun z : WType => z.1)
                                    (fun y : 'M[C]_(dim U) * 'M[C]_(dim V) => y.1)
                                    _ _ _ cvg_fst cvg_fst).
                                }
                                have HprojS_cont :
                                    continuous (fun z : WType => z.1.2).
                                {
                                  move=> z.
                                  exact: (@cvg_comp _ _ _
                                    (fun z : WType => z.1)
                                    (fun y : 'M[C]_(dim U) * 'M[C]_(dim V) => y.2)
                                    _ _ _ cvg_fst cvg_snd).
                                }
                                have HprojR_cont :
                                    continuous (fun z : WType => z.2).
                                {
                                  move=> z.
                                  exact: cvg_snd.
                                }
                                have HPsiX_cont :
                                    continuous (fun X : 'M[C]_(dim U) =>
                                      h2mx (Psi (mx2h X))).
                                {
                                  (* The superoperator part is a complex-linear
                                     matrix map after the mx2h/h2mx bridge. *)
                                  pose PsiM (X : 'M[C]_(dim U)) :=
                                    h2mx (Psi (mx2h X)).
                                  have HPsiM_linear : linear PsiM.
                                  {
                                    move=> a X Y.
                                    rewrite /PsiM.
                                    have HPsi :
                                        Psi (mx2h (a *: X + Y)) =
                                        a *: Psi (mx2h X) + Psi (mx2h Y).
                                    { rewrite (mx2hP a X Y). exact: linearP. }
                                    rewrite HPsi.
                                    exact: h2mxP.
                                  }
                                  change (continuous PsiM).
                                  exact: (@cmxlinear_continuous R
                                    (dim U) (dim U) (dim V) (dim V)
                                    PsiM HPsiM_linear).
                                }
                                have HtrAX_cont :
                                    continuous (fun X : 'M[C]_(dim U) =>
                                      (@complex.Re R (\tr (A *m X)) : R^o)).
                                {
                                  (* The trace component is a scalar linear
                                     matrix functional followed by real part. *)
                                  have HtrAX_C_cont :
                                      continuous (fun X : 'M[C]_(dim U) =>
                                        \tr (A *m X)).
                                  {
                                    apply: cmxscalar_continuous.
                                    move=> a X Y.
                                    by rewrite mulmxDr -scalemxAr linearD linearZ.
                                  }
                                  apply: (@continuous_comp_simp _ _ _
                                    (fun X : 'M[C]_(dim U) => \tr (A *m X))
                                    (fun x : C => (@complex.Re R x : R^o))).
                                  - exact: HtrAX_C_cont.
                                  - exact: continuous_c2rC.
                                }
                                have HPsiZ_cont :
                                    continuous (fun z : WType =>
                                      h2mx (Psi (mx2h z.1.1))).
                                {
                                  (* Compose the X-projection with the
                                     superoperator matrix map. *)
                                  apply: (@continuous_comp_simp _ _ _
                                    (fun z : WType => z.1.1)
                                    (fun X : 'M[C]_(dim U) =>
                                      h2mx (Psi (mx2h X)))).
                                  - exact: HprojX_cont.
                                  - exact: HPsiX_cont.
                                }
                                have HtrZ_cont :
                                    continuous (fun z : WType =>
                                      (@complex.Re R (\tr (A *m z.1.1)) : R^o)).
                                {
                                  (* Compose the X-projection with the
                                     scalar trace functional. *)
                                  apply: (@continuous_comp_simp _ _ _
                                    (fun z : WType => z.1.1)
                                    (fun X : 'M[C]_(dim U) =>
                                      (@complex.Re R (\tr (A *m X)) : R^o))).
                                  - exact: HprojX_cont.
                                  - exact: HtrAX_cont.
                                }
                                have Hmat_sub_cont :
                                    continuous (fun y : 'M[C]_(dim V) * 'M[C]_(dim V) =>
                                      y.1 - y.2).
                                {
                                  (* Matrix subtraction is continuous in
                                     each product component. *)
                                  have -> :
                                      (fun y : 'M[C]_(dim V) * 'M[C]_(dim V) =>
                                        y.1 - y.2) =
                                      ((fun y : 'M[C]_(dim V) * 'M[C]_(dim V) =>
                                        y.1 + y.2) \o
                                       (fun y : 'M[C]_(dim V) * 'M[C]_(dim V) =>
                                        (y.1, - y.2)))%FUN.
                                  {
                                    by apply/funext=> y.
                                  }
                                  apply: (@continuous_comp_simp _ _ _
                                    (fun y : 'M[C]_(dim V) * 'M[C]_(dim V) =>
                                      (y.1, - y.2))
                                    (fun y : 'M[C]_(dim V) * 'M[C]_(dim V) =>
                                      y.1 + y.2)).
                                  - move=> y.
                                    have Hneg :
                                        ((fun x : 'M[C]_(dim V) * 'M[C]_(dim V) =>
                                          - x.2) @ (nbhs y) --> - y.2)%classic.
                                    {
                                      apply: continuous_cvg cvg_snd.
                                      exact: (@cmxopp_continuous R (dim V) (dim V)).
                                    }
                                    exact: (cvg_pair cvg_fst Hneg).
                                  - exact: (@cmxadd_continuous R (dim V) (dim V)).
                                }
                                have HWpart_cont :
                                    continuous (fun z : WType =>
                                      h2mx (Psi (mx2h z.1.1)) - z.1.2).
                                {
                                  (* The upper block is the difference of
                                     two continuous matrix-valued maps. *)
                                  have Hpair_cont :
                                      continuous (fun z : WType =>
                                        (h2mx (Psi (mx2h z.1.1)), z.1.2)).
                                  {
                                    move=> z.
                                    exact: (cvg_pair (HPsiZ_cont z) (HprojS_cont z)).
                                  }
                                  apply: (@continuous_comp_simp _ _ _
                                    (fun z : WType =>
                                      (h2mx (Psi (mx2h z.1.1)), z.1.2))
                                    (fun y : 'M[C]_(dim V) * 'M[C]_(dim V) =>
                                      y.1 - y.2)).
                                  - exact: Hpair_cont.
                                  - exact: Hmat_sub_cont.
                                }
                                have Hrpart_cont :
                                    continuous (fun z : WType =>
                                      (@complex.Re R (\tr (A *m z.1.1)) + z.2 : R^o)).
                                {
                                  (* The lower scalar block is an ordinary
                                     real sum. *)
                                  move=> z.
                                  exact: cvgD (HtrZ_cont z) (HprojR_cont z).
                                }
                                have HpackC_cont :
                                    continuous (fun w : 'M[C]_(dim V) * C =>
                                      block_mx w.1 0 0 (w.2%:M : 'cV_1)).
                                {
                                  (* Factor packing into continuous upper and
                                     lower block embeddings, then add them. *)
                                  have Hupper_cont :
                                      continuous (fun W : 'M[C]_(dim V) =>
                                        block_mx W 0 0 (0 : 'cV_1)).
                                  {
                                    apply: (@cmxlinear_continuous R
                                      (dim V) (dim V) (dim V + 1) (dim V + 1)).
                                    move=> a X Y.
                                    by rewrite /= scale_block_mx add_block_mx
                                      !scaler0 !addr0.
                                  }
                                  have Hlower_cont :
                                      continuous (fun c : C =>
                                        block_mx (0 : 'M[C]_(dim V)) 0 0
                                          (c%:M : 'cV_1)).
                                  {
                                    apply: linear_to_cmx_continuousP.
                                    move=> a c d.
                                    rewrite /= scale_block_mx add_block_mx
                                      !scaler0 !addr0.
                                    congr (block_mx _ _ _ _); try by [].
                                    apply/matrixP=> i j.
                                    by rewrite (ord1 i) (ord1 j) !mxE eqxx !mulr1n.
                                  }
                                  have Hupper_pair_cont :
                                      continuous (fun w : 'M[C]_(dim V) * C =>
                                        block_mx w.1 0 0 (0 : 'cV_1)).
                                  {
                                    apply: (@continuous_comp_simp _ _ _
                                      (fun w : 'M[C]_(dim V) * C => w.1)
                                      (fun W : 'M[C]_(dim V) =>
                                        block_mx W 0 0 (0 : 'cV_1))).
                                    - by move=> w; exact: cvg_fst.
                                    - exact: Hupper_cont.
                                  }
                                  have Hlower_pair_cont :
                                      continuous (fun w : 'M[C]_(dim V) * C =>
                                        block_mx (0 : 'M[C]_(dim V)) 0 0
                                          (w.2%:M : 'cV_1)).
                                  {
                                    apply: (@continuous_comp_simp _ _ _
                                      (fun w : 'M[C]_(dim V) * C => w.2)
                                      (fun c : C =>
                                        block_mx (0 : 'M[C]_(dim V)) 0 0
                                          (c%:M : 'cV_1))).
                                    - by move=> w; exact: cvg_snd.
                                    - exact: Hlower_cont.
                                  }
                                  have Hpack_sum_cont :
                                      continuous (fun w : 'M[C]_(dim V) * C =>
                                        (block_mx w.1 0 0 (0 : 'cV_1),
                                         block_mx (0 : 'M[C]_(dim V)) 0 0
                                           (w.2%:M : 'cV_1))).
                                  {
                                    move=> w.
                                    exact: (cvg_pair (Hupper_pair_cont w)
                                      (Hlower_pair_cont w)).
                                  }
                                  have -> :
                                      (fun w : 'M[C]_(dim V) * C =>
                                        block_mx w.1 0 0 (w.2%:M : 'cV_1)) =
                                      ((fun z : 'M[C]_(dim V + 1) *
                                                 'M[C]_(dim V + 1) =>
                                        z.1 + z.2) \o
                                       (fun w : 'M[C]_(dim V) * C =>
                                        (block_mx w.1 0 0 (0 : 'cV_1),
                                         block_mx (0 : 'M[C]_(dim V)) 0 0
                                           (w.2%:M : 'cV_1))))%FUN.
                                  {
                                    apply/funext=> w /=.
                                    by rewrite add_block_mx !add0r !addr0.
                                  }
                                  apply: (@continuous_comp_simp _ _ _
                                    (fun w : 'M[C]_(dim V) * C =>
                                      (block_mx w.1 0 0 (0 : 'cV_1),
                                       block_mx (0 : 'M[C]_(dim V)) 0 0
                                         (w.2%:M : 'cV_1)))
                                    (fun z : 'M[C]_(dim V + 1) *
                                               'M[C]_(dim V + 1) =>
                                      z.1 + z.2)).
                                  - exact: Hpack_sum_cont.
                                  - exact: (@cmxadd_continuous R
                                      (dim V + 1) (dim V + 1)).
                                }
                                have Hreal_complex_cont :
                                    continuous (fun r : R^o => (r%:C : C)).
                                {
                                  (* Real scalars embed continuously into
                                     the complex scalar field. *)
                                  exact: ExtNumTopology.r2c_continuous.
                                }
                                have Hpack_cont :
                                    continuous (fun w : 'M[C]_(dim V) * R^o =>
                                      pack (w.1, w.2)).
                                {
                                  (* First embed the real lower component
                                     into C, then use complex-linear packing. *)
                                  have HpairCR_cont :
                                      continuous (fun w : 'M[C]_(dim V) * R^o =>
                                        (w.1, (w.2%:C : C))).
                                  {
                                    move=> w.
                                    have HrC :
                                        ((fun x : 'M[C]_(dim V) * R^o =>
                                          (x.2%:C : C)) @ (nbhs w) -->
                                        (w.2%:C : C))%classic.
                                    {
                                      apply: continuous_cvg cvg_snd.
                                      exact: Hreal_complex_cont.
                                    }
                                    exact: (cvg_pair cvg_fst HrC).
                                  }
                                  rewrite /pack.
                                  apply: (@continuous_comp_simp _ _ _
                                    (fun w : 'M[C]_(dim V) * R^o =>
                                      (w.1, (w.2%:C : C)))
                                    (fun w : 'M[C]_(dim V) * C =>
                                      block_mx w.1 0 0 (w.2%:M : 'cV_1))).
                                  - exact: HpairCR_cont.
                                  - exact: HpackC_cont.
                                }
                                have HpairWR_cont :
                                    continuous (fun z : WType =>
                                      (h2mx (Psi (mx2h z.1.1)) - z.1.2,
                                       (@complex.Re R (\tr (A *m z.1.1)) + z.2 : R^o))).
                                {
                                  (* Combine the continuous upper and lower
                                     packed components. *)
                                  move=> z.
                                  exact: (cvg_pair (HWpart_cont z) (Hrpart_cont z)).
                                }
                                rewrite /coneQ.
                                apply: (@continuous_comp_simp _ _ _
                                  (fun z : WType =>
                                    (h2mx (Psi (mx2h z.1.1)) - z.1.2,
                                     (@complex.Re R (\tr (A *m z.1.1)) + z.2 : R^o)))
                                  (fun w : 'M[C]_(dim V) * R^o =>
                                    pack (w.1, w.2))).
                                - exact: HpairWR_cont.
                                - exact: Hpack_cont.
                              }
                              apply: (@continuous_comp_simp _ _ _
                                (fun z : WType => coneQ z)
                                (fun Q : 'M[C]_(dim V + 1) => (distR Q : R^o))).
                              - exact: HconeQ_cont.
                              - exact: HdistR_cont.
                            }
                          have HWitness_compact :
                              compact WSet.
                        {
                          (* Slater bounds turn the witness slice into a
                             closed subset of a compact product box. *)
                            have HWitness_closed : closed WSet.
                            {
                              (* Witness closedness is the intersection of
                                 two PSD cones, one real half-line, and one
                                 distance sublevel set. *)
                              have Hclosed_psdU :
                                  closed [set X : 'M[C]_(dim U) | X \is psdmx]%classic.
                              {
                                have -> :
                                    [set X : 'M[C]_(dim U) | X \is psdmx]%classic =
                                    [set X : 'M[C]_(dim U) |
                                      (0 : 'M[C]_(dim U)) <= X]%classic.
                                {
                                  apply/funext=> X /=.
                                  apply/propext; split=> HX;
                                    by rewrite le_lownerE subr0 in HX *.
                                }
                                exact: psdmx_closed (dim U).
                              }
                              have Hclosed_psdV :
                                  closed [set S : 'M[C]_(dim V) | S \is psdmx]%classic.
                              {
                                have -> :
                                    [set S : 'M[C]_(dim V) | S \is psdmx]%classic =
                                    [set S : 'M[C]_(dim V) |
                                      (0 : 'M[C]_(dim V)) <= S]%classic.
                                {
                                  apply/funext=> S /=.
                                  apply/propext; split=> HS;
                                    by rewrite le_lownerE subr0 in HS *.
                                }
                                exact: psdmx_closed (dim V).
                              }
                              have HWitnessE :
                                  WSet =
                                  ([set z : WType | z.1.1 \is psdmx] `&`
                                   ([set z : WType | z.1.2 \is psdmx] `&`
                                    ([set z : WType | 0 <= z.2] `&`
                                     [set z : WType |
                                       distR (coneQ z) <= distR 0])))%classic.
                              {
                                apply/funext=> z.
                                rewrite /WSet /Witness /=.
                                apply/propext; split.
                                - move=> [PX PS Hr Hd].
                                  by split=> //; split=> //; split.
                                - move=> [PX [PS [Hr Hd]]].
                                  by split.
                              }
                              rewrite HWitnessE.
                              apply: closedI.
                              - change (closed
                                  ((fun z : WType => z.1.1) @^-1`
                                   [set X : 'M[C]_(dim U) | X \is psdmx])%classic).
                                apply: preimage_closed.
                                + move=> z _.
                                  exact: (@cvg_comp _ _ _
                                    (fun z : WType => z.1)
                                    (fun y : 'M[C]_(dim U) * 'M[C]_(dim V) => y.1)
                                    _ _ _ cvg_fst cvg_fst).
                                + exact: Hclosed_psdU.
                              - apply: closedI.
                                + change (closed
                                    ((fun z : WType => z.1.2) @^-1`
                                     [set S : 'M[C]_(dim V) | S \is psdmx])%classic).
                                  apply: preimage_closed.
                                  * move=> z _.
                                    exact: (@cvg_comp _ _ _
                                      (fun z : WType => z.1)
                                      (fun y : 'M[C]_(dim U) * 'M[C]_(dim V) => y.2)
                                      _ _ _ cvg_fst cvg_snd).
                                  * exact: Hclosed_psdV.
                                + apply: closedI.
                                  * change (closed
                                      ((fun z : WType => z.2) @^-1`
                                       [set r : R | 0 <= r])%classic).
                                    apply: preimage_closed.
                                    -- move=> z _.
                                       exact: cvg_snd.
                                    -- exact: closed_ge.
                                  * change (closed
                                      (distW @^-1`
                                       [set d : R | d <= distR 0])%classic).
                                    apply: preimage_closed.
                                    -- move=> z _.
                                       exact: HdistW_cont z.
                                    -- exact: closed_le.
                            }
                          have [cmX [HcmX_pos HcmX_bound]] :=
                            Hpd_trace_norm_bound (dim U) S0_slater dim_proper HS0pd.
                          have [cmS [HcmS_pos HcmS_bound]] :=
                            Hpd_trace_norm_bound (dim V) Y0 dim_proper HY0pd.
                          pose Gc : C :=
                            fbnorm (normal_pack Y0 1) *
                            (fbnorm (pack p) + fbnorm (pack p)).
                          pose GR : R := @complex.Re R Gc.
                          pose XBound : set 'M[C]_(dim U) :=
                            [set X : 'M[C]_(dim U) | mx_norm X <= cmX * Gc]%classic.
                          pose SBound : set 'M[C]_(dim V) :=
                            [set S : 'M[C]_(dim V) | mx_norm S <= cmS * Gc]%classic.
                          pose RBound : set R :=
                            [set r : R | 0 <= r <= GR]%classic.
                          have Hcomponent_bounds :
                              forall z : WType, WSet z ->
                                XBound z.1.1 /\ SBound z.1.2 /\ RBound z.2.
                          {
                            have HGc_ge0 : 0 <= Gc.
                            {
                              rewrite /Gc.
                              apply: mulr_ge0; first exact: fbnorm_ge0.
                              exact: addr_ge0 (fbnorm_ge0 _) (fbnorm_ge0 _).
                            }
                            have HGc_real : Gc \is Num.real := ger0_real HGc_ge0.
                            have HGR_ge0 : 0 <= GR.
                            {
                              move: HGc_ge0.
                              by rewrite /GR -(RRe_real HGc_real) lec0R.
                            }
                            have HGcE : GR%:C = Gc := RRe_real HGc_real.
                            move=> [[X S] r] /= [PX PS Hr Hdist].
                            pose w : 'M[C]_(dim V) * R :=
                              (h2mx (Psi (mx2h X)) - S,
                               @complex.Re R (\tr (A *m X)) + r).
                            have Hgap_bounds :=
                              Hslater_gap_bounds w X S r PX PS Hr erefl erefl.
                            case: Hgap_bounds =>
                              Hgap_ge0 HS0X_le_gap HY0S_le_gap Hr_le_gap.
                            have Hgap_le_GR :
                                w.2 - @complex.Re R (\tr (Y0 *m w.1)) <= GR.
                            {
                              pose gap :=
                                w.2 - @complex.Re R (\tr (Y0 *m w.1)).
                              pose Qw := coneQ ((X, S), r).
                              have HQw : Qw = pack w.
                              {
                                by rewrite /Qw /coneQ /w /=.
                              }
                              have HdistC :
                                  fbnorm (pack p - Qw) <= fbnorm (pack p).
                              {
                                have := HdistR_leC Qw 0 Hdist.
                                by rewrite subr0.
                              }
                              have HQw_norm :
                                  fbnorm Qw <= fbnorm (pack p) + fbnorm (pack p).
                              {
                                have Htri :
                                    fbnorm Qw <=
                                    fbnorm (Qw - pack p) + fbnorm (pack p).
                                {
                                  rewrite -[X in fbnorm X <= _](subrK (pack p) Qw).
                                  exact: (ler_fbnormD (Qw - pack p) (pack p)).
                                }
                                apply: (le_trans Htri).
                                rewrite lerD2r.
                                have Hdiff :
                                    fbnorm (Qw - pack p) =
                                    fbnorm (pack p - Qw).
                                {
                                  by rewrite -[Qw - pack p]opprK opprB schnormN.
                                }
                                by rewrite Hdiff.
                              }
                              pose ztr := \tr (normal_pack Y0 1 *m pack w).
                              have Hgap_ReN : gap = @complex.Re R (- ztr).
                              {
                                rewrite /gap /ztr raddfN /=.
                                rewrite Hpack_pairing mul1r.
                                by rewrite opprB.
                              }
                              have HgapC_le_abs :
                                  gap%:C <= `|ztr|.
                              {
                                have Habs := normc_ge_Re (- ztr).
                                move: Habs.
                                rewrite normrN.
                                rewrite -Hgap_ReN.
                                  have Hgap_ge0' : 0 <= gap := Hgap_ge0.
                                  move=> Habs.
                                  move: Habs.
                                  by rewrite (ger0_norm Hgap_ge0').
                                }
                                have Habs_le_Gc : `|ztr| <= Gc.
                                {
                                  apply: (le_trans (fbnormM_ge (normal_pack Y0 1) (pack w))).
                                  have Hnorm_pos :
                                      0 < fbnorm (normal_pack Y0 1).
                                  {
                                    rewrite schnorm_gt0.
                                    apply/eqP=> Hzero.
                                    move: (congr1 drsubmx Hzero).
                                    rewrite /normal_pack block_mxKdr => Hdr.
                                    move: (congr1 (fun M : 'M[C]_1 => M ord0 ord0) Hdr).
                                    rewrite !mxE.
                                    rewrite eqxx /= => Hbad.
                                    move: (congr1 (@complex.Re R) Hbad).
                                    rewrite /=.
                                    move=> HbadR.
                                    move: (congr1 (fun x : R => x + 1) HbadR).
                                    rewrite addNr add0r => H01.
                                    move: (esym H01).
                                    by move/eqP; rewrite oner_eq0.
                                  }
                                  rewrite /Gc (ler_pM2l Hnorm_pos).
                                  by rewrite -HQw.
                                }
                              have HgapC_le_Gc : gap%:C <= Gc :=
                                le_trans HgapC_le_abs Habs_le_Gc.
                              move: HgapC_le_Gc.
                              by rewrite -HGcE lecR.
                            }
                            have HS0X_le_GR :
                                @complex.Re R (\tr (S0_slater *m X)) <= GR :=
                              le_trans HS0X_le_gap Hgap_le_GR.
                            have HY0S_le_GR :
                                @complex.Re R (\tr (Y0 *m S)) <= GR :=
                              le_trans HY0S_le_gap Hgap_le_GR.
                            split.
                            - apply: (le_trans (HcmX_bound X PX)).
                              rewrite -HGcE ler_pM2l //.
                              by rewrite lecR.
                            - split.
                              + apply: (le_trans (HcmS_bound S PS)).
                                rewrite -HGcE ler_pM2l //.
                                by rewrite lecR.
                              + apply/andP; split=> //.
                                exact: le_trans Hr_le_gap Hgap_le_GR.
                          }
                          have Hbase_compact :
                              compact ((((XBound `*` SBound)%classic `*` RBound)%classic) :
                                set ((('M[C]_(dim U) * 'M[C]_(dim V)) * R^o))).
                          {
                            apply: compact_setX.
                            - apply: compact_setX.
                              + exact: compact_cmnorm_le.
                              + exact: compact_cmnorm_le.
                            - exact: compact_citv.
                          }
                          apply: (subclosed_compact HWitness_closed Hbase_compact _).
                          move=> [[X S] r] Hz.
                          have [HXb [HSb Hrb]] := Hcomponent_bounds _ Hz.
                          by split.
                        }
                        rewrite (_ : DistSet =
                          (distW @` WSet)%classic).
                          - change (compact (distW @` WSet)%classic).
                            apply: (@continuous_compact _ _ distW WSet).
                            + apply: continuous_subspaceT.
                              exact: HdistW_cont.
                            + exact: HWitness_compact.
                        - apply/funext=> d.
                          rewrite propeqE; split.
                          + move=> [z [Hz ->]].
                            by exists z.
                          + move=> [z Hz <-].
                            by exists z.
                      }
                      have [dmin Hdmin_mem Hdmin_le] :=
                        compact_min HDist_compact HDist_ne.
                      case: Hdmin_mem => zmin [Hzmin Hdmin].
                      case: zmin Hzmin Hdmin => [[Xmin Smin] rmin] Hzmin Hdmin.
                      move: Hzmin => [PXmin PSmin Hrmin Hdistmin].
                      pose Qmin := coneQ ((Xmin, Smin), rmin).
                      have HQmin_pack : PackCone Qmin.
                      {
                        exists (h2mx (Psi (mx2h Xmin)) - Smin,
                          @complex.Re R (\tr (A *m Xmin)) + rmin).
                        split.
                        - exists Xmin, Smin, rmin.
                          by split.
                        - by rewrite /Qmin /coneQ /=.
                      }
                      exists Qmin.
                      split.
                      - exact: HQmin_pack.
                      - move=> Q' HQ'.
                        have HminR_Q' : distR Qmin <= distR Q'.
                        {
                          case: (lerP (distR Q') (distR 0)) => HQ'le.
                          - case: HQ' => [[W rw] [Hw HQ'w]].
                            case: Hw => X [S [r [PX PS Hr Hw1 Hw2]]].
                            pose z' : ('M[C]_(dim U) * 'M[C]_(dim V)) * R :=
                              ((X, S), r).
                            have Hz' : Witness z'.
                            {
                              split=> //.
                              by rewrite /distR /coneQ /z' /= -Hw1 -Hw2 -HQ'w.
                            }
                            have HDist_Q' : DistSet (distR Q').
                            {
                              exists z'.
                              split=> //.
                              by rewrite /distR /coneQ /z' /= -Hw1 -Hw2 -HQ'w.
                            }
                            move: (Hdmin_le _ HDist_Q').
                            by rewrite Hdmin /Qmin.
                          - have HDist_0 : DistSet (distR 0).
                            {
                              exists z0.
                              split=> //.
                              by rewrite HconeQ0.
                            }
                            have Hdmin0 := Hdmin_le _ HDist_0.
                            apply: (le_trans _ (ltW HQ'le)).
                            by rewrite -Hdmin /Qmin.
                        }
                        exact: HdistR_leC HminR_Q'.
                      - apply/eqP=> HQp.
                        apply: Hp_not_cone.
                        case: HQmin_pack => w [Hw HQw].
                        move: Hw.
                        rewrite HQp in HQw.
                        have Hpw : p = w := Hpack_inj p w HQw.
                        by rewrite -Hpw.
                    }
                  case: Hpack_nearest => Q [[q [Hqcone HQ]] HQmin HQneq].
                  exists q.
                  split=> //.
                  - move=> w Hw.
                    rewrite -HQ.
                    apply: HQmin.
                    by exists w.
                  - apply/eqP=> Hpq.
                    move/eqP: HQneq; apply.
                    by rewrite HQ Hpq.
                }
                case: Hnearest_point => q [Hqcone Hqmin Hq_ne_p].
                pose dQ := pack p - pack q.
                have Hq1_herm_near : q.1 \is hermmx.
                {
                  case: Hqcone => X [S [r [PX PS _ Hq1 _]]].
                  rewrite Hq1.
                  apply/hermmxP.
                  have Hdiff_adj :
                      (h2mx (Psi (mx2h X)) - S)^*t =
                      (h2mx (Psi (mx2h X)))^*t - S^*t.
                  { by rewrite raddfB. }
                  rewrite Hdiff_adj.
                  have /hermmxP HPX := HPsi_herm _ (psdmx_herm PX).
                  have /hermmxP HS := psdmx_herm PS.
                  by rewrite -HPX -HS.
                }
                have Hnormal_pack_herm :
                    forall (Y : 'M[C]_(dim V)) (t : R),
                      Y \is hermmx -> normal_pack Y t \is hermmx.
                {
                  move=> Y t HY.
                  apply/hermmxP.
                  rewrite /normal_pack adj_block_mx !linear0.
                  have /hermmxP HYE := HY.
                  rewrite -HYE.
                  congr (block_mx _ _ _ _); try by [].
                  by rewrite adjmx_scale conjCc conjc_real.
                }
                have HdQ_herm : dQ \is hermmx.
                {
                  rewrite /dQ -(Hnormal_packE q).
                  apply: Hnormal_pack_herm.
                  rewrite /p /=.
                  apply/hermmxP.
                  rewrite linearB /=.
                  have /hermmxP HBE := HB.
                  have /hermmxP HQE := Hq1_herm_near.
                  by rewrite -HBE -HQE.
                }
                have Hpack0 : pack (0, 0) = 0.
                {
                  by rewrite /pack /= scalemx0 block_mx0.
                }
                (* Variational inequality: minimizing squared Frobenius
                   distance along each cone segment gives the normal cone. *)
                have Hproj :
                    forall w : 'M[C]_(dim V) * R, cone_member w ->
                      @complex.Re R
                        (\tr (dQ *m (pack w - pack q))) <= 0.
                {
                  move=> w Hw.
                  pose eQ := pack w - pack q.
                  pose Ldir := @complex.Re R (\tr (dQ *m eQ)).
                  case: (ltP 0 Ldir) => HLdir_pos; last exact.
                  pose Ndir := @complex.Re R (\tr (eQ^*t *m eQ)).
                  pose a := Ldir / (Ndir + Ldir + 1).
                    have Hscalar_bounds :
                        [/\ 0 <= Ndir, 0 < a, a <= 1 & a * Ndir < Ldir].
                    {
                      (* Choose a small positive step; the extra `+ 1`
                         makes the denominator strictly larger than the
                         squared direction norm. *)
                      have HNdirC_ge0 : 0 <= \tr (eQ^*t *m eQ).
                      {
                        exact: formV_tr_ge0.
                      }
                      have HNdir_real :
                          \tr (eQ^*t *m eQ) \is Num.real :=
                        ger0_real HNdirC_ge0.
                      have HNdir_ge0 : 0 <= Ndir.
                      {
                        move: HNdirC_ge0.
                        by rewrite /Ndir -(RRe_real HNdir_real) lec0R.
                      }
                      have HNplusL_pos : 0 < Ndir + Ldir.
                      {
                        rewrite addrC.
                        exact: ltr_pwDl HLdir_pos HNdir_ge0.
                      }
                      have Hden_pos : 0 < Ndir + Ldir + 1.
                      {
                        exact: ltr_pwDr ltr01 (ltW HNplusL_pos).
                      }
                      have Ha_pos : 0 < a.
                      {
                        rewrite /a.
                        exact: divr_gt0 HLdir_pos Hden_pos.
                      }
                      have HLdir_le_den : Ldir <= Ndir + Ldir + 1.
                      {
                        apply: ler_wpDr.
                        - exact: ltW ltr01.
                        - by rewrite addrC lerDl.
                      }
                      have Ha_le1 : a <= 1.
                      {
                        by rewrite /a ler_pdivrMr // mul1r.
                      }
                      have HNdir_lt_den : Ndir < Ndir + Ldir + 1.
                      {
                        apply: ltr_wpDr.
                        - exact: ltW ltr01.
                        - rewrite -[Ndir in Ndir < _]addr0 ltrD2l.
                          exact: HLdir_pos.
                      }
                      have HaN_lt : a * Ndir < Ldir.
                      {
                        rewrite /a.
                        rewrite -mulrA [(_^-1 * Ndir)]mulrC.
                        rewrite -[Ldir in _ < Ldir]mulr1.
                        rewrite ltr_pM2l; last exact: HLdir_pos.
                        rewrite ltr_pdivrMr; last exact: Hden_pos.
                        by rewrite mul1r.
                      }
                      by split.
                    }
                  case: Hscalar_bounds => HNdir_ge0 Ha_pos Ha_le1 HaN_lt.
                  pose vseg : 'M[C]_(dim V) * R :=
                    (a%:C *: w.1 + (1 - a)%:C *: q.1,
                     a * w.2 + (1 - a) * q.2).
                  have Hvseg : cone_member vseg.
                  {
                    exact: Hcone_conv a w q (ltW Ha_pos) Ha_le1 Hw Hqcone.
                  }
                  have Hminseg := Hqmin vseg Hvseg.
                    have Hsq_variation : 2 * Ldir <= a * Ndir.
                    {
                      (* Square the minimizer inequality along the cone
                         segment and expand the Frobenius inner product. *)
                      have Hpack_vseg :
                          pack vseg =
                          a%:C *: pack w + (1 - a)%:C *: pack q.
                      {
                        rewrite /pack /vseg /=.
                        rewrite !scale_block_mx add_block_mx !scaler0 !addr0.
                        congr (block_mx _ _ _ _); try by [].
                        apply/matrixP=> i j.
                        rewrite !mxE.
                        case Eij: (i == j).
                        - by rewrite !mulr1n !rmorphD !rmorphM !rmorphB !rmorphN !rmorph1.
                        - by rewrite !mulr0n !mulr0 addr0.
                      }
                      have HsegE :
                          pack p - pack vseg = dQ - a%:C *: eQ.
                      {
                        rewrite Hpack_vseg /dQ /eQ.
                        rewrite rmorphB rmorph1 scalerBl scale1r scalerBr.
                        rewrite !opprD.
                        apply/matrixP=> i j.
                        rewrite !mxE.
                        rewrite -[RHS]addrA.
                        congr (_ + _).
                        by rewrite addrCA.
                      }
                      have Hsq_from_min :
                          @complex.Re R (\tr (dQ^*t *m dQ)) <=
                          @complex.Re R
                            (\tr ((dQ - a%:C *: eQ)^*t
                                    *m (dQ - a%:C *: eQ))).
                      {
                        have Hmin_sq := lerXn2r 2
                          (fbnorm_ge0 (pack p - pack q))
                          (fbnorm_ge0 (pack p - pack vseg)) Hminseg.
                        move: Hmin_sq.
                        rewrite /dQ HsegE !fbnorm_dotV !sqrtCK.
                        have Hleft_real :
                            \tr (dQ^*t *m dQ) \is Num.real :=
                          ger0_real (formV_tr_ge0 dQ).
                        have Hright_real :
                            \tr ((dQ - a%:C *: eQ)^*t
                                  *m (dQ - a%:C *: eQ)) \is Num.real :=
                          ger0_real (formV_tr_ge0 (dQ - a%:C *: eQ)).
                        by rewrite -(RRe_real Hleft_real)
                          -(RRe_real Hright_real) lecR.
                      }
                      have Hquad_expand :
                          @complex.Re R
                            (\tr ((dQ - a%:C *: eQ)^*t
                                    *m (dQ - a%:C *: eQ))) =
                          @complex.Re R (\tr (dQ^*t *m dQ)) -
                            2 * a * Ldir + a ^+ 2 * Ndir.
                      {
                        have Hw1_herm_near : w.1 \is hermmx.
                        {
                          case: Hw => X [S [r [PX PS _ Hw1 _]]].
                          rewrite Hw1.
                          apply/hermmxP.
                          have Hdiff_adj :
                              (h2mx (Psi (mx2h X)) - S)^*t =
                              (h2mx (Psi (mx2h X)))^*t - S^*t.
                          { by rewrite raddfB. }
                          rewrite Hdiff_adj.
                          have /hermmxP HPX := HPsi_herm _ (psdmx_herm PX).
                          have /hermmxP HS := psdmx_herm PS.
                          by rewrite -HPX -HS.
                        }
                        have Hpack_herm_of_herm :
                            forall u : 'M[C]_(dim V) * R,
                              u.1 \is hermmx -> pack u \is hermmx.
                        {
                          move=> u Hu.
                          apply/hermmxP.
                          rewrite /pack adj_block_mx !linear0.
                          have /hermmxP HuE := Hu.
                          rewrite -HuE.
                          congr (block_mx _ _ _ _); try by [].
                          by rewrite adjmx_scale conjCc conjc_real.
                        }
                        have HeQ_herm : eQ \is hermmx.
                        {
                          apply/hermmxP.
                          rewrite /eQ linearB /=.
                          have /hermmxP HwE :=
                            Hpack_herm_of_herm w Hw1_herm_near.
                          have /hermmxP HqE :=
                            Hpack_herm_of_herm q Hq1_herm_near.
                          by rewrite -HwE -HqE.
                        }
                        pose D0 := @complex.Re R (\tr (dQ *m dQ)).
                        pose L0 := @complex.Re R (\tr (dQ *m eQ)).
                        pose L1 := @complex.Re R (\tr (eQ *m dQ)).
                        pose N0 := @complex.Re R (\tr (eQ *m eQ)).
                        have Hraw_expand :
                            @complex.Re R
                              (\tr ((dQ - a%:C *: eQ)^*t
                                      *m (dQ - a%:C *: eQ))) =
                            D0 - a * L0 - a * L1 + a ^+ 2 * N0.
                        {
                          have /hermmxP HdQE := HdQ_herm.
                          have /hermmxP HeQE := HeQ_herm.
                          pose D := dQ.
                          pose E := eQ.
                          rewrite -/D -/E.
                          have HDE : D^*t = D by rewrite /D -HdQE.
                          have HEE : E^*t = E by rewrite /E -HeQE.
                          have Hdiff_adj :
                              (D - a%:C *: E)^*t =
                              D - a%:C *: E.
                          {
                            rewrite [LHS]linearB /= adjmxZ conjCc conjc_real.
                            by rewrite HDE HEE.
                          }
                          rewrite Hdiff_adj mulmxBl.
                          rewrite [D *m (D - a%:C *: E)]mulmxBr.
                          rewrite [(a%:C *: E) *m (D - a%:C *: E)]mulmxBr.
                          rewrite [\tr ((D *m D - D *m (a%:C *: E)) -
                                    ((a%:C *: E) *m D -
                                     (a%:C *: E) *m (a%:C *: E)))]linearB /=.
                          rewrite [\tr (D *m D - D *m (a%:C *: E))]linearB /=.
                          rewrite [\tr ((a%:C *: E) *m D -
                                    (a%:C *: E) *m (a%:C *: E))]linearB /=.
                          rewrite raddfB /=.
                          rewrite raddfB /=.
                          rewrite raddfB /=.
                          rewrite -scalemxAr -scalemxAl.
                          rewrite !linearZ /=.
                          rewrite -[D *m pack p - D *m pack q]mulmxBr -/dQ -/D.
                          rewrite -[a%:C *: E *m E]scalemxAl linearZ /=.
                          rewrite /D0 /L0 /L1 /N0 -/D -/E.
                          rewrite (HRe_realM a (\tr (D *m E))).
                          have Haa : a * (a * @complex.Re R (\tr (E *m E))) =
                              a ^+ 2 * @complex.Re R (\tr (E *m E)).
                          {
                            by rewrite expr2 mulrA.
                          }
                          rewrite [@complex.Re R
                                    ((a%:C * \tr (E *m D))%R +
                                     a%:C *: - (a%:C * \tr (E *m E)))]raddfD /=.
                          rewrite (HRe_realM a (\tr (E *m D))).
                          rewrite [a%:C *: - (a%:C * \tr (E *m E))]scalerN.
                          rewrite [@complex.Re R (- (a%:C *: (a%:C * \tr (E *m E))))]raddfN /=.
                          rewrite scalerA -rmorphM /=.
                          change (@complex.Re R ((a * a)%:C *: \tr (E *m E))) with
                            (@complex.Re R ((a * a)%:C * \tr (E *m E))).
                          rewrite (HRe_realM (a * a) (\tr (E *m E))).
                          by rewrite opprB expr2 !addrA addrAC.
                        }
                        have Hd_normE :
                            D0 =
                            @complex.Re R (\tr (dQ^*t *m dQ)).
                        {
                          have /hermmxP HdQE := HdQ_herm.
                          by rewrite /D0 -HdQE.
                        }
                        have He_normE :
                            N0 = Ndir.
                        {
                          have /hermmxP HeQE := HeQ_herm.
                          by rewrite /N0 /Ndir -HeQE.
                        }
                        have Hcross0E : L0 = Ldir.
                        {
                          rewrite /L0.
                          rewrite /Ldir.
                          reflexivity.
                        }
                        have HcrossE :
                            L1 = Ldir.
                        {
                          by rewrite /L1 /Ldir mxtrace_mulC.
                        }
                        etransitivity; first exact: Hraw_expand.
                        rewrite Hd_normE He_normE Hcross0E HcrossE.
                        have Htwocross :
                            a * Ldir + a * Ldir = 2 * a * Ldir.
                        {
                          by rewrite mulr_natl mulr2n mulrDl.
                        }
                        have Hopcross :
                            - (a * Ldir) + - (a * Ldir) =
                            - (2 * a * Ldir).
                        {
                          by rewrite -opprD Htwocross.
                        }
                        pose R0 := @complex.Re R (\tr (dQ^*t *m dQ)).
                        pose Q0 := a ^+ 2 * Ndir.
                        change ((R0 - a * Ldir - a * Ldir) + Q0 =
                                (R0 - 2 * a * Ldir) + Q0).
                        congr (_ + Q0).
                        rewrite -[R0 - a * Ldir - a * Ldir]addrA.
                        congr (R0 + _).
                        exact: Hopcross.
                      }
                      have Hquad_ineq :
                          2 * a * Ldir <= a ^+ 2 * Ndir.
                      {
                        move: Hsq_from_min.
                        by rewrite Hquad_expand addrAC lerBrDr lerD2l.
                      }
                      have Hdivide_by_step : 2 * Ldir <= a * Ndir.
                      {
                        rewrite -(@ler_pM2l _ a); last exact: Ha_pos.
                        have Hleft : a * (2 * Ldir) = 2 * a * Ldir.
                        {
                          apply: etrans.
                          - exact: (mulrA a 2 Ldir).
                          exact: (congr1 (fun x => x * Ldir) (mulrC a 2)).
                        }
                        have Hright : a * (a * Ndir) = a ^+ 2 * Ndir.
                        {
                          apply: etrans.
                          - exact: (mulrA a a Ndir).
                          exact: (congr1 (fun x => x * Ndir) (esym (expr2 a))).
                        }
                        have Hquad_right :
                            2 * a * Ldir <= a * (a * Ndir).
                        {
                          exact: (eq_ind_r
                            (fun rhs => 2 * a * Ldir <= rhs)
                            Hquad_ineq Hright).
                        }
                        exact: (eq_ind_r
                          (fun lhs => lhs <= a * (a * Ndir))
                          Hquad_right Hleft).
                      }
                      exact: Hdivide_by_step.
                    }
                      have HLdir_lt_2Ldir : Ldir < 2 * Ldir.
                      {
                        have Hscaled : 1 * Ldir < 2 * Ldir.
                        {
                          rewrite ltr_pM2r; last exact: HLdir_pos.
                          by rewrite ltr1n.
                        }
                        by rewrite mul1r in Hscaled.
                      }
                  have H2Ldir_lt_Ldir : 2 * Ldir < Ldir :=
                    le_lt_trans Hsq_variation HaN_lt.
                  by move: (lt_trans HLdir_lt_2Ldir H2Ldir_lt_Ldir);
                    rewrite ltxx.
                }
                have Hq_orth :
                    @complex.Re R (\tr (dQ *m pack q)) = 0.
                {
                  apply/le_anti/andP; split.
                  - have Hqq : cone_member (q.1 + q.1, q.2 + q.2) :=
                      HconeD q q Hqcone Hqcone.
                    move: (Hproj _ Hqq).
                    have Hpack_qq :
                        pack (q.1 + q.1, q.2 + q.2) - pack q = pack q.
                    {
                        rewrite /pack /= opp_block_mx add_block_mx.
                        congr (block_mx _ _ _ _).
                        - by rewrite addrK.
                      - by rewrite oppr0 add0r.
                        - by rewrite oppr0 add0r.
                        - apply/matrixP=> i j.
                          rewrite !mxE.
                          case: (i == j).
                          + by rewrite !mulr1n realcD addrK.
                          + by rewrite !mulr0n oppr0 add0r.
                    }
                    by rewrite Hpack_qq.
                  - move: (Hproj (0, 0) Hcone0).
                    by rewrite Hpack0 sub0r mulmxN linearN /= raddfN /= oppr_le0.
                }
                (* Separator inequality: orthogonality to the projected cone
                   point turns the variational form into `<dQ,w> <= 0`. *)
                have Hqsep :
                    forall w : 'M[C]_(dim V) * R, cone_member w ->
                      @complex.Re R
                        (\tr (normal_pack (p.1 - q.1) (q.2 - p.2)
                                *m pack w)) <= 0.
                  {
                    move=> w Hw.
                    rewrite (Hnormal_packE q) -/dQ.
                    move: (Hproj w Hw).
                    rewrite mulmxBr linearB /= raddfB /= Hq_orth subr0.
                    by [].
                  }
                (* Strict separation: the excluded point is not the minimizer,
                   so the squared block distance is strictly positive. *)
                have Hqpos :
                    0 <
                      @complex.Re R
                          (\tr (normal_pack (p.1 - q.1) (q.2 - p.2)
                                  *m pack p)).
                  {
                    rewrite (Hnormal_packE q) -/dQ.
                    have HpackpE : pack p = dQ + pack q by rewrite /dQ addrNK.
                    rewrite HpackpE mulmxDr linearD /= raddfD /= Hq_orth addr0.
                    have Htarget_eq :
                        @complex.Re R (\tr (dQ *m dQ)) =
                        @complex.Re R (\tr (dQ^*t *m dQ)).
                    {
                      have /hermmxP HdQE := HdQ_herm.
                      by rewrite -HdQE.
                    }
                    rewrite Htarget_eq.
                  have HdQ_ne0 : dQ != 0.
                  {
                    apply/eqP=> HdQ0.
                    move/eqP: Hq_ne_p; apply.
                      apply: Hpack_inj.
                      apply/eqP.
                      by rewrite -subr_eq0 -/dQ HdQ0.
                    }
                  have Htr_ge0 : 0 <= \tr (dQ^*t *m dQ).
                  {
                    exact: formV_tr_ge0.
                  }
                  have Htr_neq0 : \tr (dQ^*t *m dQ) != 0.
                  {
                    apply/negP=> /eqP Htr0.
                    move/eqP: HdQ_ne0; apply.
                    exact: formV_tr_eq0 Htr0.
                  }
                  have Htr_gt0 : 0 < \tr (dQ^*t *m dQ).
                  {
                    by rewrite lt_def Htr_ge0 Htr_neq0.
                    }
                    have Htr_real : \tr (dQ^*t *m dQ) \is Num.real :=
                      ger0_real Htr_ge0.
                    move: Htr_gt0.
                    by rewrite -(RRe_real Htr_real) ltc0R.
                  }
                by exists q.
              }
              case: Hnearest_normal => q [Hqcone Hqsep Hqpos].
              exists (p.1 - q.1), (q.2 - p.2).
              have Hq1_herm : q.1 \is hermmx.
              {
                case: Hqcone => X [S [r [PX PS _ Hq1 _]]].
                rewrite Hq1.
                apply/hermmxP.
                have Hdiff_adj :
                    (h2mx (Psi (mx2h X)) - S)^*t =
                    (h2mx (Psi (mx2h X)))^*t - S^*t.
                { by rewrite raddfB. }
                rewrite Hdiff_adj.
                have /hermmxP HPX := HPsi_herm _ (psdmx_herm PX).
                have /hermmxP HS := psdmx_herm PS.
                by rewrite -HPX -HS.
              }
              have HYherm : (p.1 - q.1) \is hermmx.
              {
                rewrite /p /=.
                apply/hermmxP.
                have Hdiff_adj : (B - q.1)^*t = B^*t - q.1^*t.
                { by rewrite raddfB. }
                rewrite Hdiff_adj.
                have /hermmxP HBe := HB.
                have /hermmxP Hqe := Hq1_herm.
                by rewrite -HBe -Hqe.
              }
              have HZherm : Zlin (p.1 - q.1) (q.2 - p.2) \is hermmx.
              {
                apply/hermmxP.
                rewrite /Zlin [RHS]linearB /= adjmxZ conjCc conjc_real.
                have /hermmxP HAe := HA.
                have /hermmxP HPe := HPsi_dual_herm _ HYherm.
                by rewrite -HAe -HPe.
              }
              by split.
            }
            case: Hblock_separator => Y [t [HYherm HZherm HsepB HpB]].
            exists Y, t.
            split=> //.
            - move=> w Hw.
              rewrite -(Hpack_pairing Y t w).
              exact: HsepB.
            - move: HpB.
              by rewrite (Hpack_pairing Y t p) /p /=.
          }
          exact Hclosed_conic_separator.
        }
        case: Hconic_separation => Y [t [HYherm HZherm Hsep Hpsep]].
        have Ht_ge0 : 0 <= t.
        {
          have Hcone_r : cone_member (0, 1).
          {
            exists 0, 0, 1.
            split.
            - exact: psdmx0.
            - exact: psdmx0.
            - exact: ler01.
            - have HPsi0 : Psi 0 = 0 by rewrite linear0.
              by rewrite mx2h0 HPsi0 h2mx0 subr0.
            - by rewrite mulmx0 mxtrace0 add0r.
          }
          move: (Hsep _ Hcone_r).
          by rewrite /= mulmx0 mxtrace0 sub0r mulr1 oppr_le0.
        }
        have HYnonneg : dual_nonneg Y.
        {
          move=> S PS.
          have Hcone_S : cone_member (- S, 0).
          {
            exists 0, S, 0.
            split.
            - exact: psdmx0.
            - exact: PS.
            - exact: lexx.
            - have HPsi0 : Psi 0 = 0 by rewrite linear0.
              by rewrite mx2h0 HPsi0 h2mx0 sub0r.
            - by rewrite mulmx0 mxtrace0 addr0.
          }
          move: (Hsep _ Hcone_S).
          rewrite /= mulmxN linearN /= mulr0 subr0.
          move=> H.
          move: H.
          by rewrite raddfN /= oppr_le0 mxtrace_mulC.
        }
        have HZnonneg : station_nonneg Y t.
        {
          move=> X PX.
          have Hcone_X :
              cone_member (h2mx (Psi (mx2h X)),
                @complex.Re R (\tr (A *m X))).
          {
            exists X, 0, 0.
            split.
            - exact: PX.
            - exact: psdmx0.
            - exact: lexx.
            - by rewrite subr0.
            - by rewrite addr0.
          }
          have HsepX := Hsep _ Hcone_X.
          rewrite /station_nonneg /Zlin.
          have Hpair :
              \tr (X *m h2mx (Psi^*o (mx2h Y))) =
              \tr (Y *m h2mx (Psi (mx2h X))).
          {
            rewrite mxtrace_mulC.
            move: (dualso_trlfEV Psi (mx2h X) (mx2h Y)).
            rewrite /lftrace !h2mx_comp !mx2hK mxtrace_mulC.
            by move=> ->; rewrite mxtrace_mulC.
          }
          have HRe_realM : forall (c : R) (z : C),
              @complex.Re R (c%:C * z) = c * @complex.Re R z.
          {
            move=> c z.
            case: z => a b /=.
            by rewrite mul0r subr0.
          }
          rewrite mulmxBr linearB /= -scalemxAr linearZ /= Hpair.
          rewrite raddfB /= (HRe_realM t (\tr (X *m A))) mxtrace_mulC.
          move: HsepX.
          rewrite /=.
          by rewrite subr_le0 subr_ge0.
        }
        have Hobj : t * gamma < @complex.Re R (\tr (B *m Y)).
        {
          move: Hpsep.
          by rewrite mxtrace_mulC ltrBrDr add0r.
        }
        exists Y, t.
        by split.
      }
      case: Hlinear_separator =>
        Y [t [Ht_ge0 HYherm HZherm HYnonneg [HZnonneg Hobj]]].
      pose Z := Zlin Y t.
      have PY : Y \is psdmx := Hself_dual _ Y HYherm HYnonneg.
      have PZ : Z \is psdmx := Hself_dual _ Z HZherm HZnonneg.
      exists Z, Y, t.
      split=> //.
      by rewrite /Z addrC subrK.
    }
    case: Hraw_separator => Z [Y [t [Ht_ge0 PZ PY Hstat Hobj]]].
    case: (ltP 0 t) => Ht_pos.
    - by exists Z, Y, t.
    - (* If the raw separator has t = 0, perturb it by the strict dual
         witness: (Y,Z,t) + eps * (Y0, A - Psi^*[Y0], 1). *)
      have Ht0 : t = 0.
      {
        apply/eqP.
        by rewrite eq_le Ht_ge0 Ht_pos.
      }
      pose S0 := A - h2mx (Psi^*o (mx2h Y0)).
      have HY0psd : Y0 \is psdmx := pdmx_psdmx HY0pd.
      have HS0psd : S0 \is psdmx := pdmx_psdmx HS0pd.
      pose byv := @complex.Re R (\tr (B *m Y)).
      pose d0 := @complex.Re R (\tr (B *m Y0)).
      have Hbyv_pos : 0 < byv.
      {
        move: Hobj.
        by rewrite Ht0 mul0r /byv.
      }
      have [Hgamma_le_d0 | Hd0_lt_gamma] := lerP gamma d0.
      + exists (Z + S0), (Y + Y0), 1.
        split.
        * exact: ltr01.
        * exact: psdmxD PZ HS0psd.
        * exact: psdmxD PY HY0psd.
        * rewrite scale1r.
          have HdualD :
              h2mx (Psi^*o (mx2h (Y + Y0))) =
              h2mx (Psi^*o (mx2h Y)) + h2mx (Psi^*o (mx2h Y0)).
          {
            have Hmx2hD : mx2h (Y + Y0) = mx2h Y + mx2h Y0
              by rewrite linearD.
            have HPsiD :
                Psi^*o (mx2h (Y + Y0)) =
                Psi^*o (mx2h Y) + Psi^*o (mx2h Y0).
            { rewrite Hmx2hD. exact: linearD. }
            have Hh2mxD :
                h2mx (Psi^*o (mx2h Y) + Psi^*o (mx2h Y0)) =
                h2mx (Psi^*o (mx2h Y)) + h2mx (Psi^*o (mx2h Y0)).
            { by rewrite raddfD. }
            by rewrite HPsiD Hh2mxD.
          }
          rewrite HdualD /S0.
          move: Hstat.
          rewrite Ht0 scale0r => Hstat0.
          have HZY0 : h2mx (Psi^*o (mx2h Y)) + Z = 0.
          {
            by rewrite -Hstat0.
          }
          rewrite -addrA.
          rewrite [h2mx (Psi^*o (mx2h Y0)) + (Z + _)]addrA.
          rewrite [h2mx (Psi^*o (mx2h Y0)) + Z]addrC.
          rewrite !addrA.
          rewrite HZY0 add0r.
          rewrite addrC.
          by rewrite addrA addNr add0r.
        * rewrite mul1r mulmxDr linearD /= raddfD /= /byv /d0.
          apply: (le_lt_trans Hgamma_le_d0).
          by rewrite addrC ltrDl.
      + pose eps := byv / (2 * (gamma - d0)).
        have Hgap_pos : 0 < gamma - d0.
        {
          by rewrite subr_gt0.
        }
        have Heps_pos : 0 < eps.
        {
          rewrite /eps divr_gt0 //.
          by rewrite mulr_gt0 ?ltr0n.
        }
        exists (Z + eps%:C *: S0), (Y + eps%:C *: Y0), eps.
        split.
        * exact: Heps_pos.
        * apply: psdmxD; first exact: PZ.
          apply: psdmxZ; last exact: HS0psd.
          by rewrite lecR ltW.
        * apply: psdmxD; first exact: PY.
          apply: psdmxZ; last exact: HY0psd.
          by rewrite lecR ltW.
        * have HdualZD :
              h2mx (Psi^*o (mx2h (Y + eps%:C *: Y0))) =
              h2mx (Psi^*o (mx2h Y)) +
              eps%:C *: h2mx (Psi^*o (mx2h Y0)).
          {
            have Hmx2hD :
                mx2h (Y + eps%:C *: Y0) =
                mx2h Y + eps%:C *: mx2h Y0.
            {
              rewrite [Y + eps%:C *: Y0]addrC.
              rewrite (mx2hP eps%:C Y0 Y).
              by rewrite addrC.
            }
            have HPsiD :
                Psi^*o (mx2h (Y + eps%:C *: Y0)) =
                Psi^*o (mx2h Y) + eps%:C *: Psi^*o (mx2h Y0).
            {
              rewrite Hmx2hD [mx2h Y + eps%:C *: mx2h Y0]addrC.
              rewrite linearP /=.
              by rewrite addrC.
            }
            have Hh2mxD :
                h2mx (Psi^*o (mx2h Y) + eps%:C *: Psi^*o (mx2h Y0)) =
                h2mx (Psi^*o (mx2h Y)) +
                eps%:C *: h2mx (Psi^*o (mx2h Y0)).
            {
              rewrite [Psi^*o (mx2h Y) + eps%:C *: Psi^*o (mx2h Y0)]addrC.
              rewrite (h2mxP eps%:C (Psi^*o (mx2h Y0)) (Psi^*o (mx2h Y))).
              by rewrite addrC.
            }
            by rewrite HPsiD Hh2mxD.
          }
          rewrite HdualZD /S0.
          move: Hstat.
          rewrite Ht0 scale0r => Hstat0.
          have HZY0 : h2mx (Psi^*o (mx2h Y)) + Z = 0.
          {
            by rewrite -Hstat0.
          }
          rewrite -addrA.
          rewrite [eps%:C *: h2mx (Psi^*o (mx2h Y0)) + (Z + _)]addrA.
          rewrite [eps%:C *: h2mx (Psi^*o (mx2h Y0)) + Z]addrC.
          rewrite !addrA HZY0 add0r.
          by rewrite scalerBr addrCA subrr addr0.
        * rewrite mulmxDr linearD /= -scalemxAr linearZ /= raddfD /=.
          have HRe_realM : forall (c : R) (z : C),
              @complex.Re R (c%:C * z) = c * @complex.Re R z.
          {
            move=> c z.
            case: z => a b /=.
            by rewrite mul0r subr0.
          }
          rewrite (HRe_realM eps (\tr (B *m Y0))) /byv /d0.
          have Hgoal : eps * (gamma - d0) < byv.
          {
            have Hden_neq0 : 2 * (gamma - d0) != 0.
            {
              by rewrite mulf_eq0 pnatr_eq0 /= gt_eqF.
            }
            have Hhalf : eps * (gamma - d0) = byv / 2.
            {
              rewrite /eps.
              rewrite invfM ?unitfE ?gt_eqF ?pnatr_eq0 //.
              by rewrite -mulrA divfK ?gt_eqF.
            }
            rewrite Hhalf.
            rewrite [byv / 2]mulrC.
            rewrite -[X in X < byv]mul1r.
            rewrite mul1r -[byv]mul1r.
            rewrite [X in 2^-1 * X < _]mul1r.
            rewrite ltr_pM2r //.
            rewrite -div1r ltr_pdivrMr; last by rewrite ltr0n.
            by rewrite mul1r ltr1n.
          }
          move: Hgoal.
          by rewrite mulrBr ltrBlDr addrC.
  }

  exact Hseparator.
Qed.

(* path: entropy:sdp_strong_primal -> entropy:min_koenig -> *)
(*   entropy:min_omni -> entropy:minmax_dual -> entropy:smooth_iso_hmax -> *)
(*   entropy:entropy_data_proc -> *)
(*   bb84:bb84_secret *)
Lemma sdp_strong_primal (alpha beta : R) :
  A \is hermmx ->
  B \is hermmx ->
  (forall X : 'M[C]_(dim U),
      X \is hermmx -> h2mx (Psi (mx2h X)) \is hermmx) ->
  has_inf sdp_primal_set ->
  alpha = ExtNumTopology.etinf sdp_primal_set ->
  beta = ExtNumTopology.etsup sdp_dual_set ->
  (exists Y : 'M[C]_(dim V),
      Y \is pdmx /\ (A - h2mx (Psi^*o (mx2h Y))) \is pdmx) ->
  alpha = beta /\
  exists X : 'M[C]_(dim U),
    [/\ X \is psdmx,
        h2mx (Psi (mx2h X)) >= B &
        @complex.Re R (\tr (A *m X)) = alpha].
Proof.
  move=> HA HB HPsi_herm HinfP Halpha Hbeta [Y0 [HY0pd HS0pd]].
  pose S0 := A - h2mx (Psi^*o (mx2h Y0)).
  have HY0psd : Y0 \is psdmx := pdmx_psdmx HY0pd.
  have HS0psd : S0 \is psdmx := pdmx_psdmx HS0pd.
  have Hdual0_feas : h2mx (Psi^*o (mx2h Y0)) <= A.
  {
    by rewrite le_lownerE.
  }
  have Hweak_pointwise :
      forall (X : 'M[C]_(dim U)) (Y : 'M[C]_(dim V)),
        X \is psdmx ->
        h2mx (Psi (mx2h X)) >= B ->
        Y \is psdmx ->
        h2mx (Psi^*o (mx2h Y)) <= A ->
        @complex.Re R (\tr (B *m Y)) <= @complex.Re R (\tr (A *m X)).
  {
    move=> X Y PX HfeasX PY HfeasY.
    have HBY_le_Psi :
        \tr (B *m Y) <= \tr (h2mx (Psi (mx2h X)) *m Y).
    {
      move/le_lownerE_psdtr: HfeasX => /(_ Y PY).
      by rewrite mxtrace_mulC.
    }
    have HPsiY_le_A :
        \tr (h2mx (Psi^*o (mx2h Y)) *m X) <= \tr (A *m X).
    {
      move/le_lownerE_psdtr: HfeasY => /(_ X PX).
      by [].
    }
    have Hpair :
        \tr (h2mx (Psi (mx2h X)) *m Y) =
        \tr (h2mx (Psi^*o (mx2h Y)) *m X).
    {
      move: (dualso_trlfEV Psi (mx2h X) (mx2h Y)).
      rewrite /lftrace !h2mx_comp !mx2hK mxtrace_mulC.
      by [].
    }
    have Htr_le : \tr (B *m Y) <= \tr (A *m X).
    {
      apply: (le_trans HBY_le_Psi).
      rewrite Hpair.
      exact: HPsiY_le_A.
    }
    have HBY_real : \tr (B *m Y) \is Num.real.
    {
      apply/CrealP.
      rewrite -mxtrace_adj adjmxM.
      have /hermmxP BE := HB.
      have /hermmxP YE := psdmx_herm PY.
      by rewrite -BE -YE mxtrace_mulC.
    }
    have HAX_real : \tr (A *m X) \is Num.real.
    {
      apply/CrealP.
      rewrite -mxtrace_adj adjmxM.
      have /hermmxP AE := HA.
      have /hermmxP XE := psdmx_herm PX.
      by rewrite -AE -XE mxtrace_mulC.
    }
    by rewrite -(RRe_real HBY_real) -(RRe_real HAX_real) lecR in Htr_le.
  }
  have Hdual_nonempty : (sdp_dual_set !=set0)%classic.
  {
    exists (@complex.Re R (\tr (B *m Y0))).
    exists Y0.
    by split.
  }
  have Hdual_has_sup : has_sup sdp_dual_set.
  {
    split.
    - exact: Hdual_nonempty.
    - case: HinfP => Hprimal_nonempty _.
      case: Hprimal_nonempty => x0 Hx0.
      case: Hx0 => X0 [PX0 HfeasX0 _].
      exists (@complex.Re R (\tr (A *m X0))) => v [Y [PY HfeasY ->]].
      exact: (Hweak_pointwise X0 Y PX0 HfeasX0 PY HfeasY).
  }
  have Hbeta_le_alpha : beta <= alpha.
  {
    rewrite Hbeta.
    apply: (ExtNumTopology.etsup_least_ubound Hdual_has_sup).
    move=> v [Y [PY HfeasY ->]].
    rewrite Halpha /ExtNumTopology.etinf lerNr.
    apply: ExtNumTopology.etsup_least_ubound.
    - case: HinfP => Hprimal_nonempty Hprimal_lb.
      split.
      + case: Hprimal_nonempty => u0 Hu0.
        by exists (- u0), u0.
      + case: Hprimal_lb => l Hl.
        exists (- l) => w [u Hu <-].
        by rewrite lerN2; apply: Hl.
    - move=> w [u [X [PX HfeasX ->]] <-].
      rewrite lerN2.
      exact: (Hweak_pointwise X Y PX HfeasX PY HfeasY).
  }
  pose k0 := @complex.Re R (\tr (B *m Y0)).
  pose c0 := \sum_i (spectral_diag S0 0 i)^-1.
  have Hdual0_mem : sdp_dual_set k0.
  {
    exists Y0.
    by split.
  }
  have Hk0_le_beta : k0 <= beta.
  {
    rewrite Hbeta.
    exact: (ExtNumTopology.etsup_upper_bound Hdual_has_sup Hdual0_mem).
  }
  have Hk0_le_alpha : k0 <= alpha := le_trans Hk0_le_beta Hbeta_le_alpha.
  have /pdmxP [_ /posmxP HS0pos] := HS0pd.
  have Hc0_pos : 0 < c0.
  {
    have HdimU_pos : (0 < dim U)%N := dim_proper.
    pose i0 : 'I_(dim U) := Ordinal HdimU_pos.
    rewrite /c0.
    rewrite (bigD1 i0) //.
    have Hterm_pos : 0 < GRing.inv (spectral_diag S0 0 i0).
    {
      move: (HS0pos 0 i0).
      by rewrite posrE invr_gt0.
    }
    have Hrest_ge0 : 0 <= \sum_(i | i != i0) GRing.inv (spectral_diag S0 0 i).
    {
      elim/big_ind : _ => // [a b Ha Hb|i _].
      - exact: addr_ge0 Ha Hb.
      - move: (HS0pos 0 i).
        rewrite posrE => Hi_pos.
        apply: ltW.
        by rewrite /GRing.inv invr_gt0.
    }
    apply: (lt_le_trans Hterm_pos).
    by rewrite lerDl.
  }
  pose c0R := @c2r R C c0.
  have Hc0R_pos : 0 < c0R.
  {
    by rewrite /c0R; exact: ExtNumTopology.c2r_gt0.
  }
  have Hc0E : c0 = c0R%:C.
  {
    rewrite /c0R c2rK.
    - reflexivity.
    - exact: gtr0_real Hc0_pos.
  }
  have HId_le_cS0 : (1%:M : 'M[C]_(dim U)) <= c0 *: S0.
  {
    have /pdmxP [HS0herm /posmxP HS0pos0] := HS0pd.
    pose P0 := eigenmx S0.
    pose d0 := spectral_diag S0.
    have HP0u : P0 \is unitarymx := eigen_unitarymx S0.
    have HS0dec : S0 = P0 *m diag_mx d0 *m P0^*t.
    {
      move: (hermitian_normalmx HS0herm).
      by rewrite -/P0 -/d0; move/eigen_dec.
    }
    have Hdiag_psd : (c0 *: diag_mx d0 - 1%:M) \is psdmx.
    {
      have -> : c0 *: diag_mx d0 - 1%:M =
          diag_mx (\row_i (c0 * d0 0 i - 1)).
      {
        apply/matrixP=> i j.
        have [Hij|Hij] := eqVneq i j.
        - by move: Hij => ->; rewrite !mxE eqxx.
        - by rewrite !mxE (negbTE Hij) mulr0 subrr.
      }
      apply/diagmx_nnegmx_psd/nnegmxP=> i j.
      rewrite !mxE nnegrE subr_ge0.
      have Hd0j_pos : 0 < d0 0 j.
      {
        move: (HS0pos0 0 j).
        by rewrite posrE.
      }
      have Hinv_le : ((d0 0 j)^-1)%R <= c0.
      {
        rewrite /c0 (bigD1 j) //.
        rewrite lerDl.
        apply: sumr_ge0 => k _.
        have Hd0k_pos : 0 < d0 0 k.
        {
          move: (HS0pos0 0 k).
          by rewrite posrE.
        }
        by rewrite invr_ge0 (ltW Hd0k_pos).
      }
      have Htmp : ((d0 0 j)^-1)%R * d0 0 j <= c0 * d0 0 j.
      {
        by rewrite (ler_pM2r Hd0j_pos).
      }
      move: Htmp.
      by rewrite mulVf ?lt0r_neq0.
    }
    rewrite le_lownerE.
    have HcS0 : P0 *m (c0 *: diag_mx d0) *m P0^*t = c0 *: S0.
    {
      rewrite HS0dec.
      by rewrite -scalemxAr -scalemxAl.
    }
    have Hconj :
        c0 *: S0 - 1%:M =
        P0 *m (c0 *: diag_mx d0 - 1%:M) *m P0^*t.
    {
      rewrite mulmxBr mulmxBl HcS0.
      have -> : P0 *m 1%:M *m P0^*t = 1%:M.
        by rewrite mulmx1 unitarymxK.
      by [].
    }
    rewrite Hconj.
    exact: psdmx_bimap_closed_gen Hdiag_psd.
  }
  have Halpha_le_beta : alpha <= beta.
  {
    apply/negP=> Halpha_gt_beta.
    have Hbeta_lt_alpha : beta < alpha.
    {
      case: (lerP alpha beta) => [Halpha_le_beta|Hbeta_lt_alpha].
      - exfalso.
        exact: Halpha_gt_beta Halpha_le_beta.
      - by [].
    }
    pose gamma := (alpha + beta) / 2.
    have Hgamma_lt_alpha : gamma < alpha.
    {
      rewrite /gamma ltr_pdivrMr ?ltr0n ?mul1r //.
      by rewrite ?mulr_natl ?mulr_natr mulr2n ltrD2l.
    }
    have Hbeta_lt_gamma : beta < gamma.
    {
      rewrite /gamma ltr_pdivlMr ?ltr0n ?mul1r //.
      by rewrite ?mulr_natl ?mulr_natr mulr2n ltrD2r.
    }
    have Hex_gamma :
        exists Y : 'M[C]_(dim V),
          [/\ Y \is psdmx,
              h2mx (Psi^*o (mx2h Y)) <= A &
              gamma < @complex.Re R (\tr (B *m Y))].
    {
      have Hgamma_primal_infeasible :
          ~ exists X : 'M[C]_(dim U),
              [/\ X \is psdmx,
                  h2mx (Psi (mx2h X)) >= B &
                  @complex.Re R (\tr (A *m X)) <= gamma].
      {
        case=> X [PX HfeasX Hobj_le_gamma].
        have Halpha_le_obj :
            alpha <= @complex.Re R (\tr (A *m X)).
        {
          rewrite Halpha /sdp_primal_set.
          apply: ge_inf.
          - case: HinfP => _ [l Hl].
            by exists l => w Hw; exact: Hl _ Hw.
          - exists X.
            by split.
        }
        have Halpha_le_gamma : alpha <= gamma :=
          le_trans Halpha_le_obj Hobj_le_gamma.
        by move: (lt_le_trans Hgamma_lt_alpha Halpha_le_gamma); rewrite ltxx.
      }
      have Hfarkas_gamma :
          exists Y : 'M[C]_(dim V),
            [/\ Y \is psdmx,
                h2mx (Psi^*o (mx2h Y)) <= A &
                gamma < @complex.Re R (\tr (B *m Y))].
      {
        have Hsep_gamma :
            exists (Z : 'M[C]_(dim U)) (Y : 'M[C]_(dim V)) (t : R),
              [/\ 0 < t,
                  Z \is psdmx,
                  Y \is psdmx,
                  t%:C *: A =
                    h2mx (Psi^*o (mx2h Y)) + Z &
                t * gamma < @complex.Re R (\tr (B *m Y))].
        {
          have Hstrict_dual :
              exists Y0 : 'M[C]_(dim V),
                Y0 \is pdmx /\
                (A - h2mx (Psi^*o (mx2h Y0))) \is pdmx.
          {
            by exists Y0.
          }
          exact (@sdp_primal_farkas_separator
                    gamma HA HB HPsi_herm
                    Hstrict_dual Hgamma_primal_infeasible).
        }
        case: Hsep_gamma => Z [Y [t [Ht_pos PZ PY Hstat Hobj_gt]]].
        exists (t^-1%:C *: Y).
        split.
        - apply: psdmxZ; last exact: PY.
          by rewrite lecR invr_ge0 ltW.
        - rewrite le_lownerE.
          have Hdual_scaled :
              h2mx (Psi^*o (mx2h (t^-1%:C *: Y))) =
              t^-1%:C *: h2mx (Psi^*o (mx2h Y)).
          {
            have Hmx2hZ : mx2h (t^-1%:C *: Y) = t^-1%:C *: mx2h Y
              by rewrite linearZ.
            have HPsiZ :
                Psi^*o (mx2h (t^-1%:C *: Y)) =
                t^-1%:C *: Psi^*o (mx2h Y).
            { rewrite Hmx2hZ. exact: linearZ. }
            have Hh2mxZ :
                h2mx (t^-1%:C *: Psi^*o (mx2h Y)) =
                t^-1%:C *: h2mx (Psi^*o (mx2h Y)).
            {
              move: (h2mxP t^-1%:C (Psi^*o (mx2h Y)) 0).
              by rewrite h2mx0 !addr0.
            }
            by rewrite HPsiZ Hh2mxZ.
          }
          rewrite Hdual_scaled.
          have Ht_neq0 : t != 0.
          {
            by rewrite gt_eqF.
          }
          have Hscale_stat :
              A = t^-1%:C *: (h2mx (Psi^*o (mx2h Y)) + Z).
          {
            rewrite -Hstat scalerA.
            have -> : t^-1%:C * t%:C = 1 :> C.
              by rewrite -rmorphM /= mulVf // rmorph1.
            by rewrite scale1r.
          }
          rewrite Hscale_stat scalerDr addrAC subrr add0r.
          apply: psdmxZ; last exact: PZ.
          by rewrite lecR invr_ge0 ltW.
        - have HBY_real : \tr (B *m Y) \is Num.real.
          {
            apply/CrealP.
            rewrite -mxtrace_adj adjmxM.
            have /hermmxP BE := HB.
            have /hermmxP YE := psdmx_herm PY.
            by rewrite -BE -YE mxtrace_mulC.
          }
          have Hobj_scaled :
              @complex.Re R (\tr (B *m (t^-1%:C *: Y))) =
              t^-1 * @complex.Re R (\tr (B *m Y)).
          {
            rewrite -scalemxAr linearZ /=.
            by rewrite -(RRe_real HBY_real) -realcM re_realid.
          }
          rewrite Hobj_scaled.
          have Ht_neq0 : t != 0.
          {
            by rewrite gt_eqF.
          }
          rewrite -(@ltr_pM2l _ t) //.
          by rewrite [t * (t^-1 * _)]mulrA [t * t^-1]mulrC mulVf ?mul1r.
      }
      exact: Hfarkas_gamma.
    }
    case: Hex_gamma => Y [PY HfeasY HgammaY].
    have HY_mem : sdp_dual_set (@complex.Re R (\tr (B *m Y))).
    {
      exists Y.
      by split.
    }
    have HY_le_beta : @complex.Re R (\tr (B *m Y)) <= beta.
    {
      rewrite Hbeta.
      exact: (ExtNumTopology.etsup_upper_bound Hdual_has_sup HY_mem).
    }
    have Hgamma_lt_beta : gamma < beta.
    {
      exact: lt_le_trans HgammaY HY_le_beta.
    }
    by move: (lt_trans Hgamma_lt_beta Hbeta_lt_gamma); rewrite ltxx.
  }
  have [Xopt [PXopt HfeasXopt HXopt]] :
      exists X : 'M[C]_(dim U),
        [/\ X \is psdmx,
            h2mx (Psi (mx2h X)) >= B &
            @complex.Re R (\tr (A *m X)) = alpha].
  {
    pose obj (X : 'M[C]_(dim U)) := @complex.Re R (\tr (A *m X)).
    pose epsn (k : nat) : R := 1 / (k.+1)%:R.
    have Hepsn_pos k : 0 < epsn k.
    {
      rewrite /epsn div1r invr_gt0.
      exact: ltr0Sn.
    }
    have Hepsn_le1 k : epsn k <= 1.
    {
      have Hkp : 0 < (k.+1)%:R :> R.
      {
        by rewrite ltr0n.
      }
      rewrite /epsn div1r (invr_le1 (unitf_gt0 Hkp) Hkp).
      change (((1%N)%:R : R) <= (k.+1)%:R).
      by rewrite ler_nat.
    }
    have [cm Hcm_pos Hcm_bound] :
        exists2 cm : C, 0 < cm &
          forall X : 'M[C]_(dim U), mx_norm X <= cm * trnorm X.
    {
      exact: cmnorm_bounded.
    }
    have Hsup_neg_primal : has_sup (-%R @` sdp_primal_set).
    {
      exact/has_inf_supN.
    }
    have Halpha_negsup :
        alpha = - ExtNumTopology.etsup (-%R @` sdp_primal_set).
    {
      by rewrite Halpha /ExtNumTopology.etinf.
    }
    have Hex_X :
        forall k,
          exists X : 'M[C]_(dim U),
            [/\ X \is psdmx,
                h2mx (Psi (mx2h X)) >= B &
                obj X < alpha + epsn k].
    {
      move=> k.
      have [w Hw Hwgt] :=
        ExtNumTopology.etsup_adherent (Hepsn_pos k) Hsup_neg_primal.
      case: Hw => v Hv Hw.
      case: Hv => X [PX HfeasX HXv].
      have Hvlt : v < alpha + epsn k.
      {
        move: Hwgt.
        rewrite -Hw.
        rewrite -ltrN2 opprB opprK addrC -Halpha_negsup.
        by [].
      }
      exists X; split=> //.
      by rewrite /obj -HXv.
    }
    have [f Hf] := choice Hex_X.
    pose Xseq (k : nat) := f k.
    have HXpsd k : Xseq k \is psdmx.
    {
      by case: (Hf k).
    }
    have HXfeas k : h2mx (Psi (mx2h (Xseq k))) >= B.
    {
      by case: (Hf k).
    }
    have Hobj_up k : obj (Xseq k) < alpha + epsn k.
    {
      by case: (Hf k).
    }
    have Hobj_lb k : alpha <= obj (Xseq k).
    {
      rewrite Halpha /sdp_primal_set /obj.
      apply: ge_inf.
      - case: HinfP => _ [l Hl].
        by exists l => w Hw; exact: Hl _ Hw.
      - exists (Xseq k); split.
        + exact: HXpsd.
        + exact: HXfeas.
        + reflexivity.
    }
    pose rbound := c0R * (alpha + 1 - k0).
    have Hrbound_pos : 0 < rbound.
    {
      have Htmp : 0 < alpha + 1 - k0.
      {
        rewrite ltrBrDr add0r.
        have Htmp1 : k0 < alpha + 1.
        {
          have Htmp1' : k0 + 0 < alpha + 1.
          {
            exact: ler_ltD Hk0_le_alpha ltr01.
          }
          rewrite addr0 in Htmp1'.
          exact: Htmp1'.
        }
        exact: Htmp1.
      }
      by rewrite /rbound mulr_gt0.
    }
    have Hnorm_bound k : mx_norm (Xseq k) <= cm * rbound%:C.
    {
      have HtrX_real : \tr (Xseq k) \is Num.real.
      {
        exact: ger0_real (psdmx_trace (HXpsd k)).
      }
      have HS0_herm : S0 \is hermmx := psdmx_herm HS0psd.
      have HS0X_real : \tr (S0 *m Xseq k) \is Num.real.
      {
        apply/CrealP.
        rewrite -mxtrace_adj adjmxM.
        have /hermmxP SE := HS0_herm.
        have /hermmxP XE := psdmx_herm (HXpsd k).
        by rewrite -SE -XE mxtrace_mulC.
      }
      have HtrX_le_gap :
          @complex.Re R (\tr (Xseq k)) <=
          c0R * @complex.Re R (\tr (S0 *m Xseq k)).
      {
        move/le_lownerE_psdtr: HId_le_cS0 => /(_ (Xseq k) (HXpsd k)).
        rewrite mul1mx -scalemxAl linearZ /= Hc0E.
        by rewrite -(RRe_real HtrX_real) -(RRe_real HS0X_real) -realcM re_realid lecR.
      }
      have HpsiX_herm : h2mx (Psi (mx2h (Xseq k))) \is hermmx.
      {
        exact: HPsi_herm (psdmx_herm (HXpsd k)).
      }
      have HY0_herm : Y0 \is hermmx := psdmx_herm HY0psd.
      have Hdualterm_real :
          \tr (h2mx (Psi (mx2h (Xseq k))) *m Y0) \is Num.real.
      {
        apply/CrealP.
        rewrite -mxtrace_adj adjmxM.
        have /hermmxP PE := HpsiX_herm.
        have /hermmxP YE := HY0_herm.
        by rewrite -PE -YE mxtrace_mulC.
      }
      have Hdual_ge :
          k0 <= @complex.Re R (\tr (h2mx (Psi (mx2h (Xseq k))) *m Y0)).
      {
        move/le_lownerE_psdtr: (HXfeas k) => /(_ Y0 HY0psd).
        move=> Htr.
        have HBY0_real : \tr (B *m Y0) \is Num.real.
        {
          apply/CrealP.
          rewrite -mxtrace_adj adjmxM.
          have /hermmxP BE := HB.
          have /hermmxP YE := HY0_herm.
          by rewrite -BE -YE mxtrace_mulC.
        }
        by rewrite /k0 -(RRe_real HBY0_real) -(RRe_real Hdualterm_real) lecR in Htr.
      }
      have Hpair :
          \tr (h2mx (Psi^*o (mx2h Y0)) *m Xseq k) =
          \tr (h2mx (Psi (mx2h (Xseq k))) *m Y0).
      {
        move: (dualso_trlfEV Psi (mx2h (Xseq k)) (mx2h Y0)).
        rewrite /lftrace !h2mx_comp !mx2hK mxtrace_mulC.
        by [].
      }
      have Hobj_split :
          obj (Xseq k) =
          @complex.Re R (\tr (S0 *m Xseq k)) +
          @complex.Re R (\tr (h2mx (Psi (mx2h (Xseq k))) *m Y0)).
      {
        rewrite /obj.
        have -> : A = S0 + h2mx (Psi^*o (mx2h Y0)).
          by rewrite /S0 subrK.
        rewrite mulmxDl.
        have HtrD :
            \tr (S0 *m Xseq k + h2mx (Psi^*o (mx2h Y0)) *m Xseq k) =
            \tr (S0 *m Xseq k) +
            \tr (h2mx (Psi^*o (mx2h Y0)) *m Xseq k).
        { by rewrite linearD. }
        by rewrite HtrD raddfD /= Hpair.
      }
      have Hgap_le_obj :
          @complex.Re R (\tr (S0 *m Xseq k)) <= obj (Xseq k) - k0.
      {
        have Htmp :
            @complex.Re R (\tr (S0 *m Xseq k)) + k0 <= obj (Xseq k).
        {
          by rewrite Hobj_split lerD2l.
        }
        move: Htmp.
        by rewrite lerBrDr.
      }
      have HtrX_le_obj :
          @complex.Re R (\tr (Xseq k)) <= c0R * (obj (Xseq k) - k0).
      {
        apply: (le_trans HtrX_le_gap).
        by rewrite ler_pM2l.
      }
      have Hobjmk_lt :
          obj (Xseq k) - k0 < alpha + 1 - k0.
      {
        have Hobj_lt_alpha1 : obj (Xseq k) < alpha + 1.
        {
          apply: (lt_le_trans (Hobj_up k)).
          by rewrite lerD2l.
        }
        rewrite ltrBrDr -addrA addNr addr0.
        exact: Hobj_lt_alpha1.
      }
      have HtrX_le_rbound :
          @complex.Re R (\tr (Xseq k)) <= rbound.
      {
        apply: (le_trans HtrX_le_obj).
        apply: ltW.
        rewrite /rbound.
        by rewrite ltr_pM2l.
      }
      apply: (le_trans (Hcm_bound (Xseq k))).
      rewrite (psdmx_trnorm (HXpsd k)).
      have -> : \tr (Xseq k) = (@complex.Re R (\tr (Xseq k)))%:C.
      {
        exact: esym (RRe_real HtrX_real).
      }
      rewrite ler_pM2l // lecR.
      exact: HtrX_le_rbound.
    }
    have [g [Hg Hcvg_Xsub]] := ExtNumTopology.Bolzano_Weierstrass Hnorm_bound.
    pose Xsub (k : nat) := Xseq (g k).
    pose Xopt := limn Xsub.
    have Hcvg_Xsub_to :=
      (proj2 (cmxcvgn_limnE Xsub Xopt) (conj erefl Hcvg_Xsub)).
    have HXopt_ge0 : (0 : 'M[C]_(dim U)) <= Xopt.
    {
      have HXsub_lbounded : lbounded_by (0 : 'M[C]_(dim U)) Xsub.
      {
        move=> k.
        move: (HXpsd (g k)).
        by rewrite /Xsub le_lownerE subr0.
      }
      exact: cmxlimn_ge Hcvg_Xsub HXsub_lbounded.
    }
    have PXopt : Xopt \is psdmx.
    {
      by rewrite le_lownerE subr0 in HXopt_ge0.
    }
    pose PsiM (X : 'M[C]_(dim U)) := h2mx (Psi (mx2h X)).
    have HPsiM_linear : linear PsiM.
    {
      move=> a X Y.
      rewrite /PsiM.
      have HPsi :
          Psi (mx2h (a *: X + Y)) =
          a *: Psi (mx2h X) + Psi (mx2h Y).
      { rewrite (mx2hP a X Y). exact: linearP. }
      rewrite HPsi.
      exact: h2mxP.
    }
    have Hcvg_PsiXsub :
        cvgn (PsiM \o Xsub)%FUN.
    {
      apply: is_cmxcvgn_lfun.
      - exact: HPsiM_linear.
      - exact: Hcvg_Xsub.
    }
    have Hlim_PsiXsub :
        limn (PsiM \o Xsub)%FUN = PsiM Xopt.
    {
      exact: cmxlimn_lfun HPsiM_linear Hcvg_Xsub.
    }
    have HfeasXopt : PsiM Xopt >= B.
    {
      have Hpsi_lb :
          lbounded_by B (PsiM \o Xsub)%FUN.
      {
        move=> k.
        exact: HXfeas (g k).
      }
      have Hpsi_ge_lim :
          B <= limn (PsiM \o Xsub)%FUN.
      {
        exact: cmxlimn_ge Hcvg_PsiXsub Hpsi_lb.
      }
      rewrite Hlim_PsiXsub in Hpsi_ge_lim.
      exact: Hpsi_ge_lim.
    }
    have HAX_linear : linear (fun X : 'M[C]_(dim U) => A *m X).
    {
      move=> a X Y.
      by rewrite mulmxDr scalemxAr.
    }
    have Hcvg_AXsub_to :
        ((fun k => A *m Xsub k) @ \oo --> A *m Xopt)%classic.
    {
      apply: cmxcvgn_lfun.
      - exact: HAX_linear.
      - exact: Hcvg_Xsub_to.
    }
    have Hcvg_trAXsub_to :
        ((fun k => \tr (A *m Xsub k)) @ \oo --> \tr (A *m Xopt))%classic.
    {
      exact: cmxcvgn_trace Hcvg_AXsub_to.
    }
    pose objsub := fun k : nat => (obj (Xsub k) : R^o).
    have Hcvg_objsub_to :
        (objsub @ \oo -->
         (@complex.Re R (\tr (A *m Xopt)) : R^o))%classic.
    {
      rewrite /objsub /obj.
      exact: Re_cvgn_realV Hcvg_trAXsub_to.
    }
    have Hcvg_objsub_alpha :
        (objsub @ \oo --> (alpha : R^o))%classic.
    {
      apply/cvgrPdist_lt=> _ /posnumP[e].
      have [N _ HN] := near_infty_natSinv_lt e.
      near=> k.
      have HNk : (N <= k)%N by near: k; exists N.
      have Hgk_ge : (k <= g k)%N := nchain_ge Hg k.
      have Heps_lt : epsn (g k) < e%:num.
      {
        rewrite /epsn div1r.
        have /(_ (g k))/(_ (leq_trans HNk Hgk_ge)) HNgk := HN.
        exact: HNgk.
      }
      have Hobj_lb_sub : alpha <= obj (Xsub k).
      {
        exact: Hobj_lb (g k).
      }
      have Hobj_up_sub : obj (Xsub k) < alpha + epsn (g k).
      {
        exact: Hobj_up (g k).
      }
      rewrite distrC ger0_norm.
      - have Hgap_lt : obj (Xsub k) - alpha < epsn (g k).
        {
          move: Hobj_up_sub.
          by rewrite ltrBlDr addrC.
        }
        exact: (lt_trans Hgap_lt Heps_lt).
      - by rewrite subr_ge0.
    }
    Unshelve. all: end_near.
    have HXopt_obj :
        @complex.Re R (\tr (A *m Xopt)) = alpha.
    {
      have Hlim1 : limn objsub = @complex.Re R (\tr (A *m Xopt)).
      {
        exact: cvg_lim Hcvg_objsub_to.
      }
      have Hlim2 : limn objsub = alpha.
      {
        exact: cvg_lim Hcvg_objsub_alpha.
      }
      by rewrite -Hlim1 Hlim2.
    }
    exists Xopt.
    by split.
  }
  split.
  - apply/eqP.
    by rewrite eq_le Hbeta_le_alpha Halpha_le_beta.
  - by exists Xopt.
Qed.

End SDPStrongPrimal.

End FvqkdReal.
