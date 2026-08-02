(* -------------------------------------------------------------------- *)
(* prop.v — Smooth-entropy isometric invariance and duality              *)
(* -------------------------------------------------------------------- *)
(* Module: entropy.smooth.prop                      *)
(* Source: Tomamichel, 'A Framework for Non-Asymptotic Quantum          *)
(*   Information Theory' (PhD thesis, arXiv:1203.2142), Proposition 5.3  *)
(*   (tex pr:smooth-iso) and Theorem 5.4 (tex th:smooth-dual).          *)
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
From quantum.dirac Require Import hstensor setdec.

Import Order.TTheory GRing.Theory Num.Theory Num.Def MxLownerOrder.
Import VectorInternalTheory.

(* --- FVQKD imports --- *)
From utils Require Import exports.
From entropy Require Import def prop pre.
From entropy.conv Require Import prop minmax_dual.
From entropy.smooth Require Import sm.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Open Scope ring_scope.
Local Open Scope lfun_scope.
Local Open Scope hspace_scope.

Section FvqkdReal.
Variable R : realType.
Notation C := (@hermitian.C R).
Notation chsType := (@chsType R).

(* ================================================================== *)
(* Isometric invariance of smooth min/max-entropy                       *)
(* Tomamichel thesis (arXiv:1203.2142), Proposition 5.3 — tex pr:smooth-iso. *)
(* math: for embeddings U : A -> A' and V : B -> B',                     *)
(*   H^ε_min(A|B)_ρ = H^ε_min(A'|B')_{(U⊗V)ρ(U⊗V)†}                      *)
(*   H^ε_max(A|B)_ρ = H^ε_max(A'|B')_{(U⊗V)ρ(U⊗V)†}                      *)
(* consumer: pr_si is used downstream by the BB84 secrecy proof. *)
(* ================================================================== *)

(* classical_X_hmin_lift *)
(* tex: pr:class/bounds-1 first ineq min-half — the Petz-recovery content,  *)
(*      Tomamichel thesis (arXiv:1203.2142), Proposition 5.9.               *)
(* math: for ρ_XAB classical on X and 0 ≤ ε < √(Tr ρ_XAB), every τ_AB in   *)
(* B^ε(Tr_X ρ_XAB) lifts to a classical-on-X τ_XAB in B^ε(ρ_XAB) with      *)
(* hminE B τ_AB ≤ hminE B τ_XAB.                                           *)
(* Ambience: the proof uses the already ambient `X` register as the        *)
(* extension/dephasing room. No closed mini-universe or private singleton  *)
(* labels are introduced; all auxiliary casts stay inside the ambient      *)
(* set-labelled surface of this section.                                   *)
Section ClassHminLift.
Variable (L : finType) (H : L -> chsType).

(* path: entropy:classical_X_hmin_lift -> entropy:smooth_iso_hmax -> *)
(*   entropy:entropy_data_proc -> *)
(*   bb84:bb84_secret *)
Lemma classical_X_hmin_lift
    (* The `A` and `B` systems are supplied by the upstream class-bounds
       ambience; the proof does not create a private labelled universe. *)
    (X A B : {set L})
    (disAB : [disjoint A & B])
    (disXAB : [disjoint X & (A :|: B)])
    (rhoXAB : 'F[H]_(X :|: (A :|: B))) (eps : R)
    (tauAB : 'F[H]_(A :|: B)) :
  rhoXAB \is denlf ->
  (forall x x' : 'Idx[H]_X, x' != x ->
    (([> deltav x ; deltav x <] \O (\1 : 'F_(A :|: B))) \o rhoXAB \o
     ([> deltav x' ; deltav x' <] \O (\1 : 'F_(A :|: B)))) = 0) ->
  0 <= eps < Num.sqrt (@complex.Re R (\Tr rhoXAB)) ->
  eps_ball eps (ptrace_castl disXAB rhoXAB) tauAB ->
  exists tauXAB : 'F[H]_(X :|: (A :|: B)),
    eps_ball eps rhoXAB tauXAB /\
    (hminE B tauAB <= hminE B tauXAB)%E.
Proof.
  move=> Hrho_den Hclass Heps HtauAB_ball.
  pose S_AB := A :|: B.
  have Prho : rhoXAB \is psdlf := denlf_psd Hrho_den.
  have Hrho_tr : @complex.Re R (\Tr rhoXAB) <= 1.
  {
    have Hreal : \Tr rhoXAB \is Num.real := ger0_real (psdlf_trlf Prho).
    by move: (denlf_trlf Hrho_den); rewrite -(RRe_real Hreal) lecR.
  }
  have PtauAB : tauAB \is psdlf := eps_ball_psdlf HtauAB_ball.
  have HtauAB_tr : @complex.Re R (\Tr tauAB) <= 1 :=
    eps_ball_trlf HtauAB_ball.
  have disABX : [disjoint S_AB & X] by rewrite disjoint_sym.
  set eqXS := finset.setUC X S_AB : X :|: S_AB = S_AB :|: X.
  pose rhoABX : 'F[H]_(S_AB :|: X) :=
    castlf (eqXS, eqXS) rhoXAB.
  have PrhoABX : rhoABX \is psdlf by rewrite /rhoABX castlf_psdlfE.
  have HrhoABX_tr : @complex.Re R (\Tr rhoABX) <= 1
    by rewrite /rhoABX castlf_trlfE.
  have HrhoABX_marg :
      ptrace_cast disABX rhoABX = ptrace_castl disXAB rhoXAB.
  {
    rewrite /rhoABX /ptrace_cast /ptrace_castl /ptrace_cast_gen.
    have eq_res :
        (X :|: S_AB) :\: X = (S_AB :|: X) :\: X
      by rewrite eqXS.
    rewrite (@ptracelf_castlf_eq R L H (X :|: S_AB) (S_AB :|: X)
      X eqXS eq_res rhoXAB).
    rewrite castlf_comp.
    by congr (castlf (_, _) _); exact: eq_irrelevance.
  }
  have [tauABX [PtauABX [HtauABX_tr [HtauABX_marg Hpd_ext]]]] :=
    @pd_ext_subnorm R L H S_AB X disABX
      (ptrace_castl disXAB rhoXAB) tauAB rhoABX
      PrhoABX HrhoABX_tr HrhoABX_marg PtauAB HtauAB_tr.
  pose tauXAB0 : 'F[H]_(X :|: S_AB) :=
    castlf (esym eqXS, esym eqXS) tauABX.
  have PtauXAB0 : tauXAB0 \is psdlf by rewrite /tauXAB0 castlf_psdlfE.
  have HtauXAB0_tr : @complex.Re R (\Tr tauXAB0) <= 1
    by rewrite /tauXAB0 castlf_trlfE.
  (* `tauXAB` is the X-dephased extension of `tauABX`.  The dephasing
     channel uses the ambient X register supplied by this theorem. *)
  pose Kx (x : 'Idx[H]_X) : 'F[H]_(X :|: S_AB) :=
    [> deltav x ; deltav x <] \O (\1 : 'F_S_AB).
  pose DX : 'SO('H[H]_(X :|: S_AB)) := krausso Kx.
  have HK_adj : forall x, (Kx x)^A = Kx x.
  {
    move=> x.
    have Htensor : Kx x =
        ([> deltav x ; deltav x <] \⊗ (\1 : 'F_S_AB)
          : 'F[H]_(X :|: S_AB)).
    {
      by apply: to_Fnd_inj; rewrite (sdotFT _ _ disXAB) to_Fnd_tenE.
    }
    by rewrite Htensor tenf_adj adj_outp adjf1 -Htensor.
  }
  have HK_sum : \sum_(x : 'Idx[H]_X) Kx x = (\1 : 'F[H]_(X :|: S_AB)).
  {
    transitivity (\sum_(x : 'Idx[H]_X)
      ([> deltav x ; deltav x <] \⊗ (\1 : 'F_S_AB)
        : 'F[H]_(X :|: S_AB))).
    - apply: eq_bigr => x _.
      by apply: to_Fnd_inj; rewrite (sdotFT _ _ disXAB) to_Fnd_tenE.
    by rewrite -tenf_suml sumonb_out tenf11.
  }
  have HDX_cptp : DX \is cptp.
  {
    rewrite /DX.
    apply/krausso_qcP.
    rewrite /trace_presv.
    apply/eqP.
    under eq_bigr => x _ do rewrite HK_adj.
    under eq_bigr => x _.
      have Htensor : Kx x =
          ([> deltav x ; deltav x <] \⊗ (\1 : 'F_S_AB)
            : 'F[H]_(X :|: S_AB)).
      {
        by apply: to_Fnd_inj; rewrite (sdotFT _ _ disXAB) to_Fnd_tenE.
      }
      rewrite !Htensor -tenf_comp; last exact: disXAB.
      rewrite comp_lfun1l outp_comp dv_dot eqxx scale1r -Htensor.
    over.
    exact: HK_sum.
  }
  have Hrho_fix : DX rhoXAB = rhoXAB.
  {
    rewrite /DX kraussoE.
    under eq_bigr => x _ do rewrite HK_adj.
    apply: esym.
    rewrite -{1}[rhoXAB]comp_lfun1l -{1}HK_sum.
    rewrite linear_sumlz /=.
    apply: eq_bigr => y _.
    rewrite -{1}[_ \o rhoXAB]comp_lfun1r -{1}HK_sum.
    rewrite linear_sumr /=.
    rewrite (bigID (fun z : 'Idx[H]_X => z == y)) /= big_pred1_eq.
    rewrite [X in _ + X]big1; first by rewrite addr0.
    move=> z Hzy.
    by rewrite (Hclass y z Hzy).
  }
  pose tauXAB : 'F[H]_(X :|: S_AB) := DX tauXAB0.
  have PtauXAB : tauXAB \is psdlf.
  {
    have Hcp : DX \is cpmap := cptp_cpmap HDX_cptp.
    rewrite /tauXAB (CPMap_BuildE Hcp).
    exact: cp_psdP PtauXAB0.
  }
  have HtauXAB_tr : @complex.Re R (\Tr tauXAB) <= 1.
  {
    have /cptpP [_ /tpmapP Htp] := HDX_cptp.
    by rewrite /tauXAB Htp.
  }
    have HtauXAB_ball : eps_ball eps rhoXAB tauXAB.
    {
      have HpdAB := eps_ball_pur_dist HtauAB_ball.
      have Hpd_cast :
          pur_dist tauXAB0 rhoXAB =
        pur_dist tauAB (ptrace_castl disXAB rhoXAB).
    {
      have Hleft_sym :
          pur_dist tauXAB0 rhoXAB = pur_dist rhoXAB tauXAB0.
      {
        have Ptau_mx : h2mx tauXAB0 \is psdmx
          by move: PtauXAB0; rewrite qualifE.
        have Prho_mx : h2mx rhoXAB \is psdmx
          by move: Prho; rewrite qualifE.
        rewrite /pur_dist /gfid.
        exact: (f_equal (fun x => Num.sqrt (1 - x^2))
          (gfid_sym_mx Ptau_mx Prho_mx)).
      }
      have HtauABX_cast :
          tauABX = castlf (eqXS, eqXS) tauXAB0.
      {
        by rewrite /tauXAB0 castlfKV.
      }
      have Hfull_cast :
          pur_dist rhoABX tauABX = pur_dist rhoXAB tauXAB0.
      {
        rewrite /rhoABX HtauABX_cast /pur_dist /gfid !h2mx_castlf.
        set tauM := castmx
          (f_equal (fun T => dim 'H[H]_T) (esym eqXS),
           f_equal (fun T => dim 'H[H]_T) (esym eqXS))
          (h2mx tauABX).
        have Hg :
            gfidelity
              (castmx
                (f_equal (fun T => dim 'H[H]_T) eqXS,
                 f_equal (fun T => dim 'H[H]_T) eqXS) (h2mx rhoXAB))
              (castmx
                (f_equal (fun T => dim 'H[H]_T) eqXS,
                 f_equal (fun T => dim 'H[H]_T) eqXS) tauM) =
            gfidelity (h2mx rhoXAB) tauM.
        { exact: gfid_cast_mx. }
        exact: (f_equal (fun x => Num.sqrt (1 - x ^ 2)) Hg).
      }
      have Pmarg : ptrace_castl disXAB rhoXAB \is psdlf :=
        ptrace_castl_psdlf disXAB Prho.
      have Hright_sym :
          pur_dist (ptrace_castl disXAB rhoXAB) tauAB =
          pur_dist tauAB (ptrace_castl disXAB rhoXAB).
      {
        have Pmarg_mx : h2mx (ptrace_castl disXAB rhoXAB) \is psdmx
          by move: Pmarg; rewrite qualifE.
        have Ptau_mx : h2mx tauAB \is psdmx
          by move: PtauAB; rewrite qualifE.
        rewrite /pur_dist /gfid.
        exact: (f_equal (fun x => Num.sqrt (1 - x^2))
          (gfid_sym_mx Pmarg_mx Ptau_mx)).
      }
      transitivity (pur_dist rhoXAB tauXAB0).
      - exact: Hleft_sym.
      transitivity (pur_dist rhoABX tauABX).
      - exact: esym Hfull_cast.
      transitivity (pur_dist (ptrace_castl disXAB rhoXAB) tauAB).
      - exact: Hpd_ext.
      exact: Hright_sym.
    }
      have Hpd_mono :
          pur_dist tauXAB rhoXAB <= pur_dist tauXAB0 rhoXAB.
      {
        have Hmono := pd_mono_cptp HDX_cptp
          PtauXAB0 Prho HtauXAB0_tr Hrho_tr.
        by rewrite /tauXAB Hrho_fix in Hmono.
      }
      rewrite Hpd_cast in Hpd_mono.
      have HtauXAB_pd : pur_dist tauXAB rhoXAB <= eps :=
        le_trans Hpd_mono HpdAB.
      have HtauXAB_pos : 0 < @complex.Re R (\Tr tauXAB).
      {
        have Holdball :
            ((tauXAB \is psdlf) &&
              (@complex.Re R (\Tr tauXAB) <= 1)) &&
            (pur_dist tauXAB rhoXAB <= eps)
          by rewrite PtauXAB HtauXAB_tr HtauXAB_pd.
        exact: (eps_ball_trace_pos_from_small Prho Hrho_tr Heps Holdball).
      }
      rewrite /eps_ball.
      apply/andP; split.
      - apply/andP; split.
        + by apply/andP; split.
        + exact: HtauXAB_tr.
      - exact: HtauXAB_pd.
    }
  have Hhmin_le : (hminE B tauAB <= hminE B tauXAB)%E.
  {
    have HtauXAB_tr_pos : 0 < @complex.Re R (\Tr tauXAB) :=
      @eps_ball_trace_pos R L H (X :|: S_AB) eps rhoXAB tauXAB
        Prho Hrho_tr Heps HtauXAB_ball.
    have HphiX_pos : 0 < phi_min B tauXAB :=
      @phi_min_pos_trace R L H (X :|: S_AB) B tauXAB
        PtauXAB HtauXAB_tr HtauXAB_tr_pos.
    have Hblock_order :
        tauXAB <= ((\1 : 'F[H]_X) \O tauAB : 'F[H]_(X :|: S_AB)).
    {
      pose beta (x : 'Idx[H]_X) : 'F[H]_S_AB :=
        ptrace_castl disXAB (Kx x \o tauXAB0 \o Kx x).
      have HKbox : forall x : 'Idx[H]_X,
          Kx x \o tauXAB0 \o Kx x =
          ([> deltav x ; deltav x <] \O beta x
            : 'F[H]_(X :|: S_AB)).
      {
        move=> x.
        (* Diagonal block extraction: K_x tau K_x is |x><x| tensor its
           X-partial trace. *)
        set K := Kx x.
        have HK_ten : K =
            [> deltav x ; deltav x <] \⊗ (\1 : 'F[H]_S_AB).
        {
          by rewrite /K /Kx; apply: to_Fnd_inj;
            rewrite (sdotFT _ _ disXAB) to_Fnd_tenE.
        }
        have HRHS_ten :
            ([> deltav x ; deltav x <] \O beta x
              : 'F[H]_(X :|: S_AB)) =
            [> deltav x ; deltav x <] \⊗ beta x.
        {
          by apply: to_Fnd_inj;
            rewrite (sdotFT _ _ disXAB) to_Fnd_tenE.
        }
        have H1O : forall Y : 'F[H]_S_AB,
            ((\1 : 'F[H]_X) \O Y : 'F[H]_(X :|: S_AB)) =
            (\1 : 'F[H]_X) \⊗ Y.
        {
          by move=> Y; apply: to_Fnd_inj;
            rewrite (sdotFT _ _ disXAB) to_Fnd_tenE.
        }
        rewrite HRHS_ten.
        have Hmx_beta : forall e_u e_v : 'Idx[H]_S_AB,
            [< deltav e_v ; beta x (deltav e_u) >] =
            [< deltav (idxU x e_v) ;
               tauXAB0 (deltav (idxU x e_u)) >].
        {
          move=> e_u e_v.
          rewrite -!outp_trlf -!outp_compr.
          rewrite /beta.
          rewrite -(trlf_lift_partial disXAB _
            [> deltav e_u ; deltav e_v <]).
          rewrite -/K HK_ten H1O.
          have HKmid :
              ([> deltav x ; deltav x <] \⊗ (\1 : 'F[H]_S_AB)
                : 'F[H]_(X :|: S_AB)) \o
              ((\1 : 'F[H]_X) \⊗
                [> deltav e_u ; deltav e_v <]) \o
              ([> deltav x ; deltav x <] \⊗ (\1 : 'F[H]_S_AB)
                : 'F[H]_(X :|: S_AB)) =
              ([> deltav x ; deltav x <] \⊗
                [> deltav e_u ; deltav e_v <]
                : 'F[H]_(X :|: S_AB)).
          {
            rewrite -tenf_comp; last exact: disXAB.
            rewrite !comp_lfun1l !comp_lfun1r.
            rewrite -tenf_comp; last exact: disXAB.
            rewrite !comp_lfun1r.
            by rewrite outp_comp dv_dot eqxx scale1r.
          }
          rewrite -!comp_lfunA lftraceC -comp_lfunA.
          rewrite HKmid.
          congr (\Tr (_ \o _)).
          rewrite tenf_outp.
          by rewrite !(dv_tensor _ _ disXAB).
        }
        have HK_adj0 : K^A = K by rewrite HK_ten tenf_adj adj_outp adjf1 -HK_ten.
        have HKdv : forall w : 'Idx[H]_(X :|: S_AB),
            K (deltav w) =
            (x == idxSl w)%:R *: deltav (idxU x (idxSr w)).
        {
          move=> w.
          rewrite HK_ten -tenf_dv.
          rewrite outpE lfunE /= tenvZl dv_dot.
          by rewrite (dv_tensor _ _ disXAB).
        }
        apply/lfunPD => u.
        apply/intro_cdvl => v.
        rewrite !comp_lfunE.
        rewrite {1}HKdv.
        rewrite !linearZ /=.
        rewrite cdvE.
        rewrite -adj_dotEl HK_adj0.
        rewrite HKdv.
        rewrite dotpZl conjC_nat.
        rewrite -tenf_dv outpE tenvZl dv_dot.
        rewrite linearZ /=.
        rewrite cdvE {1}(dv_split v) tenv_dot; last exact: disXAB.
        rewrite dv_dot.
        rewrite [in X in _ = _ * (X * _)]eq_sym.
        congr (_ * (_ * _)).
        by rewrite Hmx_beta.
      }
      have Hbeta_psd : forall x, beta x \is psdlf.
      {
        move=> x.
        rewrite /beta.
        apply: ptrace_castl_psdlf.
        have Hform : (formso (Kx x)) tauXAB0 \is psdlf
          by exact: cp_psdP PtauXAB0.
        by move: Hform; rewrite formsoE HK_adj.
      }
      have HtauXAB_marg : ptrace_castl disXAB tauXAB = tauAB.
      {
        have HtauXAB0_marg : ptrace_castl disXAB tauXAB0 = tauAB.
        {
          rewrite /tauXAB0 /ptrace_cast /ptrace_castl /ptrace_cast_gen.
          have eq_res :
              (S_AB :|: X) :\: X = (X :|: S_AB) :\: X
            by rewrite -eqXS.
          rewrite (@ptracelf_castlf_eq R L H (S_AB :|: X) (X :|: S_AB)
            X (esym eqXS) eq_res tauABX).
          rewrite castlf_comp.
          rewrite -HtauABX_marg.
          by congr (castlf (_, _) _); exact: eq_irrelevance.
        }
        have Hdephase_marg :
            ptrace_castl disXAB tauXAB = ptrace_castl disXAB tauXAB0.
        {
          (* Partial trace over X ignores X-off-diagonal blocks. *)
          apply/eqP/trlf_intror => g.
          rewrite -!(trlf_lift_partial disXAB).
          pose Ig : 'F[H]_(X :|: S_AB) :=
            ((\1 : 'F[H]_X) \O g).
          have Hlift_fix :
              \sum_(x : 'Idx[H]_X) (Kx x \o Ig \o Kx x) = Ig.
          {
            transitivity (\sum_(x : 'Idx[H]_X)
              ([> deltav x ; deltav x <] \O g
                : 'F[H]_(X :|: S_AB))).
            - apply: eq_bigr => x _.
              have HKten : Kx x =
                  ([> deltav x ; deltav x <] \⊗ (\1 : 'F[H]_S_AB)
                    : 'F[H]_(X :|: S_AB)).
              {
                by apply: to_Fnd_inj;
                  rewrite (sdotFT _ _ disXAB) to_Fnd_tenE.
              }
              have HIgten : Ig =
                  ((\1 : 'F[H]_X) \⊗ g : 'F[H]_(X :|: S_AB)).
              {
                by rewrite /Ig; apply: to_Fnd_inj;
                  rewrite (sdotFT _ _ disXAB) to_Fnd_tenE.
              }
              have HRten :
                  ([> deltav x ; deltav x <] \O g
                    : 'F[H]_(X :|: S_AB)) =
                  [> deltav x ; deltav x <] \⊗ g.
              {
                by apply: to_Fnd_inj;
                  rewrite (sdotFT _ _ disXAB) to_Fnd_tenE.
              }
              rewrite HKten HIgten HRten.
              rewrite -tenf_comp; last exact: disXAB.
              rewrite comp_lfun1l comp_lfun1r.
              rewrite -tenf_comp; last exact: disXAB.
              by rewrite comp_lfun1r outp_comp dv_dot eqxx scale1r.
            transitivity (\sum_(x : 'Idx[H]_X)
              ([> deltav x ; deltav x <] \⊗ g
                : 'F[H]_(X :|: S_AB))).
            + apply: eq_bigr => x _.
              by apply: to_Fnd_inj;
                rewrite (sdotFT _ _ disXAB) to_Fnd_tenE.
            rewrite -tenf_suml sumonb_out.
            by rewrite /Ig; apply: to_Fnd_inj;
              rewrite (sdotFT _ _ disXAB) to_Fnd_tenE.
          }
          rewrite /tauXAB /DX kraussoE.
          under eq_bigr => x _ do rewrite HK_adj.
          rewrite linear_sumlz /= linear_sum /=.
          transitivity (\sum_(x : 'Idx[H]_X)
            \Tr (tauXAB0 \o (Kx x \o Ig \o Kx x))).
          - apply: eq_bigr => x _.
            rewrite /Ig !comp_lfunA.
            rewrite lftraceC.
            by rewrite -!comp_lfunA.
          rewrite -linear_sum /= -linear_sumr /=.
          by rewrite Hlift_fix.
        }
        by rewrite Hdephase_marg HtauXAB0_marg.
      }
      have Hbeta_sum : \sum_(x : 'Idx[H]_X) beta x = tauAB.
      {
        rewrite -HtauXAB_marg /tauXAB /DX kraussoE.
        rewrite /beta /ptrace_castl /ptrace_cast_gen.
        rewrite [\Tr_(X) _]raddf_sum /=.
        rewrite raddf_sum.
        apply: eq_bigr => x _.
        by rewrite HK_adj.
      }
      have Hbeta_le : forall x, beta x <= tauAB.
      {
        move=> x.
        rewrite lefE.
        have Hsplit :
            \sum_(y : 'Idx[H]_X) beta y =
            beta x + \sum_(y : 'Idx[H]_X | y != x) beta y.
        {
          by rewrite (bigD1 x) //=.
        }
        have -> : tauAB - beta x =
            \sum_(y : 'Idx[H]_X | y != x) beta y.
        { by rewrite -Hbeta_sum Hsplit [X0 in X0 - _]addrC addrK. }
        apply: psdlf_sum => y _.
        exact: Hbeta_psd.
      }
      have Htau_decomp :
          tauXAB =
          \sum_(x : 'Idx[H]_X)
            ([> deltav x ; deltav x <] \O beta x
              : 'F[H]_(X :|: S_AB)).
      {
        rewrite /tauXAB /DX kraussoE.
        apply: eq_bigr => x _.
        by rewrite HK_adj HKbox.
      }
      have Hlift_sum :
          \sum_(x : 'Idx[H]_X)
            ([> deltav x ; deltav x <] \O tauAB
              : 'F[H]_(X :|: S_AB)) =
          ((\1 : 'F[H]_X) \O tauAB : 'F[H]_(X :|: S_AB)).
      {
        transitivity (\sum_(x : 'Idx[H]_X)
          ([> deltav x ; deltav x <] \⊗ tauAB
            : 'F[H]_(X :|: S_AB))).
        - apply: eq_bigr => x _.
          by apply: to_Fnd_inj; rewrite (sdotFT _ _ disXAB) to_Fnd_tenE.
        rewrite -tenf_suml sumonb_out.
        by apply: to_Fnd_inj; rewrite (sdotFT _ _ disXAB) to_Fnd_tenE.
      }
      rewrite Htau_decomp -Hlift_sum lefE -sumrB /=.
      apply: psdlf_sum => x _.
      rewrite -lefE.
      have Hproj_ge0 : (0 : 'F[H]_X) <= [> deltav x ; deltav x <]
        by move: (proj1lf_psd (outp_proj1 (deltav x))); rewrite psdlfE.
      exact: (@lef_sdotfr R L H X S_AB disXAB
        [> deltav x ; deltav x <] (beta x) tauAB Hproj_ge0 (Hbeta_le x)).
    }
    have Hphi_le : phi_min B tauXAB <= phi_min B tauAB.
    {
      rewrite /phi_min.
      apply: lb_le_inf.
      - by have [Hne _] :=
          @phi_min_feasible_has_inf R L H S_AB B tauAB PtauAB.
      - move=> v [sigma [Psigma [Hsigma ->]]].
        apply: ge_inf.
        + by have [_ Hlb] :=
            @phi_min_feasible_has_inf R L H (X :|: S_AB) B tauXAB PtauXAB.
        have eq_cond : (X :|: S_AB) :&: B = S_AB :&: B.
        {
          apply/setP=> z.
          rewrite /S_AB !inE.
          have XnotB : z \in X -> (z \in B) = false.
          {
            move=> HzX.
            apply/negP=> HzB.
            have HdXAB := disXAB.
            move/disjointP: HdXAB => /(_ _ HzX).
            by rewrite !inE HzB orbT.
          }
          case HXz : (z \in X); case HAz : (z \in A);
            case HBz : (z \in B); rewrite ?HXz ?HAz ?HBz //=.
        }
        pose sigmaX : 'F[H]_((X :|: S_AB) :&: B) :=
          castlf (esym eq_cond, esym eq_cond) sigma.
        exists sigmaX.
        split.
        + by rewrite /sigmaX castlf_psdlfE.
        split; last by rewrite /sigmaX castlf_trlfE.
        set targetAB := (X0 in (X0 - tauAB) \is psdlf) in Hsigma.
        set targetX := (X0 in (X0 - tauXAB) \is psdlf).
        have HtauAB_le : tauAB <= targetAB
          by move: Hsigma; rewrite lefE.
        have Htarget_lift :
            targetX =
            ((\1 : 'F[H]_X) \O targetAB : 'F[H]_(X :|: S_AB)).
        {
          (* Easy cast bookkeeping: the XAB witness is the X-lift of the
             AB witness, with the same sigma_B. *)
          rewrite /targetX /targetAB /sigmaX.
          apply/to_Fnd_inj.
          rewrite !Fnd_cast.
          have disL :
              [disjoint ((X :|: S_AB) :\: B) & ((X :|: S_AB) :&: B)].
          { setdec. }
          rewrite (sdotFT _ _ disL).
          rewrite Fnd_cast.
          rewrite (sdotFT _ _ disXAB).
          rewrite Fnd_cast.
          have disR : [disjoint (S_AB :\: B) & (S_AB :&: B)].
          { setdec. }
          rewrite (sdotFT _ _ disR).
          rewrite tenFA tenF11.
          have Hdiff_eq :
              X :|: (S_AB :\: B) = (X :|: S_AB) :\: B.
          {
            apply/setP=> z.
            rewrite /S_AB !inE.
            have XnotB : z \in X -> (z \in B) = false.
            {
              move=> HzX.
              apply/negP=> HzB.
              have HdXAB := disXAB.
              move/disjointP: HdXAB => /(_ _ HzX).
              by rewrite !inE HzB orbT.
            }
            case HXz : (z \in X); case HAz : (z \in A);
              case HBz : (z \in B); rewrite ?HXz ?HAz ?HBz //=;
              try by move: (XnotB HXz); rewrite HBz.
          }
          f_equal.
          apply: Fnd_eq1.
          exact: esym Hdiff_eq.
        }
        have HI_psd : (0 : 'F[H]_X) <= (\1 : 'F[H]_X)
          by exact: lef01.
        have Hlift_le :
            ((\1 : 'F[H]_X) \O tauAB : 'F[H]_(X :|: S_AB)) <= targetX.
        {
          rewrite Htarget_lift.
          exact: lef_sdotfr HI_psd HtauAB_le.
        }
        have HtauX_le : tauXAB <= targetX :=
          le_trans Hblock_order Hlift_le.
        by move: HtauX_le; rewrite lefE.
    }
    have Helog_le :
        (elog2 (phi_min B tauXAB) <= elog2 (phi_min B tauAB))%E :=
      elog2_le _ _ HphiX_pos Hphi_le.
    by rewrite /hminE leeNr oppeK.
  }
  by exists tauXAB.
Qed.

End ClassHminLift.

(* Generic compound-register variant of smooth_hmin_ball_ge.                *)
(* smooth_hmin_ball_ge_gen *)
(* infra: no tex label — smooth-definition order interface (compound)      *)
Section SmoothPropGen.
Variable (L : finType) (H : L -> chsType).

(* path: entropy:smooth_hmin_ball_ge_gen -> entropy:smooth_iso_hmax -> *)
(*   entropy:entropy_data_proc -> *)
(*   bb84:bb84_secret *)
Lemma smooth_hmin_ball_ge_gen (S T : {set L}) (eps : R) (rho tau : 'F[H]_S) :
  rho \is denlf ->
  0 <= eps < Num.sqrt (@complex.Re R (\Tr rho)) ->
  eps_ball eps rho tau ->
  (hminE T tau <= smooth_hminE T eps rho)%E.
Proof.
  move=> _ _ Htau.
  rewrite /smooth_hminE.
  apply: ereal_sup_ubound.
  by exists tau.
Qed.

(* ε=0 smoothing ball is the singleton {ρ}.  pur_dist separates points  *)
(* (pur_dist_eq0), so pur_dist τ ρ ≤ 0 forces τ = ρ.                          *)
Lemma eps_ball_0_eq (S : {set L}) (rho tau : 'F[H]_S) :
  rho \is psdlf -> @complex.Re R (\Tr rho) <= 1 ->
  eps_ball 0 rho tau -> tau = rho.
Proof.
  move=> Prho Htr Hball.
  apply: pur_dist_eq0.
  - exact: (eps_ball_psdlf Hball).
  - exact: Prho.
  - exact: (eps_ball_trlf Hball).
  - exact: Htr.
  - have Hpd_ge0 : 0 <= pur_dist tau rho by rewrite /pur_dist; exact: sqrtr_ge0.
    by apply/eqP; rewrite eq_le (eps_ball_pur_dist Hball) Hpd_ge0.
Qed.

(* Smooth entropy at ε=0 collapses to the non-smooth entropy, since the      *)
(* smoothing ball is the singleton {ρ}.  Routes the EUR matrix duality        *)
(* (minmax_dual) through smooth_dual at the pure ε=0 point.                   *)
Lemma smooth_hminE_0 (S T : {set L}) (rho : 'F[H]_S) :
  rho \is psdlf -> @complex.Re R (\Tr rho) <= 1 ->
  0 < @complex.Re R (\Tr rho) ->
  smooth_hminE T 0 rho = hminE T rho.
Proof.
  move=> Prho Htr Htr_pos.
  apply/eqP; rewrite eq_le; apply/andP; split.
  - rewrite /smooth_hminE.
    apply: ge_ereal_sup => v [tau [Hball ->]].
    by rewrite (eps_ball_0_eq Prho Htr Hball).
  - apply: ereal_sup_ubound; exists rho; split; last by [].
    exact: (eps_ball_refl Prho Htr_pos Htr (lexx 0)).
Qed.

Lemma smooth_hmaxE_0 (S T : {set L}) (rho : 'F[H]_S) :
  rho \is psdlf -> @complex.Re R (\Tr rho) <= 1 ->
  0 < @complex.Re R (\Tr rho) ->
  smooth_hmaxE T 0 rho = hmaxE T rho.
Proof.
  move=> Prho Htr Htr_pos.
  rewrite /smooth_hmaxE.
  set Sset := (X in ereal_sup X).
  have Hsup : ereal_sup Sset = (- hmaxE T rho)%E.
  { apply/eqP; rewrite eq_le; apply/andP; split.
    - apply: ge_ereal_sup => v [tau [Hball ->]].
      by rewrite (eps_ball_0_eq Prho Htr Hball).
    - apply: ereal_sup_ubound; exists rho; split; last by [].
      exact: (eps_ball_refl Prho Htr_pos Htr (lexx 0)). }
  by rewrite Hsup oppeK.
Qed.

End SmoothPropGen.

(* Finite embedding bridge for the smooth min-entropy.                    *)
(* math: for a subnormalized state and ε below sqrt(trace), every point   *)
(* in the ε-ball has positive trace, so hminE is finite throughout the     *)
(* ball and the extended-real supremum is the finite embedding of the real *)
(* smooth min-entropy.                                                     *)
(* path: entropy:smooth_hminE_EFin -> bb84:bb84_secret *)
Section SmoothHMinEFin.
Variable (L : finType) (H : L -> chsType) (A B : {set L}).
Hypothesis disAB : [disjoint A & B].
Notation S_AB := (A :|: B).

Lemma smooth_hminE_EFin (eps : R) (rhoAB : 'F[H]_S_AB) :
  rhoAB \is psdlf ->
  @complex.Re R (\Tr rhoAB) <= 1 ->
  0 <= eps < Num.sqrt (@complex.Re R (\Tr rhoAB)) ->
  smooth_hminE B eps rhoAB = (smooth_hmin B eps rhoAB)%:E.
Proof.
  move=> Prho Hrho_tr Heps.
  have Hrho_den : rhoAB \is denlf.
  {
    apply/denlfP; split=> //.
    have Hreal : \Tr rhoAB \is Num.real := ger0_real (psdlf_trlf Prho).
    by rewrite -(RRe_real Hreal) lecR.
  }
  have [tauAB [Htau_ball [Htau_optE _]]] :=
    @smoothing_support_hmin R L H A B disAB eps rhoAB Hrho_den Heps.
  have Htau_psd : tauAB \is psdlf := eps_ball_psdlf Htau_ball.
  have Htau_tr : @complex.Re R (\Tr tauAB) <= 1 := eps_ball_trlf Htau_ball.
  have Htau_pos : 0 < @complex.Re R (\Tr tauAB) :=
    eps_ball_trace_pos Prho Hrho_tr Heps Htau_ball.
  have Htau_phi_pos : 0 < phi_min B tauAB :=
    @phi_min_pos_trace R L H S_AB B tauAB Htau_psd Htau_tr Htau_pos.
  have Htau_fin : hminE B tauAB = (hmin B tauAB)%:E :=
    @hminE_EFin R L H S_AB B tauAB Htau_phi_pos.
  have Htau_ub :
      forall tau : 'F[H]_S_AB,
        eps_ball eps rhoAB tau -> hmin B tau <= hmin B tauAB.
  {
    move=> tau Hball.
    have Htau0_psd : tau \is psdlf := eps_ball_psdlf Hball.
    have Htau0_tr : @complex.Re R (\Tr tau) <= 1 := eps_ball_trlf Hball.
    have Htau0_pos : 0 < @complex.Re R (\Tr tau) :=
      eps_ball_trace_pos Prho Hrho_tr Heps Hball.
    have Htau0_phi_pos : 0 < phi_min B tau :=
      @phi_min_pos_trace R L H S_AB B tau Htau0_psd Htau0_tr Htau0_pos.
    have Htau0_fin : hminE B tau = (hmin B tau)%:E :=
      @hminE_EFin R L H S_AB B tau Htau0_phi_pos.
    have HleE : (hminE B tau <= hminE B tauAB)%E.
    {
      rewrite -Htau_optE.
      apply: ereal_sup_ubound.
      exists tau.
      split; first exact: Hball.
      reflexivity.
    }
    move: HleE.
    by rewrite Htau0_fin Htau_fin lee_fin.
  }
  have Htau_opt : smooth_hmin B eps rhoAB = hmin B tauAB.
  {
    apply/eqP; rewrite eq_le.
    apply/andP; split.
    - apply: ge_sup.
      + exists (hmin B tauAB).
        by exists tauAB.
      + apply/ubP=> v [tau [Hball ->]].
        exact: Htau_ub Hball.
    - have Hsmooth_ub :
          has_ubound [set v : R | exists tauS : 'F[H]_S_AB,
            eps_ball eps rhoAB tauS /\ v = hmin B tauS].
      {
        exists (hmin B tauAB).
        apply/ubP=> v [tau [Hball ->]].
        exact: Htau_ub Hball.
      }
      have Htau_mem :
          exists tauS : 'F[H]_S_AB,
            eps_ball eps rhoAB tauS /\ hmin B tauAB = hmin B tauS.
      {
        by exists tauAB.
      }
      exact: (ub_le_sup Hsmooth_ub Htau_mem).
  }
  by rewrite Htau_optE Htau_fin Htau_opt.
Qed.

End SmoothHMinEFin.

(* Set-level representation of Tomamichel's smooth min-entropy isometry law. *)
Section SmoothIsoHMinSet.
Variable (L : finType) (H : L -> chsType) (A B A' B' : {set L}).
Hypothesis disAB : [disjoint A & B].
Hypothesis disA'B' : [disjoint A' & B'].
Hypothesis disA'B : [disjoint A' & B].
Hypothesis disAB' : [disjoint A & B'].

Notation S_AB := (A :|: B).
Notation S_A'B' := (A' :|: B').

(* smooth_iso_hmin *)
(* Tomamichel thesis (arXiv:1203.2142), Proposition 5.3 — tex pr:smooth-iso, min-half. *)
(* path: entropy:smooth_iso_hmin -> entropy:smooth_iso_hmax -> *)
(*   entropy:entropy_data_proc -> *)
(*   bb84:bb84_secret *)
Lemma smooth_iso_hmin (eps : R) (rhoAB : 'F[H]_S_AB)
    (U : 'FI[H]_(A, A')) (V : 'FI[H]_(B, B')) :
  rhoAB \is denlf ->
  0 <= eps < Num.sqrt (@complex.Re R (\Tr rhoAB)) ->
  smooth_hminE B' eps ((U \⊗ V) \o rhoAB \o (U \⊗ V)^A) =
  smooth_hminE B eps rhoAB.
Proof.
  move=> Hrho_den Heps.
  have Prho : rhoAB \is psdlf := denlf_psd Hrho_den.
  have Hrho_tr : @complex.Re R (\Tr rhoAB) <= 1.
  { have Hreal : \Tr rhoAB \is Num.real := ger0_real (psdlf_trlf Prho).
    by move: (denlf_trlf Hrho_den); rewrite -(RRe_real Hreal) lecR. }
  pose W := U \⊗ V.
  pose rho' := W \o rhoAB \o W^A.
  have W_iso : W \is isolf.
  { apply/isolfP.
    by rewrite tenf_adj -tenf_comp ?disAB // isofE isofE tenf11. }
  pose Wi := IsoLf_Build W_iso.
  have HWi : W = Wi by exact: IsoLf_BuildE W_iso.
  have Wa_b1 : W^A \is bound1lf.
    by rewrite bound1lf_adj; exact: isolf_bound1 W_iso.
  pose Wa := Bound1Lf_Build Wa_b1.
  have HWa : W^A = Wa by exact: Bound1Lf_BuildE Wa_b1.
  have HWi_cptp : formso Wi \is cptp by apply: is_cptp.
  have HWi_cptn : formso Wi \is cptn := cptp_cptn HWi_cptp.
  have HWa_cptn : formso Wa \is cptn
    by rewrite qualifE formso_cp formso_tn.
  have Hrho'E : rho' = formso Wi rhoAB by rewrite /rho' HWi formsoE.
  have Prho' : rho' \is psdlf.
  { rewrite Hrho'E (CPMap_BuildE (cptp_cpmap HWi_cptp)).
    exact: cp_psdP Prho. }
  have Hrho'_tr_eq :
      @complex.Re R (\Tr rho') = @complex.Re R (\Tr rhoAB).
  { rewrite /rho' HWi /formlf lftraceC comp_lfunA isofE comp_lfun1l.
    reflexivity. }
  have Hrho'_tr : @complex.Re R (\Tr rho') <= 1
    by rewrite Hrho'_tr_eq.
  have Hrho'_den : rho' \is denlf.
  { apply/denlfP; split=> //.
    have Hreal : \Tr rho' \is Num.real := ger0_real (psdlf_trlf Prho').
    by rewrite -(RRe_real Hreal) lecR. }
  have Heps' : 0 <= eps < Num.sqrt (@complex.Re R (\Tr rho')).
  { move: Heps; rewrite Hrho'_tr_eq. exact. }
  have Hphi_pos_trace :
      forall (S T : {set L}) (x : 'F[H]_S),
      x \is psdlf -> @complex.Re R (\Tr x) <= 1 ->
      0 < @complex.Re R (\Tr x) -> 0 < phi_min T x.
  {
    move=> S T x Px Hx_tr Hx_tr_pos.
    have eqST : (S :\: T) :|: (S :&: T) = S.
      by rewrite finset.setUC finset.setID.
    have disSplit : [disjoint (S :\: T) & (S :&: T)].
    { apply/disjointP=> z; rewrite !inE.
      by case: (z \in T); rewrite ?andbF ?andbT. }
    pose dT : R := (dim 'H[H]_(S :\: T))%:R.
    have HdT_pos : 0 < dT by rewrite /dT ltr0n dim_proper.
    rewrite /phi_min.
    apply: (@lt_le_trans _ _ ((@complex.Re R (\Tr x)) / dT)).
    - by apply: divr_gt0.
    - apply: lb_le_inf.
      + pose sigma1 : 'F[H]_(S :&: T) := \1.
        exists (@complex.Re R (\Tr sigma1)).
        rewrite /phi_min_feasible.
        exists sigma1; split.
        { by rewrite qualifE h2mx1; apply: psdmx1. }
        split; last by [].
        rewrite sdotf11 castlf1.
        have Hx_den : x \is denlf.
        { apply/denlfP; split=> //.
          have Hreal : \Tr x \is Num.real := ger0_real (psdlf_trlf Px).
          by rewrite -(RRe_real Hreal) lecR. }
        have Hx_le1 : x ⊑ (\1 : 'F[H]_S)
          := denf_le1 (DenLf_Build Hx_den).
        by move: Hx_le1; rewrite lefE.
      + move=> v [sigma [Psigma [Hfeas ->]]].
        have Htr_sigma_real :
            (\Tr sigma : C) = (@complex.Re R (\Tr sigma))%:C
          by rewrite RRe_real // ger0_real // psdlf_trlf.
        have Hx_tr_real : (\Tr x : C) = (@complex.Re R (\Tr x))%:C
          by rewrite RRe_real // ger0_real // psdlf_trlf.
        have Hx_leC :
            \Tr x <= (dim 'H[H]_(S :\: T))%:R * \Tr sigma.
        { have Hgap_nonneg := psdlf_trlf Hfeas.
          move: Hgap_nonneg.
          rewrite raddfB /= castlf_trlfE (trlf_lift_I disSplit).
          by rewrite subr_ge0. }
        move: Hx_leC; rewrite Hx_tr_real Htr_sigma_real.
        rewrite /dT -natrC -rmorphM /= lecR => Hx_leR.
        rewrite ler_pdivrMr //.
        by rewrite mulrC.
  }
  have Hhmin_forward :
      forall tau : 'F[H]_S_AB,
      eps_ball eps rhoAB tau ->
      eps_ball eps rho' (W \o tau \o W^A) ->
      (hminE B tau <= hminE B' (W \o tau \o W^A))%E.
  { move=> tau Htau_ball Htau'_ball.
    have Ptau : tau \is psdlf := eps_ball_psdlf Htau_ball.
    (* The per-witness step is exactly Φ-min isometry
       invariance (tb:Phi v), applied to the smoothing witness tau. *)
    have Hphi_le : phi_min B' (W \o tau \o W^A) <= phi_min B tau.
    { rewrite /W (@phi_min_v_iso_inv R L H A A' B B'
        disAB disA'B' tau U V Ptau).
      exact: lexx. }
    have Hphi_pos : 0 < phi_min B' (W \o tau \o W^A).
    {
      have Ptau' : (W \o tau \o W^A) \is psdlf
        := eps_ball_psdlf Htau'_ball.
      have Htau'_tr : @complex.Re R (\Tr (W \o tau \o W^A)) <= 1
        := eps_ball_trlf Htau'_ball.
      have Htau'_tr_pos : 0 < @complex.Re R (\Tr (W \o tau \o W^A))
        := eps_ball_trace_pos Prho' Hrho'_tr Heps' Htau'_ball.
      exact: (Hphi_pos_trace S_A'B' B' _ Ptau' Htau'_tr Htau'_tr_pos).
    }
    rewrite /hminE leeN2.
    exact: elog2_le _ _ Hphi_pos Hphi_le. }
  have Hhmin_back :
      forall tau' : 'F[H]_S_A'B',
      eps_ball eps rho' tau' ->
      eps_ball eps rhoAB (W^A \o tau' \o W) ->
      (hminE B' tau' <= hminE B (W^A \o tau' \o W))%E.
  { move=> tau' Htau'_ball Htau_ball.
    have Ptau' : tau' \is psdlf := eps_ball_psdlf Htau'_ball.
    have HUa_b1 : U^A \is bound1lf.
      by rewrite bound1lf_adj; exact: isolf_bound1 (is_isolf U).
    pose Ua := Bound1Lf_Build HUa_b1.
    have HUa : U^A = Ua by exact: Bound1Lf_BuildE HUa_b1.
    have HformUa_cp : (formso Ua : 'SO[H]_(A', A)) \is cpmap
      by exact: formso_cp.
    have HformUa_dualtn : (formso Ua : 'SO[H]_(A', A))^*o \is tnmap.
    { rewrite dualso_formso.
      have HUaA : Ua^A = U by rewrite -HUa adjfK.
      rewrite HUaA.
      have HU_cptp : formso U \is cptp by apply: is_cptp.
      exact: cptn_tnmap (cptp_cptn HU_cptp). }
    pose tauUa : 'F[H]_(A :|: B') :=
      (((formso Ua : 'SO[H]_(A', A)) :⊗ (\:1 : 'SO[H]_B')) tau').
    have Hphi_Ua :
        phi_min B' tauUa <= phi_min B' tau'.
    { exact: (@phi_min_data_proc_A R L H A' A B'
        disA'B' disAB' tau' (formso Ua) Ptau' HformUa_cp
        HformUa_dualtn). }
    have HtensoUa_cp :
        (((formso Ua : 'SO[H]_(A', A)) :⊗ (\:1 : 'SO[H]_B')) \is cpmap).
    { exact: (@tenso_cp R L H A' A B' B' disA'B'
        (CPMap_Build HformUa_cp) (\:1 : 'CP[H]_B')). }
    have PtauUa : tauUa \is psdlf.
    { rewrite /tauUa (CPMap_BuildE HtensoUa_cp).
      exact: cp_psdP Ptau'. }
    have HVa_b1 : V^A \is bound1lf.
      by rewrite bound1lf_adj; exact: isolf_bound1 (is_isolf V).
    pose Va := Bound1Lf_Build HVa_b1.
    have HVa : V^A = Va by exact: Bound1Lf_BuildE HVa_b1.
    have HVa_cptn : formso Va \is cptn
      by rewrite qualifE formso_cp formso_tn.
    pose EVa : 'QO[H]_(B', B) := QOperation_Build HVa_cptn.
    have HEVa : (EVa : 'SO[H]_(B', B)) = formso Va
      by [].
    have Hphi_Va :
        phi_min B (((\:1 : 'SO[H]_A) :⊗ EVa) tauUa) <= phi_min B' tauUa.
    { exact: (@phi_min_data_proc_B R L H A B' B
        disAB' disAB tauUa EVa PtauUa). }
    have Htau_map :
        (((\:1 : 'SO[H]_A) :⊗ EVa) tauUa) =
        W^A \o tau' \o W.
    { rewrite /tauUa HEVa.
      have HUmap :
          ((formso Ua : 'SO[H]_(A', A)) :⊗ (\:1 : 'SO[H]_B')) =
          formso (Ua \⊗ (\1 : 'F[H]_B')).
      { by rewrite -formso1 tenso_formso. }
      have HVmap :
          ((\:1 : 'SO[H]_A) :⊗ (formso Va : 'SO[H]_(B', B))) =
          formso ((\1 : 'F[H]_A) \⊗ Va).
      { by rewrite -formso1 tenso_formso. }
      rewrite HUmap HVmap !formsoE.
      have HcompW :
          ((\1 : 'F[H]_A) \⊗ Va) \o (Ua \⊗ (\1 : 'F[H]_B')) = W^A.
      { rewrite -HVa -HUa /W tenf_adj.
        rewrite -tenf_comp ?disAB' //.
        by rewrite comp_lfun1l comp_lfun1r. }
      rewrite [X in X \o _]comp_lfunA.
      rewrite [X in (X \o _) \o _]comp_lfunA.
      rewrite HcompW.
      have HcompWA :
          (Ua \⊗ (\1 : 'F[H]_B'))^A \o
          (((\1 : 'F[H]_A) \⊗ Va)^A) = W.
      { by rewrite -adjf_comp HcompW adjfK. }
      by rewrite -comp_lfunA HcompWA. }
    rewrite Htau_map in Hphi_Va.
    have Hphi_le : phi_min B (W^A \o tau' \o W) <= phi_min B' tau'
      := le_trans Hphi_Va Hphi_Ua.
    have Hphi_pos : 0 < phi_min B (W^A \o tau' \o W).
    {
      have Ptau : (W^A \o tau' \o W) \is psdlf
        := eps_ball_psdlf Htau_ball.
      have Htau_tr : @complex.Re R (\Tr (W^A \o tau' \o W)) <= 1
        := eps_ball_trlf Htau_ball.
      have Htau_tr_pos : 0 < @complex.Re R (\Tr (W^A \o tau' \o W))
        := eps_ball_trace_pos Prho Hrho_tr Heps Htau_ball.
      exact: (Hphi_pos_trace S_AB B _ Ptau Htau_tr Htau_tr_pos).
    }
    rewrite /hminE leeN2.
    exact: elog2_le _ _ Hphi_pos Hphi_le. }
  have Hforward :
      (smooth_hminE B eps rhoAB <= smooth_hminE B' eps rho')%E.
  { rewrite /smooth_hminE.
    apply: ge_ereal_sup => v [tau [Htau_ball ->]].
    pose tau' := W \o tau \o W^A.
    have Ptau : tau \is psdlf := eps_ball_psdlf Htau_ball.
    have Htau_tr : @complex.Re R (\Tr tau) <= 1 := eps_ball_trlf Htau_ball.
    have Htau'E : tau' = formso Wi tau by rewrite /tau' HWi formsoE.
    have Ptau' : tau' \is psdlf.
    { rewrite Htau'E (CPMap_BuildE (cptp_cpmap HWi_cptp)).
      exact: cp_psdP Ptau. }
      have Htau'_tr : @complex.Re R (\Tr tau') <= 1.
      { by rewrite /tau' HWi /formlf lftraceC comp_lfunA isofE comp_lfun1l. }
      have Htau'_pos : 0 < @complex.Re R (\Tr tau').
      { have Htau_pos : 0 < @complex.Re R (\Tr tau) :=
          eps_ball_trlf_gt0 Htau_ball.
        by rewrite /tau' HWi /formlf lftraceC comp_lfunA isofE comp_lfun1l. }
      have Htau'_pd : pur_dist tau' rho' <= eps.
      { have Hpd := eps_ball_pur_dist Htau_ball.
        rewrite Htau'E Hrho'E.
        have [_ Hmono] := pd_mono HWi_cptn Ptau Prho Htau_tr Hrho_tr.
        exact: le_trans Hmono Hpd. }
      have Htau'_ball : eps_ball eps rho' tau'
        by rewrite /eps_ball Ptau' Htau'_pos Htau'_tr Htau'_pd.
    have Hsmooth_tau' :=
      @smooth_hmin_ball_ge_gen L H S_A'B' B'
        eps rho' tau' Hrho'_den Heps' Htau'_ball.
    rewrite /tau' in Hsmooth_tau'.
    exact: (le_trans (Hhmin_forward tau Htau_ball Htau'_ball)
      Hsmooth_tau'). }
  have Hreverse :
      (smooth_hminE B' eps rho' <= smooth_hminE B eps rhoAB)%E.
  { rewrite /smooth_hminE.
    apply: ge_ereal_sup => v [tau' [Htau'_ball ->]].
    pose tau := W^A \o tau' \o W.
    have Ptau' : tau' \is psdlf := eps_ball_psdlf Htau'_ball.
    have Htau'_tr : @complex.Re R (\Tr tau') <= 1 := eps_ball_trlf Htau'_ball.
    have HtauE : tau = formso Wa tau'
      by rewrite /tau HWa formsoE -HWa adjfK.
    have Ptau : tau \is psdlf.
    { rewrite HtauE (CPMap_BuildE (cptn_cpmap HWa_cptn)).
      exact: cp_psdP Ptau'. }
    have Htau_tr : @complex.Re R (\Tr tau) <= 1.
    {
      have HleC : \Tr (formso Wa tau') <= \Tr tau'.
      { rewrite (QOperation_BuildE HWa_cptn).
        exact: qo_trlfE Ptau'. }
      have HleC_tau : \Tr tau <= \Tr tau'.
      { by rewrite HtauE. }
      have Htr_tau'_real : (\Tr tau' : C) = (@complex.Re R (\Tr tau'))%:C
        by rewrite RRe_real // ger0_real // psdlf_trlf.
      have Htr_tau_real :
          (\Tr tau : C) = (@complex.Re R (\Tr tau))%:C
        by rewrite RRe_real // ger0_real // psdlf_trlf.
      have HleR :
          @complex.Re R (\Tr tau) <= @complex.Re R (\Tr tau')
        by move: HleC_tau; rewrite Htr_tau_real Htr_tau'_real !lecR.
      exact: (le_trans HleR Htau'_tr). }
    have Hrho_back : rhoAB = formso Wa rho'.
    { rewrite /rho' HWi HWa formsoE.
      have HWaA : Wa^A = Wi by rewrite -HWa HWi adjfK.
      have HWiA' : W^A = Wi^A by exact: (f_equal (fun X => X^A) HWi).
      have HWiA : (Wa : 'F[H]_(S_A'B', S_AB)) = Wi^A.
      { transitivity (W^A : 'F[H]_(S_A'B', S_AB)).
        - exact: (esym HWa).
        - exact: HWiA'. }
      rewrite HWaA -!comp_lfunA HWiA !comp_lfunA.
      rewrite [Wi^A \o Wi]isofE comp_lfun1l.
      rewrite -comp_lfunA [Wi^A \o Wi]isofE comp_lfun1r.
      reflexivity. }
      have Htau_pd : pur_dist tau rhoAB <= eps.
      { have Hpd := eps_ball_pur_dist Htau'_ball.
        rewrite HtauE Hrho_back.
        have [_ Hmono] := pd_mono HWa_cptn Ptau' Prho' Htau'_tr Hrho'_tr.
        exact: le_trans Hmono Hpd. }
      have Htau_pos : 0 < @complex.Re R (\Tr tau).
      { have Holdball :
            ((tau \is psdlf) && (@complex.Re R (\Tr tau) <= 1)) &&
            (pur_dist tau rhoAB <= eps)
          by rewrite Ptau Htau_tr Htau_pd.
        exact: (eps_ball_trace_pos_from_small Prho Hrho_tr Heps Holdball). }
      have Htau_ball : eps_ball eps rhoAB tau
        by rewrite /eps_ball Ptau Htau_pos Htau_tr Htau_pd.
    have Hsmooth_tau :=
      @smooth_hmin_ball_ge_gen L H S_AB B
        eps rhoAB tau Hrho_den Heps Htau_ball.
    rewrite /tau in Hsmooth_tau.
    exact: (le_trans (Hhmin_back tau' Htau'_ball Htau_ball)
      Hsmooth_tau). }
  apply/eqP; rewrite eq_le.
  by apply/andP; split.
Qed.

End SmoothIsoHMinSet.

Section SmoothIsoHMax.
Variable (L : finType) (H : L -> chsType) (A B A' B' : {set L}).
Hypothesis disAB : [disjoint A & B].
Hypothesis disA'B' : [disjoint A' & B'].

Notation S_AB := (A :|: B).
Notation S_A'B' := (A' :|: B').

(* Upstream-ambient proof artifacts: Ciso is purification/support room for
   the isometry proof; Cp/Cpp pairs are the minmax-dual auxiliaries for the
   source and target sides. *)
Variable Ciso Cp_src Cpp_src Cp_tgt Cpp_tgt : {set L}.
Hypothesis disA_Ciso : [disjoint A & Ciso].
Hypothesis disB_Ciso : [disjoint B & Ciso].
Hypothesis disAp_Ciso : [disjoint A' & Ciso].
Hypothesis disBp_Ciso : [disjoint B' & Ciso].
Hypothesis dimAB_Ciso : (dim 'H[H]_S_AB <= dim 'H[H]_Ciso)%N.
Hypothesis dimA'B'_Ciso : (dim 'H[H]_S_A'B' <= dim 'H[H]_Ciso)%N.
Hypothesis disA_Cp_src : [disjoint A & Cp_src].
Hypothesis disA_Cpp_src : [disjoint A & Cpp_src].
Hypothesis disB_Cp_src : [disjoint B & Cp_src].
Hypothesis disB_Cpp_src : [disjoint B & Cpp_src].
Hypothesis disC_Cp_src : [disjoint Ciso & Cp_src].
Hypothesis disC_Cpp_src : [disjoint Ciso & Cpp_src].
Hypothesis disCp_Cpp_src : [disjoint Cp_src & Cpp_src].
Hypothesis dimA_Cp_src : dim 'H[H]_A = dim 'H[H]_Cp_src.
Hypothesis dimC_Cp_Cpp_src :
  (dim 'H[H]_Ciso * dim 'H[H]_Cp_src <= dim 'H[H]_Cpp_src)%N.
Hypothesis dimB_Cpp_src : (dim 'H[H]_B <= dim 'H[H]_Cpp_src)%N.
Hypothesis disAp_Cp_tgt : [disjoint A' & Cp_tgt].
Hypothesis disAp_Cpp_tgt : [disjoint A' & Cpp_tgt].
Hypothesis disBp_Cp_tgt : [disjoint B' & Cp_tgt].
Hypothesis disBp_Cpp_tgt : [disjoint B' & Cpp_tgt].
Hypothesis disC_Cp_tgt : [disjoint Ciso & Cp_tgt].
Hypothesis disC_Cpp_tgt : [disjoint Ciso & Cpp_tgt].
Hypothesis disCp_Cpp_tgt : [disjoint Cp_tgt & Cpp_tgt].
Hypothesis dimAp_Cp_tgt : dim 'H[H]_A' = dim 'H[H]_Cp_tgt.
Hypothesis dimC_Cp_Cpp_tgt :
  (dim 'H[H]_Ciso * dim 'H[H]_Cp_tgt <= dim 'H[H]_Cpp_tgt)%N.
Hypothesis dimBp_Cpp_tgt : (dim 'H[H]_B' <= dim 'H[H]_Cpp_tgt)%N.

(* Tomamichel thesis (arXiv:1203.2142), Proposition 5.3 (max part) — tex pr:smooth-iso/max. *)
(* consumer: pr_si_max is used downstream by the BB84 secrecy proof. *)
(* Statement: smooth max-entropy is invariant under            *)
(*   isometric embeddings U: A → A', V: B → B'.  No support-fullness          *)
(*   hypotheses appear in tex.                                                *)
(*                                                                            *)
(* Proof route: support-restricted smoothing witnesses, purification in a     *)
(* large fresh system, Qed unsmoothed min/max duality, and image-preimage     *)
(* transport under the range projection of U \otimes V.                      *)
(* path: entropy:smooth_iso_hmax -> entropy:entropy_data_proc -> *)
(*   bb84:bb84_secret *)
Lemma smooth_iso_hmax (eps : R) (rhoAB : 'F[H]_S_AB)
    (U : 'FI[H]_(A, A')) (V : 'FI[H]_(B, B')) :
  rhoAB \is denlf ->
  0 <= eps < Num.sqrt (@complex.Re R (\Tr rhoAB)) ->
  smooth_hmaxE B' eps ((U \⊗ V) \o rhoAB \o (U \⊗ V)^A) =
  smooth_hmaxE B eps rhoAB.
Proof.
  move=> Hrho_den Heps.
  have Prho : rhoAB \is psdlf := denlf_psd Hrho_den.
  have Hrho_tr : @complex.Re R (\Tr rhoAB) <= 1.
  { have Hreal : \Tr rhoAB \is Num.real := ger0_real (psdlf_trlf Prho).
    by move: (denlf_trlf Hrho_den); rewrite -(RRe_real Hreal) lecR. }
  pose W := U \⊗ V.
  pose rho' := W \o rhoAB \o W^A.
  have W_iso : W \is isolf.
  { apply/isolfP.
    by rewrite tenf_adj -tenf_comp ?disAB // isofE isofE tenf11. }
  pose Wi := IsoLf_Build W_iso.
  have HWi : W = Wi by exact: IsoLf_BuildE W_iso.
  have HWi_cptp : formso Wi \is cptp by apply: is_cptp.
  have Hrho'E : rho' = formso Wi rhoAB by rewrite /rho' HWi formsoE.
  have Prho' : rho' \is psdlf.
  { rewrite Hrho'E (CPMap_BuildE (cptp_cpmap HWi_cptp)).
    exact: cp_psdP Prho. }
  have Hrho'_tr_eq :
      @complex.Re R (\Tr rho') = @complex.Re R (\Tr rhoAB).
  { rewrite /rho' HWi /formlf lftraceC comp_lfunA isofE comp_lfun1l.
    reflexivity. }
  have Hrho'_tr : @complex.Re R (\Tr rho') <= 1
    by rewrite Hrho'_tr_eq.
  have Hrho'_den : rho' \is denlf.
  { apply/denlfP; split=> //.
    have Hreal : \Tr rho' \is Num.real := ger0_real (psdlf_trlf Prho').
    by rewrite -(RRe_real Hreal) lecR. }
  have Heps' : 0 <= eps < Num.sqrt (@complex.Re R (\Tr rho')).
  { move: Heps; rewrite Hrho'_tr_eq. exact. }
  have Hsmooth_hmax_ball_leE :
      forall (S T : {set L}) (rho tau : 'F[H]_S),
      eps_ball eps rho tau ->
      (smooth_hmaxE T eps rho <= hmaxE T tau)%E.
  { move=> S T rho tau Htau.
    rewrite /smooth_hmaxE leeNl.
    apply: ereal_sup_ubound.
    by exists tau. }
  have Hball_image :
      forall tau : 'F[H]_S_AB,
      eps_ball eps rhoAB tau ->
      eps_ball eps rho' (W \o tau \o W^A).
  {
    move=> tau Htau_ball.
    pose tau' := W \o tau \o W^A.
    have Ptau : tau \is psdlf := eps_ball_psdlf Htau_ball.
    have Ptau' : tau' \is psdlf.
    { apply/psdlfP=> x.
      rewrite /tau' comp_lfunE comp_lfunE -adj_dotEl.
      by move/psdlfP: Ptau. }
    have Htau'_tr : @complex.Re R (\Tr tau') <= 1.
    { have Htau_tr : @complex.Re R (\Tr tau) <= 1 := eps_ball_trlf Htau_ball.
      rewrite /tau' HWi /formlf lftraceC comp_lfunA isofE comp_lfun1l.
      exact: Htau_tr. }
      have Htau'_pd : pur_dist tau' rho' <= eps.
      { have Htau_tr_le1 : @complex.Re R (\Tr tau) <= 1 := eps_ball_trlf Htau_ball.
        have Htau_pd := eps_ball_pur_dist Htau_ball.
        have Htau'E : tau' = formso Wi tau by rewrite /tau' HWi formsoE.
        have Hrho'E0 : rho' = formso Wi rhoAB by rewrite /rho' HWi formsoE.
      have Hmono :
          pur_dist (formso Wi tau) (formso Wi rhoAB) <= pur_dist tau rhoAB.
      { have [/= _ Hmono] :=
          pd_mono (cptp_cptn HWi_cptp) Ptau Prho Htau_tr_le1 Hrho_tr.
        exact: Hmono. }
        rewrite Htau'E Hrho'E0.
        exact: le_trans Hmono Htau_pd. }
      have Htau'_pos : 0 < @complex.Re R (\Tr tau').
      { have Htau_pos : 0 < @complex.Re R (\Tr tau) :=
          eps_ball_trlf_gt0 Htau_ball.
        by rewrite /tau' HWi /formlf lftraceC comp_lfunA isofE comp_lfun1l. }
      by rewrite /eps_ball Ptau' Htau'_pos Htau'_tr Htau'_pd.
  }
  have Hphi_pos_trace :
      forall (S T : {set L}) (x : 'F[H]_S),
      x \is psdlf -> @complex.Re R (\Tr x) <= 1 ->
      0 < @complex.Re R (\Tr x) -> 0 < phi_min T x.
  {
    move=> S T x Px Hx_tr Hx_tr_pos.
    have eqST : (S :\: T) :|: (S :&: T) = S.
      by rewrite finset.setUC finset.setID.
    have disSplit : [disjoint (S :\: T) & (S :&: T)].
    { apply/disjointP=> z; rewrite !inE.
      by case: (z \in T); rewrite ?andbF ?andbT. }
    pose dT : R := (dim 'H[H]_(S :\: T))%:R.
    have HdT_pos : 0 < dT by rewrite /dT ltr0n dim_proper.
    rewrite /phi_min.
    apply: (@lt_le_trans _ _ ((@complex.Re R (\Tr x)) / dT)).
    - by apply: divr_gt0.
    - apply: lb_le_inf.
      + pose sigma1 : 'F[H]_(S :&: T) := \1.
        exists (@complex.Re R (\Tr sigma1)).
        rewrite /phi_min_feasible.
        exists sigma1; split.
        { by rewrite qualifE h2mx1; apply: psdmx1. }
        split; last by [].
        rewrite sdotf11 castlf1.
        have Hx_den : x \is denlf.
        { apply/denlfP; split=> //.
          have Hreal : \Tr x \is Num.real := ger0_real (psdlf_trlf Px).
          by rewrite -(RRe_real Hreal) lecR. }
        have Hx_le1 : x ⊑ (\1 : 'F[H]_S)
          := denf_le1 (DenLf_Build Hx_den).
        by move: Hx_le1; rewrite lefE.
      + move=> v [sigma [Psigma [Hfeas ->]]].
        have Htr_sigma_real :
            (\Tr sigma : C) = (@complex.Re R (\Tr sigma))%:C
          by rewrite RRe_real // ger0_real // psdlf_trlf.
        have Hx_tr_real : (\Tr x : C) = (@complex.Re R (\Tr x))%:C
          by rewrite RRe_real // ger0_real // psdlf_trlf.
        have Hx_leC :
            \Tr x <= (dim 'H[H]_(S :\: T))%:R * \Tr sigma.
        { have Hgap_nonneg := psdlf_trlf Hfeas.
          move: Hgap_nonneg.
          rewrite raddfB /= castlf_trlfE (trlf_lift_I disSplit).
          by rewrite subr_ge0. }
        move: Hx_leC; rewrite Hx_tr_real Htr_sigma_real.
        rewrite /dT -natrC -rmorphM /= lecR => Hx_leR.
        rewrite ler_pdivrMr //.
        by rewrite mulrC.
  }
  have HhminE_iso_A :
      forall (X X' Y : {set L}) (disXY : [disjoint X & Y])
        (disX'Y : [disjoint X' & Y])
        (omega : 'F[H]_(X :|: Y)) (U0 : 'FI[H]_(X, X')),
      omega \is psdlf -> @complex.Re R (\Tr omega) <= 1 ->
      0 < @complex.Re R (\Tr omega) ->
      hminE Y ((U0 \⊗ (\1 : 'F[H]_Y)) \o omega \o
        (U0 \⊗ (\1 : 'F[H]_Y))^A) = hminE Y omega.
  {
    move=> X X' Y disXY disX'Y omega U0 Pomega Homega_tr Homega_pos.
    pose W0 := U0 \⊗ (\1 : 'F[H]_Y).
    pose omega' : 'F[H]_(X' :|: Y) := W0 \o omega \o W0^A.
    have W0_iso : W0 \is isolf.
    { apply/isolfP.
      by rewrite /W0 tenf_adj -tenf_comp ?disXY ?disX'Y //
        isofE adjf1 comp_lfun1l tenf11. }
    have W0K : W0^A \o W0 = \1 by move/isolfP: W0_iso.
    have Pomega' : omega' \is psdlf.
    { apply/psdlfP=> x.
      rewrite /omega' !comp_lfunE /= -adj_dotEl.
      by move/psdlfP: Pomega. }
    have Homega'_tr_eq :
        @complex.Re R (\Tr omega') = @complex.Re R (\Tr omega).
    { by rewrite /omega' lftraceC comp_lfunA W0K comp_lfun1l. }
    have Homega'_tr : @complex.Re R (\Tr omega') <= 1
      by rewrite Homega'_tr_eq.
    have Homega'_pos : 0 < @complex.Re R (\Tr omega')
      by rewrite Homega'_tr_eq.
    (* Forward half: Φ-min isometry invariance (tb:Phi v)
       with the trivial isometry \1_Y on the conditioning register. *)
    have IY_iso : (\1 : 'F[H]_Y) \is isolf.
    { apply/isolfP. by rewrite adjf1 comp_lfun1l. }
    pose IY : 'FI[H]_(Y, Y) := IsoLf_Build IY_iso.
    have HIY : (\1 : 'F[H]_Y) = IY by exact: IsoLf_BuildE IY_iso.
    have Hphi_fwd : phi_min Y omega' <= phi_min Y omega.
    { rewrite /omega' /W0 HIY.
      rewrite (@phi_min_v_iso_inv R L H X X' Y Y
        disXY disX'Y omega U0 IY Pomega).
      exact: lexx. }
    have Hforward : (hminE Y omega <= hminE Y omega')%E.
    { rewrite /hminE leeN2.
      have Hphi_pos := Hphi_pos_trace (X' :|: Y) Y
        omega' Pomega' Homega'_tr Homega'_pos.
      exact: elog2_le _ _ Hphi_pos Hphi_fwd. }
    have HUa_b1 : U0^A \is bound1lf.
      by rewrite bound1lf_adj; exact: isolf_bound1 (is_isolf U0).
    pose Ua := Bound1Lf_Build HUa_b1.
    have HUa : U0^A = Ua by exact: Bound1Lf_BuildE HUa_b1.
    have HformUa_cp : (formso Ua : 'SO[H]_(X', X)) \is cpmap
      by exact: formso_cp.
    have HformUa_dualtn : (formso Ua : 'SO[H]_(X', X))^*o \is tnmap.
    { rewrite dualso_formso.
      have HUaA : Ua^A = U0 by rewrite -HUa adjfK.
      rewrite HUaA.
      have HU_cptp : formso U0 \is cptp by apply: is_cptp.
      exact: cptn_tnmap (cptp_cptn HU_cptp). }
    pose W0a := Ua \⊗ (\1 : 'F[H]_Y).
    have W0aW0 : W0a \o W0 = \1.
    { rewrite /W0a /W0 -HUa -tenf_comp ?disXY ?disX'Y //.
      by rewrite isofE comp_lfun1l tenf11. }
    have Hback_eq : W0a \o omega' \o W0a^A = omega.
    { rewrite /omega'.
      rewrite comp_lfunA.
      rewrite [W0a \o (W0 \o omega)]comp_lfunA W0aW0 comp_lfun1l.
      have HW0aA : W0^A \o W0a^A = \1.
      { by rewrite -adjf_comp W0aW0 adjf1. }
      by rewrite -comp_lfunA HW0aA comp_lfun1r. }
    have Hmap_back :
        (((formso Ua : 'SO[H]_(X', X)) :⊗ (\:1 : 'SO[H]_Y)) omega')
        = omega.
    {
      have HW0amap :
          ((formso Ua : 'SO[H]_(X', X)) :⊗ (\:1 : 'SO[H]_Y)) =
          formso W0a.
      { by rewrite /W0a -formso1 tenso_formso. }
      by rewrite HW0amap formsoE Hback_eq.
    }
    have Hphi_back : phi_min Y omega <= phi_min Y omega'.
    { rewrite -Hmap_back.
      exact: (@phi_min_data_proc_A R L H X' X Y
        disX'Y disXY omega' (formso Ua) Pomega'
        HformUa_cp HformUa_dualtn). }
    have Hback : (hminE Y omega' <= hminE Y omega)%E.
    { rewrite /hminE leeN2.
      have Hphi_pos := Hphi_pos_trace (X :|: Y) Y
        omega Pomega Homega_tr Homega_pos.
      exact: elog2_le _ _ Hphi_pos Hphi_back. }
    by apply/eqP; rewrite eq_le Hforward Hback.
  }
  pose Ptarget :=
    (supplf (ptrace_cast disA'B' rho') \O
     supplf (ptrace_castl disA'B' rho') : 'F[H]_S_A'B').
  have HhmaxE_image :
      forall tau : 'F[H]_S_AB,
      eps_ball eps rhoAB tau ->
      hmaxE B' (W \o tau \o W^A) = hmaxE B tau.
  {
    move=> tau Htau_ball.
    have Ptau : tau \is psdlf := eps_ball_psdlf Htau_ball.
    have Htau_tr : @complex.Re R (\Tr tau) <= 1 := eps_ball_trlf Htau_ball.
    have Htau_den : tau \is denlf.
    { apply/denlfP; split=> //.
      have Hreal : \Tr tau \is Num.real := ger0_real (psdlf_trlf Ptau).
      by rewrite -(RRe_real Hreal) lecR. }
    have Htau_pos : 0 < @complex.Re R (\Tr tau) :=
      eps_ball_trace_pos Prho Hrho_tr Heps Htau_ball.
    have Htau_ne0 : tau != 0.
    { apply/eqP=> H0.
      by move: Htau_pos; rewrite H0 raddf0 raddf0 ltxx. }
    have disAB_Ciso : [disjoint S_AB & Ciso]
      by rewrite /S_AB disjointUX disA_Ciso disB_Ciso.
    have disApBp_Ciso : [disjoint S_A'B' & Ciso]
      by rewrite /S_A'B' disjointUX disAp_Ciso disBp_Ciso.
    have HptC_src :
        forall X : 'F[H]_(S_AB :|: Ciso),
        @ptrace_cast3C R L H A B Ciso disA_Ciso disB_Ciso X =
        ptrace_cast disAB_Ciso X.
    { move=> X.
      rewrite /ptrace_cast3C /ptrace_cast /ptrace_cast_gen.
      have Hdu : setDU3_C disA_Ciso disB_Ciso = setDU_r disAB_Ciso
        := eq_irrelevance _ _.
      by rewrite Hdu. }
    have HptC_tgt :
        forall X : 'F[H]_(S_A'B' :|: Ciso),
        @ptrace_cast3C R L H A' B' Ciso disAp_Ciso disBp_Ciso X =
        ptrace_cast disApBp_Ciso X.
    { move=> X.
      rewrite /ptrace_cast3C /ptrace_cast /ptrace_cast_gen.
      have Hdu : setDU3_C disAp_Ciso disBp_Ciso = setDU_r disApBp_Ciso
        := eq_irrelevance _ _.
      by rewrite Hdu. }
    have [theta [Htheta_den [Htheta_rank_le Htheta_marg0]]] :=
      @purification_exists_with_ancilla R L H A B Ciso
        disA_Ciso disB_Ciso tau dimAB_Ciso Htau_den Htau_ne0.
    have Htheta_marg3C :
        @ptrace_cast3C R L H A B Ciso disA_Ciso disB_Ciso theta = tau.
    { rewrite HptC_src.
      rewrite (eq_irrelevance disAB_Ciso
        (pur.disAB_C disA_Ciso disB_Ciso)).
      exact: Htheta_marg0. }
    have Htheta_ne0 : theta != 0.
    { apply/eqP=> H0.
      move/eqP: Htau_ne0; apply.
      by rewrite -Htheta_marg0 H0 /ptrace_cast /ptrace_cast_gen raddf0 /= raddf0. }
    have Htheta_rank : \Rank theta = 1%N.
    {
      have Hrank_gt0 : (0 < \Rank theta)%N.
      { rewrite lt0n /lfrank mxrank_eq0.
        apply/eqP=> Hmx0.
        apply/negP: Htheta_ne0; rewrite negbK.
        by apply/eqP/h2mx_inj; rewrite Hmx0 h2mx0. }
      by apply/eqP; rewrite eqn_leq Htheta_rank_le Hrank_gt0.
    }
    pose WI : 'FI[H]_(S_AB, S_A'B') := IsoLf_Build W_iso.
    have HWI : W = WI by exact: IsoLf_BuildE W_iso.
    have IC_iso : (\1 : 'F[H]_Ciso) \is isolf.
    { apply/isolfP. by rewrite adjf1 comp_lfun1l. }
    pose IC : 'FI[H]_(Ciso, Ciso) := IsoLf_Build IC_iso.
    have HIC : (\1 : 'F[H]_Ciso) = IC by exact: IsoLf_BuildE IC_iso.
    pose W3 := WI \⊗ IC.
    pose theta' : 'F[H]_(S_A'B' :|: Ciso) := W3 \o theta \o W3^A.
    have W3_iso : W3 \is isolf.
    { apply/isolfP.
      by rewrite /W3 tenf_adj -tenf_comp ?disAB_Ciso ?disApBp_Ciso //
        isofE isofE tenf11. }
    have W3K : W3^A \o W3 = \1 by move/isolfP: W3_iso.
    have Htheta_psd : theta \is psdlf := denlf_psd Htheta_den.
    have Htheta'_psd : theta' \is psdlf.
    { apply/psdlfP=> x.
      rewrite /theta' !comp_lfunE /= -adj_dotEl.
      by move/psdlfP: Htheta_psd. }
    have Htheta_tr_eq : \Tr theta = \Tr tau.
    { rewrite -Htheta_marg0 /ptrace_cast /ptrace_cast_gen castlf_trlfE.
      have /cptpP [_ /tpmapP Htp] :=
        @ptraceso_qc R L H Ciso (S_AB :|: Ciso).
      by rewrite Htp. }
    have Htheta'_tr_eq : \Tr theta' = \Tr theta.
    { by rewrite /theta' lftraceC comp_lfunA W3K comp_lfun1l. }
    have Htheta'_tr : @complex.Re R (\Tr theta') <= 1
      by rewrite Htheta'_tr_eq Htheta_tr_eq.
    have Htheta'_den : theta' \is denlf.
    { apply/denlfP; split=> //.
      have Hreal : \Tr theta' \is Num.real :=
        ger0_real (psdlf_trlf Htheta'_psd).
      by rewrite -(RRe_real Hreal) lecR. }
    have Htheta'_rank_le : (\Rank theta' <= 1)%N.
    { rewrite /theta' /lfrank !h2mx_comp h2mx_adj.
      exact: leq_trans (mxrankM_maxl _ _)
        (leq_trans (mxrankM_maxr _ _) Htheta_rank_le). }
    have Htheta'_ne0 : theta' != 0.
    { apply/eqP=> H0.
      move: Htau_pos.
      by rewrite -Htheta_tr_eq -Htheta'_tr_eq H0 raddf0 raddf0 ltxx. }
    have Htheta'_rank : \Rank theta' = 1%N.
    {
      have Hrank_gt0 : (0 < \Rank theta')%N.
      { rewrite lt0n /lfrank mxrank_eq0.
        apply/eqP=> Hmx0.
        apply/negP: Htheta'_ne0; rewrite negbK.
        by apply/eqP/h2mx_inj; rewrite Hmx0 h2mx0. }
      by apply/eqP; rewrite eqn_leq Htheta'_rank_le Hrank_gt0.
    }
    have Htheta'_marg3C :
        @ptrace_cast3C R L H A' B' Ciso disAp_Ciso disBp_Ciso theta' =
        W \o tau \o W^A.
    { rewrite HptC_tgt /theta' /W3.
      rewrite (@ptrace_cast_isometry_conj R L H S_AB Ciso S_A'B'
        Ciso disAB_Ciso disApBp_Ciso theta WI IC).
      rewrite (eq_irrelevance disAB_Ciso
        (pur.disAB_C disA_Ciso disB_Ciso)).
      by rewrite Htheta_marg0 -HWI. }
    pose thetaAC : 'F[H]_(A :|: Ciso) :=
      @ptrace_cast3B R L H A B Ciso disAB disB_Ciso theta.
    pose thetaA'C : 'F[H]_(A' :|: Ciso) :=
      @ptrace_cast3B R L H A' B' Ciso disA'B' disBp_Ciso theta'.
    have HthetaAC_psd : thetaAC \is psdlf.
    { rewrite /thetaAC /ptrace_cast3B.
      exact: ptrace_cast_gen_psdlf Htheta_psd. }
    have HthetaAC_tr_eq : \Tr thetaAC = \Tr theta.
    { rewrite /thetaAC /ptrace_cast3B /ptrace_cast_gen castlf_trlfE.
      have /cptpP [_ /tpmapP Htp] :=
        @ptraceso_qc R L H B (A :|: B :|: Ciso).
      exact: Htp. }
    have HthetaAC_tr : @complex.Re R (\Tr thetaAC) <= 1
      by rewrite HthetaAC_tr_eq Htheta_tr_eq.
    have HthetaAC_pos : 0 < @complex.Re R (\Tr thetaAC)
      by rewrite HthetaAC_tr_eq Htheta_tr_eq.
    have HthetaA'C_eq :
        thetaA'C =
        (U \⊗ (\1 : 'F[H]_Ciso)) \o thetaAC \o
        (U \⊗ (\1 : 'F[H]_Ciso))^A.
    {
      set eqS := setUC_swap3 A B Ciso
        : A :|: B :|: Ciso = A :|: Ciso :|: B.
      set eqS' := setUC_swap3 A' B' Ciso
        : A' :|: B' :|: Ciso = A' :|: Ciso :|: B'.
      have disAC_B : [disjoint A :|: Ciso & B].
      { by rewrite disjointUX disAB disjoint_sym disB_Ciso. }
      have disApC_Bp : [disjoint A' :|: Ciso & B'].
      { by rewrite disjointUX disA'B' disjoint_sym disBp_Ciso. }
      have HptB_src_recast :
          thetaAC = ptrace_cast disAC_B (castlf (eqS, eqS) theta).
      { rewrite /thetaAC /ptrace_cast3B /ptrace_cast /ptrace_cast_gen.
        have eq_res :
            (A :|: B :|: Ciso) :\: B = (A :|: Ciso :|: B) :\: B
          by rewrite eqS.
        rewrite (ptracelf_castlf_eq eqS eq_res) castlf_comp.
        by congr (castlf (_, _) _); exact: eq_irrelevance. }
      have HptB_tgt_recast :
          thetaA'C = ptrace_cast disApC_Bp (castlf (eqS', eqS') theta').
      { rewrite /thetaA'C /ptrace_cast3B /ptrace_cast /ptrace_cast_gen.
        have eq_res :
            (A' :|: B' :|: Ciso) :\: B' =
            (A' :|: Ciso :|: B') :\: B'
          by rewrite eqS'.
        rewrite (ptracelf_castlf_eq eqS' eq_res) castlf_comp.
        by congr (castlf (_, _) _); exact: eq_irrelevance. }
      have Hcast_theta' :
          castlf (eqS', eqS') theta' =
          ((U \⊗ (\1 : 'F[H]_Ciso)) \⊗ V) \o
            castlf (eqS, eqS) theta \o
          (((U \⊗ (\1 : 'F[H]_Ciso)) \⊗ V)^A).
      { rewrite /theta' /W3 -HWI -HIC /W.
        to_Fnd.
        by rewrite -!tenFA (tenFC (to_Fnd V)
          (to_Fnd (\1 : 'F[H]_Ciso))) !tenFA. }
      have UAC_iso : (U \⊗ (\1 : 'F[H]_Ciso)) \is isolf.
      { apply/isolfP.
        by rewrite tenf_adj -tenf_comp ?disA_Ciso ?disAp_Ciso //
          isofE adjf1 comp_lfun1l tenf11. }
      pose UAC : 'FI[H]_(A :|: Ciso, A' :|: Ciso) :=
        IsoLf_Build UAC_iso.
      have HUAC : (U \⊗ (\1 : 'F[H]_Ciso)) = UAC
        by exact: IsoLf_BuildE UAC_iso.
      rewrite HptB_tgt_recast Hcast_theta' HUAC.
      rewrite (@ptrace_cast_isometry_conj R L H (A :|: Ciso) B
        (A' :|: Ciso) B' disAC_B disApC_Bp
        (castlf (eqS, eqS) theta) UAC V).
      by rewrite -HptB_src_recast.
    }
    have Hhmin_AC_iso :
        hminE Ciso thetaA'C = hminE Ciso thetaAC.
    { rewrite HthetaA'C_eq.
      exact: (@HhminE_iso_A A A' Ciso disA_Ciso disAp_Ciso
        thetaAC U HthetaAC_psd HthetaAC_tr HthetaAC_pos). }
    have Hdual_src :=
      @minmax_dual R L H A B Ciso disAB disA_Ciso disB_Ciso
        Cp_src Cpp_src
        disA_Cp_src disA_Cpp_src disB_Cp_src disB_Cpp_src
        disCp_Cpp_src dimA_Cp_src dimC_Cp_Cpp_src dimB_Cpp_src
        theta Htheta_den Htheta_rank.
    have Hdual_tgt :=
      @minmax_dual R L H A' B' Ciso disA'B' disAp_Ciso disBp_Ciso
        Cp_tgt Cpp_tgt
        disAp_Cp_tgt disAp_Cpp_tgt disBp_Cp_tgt disBp_Cpp_tgt
        disCp_Cpp_tgt dimAp_Cp_tgt dimC_Cp_Cpp_tgt dimBp_Cpp_tgt
        theta' Htheta'_den Htheta'_rank.
    rewrite -Htheta'_marg3C -Htheta_marg3C Hdual_tgt Hdual_src.
    by rewrite /thetaA'C /thetaAC Hhmin_AC_iso.
  }
  have Htarget_support_opt :
      exists taub : 'F[H]_S_A'B',
        eps_ball eps rho' taub /\
        smooth_hmaxE B' eps rho' = hmaxE B' taub /\
        Ptarget \o taub = taub /\
        taub \o Ptarget = taub.
  {
    have dimApBp_Ciso : (dim 'H[H]_A' * dim 'H[H]_B' <= dim 'H[H]_Ciso)%N.
    { by rewrite -(tenv_dim disA'B'). }
    have [taub [Hball [Hopt [Hsupp_l Hsupp_r]]]] :=
      @smoothing_support_hmax R L H A' B' Ciso disA'B'
      disAp_Ciso disBp_Ciso dimApBp_Ciso Cp_tgt Cpp_tgt
      disAp_Cp_tgt disAp_Cpp_tgt disBp_Cp_tgt disBp_Cpp_tgt
      disCp_Cpp_tgt dimAp_Cp_tgt dimC_Cp_Cpp_tgt dimBp_Cpp_tgt
      eps rho' Hrho'_den Heps'.
    exists taub; split=> //; split=> //; split;
      by rewrite /Ptarget.
  }
  have Hsupported_preimage :
      forall taub : 'F[H]_S_A'B',
      eps_ball eps rho' taub ->
      Ptarget \o taub = taub ->
      taub \o Ptarget = taub ->
      exists tau0 : 'F[H]_S_AB,
        eps_ball eps rhoAB tau0 /\
        W \o tau0 \o W^A = taub.
  {
    (* Remaining bridge: support-labelled preimage under the range
       projection of U \otimes V.  The proof should use
       ptrace_cast_isometry_conj for both marginals, then cancel
       W^A (P_A' \otimes P_B') and W (W^A taub W) W^A on the supported
       target witness. *)
    move=> taub Htaub_ball Htaub_supp_l Htaub_supp_r.
    have Htaub_ball0 := Htaub_ball.
    have Wa_b1 : W^A \is bound1lf.
      by rewrite bound1lf_adj; exact: isolf_bound1 W_iso.
    pose Wa := Bound1Lf_Build Wa_b1.
    have HWa : W^A = Wa by exact: Bound1Lf_BuildE Wa_b1.
    pose taub0 := W^A \o taub \o W.
    pose PA := (U \o U^A : 'F[H]_A').
    pose PB := (V \o V^A : 'F[H]_B').
    pose Pimg := ((U \o U^A) \⊗ (V \o V^A) : 'F[H]_S_A'B').
    have PAproj : PA \is projlf.
    {
      apply/projlfP; split.
      - by rewrite /PA adjf_comp adjfK.
      - apply/lfunP=> x; rewrite /PA !comp_lfunE /=.
        have -> : U^A (U (U^A x)) = U^A x.
        {
          rewrite -comp_lfunE [U^A \o U]isofE.
          by rewrite lfunE.
        }
        reflexivity.
    }
    have PBproj : PB \is projlf.
    {
      apply/projlfP; split.
      - by rewrite /PB adjf_comp adjfK.
      - apply/lfunP=> x; rewrite /PB !comp_lfunE /=.
        have -> : V^A (V (V^A x)) = V^A x.
        {
          rewrite -comp_lfunE [V^A \o V]isofE.
          by rewrite lfunE.
        }
        reflexivity.
    }
    have Ptaub : taub \is psdlf by exact: eps_ball_psdlf Htaub_ball.
    have Ptaub0 : taub0 \is psdlf.
    {
      apply/psdlfP=> x.
      move/psdlfP: Ptaub => /(_ (W x)) Hx.
      rewrite /taub0 !comp_lfunE /=.
      rewrite -adj_dotEl adjfK.
      exact Hx.
    }
    have Htaub0_tr : @complex.Re R (\Tr taub0) <= 1.
    {
      move: Htaub_ball => /andP [/andP [_ Htaub_tr] _].
      have Htaub_tr_real : (\Tr taub : C) = (@complex.Re R (\Tr taub))%:C.
      { by rewrite RRe_real // ger0_real // psdlf_trlf. }
      have Htaub0_tr_real : (\Tr taub0 : C) = (@complex.Re R (\Tr taub0))%:C.
      { by rewrite RRe_real // ger0_real // psdlf_trlf. }
      have HWa_tn : formso Wa \is tnmap by exact: formso_tn.
      have HWa_cptn : formso Wa \is cptn.
        by rewrite qualifE formso_cp HWa_tn.
      have Hle : \Tr taub0 <= \Tr taub.
      {
        have Htaub0E : taub0 = Wa \o taub \o Wa^A.
        {
          rewrite /taub0 HWa.
          by rewrite -HWa adjfK.
        }
        have Hsoa : ((QOperation_Build HWa_cptn) : 'SO(_, _)) = formso Wa
          by exact: QOperation_BuildE.
        have Hle' := qo_trlfE (QOperation_Build HWa_cptn) Ptaub.
        rewrite Hsoa formsoE -Htaub0E in Hle'.
        exact: Hle'.
      }
      have HleR : @complex.Re R (\Tr taub0) <= @complex.Re R (\Tr taub).
      { by move: Hle; rewrite Htaub0_tr_real Htaub_tr_real !lecR. }
      exact: le_trans HleR Htaub_tr.
    }
    have HptrA_conj :
        ptrace_cast disA'B' rho' =
        U \o ptrace_cast disAB rhoAB \o U^A.
    {
      by rewrite /rho' /W
        (@ptrace_cast_isometry_conj R L H A B A' B' disAB disA'B').
    }
    have HUAperp0 :
        U^A \o (ProjLf_Build PAproj)^⟂ = 0.
    {
      rewrite /cplmt /PA comp_lfunDr comp_lfunNr comp_lfun1r.
      rewrite comp_lfunA isofE comp_lfun1l.
      by rewrite subrr.
    }
    have HVperp0 :
        (ProjLf_Build PBproj)^⟂ \o V = 0.
    {
      rewrite /cplmt /PB comp_lfunDl comp_lfunNl comp_lfun1l.
      rewrite -comp_lfunA isofE comp_lfun1r.
      by rewrite subrr.
    }
    have HsuppA_img :
        (supph (ptrace_cast disA'B' rho') `<=`
         HSType (ProjLf_Build PAproj))%HS.
    {
      apply: (supph_trlf0_le
        (A := PsdLf_Build (ptrace_cast_psdlf disA'B' Prho'))).
      rewrite hscmpltE hsE /=.
      have Htr_eq :=
        f_equal (fun X => \Tr (X \o (ProjLf_Build PAproj)^⟂)) HptrA_conj.
      rewrite -!comp_lfunA HUAperp0 !comp_lfun0r /lftrace h2mx0 mxtrace0 in Htr_eq.
      exact: Htr_eq.
    }
    have HsuppB_img :
        (supph (ptrace_castl disA'B' rho') `<=`
         HSType (ProjLf_Build PBproj))%HS.
    {
      apply: (supph_trlf0_le
        (A := PsdLf_Build (ptrace_castl_psdlf disA'B' Prho'))).
      rewrite -trlf_lift_partial.
      rewrite -(supph_projK (ProjLf_Build PBproj)) hsE /=.
      have Hlift_ten :
          (((\1 : 'F[H]_A') \O
             ((ProjLf_Build PBproj)^⟂ : 'F[H]_B')) :
              'F[H]_S_A'B') =
          ((\1 : 'F[H]_A') \⊗
             ((ProjLf_Build PBproj)^⟂ : 'F[H]_B')).
        by apply: to_Fnd_inj; rewrite (sdotFT _ _ disA'B') to_Fnd_tenE.
      change ((supph PB)^⟂) with ((supph (ProjLf_Build PBproj))^⟂).
      rewrite (supph_projK (ProjLf_Build PBproj)) hsE /=.
      rewrite /rho' lftraceC Hlift_ten /W.
      pose Pperp := ((ProjLf_Build PBproj)^⟂ : 'F[H]_B').
      have Hkill_left :
          (((\1 : 'F[H]_A') \⊗ Pperp) \o
           (U \⊗ V)) = 0.
      {
        rewrite -tenf_comp ?disA'B' ?disAB //.
        rewrite comp_lfun1l HVperp0.
        by rewrite tenf0.
      }
      have Hassoc :
          (((\1 : 'F[H]_A') \⊗ Pperp) \o ((U \⊗ V) \o rhoAB)) =
          ((((\1 : 'F[H]_A') \⊗ Pperp) \o (U \⊗ V)) \o rhoAB).
      {
        by rewrite -comp_lfunA.
      }
      rewrite comp_lfunA.
      rewrite Hassoc Hkill_left comp_lfun0l.
      by rewrite comp_lfun0l /lftrace h2mx0 mxtrace0.
    }
    have HQA_left :
        PA \o supplf (ptrace_cast disA'B' rho') =
        supplf (ptrace_cast disA'B' rho').
    {
      have Hle :
          HSType (supplf (ptrace_cast disA'B' rho')) `<=`
          HSType (ProjLf_Build PAproj).
      {
        exact: HsuppA_img.
      }
      by move: Hle; rewrite leh_compr !hsE /= => /eqP.
    }
    have HQA_right :
        supplf (ptrace_cast disA'B' rho') \o PA =
        supplf (ptrace_cast disA'B' rho').
    {
      have Hle :
          HSType (supplf (ptrace_cast disA'B' rho')) `<=`
          HSType (ProjLf_Build PAproj).
      {
        exact: HsuppA_img.
      }
      by move: Hle; rewrite leh_compl !hsE /= => /eqP.
    }
    have HQB_left :
        PB \o supplf (ptrace_castl disA'B' rho') =
        supplf (ptrace_castl disA'B' rho').
    {
      have Hle :
          HSType (supplf (ptrace_castl disA'B' rho')) `<=`
          HSType (ProjLf_Build PBproj).
      {
        exact: HsuppB_img.
      }
      by move: Hle; rewrite leh_compr !hsE /= => /eqP.
    }
    have HQB_right :
        supplf (ptrace_castl disA'B' rho') \o PB =
        supplf (ptrace_castl disA'B' rho').
    {
      have Hle :
          HSType (supplf (ptrace_castl disA'B' rho')) `<=`
          HSType (ProjLf_Build PBproj).
      {
        exact: HsuppB_img.
      }
      by move: Hle; rewrite leh_compl !hsE /= => /eqP.
    }
    have Hq_left : Pimg \o Ptarget = Ptarget.
    {
      rewrite /Ptarget.
      have HQ_ten :
          (((supplf (ptrace_cast disA'B' rho')) \O
             supplf (ptrace_castl disA'B' rho')) : 'F[H]_S_A'B') =
          ((supplf (ptrace_cast disA'B' rho')) \⊗
           supplf (ptrace_castl disA'B' rho')).
        by apply: to_Fnd_inj; rewrite (sdotFT _ _ disA'B') to_Fnd_tenE.
      rewrite /Pimg HQ_ten -tenf_comp ?disA'B' //.
      by rewrite HQA_left HQB_left.
    }
    have Hq_right : Ptarget \o Pimg = Ptarget.
    {
      rewrite /Ptarget.
      have HQ_ten :
          (((supplf (ptrace_cast disA'B' rho')) \O
             supplf (ptrace_castl disA'B' rho')) : 'F[H]_S_A'B') =
          ((supplf (ptrace_cast disA'B' rho')) \⊗
           supplf (ptrace_castl disA'B' rho')).
        by apply: to_Fnd_inj; rewrite (sdotFT _ _ disA'B') to_Fnd_tenE.
      rewrite /Pimg HQ_ten -tenf_comp ?disA'B' //.
      by rewrite HQA_right HQB_right.
    }
    have Htaub_img_l : Pimg \o taub = taub.
    {
      by rewrite -Htaub_supp_l comp_lfunA Hq_left.
    }
    have Htaub_img_r : taub \o Pimg = taub.
    {
      by rewrite -Htaub_supp_r -comp_lfunA Hq_right.
    }
    have HW_WA : W \o W^A = Pimg.
    {
      rewrite /W /Pimg tenf_adj.
      by rewrite -tenf_comp ?disA'B' //.
    }
    have Hwitness_conj : W \o taub0 \o W^A = taub.
    {
      rewrite /taub0 -!comp_lfunA HW_WA.
      rewrite comp_lfunA HW_WA.
      by rewrite Htaub_img_r Htaub_img_l.
    }
      have Htaub0_pd : pur_dist taub0 rhoAB <= eps.
      {
        move: Htaub_ball => /andP [/andP [_ _] Htaub_pd].
      have Htaub0E : taub0 = formso Wa taub
        by rewrite /taub0 HWa formsoE -HWa adjfK.
      have Hrho0E : rhoAB = formso Wa rho'.
      {
        rewrite /rho' HWi HWa formsoE.
        have HWaA : Wa^A = Wi by rewrite -HWa HWi adjfK.
        have HWiA' : W^A = Wi^A by exact: (f_equal (fun X => X^A) HWi).
        have HWiA : (Wa : 'F[H]_(S_A'B', S_AB)) = Wi^A.
        {
          transitivity (W^A : 'F[H]_(S_A'B', S_AB)).
          - exact: (esym HWa).
          - exact: HWiA'.
        }
        rewrite HWaA.
        rewrite -!comp_lfunA.
        rewrite HWiA.
        rewrite !comp_lfunA.
        rewrite [Wi^A \o Wi]isofE comp_lfun1l.
        rewrite -comp_lfunA.
        by rewrite [Wi^A \o Wi]isofE comp_lfun1r.
      }
      have HWa_cptn : formso Wa \is cptn
        by rewrite qualifE formso_cp formso_tn.
      have Htaub_tr_le1 : @complex.Re R (\Tr taub) <= 1.
      {
        move: Htaub_ball0 => /andP [/andP [_ Htb_tr] _].
        exact: Htb_tr.
      }
      have Hmono :
          pur_dist (formso Wa taub) (formso Wa rho') <= pur_dist taub rho'.
      {
        have [/= _ Hmono] :=
          pd_mono HWa_cptn Ptaub Prho' Htaub_tr_le1 Hrho'_tr.
        exact: Hmono.
      }
        rewrite Htaub0E Hrho0E.
        exact: le_trans Hmono Htaub_pd.
      }
      have Htaub0_pos : 0 < @complex.Re R (\Tr taub0).
      {
        have Holdball :
            ((taub0 \is psdlf) && (@complex.Re R (\Tr taub0) <= 1)) &&
            (pur_dist taub0 rhoAB <= eps).
        { by rewrite Ptaub0 Htaub0_tr Htaub0_pd. }
        exact: (eps_ball_trace_pos_from_small Prho Hrho_tr Heps Holdball).
      }
      have Htaub0_ball : eps_ball eps rhoAB taub0.
      {
        by rewrite /eps_ball Ptaub0 Htaub0_pos Htaub0_tr Htaub0_pd.
      }
    by exists taub0; split.
  }
  apply/eqP; rewrite eq_le; apply/andP; split.
  - rewrite /smooth_hmaxE leeN2.
    apply: ge_ereal_sup => v [tau [Htau_ball ->]].
    pose tau' := W \o tau \o W^A.
    have Htau'_ball : eps_ball eps rho' tau' := Hball_image tau Htau_ball.
    rewrite -(HhmaxE_image tau Htau_ball).
    apply: ereal_sup_ubound.
    by exists tau'.
  - case: Htarget_support_opt => taub
      [Htaub_ball [Htarget_opt [Htaub_supp_l Htaub_supp_r]]].
    have [tau0 [Htau0_ball Htau0_img]] :=
      Hsupported_preimage taub Htaub_ball Htaub_supp_l Htaub_supp_r.
    rewrite Htarget_opt -Htau0_img HhmaxE_image //.
    exact: Hsmooth_hmax_ball_leE Htau0_ball.
Qed.

End SmoothIsoHMax.

(* ================================================================== *)
(* Duality of smooth min- and max-entropies                              *)
(* Tomamichel thesis (arXiv:1203.2142), Theorem 5.4 — tex th:smooth-dual. *)
(* math: For regular ε ≥ 0 and pure ρ_{ABC} ∈ S_≤(H_{ABC}),                  *)
(*   H^ε_max(A|B)_ρ = - H^ε_min(A|C)_ρ.                                  *)
(* Formalized on the AB and AC marginals of ρ_{ABC}.                       *)
(* The strict upper bound on ε is the regularity condition used by the    *)
(* real-valued smooth entropy interface to avoid the zero-state           *)
(* / unbounded-sup corner; downstream smooth-DPI callers already carry it.*)
(* ================================================================== *)

Section SmoothDual.
Variable (L : finType) (H : L -> chsType).
Variables (A B C0 : {set L}).
Hypothesis disAB : [disjoint A & B].
Hypothesis disAC : [disjoint A & C0].
Hypothesis disBC : [disjoint B & C0].
(* Ambient proof labels supplied by callers: Tomamichel's two smoothing
   embeddings need room for C -> Cbig and B -> Bbig. *)
Variables (Cbig Bbig : {set L}).
Hypothesis disA_Cbig : [disjoint A & Cbig].
Hypothesis disB_Cbig : [disjoint B & Cbig].
Hypothesis dimC_Cbig : (dim 'H[H]_C0 <= dim 'H[H]_Cbig)%N.
Hypothesis dimAB_Cbig : (dim 'H[H]_(A :|: B) <= dim 'H[H]_Cbig)%N.
Hypothesis disA_Bbig : [disjoint A & Bbig].
Hypothesis disBbig_C : [disjoint Bbig & C0].
Hypothesis dimB_Bbig : (dim 'H[H]_B <= dim 'H[H]_Bbig)%N.
Hypothesis dimAC_Bbig : (dim 'H[H]_(A :|: C0) <= dim 'H[H]_Bbig)%N.
(* Ambient support room for the max-side isometry/support optimizer. *)
Variable Bbig_supp : {set L}.
Hypothesis disA_Bbig_supp : [disjoint A & Bbig_supp].
Hypothesis disB_Bbig_supp : [disjoint B & Bbig_supp].
Hypothesis disBbig_Bbig_supp : [disjoint Bbig & Bbig_supp].
Hypothesis dimABbig_Bbig_supp :
  (dim 'H[H]_(A :|: Bbig) <= dim 'H[H]_Bbig_supp)%N.
(* Ambient purifier/copy labels threaded to minmax_dual and smoothing
   support; they are proof infrastructure, not extra state systems. *)
Variables (Cp Cpp : {set L}).
Hypotheses (disA_Cp : [disjoint A & Cp])
           (disA_Cpp : [disjoint A & Cpp])
           (disB_Cp : [disjoint B & Cp])
           (disB_Cpp : [disjoint B & Cpp])
           (disC_Cp : [disjoint C0 & Cp])
           (disC_Cpp : [disjoint C0 & Cpp])
           (disCbig_Cp : [disjoint Cbig & Cp])
           (disCbig_Cpp : [disjoint Cbig & Cpp])
           (disBbig_Cp : [disjoint Bbig & Cp])
           (disBbig_Cpp : [disjoint Bbig & Cpp])
           (disBbig_supp_Cp : [disjoint Bbig_supp & Cp])
           (disBbig_supp_Cpp : [disjoint Bbig_supp & Cpp])
           (disCp_Cpp : [disjoint Cp & Cpp]).
Hypothesis dimA_Cp : dim 'H[H]_A = dim 'H[H]_Cp.
Hypothesis dimC_Cp_Cpp :
  (dim 'H[H]_C0 * dim 'H[H]_Cp <= dim 'H[H]_Cpp)%N.
Hypothesis dimCbig_Cp_Cpp :
  (dim 'H[H]_Cbig * dim 'H[H]_Cp <= dim 'H[H]_Cpp)%N.
Hypothesis dimBbig_supp_Cp_Cpp :
  (dim 'H[H]_Bbig_supp * dim 'H[H]_Cp <= dim 'H[H]_Cpp)%N.
Hypothesis dimB_Cpp : (dim 'H[H]_B <= dim 'H[H]_Cpp)%N.
Hypothesis dimBbig_Cpp : (dim 'H[H]_Bbig <= dim 'H[H]_Cpp)%N.

Notation S_ABC := (A :|: B :|: C0).

(* Smooth min/max duality in labelled form. Consumers that work through    *)
(* non-smooth min/max duality can use that route directly; this theorem    *)
(* provides the full smooth labelled statement.                            *)
Lemma smooth_dual (eps : R) (rhoABC : 'F[H]_S_ABC) :
  rhoABC \is denlf ->
  \Rank rhoABC = 1%N ->
  0 <= eps < Num.sqrt (@complex.Re R (\Tr rhoABC)) ->
  smooth_hmaxE B eps
    (@ptrace_cast3C R L H A B C0 disAC disBC rhoABC) =
  oppe (smooth_hminE C0 eps
    (@ptrace_cast3B R L H A B C0 disAB disBC rhoABC)).
Proof.
  move=> Hrho_den Hrho_rank Heps_pair.
  have Prho : rhoABC \is psdlf := denlf_psd Hrho_den.
  have Hrho_tr : @complex.Re R (\Tr rhoABC) <= 1.
  { have Hreal : \Tr rhoABC \is Num.real := ger0_real (psdlf_trlf Prho).
    by move: (denlf_trlf Hrho_den); rewrite -(RRe_real Hreal) lecR. }
  move/andP: Heps_pair => [Heps Heps_lt_rho].
  pose rhoAB : 'F[H]_(A :|: B) :=
    @ptrace_cast3C R L H A B C0 disAC disBC rhoABC.
  pose rhoAC : 'F[H]_(A :|: C0) :=
    @ptrace_cast3B R L H A B C0 disAB disBC rhoABC.
  have PrhoAB : rhoAB \is psdlf.
  { rewrite /rhoAB /ptrace_cast3C.
    exact: ptrace_cast_gen_psdlf Prho. }
  have PrhoAC : rhoAC \is psdlf.
  { rewrite /rhoAC /ptrace_cast3B.
    exact: ptrace_cast_gen_psdlf Prho. }
  have trlf_ptrace3C (f : 'F[H]_S_ABC) :
      \Tr (@ptrace_cast3C R L H A B C0 disAC disBC f) = \Tr f.
  { rewrite /ptrace_cast3C /ptrace_cast_gen castlf_trlfE.
    have /cptpP [_ /tpmapP Htp] := @ptraceso_qc R L H C0 S_ABC.
    exact: Htp. }
  have trlf_ptrace3B (f : 'F[H]_S_ABC) :
      \Tr (@ptrace_cast3B R L H A B C0 disAB disBC f) = \Tr f.
  { rewrite /ptrace_cast3B /ptrace_cast_gen castlf_trlfE.
    have /cptpP [_ /tpmapP Htp] := @ptraceso_qc R L H B S_ABC.
    exact: Htp. }
  have HrhoAB_tr : @complex.Re R (\Tr rhoAB) <= 1
    by rewrite /rhoAB trlf_ptrace3C.
  have HrhoAC_tr : @complex.Re R (\Tr rhoAC) <= 1
    by rewrite /rhoAC trlf_ptrace3B.
  have Heps_lt_AB : eps < Num.sqrt (@complex.Re R (\Tr rhoAB))
    by rewrite /rhoAB trlf_ptrace3C.
  have Heps_lt_AC : eps < Num.sqrt (@complex.Re R (\Tr rhoAC))
    by rewrite /rhoAC trlf_ptrace3B.
  have disAB_C : [disjoint A :|: B & C0].
  { by rewrite disjointUX disAC disBC. }
  have HptC_eq :
      rhoAB = ptrace_cast disAB_C rhoABC.
  { rewrite /rhoAB /ptrace_cast3C /ptrace_cast /ptrace_cast_gen.
    have Hdu : setDU3_C disAC disBC = setDU_r disAB_C
      := eq_irrelevance _ _.
    by rewrite Hdu. }
  have HrhoAB_mx :
      h2mx rhoAB =
      ptrace2 ((@tenv_mxU R L H (A :|: B) C0)^*t *m h2mx rhoABC *m
               (@tenv_mxU R L H (A :|: B) C0)).
  { by rewrite HptC_eq (h2mx_ptrace_cast_ptrace2 disAB_C rhoABC). }
  set eqS := setUC_swap3 A B C0 : A :|: B :|: C0 = A :|: C0 :|: B.
  have disAC_B : [disjoint A :|: C0 & B].
  { have disCB : [disjoint C0 & B] by rewrite disjoint_sym.
    by rewrite disjointUX disAB disCB. }
  have HptB_recast :
      rhoAC = ptrace_cast disAC_B (castlf (eqS, eqS) rhoABC).
  { rewrite /rhoAC /ptrace_cast3B /ptrace_cast /ptrace_cast_gen.
    have eq_res : (A :|: B :|: C0) :\: B =
        (A :|: C0 :|: B) :\: B
      by rewrite eqS.
    rewrite (ptracelf_castlf_eq eqS eq_res).
    rewrite castlf_comp.
    by congr (castlf (_, _) _); exact: eq_irrelevance. }
  have HrhoAC_mx :
      h2mx rhoAC =
      ptrace2 ((@tenv_mxU R L H (A :|: C0) B)^*t *m
               h2mx (castlf (eqS, eqS) rhoABC) *m
               (@tenv_mxU R L H (A :|: C0) B)).
  { by rewrite HptB_recast (h2mx_ptrace_cast_ptrace2 disAC_B). }
  pose UAB_C := @tenv_mxU R L H (A :|: B) C0.
  pose rhoAB_C_mx := UAB_C^*t *m h2mx rhoABC *m UAB_C.
  have HUAB_C : UAB_C \is unitarymx := tenv_mxU_unitarymx _ _.
  have HrhoABC_mx_psd : h2mx rhoABC \is psdmx by move: Prho; rewrite qualifE.
  have HrhoAB_C_psd : rhoAB_C_mx \is psdmx.
  { rewrite /rhoAB_C_mx -[UAB_C in _ *m _ *m UAB_C]adjmxK.
    exact: psdmx_bimap_closed_gen HrhoABC_mx_psd. }
  have HrhoAB_C_rank : (\rank rhoAB_C_mx <= 1)%N.
  { rewrite /rhoAB_C_mx (mxrank_mulmxU _ HUAB_C) (mxrank_mulUCmx _ HUAB_C).
    by rewrite -/(lfrank rhoABC) Hrho_rank. }
  have HrhoAB_C_tr : @complex.Re R (\tr rhoAB_C_mx) <= 1.
  { rewrite /rhoAB_C_mx mxtrace_mulC mulmxA (unitarymxK HUAB_C) mul1mx.
    by move: Hrho_tr; rewrite /lftrace. }
  have HrhoAB_C_ptr : ptrace2 rhoAB_C_mx = h2mx rhoAB
    by rewrite /rhoAB_C_mx -HrhoAB_mx.
  have [VC0_Cbig HVC0_Cbig_iso] :=
    @labelled_isolf_via_dim_le R L H C0 Cbig dimC_Cbig.
  pose WC0_Cbig := h2mx (VC0_Cbig : 'F[H]_(C0, Cbig)).
  have HWC0_Cbig_iso : WC0_Cbig^*t *m WC0_Cbig = 1%:M.
  { move: HVC0_Cbig_iso => /isolfP Hiso.
    have := f_equal h2mx Hiso.
    by rewrite h2mx_comp h2mx_adj h2mx1. }
  pose Cbig_embed :=
    (1%:M : 'M[C]_(dim 'H[H]_(A :|: B))) *t WC0_Cbig.
  pose rhoAB_Cbig_mx := Cbig_embed *m rhoAB_C_mx *m Cbig_embed^*t.
  have HCbig_embed_iso : Cbig_embed^*t *m Cbig_embed = 1%:M.
  { rewrite /Cbig_embed adjmx_tens adjmx1 tensmx_mul mul1mx.
    by rewrite HWC0_Cbig_iso tensmx11. }
  have HrhoAB_Cbig_psd : rhoAB_Cbig_mx \is psdmx.
  { rewrite /rhoAB_Cbig_mx.
    exact: psdmx_bimap_closed_gen HrhoAB_C_psd. }
  have HrhoAB_Cbig_rank : (\rank rhoAB_Cbig_mx <= 1)%N.
  { rewrite /rhoAB_Cbig_mx.
    exact: leq_trans (mxrankM_maxl _ _)
      (leq_trans (mxrankM_maxr _ _) HrhoAB_C_rank). }
  have HrhoAB_Cbig_tr : @complex.Re R (\tr rhoAB_Cbig_mx) <= 1.
  { rewrite /rhoAB_Cbig_mx mxtrace_mulC mulmxA HCbig_embed_iso mul1mx.
    exact: HrhoAB_C_tr. }
  have HrhoAB_Cbig_ptr : ptrace2 rhoAB_Cbig_mx = h2mx rhoAB.
  { rewrite /rhoAB_Cbig_mx /Cbig_embed.
    by rewrite (@ptrace2_conj_tens_right_iso R
      (dim 'H[H]_(A :|: B)) (dim 'H[H]_C0) (dim 'H[H]_Cbig)
      WC0_Cbig rhoAB_C_mx HWC0_Cbig_iso) HrhoAB_C_ptr. }
  have Hge_uhlmann_lift :
      forall tauAB : 'F[H]_(A :|: B),
      eps_ball eps rhoAB tauAB ->
      exists tauAB_Cbig_mx : 'M[C]_(dim 'H[H]_(A :|: B) * dim 'H[H]_Cbig),
        [/\ tauAB_Cbig_mx \is psdmx,
            (\rank tauAB_Cbig_mx <= 1)%N,
            @complex.Re R (\tr tauAB_Cbig_mx) <= 1,
            ptrace2 tauAB_Cbig_mx = h2mx tauAB &
            gfidelity rhoAB_Cbig_mx tauAB_Cbig_mx =
              gfidelity (h2mx rhoAB) (h2mx tauAB)].
  { move=> tauAB HtauAB_ball.
    have HtauAB_psd : tauAB \is psdlf := eps_ball_psdlf HtauAB_ball.
    have HtauAB_mx_psd : h2mx tauAB \is psdmx
      by move: HtauAB_psd; rewrite qualifE.
    have HtauAB_tr : @complex.Re R (\tr (h2mx tauAB)) <= 1.
    { by move: (eps_ball_trlf HtauAB_ball); rewrite /lftrace. }
    have HtauAB_rank :
        (\rank (h2mx tauAB) <= dim 'H[H]_Cbig)%N.
    { exact: leq_trans (rank_leq_row _) dimAB_Cbig. }
    have [tauAB_Cbig_mx HtauAB_Cbig] :=
      @subnorm_matrix_uhlmann R
        (dim 'H[H]_(A :|: B)) (dim 'H[H]_Cbig)
        rhoAB_Cbig_mx (h2mx rhoAB) (h2mx tauAB)
        HrhoAB_Cbig_psd HrhoAB_Cbig_rank HrhoAB_Cbig_tr
        HrhoAB_Cbig_ptr HtauAB_mx_psd HtauAB_tr HtauAB_rank.
    by exists tauAB_Cbig_mx. }
  have disAB_Cbig : [disjoint A :|: B & Cbig].
  { by rewrite disjointUX disA_Cbig disB_Cbig. }
  have HptC_eq_Cbig :
      forall X : 'F[H]_(A :|: B :|: Cbig),
      @ptrace_cast3C R L H A B Cbig disA_Cbig disB_Cbig X =
      ptrace_cast disAB_Cbig X.
  { move=> X.
    rewrite /ptrace_cast3C /ptrace_cast /ptrace_cast_gen.
    have Hdu : setDU3_C disA_Cbig disB_Cbig = setDU_r disAB_Cbig
      := eq_irrelevance _ _.
    by rewrite Hdu. }
  pose UAB_Cbig := @tenv_mxU R L H (A :|: B) Cbig.
  have HUAB_Cbig : UAB_Cbig \is unitarymx := tenv_mxU_unitarymx _ _.
  have HUAB_Cbig_adj : UAB_Cbig^*t \is unitarymx
    := tenv_mxU_adj_unitarymx disAB_Cbig.
  have HUAB_CbigK : UAB_Cbig^*t *m UAB_Cbig = 1%:M.
  { by have := unitarymxK HUAB_Cbig_adj; rewrite adjmxK. }
  pose rhoABCbig_lf : 'F[H]_(A :|: B :|: Cbig) :=
    mx2h (UAB_Cbig *m rhoAB_Cbig_mx *m UAB_Cbig^*t).
  have HrhoABCbig_h2mx : h2mx rhoABCbig_lf =
      UAB_Cbig *m rhoAB_Cbig_mx *m UAB_Cbig^*t
    by rewrite /rhoABCbig_lf mx2hK.
  have PrhoABCbig_lf : rhoABCbig_lf \is psdlf.
  { rewrite qualifE HrhoABCbig_h2mx.
    exact: psdmx_bimap_closed_gen HrhoAB_Cbig_psd. }
  have HrhoABCbig_rank : (\Rank rhoABCbig_lf <= 1)%N.
  { rewrite /lfrank HrhoABCbig_h2mx.
    rewrite (mxrank_mulmxU _ HUAB_Cbig_adj).
    rewrite -[UAB_Cbig]adjmxK (mxrank_mulUCmx _ HUAB_Cbig_adj).
    exact: HrhoAB_Cbig_rank. }
  have HrhoABCbig_tr : @complex.Re R (\Tr rhoABCbig_lf) <= 1.
  { rewrite /lftrace HrhoABCbig_h2mx mxtrace_mulC mulmxA.
    by rewrite HUAB_CbigK mul1mx. }
  have HrhoABCbig_marg :
      ptrace_cast3C disA_Cbig disB_Cbig rhoABCbig_lf = rhoAB.
  { apply/h2mx_inj.
    rewrite HptC_eq_Cbig (h2mx_ptrace_cast_ptrace2 disAB_Cbig).
    have -> :
        UAB_Cbig^*t *m h2mx rhoABCbig_lf *m UAB_Cbig = rhoAB_Cbig_mx.
    { rewrite HrhoABCbig_h2mx.
      transitivity
        ((UAB_Cbig^*t *m UAB_Cbig) *m rhoAB_Cbig_mx *m
          (UAB_Cbig^*t *m UAB_Cbig)).
      - by rewrite !mulmxA.
      - by rewrite HUAB_CbigK mul1mx mulmx1. }
    exact: HrhoAB_Cbig_ptr. }
  have Hge_labelled_lift :
      forall tauAB : 'F[H]_(A :|: B),
      eps_ball eps rhoAB tauAB ->
      exists tauABCbig : 'F[H]_(A :|: B :|: Cbig),
        [/\ tauABCbig \is psdlf,
            (\Rank tauABCbig <= 1)%N,
            @complex.Re R (\Tr tauABCbig) <= 1,
            @ptrace_cast3C R L H A B Cbig
              disA_Cbig disB_Cbig tauABCbig = tauAB &
            gfidelity rhoAB_Cbig_mx
              (UAB_Cbig^*t *m h2mx tauABCbig *m UAB_Cbig) =
              gfidelity (h2mx rhoAB) (h2mx tauAB)].
  { move=> tauAB HtauAB_ball.
    have [tauAB_Cbig_mx HtauAB_Cbig] :=
      Hge_uhlmann_lift tauAB HtauAB_ball.
    case: HtauAB_Cbig => Ptau_mx Htau_rank Htau_tr Htau_ptr Htau_fid.
    pose tauABCbig : 'F[H]_(A :|: B :|: Cbig) :=
      mx2h (UAB_Cbig *m tauAB_Cbig_mx *m UAB_Cbig^*t).
    have Htau_h2mx : h2mx tauABCbig =
        UAB_Cbig *m tauAB_Cbig_mx *m UAB_Cbig^*t
      by rewrite /tauABCbig mx2hK.
    have Ptau_lf : tauABCbig \is psdlf.
    { rewrite qualifE Htau_h2mx.
      exact: psdmx_bimap_closed_gen Ptau_mx. }
    have Htau_lfrank : (\Rank tauABCbig <= 1)%N.
    { rewrite /lfrank Htau_h2mx.
      rewrite (mxrank_mulmxU _ HUAB_Cbig_adj).
      rewrite -[UAB_Cbig]adjmxK (mxrank_mulUCmx _ HUAB_Cbig_adj).
      exact: Htau_rank. }
    have Htau_lftr : @complex.Re R (\Tr tauABCbig) <= 1.
    { rewrite /lftrace Htau_h2mx mxtrace_mulC mulmxA.
      by rewrite HUAB_CbigK mul1mx. }
    have Htau_marg : ptrace_cast3C disA_Cbig disB_Cbig tauABCbig = tauAB.
    { apply/h2mx_inj.
      rewrite HptC_eq_Cbig (h2mx_ptrace_cast_ptrace2 disAB_Cbig).
      rewrite Htau_h2mx -/UAB_Cbig.
      by rewrite !mulmxA HUAB_CbigK mul1mx -mulmxA HUAB_CbigK mulmx1. }
    exists tauABCbig.
    split.
    - exact: Ptau_lf.
    - exact: Htau_lfrank.
    - exact: Htau_lftr.
    - exact: Htau_marg.
    by rewrite Htau_h2mx !mulmxA HUAB_CbigK mul1mx -mulmxA
      HUAB_CbigK mulmx1. }
  have Hge_labelled_lift_rank1 :
      forall tauAB : 'F[H]_(A :|: B),
      eps_ball eps rhoAB tauAB -> tauAB != 0 ->
      exists tauABCbig : 'F[H]_(A :|: B :|: Cbig),
        [/\ tauABCbig \is psdlf,
            \Rank tauABCbig = 1%N,
            @complex.Re R (\Tr tauABCbig) <= 1,
            @ptrace_cast3C R L H A B Cbig
              disA_Cbig disB_Cbig tauABCbig = tauAB &
            gfidelity rhoAB_Cbig_mx
              (UAB_Cbig^*t *m h2mx tauABCbig *m UAB_Cbig) =
              gfidelity (h2mx rhoAB) (h2mx tauAB)].
  { move=> tauAB HtauAB_ball HtauAB_ne0.
    have [tauABCbig Hlift] :=
      Hge_labelled_lift tauAB HtauAB_ball.
    case: Hlift => Ptau Hrank_le Htr_le Hmarg Hfid.
    have HtauABCbig_ne0 : tauABCbig != 0.
    { apply/eqP=> H0.
      move: Hmarg.
      rewrite H0 /ptrace_cast3C /ptrace_cast_gen raddf0 /= raddf0.
      by move=> Htau0; move/eqP: HtauAB_ne0; rewrite -Htau0. }
    have Hrank_gt0 : (0 < \Rank tauABCbig)%N.
    { rewrite lt0n /lfrank mxrank_eq0.
      apply/eqP=> Hmx0.
      have H0 : tauABCbig = 0 by apply/h2mx_inj; rewrite Hmx0 h2mx0.
      by move/eqP: HtauABCbig_ne0; apply. }
    have Hrank_eq1 : \Rank tauABCbig = 1%N.
    { by apply/eqP; rewrite eqn_leq Hrank_le Hrank_gt0. }
    by exists tauABCbig; split=> //. }
  have trlf_ptrace3C_Cbig (f : 'F[H]_(A :|: B :|: Cbig)) :
      \Tr (@ptrace_cast3C R L H A B Cbig disA_Cbig disB_Cbig f) =
      \Tr f.
  { rewrite /ptrace_cast3C /ptrace_cast_gen castlf_trlfE.
    have /cptpP [_ /tpmapP Htp] :=
      @ptraceso_qc R L H Cbig (A :|: B :|: Cbig).
    exact: Htp. }
  have trlf_ptrace3B_Cbig (f : 'F[H]_(A :|: B :|: Cbig)) :
      \Tr (@ptrace_cast3B R L H A B Cbig disAB disB_Cbig f) =
      \Tr f.
  { rewrite /ptrace_cast3B /ptrace_cast_gen castlf_trlfE.
    have /cptpP [_ /tpmapP Htp] :=
      @ptraceso_qc R L H B (A :|: B :|: Cbig).
    exact: Htp. }
  have Hge_nonzero_dual :
      forall tauAB : 'F[H]_(A :|: B),
      eps_ball eps rhoAB tauAB -> tauAB != 0 ->
      exists tauABCbig : 'F[H]_(A :|: B :|: Cbig),
        [/\ tauABCbig \is psdlf,
            @complex.Re R (\Tr tauABCbig) <= 1,
            @ptrace_cast3C R L H A B Cbig
              disA_Cbig disB_Cbig tauABCbig = tauAB,
            hmax B tauAB =
              - hmin Cbig
                (@ptrace_cast3B R L H A B Cbig
                  disAB disB_Cbig tauABCbig) &
            gfidelity rhoAB_Cbig_mx
              (UAB_Cbig^*t *m h2mx tauABCbig *m UAB_Cbig) =
              gfidelity (h2mx rhoAB) (h2mx tauAB)].
  { move=> tauAB HtauAB_ball HtauAB_ne0.
    have [tauABCbig Hlift] :=
      Hge_labelled_lift_rank1 tauAB HtauAB_ball HtauAB_ne0.
    case: Hlift => Ptau Hrank Htr Hmarg Hfid.
    have Htau_den : tauABCbig \is denlf.
    { apply/denlfP; split=> //.
      have Hreal : \Tr tauABCbig \is Num.real :=
        ger0_real (psdlf_trlf Ptau).
      by rewrite -(RRe_real Hreal) lecR. }
    have Heps_pair_AB : 0 <= eps < Num.sqrt (@complex.Re R (\Tr rhoAB))
      by rewrite Heps Heps_lt_AB.
    have HptC_psd_dual :
        ptrace_cast3C disA_Cbig disB_Cbig tauABCbig \is psdlf.
    { rewrite /ptrace_cast3C; exact: ptrace_cast_gen_psdlf Ptau. }
    have HptC_tr_dual :
        @complex.Re R
          (\Tr (ptrace_cast3C disA_Cbig disB_Cbig tauABCbig)) <= 1.
    { by rewrite Hmarg; exact: eps_ball_trlf HtauAB_ball. }
    have HptC_pos_dual :
        0 < @complex.Re R
          (\Tr (ptrace_cast3C disA_Cbig disB_Cbig tauABCbig)).
    { by rewrite Hmarg;
      exact: eps_ball_trace_pos PrhoAB HrhoAB_tr Heps_pair_AB HtauAB_ball. }
    pose tauACbig :=
      @ptrace_cast3B R L H A B Cbig disAB disB_Cbig tauABCbig.
    have PtauACbig : tauACbig \is psdlf.
    { rewrite /tauACbig /ptrace_cast3B.
      exact: ptrace_cast_gen_psdlf Ptau. }
    have HtauACbig_tr : @complex.Re R (\Tr tauACbig) <= 1
      by rewrite /tauACbig trlf_ptrace3B_Cbig.
    have HtauABCbig_pos : 0 < @complex.Re R (\Tr tauABCbig)
      by move: HptC_pos_dual; rewrite trlf_ptrace3C_Cbig.
    have HtauACbig_pos : 0 < @complex.Re R (\Tr tauACbig)
      by rewrite /tauACbig trlf_ptrace3B_Cbig.
    have Hphi_tauACbig_pos : 0 < phi_min Cbig tauACbig
      := @phi_min_pos_trace R L H (A :|: Cbig) Cbig
           tauACbig PtauACbig HtauACbig_tr HtauACbig_pos.
    have Hhmax_fin :
        hmaxE B (ptrace_cast3C disA_Cbig disB_Cbig tauABCbig) =
        (hmax B (ptrace_cast3C disA_Cbig disB_Cbig tauABCbig))%:E
      := @hmaxE_EFin R L H (A :|: B) B
           (ptrace_cast3C disA_Cbig disB_Cbig tauABCbig)
           HptC_psd_dual HptC_tr_dual HptC_pos_dual.
    have Hhmin_fin :
        hminE Cbig tauACbig = (hmin Cbig tauACbig)%:E
      := @hminE_EFin R L H (A :|: Cbig) Cbig
           tauACbig Hphi_tauACbig_pos.
    have Hdual :
        hmax B (ptrace_cast3C disA_Cbig disB_Cbig tauABCbig) =
        - hmin Cbig tauACbig.
    { have HdualE := @minmax_dual R L H A B Cbig
          disAB disA_Cbig disB_Cbig Cp Cpp
          disA_Cp disA_Cpp disB_Cp disB_Cpp disCp_Cpp
          dimA_Cp dimCbig_Cp_Cpp dimB_Cpp
          tauABCbig Htau_den Hrank.
      move: HdualE.
      rewrite Hhmax_fin Hhmin_fin EFinN.
      by case. }
    rewrite Hmarg in Hdual.
    by exists tauABCbig; split=> //. }
  have Hge_full_ball :
      forall tauAB : 'F[H]_(A :|: B),
      eps_ball eps rhoAB tauAB -> tauAB != 0 ->
      exists tauABCbig : 'F[H]_(A :|: B :|: Cbig),
        [/\ @ptrace_cast3C R L H A B Cbig
              disA_Cbig disB_Cbig tauABCbig = tauAB,
            hmax B tauAB =
              - hmin Cbig
                (@ptrace_cast3B R L H A B Cbig
                  disAB disB_Cbig tauABCbig) &
            eps_ball eps rhoABCbig_lf tauABCbig].
  { move=> tauAB HtauAB_ball HtauAB_ne0.
    have [tauABCbig Hdual] :=
      Hge_nonzero_dual tauAB HtauAB_ball HtauAB_ne0.
    case: Hdual => Ptau Htr Hmarg Hhmax Hfid.
    have Ptau_mx : h2mx tauABCbig \is psdmx by move: Ptau; rewrite qualifE.
    have Prho_big_mx : h2mx rhoABCbig_lf \is psdmx
      by move: PrhoABCbig_lf; rewrite qualifE.
    have HtauAB_psd : tauAB \is psdlf := eps_ball_psdlf HtauAB_ball.
    have HtauAB_mx_psd : h2mx tauAB \is psdmx
      by move: HtauAB_psd; rewrite qualifE.
    have HrhoAB_mx_psd : h2mx rhoAB \is psdmx
      by move: PrhoAB; rewrite qualifE.
    have Hrho_prod :
        UAB_Cbig^*t *m h2mx rhoABCbig_lf *m UAB_Cbig = rhoAB_Cbig_mx.
    { rewrite HrhoABCbig_h2mx.
      transitivity
        ((UAB_Cbig^*t *m UAB_Cbig) *m rhoAB_Cbig_mx *m
          (UAB_Cbig^*t *m UAB_Cbig)).
      - by rewrite !mulmxA.
      - by rewrite HUAB_CbigK mul1mx mulmx1. }
    pose tau_prod := UAB_Cbig^*t *m h2mx tauABCbig *m UAB_Cbig.
    have Ptau_prod : tau_prod \is psdmx.
    { rewrite /tau_prod -[UAB_Cbig in _ *m _ *m UAB_Cbig]adjmxK.
      exact: psdmx_bimap_closed_gen Ptau_mx. }
    have Hgf_full :
        gfid tauABCbig rhoABCbig_lf =
        gfid tauAB rhoAB.
    { rewrite /gfid.
      rewrite (gfid_tenv_mxU_conj_eq_mx disAB_Cbig Ptau_mx Prho_big_mx).
      rewrite Hrho_prod -/tau_prod.
      rewrite (gfid_sym_mx Ptau_prod HrhoAB_Cbig_psd) Hfid.
      by rewrite (gfid_sym_mx HtauAB_mx_psd HrhoAB_mx_psd). }
      have Hpd_full : pur_dist tauABCbig rhoABCbig_lf <= eps.
      { move: HtauAB_ball => /andP [/andP [_ _] HpdAB].
        by rewrite /pur_dist Hgf_full. }
      have HtauABCbig_pos : 0 < @complex.Re R (\Tr tauABCbig).
      {
        have HptC_pos :
            0 < @complex.Re R
              (\Tr (ptrace_cast3C disA_Cbig disB_Cbig tauABCbig)).
        { by rewrite Hmarg; exact: eps_ball_trlf_gt0 HtauAB_ball. }
        by move: HptC_pos; rewrite trlf_ptrace3C_Cbig.
      }
      exists tauABCbig; split=> //.
      by rewrite /eps_ball Ptau HtauABCbig_pos Htr Hpd_full. }
  have Hh2mx_castlf_gen :
      forall (S S' : {set L}) (eqSS' : S = S') (f : 'F[H]_S),
      h2mx (castlf (eqSS', eqSS') f) =
      castmx (f_equal (fun T => dim 'H[H]_T) eqSS',
              f_equal (fun T => dim 'H[H]_T) eqSS') (h2mx f).
  { move=> S S' eqSS' f.
    case: S' / eqSS' in f *.
    by rewrite castlf_id castmx_id. }
  set eqS_Cbig := setUC_swap3 A B Cbig
    : A :|: B :|: Cbig = A :|: Cbig :|: B.
  have disACbig_B : [disjoint A :|: Cbig & B].
  { have disCbig_B : [disjoint Cbig & B] by rewrite disjoint_sym.
    by rewrite disjointUX disAB disCbig_B. }
  have HptB_recast_Cbig :
      forall X : 'F[H]_(A :|: B :|: Cbig),
      @ptrace_cast3B R L H A B Cbig disAB disB_Cbig X =
      ptrace_cast disACbig_B (castlf (eqS_Cbig, eqS_Cbig) X).
  { move=> X.
    rewrite /ptrace_cast3B /ptrace_cast /ptrace_cast_gen.
    have eq_res : (A :|: B :|: Cbig) :\: B =
        (A :|: Cbig :|: B) :\: B
      by rewrite eqS_Cbig.
    rewrite (ptracelf_castlf_eq eqS_Cbig eq_res).
    rewrite castlf_comp.
    by congr (castlf (_, _) _); exact: eq_irrelevance. }
  have Hge_ACbig_ball :
      forall tauAB : 'F[H]_(A :|: B),
      eps_ball eps rhoAB tauAB -> tauAB != 0 ->
      exists tauABCbig : 'F[H]_(A :|: B :|: Cbig),
        [/\ @ptrace_cast3C R L H A B Cbig
              disA_Cbig disB_Cbig tauABCbig = tauAB,
            hmax B tauAB =
              - hmin Cbig
                (@ptrace_cast3B R L H A B Cbig
                  disAB disB_Cbig tauABCbig) &
            eps_ball eps
              (@ptrace_cast3B R L H A B Cbig
                disAB disB_Cbig rhoABCbig_lf)
              (@ptrace_cast3B R L H A B Cbig
                disAB disB_Cbig tauABCbig)].
  { move=> tauAB HtauAB_ball HtauAB_ne0.
    have [tauABCbig Hfull] :=
      Hge_full_ball tauAB HtauAB_ball HtauAB_ne0.
    case: Hfull => Hmarg Hhmax Hball_full.
    have Ptau_full : tauABCbig \is psdlf := eps_ball_psdlf Hball_full.
    have Htr_full : @complex.Re R (\Tr tauABCbig) <= 1
      := eps_ball_trlf Hball_full.
    have Hpd_full : pur_dist tauABCbig rhoABCbig_lf <= eps
      by move: Hball_full; rewrite /eps_ball => /andP [/andP [_ _] Hpd].
    have Ptau_ACbig :
        @ptrace_cast3B R L H A B Cbig disAB disB_Cbig
          tauABCbig \is psdlf.
    { rewrite /ptrace_cast3B; exact: ptrace_cast_gen_psdlf Ptau_full. }
      have Htr_ACbig :
          @complex.Re R
            (\Tr (@ptrace_cast3B R L H A B Cbig
              disAB disB_Cbig tauABCbig)) <= 1
        by rewrite trlf_ptrace3B_Cbig.
      have Hpos_ACbig :
          0 < @complex.Re R
            (\Tr (@ptrace_cast3B R L H A B Cbig
              disAB disB_Cbig tauABCbig))
        by rewrite trlf_ptrace3B_Cbig; exact: eps_ball_trlf_gt0 Hball_full.
    have Ptau_cast : castlf (eqS_Cbig, eqS_Cbig) tauABCbig \is psdlf
      by rewrite castlf_psdlfE.
    have Prho_cast : castlf (eqS_Cbig, eqS_Cbig) rhoABCbig_lf \is psdlf
      by rewrite castlf_psdlfE.
    have Hpd_cast :
        pur_dist (castlf (eqS_Cbig, eqS_Cbig) tauABCbig)
          (castlf (eqS_Cbig, eqS_Cbig) rhoABCbig_lf) =
        pur_dist tauABCbig rhoABCbig_lf.
    { rewrite /pur_dist /gfid !Hh2mx_castlf_gen.
      by rewrite gfid_cast_mx. }
    have Hpd_mono := @pd_mono_ptrace_cast
      R L H (A :|: Cbig) B disACbig_B
      (castlf (eqS_Cbig, eqS_Cbig) rhoABCbig_lf)
      (castlf (eqS_Cbig, eqS_Cbig) tauABCbig)
      Ptau_cast Prho_cast.
    rewrite -!HptB_recast_Cbig Hpd_cast in Hpd_mono.
      have Hpd_ACbig :=
        le_trans Hpd_mono Hpd_full.
      exists tauABCbig; split=> //.
      by rewrite /eps_ball Ptau_ACbig Hpos_ACbig Htr_ACbig Hpd_ACbig. }
  pose UAC_B := @tenv_mxU R L H (A :|: C0) B.
  pose rhoABC_acb := castlf (eqS, eqS) rhoABC.
  pose rhoAC_B_mx := UAC_B^*t *m h2mx rhoABC_acb *m UAC_B.
  have HUAC_B : UAC_B \is unitarymx := tenv_mxU_unitarymx _ _.
  have PrhoABC_acb : rhoABC_acb \is psdlf by rewrite /rhoABC_acb castlf_psdlfE.
  have HrhoABC_acb_mx_psd : h2mx rhoABC_acb \is psdmx
    by move: PrhoABC_acb; rewrite qualifE.
  have Hh2mx_castlf :
      h2mx rhoABC_acb =
      castmx (f_equal (fun T => dim 'H[H]_T) eqS,
              f_equal (fun T => dim 'H[H]_T) eqS) (h2mx rhoABC)
    by exact: Hh2mx_castlf_gen.
  have HrhoAC_B_psd : rhoAC_B_mx \is psdmx.
  { rewrite /rhoAC_B_mx -[UAC_B in _ *m _ *m UAC_B]adjmxK.
    exact: psdmx_bimap_closed_gen HrhoABC_acb_mx_psd. }
  have HrhoAC_B_rank : (\rank rhoAC_B_mx <= 1)%N.
  { rewrite /rhoAC_B_mx (mxrank_mulmxU _ HUAC_B) (mxrank_mulUCmx _ HUAC_B).
    rewrite Hh2mx_castlf mxrank_cast.
    by rewrite -/(lfrank rhoABC) Hrho_rank. }
  have HrhoAC_B_tr : @complex.Re R (\tr rhoAC_B_mx) <= 1.
  { rewrite /rhoAC_B_mx mxtrace_mulC mulmxA (unitarymxK HUAC_B) mul1mx.
    by rewrite Hh2mx_castlf mxtrace_castmx_sq. }
  have HrhoAC_B_ptr : ptrace2 rhoAC_B_mx = h2mx rhoAC
    by rewrite /rhoAC_B_mx -HrhoAC_mx.
  have [VB_Bbig HVB_Bbig_iso] :=
    @labelled_isolf_via_dim_le R L H B Bbig dimB_Bbig.
  pose WB_Bbig := h2mx (VB_Bbig : 'F[H]_(B, Bbig)).
  have HWB_Bbig_iso : WB_Bbig^*t *m WB_Bbig = 1%:M.
  { move: HVB_Bbig_iso => /isolfP Hiso.
    have := f_equal h2mx Hiso.
    by rewrite h2mx_comp h2mx_adj h2mx1. }
  pose Bbig_embed :=
    (1%:M : 'M[C]_(dim 'H[H]_(A :|: C0))) *t WB_Bbig.
  pose rhoAC_Bbig_mx := Bbig_embed *m rhoAC_B_mx *m Bbig_embed^*t.
  have HBbig_embed_iso : Bbig_embed^*t *m Bbig_embed = 1%:M.
  { rewrite /Bbig_embed adjmx_tens adjmx1 tensmx_mul mul1mx.
    by rewrite HWB_Bbig_iso tensmx11. }
  have HrhoAC_Bbig_psd : rhoAC_Bbig_mx \is psdmx.
  { rewrite /rhoAC_Bbig_mx.
    exact: psdmx_bimap_closed_gen HrhoAC_B_psd. }
  have HrhoAC_Bbig_rank : (\rank rhoAC_Bbig_mx <= 1)%N.
  { rewrite /rhoAC_Bbig_mx.
    exact: leq_trans (mxrankM_maxl _ _)
      (leq_trans (mxrankM_maxr _ _) HrhoAC_B_rank). }
  have HrhoAC_Bbig_tr : @complex.Re R (\tr rhoAC_Bbig_mx) <= 1.
  { rewrite /rhoAC_Bbig_mx mxtrace_mulC mulmxA HBbig_embed_iso mul1mx.
    exact: HrhoAC_B_tr. }
  have HrhoAC_Bbig_ptr : ptrace2 rhoAC_Bbig_mx = h2mx rhoAC.
  { rewrite /rhoAC_Bbig_mx /Bbig_embed.
    by rewrite (@ptrace2_conj_tens_right_iso R
      (dim 'H[H]_(A :|: C0)) (dim 'H[H]_B)
      (dim 'H[H]_Bbig) WB_Bbig rhoAC_B_mx HWB_Bbig_iso)
      HrhoAC_B_ptr. }
  have disC_Bbig : [disjoint C0 & Bbig] by rewrite disjoint_sym.
  have disAC_Bbig : [disjoint A :|: C0 & Bbig].
  { by rewrite disjointUX disA_Bbig disC_Bbig. }
  have HptBbig_eq :
      forall X : 'F[H]_(A :|: C0 :|: Bbig),
      @ptrace_cast3C R L H A C0 Bbig disA_Bbig disC_Bbig X =
      ptrace_cast disAC_Bbig X.
  { move=> X.
    rewrite /ptrace_cast3C /ptrace_cast /ptrace_cast_gen.
    have Hdu : setDU3_C disA_Bbig disC_Bbig = setDU_r disAC_Bbig
      := eq_irrelevance _ _.
    by rewrite Hdu. }
  pose UAC_Bbig := @tenv_mxU R L H (A :|: C0) Bbig.
  have HUAC_Bbig : UAC_Bbig \is unitarymx := tenv_mxU_unitarymx _ _.
  have HUAC_Bbig_adj : UAC_Bbig^*t \is unitarymx
    := tenv_mxU_adj_unitarymx disAC_Bbig.
  have HUAC_BbigK : UAC_Bbig^*t *m UAC_Bbig = 1%:M.
  { by have := unitarymxK HUAC_Bbig_adj; rewrite adjmxK. }
  pose rhoACBbig_lf : 'F[H]_(A :|: C0 :|: Bbig) :=
    mx2h (UAC_Bbig *m rhoAC_Bbig_mx *m UAC_Bbig^*t).
  have HrhoACBbig_h2mx : h2mx rhoACBbig_lf =
      UAC_Bbig *m rhoAC_Bbig_mx *m UAC_Bbig^*t
    by rewrite /rhoACBbig_lf mx2hK.
  have PrhoACBbig_lf : rhoACBbig_lf \is psdlf.
  { rewrite qualifE HrhoACBbig_h2mx.
    exact: psdmx_bimap_closed_gen HrhoAC_Bbig_psd. }
  have HrhoACBbig_rank : (\Rank rhoACBbig_lf <= 1)%N.
  { rewrite /lfrank HrhoACBbig_h2mx.
    rewrite (mxrank_mulmxU _ HUAC_Bbig_adj).
    rewrite -[UAC_Bbig]adjmxK (mxrank_mulUCmx _ HUAC_Bbig_adj).
    exact: HrhoAC_Bbig_rank. }
  have HrhoACBbig_tr : @complex.Re R (\Tr rhoACBbig_lf) <= 1.
  { rewrite /lftrace HrhoACBbig_h2mx mxtrace_mulC mulmxA.
    by rewrite HUAC_BbigK mul1mx. }
  have HrhoACBbig_marg :
      ptrace_cast3C disA_Bbig disC_Bbig rhoACBbig_lf = rhoAC.
  { apply/h2mx_inj.
    rewrite HptBbig_eq (h2mx_ptrace_cast_ptrace2 disAC_Bbig).
    have -> :
        UAC_Bbig^*t *m h2mx rhoACBbig_lf *m UAC_Bbig = rhoAC_Bbig_mx.
    { rewrite HrhoACBbig_h2mx.
      transitivity
        ((UAC_Bbig^*t *m UAC_Bbig) *m rhoAC_Bbig_mx *m
          (UAC_Bbig^*t *m UAC_Bbig)).
      - by rewrite !mulmxA.
      - by rewrite HUAC_BbigK mul1mx mulmx1. }
    exact: HrhoAC_Bbig_ptr. }
  have Hle_uhlmann_lift :
      forall tauAC : 'F[H]_(A :|: C0),
      eps_ball eps rhoAC tauAC ->
      exists tauAC_Bbig_mx : 'M[C]_(dim 'H[H]_(A :|: C0) * dim 'H[H]_Bbig),
        [/\ tauAC_Bbig_mx \is psdmx,
            (\rank tauAC_Bbig_mx <= 1)%N,
            @complex.Re R (\tr tauAC_Bbig_mx) <= 1,
            ptrace2 tauAC_Bbig_mx = h2mx tauAC &
            gfidelity rhoAC_Bbig_mx tauAC_Bbig_mx =
              gfidelity (h2mx rhoAC) (h2mx tauAC)].
  { move=> tauAC HtauAC_ball.
    have HtauAC_psd : tauAC \is psdlf := eps_ball_psdlf HtauAC_ball.
    have HtauAC_mx_psd : h2mx tauAC \is psdmx
      by move: HtauAC_psd; rewrite qualifE.
    have HtauAC_tr : @complex.Re R (\tr (h2mx tauAC)) <= 1.
    { by move: (eps_ball_trlf HtauAC_ball); rewrite /lftrace. }
    have HtauAC_rank :
        (\rank (h2mx tauAC) <= dim 'H[H]_Bbig)%N.
    { exact: leq_trans (rank_leq_row _) dimAC_Bbig. }
    have [tauAC_Bbig_mx HtauAC_Bbig] :=
      @subnorm_matrix_uhlmann R
        (dim 'H[H]_(A :|: C0)) (dim 'H[H]_Bbig)
        rhoAC_Bbig_mx (h2mx rhoAC) (h2mx tauAC)
        HrhoAC_Bbig_psd HrhoAC_Bbig_rank HrhoAC_Bbig_tr
        HrhoAC_Bbig_ptr HtauAC_mx_psd HtauAC_tr HtauAC_rank.
    by exists tauAC_Bbig_mx. }
  have Hle_labelled_lift :
      forall tauAC : 'F[H]_(A :|: C0),
      eps_ball eps rhoAC tauAC ->
      exists tauACBbig : 'F[H]_(A :|: C0 :|: Bbig),
        [/\ tauACBbig \is psdlf,
            (\Rank tauACBbig <= 1)%N,
            @complex.Re R (\Tr tauACBbig) <= 1,
            @ptrace_cast3C R L H A C0 Bbig
              disA_Bbig disC_Bbig tauACBbig = tauAC &
            gfidelity rhoAC_Bbig_mx
              (UAC_Bbig^*t *m h2mx tauACBbig *m UAC_Bbig) =
              gfidelity (h2mx rhoAC) (h2mx tauAC)].
  { move=> tauAC HtauAC_ball.
    have [tauAC_Bbig_mx HtauAC_Bbig] :=
      Hle_uhlmann_lift tauAC HtauAC_ball.
    case: HtauAC_Bbig => Ptau_mx Htau_rank Htau_tr Htau_ptr Htau_fid.
    pose tauACBbig : 'F[H]_(A :|: C0 :|: Bbig) :=
      mx2h (UAC_Bbig *m tauAC_Bbig_mx *m UAC_Bbig^*t).
    have Htau_h2mx : h2mx tauACBbig =
        UAC_Bbig *m tauAC_Bbig_mx *m UAC_Bbig^*t
      by rewrite /tauACBbig mx2hK.
    have Ptau_lf : tauACBbig \is psdlf.
    { rewrite qualifE Htau_h2mx.
      exact: psdmx_bimap_closed_gen Ptau_mx. }
    have Htau_lfrank : (\Rank tauACBbig <= 1)%N.
    { rewrite /lfrank Htau_h2mx.
      rewrite (mxrank_mulmxU _ HUAC_Bbig_adj).
      rewrite -[UAC_Bbig]adjmxK (mxrank_mulUCmx _ HUAC_Bbig_adj).
      exact: Htau_rank. }
    have Htau_lftr : @complex.Re R (\Tr tauACBbig) <= 1.
    { rewrite /lftrace Htau_h2mx mxtrace_mulC mulmxA.
      by rewrite HUAC_BbigK mul1mx. }
    have Htau_marg : ptrace_cast3C disA_Bbig disC_Bbig tauACBbig = tauAC.
    { apply/h2mx_inj.
      rewrite HptBbig_eq (h2mx_ptrace_cast_ptrace2 disAC_Bbig).
      rewrite Htau_h2mx -/UAC_Bbig.
      by rewrite !mulmxA HUAC_BbigK mul1mx -mulmxA HUAC_BbigK mulmx1. }
    exists tauACBbig.
    split.
    - exact: Ptau_lf.
    - exact: Htau_lfrank.
    - exact: Htau_lftr.
    - exact: Htau_marg.
    by rewrite Htau_h2mx !mulmxA HUAC_BbigK mul1mx -mulmxA
      HUAC_BbigK mulmx1. }
  have trlf_ptrace3C_Bbig
      (f : 'F[H]_(A :|: C0 :|: Bbig)) :
      \Tr (@ptrace_cast3C R L H A C0 Bbig
        disA_Bbig disC_Bbig f) = \Tr f.
  { rewrite /ptrace_cast3C /ptrace_cast_gen castlf_trlfE.
    have /cptpP [_ /tpmapP Htp] :=
      @ptraceso_qc R L H Bbig (A :|: C0 :|: Bbig).
    exact: Htp. }
  have trlf_ptrace3B_Bbig
      (f : 'F[H]_(A :|: C0 :|: Bbig)) :
      \Tr (@ptrace_cast3B R L H A C0 Bbig disAC disC_Bbig f) =
      \Tr f.
  { rewrite /ptrace_cast3B /ptrace_cast_gen castlf_trlfE.
    have /cptpP [_ /tpmapP Htp] :=
      @ptraceso_qc R L H C0 (A :|: C0 :|: Bbig).
    exact: Htp. }
  have HrhoACBbig_tr_eq : \Tr rhoACBbig_lf = \Tr rhoAC.
  { by rewrite -HrhoACBbig_marg trlf_ptrace3C_Bbig. }
  pose rhoABbig :=
    @ptrace_cast3B R L H A C0 Bbig disAC disC_Bbig rhoACBbig_lf.
  have PrhoABbig : rhoABbig \is psdlf.
  { rewrite /rhoABbig /ptrace_cast3B; exact: ptrace_cast_gen_psdlf. }
  have HrhoABbig_tr_eq :
      @complex.Re R (\Tr rhoABbig) = @complex.Re R (\Tr rhoAC).
  { by rewrite /rhoABbig trlf_ptrace3B_Bbig HrhoACBbig_tr_eq. }
  have HrhoABbig_tr : @complex.Re R (\Tr rhoABbig) <= 1
    by rewrite HrhoABbig_tr_eq.
  have HrhoABbig_den : rhoABbig \is denlf.
  { apply/denlfP; split=> //.
    have Hreal : \Tr rhoABbig \is Num.real :=
      ger0_real (psdlf_trlf PrhoABbig).
    by rewrite -(RRe_real Hreal) lecR. }
  have Heps_pair_ABbig :
      0 <= eps < Num.sqrt (@complex.Re R (\Tr rhoABbig)).
  { by rewrite Heps HrhoABbig_tr_eq Heps_lt_AC. }
  have dimABbig_supp_enough :
      (dim 'H[H]_A * dim 'H[H]_Bbig <=
       dim 'H[H]_Bbig_supp)%N.
  { by rewrite -(tenv_dim disA_Bbig). }
  have Hle_target_support :
      exists tauABbig : 'F[H]_(A :|: Bbig),
        eps_ball eps rhoABbig tauABbig /\
        smooth_hmax Bbig eps rhoABbig = hmax Bbig tauABbig /\
        (supplf (ptrace_cast disA_Bbig rhoABbig) \O
         supplf (ptrace_castl disA_Bbig rhoABbig)) \o tauABbig = tauABbig /\
        tauABbig \o
          (supplf (ptrace_cast disA_Bbig rhoABbig) \O
           supplf (ptrace_castl disA_Bbig rhoABbig)) = tauABbig.
  { have [tauABbig [Hball [HoptE [Hsupp_l Hsupp_r]]]] :=
      @smoothing_support_hmax R L H A Bbig Bbig_supp
        disA_Bbig disA_Bbig_supp disBbig_Bbig_supp
        dimABbig_supp_enough Cp Cpp
        disA_Cp disA_Cpp disBbig_Cp disBbig_Cpp
        disCp_Cpp
        dimA_Cp dimBbig_supp_Cp_Cpp dimBbig_Cpp
        eps rhoABbig HrhoABbig_den Heps_pair_ABbig.
    have Hsmooth_fin :
        smooth_hmaxE Bbig eps rhoABbig =
        (smooth_hmax Bbig eps rhoABbig)%:E
      := @smooth_hmaxE_EFin R L H (A :|: Bbig) Bbig
           eps rhoABbig PrhoABbig HrhoABbig_tr Heps_pair_ABbig.
    have PtauABbig : tauABbig \is psdlf := eps_ball_psdlf Hball.
    have HtauABbig_tr : @complex.Re R (\Tr tauABbig) <= 1
      := eps_ball_trlf Hball.
    have HtauABbig_pos : 0 < @complex.Re R (\Tr tauABbig)
      := eps_ball_trace_pos PrhoABbig HrhoABbig_tr
           Heps_pair_ABbig Hball.
    have Hhmax_fin :
        hmaxE Bbig tauABbig = (hmax Bbig tauABbig)%:E
      := @hmaxE_EFin R L H (A :|: Bbig) Bbig
           tauABbig PtauABbig HtauABbig_tr HtauABbig_pos.
    have HoptR : smooth_hmax Bbig eps rhoABbig = hmax Bbig tauABbig.
    { move: HoptE.
      rewrite Hsmooth_fin Hhmax_fin.
      by case. }
    by exists tauABbig; split=> //; split=> //; split=> //. }
  set eqS_Bbig := setUC_swap3 A C0 Bbig
    : A :|: C0 :|: Bbig = A :|: Bbig :|: C0.
  have disABbig_C : [disjoint A :|: Bbig & C0].
  { by rewrite disjointUX disAC disBbig_C. }
  have HptC_recast_Bbig :
      forall X : 'F[H]_(A :|: C0 :|: Bbig),
      @ptrace_cast3B R L H A C0 Bbig disAC disC_Bbig X =
      ptrace_cast disABbig_C (castlf (eqS_Bbig, eqS_Bbig) X).
  { move=> X.
    rewrite /ptrace_cast3B /ptrace_cast /ptrace_cast_gen.
    have eq_res : (A :|: C0 :|: Bbig) :\: C0 =
        (A :|: Bbig :|: C0) :\: C0
      by rewrite eqS_Bbig.
    rewrite (ptracelf_castlf_eq eqS_Bbig eq_res).
    rewrite castlf_comp.
    by congr (castlf (_, _) _); exact: eq_irrelevance. }
  pose WAC_Bbig := (\1 : 'F[H]_(A :|: C0)) \⊗ VB_Bbig.
  have HrhoACBbig_lf_form :
      rhoACBbig_lf = WAC_Bbig \o rhoABC_acb \o WAC_Bbig^A.
  { apply/h2mx_inj.
    rewrite HrhoACBbig_h2mx !h2mx_comp h2mx_adj.
    rewrite /WAC_Bbig h2mx_tenf h2mx1.
    rewrite !adjmxM adjmxK adjmx_tens adjmx1.
    rewrite /rhoAC_Bbig_mx /Bbig_embed /rhoAC_B_mx /UAC_B /UAC_Bbig
      /WB_Bbig.
    rewrite adjmx_tens adjmx1.
    by rewrite !mulmxA. }
  pose WAB_Bbig := (\1 : 'F[H]_A) \⊗ VB_Bbig.
  pose WABbig_C := WAB_Bbig \⊗ (\1 : 'F[H]_C0).
  have HrhoACBbig_abc_form :
      castlf (eqS_Bbig, eqS_Bbig) rhoACBbig_lf =
      WABbig_C \o rhoABC \o WABbig_C^A.
  { rewrite HrhoACBbig_lf_form /rhoABC_acb /WAC_Bbig /WABbig_C /WAB_Bbig.
    to_Fnd.
    rewrite -tenF11.
    by rewrite -!tenFA
      (tenFC (to_Fnd (\1 : 'F[H]_C0)) (to_Fnd VB_Bbig)) !tenFA. }
  have HrhoABbig_fixed_iso :
      rhoABbig = WAB_Bbig \o rhoAB \o WAB_Bbig^A.
  { apply/h2mx_inj.
    rewrite /rhoABbig HptC_recast_Bbig HrhoACBbig_abc_form.
    rewrite (h2mx_ptrace_cast_ptrace2 disABbig_C).
    rewrite !h2mx_comp h2mx_adj.
    rewrite (h2mx_tenf WAB_Bbig (\1 : 'F[H]_C0)) h2mx1.
    rewrite adjmxM.
    set TABbig_C := @tenv_mxU R L H (A :|: Bbig) C0.
    set WABmx := h2mx WAB_Bbig.
    set TAB_C := @tenv_mxU R L H (A :|: B) C0.
    have HTABbigK : TABbig_C^*t *m TABbig_C = 1%:M.
    { have /unitarymxK : TABbig_C^*t \is unitarymx
        := tenv_mxU_adj_unitarymx disABbig_C.
      by rewrite adjmxK. }
    rewrite -/TABbig_C -/WABmx -/TAB_C.
    rewrite adjmxK adjmxM.
    rewrite !mulmxA HTABbigK !mul1mx.
    rewrite -!mulmxA HTABbigK ?mulmx1 //.
    rewrite adjmx_tens adjmx1.
    transitivity
      (ptrace2
        ((WABmx *t (1%:M : 'M[C]_(dim 'H[H]_C0))) *m
         (TAB_C^*t *m h2mx rhoABC *m TAB_C) *m
         (WABmx^*t *t (1%:M : 'M[C]_(dim 'H[H]_C0))))).
    { congr ptrace2.
      by rewrite !mulmxA. }
    rewrite ptrace2_tens_id_sandwich.
    rewrite /rhoAB_C_mx -/TAB_C in HrhoAB_C_ptr.
    rewrite HrhoAB_C_ptr.
    by rewrite h2mx_adj -/WABmx !mulmxA. }
  have HIA_Bbig_iso : (\1 : 'F[H]_A) \is isolf.
  { apply/isolfP. by rewrite adjf1 comp_lfun1l. }
  pose IA_Bbig := IsoLf_Build HIA_Bbig_iso.
  have HIA_Bbig : (IA_Bbig : 'F[H]_(A, A)) = \1
    by exact: IsoLf_BuildE HIA_Bbig_iso.
  have Hle_labelled_lift_rank1 :
      forall tauAC : 'F[H]_(A :|: C0),
      eps_ball eps rhoAC tauAC -> tauAC != 0 ->
      exists tauACBbig : 'F[H]_(A :|: C0 :|: Bbig),
        [/\ tauACBbig \is psdlf,
            \Rank tauACBbig = 1%N,
            @complex.Re R (\Tr tauACBbig) <= 1,
            @ptrace_cast3C R L H A C0 Bbig
              disA_Bbig disC_Bbig tauACBbig = tauAC &
            gfidelity rhoAC_Bbig_mx
              (UAC_Bbig^*t *m h2mx tauACBbig *m UAC_Bbig) =
              gfidelity (h2mx rhoAC) (h2mx tauAC)].
  { move=> tauAC HtauAC_ball HtauAC_ne0.
    have [tauACBbig Hlift] := Hle_labelled_lift tauAC HtauAC_ball.
    case: Hlift => Ptau Hrank_le Htr Hmarg Hfid.
    have HtauACBbig_ne0 : tauACBbig != 0.
    { apply/eqP=> H0.
      move: Hmarg.
      rewrite H0 /ptrace_cast3C /ptrace_cast_gen raddf0 /= raddf0.
      by move=> Htau0; move/eqP: HtauAC_ne0; rewrite -Htau0. }
    have Hrank_gt0 : (0 < \Rank tauACBbig)%N.
    { rewrite lt0n /lfrank mxrank_eq0.
      apply/eqP=> Hmx0.
      have H0 : tauACBbig = 0 by apply/h2mx_inj; rewrite Hmx0 h2mx0.
      by move/eqP: HtauACBbig_ne0; apply. }
    have Hrank_eq1 : \Rank tauACBbig = 1%N.
    { by apply/eqP; rewrite eqn_leq Hrank_le Hrank_gt0. }
    by exists tauACBbig; split=> //. }
  have HptC_eq_ABbig :
      forall X : 'F[H]_(A :|: Bbig :|: C0),
      @ptrace_cast3C R L H A Bbig C0 disAC disBbig_C X =
      ptrace_cast disABbig_C X.
  { move=> X.
    rewrite /ptrace_cast3C /ptrace_cast /ptrace_cast_gen.
    have Hdu : setDU3_C disAC disBbig_C = setDU_r disABbig_C
      := eq_irrelevance _ _.
    by rewrite Hdu. }
  have HptB_cast_Bbig :
      forall X : 'F[H]_(A :|: C0 :|: Bbig),
      @ptrace_cast3B R L H A Bbig C0 disA_Bbig disBbig_C
        (castlf (eqS_Bbig, eqS_Bbig) X) =
      @ptrace_cast3C R L H A C0 Bbig disA_Bbig disC_Bbig X.
  { move=> X.
    rewrite /ptrace_cast3B /ptrace_cast3C /ptrace_cast /ptrace_cast_gen.
    have eq_res : (A :|: C0 :|: Bbig) :\: Bbig =
        (A :|: Bbig :|: C0) :\: Bbig
      by rewrite eqS_Bbig.
    rewrite (ptracelf_castlf_eq eqS_Bbig eq_res).
    rewrite castlf_comp.
    by congr (castlf (_, _) _); exact: eq_irrelevance. }
  have Hle_lift_ABbig_ball :
      forall (tauAC : 'F[H]_(A :|: C0))
             (tauACBbig : 'F[H]_(A :|: C0 :|: Bbig)),
      eps_ball eps rhoAC tauAC ->
      tauACBbig \is psdlf ->
      @complex.Re R (\Tr tauACBbig) <= 1 ->
      gfidelity rhoAC_Bbig_mx
        (UAC_Bbig^*t *m h2mx tauACBbig *m UAC_Bbig) =
        gfidelity (h2mx rhoAC) (h2mx tauAC) ->
      eps_ball eps rhoABbig
        (ptrace_cast3B disAC disC_Bbig tauACBbig).
  { move=> tauAC tauACBbig HtauAC_ball Ptau Htr Hfid.
    have Ptau_mx : h2mx tauACBbig \is psdmx by move: Ptau; rewrite qualifE.
    have Prho_big_mx : h2mx rhoACBbig_lf \is psdmx
      by move: PrhoACBbig_lf; rewrite qualifE.
    have HtauAC_psd : tauAC \is psdlf := eps_ball_psdlf HtauAC_ball.
    have HtauAC_mx_psd : h2mx tauAC \is psdmx
      by move: HtauAC_psd; rewrite qualifE.
    have HrhoAC_mx_psd : h2mx rhoAC \is psdmx
      by move: PrhoAC; rewrite qualifE.
    have Hrho_prod :
        UAC_Bbig^*t *m h2mx rhoACBbig_lf *m UAC_Bbig = rhoAC_Bbig_mx.
    { rewrite HrhoACBbig_h2mx.
      transitivity ((UAC_Bbig^*t *m UAC_Bbig) *m rhoAC_Bbig_mx *m
          (UAC_Bbig^*t *m UAC_Bbig)).
      - by rewrite !mulmxA.
      - by rewrite HUAC_BbigK mul1mx mulmx1. }
    pose tau_prod := UAC_Bbig^*t *m h2mx tauACBbig *m UAC_Bbig.
    have Ptau_prod : tau_prod \is psdmx.
    { rewrite /tau_prod -[UAC_Bbig in _ *m _ *m UAC_Bbig]adjmxK.
      exact: psdmx_bimap_closed_gen Ptau_mx. }
    have Hgf_full :
        gfid tauACBbig rhoACBbig_lf =
        gfid tauAC rhoAC.
    { rewrite /gfid.
      rewrite (gfid_tenv_mxU_conj_eq_mx disAC_Bbig Ptau_mx Prho_big_mx).
      rewrite Hrho_prod -/tau_prod.
      rewrite (gfid_sym_mx Ptau_prod HrhoAC_Bbig_psd) Hfid.
      by rewrite (gfid_sym_mx HtauAC_mx_psd HrhoAC_mx_psd). }
    have Hpd_full : pur_dist tauACBbig rhoACBbig_lf <= eps.
    { move: HtauAC_ball => /andP [/andP [_ _] HpdAC].
      by rewrite /pur_dist Hgf_full. }
      have Ptau_ABbig :
          ptrace_cast3B disAC disC_Bbig tauACBbig \is psdlf.
      { rewrite /ptrace_cast3B; exact: ptrace_cast_gen_psdlf Ptau. }
      have Htr_ABbig :
          @complex.Re R (\Tr (ptrace_cast3B disAC disC_Bbig tauACBbig)) <= 1
        by rewrite trlf_ptrace3B_Bbig.
    have Ptau_cast : castlf (eqS_Bbig, eqS_Bbig) tauACBbig \is psdlf
      by rewrite castlf_psdlfE.
    have Prho_cast : castlf (eqS_Bbig, eqS_Bbig) rhoACBbig_lf \is psdlf
      by rewrite castlf_psdlfE.
    have Hpd_cast :
        pur_dist (castlf (eqS_Bbig, eqS_Bbig) tauACBbig)
          (castlf (eqS_Bbig, eqS_Bbig) rhoACBbig_lf) =
        pur_dist tauACBbig rhoACBbig_lf.
    { rewrite /pur_dist /gfid !Hh2mx_castlf_gen.
      by rewrite gfid_cast_mx. }
    have Hpd_mono := @pd_mono_ptrace_cast
      R L H (A :|: Bbig) C0 disABbig_C
        (castlf (eqS_Bbig, eqS_Bbig) rhoACBbig_lf)
        (castlf (eqS_Bbig, eqS_Bbig) tauACBbig)
        Ptau_cast Prho_cast.
      rewrite -!HptC_recast_Bbig Hpd_cast in Hpd_mono.
      have Hpd_ABbig := le_trans Hpd_mono Hpd_full.
      have Hpos_ABbig :
          0 < @complex.Re R
            (\Tr (ptrace_cast3B disAC disC_Bbig tauACBbig)).
      {
        have Holdball :
            ((ptrace_cast3B disAC disC_Bbig tauACBbig \is psdlf) &&
             (@complex.Re R
               (\Tr (ptrace_cast3B disAC disC_Bbig tauACBbig)) <= 1)) &&
            (pur_dist (ptrace_cast3B disAC disC_Bbig tauACBbig)
               rhoABbig <= eps).
        { by rewrite Ptau_ABbig Htr_ABbig Hpd_ABbig. }
        exact:
          (eps_ball_trace_pos_from_small PrhoABbig HrhoABbig_tr
             Heps_pair_ABbig Holdball).
      }
      by rewrite /eps_ball Ptau_ABbig Hpos_ABbig Htr_ABbig Hpd_ABbig. }
  have Hle_full_ball :
      forall tauAC : 'F[H]_(A :|: C0),
      eps_ball eps rhoAC tauAC ->
      exists tauACBbig : 'F[H]_(A :|: C0 :|: Bbig),
        ptrace_cast3C disA_Bbig disC_Bbig tauACBbig = tauAC /\
        eps_ball eps rhoACBbig_lf tauACBbig.
  { move=> tauAC HtauAC_ball.
    have [tauACBbig Hlift] := Hle_labelled_lift tauAC HtauAC_ball.
    case: Hlift => Ptau Hrank_le Htr Hmarg Hfid.
    have Ptau_mx : h2mx tauACBbig \is psdmx by move: Ptau; rewrite qualifE.
    have Prho_big_mx : h2mx rhoACBbig_lf \is psdmx
      by move: PrhoACBbig_lf; rewrite qualifE.
    have HtauAC_psd : tauAC \is psdlf := eps_ball_psdlf HtauAC_ball.
    have HtauAC_mx_psd : h2mx tauAC \is psdmx
      by move: HtauAC_psd; rewrite qualifE.
    have HrhoAC_mx_psd : h2mx rhoAC \is psdmx
      by move: PrhoAC; rewrite qualifE.
    have Hrho_prod :
        UAC_Bbig^*t *m h2mx rhoACBbig_lf *m UAC_Bbig = rhoAC_Bbig_mx.
    { rewrite HrhoACBbig_h2mx.
      transitivity
        ((UAC_Bbig^*t *m UAC_Bbig) *m rhoAC_Bbig_mx *m
          (UAC_Bbig^*t *m UAC_Bbig)).
      - by rewrite !mulmxA.
      - by rewrite HUAC_BbigK mul1mx mulmx1. }
    pose tau_prod := UAC_Bbig^*t *m h2mx tauACBbig *m UAC_Bbig.
    have Ptau_prod : tau_prod \is psdmx.
    { rewrite /tau_prod -[UAC_Bbig in _ *m _ *m UAC_Bbig]adjmxK.
      exact: psdmx_bimap_closed_gen Ptau_mx. }
    have Hgf_full :
        gfid tauACBbig rhoACBbig_lf =
        gfid tauAC rhoAC.
    { rewrite /gfid.
      rewrite (gfid_tenv_mxU_conj_eq_mx disAC_Bbig Ptau_mx Prho_big_mx).
      rewrite Hrho_prod -/tau_prod.
      rewrite (gfid_sym_mx Ptau_prod HrhoAC_Bbig_psd) Hfid.
      by rewrite (gfid_sym_mx HtauAC_mx_psd HrhoAC_mx_psd). }
      have Hpd_full : pur_dist tauACBbig rhoACBbig_lf <= eps.
      { move: HtauAC_ball => /andP [/andP [_ _] HpdAC].
        by rewrite /pur_dist Hgf_full. }
      have HtauACBbig_pos : 0 < @complex.Re R (\Tr tauACBbig).
      {
        have HptC_pos :
            0 < @complex.Re R
              (\Tr (ptrace_cast3C disA_Bbig disC_Bbig tauACBbig)).
        { by rewrite Hmarg; exact: eps_ball_trlf_gt0 HtauAC_ball. }
        by move: HptC_pos; rewrite trlf_ptrace3C_Bbig.
      }
      exists tauACBbig; split=> //.
      by rewrite /eps_ball Ptau HtauACBbig_pos Htr Hpd_full. }
  have Hle_ABbig_ball :
      forall tauAC : 'F[H]_(A :|: C0),
      eps_ball eps rhoAC tauAC ->
      exists tauACBbig : 'F[H]_(A :|: C0 :|: Bbig),
        ptrace_cast3C disA_Bbig disC_Bbig tauACBbig = tauAC /\
        eps_ball eps rhoABbig
          (ptrace_cast3B disAC disC_Bbig tauACBbig).
  { move=> tauAC HtauAC_ball.
    have [tauACBbig [Hmarg Hball_full]] :=
      Hle_full_ball tauAC HtauAC_ball.
    have Ptau_full : tauACBbig \is psdlf := eps_ball_psdlf Hball_full.
    have Htr_full : @complex.Re R (\Tr tauACBbig) <= 1
      := eps_ball_trlf Hball_full.
    have Hpd_full : pur_dist tauACBbig rhoACBbig_lf <= eps
      by move: Hball_full; rewrite /eps_ball => /andP [/andP [_ _] Hpd].
    have Ptau_ABbig :
        ptrace_cast3B disAC disC_Bbig tauACBbig \is psdlf.
    { rewrite /ptrace_cast3B; exact: ptrace_cast_gen_psdlf Ptau_full. }
      have Htr_ABbig :
          @complex.Re R (\Tr (ptrace_cast3B disAC disC_Bbig tauACBbig)) <= 1
        by rewrite trlf_ptrace3B_Bbig.
      have Hpos_ABbig :
          0 < @complex.Re R
            (\Tr (ptrace_cast3B disAC disC_Bbig tauACBbig))
        by rewrite trlf_ptrace3B_Bbig; exact: eps_ball_trlf_gt0 Hball_full.
    have Ptau_cast : castlf (eqS_Bbig, eqS_Bbig) tauACBbig \is psdlf
      by rewrite castlf_psdlfE.
    have Prho_cast : castlf (eqS_Bbig, eqS_Bbig) rhoACBbig_lf \is psdlf
      by rewrite castlf_psdlfE.
    have Hpd_cast :
        pur_dist (castlf (eqS_Bbig, eqS_Bbig) tauACBbig)
          (castlf (eqS_Bbig, eqS_Bbig) rhoACBbig_lf) =
        pur_dist tauACBbig rhoACBbig_lf.
    { rewrite /pur_dist /gfid !Hh2mx_castlf_gen.
      by rewrite gfid_cast_mx. }
    have Hpd_mono := @pd_mono_ptrace_cast
      R L H (A :|: Bbig) C0 disABbig_C
        (castlf (eqS_Bbig, eqS_Bbig) rhoACBbig_lf)
        (castlf (eqS_Bbig, eqS_Bbig) tauACBbig)
        Ptau_cast Prho_cast.
      rewrite -!HptC_recast_Bbig Hpd_cast in Hpd_mono.
      have Hpd_ABbig := le_trans Hpd_mono Hpd_full.
      exists tauACBbig; split=> //.
      by rewrite /eps_ball Ptau_ABbig Hpos_ABbig Htr_ABbig Hpd_ABbig. }
  have Hle_smooth_hmax_Bbig :
      smooth_hmax B eps rhoAB <= smooth_hmax Bbig eps rhoABbig.
  { have Heps_pair_AB0 : 0 <= eps < Num.sqrt (@complex.Re R (\Tr rhoAB))
      by rewrite Heps Heps_lt_AB.
    have HrhoAB_den : rhoAB \is denlf.
    { apply/denlfP; split=> //.
      have Hreal : \Tr rhoAB \is Num.real := ger0_real (psdlf_trlf PrhoAB).
      by rewrite -(RRe_real Hreal) lecR. }
    have dimAB_ABbig : (dim 'H[H]_(A :|: B) <= dim 'H[H]_(A :|: Bbig))%N.
    { rewrite (tenv_dim disAB) (tenv_dim disA_Bbig).
      exact: leq_mul (leqnn _) dimB_Bbig. }
    have dimAB_Bbig_supp :
        (dim 'H[H]_(A :|: B) <= dim 'H[H]_Bbig_supp)%N
      := leq_trans dimAB_ABbig dimABbig_Bbig_supp.
    have HisoE := @smooth_iso_hmax L H A B A Bbig
      disAB disA_Bbig Bbig_supp Cp Cpp Cp Cpp
      disA_Bbig_supp disB_Bbig_supp
      disA_Bbig_supp disBbig_Bbig_supp
      dimAB_Bbig_supp dimABbig_Bbig_supp
      disA_Cp disA_Cpp disB_Cp disB_Cpp disCp_Cpp
      dimA_Cp dimBbig_supp_Cp_Cpp dimB_Cpp
      disA_Cp disA_Cpp disBbig_Cp disBbig_Cpp disCp_Cpp
      dimA_Cp dimBbig_supp_Cp_Cpp dimBbig_Cpp
      eps rhoAB IA_Bbig VB_Bbig HrhoAB_den Heps_pair_AB0.
    have Hsrc_fin :
        smooth_hmaxE B eps rhoAB = (smooth_hmax B eps rhoAB)%:E
      := @smooth_hmaxE_EFin R L H (A :|: B) B
           eps rhoAB PrhoAB HrhoAB_tr Heps_pair_AB0.
    have Htgt_fin :
        smooth_hmaxE Bbig eps rhoABbig =
        (smooth_hmax Bbig eps rhoABbig)%:E
      := @smooth_hmaxE_EFin R L H (A :|: Bbig) Bbig
           eps rhoABbig PrhoABbig HrhoABbig_tr Heps_pair_ABbig.
    have HisoR :
        smooth_hmax Bbig eps rhoABbig = smooth_hmax B eps rhoAB.
    { move: HisoE.
      rewrite HIA_Bbig -/WAB_Bbig -HrhoABbig_fixed_iso.
      rewrite Htgt_fin Hsrc_fin.
      by case. }
    by rewrite HisoR. }
  have Hle_lift_max_bound :
      forall (tauAC : 'F[H]_(A :|: C0))
             (tauACBbig : 'F[H]_(A :|: C0 :|: Bbig)),
      eps_ball eps rhoAC tauAC ->
      tauACBbig \is psdlf ->
      @complex.Re R (\Tr tauACBbig) <= 1 ->
      gfidelity rhoAC_Bbig_mx
        (UAC_Bbig^*t *m h2mx tauACBbig *m UAC_Bbig) =
        gfidelity (h2mx rhoAC) (h2mx tauAC) ->
      smooth_hmax B eps rhoAB <=
      hmax Bbig (ptrace_cast3B disAC disC_Bbig tauACBbig).
  { move=> tauAC tauACBbig HtauAC_ball Ptau Htr Hfid.
    have Hball_ABbig :=
      Hle_lift_ABbig_ball tauAC tauACBbig HtauAC_ball Ptau Htr Hfid.
    have Htarget_le :=
      @smooth_hmax_lb R L H (A :|: Bbig) Bbig
        eps rhoABbig (ptrace_cast3B disAC disC_Bbig tauACBbig)
        PrhoABbig HrhoABbig_tr Heps_pair_ABbig Hball_ABbig.
    exact: le_trans Hle_smooth_hmax_Bbig Htarget_le. }
  have Hle_same_witness_dual_max :
      forall tauAC : 'F[H]_(A :|: C0),
      eps_ball eps rhoAC tauAC -> tauAC != 0 ->
      exists tauACBbig : 'F[H]_(A :|: C0 :|: Bbig),
        [/\ ptrace_cast3C disA_Bbig disC_Bbig tauACBbig = tauAC,
            hmax Bbig (ptrace_cast3B disAC disC_Bbig tauACBbig) =
              - hmin C0 tauAC,
            eps_ball eps rhoABbig
              (ptrace_cast3B disAC disC_Bbig tauACBbig) &
            smooth_hmax B eps rhoAB <=
              hmax Bbig (ptrace_cast3B disAC disC_Bbig tauACBbig)].
  { move=> tauAC HtauAC_ball HtauAC_ne0.
    have [tauACBbig Hlift] :=
      Hle_labelled_lift_rank1 tauAC HtauAC_ball HtauAC_ne0.
    case: Hlift => Ptau Hrank Htr Hmarg Hfid.
    pose tauABC_cast := castlf (eqS_Bbig, eqS_Bbig) tauACBbig.
    have Ptau_cast : tauABC_cast \is psdlf
      by rewrite /tauABC_cast castlf_psdlfE.
    have Htr_cast : @complex.Re R (\Tr tauABC_cast) <= 1
      by rewrite /tauABC_cast castlf_trlfE.
    have Hrank_cast : \Rank tauABC_cast = 1%N.
    { rewrite /tauABC_cast /lfrank Hh2mx_castlf_gen mxrank_cast.
      exact: Hrank. }
    have Htau_cast_den : tauABC_cast \is denlf.
    { apply/denlfP; split=> //.
      have Hreal : \Tr tauABC_cast \is Num.real :=
        ger0_real (psdlf_trlf Ptau_cast).
      by rewrite -(RRe_real Hreal) lecR. }
    have Hball_ABbig :=
      Hle_lift_ABbig_ball tauAC tauACBbig HtauAC_ball Ptau Htr Hfid.
    have HptC_tau :
        @ptrace_cast3C R L H A Bbig C0 disAC disBbig_C tauABC_cast =
        @ptrace_cast3B R L H A C0 Bbig disAC disC_Bbig tauACBbig.
    { by rewrite /tauABC_cast HptC_eq_ABbig -HptC_recast_Bbig. }
    have HptB_tau :
        @ptrace_cast3B R L H A Bbig C0 disA_Bbig disBbig_C tauABC_cast =
        tauAC.
    { by rewrite /tauABC_cast HptB_cast_Bbig Hmarg. }
    have HptC_psd_dual :
        @ptrace_cast3C R L H A Bbig C0 disAC disBbig_C
          tauABC_cast \is psdlf.
    { by rewrite HptC_tau; exact: eps_ball_psdlf Hball_ABbig. }
    have HptC_tr_dual :
        @complex.Re R
          (\Tr (@ptrace_cast3C R L H A Bbig C0 disAC disBbig_C
            tauABC_cast)) <= 1.
    { by rewrite HptC_tau; exact: eps_ball_trlf Hball_ABbig. }
    have HptC_pos_dual :
        0 < @complex.Re R
          (\Tr (@ptrace_cast3C R L H A Bbig C0 disAC disBbig_C
            tauABC_cast)).
    { by rewrite HptC_tau;
      exact: eps_ball_trace_pos PrhoABbig HrhoABbig_tr
        Heps_pair_ABbig Hball_ABbig. }
    have PtauAC : tauAC \is psdlf := eps_ball_psdlf HtauAC_ball.
    have HtauAC_tr : @complex.Re R (\Tr tauAC) <= 1
      := eps_ball_trlf HtauAC_ball.
    have Heps_pair_AC0 : 0 <= eps < Num.sqrt (@complex.Re R (\Tr rhoAC))
      by rewrite Heps Heps_lt_AC.
    have HtauAC_pos : 0 < @complex.Re R (\Tr tauAC)
      := eps_ball_trace_pos PrhoAC HrhoAC_tr Heps_pair_AC0 HtauAC_ball.
    have Hphi_tauAC_dual_pos :
        0 < phi_min C0
          (@ptrace_cast3B R L H A Bbig C0 disA_Bbig disBbig_C tauABC_cast).
    { rewrite HptB_tau.
      exact: (@phi_min_pos_trace R L H (A :|: C0) C0
        tauAC PtauAC HtauAC_tr HtauAC_pos). }
    have Hhmax_fin :
        hmaxE Bbig
          (@ptrace_cast3C R L H A Bbig C0 disAC disBbig_C tauABC_cast) =
        (hmax Bbig
          (@ptrace_cast3C R L H A Bbig C0 disAC disBbig_C tauABC_cast))%:E
      := @hmaxE_EFin R L H (A :|: Bbig) Bbig
           (@ptrace_cast3C R L H A Bbig C0 disAC disBbig_C tauABC_cast)
           HptC_psd_dual HptC_tr_dual HptC_pos_dual.
    have Hhmin_fin :
        hminE C0
          (@ptrace_cast3B R L H A Bbig C0 disA_Bbig disBbig_C tauABC_cast) =
        (hmin C0
          (@ptrace_cast3B R L H A Bbig C0 disA_Bbig disBbig_C tauABC_cast))%:E
      := @hminE_EFin R L H (A :|: C0) C0
           (@ptrace_cast3B R L H A Bbig C0 disA_Bbig disBbig_C tauABC_cast)
           Hphi_tauAC_dual_pos.
    have Hdual :
        hmax Bbig
          (@ptrace_cast3C R L H A Bbig C0 disAC disBbig_C
            tauABC_cast) =
        - hmin C0
          (@ptrace_cast3B R L H A Bbig C0 disA_Bbig disBbig_C
            tauABC_cast).
    { have HdualE := @minmax_dual R L H A Bbig C0
          disA_Bbig disAC disBbig_C Cp Cpp
          disA_Cp disA_Cpp disBbig_Cp disBbig_Cpp disCp_Cpp
          dimA_Cp dimC_Cp_Cpp dimBbig_Cpp
          tauABC_cast Htau_cast_den Hrank_cast.
      move: HdualE.
      rewrite Hhmax_fin Hhmin_fin EFinN.
      by case. }
    rewrite HptC_tau HptB_tau in Hdual.
    have Hmax_bound :=
      Hle_lift_max_bound tauAC tauACBbig HtauAC_ball Ptau Htr Hfid.
    by exists tauACBbig; split. }
  have Hle_max_bound :
      forall tauAC : 'F[H]_(A :|: C0),
      eps_ball eps rhoAC tauAC ->
      exists tauACBbig : 'F[H]_(A :|: C0 :|: Bbig),
        ptrace_cast3C disA_Bbig disC_Bbig tauACBbig = tauAC /\
        smooth_hmax B eps rhoAB <=
        hmax Bbig (ptrace_cast3B disAC disC_Bbig tauACBbig).
  { move=> tauAC HtauAC_ball.
    have [tauACBbig [Hmarg Hball_ABbig]] :=
      Hle_ABbig_ball tauAC HtauAC_ball.
    have Htarget_le :=
      @smooth_hmax_lb R L H (A :|: Bbig) Bbig
        eps rhoABbig (ptrace_cast3B disAC disC_Bbig tauACBbig)
        PrhoABbig HrhoABbig_tr Heps_pair_ABbig Hball_ABbig.
    exists tauACBbig; split=> //.
    exact: le_trans Hle_smooth_hmax_Bbig Htarget_le. }
  pose WAB_Cbig := (\1 : 'F[H]_(A :|: B)) \⊗ VC0_Cbig.
  have HrhoABCbig_lf_form :
      rhoABCbig_lf = WAB_Cbig \o rhoABC \o WAB_Cbig^A.
  { apply/h2mx_inj.
    rewrite HrhoABCbig_h2mx !h2mx_comp h2mx_adj.
    rewrite /WAB_Cbig h2mx_tenf h2mx1.
    rewrite !adjmxM adjmxK adjmx_tens adjmx1.
    rewrite /rhoAB_Cbig_mx /Cbig_embed /rhoAB_C_mx /UAB_C /UAB_Cbig
      /WC0_Cbig.
    rewrite adjmx_tens adjmx1.
    by rewrite !mulmxA. }
  pose WAC_Cbig := (\1 : 'F[H]_A) \⊗ VC0_Cbig.
  pose WAC_B := WAC_Cbig \⊗ (\1 : 'F[H]_B).
  have HrhoABCbig_acb_form :
      castlf (eqS_Cbig, eqS_Cbig) rhoABCbig_lf =
      WAC_B \o rhoABC_acb \o WAC_B^A.
  { rewrite HrhoABCbig_lf_form /rhoABC_acb /WAB_Cbig /WAC_B /WAC_Cbig.
    to_Fnd.
    rewrite -tenF11.
    by rewrite -!tenFA
      (tenFC (to_Fnd (\1 : 'F[H]_B)) (to_Fnd VC0_Cbig)) !tenFA. }
  have HrhoACbig_fixed_iso :
      @ptrace_cast3B R L H A B Cbig disAB disB_Cbig rhoABCbig_lf =
      WAC_Cbig \o rhoAC \o WAC_Cbig^A.
  { apply/h2mx_inj.
    rewrite HptB_recast_Cbig HrhoABCbig_acb_form.
    rewrite (h2mx_ptrace_cast_ptrace2 disACbig_B).
    rewrite !h2mx_comp h2mx_adj.
    rewrite (h2mx_tenf WAC_Cbig (\1 : 'F[H]_B)) h2mx1.
    rewrite adjmxM.
    set TACbig_B := @tenv_mxU R L H (A :|: Cbig) B.
    set WACmx := h2mx WAC_Cbig.
    set TAC_B := @tenv_mxU R L H (A :|: C0) B.
    have HTACbigK : TACbig_B^*t *m TACbig_B = 1%:M.
    { have /unitarymxK : TACbig_B^*t \is unitarymx
        := tenv_mxU_adj_unitarymx disACbig_B.
      by rewrite adjmxK. }
    rewrite -/TACbig_B -/WACmx -/TAC_B.
    rewrite adjmxK adjmxM.
    rewrite !mulmxA HTACbigK !mul1mx.
    rewrite -!mulmxA HTACbigK ?mulmx1 //.
    rewrite adjmx_tens adjmx1.
    transitivity
      (ptrace2
        ((WACmx *t (1%:M : 'M[C]_(dim 'H[H]_B))) *m
         (TAC_B^*t *m h2mx rhoABC_acb *m TAC_B) *m
         (WACmx^*t *t (1%:M : 'M[C]_(dim 'H[H]_B))))).
    { congr ptrace2.
      by rewrite !mulmxA. }
    rewrite ptrace2_tens_id_sandwich.
    rewrite /rhoAC_B_mx -/TAC_B in HrhoAC_B_ptr.
    rewrite HrhoAC_B_ptr.
    by rewrite h2mx_adj -/WACmx !mulmxA. }
  have Hsmooth_Cbig_iso :
      eps < Num.sqrt (@complex.Re R (\Tr rhoAC)) ->
      smooth_hminE Cbig eps
        (@ptrace_cast3B R L H A B Cbig
          disAB disB_Cbig rhoABCbig_lf) =
      smooth_hminE C0 eps rhoAC.
  { move=> Heps_lt.
    rewrite HrhoACbig_fixed_iso.
    have HIA_iso : (\1 : 'F[H]_A) \is isolf.
    { apply/isolfP. by rewrite adjf1 comp_lfun1l. }
    pose IA := IsoLf_Build HIA_iso.
    have HIA : (IA : 'F[H]_(A, A)) = \1
      by exact: IsoLf_BuildE HIA_iso.
    have HrhoAC_den : rhoAC \is denlf.
    { apply/denlfP; split=> //.
      have Hreal : \Tr rhoAC \is Num.real := ger0_real (psdlf_trlf PrhoAC).
      by rewrite -(RRe_real Hreal) lecR. }
    have Heps_pair : 0 <= eps < Num.sqrt (@complex.Re R (\Tr rhoAC))
      by rewrite Heps Heps_lt.
    have Hiso := @smooth_iso_hmin L H A C0 A Cbig
      disAC disA_Cbig disA_Cbig eps rhoAC IA VC0_Cbig
      HrhoAC_den Heps_pair.
    by move: Hiso; rewrite HIA -/WAC_Cbig. }
  (* TeX step 1: embed the purification register into a large enough C'. *)
  have Hge :
      (oppe (smooth_hminE C0 eps rhoAC) <=
       smooth_hmaxE B eps rhoAB)%E.
  {
    pose rhoACbig :=
      @ptrace_cast3B R L H A B Cbig disAB disB_Cbig rhoABCbig_lf.
    have PrhoACbig : rhoACbig \is psdlf.
    { rewrite /rhoACbig /ptrace_cast3B; exact: ptrace_cast_gen_psdlf. }
    have HrhoACbig_tr : @complex.Re R (\Tr rhoACbig) <= 1.
    { by rewrite /rhoACbig trlf_ptrace3B_Cbig. }
    have HrhoACbig_den : rhoACbig \is denlf.
    { apply/denlfP; split=> //.
      have Hreal : \Tr rhoACbig \is Num.real :=
        ger0_real (psdlf_trlf PrhoACbig).
      by rewrite -(RRe_real Hreal) lecR. }
    have HWAC_iso : WAC_Cbig \is isolf.
    { apply/isolfP.
      rewrite /WAC_Cbig tenf_adj -tenf_comp ?disAC //.
      by rewrite adjf1 comp_lfun1l isofE tenf11. }
    have HrhoACbig_tr_eq :
        @complex.Re R (\Tr rhoACbig) = @complex.Re R (\Tr rhoAC).
    { rewrite /rhoACbig HrhoACbig_fixed_iso lftraceC comp_lfunA.
      have /isolfP HWAC := HWAC_iso.
      by rewrite HWAC comp_lfun1l. }
    have Heps_pair_AB : 0 <= eps < Num.sqrt (@complex.Re R (\Tr rhoAB))
      by rewrite Heps Heps_lt_AB.
    have Heps_pair_ACbig :
        0 <= eps < Num.sqrt (@complex.Re R (\Tr rhoACbig))
      by rewrite Heps HrhoACbig_tr_eq Heps_lt_AC.
    rewrite /smooth_hmaxE leeNr.
    apply: ge_ereal_sup => v [tauAB [HtauAB_ball ->]].
    rewrite leeN2.
    have HtauAB_pos : 0 < @complex.Re R (\Tr tauAB)
      := eps_ball_trace_pos PrhoAB HrhoAB_tr Heps_pair_AB HtauAB_ball.
    have HtauAB_ne0 : tauAB != 0.
    { apply/eqP=> Htau0.
      by move: HtauAB_pos; rewrite Htau0 raddf0 raddf0 ltxx. }
    have [tauABCbig [Hmarg Hhmax Hball_ACbig]] :=
      Hge_ACbig_ball tauAB HtauAB_ball HtauAB_ne0.
    pose tauACbig :=
      @ptrace_cast3B R L H A B Cbig disAB disB_Cbig tauABCbig.
    have PtauAB : tauAB \is psdlf := eps_ball_psdlf HtauAB_ball.
    have HtauAB_tr : @complex.Re R (\Tr tauAB) <= 1
      := eps_ball_trlf HtauAB_ball.
    have Hhmax_fin :
        hmaxE B tauAB = (hmax B tauAB)%:E
      := @hmaxE_EFin R L H (A :|: B) B
           tauAB PtauAB HtauAB_tr HtauAB_pos.
    have PtauACbig : tauACbig \is psdlf := eps_ball_psdlf Hball_ACbig.
    have HtauACbig_tr : @complex.Re R (\Tr tauACbig) <= 1
      := eps_ball_trlf Hball_ACbig.
    have HtauACbig_pos : 0 < @complex.Re R (\Tr tauACbig)
      := eps_ball_trace_pos PrhoACbig HrhoACbig_tr
           Heps_pair_ACbig Hball_ACbig.
    have Hphi_tauACbig_pos : 0 < phi_min Cbig tauACbig
      := @phi_min_pos_trace R L H (A :|: Cbig) Cbig
           tauACbig PtauACbig HtauACbig_tr HtauACbig_pos.
    have Hhmin_fin :
        hminE Cbig tauACbig = (hmin Cbig tauACbig)%:E
      := @hminE_EFin R L H (A :|: Cbig) Cbig
           tauACbig Hphi_tauACbig_pos.
    have HdualE : hmaxE B tauAB = oppe (hminE Cbig tauACbig).
    { rewrite Hhmax_fin Hhmin_fin EFinN Hhmax.
      by rewrite EFinN. }
    rewrite HdualE leeN2.
    have Hball_le := @smooth_hmin_ball_ge_gen L H
      (A :|: Cbig) Cbig eps rhoACbig tauACbig
      HrhoACbig_den Heps_pair_ACbig Hball_ACbig.
    by move: Hball_le; rewrite /rhoACbig (Hsmooth_Cbig_iso Heps_lt_AC).
  }
  (* TeX step 2: embed the B register symmetrically and get the reverse bound. *)
  have Hle :
      (smooth_hmaxE B eps rhoAB <=
       oppe (smooth_hminE C0 eps rhoAC))%E.
  {
    have Heps_pair_AB : 0 <= eps < Num.sqrt (@complex.Re R (\Tr rhoAB))
      by rewrite Heps Heps_lt_AB.
    have Hsmooth_fin :
        smooth_hmaxE B eps rhoAB =
        (smooth_hmax B eps rhoAB)%:E
      := @smooth_hmaxE_EFin R L H (A :|: B) B
           eps rhoAB PrhoAB HrhoAB_tr Heps_pair_AB.
    rewrite /smooth_hminE leeNr.
    apply: ge_ereal_sup => v [tauAC [HtauAC_ball ->]].
    have Heps_pair_AC0 : 0 <= eps < Num.sqrt (@complex.Re R (\Tr rhoAC))
      by rewrite Heps Heps_lt_AC.
    have HtauAC_pos :=
      eps_ball_trace_pos PrhoAC HrhoAC_tr Heps_pair_AC0 HtauAC_ball.
    have HtauAC_ne0 : tauAC != 0.
    { apply/eqP=> H0.
      by move: HtauAC_pos; rewrite H0 raddf0 raddf0 ltxx. }
    have [tauACBbig [Hmarg Hdual Hball_ABbig Hmax_bound]] :=
      Hle_same_witness_dual_max tauAC HtauAC_ball HtauAC_ne0.
    pose tauABbig :=
      @ptrace_cast3B R L H A C0 Bbig disAC disC_Bbig tauACBbig.
    have PtauAC : tauAC \is psdlf := eps_ball_psdlf HtauAC_ball.
    have HtauAC_tr : @complex.Re R (\Tr tauAC) <= 1
      := eps_ball_trlf HtauAC_ball.
    have Hphi_tauAC_pos : 0 < phi_min C0 tauAC
      := @phi_min_pos_trace R L H (A :|: C0) C0
           tauAC PtauAC HtauAC_tr HtauAC_pos.
    have Hhmin_fin : hminE C0 tauAC = (hmin C0 tauAC)%:E
      := @hminE_EFin R L H (A :|: C0) C0 tauAC Hphi_tauAC_pos.
    have PtauABbig : tauABbig \is psdlf := eps_ball_psdlf Hball_ABbig.
    have HtauABbig_tr : @complex.Re R (\Tr tauABbig) <= 1
      := eps_ball_trlf Hball_ABbig.
    have HtauABbig_pos : 0 < @complex.Re R (\Tr tauABbig)
      := eps_ball_trace_pos PrhoABbig HrhoABbig_tr
           Heps_pair_ABbig Hball_ABbig.
    have Hhmax_fin :
        hmaxE Bbig tauABbig = (hmax Bbig tauABbig)%:E
      := @hmaxE_EFin R L H (A :|: Bbig) Bbig
           tauABbig PtauABbig HtauABbig_tr HtauABbig_pos.
    have HdualE : hmaxE Bbig tauABbig = oppe (hminE C0 tauAC).
    { rewrite Hhmax_fin Hhmin_fin EFinN /tauABbig Hdual.
      by rewrite EFinN. }
    have Hmax_boundE : (smooth_hmaxE B eps rhoAB <= hmaxE Bbig tauABbig)%E.
    { rewrite Hsmooth_fin Hhmax_fin lee_fin /tauABbig.
      exact: Hmax_bound. }
    rewrite leeNr -HdualE.
    exact: Hmax_boundE.
  }
  apply/eqP; rewrite eq_le.
  by apply/andP; split.
Qed.

Lemma smooth_dual_pure (rhoABC : 'F[H]_S_ABC) :
  rhoABC \is denlf ->
  \Rank rhoABC = 1%N ->
  smooth_hmaxE B 0
    (@ptrace_cast3C R L H A B C0 disAC disBC rhoABC) =
  oppe (smooth_hminE C0 0
    (@ptrace_cast3B R L H A B C0 disAB disBC rhoABC)).
Proof.
  move=> Hden Hrank.
  have Prho : rhoABC \is psdlf := denlf_psd Hden.
  have Hreal : \Tr rhoABC \is Num.real :=
    ger0_real (psdlf_trlf Prho).
  have Hnz : rhoABC != 0.
  { apply/eqP => H0.
    have : \Rank rhoABC = 0%N.
    { rewrite /lfrank; apply/eqP; rewrite mxrank_eq0.
      by rewrite H0 h2mx0. }
    by rewrite Hrank. }
  have Htr_real : (\Tr rhoABC : C) = (@complex.Re R (\Tr rhoABC))%:C.
    by rewrite RRe_real.
  have Htr_ge0 : 0 <= @complex.Re R (\Tr rhoABC).
  { by move: (psdlf_trlf Prho); rewrite Htr_real lecR. }
  have Htr_ne0 : @complex.Re R (\Tr rhoABC) != 0.
  { apply/eqP => Htr0.
    have Hge0 : 0 ⊑ rhoABC
      by move: Prho; rewrite psdlfE.
    have H0 : rhoABC == 0.
    { apply/trlf0_eq0.
      split=> //.
      by rewrite Htr_real Htr0. }
    by move/negP: Hnz; rewrite H0. }
  have Htr_pos : 0 < @complex.Re R (\Tr rhoABC).
    by rewrite lt0r Htr_ge0 Htr_ne0.
  have Heps : (0 : R) <= 0 < Num.sqrt (@complex.Re R (\Tr rhoABC)).
  { by rewrite lexx /= sqrtr_gt0. }
  exact: smooth_dual Hden Hrank Heps.
Qed.

End SmoothDual.

(* ================================================================== *)
(* Matrix↔labelled bridge for smooth min/max-entropy                    *)
(* ================================================================== *)
(* tex: no direct tex label — encoding-bridge infrastructure.            *)
(*                                                                        *)
(* A bipartite labelled state `rhoAB : 'F[H]_([set A] :|: [set B])` can  *)
(* be reshaped into a matrix `'M[C]_(dim 'H_A * dim 'H_B)` via `h2mx`    *)
(* + the dimension equation `dim 'H_(A :|: B) = dim 'H_A * dim 'H_B`    *)
(* (provided by `dirac/hstensor.v:tenv_dim` for disjoint A, B). The      *)
(* resulting matrix form is PSD ↔ PSD, has the same trace, and has the  *)
(* same smooth entropies as the labelled form: labelled `smooth_hmin`    *)
(* on `[set B]` equals matrix `smooth_hmin_mx` on the reshape, and       *)
(* analogously for `smooth_hmax`.                                         *)
(*                                                                        *)
(* The bridge proof carries `h2mx`/`mx2h` through eps-ball quantification *)
(* and the hmin/hmax inf/sup. Mechanically routine, structurally large. *)
(*                                                                        *)
(* Consumers:                                                             *)
(*   - `bb84/model.v:entropic_uncertainty_relation_bb84` restatement.    *)
(*   - `bb84/prop.v:stat` (labelled goal → matrix combinatorics).          *)
(* ================================================================== *)

(* Stinespring-dilated max-half data-processing support lives in dpi.v. *)

End FvqkdReal.

(* The forward isometry halves of `smooth_iso_hmin` and the
   `smooth_iso_hmax` helper `HhminE_iso_A` use `phi_min_v_iso_inv`
   (tb:Phi v, Φ-min isometry invariance) directly. The backward
   co-isometry halves use `phi_min_data_proc`. *)
