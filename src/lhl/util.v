(* -------------------------------------------------------------------- *)
(* util.v — LHL Hölder, collision, and CQ smoothing helpers             *)
(* -------------------------------------------------------------------- *)
(* Module: lhl.util                                       *)
(* Source: Tomamichel-Schaffner-Smith-Renner, 'Leftover Hashing       *)
(*   Against Quantum Side Information' (IEEE Trans. IT 57:5524 (2011);  *)
(*   arXiv:1002.2436): lemma:hoelder (Lem. 18), lemma:coll-bound       *)
(*   (Lem. 3, 1st stmt), lemma:cq-smoothing (Lem. 19).*)
(* -------------------------------------------------------------------- *)
(* The checked LHL route keeps theorem-facing definitions in def.v,       *)
(* post-hash mechanics in post_hash.v, and the reusable analytic/CQ       *)
(* helpers here: hoelder, min_coll_bound, cq_smoothing, Kbox_cq_decomp.  *)
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
From entropy Require Import def prop util.
From entropy.smooth Require Import dpi sm.
From lhl Require Import def dephase.
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
(* Hölder inequality for matrices                                      *)
(* Tomamichel-Schaffner-Smith-Renner, 'Leftover Hashing Against Quantum *)
(* Side Information' (IEEE Trans. IT 57:5524 (2011); arXiv:1002.2436),   *)
(* Lem. 18 — tex lemma:hoelder                                           *)
(* ================================================================== *)
(* Tomamichel-Schaffner-Smith-Renner, 'Leftover Hashing Against Quantum *)
(* Side Information' (IEEE Trans. IT 57:5524 (2011); arXiv:1002.2436),   *)
(* Lem. 18 — tex lemma:hoelder — 3-operator Schatten form               *)
(* math: ||A·B·C||_1 ≤ ||A||_{S_r} · ||B||_{S_s} · ||C||_{S_t}           *)
(*       for r,s,t > 0 with 1/r + 1/s + 1/t = 1.                         *)
(* Proof: reduce to the 2-operator schnorm_hoelder/schnorm_hoelder_gen    *)
(* via the conjugate index qr of r, writing 1/s + 1/t = 1/qr.             *)
(* path: lhl:hoelder -> lhl:uniform_collision_bound -> *)
(*   bb84:privacy_amplification -> bb84:bb84_secret *)
Lemma hoelder {m1 m2 m3 m4 : nat}
    (A : 'M[C]_(m1, m2)) (B : 'M[C]_(m2, m3)) (C0 : 'M[C]_(m3, m4))
    (r s t : R) :
  (0 < r)%R -> (0 < s)%R -> (0 < t)%R ->
  (r^-1 + s^-1 + t^-1 = 1)%R ->
  trnorm (A *m B *m C0) <= schnorm r A * schnorm s B * schnorm t C0.
Proof.
  move=> Hr Hs Ht Hrst; have Hs_ge0 : (0 <= s)%R by apply: ltW.
  have Ht_ge0 : (0 <= t)%R by apply: ltW.
  have HrstA : (r^-1 + (s^-1 + t^-1) = 1)%R by rewrite -addrA in Hrst.
  have Hst_inv_gt0 : (0 < s^-1 + t^-1)%R.
    by apply: addr_gt0; rewrite invr_gt0.
  have Hr_inv_lt1 : (r^-1 < 1)%R by rewrite -HrstA ltrDl.
  have Hr_gt1 : (1 < r)%R.
    by move: Hr_inv_lt1; rewrite -invf_lt1 // => ->.
  pose qr := conjugate_index Hr_gt1.
  have Hsu : (s^-1 + t^-1 = (qr : R)^-1)%R.
    have Htmp : (r^-1 + (s^-1 + t^-1) = r^-1 + (qr : R)^-1)%R
      by rewrite HrstA ((invfD_eq1 qr)).
    have Htmp' : ((s^-1 + t^-1) + r^-1 = (qr : R)^-1 + r^-1)%R
      by rewrite [LHS]addrC [RHS]addrC.
    by move: Htmp' => /addIr.
  rewrite -mulmxA.
  apply: (le_trans (@schnorm_hoelder R r qr m1 m2 m4 A (B *m C0))).
  rewrite -mulrA.
  apply: ler_wpM2l.
  - exact: schnorm_ge0.
  - apply: (@schnorm_hoelder_gen R s t (qr : R) m2 m3 m4 B C0).
    + exact: Hs_ge0.
    + exact: Ht_ge0.
    + apply/orP; right; exact: (ci_q_ge1 qr).
    + exact: Hsu.
Qed.
(* ================================================================== *)
(* Generalized-inverse square-root sandwich identity                    *)
(* ================================================================== *)
Section SandwichId.
Variable (L : finType) (HL : L -> chsType) (S : {set L}).
(* math: A · (√A)⁺ · A · (√A)⁺ = A for A ≥ 0 (generalized inverse on supp). *)
(* Collapses the subtracted 4-point term of `uniform_to_collision` and the   *)
(* δ-term of `privacy_amp` to a bare trace once the reference operator        *)
(* equals the OWN marginal — the situation in the almost-two-universal route. *)
(* Proof: with s := √A (psd, herm) and Π := s ∘ (√A)⁺ the cosupp projector    *)
(* (Hermitian by MP cond3, Π ∘ s = s by MP cond1), one gets A ∘ (√A)⁺ = s,    *)
(* hence the quadruple is (A ∘ (√A)⁺)∘(A ∘ (√A)⁺) = s ∘ s = A.                *)
(* infra: no tex label — fundamental & reusable (mathcomp-style)              *)
Lemma pinvlf_sqrtH_quad_id (A : 'F[HL]_S) :
  A \is psdlf ->
  A \o pinvlf (sqrtH A) \o A \o pinvlf (sqrtH A) = A.
Proof.
  move=> PA; set s := sqrtH A.
  have Ps : s \is psdlf by exact: sqrtH_psd.
  have HsK : s \o s = A by exact: sqrtHK.
  have Pp : pinvlf s \is psdlf by exact: pinvlf_psdlf Ps.
  have Hp_adj : (pinvlf s)^A = pinvlf s
    by apply: hermlf_adjE; apply: psdlf_herm Pp.
  have Hs_adj : s^A = s
    by apply: hermlf_adjE; apply: psdlf_herm Ps.
  have Hcond1 : s \o pinvlf s \o s = s.
    by have := pinvlf_MP_cond1 s; rewrite Hp_adj.
  have HPi_herm : (s \o pinvlf s)^A = s \o pinvlf s.
    by have := pinvlf_MP_cond3 s; rewrite Hp_adj.
  have HsPi : s \o (s \o pinvlf s) = s.
    have H1 : s \o (s \o pinvlf s) = ((s \o pinvlf s) \o s)^A
      by rewrite adjf_comp HPi_herm Hs_adj.
    by rewrite H1 Hcond1 Hs_adj.
  have HAp : A \o pinvlf s = s by rewrite -HsK -comp_lfunA HsPi.
  by rewrite -/s HAp -comp_lfunA HAp HsK.
Qed.
End SandwichId.
(* ================================================================== *)
(* Collision entropy and min-entropy bound                              *)
(* Tomamichel-Schaffner-Smith-Renner, 'Leftover Hashing Against Quantum *)
(* Side Information' (IEEE Trans. IT 57:5524 (2011); arXiv:1002.2436),   *)
(* Lem. 3 (1st stmt), Eq. 10 — tex lemma:coll-bound / eqn:min-coll-bound *)
(* note: tex lemma:min-coll-bound (Lem. 23, D_max form) is the          *)
(* technical helper used to prove this in the paper. The Coq statement  *)
(* below packages the collision-entropy consequence needed by LHL.      *)
(* ================================================================== *)
Section CollBound.
Variable (L : finType) (HL : L -> chsType) (X E : {set L}).
Hypothesis disXE : [disjoint X & E].
Notation S_XE := (X :|: E).
(* Tomamichel-Schaffner-Smith-Renner, 'Leftover Hashing Against Quantum   *)
(* Side Information' (IEEE Trans. IT 57:5524 (2011); arXiv:1002.2436),     *)
(* Lem. 3 (1st clause), Eq. 10 — tex lemma:coll-bound / eqn:min-coll-bound *)
(* (proof via lemma:min-coll-bound, Lem. 23)                               *)
(* math: For ρ ∈ S_sub(H_XE), ∃ σ_E ∈ S_=(H_E): Γ_C(ρ|σ_E) ≤ 2^{-Hmin(X|E)_ρ}. *)
(* Note: tex adds a CQ-state hypothesis on ρ, but the clause-1 *)
(* proof uses only lemma:min-coll-bound (Lem. 23) at the H_min            *)
(* optimizer, which does not require CQ — we therefore state it without.   *)
(* Sub-normalization (Re(Tr ρ) ≤ 1) is required: without it the bound is  *)
(* (Tr ρ)·2^{-Hmin}, not 2^{-Hmin}.                                        *)
(* Proof route: (i) phi_min_attained (entropy/conv/prop.v) gives feasible σ*  *)
(*   with I_X ⊗ σ* ≥ ρ and Tr σ* = phi_min ρ = 2^{-Hmin}; (ii) normalize   *)
(*   σ_E := σ*/phi_min (or any denlf if phi_min = 0 → ρ = 0); (iii) apply  *)
(*   the Γ_C-from-Loewner step (lemma:min-coll-bound, Lem. 23):            *)
(*   ρ ≤ c·(I⊗σ) ⇒ Γ_C(ρ|σ) ≤ c·Tr ρ; (iv) use Tr ρ ≤ 1.                *)
(* path: lhl:min_coll_bound -> bb84:privacy_amplification -> *)
(*   bb84:bb84_secret *)
Lemma min_coll_bound (rhoXE : 'F[HL]_S_XE) :
  rhoXE \is psdlf ->
  @complex.Re R (\Tr rhoXE) <= 1 ->
  exists (sigmaE : 'F[HL]_E),
    sigmaE \is denlf /\
    (supph (ptrace_castl disXE rhoXE) `<=` supph sigmaE)%HS /\
    collision_ent rhoXE sigmaE <= expR (- hmin E rhoXE * ln 2%:R).
Proof.
  move=> Prho Hrho_tr; pose rhoB := ptrace_castl disXE rhoXE.
  pose phi := phi_min E rhoXE.
  have Hsigma_exists :
      exists sigmaE : 'F[HL]_E,
        sigmaE \is denlf /\
        (supph rhoB `<=` supph sigmaE)%HS /\
        collision_ent rhoXE sigmaE <= phi.
  {
    have Hraw_feas : phi_min_feasible E rhoXE phi.
    {
      pose dX := dim 'H[HL]_X.
      pose dXR : R := dX%:R.
      pose dE := dim 'H[HL]_E.
      pose n := dim 'H[HL]_S_XE.
      pose rhoM : 'M[C]_n := h2mx rhoXE.
      have disEX : [disjoint E & X].
      {
        by rewrite disjoint_sym.
      }
      have eqEX : S_XE = (E :|: X).
      {
        by rewrite /S_XE finset.setUC.
      }
      have eqX0 : S_XE :\: E = X.
      {
        exact: setDU_r disXE.
      }
      have eqE0 : (S_XE :&: E) = E.
      {
        by setdec.
      }
      have eqLift0 :
          (S_XE :\: E) :|: E = S_XE.
      {
        by rewrite eqX0.
      }
      have eqLiftSig0 :
          (S_XE :\: E) :|: (S_XE :&: E) =
          (S_XE :\: E) :|: E.
      {
        by rewrite eqE0.
      }
      pose eqPhi0 :
          (S_XE :\: E) :|: (S_XE :&: E) = S_XE :=
        eq_ind_r (eq^~ S_XE)
          (eq_ind_r (eq^~ S_XE) (erefl S_XE) (finset.setID S_XE E))
          (finset.setUC (S_XE :\: E) (S_XE :&: E)).
      have phi_lift_term0 (sigmaE : 'F[HL]_E) :
          castlf (eqPhi0, eqPhi0)
            ((\1 : 'F[HL]_(S_XE :\: E)) \O
              castlf (esym eqE0, esym eqE0) sigmaE) =
          (\1 : 'F[HL]_X) \O sigmaE.
      {
        have -> : eqPhi0 = etrans eqLiftSig0 eqLift0.
        {
          apply: eq_irrelevance.
        }
        rewrite -castlf_comp.
        rewrite (@sdotIf_cast_r R _ _ (S_XE :\: E)
          (S_XE :&: E) E
          eqE0 eqLiftSig0
          (castlf (esym eqE0, esym eqE0) sigmaE)).
        have -> :
            castlf (eqE0, eqE0)
              (castlf (esym eqE0, esym eqE0) sigmaE) = sigmaE.
        {
          exact: castlfKV.
        }
        rewrite (@sdotIf_cast_l R _ _ (S_XE :\: E) X E
          eqX0 eqLift0
          (\1 : 'F[HL]_(S_XE :\: E)) sigmaE).
        have -> :
            castlf (eqX0, eqX0)
              (\1 : 'F[HL]_(S_XE :\: E)) =
            (\1 : 'F[HL]_X).
        {
          exact: castlf1.
        }
        done.
      }
      have phi_swap_term0 (sigmaE : 'F[HL]_E) :
          castlf (esym eqEX, esym eqEX)
            (sigmaE \⊗ (\1 : 'F[HL]_X)) =
          (\1 : 'F[HL]_X) \O sigmaE.
      {
        apply: to_Fnd_inj.
        rewrite Fnd_cast (sdotFT _ _ disXE) !to_Fnd_tenE.
        by rewrite tenFC.
      }
      pose rhoEX : 'F[HL]_(E :|: X) :=
        castlf (eqEX, eqEX) rhoXE.
      have PrhoEX : rhoEX \is psdlf.
      {
        by rewrite /rhoEX castlf_psdlfE.
      }
      pose sigmaW : 'F[HL]_E :=
        (dX%:R)%:C *: ptrace_cast disEX rhoEX.
      have PsigmaW : sigmaW \is psdlf.
      {
        rewrite /sigmaW.
        apply: psdlfZ.
        - by rewrite lecR.
        - exact: ptrace_cast_psdlf PrhoEX.
      }
      have HsigmaW_gap :
          ((((\1 : 'F[HL]_X) \O sigmaW) : 'F[HL]_S_XE) - rhoXE) \is psdlf.
      {
        pose domEX : 'F[HL]_(E :|: X) :=
          sigmaW \⊗ (\1 : 'F[HL]_X).
        have Hop := @op_bound R L HL E X disEX rhoEX PrhoEX.
        have Hop_psd : (domEX - rhoEX) \is psdlf.
        {
          have -> :
              domEX =
              (dX%:R) *:
                (ptrace_cast disEX rhoEX \⊗ (\1 : 'F[HL]_X)).
          {
            by rewrite /domEX /sigmaW -natrC tenfZl.
          }
          rewrite -lefE /dX.
          exact: Hop.
        }
        have Hop_psd' :
            (castlf (esym eqEX, esym eqEX) (domEX - rhoEX)) \is psdlf.
        {
          exact: castlf_psdlf Hop_psd.
        }
        move: Hop_psd'; rewrite castlf_sub.
        have -> : castlf (esym eqEX, esym eqEX) rhoEX = rhoXE.
        {
          by rewrite /rhoEX castlfK.
        }
        rewrite /domEX phi_swap_term0.
        done.
      }
      have Htr_ptrace_cast
          (f : 'F[HL]_(E :|: X)) :
          \Tr (ptrace_cast disEX f) = \Tr f.
      {
        rewrite /ptrace_cast /ptrace_cast_gen castlf_trlfE.
        have /cptpP [_ /tpmapP Htp] := @ptraceso_qc R L HL X (E :|: X).
        exact: Htp.
      }
      have HsigmaW_tr_le : @complex.Re R (\Tr sigmaW) <= dX%:R.
      {
        have Htr_rho_real : \Tr rhoXE \is Num.real.
        {
          exact: ger0_real (psdlf_trlf Prho).
        }
        have HRe_realM : forall (c : R) (z : C),
            @complex.Re R (c%:C * z) = c * @complex.Re R z.
        {
          move=> c z; case: z => a b /=.
          by rewrite mul0r subr0.
        }
        rewrite /sigmaW linearZ /= (Htr_ptrace_cast rhoEX) /rhoEX castlf_trlfE.
        rewrite (HRe_realM dX%:R (\Tr rhoXE)) -(RRe_real Htr_rho_real).
        have /(ler_wpM2l (ler0n _ dX)) := Hrho_tr.
        by rewrite mulr1.
      }
      pose lift_sigmaM (sigma : 'M[C]_dE) : 'M[C]_n :=
        h2mx ((((\1 : 'F[HL]_X) \O (mx2h sigma : 'F[HL]_E))
                : 'F[HL]_S_XE)).
      have lift_sigmaM_linear : linear lift_sigmaM.
      {
        move=> a x y; rewrite /lift_sigmaM (mx2hP a x y) /=.
        rewrite sdotfDr sdotfZr.
        by rewrite (h2mxP a _ _) /=.
      }
      pose FeasM :=
        [set sigma : 'M[C]_dE |
          sigma \is psdmx /\ \tr sigma <= dXR%:C /\
          lift_sigmaM sigma - rhoM \is psdmx]%classic.
      pose sigmaWM : 'M[C]_dE := h2mx sigmaW.
      have HsigmaWM_feas : FeasM sigmaWM.
      {
        split.
        - by move: PsigmaW; rewrite /sigmaWM qualifE.
        split.
        - have HsigmaWM_psd : sigmaWM \is psdmx.
          {
            by move: PsigmaW; rewrite /sigmaWM qualifE.
          }
          have Htr_sigmaWM_real : \tr sigmaWM \is Num.real.
          {
            exact: ger0_real (psdmx_trace HsigmaWM_psd).
          }
          have -> : \tr sigmaWM = (@complex.Re R (\tr sigmaWM))%:C.
          {
            exact: esym (RRe_real Htr_sigmaWM_real).
          }
          rewrite lecR /sigmaWM /lftrace.
          exact: HsigmaW_tr_le.
        - rewrite /sigmaWM /lift_sigmaM /rhoM h2mxK -raddfB /=.
          by move: HsigmaW_gap; rewrite qualifE.
      }
      have HFeasM_nonempty : (FeasM !=set0)%classic.
      {
        exists sigmaWM.
        exact: HsigmaWM_feas.
      }
      have HFeasM_sub :
          (FeasM `<=` [set sigma : 'M[C]_dE | mx_norm sigma <= dXR%:C])%classic.
      {
        move=> sigma [Hsigma_psd [Hsigma_tr _]]; have Hmx_i2 : `|sigma| <= i2norm sigma.
        {
          have Hi2_ge0 : 0 <= i2norm sigma.
          {
            exact: i2norm_ge0.
          }
          have -> : i2norm sigma = (NngNum Hi2_ge0)%:num.
          {
            reflexivity.
          }
          rewrite -mx_normEV /mx_norm num_le.
          apply/bigmax_leP => /=.
          split.
          - rewrite -num_le /=.
            exact: Hi2_ge0.
          - move=> ij _.
            move: (i2norm_elem sigma ij.1 ij.2); rewrite -num_le /= => Hij_le.
            exact: Hij_le.
        }
        apply: (le_trans Hmx_i2).
        apply: (le_trans (i2norm_trnorm sigma)).
        rewrite (psdmx_trnorm Hsigma_psd).
        exact: Hsigma_tr.
      }
      pose TraceSetM : set R :=
        [set v : R | exists sigma : 'M[C]_dE,
          FeasM sigma /\ v = @complex.Re R (\tr sigma)]%classic.
      have HTraceSetM_nonempty : (TraceSetM !=set0)%classic.
      {
        exists (@complex.Re R (\tr sigmaWM)).
        exists sigmaWM.
        by split.
      }
      have HTraceSetM_has_inf : has_inf TraceSetM.
      {
        split.
        - exact: HTraceSetM_nonempty.
        - exists 0 => v [sigma [Hsigma ->]].
          case: Hsigma => Hsigma_psd _.
          have Htr_real : \tr sigma \is Num.real.
          {
            exact: ger0_real (psdmx_trace Hsigma_psd).
          }
          move: (psdmx_trace Hsigma_psd); by rewrite -(RRe_real Htr_real) lecR.
      }
      pose epsn (k : nat) : R := 1 / (k.+1)%:R.
      have Hepsn_pos k : 0 < epsn k.
      {
        rewrite /epsn div1r invr_gt0.
        exact: ltr0Sn.
      }
      have Hex_sigma :
          forall k,
            exists sigma : 'M[C]_dE,
              FeasM sigma /\
              @complex.Re R (\tr sigma) < inf TraceSetM + epsn k.
      {
        move=> k; have [v Hv Hvlt] := inf_adherent (Hepsn_pos k) HTraceSetM_has_inf.
        case: Hv => sigma [Hsigma Hv].
        exists sigma.
        split=> //.
        by rewrite -Hv.
      }
      have [f Hf] := choice Hex_sigma.
      pose sigseq (k : nat) := f k.
      have Hbound_sigma : forall k, mx_norm (sigseq k) <= dXR%:C.
      {
        move=> k; exact: HFeasM_sub ((Hf k).1).
      }
      have [g [Hg Hcvg_sigma]] := ExtNumTopology.Bolzano_Weierstrass Hbound_sigma.
      pose sigseq0 (k : nat) := sigseq (g k).
      pose sigmaM0 := limn sigseq0.
      have Hcvg_sigseq0_to :
          (sigseq0 @ \oo --> sigmaM0)%classic.
      {
        by rewrite /sigseq0 /sigmaM0.
      }
      have Hsigseq0_cvgn : cvgn sigseq0.
      {
        by rewrite /sigseq0.
      }
      have HsigmaM0_psd : sigmaM0 \is psdmx.
      {
        have Hsigma_ge0 :
            lbounded_by (0 : 'M[C]_dE) (fun k => sigseq (g k)).
        {
          move=> k; move: (Hf (g k)).1.1.
          by rewrite le_lownerE subr0.
        }
        have HsigmaM0_ge0 : (0 : 'M[C]_dE) ⊑ sigmaM0.
        {
          exact: cmxlimn_ge Hcvg_sigma Hsigma_ge0.
        }
        by rewrite le_lownerE subr0 in HsigmaM0_ge0.
      }
      have HsigmaM0_tr : \tr sigmaM0 <= dXR%:C.
      {
        have Htrace_cvgn : cvgn (fun k => \tr (sigseq (g k))).
        {
          exact: is_cmxcvgn_trace Hcvg_sigma.
        }
        have Htrace_le : forall k, \tr (sigseq (g k)) <= dXR%:C.
        {
          move=> k; exact: (Hf (g k)).1.2.1.
        }
        move: (@climn_le R dXR%:C (fun k => \tr (sigseq (g k)))
                 Htrace_cvgn Htrace_le).
        rewrite (_ : (fun k => \tr (sigseq (g k))) =
                    ((@mxtrace C dE) \o (sigseq \o g))%FUN).
        - rewrite (cmxlimn_trace Hcvg_sigma).
          exact.
        - by apply/funext=> k.
      }
      have Hgap0_psd : lift_sigmaM sigmaM0 - rhoM \is psdmx.
      {
        have Hcvg_lift :
            ((fun k => lift_sigmaM (sigseq (g k))) @ \oo -->
             lift_sigmaM sigmaM0)%classic.
        {
          apply: cmxcvgn_lfun.
          - exact: lift_sigmaM_linear.
          - exact: Hcvg_sigma.
        }
        have Hcvg_gap :
            ((fun k => lift_sigmaM (sigseq (g k)) - rhoM) @ \oo -->
             lift_sigmaM sigmaM0 - rhoM)%classic.
        {
          apply: cmxcvgnB.
          - exact: Hcvg_lift.
          - exact: cvg_cst.
        }
        have Hclosed_psd : closed [set X : 'M[C]_n | X \is psdmx]%classic.
        {
          have -> :
              [set X : 'M[C]_n | X \is psdmx]%classic =
              [set X : 'M[C]_n | (0 : 'M[C]_n) <= X]%classic.
          {
            apply/funext=> Y /=.
            apply/propext; split.
            - move=> HY.
              by rewrite le_lownerE subr0.
            - move=> HY.
              by rewrite le_lownerE subr0 in HY.
          }
          exact: psdmx_closed n.
        }
        have Hnear_gap :
            \forall k \near eventually,
              [set X : 'M[C]_n | X \is psdmx]%classic
                (lift_sigmaM (sigseq (g k)) - rhoM).
        {
          by apply: nearW => k /=; exact: (Hf (g k)).1.2.2.
        }
        have Hclosed_gap :=
          @closed_cvg _ _ _ eventually_filter
            (fun k => lift_sigmaM (sigseq (g k)) - rhoM)
            [set X : 'M[C]_n | X \is psdmx]%classic
            Hclosed_psd Hnear_gap.
        exact: Hclosed_gap _ Hcvg_gap.
      }
      have Htrace0_eq_inf :
          @complex.Re R (\tr sigmaM0) = inf TraceSetM.
      {
        have HsigmaM0_feas : FeasM sigmaM0.
        {
          split.
          - exact: HsigmaM0_psd.
          - split.
            + exact: HsigmaM0_tr.
            + exact: Hgap0_psd.
        }
        have Htrace0_mem :
            TraceSetM (@complex.Re R (\tr sigmaM0)).
        {
          exists sigmaM0.
          by split.
        }
        have Htrace0_ge_inf : inf TraceSetM <= @complex.Re R (\tr sigmaM0).
        {
          have Hlb : lbound TraceSetM (inf TraceSetM).
          {
            exact: ge_inf HTraceSetM_has_inf.2.
          }
          exact: Hlb _ Htrace0_mem.
        }
        have Hcvg_trace0 :
            ((fun k => \tr (sigseq0 k)) @ \oo --> \tr sigmaM0)%classic.
        {
          have Htrace_cvgn : cvgn ((@mxtrace C dE) \o sigseq0).
          {
            exact: is_cmxcvgn_trace Hsigseq0_cvgn.
          }
          rewrite ccvgn_limnE; split.
          - rewrite (cmxlimn_trace Hsigseq0_cvgn).
            reflexivity.
          - rewrite (_ : (fun k => \tr (sigseq0 k)) =
                        ((@mxtrace C dE) \o sigseq0)%FUN).
            + exact: Htrace_cvgn.
            + by apply/funext=> k.
        }
        have Htrace_lt :
            forall k,
              @complex.Re R (\tr (sigseq0 k)) < inf TraceSetM + epsn (g k).
        {
          move=> k; exact: (Hf (g k)).2.
        }
        have Hupper_near :
            forall e : R, 0 < e ->
            \forall k \near \oo%classic,
              @complex.Re R (\tr sigmaM0) < inf TraceSetM + e.
        {
          move=> e He; have He2 : 0 < e / 2 by rewrite divr_gt0.
          have Hnear_trace :
              \forall t \near \oo%classic,
                `|@complex.Re R (\tr (sigseq0 t)) -
                  @complex.Re R (\tr sigmaM0)| < e / 2.
          {
            pose trace_fun := fun k : nat => @complex.Re R (\tr (sigseq0 k)).
            pose trace_lim := @complex.Re R (\tr sigmaM0).
            have Hdist_trace :
                forall e0 : R, 0 < e0 ->
                \forall t \near \oo%classic,
                  `|trace_lim - trace_fun t| < e0.
            {
              move=> e0 He0; have Hcvg_trace_fun := Re_cvgn_realV Hcvg_trace0.
              have Hdist_trace0 :=
                @cvgr_dist_lt R [the normedModType R of R^o]
                  nat \oo%classic _ trace_fun trace_lim Hcvg_trace_fun.
              exact: Hdist_trace0 _ He0.
            }
            move: (Hdist_trace _ He2); under eq_near do rewrite distrC.
            exact.
          }
          near=> k.
          have Htr_close :
              `|@complex.Re R (\tr (sigseq0 k)) -
                @complex.Re R (\tr sigmaM0)| < e / 2.
          {
            near: k.
            exact: Hnear_trace.
          }
          have Heps_small : epsn (g k) < e / 2.
          {
            have Hk_small : epsn k < e / 2.
            {
              rewrite /epsn div1r.
              near: k.
              exact: near_infty_natSinv_lt (PosNum He2).
            }
            have Hgk_ge_k : (g k >= k)%N.
            {
              exact: nchain_ge Hg k.
            }
            have Hinv_le :
                epsn (g k) <= epsn k.
            {
              rewrite /epsn !div1r lef_pV2.
              - rewrite ler_nat.
                rewrite -(leq_add2r 1%N) !addn1.
                exact: Hgk_ge_k.
              - by rewrite posrE ltr0Sn.
              - by rewrite posrE ltr0Sn.
            }
            exact: (le_lt_trans Hinv_le Hk_small).
          }
          have Htr_lt :
              @complex.Re R (\tr (sigseq0 k)) < inf TraceSetM + epsn (g k).
          {
            exact: Htrace_lt k.
          }
          have Hsig_lt :
              @complex.Re R (\tr sigmaM0) <
              @complex.Re R (\tr (sigseq0 k)) + e / 2.
          {
            exact: ltr_distlCDr Htr_close.
          }
          apply: (lt_trans Hsig_lt).
          have Hmid1 :
              @complex.Re R (\tr (sigseq0 k)) + e / 2 <
              inf TraceSetM + epsn (g k) + e / 2.
          {
            by rewrite (ltrD2r (e / 2)).
          }
          have Hmid2 :
              inf TraceSetM + epsn (g k) + e / 2 <
              inf TraceSetM + e.
          {
            rewrite -addrA.
            have Hinner :
                epsn (g k) + e / 2 < e.
            {
              have He_half : e - e / 2 = e / 2.
              {
                move: (congr1 (fun x => x - e / 2) (splitr e)); by rewrite -addrA subrr addr0.
              }
              rewrite -ltrBrDr He_half.
              exact: Heps_small.
            }
            rewrite (ltrD2l (inf TraceSetM)).
            exact: Hinner.
          }
          exact: (lt_trans Hmid1 Hmid2).
          Unshelve. end_near.
        }
        have Htrace0_le_inf : @complex.Re R (\tr sigmaM0) <= inf TraceSetM.
        {
          rewrite leNgt.
          apply/negP=> Hlt.
          pose e := (@complex.Re R (\tr sigmaM0) - inf TraceSetM) / 2.
          have He_pos : 0 < e.
          {
            rewrite /e divr_gt0.
            split.
            - by rewrite subr_gt0.
            - by rewrite ltr0n.
          }
          have Hnear := Hupper_near e He_pos.
          have Hineq : @complex.Re R (\tr sigmaM0) < inf TraceSetM + e.
          {
            move: Hnear; rewrite /prop_near1 nbhs_filterE => -[N _ HN].
            exact: (HN N (leqnn N)).
          }
          pose d := @complex.Re R (\tr sigmaM0) - inf TraceSetM.
          have Hd_pos : 0 < d.
          {
            by rewrite /d subr_gt0.
          }
          have Hd_half_lt : d / 2 < d.
          {
            have Htwo_pos : 0 < (2%:R : R).
            {
              by rewrite ltr0n.
            }
            have H2_unit : (2%:R : R) \is a GRing.unit.
            {
              exact: unitf_gt0 Htwo_pos.
            }
            rewrite -(ltr_pM2r Htwo_pos) (divrK H2_unit d) mulr_natr mulr2n.
            rewrite ltrDl.
            exact: Hd_pos.
          }
          have Hupper_lt : inf TraceSetM + e < @complex.Re R (\tr sigmaM0).
          {
            have Hbase : e < d.
            {
              rewrite /e /d.
              exact: Hd_half_lt.
            }
            have Hrhs : inf TraceSetM + e < inf TraceSetM + d.
            {
              exact: (ler_ltD (lexx (inf TraceSetM)) Hbase).
            }
            have -> : @complex.Re R (\tr sigmaM0) = inf TraceSetM + d.
            {
              by rewrite /d addrC subrK.
            }
            exact: Hrhs.
          }
          have : @complex.Re R (\tr sigmaM0) < @complex.Re R (\tr sigmaM0).
          {
            exact: (lt_trans Hineq Hupper_lt).
          }
          by rewrite ltxx.
        }
        apply/eqP; rewrite eq_le; apply/andP; split.
        - exact: Htrace0_le_inf.
        - exact: Htrace0_ge_inf.
      }
      have HtraceW_le_dX :
          @complex.Re R (\tr sigmaWM) <= dX%:R.
      {
        by rewrite /sigmaWM /lftrace.
      }
      have HtraceW_mem :
          TraceSetM (@complex.Re R (\tr sigmaWM)).
      {
        exists sigmaWM.
        by split.
      }
      have Hmatrix_gap_labelled (sigmaM : 'M[C]_dE) :
          lift_sigmaM sigmaM - rhoM \is psdmx ->
          ((((\1 : 'F[HL]_X) \O (mx2h sigmaM : 'F[HL]_E))
              : 'F[HL]_S_XE) - rhoXE) \is psdlf.
      {
        move=> HgapM; rewrite qualifE.
        have -> :
            h2mx ((((\1 : 'F[HL]_X) \O
                      (mx2h sigmaM : 'F[HL]_E))
                     : 'F[HL]_S_XE) - rhoXE) =
            h2mx (((\1 : 'F[HL]_X) \O
                     (mx2h sigmaM : 'F[HL]_E))) - h2mx rhoXE.
        {
          by rewrite raddfB.
        }
        rewrite /lift_sigmaM /rhoM.
        exact: HgapM.
      }
      have HFeasM_to_phi v sigmaM :
          FeasM sigmaM ->
          v = @complex.Re R (\tr sigmaM) ->
          phi_min_feasible E rhoXE v.
      {
        move=> HsigmaM Htrv; case: HsigmaM => HsigmaM_psd [HsigmaM_tr HgapM].
        pose sigma0 : 'F[HL]_E := mx2h sigmaM.
        pose sigma_raw : 'F[HL]_(S_XE :&: E) :=
          castlf (esym eqE0, esym eqE0) sigma0.
        exists sigma_raw; split.
        - by rewrite /sigma_raw /sigma0 castlf_psdlfE qualifE mx2hK.
        - split.
          + have -> :
                (castlf (eqPhi0, eqPhi0)
                  ((\1 : 'F[HL]_(S_XE :\: E)) \O sigma_raw) - rhoXE) =
                ((((\1 : 'F[HL]_X) \O sigma0) : 'F[HL]_S_XE) - rhoXE).
            {
              congr (_ - rhoXE).
              rewrite /sigma_raw.
              exact: phi_lift_term0 sigma0.
            }
            exact: Hmatrix_gap_labelled HgapM.
          + rewrite /sigma_raw castlf_trlfE /sigma0 /lftrace /= mx2hK.
            exact: Htrv.
      }
      have Hphi_to_TraceSetM v :
          phi_min_feasible E rhoXE v ->
          v <= dX%:R ->
          TraceSetM v.
      {
        move=> [sigma_raw [Psig_raw [Hgap_raw Htrv]]] Hv_le.
        pose sigma0 : 'F[HL]_E := castlf (eqE0, eqE0) sigma_raw.
        pose sigmaM : 'M[C]_dE := h2mx sigma0.
        have PsigmaM : sigmaM \is psdmx.
        {
          have Psigma0 : sigma0 \is psdlf.
          {
            by rewrite /sigma0 castlf_psdlfE.
          }
          by move: Psigma0; rewrite /sigmaM qualifE.
        }
        have Hgap0_labelled' :
            ((((\1 : 'F[HL]_X) \O sigma0) : 'F[HL]_S_XE) - rhoXE) \is psdlf.
        {
          move: Hgap_raw.
          have -> :
              sigma_raw = castlf (esym eqE0, esym eqE0) sigma0.
          {
            by rewrite /sigma0 castlfK.
          }
          have -> :
              castlf (eqPhi0, eqPhi0)
                ((\1 : 'F[HL]_(S_XE :\: E)) \O
                  castlf (esym eqE0, esym eqE0) sigma0) =
              ((((\1 : 'F[HL]_X) \O sigma0) : 'F[HL]_S_XE)).
          {
            exact: phi_lift_term0 sigma0.
          }
          done.
        }
        have HgapM : lift_sigmaM sigmaM - rhoM \is psdmx.
        {
          move: Hgap0_labelled'; rewrite qualifE.
          have -> :
              h2mx ((((\1 : 'F[HL]_X) \O sigma0) : 'F[HL]_S_XE) - rhoXE) =
              h2mx (((\1 : 'F[HL]_X) \O sigma0)) - h2mx rhoXE.
          {
            by rewrite raddfB.
          }
          rewrite /sigmaM /lift_sigmaM /rhoM h2mxK.
          done.
        }
        have Htr_sigmaM_eq : @complex.Re R (\tr sigmaM) = v.
        {
          rewrite /sigmaM /sigma0.
          change (@complex.Re R (\Tr (castlf (eqE0, eqE0) sigma_raw)) = v).
          by rewrite castlf_trlfE Htrv.
        }
        have Htr_sigmaM_le : \tr sigmaM <= dXR%:C.
        {
          have Htr_sigmaM_real : \tr sigmaM \is Num.real.
          {
            exact: ger0_real (psdmx_trace PsigmaM).
          }
          have -> : \tr sigmaM = (@complex.Re R (\tr sigmaM))%:C.
          {
            exact: esym (RRe_real Htr_sigmaM_real).
          }
          rewrite lecR Htr_sigmaM_eq.
          exact: Hv_le.
        }
        exists sigmaM; split.
        - split.
          + exact: PsigmaM.
          + split.
            * exact: Htr_sigmaM_le.
            * exact: HgapM.
        - exact: esym Htr_sigmaM_eq.
      }
      have Hphi_eq_inf : phi = inf TraceSetM.
      {
        pose PhiSet := [set v : R | phi_min_feasible E rhoXE v]%classic.
        have HPhiSet_nonempty : (PhiSet !=set0)%classic.
        {
          exists (@complex.Re R (\tr sigmaWM)).
          exact: HFeasM_to_phi HsigmaWM_feas erefl.
        }
        have HPhiSet_has_inf : has_inf PhiSet.
        {
          split.
          - exact: HPhiSet_nonempty.
          - exists 0 => v [sigma_raw [Psig_raw [_ ->]]].
            by have := psdlf_trlf Psig_raw; rewrite lecE /= => /andP[_].
        }
        have Hphi_lb_trace : lbound TraceSetM phi.
        {
          move=> v Hv; have Hvphi : PhiSet v.
          {
            case: Hv => sigmaM [HsigmaM Htrv].
            exact: HFeasM_to_phi HsigmaM Htrv.
          }
          rewrite /phi /phi_min /PhiSet.
          apply: ge_inf=> //.
          exists 0 => w [sigma_raw [Psig_raw [_ ->]]].
          by have := psdlf_trlf Psig_raw; rewrite lecE /= => /andP[_].
        }
        have Hphi_le_inf : phi <= inf TraceSetM.
        {
          exact: lb_le_inf HTraceSetM_nonempty Hphi_lb_trace.
        }
        have Hphi_le_dX : phi <= dX%:R.
        {
          have Hphi_sigmaW : PhiSet (@complex.Re R (\tr sigmaWM)).
          {
            exact: HFeasM_to_phi HsigmaWM_feas erefl.
          }
          have Hphi_le_sigmaW : phi <= @complex.Re R (\tr sigmaWM).
          {
            rewrite /phi /phi_min /PhiSet.
            apply: ge_inf=> //.
            exists 0 => w [sigma_raw [Psig_raw [_ ->]]].
            by have := psdlf_trlf Psig_raw; rewrite lecE /= => /andP[_].
          }
          exact: le_trans Hphi_le_sigmaW HtraceW_le_dX.
        }
        have Hinf_le_phi : inf TraceSetM <= phi.
        {
          rewrite leNgt.
          apply/negP=> Hlt.
          pose e := (inf TraceSetM - phi) / 2.
          have He_pos : 0 < e.
          {
            rewrite /e divr_gt0.
            split.
            - by rewrite subr_gt0.
            - by rewrite ltr0n.
          }
          have [v Hvphi Hvlt] := inf_adherent He_pos HPhiSet_has_inf.
          have [w [HwTrace Hwlt]] :
              exists w, TraceSetM w /\ w < phi + e.
          {
            case: (lerP v dX%:R) => [Hv_le_dX | Hv_gt_dX].
            - exists v; split.
              + exact: Hphi_to_TraceSetM Hvphi Hv_le_dX.
              + exact: Hvlt.
            - exists (@complex.Re R (\tr sigmaWM)); split.
              + exact: HtraceW_mem.
              + apply: (le_lt_trans HtraceW_le_dX).
                exact: lt_trans Hv_gt_dX Hvlt.
          }
          have Hinf_lt : inf TraceSetM < phi + e.
          {
            exact: le_lt_trans (ge_inf HTraceSetM_has_inf.2 HwTrace) Hwlt.
          }
          pose d := inf TraceSetM - phi.
          have Hd_pos : 0 < d.
          {
            by rewrite /d subr_gt0.
          }
          have Hd_half_lt : d / 2 < d.
          {
            have Htwo_pos : 0 < (2%:R : R).
            {
              by rewrite ltr0n.
            }
            have H2_unit : (2%:R : R) \is a GRing.unit.
            {
              exact: unitf_gt0 Htwo_pos.
            }
            rewrite -(ltr_pM2r Htwo_pos) (divrK H2_unit d) mulr_natr mulr2n.
            rewrite ltrDl.
            exact: Hd_pos.
          }
          have Hupper_lt : phi + e < inf TraceSetM.
          {
            have Hbase : e < d.
            {
              rewrite /e /d.
              exact: Hd_half_lt.
            }
            have Hrhs : phi + e < phi + d.
            {
              exact: (ler_ltD (lexx phi) Hbase).
            }
            have -> : inf TraceSetM = phi + d.
            {
              by rewrite /d addrC subrK.
            }
            exact: Hrhs.
          }
          have : inf TraceSetM < inf TraceSetM.
          {
            exact: (lt_trans Hinf_lt Hupper_lt).
          }
          by rewrite ltxx.
        }
        apply/eqP; rewrite eq_le; apply/andP; split.
        - exact: Hphi_le_inf.
        - exact: Hinf_le_phi.
      }
      pose sigma0 : 'F[HL]_E := mx2h sigmaM0.
      pose sigma_raw0 : 'F[HL]_(S_XE :&: E) :=
        castlf (esym eqE0, esym eqE0) sigma0.
      have Psigma0 : sigma0 \is psdlf.
      {
        by rewrite /sigma0 qualifE mx2hK.
      }
      have Hgap0_labelled :
          ((((\1 : 'F[HL]_X) \O sigma0) : 'F[HL]_S_XE) - rhoXE) \is psdlf.
      {
        exact: Hmatrix_gap_labelled Hgap0_psd.
      }
      have Hsigma0_tr :
          @complex.Re R (\Tr sigma0) = inf TraceSetM.
      {
        by rewrite /sigma0 /lftrace /= mx2hK Htrace0_eq_inf.
      }
      exists sigma_raw0; split.
      - by rewrite /sigma_raw0 castlf_psdlfE.
      split.
      - have Hgap_raw_eq :
            (castlf (eqPhi0, eqPhi0)
              ((\1 : 'F[HL]_(S_XE :\: E)) \O sigma_raw0) - rhoXE) \is psdlf.
        {
          suff -> :
              (castlf (eqPhi0, eqPhi0)
                ((\1 : 'F[HL]_(S_XE :\: E)) \O sigma_raw0) - rhoXE) =
              ((((\1 : 'F[HL]_X) \O sigma0) : 'F[HL]_S_XE) - rhoXE).
          {
            exact: Hgap0_labelled.
          }
          congr (_ - rhoXE).
          exact: phi_lift_term0 sigma0.
        }
        exact: Hgap_raw_eq.
      - rewrite /sigma_raw0 castlf_trlfE.
        by rewrite Hsigma0_tr -Hphi_eq_inf.
    }
    case: Hraw_feas => sigma_raw [Psig_raw [Hfeas_raw Htr_raw]].
    have eqX : S_XE :\: E = X.
    {
      exact: setDU_r disXE.
    }
    have eqE : (S_XE :&: E) = E.
    {
      by setdec.
    }
    have eqLift :
        (S_XE :\: E) :|: E = S_XE.
    {
      by rewrite eqX.
    }
    have eqLiftSig :
        (S_XE :\: E) :|: (S_XE :&: E) =
        (S_XE :\: E) :|: E.
    {
      by rewrite eqE.
    }
    pose eqPhi :
        (S_XE :\: E) :|: (S_XE :&: E) = S_XE :=
      eq_ind_r (eq^~ S_XE)
        (eq_ind_r (eq^~ S_XE) (erefl S_XE) (finset.setID S_XE E))
        (finset.setUC (S_XE :\: E) (S_XE :&: E)).
    pose sigma0 : 'F[HL]_E := castlf (eqE, eqE) sigma_raw.
    have Psig0 : sigma0 \is psdlf.
    {
      by rewrite /sigma0 castlf_psdlfE.
    }
    have Htr_sigma0 : phi = @complex.Re R (\Tr sigma0).
    {
      by rewrite /sigma0 castlf_trlfE Htr_raw.
    }
    have Hfeas0 :
        (((\1 : 'F_X) \O sigma0 : 'F[HL]_S_XE) - rhoXE) \is psdlf.
    {
      have Hfeas_raw_eq :
          (castlf (eqPhi, eqPhi)
            ((\1 : 'F[HL]_(S_XE :\: E)) \O sigma_raw) - rhoXE) \is psdlf.
      {
        exact: Hfeas_raw.
      }
      suff -> :
          (((\1 : 'F_X) \O sigma0 : 'F[HL]_S_XE) - rhoXE) =
          (castlf (eqPhi, eqPhi)
            ((\1 : 'F[HL]_(S_XE :\: E)) \O sigma_raw) - rhoXE).
      {
        exact: Hfeas_raw_eq.
      }
      congr (_ - rhoXE).
      have -> : eqPhi = etrans eqLiftSig eqLift.
      {
        apply: eq_irrelevance.
      }
      rewrite -castlf_comp.
      rewrite (@sdotIf_cast_r R _ _ (S_XE :\: E)
        (S_XE :&: E) E
        eqE eqLiftSig sigma_raw).
      rewrite (@sdotIf_cast_l R _ _ (S_XE :\: E) X E
        eqX eqLift
        (\1 : 'F[HL]_(S_XE :\: E))
        (castlf (eqE, eqE) sigma_raw)).
      have -> :
          castlf (eqX, eqX)
            (\1 : 'F[HL]_(S_XE :\: E)) =
          (\1 : 'F_X).
      {
        exact: castlf1.
      }
      by rewrite /sigma0.
    }
    have Hsupp0 : (supph rhoB `<=` supph sigma0)%HS.
    {
      have PrhoB : rhoB \is psdlf.
      {
        exact: ptrace_castl_psdlf Prho.
      }
      have Hptr_psd :
          ptrace_castl disXE
            ((((\1 : 'F_X) \O sigma0 : 'F[HL]_S_XE) - rhoXE)) \is psdlf.
      {
        exact: ptrace_castl_psdlf Hfeas0.
      }
        have HordB :
            rhoB <= ptrace_castl disXE
              (((\1 : 'F_X) \O sigma0 : 'F[HL]_S_XE)).
        {
          have HptrB :
              ptrace_castl disXE
                (((\1 : 'F_X) \O sigma0 : 'F[HL]_S_XE) - rhoXE) =
              ptrace_castl disXE
                (((\1 : 'F_X) \O sigma0 : 'F[HL]_S_XE)) -
              ptrace_castl disXE rhoXE.
          {
            rewrite /ptrace_castl /ptrace_cast_gen.
            set aXE := ((\1 : 'F_X) \O sigma0 : 'F[HL]_S_XE).
            have HtrB : \Tr_(X) (aXE - rhoXE) =
                \Tr_(X) aXE - \Tr_(X) rhoXE.
            {
              have HlinTr := superop_is_linear (@ptraceso R L HL X S_XE).
              have Htr := HlinTr (-1 : C) rhoXE aXE.
              rewrite !scaleN1r in Htr.
              rewrite [aXE - rhoXE]addrC
                [\Tr_(X) aXE - \Tr_(X) rhoXE]addrC.
              exact: Htr.
            }
            by rewrite HtrB castlf_sub.
          }
          rewrite lefE.
          by rewrite /rhoB -HptrB.
        }
      have Hlift_ptr :
          ptrace_castl disXE
            (((\1 : 'F_X) \O sigma0 : 'F[HL]_S_XE)) =
          (dim 'H[HL]_X)%:R%:C *: sigma0.
      {
        exact: ptrace_castl_sdot_I disXE sigma0.
      }
      have HordB_scaled :
          rhoB <= (dim 'H[HL]_X)%:R%:C *: sigma0.
      {
        by rewrite -Hlift_ptr.
      }
      have HordB_scaled' :
          ((PsdLf_Build PrhoB)%:VF) <=
          (dim 'H[HL]_X)%:R%:C *: sigma0.
      {
        rewrite -(PsdLf_BuildE PrhoB).
        exact: HordB_scaled.
      }
      have Hsupp_scaled :
          (supph ((PsdLf_Build PrhoB)%:VF) `<=`
           supph ((dim 'H[HL]_X)%:R%:C *: sigma0))%HS.
      {
        exact: supph_lef HordB_scaled'.
      }
      have Hsupp_sigma :
          supph ((dim 'H[HL]_X)%:R%:C *: sigma0) = supph sigma0.
      {
        have HdimX_neq0 : ((dim 'H[HL]_X)%:R != 0 :> R).
        {
          by rewrite pnatr_eq0 -lt0n dim_proper.
        }
        rewrite supphZ.
        - done.
        - by rewrite realc_eq0 HdimX_neq0.
      }
      rewrite -(PsdLf_BuildE PrhoB) Hsupp_sigma in Hsupp_scaled.
      exact: Hsupp_scaled.
    }
    have Hraw_coll : collision_ent rhoXE sigma0 <= 1.
    {
      pose P : 'F[HL]_E := pinvlf (sqrtH sigma0).
      pose M : 'F[HL]_S_XE := (\1 : 'F_X) \O P.
      pose Q : 'F[HL]_E := supplf (sqrtH sigma0).
      pose Xmid : 'F[HL]_S_XE := M \o rhoXE \o M.
      have HP_psd : P \is psdlf.
      {
        exact: pinvlf_psdlf (sqrtH_psd Psig0).
      }
      have HP_herm : P^A = P.
      {
        exact: hermlf_adjE (psdlf_herm HP_psd).
      }
      have Hsqrt_herm : (sqrtH sigma0)^A = sqrtH sigma0.
      {
        exact: hermlf_adjE (sqrtH_herm (psdlf_herm Psig0)).
      }
      have HQ_proj : Q \is projlf.
      {
        exact: supplf_proj (sqrtH sigma0).
      }
      have /projlfP [HQ_herm HQ_id] := HQ_proj.
      have HM_herm : M^A = M.
      {
        by rewrite /M sdot_I_adj HP_herm.
      }
      have HPsqrt : P \o sqrtH sigma0 = Q.
      {
        by rewrite /Q /supplf HP_herm.
      }
      have HsqrtP : sqrtH sigma0 \o P = Q.
      {
        apply: adjf_inj.
        by rewrite adjf_comp HP_herm Hsqrt_herm HQ_herm HPsqrt.
      }
      have Hsand_sigma : P \o sigma0 \o P = Q.
      {
        have -> : P \o sigma0 \o P =
            P \o (sqrtH sigma0 \o sqrtH sigma0) \o P.
        {
          by rewrite (sqrtHK Psig0).
        }
        rewrite comp_lfunA HPsqrt.
        by rewrite -comp_lfunA HsqrtP HQ_id.
      }
      have HQ_le1 : Q <= (\1 : 'F[HL]_E).
      {
        have HQ_bound1 : Q \is bound1lf.
        {
          exact: projlf_bound1 HQ_proj.
        }
        have HQ_formV : Q \o Q^A <= (\1 : 'F[HL]_E).
        {
          by rewrite -bound1lf_formV_le1.
        }
        by rewrite HQ_herm HQ_id in HQ_formV.
      }
      have HQlift_proj : (((\1 : 'F_X) \O Q : 'F[HL]_S_XE)) \is projlf.
      {
        apply/projlfP; split.
        - by rewrite sdot_I_adj HQ_herm.
        - by rewrite sdotI_comp HQ_id.
      }
      have HQlift_le1 :
          (((\1 : 'F_X) \O Q : 'F[HL]_S_XE) <= (\1 : 'F[HL]_S_XE)).
      {
        have HQlift_bound1 :
            (((\1 : 'F_X) \O Q : 'F[HL]_S_XE)) \is bound1lf.
        {
          exact: projlf_bound1 HQlift_proj.
        }
        have HQlift_formV :
            (((\1 : 'F_X) \O Q : 'F[HL]_S_XE) \o
             ((\1 : 'F_X) \O Q : 'F[HL]_S_XE)^A <=
             (\1 : 'F[HL]_S_XE)).
        {
          by rewrite -bound1lf_formV_le1.
        }
        by rewrite sdot_I_adj HQ_herm sdotI_comp HQ_id in HQlift_formV.
      }
      have Hfeas_le : rhoXE <= (((\1 : 'F_X) \O sigma0 : 'F[HL]_S_XE)).
      {
        by move: Hfeas0; rewrite -lefE.
      }
      have HXmid_leQ : Xmid <= (((\1 : 'F_X) \O Q : 'F[HL]_S_XE)).
      {
        move: (formlf_lef M Hfeas_le); rewrite !formlfE HM_herm /Xmid /M !sdotI_comp Hsand_sigma.
        done.
      }
      have HXmid_le1 : Xmid <= (\1 : 'F[HL]_S_XE).
      {
        exact: le_trans HXmid_leQ HQlift_le1.
      }
      have H1mX_psd : ((\1 : 'F[HL]_S_XE) - Xmid) \is psdlf.
      {
        by move: HXmid_le1; rewrite -lefE.
      }
      pose Srho : 'F[HL]_S_XE := sqrtH rhoXE.
      have Hsqrt_rho_herm : Srho^A = Srho.
      {
        rewrite /Srho.
        exact: hermlf_adjE (sqrtH_herm (psdlf_herm Prho)).
      }
      have Hsqrt_rhoK : Srho \o Srho = rhoXE.
      {
        rewrite /Srho.
        exact: sqrtHK Prho.
      }
        have HSsand_le : Srho \o Xmid \o Srho <= rhoXE.
        {
          move: (lef_formV Srho HXmid_le1); by rewrite Hsqrt_rho_herm comp_lfun1r Hsqrt_rhoK.
        }
      have HXtrace_eq : \Tr (Srho \o Xmid \o Srho) = \Tr (Xmid \o rhoXE).
      {
        transitivity (\Tr ((Xmid \o Srho) \o Srho)).
        {
          by rewrite -comp_lfunA lftraceC.
        }
        by rewrite -comp_lfunA Hsqrt_rhoK.
      }
      have HXtrace_le :
          @complex.Re R (\Tr (Xmid \o rhoXE)) <= @complex.Re R (\Tr rhoXE).
      {
        move: (lef_trlf HSsand_le); rewrite -HXtrace_eq.
        rewrite lecE /= => /andP[_].
        done.
      }
      have -> : collision_ent rhoXE sigma0 =
          @complex.Re R (\Tr (Xmid \o rhoXE)).
      {
        rewrite /collision_ent /Xmid /M /P /=.
        done.
      }
      exact: le_trans HXtrace_le Hrho_tr.
    }
    case: (eqVneq phi 0) => [Hphi0|Hphi0].
    - pose omegaE : 'F[HL]_E :=
        (((dim 'H[HL]_E)%:R)^-1)%:C *: (\1 : 'F[HL]_E).
      have Homega_den : omegaE \is denlf.
      {
        apply/denlfP; split.
        - rewrite /omegaE.
          apply: psdlfZ.
          + by rewrite lecR invr_ge0 ler0n.
          + by rewrite qualifE h2mx1; apply: psdmx1.
        - have HdimE_neq0 : ((dim 'H[HL]_E)%:R : R) != 0.
          {
            by rewrite pnatr_eq0 -lt0n dim_proper.
          }
          have Homega_tr1 : \Tr omegaE = 1.
          {
            rewrite /omegaE linearZ /= /lftrace h2mx1 mxtrace1 -natrC -realcM.
            by rewrite mulrC mulfV.
          }
          by rewrite Homega_tr1.
      }
      have Hrho0 : rhoXE = 0.
      {
        have Hsigma0_tr0 : \Tr sigma0 = 0.
        {
          rewrite -(RRe_real (ger0_real (psdlf_trlf Psig0))) -Htr_sigma0 Hphi0.
            by rewrite rmorph0.
        }
        have Hsigma0_eq0 : sigma0 = 0.
        {
          apply/eqP/trlf0_eq0; split.
          - by move: Psig0; rewrite psdlfE.
          - exact: Hsigma0_tr0.
        }
        have Hneg_rho_psd : (- rhoXE) \is psdlf.
        {
          move: Hfeas0; by rewrite Hsigma0_eq0 sdotf0 sub0r.
        }
        have Hrho_tr_ge0 : 0 <= @complex.Re R (\Tr rhoXE).
        {
          by move: (psdlf_trlf Prho); rewrite lecE /= => /andP[_].
        }
        have Hrho_tr_le0 : @complex.Re R (\Tr rhoXE) <= 0.
        {
          have Htmp : 0 <= - @complex.Re R (\Tr rhoXE).
          {
            move: (psdlf_trlf Hneg_rho_psd); rewrite lecE /=.
            move=> /andP[_ Htmp].
              have HnegRe
                : @complex.Re R (\Tr (- rhoXE))
                    = - @complex.Re R (\Tr rhoXE).
              {
                have HtrN : \Tr (- rhoXE) = - \Tr rhoXE.
          {
            have HlinTr := @lftrace_is_linear R ('H[HL]_S_XE).
            have Htr := HlinTr (-1 : C) rhoXE 0.
            rewrite !scaleN1r !mulN1r linear0 !addr0 in Htr.
            exact: Htr.
          }
                rewrite HtrN.
                exact: raddfN.
              }
            rewrite -HnegRe.
            exact: Htmp.
          }
          rewrite -lerN2 oppr0.
          exact: Htmp.
        }
        have Hrho_tr0R : @complex.Re R (\Tr rhoXE) = 0.
        {
          apply/eqP.
          by rewrite eq_le Hrho_tr_le0 Hrho_tr_ge0.
        }
        have Htr_rho0 : \Tr rhoXE = 0.
        {
          have Htr_rho_real : \Tr rhoXE \is Num.real.
          {
            exact: ger0_real (psdlf_trlf Prho).
          }
          rewrite -(RRe_real Htr_rho_real) Hrho_tr0R.
          by rewrite rmorph0.
        }
        apply/eqP/trlf0_eq0; split.
        - by move: Prho; rewrite psdlfE.
        - exact: Htr_rho0.
      }
      have Hsupp_omega : (supph rhoB `<=` supph omegaE)%HS.
      {
        have HrhoB0 : rhoB = 0.
        {
          have PrhoB : rhoB \is psdlf.
          {
            rewrite /rhoB /ptrace_castl.
            apply: (@ptrace_cast_gen_psdlf R L HL S_XE E X
                      (setDU_l disXE) rhoXE).
            exact: Prho.
          }
          apply/eqP/trlf0_eq0; split.
          - by move: PrhoB; rewrite psdlfE.
          - by rewrite /rhoB trlf_ptrace_castl Hrho0 linear0.
        }
        rewrite HrhoB0 supph0.
        exact: le0h.
      }
      have Hcoll_omega : collision_ent rhoXE omegaE <= phi.
      {
        rewrite Hphi0 Hrho0 /collision_ent /=.
        by rewrite !comp_lfun0r linear0 raddf0.
      }
      exists omegaE; split=> //; split=> //.
    - have Hphi_ge0 : 0 <= phi.
      {
        rewrite Htr_sigma0.
        move: (psdlf_trlf Psig0); by rewrite lecE /= => /andP[_].
      }
      have Hphi_pos : 0 < phi.
      {
        by rewrite lt_def Hphi_ge0 Hphi0.
      }
      pose sigmaE : 'F[HL]_E := (phi^-1)%:C *: sigma0.
      have HsigmaE_den : sigmaE \is denlf.
      {
        apply/denlfP; split.
        - rewrite /sigmaE.
          apply: psdlfZ.
          + by rewrite lecR invr_ge0 ltW.
          + exact: Psig0.
        - have Htr_sigma0_real :
              (\Tr sigma0 : C) = (@complex.Re R (\Tr sigma0))%:C.
          {
            by rewrite RRe_real // ger0_real // psdlf_trlf.
          }
          have Hphi_unit : phi \is a GRing.unit := unitf_gt0 Hphi_pos.
          have HsigmaE_tr1 : \Tr sigmaE = 1.
          {
            rewrite /sigmaE linearZ /= Htr_sigma0_real -realcM.
            have -> : phi^-1 * complex.Re (\Tr sigma0) = 1.
            {
              by rewrite -Htr_sigma0 mulVf.
            }
            done.
          }
          rewrite HsigmaE_tr1.
          exact: lexx.
      }
      have HsuppE : (supph rhoB `<=` supph sigmaE)%HS.
      {
        rewrite /sigmaE supphZ.
        - exact: Hsupp0.
        - by rewrite fmorph_eq0 invr_eq0 Hphi0.
      }
      have HcollE : collision_ent rhoXE sigmaE <= phi.
      {
        pose c : R := (phi^-1)%R.
        pose P0 : 'F[HL]_E := pinvlf (sqrtH sigma0).
        pose M0 : 'F[HL]_S_XE := (\1 : 'F_X) \O P0.
        pose aR : R := ((Num.sqrt c)^-1)%R.
        have Hc_ge0 : 0 <= c.
        {
          by rewrite /c invr_ge0 ltW.
        }
        have Hc_pos : 0 < c.
        {
          by rewrite /c invr_gt0.
        }
        have Hsqrt_sigmaE :
            sqrtH sigmaE = (Num.sqrt c)%:C *: sqrtH sigma0.
        {
          rewrite /sigmaE /c.
          exact: sqrtHZ_nn Hc_ge0 Psig0.
        }
        have Hsqrtc_neq0 : Num.sqrt c != 0.
        {
          apply: lt0r_neq0.
          by rewrite sqrtr_gt0.
        }
        have Hsqrt_sq : (Num.sqrt c * Num.sqrt c = c :> R).
        {
          by rewrite -expr2 sqr_sqrtr.
        }
        have Hpinv_sigmaE :
            pinvlf (sqrtH sigmaE) = (aR%:C) *: P0.
        {
          rewrite Hsqrt_sigmaE /aR (pinvlfZ_nn _ Hsqrtc_neq0).
          by rewrite /c.
        }
        have Hscale_pull :
            ((aR%:C *: M0) \o rhoXE \o (aR%:C *: M0) \o rhoXE) =
            (aR%:C * aR%:C) *:
              (M0 \o rhoXE \o M0 \o rhoXE).
        {
          rewrite -comp_lfunZl.
          rewrite -comp_lfunZl.
          rewrite -comp_lfunZl -comp_lfunZr.
          rewrite -comp_lfunZl.
          by rewrite scalerA.
        }
        have ReCmul : forall (r : R) (z : C),
            @complex.Re R (r%:C * z) = r * @complex.Re R z.
        {
          by move=> r [x y] /=; rewrite mul0r subr0.
        }
        have Ha2 : aR * aR = phi.
        {
          rewrite /aR.
          rewrite -[(Num.sqrt c)^-1 * (Num.sqrt c)^-1]expr2 exprVn //.
          rewrite sqr_sqrtr; last exact: Hc_ge0.
          by rewrite /c invrK.
        }
        rewrite /collision_ent /= Hpinv_sigmaE sdotfZr.
        rewrite Hscale_pull linearZ /= -realcM ReCmul Ha2.
        have Hphi_mul := ler_wpM2l (ltW Hphi_pos) Hraw_coll.
        by rewrite mulr1 in Hphi_mul.
      }
      exists sigmaE; split=> //; split=> //.
  }
  have Hphi_exp :
      phi <= expR (- hmin E rhoXE * ln 2%:R).
  {
    case: (lerP phi 0) => Hphi_le0.
    - apply: (le_trans Hphi_le0).
      exact: (ltW (expR_gt0 _)).
    - have Hphi_pos : 0 < phi := Hphi_le0.
      have Hln2_unit : ln 2%:R \is a GRing.unit := unitf_gt0 (@ln2_gt0 R).
      rewrite /phi /hmin /log2.
      have -> :
          - (- (ln (phi_min E rhoXE) / ln 2%:R)) * ln 2%:R =
          (ln (phi_min E rhoXE) / ln 2%:R) * ln 2%:R.
      {
        by rewrite opprK.
      }
      rewrite (divrK Hln2_unit (ln (phi_min E rhoXE))).
      by rewrite (lnK Hphi_pos).
  }
  case: Hsigma_exists => sigmaE [Hden [Hsupp Hcoll]].
  exists sigmaE; split=> //; split=> //.
  exact: (le_trans Hcoll Hphi_exp).
Qed.
(* Tomamichel-Schaffner-Smith-Renner, 'Leftover Hashing Against Quantum     *)
(* Side Information' (IEEE Trans. IT 57:5524 (2011); arXiv:1002.2436),       *)
(* Lem. 19 — tex lemma:cq-smoothing                                          *)
(* math: For ρ ∈ S_sub(H_XE) CQ, ∃ τ ∈ B^ε(ρ) CQ with H_min(X|E)_τ         *)
(*       = H^ε_min(X|E)_ρ.                                                  *)
(* Note: tex requires ρ ∈ subnormstates (Tr ρ ≤ 1) since the ε-ball *)
(* is only well-defined for subnormalized endpoints under pur_dist.         *)
(* Donor: Tomamichel's `smoothing_support_hmin` (entropy/smooth/sm.v) gives a    *)
(* general smoothing witness with support preservation; we dephase via the  *)
(* X-register to force CQ (idempotent on CQ inputs, preserves ε-ball by     *)
(* pur-dist DPI, preserves H_min via `dephase_X_hmin_preserve`).            *)
(* path: lhl:cq_smoothing -> bb84:privacy_amplification -> *)
(*   bb84:bb84_secret *)
Lemma cq_smoothing (eps : R) (rhoXE : 'F[HL]_S_XE) :
    rhoXE \is psdlf ->
    @complex.Re R (\Tr rhoXE) <= 1 ->
    0 <= eps ->
    eps < Num.sqrt (@complex.Re R (\Tr rhoXE)) ->
    is_cq_state rhoXE ->
  exists (tauXE : 'F[HL]_S_XE),
    eps_ball eps rhoXE tauXE /\
    is_cq_state tauXE /\
    smooth_hminE E eps rhoXE = hminE E tauXE.
Proof.
    move=> Prho Hrho_tr Heps Heps_lt HrhoCQ.
  have Hzero_psd : (0 : 'F[HL]_S_XE) \is psdlf.
    by rewrite qualifE h2mx0 psdmx0.
  have Hzero_tr : @complex.Re R (\Tr (0 : 'F[HL]_S_XE)) <= 1.
    by rewrite linear0 raddf0 ler01.
  have Hpd_zero_eq :
      forall tau : 'F[HL]_S_XE,
        tau \is psdlf ->
        @complex.Re R (\Tr tau) <= 1 ->
        pur_dist (0 : 'F[HL]_S_XE) tau = Num.sqrt (@complex.Re R (\Tr tau)).
  {
    move=> tau Ptau Htau_tr; have Hzero_mx_psd : h2mx (0 : 'F[HL]_S_XE) \is psdmx.
    {
      by move: Hzero_psd; rewrite qualifE.
    }
    have Htau_mx_psd : h2mx tau \is psdmx.
    {
      by move: Ptau; rewrite qualifE.
    }
    have Hgfid0 :
        gfid (0 : 'F[HL]_S_XE) tau =
        Num.sqrt (1 - @complex.Re R (\Tr tau)).
    {
      rewrite /gfid (alt_gfid_gen Hzero_mx_psd Htau_mx_psd).
      have -> :
          @complex.Re R
            (trnorm (sqrtmx (h2mx (0 : 'F[HL]_S_XE)) *m sqrtmx (h2mx tau))) = 0.
        {
          by rewrite h2mx0 sqrtmx0 mul0mx trnorm0 raddf0.
        }
      have -> :
          @complex.Re R (1 - \tr (h2mx (0 : 'F[HL]_S_XE))) = 1.
        {
          by rewrite h2mx0 mxtrace0 subr0.
        }
      have -> :
          @complex.Re R (1 - \tr (h2mx tau)) =
          1 - @complex.Re R (\Tr tau).
      {
        by rewrite raddfB /= /lftrace.
      }
      by rewrite sqrtr1 mul1r add0r.
    }
    rewrite /pur_dist.
    pose a := 1 - @complex.Re R (\Tr tau).
    have Ha_ge0 : 0 <= a.
    {
      rewrite /a.
      by rewrite subr_ge0.
    }
    have -> :
        (gfid (0 : 'F[HL]_S_XE) tau)^2 = a.
    {
      rewrite Hgfid0.
      exact: sqr_sqrtr Ha_ge0.
    }
    by rewrite /a opprB addrCA subrr addr0.
  }
  have Hphi0 : phi_min E (0 : 'F[HL]_S_XE) = 0.
  {
    pose E0 : set R := fun v : R =>
      phi_min_feasible E (0 : 'F[HL]_S_XE) v.
    have Hne0 : nonempty E0.
    {
      exists 0.
      rewrite /E0 /phi_min_feasible.
      exists (0 : 'F[HL]_(S_XE :&: E)).
      split.
      - by rewrite psdlfE lexx.
      - split.
        + by rewrite sdotf0 linear0 subrr.
        + by rewrite linear0.
    }
    have Hlb0 : lbound E0 0.
    {
      move=> v; rewrite /E0 => -[sigma [Psigma [_ ->]]].
      have := psdlf_trlf Psigma.
      by rewrite lecE /= => /andP[].
    }
    have Hhas_lb0 : has_lbound E0.
    {
      by exists 0.
    }
    have Hmem0 : E0 0.
    {
      rewrite /E0 /phi_min_feasible.
      exists (0 : 'F[HL]_(S_XE :&: E)).
      split.
      - by rewrite psdlfE lexx.
      - split.
        + by rewrite sdotf0 linear0 subrr.
        + by rewrite linear0.
    }
    rewrite /phi_min.
    apply/eqP; rewrite eq_le.
    apply/andP; split.
    - exact: (ge_inf Hhas_lb0 Hmem0).
    - exact: (lb_le_inf Hne0 Hlb0).
  }
  have [Hsmall | Hlarge] :=
      ltP eps (Num.sqrt (@complex.Re R (\Tr rhoXE))).
  - have Hsmall_range :
        0 <= eps < Num.sqrt (@complex.Re R (\Tr rhoXE)).
    {
      by apply/andP; split.
    }
    have Hrho_den : rhoXE \is denlf.
    { apply/denlfP; split=> //.
      have Hreal : \Tr rhoXE \is Num.real := ger0_real (psdlf_trlf Prho).
      by rewrite -(RRe_real Hreal) lecR. }
    have Htau0_data :=
      @smoothing_support_hmin R L HL X E disXE eps rhoXE
        Hrho_den Hsmall_range.
    case: Htau0_data => tau0 [Htau0_ball [Htau0_opt [_ _]]].
    pose DX := (@dephase_X_so R L HL X E).
    pose tau1 := DX tau0.
    have Hball_trace_pos :
        forall tau : 'F[HL]_S_XE, eps_ball eps rhoXE tau ->
          0 < @complex.Re R (\Tr tau).
    {
      move=> tau Hb; have Ptau : tau \is psdlf := eps_ball_psdlf Hb.
      have Htau_tr : @complex.Re R (\Tr tau) <= 1 := eps_ball_trlf Hb.
      have Htau_pd : pur_dist tau rhoXE <= eps.
      {
        move: Hb; by rewrite /eps_ball => /andP [/andP [_ _] Hpd].
      }
      have Hrho_zero := Hpd_zero_eq rhoXE Prho Hrho_tr.
      have Htau_zero := Hpd_zero_eq tau Ptau Htau_tr.
      have Hgap_pos : 0 < Num.sqrt (@complex.Re R (\Tr rhoXE)) - eps.
      {
        by rewrite subr_gt0.
      }
      have Hsqrt_le :
          Num.sqrt (@complex.Re R (\Tr rhoXE)) <=
          Num.sqrt (@complex.Re R (\Tr tau)) + eps.
      {
        rewrite -Hrho_zero -Htau_zero.
        have Htri := @pd_metric_triangle R L HL S_XE
          (0 : 'F[HL]_S_XE) rhoXE tau
          Hzero_psd Prho Ptau Hzero_tr Hrho_tr Htau_tr.
        have Hstep :
            pur_dist (0 : 'F[HL]_S_XE) tau + pur_dist tau rhoXE <=
            pur_dist (0 : 'F[HL]_S_XE) tau + eps.
        {
          apply: lerD.
          - exact: lexx.
          - exact: Htau_pd.
        }
        exact: le_trans Htri Hstep.
      }
      have Hgap_le :
          Num.sqrt (@complex.Re R (\Tr rhoXE)) - eps <=
          Num.sqrt (@complex.Re R (\Tr tau)).
      {
        move: Hsqrt_le; by rewrite lerBlDr addrC.
      }
      have Htau_sqrt_pos : 0 < Num.sqrt (@complex.Re R (\Tr tau)).
      {
        exact: lt_le_trans Hgap_pos Hgap_le.
      }
      by rewrite -sqrtr_gt0.
    }
    have eqXE_diff : S_XE :\: E = X.
    {
      exact: setDU_r disXE.
    }
    have eqXE_cond : S_XE :&: E = E.
    {
      by setdec.
    }
    have eqXE_lift :
        (S_XE :\: E) :|: E = S_XE.
    {
      by rewrite eqXE_diff.
    }
    have eqXE_lift_sig :
        (S_XE :\: E) :|: (S_XE :&: E) =
        (S_XE :\: E) :|: E.
    {
      by rewrite eqXE_cond.
    }
    have eqXE_phi :
        (S_XE :\: E) :|: (S_XE :&: E) = S_XE.
    {
      by rewrite finset.setUC finset.setID.
    }
    have phi_lift_term (sigmaE : 'F[HL]_E) :
        castlf (eqXE_phi, eqXE_phi)
          ((\1 : 'F[HL]_(S_XE :\: E)) \O
            castlf (esym eqXE_cond, esym eqXE_cond) sigmaE) =
        (\1 : 'F[HL]_X) \O sigmaE.
    {
      have -> : eqXE_phi = etrans eqXE_lift_sig eqXE_lift.
      {
        apply: eq_irrelevance.
      }
      rewrite -castlf_comp.
      rewrite (@sdotIf_cast_r R _ _ (S_XE :\: E)
        (S_XE :&: E) E
        eqXE_cond eqXE_lift_sig
        (castlf (esym eqXE_cond, esym eqXE_cond) sigmaE)).
      have -> :
          castlf (eqXE_cond, eqXE_cond)
            (castlf (esym eqXE_cond, esym eqXE_cond) sigmaE) = sigmaE.
      {
        exact: castlfKV.
      }
      rewrite (@sdotIf_cast_l R _ _ (S_XE :\: E) X E
        eqXE_diff eqXE_lift
        (\1 : 'F[HL]_(S_XE :\: E)) sigmaE).
      have -> :
          castlf (eqXE_diff, eqXE_diff)
            (\1 : 'F[HL]_(S_XE :\: E)) =
          (\1 : 'F[HL]_X).
      {
        exact: castlf1.
      }
      done.
    }
    have psdlf_le_tr_id_local :
        forall (S : {set L}) (f : 'F[HL]_S),
          f \is psdlf ->
          f <= (@complex.Re R (\Tr f))%:C *: (\1 : 'F[HL]_S).
    {
      move=> S f Pf; have Htr_real : \Tr f \is Num.real := ger0_real (psdlf_trlf Pf).
      rewrite lef_h2mx.
      have -> :
          h2mx ((@complex.Re R (\Tr f))%:C *: (\1 : 'F[HL]_S)) =
          (\tr (h2mx f))%:M.
      {
        rewrite h2mxZ_lf /= h2mx1 /lftrace (RRe_real Htr_real) scalemx1.
        done.
      }
      apply: lemx_psd_ub.
      by rewrite qualifE.
    }
    have Hphi_trace_lb :
        forall tau : 'F[HL]_S_XE,
          tau \is psdlf ->
          @complex.Re R (\Tr tau) <= 1 ->
          @complex.Re R (\Tr tau) / (dim 'H[HL]_X)%:R <=
            phi_min E tau.
    {
      move=> tau Ptau Htau_tr; have Htr_tau_real : \Tr tau \is Num.real.
      {
        exact: ger0_real (psdlf_trlf Ptau).
      }
      apply: lb_le_inf.
      - pose sigmaE := (@complex.Re R (\Tr tau))%:C *:
                       (\1 : 'F[HL]_E).
        pose sigma0 : 'F[HL]_(S_XE :&: E) :=
          castlf (esym eqXE_cond, esym eqXE_cond) sigmaE.
        exists (@complex.Re R (\Tr sigma0)).
        exists sigma0.
        split.
        + rewrite /sigma0 /sigmaE castlf_psdlfE.
          apply: psdlfZ.
          * by rewrite lecE /= eqxx; move: (psdlf_trlf Ptau); rewrite lecE /= => /andP[].
          * by apply/gef0_psd; exact: lef01.
        + split.
          * have Hlift_one :
                ((\1 : 'F[HL]_X) \O (\1 : 'F[HL]_E)
                  : 'F[HL]_S_XE) = (\1 : 'F[HL]_S_XE).
            {
              apply: to_Fnd_inj.
              by rewrite (sdotFT _ _ disXE) -!to_FndEV tenf11.
            }
            match goal with
            | |- context[castlf (?p, ?p) _] =>
                have -> : p = eqXE_phi by apply: eq_irrelevance
            end.
            rewrite /sigma0 phi_lift_term /sigmaE sdotfZr Hlift_one.
            apply: psdlf_le_tr_id_local.
            exact: Ptau.
          * done.
      - move=> v [sigma [Psigma [Hfeas ->]]].
        have Htr_sigma_real : (\Tr sigma : C) =
            (@complex.Re R (\Tr sigma))%:C.
        {
          by rewrite RRe_real // ger0_real // psdlf_trlf.
        }
        have Htau_leR :
            @complex.Re R (\Tr tau) <=
            (dim 'H[HL]_X)%:R * @complex.Re R (\Tr sigma).
        {
          have [p0 Hfeas0] :
              exists p0 :
                (S_XE :\: E) :|: (S_XE :&: E) = S_XE,
                (castlf (p0, p0)
                  ((\1 : 'F[HL]_(S_XE :\: E)) \O sigma) - tau)
                \is psdlf.
          {
            match type of Hfeas with
            | context[castlf (?p, ?p) _] => exists p
            end.
            exact: Hfeas.
          }
          pose gap :=
            castlf (p0, p0)
              ((\1 : 'F[HL]_(S_XE :\: E)) \O sigma).
          have Hp0_eq : p0 = eqXE_phi by apply: eq_irrelevance.
          have Htau_leC :
              \Tr tau <= \Tr gap.
          {
            have Hle : tau ⊑ gap.
            {
              rewrite /gap lefE.
              exact: Hfeas0.
            }
            exact: lef_trlf Hle.
          }
          rewrite -(RRe_real Htr_tau_real) in Htau_leC.
          have Hcast :
              \Tr gap =
              ((dim 'H[HL]_X)%:R * @complex.Re R (\Tr sigma))%:C.
          {
            rewrite /gap Hp0_eq castlf_trlfE.
            have disSplit :
                [disjoint (S_XE :\: E) & (S_XE :&: E)].
            {
              setdec.
            }
            rewrite (trlf_lift_I disSplit) Htr_sigma_real -natrC -realcM.
            by rewrite eqXE_diff re_realid.
          }
          rewrite Hcast in Htau_leC.
          by move: Htau_leC; rewrite lecR.
        }
        rewrite ler_pdivrMr; last by rewrite ltr0n dim_proper.
        by rewrite mulrC.
    }
    have HhminE_fin_on_ball :
        forall tau : 'F[HL]_S_XE, eps_ball eps rhoXE tau ->
          hminE E tau = (hmin E tau)%:E.
    {
      move=> tau Htau_ball; have Ptau : tau \is psdlf := eps_ball_psdlf Htau_ball.
      have Htau_tr : @complex.Re R (\Tr tau) <= 1 := eps_ball_trlf Htau_ball.
      have Htau_pos : 0 < @complex.Re R (\Tr tau).
      {
        exact: Hball_trace_pos Htau_ball.
      }
      have Hphi_lb :
          @complex.Re R (\Tr tau) / (dim 'H[HL]_X)%:R <=
          phi_min E tau.
      {
        exact: Hphi_trace_lb Ptau Htau_tr.
      }
      have Hphi_pos : 0 < phi_min E tau.
      {
        have Htau_dim_pos :
            0 < @complex.Re R (\Tr tau) / (dim 'H[HL]_X)%:R.
        {
          apply: divr_gt0.
          - exact: Htau_pos.
          - by rewrite ltr0n dim_proper.
        }
        exact: lt_le_trans Htau_dim_pos Hphi_lb.
      }
      rewrite /hminE /hmin (elog2_gt0 Hphi_pos).
      by rewrite EFinN.
    }
    pose Sreal : set R := fun v : R =>
      exists tauS : 'F[HL]_S_XE,
        eps_ball eps rhoXE tauS /\ v = hmin E tauS.
    have Hreal_has_ub :
        has_ubound Sreal.
    {
      pose dX : R := (dim 'H[HL]_X)%:R.
      pose gap := Num.sqrt (@complex.Re R (\Tr rhoXE)) - eps.
      pose alpha := gap ^+ 2.
      exists (- log2 (alpha / dX)).
      apply/ubP => v.
      rewrite /Sreal => -[tau [Htau_ball ->]].
      have Ptau : tau \is psdlf := eps_ball_psdlf Htau_ball.
      have Htau_tr : @complex.Re R (\Tr tau) <= 1 := eps_ball_trlf Htau_ball.
      have Htau_tr_ge0 : 0 <= @complex.Re R (\Tr tau).
      {
        have := psdlf_trlf Ptau.
        by rewrite lecE /= => /andP[].
      }
      have Htau_pd : pur_dist tau rhoXE <= eps.
      {
        move: Htau_ball; by rewrite /eps_ball => /andP [/andP [_ _] Hpd].
      }
      have Hgap_pos : 0 < gap.
      {
        rewrite /gap.
        by rewrite subr_gt0.
      }
      have Hrho_zero := Hpd_zero_eq rhoXE Prho Hrho_tr.
      have Htau_zero := Hpd_zero_eq tau Ptau Htau_tr.
      have Hsqrt_le :
          Num.sqrt (@complex.Re R (\Tr rhoXE)) <=
          Num.sqrt (@complex.Re R (\Tr tau)) + eps.
      {
        rewrite -Hrho_zero -Htau_zero.
        have Htri := @pd_metric_triangle R L HL S_XE
          (0 : 'F[HL]_S_XE) rhoXE tau
          Hzero_psd Prho Ptau Hzero_tr Hrho_tr Htau_tr.
        have Hstep :
            pur_dist (0 : 'F[HL]_S_XE) tau + pur_dist tau rhoXE <=
            pur_dist (0 : 'F[HL]_S_XE) tau + eps.
        {
          apply: lerD.
          - exact: lexx.
          - exact: Htau_pd.
        }
        exact: le_trans Htri Hstep.
      }
      have Hgap_le :
          gap <= Num.sqrt (@complex.Re R (\Tr tau)).
      {
        move: Hsqrt_le; by rewrite /gap lerBlDr addrC.
      }
      have Halpha_le :
          alpha <= @complex.Re R (\Tr tau).
      {
        have Hsq_le :
            gap ^+ 2 <= (Num.sqrt (@complex.Re R (\Tr tau))) ^+ 2.
        {
          pose s := Num.sqrt (@complex.Re R (\Tr tau)).
          have Hgap_le2 : gap <= s by exact: Hgap_le.
          have Hsq_le' : gap * gap <= s * s.
          {
            exact: ler_pM (ltW Hgap_pos) (ltW Hgap_pos) Hgap_le Hgap_le2.
          }
          move: Hsq_le'; by rewrite /s !expr2.
        }
        move: Hsq_le; rewrite /alpha /gap.
        by rewrite sqr_sqrtr.
      }
      have Hdiv_le :
          alpha / dX <= @complex.Re R (\Tr tau) / dX.
      {
        have HdXinv : 0 < (dX^-1)%R.
        {
          rewrite /dX invr_gt0 ltr0n.
          exact: dim_proper.
        }
        have Hmul :
            alpha * dX^-1 <= @complex.Re R (\Tr tau) * dX^-1.
        {
          rewrite ler_pM2r; last exact: HdXinv.
          exact: Halpha_le.
        }
        exact: Hmul.
      }
      have Hphi_lb :
          @complex.Re R (\Tr tau) / dX <= phi_min E tau.
      {
        exact: Hphi_trace_lb Ptau Htau_tr.
      }
      have Hphi_ge :
          alpha / dX <= phi_min E tau.
      {
        exact: le_trans Hdiv_le Hphi_lb.
      }
      have Halpha_pos : 0 < alpha / dX.
      {
        apply: divr_gt0.
        - rewrite /alpha.
          by rewrite exprn_gt0.
        - by rewrite /dX ltr0n dim_proper.
      }
      rewrite /hmin.
      have Hlog_le :
          log2 (alpha / dX) <= log2 (phi_min E tau).
      {
        exact: log2_le_pos Halpha_pos Hphi_ge.
      }
      move: Hlog_le; by rewrite /dX /alpha /gap lerNl opprK.
    }
    have Htau0_ubE :
        forall tau : 'F[HL]_S_XE, eps_ball eps rhoXE tau ->
          (hminE E tau <= hminE E tau0)%E.
    {
      move=> tau Htau_ball; rewrite -Htau0_opt /smooth_hminE.
      apply: ereal_sup_ubound.
      exists tau.
      split.
      - exact: Htau_ball.
      - reflexivity.
    }
    have Htau0_psd : tau0 \is psdlf := eps_ball_psdlf Htau0_ball.
    have Htau1_psd : tau1 \is psdlf.
    {
      have Hcp : DX \is cpmap :=
        cptp_cpmap (@dephase_X_cptp R L HL X E disXE).
      exact: (cp_psdP (CPMap_Build Hcp) Htau0_psd).
    }
    have Htr_tau1 : \Tr tau1 = \Tr tau0.
    {
      have /cptpP [_ /tpmapP Htp] := @dephase_X_cptp R L HL X E disXE.
      exact: Htp.
    }
      have Htau1_ball : eps_ball eps rhoXE tau1.
      {
        have Htau0_tr : @complex.Re R (\Tr tau0) <= 1 :=
          eps_ball_trlf Htau0_ball.
        have Htau1_pos : 0 < @complex.Re R (\Tr tau1)
          by rewrite Htr_tau1; exact: eps_ball_trlf_gt0 Htau0_ball.
        have Htau1_tr : @complex.Re R (\Tr tau1) <= 1
          by rewrite Htr_tau1.
        have Htau1_pd : pur_dist tau1 rhoXE <= eps.
        {
          have Htau0_pd := eps_ball_pur_dist Htau0_ball.
          have Hrho_fix : DX rhoXE = rhoXE.
          {
            exact: dephase_X_cq_id HrhoCQ.
          }
          rewrite -Hrho_fix.
          apply: (le_trans _ Htau0_pd).
          exact: (pd_mono_cptp (@dephase_X_cptp R L HL X E disXE)
            Htau0_psd Prho Htau0_tr Hrho_tr).
        }
        by rewrite /eps_ball Htau1_psd Htau1_pos Htau1_tr Htau1_pd.
      }
    have Htau1_cq : is_cq_state tau1.
    {
      exact: dephase_X_is_cq Htau0_psd.
    }
    have HsmoothE_le_tau0 :
        (smooth_hminE E eps rhoXE <= hminE E tau0)%E.
    {
      apply: ge_ereal_sup => v [tau [Htau_ball ->]].
      exact: Htau0_ubE Htau_ball.
    }
    have Htau1_le_smoothE :
        (hminE E tau1 <= smooth_hminE E eps rhoXE)%E.
    {
      apply: ereal_sup_ubound.
      exists tau1.
      split.
      - exact: Htau1_ball.
      - reflexivity.
    }
    have Htau0_le_tau1 :
        (hminE E tau0 <= hminE E tau1)%E.
    {
      rewrite /tau1 /DX.
      exact: dephase_X_hmin_preserve Htau0_psd.
    }
    exists tau1.
    split.
    - exact: Htau1_ball.
    split.
    - exact: Htau1_cq.
    - apply/eqP; rewrite eq_le.
      apply/andP; split.
      + exact: le_trans HsmoothE_le_tau0 Htau0_le_tau1.
      + exact: Htau1_le_smoothE.
    - have Hbad : eps < eps := lt_le_trans Heps_lt Hlarge.
      by move: Hbad; rewrite ltxx.
Qed.
(* tex: derived matrix-block extraction identity for cq_block.            *)
(* math: K_x · ρ · K_x = |x><x| ⊗ ρ_E^[x] where K_x = |x><x| ⊗ I_E.       *)
(* Standalone justification: foundational matrix-extraction identity      *)
(* (Watrous §1.1.2).                                                       *)
(* Consumers (≥2): pd_mono_post_hash (this file), Gamma_C_post_hash_split *)
(* (lhl/prop.v).                                                           *)
(* Kbox_cq_decomp *)
(* infra: no tex label — fundamental & reusable (mathcomp-style) *)
(* consumer: Kbox_cq_decomp is used downstream by the BB84 secrecy proof. *)
(* path: lhl:Kbox_cq_decomp -> lhl:pd_mono_post_hash -> *)
(*   bb84:privacy_amplification -> bb84:bb84_secret *)
Lemma Kbox_cq_decomp (x : 'Idx[HL]_X) (rhoXE : 'F[HL]_S_XE) :
  (([> deltav x; deltav x <] \O (\1 : 'F[HL]_E)
    : 'F[HL]_S_XE) \o rhoXE \o
   ([> deltav x; deltav x <] \O (\1 : 'F[HL]_E)
    : 'F[HL]_S_XE)) =
  [> deltav x; deltav x <] \O cq_block disXE x rhoXE.
Proof.
  set K := ([> deltav x; deltav x <] \O (\1 : 'F[HL]_E)
            : 'F[HL]_S_XE).
  have HK_ten : K = [> deltav x; deltav x <] \⊗
                    (\1 : 'F[HL]_E).
    by apply: to_Fnd_inj; rewrite (sdotFT _ _ disXE) to_Fnd_tenE.
  have HRHS_ten :
    ([> deltav x; deltav x <] \O cq_block disXE x rhoXE
      : 'F[HL]_S_XE) =
    [> deltav x; deltav x <] \⊗ cq_block disXE x rhoXE.
    by apply: to_Fnd_inj; rewrite (sdotFT _ _ disXE) to_Fnd_tenE.
  have H1O : forall (Y : 'F[HL]_E),
    ((\1 : 'F[HL]_X) \O Y : 'F[HL]_S_XE) =
    (\1 : 'F[HL]_X) \⊗ Y.
    by move=> Y; apply: to_Fnd_inj;
       rewrite (sdotFT _ _ disXE) to_Fnd_tenE.
  rewrite HRHS_ten.
  have Hmx_cq : forall (e_u e_v : 'Idx[HL]_E),
    [< deltav e_v; cq_block disXE x rhoXE (deltav e_u) >] =
    [< deltav (idxU x e_v); rhoXE (deltav (idxU x e_u)) >].
  { move=> e_u e_v.
    rewrite -!outp_trlf -!outp_compr /cq_block.
    rewrite -(trlf_lift_partial disXE _ [>deltav e_u; deltav e_v<]).
    rewrite -/K HK_ten H1O.
    have HKmid :
      ([> deltav x; deltav x <] \⊗ (\1 : 'F[HL]_E)
        : 'F[HL]_S_XE) \o
      ((\1 : 'F[HL]_X) \⊗
        [> deltav e_u; deltav e_v <]) \o
      ([> deltav x; deltav x <] \⊗ (\1 : 'F[HL]_E)
        : 'F[HL]_S_XE) =
      ([> deltav x; deltav x <] \⊗
        [> deltav e_u; deltav e_v <] : 'F[HL]_S_XE).
    { rewrite -tenf_comp; last exact: disXE.
      rewrite !comp_lfun1l !comp_lfun1r.
      rewrite -tenf_comp; last exact: disXE.
      rewrite !comp_lfun1r.
      by rewrite outp_comp dv_dot eqxx scale1r. }
    rewrite -!comp_lfunA lftraceC -comp_lfunA HKmid.
    congr (\Tr (_ \o _)).
    rewrite tenf_outp.
    by rewrite !(dv_tensor _ _ disXE). }
  have HK_adj : K^A = K.
    by rewrite HK_ten tenf_adj adj_outp adjf1 -HK_ten.
  have HKdv : forall w : 'Idx[HL]_S_XE,
    K (deltav w) =
    (x == idxSl w)%:R *: deltav (idxU x (idxSr w)).
  { move=> w.
    rewrite HK_ten -tenf_dv outpE lfunE /= tenvZl dv_dot.
    by rewrite (dv_tensor _ _ disXE). }
  apply/lfunPD => u.
  apply/intro_cdvl => v.
  rewrite !comp_lfunE {1}HKdv.
  rewrite !linearZ /= cdvE.
  rewrite -adj_dotEl HK_adj HKdv.
  rewrite dotpZl conjC_nat -tenf_dv outpE tenvZl dv_dot.
  rewrite linearZ /=.
  rewrite cdvE {1}(dv_split v) tenv_dot; last exact: disXE.
  rewrite dv_dot.
  rewrite [in X in _ = _ * (X * _)]eq_sym.
  congr (_ * (_ * _)).
  by rewrite Hmx_cq.
Qed.
Lemma cq_state_decomp (rhoXE : 'F[HL]_S_XE) :
  is_cq_state rhoXE ->
  rhoXE =
    \sum_(x : 'Idx[HL]_X)
      ([> deltav x; deltav x <] \O cq_block disXE x rhoXE
        : 'F[HL]_S_XE).
Proof.
  move=> Hcq; rewrite -{1}(dephase_X_cq_id disXE Hcq).
  rewrite /dephase_X_so kraussoE.
  apply: eq_bigr => x _.
  have HKadj :
    (([> deltav x; deltav x <] \O (\1 : 'F[HL]_E)
      : 'F[HL]_S_XE))^A =
    ([> deltav x; deltav x <] \O (\1 : 'F[HL]_E)
      : 'F[HL]_S_XE).
  {
    have Htensor :
      ([> deltav x; deltav x <] \O (\1 : 'F[HL]_E)
        : 'F[HL]_S_XE) =
      [> deltav x; deltav x <] \⊗ (\1 : 'F[HL]_E).
    { by apply: to_Fnd_inj; rewrite (sdotFT _ _ disXE) to_Fnd_tenE. }
    by rewrite Htensor tenf_adj adj_outp adjf1 -Htensor.
  }
  by rewrite HKadj Kbox_cq_decomp.
Qed.
Fact cq_lowner_blockwise (rhoXE tauXE : 'F[HL]_S_XE) :
  is_cq_state rhoXE ->
  is_cq_state tauXE ->
  (forall x : 'Idx[HL]_X,
    cq_block disXE x rhoXE <= cq_block disXE x tauXE) ->
  rhoXE <= tauXE.
Proof.
  move=> Hrho Htau Hblock; rewrite (cq_state_decomp Hrho) (cq_state_decomp Htau).
  rewrite lefE -sumrB.
  apply: psdlf_sum => x _.
  rewrite -lefE.
  have Hproj_ge0 : (0 : 'F[HL]_X) <= [> deltav x; deltav x <].
  { by move: (proj1lf_psd (outp_proj1 (deltav x))); rewrite psdlfE. }
  exact: lef_sdotfr Hproj_ge0 (Hblock x).
Qed.
Lemma cq_block_biprod_mx_project
    (x : 'Idx[HL]_X) (rhoXE : 'F[HL]_S_XE) :
  h2mx (cq_block disXE x rhoXE) =
  ptrace1
    (((h2mx [> deltav x; deltav x <]) *t
        (1%:M : 'M[C]_(dim 'H[HL]_E))) *m
      biprod_mx disXE rhoXE *m
      ((h2mx [> deltav x; deltav x <]) *t
        (1%:M : 'M[C]_(dim 'H[HL]_E)))).
Proof.
  rewrite /cq_block (h2mx_ptrace_castl_ptrace1 disXE).
  rewrite -!h2mx1 -!biprod_mx_sdot -!biprod_mx_comp.
  set A :=
    (([> deltav x; deltav x <] \O \1 \o rhoXE) \o
      [> deltav x; deltav x <] \O \1).
  have Hbiprod_raw :
      biprod_mx disXE A =
      (@tenv_mxU R L HL X E)^*t *m h2mx A *m
        @tenv_mxU R L HL X E.
  {
    rewrite /biprod_mx.
    set Q := castmx _ (@tenv_mxU R L HL X E).
    have HQ_t : Q^*t =
        castmx (erefl, tenv_dim disXE) (@tenv_mxU R L HL X E)^*t.
    {
      rewrite /Q.
      exact: (@castmx_mx_mxT _ _ (@adjmx _) _ _ _ _
        (tenv_dim disXE, erefl) (@tenv_mxU R L HL X E)).
    }
    rewrite HQ_t /Q mcextra.castmx_mul.
    rewrite mcextra.castmx_mul.
    by rewrite !castmx_id.
  }
  by rewrite -Hbiprod_raw.
Qed.
(* ================================================================== *)
(* D_max → collision-entropy step                                       *)
(* Tomamichel-Schaffner-Smith-Renner, 'Leftover Hashing Against Quantum *)
(* Side Information' (IEEE Trans. IT 57:5524 (2011); arXiv:1002.2436),   *)
(* Lem. 23 — tex lemma:min-coll-bound                                    *)
(* math: ρ ⊑ c·(I_X ⊗ σ)  ⟹  Γ_C(ρ|σ) ≤ c·Tr ρ.                        *)
(* Proof: conjugating by I⊗σ^{-½} (a `formlf`) sends the Loewner bound to *)
(*   M := σ^{-½}ρσ^{-½} ⊑ c·(I⊗Π_σ) ⊑ c·I; then Γ_C = Re Tr(M·ρ)         *)
(*   ≤ c·Tr ρ via √ρ-sandwiching and trace monotonicity.  Generalizes the *)
(*   c = 1 step inside `min_coll_bound`.                                  *)
(* infra: no tex label beyond lemma:min-coll-bound — reusable            *)
Lemma coll_from_dmax (rhoXE : 'F[HL]_S_XE) (sigmaE : 'F[HL]_E) (c : R) :
  rhoXE \is psdlf ->
  sigmaE \is psdlf ->
  0 <= c ->
  rhoXE <= c%:C *: ((\1 : 'F_X) \O sigmaE) ->
  collision_ent rhoXE sigmaE <= c * @complex.Re R (\Tr rhoXE).
Proof.
  move=> Prho Psig Hc Hfeas_le; pose P : 'F[HL]_E := pinvlf (sqrtH sigmaE).
  pose M : 'F[HL]_S_XE := (\1 : 'F_X) \O P.
  pose Q : 'F[HL]_E := supplf (sqrtH sigmaE).
  pose Xmid : 'F[HL]_S_XE := M \o rhoXE \o M.
  have HP_psd : P \is psdlf by exact: pinvlf_psdlf (sqrtH_psd Psig).
  have HP_herm : P^A = P by exact: hermlf_adjE (psdlf_herm HP_psd).
  have Hsqrt_herm : (sqrtH sigmaE)^A = sqrtH sigmaE
    by exact: hermlf_adjE (sqrtH_herm (psdlf_herm Psig)).
  have HQ_proj : Q \is projlf by exact: supplf_proj (sqrtH sigmaE).
  have /projlfP [HQ_herm HQ_id] := HQ_proj.
  have HM_herm : M^A = M by rewrite /M sdot_I_adj HP_herm.
  have HPsqrt : P \o sqrtH sigmaE = Q by rewrite /Q /supplf HP_herm.
  have HsqrtP : sqrtH sigmaE \o P = Q.
  { apply: adjf_inj.
    by rewrite adjf_comp HP_herm Hsqrt_herm HQ_herm HPsqrt. }
  have Hsand_sigma : P \o sigmaE \o P = Q.
  { have -> : P \o sigmaE \o P = P \o (sqrtH sigmaE \o sqrtH sigmaE) \o P
      by rewrite (sqrtHK Psig).
    by rewrite comp_lfunA HPsqrt -comp_lfunA HsqrtP HQ_id. }
  have HQlift_le1 :
      (((\1 : 'F_X) \O Q : 'F[HL]_S_XE) <= (\1 : 'F[HL]_S_XE)).
  { have HQlift_proj : (((\1 : 'F_X) \O Q : 'F[HL]_S_XE)) \is projlf
      by apply/projlfP; split; [by rewrite sdot_I_adj HQ_herm
        | by rewrite sdotI_comp HQ_id].
    have HQlift_formV :
        (((\1 : 'F_X) \O Q : 'F[HL]_S_XE) \o
         ((\1 : 'F_X) \O Q : 'F[HL]_S_XE)^A <= (\1 : 'F[HL]_S_XE))
      by rewrite -bound1lf_formV_le1; exact: projlf_bound1 HQlift_proj.
    by rewrite sdot_I_adj HQ_herm sdotI_comp HQ_id in HQlift_formV. }
  have HXmid_leQ : Xmid <= c%:C *: ((\1 : 'F_X) \O Q : 'F[HL]_S_XE).
  { move: (formlf_lef M Hfeas_le).
    rewrite !formlfE HM_herm -comp_lfunZr -comp_lfunZl /Xmid /M
      !sdotI_comp Hsand_sigma.
    by []. }
  have HXmid_lecI : Xmid <= c%:C *: (\1 : 'F[HL]_S_XE).
  { apply: (le_trans HXmid_leQ).
    rewrite lefE -scalerBr.
    apply: psdlfZ; first by rewrite lecR.
    by rewrite -lefE. }
  pose Srho : 'F[HL]_S_XE := sqrtH rhoXE.
  have Hsqrt_rho_herm : Srho^A = Srho
    by rewrite /Srho; exact: hermlf_adjE (sqrtH_herm (psdlf_herm Prho)).
  have Hsqrt_rhoK : Srho \o Srho = rhoXE by rewrite /Srho; exact: sqrtHK Prho.
  have HSsand_le : Srho \o Xmid \o Srho <= c%:C *: rhoXE.
  { move: (lef_formV Srho HXmid_lecI).
    by rewrite Hsqrt_rho_herm -comp_lfunZr -comp_lfunZl comp_lfun1r Hsqrt_rhoK. }
  have HXtrace_eq : \Tr (Srho \o Xmid \o Srho) = \Tr (Xmid \o rhoXE).
  { transitivity (\Tr ((Xmid \o Srho) \o Srho));
      first by rewrite -comp_lfunA lftraceC.
    by rewrite -comp_lfunA Hsqrt_rhoK. }
  have HXtrace_le :
      @complex.Re R (\Tr (Xmid \o rhoXE)) <= c * @complex.Re R (\Tr rhoXE).
  { have HReZ : @complex.Re R (c%:C * \Tr rhoXE) = c * @complex.Re R (\Tr rhoXE)
      by case: (\Tr rhoXE) => zr zi /=; rewrite mul0r subr0.
    have Htr_le : \Tr (Xmid \o rhoXE) <= c%:C * \Tr rhoXE.
    { move: (lef_trlf HSsand_le).
      by rewrite HXtrace_eq linearZ. }
    rewrite -HReZ.
    by move: Htr_le; rewrite lecE => /andP[_ H]; exact: H. }
  have -> : collision_ent rhoXE sigmaE = @complex.Re R (\Tr (Xmid \o rhoXE))
    by rewrite /collision_ent /Xmid /M /P /=.
  exact: HXtrace_le.
Qed.
(* ================================================================== *)
(* Projection distance (gentle measurement)                             *)
(* Tomamichel-Schaffner-Smith-Renner, 'Leftover Hashing Against Quantum  *)
(* Side Information' (IEEE Trans. IT 57:5524 (2011); arXiv:1002.2436),    *)
(* Lem. 17 — tex lemma:project-dist                                       *)
(* math: P(ρ, ΠρΠ) ≤ √(1 − (1−Tr(Π^⊥ρ))²)  (= √(2·Tr(Π^⊥ρ) − Tr(Π^⊥ρ)²), *)
(*   the printed form of lemma:project-dist) for a projector Π.            *)
(* Proof: F̄(ρ,ΠρΠ) ≥ 1 − Tr(Π^⊥ρ).  The fidelity term equals Tr(Πρ)     *)
(*   (fid_iv_proj_mx + √(ΠρΠ)²=ΠρΠ + trnorm of psd = trace); the          *)
(*   correction term √((1−Tr ρ)(1−Tr ΠρΠ)) ≥ 1 − Tr ρ.  Then             *)
(*   P = √(1−F̄²) ≤ √(1−(1−t)²).                                          *)
(* infra: no tex label beyond lemma:project-dist — reusable             *)
Fact pd_proj (G : {set L}) (Pi rho : 'F[HL]_G) :
  Pi \is projlf -> rho \is psdlf ->
  @complex.Re R (\Tr rho) <= 1 ->
  pur_dist rho (Pi \o rho \o Pi) <=
    Num.sqrt (1 - (1 - @complex.Re R (\Tr ((\1 - Pi) \o rho))) ^+ 2).
Proof.
  move=> Pproj Prho Hrho_tr; pose Pm := h2mx Pi.
  pose rm := h2mx rho.
  pose tm := Pm *m rm *m Pm.
  have HPm_proj : Pm \is projmx by rewrite /Pm; move: Pproj; rewrite qualifE.
  have Hrm_psd : rm \is psdmx by rewrite /rm; move: Prho; rewrite qualifE.
  have /projmxP_id [/hermmxP HPm_adj HPm_id] := HPm_proj.
  have HPm_obs : Pm \is obsmx := projmx_obs HPm_proj.
  have HPm_psd : Pm \is psdmx := obsmx_psd HPm_obs.
  have HPmc_psd : 1%:M - Pm \is psdmx.
  { by move: HPm_obs; rewrite obsmx_psd_eq => /andP[]. }
  have Htm_psd : tm \is psdmx.
  { rewrite /tm.
    have -> : Pm *m rm *m Pm = Pm *m rm *m Pm^*t
      by rewrite [Pm in _ *m _ *m Pm]HPm_adj.
    exact: psdmx_bimap_closed_gen Hrm_psd. }
  have Htau_h2mx : h2mx (Pi \o rho \o Pi) = tm by rewrite /tm !h2mx_comp.
  have Htr_tm : \tr tm = \tr (Pm *m rm)
    by rewrite /tm mxtrace_mulC mulmxA HPm_id.
  set t := @complex.Re R (\Tr ((\1 - Pi) \o rho)).
  have Ht_val : t = @complex.Re R (\tr rm) - @complex.Re R (\tr (Pm *m rm)).
  { rewrite /t /lftrace h2mx_comp raddfB/= h2mx1 mulmxBl mul1mx.
    by rewrite raddfB/= raddfB/=. }
  have /hermmxP Hsr_herm : sqrtmx rm \is hermmx
    by exact: sqrtmx_herm (psdmx_herm Hrm_psd).
  have Htr_psd_ge0 : forall A : 'M[C]_(dim 'H[HL]_G),
      A \is psdmx -> 0 <= @complex.Re R (\tr (A *m rm)).
  { move=> A HA.
    have Hbi : sqrtmx rm *m A *m (sqrtmx rm)^*t \is psdmx
      by apply: psdmx_bimap_closed_gen; exact: HA.
    move: (psdmx_trace Hbi); rewrite -Hsr_herm -mulmxA mxtrace_mulC -mulmxA (sqrtmxK Hrm_psd).
    by rewrite lecE /= => /andP[]. }
  have HtrPmrm_ge0 : 0 <= @complex.Re R (\tr (Pm *m rm))
    := Htr_psd_ge0 Pm HPm_psd.
  have HtrPmrm_le : @complex.Re R (\tr (Pm *m rm)) <= @complex.Re R (\tr rm).
  { move: (Htr_psd_ge0 (1%:M - Pm) HPmc_psd).
    by rewrite mulmxBl mul1mx raddfB/= raddfB/= subr_ge0. }
  have Ht_ge0 : 0 <= t by rewrite Ht_val subr_ge0.
  have Hrho_trm : @complex.Re R (\tr rm) <= 1 by [].
  have Ha_ge0 : 0 <= 1 - @complex.Re R (\tr rm) by rewrite subr_ge0.
  have H1mt_ge0 : 0 <= 1 - t.
  { rewrite subr_ge0 Ht_val.
    apply: le_trans Hrho_trm.
    by rewrite lerBlDl lerDr. }
  (* generalized-fidelity lower bound F̄(ρ, ΠρΠ) ≥ 1 − t *)
  have Hgfid_lb : 1 - t <= gfid rho (Pi \o rho \o Pi).
  { rewrite /gfid Htau_h2mx -/rm (alt_gfid_gen Hrm_psd Htm_psd).
    have [_ Hfid2] := fid_iv_proj_mx HPm_proj Hrm_psd Hrm_psd.
    have Hpart_a : @complex.Re R (trnorm (sqrtmx rm *m sqrtmx tm))
                 = @complex.Re R (\tr (Pm *m rm)).
    { rewrite -/tm in Hfid2; rewrite -Hfid2.
      by rewrite (sqrtmxK Htm_psd) (psdmx_trnorm Htm_psd) Htr_tm. }
    rewrite Hpart_a.
    have R1 : @complex.Re R 1 = 1 by rewrite -(re_realid 1).
    have HReA : @complex.Re R (1 - \tr rm) = 1 - @complex.Re R (\tr rm)
      by rewrite raddfB/= ?R1.
    have HReB : @complex.Re R (1 - \tr tm) = 1 - @complex.Re R (\tr (Pm *m rm))
      by rewrite Htr_tm raddfB/= ?R1.
    have Hcorr :
        1 - @complex.Re R (\tr rm) <=
        Num.sqrt (@complex.Re R (1 - \tr rm)) *
        Num.sqrt (@complex.Re R (1 - \tr tm)).
    { rewrite HReA HReB.
      rewrite -[X in X <= _](sqr_sqrtr Ha_ge0) expr2.
      apply: ler_pM; rewrite ?sqrtr_ge0 //.
      apply: ler_wsqrtr.
      by rewrite lerD2l lerN2. }
    rewrite Ht_val opprB addrCA.
    by rewrite lerD2l. }
  (* conclude via P = √(1 − F̄²) *)
  have Hgfid_lb' : 1 - t <= gfidelity rm tm
    by move: Hgfid_lb; rewrite /gfid Htau_h2mx -/rm.
  have Hsq : (1 - t) ^+ 2 <= (gfidelity rm tm) ^+ 2.
  { rewrite expr2 [leRHS]expr2.
    apply: ler_pM.
    - exact: H1mt_ge0.
    - exact: H1mt_ge0.
    - exact: Hgfid_lb'.
    - exact: Hgfid_lb'. }
  rewrite /pur_dist /gfid Htau_h2mx -/rm.
  apply: ler_wsqrtr.
  by rewrite lerD2l lerN2.
Qed.
(* ================================================================== *)
(* Tomamichel-Colbeck-Renner, 'Duality Between Smooth Min- and Max-     *)
(* Entropies' (2009; arXiv:0907.5238), Lem. 20 (Φ_min lower bound);     *)
(* invoked in the proof of lemma:min-bound-1 (Lem. 21) of Tomamichel-   *)
(* Schaffner-Smith-Renner, 'Leftover Hashing Against Quantum Side       *)
(* Information0 (arXiv:1002.2436) (λ ≥ Tr ρ / d_A).                      *)
(* math: Φ_min(X|E)_ρ ≥ Tr ρ / d_X.  Every feasible σ has I_X⊗σ ≥ ρ,    *)
(*   hence d_X·Tr σ = Tr(I_X⊗σ) ≥ Tr ρ, so Tr σ ≥ Tr ρ / d_X; the inf    *)
(*   inherits the bound.  Used in `min_bound_op` to turn 1/d_X into 1/Tr ρ.*)
(* infra: the inner lower bound of `entropy:phi_min_pos_trace`.          *)
Lemma phi_min_lb (rhoXE : 'F[HL]_S_XE) :
  rhoXE \is psdlf ->
  @complex.Re R (\Tr rhoXE) <= 1 ->
  @complex.Re R (\Tr rhoXE) / (dim 'H[HL]_X)%:R <= phi_min E rhoXE.
Proof.
  move=> Prho Hrho_tr; have eqX : S_XE :\: E = X := setDU_r disXE.
  have disSplit : [disjoint (S_XE :\: E) & (S_XE :&: E)].
  { apply/disjointP=> z; rewrite !inE.
    by case: (z \in E); rewrite ?andbF ?andbT. }
  rewrite /phi_min.
  apply: lb_le_inf.
  - pose sigma1 : 'F[HL]_(S_XE :&: E) := \1.
    exists (@complex.Re R (\Tr sigma1)).
    rewrite /phi_min_feasible; exists sigma1; split.
    { by rewrite qualifE h2mx1; apply: psdmx1. }
    split; last by [].
    rewrite sdotf11 castlf1.
    have Hrho_den : rhoXE \is denlf.
    { apply/denlfP; split=> //.
      have Hreal : \Tr rhoXE \is Num.real := ger0_real (psdlf_trlf Prho).
      by rewrite -(RRe_real Hreal) lecR. }
    by move: (denf_le1 (DenLf_Build Hrho_den)); rewrite lefE.
  - move=> v [sigma [Psigma [Hfeas ->]]].
    have Htr_sigma_real : (\Tr sigma : C) = (@complex.Re R (\Tr sigma))%:C
      by rewrite RRe_real // ger0_real // psdlf_trlf.
    have Hrho_tr_real : (\Tr rhoXE : C) = (@complex.Re R (\Tr rhoXE))%:C
      by rewrite RRe_real // ger0_real // psdlf_trlf.
    have Hrho_leC :
        \Tr rhoXE <= (dim 'H[HL]_(S_XE :\: E))%:R * \Tr sigma.
    { have Hgap := psdlf_trlf Hfeas. move: Hgap.
      rewrite linearB /= castlf_trlfE (trlf_lift_I disSplit).
      by rewrite subr_ge0. }
    move: Hrho_leC; rewrite Hrho_tr_real Htr_sigma_real eqX.
    rewrite -natrC -rmorphM /= lecR => Hrho_leR.
    rewrite ler_pdivrMr; last by rewrite ltr0n dim_proper.
    by rewrite mulrC.
Qed.
(* ================================================================== *)
(* Matrix helpers for the spectral eigenvalue-cutoff projector          *)
(* ================================================================== *)
(* diagonal Löwner order from entrywise nonnegativity *)
Lemma diagmx_lev (n : nat) (a b : 'rV[C]_n) :
  (b - a) \is a nnegmx -> diag_mx a <= diag_mx b.
Proof.
  by move=> Hab; rewrite le_lownerE -linearB/=; exact: diagmx_nnegmx_psd.
Qed.
(* unitary conjugation is Löwner-monotone *)
Lemma mxconj_lev (n : nat) (U M N : 'M[C]_n) :
  U \is unitarymx -> M <= N -> U^*t *m M *m U <= U^*t *m N *m U.
Proof.
  move=> HU HMN.
  rewrite le_lownerE.
  have -> : U^*t *m N *m U - U^*t *m M *m U = U^*t *m (N - M) *m U
    by rewrite mulmxBr mulmxBl.
  rewrite -[U in _ *m _ *m U]adjmxK.
  by apply: psdmx_bimap_closed_gen; rewrite -le_lownerE.
Qed.
(* ================================================================== *)
(* Spectral eigenvalue-cutoff projector                                 *)
(* Tomamichel-Schaffner-Smith-Renner, 'Leftover Hashing Against Quantum  *)
(* Side Information' (IEEE Trans. IT 57:5524 (2011); arXiv:1002.2436);    *)
(* implicit in the proof of lemma:min-bound-1 (Lem. 21) (P_B onto the     *)
(*   smallest eigenvalues of Gamma_B)                                    *)
(* math: For Γ ⪰ 0 and threshold T ≥ 0 there is a projector P commuting  *)
(*   with Γ with P·Γ·P ⪯ T·P (eigenvalues ≤ T on range P) and            *)
(*   T·(1−P) ⪯ (1−P)·Γ·(1−P) (eigenvalues > T off range); the latter      *)
(*   yields the Markov bound Tr((1−P)w) ≤ Tr(wΓ)/T for any w ⪰ 0.        *)
(* Proof: spectral decomposition Γ = U^†·diag(d)·U (psdmx_svd), cut by    *)
(*   the 0/1 indicator diag(d_i ≤ T).                                    *)
Lemma spectral_cutoff (n : nat) (G : 'M[C]_n) (T : R) :
  G \is psdmx -> 0 <= T ->
  exists P : 'M[C]_n,
    [/\ P \is projmx,
        G *m P = P *m G,
        P *m G *m P <= T%:C *: P &
        T%:C *: (1%:M - P) <= (1%:M - P) *m G *m (1%:M - P) ].
Proof.
  move=> HG HT.
  case: (psdmx_svd HG) => -[U d] /= /and3P [HU Hd /eqP HGeq].
  have HUU : U *m U^*t = 1%:M by apply: unitarymxK.
  have HUUV : U^*t *m U = 1%:M by apply: unitarymxKV.
  (* eigenvalues are real *)
  have Hd_realE : forall j, (@complex.Re R (d 0 j))%:C = d 0 j.
  { move=> j; apply: RRe_real; apply: ger0_real.
    by apply/svd_diag_ge0; exact: Hd. }
  (* 0/1 indicator of "eigenvalue ≤ T" *)
  pose dp : 'rV[C]_n :=
    \row_i (if @complex.Re R (d 0 i) <= T then 1 else 0).
  pose P : 'M[C]_n := U^*t *m diag_mx dp *m U.
  (* conjugation of a diagonal by U respects products *)
  have conjP : forall a b : 'rV[C]_n,
    (U^*t *m diag_mx a *m U) *m (U^*t *m diag_mx b *m U)
     = U^*t *m diag_mx (dmulmx a b) *m U.
  { move=> a b; rewrite -!mulmxA; congr (_ *m _).
    by rewrite [U *m (U^*t *m _)]mulmxA HUU mul1mx mulmxA diag_mx_dmul. }
  have Hdpdp : dmulmx dp dp = dp.
  { apply/rowP => j; rewrite mxE /dp !mxE.
    by case: ifP => _; rewrite ?mulr1 ?mulr0. }
  have Hdp_herm : (diag_mx dp)^*t = diag_mx dp.
  { rewrite diag_mx_adj; congr diag_mx; apply/rowP => j.
    by rewrite !mxE; case: ifP => _; rewrite ?conjC1 ?conjC0. }
  have HP_proj : P \is projmx.
  { apply/projmxP_id; split.
    - by apply/hermmxP; rewrite /P !adjmxM adjmxK Hdp_herm mulmxA.
    - by rewrite /P conjP Hdpdp. }
  have HGP_eq : G *m P = P *m G by rewrite /P HGeq !conjP dmulmxC.
  exists P; split; [exact: HP_proj | exact: HGP_eq | | ].
  - (* P G P ≤ T·P : eigenvalues retained by P are ≤ T *)
    rewrite /P HGeq !conjP scalemxAl scalemxAr.
    have -> : T%:C *: diag_mx dp = diag_mx (T%:C *: dp)
      by apply/matrixP=> a b; rewrite !mxE mulrnAr.
    apply: mxconj_lev; first exact: HU.
    apply: diagmx_lev; apply/nnegmxP=> i j.
    rewrite nnegrE /dp !mxE !ord1.
    case: ifP => Hi.
    + rewrite !mulr1 mul1r -(Hd_realE j) -realcB lec0R subr_ge0; exact: Hi.
    + by rewrite !mulr0 subrr lexx.
  - (* T·(1−P) ≤ (1−P)G(1−P) : eigenvalues discarded by P are > T *)
    have H1P : 1%:M - P = U^*t *m diag_mx (const_mx 1 - dp) *m U.
    { rewrite /P linearB/= diag_const_mx mulmxBr mulmxBl mulmx1 HUUV.
      by []. }
    rewrite H1P HGeq !conjP scalemxAl scalemxAr.
    have -> : T%:C *: diag_mx (const_mx 1 - dp)
              = diag_mx (T%:C *: (const_mx 1 - dp))
      by apply/matrixP=> a b; rewrite !mxE mulrnAr.
    apply: mxconj_lev; first exact: HU.
    apply: diagmx_lev; apply/nnegmxP=> i j.
    rewrite nnegrE /dp !mxE !ord1.
    case: ifP => Hi.
    + by rewrite !subrr !mulr0 subrr lexx.
    + rewrite !subr0 !mulr1 mul1r -(Hd_realE j) -realcB lec0R subr_ge0.
      by apply: ltW; rewrite ltNge Hi.
Qed.
(* ================================================================== *)
(* Matrix transpose trick (core of lemma:mirror, Lem. 14 of            *)
(* Tomamichel-Schaffner-Smith-Renner, 'Leftover Hashing Against        *)
(* Quantum Side Information', arXiv:1002.2436)                          *)
(* ================================================================== *)
(* `tensmx_mul`'s rewrite-matching fails on non-square (column) factors  *)
(* in this scope, so we reprove the mixed-product law for the column     *)
(* case from scratch (same proof as mxtens.v's tensmx_mul).             *)
Lemma tensmx_mul_cV (m1 : nat) (A B : 'M[C]_m1) (u v : 'cV[C]_m1) :
  (A *t B) *m (u *t v) = (A *m u) *t (B *m v).
Proof.
  apply/matrixP=> /= i j.
  case (mxtens_indexP i)=> [im ip] {i}; case (mxtens_indexP j)=> [jr js] {j}.
  rewrite !mxE !mxtens_indexK mulr_sum; apply: congr_big=> // k _.
  by rewrite !mxE !mxtens_indexK mulrCA !mulrA [u _ _ * A _ _]mulrC.
Qed.
(* math: For the unnormalised maximally entangled column                *)
(*   |Φ⟩ = Σ_i e_i ⊗ e_i, every operator A on the first factor mirrors  *)
(*   to its transpose on the second:  (A ⊗ I)|Φ⟩ = (I ⊗ Aᵀ)|Φ⟩.         *)
(* This is the matrix substrate of lemma:mirror.                        *)
Fact tens_transpose_trick (m1 : nat) (A : 'M[C]_m1) :
  (A *t (1%:M : 'M[C]_m1))
    *m (\sum_(i < m1) (delta_mx i 0 : 'cV[C]_m1) *t (delta_mx i 0 : 'cV[C]_m1))
   = ((1%:M : 'M[C]_m1) *t A^T)
    *m (\sum_(i < m1) (delta_mx i 0 : 'cV[C]_m1) *t (delta_mx i 0 : 'cV[C]_m1)).
Proof.
  have Hcol : forall (M : 'M[C]_m1) (i r : 'I_m1),
      (M *m (delta_mx i 0 : 'cV[C]_m1)) r 0 = M r i.
  { move=> M i r; rewrite mxE (bigD1 i)//= big1 ?addr0.
    - by rewrite !mxE !eqxx /= mulr1.
    - by move=> k /negPf nki; rewrite !mxE nki/= mulr0. }
  have Hdel : forall (i s : 'I_m1),
      (delta_mx i 0 : 'cV[C]_m1) s 0 = (i == s)%:R.
  { by move=> i s; rewrite !mxE eqxx andbT eq_sym. }
  rewrite !mulmx_sumr.
  under eq_bigr => i _ do rewrite tensmx_mul_cV mul1mx.
  under [RHS]eq_bigr => i _ do rewrite tensmx_mul_cV mul1mx.
  apply/matrixP => ridx cidx.
  rewrite !summxE.
  case: (mxtens_indexP ridx) => r s.
  case: (mxtens_indexP cidx) => c1 c2.
  rewrite [c1]ord1 [c2]ord1.
  under eq_bigr => i _ do rewrite tensmxE Hcol Hdel.
  under [RHS]eq_bigr => i _ do rewrite tensmxE Hdel Hcol.
  rewrite (bigD1 s)//= big1 => [|i /negPf nis]; last by rewrite nis mulr0.
  rewrite addr0 eqxx mulr1.
  rewrite [RHS](bigD1 r)//= big1 => [|i /negPf nir]; last by rewrite nir mul0r.
  by rewrite addr0 eqxx mul1r mxE.
Qed.
(* ================================================================== *)
(* Labelled eigenvalue-cutoff projector on E (lift of spectral_cutoff).  *)
(* ================================================================== *)
Fact cutoff_projlf (Gamma : 'F[HL]_E) (T : R) :
  Gamma \is psdlf -> 0 <= T ->
  exists PE : 'F[HL]_E,
    [/\ PE \is projlf,
        Gamma \o PE = PE \o Gamma,
        PE \o Gamma \o PE <= T%:C *: PE &
        T%:C *: ((\1 : 'F[HL]_E) - PE)
          <= ((\1 : 'F[HL]_E) - PE) \o Gamma \o ((\1 : 'F[HL]_E) - PE)].
Proof.
  move=> PGamma HT.
  have HG_mx : h2mx Gamma \is psdmx by move: PGamma; rewrite qualifE.
  have [P [HP_proj HPcomm HPGP HPc]] := spectral_cutoff HG_mx HT.
  have H1mP : h2mx ((\1 : 'F[HL]_E) - mx2h P) = 1%:M - P
    by rewrite raddfB/= h2mx1 mx2hK.
  exists (mx2h P); split.
  - by rewrite qualifE mx2hK.
  - apply: h2mx_inj; rewrite !h2mx_comp !mx2hK; exact: HPcomm.
  - rewrite lef_h2mx !h2mx_comp h2mxZ_lf !mx2hK; exact: HPGP.
  - rewrite lef_h2mx h2mxZ_lf !h2mx_comp H1mP; exact: HPc.
Qed.
(* Composition distributes over subtraction (left/right) for set-labelled  *)
(* operators — local helpers (mathcomp's comp_lfunBl/Br are not in scope).  *)
Fact comp_lfunBl_lab (T : {set L}) (a b c : 'F[HL]_T) :
  (a - b) \o c = (a \o c) - (b \o c).
Proof. by rewrite comp_lfunDl comp_lfunNl. Qed.
Fact comp_lfunBr_lab (T : {set L}) (a b c : 'F[HL]_T) :
  a \o (b - c) = (a \o b) - (a \o c).
Proof. by rewrite comp_lfunDr comp_lfunNr. Qed.
(* Fidelity-of-conjugation lower bound (abstract matrices; the heart of the   *)
(* mirror step, kept abstract so the matrix algebra stays cheap):             *)
(*   Re Tr(N ρ) ≤ F(ρ, N ρ N†) = Re ‖√ρ √(N ρ N†)‖₁, when Tr(N ρ) ≥ 0.        *)
Lemma fid_conj_ge (d : nat) (rho N : 'M[C]_d) :
  rho \is psdmx -> (0 : C) <= \tr (N *m rho) ->
  @complex.Re R (\tr (N *m rho))
  <= @complex.Re R (trnorm (sqrtmx rho *m sqrtmx (N *m rho *m N^*t))).
Proof.
  move=> Hrho Hge0.
  have HSh : sqrtmx rho = (sqrtmx rho)^*t
    by apply/hermmxP; exact: sqrtmx_herm (psdmx_herm Hrho).
  have HSK : sqrtmx rho *m sqrtmx rho = rho := sqrtmxK Hrho.
  have E1 : sqrtmx rho = sqrtmx (sqrtmx rho *m (sqrtmx rho)^*t)
    by congr sqrtmx; rewrite -HSh HSK.
  have E2 : sqrtmx (N *m rho *m N^*t)
          = sqrtmx ((N *m sqrtmx rho) *m (N *m sqrtmx rho)^*t)
    by congr sqrtmx; rewrite -[X in N *m X *m N^*t]HSK adjmxM -HSh !mulmxA.
  have Hfid_eq :
      @complex.Re R (trnorm (sqrtmx rho *m sqrtmx (N *m rho *m N^*t)))
      = @complex.Re R (trnorm (sqrtmx rho *m N *m sqrtmx rho))
    by rewrite {1}E1 E2 fid_gram_general_mx -HSh mulmxA.
  rewrite Hfid_eq.
  have HtrEq : \tr (sqrtmx rho *m N *m sqrtmx rho) = \tr (N *m rho)
    by rewrite mxtrace_mulC mulmxA HSK mxtrace_mulC.
  rewrite -HtrEq.
  have Hge0' : (0 : C) <= \tr (sqrtmx rho *m N *m sqrtmx rho) by rewrite HtrEq.
  have Hcmp := trnorm_ge_tr (sqrtmx rho *m N *m sqrtmx rho).
  rewrite (ger0_norm Hge0') in Hcmp.
  by move: Hcmp; rewrite lecE => /andP[_].
Qed.
(* ================================================================== *)
(* Normalisation:                                              *)
(*   ρ̄ is SUB-normalised with `Re (Tr ρ̄) = Re (Tr ρ)` — exactly the      *)
(*   paper's lemma:min-bound-1 (Lem. 21: ρ̄ ∈ S_sub, construction        *)
(*   ρ̄ = ρ̃ + I_X/d_X ⊗ (ρ_E − ρ̃_E) gives Tr ρ̄ = Tr ρ).  Note that       *)
(*   the requirement `Re (Tr ρ̄) = 1` fails in general     for sub-norm    *)
(*   input: gfid(ρ,ρ̄)=F(ρ,ρ̄)≤√(Tr ρ) ⇒ pur_dist(ρ,ρ̄)≥√(1−Tr ρ) > ε̄.    *)
(*   Accordingly, downstream:          the `privacy_amp` chain            *)
(*   (lhl/prop.v + lhl/post_hash.v) takes `tauE \is psdlf` (sub-norm     *)
(*   input), and `almost_two_universal_hashing`'s bound carries           *)
(*   `+ ε²` (the 4-pt / δ terms carry a `Tr ρ ≤ 1` factor instead of 1).  *)
(* ================================================================== *)
(* Operator form of lemma:min-bound-1 (2nd statement)                   *)
(* Tomamichel-Schaffner-Smith-Renner, 'Leftover Hashing Against Quantum *)
(* Side Information' (IEEE Trans. IT 57:5524 (2011); arXiv:1002.2436),   *)
(* Lem. 21 (2nd statement) — tex lemma:min-bound-1                        *)
(* math: For a CQ ρ_XE ∈ S_sub(H_XE) and ε̄ > 0, there is a (sub-norm)    *)
(*   CQ ρ̄_XE ∈ B^{ε̄}(ρ_XE) with                                         *)
(*     ρ̄_XE ⊑ ((2/ε̄² + 1/Tr ρ)·Φ_min(X|E)_ρ) · (I_X ⊗ ρ̄_E),            *)
(*   i.e. H̄_min^alt(X|E)_ρ̄ = −D_max(ρ̄ ‖ I_X⊗ρ̄_E) ≥ Hmin(X|E)_ρ           *)
(*   − log(2/ε̄² + 1/Tr ρ).  This is the alternative-min-entropy bound of  *)
(*   lemma:min-bound-1, rephrased as a Löwner inequality so that          *)
(*   `coll_from_dmax` turns it into the collision bound of `coll_bound`.  *)
(* Proof outline (Lem. 21): with σ the Φ_min-optimizer (I_X⊗σ ≥ ρ,        *)
(*   Tr σ = Φ_min), Γ_B := ρ_B^{-½}σρ_B^{-½}, cut the large eigenvalues of *)
(*   Γ_B by a spectral projector P_B keeping Tr(P_B^⊥ ρ_B) ≤ ε̄²/2; via    *)
(*   the mirror projector of P_B on a purification, ρ̃ := Π_AC ρ Π_AC      *)
(*   satisfies P(ρ,ρ̃) ≤ ε̄ and ρ̃_B ≤ ρ_B; set ρ̄ := ρ̃ + I_X/d_X ⊗(ρ_B−ρ̃_B)*)
(*   (so ρ̄_B = ρ_B) and bound ‖P_B Γ_B P_B‖ ≤ 2/ε̄², using Φ_min ≥ Tr/d_X. *)
(*   Uses:  purification (utils/pur.v), mirror/projection-distance, and a  *)
(*   spectral eigenvalue cutoff.      *)
(* path: lhl:min_bound_op -> lhl:coll_bound ->                            *)
(*   lhl:almost_two_universal_hashing *)
Lemma min_bound_op (eps_bar : R) (rhoXE : 'F[HL]_S_XE) :
  rhoXE \is psdlf ->
  0 < @complex.Re R (\Tr rhoXE) ->
  @complex.Re R (\Tr rhoXE) <= 1 ->
  is_cq_state rhoXE ->
  0 < eps_bar ->
  exists (rhobarXE : 'F[HL]_S_XE),
    [/\ rhobarXE \is psdlf,
        @complex.Re R (\Tr rhobarXE) = @complex.Re R (\Tr rhoXE),
        is_cq_state rhobarXE,
        eps_ball eps_bar rhoXE rhobarXE &
        rhobarXE <=
          ((2%:R * eps_bar^-2 + (@complex.Re R (\Tr rhoXE))^-1)
            * phi_min E rhoXE)%:C
          *: ((\1 : 'F_X) \O ptrace_castl disXE rhobarXE)].
Proof.
  move=> Prho Hrho_pos Hrho_tr Hcq Hepsbar.
  (* σ : Φ_min-optimiser, ρ ⪯ I_X⊗σ, Tr σ = Φ_min. *)
  have [sigma0 [Psigma0 [Hgap Hsigma_tr]]] := phi_min_primal_attained disXE Prho.
  have HsiE : S_XE :&: E = E by setdec.
  pose sigma : 'F[HL]_E := castlf (HsiE, HsiE) sigma0.
  have Psigma : sigma \is psdlf by rewrite /sigma castlf_psdlfE.
  pose rhoE := ptrace_castl disXE rhoXE.
  pose srhoE := sqrtH rhoE.                  (* ρ_E^{1/2}  *)
  pose isrhoE := pinvlf srhoE.               (* ρ_E^{-1/2} *)
  pose Gamma := isrhoE \o sigma \o isrhoE.    (* Γ = ρ_E^{-½} σ ρ_E^{-½} *)
  pose Thr := 2%:R * eps_bar^-2 * phi_min E rhoXE.   (* cutoff threshold *)
  have HrhoE_psd : rhoE \is psdlf
    by rewrite /rhoE; apply: ptrace_castl_psdlf; exact: Prho.
  have HisrhoE_psd : isrhoE \is psdlf
    by rewrite /isrhoE; exact: pinvlf_psdlf (sqrtH_psd HrhoE_psd).
  have HisrhoE_herm : (h2mx isrhoE)^*t = h2mx isrhoE.
  { rewrite -h2mx_adj; congr h2mx.
    exact: hermlf_adjE (psdlf_herm HisrhoE_psd). }
  have Heb2_pos : 0 < eps_bar ^+ 2 by exact: exprn_gt0.
  have Hphi_pos : 0 < phi_min E rhoXE
    by apply: phi_min_pos_trace; [exact: Prho | exact: Hrho_tr | exact: Hrho_pos].
  have HGamma_psd : Gamma \is psdlf.
  { rewrite /Gamma qualifE !h2mx_comp -[X in _ *m _ *m X]HisrhoE_herm.
    by apply: psdmx_bimap_closed_gen; move: Psigma; rewrite qualifE. }
  have HThr_ge0 : 0 <= Thr.
  { rewrite /Thr; apply: mulr_ge0; last exact: ltW Hphi_pos.
    apply: mulr_ge0; first exact: ler0n.
    by rewrite invr_ge0; exact: ltW Heb2_pos. }
  have [PE [HPE_proj HPEcomm HPEbound HPEmarkov]] := cutoff_projlf HGamma_psd HThr_ge0.
  pose oneX : 'F[HL]_X := \1.                (* bare id_lfun: matches h2mx1 AND lift.v lemmas *)
  pose NN := srhoE \o PE \o isrhoE.          (* N = ρ_E^{½} P ρ_E^{-½} *)
  pose rhotilde := formlf (oneX \O NN) rhoXE.   (* ρ̃ = (I⊗N)ρ(I⊗N†) *)
  pose rhotildeE := ptrace_castl disXE rhotilde.
  pose Delta := rhoE - rhotildeE.
  pose rhobar := rhotilde
    + ((dim 'H[HL]_X)%:R^-1)%:C *: (oneX \O Delta).
  (* ρ̃_E = N ρ_E N† = ρ_E^{½} P ρ_E^{½} ⪯ ρ_E (P ⪯ \1), so Δ ⪰ 0;        *)
  (* ρ̄_E = ρ̃_E + Δ = ρ_E, Tr ρ̄ = Tr ρ. *)
  (* ρ̄ psdlf (hoisted before split: reused by the psd conjunct AND eps_ball).*)
  (* Nρ_EN† = formlf √ρ_E (P·Π·P) ⪯ formlf √ρ_E 1 = ρ_E (Π,P projectors ⪯1);  *)
  (* Δ = ρ_E − Nρ_EN† ⪰ 0; (I_X\O Δ) psd; ρ̄ = ρ̃ + c·(I_X\O Δ), c≥0.        *)
  (* Supporting facts (hoisted: shared by psd conjunct, eps_ball, Löwner).      *)
  have Hsp : srhoE \is psdlf := sqrtH_psd HrhoE_psd.
  have Hsa : srhoE^A = srhoE := hermlf_adjE (psdlf_herm Hsp).
  have Hia : isrhoE^A = isrhoE := hermlf_adjE (psdlf_herm HisrhoE_psd).
  have Hpa : PE^A = PE := hermlf_adjE (projlf_herm HPE_proj).
  have HsK : srhoE \o srhoE = rhoE := sqrtHK HrhoE_psd.
  have HPi_proj : cosupplf srhoE \is projlf := cosupplf_proj srhoE.
  have HPi : srhoE \o isrhoE = cosupplf srhoE.
  { rewrite /cosupplf /isrhoE.
    by rewrite (hermlf_adjE (psdlf_herm (pinvlf_psdlf Hsp))). }
  have HiPi : isrhoE \o srhoE = cosupplf srhoE.
  { have -> : isrhoE \o srhoE = (srhoE \o isrhoE)^A
      by rewrite adjf_comp Hsa Hia.
    by rewrite HPi (hermlf_adjE (projlf_herm HPi_proj)). }
  have HQ : formlf isrhoE rhoE = cosupplf srhoE.
  { rewrite -[rhoE in formlf isrhoE rhoE](_ : formlf srhoE \1 = rhoE);
      last by rewrite formlf1E Hsa HsK.
    rewrite formlf_comp formlf1E adjf_comp Hsa Hia HiPi HPi.
    exact: projlf_idem HPi_proj. }
  have HrhotildeE_val : rhotildeE = formlf NN rhoE.
  { rewrite /rhotildeE /rhotilde /oneX /rhoE.
    exact: ptrace_castl_formlf_lift_I. }
  have HrhotildeE_le : rhotildeE <= rhoE.
  { rewrite HrhotildeE_val /NN -!formlf_comp.
    rewrite -[X in _ <= X](_ : formlf srhoE \1 = rhoE);
      last by rewrite formlf1E Hsa HsK.
    apply: formlf_lef.
    apply: (le_trans (y := formlf PE \1)).
    - apply: formlf_lef.
      by rewrite HQ; apply: obslf_le1; apply: projlf_obs; exact: HPi_proj.
    - by rewrite formlf1E Hpa (projlf_idem HPE_proj);
        apply: obslf_le1; apply: projlf_obs; exact: HPE_proj. }
  have HDelta_psd : Delta \is psdlf.
  { by rewrite /Delta psdlfE subv_ge0. }
  have Hrhotilde_psd : rhotilde \is psdlf.
  { rewrite /rhotilde formlfE qualifE !h2mx_comp h2mx_adj.
    by apply: psdmx_bimap_closed_gen; move: Prho; rewrite qualifE. }
  have HoneXDelta : (oneX \O Delta) \is psdlf.
  { have Hten : (oneX \O Delta : 'F[HL]_S_XE) = oneX \⊗ Delta
      by apply: to_Fnd_inj; rewrite (sdotFT _ _ disXE) to_Fnd_tenE.
    rewrite Hten psdlfE; apply: tenf_ge0; first exact: disXE.
    - by rewrite /oneX; exact: lef01.
    - by move: HDelta_psd; rewrite psdlfE. }
  have Htil_le : rhotilde <= rhobar.
  { rewrite /rhobar -subv_ge0 addrAC subrr add0r.
    rewrite -psdlfE; apply: psdlfZ; last exact: HoneXDelta.
    by rewrite ler0c invr_ge0 ler0n. }
  have Hpsd : rhobar \is psdlf.
  { rewrite /rhobar; apply: psdlfD; first exact: Hrhotilde_psd.
    apply: psdlfZ; last exact: HoneXDelta.
    by rewrite ler0c invr_ge0 ler0n. }
  (* Re Tr ρ̄ = Re Tr ρ (hoisted: reused by the trace conjunct AND eps_ball). *)
  have Htr : @complex.Re R (\Tr rhobar) = @complex.Re R (\Tr rhoXE).
  { have eqEX : S_XE = (E :|: X) by rewrite finset.setUC.
    have disEX : [disjoint E & X] by rewrite disjoint_sym.
    have HdX_neq0 : ((dim 'H[HL]_X)%:R : C) != 0
      by rewrite pnatr_eq0 -lt0n dim_proper.
    have Htr1X : \Tr oneX = (dim 'H[HL]_X)%:R
      by rewrite /oneX /lftrace h2mx1 mxtrace1.
    have HtrXO : forall s : 'F[HL]_E,
        \Tr (oneX \O s) = (dim 'H[HL]_X)%:R * \Tr s.
    { move=> s.
      have Hconv : oneX \O s = castlf (esym eqEX, esym eqEX) (s \⊗ oneX).
      { apply: to_Fnd_inj; rewrite Fnd_cast (sdotFT _ _ disXE) !to_Fnd_tenE.
        by rewrite tenFC. }
      by rewrite Hconv castlf_trlfE (lftrace_tenf _ _ disEX) Htr1X mulrC. }
    have HdXR_neq0 : ((dim 'H[HL]_X)%:R : R) != 0
      by rewrite pnatr_eq0 -lt0n dim_proper.
    have Hsc1 : ((dim 'H[HL]_X)%:R^-1)%:C * (dim 'H[HL]_X)%:R = 1 :> C
      by rewrite -natrC -rmorphM (mulVf HdXR_neq0) rmorph1.
    (* plain-`\Tr` helpers (linearD/Z/B bundle `\Tr`, breaking later matches) *)
    have trD : \Tr (rhotilde + ((dim 'H[HL]_X)%:R^-1)%:C *: (oneX \O Delta))
             = \Tr rhotilde + ((dim 'H[HL]_X)%:R^-1)%:C * \Tr (oneX \O Delta)
      by rewrite linearD linearZ.
    have trDelta : \Tr Delta = \Tr rhoXE - \Tr rhotilde.
    { have hB : \Tr (rhoE - rhotildeE) = \Tr rhoE - \Tr rhotildeE
        by rewrite raddfB.
      by rewrite /Delta hB /rhoE /rhotildeE !trlf_ptrace_castl. }
    rewrite /rhobar trD HtrXO trDelta mulrA Hsc1 mul1r.
    by rewrite addrC subrK. }
  exists rhobar; split.
  - exact: Hpsd.
  - exact: Htr.
  - (* is_cq_state ρ̄: ρ̃=formlf(I_X\O N)ρ and I_X\O Δ are CQ.  N,Δ act on E   *)
    (* only ⇒ commute with X-projectors |x⟩⟨x|\O I; Hcq passes through ρ̃,    *)
    (* and |x⟩⟨x|·|x'⟩⟨x'|=0 (x≠x') kills the I_X\O Δ block.                  *)
    have oneXE : oneX = (\1 : 'F[HL]_X) by rewrite /oneX.
    have liftXl : forall f : 'F[HL]_X,
        f \O (\1 : 'F_E) = lift_lf (finset.subsetUl X E) f.
    { move=> f.
      rewrite -(lift_lf_id (subUsetPP (finset.subsetUl X E)
                  (finset.subsetUr X E)) (f \O (\1 : 'F_E))).
      by rewrite lift_lf_sdot lift_lf1 comp_lfun1r. }
    have liftEr : forall g : 'F[HL]_E,
        (\1 : 'F_X) \O g = lift_lf (finset.subsetUr X E) g.
    { move=> g.
      rewrite -(lift_lf_id (subUsetPP (finset.subsetUl X E)
                  (finset.subsetUr X E)) ((\1 : 'F_X) \O g)).
      by rewrite lift_lf_sdot lift_lf1 comp_lfun1l. }
    have commXE : forall (f : 'F[HL]_X) (g : 'F[HL]_E),
        (f \O (\1 : 'F_E)) \o ((\1 : 'F_X) \O g) =
        ((\1 : 'F_X) \O g) \o (f \O (\1 : 'F_E)).
    { move=> f g; rewrite liftXl liftEr; exact: lift_lf_compC _ _ _ _ disXE. }
    apply/forallP => x; apply/forallP => x'; apply/implyP => Hne; apply/eqP.
    have Hcq0 : ([> deltav x; deltav x <] \O (\1 : 'F_E)) \o rhoXE \o
                ([> deltav x'; deltav x' <] \O (\1 : 'F_E)) = 0.
    { by apply/eqP;
        move: Hcq=> /forallP/(_ x)/forallP/(_ x')/implyP/(_ Hne). }
    have Hxx' : (x == x') = false by rewrite eq_sym; exact: negbTE Hne.
    have HPxx' : [> deltav x; deltav x <] \o [> deltav x'; deltav x' <]
               = (0 : 'F[HL]_X).
    { by rewrite outp_comp onb_dot Hxx' scale0r. }
    set Lx := [> deltav x; deltav x <] \O (\1 : 'F_E).
    set Lx' := [> deltav x'; deltav x' <] \O (\1 : 'F_E).
    have HcqL : Lx \o rhoXE \o Lx' = 0 by rewrite /Lx /Lx'; exact: Hcq0.
    have liftNadj : ((\1 : 'F_X) \O NN)^A = (\1 : 'F_X) \O NN^A
      by rewrite !liftEr -lift_lf_adj.
    have cAL : Lx \o ((\1 : 'F_X) \O NN) = ((\1 : 'F_X) \O NN) \o Lx
      by rewrite /Lx; exact: commXE.
    have cAR : ((\1 : 'F_X) \O NN^A) \o Lx' = Lx' \o ((\1 : 'F_X) \O NN^A)
      by rewrite /Lx' commXE.
    rewrite /rhobar comp_lfunDr comp_lfunDl.
    have H2 : Lx \o (((dim 'H[HL]_X)%:R^-1)%:C *: (oneX \O Delta)) \o Lx' = 0.
    { rewrite oneXE -comp_lfunZr -comp_lfunZl /Lx /Lx' commXE -comp_lfunA.
      by rewrite !liftXl -lift_lf_comp HPxx' raddf0 comp_lfun0r scaler0. }
    have H1 : Lx \o rhotilde \o Lx' = 0.
    { transitivity (((\1 : 'F_X) \O NN) \o (Lx \o rhoXE \o Lx') \o
                    ((\1 : 'F_X) \O NN^A)).
      - rewrite /rhotilde formlfE oneXE liftNadj.
        by rewrite !comp_lfunA cAL -!comp_lfunA cAR !comp_lfunA.
      - by rewrite HcqL comp_lfun0r comp_lfun0l. }
    by rewrite H1 H2 addr0.
  - (* eps_ball ε̄ ρ ρ̄ = (ρ̄ psd)&&(0<Tr ρ̄)&&(Tr ρ̄≤1)&&(pur_dist ρ̄ ρ ≤ ε̄).  *)
    (* First three components from the hoisted Hpsd/Htr.                       *)
    rewrite /eps_ball Hpsd Htr Hrho_pos Hrho_tr /=.
    (* pur_dist ρ̄ ρ ≤ ε̄.  ρ̃ = Tr_C(Π ρ̂ Π) (mirror of cutoff P on a          *)
    (* purification ρ̂); F(ρ,ρ̄) ≥ F(ρ,ρ̃) [fid_v_mono_r_psd, ρ̃⪯ρ̄] ≥           *)
    (* F(ρ̂,Πρ̂Π) [fid_ptr_mono] = Tr(Π ρ̂) [pure+proj] = Tr(P ρ_E) [mirror]    *)
    (* ≥ Tr ρ − ε̄²/2 [Markov, HPEmarkov]; gfid = F + (1−Tr ρ) ≥ 1−ε̄²/2       *)
    (* ⇒ pur_dist = √(1−gfid²) ≤ ε̄. *)
    rewrite /pur_dist.
    set g := gfid rhobar rhoXE.
    (* scalar inputs (filled below): 0 ≤ g ≤ 1 and the gfid lower bound. *)
    have Prhobar_mx : h2mx rhobar \is psdmx by move: Hpsd; rewrite qualifE.
    have ProXE_mx : h2mx rhoXE \is psdmx by move: Prho; rewrite qualifE.
    have HtrmxE : forall f : 'F[HL]_S_XE, \tr (h2mx f) = \Tr f
      by move=> f; rewrite /lftrace.
    have Hg_ge0 : (0:R) <= g.
    { rewrite /g /gfid; apply: gfid_ge0_mx; [exact: Prhobar_mx | exact: ProXE_mx]. }
    have Hg_le1 : g <= 1.
    { rewrite /g /gfid.
      apply: gfid_le1_mx; apply: denmx_psd_re_tr_le.
      - exact: Prhobar_mx.
      - by rewrite HtrmxE Htr.
      - exact: ProXE_mx.
      - by rewrite HtrmxE. }
    (* gfid ρ̄ ρ = F(ρ̄,ρ) + √((1−Trρ̄)(1−Trρ)) = F(ρ̄,ρ) + (1−Trρ) (Trρ̄=Trρ). *)
    have RtrR_rhoXE : \Tr rhoXE \is Num.real := ger0_real (psdlf_trlf Prho).
    have RtrR_rhobar : \Tr rhobar \is Num.real := ger0_real (psdlf_trlf Hpsd).
    have HtrFull : \Tr rhobar = \Tr rhoXE
      by rewrite -(RRe_real RtrR_rhobar) Htr (RRe_real RtrR_rhoXE).
    have Hgfid_eq : g =
        @complex.Re R (trnorm (sqrtmx (h2mx rhobar) *m sqrtmx (h2mx rhoXE)))
        + (1 - @complex.Re R (\Tr rhoXE)).
    { rewrite /g /gfid (alt_gfid_gen Prhobar_mx ProXE_mx).
      congr (_ + _).
      rewrite (HtrmxE rhobar) (HtrmxE rhoXE) HtrFull.
      rewrite -expr2 sqr_sqrtr; last by rewrite raddfB /= subr_ge0.
      by rewrite raddfB /= /lftrace. }
    (* F(ρ̄,ρ) ≥ Trρ − ε̄²/2: monotonicity (ρ̃⪯ρ̄) + mirror + Markov.            *)
    have Hfid_lb :
        @complex.Re R (\Tr rhoXE) - eps_bar ^+ 2 / 2%:R
        <= @complex.Re R (trnorm (sqrtmx (h2mx rhobar) *m sqrtmx (h2mx rhoXE))).
    { have Prhotilde_mx : h2mx rhotilde \is psdmx
        by move: Hrhotilde_psd; rewrite qualifE.
      have Htil_le_mx : h2mx rhotilde <= h2mx rhobar by rewrite -lef_h2mx.
      (* HA: F(ρ̄,ρ)=F(ρ,ρ̄) ≥ F(ρ,ρ̃) since ρ̃ ⪯ ρ̄ [fid_v_mono_r_psd_mx]. *)
      have HA :
          @complex.Re R (trnorm (sqrtmx (h2mx rhoXE) *m sqrtmx (h2mx rhotilde)))
          <= @complex.Re R (trnorm (sqrtmx (h2mx rhobar) *m sqrtmx (h2mx rhoXE))).
      { rewrite -(fid_i_sym_mx ProXE_mx Prhobar_mx).
        apply: fid_v_mono_r_psd_mx;
          [exact: ProXE_mx | exact: Prhotilde_mx | exact: Prhobar_mx
           | exact: Htil_le_mx]. }
      (* HMarkov: Re Tr(P^⊥ρ_E) ≤ ε̄²/2 ⟹ Re Trρ − ε̄²/2 ≤ Re Tr(P ρ_E).      *)
      have HMarkov :
          @complex.Re R (\Tr rhoXE) - eps_bar ^+ 2 / 2%:R
          <= @complex.Re R (\Tr (PE \o rhoE)).
      { have HQ_psd : ((\1 : 'F[HL]_E) - PE) \is psdlf
          by rewrite psdlfE subv_ge0; apply: obslf_le1; exact: projlf_obs HPE_proj.
        (* Tr(P ρ_E) = Tr ρ_E − Tr(P^⊥ ρ_E), and Tr ρ_E = Tr ρ. *)
        have Hsplit : \Tr (PE \o rhoE)
                    = \Tr rhoE - \Tr (((\1 : 'F[HL]_E) - PE) \o rhoE).
        { have Hsum : \Tr (PE \o rhoE)
                    + \Tr (((\1 : 'F[HL]_E) - PE) \o rhoE) = \Tr rhoE
            by rewrite -linearD -comp_lfunDl addrCA subrr addr0 comp_lfun1l.
          by rewrite -Hsum addrK. }
        have HrhoEtr : @complex.Re R (\Tr rhoE) = @complex.Re R (\Tr rhoXE)
          by rewrite /rhoE trlf_ptrace_castl.
        (* Markov: Re Tr(P^⊥ ρ_E) ≤ ε̄²/2 (from the spectral lower cutoff).      *)
        have HMarkov0 :
            @complex.Re R (\Tr (((\1 : 'F[HL]_E) - PE) \o rhoE))
            <= eps_bar ^+ 2 / 2%:R.
        { have HBl := @comp_lfunBl_lab E.
          have HBr := @comp_lfunBr_lab E.
          have Hz_ge0 : (0 : C) <= \Tr (((\1 : 'F[HL]_E) - PE) \o rhoE)
            := psdlf_TrM HQ_psd HrhoE_psd.
          have Hz_real : \Tr (((\1 : 'F[HL]_E) - PE) \o rhoE) \is Num.real
            := ger0_real Hz_ge0.
          have Hsig_real : \Tr sigma \is Num.real := ger0_real (psdlf_trlf Psigma).
          have Hsig_tr : @complex.Re R (\Tr sigma) = phi_min E rhoXE
            by rewrite /sigma castlf_trlfE -Hsigma_tr.
          (* Γ commutes with Q := 1−PE; (1−PE)Γ(1−PE) ⪯ Γ. *)
          have HGam_form : Gamma = formlf isrhoE sigma by rewrite /Gamma formlfE Hia.
          have Hcomm2 : ((\1 : 'F[HL]_E) - PE) \o Gamma = Gamma \o ((\1 : 'F[HL]_E) - PE)
            by rewrite HBl comp_lfun1l HBr comp_lfun1r HPEcomm.
          have HQidem : ((\1 : 'F[HL]_E) - PE) \o ((\1 : 'F[HL]_E) - PE)
                      = (\1 : 'F[HL]_E) - PE
            by rewrite HBl comp_lfun1l HBr comp_lfun1r (projlf_idem HPE_proj)
               subrr subr0.
          have HGPE_psd : Gamma \o PE \is psdlf.
          { have HGPEf : Gamma \o PE = formlf PE Gamma
              by rewrite formlfE Hpa -HPEcomm -comp_lfunA (projlf_idem HPE_proj).
            rewrite HGPEf formlfE qualifE h2mx_comp h2mx_comp h2mx_adj.
            by apply: psdmx_bimap_closed_gen; move: HGamma_psd; rewrite qualifE. }
          have HM_le : ((\1 : 'F[HL]_E) - PE) \o Gamma \o ((\1 : 'F[HL]_E) - PE)
                     <= Gamma.
          { rewrite Hcomm2 -comp_lfunA HQidem -subv_ge0 HBr comp_lfun1r
              opprB addrCA subrr addr0 -psdlfE.
            exact: HGPE_psd. }
          have HformGsig : formlf srhoE Gamma = formlf (cosupplf srhoE) sigma
            by rewrite HGam_form formlf_comp HPi.
          have HtrGsig : \Tr (formlf (cosupplf srhoE) sigma) <= \Tr sigma.
          { have Hch : (cosupplf srhoE)^A = cosupplf srhoE
              := hermlf_adjE (projlf_herm HPi_proj).
            have HQc_psd : ((\1 : 'F[HL]_E) - cosupplf srhoE) \is psdlf
              by rewrite psdlfE subv_ge0; apply: obslf_le1;
                 exact: projlf_obs HPi_proj.
            rewrite formlfE Hch lftraceC comp_lfunA (projlf_idem HPi_proj).
            rewrite -subr_ge0 -raddfB.
            have -> : sigma - (cosupplf srhoE \o sigma)
                    = ((\1 : 'F[HL]_E) - cosupplf srhoE) \o sigma
              by rewrite HBl comp_lfun1l.
            exact: psdlf_TrM HQc_psd Psigma. }
          have HLHS_tr :
              \Tr (formlf srhoE (Thr%:C *: ((\1 : 'F[HL]_E) - PE)))
              = Thr%:C * \Tr (((\1 : 'F[HL]_E) - PE) \o rhoE).
          { have HsKm : h2mx srhoE *m h2mx srhoE = h2mx rhoE
              by rewrite -h2mx_comp HsK.
            rewrite /lftrace formlfE Hsa !h2mx_comp h2mxZ_lf.
            rewrite -scalemxAr -scalemxAl mxtraceZ.
            congr (_ * _).
            by rewrite [X in _ = X]mxtrace_mulC [X in X = _]mxtrace_mulC
               mulmxA HsKm. }
          have step1 :
              \Tr (formlf srhoE (Thr%:C *: ((\1 : 'F[HL]_E) - PE)))
              <= \Tr (formlf srhoE
                   (((\1 : 'F[HL]_E) - PE) \o Gamma \o ((\1 : 'F[HL]_E) - PE)))
            by apply: lef_trlf; apply: formlf_lef; exact: HPEmarkov.
          have step2 :
              \Tr (formlf srhoE
                   (((\1 : 'F[HL]_E) - PE) \o Gamma \o ((\1 : 'F[HL]_E) - PE)))
              <= \Tr (formlf srhoE Gamma)
            by apply: lef_trlf; apply: formlf_lef; exact: HM_le.
          have step3 : \Tr (formlf srhoE Gamma) <= \Tr sigma
            by rewrite HformGsig; exact: HtrGsig.
          have Hcplx : Thr%:C * \Tr (((\1 : 'F[HL]_E) - PE) \o rhoE) <= \Tr sigma
            by rewrite -HLHS_tr; exact: le_trans step1 (le_trans step2 step3).
          have HThr_pos : 0 < Thr.
          { rewrite /Thr; apply: mulr_gt0; last exact: Hphi_pos.
            apply: mulr_gt0; first by rewrite ltr0n.
            by rewrite invr_gt0 exprn_gt0. }
          have HcplxRe :
              Thr * @complex.Re R (\Tr (((\1 : 'F[HL]_E) - PE) \o rhoE))
              <= phi_min E rhoXE.
          { rewrite -(@lecR R) rmorphM/= (RRe_real Hz_real) -Hsig_tr
              (RRe_real Hsig_real).
            exact: Hcplx. }
          have HThr_eps : Thr * (eps_bar ^+ 2 / 2%:R) = phi_min E rhoXE.
          { have H2n0 : (2%:R : R) != 0 by rewrite pnatr_eq0.
            have He2n0 : (eps_bar ^+ 2 : R) != 0 := lt0r_neq0 Heb2_pos.
            rewrite /Thr -mulrA mulrCA.
            have -> : (2%:R * eps_bar ^- 2) * (eps_bar ^+ 2 / 2%:R) = 1
              by rewrite [2%:R * eps_bar ^- 2]mulrC mulrACA mulVf// mulfV// mulr1.
            by rewrite mulr1. }
          rewrite -(ler_pM2l HThr_pos) HThr_eps; exact: HcplxRe. }
        have ReB : forall a b : C, @complex.Re R (a - b)
                 = @complex.Re R a - @complex.Re R b
          by move=> a b; rewrite raddfB.
        rewrite Hsplit ReB HrhoEtr.
        exact: lerB (lexx _) HMarkov0. }
      (* HMirror: F(ρ,ρ̃) ≥ Re Tr(P ρ_E), purification-free.                    *)
      (* F(ρ,ρ̃)=Re trnorm(√ρ N √ρ) [fid_gram, ρ̃=N ρ N†] ≥ Re Tr(N ρ) [trnorm   *)
      (* ≥ Re Tr] = Tr(P ρ_E) [√ρ_E⁺ρ_E√ρ_E=ρ_E via cosupplfv].                 *)
      have HMirror :
          @complex.Re R (\Tr (PE \o rhoE))
          <= @complex.Re R (trnorm (sqrtmx (h2mx rhoXE) *m sqrtmx (h2mx rhotilde))).
      { (* ρ̃ = N' ρ N'† at matrix level (N' = oneX⊗NN). *)
        have Hrhotm : h2mx rhotilde
            = h2mx (oneX \O NN) *m h2mx rhoXE *m (h2mx (oneX \O NN))^*t
          by rewrite /rhotilde formlfE !h2mx_comp h2mx_adj.
        (* √ρ_E⁺ ρ_E = √ρ_E ; Tr(N' ρ) = Tr(P ρ_E). *)
        have HisrhoE_rhoE : isrhoE \o rhoE = srhoE
          by rewrite -HsK comp_lfunA HiPi cosupplfv.
        have HtrPE : \tr (h2mx (oneX \O NN) *m h2mx rhoXE) = \Tr (PE \o rhoE).
        { (* trlf_lift_partial uses \1%:VF; bridge to oneX=\1 via exact (conv). *)
          rewrite -h2mx_comp.
          transitivity (\Tr ((oneX \O NN) \o rhoXE)); first by [].
          have Hpair : \Tr (rhoXE \o (oneX \O NN)) = \Tr (rhoE \o NN)
            by exact: trlf_lift_partial.
          rewrite lftraceC Hpair.
          by rewrite /NN lftraceC -!comp_lfunA HisrhoE_rhoE
             lftraceC -comp_lfunA HsK. }
        have Hge0 : (0 : C) <= \tr (h2mx (oneX \O NN) *m h2mx rhoXE)
          by rewrite HtrPE; exact: psdlf_TrM (projlf_psd HPE_proj) HrhoE_psd.
        rewrite -HtrPE Hrhotm.
        exact: fid_conj_ge ProXE_mx Hge0. }
      exact: le_trans HMarkov (le_trans HMirror HA). }
    have Hgfid_lb : 1 - eps_bar ^+ 2 / 2%:R <= g.
    { have Hcomb : (@complex.Re R (\Tr rhoXE) - eps_bar ^+ 2 / 2%:R)
                   + (1 - @complex.Re R (\Tr rhoXE)) = 1 - eps_bar ^+ 2 / 2%:R
        by rewrite addrAC addrCA subrr addr0.
      rewrite Hgfid_eq -Hcomb.
      apply: lerD; [exact: Hfid_lb | exact: lexx]. }
    (* scalar reduction: 1−g² = (1−g)(1+g) ≤ (1−g)·2 ≤ (ε̄²/2)·2 = ε̄². *)
    have He0 : (0:R) <= eps_bar ^+ 2 by rewrite exprn_ge0// ltW.
    have H1mg : (0:R) <= 1 - g by rewrite subr_ge0.
    have H2n0 : (2%:R : R) != 0 by rewrite pnatr_eq0.
    have He2 : (2%:R : R) = 1 + 1 by rewrite mulrSr mulr1n.
    have Hstep : 1 - g ^+ 2 <= eps_bar ^+ 2.
    { have Hfac : 1 - g ^+ 2 = (1 - g) * (1 + g)
        by rewrite -{1}(expr1n R 2%N) subr_sqr.
      rewrite Hfac -[eps_bar ^+ 2](divfK H2n0).
      apply: ler_pM.
      - exact: H1mg.
      - exact: (addr_ge0 ler01 Hg_ge0).
      - by rewrite lerBlDr addrC -lerBlDr.
      - by rewrite He2 lerD2l. }
    have Hrw : eps_bar = Num.sqrt (eps_bar ^+ 2)
      by rewrite sqrtr_sqr ger0_norm// ltW.
    by rewrite [X in _ <= X]Hrw ler_sqrt.
  - (* Löwner bound.  ρ̄_E = ρ_E. *)
    have ptrZ : forall z : 'F[HL]_S_XE,
        ptrace_castl disXE (((dim 'H[HL]_X)%:R^-1)%:C *: z)
        = ((dim 'H[HL]_X)%:R^-1)%:C *: ptrace_castl disXE z.
    { move=> z; rewrite /ptrace_castl /ptrace_cast_gen.
      have Hptr_trZ :
          \Tr_(X) (((dim 'H[HL]_X)%:R^-1)%:C *: z) =
          ((dim 'H[HL]_X)%:R^-1)%:C *: \Tr_(X) z.
      { exact: linearZ. }
      rewrite Hptr_trZ.
      exact: linearZ. }
    have ptrD : forall z w : 'F[HL]_S_XE,
        ptrace_castl disXE (z + w)
        = ptrace_castl disXE z + ptrace_castl disXE w.
    { move=> z w; rewrite /ptrace_castl /ptrace_cast_gen.
      have Hptr_trD :
          \Tr_(X) (z + w) = \Tr_(X) z + \Tr_(X) w.
      { exact: raddfD. }
      rewrite Hptr_trD.
      exact: raddfD. }
    have Htr_oneX : \Tr oneX = (dim 'H[HL]_X)%:R
      by rewrite /oneX /lftrace h2mx1 mxtrace1.
    have HdXR_neq0 : ((dim 'H[HL]_X)%:R : R) != 0
      by rewrite pnatr_eq0 -lt0n dim_proper.
    have Hc_dX : ((dim 'H[HL]_X)%:R^-1)%:C * (dim 'H[HL]_X)%:R = 1 :> C
      by rewrite -natrC -rmorphM (mulVf HdXR_neq0) rmorph1.
    have Hrhobar_E : ptrace_castl disXE rhobar = rhoE.
    { rewrite /rhobar ptrD ptrZ ptrace_castl_sdot_trace_l Htr_oneX.
      by rewrite scalerA Hc_dX scale1r -/rhotildeE /Delta addrC subrK. }
    rewrite Hrhobar_E.
    (* identity-form bridge + sdot monotonicity *)
    have oneXE : oneX = (\1 : 'F[HL]_X) by rewrite /oneX.
    have liftEr : forall g : 'F[HL]_E,
        oneX \O g = lift_lf (finset.subsetUr X E) g.
    { move=> g; rewrite /oneX
        -(lift_lf_id (subUsetPP (finset.subsetUl X E) (finset.subsetUr X E))
           ((\1 : 'F_X) \O g)).
      by rewrite lift_lf_sdot lift_lf1 comp_lfun1l. }
    have HsdotLef : forall A B : 'F[HL]_E, A <= B -> oneX \O A <= oneX \O B
      by move=> A B HAB; rewrite !liftEr lift_lf_lef.
    (* feasibility ρ ⪯ I_X⊗σ (Hgap cast-reconciled to oneX\O sigma via the   *)
    (* same sdotIf_cast machinery as the first-clause feasibility).           *)
    have eqX0 : S_XE :\: E = X by exact: setDU_r disXE.
    have eqE0 : S_XE :&: E = E by setdec.
    have eqLift0 : (S_XE :\: E) :|: E = S_XE by rewrite eqX0.
    have eqLiftSig0 : (S_XE :\: E) :|: (S_XE :&: E) = (S_XE :\: E) :|: E
      by rewrite eqE0.
    pose eqPhi0 : (S_XE :\: E) :|: (S_XE :&: E) = S_XE :=
      eq_ind_r (eq^~ S_XE)
        (eq_ind_r (eq^~ S_XE) (erefl S_XE) (finset.setID S_XE E))
        (finset.setUC (S_XE :\: E) (S_XE :&: E)).
    have phi_lift0 :
        castlf (eqPhi0, eqPhi0)
          ((\1 : 'F[HL]_(S_XE :\: E)) \O castlf (esym eqE0, esym eqE0) sigma)
        = (\1 : 'F[HL]_X) \O sigma.
    { have -> : eqPhi0 = etrans eqLiftSig0 eqLift0 by apply: eq_irrelevance.
      rewrite -castlf_comp
        (@sdotIf_cast_r R _ _ (S_XE :\: E) (S_XE :&: E) E eqE0 eqLiftSig0
           (castlf (esym eqE0, esym eqE0) sigma)).
      have -> : castlf (eqE0, eqE0) (castlf (esym eqE0, esym eqE0) sigma) = sigma
        by exact: castlfKV.
      rewrite (@sdotIf_cast_l R _ _ (S_XE :\: E) X E eqX0 eqLift0
           (\1 : 'F[HL]_(S_XE :\: E)) sigma).
      by have -> : castlf (eqX0, eqX0) (\1 : 'F[HL]_(S_XE :\: E))
                 = (\1 : 'F[HL]_X) by exact: castlf1. }
    have HsigEq : castlf (esym eqE0, esym eqE0) sigma = sigma0.
    { rewrite /sigma castlf_comp.
      rewrite (_ : (etrans HsiE (esym eqE0), etrans HsiE (esym eqE0))
                 = (erefl (S_XE :&: E), erefl (S_XE :&: E)));
        last by congr (_, _); apply: eq_irrelevance.
      by rewrite castlf_id. }
    have Hgap_le : rhoXE <= oneX \O sigma.
    { rewrite -subv_ge0 -psdlfE oneXE -phi_lift0 HsigEq; exact: Hgap. }
    (* [A] cutoff: ρ̃ ⪯ (2φ_min/ε̄²)·(I_X⊗ρ_E).                                *)
    (* ρ̃ = formlf(I_X⊗N)ρ ⪯ formlf(I_X⊗N)(I_X⊗σ) [formlf_lef, Hgap_le]        *)
    (*   = I_X⊗(formlf N σ) = I_X⊗(formlf √ρ_E (P·Γ·P))                       *)
    (*   ⪯ I_X⊗(formlf √ρ_E (Thr·P)) [HPEbound] = I_X⊗(Thr·√ρ_E·P·√ρ_E)       *)
    (*   ⪯ I_X⊗(Thr·ρ_E) = Thr·(I_X⊗ρ_E) [P⪯1].                              *)
    have HA : rhotilde <= Thr%:C *: (oneX \O rhoE).
    { rewrite /rhotilde.
      apply: (le_trans (y := formlf (oneX \O NN) (oneX \O sigma))).
        by apply: formlf_lef.
      have A2 : formlf (oneX \O NN) (oneX \O sigma) = oneX \O formlf NN sigma
        by rewrite !liftEr -formlf_lift.
      rewrite A2 -[Thr%:C *: (oneX \O rhoE)]sdotfZr.
      apply: HsdotLef.
      have A3 : formlf NN sigma = formlf srhoE (formlf PE Gamma).
      { rewrite /NN -!formlf_comp; congr (formlf srhoE (formlf PE _)).
        by rewrite /Gamma formlfE (hermlf_adjE (psdlf_herm HisrhoE_psd)). }
      rewrite A3.
      apply: (le_trans (y := formlf srhoE (Thr%:C *: PE))).
        apply: formlf_lef.
        rewrite formlfE (hermlf_adjE (projlf_herm HPE_proj)).
        exact: HPEbound.
      rewrite linearZ.
      apply: lev_wpscale2l; first by rewrite ler0c.
      rewrite -[rhoE in _ <= rhoE](_ : formlf srhoE \1 = rhoE);
        last by rewrite formlf1E (hermlf_adjE (psdlf_herm (sqrtH_psd HrhoE_psd)))
          (sqrtHK HrhoE_psd).
      apply: formlf_lef; apply: obslf_le1; apply: projlf_obs; exact: HPE_proj. }
    (* [B] Δ-term: (1/d_X)·(I_X⊗Δ) ⪯ (φ_min/Tr ρ)·(I_X⊗ρ_E) via phi_min_lb *)
    have HB : ((dim 'H[HL]_X)%:R^-1)%:C *: (oneX \O Delta)
            <= ((@complex.Re R (\Tr rhoXE))^-1 * phi_min E rhoXE)%:C
               *: (oneX \O rhoE).
    { have HrhotildeE_psd : rhotildeE \is psdlf.
      { rewrite /rhotildeE; apply: ptrace_castl_psdlf.
        rewrite /rhotilde formlfE qualifE !h2mx_comp h2mx_adj.
        by apply: psdmx_bimap_closed_gen; move: Prho; rewrite qualifE. }
      have HrhoE_oneX_psd : (oneX \O rhoE) \is psdlf.
      { have Hten : (oneX \O rhoE : 'F[HL]_S_XE) = oneX \⊗ rhoE
          by apply: to_Fnd_inj; rewrite (sdotFT _ _ disXE) to_Fnd_tenE.
        rewrite Hten psdlfE; apply: tenf_ge0; first exact: disXE.
        - by rewrite /oneX; exact: lef01.
        - by move: HrhoE_psd; rewrite psdlfE. }
      have HDelta_le : Delta <= rhoE.
      { rewrite /Delta -[X in _ <= X]subr0; apply: levB; first exact: lexx.
        by rewrite -psdlfE. }
      have Hscalar : ((dim 'H[HL]_X)%:R^-1)%:C
                   <= ((@complex.Re R (\Tr rhoXE))^-1 * phi_min E rhoXE)%:C.
      { rewrite lecR -(ler_pM2l Hrho_pos) mulrA
          (mulfV (lt0r_neq0 Hrho_pos)) mul1r.
        by apply: phi_min_lb. }
      apply: (le_trans (y := ((dim 'H[HL]_X)%:R^-1)%:C *: (oneX \O rhoE))).
      - apply: lev_wpscale2l; first by rewrite ler0c invr_ge0 ler0n.
        exact: HsdotLef HDelta_le.
      - rewrite -subv_ge0 -scalerBl -psdlfE.
        apply: psdlfZ; first by rewrite subr_ge0.
        exact: HrhoE_oneX_psd. }
    (* sum: ρ̄ ⪯ HA + HB = (K·φ_min)·(I_X⊗ρ_E) *)
    rewrite -oneXE /rhobar.
    apply: le_trans; first exact: (levD HA HB).
    by rewrite -scalerDl -rmorphD/= /Thr -mulrDl lexx.
Qed.
(* ================================================================== *)
(* Collision bound, second clause (almost-two-universal route)          *)
(* Tomamichel-Schaffner-Smith-Renner, 'Leftover Hashing Against Quantum *)
(* Side Information' (IEEE Trans. IT 57:5524 (2011); arXiv:1002.2436),   *)
(* Lem. 3 (2nd clause), Eq. 11 — tex lemma:coll-bound /                  *)
(* eqn:minalt-coll-bound (proof via lemma:min-coll-bound (Lem. 23) and   *)
(* lemma:min-bound-1 (Lem. 21), 2nd statement).                          *)
(* math: For a CQ ρ_XE ∈ S_sub(H_XE) and ε̄ > 0, there is a normalized    *)
(*   CQ ρ̄_XE ∈ B^{ε̄}(ρ_XE) with                                         *)
(*     Γ_C(ρ̄_XE | ρ̄_E) ≤ 2^{-Hmin(X|E)_ρ} · (2/ε̄² + 1/Tr ρ).            *)
(*   (ρ̄_E := Tr_X ρ̄_XE is the OWN marginal — the alternative-min-entropy *)
(*   regime, distinct from the optimal-σ first clause `min_coll_bound`.)  *)
(* Note: the paper's printed bound (Eq. 11) drops            *)
(*   the 1/Tr ρ to the constant "+1", i.e. assumes ρ effectively          *)
(*   normalized; the honest consequence of lemma:min-bound-1 (which is    *)
(*   what we prove) carries 1/Tr ρ.  Since here ρ is a sub-normalized     *)
(*   smoothing witness, the (Re Tr ρ)^-1 factor is correct and tight.    *)
(* Proof route: min_bound_op (operator form of lemma:min-bound-1 2nd      *)
(*   statement) gives ρ̄ with ρ̄ ⊑ ((2/ε̄² + 1/Tr ρ)·phi_min ρ)(I_X ⊗ ρ̄_E);*)
(*   coll_from_dmax (lemma:min-coll-bound, Lem. 23) converts that         *)
(*   Loewner bound to Γ_C(ρ̄|ρ̄_E) ≤ that constant · Tr ρ̄ = the constant   *)
(*   (ρ̄ normalized); finally 2^{-Hmin ρ} = phi_min ρ.                     *)
(* path: lhl:coll_bound -> lhl:almost_two_universal_hashing *)
Lemma coll_bound (eps_bar : R) (rhoXE : 'F[HL]_S_XE) :
  rhoXE \is psdlf ->
  0 < @complex.Re R (\Tr rhoXE) ->
  @complex.Re R (\Tr rhoXE) <= 1 ->
  is_cq_state rhoXE ->
  0 < eps_bar ->
  exists (rhobarXE : 'F[HL]_S_XE),
    [/\ rhobarXE \is psdlf,
        @complex.Re R (\Tr rhobarXE) = @complex.Re R (\Tr rhoXE),
        is_cq_state rhobarXE,
        eps_ball eps_bar rhoXE rhobarXE &
        collision_ent rhobarXE (ptrace_castl disXE rhobarXE) <=
          expR ((- hmin E rhoXE +
                 log2 (2%:R * eps_bar^-2 + (@complex.Re R (\Tr rhoXE))^-1))
                * ln 2%:R)].
Proof.
  move=> Prho Hrho_pos Hrho_tr Hcq Hepsbar.
  set K := 2%:R * eps_bar^-2 + (@complex.Re R (\Tr rhoXE))^-1.
  have Hphi_pos : 0 < phi_min E rhoXE
    by apply: phi_min_pos_trace; [exact: Prho | exact: Hrho_tr | exact: Hrho_pos].
  have Heb2_pos : 0 < eps_bar ^+ 2 by exact: exprn_gt0.
  have HK_pos : 0 < K.
  { apply: addr_gt0; last by rewrite invr_gt0.
    by apply: mulr_gt0; [exact: ltr0n | rewrite invr_gt0]. }
  have [rhobar [Hpsd Htr1 Hcqb Hball Hle]] :=
    min_bound_op Prho Hrho_pos Hrho_tr Hcq Hepsbar.
  exists rhobar; split=> //.
  have HsigE_psd : ptrace_castl disXE rhobar \is psdlf
    by exact: (ptrace_castl_psdlf disXE Hpsd).
  have Hc_ge0 : 0 <= K * phi_min E rhoXE
    by apply: mulr_ge0; [exact: ltW HK_pos | exact: ltW Hphi_pos].
  have Hcoll := coll_from_dmax Hpsd HsigE_psd Hc_ge0 Hle.
  apply: (le_trans Hcoll).
  rewrite Htr1.
  (* K · Φ_min(ρ) = 2^{-Hmin(ρ)} · K = expR((−Hmin + log₂ K)·ln 2). *)
  have Hln2 : ln 2%:R != 0 :> R by exact: lt0r_neq0 ln2_gt0.
  have Hexp_log2 : forall y : R, 0 < y -> expR (log2 y * ln 2%:R) = y
    by move=> y Hy; rewrite /log2 -mulrA mulVf // mulr1 lnK.
  have Hphi_exp : expR (- hmin E rhoXE * ln 2%:R) = phi_min E rhoXE.
  { rewrite /hmin opprK; exact: (Hexp_log2 _ Hphi_pos). }
  have HRHS :
      expR ((- hmin E rhoXE + log2 K) * ln 2%:R) = K * phi_min E rhoXE.
  { by rewrite mulrDl expRD Hphi_exp (Hexp_log2 _ HK_pos) mulrC. }
  rewrite HRHS.
  (* (K·Φ_min)·Re Tr ρ ≤ K·Φ_min, since Re Tr ρ ≤ 1 and K·Φ_min ≥ 0. *)
  rewrite -[X in _ <= X]mulr1.
  by apply: ler_wpM2l; [exact: Hc_ge0 | exact: Hrho_tr].
Qed.
End CollBound.
End FvqkdReal.
