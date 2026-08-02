(* -------------------------------------------------------------------- *)
(* eur.v — Smooth entropic uncertainty relation                         *)
(* -------------------------------------------------------------------- *)
(* Module: eur.eur                                        *)
(* Paper: Tomamichel & Renner, 'The Uncertainty Relation for Smooth     *)
(*   Entropies' (PRL 106, 110506 (2011); arXiv:1009.2015), Theorem 1.   *)
(* tex label: thm:mother                                                *)
(* -------------------------------------------------------------------- *)
(* Mirrors the `lhl/lhl.v` pattern: this file hosts the main EUR paper  *)
(* theorem. The exported statement is ambient set-labelled; the matrix  *)
(* proof core is local implementation detail.                           *)
(* -------------------------------------------------------------------- *)
(* --- Library imports --- *)
From HB Require Import structures.
From mathcomp Require Import all_boot all_order all_algebra.
From quantum.external Require Import spectral complex.
From mathcomp.classical Require Import boolp classical_sets.
From mathcomp.reals Require Import reals.
From mathcomp.analysis Require Import ereal.
From quantum Require Import mcextra mcaextra notation hermitian quantum
  cpo mxpred extnum ctopology svd mxnorm hspace qtype.
From quantum.dirac Require Import hstensor.
Import Order.TTheory GRing.Theory Num.Theory Num.Def MxLownerOrder.
(* --- FVQKD imports --- *)
From utils Require Import exports.
From entropy Require Import def prop.
From entropy.smooth Require Import prop.
From eur Require Import def prop.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Section FvqkdReal.
Variable R : realType.
Notation C := (@hermitian.C R).
Notation chsType := (@chsType R).
(* Matrix proof core for the smooth entropic uncertainty relation.       *)
(* Paper: Tomamichel & Renner, 'The Uncertainty Relation for Smooth      *)
(*   Entropies' (PRL 106, 110506 (2011); arXiv:1009.2015), Theorem 1.    *)
(*   Equivalently the K-trivial (single-outcome) special case of         *)
(*   Tomamichel, 'A Framework for Non-Asymptotic Quantum Information      *)
(*   Theory' (arXiv:1203.2142), Theorem 7.2 (Generalized UCR).           *)
(* tex label: thm:mother                                                 *)
(* math: for ρ ∈ S_≤(ℋ_ABC) (sub-normalized), POVMs X={M_x},            *)
(*       Z={N_z} on A, and ε ≥ 0,                                         *)
(*         H^ε_min(X|B)_ρ + H^ε_max(Z|C)_ρ ≥ -log c,                      *)
(*       where c := max_{x,z} ||√M_x √N_z||_∞².                          *)
(*   The R-valued matrix surface adds the well-definedness side          *)
(*   condition `ε < √(Re(Tr ρ))`, which collapses to `ε < 1` when ρ is   *)
(*   normalized; for sub-normalized ρ the bound carries the trace        *)
(*   factor explicitly. The bound `eps ≥ 0` ∧ `eps < √(Tr ρ)` implicitly *)
(*   implies `ρ ≠ 0` (so the proof's `purification_mx_exists` and        *)
(*   dimension/overlap derivations are well-defined).                    *)
(*   The side condition is necessary: when `ε ≥ √(Re(Tr ρ))` the ε-ball *)
(*   admits states of arbitrarily small but positive trace, on which     *)
(*   `hmin_mx → +∞` and `hmax_mx → −∞`. Because `smooth_hmin_mx` and      *)
(*   `smooth_hmax_mx` are R-valued (a `sup`/`inf` over R), an unbounded   *)
(*   witness set triggers MathComp's `sup_out`/`inf_out` default of 0, so *)
(*   the LHS collapses to `0 + 0` and `… ≥ q_of_mx` becomes FALSE for any *)
(*   `q_of_mx > 0`. Hence this hypothesis cannot be dropped. The only     *)
(*   "all-ε" variant lives on `\bar R`, where it holds at the boundary    *)
(*   only through the indeterminate `+∞ + (−∞)` convention and is thus    *)
(*   mathematically vacuous there.                                        *)
(* path: eur:entropic_uncertainty_relation -> *)
(*   bb84:entropic_uncertainty_relation_bb84 -> bb84:bb84_secret *)
Local Lemma entropic_uncertainty_relation_core
    (na nb nc nx nz : nat)
    (eps : R)
    (rhoABC : 'M[C]_(na * nb * nc))
    (M : 'I_nx -> 'M[C]_na) (N : 'I_nz -> 'M[C]_na) :
  rhoABC \is denmx ->
  is_povm_mx M -> is_povm_mx N ->
  0 <= eps -> eps < Num.sqrt (@complex.Re R (\tr rhoABC)) ->
  smooth_hmin_mx eps (rho_XB M rhoABC) +
  smooth_hmax_mx eps (rho_ZC N rhoABC) >=
  q_of_mx M N.
Proof.
  move=> Hden HM HN Heps0 Heps_lt_sqrt.
  rewrite /q_of_mx.
  (* TeX final paragraph: purify rhoABC, prove the pure statement on
     Z|CD, then apply the max-entropy data-processing inequality
     Hmax^eps(Z|CD) <= Hmax^eps(Z|C). *)
  have Hpsd : rhoABC \is psdmx := denmx_psd Hden.
  (* eps ≥ 0 and eps < sqrt(Re(Tr ρ)) ⇒ sqrt(Re(Tr ρ)) > 0 ⇒
     Re(Tr ρ) > 0 ⇒ Tr ρ ≠ 0 ⇒ ρ ≠ 0 (psdmx). *)
  have Hsqrt_pos : 0 < Num.sqrt (@complex.Re R (\tr rhoABC))
    := le_lt_trans Heps0 Heps_lt_sqrt.
  have Htr_real_nn : 0 <= @complex.Re R (\tr rhoABC).
  { by move: (psdmx_trace Hpsd); rewrite lecE/= => /andP[_]. }
  have Htr_pos : 0 < @complex.Re R (\tr rhoABC).
  { have Hsq : 0 < (Num.sqrt (@complex.Re R (\tr rhoABC))) ^+ 2
      by exact: exprn_gt0.
    by move: Hsq; rewrite sqr_sqrtr. }
  have Htr_ne0 : \tr rhoABC != 0.
  { apply/negP => /eqP Htr0.
    by move: Htr_pos; rewrite Htr0 raddf0 ltxx. }
  have Hne : rhoABC != 0.
  { by rewrite -(psdmx_trace_eq0 Hpsd). }
  have Hdim_pos : (0 < na * nb * nc)%N.
  { have Hrank_pos : (0 < \rank rhoABC)%N
      by rewrite lt0n mxrank_eq0 Hne.
    exact: leq_trans Hrank_pos (rank_leq_row rhoABC). }
  have Hna_pos : (0 < na)%N by
    move: Hdim_pos; rewrite !muln_gt0 => /andP[/andP[Hna_pos _] _].
  have Hc : overlap_mx M N != 0 :=
    overlap_mx_povm_neq0 Hna_pos HM HN.
  have Hle : (na * nb * nc <= na * nb * nc)%N by [].
  have [rhoABCD [HrhoABCD_den [Hext HrhoABCD_rk]]] :=
    purification_mx_exists Hden Hne Hle.
  have HrhoABCD_psd : rhoABCD \is psdmx := denmx_psd HrhoABCD_den.
  have HrhoABCD_tr_eq : \tr rhoABCD = \tr rhoABC
    by rewrite tr_ptrace2 Hext.
  have HrhoABCD_nz : rhoABCD != 0.
  { rewrite -(psdmx_trace_eq0 HrhoABCD_psd).
    by rewrite HrhoABCD_tr_eq. }
  pose rhoABCD_cast := purif_reshape rhoABCD.
  have Hcast_den : rhoABCD_cast \is denmx
    by rewrite /rhoABCD_cast /purif_reshape cast_qualifier_diag.
  have Hcast_rk : \rank rhoABCD_cast = 1%N by
    rewrite /rhoABCD_cast purif_reshape_rank.
  have Hcast_tr_eq : \tr rhoABCD_cast = \tr rhoABC by
    rewrite /rhoABCD_cast /purif_reshape mxtrace_castmx_sq
      HrhoABCD_tr_eq.
  have Hcast_eps_lt_sqrt :
      eps < Num.sqrt (@complex.Re R (\tr rhoABCD_cast)) by
    rewrite Hcast_tr_eq.
  have Hstage1 :=
    @ucr_pure_smooth R na nb (nc * (na * nb * nc))%N nx nz eps
      rhoABCD_cast M N Hcast_den Hcast_rk HM HN Hc
      Heps0 Hcast_eps_lt_sqrt.
  have Hinv_XB : rho_XB M rhoABCD_cast = rho_XB M rhoABC :=
    rho_XB_purif_reshape_marginal_mx M Hext.
  have Heps_lt_sqrt_ABCD :
      eps < Num.sqrt (@complex.Re R (\tr rhoABCD)) by
    rewrite HrhoABCD_tr_eq.
  have HDPI :
      smooth_hmax_mx eps (rho_ZC N rhoABCD_cast) <=
      smooth_hmax_mx eps (rho_ZC N rhoABC) :=
    @smooth_hmax_mx_rho_ZC_purif_dpi R na nb nc (na * nb * nc) nz
      eps N rhoABC rhoABCD HrhoABCD_den HrhoABCD_nz
      Hext HN Heps0 Heps_lt_sqrt_ABCD.
  rewrite Hinv_XB in Hstage1.
  apply: le_trans Hstage1 _.
  by apply: lerD.
Qed.
(* Default ambient set-labelled surface for EUR's smooth entropic        *)
(* uncertainty theorem.                                                  *)
(* Paper: Tomamichel & Renner, 'The Uncertainty Relation for Smooth     *)
(*   Entropies' (PRL 106, 110506 (2011); arXiv:1009.2015), Theorem 1    *)
(*   — tex thm:mother — math: H^ε_min(X|B)_ρ + H^ε_max(Z|C)_ρ ≥ q.      *)
(* path: eur:entropic_uncertainty_relation -> *)
(*   bb84:entropic_uncertainty_relation_bb84 -> bb84:bb84_secret *)
Theorem entropic_uncertainty_relation
    (L : finType) (HL : L -> chsType)
    (X B Z C0 : {set L})
    (disXB : [disjoint X & B])
    (disZC : [disjoint Z & C0])
    (na nb nc nx nz : nat)
    (eps : R)
    (rhoABC : 'M[C]_(na * nb * nc))
    (M : 'I_nx -> 'M[C]_na)
    (N : 'I_nz -> 'M[C]_na)
    (dimXB : nx * nb = dim ('H[HL]_(X :|: B)))
    (dimZC : nz * nc = dim ('H[HL]_(Z :|: C0)))
    (dim_X : nx = dim ('H[HL]_X))
    (dim_B : nb = dim ('H[HL]_B))
    (dim_Z : nz = dim ('H[HL]_Z))
    (dim_C : nc = dim ('H[HL]_C0)) :
  rhoABC \is denmx ->
  is_povm_mx M -> is_povm_mx N ->
  0 <= eps -> eps < Num.sqrt (@complex.Re R (\tr rhoABC)) ->
  smooth_hmin B eps (eur_rho_XB disXB rhoABC M dimXB) +
  smooth_hmax C0 eps (eur_rho_ZC disZC rhoABC N dimZC)
    >= q_of_mx M N.
Proof.
  move=> Hden HM HN Heps0 Heps_lt.
  set rhoXB := eur_rho_XB disXB rhoABC M dimXB.
  set rhoZC := eur_rho_ZC disZC rhoABC N dimZC.
  have HrhoXB_psd : rho_XB M rhoABC \is psdmx
    := denmx_psd (rho_XB_subden HM Hden).
  have HrhoZC_psd : rho_ZC N rhoABC \is psdmx
    := denmx_psd (rho_ZC_subden HN Hden).
  have HrhoXB_psd_labelled : rhoXB \is psdlf.
  { rewrite /rhoXB /eur_rho_XB qualifE mx2hK.
    apply: (@castmx_sq_psdmx R _ _ (esym (tenv_dim disXB))).
    have Hprod_psd :
        castmx (etrans dimXB (tenv_dim disXB),
                etrans dimXB (tenv_dim disXB)) (rho_XB M rhoABC) \is psdmx.
    { exact: (@castmx_sq_psdmx R _ _ (etrans dimXB (tenv_dim disXB))
        (rho_XB M rhoABC) HrhoXB_psd). }
    exact: psdmx_bimap_closed_gen Hprod_psd. }
  have HrhoZC_psd_labelled : rhoZC \is psdlf.
  { rewrite /rhoZC /eur_rho_ZC qualifE mx2hK.
    apply: (@castmx_sq_psdmx R _ _ (esym (tenv_dim disZC))).
    have Hprod_psd :
        castmx (etrans dimZC (tenv_dim disZC),
                etrans dimZC (tenv_dim disZC)) (rho_ZC N rhoABC) \is psdmx.
    { exact: (@castmx_sq_psdmx R _ _ (etrans dimZC (tenv_dim disZC))
        (rho_ZC N rhoABC) HrhoZC_psd). }
    exact: psdmx_bimap_closed_gen Hprod_psd. }
  rewrite (smooth_hmin_labelled_mx disXB eps HrhoXB_psd_labelled).
  rewrite (smooth_hmax_labelled_mx disZC eps HrhoZC_psd_labelled).
  have Heur := @entropic_uncertainty_relation_core
    na nb nc nx nz eps rhoABC M N
    Hden HM HN Heps0 Heps_lt.
  have Hbridge_min :
      smooth_hmin_mx eps (biprod_mx disXB rhoXB) =
      smooth_hmin_mx eps (rho_XB M rhoABC).
  { rewrite /rhoXB /eur_rho_XB /biprod_mx mx2hK.
    set Q := castmx _ (@tenv_mxU R L HL X B).
    have HQ_t : Q^*t = castmx (erefl, tenv_dim disXB)
                      (@tenv_mxU R L HL X B)^*t.
    { rewrite /Q.
      exact: (@castmx_mx_mxT _ _ (@adjmx _) _ _ _ _
        (tenv_dim disXB, erefl)
        (@tenv_mxU R L HL X B)). }
    have HQtQ : Q^*t *m Q = 1%:M.
    { rewrite /Q HQ_t mcextra.castmx_mul.
      have HU : (@tenv_mxU R L HL X B)^*t
                  *m (@tenv_mxU R L HL X B) = 1%:M.
      { have := unitarymxK
          (@tenv_mxU_adj_unitarymx R L HL X B disXB).
        by rewrite adjmxK. }
      rewrite HU.
      by case: _ / (tenv_dim disXB); rewrite castmx_id. }
    rewrite castmx_comp.
    rewrite (eq_irrelevance
      (etrans (esym (tenv_dim disXB)) (tenv_dim disXB)) (erefl _)).
    rewrite castmx_id !mulmxA HQtQ mul1mx -mulmxA HQtQ mulmx1.
    rewrite (eq_irrelevance (etrans dimXB (tenv_dim disXB))
      (f_equal2 muln dim_X dim_B)).
    exact: smooth_hmin_mx_cast_bipartite. }
  have Hbridge_max :
      smooth_hmax_mx eps (biprod_mx disZC rhoZC) =
      smooth_hmax_mx eps (rho_ZC N rhoABC).
  { rewrite /rhoZC /eur_rho_ZC /biprod_mx mx2hK.
    set Q := castmx _ (@tenv_mxU R L HL Z C0).
    have HQ_t : Q^*t = castmx (erefl, tenv_dim disZC)
                      (@tenv_mxU R L HL Z C0)^*t.
    { rewrite /Q.
      exact: (@castmx_mx_mxT _ _ (@adjmx _) _ _ _ _
        (tenv_dim disZC, erefl)
        (@tenv_mxU R L HL Z C0)). }
    have HQtQ : Q^*t *m Q = 1%:M.
    { rewrite /Q HQ_t mcextra.castmx_mul.
      have HU : (@tenv_mxU R L HL Z C0)^*t
                  *m (@tenv_mxU R L HL Z C0) = 1%:M.
      { have := unitarymxK
          (@tenv_mxU_adj_unitarymx R L HL Z C0 disZC).
        by rewrite adjmxK. }
      rewrite HU.
      by case: _ / (tenv_dim disZC); rewrite castmx_id. }
    rewrite castmx_comp.
    rewrite (eq_irrelevance
      (etrans (esym (tenv_dim disZC)) (tenv_dim disZC)) (erefl _)).
    rewrite castmx_id !mulmxA HQtQ mul1mx -mulmxA HQtQ mulmx1.
    rewrite (eq_irrelevance (etrans dimZC (tenv_dim disZC))
      (f_equal2 muln dim_Z dim_C)).
    exact: smooth_hmax_mx_cast_bipartite. }
  by rewrite Hbridge_min Hbridge_max.
Qed.
(* Extended-real (\bar R) form of the smooth entropic uncertainty         *)
(* relation, for a NORMALIZED source and the meaningful smoothing regime  *)
(* `0 ≤ ε < 1`.  Honest extended-real companion of                        *)
(* `entropic_uncertainty_relation`: it lifts the R-valued bound through    *)
(* the finiteness bridges `smooth_hminE_EFin`/`smooth_hmaxE_EFin`, which   *)
(* apply precisely because `ε < 1 = √(Tr ρ)` keeps every ε-ball state of   *)
(* positive trace, so both smooth entropies stay finite (= their `%:E`     *)
(* embeddings). This theorem is not generalized to all `ε >= 0`: once      *)
(* `ε ≥ √(Tr ρ)` the ball reaches states of vanishing trace, where         *)
(* `H_min^ε → +∞` and `H_max^ε → −∞`, and the sum `+∞ + (−∞)` is pinned    *)
(* only by MathComp's `adde` convention, which is a mathematically vacuous *)
(* regime for this inequality.                                            *)
(* path: eur:entropic_uncertainty_relation_E -> (extended-real surface;    *)
(*   no downstream consumer, companion of entropic_uncertainty_relation)   *)
Theorem entropic_uncertainty_relation_E
    (L : finType) (HL : L -> chsType)
    (X B Z C0 : {set L})
    (disXB : [disjoint X & B])
    (disZC : [disjoint Z & C0])
    (na nb nc nx nz : nat)
    (eps : R)
    (rhoABC : 'M[C]_(na * nb * nc))
    (M : 'I_nx -> 'M[C]_na)
    (N : 'I_nz -> 'M[C]_na)
    (dimXB : nx * nb = dim ('H[HL]_(X :|: B)))
    (dimZC : nz * nc = dim ('H[HL]_(Z :|: C0)))
    (dim_X : nx = dim ('H[HL]_X))
    (dim_B : nb = dim ('H[HL]_B))
    (dim_Z : nz = dim ('H[HL]_Z))
    (dim_C : nc = dim ('H[HL]_C0)) :
  rhoABC \is den1mx ->
  is_povm_mx M -> is_povm_mx N ->
  0 <= eps -> eps < 1 ->
  ((q_of_mx M N)%:E <=
   smooth_hminE B eps (eur_rho_XB disXB rhoABC M dimXB) +
   smooth_hmaxE C0 eps (eur_rho_ZC disZC rhoABC N dimZC))%E.
Proof.
  move=> Hden1 HM HN Heps0 Heps1.
  have Hden : rhoABC \is denmx := den1mx_den Hden1.
  have Htr1 : \tr rhoABC = 1 by have /den1mxP[_ /eqP ->] := Hden1.
  have Heps_lt : eps < Num.sqrt (@complex.Re R (\tr rhoABC)).
  { rewrite Htr1 re_realid sqrtr1. exact: Heps1. }
  have Heur := @entropic_uncertainty_relation L HL X B Z C0 disXB disZC
    na nb nc nx nz eps rhoABC M N dimXB dimZC dim_X dim_B dim_Z dim_C
    Hden HM HN Heps0 Heps_lt.
  have HXB_psd : eur_rho_XB disXB rhoABC M dimXB \is psdlf
    := eur_rho_XB_psd disXB dimXB HM Hden1.
  have HZC_psd : eur_rho_ZC disZC rhoABC N dimZC \is psdlf
    := eur_rho_ZC_psd disZC dimZC HN Hden1.
  have HXB_tr : @complex.Re R (\Tr (eur_rho_XB disXB rhoABC M dimXB)) <= 1
    := eur_rho_XB_tr_le1 disXB dimXB HM Hden1.
  have HZC_tr : @complex.Re R (\Tr (eur_rho_ZC disZC rhoABC N dimZC)) <= 1
    := eur_rho_ZC_tr_le1 disZC dimZC HN Hden1.
  have HXB_eps :
      0 <= eps < Num.sqrt (@complex.Re R
        (\Tr (eur_rho_XB disXB rhoABC M dimXB))) by
    rewrite (eur_rho_XB_tr1 disXB dimXB HM Hden1) re_realid sqrtr1
      Heps0 Heps1.
  have HZC_eps :
      0 <= eps < Num.sqrt (@complex.Re R
        (\Tr (eur_rho_ZC disZC rhoABC N dimZC))) by
    rewrite (eur_rho_ZC_tr1 disZC dimZC HN Hden1) re_realid sqrtr1
      Heps0 Heps1.
  rewrite (@smooth_hminE_EFin R L HL X B disXB eps
    (eur_rho_XB disXB rhoABC M dimXB) HXB_psd HXB_tr HXB_eps).
  rewrite (@smooth_hmaxE_EFin R L HL (Z :|: C0) C0 eps
    (eur_rho_ZC disZC rhoABC N dimZC) HZC_psd HZC_tr HZC_eps).
  rewrite -EFinD lee_fin.
  exact: Heur.
Qed.
End FvqkdReal.
