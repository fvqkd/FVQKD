(* -------------------------------------------------------------------- *)
(* prop.v — Entropy characterization helpers for def.v              *)
(* -------------------------------------------------------------------- *)
(* Module: entropy.prop                         *)
(*                                                                       *)
(* These helper lemmas provide the smooth-min/smooth-max attainment,    *)
(* lower-bound, and representation interfaces used by entropy modules.  *)
(* -------------------------------------------------------------------- *)

From HB Require Import structures.
From mathcomp Require Import all_boot all_order all_algebra finmap fingroup perm.
From quantum.external Require Import spectral complex.
From mathcomp.classical Require Import boolp classical_sets.
From mathcomp Require Import interval_inference.
From mathcomp.reals Require Import reals.
From mathcomp.analysis.topology_theory Require Import topology.
From mathcomp.analysis.normedtype_theory Require Import normedtype.
From mathcomp.analysis Require Import realfun sequences exp ereal.
From mathcomp.real_closed Require Import mxtens.
From Stdlib Require Import Psatz.
Require Import mathcomp.algebra.archimedean.
From quantum Require Import mcextra mcaextra notation hermitian quantum
  cpo mxpred extnum ctopology svd mxnorm hspace inhabited summable.
From quantum.dirac Require Import hstensor setdec.

Import Order.TTheory GRing.Theory Num.Theory Num.Def MxLownerOrder.
Import VectorInternalTheory.

From utils Require Import exports.
From entropy Require Import def pre.

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
(* Matrix smooth-entropy cast facts                                    *)
(* ================================================================== *)

(* path: entropy:smooth_hmax_mx_cast_bipartite -> bb84:stat -> *)
(*   bb84:bb84_secret *)
Lemma smooth_hmax_mx_cast_bipartite
    (n1 n2 n1' n2' : nat) (ea : n1 = n1') (eb : n2 = n2')
    (rho : 'M[C]_(n1 * n2)) (eps0 : R) :
  smooth_hmax_mx eps0
    (castmx (f_equal2 muln ea eb, f_equal2 muln ea eb) rho) =
  smooth_hmax_mx eps0 rho.
Proof.
  by case: n1' / ea; case: n2' / eb; rewrite castmx_id.
Qed.

(* path: entropy:smooth_hmin_mx_cast_bipartite -> *)
(*   eur:entropic_uncertainty_relation -> *)
(*   bb84:entropic_uncertainty_relation_bb84 -> bb84:bb84_secret *)
Lemma smooth_hmin_mx_cast_bipartite
    (n1 n2 n1' n2' : nat) (ea : n1 = n1') (eb : n2 = n2')
    (rho : 'M[C]_(n1 * n2)) (eps0 : R) :
  smooth_hmin_mx eps0
    (castmx (f_equal2 muln ea eb, f_equal2 muln ea eb) rho) =
  smooth_hmin_mx eps0 rho.
Proof.
  by case: n1' / ea; case: n2' / eb; rewrite castmx_id.
Qed.

(* ================================================================== *)
(* Matrix-level entropy facts.                                          *)
(* ================================================================== *)

Section MatrixEntropyFacts.
Variable (na nb : nat).

(* path: entropy:mmix_mx_psd -> bb84:stat -> bb84:bb84_secret *)
Lemma mmix_mx_psd (n : nat) :
  @mmix_mx R n \is psdmx.
Proof.
  rewrite /mmix_mx; apply: psdmxZ; last exact: psdmx1.
  by rewrite lecE /= eqxx invr_ge0 ler0n.
Qed.

(* path: entropy:tr_mmix_mx -> bb84:stat -> bb84:bb84_secret *)
Lemma tr_mmix_mx (n : nat) :
  (0 < n)%N -> \tr (@mmix_mx R n) = 1.
Proof.
  move=> Hn.
  rewrite /mmix_mx mxtraceZ mxtrace1.
  rewrite -mulr_natr fmorphV.
  rewrite [1 * n%:R]mul1r.
  rewrite -natrC.
  by rewrite mulVf ?rmorph1 // fmorph_eq0 pnatr_eq0 -lt0n.
Qed.

(* path: entropy:mmix_mx_den1 -> entropy:hmax_mx_has_sup -> bb84:stat -> *)
(*   bb84:bb84_secret *)
Lemma mmix_mx_den1 (n : nat) :
  (0 < n)%N -> @mmix_mx R n \is den1mx.
Proof.
  move=> Hn; apply/den1mxP; split.
  - exact: mmix_mx_psd.
  - by apply/eqP; rewrite tr_mmix_mx.
Qed.

End MatrixEntropyFacts.

(* Tensor-factored unitary-conjugation invariance for hmin/hmax_mx and  *)
(* smooth variants (smooth-entropy route). For Q := P_A *t P_B unitary, the *)
(* witness 1 *t sigma in hmin/hmax_mx becomes 1 *t (P_B^*t sigma P_B)   *)
(* after Q-conjugation (uses unitarymxKV on P_A). The smooth versions   *)
(* additionally need rho psdmx for the gfidelity invariance under the   *)
(* tau ↔ Q^*t tau Q ball bijection. Consumes ucr_reduction (BB84).      *)

Section MatrixUnitaryConj.
Variable (na nb : nat).

(* Helper: hmin_mx is invariant under tensor-factored unitary conjugation. *)
(* path: entropy:hmin_mx_unitarymx_conj_tens -> *)
(*   bb84:bb84_secret *)
Lemma hmin_mx_unitarymx_conj_tens
    (P_A : 'M[C]_na) (P_B : 'M[C]_nb)
    (rho : 'M[C]_(na * nb)) :
  P_A \is unitarymx -> P_B \is unitarymx ->
  hmin_mx ((P_A *t P_B)^*t *m rho *m (P_A *t P_B)) = hmin_mx rho.
Proof.
  move=> HPA HPB.
  have HQ_unit : (P_A *t P_B) \is unitarymx by apply: unitarymx_tens.
  have HQQt : (P_A *t P_B) *m (P_A *t P_B)^*t = 1%:M := unitarymxK HQ_unit.
  have HQtQ : (P_A *t P_B)^*t *m (P_A *t P_B) = 1%:M := unitarymxKV HQ_unit.
  rewrite /hmin_mx.
  have Hfeas_eq :
      [set v : R | exists sigma : 'M[C]_nb,
        sigma \is psdmx /\
        (1%:M *t sigma -
          ((P_A *t P_B)^*t *m rho *m (P_A *t P_B))) \is psdmx /\
        v = @complex.Re R (\tr sigma)]%classic =
      [set v : R | exists sigma : 'M[C]_nb,
        sigma \is psdmx /\
        (1%:M *t sigma - rho) \is psdmx /\
        v = @complex.Re R (\tr sigma)]%classic.
  { apply/predeqP=> v; split.
  - (* Q-conjugate side -> original side *)
    move=> [sigma [Hsigma_psd [Hpsd_diff Hv]]].
    exists (P_B *m sigma *m P_B^*t); split.
    { have := psdmx_bimap_closed_gen P_B Hsigma_psd; by []. }
    split.
    { (* (1 *t (P_B sigma P_B^*t) - rho) psdmx *)
      have Hwit_eq :
        1%:M *t (P_B *m sigma *m P_B^*t) =
        (P_A *t P_B) *m (1%:M *t sigma) *m (P_A *t P_B)^*t.
      { rewrite tensmx_adj tensmx_mul tensmx_mul.
        rewrite mulmx1.
        by rewrite (unitarymxK HPA). }
      have Hrho_eq :
        rho = (P_A *t P_B) *m
              ((P_A *t P_B)^*t *m rho *m (P_A *t P_B)) *m
              (P_A *t P_B)^*t.
      { rewrite !mulmxA HQQt mul1mx.
        rewrite -!mulmxA HQQt mulmx1.
        by []. }
      rewrite Hwit_eq [X in _ - X]Hrho_eq.
      rewrite -mulmxBl -mulmxBr.
      have := psdmx_bimap_closed_gen (P_A *t P_B) Hpsd_diff; by []. }
    rewrite Hv mxtrace_mulC mulmxA (unitarymxKV HPB) mul1mx.
    by [].
  - (* original side -> Q-conjugate side *)
    move=> [sigma [Hsigma_psd [Hpsd_diff Hv]]].
    exists (P_B^*t *m sigma *m P_B); split.
    { have := psdmx_bimap_closed_gen P_B^*t Hsigma_psd.
      by rewrite adjmxK. }
    split.
    { have Hwit_eq :
        1%:M *t (P_B^*t *m sigma *m P_B) =
        (P_A *t P_B)^*t *m (1%:M *t sigma) *m (P_A *t P_B).
      { rewrite tensmx_adj tensmx_mul tensmx_mul.
        rewrite mulmx1.
        by rewrite (unitarymxKV HPA). }
      rewrite Hwit_eq.
      have Hrho_eq :
        (P_A *t P_B)^*t *m rho *m (P_A *t P_B)
        = (P_A *t P_B)^*t *m (1%:M *m rho *m 1%:M) *m (P_A *t P_B)
        by rewrite mul1mx mulmx1.
      rewrite [X in _ - X]Hrho_eq.
      rewrite -mulmxBl -mulmxBr.
      rewrite mul1mx mulmx1.
      have := psdmx_bimap_closed_gen (P_A *t P_B)^*t Hpsd_diff.
      by rewrite adjmxK. }
    rewrite Hv mxtrace_mulC mulmxA (unitarymxK HPB) mul1mx.
    by []. }
  exact: (congr1 (fun S : set R => - log2 (inf S)) Hfeas_eq).
Qed.

(* gfidelity unitary-conj invariance without trace bound. Generalises       *)
(* gfid_unitary_conj_mx (fid.v:1543) via alt_gfid_gen +                  *)
(* fid_unitary_conj_mx. Mirrors gfid_tenv_mxU_conj_eq_mx.            *)
(* path: entropy:gfidelity_unitarymx_conj_psd_only -> *)
(*   bb84:bb84_secret *)
Lemma gfidelity_unitarymx_conj_psd_only {n : nat}
    (U : 'M[C]_n) (rho sigma : 'M[C]_n) :
  U \is unitarymx -> rho \is psdmx -> sigma \is psdmx ->
  gfidelity (U *m rho *m U^*t) (U *m sigma *m U^*t) = gfidelity rho sigma.
Proof.
  move=> HU Hrho Hsigma.
  have HUadj : U^*t \is unitarymx by rewrite trmxC_unitary.
  have HUrho : U *m rho *m U^*t \is psdmx.
  { exact: psdmx_bimap_closed_gen Hrho. }
  have HUsigma : U *m sigma *m U^*t \is psdmx.
  { exact: psdmx_bimap_closed_gen Hsigma. }
  rewrite (alt_gfid_gen Hrho Hsigma).
  rewrite (alt_gfid_gen HUrho HUsigma).
  have Htr_preserve :
      forall (X : 'M[C]_n), \tr (U *m X *m U^*t) = \tr X.
  { move=> X.
    by rewrite mxtrace_mulC mulmxA (unitarymxKV HU) mul1mx. }
  rewrite !Htr_preserve.
    by rewrite (fid_unitary_conj_mx HU Hrho Hsigma).
Qed.

(* hmax_mx invariance under tensor-factored unitary conjugation; needs    *)
(* rho psdmx (gfidelity invariance prerequisite).                         *)
(* path: entropy:hmax_mx_unitarymx_conj_tens -> *)
(*   bb84:bb84_secret *)
Lemma hmax_mx_unitarymx_conj_tens
    (P_A : 'M[C]_na) (P_B : 'M[C]_nb)
    (rho : 'M[C]_(na * nb)) :
  P_A \is unitarymx -> P_B \is unitarymx ->
  rho \is psdmx ->
  hmax_mx ((P_A *t P_B)^*t *m rho *m (P_A *t P_B)) = hmax_mx rho.
Proof.
  move=> HPA HPB Hrho_psd.
  have HQ_unit : (P_A *t P_B) \is unitarymx by apply: unitarymx_tens.
  have HQQt : (P_A *t P_B) *m (P_A *t P_B)^*t = 1%:M := unitarymxK HQ_unit.
  have HQtQ : (P_A *t P_B)^*t *m (P_A *t P_B) = 1%:M := unitarymxKV HQ_unit.
  have HQadj_unit : (P_A *t P_B)^*t \is unitarymx by rewrite trmxC_unitary.
  have Hrho'_psd : (P_A *t P_B)^*t *m rho *m (P_A *t P_B) \is psdmx.
  { have := psdmx_bimap_closed_gen (P_A *t P_B)^*t Hrho_psd.
    by rewrite adjmxK. }
  have Hpi_fwd :
      P_A *m mmix_mx na *m P_A^*t = mmix_mx na.
  { rewrite /mmix_mx -scalemxAr mulmx1 -scalemxAl.
    by rewrite (unitarymxK HPA). }
  have Hpi_bwd :
      P_A^*t *m mmix_mx na *m P_A = mmix_mx na.
  { rewrite /mmix_mx -scalemxAr mulmx1 -scalemxAl.
    by rewrite (unitarymxKV HPA). }
  rewrite /hmax_mx.
  have Hfeas_eq :
      [set v : R | exists sigma : 'M[C]_nb,
        sigma \is den1mx /\
        elog2
          (na%:R *
            (gfidelity ((P_A *t P_B)^*t *m rho *m (P_A *t P_B))
               (mmix_mx na *t sigma)) ^+ 2) = v%:E]%classic =
      [set v : R | exists sigma : 'M[C]_nb,
        sigma \is den1mx /\
        elog2 (na%:R * (gfidelity rho (mmix_mx na *t sigma)) ^+ 2) =
          v%:E]%classic.
  { apply/predeqP=> v; split.
    - move=> [sigma [Hsigma_den Hfid_eq]].
      exists (P_B *m sigma *m P_B^*t); split.
      { exact: den1mx_unitary_closed HPB Hsigma_den. }
      have Hwit_eq :
        mmix_mx na *t (P_B *m sigma *m P_B^*t) =
        (P_A *t P_B) *m (mmix_mx na *t sigma) *m (P_A *t P_B)^*t.
      { rewrite tensmx_adj tensmx_mul tensmx_mul.
        by rewrite Hpi_fwd. }
      have Hrho_eq :
        rho = (P_A *t P_B) *m
              ((P_A *t P_B)^*t *m rho *m (P_A *t P_B)) *m
              (P_A *t P_B)^*t.
      { rewrite !mulmxA HQQt mul1mx.
        rewrite -!mulmxA HQQt mulmx1.
        by []. }
      rewrite [X in elog2 (na%:R * (gfidelity X _) ^+ _) = _]Hrho_eq.
      rewrite Hwit_eq.
      have Hpi_psd : mmix_mx na \is psdmx := mmix_mx_psd na.
      have Hsigma_psd : sigma \is psdmx by move/den1mxP: Hsigma_den => [].
      have Hwit_psd : (mmix_mx na *t sigma) \is psdmx
        by exact: psdmx_tens Hpi_psd Hsigma_psd.
      rewrite (gfidelity_unitarymx_conj_psd_only HQ_unit Hrho'_psd Hwit_psd).
      exact: Hfid_eq.
    - move=> [sigma [Hsigma_den Hfid_eq]].
      exists (P_B^*t *m sigma *m P_B); split.
      { have HPB_adj : P_B^*t \is unitarymx by rewrite trmxC_unitary.
        have := den1mx_unitary_closed HPB_adj Hsigma_den.
        by rewrite adjmxK. }
      have Hwit_eq :
        mmix_mx na *t (P_B^*t *m sigma *m P_B) =
        (P_A *t P_B)^*t *m (mmix_mx na *t sigma) *m (P_A *t P_B).
      { rewrite tensmx_adj tensmx_mul tensmx_mul.
        by rewrite Hpi_bwd. }
      rewrite Hwit_eq.
      have Hpi_psd : mmix_mx na \is psdmx := mmix_mx_psd na.
      have Hsigma_psd : sigma \is psdmx by move/den1mxP: Hsigma_den => [].
      have Hwit_psd : (mmix_mx na *t sigma) \is psdmx
        by exact: psdmx_tens Hpi_psd Hsigma_psd.
      have Heq_fid : gfidelity ((P_A *t P_B)^*t *m rho *m (P_A *t P_B))
                  ((P_A *t P_B)^*t *m (mmix_mx na *t sigma) *m (P_A *t P_B))
              = gfidelity rho (mmix_mx na *t sigma).
      { have := gfidelity_unitarymx_conj_psd_only HQadj_unit Hrho_psd Hwit_psd.
        by rewrite adjmxK. }
      rewrite Heq_fid.
      exact: Hfid_eq. }
  exact: (congr1 (fun S : set R => sup S) Hfeas_eq).
Qed.

(* Strategy: tau ↔ Q^*t *m tau *m Q ball bijection. psdmx preserved by     *)
(* psdmx_bimap_closed_gen, trace by mxtrace_mulC + Q^*t Q = 1, pur_dist by *)
(* gfidelity_unitarymx_conj_psd_only. Needs rho psdmx since gfidelity      *)
(* invariance requires both args psd. Inner hmin_mx bridged by helper.    *)
(* path: entropy:smooth_hmin_mx_unitarymx_conj_tens -> *)
(*   bb84:bb84_secret *)
Lemma smooth_hmin_mx_unitarymx_conj_tens
    (P_A : 'M[C]_na) (P_B : 'M[C]_nb)
    (rho : 'M[C]_(na * nb)) (eps : R) :
  P_A \is unitarymx -> P_B \is unitarymx ->
  rho \is psdmx ->
  smooth_hmin_mx eps ((P_A *t P_B)^*t *m rho *m (P_A *t P_B)) =
    smooth_hmin_mx eps rho.
Proof.
  move=> HPA HPB Hrho_psd.
  have HQ_unit : (P_A *t P_B) \is unitarymx by apply: unitarymx_tens.
  have HQadj_unit : (P_A *t P_B)^*t \is unitarymx by rewrite trmxC_unitary.
  have HQQt : (P_A *t P_B) *m (P_A *t P_B)^*t = 1%:M := unitarymxK HQ_unit.
  have HQtQ : (P_A *t P_B)^*t *m (P_A *t P_B) = 1%:M := unitarymxKV HQ_unit.
  have Hrho'_psd : (P_A *t P_B)^*t *m rho *m (P_A *t P_B) \is psdmx.
  { have := psdmx_bimap_closed_gen (P_A *t P_B)^*t Hrho_psd.
    by rewrite adjmxK. }
  rewrite /smooth_hmin_mx.
  have Hfeas_eq :
      [set v : R | exists tau : 'M[C]_(na * nb),
        (tau \is denmx) && (0 < @complex.Re R (\tr tau)) &&
        (pur_dist_mx tau
          ((P_A *t P_B)^*t *m rho *m (P_A *t P_B)) <= eps) /\
        v = hmin_mx tau]%classic =
      [set v : R | exists tau : 'M[C]_(na * nb),
        (tau \is denmx) && (0 < @complex.Re R (\tr tau)) &&
        (pur_dist_mx tau rho <= eps) /\
        v = hmin_mx tau]%classic.
  { apply/predeqP=> v; split.
  - (* Q-conj side feasible -> original side feasible *)
    move=> [tau [Hball Hv]].
    move: Hball => /andP [/andP [/andP [Htau_psd Htau_tr] Htau_pos] Hpd_le].
    exists ((P_A *t P_B) *m tau *m (P_A *t P_B)^*t); split.
    + apply/andP; split.
      * apply/andP; split.
        -- apply/andP; split.
           ++ have := psdmx_bimap_closed_gen (P_A *t P_B) Htau_psd; by [].
           ++ rewrite mxtrace_mulC mulmxA HQtQ mul1mx.
              by [].
        -- rewrite mxtrace_mulC mulmxA HQtQ mul1mx.
           exact: Htau_pos.
      * (* pur_dist_mx ((Q tau Q^*t) rho <= eps from pur_dist_mx tau (Q^*t rho Q) <= eps *)
        rewrite /pur_dist_mx.
        have Hrho_eq : rho =
            (P_A *t P_B) *m
            ((P_A *t P_B)^*t *m rho *m (P_A *t P_B)) *m
            (P_A *t P_B)^*t.
        { rewrite !mulmxA HQQt mul1mx.
          rewrite -!mulmxA HQQt mulmx1.
          by []. }
        rewrite [X in gfidelity _ X]Hrho_eq.
        rewrite (gfidelity_unitarymx_conj_psd_only HQ_unit Htau_psd Hrho'_psd).
        exact: Hpd_le.
    + rewrite Hv.
      pose tauQ := (P_A *t P_B) *m tau *m (P_A *t P_B)^*t.
      have Htau_recover :
        (P_A *t P_B)^*t *m tauQ *m (P_A *t P_B) = tau.
      { rewrite /tauQ !mulmxA HQtQ mul1mx.
        rewrite -!mulmxA HQtQ mulmx1.
        by []. }
      have Heq_helper :=
        @hmin_mx_unitarymx_conj_tens P_A P_B tauQ HPA HPB.
      rewrite Htau_recover in Heq_helper.
      exact: Heq_helper.
  - (* original side feasible -> Q-conj side feasible *)
    move=> [tau [Hball Hv]].
    move: Hball => /andP [/andP [/andP [Htau_psd Htau_tr] Htau_pos] Hpd_le].
    exists ((P_A *t P_B)^*t *m tau *m (P_A *t P_B)); split.
    + apply/andP; split.
      * apply/andP; split.
        -- apply/andP; split.
           ++ have := psdmx_bimap_closed_gen (P_A *t P_B)^*t Htau_psd.
              by rewrite adjmxK.
           ++ rewrite mxtrace_mulC mulmxA HQQt mul1mx.
              by [].
        -- rewrite mxtrace_mulC mulmxA HQQt mul1mx.
           exact: Htau_pos.
      * rewrite /pur_dist_mx.
        have Heq_fid : gfidelity ((P_A *t P_B)^*t *m tau *m (P_A *t P_B))
                    ((P_A *t P_B)^*t *m rho *m (P_A *t P_B))
                = gfidelity tau rho.
        { have := gfidelity_unitarymx_conj_psd_only HQadj_unit Htau_psd Hrho_psd.
          by rewrite adjmxK. }
        rewrite Heq_fid.
        exact: Hpd_le.
    + rewrite Hv.
      by rewrite (@hmin_mx_unitarymx_conj_tens P_A P_B _ HPA HPB). }
  exact: (congr1 (fun S : set R => sup S) Hfeas_eq).
Qed.

(* Mirror of smooth_hmin counterpart with inf and hmax_mx helper.          *)
(* path: entropy:smooth_hmax_mx_unitarymx_conj_tens -> *)
(*   bb84:bb84_secret *)
Lemma smooth_hmax_mx_unitarymx_conj_tens
    (P_A : 'M[C]_na) (P_B : 'M[C]_nb)
    (rho : 'M[C]_(na * nb)) (eps : R) :
  P_A \is unitarymx -> P_B \is unitarymx ->
  rho \is psdmx ->
  smooth_hmax_mx eps ((P_A *t P_B)^*t *m rho *m (P_A *t P_B)) =
    smooth_hmax_mx eps rho.
Proof.
  move=> HPA HPB Hrho_psd.
  have HQ_unit : (P_A *t P_B) \is unitarymx by apply: unitarymx_tens.
  have HQadj_unit : (P_A *t P_B)^*t \is unitarymx by rewrite trmxC_unitary.
  have HQQt : (P_A *t P_B) *m (P_A *t P_B)^*t = 1%:M := unitarymxK HQ_unit.
  have HQtQ : (P_A *t P_B)^*t *m (P_A *t P_B) = 1%:M := unitarymxKV HQ_unit.
  have Hrho'_psd : (P_A *t P_B)^*t *m rho *m (P_A *t P_B) \is psdmx.
  { have := psdmx_bimap_closed_gen (P_A *t P_B)^*t Hrho_psd.
    by rewrite adjmxK. }
  rewrite /smooth_hmax_mx.
  have Hfeas_eq :
      [set v : R | exists tau : 'M[C]_(na * nb),
        (tau \is denmx) && (0 < @complex.Re R (\tr tau)) &&
        (pur_dist_mx tau
          ((P_A *t P_B)^*t *m rho *m (P_A *t P_B)) <= eps) /\
        v = hmax_mx tau]%classic =
      [set v : R | exists tau : 'M[C]_(na * nb),
        (tau \is denmx) && (0 < @complex.Re R (\tr tau)) &&
        (pur_dist_mx tau rho <= eps) /\
        v = hmax_mx tau]%classic.
  { apply/predeqP=> v; split.
  - move=> [tau [Hball Hv]].
    move: Hball => /andP [/andP [/andP [Htau_psd Htau_tr] Htau_pos] Hpd_le].
    exists ((P_A *t P_B) *m tau *m (P_A *t P_B)^*t); split.
    + apply/andP; split.
      * apply/andP; split.
        -- apply/andP; split.
           ++ have := psdmx_bimap_closed_gen (P_A *t P_B) Htau_psd; by [].
           ++ rewrite mxtrace_mulC mulmxA HQtQ mul1mx.
              by [].
        -- rewrite mxtrace_mulC mulmxA HQtQ mul1mx.
           exact: Htau_pos.
      * rewrite /pur_dist_mx.
        have Hrho_eq : rho =
            (P_A *t P_B) *m
            ((P_A *t P_B)^*t *m rho *m (P_A *t P_B)) *m
            (P_A *t P_B)^*t.
        { rewrite !mulmxA HQQt mul1mx.
          rewrite -!mulmxA HQQt mulmx1.
          by []. }
        rewrite [X in gfidelity _ X]Hrho_eq.
        rewrite (gfidelity_unitarymx_conj_psd_only HQ_unit Htau_psd Hrho'_psd).
        exact: Hpd_le.
    + rewrite Hv.
      pose tauQ := (P_A *t P_B) *m tau *m (P_A *t P_B)^*t.
      have Htau_recover :
        (P_A *t P_B)^*t *m tauQ *m (P_A *t P_B) = tau.
      { rewrite /tauQ !mulmxA HQtQ mul1mx.
        rewrite -!mulmxA HQtQ mulmx1.
        by []. }
      have Htau_Q_psd : tauQ \is psdmx.
      { rewrite /tauQ.
        have := psdmx_bimap_closed_gen (P_A *t P_B) Htau_psd; by []. }
      have Heq_helper :=
        @hmax_mx_unitarymx_conj_tens P_A P_B tauQ HPA HPB Htau_Q_psd.
      rewrite Htau_recover in Heq_helper.
      exact: Heq_helper.
  - move=> [tau [Hball Hv]].
    move: Hball => /andP [/andP [/andP [Htau_psd Htau_tr] Htau_pos] Hpd_le].
    exists ((P_A *t P_B)^*t *m tau *m (P_A *t P_B)); split.
    + apply/andP; split.
      * apply/andP; split.
        -- apply/andP; split.
           ++ have := psdmx_bimap_closed_gen (P_A *t P_B)^*t Htau_psd.
              by rewrite adjmxK.
           ++ rewrite mxtrace_mulC mulmxA HQQt mul1mx.
              by [].
        -- rewrite mxtrace_mulC mulmxA HQQt mul1mx.
           exact: Htau_pos.
      * rewrite /pur_dist_mx.
        have Heq_fid : gfidelity ((P_A *t P_B)^*t *m tau *m (P_A *t P_B))
                    ((P_A *t P_B)^*t *m rho *m (P_A *t P_B))
                = gfidelity tau rho.
        { have := gfidelity_unitarymx_conj_psd_only HQadj_unit Htau_psd Hrho_psd.
          by rewrite adjmxK. }
        rewrite Heq_fid.
        exact: Hpd_le.
    + rewrite Hv.
      by rewrite (@hmax_mx_unitarymx_conj_tens P_A P_B _ HPA HPB Htau_psd). }
  exact: (congr1 (fun S : set R => inf S) Hfeas_eq).
Qed.

End MatrixUnitaryConj.

(* ================================================================== *)
(* Matrix hmax/smooth-hmax support facts.                              *)
(* ================================================================== *)

(* hmax_mx_has_sup *)
(* infra: no tex label — reusable hmax witness-set boundedness.            *)
(* path: entropy:hmax_mx_has_sup -> bb84:stat -> bb84:bb84_secret *)
Lemma hmax_mx_has_sup {na nb : nat} (rho : 'M[C]_(na * nb)) :
  (0 < na)%N ->
  (0 < nb)%N ->
  rho \is denmx ->
  0 < @complex.Re R (\tr rho) ->
  has_sup [set v : R | exists sigma : 'M[C]_nb,
    sigma \is den1mx /\
    elog2 (na%:R * (gfidelity rho (mmix_mx na *t sigma)) ^+ 2) = v%:E].
Proof.
  move=> Hna_pos Hnb_pos Hrho_den Hrho_tr_pos.
  have /denmxP[Hrho Hrho_trC] := Hrho_den.
  have Hrho_tr : @complex.Re R (\tr rho) <= 1
    by move: Hrho_trC; rewrite lecE /= => /andP [_].
  have HRe_realM : forall (cc : R) (zz : C),
      @complex.Re R (cc%:C * zz) = cc * @complex.Re R zz.
  { move=> cc zz; case: zz => a b /=. by rewrite mul0r subr0. }
  have Hnonempty :
    nonempty [set v : R | exists sigma : 'M[C]_nb,
      sigma \is den1mx /\
      elog2 (na%:R * (gfidelity rho (mmix_mx na *t sigma)) ^+ 2)
        = v%:E].
  { pose sigma_w : 'M[C]_nb := mmix_mx nb.
    pose XI : 'M[C]_(na * nb) := mmix_mx na *t sigma_w.
    have Hsigma_w_den : sigma_w \is den1mx
      by rewrite /sigma_w; exact: mmix_mx_den1.
    have Hsigma_w_psd : sigma_w \is psdmx
      by move/den1mxP: Hsigma_w_den => [].
    have HXI_psd : XI \is psdmx
      by exact: psdmx_tens (mmix_mx_psd na) Hsigma_w_psd.
    pose t := @complex.Re R (\tr rho).
    pose dinv : R := (na%:R)^-1%R * (nb%:R)^-1%R.
    have Hdinv_pos : 0 < dinv
      by rewrite /dinv mulr_gt0 ?invr_gt0 ?ltr0n.
    have Hdinv_ge0 : 0 <= dinv := ltW Hdinv_pos.
    have Hdinv_C_ge0 : (0 : C) <= dinv%:C
      by rewrite lecE /= eqxx Hdinv_ge0.
    have HXI_eq : XI = dinv%:C *: (1%:M : 'M[C]_(na * nb)).
    { rewrite /XI /sigma_w /mmix_mx /dinv.
      have Hcoef :
          (((na%:R : R)^-1)%:C) * (((nb%:R : R)^-1)%:C) =
          dinv%:C.
      { by rewrite /dinv -rmorphM. }
      apply/matrixP=> i j.
      case: (mxtens_indexP i)=> i0 i1.
      case: (mxtens_indexP j)=> j0 j1.
      rewrite mxE !mxtens_indexK/= !mxE
        (can_eq (@mxtens_indexK _ _)) -pair_eqE/=.
      rewrite -Hcoef.
      case H0: (i0 == j0); case H1: (i1 == j1);
        rewrite /= ?mul0r ?mulr0 ?mul1r ?mulr1
          ?mulr0n ?mulr1n ?mulrA;
        by rewrite ?mul0r ?mulr0. }
    have scale_lemx_local :
        forall (x y : 'M[C]_(na * nb)) (a : R),
          0 <= a -> x <= y -> a%:C *: x <= a%:C *: y.
    { move=> x y a Ha Hxy.
      move: Hxy; rewrite le_lownerE => Hpsd.
      rewrite le_lownerE.
      have -> : a%:C *: y - a%:C *: x = a%:C *: (y - x)
        by rewrite scalerBr.
      apply: psdmxZ; first by rewrite lecE /= eqxx.
      exact: Hpsd. }
    have Htr_real : (\tr rho) \is Num.real := ger0_real (psdmx_trace Hrho).
    have Hrho_le_tI : rho <= t%:C *: (1%:M : 'M[C]_(na * nb)).
    { rewrite /t (RRe_real Htr_real) scalemx1.
      exact: lemx_psd_ub Hrho. }
    have HtI_le_I : t%:C *: (1%:M : 'M[C]_(na * nb)) <=
                    (1%:M : 'M[C]_(na * nb)).
    { rewrite le_lownerE.
      have -> :
          (1%:M : 'M[C]_(na * nb)) - t%:C *: 1%:M =
          (1 - t)%:C *: (1%:M : 'M[C]_(na * nb)).
      { rewrite -[X in X - _]scale1r realcB scalerBl. by rewrite scale1r. }
      apply: psdmxZ; last exact: psdmx1.
      by rewrite lecE /= eqxx subr_ge0. }
    have Hrho_le_I : rho <= (1%:M : 'M[C]_(na * nb))
      := le_trans Hrho_le_tI HtI_le_I.
    have Hscaled_le_XI : dinv%:C *: rho <= XI.
    { rewrite HXI_eq.
      exact: scale_lemx_local Hdinv_ge0 Hrho_le_I. }
    have Hscaled_psd : (dinv%:C *: rho : 'M[C]_(na * nb)) \is psdmx
      by exact: psdmxZ Hdinv_C_ge0 Hrho.
    have Hfid_scaled_le :
        @complex.Re R
          (trnorm (sqrtmx rho *m sqrtmx (dinv%:C *: rho))) <=
        @complex.Re R (trnorm (sqrtmx rho *m sqrtmx XI)).
    { exact: fid_v_mono_r_psd_mx Hrho Hscaled_psd HXI_psd Hscaled_le_XI. }
    have Hsqrt_scaled :
        sqrtmx (dinv%:C *: rho) = (Num.sqrt dinv)%:C *: sqrtmx rho.
    { exact: sqrtmxZ_nn Hdinv_ge0 Hrho. }
    have Hfid_scaled_eq :
        @complex.Re R
          (trnorm (sqrtmx rho *m sqrtmx (dinv%:C *: rho))) =
        Num.sqrt dinv * t.
      { rewrite Hsqrt_scaled.
        have -> :
            sqrtmx rho *m ((Num.sqrt dinv)%:C *: sqrtmx rho) =
            (Num.sqrt dinv)%:C *: rho.
        { have HsqrtK : sqrtmx rho *m sqrtmx rho = rho := sqrtmxK Hrho.
          by rewrite -scalemxAr HsqrtK. }
      rewrite trnormZ.
      have Hsqrt_dinv_ge0 : 0 <= Num.sqrt dinv by exact: sqrtr_ge0.
      have Hsqrt_dinv_C_ge0 : (0 : C) <= (Num.sqrt dinv)%:C
        by rewrite lecE /= eqxx Hsqrt_dinv_ge0.
      rewrite (ger0_norm Hsqrt_dinv_C_ge0).
      rewrite (psdmx_trnorm Hrho) HRe_realM.
      by []. }
    have Hfid_XI_le_gfid :
        @complex.Re R (trnorm (sqrtmx rho *m sqrtmx XI)) <= gfidelity rho XI.
    { rewrite (alt_gfid_gen Hrho HXI_psd).
      rewrite lerDl.
      apply: mulr_ge0; exact: sqrtr_ge0. }
    have Hsqrtd_t_le_gfid :
        Num.sqrt dinv * t <= gfidelity rho XI.
    { rewrite -Hfid_scaled_eq.
      exact: le_trans Hfid_scaled_le Hfid_XI_le_gfid. }
    have Hsqrtd_t_pos : 0 < Num.sqrt dinv * t.
    { apply: mulr_gt0; first by rewrite sqrtr_gt0.
      exact: Hrho_tr_pos. }
    have Hgfid_XI_pos : 0 < gfidelity rho XI
      := lt_le_trans Hsqrtd_t_pos Hsqrtd_t_le_gfid.
    have Harg_pos : 0 < na%:R * (gfidelity rho XI) ^+ 2.
    { apply: mulr_gt0; first by rewrite ltr0n.
      rewrite expr2; apply: mulr_gt0; exact: Hgfid_XI_pos. }
    exists (log2 (na%:R * (gfidelity rho XI) ^+ 2)).
    exists sigma_w; split; first exact: Hsigma_w_den.
    rewrite /XI. exact: elog2_gt0 Harg_pos. }
  split; first exact: Hnonempty.
  exists (log2 na%:R).
  move=> v [sigma [Hsigma_den Hv]].
  have Hsigma_psd : sigma \is psdmx by move/den1mxP: Hsigma_den => [].
  have Htens_psd : (mmix_mx na *t sigma) \is psdmx
    by exact: psdmx_tens (mmix_mx_psd na) Hsigma_psd.
  have /den1mxP [_ /eqP Hsigma_tr1] := Hsigma_den.
  have Htens_tr1 : \tr (mmix_mx na *t sigma) = 1.
  { by rewrite mxtrace_tens (tr_mmix_mx Hna_pos) Hsigma_tr1 mulr1. }
    have Htens_tr_le : @complex.Re R (\tr (mmix_mx na *t sigma)) <= 1
      by rewrite Htens_tr1 -(re_realid 1).
    have Htens_den : (mmix_mx na *t sigma) \is denmx :=
      denmx_psd_re_tr_le Htens_psd Htens_tr_le.
    have Hgf_le1 : gfidelity rho (mmix_mx na *t sigma) <= 1
      := gfid_le1_mx Hrho_den Htens_den.
  have Hgf_ge0 : 0 <= gfidelity rho (mmix_mx na *t sigma)
    := gfid_ge0_mx Hrho Htens_psd.
  have Hsq_le1 : (gfidelity rho (mmix_mx na *t sigma)) ^+ 2 <= 1.
  { rewrite -[leRHS]mulr1.
    by apply: ler_pM. }
  have Harg_le_na :
      na%:R * (gfidelity rho (mmix_mx na *t sigma)) ^+ 2 <= na%:R.
  { have Hna_ge0 : 0 <= na%:R :> R by rewrite ler0n.
    have := ler_wpM2l Hna_ge0 Hsq_le1.
    by rewrite mulr1. }
  have Harg_pos :
    0 < na%:R * (gfidelity rho (mmix_mx na *t sigma)) ^+ 2.
  { case: (ltP 0 (na%:R *
          (gfidelity rho (mmix_mx na *t sigma)) ^+ 2)) => // Harg_le0.
    move: Hv. rewrite (elog2_le0 Harg_le0). by discriminate. }
  have Hv_eq :
      v = log2 (na%:R * (gfidelity rho (mmix_mx na *t sigma)) ^+ 2).
  { move: Hv. rewrite (elog2_gt0 Harg_pos). by case. }
  rewrite Hv_eq.
  exact: log2_le_pos Harg_pos Harg_le_na.
Qed.

(* hmax_mx_ptrace2_le *)
(* infra: no tex label — reusable nonsmooth max comparison under        *)
(* conditioning-system partial trace. Consumers:                         *)
(* smooth data-processing support and eur:smooth_hmax_mx_rho_ZC_purif_dpi. *)
(* path: entropy:hmax_mx_ptrace2_le -> eur:smooth_hmax_mx_rho_ZC_purif_dpi -> *)
(*   eur:entropic_uncertainty_relation -> *)
(*   eur:entropic_uncertainty_relation -> *)
(*   bb84:entropic_uncertainty_relation_bb84 -> bb84:bb84_secret *)
Lemma hmax_mx_ptrace2_le {nA nB z : nat}
    (omega_big : 'M[C]_(nA * (nB * z)))
    (omega_small : 'M[C]_(nA * nB)) :
  (0 < nA)%N ->
  (0 < nB)%N ->
  (0 < z)%N ->
  omega_big \is psdmx ->
  @complex.Re R (\tr omega_big) <= 1 ->
  0 < @complex.Re R (\tr omega_big) ->
  omega_small \is psdmx ->
  @complex.Re R (\tr omega_small) <= 1 ->
  ptrace2 (castmx (mulnA nA nB z, mulnA nA nB z) omega_big) =
    omega_small ->
  hmax_mx omega_big <= hmax_mx omega_small.
Proof.
  move=> HnA_pos HnB_pos Hz_pos Homega_big_psd Homega_big_tr
    Homega_big_tr_pos Homega_small_psd Homega_small_tr Homega_marg.
  have HnBz_pos : (0 < nB * z)%N by rewrite muln_gt0 HnB_pos Hz_pos.
  pose omega_big_assoc :=
    castmx (mulnA nA nB z, mulnA nA nB z) omega_big.
  have Homega_small_tr_pos : 0 < @complex.Re R (\tr omega_small).
  { rewrite -Homega_marg -tr_ptrace2 /omega_big_assoc.
    rewrite -/(castmx_sq (mulnA nA nB z) omega_big) mxtrace_castmx_sq.
    exact: Homega_big_tr_pos. }
    have Hsmall_has_sup :
      has_sup [set v : R | exists sigma : 'M[C]_nB,
        sigma \is den1mx /\
        elog2 (nA%:R * (gfidelity omega_small
                  (mmix_mx nA *t sigma)) ^+ 2) = v%:E]
      := hmax_mx_has_sup HnA_pos HnB_pos
           (denmx_psd_re_tr_le Homega_small_psd Homega_small_tr)
           Homega_small_tr_pos.
  have Hbig_nonempty :
      nonempty [set v : R | exists sigma : 'M[C]_(nB * z),
        sigma \is den1mx /\
        elog2 (nA%:R * (gfidelity omega_big
                  (mmix_mx nA *t sigma)) ^+ 2) = v%:E].
    { have Hbig_has_sup :=
        hmax_mx_has_sup HnA_pos HnBz_pos
          (denmx_psd_re_tr_le Homega_big_psd Homega_big_tr)
          Homega_big_tr_pos.
    by case: Hbig_has_sup. }
  rewrite /hmax_mx.
  apply: sup_le; last exact: Hsmall_has_sup; first last.
  { exact: Hbig_nonempty. }
  move=> v [sigma_w [Hsigma_w_den Hv_w]].
  pose sigma : 'M[C]_nB := ptrace2 sigma_w.
  have Hsigma_w_psd : sigma_w \is psdmx
    by move/den1mxP: Hsigma_w_den => [].
  have Hsigma_psd : sigma \is psdmx := ptrace2_psd Hsigma_w_psd.
  have /den1mxP [_ /eqP Hsigma_w_tr1] := Hsigma_w_den.
  have Hsigma_tr_eq : \tr sigma = \tr sigma_w
    by rewrite /sigma -tr_ptrace2.
  have Hsigma_den : sigma \is den1mx.
  { apply/den1mxP; split=> //.
    by apply/eqP; rewrite Hsigma_tr_eq Hsigma_w_tr1. }
  have Hbig_arg_pos :
    0 < nA%:R * (gfidelity omega_big (mmix_mx nA *t sigma_w)) ^+ 2.
  { case: (ltP 0
        (nA%:R *
          (gfidelity omega_big (mmix_mx nA *t sigma_w)) ^+ 2)) => // Harg_le0.
    move: Hv_w. rewrite (elog2_le0 Harg_le0). by discriminate. }
  have Hv_eq_w :
    v = log2 (nA%:R *
      (gfidelity omega_big (mmix_mx nA *t sigma_w)) ^+ 2).
  { move: Hv_w. rewrite (elog2_gt0 Hbig_arg_pos). by case. }
  have Htens_w_psd :
    (mmix_mx nA *t sigma_w) \is psdmx
    by exact: psdmx_tens (mmix_mx_psd nA) Hsigma_w_psd.
  have Htens_psd :
    (mmix_mx nA *t sigma) \is psdmx
    by exact: psdmx_tens (mmix_mx_psd nA) Hsigma_psd.
  pose tens_w_assoc :=
    castmx (mulnA nA nB z, mulnA nA nB z)
           (mmix_mx nA *t sigma_w).
  have Homega_assoc_psd : omega_big_assoc \is psdmx.
  { rewrite /omega_big_assoc -/(castmx_sq (mulnA nA nB z) _).
    exact: castmx_sq_psdmx Homega_big_psd. }
  have Htens_assoc_psd : tens_w_assoc \is psdmx.
  { rewrite /tens_w_assoc -/(castmx_sq (mulnA nA nB z) _).
    exact: castmx_sq_psdmx Htens_w_psd. }
  have Hgfid_cast_eq :
    gfidelity omega_big_assoc tens_w_assoc =
    gfidelity omega_big (mmix_mx nA *t sigma_w)
    by rewrite /omega_big_assoc /tens_w_assoc gfid_cast_mx.
  have Hdpi : gfidelity omega_big_assoc tens_w_assoc <=
              gfidelity (ptrace2 omega_big_assoc) (ptrace2 tens_w_assoc)
    := gfid_ptr_mono_mx Hz_pos Homega_assoc_psd Htens_assoc_psd.
  have Hp2 : ptrace2 tens_w_assoc = mmix_mx nA *t sigma.
  { rewrite /tens_w_assoc /sigma.
    exact: ptrace2_castmx_tensmx_assoc. }
  have Hper_wit_le :
      gfidelity omega_big (mmix_mx nA *t sigma_w) <=
      gfidelity omega_small (mmix_mx nA *t sigma).
  { rewrite -Hgfid_cast_eq -Homega_marg -Hp2. exact: Hdpi. }
  have Hbig_gf_ge0 :
    0 <= gfidelity omega_big (mmix_mx nA *t sigma_w)
    := gfid_ge0_mx Homega_big_psd Htens_w_psd.
  have Hsmall_gf_ge0 :
    0 <= gfidelity omega_small (mmix_mx nA *t sigma)
    := gfid_ge0_mx Homega_small_psd Htens_psd.
  have Hsmall_gf_pos :
    0 < gfidelity omega_small (mmix_mx nA *t sigma).
  { have Hbig_gf_pos :
      0 < gfidelity omega_big (mmix_mx nA *t sigma_w).
    { have Hbig_sq_pos :
          0 < (gfidelity omega_big (mmix_mx nA *t sigma_w)) ^+ 2.
      { have HnA_R_pos : 0 < nA%:R :> R by rewrite ltr0n.
        have Htmp :
            nA%:R * 0 <
            nA%:R * (gfidelity omega_big (mmix_mx nA *t sigma_w)) ^+ 2.
        { by rewrite mulr0. }
        by move: Htmp; rewrite (ltr_pM2l HnA_R_pos). }
      move: Hbig_sq_pos; rewrite expr2.
      move: Hbig_gf_ge0; rewrite le0r => /orP [/eqP Hgf0 | Hgf_pos].
      - by rewrite Hgf0 mul0r ltxx.
      - by move=> _; exact: Hgf_pos. }
    exact: lt_le_trans Hbig_gf_pos Hper_wit_le. }
  have Hsmall_arg_pos :
    0 < nA%:R * (gfidelity omega_small (mmix_mx nA *t sigma)) ^+ 2.
  { apply: mulr_gt0; first by rewrite ltr0n.
    rewrite expr2. exact: mulr_gt0. }
  have Hgfid2_le :
    (gfidelity omega_big (mmix_mx nA *t sigma_w)) ^+ 2 <=
    (gfidelity omega_small (mmix_mx nA *t sigma)) ^+ 2.
  { apply: lerXn2r; first exact: Hbig_gf_ge0.
    - exact: Hsmall_gf_ge0.
    - exact: Hper_wit_le. }
  have Harg_le :
      nA%:R * (gfidelity omega_big (mmix_mx nA *t sigma_w)) ^+ 2 <=
      nA%:R * (gfidelity omega_small (mmix_mx nA *t sigma)) ^+ 2.
  { have HnA_R_ge0 : 0 <= nA%:R :> R by rewrite ler0n.
    have := ler_wpM2l HnA_R_ge0 Hgfid2_le.
    by []. }
  pose w := log2 (nA%:R *
    (gfidelity omega_small (mmix_mx nA *t sigma)) ^+ 2).
  exists w; split.
  - exists sigma; split; first exact: Hsigma_den.
    rewrite /w. by rewrite (elog2_gt0 Hsmall_arg_pos).
  - rewrite Hv_eq_w /w.
    exact: log2_le_pos Hbig_arg_pos Harg_le.
Qed.

(* hmax_mx_lb_trace_dimB *)
(* infra: no tex label — reusable matrix hmax lower bound for smooth optimizers. *)
(* path: entropy:hmax_mx_lb_trace_dimB -> entropy:smooth_hmax_mx_has_inf -> *)
(*   eur:smooth_hmax_mx_rho_ZC_purif_dpi -> *)
(*   eur:entropic_uncertainty_relation -> *)
(*   eur:entropic_uncertainty_relation -> *)
(*   bb84:entropic_uncertainty_relation_bb84 -> bb84:bb84_secret *)
Lemma hmax_mx_lb_trace_dimB {na nb : nat} (rho : 'M[C]_(na * nb)) :
  (0 < na)%N ->
  (0 < nb)%N ->
  rho \is psdmx ->
  @complex.Re R (\tr rho) <= 1 ->
  0 < @complex.Re R (\tr rho) ->
  log2 ((nb%:R)^-1 * (@complex.Re R (\tr rho)) ^+ 2) <= hmax_mx rho.
Proof.
  move=> Hna_pos Hnb_pos Hrho Hrho_tr Htr_pos.
  pose t := @complex.Re R (\tr rho).
  pose dinv : R := (na%:R)^-1%R * (nb%:R)^-1%R.
  pose dinvB : R := (nb%:R)^-1%R.
  have HRe_realM : forall (cc : R) (zz : C),
      @complex.Re R (cc%:C * zz) = cc * @complex.Re R zz.
  { move=> cc zz; case: zz => a b /=. by rewrite mul0r subr0. }
  have Htr_ge0 : 0 <= t.
  { have /= := psdmx_trace Hrho.
    by rewrite /t lecE /= => /andP [_]. }
  have Hna_R_pos : 0 < na%:R :> R by rewrite ltr0n.
  have Hnb_R_pos : 0 < nb%:R :> R by rewrite ltr0n.
  have Hna_R_ne0 : (na%:R : R) != 0 by exact: lt0r_neq0.
  have Hnb_R_ne0 : (nb%:R : R) != 0 by exact: lt0r_neq0.
  have Hdinv_pos : 0 < dinv
    by rewrite /dinv mulr_gt0 ?invr_gt0.
  have Hdinv_ge0 : 0 <= dinv := ltW Hdinv_pos.
  have Hdinv_C_ge0 : (0 : C) <= dinv%:C by rewrite lecE /= eqxx Hdinv_ge0.
  have scale_lemx_local :
      forall (x y : 'M[C]_(na * nb)) (a : R),
        0 <= a -> x <= y -> a%:C *: x <= a%:C *: y.
  { move=> x y a Ha Hxy.
    move: Hxy; rewrite le_lownerE => Hpsd.
    rewrite le_lownerE.
    have -> : a%:C *: y - a%:C *: x = a%:C *: (y - x)
      by rewrite scalerBr.
    apply: psdmxZ; first by rewrite lecE /= eqxx.
    exact: Hpsd. }
  pose sigmaI : 'M[C]_nb := mmix_mx nb.
  pose XI : 'M[C]_(na * nb) := mmix_mx na *t sigmaI.
  pose vI := log2 (na%:R * (gfidelity rho XI) ^+ 2).
  have HsigmaI_den : sigmaI \is den1mx
    by rewrite /sigmaI; exact: mmix_mx_den1.
  have HsigmaI_psd : sigmaI \is psdmx
    by move/den1mxP: HsigmaI_den => [].
  have HXI_eq : XI = dinv%:C *: (1%:M : 'M[C]_(na * nb)).
  { rewrite /XI /sigmaI /mmix_mx /dinv.
    have Hcoef :
        (((na%:R : R)^-1)%:C) * (((nb%:R : R)^-1)%:C) =
        dinv%:C.
    { by rewrite /dinv -rmorphM. }
    apply/matrixP=> i j.
    case: (mxtens_indexP i)=> i0 i1.
    case: (mxtens_indexP j)=> j0 j1.
    rewrite mxE !mxtens_indexK/= !mxE
      (can_eq (@mxtens_indexK _ _)) -pair_eqE/=.
    rewrite -Hcoef.
    case H0: (i0 == j0); case H1: (i1 == j1);
      rewrite /= ?mul0r ?mulr0 ?mul1r ?mulr1
        ?mulr0n ?mulr1n ?mulrA;
      by rewrite ?mul0r ?mulr0. }
  have HXI_psd : XI \is psdmx.
  { rewrite HXI_eq. exact: psdmxZ Hdinv_C_ge0 (psdmx1 _ _). }
  have Htr_real : (\tr rho) \is Num.real := ger0_real (psdmx_trace Hrho).
  have Hrho_le_tI : rho <= t%:C *: (1%:M : 'M[C]_(na * nb)).
  { rewrite /t (RRe_real Htr_real) scalemx1.
    exact: lemx_psd_ub Hrho. }
  have HtI_le_I : t%:C *: (1%:M : 'M[C]_(na * nb)) <=
                  (1%:M : 'M[C]_(na * nb)).
  { rewrite le_lownerE.
    have -> :
        (1%:M : 'M[C]_(na * nb)) - t%:C *: 1%:M =
        (1 - t)%:C *: (1%:M : 'M[C]_(na * nb)).
    { rewrite -[X in X - _]scale1r realcB scalerBl. by rewrite scale1r. }
    apply: psdmxZ.
    - by rewrite lecE /= eqxx subr_ge0.
    - exact: psdmx1. }
  have Hrho_le_I : rho <= (1%:M : 'M[C]_(na * nb))
    := le_trans Hrho_le_tI HtI_le_I.
  have Hscaled_le_XI : dinv%:C *: rho <= XI.
  { rewrite HXI_eq.
    exact: scale_lemx_local Hdinv_ge0 Hrho_le_I. }
  have Hscaled_psd : (dinv%:C *: rho : 'M[C]_(na * nb)) \is psdmx
    by exact: psdmxZ Hdinv_C_ge0 Hrho.
  have Hfid_scaled_le :
      @complex.Re R
        (trnorm (sqrtmx rho *m sqrtmx (dinv%:C *: rho))) <=
      @complex.Re R (trnorm (sqrtmx rho *m sqrtmx XI)).
  { exact: fid_v_mono_r_psd_mx Hrho Hscaled_psd HXI_psd Hscaled_le_XI. }
  have Hsqrt_scaled :
      sqrtmx (dinv%:C *: rho) = (Num.sqrt dinv)%:C *: sqrtmx rho.
  { exact: sqrtmxZ_nn Hdinv_ge0 Hrho. }
  have Hfid_scaled_eq :
      @complex.Re R
        (trnorm (sqrtmx rho *m sqrtmx (dinv%:C *: rho))) =
      Num.sqrt dinv * t.
  { rewrite Hsqrt_scaled.
    have -> :
        sqrtmx rho *m ((Num.sqrt dinv)%:C *: sqrtmx rho) =
        (Num.sqrt dinv)%:C *: rho
      by rewrite -scalemxAr sqrtmxK.
    rewrite trnormZ.
    have Hsqrt_dinv_ge0 : 0 <= Num.sqrt dinv by exact: sqrtr_ge0.
    have Hsqrt_dinv_C_ge0 : (0 : C) <= (Num.sqrt dinv)%:C
      by rewrite lecE /= eqxx Hsqrt_dinv_ge0.
    rewrite (ger0_norm Hsqrt_dinv_C_ge0).
    rewrite (psdmx_trnorm Hrho) HRe_realM.
    by []. }
  have Hfid_XI_le_gfid :
      @complex.Re R (trnorm (sqrtmx rho *m sqrtmx XI)) <= gfidelity rho XI.
  { rewrite (alt_gfid_gen Hrho HXI_psd).
    rewrite lerDl.
    apply: mulr_ge0; exact: sqrtr_ge0. }
  have Hsqrtd_t_le_gfid :
      Num.sqrt dinv * t <= gfidelity rho XI.
  { rewrite -Hfid_scaled_eq.
    exact: le_trans Hfid_scaled_le Hfid_XI_le_gfid. }
  have Hsqrtd_t_pos : 0 < Num.sqrt dinv * t.
  { apply: mulr_gt0.
    - by rewrite sqrtr_gt0.
    - exact: Htr_pos. }
  have Hsqrtd_t_ge0 : 0 <= Num.sqrt dinv * t := ltW Hsqrtd_t_pos.
  have Hgfid_XI_ge0 : 0 <= gfidelity rho XI := gfid_ge0_mx Hrho HXI_psd.
  have Hgfid_XI_pos : 0 < gfidelity rho XI
    := lt_le_trans Hsqrtd_t_pos Hsqrtd_t_le_gfid.
  have Hbase_le_gf2 :
      dinv * t ^+ 2 <= (gfidelity rho XI) ^+ 2.
  { have Htmp := lerXn2r 2 Hsqrtd_t_ge0 Hgfid_XI_ge0 Hsqrtd_t_le_gfid.
    have Hleft_eq : (Num.sqrt dinv * t) ^+ 2 = dinv * t ^+ 2.
    { by rewrite exprMn sqr_sqrtr. }
    by rewrite -Hleft_eq. }
  have Htarget_eq : dinvB * t ^+ 2 = na%:R * (dinv * t ^+ 2).
  { rewrite /dinv /dinvB.
    rewrite -!mulrA.
    rewrite [RHS]mulrA.
    by rewrite [na%:R * (na%:R)^-1]mulfV ?mul1r. }
  have Htarget_le_arg :
      dinvB * t ^+ 2 <= na%:R * (gfidelity rho XI) ^+ 2.
  { rewrite Htarget_eq.
    have Hna_R_ge0 : 0 <= na%:R :> R by exact: ltW Hna_R_pos.
    have := ler_wpM2l Hna_R_ge0 Hbase_le_gf2.
    by []. }
  have Hc_pos : 0 < dinvB * t ^+ 2.
  { apply: mulr_gt0.
    - by rewrite /dinvB invr_gt0.
    - rewrite expr2; apply: mulr_gt0; exact: Htr_pos. }
  have HfeasI :
      ([set v : R | exists sigma : 'M[C]_nb,
        sigma \is den1mx /\
        elog2 (na%:R * (gfidelity rho (mmix_mx na *t sigma)) ^+ 2) = v%:E]%classic) vI.
  { exists sigmaI; split; first exact: HsigmaI_den.
    - rewrite /vI /XI.
      rewrite (elog2_gt0); first reflexivity.
      apply: mulr_gt0; first exact: Hna_R_pos.
      rewrite expr2; apply: mulr_gt0; exact: Hgfid_XI_pos. }
  have Hdown :
      ([set log2 (dinvB * t ^+ 2)] `<=`
       down [set v : R | exists sigma : 'M[C]_nb,
        sigma \is den1mx /\
        elog2 (na%:R * (gfidelity rho (mmix_mx na *t sigma)) ^+ 2) = v%:E])%classic.
  { move=> y /= ->.
    rewrite /down /=.
    exists vI; split; first exact: HfeasI.
    rewrite /vI.
    exact: log2_le_pos Hc_pos Htarget_le_arg. }
  have Hnz : nonempty [set log2 (dinvB * t ^+ 2)].
  { by exists (log2 (dinvB * t ^+ 2)). }
    have Hsup := hmax_mx_has_sup Hna_pos Hnb_pos
      (denmx_psd_re_tr_le Hrho Hrho_tr) Htr_pos.
  have := sup_le Hdown Hnz Hsup.
  by rewrite sup1 /hmax_mx /dinvB /t.
Qed.

(* smooth_hmax_mx_has_inf *)
(* infra: no tex label — reusable matrix smooth-max finite-branch       *)
(* infimum fact. Consumers: smooth data-processing support and           *)
(* eur:smooth_hmax_mx_rho_ZC_purif_dpi.                                *)
(* path: entropy:smooth_hmax_mx_has_inf -> *)
(*   eur:smooth_hmax_mx_rho_ZC_purif_dpi -> *)
(*   eur:entropic_uncertainty_relation -> *)
(*   eur:entropic_uncertainty_relation -> *)
(*   bb84:entropic_uncertainty_relation_bb84 -> bb84:bb84_secret *)
Lemma smooth_hmax_mx_has_inf {na nb : nat}
    (eps : R) (rho : 'M[C]_(na * nb)) :
  (0 < na)%N ->
  (0 < nb)%N ->
  rho \is denmx ->
  0 <= eps ->
  eps < Num.sqrt (@complex.Re R (\tr rho)) ->
  has_inf [set v : R | exists tau : 'M[C]_(na * nb),
    (tau \is denmx) && (0 < @complex.Re R (\tr tau)) &&
    (pur_dist_mx tau rho <= eps) /\ v = hmax_mx tau].
Proof.
  move=> Hna_pos Hnb_pos Hrho_den Heps0 Heps_lt.
  have /denmxP [Hrho Hrho_trC] := Hrho_den.
  have Hrho_tr : @complex.Re R (\tr rho) <= 1
    by move: Hrho_trC; rewrite lecE /= => /andP [_].
  have Hrho_pos : 0 < @complex.Re R (\tr rho).
  {
    have Hsqrt_gt0 : 0 < Num.sqrt (@complex.Re R (\tr rho)) :=
      le_lt_trans Heps0 Heps_lt.
    have Hrho_ge0 : 0 <= @complex.Re R (\tr rho).
    {
      have /= := psdmx_trace Hrho.
      by rewrite lecE /= => /andP[].
    }
    have Hsqrt_sq_pos : 0 < (Num.sqrt (@complex.Re R (\tr rho))) ^+ 2.
    {
      rewrite expr2.
      by apply: mulr_gt0.
    }
    by rewrite (sqr_sqrtr Hrho_ge0) in Hsqrt_sq_pos.
  }
  split.
  - exists (hmax_mx rho). exists rho; split; last reflexivity.
    by rewrite Hrho_den Hrho_pos (pur_dist_mx_refl Hrho_den).
  - pose dB_inv : R := (nb%:R)^-1%R.
    pose gap : R := Num.sqrt (@complex.Re R (\tr rho)) - eps.
    pose lb_const : R := log2 (dB_inv * (gap ^+ 2) ^+ 2).
    exists lb_const => w [tau [Htau_feas ->]].
    move: Htau_feas => /andP[/andP [Htau_den _] Htau_pd].
    have /denmxP[Htau_psd Htau_trC] := Htau_den.
    have Htau_tr : @complex.Re R (\tr tau) <= 1
      by move: Htau_trC; rewrite lecE /= => /andP [_].
    have Htot_pos : (0 < na * nb)%N
      by rewrite muln_gt0 Hna_pos Hnb_pos.
    have Hgap_pos : 0 < gap by rewrite /gap subr_gt0.
      have Hsqrt_le0 :
          Num.sqrt (@complex.Re R (\tr rho)) <=
          Num.sqrt (@complex.Re R (\tr tau)) + pur_dist_mx tau rho.
      { rewrite /pur_dist_mx.
        exact: pur_dist_mx_trace_sqrt_bound Htot_pos
          Hrho_den Htau_den. }
    have Hsqrt_le :
        Num.sqrt (@complex.Re R (\tr rho)) <=
        Num.sqrt (@complex.Re R (\tr tau)) + eps.
    { have Hadd_le :
          Num.sqrt (@complex.Re R (\tr tau)) + pur_dist_mx tau rho <=
          Num.sqrt (@complex.Re R (\tr tau)) + eps
        by rewrite lerD2l.
      exact: le_trans Hsqrt_le0 Hadd_le. }
    have Hgap_le_sqrt :
        gap <= Num.sqrt (@complex.Re R (\tr tau)).
    { have Htmp : gap + eps <=
          Num.sqrt (@complex.Re R (\tr tau)) + eps
        by rewrite /gap subrK; exact: Hsqrt_le.
      by move: Htmp; rewrite lerD2r. }
    have Htrace_lb :
        gap ^+ 2 <= @complex.Re R (\tr tau).
    { have Hsq :
          gap ^+ 2 <= (Num.sqrt (@complex.Re R (\tr tau))) ^+ 2.
      { rewrite (ler_sqr (ltW Hgap_pos) (sqrtr_ge0 _)).
        exact: Hgap_le_sqrt. }
      have Htau_sq :
          (Num.sqrt (@complex.Re R (\tr tau))) ^+ 2 <=
          @complex.Re R (\tr tau).
      { have Htau_tr_ge0 : 0 <= @complex.Re R (\tr tau).
        { have /= := psdmx_trace Htau_psd.
          by rewrite lecE /= => /andP [_]. }
        by rewrite sqr_sqrtr. }
      exact: le_trans Hsq Htau_sq. }
    have Htau_tr_pos : 0 < @complex.Re R (\tr tau).
    { have Hgap_sq_pos : 0 < gap ^+ 2
        by rewrite expr2; apply: mulr_gt0.
      exact: lt_le_trans Hgap_sq_pos Htrace_lb. }
    have Hhmax_lb :
        log2 ((nb%:R)^-1 * (@complex.Re R (\tr tau)) ^+ 2) <=
        hmax_mx tau.
    { exact: hmax_mx_lb_trace_dimB Hna_pos Hnb_pos
        Htau_psd Htau_tr Htau_tr_pos. }
    apply: le_trans _ Hhmax_lb.
    rewrite /lb_const /dB_inv /gap.
    apply: log2_le_pos.
    + apply: mulr_gt0.
      * by rewrite invr_gt0 ltr0n.
      * by rewrite expr2; apply: mulr_gt0; rewrite expr2; apply: mulr_gt0.
    + apply: ler_wpM2l.
      * by rewrite invr_ge0 ler0n.
      * have Hgap_sq_ge0 : 0 <= gap ^+ 2
          by rewrite expr2; apply: mulr_ge0; exact: ltW.
        have Htau_re_ge0 : 0 <= @complex.Re R (\tr tau)
          := le_trans Hgap_sq_ge0 Htrace_lb.
        exact: (lerXn2r 2 Hgap_sq_ge0 Htau_re_ge0 Htrace_lb).
Qed.

Section EpsBallProps.
Variable (L : finType) (H : L -> chsType) (S : {set L}).

(* eps_ball_psdlf *)
(* infra: no tex label — fundamental & reusable (mathcomp-style) *)
(* path: entropy:eps_ball_psdlf -> *)
(*   bb84:privacy_amplification -> bb84:bb84_secret *)
Lemma eps_ball_psdlf (eps : R) (rho tau : 'F[H]_S) :
  eps_ball eps rho tau -> tau \is psdlf.
Proof.
  by rewrite /eps_ball => /andP [/andP [/andP [-> _] _] _].
Qed.

(* eps_ball_trlf_gt0 *)
(* infra: no tex label — accessor for τ ∈ S_≤(H), whose trace is nonzero *)
Lemma eps_ball_trlf_gt0 (eps : R) (rho tau : 'F[H]_S) :
  eps_ball eps rho tau -> 0 < @complex.Re R (\Tr tau).
Proof.
  by rewrite /eps_ball => /andP [/andP [/andP [_ ->] _] _].
Qed.

(* eps_ball_trlf *)
(* infra: no tex label — fundamental & reusable (mathcomp-style) *)
(* path: entropy:eps_ball_trlf -> bb84:privacy_amplification -> *)
(*   bb84:bb84_secret *)
Lemma eps_ball_trlf (eps : R) (rho tau : 'F[H]_S) :
  eps_ball eps rho tau -> @complex.Re R (\Tr tau) <= 1.
Proof.
  by rewrite /eps_ball => /andP [/andP [/andP [_ _] ->] _].
Qed.

(* eps_ball_trace_pos *)
(* infra: no tex label — reusable positive-trace consequence of a strict ball *)
(* path: entropy:eps_ball_trace_pos -> *)
(*   bb84:privacy_amplification -> bb84:bb84_secret *)
Lemma eps_ball_trace_pos (eps : R) (rho tau : 'F[H]_S) :
  rho \is psdlf ->
  @complex.Re R (\Tr rho) <= 1 ->
  0 <= eps < Num.sqrt (@complex.Re R (\Tr rho)) ->
  eps_ball eps rho tau ->
  0 < @complex.Re R (\Tr tau).
Proof. by move=> _ _ _ /eps_ball_trlf_gt0. Qed.

Lemma eps_ball_pur_dist (eps : R) (rho tau : 'F[H]_S) :
  eps_ball eps rho tau -> pur_dist tau rho <= eps.
Proof.
  by rewrite /eps_ball => /andP [_ ->].
Qed.

Lemma eps_ball_refl (eps : R) (rho : 'F[H]_S) :
  rho \is psdlf ->
  0 < @complex.Re R (\Tr rho) ->
  @complex.Re R (\Tr rho) <= 1 ->
  0 <= eps ->
  eps_ball eps rho rho.
Proof.
  move=> Prho Hrho_gt0 Hrho_tr Heps.
  by rewrite /eps_ball Prho Hrho_gt0 Hrho_tr (pur_dist_refl Prho Hrho_tr) Heps.
Qed.

Lemma eps_ball_trace_pos_from_small (eps : R) (rho tau : 'F[H]_S) :
  rho \is psdlf ->
  @complex.Re R (\Tr rho) <= 1 ->
  0 <= eps < Num.sqrt (@complex.Re R (\Tr rho)) ->
  ((tau \is psdlf) && (@complex.Re R (\Tr tau) <= 1)) &&
    (pur_dist tau rho <= eps) ->
  0 < @complex.Re R (\Tr tau).
Proof.
  move=> Prho Hrho_tr /andP [_ Heps_lt] Hball.
  move: Hball => /andP [/andP [Ptau Htau_tr] Htau_pd].
  have Hzero_psd : (0 : 'F[H]_S) \is psdlf.
  {
    by rewrite qualifE h2mx0 psdmx0.
  }
  have Hzero_tr : @complex.Re R (\Tr (0 : 'F[H]_S)) <= 1.
    by rewrite linear0 raddf0 ler01.
  have Hpd_zero_eq :
      forall x : 'F[H]_S,
        x \is psdlf ->
        @complex.Re R (\Tr x) <= 1 ->
        pur_dist (0 : 'F[H]_S) x = Num.sqrt (@complex.Re R (\Tr x)).
  {
    move=> x Px Hx_tr.
    have Hzero_mx_psd : h2mx (0 : 'F[H]_S) \is psdmx.
    {
      by move: Hzero_psd; rewrite qualifE.
    }
    have Hx_mx_psd : h2mx x \is psdmx.
    {
      by move: Px; rewrite qualifE.
    }
    have Hgfid0 :
        gfid (0 : 'F[H]_S) x =
        Num.sqrt (1 - @complex.Re R (\Tr x)).
    {
      rewrite /gfid.
      rewrite (alt_gfid_gen Hzero_mx_psd Hx_mx_psd).
      have -> :
          @complex.Re R
            (trnorm (sqrtmx (h2mx (0 : 'F[H]_S)) *m sqrtmx (h2mx x))) = 0.
      {
        by rewrite h2mx0 sqrtmx0 mul0mx trnorm0 raddf0.
      }
      have -> :
          @complex.Re R (1 - \tr (h2mx (0 : 'F[H]_S))) = 1.
        {
            by rewrite h2mx0 mxtrace0 subr0.
        }
      have -> :
          @complex.Re R (1 - \tr (h2mx x)) =
          1 - @complex.Re R (\Tr x).
        {
          by rewrite raddfB /= /lftrace.
        }
      by rewrite sqrtr1 mul1r add0r.
    }
    rewrite /pur_dist.
    pose a := 1 - @complex.Re R (\Tr x).
    have Ha_ge0 : 0 <= a.
    {
      rewrite /a.
      by rewrite subr_ge0.
    }
    have -> :
        (gfid (0 : 'F[H]_S) x)^2 = a.
    {
      rewrite Hgfid0.
      exact: sqr_sqrtr Ha_ge0.
    }
    by rewrite /a opprB addrCA subrr addr0.
  }
  have Hgap_pos : 0 < Num.sqrt (@complex.Re R (\Tr rho)) - eps.
  {
    by rewrite subr_gt0.
  }
  have Hrho_zero := Hpd_zero_eq rho Prho Hrho_tr.
  have Htau_zero := Hpd_zero_eq tau Ptau Htau_tr.
  have Hsqrt_le :
      Num.sqrt (@complex.Re R (\Tr rho)) <=
      Num.sqrt (@complex.Re R (\Tr tau)) + eps.
  {
    rewrite -Hrho_zero -Htau_zero.
    have Htri := @pd_metric_triangle R L H S
      (0 : 'F[H]_S) rho tau Hzero_psd Prho Ptau Hzero_tr Hrho_tr Htau_tr.
    have Hstep :
        pur_dist (0 : 'F[H]_S) tau + pur_dist tau rho <=
        pur_dist (0 : 'F[H]_S) tau + eps.
    {
      apply: lerD.
      - exact: lexx.
      - exact: Htau_pd.
    }
    exact: le_trans Htri Hstep.
  }
  have Hgap_le :
      Num.sqrt (@complex.Re R (\Tr rho)) - eps <=
      Num.sqrt (@complex.Re R (\Tr tau)).
  {
    move: Hsqrt_le.
    by rewrite lerBlDr addrC.
  }
  have Htau_sqrt_pos : 0 < Num.sqrt (@complex.Re R (\Tr tau)).
  {
    exact: lt_le_trans Hgap_pos Hgap_le.
  }
  by rewrite -sqrtr_gt0.
Qed.

End EpsBallProps.

(* ================================================================== *)
(* Finite bridges from extended Tomamichel entropies to the real compatibility *)
(* layer used by LHL/BB84 numerical bounds.                              *)
(* ================================================================== *)

Section HminEProps.
Variable (L : finType) (H : L -> chsType).
Variable (S T : {set L}).

(* path: entropy:phi_min_feasible_has_inf -> *)
(*   bb84:bb84_secret *)
Lemma phi_min_feasible_has_inf (rhoS : 'F[H]_S) :
  rhoS \is psdlf ->
  has_inf [set v : R | phi_min_feasible T rhoS v].
Proof.
  move=> Prho; split.
  - pose c := @complex.Re R (\Tr rhoS).
    pose sigma0 : 'F[H]_(S :&: T) := c%:C *: (\1 : 'F[H]_(S :&: T)).
    have Htr_rho_real : (\Tr rhoS : C) = c%:C.
    {
      by rewrite /c RRe_real // ger0_real // psdlf_trlf.
    }
    have Psigma0 : sigma0 \is psdlf.
    {
      rewrite /sigma0.
      apply: psdlfZ.
      - by move: (psdlf_trlf Prho); rewrite Htr_rho_real lecR.
      - by rewrite qualifE h2mx1; apply: psdmx1.
    }
    have Htr_id :
        rhoS <= (@complex.Re R (\Tr rhoS))%:C *: (\1 : 'F[H]_S).
    {
      have Htr_real : \Tr rhoS \is Num.real := ger0_real (psdlf_trlf Prho).
      rewrite lef_h2mx.
      have -> :
          h2mx (((@complex.Re R (\Tr rhoS))%:C) *: (\1 : 'F[H]_S)) =
          (\tr (h2mx rhoS))%:M.
      {
        move: (h2mxP ((@complex.Re R (\Tr rhoS))%:C) (\1 : 'F[H]_S) 0).
        rewrite h2mx0 !addr0 => ->.
        by rewrite h2mx1 /lftrace (RRe_real Htr_real) scalemx1.
      }
      apply: lemx_psd_ub.
      by rewrite qualifE.
    }
    exists (@complex.Re R (\Tr sigma0)).
    exists sigma0; split; first exact: Psigma0.
    split; last reflexivity.
    move: Htr_id.
    rewrite /sigma0 sdotfZr sdotf11 linearZ /= castlf1.
    done.
  - exists 0 => v [sigma [Psigma [_ ->]]].
    by have := psdlf_trlf Psigma; rewrite lecE /= => /andP[_].
Qed.

End HminEProps.

Section PhiMinDualBridge.
Variable (L : finType) (H : L -> chsType).
Variable (A B : {set L}).
Hypothesis disAB : [disjoint A & B].

Notation S_AB := (A :|: B).

(* infra: no tex label — reusable SDP bridge for Tomamichel's Phi functional. *)
(* math: strong SDP duality plus primal attainment for the Φ functional   *)
(*   (Tomamichel thesis, arXiv:1203.2142, Sec. 4.5; cf. Theorem 2.6).      *)
(* path: entropy:phi_min_sdp_strong -> *)
(*   bb84:bb84_secret *)
Lemma phi_min_sdp_strong (rhoAB : 'F[H]_S_AB) :
  rhoAB \is psdlf ->
  phi_min B rhoAB =
    sup [set v : R | exists Y : 'F[H]_S_AB,
      [/\ Y \is psdlf,
          ptrace_castl disAB Y <= (\1 : 'F[H]_B) &
          v = @complex.Re R (\Tr (rhoAB \o Y))]] /\
  phi_min_feasible B rhoAB (phi_min B rhoAB).
Proof.
  move=> Prho.
  pose PhiSet : set R := [set v : R | phi_min_feasible B rhoAB v]%classic.
  have Halpha_phi :
      phi_min B rhoAB = ExtNumTopology.etinf PhiSet.
  { by rewrite /phi_min /PhiSet /ExtNumTopology.etinf. }
  pose Psi_fun (sigmaB : 'F[H]_B) : 'F[H]_S_AB :=
    (\1 : 'F[H]_A) \O sigmaB.
  have HPsi_fun_linear : linear Psi_fun.
  { by move=> c sigma tau; rewrite /Psi_fun sdotfDr sdotfZr. }
  pose Psi_lfun : {linear 'F[H]_B -> 'F[H]_S_AB} :=
    HB.pack Psi_fun
      (GRing.isLinear.Build C _ _ *:%R _ HPsi_fun_linear).
  pose Psi : 'SO('H[H]_B, 'H[H]_S_AB) :=
    SOType (linfun Psi_lfun).
  pose SdpP : set R :=
    @sdp_primal_set R 'H[H]_B 'H[H]_S_AB
      (h2mx (\1 : 'F[H]_B)) (h2mx rhoAB) Psi.
  pose SdpD : set R :=
    @sdp_dual_set R 'H[H]_B 'H[H]_S_AB
      (h2mx (\1 : 'F[H]_B)) (h2mx rhoAB) Psi.
  have eqAB_diff : S_AB :\: B = A by exact: setDU_r.
  have eqAB_cond : S_AB :&: B = B by setdec.
  have eqAB_lift : (S_AB :\: B) :|: B = S_AB by rewrite eqAB_diff.
  have eqAB_lift_sig :
      (S_AB :\: B) :|: (S_AB :&: B) =
      (S_AB :\: B) :|: B by rewrite eqAB_cond.
  have eqAB_phi :
      (S_AB :\: B) :|: (S_AB :&: B) = S_AB
    by rewrite finset.setUC finset.setID.
  have phi_lift_term (sigmaB : 'F[H]_B) :
      castlf (eqAB_phi, eqAB_phi)
        ((\1 : 'F[H]_(S_AB :\: B)) \O
          castlf (esym eqAB_cond, esym eqAB_cond) sigmaB) =
      (\1 : 'F[H]_A) \O sigmaB.
  {
    have -> : eqAB_phi = etrans eqAB_lift_sig eqAB_lift
      by apply: eq_irrelevance.
    rewrite -castlf_comp.
    rewrite (@sdotIf_cast_r R _ _ (S_AB :\: B)
      (S_AB :&: B) B eqAB_cond eqAB_lift_sig
      (castlf (esym eqAB_cond, esym eqAB_cond) sigmaB)).
    have -> :
        castlf (eqAB_cond, eqAB_cond)
          (castlf (esym eqAB_cond, esym eqAB_cond) sigmaB) = sigmaB
      by exact: castlfKV.
    rewrite (@sdotIf_cast_l R _ _ (S_AB :\: B) A B
      eqAB_diff eqAB_lift
      (\1 : 'F[H]_(S_AB :\: B)) sigmaB).
    have -> :
        castlf (eqAB_diff, eqAB_diff)
          (\1 : 'F[H]_(S_AB :\: B)) =
        (\1 : 'F[H]_A) by exact: castlf1.
    done.
  }
  have phi_lift_term_any
      (eqp : (S_AB :\: B) :|: (S_AB :&: B) = S_AB)
      (sigmaB : 'F[H]_B) :
      castlf (eqp, eqp)
        ((\1 : 'F[H]_(S_AB :\: B)) \O
          castlf (esym eqAB_cond, esym eqAB_cond) sigmaB) =
      (\1 : 'F[H]_A) \O sigmaB.
  {
    have -> : eqp = eqAB_phi by apply: eq_irrelevance.
    exact: phi_lift_term.
  }
  have Hphi_primal : PhiSet = SdpP.
  {
    apply/funext=> v /=.
    apply/propext; split.
    - rewrite /PhiSet /SdpP /sdp_primal_set /=.
      move=> [sigma [Psigma [Hgap ->]]].
      pose sigmaB : 'F[H]_B :=
        castlf (eqAB_cond, eqAB_cond) sigma.
      exists (h2mx sigmaB).
      split.
      + have PsigmaB : sigmaB \is psdlf
          by rewrite /sigmaB castlf_psdlfE.
        by move: PsigmaB; rewrite qualifE.
      + have Hpsi_sigma :
            Psi (mx2h (h2mx sigmaB)) =
            (\1 : 'F[H]_A) \O sigmaB.
        {
          rewrite /Psi superopE lfunE /= /Psi_lfun /Psi_fun.
          by rewrite h2mxK.
        }
        rewrite Hpsi_sigma -lef_h2mx.
        have Hsigma_cast :
            sigma =
            castlf (esym eqAB_cond, esym eqAB_cond) sigmaB
          by rewrite /sigmaB castlfK.
        move: Hgap.
        rewrite Hsigma_cast (phi_lift_term_any _ sigmaB).
        move=> Hgap_psd.
        rewrite {1}/Order.le /= /lef_def.
        exact: Hgap_psd.
      + rewrite h2mx1 mul1mx.
        change (@complex.Re R (\Tr sigma) =
                @complex.Re R (\Tr sigmaB)).
        by rewrite /sigmaB castlf_trlfE.
    - rewrite /PhiSet /SdpP /sdp_primal_set /=.
      move=> [X [PX HXfeas ->]].
      pose sigmaB : 'F[H]_B := mx2h X.
      pose sigma : 'F[H]_(S_AB :&: B) :=
        castlf (esym eqAB_cond, esym eqAB_cond) sigmaB.
      exists sigma.
      split.
      + by rewrite /sigma /sigmaB castlf_psdlfE qualifE mx2hK.
      + split.
        * rewrite /sigma (phi_lift_term_any _ sigmaB).
          have Hpsi_X : Psi (mx2h X) =
              (\1 : 'F[H]_A) \O sigmaB
            by rewrite /Psi superopE lfunE /= /Psi_lfun /Psi_fun /sigmaB.
          have Hmx :
              h2mx (((\1 : 'F[H]_A) \O sigmaB) - rhoAB) \is psdmx.
          {
            move: HXfeas.
            rewrite Hpsi_X le_lownerE.
            by rewrite raddfB.
          }
          rewrite qualifE.
          exact: Hmx.
        * rewrite h2mx1 mul1mx /sigma castlf_trlfE /sigmaB /lftrace mx2hK.
          done.
  }
  have [Hstrong_dual Hprimal_attained] :
      ExtNumTopology.etinf SdpP = ExtNumTopology.etsup SdpD /\
      SdpP (ExtNumTopology.etinf SdpP).
  {
    have HA : h2mx (\1 : 'F[H]_B) \is hermmx.
    {
      apply: psdmx_herm.
      by rewrite h2mx1; exact: psdmx1.
    }
    have HB : h2mx rhoAB \is hermmx.
    {
      apply: psdmx_herm.
      by move: Prho; rewrite qualifE.
    }
    have HPsi_herm :
        forall X : 'M[C]_(dim 'H[H]_B),
          X \is hermmx -> h2mx (Psi (mx2h X)) \is hermmx.
    {
      move=> X HX.
      rewrite /Psi superopE lfunE /= /Psi_lfun /Psi_fun.
      have HX_lf : mx2h X \is hermlf.
      {
        apply/hermlfP.
        apply/h2mx_inj.
        rewrite h2mx_adj !mx2hK.
        by move/hermmxP: HX.
      }
      have Hten_lf :
          ((\1 : 'F[H]_A) \O mx2h X : 'F[H]_S_AB) \is hermlf.
      {
        apply/hermlfP.
        move/hermlfP: HX_lf => HX_adj.
        by rewrite sdot_I_adj HX_adj.
      }
      by move: Hten_lf; rewrite qualifE.
    }
    have Hhas_inf : has_inf SdpP.
    {
      rewrite -Hphi_primal.
      exact: (@phi_min_feasible_has_inf L H S_AB B rhoAB Prho).
    }
    have Halpha_refl :
        ExtNumTopology.etinf SdpP =
        ExtNumTopology.etinf (@sdp_primal_set R 'H[H]_B 'H[H]_S_AB
          (h2mx (\1 : 'F[H]_B)) (h2mx rhoAB) Psi)
      by [].
    have Hbeta_refl :
        ExtNumTopology.etsup SdpD =
        ExtNumTopology.etsup (@sdp_dual_set R 'H[H]_B 'H[H]_S_AB
          (h2mx (\1 : 'F[H]_B)) (h2mx rhoAB) Psi)
      by [].
    have Hslater :
        exists Y : 'M[C]_(dim 'H[H]_S_AB),
          Y \is pdmx /\
          (h2mx (\1 : 'F[H]_B) - h2mx (Psi^*o (mx2h Y))) \is pdmx.
    {
      have Hscalar_pdmx :
          forall n (a : R), 0 < a ->
            (a%:C *: 1%:M : 'M[C]_n) \is pdmx.
      {
        move=> n a Ha.
        apply/pdmxP; split.
        - apply/hermmxP/matrixP=> i j.
          rewrite !mxE.
          case Eij: (i == j).
          + move/eqP: Eij=> ->.
            rewrite eqxx !mulr1.
            change (a%:C = (a%:C)^*%C).
            by rewrite conjc_real.
          + have Eji : (j == i) = false by rewrite eq_sym Eij.
            rewrite Eji !mulr0.
            change ((0 : C) = (0 : C)^*%C).
            by rewrite conjc0.
        - apply/posmxP=> i j.
          by rewrite scalemx1 spectral_diag_scale mxE posrE ltc0R.
      }
      have HPsi_dual_ptrace :
          forall Y : 'F[H]_S_AB,
            Psi^*o Y = ptrace_castl disAB Y.
      {
        move=> Y.
        apply/eqP/trlf_intror=> X.
        rewrite -dualso_trlfEV.
        rewrite /Psi superopE lfunE /= /Psi_lfun /Psi_fun.
        by rewrite trlf_lift_partial.
      }
      pose dA_R : R := (dim 'H[H]_A)%:R.
      pose half_R : R := GRing.inv (2%:R : R).
      pose c_R : R := half_R * GRing.inv dA_R.
      have HdA_pos : 0 < dA_R by rewrite /dA_R ltr0n dim_proper.
      have HdA_neq0 : dA_R != 0 by rewrite gt_eqF.
      have Hhalf_pos : 0 < half_R by rewrite /half_R invr_gt0 ltr0n.
      have Hc_pos : 0 < c_R.
      {
        rewrite /c_R.
        apply: mulr_gt0 => //.
        by rewrite invr_gt0.
      }
      have Hc_d : c_R * dA_R = half_R
        by rewrite /c_R -mulrA mulVf ?mulr1.
      have Hhalf_sub : 1 - half_R = half_R.
      {
        have Hsplit : 1 = half_R + half_R
          by rewrite /half_R split21.
        by rewrite {1}Hsplit addrK.
      }
      pose Ylf : 'F[H]_S_AB := c_R%:C *: \1.
      exists (h2mx Ylf).
      split.
      - rewrite /Ylf.
        move: (h2mxP c_R%:C (\1 : 'F[H]_S_AB) 0).
        rewrite h2mx0 !addr0 => ->.
        rewrite h2mx1.
        exact: Hscalar_pdmx Hc_pos.
      - have HPsiY :
            Psi^*o (mx2h (h2mx Ylf)) =
            half_R%:C *: (\1 : 'F[H]_B).
        {
          have HptrI :
              ptrace_castl disAB (\1 : 'F[H]_S_AB) =
              dA_R%:C *: (\1 : 'F[H]_B)
            by rewrite -sdotf11 ptrace_castl_sdot_I /dA_R.
          have HptrZ :
              ptrace_castl disAB Ylf =
              c_R%:C *: ptrace_castl disAB (\1 : 'F[H]_S_AB)
            by rewrite /Ylf /ptrace_castl /ptrace_cast_gen linearZ /=
              linearZ /=.
          rewrite h2mxK HPsi_dual_ptrace HptrZ HptrI scalerA.
          by rewrite -realcM Hc_d.
        }
        rewrite HPsiY.
        move: (h2mxP half_R%:C (\1 : 'F[H]_B) 0).
        rewrite h2mx0 !addr0 => ->.
        rewrite h2mx1.
        have Hhalf_subC : 1 - half_R%:C = half_R%:C
          by rewrite -realcB Hhalf_sub.
        have Hdiff_eq :
            (1%:M : 'M[C]_(dim 'H[H]_B)) -
              half_R%:C *: 1%:M =
            half_R%:C *: 1%:M.
        {
          have Hright :
              half_R%:C *: (1%:M : 'M[C]_(dim 'H[H]_B)) =
              ((1 : C) - half_R%:C) *: 1%:M
            by rewrite Hhalf_subC.
          rewrite [X in _ = X]Hright.
          by rewrite scalerBl scale1r.
        }
        rewrite Hdiff_eq.
        exact: Hscalar_pdmx Hhalf_pos.
    }
    have [Hdual_eq Hprimal] :=
      @sdp_strong_primal R 'H[H]_B 'H[H]_S_AB
        (h2mx (\1 : 'F[H]_B)) (h2mx rhoAB) Psi
        (ExtNumTopology.etinf SdpP) (ExtNumTopology.etsup SdpD)
        HA HB HPsi_herm Hhas_inf Halpha_refl Hbeta_refl Hslater.
    split; first exact: Hdual_eq.
    move: Hprimal => [X [PX HfeasX HobjX]].
    exists X.
    by split.
  }
  have HPsi_dual_ptrace :
      forall Y : 'F[H]_S_AB,
        Psi^*o Y = ptrace_castl disAB Y.
  {
    move=> Y.
    apply/eqP/trlf_intror=> X.
    rewrite -dualso_trlfEV.
    rewrite /Psi superopE lfunE /= /Psi_lfun /Psi_fun.
    by rewrite trlf_lift_partial.
  }
  pose Dineq : set R := fun v : R =>
    exists Y : 'F[H]_S_AB,
      [/\ Y \is psdlf,
          ptrace_castl disAB Y <= (\1 : 'F[H]_B) &
          v = @complex.Re R (\Tr (rhoAB \o Y))].
  have Hdual_ineq : SdpD = Dineq.
  {
    apply/funext=> v /=.
    apply/propext; split.
    - rewrite /SdpD /Dineq /sdp_dual_set /=.
      move=> [Y [PY HY ->]].
      exists (mx2h Y).
      split.
      + by rewrite qualifE mx2hK.
      + rewrite lef_h2mx h2mx1.
        move: HY.
        rewrite h2mx1.
        move=> HYmx.
        have HptrY := congr1 h2mx (HPsi_dual_ptrace (mx2h Y)).
        move: HptrY.
        move=> <-.
        exact: HYmx.
      + by rewrite /lftrace h2mx_comp mx2hK.
    - rewrite /SdpD /Dineq /sdp_dual_set /=.
      move=> [Y [PY HY ->]].
      exists (h2mx Y).
      split.
      + by move: PY; rewrite qualifE.
      + move: HY.
        rewrite lef_h2mx h2mx1.
        have HptrY := congr1 h2mx (HPsi_dual_ptrace Y).
        rewrite h2mxK.
        move=> HYmx.
        move: HptrY.
        move=> ->.
        exact: HYmx.
      + by rewrite /lftrace h2mx_comp.
  }
  split.
  - rewrite Halpha_phi Hphi_primal Hstrong_dual Hdual_ineq /Dineq.
    by rewrite /ExtNumTopology.etsup /sup.
  - change (PhiSet (phi_min B rhoAB)).
    by rewrite Halpha_phi Hphi_primal.
Qed.

(* infra: no tex label — reusable SDP bridge for Tomamichel's Phi functional. *)
(* math: the primal Phi value equals the dual SDP value for the Φ         *)
(*   functional (Tomamichel thesis, arXiv:1203.2142, Sec. 4.5).           *)
(* path: entropy:phi_min_dual -> *)
(*   bb84:bb84_secret *)
Lemma phi_min_dual (rhoAB : 'F[H]_S_AB) :
  rhoAB \is psdlf ->
  phi_min B rhoAB =
  sup [set v : R | exists Y : 'F[H]_S_AB,
    [/\ Y \is psdlf,
        ptrace_castl disAB Y <= (\1 : 'F[H]_B) &
        v = @complex.Re R (\Tr (rhoAB \o Y))]].
Proof.
  by move=> Prho; have [Hdual _] := phi_min_sdp_strong Prho.
Qed.

(* infra: no tex label — reusable primal optimizer for Tomamichel's Phi SDP. *)
(* path: entropy:phi_min_primal_attained -> *)
(*   bb84:bb84_secret *)
Lemma phi_min_primal_attained (rhoAB : 'F[H]_S_AB) :
  rhoAB \is psdlf ->
  phi_min_feasible B rhoAB (phi_min B rhoAB).
Proof.
  by move=> Prho; have [_ Hprimal] := phi_min_sdp_strong Prho.
Qed.

(* infra: no tex label — pointwise weak duality for Phi dual witnesses. *)
(* path: entropy:phi_min_dual_feasible_ub -> *)
(*   bb84:bb84_secret *)
Lemma phi_min_dual_feasible_ub (rhoAB Y : 'F[H]_S_AB) :
  rhoAB \is psdlf ->
  Y \is psdlf ->
  ptrace_castl disAB Y <= (\1 : 'F[H]_B) ->
  @complex.Re R (\Tr (rhoAB \o Y)) <= phi_min B rhoAB.
Proof.
  move=> Prho PY HY.
  have [sigma [Psigma [Hgap Hsigma_tr]]] :=
    phi_min_primal_attained Prho.
  have eqAB_diff : S_AB :\: B = A by exact: setDU_r.
  have eqAB_cond : S_AB :&: B = B by setdec.
  have eqAB_lift : (S_AB :\: B) :|: B = S_AB by rewrite eqAB_diff.
  have eqAB_lift_sig :
      (S_AB :\: B) :|: (S_AB :&: B) =
      (S_AB :\: B) :|: B by rewrite eqAB_cond.
  have eqAB_phi :
      (S_AB :\: B) :|: (S_AB :&: B) = S_AB
    by rewrite finset.setUC finset.setID.
  pose sigmaB : 'F[H]_B := castlf (eqAB_cond, eqAB_cond) sigma.
  have PsigmaB : sigmaB \is psdlf
    by rewrite /sigmaB castlf_psdlfE.
  have phi_lift_term
      (eqp : (S_AB :\: B) :|: (S_AB :&: B) = S_AB) :
      castlf (eqp, eqp)
        ((\1 : 'F[H]_(S_AB :\: B)) \O sigma) =
      (\1 : 'F[H]_A) \O sigmaB.
  {
    have -> : eqp = etrans eqAB_lift_sig eqAB_lift
      by apply: eq_irrelevance.
    rewrite -castlf_comp.
    rewrite (@sdotIf_cast_r R _ _ (S_AB :\: B)
      (S_AB :&: B) B eqAB_cond eqAB_lift_sig sigma).
    rewrite (@sdotIf_cast_l R _ _ (S_AB :\: B) A B
      eqAB_diff eqAB_lift
      (\1 : 'F[H]_(S_AB :\: B)) sigmaB).
    have -> :
        castlf (eqAB_diff, eqAB_diff)
          (\1 : 'F[H]_(S_AB :\: B)) =
        (\1 : 'F[H]_A) by exact: castlf1.
    by rewrite /sigmaB.
  }
  have Hrho_le_lift : rhoAB <= (\1 : 'F[H]_A) \O sigmaB.
  {
    move: Hgap.
    rewrite lefE.
    match goal with
    | |- context[castlf (?p, ?p) _] =>
        rewrite (phi_lift_term p)
    end.
    done.
  }
  have HrhoY_le : \Tr (rhoAB \o Y) <=
      \Tr (((\1 : 'F[H]_A) \O sigmaB) \o Y).
  {
    move/lef_psdtr: Hrho_le_lift => /(_ Y PY).
    exact.
  }
  have HrhoY_leR :
      @complex.Re R (\Tr (rhoAB \o Y)) <=
      @complex.Re R (\Tr (((\1 : 'F[H]_A) \O sigmaB) \o Y)).
  {
    move: HrhoY_le.
    by rewrite lecE /= => /andP[_].
  }
  have Hlift_trace :
      \Tr (((\1 : 'F[H]_A) \O sigmaB) \o Y) =
      \Tr ((ptrace_castl disAB Y) \o sigmaB).
  {
    rewrite lftraceC.
    by rewrite trlf_lift_partial.
  }
  have Hptr_le : \Tr ((ptrace_castl disAB Y) \o sigmaB) <=
      \Tr ((\1 : 'F[H]_B) \o sigmaB).
  {
    move/lef_psdtr: HY => /(_ sigmaB PsigmaB).
    exact.
  }
  have Hptr_leR :
      @complex.Re R (\Tr ((ptrace_castl disAB Y) \o sigmaB)) <=
      @complex.Re R (\Tr sigmaB).
  {
    move: Hptr_le.
    rewrite comp_lfun1l lecE /= => /andP[_].
    exact.
  }
  apply: (le_trans HrhoY_leR).
  rewrite Hlift_trace.
  apply: (le_trans Hptr_leR).
  rewrite /sigmaB castlf_trlfE.
  by rewrite -Hsigma_tr.
Qed.

End PhiMinDualBridge.

Section HminEProps.
Variable (L : finType) (H : L -> chsType).
Variable (S T : {set L}).

(* path: entropy:phi_min_pos_trace -> *)
(*   bb84:privacy_amplification -> bb84:bb84_secret *)
Lemma phi_min_pos_trace (rhoS : 'F[H]_S) :
  rhoS \is psdlf ->
  @complex.Re R (\Tr rhoS) <= 1 ->
  0 < @complex.Re R (\Tr rhoS) ->
  0 < phi_min T rhoS.
Proof.
  move=> Prho Hrho_tr Hrho_tr_pos.
  have eqST : (S :\: T) :|: (S :&: T) = S.
    by rewrite finset.setUC finset.setID.
  have disSplit : [disjoint (S :\: T) & (S :&: T)].
  { apply/disjointP=> z; rewrite !inE.
    by case: (z \in T); rewrite ?andbF ?andbT. }
  pose dT : R := (dim 'H[H]_(S :\: T))%:R.
  have HdT_pos : 0 < dT by rewrite /dT ltr0n dim_proper.
  rewrite /phi_min.
  apply: (@lt_le_trans _ _ ((@complex.Re R (\Tr rhoS)) / dT)).
  - by apply: divr_gt0.
  - apply: lb_le_inf.
    + pose sigma1 : 'F[H]_(S :&: T) := \1.
      exists (@complex.Re R (\Tr sigma1)).
      rewrite /phi_min_feasible.
      exists sigma1; split.
      { by rewrite qualifE h2mx1; apply: psdmx1. }
      split; last by [].
      rewrite sdotf11 castlf1.
      have Hrho_den : rhoS \is denlf.
      { apply/denlfP; split=> //.
        have Hreal : \Tr rhoS \is Num.real := ger0_real (psdlf_trlf Prho).
        by rewrite -(RRe_real Hreal) lecR. }
      have Hrho_le1 : rhoS ⊑ (\1 : 'F[H]_S)
        := denf_le1 (DenLf_Build Hrho_den).
      by move: Hrho_le1; rewrite lefE.
    + move=> v [sigma [Psigma [Hfeas ->]]].
      have Htr_sigma_real :
          (\Tr sigma : C) = (@complex.Re R (\Tr sigma))%:C
        by rewrite RRe_real // ger0_real // psdlf_trlf.
      have Hrho_tr_real : (\Tr rhoS : C) = (@complex.Re R (\Tr rhoS))%:C
        by rewrite RRe_real // ger0_real // psdlf_trlf.
      have Hrho_leC :
          \Tr rhoS <= (dim 'H[H]_(S :\: T))%:R * \Tr sigma.
      { have Hgap_nonneg := psdlf_trlf Hfeas.
        move: Hgap_nonneg.
        rewrite linearB /= castlf_trlfE (trlf_lift_I disSplit).
        by rewrite subr_ge0. }
      move: Hrho_leC; rewrite Hrho_tr_real Htr_sigma_real.
      rewrite /dT -natrC -rmorphM /= lecR => Hrho_leR.
      rewrite ler_pdivrMr //.
      by rewrite mulrC.
Qed.

(* path: entropy:hminE_EFin -> bb84:privacy_amplification -> *)
(*   bb84:bb84_secret *)
Lemma hminE_EFin (rhoS : 'F[H]_S) :
  0 < phi_min T rhoS ->
  hminE T rhoS = (hmin T rhoS)%:E.
Proof.
  by move=> Hphi; rewrite /hminE /hmin (elog2_gt0 Hphi).
Qed.

End HminEProps.

Section HmaxProps.
Variable (L : finType) (H : L -> chsType).
Variable (S T : {set L}).

Let eqST_max : (S :\: T) :|: (S :&: T) = S.
Proof.
  by rewrite finset.setUC finset.setID.
Defined.

(* hmax_has_sup *)
(* infra: no tex label — reusable labelled hmax witness-set boundedness. *)
(* path: entropy:hmax_has_sup -> entropy:entropy_data_proc -> *)
(*   bb84:bb84_secret *)
Lemma hmax_has_sup (rhoS : 'F[H]_S) :
  rhoS \is psdlf ->
  @complex.Re R (\Tr rhoS) <= 1 ->
  0 < @complex.Re R (\Tr rhoS) ->
  has_sup [set v : R | hmax_feasible T rhoS v].
Proof.
  move=> Prho Htr Ht_pos.
  pose t := @complex.Re R (\Tr rhoS).
  pose dA : R := (dim 'H[H]_(S :\: T))%:R.
  pose dB : R := (dim 'H[H]_(S :&: T))%:R.
  pose dinvB : R := GRing.inv dB.
  pose dinv : R := GRing.inv dA * GRing.inv dB.
  pose E : set R := [set v : R | hmax_feasible T rhoS v]%classic.
  have Ht_ge0 : 0 <= t.
  {
    have /= := psdlf_trlf Prho.
    by rewrite /t lecE /= => /andP[].
  }
  have HdA_pos_nat : (0 < dim 'H[H]_(S :\: T))%N := dim_proper.
  have HdB_pos_nat : (0 < dim 'H[H]_(S :&: T))%N := dim_proper.
  have HdA_pos : 0 < dA by rewrite /dA ltr0n.
  have HdB_pos : 0 < dB by rewrite /dB ltr0n.
  have HdinvB_pos : 0 < dinvB by rewrite /dinvB invr_gt0.
  have Hdinv_pos : 0 < dinv.
  {
    by rewrite /dinv mulr_gt0 ?invr_gt0.
  }
  have Hlift_psd :
      forall sigma : 'F[H]_(S :&: T),
        sigma \is psdlf ->
        castlf (eqST_max, eqST_max)
          ((\1 : 'F[H]_(S :\: T)) \O sigma) \is psdlf.
  {
    move=> sigma Psigma.
    have disST : [disjoint S :\: T & S :&: T].
    {
      apply/disjointP=> x.
      rewrite !inE.
      by case: (x \in S); case: (x \in T).
    }
    have Hten :
        ((\1 : 'F[H]_(S :\: T)) \O sigma :
          'F[H]_((S :\: T) :|: (S :&: T))) =
        ((\1 : 'F[H]_(S :\: T)) \⊗ sigma).
    {
      by apply: to_Fnd_inj; rewrite (sdotFT _ _ disST) to_Fnd_tenE.
    }
    rewrite castlf_psdlfE Hten psdlfE.
    apply: tenf_ge0; first exact: disST.
    - by rewrite -psdlfE qualifE h2mx1; exact: psdmx1.
    - by rewrite -psdlfE.
  }
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
      move: (h2mxP ((@complex.Re R (\Tr f))%:C) (\1 : 'F[H]_S0) 0).
      rewrite h2mx0 !addr0 => ->.
      by rewrite h2mx1 /lftrace (RRe_real Htr_real) scalemx1.
    }
    apply: lemx_psd_ub.
    by rewrite qualifE.
  }
  have scale_lef_local :
      forall (S0 : {set L}) (x y : 'F[H]_S0) (a : R),
        0 <= a -> x <= y -> (a%:C *: x) <= (a%:C *: y).
  {
    move=> S0 x y a Ha Hxy.
    move: Hxy; rewrite lefE=> Hpsd.
    rewrite lefE.
    have -> : a%:C *: y - a%:C *: x = a%:C *: (y - x).
      by rewrite scalerBr.
    apply: psdlfZ.
    - by rewrite lecR.
    - exact: Hpsd.
  }
  have Hfid_scale :
      forall (S0 : {set L}) (x y : 'F[H]_S0) (a b : R),
        0 <= a -> 0 <= b ->
        x \is psdlf -> y \is psdlf ->
        fidelity (a%:C *: x) (b%:C *: y) =
          Num.sqrt a * Num.sqrt b * fidelity x y.
  {
    move=> S0 x y a b Ha Hb Px Py.
    rewrite /fidelity.
    rewrite (sqrtHZ_nn Ha Px) (sqrtHZ_nn Hb Py).
    rewrite -!comp_lfunZl -!comp_lfunZr scalerA.
    have -> :
        ((Num.sqrt a)%:C * (Num.sqrt b)%:C : C) =
        ((Num.sqrt a * Num.sqrt b)%:C : C).
      by rewrite rmorphM.
    change (trnormH (((Num.sqrt a * Num.sqrt b)%:C) *:
              (sqrtH x \o sqrtH y)) =
            Num.sqrt a * Num.sqrt b * fidelity x y).
    rewrite trnormH_scaleZ.
    rewrite ger0_norm; last first.
    {
      apply: mulr_ge0; exact: sqrtr_ge0.
    }
    by rewrite /fidelity /trnormH.
  }
  have Hfid_ge0 :
      forall (S0 : {set L}) (x y : 'F[H]_S0), 0 <= fidelity x y.
  {
    move=> S0 x y.
    rewrite /fidelity.
    have /= := trnorm_ge0 (h2mx (sqrtH x \o sqrtH y)).
    by rewrite lecE /= => /andP[].
  }
  have Hfid_le_gfid :
      forall (S0 : {set L}) (x y : 'F[H]_S0),
        x \is psdlf -> y \is psdlf ->
        fidelity x y <= gfid x y.
  {
    move=> S0 x y Px Py.
    have Pxmx : h2mx x \is psdmx by move: Px; rewrite qualifE.
    have Pymx : h2mx y \is psdmx by move: Py; rewrite qualifE.
    have Hgf := alt_gfid_gen (rho:=h2mx x) (tau:=h2mx y) Pxmx Pymx.
    rewrite /fidelity !h2mx_comp !sqrtH_h2mx.
    rewrite /gfid Hgf.
    rewrite lerDl.
    apply: mulr_ge0; exact: sqrtr_ge0.
  }
  pose sigmaI : 'F[H]_(S :&: T) := dinvB%:C *: (\1 : 'F[H]_(S :&: T)).
  pose XI := castlf (eqST_max, eqST_max)
    ((GRing.inv dA)%:C *: ((\1 : 'F_(S :\: T)) \O sigmaI)).
  pose vI := log2 (dA * (gfid rhoS XI) ^+ 2).
  have PsigmaI : sigmaI \is psdlf.
  {
    rewrite /sigmaI.
    apply: psdlfZ.
    - by rewrite lecR invr_ge0.
    - by rewrite qualifE h2mx1; exact: psdmx1.
  }
  have HsigmaI_tr1 : \Tr sigmaI = 1.
  {
    have Hd_nonzero : dB != 0.
    {
      exact: lt0r_neq0 HdB_pos.
    }
    rewrite /sigmaI linearZ /= /dinvB /dB /lftrace h2mx1 mxtrace1.
    rewrite -natrC -rmorphM /= mulrC (mulfV Hd_nonzero).
    exact: rmorph1.
  }
  have HsigmaI_den : sigmaI \is den1lf
    by apply/den1lfP; split.
  have HXI_eq : XI = dinv%:C *: (\1 : 'F[H]_S).
  {
    rewrite /XI /sigmaI sdotfZr !linearZ /=.
    have -> :
        castlf (eqST_max, eqST_max)
          ((\1 : 'F_(S :\: T)) \O (\1 : 'F[H]_(S :&: T))) =
        (\1 : 'F[H]_S).
    {
      rewrite sdotf11.
      exact: castlf1.
    }
    by rewrite scalerA /dinv -rmorphM.
  }
  have PXI : XI \is psdlf.
  {
    rewrite /XI linearZ /=.
    apply: psdlfZ; first by rewrite lecR invr_ge0 /dA ler0n.
    exact: Hlift_psd PsigmaI.
  }
  have Hrho_le_tI : rhoS <= t%:C *: (\1 : 'F[H]_S).
    exact: psdlf_le_tr_id_local.
  have HtI_le_I : t%:C *: (\1 : 'F[H]_S) <= (\1 : 'F[H]_S).
  {
    rewrite lefE.
    have -> :
        (\1 : 'F[H]_S) - t%:C *: (\1 : 'F[H]_S) =
        (1 - t)%:C *: (\1 : 'F[H]_S).
    {
      rewrite rmorphB scalerBl.
      by rewrite scale1r.
    }
    apply: psdlfZ.
    - by rewrite lecR subr_ge0.
    - by rewrite qualifE h2mx1; exact: psdmx1.
  }
  have Hrho_le_I : rhoS <= (\1 : 'F[H]_S).
    exact: le_trans Hrho_le_tI HtI_le_I.
  have Hscaled_le_XI : dinv%:C *: rhoS <= XI.
  {
    rewrite HXI_eq.
    apply: (@scale_lef_local S rhoS (\1 : 'F[H]_S) dinv).
    - exact: ltW Hdinv_pos.
    - exact: Hrho_le_I.
  }
  have Pscaled : (dinv%:C *: rhoS : 'F[H]_S) \is psdlf.
  {
    apply: psdlfZ.
    - rewrite lecR; exact: ltW Hdinv_pos.
    - exact: Prho.
  }
  have Hfid_scaled_le :
      fidelity rhoS (dinv%:C *: rhoS) <= fidelity rhoS XI.
  {
    rewrite /fidelity !h2mx_comp !sqrtH_h2mx.
    apply: fid_v_mono_r_psd_mx.
    - by move: Prho; rewrite qualifE.
    - by move: Pscaled; rewrite qualifE.
    - by move: PXI; rewrite qualifE.
    - by move: Hscaled_le_XI; rewrite lef_h2mx.
  }
  have Hfid_refl : fidelity rhoS rhoS = t.
  {
    have Prho_mx : h2mx rhoS \is psdmx.
    {
      by move: Prho; rewrite qualifE.
    }
    rewrite /fidelity !h2mx_comp !sqrtH_h2mx.
    have -> : sqrtmx (h2mx rhoS) *m sqrtmx (h2mx rhoS) = h2mx rhoS.
      by rewrite sqrtmxK.
    by rewrite (psdmx_trnorm Prho_mx) /t /lftrace.
  }
  have Hfid_scaled_eq :
      fidelity rhoS (dinv%:C *: rhoS) = Num.sqrt dinv * t.
  {
    have Htmp := @Hfid_scale S rhoS rhoS 1 dinv
      ler01 (ltW Hdinv_pos) Prho Prho.
    rewrite sqrtr1 mul1r Hfid_refl in Htmp.
    have -> : fidelity rhoS (dinv%:C *: rhoS) =
              fidelity ((1 : C) *: rhoS) (dinv%:C *: rhoS).
    {
      by rewrite scale1r.
    }
    exact: Htmp.
  }
  have Hsqrtd_t_le_fid : Num.sqrt dinv * t <= fidelity rhoS XI.
  {
    by rewrite -Hfid_scaled_eq.
  }
  have Hsqrtd_t_pos : 0 < Num.sqrt dinv * t.
  {
    apply: mulr_gt0.
    - by rewrite sqrtr_gt0.
    - exact: Ht_pos.
  }
  have HfidXI_pos : 0 < fidelity rhoS XI.
  {
    exact: lt_le_trans Hsqrtd_t_pos Hsqrtd_t_le_fid.
  }
  have HgfXI_pos : 0 < gfid rhoS XI.
  {
    exact: lt_le_trans HfidXI_pos (Hfid_le_gfid _ _ _ Prho PXI).
  }
  have HfeasI : E vI.
  {
    exists sigmaI; split.
    - exact: HsigmaI_den.
    - rewrite /vI elog2_gt0.
      + reflexivity.
      + apply: mulr_gt0; first exact: HdA_pos.
        by rewrite expr2; apply: mulr_gt0.
  }
  split.
  - exists vI.
    exact: HfeasI.
  - pose aDim : R := (dim 'H[H]_(S :\: T))%:R.
    have HaDim_ge1 : 1 <= aDim.
    {
      rewrite /aDim.
      have Hdim_ge1 : (1 <= dim 'H[H]_(S :\: T))%N := dim_proper.
      change (((1%N)%:R : R) <= (dim 'H[H]_(S :\: T))%:R).
      by rewrite ler_nat.
    }
    exists (log2 aDim) => v [sigma [Psigma_den Hve]].
    have Psigma : sigma \is psdlf := den1lf_psd Psigma_den.
    pose X :=
      castlf (eqST_max, eqST_max)
        (((dim 'H[H]_(S :\: T))%:R^-1)%:C *:
          ((\1 : 'F_(S :\: T)) \O sigma)).
    have PX : X \is psdlf.
    {
      rewrite /X linearZ /=.
      apply: psdlfZ; first by rewrite lecR invr_ge0 ler0n.
      exact: Hlift_psd Psigma.
    }
    have Hsq_le : aDim * (gfid rhoS X) ^+ 2 <= aDim.
    {
      have disST : [disjoint S :\: T & S :&: T].
      {
        apply/disjointP=> x.
        rewrite !inE.
        by case: (x \in S); case: (x \in T).
      }
      have Htr_X1 : \Tr X = 1.
      {
        have HaDim_neq0 : aDim != 0 by exact: lt0r_neq0.
        rewrite /X castlf_trlfE linearZ /= (trlf_lift_I disST).
        rewrite (den1lf_trlf Psigma_den).
        rewrite /aDim -natrC -rmorphM /=.
        rewrite mulr1 -rmorphM /=.
        by rewrite mulVf ?rmorph1.
      }
      have Htr_X_le : @complex.Re R (\Tr X) <= 1
        by rewrite Htr_X1 -(re_realid 1).
        have Hgf_le1 : gfid rhoS X <= 1.
        {
          rewrite /gfid.
          have Hrho_mx_den : h2mx rhoS \is denmx.
          { apply: denmx_psd_re_tr_le; first by move: Prho; rewrite qualifE.
            exact: Htr. }
          have HX_mx_den : h2mx X \is denmx.
          { apply: denmx_psd_re_tr_le; first by move: PX; rewrite qualifE.
            exact: Htr_X_le. }
          exact: gfid_le1_mx Hrho_mx_den HX_mx_den.
        }
      have Hgf_ge0 : 0 <= gfid rhoS X.
      {
        rewrite /gfid.
        apply: gfid_ge0_mx.
        - by move: Prho; rewrite qualifE.
        - by move: PX; rewrite qualifE.
      }
      have Hsq_le1 : (gfid rhoS X) ^+ 2 <= 1.
      {
        rewrite -[leRHS]mulr1.
        by apply: ler_pM.
      }
      have HaDim_ge0 : 0 <= aDim by exact: ltW.
      have := ler_wpM2l HaDim_ge0 Hsq_le1.
      by rewrite mulr1.
    }
    set g2 := aDim * (gfid rhoS X) ^+ 2 in Hsq_le *.
    have Hg2_pos : 0 < g2.
    {
      case: (ltP 0 g2) => // Hg2_le0.
      move: Hve.
      rewrite (elog2_le0 Hg2_le0).
      by discriminate.
    }
    have -> : v = log2 g2.
    {
      move: Hve.
      rewrite (elog2_gt0 Hg2_pos).
      by case.
    }
    exact: (log2_le_pos Hg2_pos Hsq_le).
Qed.

(* hmax_ub *)
(* infra: API wrapper for hmax_feasible → hmax upper bound                *)
(* consumer: hmax_ub is used downstream by the BB84 secrecy proof. *)
(* path: entropy:hmax_ub -> entropy:entropy_data_proc -> *)
(*   bb84:bb84_secret *)
Lemma hmax_ub (rhoS : 'F[H]_S) v :
  has_sup [set w : R | hmax_feasible T rhoS w] ->
  hmax_feasible T rhoS v -> v <= hmax T rhoS.
Proof.
  move=> Hsup Hv.
  rewrite /hmax.
  have /ubP Hub := sup_upper_bound Hsup.
  exact: Hub.
Qed.

(* hmax_lub *)
(* infra: API wrapper — least-upper-bound property of hmax                *)
(* consumer: hmax_lub is used downstream by the BB84 secrecy proof. *)
(* path: entropy:hmax_lub -> entropy:entropy_data_proc -> *)
(*   bb84:bb84_secret *)
Lemma hmax_lub (rhoS : 'F[H]_S) ub :
  has_sup [set v : R | hmax_feasible T rhoS v] ->
  (forall v, hmax_feasible T rhoS v -> v <= ub) ->
  hmax T rhoS <= ub.
Proof.
  move=> Hsup Hub.
  have Hne : ([set v : R | hmax_feasible T rhoS v] !=set0)%classic
    by case: Hsup.
  rewrite /hmax.
  exact: ge_sup Hne Hub.
Qed.

(* hmaxE_EFin *)
(* infra: finite-branch bridge for the extended max-entropy definition.  *)
(* path: entropy:hmaxE_EFin -> entropy:smooth_hmaxE_EFin -> *)
(*   bb84:bb84_secret *)
Lemma hmaxE_EFin (rhoS : 'F[H]_S) :
  rhoS \is psdlf ->
  @complex.Re R (\Tr rhoS) <= 1 ->
  0 < @complex.Re R (\Tr rhoS) ->
  hmaxE T rhoS = (hmax T rhoS)%:E.
Proof.
  move=> Prho Htr Hpos.
  pose Efin : set R := [set v : R | hmax_feasible T rhoS v]%classic.
  have Hsup : has_sup Efin := hmax_has_sup Prho Htr Hpos.
  have Hhas_ub : has_ubound Efin by case: Hsup.
  have Hne : (Efin !=set0)%classic by case: Hsup.
  apply/eqP; rewrite eq_le; apply/andP; split.
  - rewrite /hmaxE.
    apply: ge_ereal_sup => v [sigma [Psigma ->]].
    set arg := (dim 'H[H]_(S :\: T))%:R *
      (gfid rhoS
        (castlf (eqST_max, eqST_max)
          ((((dim 'H[H]_(S :\: T))%:R^-1)%:C *:
            ((\1 : 'F_(S :\: T)) \O sigma))))) ^+ 2.
    case: (ltP 0 arg) => Harg_pos.
    + rewrite (elog2_gt0 Harg_pos) lee_fin.
      have Hfeas : hmax_feasible T rhoS
          (log2 arg).
      {
        exists sigma; split=> //.
        rewrite /arg.
        by rewrite (elog2_gt0 Harg_pos).
      }
      exact: hmax_ub Hsup Hfeas.
    + by rewrite (elog2_le0 Harg_pos) leNye.
  - rewrite /hmax /hmaxE.
    rewrite -(@ereal_sup_EFin R Efin Hhas_ub Hne).
    apply: ereal_sup_le => v [r Hr <-].
    move: Hr => [sigma [Psigma Hv]].
    exists sigma; split.
    + exact: Psigma.
    + exact: esym Hv.
Qed.

(* hmax_lb_dim *)
(* infra: no tex label — fundamental & reusable (mathcomp-style) *)
(* path: entropy:hmax_lb_dim -> entropy:smooth_hmax_lb -> *)
(*   entropy:smooth_hmaxE_EFin -> *)
(*   bb84:bb84_secret *)
Lemma hmax_lb_dim (rhoS : 'F[H]_S) :
  rhoS \is psdlf ->
  @complex.Re R (\Tr rhoS) <= 1 ->
  0 < @complex.Re R (\Tr rhoS) ->
  log2 (((dim 'H[H]_(S :&: T))%:R)^-1 *
        (@complex.Re R (\Tr rhoS)) ^+ 2) <= hmax T rhoS.
Proof.
  move=> Prho Htr Ht_pos.
  pose t := @complex.Re R (\Tr rhoS).
  pose dA : R := (dim 'H[H]_(S :\: T))%:R.
  pose dB : R := (dim 'H[H]_(S :&: T))%:R.
  pose dinvB : R := GRing.inv dB.
  pose dinv : R := GRing.inv dA * GRing.inv dB.
  pose E : set R := [set v : R | hmax_feasible T rhoS v]%classic.
  have Ht_ge0 : 0 <= t.
  {
    have /= := psdlf_trlf Prho.
    by rewrite /t lecE /= => /andP[].
  }
  have HdA_pos_nat : (0 < dim 'H[H]_(S :\: T))%N := dim_proper.
  have HdB_pos_nat : (0 < dim 'H[H]_(S :&: T))%N := dim_proper.
  have HdA_pos : 0 < dA by rewrite /dA ltr0n.
  have HdB_pos : 0 < dB by rewrite /dB ltr0n.
  have HdinvB_pos : 0 < dinvB by rewrite /dinvB invr_gt0.
  have Hdinv_pos : 0 < dinv.
  {
    by rewrite /dinv mulr_gt0 ?invr_gt0.
  }
  have Hlift_psd :
      forall sigma : 'F[H]_(S :&: T),
        sigma \is psdlf ->
        castlf (eqST_max, eqST_max)
          ((\1 : 'F[H]_(S :\: T)) \O sigma) \is psdlf.
  {
    move=> sigma Psigma.
    have disST : [disjoint S :\: T & S :&: T].
    {
      apply/disjointP=> x.
      rewrite !inE.
      by case: (x \in S); case: (x \in T).
    }
    have Hten :
        ((\1 : 'F[H]_(S :\: T)) \O sigma :
          'F[H]_((S :\: T) :|: (S :&: T))) =
        ((\1 : 'F[H]_(S :\: T)) \⊗ sigma).
    {
      by apply: to_Fnd_inj; rewrite (sdotFT _ _ disST) to_Fnd_tenE.
    }
    rewrite castlf_psdlfE Hten psdlfE.
    apply: tenf_ge0; first exact: disST.
    - by rewrite -psdlfE qualifE h2mx1; exact: psdmx1.
    - by rewrite -psdlfE.
  }
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
      move: (h2mxP ((@complex.Re R (\Tr f))%:C) (\1 : 'F[H]_S0) 0).
      rewrite h2mx0 !addr0 => ->.
      by rewrite h2mx1 /lftrace (RRe_real Htr_real) scalemx1.
    }
    apply: lemx_psd_ub.
    by rewrite qualifE.
  }
  have scale_lef_local :
      forall (S0 : {set L}) (x y : 'F[H]_S0) (a : R),
        0 <= a -> x <= y -> (a%:C *: x) <= (a%:C *: y).
  {
    move=> S0 x y a Ha Hxy.
    move: Hxy; rewrite lefE=> Hpsd.
    rewrite lefE.
    have -> : a%:C *: y - a%:C *: x = a%:C *: (y - x).
      by rewrite scalerBr.
    apply: psdlfZ.
    - by rewrite lecR.
    - exact: Hpsd.
  }
  have Hfid_scale :
      forall (S0 : {set L}) (x y : 'F[H]_S0) (a b : R),
        0 <= a -> 0 <= b ->
        x \is psdlf -> y \is psdlf ->
        fidelity (a%:C *: x) (b%:C *: y) =
          Num.sqrt a * Num.sqrt b * fidelity x y.
  {
    move=> S0 x y a b Ha Hb Px Py.
    rewrite /fidelity.
    rewrite (sqrtHZ_nn Ha Px) (sqrtHZ_nn Hb Py).
    rewrite -!comp_lfunZl -!comp_lfunZr scalerA.
    have -> :
        ((Num.sqrt a)%:C * (Num.sqrt b)%:C : C) =
        ((Num.sqrt a * Num.sqrt b)%:C : C).
      by rewrite rmorphM.
    change (trnormH (((Num.sqrt a * Num.sqrt b)%:C) *:
              (sqrtH x \o sqrtH y)) =
            Num.sqrt a * Num.sqrt b * fidelity x y).
    rewrite trnormH_scaleZ.
    rewrite ger0_norm; last first.
    {
      apply: mulr_ge0; exact: sqrtr_ge0.
    }
    by rewrite /fidelity /trnormH.
  }
  have Hfid_ge0 :
      forall (S0 : {set L}) (x y : 'F[H]_S0), 0 <= fidelity x y.
  {
    move=> S0 x y.
    rewrite /fidelity.
    have /= := trnorm_ge0 (h2mx (sqrtH x \o sqrtH y)).
    by rewrite lecE /= => /andP[].
  }
  have Hfid_le_gfid :
      forall (S0 : {set L}) (x y : 'F[H]_S0),
        x \is psdlf -> y \is psdlf ->
        fidelity x y <= gfid x y.
  {
    move=> S0 x y Px Py.
    have Pxmx : h2mx x \is psdmx by move: Px; rewrite qualifE.
    have Pymx : h2mx y \is psdmx by move: Py; rewrite qualifE.
    have Hgf := alt_gfid_gen (rho:=h2mx x) (tau:=h2mx y) Pxmx Pymx.
    rewrite /fidelity !h2mx_comp !sqrtH_h2mx.
    rewrite /gfid Hgf.
    rewrite lerDl.
    apply: mulr_ge0; exact: sqrtr_ge0.
  }
  pose sigmaI : 'F[H]_(S :&: T) := dinvB%:C *: (\1 : 'F[H]_(S :&: T)).
  pose XI := castlf (eqST_max, eqST_max)
    ((GRing.inv dA)%:C *: ((\1 : 'F_(S :\: T)) \O sigmaI)).
  pose vI := log2 (dA * (gfid rhoS XI) ^+ 2).
  have PsigmaI : sigmaI \is psdlf.
  {
    rewrite /sigmaI.
    apply: psdlfZ.
    - by rewrite lecR invr_ge0.
    - by rewrite qualifE h2mx1; exact: psdmx1.
  }
  have HsigmaI_tr1 : \Tr sigmaI = 1.
  {
    have Hd_nonzero : dB != 0 by exact: lt0r_neq0 HdB_pos.
    rewrite /sigmaI linearZ /= /dinvB /dB /lftrace h2mx1 mxtrace1.
    rewrite -natrC -rmorphM /= mulrC (mulfV Hd_nonzero).
    exact: rmorph1.
  }
  have HsigmaI_den : sigmaI \is den1lf
    by apply/den1lfP; split.
  have HXI_eq : XI = dinv%:C *: (\1 : 'F[H]_S).
  {
    rewrite /XI /sigmaI sdotfZr !linearZ /=.
    have -> :
        castlf (eqST_max, eqST_max)
          ((\1 : 'F_(S :\: T)) \O (\1 : 'F[H]_(S :&: T))) =
        (\1 : 'F[H]_S).
    {
      rewrite sdotf11.
      exact: castlf1.
    }
    by rewrite scalerA /dinv -rmorphM.
  }
  have PXI : XI \is psdlf.
  {
    rewrite /XI linearZ /=.
    apply: psdlfZ; first by rewrite lecR invr_ge0 /dA ler0n.
    exact: Hlift_psd PsigmaI.
  }
  have Hrho_le_tI : rhoS <= t%:C *: (\1 : 'F[H]_S).
    exact: psdlf_le_tr_id_local.
  have HtI_le_I : t%:C *: (\1 : 'F[H]_S) <= (\1 : 'F[H]_S).
  {
    rewrite lefE.
    have -> :
        (\1 : 'F[H]_S) - t%:C *: (\1 : 'F[H]_S) =
        (1 - t)%:C *: (\1 : 'F[H]_S).
    {
      rewrite rmorphB scalerBl.
      by rewrite scale1r.
    }
    apply: psdlfZ.
    - by rewrite lecR subr_ge0.
    - by rewrite qualifE h2mx1; exact: psdmx1.
  }
  have Hrho_le_I : rhoS <= (\1 : 'F[H]_S).
    exact: le_trans Hrho_le_tI HtI_le_I.
  have Hscaled_le_XI : dinv%:C *: rhoS <= XI.
  {
    rewrite HXI_eq.
    apply: (@scale_lef_local S rhoS (\1 : 'F[H]_S) dinv).
    - exact: ltW Hdinv_pos.
    - exact: Hrho_le_I.
  }
  have Pscaled : (dinv%:C *: rhoS : 'F[H]_S) \is psdlf.
  {
    apply: psdlfZ.
    - rewrite lecR; exact: ltW Hdinv_pos.
    - exact: Prho.
  }
  have Hfid_scaled_le :
      fidelity rhoS (dinv%:C *: rhoS) <= fidelity rhoS XI.
  {
    rewrite /fidelity !h2mx_comp !sqrtH_h2mx.
    apply: fid_v_mono_r_psd_mx.
    - by move: Prho; rewrite qualifE.
    - by move: Pscaled; rewrite qualifE.
    - by move: PXI; rewrite qualifE.
    - by move: Hscaled_le_XI; rewrite lef_h2mx.
  }
  have Hfid_refl : fidelity rhoS rhoS = t.
  {
    have Prho_mx : h2mx rhoS \is psdmx.
    {
      by move: Prho; rewrite qualifE.
    }
    rewrite /fidelity !h2mx_comp !sqrtH_h2mx.
    have -> : sqrtmx (h2mx rhoS) *m sqrtmx (h2mx rhoS) = h2mx rhoS.
      by rewrite sqrtmxK.
    by rewrite (psdmx_trnorm Prho_mx) /t /lftrace.
  }
  have Hfid_scaled_eq :
      fidelity rhoS (dinv%:C *: rhoS) = Num.sqrt dinv * t.
  {
    have Htmp := @Hfid_scale S rhoS rhoS 1 dinv
      ler01 (ltW Hdinv_pos) Prho Prho.
    rewrite sqrtr1 mul1r Hfid_refl in Htmp.
    have -> : fidelity rhoS (dinv%:C *: rhoS) =
              fidelity ((1 : C) *: rhoS) (dinv%:C *: rhoS).
    {
      by rewrite scale1r.
    }
    exact: Htmp.
  }
  have Hsqrtd_t_le_fid : Num.sqrt dinv * t <= fidelity rhoS XI.
  {
    by rewrite -Hfid_scaled_eq.
  }
  have Hsqrtd_t_pos : 0 < Num.sqrt dinv * t.
  {
    apply: mulr_gt0.
    - by rewrite sqrtr_gt0.
    - exact: Ht_pos.
  }
  have HfidXI_pos : 0 < fidelity rhoS XI.
  {
    exact: lt_le_trans Hsqrtd_t_pos Hsqrtd_t_le_fid.
  }
  have HgfXI_pos : 0 < gfid rhoS XI.
  {
    exact: lt_le_trans HfidXI_pos (Hfid_le_gfid _ _ _ Prho PXI).
  }
  have HfeasI : E vI.
  {
    exists sigmaI; split.
    - exact: HsigmaI_den.
    - rewrite /vI elog2_gt0.
      + reflexivity.
      + apply: mulr_gt0; first exact: HdA_pos.
        by rewrite expr2; apply: mulr_gt0.
  }
  have HsupE : has_sup E := hmax_has_sup Prho Htr Ht_pos.
  pose c0 := dinv * t ^+ 2.
  pose c := dinvB * t ^+ 2.
  have Hc_pos : 0 < c.
  {
    rewrite /c.
    apply: mulr_gt0.
    - exact: HdinvB_pos.
    - by rewrite expr2; apply: mulr_gt0.
  }
  have Htarget_le_fsq : c0 <= (fidelity rhoS XI) ^+ 2.
  {
    have Hsqrtd_t_ge0 : 0 <= Num.sqrt dinv * t.
    {
      exact: ltW Hsqrtd_t_pos.
    }
    have Hfid_ge0_XI : 0 <= fidelity rhoS XI.
    {
      exact: Hfid_ge0.
    }
    have Htmp := lerXn2r 2 Hsqrtd_t_ge0 Hfid_ge0_XI Hsqrtd_t_le_fid.
    by move: Htmp; rewrite /c0 exprMn sqr_sqrtr ?(ltW Hdinv_pos).
  }
  have Htarget_le_gfsq_base : c0 <= (gfid rhoS XI) ^+ 2.
  {
    apply: le_trans Htarget_le_fsq _.
    apply: lerXn2r.
    - exact: Hfid_ge0.
    - rewrite /gfid.
      apply: gfid_ge0_mx.
      + by move: Prho; rewrite qualifE.
      + by move: PXI; rewrite qualifE.
    - exact: Hfid_le_gfid _ _ _ Prho PXI.
  }
  have Htarget_eq : c = dA * c0.
  {
    have HdA_neq0 : dA != 0 by exact: lt0r_neq0 HdA_pos.
    rewrite /c /c0 /dinv /dinvB.
    rewrite -!mulrA.
    rewrite [RHS]mulrA.
    by rewrite [dA * dA^-1]mulfV ?mul1r.
  }
  have Htarget_le_arg : c <= dA * (gfid rhoS XI) ^+ 2.
  {
    rewrite Htarget_eq.
    apply: ler_wpM2l; first exact: ltW HdA_pos.
    exact: Htarget_le_gfsq_base.
  }
  have Hdown : ([set log2 c] `<=` down E)%classic.
  {
    move=> y /= ->.
    rewrite /down /=.
    exists vI.
    split.
    - exact: HfeasI.
    - rewrite /vI.
      exact: (log2_le_pos Hc_pos Htarget_le_arg).
  }
  have Hnz : nonempty [set log2 c].
  {
    by exists (log2 c).
  }
  have := sup_le Hdown Hnz HsupE.
  by rewrite sup1 /hmax /c /dinvB /dB.
Qed.

(* smooth_hmax_lb *)
(* infra: no tex label — fundamental & reusable (mathcomp-style) *)
(* path: entropy:smooth_hmax_lb -> entropy:smooth_hmaxE_EFin -> *)
(*   bb84:bb84_secret *)
Lemma smooth_hmax_lb eps (rhoS tauS : 'F[H]_S) :
  rhoS \is psdlf ->
  @complex.Re R (\Tr rhoS) <= 1 ->
  0 <= eps < Num.sqrt (@complex.Re R (\Tr rhoS)) ->
  eps_ball eps rhoS tauS ->
  smooth_hmax T eps rhoS <= hmax T tauS.
Proof.
  move=> Prho Hrho_tr /andP [Heps Hepslt] Hball.
  have Hzero_psd : (0 : 'F[H]_S) \is psdlf.
    by rewrite psdlfE lexx.
  have Hzero_tr : @complex.Re R (\Tr (0 : 'F[H]_S)) <= 1.
    by rewrite linear0 raddf0 ler01.
  have Hpd_zero_eq :
      forall tau : 'F[H]_S,
        tau \is psdlf ->
        @complex.Re R (\Tr tau) <= 1 ->
        pur_dist (0 : 'F[H]_S) tau = Num.sqrt (@complex.Re R (\Tr tau)).
  {
    move=> tau Ptau Htau_tr.
    have Hzero_mx_psd : h2mx (0 : 'F[H]_S) \is psdmx.
      by move: Hzero_psd; rewrite qualifE.
    have Htau_mx_psd : h2mx tau \is psdmx.
      by move: Ptau; rewrite qualifE.
    have Htau_tr_real : \Tr tau \is Num.real.
      exact: ger0_real (psdlf_trlf Ptau).
    have Hgfid0 :
        gfid (0 : 'F[H]_S) tau =
        Num.sqrt (1 - @complex.Re R (\Tr tau)).
    {
      rewrite /gfid.
      rewrite (alt_gfid_gen Hzero_mx_psd Htau_mx_psd).
      have -> :
          @complex.Re R
            (trnorm (sqrtmx (h2mx (0 : 'F[H]_S)) *m sqrtmx (h2mx tau))) = 0.
      {
        by rewrite h2mx0 sqrtmx0 mul0mx trnorm0 raddf0.
      }
      have -> :
          @complex.Re R (1 - \tr (h2mx (0 : 'F[H]_S))) = 1.
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
        (gfid (0 : 'F[H]_S) tau)^2 = a.
    {
      rewrite Hgfid0.
      exact: sqr_sqrtr Ha_ge0.
    }
    by rewrite /a opprB addrCA subrr addr0.
  }
  pose alpha := (Num.sqrt (@complex.Re R (\Tr rhoS)) - eps) ^+ 2.
  have Hd_pos_nat : (0 < dim 'H[H]_(S :&: T))%N := dim_proper.
  pose dST : R := (dim 'H[H]_(S :&: T))%:R.
  have Hdinv_pos : 0 < GRing.inv dST.
  {
    rewrite /dST invr_gt0 ltr0n.
    exact: Hd_pos_nat.
  }
  have Hgap_pos : 0 < Num.sqrt (@complex.Re R (\Tr rhoS)) - eps.
  {
    by rewrite subr_gt0.
  }
  rewrite /smooth_hmax.
  have Hlb : has_lbound [set v : R | exists tau : 'F[H]_S,
    eps_ball eps rhoS tau /\ v = hmax T tau].
  {
    exists (log2 (((dim 'H[H]_(S :&: T))%:R)^-1 * alpha ^+ 2))
      => w [tau [Hb ->]].
    have Ptau : tau \is psdlf := eps_ball_psdlf Hb.
    have Htau_tr : @complex.Re R (\Tr tau) <= 1 := eps_ball_trlf Hb.
    have Htau_pd : pur_dist tau rhoS <= eps.
    {
      move: Hb.
      by rewrite /eps_ball => /andP [/andP [_ _] Hpd].
    }
    have Hrho_zero := Hpd_zero_eq rhoS Prho Hrho_tr.
    have Htau_zero := Hpd_zero_eq tau Ptau Htau_tr.
    have Hsqrt_le :
        Num.sqrt (@complex.Re R (\Tr rhoS)) <=
        Num.sqrt (@complex.Re R (\Tr tau)) + eps.
    {
      rewrite -Hrho_zero -Htau_zero.
      have Htri := @pd_metric_triangle R L H S
        (0 : 'F[H]_S) rhoS tau
        Hzero_psd Prho Ptau Hzero_tr Hrho_tr Htau_tr.
      have Hstep :
          pur_dist (0 : 'F[H]_S) tau + pur_dist tau rhoS <=
          pur_dist (0 : 'F[H]_S) tau + eps.
      {
        apply: lerD.
        - exact: lexx.
        - exact: Htau_pd.
      }
      exact: le_trans Htri Hstep.
    }
    have Hgap_le :
        Num.sqrt (@complex.Re R (\Tr rhoS)) - eps <=
        Num.sqrt (@complex.Re R (\Tr tau)).
    {
      move: Hsqrt_le.
      by rewrite lerBlDr addrC.
    }
    have Htau_sqrt_pos : 0 < Num.sqrt (@complex.Re R (\Tr tau)).
    {
      exact: lt_le_trans Hgap_pos Hgap_le.
    }
    have Htau_tr_ge0 : 0 <= @complex.Re R (\Tr tau).
    {
      have /= := psdlf_trlf Ptau.
      by rewrite lecE /= => /andP[].
    }
    have Htau_pos : 0 < @complex.Re R (\Tr tau).
    {
      by rewrite -sqrtr_gt0.
    }
    have Halpha_le_tau : alpha <= @complex.Re R (\Tr tau).
    {
      have Htmp := lerXn2r 2 (ltW Hgap_pos) (sqrtr_ge0 _) Hgap_le.
      rewrite /alpha (sqr_sqrtr Htau_tr_ge0) in Htmp.
      exact: Htmp.
    }
    have Halpha2_le_tau2 : alpha ^+ 2 <= (@complex.Re R (\Tr tau)) ^+ 2.
    {
      have Htmp := lerXn2r 2 (sqr_ge0 _) Htau_tr_ge0 Halpha_le_tau.
      exact: Htmp.
    }
    have Halpha_pos : 0 < alpha.
    {
      rewrite /alpha expr2.
      apply: mulr_gt0; exact: Hgap_pos.
    }
    have Hconst_le_tau :
        (((dim 'H[H]_(S :&: T))%:R)^-1 * alpha ^+ 2) <=
        (((dim 'H[H]_(S :&: T))%:R)^-1 * (@complex.Re R (\Tr tau)) ^+ 2).
    {
      rewrite (ler_pM2l Hdinv_pos).
      exact: Halpha2_le_tau2.
    }
    apply: (le_trans (log2_le_pos _ Hconst_le_tau)).
    - apply: mulr_gt0.
      + exact: Hdinv_pos.
      + rewrite expr2.
        apply: mulr_gt0; exact: Halpha_pos.
    - exact: hmax_lb_dim Ptau Htau_tr Htau_pos.
  }
  apply: ge_inf => //.
  by exists tauS.
Qed.

(* smooth_hmax_attained *)
(* infra: no tex label — fundamental & reusable (mathcomp-style) *)
(* path: entropy:smooth_hmax_attained -> entropy:smooth_hmaxE_EFin -> *)
(*   bb84:bb84_secret *)
Lemma smooth_hmax_attained eps (rhoS : 'F[H]_S) :
  rhoS \is psdlf ->
  @complex.Re R (\Tr rhoS) <= 1 ->
  0 <= eps < Num.sqrt (@complex.Re R (\Tr rhoS)) ->
  exists tauS : 'F[H]_S,
    eps_ball eps rhoS tauS /\
    smooth_hmax T eps rhoS = hmax T tauS.
Proof.
  move=> Prho Hrho_tr /andP [Heps Hepslt].
  have Hrho_gt0 : 0 < @complex.Re R (\Tr rhoS).
  {
    have Hsqrt_gt0 : 0 < Num.sqrt (@complex.Re R (\Tr rhoS)) :=
      le_lt_trans Heps Hepslt.
    have Hrho_ge0 : 0 <= @complex.Re R (\Tr rhoS).
    {
      have /= := psdlf_trlf Prho.
      by rewrite lecE /= => /andP[].
    }
    have Hsqrt_sq_pos : 0 < (Num.sqrt (@complex.Re R (\Tr rhoS))) ^+ 2.
    {
      rewrite expr2.
      by apply: mulr_gt0.
    }
    by rewrite (sqr_sqrtr Hrho_ge0) in Hsqrt_sq_pos.
  }
  pose Sset := [set v : R | exists tauS : 'F[H]_S,
    eps_ball eps rhoS tauS /\ v = hmax T tauS]%classic.
  pose h := smooth_hmax T eps rhoS.
  have Hlower_bound : has_lbound Sset.
  {
    exists h.
    move=> y [tauS [Htau_ball Hy]].
    rewrite Hy.
    apply: smooth_hmax_lb.
    - exact: Prho.
    - exact: Hrho_tr.
    - by apply/andP.
    - exact: Htau_ball.
  }
  have Hnz : nonempty Sset.
  {
    exists (hmax T rhoS).
    rewrite /Sset.
    exists rhoS.
    split.
    - exact: eps_ball_refl Prho Hrho_gt0 Hrho_tr Heps.
    - reflexivity.
  }
  have Hhas_inf : has_inf Sset.
  {
    split.
    - exact: Hnz.
    - exact: Hlower_bound.
  }
  have Hseq_exists :
      forall n : nat,
      exists tauS : 'F[H]_S,
        eps_ball eps rhoS tauS /\
        h <= hmax T tauS /\
        hmax T tauS < h + 1 / (n.+1)%:R.
  {
    move=> n.
    pose eta : R := 1 / (n.+1)%:R.
    have Hepsn_pos : 0 < eta.
    {
      by rewrite /eta divr_gt0 ?ltr0Sn.
    }
    have [y Hy Hylt] := inf_adherent Hepsn_pos Hhas_inf.
    case: Hy => tauS [HtauS Hy].
    exists tauS.
    split.
    - exact: HtauS.
    - split.
      + rewrite /h /smooth_hmax.
        apply: ge_inf => //.
        by exists tauS.
      + rewrite -Hy /h /smooth_hmax /eta.
        exact: Hylt.
  }
  have [f Hf] := choice Hseq_exists.
  pose n := dim 'H[H]_S.
  pose rhoM := h2mx rhoS : 'M[C]_n.
  pose fM (k : nat) := h2mx (f k) : 'M[C]_n.
  have Hn_pos : (0 < n)%N.
  {
    rewrite /n.
    exact: dim_proper.
  }
    pose BallM (tauM : 'M[C]_n) :=
      tauM \is denmx /\
      pur_dist (mx2h tauM : 'F[H]_S) rhoS <= eps.
    have HballM_compact : compact BallM.
    {
      have HDenM_closed :
          closed [set tau : 'M[C]_n |
            tau \is denmx].
      {
        have HDen_denE :
            [set tau : 'M[C]_n | tau \is denmx]%classic =
            [set tau : 'M[C]_n |
              tau \is psdmx /\ @complex.Re R (\tr tau) <= 1]%classic.
        {
          apply/funext=> tau /=.
          apply/propext; split.
          - move=> Htau_den.
            have /denmxP[Htau_psd Htau_trC] := Htau_den.
            split; first exact: Htau_psd.
            by move: Htau_trC; rewrite lecE /= => /andP [_].
          - move=> [Htau_psd Htau_tr].
            exact: denmx_psd_re_tr_le Htau_psd Htau_tr.
        }
        have HDenE :
            [set tau : 'M[C]_n |
              tau \is psdmx /\ @complex.Re R (\tr tau) <= 1]%classic =
          setI [set tau : 'M[C]_n | (0 : 'M[C]_n) <= tau]%classic
               [set tau : 'M[C]_n | \tr tau <= 1%:C]%classic.
      {
        apply/funext=> tau /=.
        apply/propext; split.
        - move=> [Htau_psd Htau_tr].
          split.
          + by rewrite le_lownerE subr0.
          + have Htau_tr_real : \tr tau \is Num.real.
            {
              exact: ger0_real (psdmx_trace Htau_psd).
            }
            have -> : \tr tau = (@complex.Re R (\tr tau))%:C.
            {
              exact: esym (RRe_real Htau_tr_real).
            }
            by rewrite lecR.
        - move=> [Htau_ge0 Htau_tr].
          have Htau_psd : tau \is psdmx.
          {
            by rewrite le_lownerE subr0 in Htau_ge0.
          }
          have Htau_tr_real : \tr tau \is Num.real.
          {
            exact: ger0_real (psdmx_trace Htau_psd).
          }
          split.
          + exact: Htau_psd.
          + move: Htau_tr.
            have -> : \tr tau = (@complex.Re R (\tr tau))%:C.
            {
              exact: esym (RRe_real Htau_tr_real).
            }
            by rewrite lecR.
        }
        rewrite HDen_denE HDenE.
        apply: closedI.
        - exact: psdmx_closed n.
        - exact: closed_letr _.
    }
    have HballM_closed : closed BallM.
    {
      rewrite /BallM closedE => tauM Htau_near.
      pose DenM (tau : 'M[C]_n) :=
        tau \is denmx.
      have Htau_den :
          tauM \is denmx.
      {
        have Htau_den_near :
            ~ (\forall X \near tauM, ~ DenM X).
        {
          move=> Hnear_not_den.
          apply: Htau_near.
          near=> X.
          move=> [HXden _].
          have HXnotden : ~ DenM X.
          {
            near: X.
            exact: Hnear_not_den.
          }
          exact: HXnotden HXden.
          Unshelve. end_near.
        }
        move: HDenM_closed.
        rewrite closedE.
        move=> /(_ tauM) Hclosed_tau.
          exact: Hclosed_tau Htau_den_near.
        }
        have /denmxP[Htau_psd Htau_trC] := Htau_den.
        have Htau_tr : @complex.Re R (\tr tauM) <= 1
          by move: Htau_trC; rewrite lecE /= => /andP [_].
      have Htau_psdlf : (mx2h tauM : 'F[H]_S) \is psdlf.
      {
        by rewrite qualifE /= mx2hK.
      }
      have Hrho_psdlf : (mx2h rhoM : 'F[H]_S) \is psdlf.
      {
        have -> : (mx2h rhoM : 'F[H]_S) = rhoS.
        {
          apply/h2mx_inj.
          by rewrite /rhoM mx2hK.
        }
        exact: Prho.
      }
      pose dtau := pur_dist (mx2h tauM : 'F[H]_S) rhoS.
        pose close_tau := (dtau <= eps).
        have [Htau_dist|Htau_far] := boolP close_tau.
        - exact: conj Htau_den Htau_dist.
      - move: Htau_far.
        rewrite /close_tau -ltNge => Htau_far.
        pose gap := dtau - eps.
        pose eta := gap / 2%:R.
        have Htwo_pos : 0 < (2%:R : R).
        {
          exact: ltr0Sn.
        }
        have Hgap_pos : 0 < gap.
        {
          rewrite /gap subr_gt0.
          exact: Htau_far.
        }
        have Heta_pos : 0 < eta.
        {
          rewrite /eta.
          exact: divr_gt0 Hgap_pos Htwo_pos.
        }
        have Heta_lt_gap : eta < gap.
        {
          rewrite /eta ltr_pdivrMr.
          - rewrite mulr_natr mulr2n ltrDl.
            exact: Hgap_pos.
          - exact: Htwo_pos.
        }
        have [c Hc_pos Hc_bound] :
            exists2 c : C, 0 < c &
              forall X : 'M[C]_n, trnorm X <= c * mx_norm X.
        {
          exact: cmnorm_bounded.
        }
        apply: False_ind.
        apply: Htau_near.
        apply/nbhs_ballP.
        (* Ball radius halved so trnorm + |Tr diff| <= eta^2 (   *)
        (* `pd_gtd_ub'` returns `\sqrt(2D̄)` with `D̄ = D + ½|Tr ρ - Tr τ|`.    *)
        (* Since `|Tr ρ - Tr τ| <= ||ρ-τ||₁` (`trnorm_ge_tr`), shrinking the    *)
        (* ball to `eta^2 / 2` keeps the contradiction tight.)                  *)
        exists ((eta ^+ 2 / 2%:R)%:C / c).
        + have Heta2_pos : 0 < (eta ^+ 2 / 2%:R)%:C :> C.
          {
            rewrite ltcR.
            apply: divr_gt0; last by apply: ltr0Sn.
            by rewrite expr2; apply: mulr_gt0.
          }
          exact: divr_gt0 Heta2_pos Hc_pos.
          + move=> sigma Hsigma_close.
            move=> [Hsigma_den Hsigma_dist].
            have /denmxP[Hsigma_psd Hsigma_trC] := Hsigma_den.
            have Hsigma_tr : @complex.Re R (\tr sigma) <= 1
              by move: Hsigma_trC; rewrite lecE /= => /andP [_].
          have Hsigma_psdlf : (mx2h sigma : 'F[H]_S) \is psdlf.
          {
            by rewrite qualifE /= mx2hK.
          }
            have Htrnorm_le : trnorm (tauM - sigma) <= (eta ^+ 2 / 2%:R)%:C.
            {
              have Hn0F : (n == 0)%N = false.
              {
                apply/negbTE.
                by rewrite -lt0n.
              }
              have H0nF : (0 == n)%N = false.
              {
                by rewrite eq_sym Hn0F.
              }
              have Hrad_pos : 0 < (eta ^+ 2 / 2%:R)%:C / c.
              {
                have Heta2_pos : 0 < (eta ^+ 2 / 2%:R)%:C :> C.
                {
                  rewrite ltcR.
                  apply: divr_gt0; last by apply: ltr0Sn.
                  by rewrite expr2; apply: mulr_gt0.
                }
                exact: divr_gt0 Heta2_pos Hc_pos.
              }
              have Hmx_lt :
                  mx_norm (tauM - sigma) < (eta ^+ 2 / 2%:R)%:C / c.
              {
                move: Hsigma_close.
                move/(@mxball_normE C n n tauM
                  ((eta ^+ 2 / 2%:R)%:C / c) sigma Hrad_pos).
                by rewrite /= ?Hn0F ?H0nF.
              }
              have Hmx_le :
                  mx_norm (tauM - sigma) <= (eta ^+ 2 / 2%:R)%:C / c.
                {
                  move: (ltW Hmx_lt).
                  by rewrite ?opprB ?mx_normN.
                }
                have Hscaled :
                  c * mx_norm (tauM - sigma) <= (eta ^+ 2 / 2%:R)%:C.
                {
                  rewrite mulrC -ler_pdivlMr; last exact: Hc_pos.
                  exact: Hmx_le.
                }
                  exact: (le_trans (Hc_bound (tauM - sigma)) Hscaled).
            }
          have Htrnorm_real : trnorm (tauM - sigma) \is Num.real.
          {
            exact: ger0_real (trnorm_ge0 _).
          }
          have Htrnorm_leR :
              trnormH ((mx2h tauM : 'F[H]_S) - mx2h sigma)
                <= eta ^+ 2 / 2%:R.
          {
            rewrite /trnormH.
            have Hh2mxB :
                h2mx ((mx2h tauM : 'F[H]_S) - mx2h sigma) = tauM - sigma.
            {
              apply: mx2h_inj.
              rewrite h2mxK.
              by rewrite raddfB.
            }
            rewrite Hh2mxB.
            move: Htrnorm_le.
            by rewrite -(RRe_real Htrnorm_real) lecR.
          }
          (* Bound `|Re(Tr(tauM-sigma))|_R ≤ trnorm (tauM-sigma)` via         *)
          (* `trnorm_ge_tr`, then chain in the same `eta^2/2` bound.          *)
          have Htr_diff_real :
              \tr tauM - \tr sigma \is Num.real.
          {
            apply: rpredB; apply: ger0_real;
              [exact: psdmx_trace Htau_psd | exact: psdmx_trace Hsigma_psd].
          }
          have Hre_tr_diff_le :
              `|@complex.Re R (\Tr (mx2h tauM : 'F[H]_S)) -
                @complex.Re R (\Tr (mx2h sigma : 'F[H]_S))|
              <= eta ^+ 2 / 2%:R.
          {
            rewrite /lftrace /= !mx2hK -raddfB/=.
            have Habs_C : `|\tr tauM - \tr sigma| <= trnorm (tauM - sigma).
            {
              rewrite -linearB/=.
              exact: trnorm_ge_tr.
            }
            (* For real `d = \tr tauM - \tr sigma`, `|d|_C = (|Re d|)%:C`. *)
            rewrite -(RRe_real Htr_diff_real) normc_real in Habs_C.
            have Hchain :
                (`|@complex.Re R (\tr tauM - \tr sigma)|)%:C
                  <= (eta ^+ 2 / 2%:R)%:C
              := le_trans Habs_C Htrnorm_le.
            by rewrite -lecR.
          }
          have Hsum_le :
              trnormH ((mx2h tauM : 'F[H]_S) - mx2h sigma) +
              `|@complex.Re R (\Tr (mx2h tauM : 'F[H]_S)) -
                @complex.Re R (\Tr (mx2h sigma : 'F[H]_S))|
              <= eta ^+ 2.
          {
            have Hsum : eta ^+ 2 / 2%:R + eta ^+ 2 / 2%:R = eta ^+ 2.
            { have H2 : (2%:R : R) != 0 by rewrite pnatr_eq0.
              rewrite [in RHS](_ : eta ^+ 2 = (eta ^+ 2 / 2%:R) * 2%:R);
                last by rewrite -mulrA mulVf// mulr1.
              by rewrite mulr_natr mulr2n. }
            by rewrite -Hsum; apply: lerD.
          }
          pose dtau_sigma :=
            pur_dist (mx2h tauM : 'F[H]_S) (mx2h sigma : 'F[H]_S).
          have Hpd_tau_sigma :
              dtau_sigma <= eta.
          {
            have Hpd_lf :
                pur_dist (mx2h tauM : 'F[H]_S) (mx2h sigma) <=
                Num.sqrt (trnormH
                  ((mx2h tauM : 'F[H]_S) - mx2h sigma) +
                  `|@complex.Re R (\Tr (mx2h tauM : 'F[H]_S)) -
                    @complex.Re R (\Tr (mx2h sigma : 'F[H]_S))|).
            {
              have Htau_trlf :
                  @complex.Re R (\Tr (mx2h tauM : 'F[H]_S)) <= 1
                by rewrite /lftrace mx2hK.
              have Hsigma_trlf :
                  @complex.Re R (\Tr (mx2h sigma : 'F[H]_S)) <= 1
                by rewrite /lftrace mx2hK.
              exact: pd_gtd_ub' Htau_psdlf Hsigma_psdlf
                Htau_trlf Hsigma_trlf.
            }
            rewrite /dtau_sigma.
            apply: (le_trans Hpd_lf).
            have Heta_sqrt : Num.sqrt (eta ^+ 2) = eta.
            {
              rewrite sqrtr_sqr.
              exact: ger0_norm (ltW Heta_pos).
            }
            rewrite -Heta_sqrt.
            exact: ler_wsqrtr Hsum_le.
          }
          have Htau_rho_le : dtau <= eps + eta.
          {
            have Htri :
                dtau <= dtau_sigma + pur_dist (mx2h sigma : 'F[H]_S) rhoS.
            {
              rewrite /dtau /dtau_sigma.
              have Htri0 :
                  pur_dist (mx2h tauM : 'F[H]_S) rhoS <=
                  pur_dist (mx2h tauM : 'F[H]_S) (mx2h sigma : 'F[H]_S) +
                  pur_dist (mx2h sigma : 'F[H]_S) rhoS.
              {
                have Htau_tr_lf :
                    @complex.Re R (\Tr (mx2h tauM : 'F[H]_S)) <= 1
                  by rewrite /lftrace /= mx2hK.
                have Hsigma_tr_lf :
                    @complex.Re R (\Tr (mx2h sigma : 'F[H]_S)) <= 1
                  by rewrite /lftrace /= mx2hK.
                exact: pd_metric_triangle Htau_psdlf Prho Hsigma_psdlf
                  Htau_tr_lf Hrho_tr Hsigma_tr_lf.
              }
              exact: Htri0.
            }
            have Hrhs :
                dtau_sigma + pur_dist (mx2h sigma : 'F[H]_S) rhoS <= eps + eta.
            {
              have -> : eps + eta = eta + eps.
              {
                exact: addrC eps eta.
              }
              exact: lerD Hpd_tau_sigma Hsigma_dist.
            }
            exact: le_trans Htri Hrhs.
          }
          have Heps_eta_lt : eps + eta < dtau.
          {
            move: Heta_lt_gap.
            by rewrite /gap ltrBrDl addrC.
          }
          have Hcontra := le_lt_trans Htau_rho_le Heps_eta_lt.
          by rewrite ltxx in Hcontra.
    }
      have HballM_sub :
          (BallM `<=` [set tau : 'M[C]_n | mx_norm tau <= 1])%classic.
      {
        move=> tauM [Htau_den _].
        have /denmxP[Htau_psd Htau_trC] := Htau_den.
        have Htau_tr : @complex.Re R (\tr tauM) <= 1
          by move: Htau_trC; rewrite lecE /= => /andP [_].
      have Hmx_i2 : `|tauM| <= i2norm tauM.
      {
        have Hi2_ge0 : 0 <= i2norm tauM.
        {
          exact: i2norm_ge0.
        }
        have -> : i2norm tauM = (NngNum Hi2_ge0)%:num.
        {
          reflexivity.
        }
        rewrite -mx_normEV /mx_norm num_le.
        apply/bigmax_leP => /=.
        split.
        - rewrite -num_le /=.
          exact: Hi2_ge0.
        - move=> ij _.
          move: (i2norm_elem tauM ij.1 ij.2).
          rewrite -num_le /= => Hij_le.
          exact: Hij_le.
      }
      apply: (le_trans Hmx_i2).
      apply: (le_trans (i2norm_trnorm tauM)).
      have Htau_tr_real : \tr tauM \is Num.real.
      {
        exact: ger0_real (psdmx_trace Htau_psd).
        }
        rewrite (psdmx_trnorm Htau_psd).
        exact: Htau_trC.
    }
    have Hcube_compact :
        compact [set tau : 'M[C]_n | mx_norm tau <= 1].
    {
      exact: compact_cmnorm_le.
    }
    apply: (subclosed_compact HballM_closed Hcube_compact _).
    exact: HballM_sub.
  }
  have Hbound_f : forall k, mx_norm (fM k) <= 1.
  {
    move=> k.
    have Hfk_ball : BallM (fM k).
    {
      move: (Hf k).1 => Hball_fk.
      have Hfk_psd : (f k) \is psdlf := eps_ball_psdlf Hball_fk.
      have Hfk_tr : @complex.Re R (\Tr (f k)) <= 1 := eps_ball_trlf Hball_fk.
      have Hfk_pd : pur_dist (f k) rhoS <= eps.
      {
        move: Hball_fk.
        by rewrite /eps_ball => /andP [/andP [_ _] Hpd].
        }
        split.
        - apply: denmx_psd_re_tr_le.
          + by move: Hfk_psd; rewrite qualifE.
          + exact: Hfk_tr.
        - rewrite /fM /= h2mxK.
          exact: Hfk_pd.
    }
      have HballM_sub :
          (BallM `<=` [set tau : 'M[C]_n | mx_norm tau <= 1])%classic.
      {
        move=> tauM [Htau_den _].
        have /denmxP[Htau_psd Htau_trC] := Htau_den.
      have Hmx_i2 : `|tauM| <= i2norm tauM.
      {
        have Hi2_ge0 : 0 <= i2norm tauM by exact: i2norm_ge0.
        have -> : i2norm tauM = (NngNum Hi2_ge0)%:num by reflexivity.
        rewrite -mx_normEV /mx_norm num_le.
        apply/bigmax_leP => /=.
        split.
        - by rewrite -num_le /=.
        - move=> ij _.
          move: (i2norm_elem tauM ij.1 ij.2).
          by rewrite -num_le /=.
      }
      apply: (le_trans Hmx_i2).
      apply: (le_trans (i2norm_trnorm tauM)).
      have Htau_tr_real : \tr tauM \is Num.real.
      {
        exact: ger0_real (psdmx_trace Htau_psd).
        }
        rewrite (psdmx_trnorm Htau_psd).
        exact: Htau_trC.
      }
    exact: HballM_sub Hfk_ball.
  }
  have [g [Hg Hcvg_f]] := ExtNumTopology.Bolzano_Weierstrass Hbound_f.
  pose fgM (k : nat) := fM (g k).
  pose fgS (k : nat) := f (g k).
  pose tauM0 := limn fgM.
  pose tauS0 := mx2h tauM0 : 'F[H]_S.
  have Hnear_ball : \forall k \near \oo%classic, BallM (fgM k).
  {
    near=> k.
    move: (Hf (g k)).1 => Hball_fk.
    have Hfk_pd : pur_dist (fgS k) rhoS <= eps.
    {
      move: Hball_fk.
      by rewrite /eps_ball => /andP [/andP [_ _] Hpd].
      }
      split.
      - apply: denmx_psd_re_tr_le.
        + by move: (eps_ball_psdlf Hball_fk); rewrite qualifE.
        + by move: (eps_ball_trlf Hball_fk).
      - rewrite /fgM /fM /= h2mxK.
        exact: Hfk_pd.
    Unshelve. end_near.
  }
  have HtauM0_ball : BallM tauM0.
  {
    have HballM_closed : closed BallM.
    {
      apply: compact_closed.
      - exact: ExtNumTopology.mxhausdorff.
      - exact: HballM_compact.
    }
    exact: (@closed_cvg _ _ _ _ fgM BallM
      HballM_closed Hnear_ball tauM0 Hcvg_f).
  }
    have HtauS0_ball : eps_ball eps rhoS tauS0.
    {
      move: HtauM0_ball => [Htau0_den Htau0_pd].
      have /denmxP[Htau0_psd Htau0_trC] := Htau0_den.
      have Htau0_tr : @complex.Re R (\tr tauM0) <= 1
        by move: Htau0_trC; rewrite lecE /= => /andP [_].
      have HtauS0_psd : tauS0 \is psdlf
        by rewrite /tauS0 qualifE /= mx2hK.
      have HtauS0_tr : @complex.Re R (\Tr tauS0) <= 1
        by rewrite /tauS0 /lftrace /= mx2hK.
      have HtauS0_pos : 0 < @complex.Re R (\Tr tauS0).
      {
        have Hsmall : 0 <= eps < Num.sqrt (@complex.Re R (\Tr rhoS))
          by apply/andP; split.
        have Holdball :
            ((tauS0 \is psdlf) &&
              (@complex.Re R (\Tr tauS0) <= 1)) &&
            (pur_dist tauS0 rhoS <= eps).
        {
          rewrite HtauS0_psd HtauS0_tr.
          by rewrite /tauS0.
        }
        exact: (eps_ball_trace_pos_from_small Prho Hrho_tr Hsmall Holdball).
      }
      rewrite /eps_ball.
    apply/andP; split.
    - apply/andP; split.
      + apply/andP; split.
        * exact: HtauS0_psd.
        * exact: HtauS0_pos.
      + exact: HtauS0_tr.
    - exact: Htau0_pd.
  }
  have Hzero_psd : (0 : 'F[H]_S) \is psdlf.
  {
    by rewrite qualifE h2mx0 psdmx0.
  }
  have Hzero_tr : @complex.Re R (\Tr (0 : 'F[H]_S)) <= 1.
    by rewrite linear0 raddf0 ler01.
  have Hpd_zero_eq :
      forall tau : 'F[H]_S,
        tau \is psdlf ->
        @complex.Re R (\Tr tau) <= 1 ->
        pur_dist (0 : 'F[H]_S) tau = Num.sqrt (@complex.Re R (\Tr tau)).
  {
    move=> tau Ptau Htau_tr.
    have Hzero_mx_psd : h2mx (0 : 'F[H]_S) \is psdmx.
    {
      by move: Hzero_psd; rewrite qualifE.
    }
    have Htau_mx_psd : h2mx tau \is psdmx.
    {
      by move: Ptau; rewrite qualifE.
    }
    have Hgfid0 :
        gfid (0 : 'F[H]_S) tau =
        Num.sqrt (1 - @complex.Re R (\Tr tau)).
    {
      rewrite /gfid.
      rewrite (alt_gfid_gen Hzero_mx_psd Htau_mx_psd).
      have -> :
          @complex.Re R
            (trnorm (sqrtmx (h2mx (0 : 'F[H]_S)) *m sqrtmx (h2mx tau))) = 0.
      {
        by rewrite h2mx0 sqrtmx0 mul0mx trnorm0 raddf0.
      }
      have -> :
          @complex.Re R (1 - \tr (h2mx (0 : 'F[H]_S))) = 1.
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
        (gfid (0 : 'F[H]_S) tau)^2 = a.
    {
      rewrite Hgfid0.
      exact: sqr_sqrtr Ha_ge0.
    }
    by rewrite /a opprB addrCA subrr addr0.
  }
  have Hgap_pos : 0 < Num.sqrt (@complex.Re R (\Tr rhoS)) - eps.
  {
    by rewrite subr_gt0.
  }
  have Hball_trace_pos :
      forall tau : 'F[H]_S, eps_ball eps rhoS tau ->
        0 < @complex.Re R (\Tr tau).
  {
    move=> tau Hb.
    have Ptau : tau \is psdlf := eps_ball_psdlf Hb.
    have Htau_tr : @complex.Re R (\Tr tau) <= 1 := eps_ball_trlf Hb.
    have Htau_pd : pur_dist tau rhoS <= eps.
    {
      move: Hb.
      by rewrite /eps_ball => /andP [/andP [_ _] Hpd].
    }
    have Hrho_zero := Hpd_zero_eq rhoS Prho Hrho_tr.
    have Htau_zero := Hpd_zero_eq tau Ptau Htau_tr.
    have Hsqrt_le :
        Num.sqrt (@complex.Re R (\Tr rhoS)) <=
        Num.sqrt (@complex.Re R (\Tr tau)) + eps.
    {
      rewrite -Hrho_zero -Htau_zero.
      have Htri := @pd_metric_triangle R L H S
        (0 : 'F[H]_S) rhoS tau
        Hzero_psd Prho Ptau Hzero_tr Hrho_tr Htau_tr.
      have Hstep :
          pur_dist (0 : 'F[H]_S) tau + pur_dist tau rhoS <=
          pur_dist (0 : 'F[H]_S) tau + eps.
      {
        apply: lerD.
        - exact: lexx.
        - exact: Htau_pd.
      }
      exact: le_trans Htri Hstep.
    }
    have Hgap_le :
        Num.sqrt (@complex.Re R (\Tr rhoS)) - eps <=
        Num.sqrt (@complex.Re R (\Tr tau)).
    {
      move: Hsqrt_le.
      by rewrite lerBlDr addrC.
    }
    have Htau_sqrt_pos : 0 < Num.sqrt (@complex.Re R (\Tr tau)).
    {
      exact: lt_le_trans Hgap_pos Hgap_le.
    }
    by rewrite -sqrtr_gt0.
  }
  have Hhmax_feasible_has_sup :
      forall tauS : 'F[H]_S,
        tauS \is psdlf ->
        @complex.Re R (\Tr tauS) <= 1 ->
        0 < @complex.Re R (\Tr tauS) ->
        has_sup [set v : R | hmax_feasible T tauS v].
  {
    move=> tauS Ptau Htau_tr Htau_pos.
    exact: hmax_has_sup Ptau Htau_tr Htau_pos.
  }
  have HfgM_psd : forall k, fgM k \is psdmx.
  {
    move=> k.
    move: (Hf (g k)).1.
    by move/eps_ball_psdlf; rewrite /fgS /fM /fgM /= qualifE.
  }
  have HfgM_tr : forall k, @complex.Re R (\tr (fgM k)) <= 1.
  {
    move=> k.
    move: (Hf (g k)).1.
    by move/eps_ball_trlf; rewrite /fgS /fM /fgM /= /lftrace.
  }
  have Hi2norm_sqrt_psd_le1 :
      forall M : 'M[C]_n,
        M \is psdmx ->
        @complex.Re R (\tr M) <= 1 ->
        i2norm (sqrtmx M) <= 1.
  {
    move=> M HM Htr.
    pose m := n.-1.
    have Em : n = m.+1.
    {
      by rewrite /m prednK.
    }
    pose M0 : 'M[C]_(m.+1) := castmx_sq Em M.
    have HM0 : M0 \is psdmx.
    {
      rewrite /M0.
      exact: (@castmx_sq_psdmx R _ _ Em M HM).
    }
    have Htr0 : @complex.Re R (\tr M0) <= 1.
    {
      rewrite /M0 (@mxtrace_castmx_sq R _ _ Em M).
      exact: Htr.
    }
    have HS0_herm : (sqrtmx M0)^*t = sqrtmx M0.
    {
      have /hermmxP HS0 := sqrtmx_herm (psdmx_herm HM0).
      by rewrite -HS0.
    }
    have HS0_sq : sqrtmx M0 *m sqrtmx M0 = M0.
    {
      exact: sqrtmxK HM0.
    }
    have HMleI : M0 <= 1%:M.
    {
      have HMtr_real : \tr M0 \is Num.real.
      {
        exact: ger0_real (psdmx_trace HM0).
      }
      have HMtr_le1 : \tr M0 <= 1%:C.
      {
        move: Htr0.
        by rewrite -(RRe_real HMtr_real) lecR.
      }
      have HMleTr : M0 <= (\tr M0)%:M.
      {
        exact: lemx_psd_ub HM0.
      }
      have HMtr_leI : (\tr M0)%:M <= (1%:M : 'M[C]_(m.+1)).
      {
        apply: scalemx_le.
        exact: HMtr_le1.
      }
      exact: le_trans HMleTr HMtr_leI.
    }
    have [v Hv_norm Hv_eq] := i2norm_existsr (sqrtmx M0) 0.
    have Hsq_le : (l2norm (sqrtmx M0 *m v)) ^+ 2 <= 1.
    {
      move: HMleI.
      rewrite le_lownerE => /psdmx_dot/(_ v).
      rewrite nnegrE mulmxBr mulmxBl linearB/= subr_ge0.
      rewrite mulmx1.
      have -> :
          v^*t *m M0 *m v =
          (sqrtmx M0 *m v)^*t *m (sqrtmx M0 *m v).
      {
        symmetry.
        rewrite adjmxM HS0_herm -mulmxA.
        have -> : sqrtmx M0 *m (sqrtmx M0 *m v) = M0 *m v.
        {
          rewrite [sqrtmx M0 *m (sqrtmx M0 *m v)]mulmxA.
          by rewrite HS0_sq.
        }
        by rewrite mulmxA.
      }
      rewrite !dotV_l2norm Hv_norm expr1n.
      done.
    }
    have Hres : i2norm (sqrtmx M0) <= 1.
    {
      have Hone_sq : (1 : C) ^+ 2 = 1 by rewrite expr2 mul1r.
      have Hsq_le1 : (l2norm (sqrtmx M0 *m v)) ^+ 2 <= 1 ^+ 2.
      {
        rewrite Hone_sq.
        exact: Hsq_le.
      }
      rewrite -Hv_eq.
      rewrite -(ler_pXn2r (n := 2)) // ?nnegrE // ?mulr_ge0 //.
    }
    have Hi2_eq : i2norm (sqrtmx M0) = i2norm (sqrtmx M).
    {
      clear HM Htr HM0 Htr0 HS0_herm HS0_sq HMleI v Hv_norm Hv_eq Hsq_le Hres.
      rewrite /M0 /castmx_sq.
      clear M0.
      case: _ / Em M => M /=.
      by rewrite castmx_id.
    }
    by rewrite Hi2_eq in Hres.
  }
  have Htrnorm_sqrt_psd_le :
      forall M : 'M[C]_n,
        M \is psdmx ->
        @complex.Re R (\tr M) <= 1 ->
        trnorm (sqrtmx M) <= n%:R.
  {
    move=> M HM Htr.
    have Hsqrt_psd : sqrtmx M \is psdmx.
    {
      exact: sqrtmx_psd HM.
    }
    have Hi2 := Hi2norm_sqrt_psd_le1 M HM Htr.
    have Hle : trnorm (sqrtmx M) = trnorm (sqrtmx M *m 1%:M).
    {
      by rewrite mulmx1.
    }
    rewrite Hle.
    apply: (le_trans (trnormMr _ _)).
    rewrite trnorm1.
    rewrite -[X in _ <= X]mul1r.
    apply: ler_pM.
    - exact: i2norm_ge0.
    - exact: ler0n.
    - exact: Hi2.
    - exact: lexx.
  }
  have Hcvg_sqrt_fg :
      ((fun k => sqrtmx (fgM k)) @ \oo --> sqrtmx tauM0)%classic.
    {
      have HtauM0_psd_mx : tauM0 \is psdmx.
      {
        exact: denmx_psd HtauM0_ball.1.
      }
      have HtauM0_tr_mx : @complex.Re R (\tr tauM0) <= 1.
      {
        have /denmxP[_ HtrC] := HtauM0_ball.1.
        by move: HtrC; rewrite lecE /= => /andP [_].
      }
    have Htmp : exists2 c : C, 0 < c &
      forall x : 'M[C]_n, mx_norm x <= c * trnorm x.
    {
      exact: cmnorm_bounded.
    }
    move: Htmp => [Cbound HCbound_pos HCbound_ineq].
    set Mbound := Cbound * n%:R.
    have Hsqrt_bound : forall i, mx_norm (sqrtmx (fgM i)) <= Mbound.
    {
      move=> i.
      have Hle := HCbound_ineq (sqrtmx (fgM i)).
      have Htr := Htrnorm_sqrt_psd_le (fgM i) (HfgM_psd i) (HfgM_tr i).
      apply: (le_trans Hle).
      rewrite /Mbound.
      apply: ler_pM.
      - exact: ltW HCbound_pos.
      - exact: trnorm_ge0.
      - exact: lexx.
      - exact: Htr.
    }
    apply/(@cmxcvgn_subseqP_cvgn R n n _ _ Mbound).
    - exact: Hsqrt_bound.
    - move=> hs Hh_inc Hh_cvg.
      set T0 := limn ((fun i => sqrtmx (fgM i)) \o hs).
      have HT0_psd : T0 \is psdmx.
      {
        have Hclosed_psd : closed [set X : 'M[C]_n | X \is psdmx]%classic.
        {
          have -> :
              [set X : 'M[C]_n | X \is psdmx]%classic =
              [set X : 'M[C]_n | (0 : 'M[C]_n) <= X]%classic.
          {
            apply/funext=> X /=.
            apply/propext; split.
            - move=> HX.
              by rewrite le_lownerE subr0.
            - move=> HX.
              by rewrite le_lownerE subr0 in HX.
          }
          exact: psdmx_closed n.
        }
        have Hnear :
            \forall x \near \oo%classic,
              [set X : 'M[C]_n | X \is psdmx]%classic
                (sqrtmx (fgM (hs x))).
        {
          apply: nearW => i /=.
          exact: sqrtmx_psd (HfgM_psd (hs i)).
        }
        exact: (@closed_cvg _ _ _ eventually_filter
          (fun i => sqrtmx (fgM (hs i)))
          [set X : 'M[C]_n | X \is psdmx]%classic
          Hclosed_psd Hnear T0 Hh_cvg).
      }
      have Hfgh_cvg : ((fgM \o hs) @ \oo --> tauM0)%classic.
      {
        have := (cmxcvgn_subseqP fgM tauM0).1 Hcvg_f hs Hh_inc.
        exact.
      }
      have HT0_sq : T0 *m T0 = tauM0.
      {
        set f0 := fun k => sqrtmx (fgM (hs k)).
        have Hf0_sq : forall k, f0 k *m f0 k = fgM (hs k).
        {
          move=> k /=.
          exact: sqrtmxK (HfgM_psd (hs k)).
        }
        apply/matrixP => i j.
        rewrite !mxE.
        have Hlhs_cvg :
            ((fun n0 => \sum_l (f0 n0 i l * f0 n0 l j)) @ \oo -->
            \sum_l (T0 i l * T0 l j))%classic.
        {
          have Hentry :
              forall l : 'I_n,
                ((fun n0 => f0 n0 i l * f0 n0 l j) @ \oo -->
                T0 i l * T0 l j)%classic.
          {
            move=> l.
            apply: ccvgnM.
            - have Hsc : scalar (fun M : 'M[C]_n => M i l).
              {
                move=> c A B.
                by rewrite !mxE.
              }
              exact: (cmxcvgn_sfun Hsc Hh_cvg).
            - have Hsc : scalar (fun M : 'M[C]_n => M l j).
              {
                move=> c A B.
                by rewrite !mxE.
              }
              exact: (cmxcvgn_sfun Hsc Hh_cvg).
          }
          suff Haux :
              forall s : seq 'I_n,
                ((fun n0 => \sum_(l <- s) (f0 n0 i l * f0 n0 l j)) @ \oo -->
                \sum_(l <- s) (T0 i l * T0 l j))%classic.
          {
            exact: Haux.
          }
          elim=> [|l0 s IH].
          - rewrite big_nil.
            under eq_cvg do rewrite big_nil.
            exact: (cvg_cst (0 : C)).
          - rewrite big_cons.
            under eq_cvg do rewrite big_cons.
            apply: cvgD.
            + exact: Hentry l0.
            + exact: IH.
        }
        have Hrhs_cvg :
            ((fun k => fgM (hs k) i j) @ \oo --> tauM0 i j)%classic.
        {
          have Hsc : scalar (fun M : 'M[C]_n => M i j).
          {
            move=> c A B.
            by rewrite !mxE.
          }
          exact: (cmxcvgn_sfun Hsc Hfgh_cvg).
        }
        rewrite /f0 in Hlhs_cvg.
        have Hrhs_cvg' :
            ((fun k => \sum_l (sqrtmx (fgM (hs k)) i l * sqrtmx (fgM (hs k)) l j))
              @ \oo --> tauM0 i j)%classic.
        {
          have -> :
              (fun k => \sum_l (sqrtmx (fgM (hs k)) i l * sqrtmx (fgM (hs k)) l j)) =
              (fun k => fgM (hs k) i j).
          {
            apply: funext => k.
            move: (congr1 (fun M : 'M[C]_n => M i j) (Hf0_sq k)).
            by rewrite !mxE.
          }
          exact: Hrhs_cvg.
        }
        move/ccvgn_limnE: Hlhs_cvg => [Hlhs_lim _].
        move/ccvgn_limnE: Hrhs_cvg' => [Hrhs_lim _].
        by rewrite -Hlhs_lim -Hrhs_lim.
      }
      have HT0_eq : T0 = sqrtmx tauM0.
      {
        by rewrite -HT0_sq sqrtmx_psd_square.
      }
      by rewrite -HT0_eq.
  }
  have Htrace_fg_cvgC :
      ((fun k => \tr (fgM k)) @ \oo --> \tr tauM0)%classic.
  {
    exact: cmxcvgn_trace Hcvg_f.
  }
  have Htrace_fg_cvg := Re_cvgn_realV Htrace_fg_cvgC.
  have Hnear_from_witness :
      forall (y v : R) (sigmaB : 'F[H]_(S :&: T)),
        sigmaB \is den1lf ->
        let sigmaX :=
          castlf (eqST_max, eqST_max)
            ((((dim 'H[H]_(S :\: T))%:R^-1)%:C *:
              ((\1 : 'F_(S :\: T)) \O sigmaB))) in
        elog2 ((dim 'H[H]_(S :\: T))%:R *
          (gfid tauS0 sigmaX) ^+ 2) = v%:E ->
        y < v ->
        \forall k \near \oo%classic, y < hmax T (fgS k).
  {
    move=> y v sigmaB PsigmaB_den sigmaX Hve Hy.
    pose dA : R := (dim 'H[H]_(S :\: T))%:R.
    have HdA_pos : 0 < dA by rewrite /dA ltr0n dim_proper.
    have PsigmaB : sigmaB \is psdlf := den1lf_psd PsigmaB_den.
    have HtauS0_psd : tauS0 \is psdlf.
    {
      exact: eps_ball_psdlf HtauS0_ball.
    }
    have HtauS0_tr : @complex.Re R (\Tr tauS0) <= 1.
    {
      exact: eps_ball_trlf HtauS0_ball.
    }
    have HtauM0_psd : tauM0 \is psdmx.
    {
      move: HtauS0_psd.
      by rewrite /tauS0 qualifE /= mx2hK.
    }
    have disST : [disjoint S :\: T & S :&: T].
    {
      apply/disjointP=> x.
      rewrite !inE.
      by case: (x \in S); case: (x \in T).
    }
    have HsigmaX_psd : sigmaX \is psdlf.
    {
      have Hten :
          ((\1 : 'F[H]_(S :\: T)) \O sigmaB :
            'F[H]_((S :\: T) :|: (S :&: T))) =
          ((\1 : 'F[H]_(S :\: T)) \⊗ sigmaB).
      {
        by apply: to_Fnd_inj; rewrite (sdotFT _ _ disST) to_Fnd_tenE.
      }
      rewrite /sigmaX castlf_psdlfE.
      apply: psdlfZ; first by rewrite lecR invr_ge0 /dA ler0n.
      rewrite Hten psdlfE.
      apply: tenf_ge0; first exact: disST.
      - exact: lef01.
      - by move: PsigmaB; rewrite psdlfE.
    }
    have HsigmaX_mx : h2mx sigmaX \is psdmx.
    {
      by move: HsigmaX_psd; rewrite qualifE.
    }
    have Harg0_pos :
        0 < dA * (gfid tauS0 sigmaX) ^+ 2.
    {
      case: (ltP 0 (dA * (gfid tauS0 sigmaX) ^+ 2))
          => // Harg0_le0.
      move: Hve.
      rewrite (elog2_le0 Harg0_le0).
      by discriminate.
    }
    have Hgfid0_sq_pos : 0 < (gfid tauS0 sigmaX) ^+ 2.
    {
      rewrite -(ltr_pM2l HdA_pos) mulr0.
      exact: Harg0_pos.
    }
    have Hv_eq : v = log2 (dA * (gfid tauS0 sigmaX) ^+ 2).
    {
      move: Hve.
      rewrite (elog2_gt0 Harg0_pos).
      by case.
    }
    pose sigsqrt := sqrtmx (h2mx sigmaX).
    pose fid_fun := fun k : nat =>
      @complex.Re R (\tr| sqrtmx (fgM k) *m sigsqrt |).
    pose fid_lim := @complex.Re R (\tr| sqrtmx tauM0 *m sigsqrt |).
    pose trarg_fun := fun k : nat => 1 - @complex.Re R (\tr (fgM k)).
    pose trarg_lim := 1 - @complex.Re R (\tr tauM0).
    pose sigcorr := Num.sqrt (@complex.Re R (1 - \tr (h2mx sigmaX))).
    pose gfid_fun := fun k : nat =>
      fid_fun k + Num.sqrt (trarg_fun k) * sigcorr.
    pose gfid_lim := fid_lim + Num.sqrt trarg_lim * sigcorr.
    have Hmul_sig_linear :
        linear (fun X : 'M[C]_n => X *m sigsqrt).
    {
      move=> c X Y.
      by rewrite mulmxDl scalemxAl.
    }
    have Hcvg_mul_sig :
        ((fun k => sqrtmx (fgM k) *m sigsqrt) @ \oo --> sqrtmx tauM0 *m sigsqrt)%classic.
    {
      exact: (@cmxcvgn_lfun R n n n n
        (fun X : 'M[C]_n => X *m sigsqrt)
        (fun k => sqrtmx (fgM k)) (sqrtmx tauM0)
        Hmul_sig_linear Hcvg_sqrt_fg).
    }
    have Hcvg_fidC :
        ((fun k => \tr| sqrtmx (fgM k) *m sigsqrt |) @ \oo
          --> \tr| sqrtmx tauM0 *m sigsqrt |)%classic.
    {
      exact: cmxcvgn_trnorm Hcvg_mul_sig.
    }
    have Hcvg_fidR :
        ((fun k : nat => (fid_fun k : R^o)) @ \oo --> (fid_lim : R^o))%classic.
    {
      exact: @Re_cvgn_realV R
        (fun k => \tr| sqrtmx (fgM k) *m sigsqrt |)
        (\tr| sqrtmx tauM0 *m sigsqrt |) Hcvg_fidC.
    }
    have Hcvg_one :
        ((fun _ : nat => ((1 : R) : R^o)) @ \oo --> ((1 : R) : R^o))%classic.
    {
      exact: (@cvg_cst [the topologicalType of R^o] (1 : R) nat eventually _).
    }
    have Htrarg_cvg0 :
        ((fun k : nat => (trarg_fun k : R^o)) @ \oo --> (trarg_lim : R^o))%classic.
    {
      rewrite /trarg_fun /trarg_lim.
      exact: cvgB Hcvg_one Htrace_fg_cvg.
    }
    have Hcvg_sqrt_tr :
        ((fun k : nat => (Num.sqrt (trarg_fun k) : R^o))
          @ \oo --> (Num.sqrt trarg_lim : R^o))%classic.
    {
      apply: continuous_cvg Htrarg_cvg0.
      exact: sqrt_continuous.
    }
    have Hcvg_sigcorr :
        ((fun _ : nat => (sigcorr : R^o)) @ \oo --> (sigcorr : R^o))%classic.
    {
      exact: (@cvg_cst [the topologicalType of R^o] sigcorr nat eventually _).
    }
    have Hcvg_corr :
        ((fun k : nat =>
            (Num.sqrt (trarg_fun k) * sigcorr : R^o))
          @ \oo --> (Num.sqrt trarg_lim * sigcorr : R^o))%classic.
    {
      exact: cvgM Hcvg_sqrt_tr Hcvg_sigcorr.
    }
    have Hcvg_gfid :
        ((fun k : nat => (gfid_fun k : R^o)) @ \oo --> (gfid_lim : R^o))%classic.
    {
      rewrite /gfid_fun /gfid_lim.
      exact: cvgD Hcvg_fidR Hcvg_corr.
    }
    have Hlim_eq : gfid_lim = gfid tauS0 sigmaX.
    {
      have Hgf := alt_gfid_gen (rho:=tauM0) (tau:=h2mx sigmaX)
        HtauM0_psd HsigmaX_mx.
      have Hgf' : gfid tauS0 sigmaX = gfid_lim.
      {
        rewrite /gfid_lim /fid_lim /trarg_lim /sigcorr /gfid /tauS0 /sigsqrt mx2hK.
        have -> : 1 - @complex.Re R (\tr tauM0) = @complex.Re R (1 - \tr tauM0).
        {
          by rewrite raddfB /=.
        }
        exact: Hgf.
      }
      by rewrite Hgf'.
    }
    have Hfun_eq :
        forall k, gfid_fun k = gfid (fgS k) sigmaX.
    {
      move=> k.
      have Hgf := alt_gfid_gen (rho:=fgM k) (tau:=h2mx sigmaX)
        (HfgM_psd k) HsigmaX_mx.
      have Hgf' : gfid (fgS k) sigmaX = gfid_fun k.
      {
        rewrite /gfid_fun /fid_fun /trarg_fun /sigcorr /gfid /fgS /fgM /fM /sigsqrt /=.
        have -> : 1 - @complex.Re R (\tr (fgM k)) = @complex.Re R (1 - \tr (fgM k)).
        {
          by rewrite raddfB /=.
        }
        exact: Hgf.
      }
      by rewrite Hgf'.
    }
    have Hgfid_lim_ge0 : 0 <= gfid_lim.
    {
      rewrite Hlim_eq.
      rewrite /gfid.
      apply: gfid_ge0_mx.
      - by move: HtauS0_psd; rewrite qualifE.
      - by move: HsigmaX_psd; rewrite qualifE.
    }
    have Htwo_pow_pos : 0 < 2 `^ y.
    {
      by rewrite powR_gt0.
    }
    have Hlimit_gt : 2 `^ y < dA * gfid_lim ^+ 2.
    {
      have Hlog_gt : ln (2 `^ y) < ln (dA * gfid_lim ^+ 2).
      {
        have Hln2_unit : ln 2 \is a GRing.unit := unitf_gt0 (@ln2_gt0 R).
        have Htmp0 : y < log2 (dA * gfid_lim ^+ 2).
        {
          by rewrite Hlim_eq -Hv_eq.
        }
        have Htmp : y * ln 2 < ln (dA * gfid_lim ^+ 2).
        {
          have Htmp1 := Htmp0.
          rewrite -(ltr_pM2r ln2_gt0) in Htmp1.
          rewrite /log2 (divrK Hln2_unit) in Htmp1.
          exact: Htmp1.
        }
        rewrite ln_powR.
        exact: Htmp.
      }
      have Hlim_arg_pos0 : 0 < dA * gfid_lim ^+ 2.
      {
        rewrite Hlim_eq.
        exact: Harg0_pos.
      }
      by rewrite -ltr_ln ?powR_gt0 //.
    }
    have Hsqrt_gt : Num.sqrt ((2 `^ y) / dA) < gfid_lim.
    {
      have Hdiv_lt : (2 `^ y) / dA < gfid_lim ^+ 2.
      {
        rewrite ltr_pdivrMr //.
        by rewrite mulrC.
      }
      have -> : gfid_lim = Num.sqrt (gfid_lim ^+ 2).
      {
        symmetry.
        rewrite sqrtr_sqr.
        exact: ger0_norm Hgfid_lim_ge0.
      }
      rewrite ltr_sqrt.
      - exact: Hdiv_lt.
      - exact: lt_trans (divr_gt0 Htwo_pow_pos HdA_pos) Hdiv_lt.
    }
    have Hnear_gfid :
        \forall k \near \oo%classic, Num.sqrt ((2 `^ y) / dA) < gfid_fun k.
    {
      have Hgap_gfid_pos : 0 < gfid_lim - Num.sqrt ((2 `^ y) / dA).
      {
        by rewrite subr_gt0.
      }
      have Hdist_gfid :
          \forall k \near \oo%classic,
            `| gfid_lim - gfid_fun k | <
              gfid_lim - Num.sqrt ((2 `^ y) / dA).
      {
        exact: (@cvgr_dist_lt R [the normedModType R of R^o]
          nat eventually _ gfid_fun gfid_lim Hcvg_gfid _ Hgap_gfid_pos).
      }
      near=> k.
      have Hdist_k :
          `| gfid_lim - gfid_fun k | <
            gfid_lim - Num.sqrt ((2 `^ y) / dA).
      {
        near: k.
        exact: Hdist_gfid.
      }
      rewrite -ltrN2.
      rewrite -(ltrD2l gfid_lim).
      by rewrite ltr_normlW.
      Unshelve. end_near.
    }
    near=> k.
    have Hfg_ball : eps_ball eps rhoS (fgS k).
    {
      exact: (Hf (g k)).1.
    }
    have Hfg_psd : fgS k \is psdlf.
    {
      exact: eps_ball_psdlf Hfg_ball.
    }
    have Hfg_tr : @complex.Re R (\Tr (fgS k)) <= 1.
    {
      exact: eps_ball_trlf Hfg_ball.
    }
    have Hgfid_k_ge0 : 0 <= gfid_fun k.
    {
      rewrite Hfun_eq.
      rewrite /gfid.
      apply: gfid_ge0_mx.
      - by move: Hfg_psd; rewrite qualifE.
      - by move: HsigmaX_psd; rewrite qualifE.
    }
    have Hsq_gt : 2 `^ y < dA * (gfid_fun k) ^+ 2.
    {
      have Hgfid_k_gt : Num.sqrt ((2 `^ y) / dA) < gfid_fun k.
      {
        near: k.
        exact: Hnear_gfid.
      }
      have Hsqrt_gfid : gfid_fun k = Num.sqrt ((gfid_fun k) ^+ 2).
      {
        symmetry.
        rewrite sqrtr_sqr.
        exact: ger0_norm Hgfid_k_ge0.
      }
      have Htmp :
          Num.sqrt ((2 `^ y) / dA) < Num.sqrt ((gfid_fun k) ^+ 2).
      {
        by rewrite -Hsqrt_gfid.
      }
      have Hgfid_k_pos : 0 < gfid_fun k.
      {
        exact: le_lt_trans (sqrtr_ge0 ((2 `^ y) / dA)) Hgfid_k_gt.
      }
      have Hgfid_k_sq_pos0 : 0 < (gfid_fun k) ^+ 2.
      {
        rewrite expr2.
        apply: mulr_gt0; exact: Hgfid_k_pos.
      }
      have Hdiv_lt : (2 `^ y) / dA < (gfid_fun k) ^+ 2.
      {
        by rewrite -ltr_sqrt ?divr_ge0 ?ltW ?powR_gt0.
      }
      move: Hdiv_lt.
      rewrite ltr_pdivrMr //.
      by rewrite mulrC.
    }
    have Harg_k_pos : 0 < dA * (gfid_fun k) ^+ 2.
    {
      exact: lt_trans Htwo_pow_pos Hsq_gt.
    }
    have Hy_lt_val : y < log2 (dA * (gfid_fun k) ^+ 2).
    {
      have Hlog_sq : ln (2 `^ y) < ln (dA * (gfid_fun k) ^+ 2).
      {
        by rewrite -ltr_ln ?powR_gt0 // in Hsq_gt.
      }
      have Hln2_unit : ln 2 \is a GRing.unit := unitf_gt0 (@ln2_gt0 R).
      have Htmp : y * ln 2 < ln (dA * (gfid_fun k) ^+ 2).
      {
        move: Hlog_sq.
        by rewrite ln_powR.
      }
      rewrite -(ltr_pM2r ln2_gt0).
      rewrite /log2 (divrK Hln2_unit).
      exact: Htmp.
    }
    have Hfeas_k :
        hmax_feasible T (fgS k) (log2 (dA * (gfid_fun k) ^+ 2)).
    {
      exists sigmaB; split.
      - exact: PsigmaB_den.
      - rewrite -Hfun_eq.
        by rewrite (elog2_gt0 Harg_k_pos).
    }
    have Hle_hmax : log2 (dA * (gfid_fun k) ^+ 2) <= hmax T (fgS k).
    {
      have Hfg_sup := hmax_has_sup Hfg_psd Hfg_tr
        (Hball_trace_pos _ Hfg_ball).
      exact: hmax_ub Hfg_sup Hfeas_k.
    }
    exact: lt_le_trans Hy_lt_val Hle_hmax.
    Unshelve. end_near.
  }
  have Hopt_upper : hmax T tauS0 <= h.
  {
    have Hnot_gt : ~~ (h < hmax T tauS0).
    {
      apply/negP=> Hgt.
      pose y := h + (hmax T tauS0 - h) / 2%:R.
      have Hy_gt_h : h < y.
      {
        rewrite /y ltrDl.
        apply: divr_gt0.
        - by rewrite subr_gt0.
        - by rewrite ltr0Sn.
      }
      have Hy_lt_opt : y < hmax T tauS0.
      {
        rewrite /y.
        have Hhalf_lt :
            (hmax T tauS0 - h) / 2%:R < hmax T tauS0 - h.
        {
          rewrite ltr_pdivrMr.
          - rewrite mulr_natr mulr2n ltrDl.
            by rewrite subr_gt0.
          - by rewrite ltr0Sn.
        }
        have Htmp :
            h + (hmax T tauS0 - h) / 2%:R <
            h + (hmax T tauS0 - h).
        {
          by rewrite ltrD2l.
        }
        have Hrhs_eq : h + (hmax T tauS0 - h) = hmax T tauS0.
        {
          by rewrite addrC subrK.
        }
        by rewrite Hrhs_eq in Htmp.
      }
      pose E0 := [set v : R | hmax_feasible T tauS0 v]%classic.
      have HtauS0_psd : tauS0 \is psdlf.
      {
        exact: eps_ball_psdlf HtauS0_ball.
      }
      have HtauS0_tr : @complex.Re R (\Tr tauS0) <= 1.
      {
        exact: eps_ball_trlf HtauS0_ball.
      }
      have HsupE0 : has_sup E0.
      {
        exact: Hhmax_feasible_has_sup HtauS0_psd HtauS0_tr
          (Hball_trace_pos _ HtauS0_ball).
      }
      pose eta0 := (hmax T tauS0 - y) / 2%:R.
      have Heta0_pos : 0 < eta0.
      {
        rewrite /eta0.
        apply: divr_gt0.
        - by rewrite subr_gt0.
        - by rewrite ltr0Sn.
      }
      have [v HvE Hvgt] := sup_adherent Heta0_pos HsupE0.
      move: HvE => [sigmaB [PsigmaB Hv]].
      pose sigmaX :=
        castlf (eqST_max, eqST_max)
          ((((dim 'H[H]_(S :\: T))%:R^-1)%:C *:
            ((\1 : 'F_(S :\: T)) \O sigmaB))).
      have Hy_lt_v : y < v.
      {
        have Hgap_half :
            (hmax T tauS0 - y) / 2%:R < hmax T tauS0 - y.
        {
          rewrite ltr_pdivrMr.
          - rewrite mulr_natr mulr2n ltrDl.
            by rewrite subr_gt0.
          - by rewrite ltr0Sn.
        }
        have Htmp :
            y + (hmax T tauS0 - y) / 2%:R <
            y + (hmax T tauS0 - y).
        {
          rewrite ltrD2l.
          exact: Hgap_half.
        }
        have Hsum :
            y + (hmax T tauS0 - y) = hmax T tauS0.
        {
          rewrite addrC subrK.
          reflexivity.
        }
        have Hhalf_lt_hmax :
            y + eta0 < hmax T tauS0.
        {
          rewrite /eta0 Hsum in Htmp.
          exact: Htmp.
        }
        have Hhmax_lt_v :
            hmax T tauS0 - eta0 < v.
        {
          exact: Hvgt.
        }
        have Hy_lt_gap : y < hmax T tauS0 - eta0.
        {
          move: Hhalf_lt_hmax.
          by rewrite ltrBrDr.
        }
        exact: lt_trans Hy_lt_gap Hhmax_lt_v.
      }
      have Hnear_opt : \forall k \near \oo%classic, y < hmax T (fgS k).
      {
        exact: Hnear_from_witness PsigmaB Hv Hy_lt_v.
      }
      have Heps_pos : 0 < y - h.
      {
        by rewrite subr_gt0.
      }
      have [N HN] := ExtNumTopology.extNum_archi Heps_pos.
      have Hk_gt_N_near : \forall k \near \oo%classic, (N < k)%N.
      {
        exact: nbhs_infty_gt N.
      }
      have Hfalse_near : \forall k \near \oo%classic, False.
      {
        near=> k.
        have Hk_ge_N : (k >= N)%N.
        {
          have Hk_gt_N0 : (N < k)%N.
          {
            near: k.
            exact: Hk_gt_N_near.
          }
          exact: ltnW Hk_gt_N0.
        }
        have Hgk_ge_k : (g k >= k)%N.
        {
          exact: nchain_ge Hg k.
        }
        have Hgk_ge_N : (g k >= N)%N.
        {
          exact: leq_trans Hk_ge_N Hgk_ge_k.
        }
        pose gkR : R := (g k).+1%:R.
        pose NR : R := N.+1%:R.
        have Hupper_k : hmax T (fgS k) < h + 1 / NR.
        {
          move: (Hf (g k)).2 => Hlt.
          move: Hlt => [_ Hlt].
          have Hsum_le :
              h + 1 / gkR <= h + 1 / NR.
          {
            rewrite lerD2l /gkR /NR.
            rewrite !div1r.
            rewrite lef_pV2.
            - rewrite ler_nat.
              rewrite -(leq_add2r 1%N) !addn1.
              exact: Hgk_ge_N.
            - by rewrite posrE ltr0Sn.
            - by rewrite posrE ltr0Sn.
          }
          exact: lt_le_trans Hlt Hsum_le.
        }
        have HboundN : h + 1 / NR < y.
        {
          have Htmp :
              h + 1 / NR < h + (y - h).
          {
            rewrite ltrD2l /NR div1r.
            exact: HN.
          }
          have Hy_eq : h + (y - h) = y.
          {
            by rewrite addrC subrK.
          }
          rewrite -Hy_eq.
          exact: Htmp.
        }
        have Hcontra0 : hmax T (fgS k) < y.
        {
          exact: lt_trans Hupper_k HboundN.
        }
        have Hcontra1 : y < hmax T (fgS k).
        {
          near: k.
          exact: Hnear_opt.
        }
        have Hcontra := lt_trans Hcontra1 Hcontra0.
        by rewrite ltxx in Hcontra.
        Unshelve. end_near.
      }
      have Hfalse : False.
      {
        have [k Hkfalse] :=
          @filter_ex nat _ _ (fun _ : nat => False) Hfalse_near.
        exact: Hkfalse.
      }
      exact: Hfalse.
    }
    by rewrite -leNgt in Hnot_gt.
  }
  have Hopt_lower : h <= hmax T tauS0.
  {
    apply: smooth_hmax_lb.
    - exact: Prho.
    - exact: Hrho_tr.
    - by apply/andP.
    - exact: HtauS0_ball.
  }
  exists tauS0; split=> //.
  apply/eqP; rewrite eq_le.
  by apply/andP; split.
Qed.

(* path: entropy:smooth_hmaxE_EFin -> *)
(*   bb84:bb84_secret *)
Lemma smooth_hmaxE_EFin eps (rhoS : 'F[H]_S) :
  rhoS \is psdlf ->
  @complex.Re R (\Tr rhoS) <= 1 ->
  0 <= eps < Num.sqrt (@complex.Re R (\Tr rhoS)) ->
  smooth_hmaxE T eps rhoS = (smooth_hmax T eps rhoS)%:E.
Proof.
  move=> Prho Hrho_tr Heps.
  have [tauS [Htau_ball Htau_opt]] :=
    smooth_hmax_attained Prho Hrho_tr Heps.
  have Htau_psd : tauS \is psdlf := eps_ball_psdlf Htau_ball.
  have Htau_tr : @complex.Re R (\Tr tauS) <= 1 := eps_ball_trlf Htau_ball.
  have Htau_pos : 0 < @complex.Re R (\Tr tauS).
  { exact: eps_ball_trace_pos Prho Hrho_tr Heps Htau_ball. }
  apply/eqP; rewrite eq_le; apply/andP; split.
  - rewrite /smooth_hmaxE leeNl Htau_opt.
    apply: ereal_sup_ubound.
    exists tauS; split; first exact: Htau_ball.
    by rewrite (hmaxE_EFin Htau_psd Htau_tr Htau_pos).
  - rewrite /smooth_hmaxE leeNr.
    apply: ge_ereal_sup => v [tau [Hball ->]].
    rewrite leeN2.
    have Htau'_psd : tau \is psdlf := eps_ball_psdlf Hball.
    have Htau'_tr : @complex.Re R (\Tr tau) <= 1 := eps_ball_trlf Hball.
    have Htau'_pos : 0 < @complex.Re R (\Tr tau).
    { exact: eps_ball_trace_pos Prho Hrho_tr Heps Hball. }
    rewrite (hmaxE_EFin Htau'_psd Htau'_tr Htau'_pos).
    rewrite lee_fin.
    exact: smooth_hmax_lb Prho Hrho_tr Heps Hball.
Qed.

End HmaxProps.

(* ================================================================== *)
(* Labelled/matrix entropy bridges.                                    *)
(* ================================================================== *)

Section LabelledMatrixBridge.
Variable (L : finType) (H : L -> chsType).

(* biprod_lift_mx *)
(* infra: no tex label — reusable singleton hmax witness product bridge. *)
(* path: entropy:biprod_lift_mx -> entropy:hmax_labelled_product_mx -> *)
(*   entropy:entropy_data_proc -> *)
(*   bb84:bb84_secret *)
Lemma biprod_lift_mx
    (A B : {set L}) (disAB : [disjoint A & B])
    (eqST : (((A :|: B) :\: B) :|:
             ((A :|: B) :&: B) =
             (A :|: B)))
    (eqB : ((A :|: B) :&: B) = B)
    (sigma0 : 'F[H]_(((A :|: B) :&: B))) :
  biprod_mx disAB
    (castlf (eqST, eqST)
      ((\1 : 'F[H]_(((A :|: B) :\: B))) \O sigma0)) =
  (1%:M : 'M[C]_(dim 'H[H]_A)) *t
    h2mx (castlf (eqB, eqB) sigma0).
Proof.
  set S_AB := (A :|: B).
  have eqA : S_AB :\: B = A.
  {
    rewrite /S_AB.
    exact: setDU_r disAB.
  }
  have Hcast_lift :
      castlf (eqST, eqST)
        ((\1 : 'F[H]_(S_AB :\: B)) \O sigma0) =
      ((\1 : 'F[H]_A) \O castlf (eqB, eqB) sigma0 : 'F[H]_S_AB).
  {
    have eqU1 :
        (S_AB :\: B) :|: (S_AB :&: B) =
        A :|: (S_AB :&: B).
    {
      by rewrite eqA.
    }
    have eqU2 : A :|: (S_AB :&: B) = S_AB.
    {
      by rewrite eqB /S_AB.
    }
    transitivity
      (castlf (etrans eqU1 eqU2, etrans eqU1 eqU2)
        ((\1 : 'F[H]_(S_AB :\: B)) \O sigma0)).
    {
      by rewrite (eq_irrelevance (etrans eqU1 eqU2) eqST).
    }
    rewrite -(castlf_comp eqU1 eqU1 eqU2 eqU2).
    rewrite (sdotIf_cast_l eqA eqU1) castlf1.
    by rewrite (sdotIf_cast_r eqB eqU2).
  }
  pose sigmaB := castlf (eqB, eqB) sigma0.
  have Hten :
      (((\1 : 'F[H]_A) \O sigmaB) : 'F[H]_S_AB) =
      ((\1 : 'F[H]_A) \⊗ sigmaB).
  {
    by apply: to_Fnd_inj; rewrite (sdotFT _ _ disAB) to_Fnd_tenE.
  }
  rewrite /biprod_mx Hcast_lift Hten h2mx_tenf h2mx1.
  set Q := castmx (tenv_dim disAB, erefl)
      (@tenv_mxU R L H A B).
  have HQt :
      Q^*t =
      castmx (erefl, tenv_dim disAB)
        (@tenv_mxU R L H A B)^*t.
  {
    rewrite /Q.
    exact: (@castmx_mx_mxT _ _ (@adjmx _) _ _ _ _
      (tenv_dim disAB, erefl)
      (@tenv_mxU R L H A B)).
  }
  rewrite -/Q HQt.
  rewrite mcextra.castmx_mul.
  rewrite mcextra.castmx_mul.
  have HU1 :
      (@tenv_mxU R L H A B)^*t *m
      @tenv_mxU R L H A B = 1%:M.
  {
    have := unitarymxK (@tenv_mxU_adj_unitarymx R L H A B disAB).
    by rewrite adjmxK.
  }
  rewrite !mulmxA.
  rewrite HU1 mul1mx.
  rewrite -!mulmxA HU1 mulmx1.
  by rewrite castmx_id.
Qed.

(* pur_dist_labelled_mx                                                     *)
(* infra: no tex label — fundamental & reusable (mathcomp-style)            *)
(* math: pur_dist(rho,tau) = pur_dist_mx(bip_mx rho,         *)
(*                                       bip_mx tau).         *)
(* Consumers (≥2): smooth_hmin_labelled_mx, smooth_hmax_labelled_mx         *)
(* path: entropy:pur_dist_labelled_mx -> *)
(*   bb84:bb84_secret *)
Lemma pur_dist_labelled_mx
    (A B : {set L}) (disAB : [disjoint A & B])
    (rho tau : 'F[H]_(A :|: B)) :
  pur_dist rho tau =
  pur_dist_mx (bip_mx disAB rho)
              (bip_mx disAB tau).
Proof.
  rewrite /bip_mx /pur_dist /pur_dist_mx /gfid.
  by rewrite gfid_cast_mx.
Qed.

(* hmin_labelled_product_mx                                                 *)
(* infra: no tex label — fundamental & reusable (mathcomp-style)            *)
(* math: hmin B tauS = hmin_mx (biprod_mx disAB tauS). *)
(* path: entropy:hmin_labelled_product_mx -> *)
(*   entropy:smooth_hmin_labelled_mx -> eur:entropic_uncertainty_relation -> *)
(*   bb84:entropic_uncertainty_relation_bb84 -> bb84:bb84_secret *)
Lemma hmin_labelled_product_mx
    (A B : {set L}) (disAB : [disjoint A & B])
    (tauS : 'F[H]_(A :|: B)) :
  hmin B tauS = hmin_mx (biprod_mx disAB tauS).
Proof.
  set S_AB := A :|: B.
  have eqB_set : S_AB :&: B = B.
  { rewrite /S_AB. setdec. }
  have eqST_set :
      (S_AB :\: B) :|: (S_AB :&: B) = S_AB.
  { by rewrite finset.setUC finset.setID. }
  pose Q : 'M[C]_(dim 'H[H]_A * dim 'H[H]_B) :=
    castmx (tenv_dim disAB, erefl) (@tenv_mxU R L H A B).
  have HQadj : Q^*t = castmx (erefl, tenv_dim disAB)
                       (@tenv_mxU R L H A B)^*t.
  { rewrite /Q.
    exact: (@castmx_mx_mxT _ _ (@adjmx _) _ _ _ _
      (tenv_dim disAB, erefl) (@tenv_mxU R L H A B)). }
  have HUtU :
      (@tenv_mxU R L H A B)^*t *m
      @tenv_mxU R L H A B = 1%:M.
  { have := unitarymxK (@tenv_mxU_adj_unitarymx R L H A B disAB).
    by rewrite adjmxK. }
  have HUUt :
      @tenv_mxU R L H A B *m
      (@tenv_mxU R L H A B)^*t = 1%:M.
  { exact: unitarymxK (@tenv_mxU_unitarymx R L H A B). }
  have Hcast1 : forall (n n' : nat) (e : n = n'),
      castmx (e, e) (1%:M : 'M[C]_n) = 1%:M.
  { by move=> n n' e; case: n' / e; rewrite castmx_id. }
  have HQadjQ : Q^*t *m Q = 1%:M.
  { rewrite HQadj /Q mcextra.castmx_mul.
    by rewrite HUtU Hcast1. }
  have HQQadj : Q *m Q^*t = 1%:M.
  { rewrite HQadj /Q mcextra.castmx_mul.
    by rewrite HUUt Hcast1. }
  have HQ_QadjT : Q = (Q^*t)^*t by rewrite adjmxK.
  rewrite /hmin /hmin_mx /phi_min.
  congr (- log2 _); congr (inf _).
  apply/predeqP=> v; split.
  - (* labelled feasible -> matrix feasible *)
    move=> [sigma [Hsig_psd [Hfeas Htr]]].
    pose sigmaB : 'F[H]_B := castlf (eqB_set, eqB_set) sigma.
    pose sigmaM : 'M[C]_(dim 'H[H]_B) := h2mx sigmaB.
    exists sigmaM.
    have HsigmaB_psd : sigmaB \is psdlf
      by exact: castlf_psdlf Hsig_psd.
    have HsigmaM_psd : sigmaM \is psdmx
      by move: HsigmaB_psd; rewrite qualifE.
    split=> //.
    (* normalize the cast proof in Hfeas to the eqST_set *)
    have Hfeas' :
        (castlf (eqST_set, eqST_set)
          ((\1 : 'F[H]_(S_AB :\: B)) \O sigma) - tauS) \is psdlf.
    { move: Hfeas. set e1 := (X in castlf (X, X) _). set e2 := eqST_set.
      by rewrite (eq_irrelevance e1 e2). }
    split.
    + (* (1 *t sigmaM - biprod_mx disAB tauS) \is psdmx *)
      have Hlift :=
        biprod_lift_mx disAB eqST_set eqB_set sigma.
      have Hfeas_mx :
          h2mx (castlf (eqST_set, eqST_set)
            ((\1 : 'F[H]_(S_AB :\: B)) \O sigma) - tauS) \is psdmx
        := psdlf_h2mx Hfeas'.
      have Hcast_psd :
          castmx (tenv_dim disAB, tenv_dim disAB)
            (h2mx (castlf (eqST_set, eqST_set)
              ((\1 : 'F[H]_(S_AB :\: B)) \O sigma) - tauS))
            \is psdmx
        by exact: castmx_sq_psdmx Hfeas_mx.
      have Hbimap : Q^*t *m
          castmx (tenv_dim disAB, tenv_dim disAB)
            (h2mx (castlf (eqST_set, eqST_set)
              ((\1 : 'F[H]_(S_AB :\: B)) \O sigma) - tauS))
            *m Q \is psdmx.
      { rewrite {2}HQ_QadjT.
        exact: psdmx_bimap_closed_gen Hcast_psd. }
      have Hexpand :
          Q^*t *m
            castmx (tenv_dim disAB, tenv_dim disAB)
              (h2mx (castlf (eqST_set, eqST_set)
                ((\1 : 'F[H]_(S_AB :\: B)) \O sigma) - tauS))
              *m Q
        = (1%:M : 'M[C]_(dim 'H[H]_A)) *t sigmaM
            - biprod_mx disAB tauS.
        { rewrite raddfB /=.
        have Hcast_lin : forall (X Y : 'F[H]_S_AB),
            castmx (tenv_dim disAB, tenv_dim disAB) (h2mx X - h2mx Y) =
            castmx (tenv_dim disAB, tenv_dim disAB) (h2mx X)
            - castmx (tenv_dim disAB, tenv_dim disAB) (h2mx Y).
          { by move=> X Y; rewrite raddfB. }
        rewrite Hcast_lin.
        rewrite mulmxBr mulmxBl.
        rewrite -[X in _ - X = _]/(biprod_mx disAB tauS).
        rewrite -/Q.
        congr (_ - _).
        by rewrite -Hlift /biprod_mx -/Q. }
      by rewrite -Hexpand.
    + rewrite Htr /sigmaM /sigmaB.
      have -> : (\tr (h2mx (castlf (eqB_set, eqB_set) sigma)) : C) = \Tr sigma
        by rewrite -[in RHS](castlf_trlfE eqB_set sigma).
      reflexivity.
  - (* matrix feasible -> labelled feasible *)
    move=> [sigmaM [HsigmaM_psd [Hfeas_mx Htr_mx]]].
    pose sigmaB : 'F[H]_B := mx2h sigmaM.
    pose sigma : 'F[H]_(S_AB :&: B) :=
      castlf (esym eqB_set, esym eqB_set) sigmaB.
    exists sigma.
    have HsigmaB_psd : sigmaB \is psdlf
      by rewrite qualifE /sigmaB mx2hK.
    have Hsigma_psd : sigma \is psdlf
      by exact: castlf_psdlf HsigmaB_psd.
    split=> //.
    split.
    + (* (castlf (eqST_set) (\1 \O sigma) - tauS) \is psdlf *)
      have HsigmaB_eq : castlf (eqB_set, eqB_set) sigma = sigmaB.
      { rewrite /sigma castlf_comp.
        rewrite (eq_irrelevance (etrans (esym eqB_set) eqB_set) (erefl _)).
        by rewrite castlf_id. }
      have Hlift :=
        biprod_lift_mx disAB eqST_set eqB_set sigma.
      rewrite HsigmaB_eq in Hlift.
      have Hfeas_conj :
          Q *m ((1%:M : 'M[C]_(dim 'H[H]_A)) *t sigmaM
                - biprod_mx disAB tauS) *m Q^*t
            \is psdmx.
      { exact: psdmx_bimap_closed_gen Hfeas_mx. }
      have Hexpand :
          Q *m ((1%:M : 'M[C]_(dim 'H[H]_A)) *t sigmaM
                - biprod_mx disAB tauS) *m Q^*t
        = castmx (tenv_dim disAB, tenv_dim disAB)
            (h2mx (castlf (eqST_set, eqST_set)
              ((\1 : 'F[H]_(S_AB :\: B)) \O sigma) - tauS)).
        { have Hb : sigmaM = h2mx sigmaB by rewrite /sigmaB mx2hK.
          have Hcanc : forall (M : 'M[C]_(dim 'H[H]_S_AB)),
              Q *m (Q^*t *m castmx (tenv_dim disAB, tenv_dim disAB) M *m Q)
                *m Q^*t = castmx (tenv_dim disAB, tenv_dim disAB) M.
          { move=> M.
            rewrite !mulmxA HQQadj mul1mx.
            by rewrite -mulmxA HQQadj mulmx1. }
          have Hforward :
              Q^*t *m
                castmx (tenv_dim disAB, tenv_dim disAB)
                  (h2mx (castlf (eqST_set, eqST_set)
                    ((\1 : 'F[H]_(S_AB :\: B)) \O sigma) - tauS))
                  *m Q
            = (1%:M : 'M[C]_(dim 'H[H]_A)) *t sigmaM
                - biprod_mx disAB tauS.
          {
              rewrite raddfB /=.
            have Hcast_lin : forall (X Y : 'F[H]_S_AB),
                castmx (tenv_dim disAB, tenv_dim disAB) (h2mx X - h2mx Y) =
                castmx (tenv_dim disAB, tenv_dim disAB) (h2mx X)
                - castmx (tenv_dim disAB, tenv_dim disAB) (h2mx Y).
              { by move=> X Y; rewrite raddfB. }
            rewrite Hcast_lin.
            rewrite mulmxBr mulmxBl.
            rewrite -[X in _ - X = _]/(biprod_mx disAB tauS).
            rewrite -/Q.
            congr (_ - _).
            rewrite Hb.
            by rewrite -Hlift /biprod_mx -/Q.
          }
          rewrite -Hforward.
          exact: Hcanc _. }
      rewrite Hexpand in Hfeas_conj.
      have Hh2mx_psd :
          h2mx (castlf (eqST_set, eqST_set)
            ((\1 : 'F[H]_(S_AB :\: B)) \O sigma) - tauS) \is psdmx.
      { have Hcast_eq :
            forall (M : 'M[C]_(dim 'H[H]_S_AB)),
            castmx (esym (tenv_dim disAB), esym (tenv_dim disAB))
              (castmx (tenv_dim disAB, tenv_dim disAB) M) = M.
        { move=> M. rewrite castmx_comp.
          rewrite (eq_irrelevance
            (etrans (tenv_dim disAB) (esym (tenv_dim disAB)))
            (erefl _)).
          by rewrite castmx_id. }
        rewrite -[X in X \is _](Hcast_eq).
        exact: castmx_sq_psdmx Hfeas_conj. }
      (* normalize the cast back to whatever phi_min_feasible expects *)
      rewrite qualifE.
      set e := (X in castlf (X, X) _).
      by rewrite (eq_irrelevance e eqST_set) Hh2mx_psd.
    + rewrite Htr_mx /sigma castlf_trlfE.
      by rewrite /sigmaB /lftrace mx2hK.
Qed.

(* path: entropy:hminE_labelled_product_mx -> *)
(*   bb84:bb84_secret *)
Lemma hminE_labelled_product_mx
    (A B : {set L}) (disAB : [disjoint A & B])
    (tauS : 'F[H]_(A :|: B)) :
  0 < phi_min B tauS ->
  hminE B tauS =
    (hmin_mx (biprod_mx disAB tauS))%:E.
Proof.
  move=> Hphi.
  by rewrite (@hminE_EFin L H (A :|: B) B tauS Hphi)
    (hmin_labelled_product_mx disAB tauS).
Qed.

(* hmax_labelled_product_mx                                                 *)
(* infra: no tex label — fundamental & reusable (mathcomp-style)            *)
(* math: hmax B tauS = hmax_mx (biprod_mx disAB tauS). *)
(* path: entropy:hmax_labelled_product_mx -> entropy:entropy_data_proc -> *)
(*   bb84:bb84_secret *)
Lemma hmax_labelled_product_mx
    (A B : {set L}) (disAB : [disjoint A & B])
    (tauS : 'F[H]_(A :|: B)) :
  tauS \is psdlf ->
  hmax B tauS = hmax_mx (biprod_mx disAB tauS).
Proof.
  move=> HtauS_psd.
  set S_AB := A :|: B.
  have eqB_set : S_AB :&: B = B.
  { rewrite /S_AB. setdec. }
  have eqA_set : S_AB :\: B = A.
  { rewrite /S_AB; exact: setDU_r disAB. }
  have eqST_set :
      (S_AB :\: B) :|: (S_AB :&: B) = S_AB.
  { by rewrite finset.setUC finset.setID. }
  (* Hbridge: labelled hmax now uses the normalized generalized-fidelity    *)
  (* form. The labelled π_A tensor is first transported by the existing     *)
  (* product lift, then the same simultaneous Q-conjugation/cast argument   *)
  (* as the hmin bridge removes the labelled encoding.                      *)
  have Hbridge : forall (sigma : 'F[H]_(S_AB :&: B)),
      sigma \is psdlf ->
      tauS \is psdlf ->
      (gfid tauS
        (castlf (eqST_set, eqST_set)
          (((GRing.inv ((dim 'H[H]_(S_AB :\: B))%:R : R))%:C) *:
            ((\1 : 'F[H]_(S_AB :\: B)) \O sigma)))) ^+ 2 =
      (gfidelity (biprod_mx disAB tauS)
        (mmix_mx (dim 'H[H]_A)
           *t h2mx (castlf (eqB_set, eqB_set) sigma))) ^+ 2.
  { move=> sigma Hsig_psd HtauS_psd'.
    congr (_ ^+ 2).
    pose cA : R := GRing.inv ((dim 'H[H]_(S_AB :\: B))%:R : R).
    pose sigmaB : 'F[H]_B := castlf (eqB_set, eqB_set) sigma.
    have Hlift :=
      biprod_lift_mx disAB eqST_set eqB_set sigma.
      have HlbpZ : forall (c : C) (rho : 'F[H]_S_AB),
          biprod_mx disAB (c *: rho) =
          c *: biprod_mx disAB rho.
        { move=> c rho.
          have Hh2mxZ : h2mx (c *: rho) = c *: h2mx rho.
          {
            move: (h2mxP c rho 0).
            by rewrite h2mx0 !addr0.
          }
          rewrite /biprod_mx Hh2mxZ linearZ /=.
          by rewrite scalemxAl scalemxAr. }
    have Hwit_scale :
        mmix_mx (dim 'H[H]_A) *t h2mx sigmaB =
        cA%:C *:
          ((1%:M : 'M[C]_(dim 'H[H]_A)) *t h2mx sigmaB).
    { rewrite /mmix_mx /cA eqA_set.
      apply/matrixP=> i j.
      by rewrite !mxE mulrA. }
    have Hscaled_lift :
        biprod_mx disAB
          (castlf (eqST_set, eqST_set)
            (cA%:C *:
              ((\1 : 'F[H]_(S_AB :\: B)) \O sigma))) =
        mmix_mx (dim 'H[H]_A) *t h2mx sigmaB.
    { by rewrite linearZ /= HlbpZ Hlift -Hwit_scale. }
    rewrite -/cA -Hscaled_lift.
    rewrite /biprod_mx /gfid.
    set U := @tenv_mxU R L H A B.
    set Q : 'M[C]_(dim 'H[H]_A * dim 'H[H]_B) :=
      castmx (tenv_dim disAB, erefl) U.
    set rho_lf : 'F[H]_S_AB :=
      castlf (eqST_set, eqST_set)
        (cA%:C *: ((\1 : 'F[H]_(S_AB :\: B)) \O sigma)).
    have HQt : Q^*t = castmx (erefl, tenv_dim disAB) U^*t
      by rewrite /Q;
         exact: (@castmx_mx_mxT _ _ (@adjmx _) _ _ _ _
                   (tenv_dim disAB, erefl) U).
    have Hpeel : forall (M : 'M[C]_(dim 'H[H]_S_AB)),
        Q^*t *m castmx (tenv_dim disAB, tenv_dim disAB) M *m Q
        = U^*t *m M *m U.
    { move=> M; rewrite HQt /Q.
      rewrite mcextra.castmx_mul mcextra.castmx_mul castmx_id.
      reflexivity. }
    rewrite -/Q !Hpeel.
    have disDB : [disjoint (S_AB :\: B) & (S_AB :&: B)].
    { setdec. }
    have HcA_ge0 : 0 <= cA by rewrite /cA invr_ge0 ler0n.
    have Hrho_psd : h2mx rho_lf \is psdmx.
    { apply: psdlf_h2mx; rewrite /rho_lf; apply: castlf_psdlf.
      apply: psdlfZ; first by rewrite lecR.
      have -> : ((\1 : 'F[H]_(S_AB :\: B)) \O sigma
                  : 'F[H]_((S_AB :\: B) :|: (S_AB :&: B)))
                = (\1 : 'F[H]_(S_AB :\: B)) \⊗ sigma.
      { by apply: to_Fnd_inj; rewrite (sdotFT _ _ disDB) to_Fnd_tenE. }
      rewrite psdlfE; apply: tenf_ge0; first exact: disDB.
      - exact: lef01.
      - by rewrite -psdlfE. }
    have HtauS_mxpsd : h2mx tauS \is psdmx by exact: psdlf_h2mx.
    have HU_unitary : U \is unitarymx by exact: tenv_mxU_unitarymx.
    have HUadj_unitary : U^*t \is unitarymx
      by exact: tenv_mxU_adj_unitarymx.
    have <- := @gfid_tenv_mxU_conj_eq_mx R L H A B disAB
                 (h2mx tauS) (h2mx rho_lf) HtauS_mxpsd Hrho_psd.
    by []. }
  rewrite /hmax /hmax_mx.
  (* The post-cascade equation is used on the finite psd branch supplied by  *)
  (* HtauS_psd.                                                             *)
  congr (sup _).
  apply/predeqP=> v; split.
  - (* labelled feasible -> matrix feasible *)
    move=> [sigma [Hsig_den Hfid_eq]].
    pose sigmaB : 'F[H]_B := castlf (eqB_set, eqB_set) sigma.
    pose sigmaM : 'M[C]_(dim 'H[H]_B) := h2mx sigmaB.
    exists sigmaM.
    have Hsig_psd : sigma \is psdlf := den1lf_psd Hsig_den.
    have Hsig_tr1 : \Tr sigma = 1 := den1lf_trlf Hsig_den.
    have HsigmaB_psd : sigmaB \is psdlf
      by exact: castlf_psdlf Hsig_psd.
    have HsigmaB_den : sigmaB \is den1lf.
    { apply/den1lfP; split; first exact: HsigmaB_psd.
      by rewrite /sigmaB castlf_trlfE Hsig_tr1. }
      have HsigmaM_den : sigmaM \is den1mx.
      by move: HsigmaB_den; rewrite /sigmaM qualifE.
    split; first exact: HsigmaM_den.
    move: Hfid_eq.
    set e := (X in castlf (X, X) _).
    rewrite (eq_irrelevance e eqST_set) -/sigmaB -/sigmaM.
      rewrite -/S_AB.
      rewrite (Hbridge sigma Hsig_psd HtauS_psd).
      have HdimA :
          dim 'H[H]_(S_AB :\: B) = dim 'H[H]_A
        by rewrite eqA_set.
      by rewrite HdimA.
  - (* matrix feasible -> labelled feasible *)
    move=> [sigmaM [HsigmaM_den Hfid_eq]].
    pose sigmaB : 'F[H]_B := mx2h sigmaM.
    pose sigma : 'F[H]_(S_AB :&: B) :=
      castlf (esym eqB_set, esym eqB_set) sigmaB.
    exists sigma.
    have HsigmaB_den : sigmaB \is den1lf.
    { apply/den1lfP; split.
      - have /den1mxP [Hpsd _] := HsigmaM_den.
        by rewrite qualifE /sigmaB mx2hK.
      - have /den1mxP [_ /eqP Htr] := HsigmaM_den.
        by rewrite /sigmaB /lftrace mx2hK Htr. }
    have HsigmaB_psd : sigmaB \is psdlf := den1lf_psd HsigmaB_den.
    have Hsigma_den : sigma \is den1lf.
    { apply/den1lfP; split.
      - exact: castlf_psdlf HsigmaB_psd.
      - by rewrite /sigma castlf_trlfE (den1lf_trlf HsigmaB_den). }
    split; first exact: Hsigma_den.
    move: Hfid_eq.
    set e := (X in castlf (X, X) _).
    rewrite (eq_irrelevance e eqST_set).
    have HsigmaB_eq : castlf (eqB_set, eqB_set) sigma = sigmaB.
    { rewrite /sigma castlf_comp.
      rewrite (eq_irrelevance (etrans (esym eqB_set) eqB_set) (erefl _)).
      by rewrite castlf_id. }
    have HsigmaM_eq : sigmaM = h2mx (castlf (eqB_set, eqB_set) sigma)
      by rewrite HsigmaB_eq /sigmaB mx2hK.
      rewrite [in X in elog2 (_ * (gfidelity _ (mmix_mx _ *t X)) ^+ 2) = _]HsigmaM_eq.
      rewrite -(Hbridge sigma (den1lf_psd Hsigma_den) HtauS_psd).
      have HdimA :
          dim 'H[H]_(S_AB :\: B) = dim 'H[H]_A
        by rewrite eqA_set.
      by rewrite -HdimA.
Qed.

(* path: entropy:hmaxE_labelled_product_mx -> entropy:entropy_data_proc -> *)
(*   bb84:bb84_secret *)
Lemma hmaxE_labelled_product_mx
    (A B : {set L}) (disAB : [disjoint A & B])
    (tauS : 'F[H]_(A :|: B)) :
  tauS \is psdlf ->
  @complex.Re R (\Tr tauS) <= 1 ->
  0 < @complex.Re R (\Tr tauS) ->
  hmaxE B tauS =
    (hmax_mx (biprod_mx disAB tauS))%:E.
Proof.
  move=> Htau_psd Htau_tr Htau_pos.
  by rewrite (@hmaxE_EFin L H (A :|: B) B tauS
      Htau_psd Htau_tr Htau_pos)
    (hmax_labelled_product_mx disAB Htau_psd).
Qed.

(* tex: encoding bridge — no tex label.                                   *)
(* math: `smooth_hmin B eps rhoAB = smooth_hmin_mx eps (product).`  *)
(* Strategy: the bijection tau ↔ LBPmx tau between labelled and matrix     *)
(* eps-balls preserves psdmx (via psdmx_bimap_closed_gen + tenv_mxU adj    *)
(* unitary), trace (via mxtrace_mulC + unitarymxKV), and pur_dist (via    *)
(* gfid_tenv_mxU_conj_eq_mx + gfid_cast_mx). hmin matches via         *)
(* hmin_labelled_product_mx. The two value sets are then equal.            *)
(* Note: hypothesis `rhoAB \is psdlf` was added — required so that         *)
(* `gfid_tenv_mxU_conj_eq_mx` (which assumes both arguments psdmx)       *)
(* applies. Consumer rhoAB's are denmx → psdlf, so this is benign.         *)
(* path: entropy:smooth_hmin_labelled_mx -> *)
(*   eur:entropic_uncertainty_relation -> *)
(*   bb84:entropic_uncertainty_relation_bb84 -> bb84:bb84_secret *)
Lemma smooth_hmin_labelled_mx
    (A B : {set L}) (disAB : [disjoint A & B])
    (eps : R) (rhoAB : 'F[H]_(A :|: B)) :
  rhoAB \is psdlf ->
  smooth_hmin B eps rhoAB =
    smooth_hmin_mx eps (biprod_mx disAB rhoAB).
Proof.
  move=> Hrho_psd.
  set S_AB := A :|: B.
  pose U := @tenv_mxU R L H A B.
  pose Q : 'M[C]_(dim 'H[H]_A * dim 'H[H]_B) :=
    castmx (tenv_dim disAB, erefl) U.
  have HU : U \is unitarymx by exact: tenv_mxU_unitarymx.
  have HUadj : U^*t \is unitarymx by exact: tenv_mxU_adj_unitarymx.
  have HQadj : Q^*t = castmx (erefl, tenv_dim disAB) U^*t.
  { rewrite /Q.
    exact: (@castmx_mx_mxT _ _ (@adjmx _) _ _ _ _
      (tenv_dim disAB, erefl) U). }
  have Hcast1 : forall (n n' : nat) (e : n = n'),
      castmx (e, e) (1%:M : 'M[C]_n) = 1%:M.
  { by move=> n n' e; case: n' / e; rewrite castmx_id. }
  have HUtU : U^*t *m U = 1%:M.
  { have := unitarymxK HUadj. by rewrite adjmxK. }
  have HUUt : U *m U^*t = 1%:M by exact: unitarymxK HU.
  have HQadjQ : Q^*t *m Q = 1%:M.
  { rewrite HQadj /Q mcextra.castmx_mul. by rewrite HUtU Hcast1. }
  have HQQadj : Q *m Q^*t = 1%:M.
  { rewrite HQadj /Q mcextra.castmx_mul. by rewrite HUUt Hcast1. }
  have Hrho_mxpsd : h2mx rhoAB \is psdmx := psdlf_h2mx Hrho_psd.
  have HpeelQ : forall (X : 'M[C]_(dim 'H[H]_S_AB)),
      Q^*t *m castmx (tenv_dim disAB, tenv_dim disAB) X *m Q
      = U^*t *m X *m U.
  { move=> X; rewrite HQadj /Q.
    by rewrite mcextra.castmx_mul mcextra.castmx_mul castmx_id. }
  (* Bridge: pur_dist on labelled = pur_dist_mx on the LBPmx images. *)
  have Hpd_bridge :
      forall (tau : 'F[H]_S_AB),
      tau \is psdlf ->
      pur_dist tau rhoAB =
        pur_dist_mx (biprod_mx disAB tau)
                    (biprod_mx disAB rhoAB).
  { move=> tau Htau_psd.
    rewrite /pur_dist /pur_dist_mx /gfid.
    congr (Num.sqrt (1 - _ ^ 2)).
    have Htau_mxpsd : h2mx tau \is psdmx := psdlf_h2mx Htau_psd.
    rewrite /biprod_mx -/U -/Q.
    rewrite -[X in _ = gfidelity X _]/(Q^*t *m _ *m Q).
    rewrite -[X in _ = gfidelity _ X]/(Q^*t *m _ *m Q).
    rewrite !HpeelQ.
    by rewrite -(@gfid_tenv_mxU_conj_eq_mx R L H _ _ disAB
                  (h2mx tau) (h2mx rhoAB) Htau_mxpsd Hrho_mxpsd). }
  rewrite /smooth_hmin /smooth_hmin_mx.
  congr (sup _).
  apply/predeqP=> v; split.
  - (* labelled feasible -> matrix feasible *)
    move=> [tauS [Hball Hv]].
    move: Hball; rewrite /eps_ball
      => /andP [/andP [/andP [HtauS_psd HtauS_pos] HtauS_tr] Hpd_le].
    pose tauM := biprod_mx disAB tauS.
    exists tauM.
    have HtauM_eq :
        tauM = Q^*t *m castmx (tenv_dim disAB, tenv_dim disAB) (h2mx tauS) *m Q
      by rewrite /tauM /biprod_mx -/U -/Q.
    have HtauS_mxpsd : h2mx tauS \is psdmx := psdlf_h2mx HtauS_psd.
    have Hcast_psd : castmx (tenv_dim disAB, tenv_dim disAB) (h2mx tauS)
        \is psdmx := castmx_sq_psdmx _ HtauS_mxpsd.
    have HtauM_psd : tauM \is psdmx.
    { rewrite HtauM_eq -[Q in _ *m _ *m Q]adjmxK.
      exact: psdmx_bimap_closed_gen Hcast_psd. }
      have HtauM_tr : @complex.Re R (\tr tauM) <= 1.
      { rewrite HtauM_eq mxtrace_mulC mulmxA HQQadj mul1mx.
        rewrite (mxtrace_castmx_sq (tenv_dim disAB) (h2mx tauS)).
        by move: HtauS_tr; rewrite /lftrace. }
      have HtauM_pos : 0 < @complex.Re R (\tr tauM).
      { rewrite HtauM_eq mxtrace_mulC mulmxA HQQadj mul1mx.
        rewrite (mxtrace_castmx_sq (tenv_dim disAB) (h2mx tauS)).
        by move: HtauS_pos; rewrite /lftrace. }
      have HtauM_den : tauM \is denmx.
      { apply/denmxP; split=> //.
        have Hreal : \tr tauM \is Num.real :=
          ger0_real (psdmx_trace HtauM_psd).
        by rewrite -(RRe_real Hreal) lecR1. }
      split.
      + apply/andP; split.
        * apply/andP; split.
          -- exact: HtauM_den.
          -- exact: HtauM_pos.
        * by rewrite -(Hpd_bridge tauS HtauS_psd).
      + by rewrite Hv (hmin_labelled_product_mx disAB tauS).
    - (* matrix feasible -> labelled feasible *)
      move=> [tauM [Hconj Hv]].
      move: Hconj => /andP [/andP [HtauM_den HtauM_pos] Hpd_le].
      have /denmxP [HtauM_psd HtauM_trC] := HtauM_den.
      have HtauM_tr : @complex.Re R (\tr tauM) <= 1
        by move: HtauM_trC; rewrite lecE /= => /andP [_].
    pose tauS_mx : 'M[C]_(dim 'H[H]_S_AB) :=
      castmx (esym (tenv_dim disAB), esym (tenv_dim disAB))
        (Q *m tauM *m Q^*t).
    pose tauS : 'F[H]_S_AB := mx2h tauS_mx.
    exists tauS.
    have HtauS_mx_eq : h2mx tauS = tauS_mx by rewrite /tauS mx2hK.
    have HQconj_psd : Q *m tauM *m Q^*t \is psdmx
      by exact: psdmx_bimap_closed_gen HtauM_psd.
    have HtauS_mx_psd : tauS_mx \is psdmx
      by rewrite /tauS_mx; exact: castmx_sq_psdmx HQconj_psd.
    have HtauS_psd : tauS \is psdlf
      by rewrite qualifE HtauS_mx_eq.
    have HQinv_eq : biprod_mx disAB tauS = tauM.
    { rewrite /biprod_mx -/U -/Q HtauS_mx_eq /tauS_mx.
      rewrite castmx_comp !etrans_esymV castmx_id !mulmxA HQadjQ mul1mx.
      by rewrite -mulmxA HQadjQ mulmx1. }
    have HtauS_tr : @complex.Re R (\Tr tauS) <= 1.
    { rewrite /lftrace HtauS_mx_eq /tauS_mx.
      rewrite (mxtrace_castmx_sq (esym (tenv_dim disAB)) _).
      rewrite mxtrace_mulC mulmxA HQadjQ mul1mx.
      exact: HtauM_tr. }
    have HtauS_pos : 0 < @complex.Re R (\Tr tauS).
    { rewrite /lftrace HtauS_mx_eq /tauS_mx.
      rewrite (mxtrace_castmx_sq (esym (tenv_dim disAB)) _).
      rewrite mxtrace_mulC mulmxA HQadjQ mul1mx.
      exact: HtauM_pos. }
    split.
    + rewrite /eps_ball.
      apply/andP; split; [apply/andP; split; [apply/andP; split=> //|exact: HtauS_tr]|].
      by rewrite (Hpd_bridge tauS HtauS_psd) HQinv_eq.
    + by rewrite Hv (hmin_labelled_product_mx disAB tauS) HQinv_eq.
Qed.

(* path: entropy:smooth_hminE_labelled_mx_finite -> *)
(*   bb84:bb84_secret *)
Lemma smooth_hminE_labelled_mx_finite
    (A B : {set L}) (disAB : [disjoint A & B])
    (eps : R) (rhoAB : 'F[H]_(A :|: B)) :
  rhoAB \is psdlf ->
  smooth_hminE B eps rhoAB = (smooth_hmin B eps rhoAB)%:E ->
  smooth_hminE B eps rhoAB =
    (smooth_hmin_mx eps (biprod_mx disAB rhoAB))%:E.
Proof.
  move=> Hrho_psd Hfin.
  by rewrite Hfin (smooth_hmin_labelled_mx disAB eps Hrho_psd).
Qed.

(* tex: encoding bridge — no tex label.                                   *)
(* math: `smooth_hmax B eps rhoAB = smooth_hmax_mx eps (product).`  *)
(* Strategy: mirror of `smooth_hmin_labelled_mx`. The bijection             *)
(* tau ↔ LBPmx tau preserves psdmx (psdmx_bimap_closed_gen + tenv_mxU adj   *)
(* unitary), trace (mxtrace_mulC + unitarymxKV), and pur_dist               *)
(* (gfid_tenv_mxU_conj_eq_mx + gfid_cast_mx). hmax matches via          *)
(* hmax_labelled_product_mx. Hypothesis `rhoAB \is psdlf` is required so    *)
(* `gfid_tenv_mxU_conj_eq_mx` (assumes both arguments psdmx) applies.     *)
(* path: entropy:smooth_hmax_labelled_mx -> bb84:stat -> bb84:bb84_secret *)
Lemma smooth_hmax_labelled_mx
    (A B : {set L}) (disAB : [disjoint A & B])
    (eps : R) (rhoAB : 'F[H]_(A :|: B)) :
  rhoAB \is psdlf ->
  smooth_hmax B eps rhoAB =
    smooth_hmax_mx eps (biprod_mx disAB rhoAB).
Proof.
  move=> Hrho_psd.
  set S_AB := A :|: B.
  pose U := @tenv_mxU R L H A B.
  pose Q : 'M[C]_(dim 'H[H]_A * dim 'H[H]_B) :=
    castmx (tenv_dim disAB, erefl) U.
  have HU : U \is unitarymx by exact: tenv_mxU_unitarymx.
  have HUadj : U^*t \is unitarymx by exact: tenv_mxU_adj_unitarymx.
  have HQadj : Q^*t = castmx (erefl, tenv_dim disAB) U^*t.
  { rewrite /Q.
    exact: (@castmx_mx_mxT _ _ (@adjmx _) _ _ _ _
      (tenv_dim disAB, erefl) U). }
  have Hcast1 : forall (n n' : nat) (e : n = n'),
      castmx (e, e) (1%:M : 'M[C]_n) = 1%:M.
  { by move=> n n' e; case: n' / e; rewrite castmx_id. }
  have HUtU : U^*t *m U = 1%:M.
  { have := unitarymxK HUadj. by rewrite adjmxK. }
  have HUUt : U *m U^*t = 1%:M by exact: unitarymxK HU.
  have HQadjQ : Q^*t *m Q = 1%:M.
  { rewrite HQadj /Q mcextra.castmx_mul. by rewrite HUtU Hcast1. }
  have HQQadj : Q *m Q^*t = 1%:M.
  { rewrite HQadj /Q mcextra.castmx_mul. by rewrite HUUt Hcast1. }
  have Hrho_mxpsd : h2mx rhoAB \is psdmx := psdlf_h2mx Hrho_psd.
  have HpeelQ : forall (X : 'M[C]_(dim 'H[H]_S_AB)),
      Q^*t *m castmx (tenv_dim disAB, tenv_dim disAB) X *m Q
      = U^*t *m X *m U.
  { move=> X; rewrite HQadj /Q.
    by rewrite mcextra.castmx_mul mcextra.castmx_mul castmx_id. }
  (* Bridge: pur_dist on labelled = pur_dist_mx on the LBPmx images. *)
  have Hpd_bridge :
      forall (tau : 'F[H]_S_AB),
      tau \is psdlf ->
      pur_dist tau rhoAB =
        pur_dist_mx (biprod_mx disAB tau)
                    (biprod_mx disAB rhoAB).
  { move=> tau Htau_psd.
    rewrite /pur_dist /pur_dist_mx /gfid.
    congr (Num.sqrt (1 - _ ^ 2)).
    have Htau_mxpsd : h2mx tau \is psdmx := psdlf_h2mx Htau_psd.
    rewrite /biprod_mx -/U -/Q.
    rewrite -[X in _ = gfidelity X _]/(Q^*t *m _ *m Q).
    rewrite -[X in _ = gfidelity _ X]/(Q^*t *m _ *m Q).
    rewrite !HpeelQ.
    by rewrite -(@gfid_tenv_mxU_conj_eq_mx R L H _ _ disAB
                  (h2mx tau) (h2mx rhoAB) Htau_mxpsd Hrho_mxpsd). }
  rewrite /smooth_hmax /smooth_hmax_mx.
  congr (inf _).
  apply/predeqP=> v; split.
  - (* labelled feasible -> matrix feasible *)
    move=> [tauS [Hball Hv]].
    move: Hball; rewrite /eps_ball
      => /andP [/andP [/andP [HtauS_psd HtauS_pos] HtauS_tr] Hpd_le].
    pose tauM := biprod_mx disAB tauS.
    exists tauM.
    have HtauM_eq :
        tauM = Q^*t *m castmx (tenv_dim disAB, tenv_dim disAB) (h2mx tauS) *m Q
      by rewrite /tauM /biprod_mx -/U -/Q.
    have HtauS_mxpsd : h2mx tauS \is psdmx := psdlf_h2mx HtauS_psd.
    have Hcast_psd : castmx (tenv_dim disAB, tenv_dim disAB) (h2mx tauS)
        \is psdmx := castmx_sq_psdmx _ HtauS_mxpsd.
    have HtauM_psd : tauM \is psdmx.
    { rewrite HtauM_eq -[Q in _ *m _ *m Q]adjmxK.
      exact: psdmx_bimap_closed_gen Hcast_psd. }
      have HtauM_tr : @complex.Re R (\tr tauM) <= 1.
      { rewrite HtauM_eq mxtrace_mulC mulmxA HQQadj mul1mx.
        rewrite (mxtrace_castmx_sq (tenv_dim disAB) (h2mx tauS)).
        by move: HtauS_tr; rewrite /lftrace. }
      have HtauM_pos : 0 < @complex.Re R (\tr tauM).
      { rewrite HtauM_eq mxtrace_mulC mulmxA HQQadj mul1mx.
        rewrite (mxtrace_castmx_sq (tenv_dim disAB) (h2mx tauS)).
        by move: HtauS_pos; rewrite /lftrace. }
      have HtauM_den : tauM \is denmx.
      { apply/denmxP; split=> //.
        have Hreal : \tr tauM \is Num.real :=
          ger0_real (psdmx_trace HtauM_psd).
        by rewrite -(RRe_real Hreal) lecR1. }
      split.
      + apply/andP; split.
        * apply/andP; split.
          -- exact: HtauM_den.
          -- exact: HtauM_pos.
        * by rewrite -(Hpd_bridge tauS HtauS_psd).
      + by rewrite Hv (hmax_labelled_product_mx disAB HtauS_psd).
    - (* matrix feasible -> labelled feasible *)
      move=> [tauM [Hconj Hv]].
      move: Hconj => /andP [/andP [HtauM_den HtauM_pos] Hpd_le].
      have /denmxP [HtauM_psd HtauM_trC] := HtauM_den.
      have HtauM_tr : @complex.Re R (\tr tauM) <= 1
        by move: HtauM_trC; rewrite lecE /= => /andP [_].
    pose tauS_mx : 'M[C]_(dim 'H[H]_S_AB) :=
      castmx (esym (tenv_dim disAB), esym (tenv_dim disAB))
        (Q *m tauM *m Q^*t).
    pose tauS : 'F[H]_S_AB := mx2h tauS_mx.
    exists tauS.
    have HtauS_mx_eq : h2mx tauS = tauS_mx by rewrite /tauS mx2hK.
    have HQconj_psd : Q *m tauM *m Q^*t \is psdmx
      by exact: psdmx_bimap_closed_gen HtauM_psd.
    have HtauS_mx_psd : tauS_mx \is psdmx
      by rewrite /tauS_mx; exact: castmx_sq_psdmx HQconj_psd.
    have HtauS_psd : tauS \is psdlf
      by rewrite qualifE HtauS_mx_eq.
    have HQinv_eq : biprod_mx disAB tauS = tauM.
    { rewrite /biprod_mx -/U -/Q HtauS_mx_eq /tauS_mx.
      rewrite castmx_comp !etrans_esymV castmx_id !mulmxA HQadjQ mul1mx.
      by rewrite -mulmxA HQadjQ mulmx1. }
    have HtauS_tr : @complex.Re R (\Tr tauS) <= 1.
    { rewrite /lftrace HtauS_mx_eq /tauS_mx.
      rewrite (mxtrace_castmx_sq (esym (tenv_dim disAB)) _).
      rewrite mxtrace_mulC mulmxA HQadjQ mul1mx.
      exact: HtauM_tr. }
    have HtauS_pos : 0 < @complex.Re R (\Tr tauS).
    { rewrite /lftrace HtauS_mx_eq /tauS_mx.
      rewrite (mxtrace_castmx_sq (esym (tenv_dim disAB)) _).
      rewrite mxtrace_mulC mulmxA HQadjQ mul1mx.
      exact: HtauM_pos. }
    split.
    + rewrite /eps_ball.
      apply/andP; split; [apply/andP; split; [apply/andP; split=> //|exact: HtauS_tr]|].
      by rewrite (Hpd_bridge tauS HtauS_psd) HQinv_eq.
    + by rewrite Hv (hmax_labelled_product_mx disAB HtauS_psd) HQinv_eq.
Qed.

(* path: entropy:smooth_hmaxE_labelled_mx_finite -> *)
(*   bb84:bb84_secret *)
Lemma smooth_hmaxE_labelled_mx_finite
    (A B : {set L}) (disAB : [disjoint A & B])
    (eps : R) (rhoAB : 'F[H]_(A :|: B)) :
  rhoAB \is psdlf ->
  smooth_hmaxE B eps rhoAB = (smooth_hmax B eps rhoAB)%:E ->
  smooth_hmaxE B eps rhoAB =
    (smooth_hmax_mx eps (biprod_mx disAB rhoAB))%:E.
Proof.
  move=> Hrho_psd Hfin.
  by rewrite Hfin (smooth_hmax_labelled_mx disAB eps Hrho_psd).
Qed.

End LabelledMatrixBridge.

End FvqkdReal.
