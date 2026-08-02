(* -------------------------------------------------------------------- *)
(* pur.v — Purification of sub-normalized states, Uhlmann's theorem     *)
(* -------------------------------------------------------------------- *)
(* Module: utils.pur                                      *)
(* TeX source: LHL arXiv:1002.2436 (Uhlmann pure-state form; lemma:uhlmann-pure) +                     *)
(*   Tomamichel, 'A Framework for Non-Asymptotic Quantum Information      *)
(*   Theory' (PhD thesis, arXiv:1203.2142), Lemma 2.4 (Stinespring       *)
(*   Dilation, lm:stinespring).                                          *)
(* TeX labels: lemma:uhlmann-pure, lm:stinespring                        *)
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
From utils.labelled Require Import op sys.
From utils.dist Require Import fid.

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
(* Purification: every PSD operator ρ has a purification                *)
(*   purification ρ = |ψ⟩⟨ψ| s.t. Tr_B(|ψ⟩⟨ψ|) = ρ                  *)
(* ================================================================== *)

Section Purification.
Variable (L : finType) (HL : L -> chsType) (A B : {set L}).
Hypothesis disAB : [disjoint A & B].
(* Refinement: dim A = dim B is a structural precondition for the
   canonical purification |ψ⟩ = Σ_i √λ_i |i⟩_A |i⟩_B (cf. Tomamichel,
   "A Framework for Non-Asymptotic Quantum Information Theory" (PhD
   thesis, arXiv:1203.2142), Chapter 3 — purification / Uhlmann material,
   Table 3.1 item (iii) and th:pd-uhl, Theorem 3.5). Without it, neither
   the mxvec construction nor the ptrace identity has the required
   dimensions. *)
Hypothesis dimAB : dim 'H[HL]_A = dim 'H[HL]_B.
Notation S_AB := (A :|: B).

Lemma h2mxZ_pur (S : {set L}) (c : C) (x : 'F[HL]_S) :
  h2mx (c *: x) = c *: h2mx x.
Proof.
  have Hlin := @h2mxP R ('H[HL]_S) ('H[HL]_S).
  move: (Hlin c x 0).
  rewrite addr0 h2mx0 addr0.
  by move=> ->.
Qed.

(* Purification existence: every sub-normalized PSD ρ on A has a
   purification on A⊗B s.t. Tr_B(purification) = ρ.
   Canonical construction (cf. Tomamichel, "A Framework for Non-Asymptotic
   Quantum Information Theory" (PhD thesis, arXiv:1203.2142), Chapter 3,
   Table 3.1 item (iii) Uhlmann's theorem) and the
   standard ansatz |ψ⟩ = (√ρ ⊗ I_B)|Φ⟩, where
     |Φ⟩ = Σ_i |e_i⟩_A ⊗ |e_{c i}⟩_B
   is the (un-normalized) maximally entangled vector obtained by pairing
   the computational basis of A with that of B via the dimAB cast. Then
     |ψ⟩⟨ψ| = (√ρ ⊗ I) |Φ⟩⟨Φ| (√ρ ⊗ I)
   and a direct computation gives Tr_B |ψ⟩⟨ψ| = √ρ · (√ρ)^† = ρ. *)

(* dim cast between 'H_A and 'H_B, via the caller-supplied dimAB. *)
(* dim_HA_HB *)
(* infra: no tex label — fundamental & reusable (mathcomp-style) *)
(* consumer: dim_HA_HB is used downstream by the BB84 secrecy proof. *)
Local Definition dim_HA_HB : dim 'H[HL]_A = dim 'H[HL]_B := dimAB.

(* Purification vector: |ψ⟩ = Σ_i (√ρ)|e_i⟩_A ⊗v |e_{c i}⟩_B, with c the
   dim cast between A and B. Equivalently |ψ⟩ = (√ρ ⊗ I_B)|Φ⁺⟩ for the
   maximally entangled |Φ⁺⟩ = Σ_i |e_i⟩_A ⊗v |e_{c i}⟩_B. *)
(* pur_vec *)
(* infra: no tex label — fundamental & reusable (mathcomp-style) *)
(* consumer: pur_vec is used downstream by the BB84 secrecy proof. *)
Local Definition pur_vec (rho : 'F[HL]_A) : 'H[HL]_S_AB :=
  \sum_(i : 'I_(dim 'H[HL]_A))
    tenv ((sqrtH rho) (eb i)) (eb (cast_ord dim_HA_HB i)).

(* purification *)
(* infra: no tex label — fundamental & reusable (mathcomp-style) *)
(* consumer: purification is used downstream by the BB84 secrecy proof. *)
Definition purification (rho : 'F[HL]_A) : 'F[HL]_S_AB :=
  [> pur_vec rho ; pur_vec rho <].

(* ================================================================== *)
(* Maximally entangled state γ_AB (Tomamichel's γ_{AC'} in 4-conv/2-minmax) *)
(* Uhlmann/Gram route.                *)
(* Defined as the (un-normalized) purification of the identity on A.   *)
(*   |γ⟩_{AB} = Σ_i |e_i⟩_A ⊗v |e_{c i}⟩_B                            *)
(* where c := cast_ord dim_HA_HB pairs A's basis with B's via the       *)
(* dimAB assumption. Its partial trace is the A-identity (unnormalized  *)
(* form), matching Tomamichel's γ_{AC'} which purifies the fully-mixed π_A  *)
(* up to the d_A normalization factor inherent in hmin/hmax defs.      *)
(* ================================================================== *)

(* Purification of the identity on A. *)
(* max_entangled *)
(* infra: no tex label — fundamental & reusable (mathcomp-style) *)
(* consumer: max_entangled is used downstream by the BB84 secrecy proof. *)
Definition max_entangled : 'F[HL]_S_AB :=
  purification (\1 : 'F[HL]_A).

(* max_entangled_ptrace and max_entangled_psd are the identity-purifier    *)
(* facts needed by entropy and EUR consumers.                             *)
(* max_entangled_ptrace *)
(* infra: no tex label — fundamental & reusable (mathcomp-style) *)
(* consumer: max_entangled_ptrace is used downstream by the BB84 secrecy proof. *)
(* path: utils:max_entangled_ptrace -> utils:gamma_state_ptrace -> *)
(*   entropy:minmax_dual -> entropy:smooth_iso_hmax -> *)
(*   entropy:entropy_data_proc -> *)
(*   bb84:bb84_secret *)
Lemma max_entangled_ptrace :
  ptrace_cast disAB max_entangled = (\1 : 'F[HL]_A).
Proof.
  have tens_cv_entry (dA dB : nat) (X : 'M[C]_(dA, 1)) (Y : 'cV[C]_dB)
      (r : 'I_dA) (s : 'I_dB) :
      (X *t Y) (mxtens_index (r, s)) 0 = X r 0 * Y s 0.
  {
    rewrite mxE mxtens_indexK /=.
    by apply: f_equal2; congr (_ _ _); apply/val_inj.
  }
  apply/h2mx_inj.
  rewrite (@h2mx_ptrace_cast_ptrace2 R L HL A B disAB).
  rewrite /max_entangled /purification outp.unlock mx2hK.
  set U := @tenv_mxU R L HL A B.
  pose M : 'cV[C]_(dim 'H[HL]_A * dim 'H[HL]_B) :=
    \sum_(i : 'I_(dim 'H[HL]_A))
      ((h2mx (sqrtH (\1 : 'F[HL]_A)) *m delta_mx i (0 : 'I_1))
        *t (delta_mx (cast_ord dim_HA_HB i) (0 : 'I_1)
             : 'cV_(dim 'H[HL]_B))).
  have Hpv : h2c (pur_vec (\1 : 'F[HL]_A)) = U *m M.
  {
    rewrite /pur_vec.
    rewrite raddf_sum /=.
    rewrite /M.
    rewrite mulmx_sumr.
    apply: eq_bigr=> i _.
    rewrite tenv_h2cE.
    have Hleft :
        h2c ((sqrtH (\1 : 'F[HL]_A)) (eb i)) =
        h2mx (sqrtH (\1 : 'F[HL]_A)) *m delta_mx i (0 : 'I_1).
    {
      rewrite applyfh.
      rewrite c2hK.
      by rewrite h2c_eb.
    }
    rewrite Hleft.
    by rewrite h2c_eb.
  }
  rewrite Hpv.
  have HUU : U^*t *m U = 1%:M.
  {
    move: (@tenv_mxU_adj_unitarymx R L HL A B disAB).
    by move/unitarymxK; rewrite adjmxK.
  }
  rewrite adjmxM !mulmxA HUU mul1mx.
  rewrite -(mulmxA _ U^*t U) HUU mulmx1.
  have Phrho : sqrtH (\1 : 'F[HL]_A) \is hermlf :=
    psdlf_herm (sqrtH_psd (@one_psdlf R L HL A)).
  have HsqRadj :
      (h2mx (sqrtH (\1 : 'F[HL]_A)))^*t =
      h2mx (sqrtH (\1 : 'F[HL]_A)).
  {
    rewrite -h2mx_adj.
    congr h2mx.
    by apply/hermlfP: Phrho.
  }
  have HsqR_sq :
      h2mx (sqrtH (\1 : 'F[HL]_A)) *m
      h2mx (sqrtH (\1 : 'F[HL]_A)) =
      h2mx (\1 : 'F[HL]_A).
  {
    by rewrite -h2mx_comp (sqrtHK (@one_psdlf R L HL A)).
  }
  have ptrace2E' : forall s t (B' : 'M[C]_(s * t)) r1 r2,
      (ptrace2 B') r1 r2 =
      \sum_l B' (mxtens_index (r1, l)) (mxtens_index (r2, l)).
  {
    move=> s t B' r1 r2.
    rewrite ptrace2E1 ptrace1E.
    by apply: eq_bigr=> l _; rewrite mxE !mxtens_indexK.
  }
  have col_select :
      forall (f : 'End('H[HL]_A)) (i : 'I_(dim 'H[HL]_A))
             (r : 'I_(dim 'H[HL]_A)),
        (h2mx f *m delta_mx i (0 : 'I_1)) r 0 = h2mx f r i.
  {
    move=> f i r.
    rewrite mxE (bigD1 i) //= big1 ?addr0.
    - by rewrite /delta_mx !mxE !eqxx mulr1.
    - move=> k /negPf nki.
      by rewrite /delta_mx !mxE nki /= mulr0.
  }
  have deltaB_entry :
      forall (i s : 'I_(dim 'H[HL]_B)),
        (delta_mx i (0 : 'I_1) : 'M[C]_(dim 'H[HL]_B, 1)) s 0 =
        (s == i)%:R.
  {
    move=> i s.
    by rewrite mxE eqxx andbT.
  }
  have Mentry :
      forall (r : 'I_(dim 'H[HL]_A)) (s : 'I_(dim 'H[HL]_B)),
        M (mxtens_index (r, s)) 0 =
        h2mx (sqrtH (\1 : 'F[HL]_A)) r (cast_ord (esym dim_HA_HB) s).
  {
    move=> r s.
    rewrite /M summxE.
    rewrite (bigD1 (cast_ord (esym dim_HA_HB) s)) //= big1 ?addr0; last first.
    {
      move=> k /eqP Hk.
      rewrite tens_cv_entry col_select deltaB_entry.
      have -> : (s == cast_ord dim_HA_HB k) = false.
      {
        apply/eqP => Hs.
        apply: Hk.
        by apply/val_inj; move: Hs => /(f_equal val)/= ->.
      }
      by rewrite /= mulr0.
    }
    rewrite tens_cv_entry col_select deltaB_entry.
    have -> : (s == cast_ord dim_HA_HB (cast_ord (esym dim_HA_HB) s)) = true.
      by apply/eqP/val_inj.
    by rewrite /= mulr1.
  }
  apply/matrixP=> i j.
  rewrite ptrace2E'.
  under eq_bigr => l _.
  {
    rewrite mxE big_ord1 mxE_adj Mentry [X in _ * (X)^*]Mentry.
    over.
  }
  have hcast_bij : {on [pred x | true], bijective (cast_ord dim_HA_HB)}.
  {
    exists (cast_ord (esym dim_HA_HB)).
    - move=> k _.
      by apply/val_inj.
    - move=> k _.
      by apply/val_inj.
  }
  rewrite (reindex (cast_ord dim_HA_HB) hcast_bij) /=.
  have hcastK : forall k,
      cast_ord (esym dim_HA_HB) (cast_ord dim_HA_HB k) = k.
  {
    move=> k.
    by apply/val_inj.
  }
  under eq_bigr => k _.
  {
    rewrite hcastK.
    over.
  }
  rewrite -HsqR_sq !mxE.
  apply: eq_bigr=> k _.
  congr (_ * _).
  by rewrite -mxE_adj HsqRadj.
Qed.

(* max_entangled_psd *)
(* infra: no tex label — fundamental & reusable (mathcomp-style) *)
(* consumer: max_entangled_psd is used downstream by the BB84 secrecy proof. *)
(* path: utils:max_entangled_psd -> utils:gamma_state_den1 -> *)
(*   entropy:minmax_dual -> entropy:smooth_iso_hmax -> *)
(*   entropy:entropy_data_proc -> *)
(*   bb84:bb84_secret *)
Lemma max_entangled_psd : max_entangled \is psdlf.
Proof.
  by rewrite /max_entangled /purification outp_psd.
Qed.

(* gamma_state *)
(* infra: no tex label — normalized fully entangled state helper bundle *)
Definition gamma_state : 'F[HL]_S_AB :=
  ((dim 'H[HL]_A)%:R^-1)%:C *: max_entangled.

(* gamma_state_ptrace *)
(* infra: no tex label — normalized fully entangled state helper bundle *)
(* path: utils:gamma_state_ptrace -> entropy:minmax_dual -> *)
(*   entropy:smooth_iso_hmax -> entropy:entropy_data_proc -> *)
(*   bb84:bb84_secret *)
Lemma gamma_state_ptrace :
  ptrace_cast disAB gamma_state =
  ((dim 'H[HL]_A)%:R^-1)%:C *: (\1 : 'F[HL]_A).
Proof.
  have Hme :
      castlf (setDU_r disAB, setDU_r disAB) (\Tr_(B) max_entangled) =
      (\1 : 'F[HL]_A).
  {
    move: max_entangled_ptrace.
    by rewrite /ptrace_cast /ptrace_cast_gen.
  }
  rewrite /gamma_state /ptrace_cast /ptrace_cast_gen.
  rewrite linearZ /= [castlf _ (_ *: _)]linearZ /=.
  by rewrite Hme.
Qed.

(* gamma_state_den1 *)
(* infra: no tex label — normalized fully entangled state helper bundle *)
(* path: utils:gamma_state_den1 -> entropy:minmax_dual -> *)
(*   entropy:smooth_iso_hmax -> entropy:entropy_data_proc -> *)
(*   bb84:bb84_secret *)
Lemma gamma_state_den1 : gamma_state \is den1lf.
Proof.
  have Htr_ptrace (f : 'F[HL]_S_AB) : \Tr (ptrace_cast disAB f) = \Tr f.
  {
    rewrite /ptrace_cast /ptrace_cast_gen castlf_trlfE.
    have /cptpP [_ /tpmapP Htp] := @ptraceso_qc R L HL B S_AB.
    exact: Htp.
  }
  apply/den1lfP; split.
  - rewrite /gamma_state.
    apply: psdlfZ.
    + by rewrite lecR invr_ge0 ler0n.
    + exact: max_entangled_psd.
  - rewrite -(Htr_ptrace gamma_state) gamma_state_ptrace.
    rewrite linearZ /= /lftrace h2mx1 mxtrace1.
    rewrite -natrC -rmorphM /=.
    by rewrite mulVf ?rmorph1 // pnatr_eq0 -lt0n dim_proper.
Qed.

(* gamma_state_rank1 *)
(* infra: no tex label — normalized fully entangled state helper bundle *)
(* path: utils:gamma_state_rank1 -> entropy:minmax_dual -> *)
(*   entropy:smooth_iso_hmax -> entropy:entropy_data_proc -> *)
(*   bb84:bb84_secret *)
Lemma gamma_state_rank1 : \Rank gamma_state = 1%N.
Proof.
  have HdimA_neq0 : (((dim 'H[HL]_A)%:R^-1)%:C : C) != 0.
  {
    by rewrite fmorph_eq0 invr_eq0 pnatr_eq0 -lt0n dim_proper.
  }
  have Hme_rank1 : \Rank max_entangled = 1%N.
  {
    have Htr_ptrace (f : 'F[HL]_S_AB) : \Tr (ptrace_cast disAB f) = \Tr f.
    {
      rewrite /ptrace_cast /ptrace_cast_gen castlf_trlfE.
      have /cptpP [_ /tpmapP Htp] := @ptraceso_qc R L HL B S_AB.
      exact: Htp.
    }
    rewrite /lfrank /max_entangled /purification outp.unlock mx2hK.
    set v := h2c (pur_vec (\1 : 'F[HL]_A)).
    have Hv_me : h2c (pur_vec (\1 : 'F[HL]_A)) *m
                 (h2c (pur_vec (\1 : 'F[HL]_A)))^*t =
                 v *m v^*t.
    {
      by rewrite /v.
    }
    apply/eqP; rewrite eqn_leq; apply/andP; split.
    - have H1 : (\rank (v *m v^*t) <= \rank v)%N by exact: mxrankM_maxl.
      have H2 : (\rank v <= 1)%N by exact: rank_leq_col.
      exact: (leq_trans H1 H2).
    - rewrite lt0n mxrank_eq0.
      apply/eqP => Hv0.
      have Hme0 : max_entangled = 0.
      {
        apply/h2mx_inj.
        by rewrite h2mx0 /max_entangled /purification outp.unlock mx2hK Hv_me Hv0.
      }
      have Htr_me : \Tr max_entangled = (dim 'H[HL]_A)%:R.
      {
        rewrite -(Htr_ptrace max_entangled) max_entangled_ptrace.
        by rewrite /lftrace h2mx1 mxtrace1.
      }
      move: Htr_me.
      rewrite Hme0 linear0.
      move=> Htr0.
      have Hdim_neq0 : ((dim 'H[HL]_A)%:R : C) != 0.
      {
        by rewrite pnatr_eq0 -lt0n dim_proper.
      }
      by move: Hdim_neq0; rewrite Htr0 eqxx.
  }
  have /eqmxP Hgamma_eqmx := eqmx_scale (h2mx max_entangled) HdimA_neq0.
  rewrite /lfrank /gamma_state h2mxZ_pur /= (eqmx_rank Hgamma_eqmx).
  exact: Hme_rank1.
Qed.

End Purification.

(* ================================================================== *)
(* Pure extensions of a normalized pure state factor as a tensor       *)
(* ================================================================== *)

Section PureExtensionSplit.
Variable (L : finType) (HL : L -> chsType) (A B C : {set L}).
Hypothesis disAB : [disjoint A & B].
Hypothesis disAB_C : [disjoint (A :|: B) & C].
Notation S_AB := (A :|: B).
Notation S_ABC0 := (S_AB :|: C).
Notation S_ABC := (A :|: B :|: C).

Local Definition eqABC : S_ABC0 = S_ABC.
Proof.
  apply/setP=> x.
  by rewrite /S_ABC0 /S_ABC !inE.
Defined.

(* pure_extension_split *)
(* infra: no tex label — “extensions of a pure state are product” *)
(* path: utils:pure_extension_split -> entropy:minmax_dual -> *)
(*   entropy:smooth_iso_hmax -> entropy:entropy_data_proc -> *)
(*   bb84:bb84_secret *)
Lemma pure_extension_split (rhoAB : 'F[HL]_S_AB) (thetaABC : 'F[HL]_S_ABC) :
  rhoAB \is den1lf ->
  \Rank rhoAB = 1%N ->
  thetaABC \is den1lf ->
  ptrace_cast disAB_C thetaABC = rhoAB ->
  exists tauC : 'F[HL]_C,
    tauC \is den1lf /\
    thetaABC =
      castlf (esym eqABC, esym eqABC)
        ((rhoAB \O tauC) : 'F[HL]_S_ABC0).
Proof.
  move=> HrhoAB_den HrhoAB_rank HthetaABC_den HthetaABC_ptrace.
  pose theta0 : 'F[HL]_S_ABC0 :=
    castlf (esym eqABC, esym eqABC) thetaABC.
  pose tauC : 'F[HL]_C := ptrace_castl disAB_C theta0.
  have Htheta0_psd : theta0 \is psdlf.
  {
    apply: castlf_psdlf.
    exact: den1lf_psd.
  }
  have Htheta0_tr : \Tr theta0 = 1.
  {
    rewrite /theta0 castlf_trlfE.
    by move/den1lfP: HthetaABC_den => [_ ->].
  }
  have HtauC_psd : tauC \is psdlf.
  {
    exact: ptrace_castl_psdlf.
  }
  have HtauC_tr : \Tr tauC = 1.
  {
    rewrite /tauC /ptrace_castl /ptrace_cast_gen castlf_trlfE.
    have /cptpP [_ /tpmapP Htp] :=
      @ptraceso_qc R L HL (A :|: B) S_ABC0.
    by rewrite Htp.
  }
  have HtauC_den : tauC \is den1lf.
  {
    by apply/den1lfP; split.
  }
  exists tauC; split.
  - exact: HtauC_den.
  - have eqABC_refl : eqABC = erefl S_ABC0.
    { by apply: eq_irrelevance. }
    rewrite eqABC_refl /=.
    rewrite castlf_id.
    have theta0_eq : theta0 = thetaABC.
    { by rewrite /theta0 eqABC_refl /= castlf_id. }
    rewrite -theta0_eq.
    have sdot_ten_eq : rhoAB \O tauC = rhoAB \⊗ tauC.
    { apply: to_Fnd_inj.
      by rewrite (sdotFT _ _ disAB_C) to_Fnd_tenE. }
    rewrite sdot_ten_eq.
    apply/h2mx_inj.
    rewrite h2mx_tenf.
    set U := @tenv_mxU R L HL S_AB C.
    pose tM : 'M[(@hermitian.C R)]_(dim 'H[HL]_S_AB * dim 'H[HL]_C) :=
      U^*t *m h2mx theta0 *m U.
    have HtM_psd : tM \is psdmx.
    { rewrite /tM.
      have Htheta0_psdmx : h2mx theta0 \is psdmx.
      { by move: Htheta0_psd; rewrite qualifE. }
      by apply: formV_psdmx. }
    have HptrM2 : ptrace2 tM = h2mx rhoAB.
    { rewrite /tM -HthetaABC_ptrace.
      have theta0_as_cast : theta0 = castlf (esym eqABC, esym eqABC) thetaABC.
      { by []. }
      have eqcast : ptrace_cast disAB_C thetaABC =
                    ptrace_cast disAB_C theta0.
      { by rewrite theta0_as_cast /ptrace_cast /ptrace_cast_gen
                  /= eqABC_refl /= castlf_id. }
      rewrite eqcast.
      by rewrite (@h2mx_ptrace_cast_ptrace2 R L HL S_AB C disAB_C). }
    have HUUt : U *m U^*t = 1%:M.
    { move: (@tenv_mxU_unitarymx R L HL S_AB C).
      move/unitarymxP=> HU.
      by rewrite -[U *m U^*t]/(U *m U^*t) HU. }
    have HUtU : U^*t *m U = 1%:M.
    { move: (@tenv_mxU_adj_unitarymx R L HL S_AB C disAB_C).
      by move/unitarymxK; rewrite adjmxK. }
    have HtrtM : \tr tM = 1.
    { rewrite /tM mxtrace_mulC mulmxA HUUt mul1mx.
      by move: Htheta0_tr; rewrite /lftrace. }
    have HrhoAB_psdmx : h2mx rhoAB \is psdmx.
    { have HrhoAB_psd : rhoAB \is psdlf := den1lf_psd HrhoAB_den.
      by move: HrhoAB_psd; rewrite qualifE. }
    have HrhoAB_rankmx : \rank (h2mx rhoAB) = 1%N.
    { by move: HrhoAB_rank; rewrite /lfrank. }
    have [v Hv] := psdmx_rank1_form HrhoAB_psdmx HrhoAB_rankmx.
    suff Hcore :
        h2mx theta0 = U *m (h2mx rhoAB *t h2mx tauC) *m U^*t.
    { exact: Hcore. }
    have reduce : tM = h2mx rhoAB *t h2mx tauC ->
                  h2mx theta0 = U *m (h2mx rhoAB *t h2mx tauC) *m U^*t.
    { move=> HtM_eq.
      have Hsandwich : h2mx theta0 = U *m tM *m U^*t.
      { rewrite /tM.
        rewrite !mulmxA HUUt mul1mx.
        by rewrite -!mulmxA HUUt mulmx1. }
      by rewrite Hsandwich HtM_eq. }
    apply: reduce.
    have HtrHrho : \tr (h2mx rhoAB) = 1.
    { have := HtrtM.
      rewrite (tr_ptrace2 tM) HptrM2 => <-.
      by []. }
    have HvvA : v^*t *m v = 1%:M.
    { apply/matrixP=> i j.
      rewrite !(ord1 i) !(ord1 j).
      rewrite -trace_mx11 mxtrace_mulC -Hv HtrHrho.
      by rewrite mxE eqxx /= mulr1n. }
    pose Q : 'M[(@hermitian.C R)]_(dim 'H[HL]_S_AB) := v *m v^*t.
    have HQ_eq : Q = h2mx rhoAB.
    { by rewrite /Q -Hv. }
    have HQ_adj : Q^*t = Q.
    { by rewrite /Q adjmxM adjmxK. }
    have HQ_idem : Q *m Q = Q.
    { rewrite /Q -!mulmxA.
      rewrite (mulmxA v^*t v v^*t) HvvA mul1mx //. }
    have HQv : Q *m v = v.
    { rewrite /Q -mulmxA.
      have -> : v^*t *m v = 1%:M by exact: HvvA.
      by rewrite mulmx1. }
    pose Pj : 'M[(@hermitian.C R)]_(dim 'H[HL]_S_AB) := 1%:M - Q.
    have HPj_adj : Pj^*t = Pj.
    { rewrite /Pj.
      by rewrite linearB /= adjmx1 HQ_adj. }
    have HPj_idem : Pj *m Pj = Pj.
    { rewrite /Pj mulmxBl mulmxBr mulmxBr mul1mx mulmx1.
      rewrite HQ_idem mul1mx.
      by rewrite subrr subr0. }
    have HPjv : Pj *m v = 0.
    { rewrite /Pj mulmxBl mul1mx HQv subrr //. }
    pose P1 : 'M[(@hermitian.C R)]_(dim 'H[HL]_S_AB * dim 'H[HL]_C) :=
      Pj *t 1%:M.
    have HP1_adj : P1^*t = P1.
    { by rewrite /P1 adjmx_tens adjmx1 HPj_adj. }
    have HP1_idem : P1 *m P1 = P1.
    { by rewrite /P1 tensmx_mul HPj_idem mulmx1. }
    pose S := P1 *m tM *m P1.
    have HS_psd : S \is psdmx.
    { rewrite /S.
      have -> : P1 *m tM *m P1 = P1 *m tM *m P1^*t
        by rewrite HP1_adj.
      exact: form_psdmx HtM_psd. }
    have HtrS : \tr S = 0.
    { rewrite /S.
      rewrite (mxtrace_mulC (P1 *m tM) P1).
      rewrite mulmxA HP1_idem.
      rewrite (mxtrace_mulC P1 tM).
      rewrite (tr_ptrace2 (tM *m P1)).
      rewrite /P1 ptrace2_mulmxI HptrM2.
      rewrite Hv.
      rewrite -mulmxA.
      have Hvt_Pj : v^*t *m Pj = 0.
      { have Hadj : (Pj *m v)^*t = 0 by rewrite HPjv raddf0.
        move: Hadj; rewrite adjmxM HPj_adj //. }
      rewrite Hvt_Pj mulmx0 linear0 //. }
    have HS_eq0 : S = 0.
    { apply/eqP.
      rewrite -(psdmx_trace_eq0 HS_psd).
      by apply/eqP. }
    pose sT := sqrtmx tM.
    have HsTsT : sT *m sT = tM by rewrite /sT sqrtmxK.
    have HsT_adj : sT^*t = sT.
    { have /hermmxP := sqrtmx_herm (psdmx_herm HtM_psd).
      by rewrite /sT. }
    pose K := P1 *m sT.
    have HKKt : K *m K^*t = 0.
    { rewrite /K adjmxM HsT_adj HP1_adj.
      rewrite -mulmxA (mulmxA sT sT P1) HsTsT mulmxA.
      by rewrite -/(P1 *m tM *m P1) -/S HS_eq0. }
    have HK0 : K = 0.
    { apply/matrixP=> i j.
      have HKKt_ii : (K *m K^*t) i i = 0 by rewrite HKKt mxE.
      have Hnneg : forall k' : 'I_(dim 'H[HL]_S_AB * dim 'H[HL]_C),
        true -> 0 <= K i k' * (K^*t) k' i.
      { move=> k' _.
        rewrite mxE_adj.
        by rewrite -normCK exprn_ge0. }
      move: HKKt_ii; rewrite mxE.
      move/(psumr_eq0P Hnneg) => Hzero.
      have Hterm_zero : K i j * (K^*t) j i = 0 := Hzero j isT.
      move: Hterm_zero; rewrite mxE_adj -normCK => Hsq.
      have Hknorm_eq : K i j = 0.
      { apply/eqP; rewrite -normr_eq0.
        by move/eqP: Hsq; rewrite expf_eq0 /=. }
      rewrite [in RHS]mxE.
      exact: Hknorm_eq. }
    have HP1sT : P1 *m sT = 0 by rewrite -/K HK0.
    have HP1tM : P1 *m tM = 0.
    { rewrite -HsTsT.
      rewrite mulmxA HP1sT mul0mx //. }
    have Htm_left : tM = (Q *t 1%:M) *m tM.
    { have : (1%:M : 'M_(dim 'H[HL]_S_AB * dim 'H[HL]_C)) *m tM = tM
        by rewrite mul1mx.
      rewrite -[1%:M in X in X *m _ = _](@tensmx11 _ _ _).
      have -> : (1%:M : 'M_(dim 'H[HL]_S_AB)) *t (1%:M : 'M_(dim 'H[HL]_C))
              = Q *t 1%:M + Pj *t 1%:M.
      { rewrite -linearDl /=.
        congr (_ *t _).
        by rewrite /Pj addrC subrK. }
      rewrite mulmxDl -/P1 HP1tM addr0.
      by move=> ->. }
    have HtM_herm : tM^*t = tM.
    { have /hermmxP := psdmx_herm HtM_psd.
      by []. }
    have Htm_right : tM = tM *m (Q *t 1%:M).
    { have HQ1_adj : (Q *t (1%:M : 'M[(@hermitian.C R)]_(dim 'H[HL]_C)))^*t
                   = Q *t 1%:M.
      { by rewrite adjmx_tens HQ_adj adjmx1. }
      have Htm_left_adj : tM^*t = ((Q *t 1%:M) *m tM)^*t.
      { by f_equal; exact: Htm_left. }
      rewrite HtM_herm in Htm_left_adj.
      rewrite adjmxM in Htm_left_adj.
      rewrite HQ1_adj in Htm_left_adj.
      rewrite HtM_herm in Htm_left_adj.
      exact: Htm_left_adj. }
    have Htm_sandwich : tM = (Q *t 1%:M) *m tM *m (Q *t 1%:M).
    { rewrite -mulmxA -Htm_right -Htm_left //. }
    rewrite -HQ_eq.
    have Hsand_entry :
      forall (a c : 'I_(dim 'H[HL]_S_AB)) (b d : 'I_(dim 'H[HL]_C)),
        tM (mxtens_index (a,b)) (mxtens_index (c,d))
        = \sum_e \sum_g
            Q a e * tM (mxtens_index (e,b)) (mxtens_index (g,d)) * Q g c.
    { move=> a c b d.
      rewrite {1}Htm_sandwich.
      rewrite tensmxE_mid.
      transitivity
        (\sum_g
          ((Q *t 1%:M) *m tM) (mxtens_index (a,b)) (mxtens_index (g,d)) *
          Q g c).
      { apply: eq_bigr => g _.
        have HQt1E : forall (x y : 'I_(dim 'H[HL]_S_AB)) (h k : 'I_(dim 'H[HL]_C)),
          (Q *t (1%:M : 'M[(@hermitian.C R)]_(dim 'H[HL]_C)))
            (mxtens_index (x,h)) (mxtens_index (y,k))
          = Q x y * (h == k)%:R.
        { move=> x y h k.
          rewrite tensmxE.
          have -> : (1%:M : 'M[(@hermitian.C R)]_(dim 'H[HL]_C)) h k
                  = (h == k)%:R.
          { rewrite mxE.
            by case: (h == k); rewrite ?mulr1n ?mulr0n. }
          by []. }
        rewrite (bigD1 d) //=.
        rewrite HQt1E eqxx mulr1.
        rewrite big1 ?addr0 //.
        move=> h Hh.
        rewrite HQt1E.
        have /negPf -> : h != d by [].
        by rewrite mulr0 mulr0. }
      transitivity
        (\sum_g
          (\sum_e \sum_f
            (Q a e * (1%:M : 'M[(@hermitian.C R)]_(dim 'H[HL]_C)) b f) *
            tM (mxtens_index (e,f)) (mxtens_index (g,d))) * Q g c).
      { apply: eq_bigr => g _.
        congr (_ * _).
        rewrite tensmxE_mid.
        apply: eq_bigr => e _.
        apply: eq_bigr => f _.
        by rewrite tensmxE. }
      transitivity
        (\sum_g
          (\sum_e Q a e *
                  tM (mxtens_index (e,b)) (mxtens_index (g,d))) * Q g c).
      { apply: eq_bigr => g _.
        congr (_ * _).
        apply: eq_bigr => e _.
        have H1E : forall h k : 'I_(dim 'H[HL]_C),
          (1%:M : 'M[(@hermitian.C R)]_(dim 'H[HL]_C)) h k = (h == k)%:R.
        { move=> h k; rewrite mxE.
          by case: (h == k); rewrite ?mulr1n ?mulr0n. }
        rewrite (bigD1 b) //= H1E eqxx mulr1.
        rewrite big1 ?addr0 //.
        move=> f Hf.
        rewrite H1E.
        have /negPf -> : b != f by rewrite eq_sym.
        by rewrite mulr0 mul0r. }
      under eq_bigr do rewrite mulr_suml.
      rewrite exchange_big /=.
      apply: eq_bigr => e _.
      by apply: eq_bigr => g _. }
    have HQ_v : forall (a c : 'I_(dim 'H[HL]_S_AB)),
      Q a c = v a 0 * (v c 0)^*.
    { move=> a c.
      rewrite /Q mxE big_ord1.
      by rewrite mxE_adj. }
    pose Y (b d : 'I_(dim 'H[HL]_C)) : @hermitian.C R :=
      \sum_e \sum_g (v e 0)^* * tM (mxtens_index (e,b)) (mxtens_index (g,d))
                              * v g 0.
    have Htm_Y : forall a b c d,
      tM (mxtens_index (a,b)) (mxtens_index (c,d)) =
        v a 0 * (v c 0)^* * Y b d.
    { move=> a b c d.
      rewrite Hsand_entry /Y.
      rewrite mulr_sumr.
      apply: eq_bigr => e _.
      rewrite mulr_sumr.
      apply: eq_bigr => g _.
      rewrite HQ_v HQ_v.
      set xa := v a 0.
      set xb := (v e 0)^*.
      set xc := v g 0.
      set xd := (v c 0)^*.
      set xt := tM _ _.
      rewrite -!mulrA.
      congr (_ * _).
      rewrite mulrA mulrA.
      rewrite mulrC.
      congr (_ * _).
      by rewrite mulrA. }
    have HsumDiag_Y : forall b d,
      \sum_a tM (mxtens_index (a,b)) (mxtens_index (a,d)) = Y b d.
    { move=> b d.
      under eq_bigr => a _.
        rewrite Htm_Y.
      over.
      rewrite -mulr_suml.
      have HvtvE : (v^*t *m v) (0 : 'I_1) (0 : 'I_1) = 1.
      { by rewrite HvvA mxE eqxx. }
      have Hsum_unit : \sum_a v a 0 * (v a 0)^* = 1.
      { rewrite -HvtvE mxE.
        apply: eq_bigr => a _.
        by rewrite mxE_adj mulrC. }
      by rewrite Hsum_unit mul1r. }
    have HY_ptr1 : forall b d, Y b d = ptrace1 tM b d.
    { move=> b d.
      rewrite -HsumDiag_Y.
      by rewrite ptrace1E. }
    have HtM_Qptr1 : tM = Q *t (ptrace1 tM).
    { apply/matrixP => i j.
      case: (mxtens_indexP i) => a b.
      case: (mxtens_indexP j) => c d.
      rewrite tensmxE.
      rewrite Htm_Y.
      rewrite -HY_ptr1.
      by rewrite HQ_v -mulrA. }
    have HtauC_ptr1 : h2mx tauC = ptrace1 tM.
    { apply/matrixP=> i j.
      have Hlhs :
        h2mx tauC i j =
        \sum_(k : 'Idx[HL]_(S_ABC0 :&: S_AB))
          [< deltav (idxU k (castidx (esym (setDU_l disAB_C)) (n2i i))) ;
             castlf (esym (setID S_ABC0 S_AB), esym (setID S_ABC0 S_AB)) theta0
               (deltav (idxU k (castidx (esym (setDU_l disAB_C)) (n2i j)))) >].
      { rewrite /tauC /ptrace_castl /ptrace_cast_gen h2mx_dec.
        have eb_dv : forall (x : 'I_(dim 'H[HL]_C)),
          eb x = deltav (n2i x) :> 'H[HL]_C.
        { by move=> x; rewrite deltav.unlock n2iK. }
        rewrite !eb_dv.
        rewrite castlfE casths_dotr !deltav_cast.
        set a1 := castidx _ (n2i i).
        set a2 := castidx _ (n2i j).
        rewrite /ptraceso {1}/fun_of_superof/= lfunE/=.
        rewrite ptraceso_fun.unlock.
        rewrite sum_lfunE dotp_sumr; apply: eq_bigr => k _.
        rewrite sum_lfunE dotp_sumr.
        under eq_bigr => i0 _.
          rewrite sum_lfunE dotp_sumr.
          under eq_bigr => j0 _.
            rewrite scale_lfunE outpE dotpZr dotpZr dv_dot dv_dot.
            over.
          over.
        simpl.
        under eq_bigr => i0 _.
          rewrite (bigD1 a2)//= eqxx mul1r big1 ?addr0.
          2: by move=> j0 /negPf ->; rewrite mul0r mulr0.
          over.
        simpl.
        rewrite (bigD1 a1)//= eqxx mulr1 big1 ?addr0//.
        by move=> i0 /negPf ni0; rewrite [a1 == i0]eq_sym ni0 mulr0. }
      have Hrhs :
        ptrace1 tM i j =
        \sum_(k : 'I_(dim 'H[HL]_S_AB))
          [< deltav (idxU (n2i k) (n2i i)) ;
             theta0 (deltav (idxU (n2i k) (n2i j))) >].
      { rewrite ptrace1E.
        apply: eq_bigr => k _.
        rewrite /tM.
        rewrite mxE (bigD1 (tenv_indexl (mxtens_index (k, j))))//= big1 ?addr0.
        2: {
          move=> q Hq.
          rewrite !mxE /= (can2_eq (@tenv_indexrK R L HL S_AB C) (tenv_indexlK disAB_C)).
          by rewrite (negPf Hq) !mulr0.
        }
        rewrite mxE (bigD1 (tenv_indexl (mxtens_index (k, i))))//= big1 ?addr0.
        2: {
          move=> p Hp.
          rewrite adjmxE !mxE.
          rewrite (can2_eq (@tenv_indexrK R L HL S_AB C) (tenv_indexlK disAB_C)).
          by rewrite (negPf Hp) conjC0 !mul0r.
        }
        rewrite adjmxE !mxE.
        rewrite (tenv_indexlK disAB_C) (tenv_indexlK disAB_C) !eqxx !mulr1 conjC1.
        rewrite mul1r /tenv_indexl !mxtens_indexK/=.
        rewrite h2mx_dec.
        have eb_dv : forall S0 (x : 'Idx[HL]_S0),
          eb (i2n x) = deltav x :> 'H[HL]_S0.
        { by move=> S0 x; rewrite deltav.unlock. }
        by rewrite !eb_dv. }
      rewrite Hlhs Hrhs.
      have eqIA : S_ABC0 :&: S_AB = S_AB.
      { by have /finset.setIidPr-> := @finset.subsetUl _ S_AB C. }
      rewrite (reindex (fun k : 'I_(dim 'H[HL]_S_AB) =>
        castidx (esym eqIA) (n2i k))) /=.
      2: {
        exists (fun k : 'Idx[HL]_(S_ABC0 :&: S_AB) =>
          i2n (castidx eqIA k)) => k _.
        - by rewrite castidx_comp (eq_irrelevance (etrans _ _) (erefl _)) castidx_id n2iK.
        - by rewrite i2nK castidx_comp (eq_irrelevance (etrans _ _) (erefl _)) castidx_id.
      }
      apply: eq_bigr => k _.
      rewrite castlfE casths_dotr !deltav_cast esymK.
      have bridge :
        forall (k0 : 'I_(dim 'H[HL]_S_AB))
               (x : 'I_(dim 'H[HL]_C)),
          castidx (setID S_ABC0 S_AB)
            (idxU (castidx (esym eqIA) (n2i k0))
                  (castidx (esym (setDU_l disAB_C)) (n2i x)))
          = idxU (n2i k0) (n2i x).
      { move=> k0 x.
        apply/idxP => y.
        rewrite castidx_app /= idxE.
        have Hy_in : val y \in S_ABC0 by case: y => /= ?.
        case: eqP => HA.
        - rewrite castidx_app /=.
          have HA_in : val y \in S_AB by move/setIP: HA => [].
          have HnC : (val y \in C) = false.
            apply/negP => HC'.
            move/disjointP: disAB_C => /(_ _ HA_in).
            by rewrite HC'.
          rewrite idxE.
          case: eqP => HSAB; last by case: (HSAB HA_in).
          exact: n2i_exist_irr.
        - rewrite castidx_app /=.
          have HnSAB : (val y \in S_AB) = false.
            by apply/negP => HSAB; apply: HA; rewrite inE Hy_in HSAB.
          rewrite idxE.
          case: eqP => HSAB; first by rewrite HSAB in HnSAB.
          exact: n2i_exist_irr. }
      by rewrite !bridge. }
    by rewrite HtM_Qptr1 HtauC_ptr1.
Qed.

End PureExtensionSplit.

(* ================================================================== *)
(* Matrix-level purification existence: every sub-normalised rho_A      *)
(* has a rank-1 extension rho_AD on a register D with dim D ≥ dim A.   *)
(* Ported from CoqQ-bb84 (utils/pur.v:183).                            *)
(* tex: Tomamichel, A Framework for Non-Asymptotic QIT (arXiv:1203.2142), Sec. 2.2 (purification of a sub-normalised state).        *)
(* Consumer: eur/prop.v.                                               *)
(* ================================================================== *)

Section PurificationMxExists.

(* purification_mx_exists *)
(* infra: no tex label — fundamental & reusable (mathcomp-style) *)
(* consumer: purification_mx_exists is used downstream by the BB84 secrecy proof. *)
(* path: utils:purification_mx_exists -> utils:gfid_cast_mx -> *)
(*   entropy:entropy_data_proc -> *)
(*   bb84:bb84_secret *)
Lemma purification_mx_exists (na nd : nat) (rhoA : 'M[C]_na) :
  rhoA \is denmx -> rhoA != 0 ->
  (na <= nd)%N ->
  exists rhoAD : 'M[C]_(na * nd),
    rhoAD \is denmx /\
    ptrace2 rhoAD = rhoA /\ \rank rhoAD = 1%N.
Proof.
  move=> Hden Hne Hle.
  have Hpsd : rhoA \is psdmx by apply: denmx_psd.
  have [B HB] := psdmx_form Hpsd.
  pose Apad : 'M[C]_(na, na + (nd - na)) :=
    row_mx B (0 : 'M[C]_(na, nd - na)).
  pose A : 'M[C]_(na, nd) :=
    castmx (erefl na, subnKC Hle) Apad.
  have HApad_eq : Apad *m Apad^*t = rhoA.
    rewrite /Apad adjmxE tr_row_mx trmx0 map_col_mx map_mx0 -adjmxE.
    by rewrite mul_row_col mul0mx addr0 -HB.
  have HA_eq : A *m A^*t = rhoA.
    rewrite /A.
    have Hadj : (castmx (erefl na, subnKC Hle) Apad)^*t
              = castmx (subnKC Hle, erefl na) Apad^*t
      by rewrite -(adjmx_castV (subnKC Hle, erefl na)).
    rewrite Hadj mcextra.castmx_mul castmx_id.
    exact: HApad_eq.
  pose v : 'cV[C]_(na * nd) := ((mxvec A)^T)%R.
  have Hvm : vec_mx ((v^T)%R) = A by rewrite /v trmxK mxvecK.
  have Hptrace : ptrace2 (v *m v^*t) = rhoA
    by rewrite ptrace2_outerM Hvm HA_eq.
  exists (v *m v^*t); split; last split.
  - apply/denmxP; split; first exact: form_psd.
    rewrite tr_ptrace2 Hptrace.
    by move/denmxP: Hden => [_ Htr].
  - exact: Hptrace.
  - apply/eqP; rewrite eqn_leq; apply/andP; split.
    + have H1 : (\rank (v *m v^*t) <= \rank v)%N by exact: mxrankM_maxl.
      have H2 : (\rank v <= 1)%N by exact: rank_leq_col.
      exact: (leq_trans H1 H2).
    + rewrite lt0n mxrank_eq0.
      apply/eqP => Hvv0.
      have Hrho0 : rhoA = 0 by rewrite -Hptrace Hvv0 linear0.
      by move/eqP: Hne; rewrite Hrho0.
Qed.

End PurificationMxExists.

(* ================================================================== *)
(* Uhlmann's theorem                                                    *)
(* ================================================================== *)

(* ================================================================== *)
(* Set-level normalized purification with an ancilla                   *)
(* ================================================================== *)

Section PurExistsDen1.
Variable (L : finType) (HL : L -> chsType) (S T : {set L}).
Hypothesis disST : [disjoint S & T].

(* pur_exists_den1 *)
(* infra: no tex label — fundamental normalized purification utility. *)
(* math: every normalized state on S has a normalized pure extension  *)
(*       on S ∪ T when T has enough dimension.                        *)
(* path: utils:pur_exists_den1 -> entropy:minmax_dual -> *)
(*   entropy:smooth_iso_hmax -> entropy:entropy_data_proc -> *)
(*   bb84:bb84_secret *)
Lemma pur_exists_den1 (rhoS : 'F[HL]_S) :
  (dim 'H[HL]_S <= dim 'H[HL]_T)%N ->
  rhoS \is den1lf ->
  exists rhoST : 'F[HL]_(S :|: T),
    rhoST \is den1lf /\
    \Rank rhoST = 1%N /\
    ptrace_cast disST rhoST = rhoS.
Proof.
  move=> HdimT HrhoS_den1.
  pose sigma := h2mx rhoS.
  have Hsigma_den1 : sigma \is den1mx
    by move: HrhoS_den1; rewrite qualifE.
  have Hsigma_den : sigma \is denmx := den1mx_den Hsigma_den1.
  have Hsigma_nz : sigma != 0.
  { apply/eqP=> Hsigma0.
    by move/den1mxP: Hsigma_den1 => [_ /eqP];
      rewrite Hsigma0 linear0 => /eqP; rewrite eq_sym oner_eq0. }
  have Hsigma_rank : (\rank sigma <= dim 'H[HL]_T)%N.
  { exact: leq_trans (rank_leq_row _) HdimT. }
  have [theta0 [Htheta_den [Htheta_rank Htheta_ptr]]] :=
    purification_exists_in_dim Hsigma_den Hsigma_nz Hsigma_rank.
  pose U := @tenv_mxU R L HL S T.
  have HU : U \is unitarymx := tenv_mxU_unitarymx _ _.
  have HUadj : U^*t \is unitarymx := tenv_mxU_adj_unitarymx disST.
  have Uadj_mul_U : U^*t *m U = 1%:M.
  { by have := unitarymxK HUadj; rewrite adjmxK. }
  pose rhoST : 'F[HL]_(S :|: T) := mx2h (U *m theta0 *m U^*t).
  have HrhoST_h2mx : h2mx rhoST = U *m theta0 *m U^*t
    by rewrite /rhoST mx2hK.
  have Htheta_psd : theta0 \is psdmx := denmx_psd Htheta_den.
  have HrhoST_mx_psd : h2mx rhoST \is psdmx.
  { by rewrite HrhoST_h2mx; exact: psdmx_bimap_closed_gen. }
  have HrhoST_psd : rhoST \is psdlf by rewrite qualifE HrhoST_mx_psd.
  have Htheta_tr : \tr theta0 = \tr sigma.
  { by rewrite -Htheta_ptr -tr_ptrace2. }
  have HrhoST_tr1 : \Tr rhoST = 1.
  { rewrite /lftrace HrhoST_h2mx mxtrace_mulC mulmxA Uadj_mul_U mul1mx.
    move/den1mxP: Hsigma_den1 => [_ /eqP Hsigma_tr1].
    by rewrite Htheta_tr Hsigma_tr1. }
  have HrhoST_den1 : rhoST \is den1lf
    by apply/den1lfP; split.
  have HrhoST_rank : \Rank rhoST = 1%N.
  { rewrite /lfrank HrhoST_h2mx.
    rewrite (mxrank_mulmxU _ HUadj).
    by rewrite -[U]adjmxK (mxrank_mulUCmx _ HUadj) Htheta_rank. }
  have HrhoST_ptr : ptrace_cast disST rhoST = rhoS.
  { apply/h2mx_inj.
    rewrite (h2mx_ptrace_cast_ptrace2 disST rhoST).
    rewrite HrhoST_h2mx -/U.
    have -> : U^*t *m (U *m theta0 *m U^*t) *m U = theta0.
    { by rewrite !mulmxA Uadj_mul_U mul1mx -mulmxA Uadj_mul_U mulmx1. }
    exact: Htheta_ptr. }
  exists rhoST; do !split=> //.
Qed.

End PurExistsDen1.

(* ================================================================== *)
(* Labelled-level lift of purification_exists_in_dim.                  *)
(* Given disjoint singleton labels A, B and a fresh label C0 disjoint  *)
(* from both, with dim 'H_(S_AB) <= dim 'H_[C0], every nonzero          *)
(* sub-normalized rhoAB on S_AB admits a rank<=1 sub-normalized         *)
(* purification rhoABC on S_AB ∪ [C0] whose marginal on S_AB is rhoAB. *)
(* ================================================================== *)

Section PurificationExistsLf.
Variable (L : finType) (HL : L -> chsType) (A B C0 : {set L}).
Hypothesis disAC : [disjoint A & C0].
Hypothesis disBC : [disjoint B & C0].
Notation S_AB := (A :|: B).

(* path: utils:disAB_C -> entropy:entropy_data_proc -> *)
(*   bb84:bb84_secret *)
Local Lemma disAB_C : [disjoint S_AB & C0].
Proof.
  by rewrite disjointUX disAC disBC.
Qed.

(* purification_exists_with_ancilla *)
(* infra: no tex label — fundamental & reusable (mathcomp-style)       *)
(* consumer: purification_exists_with_ancilla is used downstream by the BB84 secrecy proof. *)
(* chain). Lift of utils/mx/prop.v:purification_exists_in_dim.         *)
(* path: utils:purification_exists_with_ancilla -> utils:disAB_C -> *)
(*   entropy:entropy_data_proc -> *)
(*   bb84:bb84_secret *)
Lemma purification_exists_with_ancilla
    (rhoAB : 'F[HL]_S_AB)
    (dim_C0_enough : (dim 'H[HL]_S_AB <= dim 'H[HL]_C0)%N) :
  rhoAB \is denlf ->
  rhoAB != 0 ->
  exists rhoABC : 'F[HL]_(S_AB :|: C0),
    rhoABC \is denlf /\
    (\Rank rhoABC <= 1)%N /\
    ptrace_cast disAB_C rhoABC = rhoAB.
Proof.
  move=> HrhoAB_den HrhoAB_nz.
  (* Matrix-level setup. *)
  pose sigma_A : 'M[C]_(dim 'H[HL]_S_AB) := h2mx rhoAB.
  have Hsigma_den : sigma_A \is denmx by move: HrhoAB_den; rewrite qualifE.
  have Hsigma_nz : sigma_A != 0.
  { apply: contra HrhoAB_nz => /eqP Hsig0.
    apply/eqP/h2mx_inj.
    by rewrite -/sigma_A Hsig0 h2mx0. }
  have Hsigma_rank : (\rank sigma_A <= dim 'H[HL]_C0)%N.
  { exact: leq_trans (rank_leq_row _) dim_C0_enough. }
  (* Apply matrix-level purification existence. *)
  have [theta0 [Htheta_den [Htheta_rank Htheta_ptr]]] :=
    purification_exists_in_dim Hsigma_den Hsigma_nz Hsigma_rank.
  (* Lift via U = tenv_mxU. *)
  pose U := @tenv_mxU R L HL S_AB C0.
  have HU : U \is unitarymx := tenv_mxU_unitarymx _ _.
  have HUadj : U^*t \is unitarymx := tenv_mxU_adj_unitarymx disAB_C.
  have Uadj_mul_U : U^*t *m U = 1%:M.
  { by have := unitarymxK HUadj; rewrite adjmxK. }
  pose rhoABC : 'F[HL]_(S_AB :|: C0) := mx2h (U *m theta0 *m U^*t).
  have HrhoABC_h2mx : h2mx rhoABC = U *m theta0 *m U^*t.
  { by rewrite /rhoABC mx2hK. }
  have Htheta_psd : theta0 \is psdmx by move/denmxP: Htheta_den => [].
  have HrhoABC_mx_psd : h2mx rhoABC \is psdmx.
  { by rewrite HrhoABC_h2mx; exact: psdmx_bimap_closed_gen. }
  have HrhoABC_psd : rhoABC \is psdlf by rewrite qualifE HrhoABC_mx_psd.
  (* Trace ≤ 1 lifts from theta0. *)
  have HrhoABC_tr : \tr (h2mx rhoABC) = \tr theta0.
  { rewrite HrhoABC_h2mx mxtrace_mulC mulmxA Uadj_mul_U mul1mx //. }
  have HrhoABC_tr_le1 : \tr (h2mx rhoABC) <= 1.
  { rewrite HrhoABC_tr.
    by have /denmxP [_] := Htheta_den. }
  have HrhoABC_den : rhoABC \is denlf.
  { rewrite qualifE; apply/denmxP; split.
    - exact: HrhoABC_mx_psd.
    - exact: HrhoABC_tr_le1. }
  (* Rank lifts from theta0. *)
  have HrhoABC_rank : (\Rank rhoABC <= 1)%N.
  { rewrite /lfrank HrhoABC_h2mx.
    rewrite (mxrank_mulmxU _ HUadj).
    rewrite -[U]adjmxK (mxrank_mulUCmx _ HUadj).
    by rewrite Htheta_rank. }
  (* ptrace_cast identity via h2mx_ptrace_cast_ptrace2 bridge. *)
  have HrhoABC_ptr : ptrace_cast disAB_C rhoABC = rhoAB.
  { apply/h2mx_inj.
    rewrite (h2mx_ptrace_cast_ptrace2 disAB_C rhoABC).
    rewrite HrhoABC_h2mx -/U.
    have -> : U^*t *m (U *m theta0 *m U^*t) *m U
            = theta0.
    { by rewrite !mulmxA Uadj_mul_U mul1mx -mulmxA Uadj_mul_U mulmx1. }
    exact: Htheta_ptr. }
  exists rhoABC; do !split=> //.
Qed.

(* pur_exists_den1_ancilla *)
(* infra: no tex label — normalized variant of ancilla purification. *)
(* Consumers: minmax_dual and smooth/DPI purification bridges.        *)
(* path: utils:pur_exists_den1_ancilla -> entropy:minmax_dual -> *)
(*   entropy:smooth_iso_hmax -> entropy:entropy_data_proc -> *)
(*   bb84:bb84_secret *)
Lemma pur_exists_den1_ancilla
    (rhoAB : 'F[HL]_S_AB)
    (dim_C0_enough : (dim 'H[HL]_S_AB <= dim 'H[HL]_C0)%N) :
  rhoAB \is den1lf ->
  exists rhoABC : 'F[HL]_(S_AB :|: C0),
    rhoABC \is den1lf /\
    \Rank rhoABC = 1%N /\
    ptrace_cast disAB_C rhoABC = rhoAB.
Proof.
  move=> HrhoAB_den1.
  have HrhoAB_nz : rhoAB != 0.
  { apply/eqP=> Hrho0.
    move: (den1lf_trlf HrhoAB_den1).
    rewrite Hrho0 linear0 => H01.
    move: (@oner_eq0 C).
    by rewrite -H01 eqxx. }
  have [rhoABC [HrhoABC_den [HrhoABC_rank_le Hptr]]] :=
    purification_exists_with_ancilla dim_C0_enough
      (den1lf_den HrhoAB_den1) HrhoAB_nz.
  have Htr_eq : \Tr rhoABC = \Tr rhoAB.
  { rewrite -Hptr /ptrace_cast /ptrace_cast_gen castlf_trlfE.
    have /cptpP [_ /tpmapP Htp] :=
      @ptraceso_qc R L HL C0 (S_AB :|: C0).
    by rewrite Htp. }
  have HrhoABC_den1 : rhoABC \is den1lf.
  { apply/den1lfP; split.
    - by move/denlfP: HrhoABC_den => [].
    - by rewrite Htr_eq (den1lf_trlf HrhoAB_den1). }
  have HrhoABC_nz : rhoABC != 0.
  { apply/eqP=> HrhoABC0.
    move: (den1lf_trlf HrhoABC_den1).
    rewrite HrhoABC0 linear0 => H01.
    move: (@oner_eq0 C).
    by rewrite -H01 eqxx. }
  have HrhoABC_rank : \Rank rhoABC = 1%N.
  { have Hrank_gt0 : (0 < \Rank rhoABC)%N.
    { rewrite lt0n /lfrank mxrank_eq0.
      apply/eqP=> Hmx0.
      have H0 : rhoABC = 0 by apply/h2mx_inj; rewrite Hmx0 h2mx0.
      by move/eqP: HrhoABC_nz; apply. }
    by apply/eqP; rewrite eqn_leq HrhoABC_rank_le Hrank_gt0. }
  exists rhoABC; do !split=> //.
Qed.

End PurificationExistsLf.

End FvqkdReal.
