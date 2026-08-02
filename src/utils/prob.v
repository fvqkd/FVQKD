(* -------------------------------------------------------------------- *)
(* prob.v — Probability distributions and Serfling bound                *)
(* -------------------------------------------------------------------- *)
(* Module: utils.prob                                     *)
(* TeX source: none (library utility)                                   *)
(* TeX labels: none                                                      *)
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
From mathcomp.analysis Require Import sequences exp ereal derive convex realfun.
From mathcomp.real_closed Require Import mxtens.
Require Import mathcomp.algebra.archimedean.
Import numFieldTopology.Exports.
From quantum Require Import mcextra mcaextra notation hermitian quantum
  cpo mxpred extnum ctopology svd mxnorm hspace majorization.

Import Order.TTheory GRing.Theory Num.Theory Num.Def MxLownerOrder.
Import VectorInternalTheory.

(* --- FVQKD imports --- *)
From utils Require Import arith bitstr.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Open Scope ring_scope.

Section FvqkdReal.
Variable R : realType.
Notation C := (@hermitian.C R).
Notation chsType := (@chsType R).

(* ================================================================== *)
(* Bayes' Theorem and basic probability                                 *)
(* ================================================================== *)

(* Pr_event *)
(* infra: no tex label — fundamental & reusable (mathcomp-style) *)
(* consumer: Pr_event is used downstream by the BB84 secrecy proof. *)
Definition Pr_event {T : finType} (mu : T -> R) (A : {set T}) : R :=
  \sum_(t in A) mu t.

(* Pr_cond *)
(* infra: no tex label — fundamental & reusable (mathcomp-style) *)
(* consumer: Pr_cond is used downstream by the BB84 secrecy proof. *)
Definition Pr_cond {T : finType} (mu : T -> R) (A B : {set T}) : R :=
  if Pr_event mu B == 0 then 0
  else Pr_event mu (A :&: B) / Pr_event mu B.

Definition uniform_fin_mu {T : finType} (_ : T) : R :=
  (#|{: T}|%:R)^-1.

(* bayes_theorem *)
(* infra: no tex label — fundamental & reusable (mathcomp-style) *)
(* consumer: bayes_theorem is used downstream by the BB84 secrecy proof. *)
(* path: utils:bayes_theorem -> bb84:stat -> bb84:bb84_secret *)
Lemma bayes_theorem {T : finType} (mu : T -> R) (A B : {set T}) :
  Pr_event mu B != 0 ->
  Pr_event mu (A :&: B) = Pr_cond mu A B * Pr_event mu B.
Proof.
  move=> HB.
  rewrite /Pr_cond (negbTE HB).
  by rewrite mulrVK ?unitfE.
Qed.

(* Any event has probability at most one under a nonnegative mass function
   of total mass one. *)
(* Pr_event_le1 *)
(* infra: no tex label — fundamental & reusable classical probability. *)
(* path: utils:Pr_event_le1 -> bb84:bb84_secret *)
Lemma Pr_event_le1 {T : finType} (mu : T -> R) (A : {set T}) :
  (forall t, 0 <= mu t) ->
  \sum_(t : T) mu t = 1 ->
  Pr_event mu A <= 1.
Proof.
  move=> Hmu_ge0 Hmu_sum1.
  rewrite /Pr_event -Hmu_sum1.
  rewrite [X in _ <= X](bigID (mem A)) /=.
  rewrite -[leLHS]addr0 lerD2l.
  by apply: sumr_ge0 => t _; exact: Hmu_ge0.
Qed.

Lemma Pr_event_cap_le {T : finType} (mu : T -> R) (A B : {set T}) :
  (forall t, 0 <= mu t) ->
  Pr_event mu (A :&: B) <= Pr_event mu A.
Proof.
  move=> Hmu_ge0.
  rewrite /Pr_event.
  have HcapE :
      \sum_(t in A :&: B) mu t = \sum_(t in A | t \in B) mu t.
  {
    apply: eq_bigl => t.
    by rewrite !inE.
  }
  rewrite HcapE.
  rewrite [X in _ <= X](bigID (mem B)) /=.
  rewrite -[leLHS]addr0 lerD2l.
  by apply: sumr_ge0 => t _; exact: Hmu_ge0.
Qed.

Fact Pr_cond_le_inter_div {T : finType} (mu : T -> R)
    (A B : {set T}) (eps : R) :
  0 < Pr_event mu B ->
  Pr_event mu (A :&: B) <= eps ->
  Pr_cond mu A B <= eps / Pr_event mu B.
Proof.
  move=> HB_pos Hinter_le.
  have HB_nz : Pr_event mu B != 0 := lt0r_neq0 HB_pos.
  rewrite /Pr_cond (negbTE HB_nz).
  rewrite ler_pdivrMr //.
  apply: le_trans Hinter_le _.
  by rewrite divrK ?unitfE.
Qed.

Fact Pr_cond_le_event_div {T : finType} (mu : T -> R)
    (A B : {set T}) (eps : R) :
  (forall t, 0 <= mu t) ->
  0 < Pr_event mu B ->
  Pr_event mu A <= eps ->
  Pr_cond mu A B <= eps / Pr_event mu B.
Proof.
  move=> Hmu_ge0 HB_pos HA_le.
  apply: (@Pr_cond_le_inter_div T mu A B eps HB_pos).
  exact: le_trans (@Pr_event_cap_le T mu A B Hmu_ge0) HA_le.
Qed.

(* path: utils:uniform_fin_mu_nonneg -> *)
(*   utils:serfling_uniform_perm_pair_deviation_tail -> bb84:bb84_bbkey -> *)
(*   bb84:stat -> bb84:bb84_secret *)
Lemma uniform_fin_mu_nonneg {T : finType} (t : T) :
  0 <= uniform_fin_mu t.
Proof.
  by rewrite /uniform_fin_mu invr_ge0 ler0n.
Qed.

(* path: utils:uniform_fin_mu_sum1 -> *)
(*   utils:serfling_uniform_perm_pair_deviation_tail -> bb84:bb84_bbkey -> *)
(*   bb84:stat -> bb84:bb84_secret *)
Lemma uniform_fin_mu_sum1 {T : finType} :
  (0 < #|{: T}|)%N ->
  \sum_(t : T) uniform_fin_mu t = 1.
Proof.
  move=> Hcard.
  transitivity (((#|{: T}|%:R)^-1) * ((#|{: T}|)%:R : R)).
  - rewrite /uniform_fin_mu sumr_const.
    by rewrite mulr_natr.
  - rewrite mulVf //.
    by rewrite lt0r_neq0 // ltr0n.
Qed.

(* path: utils:Pr_event_uniform_fin -> *)
(*   utils:serfling_uniform_perm_pair_deviation_tail -> bb84:bb84_bbkey -> *)
(*   bb84:stat -> bb84:bb84_secret *)
Lemma Pr_event_uniform_fin {T : finType} (A : {set T}) :
  Pr_event (@uniform_fin_mu T) A =
    ((#|A|%:R : R) * (#|{: T}|%:R)^-1).
Proof.
  rewrite /Pr_event /uniform_fin_mu sumr_const.
  by rewrite mulrC mulr_natr.
Qed.

Local Open Scope classical_set_scope.

(* ================================================================== *)
(* Serfling tail for sampling without replacement                       *)
(*                                                                      *)
(* Public API (exported for bb84/util.v):                               *)
(*   - uniform_perm_mu{_nonneg,_sum1} Uniform sampling on Sₙ             *)
(*   - perm_bool_*  / tuple_bool_*    Boolean-population sampling         *)
(*   - perm_pair_*                    Pair-bitstring sample/holdout facade *)
(*   - serfling_uniform_perm_pair_deviation_tail  Main result              *)
(*                                                                      *)
(* Internal proof structure (marked `Local`):                                 *)
(*   - is_derive_* helpers for the MGF calculus                          *)
(*   - tuple_* / serfling_inv_* inductive proof steps                    *)
(*   - base_holdout_tuple / left_block_perm / uniform holdout pushforward   *)
(*     — the pushforward from permutation distribution to tuple distribution *)
(*                                                                      *)
(* Main proof layers: scalar MGF bound, tuple sampling tail, permutation *)
(* pushforward, then the pair-bitstring xor facade.                      *)
(* ================================================================== *)

(* The one-step Serfling induction needs the centered Bernoulli mgf estimate
   from Hoeffding's lemma.  We keep it scalar here so the tuple proof below
   can reuse it without dragging in any BB84-specific notation. *)
(* Helper: d/ds [a * expR(c * s)] = a * c * expR(c * s).
   Built entirely in the R -> R world so is_derive1_comp works.
   Local: used only by bernoulli_centered_mgf_le below. *)
(* is_derive_scaled_exp_linear *)
(* infra: no tex label — fundamental & reusable (mathcomp-style) *)
(* consumer: is_derive_scaled_exp_linear is used downstream by the BB84 secrecy proof. *)
(* path: utils:is_derive_scaled_exp_linear -> *)
(*   utils:bernoulli_centered_mgf_le -> utils:tuple_step_mgf_le -> *)
(*   utils:tuple_serfling_mgf_step -> utils:tuple_serfling_mgf_bound -> *)
(*   utils:serfling_uniform_tuple_bool_tail -> *)
(*   utils:serfling_uniform_perm_pair_deviation_tail -> bb84:bb84_bbkey -> *)
(*   bb84:stat -> bb84:bb84_secret *)
Local Lemma is_derive_scaled_exp_linear (a c s : R) :
  is_derive (s : R^o) 1 (fun x : R => a * expR (c * x) : R^o) (a * c * expR (c * s)).
Proof.
  (* derivative of id is 1 *)
  have Hid : is_derive (s : R^o) 1%R (fun z : R => (z : R^o)) (1 : R^o).
  exact: (@is_derive_id R [the normedModType R of R^o] (s : R^o) 1%R).
  (* derivative of c * x is c *)
  have Hcx : is_derive (s : R^o) 1%R (fun x : R => (c * x : R^o)) (c : R^o).
  have := @is_deriveZ R [the normedModType R of R^o]
    [the normedModType R of R^o] (fun z : R => (z : R^o))
    c s 1%R (1 : R^o) Hid.
  by rewrite /GRing.scale /= mulr1.
  (* derivative of expR(c * x) is c * expR(c * s) via chain rule *)
  have Hexp : is_derive (s : R^o) 1%R (fun x : R => expR (c * x) : R^o)
  (expR (c * s) * c : R^o).
  exact: is_derive1_comp (is_derive_expR (c * s)) Hcx.
  (* scale by a *)
  have -> : (fun x : R => a * expR (c * x) : R^o) =
          (a \*: (fun x : R => expR (c * x) : R^o)).
  by apply/funext => x; rewrite /GRing.scale /=.
  apply: (is_derive_eq
  (@is_deriveZ R [the normedModType R of R^o]
    [the normedModType R of R^o] (fun x : R => expR (c * x) : R^o)
    a s 1%R (expR (c * s) * c : R^o) Hexp)).
  by rewrite /GRing.scale /= -mulrA [c * expR _]mulrC.
Qed.

(* Local: used only by bernoulli_centered_mgf_le below. *)
(* is_derive_quad_div8 *)
(* infra: no tex label — fundamental & reusable (mathcomp-style) *)
(* consumer: is_derive_quad_div8 is used downstream by the BB84 secrecy proof. *)
(* path: utils:is_derive_quad_div8 -> utils:bernoulli_centered_mgf_le -> *)
(*   utils:tuple_step_mgf_le -> utils:tuple_serfling_mgf_step -> *)
(*   utils:tuple_serfling_mgf_bound -> *)
(*   utils:serfling_uniform_tuple_bool_tail -> *)
(*   utils:serfling_uniform_perm_pair_deviation_tail -> bb84:bb84_bbkey -> *)
(*   bb84:stat -> bb84:bb84_secret *)
Local Lemma is_derive_quad_div8 (x : R) :
  is_derive (x : R^o) 1%R (fun u : R => u ^+ 2 / 8%:R : R^o) (x / 4%:R : R^o).
Proof.
  have Hid : is_derive (x : R^o) 1%R (fun z : R => (z : R^o)) (1 : R^o).
    exact: (@is_derive_id R [the normedModType R of R^o] (x : R^o) 1%R).
  have Hsq : is_derive (x : R^o) 1%R (fun u : R => (u * u : R^o)) (x + x : R^o).
    apply: (is_derive_eq (is_deriveM Hid Hid)).
    rewrite /GRing.scale /= !mulr1.
    by [].
  have -> : (fun u : R => u ^+ 2 / 8%:R : R^o) = (8%:R^-1 \*: (fun u : R => (u * u : R^o))).
    apply/funext => u.
    rewrite expr2 /GRing.scale /=.
    by rewrite mulrC.
  apply: (is_derive_eq
    (@is_deriveZ R [the normedModType R of R^o]
      [the normedModType R of R^o] (fun u : R => (u * u : R^o))
      8%:R^-1 x 1%R (x + x : R^o) Hsq)).
  rewrite /GRing.scale /=.
  rewrite mulrDr.
  have -> : (8%:R)^-1 * x + (8%:R)^-1 * x = x / 4%:R.
    have Hterm : (8%:R)^-1 * x = x * (4%:R)^-1 * (2%:R)^-1.
      rewrite mulrC.
      have H8 : (8 : R) = 4 * 2 by rewrite -natrM.
      rewrite H8 invfM ?pnatr_eq0 //.
      by rewrite mulrA.
    rewrite [X in X + _]Hterm [X in _ + X]Hterm.
    exact: (@split2r R (x * (4%:R)^-1)).
  by [].
Qed.

(* bernoulli_centered_mgf_le *)
(* infra: no tex label — fundamental & reusable (mathcomp-style) *)
(* consumer: bernoulli_centered_mgf_le is used downstream by the BB84 secrecy proof. *)
(* path: utils:bernoulli_centered_mgf_le -> utils:tuple_step_mgf_le -> *)
(*   utils:tuple_serfling_mgf_step -> utils:tuple_serfling_mgf_bound -> *)
(*   utils:serfling_uniform_tuple_bool_tail -> *)
(*   utils:serfling_uniform_perm_pair_deviation_tail -> bb84:bb84_bbkey -> *)
(*   bb84:stat -> bb84:bb84_secret *)
Local Lemma bernoulli_centered_mgf_le (p t : R) :
  0 <= p <= 1 ->
  0 <= t ->
  (1 - p) * expR (- p * t) + p * expR ((1 - p) * t) <=
    expR (t ^+ 2 / 8%:R).
Proof.
  move=> /andP [Hp0 Hp1] Ht.
  set q := 1 - p.
  have Hq0 : 0 <= q by rewrite /q subr_ge0.
  have Hpq1 : p + q = 1 by rewrite /q addrC subrK.
  (* M(s) = q * expR(-p*s) + p * expR(q*s)
    Type the function R^o -> R^o so derivable resolves normedModType *)
  pose M : R^o -> R^o := fun s => q * expR (- p * s) + p * expR (q * s).
  have M_pos : forall s, 0 < M s.
  { move=> s; rewrite /M.
    have [Hpz | Hp_ne] := eqVneq p 0.
    - rewrite /q Hpz subr0 oppr0 !mul0r addr0 mul1r expR0. exact: ltr01.
    - have Hp_pos : 0 < p by rewrite lt_neqAle Hp0 andbT eq_sym.
      apply: ltr_pwDr.
      + exact: mulr_gt0 Hp_pos (expR_gt0 _).
      + exact: mulr_ge0 Hq0 (ltW (expR_gt0 _)). }
  (* Reduce to ln(M t) <= t^2/8 *)
  rewrite -(ler_ln (M_pos t) (expR_gt0 _)) expRK.
  (* Derivative helpers — use (s : R^o) for point and `: R^o` for output *)
  pose M'_val : R^o -> R^o := fun s => (-p * q) * expR (-p * s) + (p * q) * expR (q * s).
  have H_Mderiv (s : R) : is_derive (s : R^o) 1
      (fun s : R => q * expR (- p * s) + p * expR (q * s) : R^o)
      (M'_val s : R^o).
  { rewrite /M'_val.
    apply: (is_derive_eq (is_deriveD
      (is_derive_scaled_exp_linear q (-p) s)
      (is_derive_scaled_exp_linear p q s))).
    by congr (_ * _ + _); rewrite mulrN [q * p]mulrC -mulNr. }
  (* Bridge: convert R^o-is_derive to plain derivable.
    The key insight: (fun s : R => body : R^o) and M are convertible
    at the sort level, but Coq needs an explicit change. *)
  have M_derivable (s : R) : derivable M s 1.
  { have [Hdrv _] := H_Mderiv s.
    change (derivable M s 1). exact: Hdrv. }
  (* phi(s) = ln(M s) - s^2/8 *)
  pose phi : R^o -> R^o := fun s : R^o => ln (q * expR (- p * s) + p * expR (q * s)) - s ^+ 2 / 8%:R.
  pose phi'_val : R^o -> R^o := fun s => (M s)^-1 * M'_val s - s / 4%:R.
  have H_phideriv (s : R) :
    is_derive (s : R^o) 1 phi (phi'_val s : R^o).
  { rewrite /phi'_val.
    apply: is_deriveB; last exact: is_derive_quad_div8.
    (* ln(M(s)) derivative = M'(s)/M(s) via chain rule *)
    have Hln_M : is_derive (s : R^o) 1
      (fun s : R => ln (q * expR (- p * s) + p * expR (q * s)) : R^o)
      ((M s)^-1 * M'_val s : R^o).
    { have Hln : is_derive (M s : R^o) 1 (fun x : R => ln x : R^o) ((M s)^-1 : R^o).
      { apply: is_derive_eq; first exact: is_derive1_ln (M_pos s).
        done. }
      have Hcomp := is_derive1_comp Hln (H_Mderiv s).
      apply: (is_derive_eq Hcomp).
      done. }
    apply: (is_derive_eq Hln_M). by rewrite mulrC. }
  (* phi(0) = 0 *)
  have Hphi0 : phi 0 = 0.
  { rewrite /phi /M mulr0 mulr0 !expR0 !mulr1.
    have -> : q + p = 1 by rewrite addrC Hpq1.
    rewrite ln1.
    rewrite expr2 mul0r mul0r subrr. done. }
  (* Goal: ln(M t) <= t^2/8, which is phi t <= 0 *)
  suff Hphi_le : phi t <= 0 by move: Hphi_le; rewrite /phi subr_le0.
  rewrite -Hphi0.
  (* Apply ler0_derive1_le_cc to phi on [0, t] *)
  apply: (ler0_derive1_le_cc (f := phi) (a := 0) (b := t)) => //.
  - (* phi' <= 0 *)
    move=> s Hs.
    have Hd := H_phideriv s.
    rewrite derive1E (@derive_val _ _ _ (s : R^o) 1 phi _ Hd).
    (* Goal: phi'_val s <= 0 *)
    (* phi'_val s = (M s)^-1 * M'_val s - s / 4 *)
    (* Strategy: phi'_val 0 = 0 and phi'_val is non-increasing (phi'' <= 0) *)
    have Hphi'0 : phi'_val 0 = 0.
    { rewrite /phi'_val /M /M'_val !mulr0 !expR0 !mulr1 mul0r subr0 mulNr addNr mulr0.
      done. }
    (* Second derivatives *)
    pose M''_val : R^o -> R^o := fun s =>
      (p ^+ 2 * q) * expR (-p * s) + (p * q ^+ 2) * expR (q * s).
    have H_M'deriv (u : R) : is_derive (u : R^o) 1
      (fun u : R => (-p * q) * expR (-p * u) + (p * q) * expR (q * u) : R^o)
      (M''_val u : R^o).
    { rewrite /M''_val.
      apply: (is_derive_eq (is_deriveD
        (is_derive_scaled_exp_linear (-p * q) (-p) u)
        (is_derive_scaled_exp_linear (p * q) q u))).
      (* LHS: (-p*q)*(-p) * expR(-p*u) + (p*q)*q * expR(q*u)
         RHS: (p^+2*q) * expR(-p*u) + (p*q^+2) * expR(q*u) *)
      congr (_ * _ + _ * _).
      - by rewrite [(-p * q) * _]mulrAC mulrNN -expr2.
      - by rewrite -mulrA -expr2. }
    (* Now prove phi'_val s <= 0 using inner ler0_derive1_le_cc *)
    (* phi'(u) = M'(u)/M(u) - u/4  
       phi''(u) = [M''(u)*M(u) - M'(u)^2]/M(u)^2 - 1/4
       phi''(u) <= 0 by AM-GM: M(u)^2 >= 4pq*e^{(q-p)u} *)
    pose phi''_val : R^o -> R^o := fun u =>
      (M u)^-2 * (M''_val u * M u - (M'_val u) ^+ 2) - (4%:R)^-1.
    have M_ne0 (u : R) : M u != 0 by rewrite gt_eqF // M_pos.
    (* H_Mderiv2: same as H_Mderiv but with function = M *)
    have H_Mderiv2 (u : R) : is_derive (u : R^o) 1 M (M'_val u : R^o).
    { rewrite /M. exact: H_Mderiv u. }
    (* is_derive for 1/M via DeriveDef + deriveV *)
    have H_Minv_deriv (u : R) :
      is_derive (u : R^o) 1
        (fun u : R => (M u)^-1 : R^o)
        (- (M u) ^-2 * M'_val u : R^o).
    { apply: DeriveDef.
      - exact: (derivableV (M_ne0 u) (M_derivable u)).
      - rewrite deriveV //
          (@derive_val _ _ _ (u : R^o) 1 M _ (H_Mderiv2 u)).
        done. }
    (* is_derive for M'/M via product rule *)
    have H_ratio_deriv (u : R) :
      is_derive (u : R^o) 1
        (fun u : R => (M u)^-1 * M'_val u : R^o)
        ((M u)^-1 * M''_val u + M'_val u * (- (M u) ^-2 * M'_val u) : R^o).
    { exact: is_deriveM (H_Minv_deriv u) (H_M'deriv u). }
    (* is_derive for phi'_val = (M^-1 * M') - (id/4) *)
    have H_lin_deriv (u : R) :
      is_derive (u : R^o) 1 
        (fun u : R => u / 4%:R : R^o)
        ((4%:R)^-1 : R^o).
    { have Hid := @is_derive_id _ _ (u : R^o) 1.
      have Hcst := @is_derive_cst _ _ _ ((4%:R)^-1 : R^o) (u : R^o) 1.
      have Hprod := is_deriveM Hid Hcst.
      apply: (is_derive_eq Hprod).
      by rewrite /= scaler0 add0r /GRing.scale /= mulr1. }
    have H_phi'deriv (u : R) :
      is_derive (u : R^o) 1 phi'_val (phi''_val u : R^o).
    { rewrite /phi'_val /phi''_val.
      apply: (is_derive_eq (is_deriveB (H_ratio_deriv u) (H_lin_deriv u))).
      (* Need to show the derivative values are equal:
         LHS: (M u)^-1 * M''_val u + M'_val u * (-(M u)^-2 * M'_val u) - (4^-1)
         RHS: (M u)^-2 * (M''_val u * M u - M'_val u ^+2) - (4^-1) *)
      congr (_ - _).
      have Mne := M_ne0 u.
      (* After congr, need: 
         (M u)^-1 * M''_val u + M'_val u * (-(M u)^-2 * M'_val u) 
         = (M u)^-2 * (M''_val u * M u - M'_val u ^+2) *)
      (* RHS: distribute *)
      rewrite mulrBr.
      (* RHS: (M u)^-2 * (M''_val u * M u) - (M u)^-2 * M'_val u ^+2 *)
      (* First term: (M u)^-2 * (M''_val u * M u) = (M u)^-1 * M''_val u *)
      have -> : M u ^- 2 * (M''_val u * M u) = (M u)^-1 * M''_val u.
      { rewrite expr2 invfM // -!mulrA. congr (_ * _).
        by rewrite mulrCA mulVf // mulr1. }
      (* Now need: M^-1*M'' + M'*(-(M^-2)*M') = M^-1*M'' - M^-2*M'^2 *)
      congr (_ + _).
      rewrite expr2.
      rewrite [in LHS]mulNr mulrN.
      congr (- _).
      by rewrite mulrCA. }
    (* Key identity: M''*M - M'^2 = pq * exp((q-p)*u) *)
    have MM_identity (u : R) :
      M''_val u * M u - (M'_val u) ^+ 2 = p * q * expR ((q - p) * u).
    { rewrite /M''_val /M /M'_val.
      set A : R := expR (-p * u). set B : R := expR (q * u).
      have HAB : A * B = expR ((q - p) * u).
      { rewrite /A /B -expRD. congr (expR _).
        by rewrite -mulrDl addrC. }
      set D : R := B - A.
      have HM2E : ((p ^+ 2 * q) * A + (p * q ^+ 2) * B) =
          p * q * (p * A + q * B) :> R.
      { have -> : p * q * (p * A + q * B) = p * q * (p * A) + p * q * (q * B).
        { by rewrite mulrDr. }
        have -> : p * q * (p * A) = (p ^+ 2 * q) * A :> R.
        { rewrite expr2 -!mulrA.
          congr (p * _).
          by rewrite !mulrA [p * q]mulrC. }
        have -> : p * q * (q * B) = (p * q ^+ 2) * B :> R.
        { by rewrite expr2 -!mulrA. }
        by [].
      }
      have HM1E : ((- p * q) * A + p * q * B) = p * q * D :> R.
      { rewrite addrC -!mulrA mulNr.
        rewrite -mulrBr -(mulrBr q B A) /D.
        by rewrite mulrA. }
      have Hsplit : (p * A + q * B) * (q * A + p * B) - p * q * D ^+ 2 = A * B.
      { have Hlhs : p * A + q * B = B - p * D.
        { rewrite /D [p * (B - A)]mulrBr opprB.
          have -> : q * B = B - p * B :> R.
          { by rewrite /q mulrBl mul1r. }
          by rewrite addrCA. }
        have Hrhs : q * A + p * B = A + p * D.
        { have -> : A + p * D = A + p * B - p * A :> R.
          { rewrite /D [p * (B - A)]mulrBr.
            by rewrite addrA. }
          rewrite /q mulrBl mul1r.
          have -> : A + p * B - p * A = A - p * A + p * B :> R.
          { rewrite -addrA.
            by rewrite [p * B - p * A]addrC addrA. }
          by [].
        }
        rewrite Hlhs Hrhs.
        have HDcross : B * D - D * A = D ^+ 2.
        { have -> : D ^+ 2 = B * B - A * B - A * B + A * A :> R.
          { rewrite /D sqrrB [B ^+ 2]expr2 [A ^+ 2]expr2 [B * A]mulrC.
            by rewrite opprD -!addrA. }
          rewrite /D mulrBr mulrBl [B * A]mulrC.
          have -> : B * B - A * B - (A * B - A * A)
              = B * B - A * B - A * B + A * A :> R.
          { by rewrite opprB [A * A - A * B]addrC addrA. }
          by [].
        }
        have Hleft : B * (A + p * D) = A * B + p * (B * D) :> R.
        { rewrite mulrDr !mulrA.
          by rewrite [B * A]mulrC [B * p]mulrC. }
        have Hright :
            (p * D) * (A + p * D) = p * (D * A) + p ^+ 2 * D ^+ 2 :> R.
        { rewrite mulrDr.
          have -> : (p * D) * A = p * (D * A).
          { by rewrite mulrA. }
          have -> : (p * D) * (p * D) = p ^+ 2 * D ^+ 2.
          { rewrite expr2.
            have -> : (p * D) * (p * D) = p * (D * (p * D)) :> R.
            { by rewrite !mulrA. }
            have -> : D * (p * D) = p * (D * D) :> R.
            { rewrite mulrA [D * p]mulrC.
              by rewrite -mulrA. }
            rewrite -mulrA.
            by rewrite [D * D]mulrC. }
          by [].
        }
        rewrite mulrBl Hleft Hright.
        rewrite opprD !addrA.
        have -> : A * B + p * (B * D) + - (p * (D * A))
            = A * B + (p * (B * D) - p * (D * A)) :> R.
        { by rewrite -addrA. }
        have -> : p * (B * D) - p * (D * A) = p * D ^+ 2.
        { by rewrite -mulrBr HDcross. }
        have -> : A * B + p * D ^+ 2 + - (p ^+ 2 * D ^+ 2)
            = A * B + (p * D ^+ 2 - p ^+ 2 * D ^+ 2) :> R.
        { by rewrite -addrA. }
        have -> : p * D ^+ 2 - p ^+ 2 * D ^+ 2 = p * q * D ^+ 2.
        { rewrite -mulrBl.
          have -> : p - p ^+ 2 = p * q.
          { rewrite /q expr2 mulrBr mulr1.
            by [].
          }
          by [].
        }
        by rewrite -addrA subrr addr0. }
      rewrite HM2E HM1E.
      have Hsq : (p * q * D) ^+ 2 = p * q * (p * q * D ^+ 2) :> R.
      { rewrite expr2.
        have -> : (p * q * D) * (p * q * D) = p * q * (D * (p * q * D)) :> R.
        { by rewrite !mulrA. }
        have -> : D * (p * q * D) = p * q * D ^+ 2 :> R.
        { rewrite expr2 mulrA [D * (p * q)]mulrC -!mulrA.
          by [].
        }
        by [].
      }
      rewrite Hsq.
      have -> : p * q * (p * A + q * B) * (q * A + p * B)
          = p * q * ((p * A + q * B) * (q * A + p * B)) :> R.
      { by rewrite -mulrA. }
      have -> : p * q * ((p * A + q * B) * (q * A + p * B))
              - p * q * (p * q * D ^+ 2)
              = p * q * (((p * A + q * B) * (q * A + p * B)) - p * q * D ^+ 2)
          :> R.
      { by rewrite -mulrBr. }
      rewrite Hsplit.
      by rewrite HAB. }
    (* AM-GM: M(u)^2 >= 4pq*exp((q-p)*u) *)
    have M_sq_ge (u : R) :
      4%:R * (p * q) * expR ((q - p) * u) <= (M u) ^+ 2.
    { rewrite /M -subr_ge0.
      set A : R := expR (-p * u). set B : R := expR (q * u).
      have HAB : A * B = expR ((q - p) * u).
      { rewrite /A /B -expRD. congr (expR _).
        by rewrite -mulrDl addrC. }
      rewrite -HAB.
      have -> : (q * A + p * B) ^+ 2 - 4%:R * (p * q) * (A * B) =
          (q * A - p * B) ^+ 2 :> R.
      { pose D : R := p * q * (A * B).
        have Hcross1 : q * A * (p * B) = D :> R.
        { have -> : q * A * (p * B) = (q * p) * (A * B) :> R.
          { by rewrite -!mulrA [A * (p * B)]mulrA [A * p]mulrC !mulrA. }
          by rewrite /D [q * p]mulrC. }
        have H4D : 4%:R * (p * q) * (A * B) = (D + D) + (D + D) :> R.
        { rewrite /D -mulrA.
          have -> : (4%:R : R) = 2%:R + 2%:R by rewrite -natrD.
          by rewrite mulrDl !mulr_natl !mulr2n. }
        rewrite sqrrD sqrrB !Hcross1 H4D.
        have -> : (q * A) ^+ 2 - (D + D) + (p * B) ^+ 2
                = ((q * A) ^+ 2 + (p * B) ^+ 2) - (D + D) :> R.
        { rewrite -!addrA.
          by rewrite [-(D + D) + (p * B) ^+ 2]addrC. }
        have -> : (((q * A) ^+ 2 + (D + D)) + (p * B) ^+ 2)
                = (((q * A) ^+ 2 + (p * B) ^+ 2) + (D + D)) :> R.
        { rewrite -addrA.
          rewrite [(D + D) + (p * B) ^+ 2]addrC.
          by rewrite -addrA. }
        exact: addrKA. }
      exact: sqr_ge0. }
    (* phi''_val u <= 0 for all u *)
    have Hphi''_le0 (u : R) : phi''_val u <= 0.
    { rewrite /phi''_val MM_identity subr_le0.
      have Mpos := M_pos u.
      have Mne := M_ne0 u.
      have M2pos : 0 < (M u) ^+ 2 by exact: exprn_gt0.
      have M2ne : (M u) ^+ 2 != 0 by rewrite gt_eqF // exprn_gt0.
      have Msq := M_sq_ge u.
      (* Reduce the second-derivative bound by clearing `(M u)^-2`. *)
      (* Multiply both sides by positive (M u)^+2 *)
      rewrite -(ler_pM2r M2pos).
      rewrite mulrAC mulVf ?M2ne // mul1r.
      (* Move the factor `4` to the left-hand side. *)
      rewrite ler_pdivlMl; last by rewrite ltr0n.
      (* Close with the square lower bound for `M u`. *)
      rewrite mulrA.
      exact: M_sq_ge. }

    (* Inner ler0_derive1_le_cc: phi'_val is non-increasing on [0, s] *)
    rewrite -Hphi'0.
    have Hs0 : 0 < s by move: Hs; rewrite in_itv /=; case/andP.
    apply: (ler0_derive1_le_cc (f := phi'_val) (a := 0) (b := s)).
    + by move=> x _; move: (H_phi'deriv x)=>[].
    + move=> x Hx.
      have Hd' := H_phi'deriv x.
      rewrite derive1E (@derive_val _ _ _ (x : R^o) 1 phi'_val _ Hd').
      exact: Hphi''_le0.
    + apply: continuous_in_subspaceT=> x.
      rewrite inE /= in_itv /= => _.
      move: (H_phi'deriv x)=>[].
      by rewrite derivable1_diffP=>/differentiable_continuous.
    + by rewrite in_itv /= lexx (ltW Hs0).
    + by rewrite in_itv /= lexx (ltW Hs0).
    + exact: ltW Hs0.
  - (* continuity *)
    apply: continuous_in_subspaceT=> s0.
    rewrite inE /= in_itv /= => _.
    move: (H_phideriv s0)=>[].
    by rewrite derivable1_diffP=>/differentiable_continuous.
  - by rewrite in_itv /= lexx Ht.
  - by rewrite in_itv /= lexx Ht.
Qed.

(* Chernoff bound *)

Section UniformPermutationSampling.

(* A uniform measure on permutations is the classical source for sampling
   without replacement: first choose a raw mismatch pattern, then draw a
   permutation uniformly and read the first `k` slots as the sample block and
   the last `n` as the holdout block. *)
(* uniform_perm_mu *)
(* infra: no tex label — fundamental & reusable (mathcomp-style) *)
(* consumer: uniform_perm_mu is used downstream by the BB84 secrecy proof. *)
Definition uniform_perm_mu (N : nat) (pi : 'S_N) : R :=
  (#|{: 'S_N}|%:R)^-1.

(* uniform_perm_mu_nonneg *)
(* infra: no tex label — fundamental & reusable (mathcomp-style) *)
(* consumer: uniform_perm_mu_nonneg is used downstream by the BB84 secrecy proof. *)
(* path: utils:uniform_perm_mu_nonneg -> bb84:bb84_secret *)
Lemma uniform_perm_mu_nonneg (N : nat) (pi : 'S_N) :
  0 <= @uniform_perm_mu N pi.
Proof.
  rewrite /uniform_perm_mu.
  by rewrite invr_ge0 ler0n.
Qed.

(* uniform_perm_mu_pos *)
(* infra: no tex label — fundamental & reusable classical probability. *)
(* consumer: uniform_perm_mu_pos is used downstream by the BB84 secrecy proof. *)
(* path: utils:uniform_perm_mu_pos -> *)
(*   utils:serfling_uniform_perm_pair_deviation_tail -> bb84:bb84_bbkey -> *)
(*   bb84:stat -> bb84:bb84_secret *)
Lemma uniform_perm_mu_pos (N : nat) (pi : 'S_N) :
  0 < @uniform_perm_mu N pi.
Proof.
  rewrite /uniform_perm_mu invr_gt0 ltr0n.
  apply/card_gt0P.
  exists pi.
  by rewrite inE.
Qed.

(* uniform_perm_mu_sum1 *)
(* infra: no tex label — fundamental & reusable (mathcomp-style) *)
(* consumer: uniform_perm_mu_sum1 is used downstream by the BB84 secrecy proof. *)
(* path: utils:uniform_perm_mu_sum1 -> bb84:bb84_secret *)
Lemma uniform_perm_mu_sum1 (N : nat) :
  \sum_(pi : 'S_N) @uniform_perm_mu N pi = 1.
Proof.
  transitivity (((#|{: 'S_N}|%:R)^-1) * ((#|{: 'S_N}|)%:R : R)).
  - rewrite /uniform_perm_mu sumr_const.
    rewrite mulr_natr.
    reflexivity.
  - rewrite mulVf.
    + reflexivity.
    + have Hcard_pos : 0 < (#|{: 'S_N}|)%:R :> R.
      {
        rewrite ltr0n.
        apply/card_gt0P.
        exists (1%g : 'S_N).
        by rewrite inE.
      }
      exact: lt0r_neq0 Hcard_pos.
Qed.

(* product_prob_sum1 *)
(* infra: no tex label — fundamental & reusable (mathcomp-style) *)
(* consumer: product_prob_sum1 is used downstream by the BB84 secrecy proof. *)
(* path: utils:product_prob_sum1 -> *)
(*   utils:serfling_uniform_perm_pair_deviation_tail -> bb84:bb84_bbkey -> *)
(*   bb84:stat -> bb84:bb84_secret *)
Lemma product_prob_sum1
  {A B : finType} (muA : A -> R) (muB : B -> R) :
  (\sum_(a : A) muA a = 1) ->
  (\sum_(b : B) muB b = 1) ->
  \sum_(ab : A * B) (muA ab.1 * muB ab.2) = 1.
Proof.
  move=> HmuA HmuB.
  rewrite pair_bigV /=.
  apply: eq_trans.
  {
    apply: eq_bigr => a _.
    rewrite -mulr_sumr.
    reflexivity.
  }
  rewrite (eq_bigr (fun a => muA a * 1)); last first.
  {
    move=> a _.
    by rewrite HmuB.
  }
  rewrite (eq_bigr (fun a => muA a)); last first.
  {
    move=> a _.
    by rewrite mulr1.
  }
  exact: HmuA.
Qed.

(* product_prob_fiber_le *)
(* infra: no tex label — fundamental & reusable (mathcomp-style) *)
(* consumer: product_prob_fiber_le is used downstream by the BB84 secrecy proof. *)
(* path: utils:product_prob_fiber_le -> *)
(*   utils:serfling_uniform_perm_pair_deviation_tail -> bb84:bb84_bbkey -> *)
(*   bb84:stat -> bb84:bb84_secret *)
Lemma product_prob_fiber_le
  {A B : finType} (muA : A -> R) (muB : B -> R)
  (E : A -> {set B}) (r : R) :
  (forall a, 0 <= muA a) ->
  (forall b, 0 <= muB b) ->
  (\sum_(a : A) muA a = 1) ->
  (forall a, Pr_event muB (E a) <= r) ->
  \sum_(ab : A * B | ab.2 \in E ab.1) (muA ab.1 * muB ab.2) <= r.
Proof.
  move=> HmuA_nonneg HmuB_nonneg HmuA_sum1 HE.
  rewrite pair_bigV /=.
  have Hstep :
      \sum_(a : A) \sum_(b : B | b \in E a) (muA a * muB b) <=
        \sum_(a : A) (muA a * r).
  {
    apply: ler_sum => a _.
    have Hprob_nonneg : 0 <= Pr_event muB (E a).
    {
      rewrite /Pr_event.
      apply: sumr_ge0 => b _.
      exact: HmuB_nonneg.
    }
    have Hscaled :
        muA a * Pr_event muB (E a) <= muA a * r.
    {
      exact: (ler_pM (HmuA_nonneg a) Hprob_nonneg
        (lexx (muA a)) (HE a)).
    }
      rewrite /Pr_event mulr_sumr in Hscaled.
      exact: Hscaled.
  }
  apply: (le_trans Hstep).
  rewrite -mulr_suml HmuA_sum1.
  by rewrite mul1r.
Qed.

(* path: utils:product_prob_fst_event -> *)
(*   utils:serfling_uniform_perm_pair_deviation_tail -> bb84:bb84_bbkey -> *)
(*   bb84:stat -> bb84:bb84_secret *)
Lemma product_prob_fst_event
  {A B : finType} (muA : A -> R) (muB : B -> R) (E : {set A}) :
  (\sum_(b : B) muB b = 1) ->
  Pr_event (fun ab : A * B => muA ab.1 * muB ab.2)
    [set ab : A * B | ab.1 \in E] =
  Pr_event muA E.
Proof.
  move=> HmuB.
  rewrite /Pr_event pair_bigV /=.
  rewrite (bigID (mem E)) /=.
  rewrite [X in _ + X]big1; last first.
  {
    move=> a Ha.
    rewrite big_pred0 // => b.
    have HEaF : (a \in E) = false.
    { apply/negP => HEa; move: Ha; by rewrite HEa. }
    by rewrite inE HEaF.
  }
  rewrite addr0.
  apply: eq_bigr => a Ha.
  rewrite (eq_bigl (fun _ : B => true)); last by move=> b; rewrite inE Ha.
  by rewrite -mulr_sumr HmuB mulr1.
Qed.

(* markov_event_bound *)
(* infra: no tex label — fundamental & reusable (mathcomp-style) *)
(* consumer: markov_event_bound is used downstream by the BB84 secrecy proof. *)
(* path: utils:markov_event_bound -> utils:serfling_uniform_tuple_bool_tail -> *)
(*   utils:serfling_uniform_perm_pair_deviation_tail -> bb84:bb84_bbkey -> *)
(*   bb84:stat -> bb84:bb84_secret *)
Local Lemma markov_event_bound
  {A : finType} (mu : A -> R) (X : A -> R) (E : {set A}) (c : R) :
  0 < c ->
  (forall a, 0 <= mu a) ->
  (forall a, 0 <= X a) ->
  (forall a, a \in E -> c <= X a) ->
  Pr_event mu E <= (\sum_(a : A) mu a * X a) / c.
Proof.
  move=> Hc_pos Hmu_nonneg HX_nonneg HEX.
  rewrite ler_pdivlMr.
  - rewrite [(\sum_(a in E) mu a) * c]mulrC.
    rewrite mulr_sumr.
    apply: le_trans.
    + apply: ler_sum => a Ha.
      rewrite [c * mu a]mulrC.
      apply: ler_wpM2l.
      * exact: Hmu_nonneg.
      * exact: HEX a Ha.
    + rewrite [X in _ <= X](bigID (fun a : A => a \in E)) /=.
      rewrite -{1}(addr0 (\sum_(a | a \in E) mu a * X a)).
      rewrite lerD2l.
      apply: sumr_ge0 => a _.
      apply: mulr_ge0.
      * exact: Hmu_nonneg.
      * exact: HX_nonneg.
  - exact: Hc_pos.
Qed.

Section PermutationBooleanPopulation.

Variables (n k : nat).

Local Notation N := (k + n)%N.

(* The total number of mismatches in the Boolean population.  We keep this
   as a bigop count because the Serfling proof repeatedly removes one point
   from the population. *)
(* perm_bool_pop_count *)
(* infra: no tex label — fundamental & reusable (mathcomp-style) *)
(* consumer: perm_bool_pop_count is used downstream by the BB84 secrecy proof. *)
Definition perm_bool_pop_count (d : bitstr N) : nat :=
  \sum_(i : 'I_N | d i) 1%N.

(* The Boolean population is the total mismatch string.  A permutation picks
   the first `k` sample positions and the last `n` holdout positions. *)
(* perm_bool_sample_count *)
(* infra: no tex label — fundamental & reusable (mathcomp-style) *)
(* consumer: perm_bool_sample_count is used downstream by the BB84 secrecy proof. *)
Definition perm_bool_sample_count (d : bitstr N) (pi : 'S_N) : nat :=
  \sum_(i : 'I_k | d (pi (@lshift k n i))) 1%N.

(* perm_bool_holdout_count *)
(* infra: no tex label — fundamental & reusable (mathcomp-style) *)
(* consumer: perm_bool_holdout_count is used downstream by the BB84 secrecy proof. *)
Definition perm_bool_holdout_count (d : bitstr N) (pi : 'S_N) : nat :=
  \sum_(i : 'I_n | d (pi (@rshift k n i))) 1%N.

(* perm_bool_sample_err *)
(* infra: no tex label — fundamental & reusable (mathcomp-style) *)
(* consumer: perm_bool_sample_err is used downstream by the BB84 secrecy proof. *)
Definition perm_bool_sample_err (d : bitstr N) (pi : 'S_N) : R :=
  (perm_bool_sample_count d pi)%:R / k%:R.

(* perm_bool_holdout_err *)
(* infra: no tex label — fundamental & reusable (mathcomp-style) *)
(* consumer: perm_bool_holdout_err is used downstream by the BB84 secrecy proof. *)
Definition perm_bool_holdout_err (d : bitstr N) (pi : 'S_N) : R :=
  (perm_bool_holdout_count d pi)%:R / n%:R.

(* perm_bool_deviation_event *)
(* infra: no tex label — fundamental & reusable (mathcomp-style) *)
(* consumer: perm_bool_deviation_event is used downstream by the BB84 secrecy proof. *)
Definition perm_bool_deviation_event (d : bitstr N) (mu : R) : {set 'S_N} :=
  [set pi : 'S_N | perm_bool_holdout_err d pi >= perm_bool_sample_err d pi + mu].

(* perm_bool_centered_over_k *)
(* infra: no tex label — fundamental & reusable (mathcomp-style) *)
(* consumer: perm_bool_centered_over_k is used downstream by the BB84 secrecy proof. *)
Definition perm_bool_centered_over_k (d : bitstr N) (pi : 'S_N) : R :=
  ((perm_bool_holdout_count d pi)%:R -
    n%:R * (perm_bool_pop_count d)%:R / N%:R) / k%:R.

(* perm_bool_holdout_tuple *)
(* infra: no tex label — fundamental & reusable (mathcomp-style) *)
(* consumer: perm_bool_holdout_tuple is used downstream by the BB84 secrecy proof. *)
Definition perm_bool_holdout_tuple (pi : 'S_N) : n.-tuple 'I_N :=
  [tuple pi (@rshift k n i) | i < n].

(* tuple_uniform_mu *)
(* infra: no tex label — fundamental & reusable (mathcomp-style) *)
(* consumer: tuple_uniform_mu is used downstream by the BB84 secrecy proof. *)
Definition tuple_uniform_mu (t : n.-tuple 'I_N) : R :=
  if uniq t then ((N ^_ n)%:R)^-1 else 0.

(* tuple_bool_holdout_count *)
(* infra: no tex label — fundamental & reusable (mathcomp-style) *)
(* consumer: tuple_bool_holdout_count is used downstream by the BB84 secrecy proof. *)
Definition tuple_bool_holdout_count (d : bitstr N) (t : n.-tuple 'I_N) : nat :=
  \sum_(i < n | d (tnth t i)) 1%N.

(* tuple_bool_centered_over_k *)
(* infra: no tex label — fundamental & reusable (mathcomp-style) *)
(* consumer: tuple_bool_centered_over_k is used downstream by the BB84 secrecy proof. *)
Definition tuple_bool_centered_over_k (d : bitstr N) (t : n.-tuple 'I_N) : R :=
  ((tuple_bool_holdout_count d t)%:R -
    n%:R * (perm_bool_pop_count d)%:R / N%:R) / k%:R.

(* tuple_bool_deviation_event *)
(* infra: no tex label — fundamental & reusable (mathcomp-style) *)
(* consumer: tuple_bool_deviation_event is used downstream by the BB84 secrecy proof. *)
Definition tuple_bool_deviation_event (d : bitstr N) (mu : R) :
    {set n.-tuple 'I_N} :=
  [set t : n.-tuple 'I_N |
    uniq t &&
    (n%:R * mu / N%:R <= tuple_bool_centered_over_k d t)].

(* perm_bool_pop_countE *)
(* infra: no tex label — fundamental & reusable (mathcomp-style) *)
(* consumer: perm_bool_pop_countE is used downstream by the BB84 secrecy proof. *)
(* path: utils:perm_bool_pop_countE -> *)
(*   utils:serfling_uniform_perm_pair_deviation_tail -> bb84:bb84_bbkey -> *)
(*   bb84:stat -> bb84:bb84_secret *)
Lemma perm_bool_pop_countE (d : bitstr N) :
  perm_bool_pop_count d = wt_ham d.
Proof.
  rewrite /perm_bool_pop_count /wt_ham.
  rewrite -sum1_card.
  apply: eq_bigl => i.
  by rewrite inE.
Qed.

(* perm_bool_partition_countE *)
(* infra: no tex label — fundamental & reusable (mathcomp-style) *)
(* consumer: perm_bool_partition_countE is used downstream by the BB84 secrecy proof. *)
(* path: utils:perm_bool_partition_countE -> *)
(*   utils:perm_bool_deviation_event_tupleE -> *)
(*   utils:uniform_perm_key_tuple_pushforward -> *)
(*   utils:serfling_uniform_perm_pair_deviation_tail -> bb84:bb84_bbkey -> *)
(*   bb84:stat -> bb84:bb84_secret *)
Lemma perm_bool_partition_countE (d : bitstr N) (pi : 'S_N) :
  perm_bool_pop_count d = perm_bool_sample_count d pi + perm_bool_holdout_count d pi.
Proof.
  rewrite /perm_bool_pop_count /perm_bool_sample_count /perm_bool_holdout_count.
  rewrite !big_mkcond.
  rewrite (reindex_perm pi) /=.
  rewrite big_split_ord /=.
  rewrite -!big_mkcond.
  reflexivity.
Qed.

(* perm_bool_holdout_tuple_uniq *)
(* infra: no tex label — fundamental & reusable (mathcomp-style) *)
(* consumer: perm_bool_holdout_tuple_uniq is used downstream by the BB84 secrecy proof. *)
(* path: utils:perm_bool_holdout_tuple_uniq -> *)
(*   utils:card_perm_bool_holdout_tuple_fiber -> *)
(*   utils:uniform_perm_key_tuple_pushforward -> *)
(*   utils:serfling_uniform_perm_pair_deviation_tail -> bb84:bb84_bbkey -> *)
(*   bb84:stat -> bb84:bb84_secret *)
Local Lemma perm_bool_holdout_tuple_uniq (pi : 'S_N) :
  uniq (perm_bool_holdout_tuple pi).
Proof.
  apply/tuple_uniqP => i j Hij.
  apply: rshift_inj.
  have Hpi :
      pi (@rshift k n i) = pi (@rshift k n j).
  {
    move: Hij.
    rewrite /perm_bool_holdout_tuple /=.
    move=> H.
    move: H.
    rewrite !tnth_mktuple.
    move=> Hpi.
    exact Hpi.
  }
  exact: (perm_inj Hpi).
Qed.

(* tuple_uniform_mu_nonneg *)
(* infra: no tex label — fundamental & reusable (mathcomp-style) *)
(* consumer: tuple_uniform_mu_nonneg is used downstream by the BB84 secrecy proof. *)
(* path: utils:tuple_uniform_mu_nonneg -> *)
(*   utils:serfling_uniform_tuple_bool_tail -> *)
(*   utils:serfling_uniform_perm_pair_deviation_tail -> bb84:bb84_bbkey -> *)
(*   bb84:stat -> bb84:bb84_secret *)
Lemma tuple_uniform_mu_nonneg (t : n.-tuple 'I_N) :
  0 <= tuple_uniform_mu t.
Proof.
  rewrite /tuple_uniform_mu.
  case: (uniq t); last by exact: lexx.
  by rewrite invr_ge0 ler0n.
Qed.

(* tuple_bool_holdout_countE *)
(* infra: no tex label — fundamental & reusable (mathcomp-style) *)
(* consumer: tuple_bool_holdout_countE is used downstream by the BB84 secrecy proof. *)
(* path: utils:tuple_bool_holdout_countE -> *)
(*   utils:perm_bool_deviation_event_tupleE -> *)
(*   utils:uniform_perm_key_tuple_pushforward -> *)
(*   utils:serfling_uniform_perm_pair_deviation_tail -> bb84:bb84_bbkey -> *)
(*   bb84:stat -> bb84:bb84_secret *)
Local Lemma tuple_bool_holdout_countE (d : bitstr N) (pi : 'S_N) :
  tuple_bool_holdout_count d (perm_bool_holdout_tuple pi) = perm_bool_holdout_count d pi.
Proof.
  rewrite /tuple_bool_holdout_count /perm_bool_holdout_tuple /perm_bool_holdout_count.
  apply: eq_bigl => i.
  by rewrite tnth_mktuple.
Qed.

(* The sample/holdout comparison is exactly the centered holdout-count
   threshold that the Serfling mgf controls.  This version uses only positivity-preserving
   multiplications and one final scalar normalization, avoiding the brittle
   cast-cancellation route on `%:R` expressions. *)
(* perm_bool_deviation_event_tupleE *)
(* infra: no tex label — fundamental & reusable (mathcomp-style) *)
(* consumer: perm_bool_deviation_event_tupleE is used downstream by the BB84 secrecy proof. *)
(* path: utils:perm_bool_deviation_event_tupleE -> *)
(*   utils:uniform_perm_key_tuple_pushforward -> *)
(*   utils:serfling_uniform_perm_pair_deviation_tail -> bb84:bb84_bbkey -> *)
(*   bb84:stat -> bb84:bb84_secret *)
Local Lemma perm_bool_deviation_event_tupleE (d : bitstr N) (mu : R) (pi : 'S_N) :
  (0 < n)%N ->
  (0 < k)%N ->
  (pi \in perm_bool_deviation_event d mu) =
    (perm_bool_holdout_tuple pi \in tuple_bool_deviation_event d mu).
Proof.
  move=> Hn_pos Hk_pos.
  rewrite !inE.
  rewrite /perm_bool_deviation_event /tuple_bool_deviation_event /perm_bool_holdout_err.
  rewrite /perm_bool_sample_err /tuple_bool_centered_over_k /= tuple_bool_holdout_countE.
  set x := (perm_bool_holdout_count d pi)%:R.
  set y := (perm_bool_sample_count d pi)%:R.
  set m := (perm_bool_pop_count d)%:R.
  have HmE : m = y + x.
  {
    rewrite /m /x /y.
    rewrite (perm_bool_partition_countE d pi).
    rewrite natrD.
    reflexivity.
  }
  have HnR_pos : 0 < n%:R :> R by rewrite ltr0n.
  have HkR_pos : 0 < k%:R :> R by rewrite ltr0n.
  have HNR_pos : 0 < N%:R :> R.
  {
    rewrite ltr0n /N.
    by rewrite addn_gt0 Hn_pos orbT.
  }
  apply/idP/idP.
  - move=> Hbad.
    have H1 : (y / k%:R + mu) * n%:R <= x / n%:R * n%:R.
    {
      rewrite (ler_pM2r HnR_pos).
      exact: Hbad.
    }
    have H2 : ((y / k%:R + mu) * n%:R) * k%:R <= (x / n%:R * n%:R) * k%:R.
    {
      rewrite (ler_pM2r HkR_pos).
      exact: H1.
    }
    have H3 : y * n%:R + mu * n%:R * k%:R <= x * k%:R.
    {
      move: H2.
      have Hlhs :
          ((y / k%:R + mu) * n%:R) * k%:R =
          y * n%:R + mu * n%:R * k%:R :> R.
      {
        have Hk_unit : k%:R \is a GRing.unit := unitf_gt0 HkR_pos.
        have Hdiv : y / k%:R * k%:R = y :> R.
        {
          exact: (divrK Hk_unit y).
        }
        have Hterm1 :
            y / k%:R * (n%:R * k%:R) = y * n%:R :> R.
        {
          rewrite [n%:R * k%:R]mulrC.
          rewrite mulrA.
          rewrite Hdiv.
          reflexivity.
        }
        have Hterm2 :
            mu * (n%:R * k%:R) = mu * n%:R * k%:R :> R.
        {
          rewrite mulrA.
          reflexivity.
        }
        rewrite -mulrA.
        rewrite mulrDl.
        rewrite Hterm1 Hterm2.
        reflexivity.
      }
      have Hrhs : (x / n%:R * n%:R) * k%:R = x * k%:R :> R.
      {
        have Hn_unit : n%:R \is a GRing.unit := unitf_gt0 HnR_pos.
        have Hdivn : x / n%:R * n%:R = x :> R := divrK Hn_unit x.
        rewrite Hdivn.
        reflexivity.
      }
      rewrite Hlhs Hrhs.
      done.
    }
    have H4 : mu * n%:R * k%:R <= x * k%:R - y * n%:R.
    {
      have H3' := H3.
      have Htmp : 0 <= x * k%:R - (y * n%:R + mu * n%:R * k%:R).
      {
        rewrite subr_ge0.
        exact: H3'.
      }
      have Hexpr :
          x * k%:R - (y * n%:R + mu * n%:R * k%:R) =
          (x * k%:R - y * n%:R) - mu * n%:R * k%:R :> R.
      {
        rewrite opprD addrA.
        reflexivity.
      }
      rewrite -subr_ge0.
      rewrite -Hexpr.
      exact: Htmp.
    }
    have H5 : mu * n%:R * k%:R <= x * N%:R - n%:R * m.
    {
      rewrite HmE.
      move: H4.
      have -> : x * N%:R - n%:R * (y + x) = x * k%:R - y * n%:R :> R.
      {
        have HNx : x * N%:R = x * k%:R + x * n%:R :> R.
        {
          rewrite /N natrD mulrDr addrC.
          reflexivity.
        }
        have HNy : n%:R * (y + x) = x * n%:R + y * n%:R :> R.
        {
          rewrite mulrDr.
          rewrite [n%:R * y]mulrC [n%:R * x]mulrC.
          rewrite addrC.
          reflexivity.
        }
        rewrite HNx HNy.
        rewrite addrKA.
        reflexivity.
      }
      done.
    }
    have H6 : mu * n%:R * k%:R / N%:R <= x - n%:R * m / N%:R.
    {
      rewrite ler_pdivrMr; last exact: HNR_pos.
      have HN_unit : N%:R \is a GRing.unit := unitf_gt0 HNR_pos.
      have Hrhs :
          (x - n%:R * m / N%:R) * N%:R = x * N%:R - n%:R * m :> R.
      {
        rewrite mulrBl.
        rewrite (divrK HN_unit (n%:R * m)).
        reflexivity.
      }
      rewrite Hrhs.
      exact: H5.
    }
    have Hk_unit : k%:R \is a GRing.unit := unitf_gt0 HkR_pos.
    have Hlhsk :
        (n%:R * mu / N%:R) * k%:R = mu * n%:R * k%:R / N%:R :> R.
    {
      have HN_ne0 : N%:R != 0 := lt0r_neq0 HNR_pos.
      have HN_unit : N%:R \is a GRing.unit := unitf_gt0 HNR_pos.
      have Hleft :
          ((n%:R * mu / N%:R) * k%:R) * N%:R = (n%:R * mu) * k%:R :> R.
      {
        rewrite -mulrA.
        rewrite [k%:R * N%:R]mulrC.
        rewrite mulrA.
        rewrite (divrK HN_unit (n%:R * mu)).
        reflexivity.
      }
      have Hright :
          (mu * n%:R * k%:R / N%:R) * N%:R = mu * n%:R * k%:R :> R.
      {
        exact: (divrK HN_unit (mu * n%:R * k%:R)).
      }
      apply: (mulIf HN_ne0).
      rewrite Hleft Hright.
      rewrite [n%:R * mu]mulrC.
      reflexivity.
    }
    have Hscaled :
        (n%:R * mu / N%:R) * k%:R <= x - n%:R * m / N%:R.
    {
      rewrite Hlhsk.
      exact: H6.
    }
    have Hgoal : n%:R * mu / N%:R <= (x - n%:R * m / N%:R) / k%:R.
    {
      rewrite ler_pdivlMr.
      - exact: Hscaled.
      - exact: HkR_pos.
    }
    apply/andP.
    split.
    - exact: perm_bool_holdout_tuple_uniq.
    - exact: Hgoal.
  - move=> /andP[_ Htuple].
    have H1 : (n%:R * mu / N%:R) * k%:R <=
      ((x - n%:R * m / N%:R) / k%:R) * k%:R.
    {
      rewrite (ler_pM2r HkR_pos).
      exact: Htuple.
    }
    have H2 : mu * n%:R * k%:R / N%:R <= x - n%:R * m / N%:R.
    {
      have HN_unit : N%:R \is a GRing.unit := unitf_gt0 HNR_pos.
      have HN_ne0 : N%:R != 0 := lt0r_neq0 HNR_pos.
      have Hk_unit : k%:R \is a GRing.unit := unitf_gt0 HkR_pos.
      have Hlhsk :
          (n%:R * mu / N%:R) * k%:R = mu * n%:R * k%:R / N%:R :> R.
      {
        have Hleft :
            ((n%:R * mu / N%:R) * k%:R) * N%:R = (n%:R * mu) * k%:R :> R.
        {
          rewrite -mulrA.
          rewrite [k%:R * N%:R]mulrC.
          rewrite mulrA.
          rewrite (divrK HN_unit (n%:R * mu)).
          reflexivity.
        }
        have Hright :
            (mu * n%:R * k%:R / N%:R) * N%:R = mu * n%:R * k%:R :> R.
        {
          exact: (divrK HN_unit (mu * n%:R * k%:R)).
        }
        apply: (mulIf HN_ne0).
        rewrite Hleft Hright.
        rewrite [n%:R * mu]mulrC.
        reflexivity.
      }
      have Hrhs :
          ((x - n%:R * m / N%:R) / k%:R) * k%:R =
          x - n%:R * m / N%:R :> R.
      {
        exact: (divrK Hk_unit (x - n%:R * m / N%:R)).
      }
      move: H1.
      rewrite Hrhs Hlhsk.
      done.
    }
    have H3 : (mu * n%:R * k%:R / N%:R) * N%:R <=
      (x - n%:R * m / N%:R) * N%:R.
    {
      rewrite (ler_pM2r HNR_pos).
      exact: H2.
    }
    have H4 : mu * n%:R * k%:R <= x * N%:R - n%:R * m.
    {
      have HN_unit : N%:R \is a GRing.unit := unitf_gt0 HNR_pos.
      have Hlhs :
          (mu * n%:R * k%:R / N%:R) * N%:R = mu * n%:R * k%:R :> R.
      {
        exact: (divrK HN_unit (mu * n%:R * k%:R)).
      }
      have Hrhs :
          (x - n%:R * m / N%:R) * N%:R = x * N%:R - n%:R * m :> R.
      {
        rewrite mulrBl.
        rewrite (divrK HN_unit (n%:R * m)).
        reflexivity.
      }
      rewrite -Hlhs -Hrhs.
      exact: H3.
    }
    have H5 : mu * n%:R * k%:R <= x * k%:R - y * n%:R.
    {
      rewrite HmE in H4.
      move: H4.
      have -> : x * N%:R - n%:R * (y + x) = x * k%:R - y * n%:R :> R.
      {
        have HNx : x * N%:R = x * k%:R + x * n%:R :> R.
        {
          rewrite /N natrD mulrDr addrC.
          reflexivity.
        }
        have HNy : n%:R * (y + x) = x * n%:R + y * n%:R :> R.
        {
          rewrite mulrDr.
          rewrite [n%:R * y]mulrC [n%:R * x]mulrC.
          rewrite addrC.
          reflexivity.
        }
        rewrite HNx HNy.
        rewrite addrKA.
        reflexivity.
      }
      done.
    }
    have H6 : y * n%:R + mu * n%:R * k%:R <= x * k%:R.
    {
      have H5' := H5.
      have Htmp : 0 <= (x * k%:R - y * n%:R) - mu * n%:R * k%:R.
      {
        rewrite subr_ge0.
        exact: H5'.
      }
      have Hexpr :
          x * k%:R - (y * n%:R + mu * n%:R * k%:R) =
          (x * k%:R - y * n%:R) - mu * n%:R * k%:R :> R.
      {
        rewrite opprD addrA.
        reflexivity.
      }
      rewrite -subr_ge0.
      rewrite Hexpr.
      exact: Htmp.
    }
    have H7 : ((y / k%:R + mu) * n%:R) * k%:R <= (x / n%:R * n%:R) * k%:R.
    {
      have Hk_unit : k%:R \is a GRing.unit := unitf_gt0 HkR_pos.
      have Hn_unit : n%:R \is a GRing.unit := unitf_gt0 HnR_pos.
      have Hlhs :
          ((y / k%:R + mu) * n%:R) * k%:R =
          y * n%:R + mu * n%:R * k%:R :> R.
      {
        have Hdiv : y / k%:R * k%:R = y :> R.
        {
          exact: (divrK Hk_unit y).
        }
        have Hterm1 :
            y / k%:R * (n%:R * k%:R) = y * n%:R :> R.
        {
          rewrite [n%:R * k%:R]mulrC.
          rewrite mulrA.
          rewrite Hdiv.
          reflexivity.
        }
        have Hterm2 :
            mu * (n%:R * k%:R) = mu * n%:R * k%:R :> R.
        {
          rewrite mulrA.
          reflexivity.
        }
        rewrite -mulrA.
        rewrite mulrDl.
        rewrite Hterm1 Hterm2.
        reflexivity.
      }
      have Hrhs : (x / n%:R * n%:R) * k%:R = x * k%:R :> R.
      {
        have Hdivn : x / n%:R * n%:R = x :> R := divrK Hn_unit x.
        rewrite Hdivn.
        reflexivity.
      }
      move: H6.
      rewrite -Hlhs -Hrhs.
      done.
    }
    have H8 : (y / k%:R + mu) * n%:R <= x / n%:R * n%:R.
    {
      have Hk_neq0 : k%:R != 0 := lt0r_neq0 HkR_pos.
      have H8' :
          (y / k%:R + mu) * n%:R <=
          ((x / n%:R * n%:R) * k%:R) / k%:R.
      {
        rewrite ler_pdivlMr.
        - exact: H7.
        - exact: HkR_pos.
      }
      rewrite (mulfK Hk_neq0) in H8'.
      exact: H8'.
    }
    have H9 : y / k%:R + mu <= x / n%:R.
    {
      have Hn_neq0 : n%:R != 0 := lt0r_neq0 HnR_pos.
      have H9' : y / k%:R + mu <= (x / n%:R * n%:R) / n%:R.
      {
        rewrite ler_pdivlMr.
        - exact: H8.
        - exact: HnR_pos.
      }
      rewrite (mulfK Hn_neq0) in H9'.
      exact: H9'.
    }
    by [].
Qed.

(* The pair view wraps two total bitstrings around the mismatch-string
   population view while keeping the split generic: first `k` entries are the
   sample block and last `n` entries are the holdout block. *)
(* perm_pair_sample *)
(* infra: no tex label — fundamental & reusable (mathcomp-style) *)
(* consumer: perm_pair_sample is used downstream by the BB84 secrecy proof. *)
Definition perm_pair_sample (z : bitstr N) (pi : 'S_N) : bitstr k :=
  fun i => z (pi (@lshift k n i)).

(* perm_pair_holdout *)
(* infra: no tex label — fundamental & reusable (mathcomp-style) *)
(* consumer: perm_pair_holdout is used downstream by the BB84 secrecy proof. *)
Definition perm_pair_holdout (z : bitstr N) (pi : 'S_N) : bitstr n :=
  fun i => z (pi (@rshift k n i)).

(* perm_pair_assemble *)
(* infra: no tex label — inverse of the sample/holdout split. *)
(* consumer: used by the Born-derived BB84 distribution semantics. *)
Definition perm_pair_assemble
    (pi : 'S_N) (sample : bitstr k) (holdout : bitstr n) : bitstr N :=
  fun m =>
    match split ((pi^-1)%g m) with
    | inl i => sample i
    | inr j => holdout j
    end.

Lemma perm_pair_sample_assemble
    (pi : 'S_N) (sample : bitstr k) (holdout : bitstr n) :
  perm_pair_sample (perm_pair_assemble pi sample holdout) pi = sample.
Proof.
  apply/funext=> i.
  rewrite /perm_pair_sample /perm_pair_assemble permK.
  by rewrite splitEl.
Qed.

Lemma perm_pair_holdout_assemble
    (pi : 'S_N) (sample : bitstr k) (holdout : bitstr n) :
  perm_pair_holdout (perm_pair_assemble pi sample holdout) pi = holdout.
Proof.
  apply/funext=> i.
  rewrite /perm_pair_holdout /perm_pair_assemble permK.
  by rewrite splitEr.
Qed.

Lemma perm_pair_assembleK (z : bitstr N) (pi : 'S_N) :
  perm_pair_assemble pi (perm_pair_sample z pi) (perm_pair_holdout z pi) = z.
Proof.
  apply/funext=> m.
  rewrite /perm_pair_assemble /perm_pair_sample /perm_pair_holdout.
  case E: (split ((pi^-1)%g m)) => [i|j].
  - have Hm : (pi^-1)%g m = @lshift k n i.
    {
      apply: (can_inj splitK).
      by rewrite E splitEl.
    }
    by rewrite -Hm permKV.
  - have Hm : (pi^-1)%g m = @rshift k n j.
    {
      apply: (can_inj splitK).
      by rewrite E splitEr.
    }
    by rewrite -Hm permKV.
Qed.

Lemma perm_pair_assemble_holdout_ord_inj
    (pi : 'S_N) (sample : bitstr k) :
  injective
    (fun w : 'I_(2 ^ n) =>
      bitstring_to_ord (perm_pair_assemble pi sample (ord_to_bitstring w))).
Proof.
  move=> w1 w2 Hord.
  have Hbits :
      perm_pair_assemble pi sample (ord_to_bitstring w1) =
      perm_pair_assemble pi sample (ord_to_bitstring w2).
  {
    have := congr1 (@ord_to_bitstring N) Hord.
    by rewrite !ord_to_bitstringK.
  }
  have Hhold := congr1 (fun z => perm_pair_holdout z pi) Hbits.
  rewrite !perm_pair_holdout_assemble in Hhold.
  have := congr1 (@bitstring_to_ord n) Hhold.
  by rewrite !bitstring_to_ordK.
Qed.

Definition perm_pair_split_ord (pi : 'S_N)
    (z : 'I_(2 ^ N)) : 'I_(2 ^ k) * 'I_(2 ^ n) :=
  (bitstring_to_ord (perm_pair_sample (ord_to_bitstring z) pi),
   bitstring_to_ord (perm_pair_holdout (ord_to_bitstring z) pi)).

Definition perm_pair_assemble_ord (pi : 'S_N)
    (aw : 'I_(2 ^ k) * 'I_(2 ^ n)) : 'I_(2 ^ N) :=
  bitstring_to_ord
    (perm_pair_assemble pi (ord_to_bitstring aw.1) (ord_to_bitstring aw.2)).

Lemma perm_pair_assemble_ordK (pi : 'S_N) :
  cancel (perm_pair_split_ord pi) (perm_pair_assemble_ord pi).
Proof.
  move=> z.
  rewrite /perm_pair_split_ord /perm_pair_assemble_ord /=.
  rewrite !ord_to_bitstringK perm_pair_assembleK.
  exact: bitstring_to_ordK.
Qed.

Lemma perm_pair_split_ordK (pi : 'S_N) :
  cancel (perm_pair_assemble_ord pi) (perm_pair_split_ord pi).
Proof.
  move=> [a w].
  rewrite /perm_pair_split_ord /perm_pair_assemble_ord /=.
  congr (_, _).
  - by rewrite ord_to_bitstringK perm_pair_sample_assemble bitstring_to_ordK.
  - by rewrite ord_to_bitstringK perm_pair_holdout_assemble bitstring_to_ordK.
Qed.

Lemma perm_pair_sum_split_ord {V : zmodType}
    (pi : 'S_N) (F : 'I_(2 ^ N) -> V) :
  \sum_(z : 'I_(2 ^ N)) F z =
  \sum_(a : 'I_(2 ^ k)) \sum_(w : 'I_(2 ^ n))
    F (perm_pair_assemble_ord pi (a, w)).
Proof.
  rewrite pair_big /=.
  apply: reindex => /=.
  exists (perm_pair_split_ord pi).
  - move=> [a w] _.
    exact: perm_pair_split_ordK.
  - move=> z _.
    exact: perm_pair_assemble_ordK.
Qed.

(* perm_pair_sample_count *)
(* infra: no tex label — fundamental & reusable (mathcomp-style) *)
(* consumer: perm_pair_sample_count is used downstream by the BB84 secrecy proof. *)
Definition perm_pair_sample_count
  (z z' : bitstr N) (pi : 'S_N) : nat :=
  d_ham (perm_pair_sample z pi) (perm_pair_sample z' pi).

(* perm_pair_holdout_count *)
(* infra: no tex label — fundamental & reusable (mathcomp-style) *)
(* consumer: perm_pair_holdout_count is used downstream by the BB84 secrecy proof. *)
Definition perm_pair_holdout_count
  (z z' : bitstr N) (pi : 'S_N) : nat :=
  d_ham (perm_pair_holdout z pi) (perm_pair_holdout z' pi).

(* perm_pair_sample_err *)
(* infra: no tex label — fundamental & reusable (mathcomp-style) *)
(* consumer: perm_pair_sample_err is used downstream by the BB84 secrecy proof. *)
Definition perm_pair_sample_err
  (z z' : bitstr N) (pi : 'S_N) : R :=
  (perm_pair_sample_count z z' pi)%:R / k%:R.

(* perm_pair_sample_le_event *)
(* infra: no tex label — fundamental & reusable (mathcomp-style) *)
Definition perm_pair_sample_le_event (z z' : bitstr N) (Qtol : R) : {set 'S_N} :=
  [set pi : 'S_N | perm_pair_sample_err z z' pi <= Qtol].

(* perm_pair_sample_le_prob *)
(* infra: no tex label — fundamental & reusable (mathcomp-style) *)
Definition perm_pair_sample_le_prob (z z' : bitstr N) (Qtol : R) : R :=
  Pr_event (fun pi : 'S_N => @uniform_perm_mu N pi)
    (perm_pair_sample_le_event z z' Qtol).

(* path: utils:perm_pair_sample_le_probE -> *)
(*   utils:serfling_uniform_perm_pair_deviation_tail -> bb84:bb84_bbkey -> *)
(*   bb84:stat -> bb84:bb84_secret *)
Lemma perm_pair_sample_le_probE (z z' : bitstr N) (Qtol : R) :
  perm_pair_sample_le_prob z z' Qtol =
  Pr_event (fun pi : 'S_N => @uniform_perm_mu N pi)
    [set pi : 'S_N | perm_pair_sample_err z z' pi <= Qtol].
Proof.
  by rewrite /perm_pair_sample_le_prob /perm_pair_sample_le_event.
Qed.

(* perm_pair_holdout_err *)
(* infra: no tex label — fundamental & reusable (mathcomp-style) *)
(* consumer: perm_pair_holdout_err is used downstream by the BB84 secrecy proof. *)
Definition perm_pair_holdout_err
  (z z' : bitstr N) (pi : 'S_N) : R :=
  (perm_pair_holdout_count z z' pi)%:R / n%:R.

(* perm_pair_deviation_event *)
(* infra: no tex label — fundamental & reusable (mathcomp-style) *)
(* consumer: perm_pair_deviation_event is used downstream by the BB84 secrecy proof. *)
Definition perm_pair_deviation_event (z z' : bitstr N) (mu : R) : {set 'S_N} :=
  [set pi : 'S_N | perm_pair_holdout_err z z' pi >= perm_pair_sample_err z z' pi + mu].

(* The mismatch population for the pair `(z,z')` is the XOR string.
   This lets the BB84-facing pair tail reduce to the single Boolean-population
   Serfling theorem below. *)
(* pair_mismatch_string *)
(* infra: no tex label — fundamental & reusable (mathcomp-style) *)
(* consumer: pair_mismatch_string is used downstream by the BB84 secrecy proof. *)
Definition pair_mismatch_string (z z' : bitstr N) : bitstr N :=
  xor_str z z'.

(* perm_pair_sample_countE *)
(* infra: no tex label — fundamental & reusable (mathcomp-style) *)
(* consumer: perm_pair_sample_countE is used downstream by the BB84 secrecy proof. *)
(* path: utils:perm_pair_sample_countE -> utils:perm_pair_sample_errE -> *)
(*   utils:perm_pair_deviation_eventE -> *)
(*   utils:serfling_uniform_perm_pair_deviation_tail -> bb84:bb84_bbkey -> *)
(*   bb84:stat -> bb84:bb84_secret *)
Lemma perm_pair_sample_countE
  (z z' : bitstr N) (pi : 'S_N) :
  perm_pair_sample_count z z' pi =
    perm_bool_sample_count (pair_mismatch_string z z') pi.
Proof.
  rewrite /perm_pair_sample_count /perm_bool_sample_count /pair_mismatch_string.
  rewrite /d_ham /wt_ham /perm_pair_sample /xor_str.
  rewrite -sum1_card.
  apply: eq_bigl => i.
  rewrite inE.
  case: (z (pi (@lshift k n i)));
    case: (z' (pi (@lshift k n i))); reflexivity.
Qed.

(* perm_pair_holdout_countE *)
(* infra: no tex label — fundamental & reusable (mathcomp-style) *)
(* consumer: perm_pair_holdout_countE is used downstream by the BB84 secrecy proof. *)
(* path: utils:perm_pair_holdout_countE -> utils:perm_pair_holdout_errE -> *)
(*   utils:perm_pair_deviation_eventE -> *)
(*   utils:serfling_uniform_perm_pair_deviation_tail -> bb84:bb84_bbkey -> *)
(*   bb84:stat -> bb84:bb84_secret *)
Lemma perm_pair_holdout_countE
  (z z' : bitstr N) (pi : 'S_N) :
  perm_pair_holdout_count z z' pi =
    perm_bool_holdout_count (pair_mismatch_string z z') pi.
Proof.
  rewrite /perm_pair_holdout_count /perm_bool_holdout_count /pair_mismatch_string.
  rewrite /d_ham /wt_ham /perm_pair_holdout /xor_str.
  rewrite -sum1_card.
  apply: eq_bigl => i.
  rewrite inE.
  case: (z (pi (@rshift k n i)));
    case: (z' (pi (@rshift k n i))); reflexivity.
Qed.

(* perm_pair_sample_errE *)
(* infra: no tex label — fundamental & reusable (mathcomp-style) *)
(* consumer: perm_pair_sample_errE is used downstream by the BB84 secrecy proof. *)
(* path: utils:perm_pair_sample_errE -> utils:perm_pair_deviation_eventE -> *)
(*   utils:serfling_uniform_perm_pair_deviation_tail -> bb84:bb84_bbkey -> *)
(*   bb84:stat -> bb84:bb84_secret *)
Lemma perm_pair_sample_errE
  (z z' : bitstr N) (pi : 'S_N) :
  perm_pair_sample_err z z' pi =
    perm_bool_sample_err (pair_mismatch_string z z') pi.
Proof.
  rewrite /perm_pair_sample_err /perm_bool_sample_err.
  by rewrite perm_pair_sample_countE.
Qed.

(* perm_pair_holdout_errE *)
(* infra: no tex label — fundamental & reusable (mathcomp-style) *)
(* consumer: perm_pair_holdout_errE is used downstream by the BB84 secrecy proof. *)
(* path: utils:perm_pair_holdout_errE -> utils:perm_pair_deviation_eventE -> *)
(*   utils:serfling_uniform_perm_pair_deviation_tail -> bb84:bb84_bbkey -> *)
(*   bb84:stat -> bb84:bb84_secret *)
Lemma perm_pair_holdout_errE
  (z z' : bitstr N) (pi : 'S_N) :
  perm_pair_holdout_err z z' pi =
    perm_bool_holdout_err (pair_mismatch_string z z') pi.
Proof.
  rewrite /perm_pair_holdout_err /perm_bool_holdout_err.
  by rewrite perm_pair_holdout_countE.
Qed.

(* perm_pair_deviation_eventE *)
(* infra: no tex label — fundamental & reusable (mathcomp-style) *)
(* consumer: perm_pair_deviation_eventE is used downstream by the BB84 secrecy proof. *)
(* path: utils:perm_pair_deviation_eventE -> *)
(*   utils:serfling_uniform_perm_pair_deviation_tail -> bb84:bb84_bbkey -> *)
(*   bb84:stat -> bb84:bb84_secret *)
Lemma perm_pair_deviation_eventE
  (z z' : bitstr N) (mu : R) :
  perm_pair_deviation_event z z' mu =
    perm_bool_deviation_event (pair_mismatch_string z z') mu.
Proof.
  apply/setP => pi.
  rewrite !inE.
  by rewrite perm_pair_holdout_errE perm_pair_sample_errE.
Qed.

(* --- Total-count / total-err on the pair and partition identities --- *)

(* perm_pair_total_count *)
(* infra: no tex label — fundamental & reusable (mathcomp-style) *)
(* consumer: perm_pair_total_count is used downstream by the BB84 secrecy proof. *)
Definition perm_pair_total_count (z z' : bitstr N) : nat :=
  d_ham z z'.

(* perm_pair_total_err *)
(* infra: no tex label — fundamental & reusable (mathcomp-style) *)
(* consumer: perm_pair_total_err is used downstream by the BB84 secrecy proof. *)
Definition perm_pair_total_err (z z' : bitstr N) (_ : 'S_N) : R :=
  (perm_pair_total_count z z')%:R / N%:R.

(* tex: Nat. Commun. 3:634 (2012), Suppl. (Lemma 3 proof) (integer partition d_ham = pe + key)             *)
(* perm_pair_partition_countE *)
(* infra: no tex label — fundamental & reusable (mathcomp-style) *)
(* consumer: perm_pair_partition_countE is used downstream by the BB84 secrecy proof. *)
(* path: utils:perm_pair_partition_countE -> *)
(*   utils:serfling_uniform_perm_pair_deviation_tail -> bb84:bb84_bbkey -> *)
(*   bb84:stat -> bb84:bb84_secret *)
Lemma perm_pair_partition_countE (z z' : bitstr N) (pi : 'S_N) :
  perm_pair_total_count z z' =
    perm_pair_sample_count z z' pi + perm_pair_holdout_count z z' pi.
Proof.
  rewrite /perm_pair_total_count /perm_pair_sample_count /perm_pair_holdout_count.
  rewrite /d_ham /wt_ham /xor_str /perm_pair_sample /perm_pair_holdout.
  rewrite -sum1_card -!sum1_card.
  rewrite !big_mkcond.
  rewrite (reindex_perm pi) /=.
  rewrite big_split_ord /=.
  rewrite -!big_mkcond.
  congr (_ + _).
  - apply: eq_bigl => i.
    by rewrite !inE.
  - apply: eq_bigl => i.
    by rewrite !inE.
Qed.

(* tex: Nat. Commun. 3:634 (2012), Suppl. (Lemma 3 proof) (real-valued N-scaled form)                       *)

End PermutationBooleanPopulation.

Section SerflingTail.

Variables (n k : nat).

Local Notation N := (k + n)%N.

(* The Serfling induction is more stable on prefixes of ordered unique tuples
   of the fixed ambient type `'I_N` than on a shrinking `'I_(N - m)` type. *)
(* tuple_uniform_mu_m *)
(* infra: no tex label — fundamental & reusable (mathcomp-style) *)
(* consumer: tuple_uniform_mu_m is used downstream by the BB84 secrecy proof. *)
Local Definition tuple_uniform_mu_m {m : nat} (t : m.-tuple 'I_N) : R :=
  if uniq t then ((N ^_ m)%:R)^-1 else 0.

(* tuple_bool_holdout_count_m *)
(* infra: no tex label — fundamental & reusable (mathcomp-style) *)
(* consumer: tuple_bool_holdout_count_m is used downstream by the BB84 secrecy proof. *)
Local Definition tuple_bool_holdout_count_m {m : nat}
  (d : bitstr N) (t : m.-tuple 'I_N) : nat :=
  \sum_(i < m | d (tnth t i)) 1%N.

(* tuple_serfling_Zstar *)
(* infra: no tex label — fundamental & reusable (mathcomp-style) *)
(* consumer: tuple_serfling_Zstar is used downstream by the BB84 secrecy proof. *)
Local Definition tuple_serfling_Zstar {m : nat}
  (d : bitstr N) (t : m.-tuple 'I_N) : R :=
  ((tuple_bool_holdout_count_m d t)%:R -
    m%:R * (perm_bool_pop_count d)%:R / N%:R) / (N - m)%:R.

(* tuple_prefix_mean *)
(* infra: no tex label — fundamental & reusable (mathcomp-style) *)
(* consumer: tuple_prefix_mean is used downstream by the BB84 secrecy proof. *)
Local Definition tuple_prefix_mean {m : nat}
  (d : bitstr N) (t : m.-tuple 'I_N) : R :=
  (perm_bool_pop_count d)%:R / N%:R - tuple_serfling_Zstar d t.

(* tuple_uniform_mu_m_nonneg *)
(* infra: no tex label — fundamental & reusable (mathcomp-style) *)
(* consumer: tuple_uniform_mu_m_nonneg is used downstream by the BB84 secrecy proof. *)
(* path: utils:tuple_uniform_mu_m_nonneg -> utils:tuple_serfling_mgf_step -> *)
(*   utils:tuple_serfling_mgf_bound -> *)
(*   utils:serfling_uniform_tuple_bool_tail -> *)
(*   utils:serfling_uniform_perm_pair_deviation_tail -> bb84:bb84_bbkey -> *)
(*   bb84:stat -> bb84:bb84_secret *)
Local Lemma tuple_uniform_mu_m_nonneg m (t : m.-tuple 'I_N) :
  0 <= tuple_uniform_mu_m t.
Proof.
  rewrite /tuple_uniform_mu_m.
  case: ifP => _.
  - by rewrite invr_ge0 ler0n.
  - by rewrite lexx.
Qed.

(* tuple_uniform_mu_m_sum1 *)
(* infra: no tex label — fundamental & reusable (mathcomp-style) *)
(* consumer: tuple_uniform_mu_m_sum1 is used downstream by the BB84 secrecy proof. *)
(* path: utils:tuple_uniform_mu_m_sum1 -> utils:tuple_serfling_mgf_bound -> *)
(*   utils:serfling_uniform_tuple_bool_tail -> *)
(*   utils:serfling_uniform_perm_pair_deviation_tail -> bb84:bb84_bbkey -> *)
(*   bb84:stat -> bb84:bb84_secret *)
Local Lemma tuple_uniform_mu_m_sum1 m :
  (m <= N)%N ->
  \sum_(t : m.-tuple 'I_N) tuple_uniform_mu_m t = 1.
Proof.
  move=> HmN.
  rewrite /tuple_uniform_mu_m.
  rewrite -big_mkcond.
  have Hfall_pos : 0 < (N ^_ m)%:R :> R.
  {
    rewrite ltr0n ffact_gt0.
    exact: HmN.
  }
  rewrite big_const.
  have -> :
      #|[pred t : m.-tuple 'I_N | uniq t]| =
      #|[set t : m.-tuple 'I_N | all predT t & uniq t]|.
  {
    apply: eq_card => t.
    by rewrite !inE all_predT andTb.
  }
  rewrite card_uniq_tuples.
  have HcardT : #|(@predT 'I_N)| = #|'I_N|.
  {
    rewrite eq_cardT.
    - reflexivity.
    - by move=> i.
  }
  rewrite HcardT card_ord iter_addr_0.
  have Hnatmul_mul (x : R) (r : nat) :
      x *+ r = x * r%:R.
  {
    elim: r => [|r IHr].
    - by rewrite mulr0n mulr0.
    - rewrite mulrSr -addn1 natrD mulrDr IHr.
      by rewrite mulr1.
  }
  rewrite Hnatmul_mul.
  by rewrite mulVf ?lt0r_neq0.
Qed.

(* tuple_bool_holdout_count_m_rconsE *)
(* infra: no tex label — fundamental & reusable (mathcomp-style) *)
(* consumer: tuple_bool_holdout_count_m_rconsE is used downstream by the BB84 secrecy proof. *)
(* path: utils:tuple_bool_holdout_count_m_rconsE -> *)
(*   utils:tuple_serfling_Zstar_rconsE -> utils:tuple_serfling_exp_rconsE -> *)
(*   utils:tuple_serfling_mgf_step -> utils:tuple_serfling_mgf_bound -> *)
(*   utils:serfling_uniform_tuple_bool_tail -> *)
(*   utils:serfling_uniform_perm_pair_deviation_tail -> bb84:bb84_bbkey -> *)
(*   bb84:stat -> bb84:bb84_secret *)
Local Lemma tuple_bool_holdout_count_m_rconsE m (d : bitstr N)
  (t : m.-tuple 'I_N) (x : 'I_N) :
  tuple_bool_holdout_count_m d [tuple of rcons t x] =
    tuple_bool_holdout_count_m d t + d x.
Proof.
  rewrite /tuple_bool_holdout_count_m.
  rewrite big_mkcond big_ord_recr /= -big_mkcond tnthN.
  rewrite (eq_bigl (fun i : 'I_m => d (tnth t i))).
  2:{
    move=> i.
    by rewrite tnthNS.
  }
  have -> : (if d x then 1%N else 0%N) = d x :> nat.
  {
    by case: (d x).
  }
  reflexivity.
Qed.

(* tuple_mem_imsetE *)
(* infra: no tex label — fundamental & reusable (mathcomp-style) *)
(* consumer: tuple_mem_imsetE is used downstream by the BB84 secrecy proof. *)
(* path: utils:tuple_mem_imsetE -> utils:tuple_complement_card -> *)
(*   utils:tuple_step_mgf_le -> utils:tuple_serfling_mgf_step -> *)
(*   utils:tuple_serfling_mgf_bound -> *)
(*   utils:serfling_uniform_tuple_bool_tail -> *)
(*   utils:serfling_uniform_perm_pair_deviation_tail -> bb84:bb84_bbkey -> *)
(*   bb84:stat -> bb84:bb84_secret *)
Local Lemma tuple_mem_imsetE m (t : m.-tuple 'I_N) (x : 'I_N) :
  (x \in t) = (x \in (tnth t) @: (predT : pred 'I_m)).
Proof.
  apply/idP/idP.
  - move=> Hx.
    have Hex : exists i : 'I_m, x = tnth t i.
    {
      apply/(tnthP t x).
      exact: Hx.
    }
    case: Hex => i ->.
    apply/imsetP.
    exists i.
    - by [].
    - reflexivity.
  - move=> /imsetP [i _ ->].
    exact: mem_tnth.
Qed.

(* tuple_bool_holdout_count_m_memE *)
(* infra: no tex label — fundamental & reusable (mathcomp-style) *)
(* consumer: tuple_bool_holdout_count_m_memE is used downstream by the BB84 secrecy proof. *)
(* path: utils:tuple_bool_holdout_count_m_memE -> *)
(*   utils:tuple_bool_partition_count_mE -> *)
(*   utils:tuple_prefix_mean_remainingE -> utils:tuple_step_mgf_le -> *)
(*   utils:tuple_serfling_mgf_step -> utils:tuple_serfling_mgf_bound -> *)
(*   utils:serfling_uniform_tuple_bool_tail -> *)
(*   utils:serfling_uniform_perm_pair_deviation_tail -> bb84:bb84_bbkey -> *)
(*   bb84:stat -> bb84:bb84_secret *)
Local Lemma tuple_bool_holdout_count_m_memE m (d : bitstr N)
  (t : m.-tuple 'I_N) :
  uniq t ->
  tuple_bool_holdout_count_m d t =
    \sum_(x : 'I_N | (x \in t) && d x) 1%N.
Proof.
  move=> Huniq.
  have Htnth_inj : injective (tnth t).
  {
    move/(tuple_uniqP t): Huniq.
    exact.
  }
  have Hsum :
      \sum_(x in (tnth t) @: (predT : pred 'I_m) | d x) 1%N =
      \sum_(i in (predT : pred 'I_m) | d (tnth t i)) 1%N.
  {
    rewrite (@big_imset_cond nat 0%N addn 'I_m 'I_N
      (tnth t) (predT : pred 'I_m) (fun x : 'I_N => d x)
      (fun _ : 'I_N => 1%N)).
    reflexivity.
    move=> i j _ _ Hij.
    exact: Htnth_inj.
  }
  rewrite /tuple_bool_holdout_count_m -Hsum.
  apply: eq_bigl => x.
  by rewrite (tuple_mem_imsetE t x) andbC.
Qed.

(* tuple_complement_card *)
(* infra: no tex label — fundamental & reusable (mathcomp-style) *)
(* consumer: tuple_complement_card is used downstream by the BB84 secrecy proof. *)
(* path: utils:tuple_complement_card -> utils:tuple_step_mgf_le -> *)
(*   utils:tuple_serfling_mgf_step -> utils:tuple_serfling_mgf_bound -> *)
(*   utils:serfling_uniform_tuple_bool_tail -> *)
(*   utils:serfling_uniform_perm_pair_deviation_tail -> bb84:bb84_bbkey -> *)
(*   bb84:stat -> bb84:bb84_secret *)
Local Lemma tuple_complement_card m (t : m.-tuple 'I_N) :
  uniq t ->
  #|predC (mem t)| = (N - m)%N.
Proof.
  move=> Huniq.
  have Htnth_inj : injective (tnth t).
  {
    move/(tuple_uniqP t): Huniq.
    exact.
  }
  have Hcard_mem : #|[set x in mem t]| = m.
  {
    rewrite cardsE.
    have Hset_card :
        #|mem t| =
        #|(tnth t) @: (predT : pred 'I_m)|.
    {
      apply: eq_card => x.
      exact: tuple_mem_imsetE.
    }
    have Himg_card : #|(tnth t) @: (predT : pred 'I_m)| = m.
    {
      rewrite card_imset ?cardsT ?card_ord //.
    }
    exact: (eq_trans Hset_card Himg_card).
  }
  have Hcomp_card : #|~: [set x in mem t]| = (N - m)%N.
  {
    have Hsum : (#|~: [set x in mem t]| + m = N)%N.
    {
      have Hcards := cardsC [set x in mem t].
      rewrite card_ord Hcard_mem addnC in Hcards.
      exact: Hcards.
    }
    have Hle : (m <= N)%N.
    {
      have Hle0 : (#|[set x in mem t]| <= #|'I_N|)%N.
      {
        exact: max_card.
      }
      rewrite Hcard_mem card_ord in Hle0.
      exact: Hle0.
    }
    have Hsub : ((N - m)%N + m = N)%N.
    {
      rewrite addnC.
      exact: subnKC Hle.
    }
    have Hlhs : (#|~: [set x in mem t]| + m = (N - m)%N + m)%N.
    {
      rewrite Hsum Hsub.
      reflexivity.
    }
    have Hcancel := addIn Hlhs.
    exact: Hcancel.
  }
  have HpredC : #|predC (mem t)| = #|~: [set x in mem t]|.
  {
    apply: eq_card => x.
    apply/idP/idP.
    - move=> Hx.
      rewrite inE.
      rewrite inE.
      exact: Hx.
    - move=> Hx.
      move: Hx.
      rewrite inE.
      rewrite inE.
      move=> Hx.
      exact: Hx.
  }
  rewrite HpredC.
  rewrite Hcomp_card.
  reflexivity.
Qed.

(* tuple_bool_partition_count_mE *)
(* infra: no tex label — fundamental & reusable (mathcomp-style) *)
(* consumer: tuple_bool_partition_count_mE is used downstream by the BB84 secrecy proof. *)
(* path: utils:tuple_bool_partition_count_mE -> *)
(*   utils:tuple_prefix_mean_remainingE -> utils:tuple_step_mgf_le -> *)
(*   utils:tuple_serfling_mgf_step -> utils:tuple_serfling_mgf_bound -> *)
(*   utils:serfling_uniform_tuple_bool_tail -> *)
(*   utils:serfling_uniform_perm_pair_deviation_tail -> bb84:bb84_bbkey -> *)
(*   bb84:stat -> bb84:bb84_secret *)
Local Lemma tuple_bool_partition_count_mE m (d : bitstr N)
  (t : m.-tuple 'I_N) :
  uniq t ->
  (perm_bool_pop_count d =
    \sum_(x : 'I_N | (x \notin t) && d x) 1%N +
    tuple_bool_holdout_count_m d t)%N.
Proof.
  move=> Huniq.
  rewrite /perm_bool_pop_count (bigID (fun x : 'I_N => x \in t)) /=.
  have Hleft :
      \sum_(x : 'I_N | d x && (x \in t)) 1%N =
      tuple_bool_holdout_count_m d t.
  {
    have Hmem := @tuple_bool_holdout_count_m_memE m d t Huniq.
    rewrite (eq_bigl (fun x : 'I_N => (x \in t) && d x)).
    - exact: (esym Hmem).
    - move=> x.
      by rewrite andbC.
  }
  have Hright :
      \sum_(x : 'I_N | d x && ~~ (x \in t)) 1%N =
      \sum_(x : 'I_N | (x \notin t) && d x) 1%N.
  {
    apply: eq_bigl => x.
    by rewrite andbC.
  }
  rewrite Hleft Hright addnC.
  reflexivity.
Qed.

(* tuple_prefix_mean_remainingE *)
(* infra: no tex label — fundamental & reusable (mathcomp-style) *)
(* consumer: tuple_prefix_mean_remainingE is used downstream by the BB84 secrecy proof. *)
(* path: utils:tuple_prefix_mean_remainingE -> utils:tuple_step_mgf_le -> *)
(*   utils:tuple_serfling_mgf_step -> utils:tuple_serfling_mgf_bound -> *)
(*   utils:serfling_uniform_tuple_bool_tail -> *)
(*   utils:serfling_uniform_perm_pair_deviation_tail -> bb84:bb84_bbkey -> *)
(*   bb84:stat -> bb84:bb84_secret *)
Local Lemma tuple_prefix_mean_remainingE m (d : bitstr N)
  (t : m.-tuple 'I_N) :
  uniq t ->
  (m < N)%N ->
  tuple_prefix_mean d t =
    (\sum_(x : 'I_N | (x \notin t) && d x) 1%N)%:R / (N - m)%:R.
Proof.
  move=> Huniq HmN.
  set rem := \sum_(x : 'I_N | (x \notin t) && d x) 1%N.
  set cnt := tuple_bool_holdout_count_m d t.
  set pop := perm_bool_pop_count d.
  have Hpart : (pop = rem + cnt)%N.
  {
    rewrite /pop /rem /cnt.
    exact: tuple_bool_partition_count_mE.
  }
  have HNm_pos : 0 < (N - m)%:R :> R.
  {
    by rewrite ltr0n subn_gt0.
  }
  have HNm_unit : (N - m)%:R \is a GRing.unit := unitf_gt0 HNm_pos.
  have HNR_pos : 0 < N%:R :> R.
  {
    rewrite ltr0n.
    case: N HmN => [|N'] //=.
  }
  have HNR_unit : N%:R \is a GRing.unit := unitf_gt0 HNR_pos.
  apply: (mulIf (lt0r_neq0 HNm_pos)).
  rewrite /tuple_prefix_mean /tuple_serfling_Zstar /rem /cnt /pop.
  rewrite mulrBl.
  rewrite (divrK HNm_unit (_)).
  set popR := (perm_bool_pop_count d)%:R.
  set cntR := (tuple_bool_holdout_count_m d t)%:R.
  set p := popR / N%:R.
  have Hsplit : p * (N - m)%:R = popR - p * m%:R.
  {
    have HpN : p * N%:R = popR.
    {
      rewrite /p.
      exact: (divrK HNR_unit popR).
    }
    have HNatR : (m + (N - m))%:R = N%:R :=
      congr1 (fun x : nat => x%:R : R) (subnKC (ltnW HmN)).
    have Hmul := congr1 (fun z : R => p * z) HNatR.
    rewrite natrD mulrDr in Hmul.
    rewrite HpN in Hmul.
    have Hmul' := congr1 (fun z : R => - (p * m%:R) + z) Hmul.
    rewrite addrA addNr add0r in Hmul'.
    rewrite addrC in Hmul'.
    exact: Hmul'.
  }
  rewrite Hsplit /p /popR /cntR.
  have Hcancel :
      m%:R * ((perm_bool_pop_count d)%:R / N%:R) =
      (perm_bool_pop_count d)%:R / N%:R * m%:R :> R.
  {
    rewrite mulrC.
    reflexivity.
  }
  rewrite opprB -[m%:R * (perm_bool_pop_count d)%:R / N%:R]mulrA Hcancel.
  rewrite -!addrA addKr.
  have HpartNat :
      (perm_bool_pop_count d =
        \sum_(x : 'I_N | (x \notin t) && d x) 1%N +
        tuple_bool_holdout_count_m d t)%N.
  {
    exact: Hpart.
  }
  have HpartR0 :
      (perm_bool_pop_count d)%:R =
        (\sum_(x : 'I_N | (x \notin t) && d x) 1%N +
         tuple_bool_holdout_count_m d t)%:R :=
    congr1 (fun x : nat => x%:R : R) HpartNat.
  have Hpart_sub :=
    congr1 (fun z : R => z - (tuple_bool_holdout_count_m d t)%:R) HpartR0.
  rewrite natrD addrK in Hpart_sub.
  rewrite /rem /cnt in Hpart_sub.
  rewrite Hpart_sub.
  rewrite (divrK HNm_unit (_)).
  reflexivity.
Qed.

(* tuple_prefix_mean_bounds *)
(* infra: no tex label — fundamental & reusable (mathcomp-style) *)
(* consumer: tuple_prefix_mean_bounds is used downstream by the BB84 secrecy proof. *)
(* path: utils:tuple_prefix_mean_bounds -> utils:tuple_step_mgf_le -> *)
(*   utils:tuple_serfling_mgf_step -> utils:tuple_serfling_mgf_bound -> *)
(*   utils:serfling_uniform_tuple_bool_tail -> *)
(*   utils:serfling_uniform_perm_pair_deviation_tail -> bb84:bb84_bbkey -> *)
(*   bb84:stat -> bb84:bb84_secret *)
Local Lemma tuple_prefix_mean_bounds m (d : bitstr N)
  (t : m.-tuple 'I_N) :
  uniq t ->
  (m < N)%N ->
  0 <= tuple_prefix_mean d t <= 1.
Proof.
  move=> Huniq HmN.
  have Hden_pos : 0 < (N - m)%:R :> R.
  {
    by rewrite ltr0n subn_gt0.
  }
  rewrite tuple_prefix_mean_remainingE //.
  apply/andP.
  split.
  - apply: divr_ge0.
    + exact: ler0n.
    + exact: (ltW Hden_pos).
  - rewrite ler_pdivrMr.
    + rewrite mul1r.
      change
        (((\sum_(x : 'I_N | (x \notin t) && d x) 1%N)%:R : R) <=
         ((N - m)%N)%:R).
      rewrite ler_nat.
      have Hcard :
          \sum_(x : 'I_N | (x \notin t) && d x) 1%N =
          #|[set x : 'I_N | x \notin t & d x]|.
      {
        rewrite sum1dep_card.
        reflexivity.
      }
      rewrite Hcard.
      have Hsubset :
          [set x : 'I_N | x \notin t & d x] :<=: predC (mem t).
      {
        apply/mathcomp.boot.fintype.subsetP => x.
        rewrite !inE.
        by move=> /andP[].
      }
      have Hle :
          (#|[set x : 'I_N | x \notin t & d x]| <= #|predC (mem t)|)%N.
      {
        exact: subset_leq_card Hsubset.
      }
      have Hcomp : (#|predC (mem t)| <= (N - m)%N)%N.
      {
        by rewrite tuple_complement_card.
      }
      exact: leq_trans Hle Hcomp.
    + rewrite ltr0n.
      by rewrite subn_gt0.
Qed.

(* tuple_serfling_Zstar_rconsE *)
(* infra: no tex label — fundamental & reusable (mathcomp-style) *)
(* consumer: tuple_serfling_Zstar_rconsE is used downstream by the BB84 secrecy proof. *)
(* path: utils:tuple_serfling_Zstar_rconsE -> *)
(*   utils:tuple_serfling_exp_rconsE -> utils:tuple_serfling_mgf_step -> *)
(*   utils:tuple_serfling_mgf_bound -> *)
(*   utils:serfling_uniform_tuple_bool_tail -> *)
(*   utils:serfling_uniform_perm_pair_deviation_tail -> bb84:bb84_bbkey -> *)
(*   bb84:stat -> bb84:bb84_secret *)
Local Lemma tuple_serfling_Zstar_rconsE m (d : bitstr N)
  (t : m.-tuple 'I_N) (x : 'I_N) :
  (m.+1 < N)%N ->
  tuple_serfling_Zstar d [tuple of rcons t x] =
    tuple_serfling_Zstar d t +
    ((d x)%:R - tuple_prefix_mean d t) / (N - m.+1)%:R.
Proof.
  move=> Hm1N.
  have HmN : (m < N)%N.
  {
    exact: ltn_trans (ltnSn m) Hm1N.
  }
  have HNm_pos : 0 < (N - m)%:R :> R.
  {
    by rewrite ltr0n subn_gt0.
  }
  have HNm1_pos : 0 < (N - m.+1)%:R :> R.
  {
    by rewrite ltr0n subn_gt0.
  }
  have HNm_unit : (N - m)%:R \is a GRing.unit := unitf_gt0 HNm_pos.
  have HNm1_unit : (N - m.+1)%:R \is a GRing.unit := unitf_gt0 HNm1_pos.
  pose a : R := (tuple_bool_holdout_count_m d t)%:R.
  pose p : R := (perm_bool_pop_count d)%:R / N%:R.
  pose z : R := (a - m%:R * p) / (N - m)%:R.
  have Hcount :
      (tuple_bool_holdout_count_m d [tuple of rcons t x])%:R =
      a + (d x)%:R.
  {
    rewrite tuple_bool_holdout_count_m_rconsE.
    rewrite natrD.
    reflexivity.
  }
  rewrite /tuple_prefix_mean /tuple_serfling_Zstar /=.
  rewrite Hcount.
  rewrite /z.
  have HNm1E : (N - m)%:R = (N - m.+1)%:R + (1 : R).
  {
    have Hnat : (N - m)%N = (N - m.+1).+1.
    {
      by rewrite subnSK.
    }
    have HnatR : (N - m)%:R = ((N - m.+1).+1)%:R :=
      congr1 (fun z0 : nat => z0%:R : R) Hnat.
    have Hsucc : ((N - m.+1).+1)%:R = (N - m.+1)%:R + (1 : R).
    {
      rewrite -[X in X%:R]addn1 natrD natr1.
      reflexivity.
    }
    have Htmp := HnatR.
    rewrite Hsucc in Htmp.
    exact: Htmp.
  }
  have Hzden :
      z * (N - m.+1)%:R + z = a - m%:R * p.
  {
    have Hfact :
        z * ((N - m.+1)%:R + 1) = z * (N - m.+1)%:R + z.
    {
      rewrite mulrDr mulr1.
      reflexivity.
    }
    rewrite -Hfact.
    rewrite -HNm1E.
    rewrite divrK //.
  }
  have Hm1p : m.+1%:R * p = m%:R * p + p.
  {
    have Hm1cast : m.+1%:R = m%:R + (1 : R).
    {
      rewrite -[m.+1]addn1 natrD natr1.
      reflexivity.
    }
    rewrite Hm1cast mulrDl mul1r.
    reflexivity.
  }
  apply: (mulIf (lt0r_neq0 HNm1_pos)).
  rewrite [X in X = _]divrK //.
  rewrite mulrDl.
  rewrite [X in _ = _ + X]divrK //.
  rewrite opprB.
  rewrite -/p -/z.
  have Hzsub_occ :
      (d x)%:R +
      ((((tuple_bool_holdout_count_m d t)%:R -
         m%:R * (perm_bool_pop_count d)%:R / N%:R) / (N - m)%:R) - p) =
      (d x)%:R + (z - p).
  {
    rewrite /z /a /p.
    rewrite mulrA.
    reflexivity.
  }
  rewrite [X in _ = _ + X]Hzsub_occ.
  have Hstep2 :
      (d x)%:R + (z - p) = ((d x)%:R + z) - p.
  {
    rewrite addrA.
    reflexivity.
  }
  rewrite [in RHS]Hstep2.
  have Hzmul_occ :
      (((tuple_bool_holdout_count_m d t)%:R -
         m%:R * (perm_bool_pop_count d)%:R / N%:R) / (N - m)%:R *
       (N - m.+1)%:R)%R =
      z * (N - m.+1)%:R.
  {
    rewrite /z /a /p.
    rewrite mulrA.
    reflexivity.
  }
  rewrite [X in _ = X + _]Hzmul_occ.
  have Hstep3 :
      z * (N - m.+1)%:R + (((d x)%:R + z) - p) =
      z * (N - m.+1)%:R + (z + ((d x)%:R - p)).
  {
    have -> :
        ((d x)%:R + z) - p = z + ((d x)%:R - p).
    {
      rewrite addrA.
      rewrite [((d x)%:R + z)]addrC.
      rewrite -addrA.
      reflexivity.
    }
    reflexivity.
  }
  rewrite [in RHS]Hstep3.
  have Hrhs_den :
      z * (N - m.+1)%:R + (z + ((d x)%:R - p)) =
      (z * (N - m.+1)%:R + z) + ((d x)%:R - p).
  {
    rewrite -addrA.
    reflexivity.
  }
  rewrite [in RHS]Hrhs_den.
  rewrite [in RHS]Hzden.
  have Hm1p_occ :
      m.+1%:R * (perm_bool_pop_count d)%:R / N%:R = m.+1%:R * p.
  {
    rewrite /p mulrA.
    reflexivity.
  }
  rewrite Hm1p_occ.
  rewrite Hm1p.
  have Hfinal :
      (a + (d x)%:R) - ((m%:R * p) + p) =
      (a - m%:R * p) + ((d x)%:R - p).
  {
    rewrite opprD.
    rewrite addrACA.
    reflexivity.
  }
  rewrite Hfinal.
  reflexivity.
Qed.

(* tuple_uniform_mu_m_rconsE *)
(* infra: no tex label — fundamental & reusable (mathcomp-style) *)
(* consumer: tuple_uniform_mu_m_rconsE is used downstream by the BB84 secrecy proof. *)
(* path: utils:tuple_uniform_mu_m_rconsE -> utils:tuple_uniform_mu_m_stepE -> *)
(*   utils:tuple_serfling_mgf_step -> utils:tuple_serfling_mgf_bound -> *)
(*   utils:serfling_uniform_tuple_bool_tail -> *)
(*   utils:serfling_uniform_perm_pair_deviation_tail -> bb84:bb84_bbkey -> *)
(*   bb84:stat -> bb84:bb84_secret *)
Local Lemma tuple_uniform_mu_m_rconsE m (t : m.-tuple 'I_N) (x : 'I_N) :
  tuple_uniform_mu_m [tuple of rcons t x] =
    tuple_uniform_mu_m t *
      (if x \in t then 0 else ((N - m)%:R)^-1).
Proof.
  rewrite /tuple_uniform_mu_m rcons_uniq.
  case Ht : (uniq t); case Hx : (x \in t).
  - rewrite /= mulr0.
    reflexivity.
  - have HmN : (m < N)%N.
    {
      have Hcard_pos : (0 < #|predC (mem t)|)%N.
      {
        apply/card_gt0P.
        exists x.
        rewrite inE.
        case Hmem : (x \in t).
        - move: Hx.
          by rewrite Hmem.
        - change (~~ (x \in t)).
          by rewrite Hmem.
      }
      move: Hcard_pos.
      rewrite tuple_complement_card // subn_gt0.
      exact.
    }
    have Hfall_pos : 0 < (N ^_ m)%:R :> R.
    {
      rewrite ltr0n ffact_gt0.
      exact: ltnW HmN.
    }
    have HNm_pos : 0 < (N - m)%:R :> R.
    {
      by rewrite ltr0n subn_gt0.
    }
    have Hprod_pos : 0 < ((N ^_ m)%:R * (N - m)%:R) :> R.
    {
      exact: mulr_gt0 Hfall_pos HNm_pos.
    }
    have Hfall_unit : (N ^_ m)%:R \is a GRing.unit := unitf_gt0 Hfall_pos.
    have HNm_unit : (N - m)%:R \is a GRing.unit := unitf_gt0 HNm_pos.
    have Hprod_unit : ((N ^_ m)%:R * (N - m)%:R) \is a GRing.unit :=
      unitf_gt0 Hprod_pos.
    have HinvM :
        ((((N ^_ m)%:R : R) * (N - m)%:R)^-1 : R) =
        (((N ^_ m)%:R)^-1 / (N - m)%:R : R).
    {
      rewrite invfM ?(lt0r_neq0 Hfall_pos) ?(lt0r_neq0 HNm_pos).
      reflexivity.
    }
    rewrite ffactnSr.
    rewrite natrM HinvM.
    reflexivity.
  - rewrite /= mul0r.
    reflexivity.
  - rewrite /= mul0r.
    reflexivity.
Qed.

(* tuple_sum_rconsE *)
(* infra: no tex label — fundamental & reusable (mathcomp-style) *)
(* consumer: tuple_sum_rconsE is used downstream by the BB84 secrecy proof. *)
(* path: utils:tuple_sum_rconsE -> utils:tuple_uniform_mu_m_stepE -> *)
(*   utils:tuple_serfling_mgf_step -> utils:tuple_serfling_mgf_bound -> *)
(*   utils:serfling_uniform_tuple_bool_tail -> *)
(*   utils:serfling_uniform_perm_pair_deviation_tail -> bb84:bb84_bbkey -> *)
(*   bb84:stat -> bb84:bb84_secret *)
Local Lemma tuple_sum_rconsE m (F : m.+1.-tuple 'I_N -> R) :
  \sum_(u : m.+1.-tuple 'I_N) F u =
    \sum_(x : 'I_N) \sum_(t : m.-tuple 'I_N) F [tuple of rcons t x].
Proof.
  rewrite pair_big /=.
  apply: reindex => /=.
  exists (fun s : m.+1.-tuple 'I_N => (tlast s, [tuple of tfirst s])).
  - move=> xt _.
    case: xt => x t /=.
    rewrite /tlast tnthN /=.
    f_equal.
    apply/val_inj => /=.
    exact: tfirst_rcons.
  - move=> s _.
    rewrite /= -tupleN_eta.
    reflexivity.
Qed.

(* tuple_uniform_mu_m_stepE *)
(* infra: no tex label — fundamental & reusable (mathcomp-style) *)
(* consumer: tuple_uniform_mu_m_stepE is used downstream by the BB84 secrecy proof. *)
(* path: utils:tuple_uniform_mu_m_stepE -> utils:tuple_serfling_mgf_step -> *)
(*   utils:tuple_serfling_mgf_bound -> *)
(*   utils:serfling_uniform_tuple_bool_tail -> *)
(*   utils:serfling_uniform_perm_pair_deviation_tail -> bb84:bb84_bbkey -> *)
(*   bb84:stat -> bb84:bb84_secret *)
Local Lemma tuple_uniform_mu_m_stepE m (F : m.+1.-tuple 'I_N -> R) :
  \sum_(u : m.+1.-tuple 'I_N) tuple_uniform_mu_m u * F u =
    \sum_(x : 'I_N) \sum_(t : m.-tuple 'I_N)
      (tuple_uniform_mu_m t *
        (if x \in t then 0 else ((N - m)%:R)^-1)) * F [tuple of rcons t x].
Proof.
  rewrite tuple_sum_rconsE.
  apply: eq_bigr => x _.
  apply: eq_bigr => t _.
  rewrite tuple_uniform_mu_m_rconsE.
  reflexivity.
Qed.

(* Local: arithmetic helper for the MGF induction step. *)
(* sumr_const_pred *)
(* infra: no tex label — fundamental & reusable (mathcomp-style) *)
(* consumer: sumr_const_pred is used downstream by the BB84 secrecy proof. *)
(* path: utils:sumr_const_pred -> utils:uniform_perm_key_tuple_pushforward -> *)
(*   utils:serfling_uniform_perm_pair_deviation_tail -> bb84:bb84_bbkey -> *)
(*   bb84:stat -> bb84:bb84_secret *)
Local Lemma sumr_const_pred {A : finType} (P : pred A) (c : R) :
  \sum_(x : A | P x) c = (\sum_(x : A | P x) 1%N)%:R * c.
Proof.
  rewrite big_const GRing.iter_addr_0.
  rewrite -cardsE -sum1dep_card.
  rewrite mulr_natl.
  reflexivity.
Qed.

(* tuple_step_mgf_le *)
(* infra: no tex label — fundamental & reusable (mathcomp-style) *)
(* consumer: tuple_step_mgf_le is used downstream by the BB84 secrecy proof. *)
(* path: utils:tuple_step_mgf_le -> utils:tuple_serfling_mgf_step -> *)
(*   utils:tuple_serfling_mgf_bound -> *)
(*   utils:serfling_uniform_tuple_bool_tail -> *)
(*   utils:serfling_uniform_perm_pair_deviation_tail -> bb84:bb84_bbkey -> *)
(*   bb84:stat -> bb84:bb84_secret *)
Local Lemma tuple_step_mgf_le m (d : bitstr N) (t : m.-tuple 'I_N) (lambda : R) :
  uniq t ->
  (m.+1 < N)%N ->
  0 <= lambda ->
  \sum_(x : 'I_N)
    (if x \in t then 0 else ((N - m)%:R)^-1) *
      expR (lambda *
        (((d x)%:R - tuple_prefix_mean d t) / (N - m.+1)%:R)) <=
    expR (lambda ^+ 2 / (8%:R * ((N - m.+1)%:R)^+2)).
Proof.
  move=> Huniq Hm1N Hlambda.
  have HmN : (m < N)%N.
  {
    exact: ltn_trans (ltnSn m) Hm1N.
  }
  pose p := tuple_prefix_mean d t.
  pose rem := \sum_(x : 'I_N | (x \notin t) && d x) 1%N.
  pose comp : R := (N - m)%:R.
  pose tau : R := lambda / (N - m.+1)%:R.
  have Hp_bounds : 0 <= p <= 1.
  {
    exact: tuple_prefix_mean_bounds Huniq HmN.
  }
  have Htau_nonneg : 0 <= tau.
  {
    rewrite /tau.
    apply: divr_ge0.
    - exact: Hlambda.
    - by rewrite ler0n.
  }
  have HpE : p = rem%:R / comp.
  {
    rewrite /p /rem /comp.
    exact: tuple_prefix_mean_remainingE Huniq HmN.
  }
  have Hcomp_pos : 0 < comp :> R.
  {
    rewrite /comp ltr0n subn_gt0.
    exact: HmN.
  }
  have Hcomp_unit : comp \is a GRing.unit := unitf_gt0 Hcomp_pos.
  have Hrem_le : (rem <= N - m)%N.
  {
    rewrite /rem.
    have Hcard :
        \sum_(x : 'I_N | (x \notin t) && d x) 1%N =
        #|[set x : 'I_N | x \notin t & d x]|.
    {
      rewrite sum1dep_card.
      reflexivity.
    }
    rewrite Hcard.
    have Hsubset :
        [set x : 'I_N | x \notin t & d x] :<=: predC (mem t).
    {
      apply/mathcomp.boot.fintype.subsetP => x.
      rewrite !inE.
      by move=> /andP[].
    }
    have Hle :
        (#|[set x : 'I_N | x \notin t & d x]| <= #|predC (mem t)|)%N.
    {
      exact: subset_leq_card Hsubset.
    }
    rewrite tuple_complement_card // in Hle.
  }
  have Hnotin_false :
      \sum_(x : 'I_N | ~~ (x \notin t))
        (if x \in t then 0 else ((N - m)%:R)^-1) *
          expR (lambda * (((d x)%:R - p) / (N - m.+1)%:R)) = 0.
  {
    apply: big1 => x.
    move=> Hx.
    rewrite negbK in Hx.
    rewrite Hx mul0r.
    reflexivity.
  }
  rewrite (bigID (fun x : 'I_N => x \notin t)) /= Hnotin_false addr0.
  rewrite (bigID d) /=.
  have Hone :
      \sum_(x : 'I_N | d x && (x \notin t))
        (if x \in t then 0 else ((N - m)%:R)^-1) *
          expR (lambda * (((d x)%:R - p) / (N - m.+1)%:R)) =
      (rem%:R / comp) * expR ((1 - p) * tau).
  {
    transitivity
      (\sum_(x : 'I_N | d x && (x \notin t))
        (((N - m)%:R)^-1 * expR ((1 - p) * tau))).
    - apply: eq_bigr => x.
      move=> /andP [Hdx Hxt].
      move/negPf: Hxt => Hxt.
      move: Hdx => /= Hdx.
      rewrite Hxt.
      have -> : (d x)%:R = 1 :> R.
      {
        by rewrite Hdx.
      }
      rewrite /tau.
      have -> :
          lambda * ((1 - p) / (N - m.+1)%:R) =
          (1 - p) * (lambda / (N - m.+1)%:R).
      {
        rewrite mulrA.
        rewrite [lambda * (1 - p)]mulrC.
        rewrite -mulrA.
        reflexivity.
      }
      reflexivity.
    - have HremE :
          \sum_(x : 'I_N | d x && (x \notin t)) 1%N = rem.
      {
        rewrite /rem.
        apply: eq_bigl => y.
        by rewrite andbC.
      }
      rewrite sumr_const_pred.
      rewrite HremE.
      rewrite -mulrA.
      congr (_ * _).
  }
  have Hzero_count :
      \sum_(x : 'I_N | ~~ d x && (x \notin t)) 1%N = (N - m - rem)%N.
  {
    pose z := \sum_(x : 'I_N | ~~ d x && (x \notin t)) 1%N.
    have Hrem_count :
        \sum_(x : 'I_N | d x && (x \notin t)) 1%N = rem.
    {
      rewrite /rem.
      apply: eq_bigl => y.
      by rewrite andbC.
    }
    have Hcomp_count :
        \sum_(x : 'I_N | x \notin t) 1%N = (N - m)%N.
    {
      rewrite (eq_bigl (fun x : 'I_N => predC (mem t) x)).
      2:{
        move=> x.
        by rewrite inE.
      }
      rewrite sum1dep_card cardsE.
      exact: tuple_complement_card Huniq.
    }
    have Hsplit :
        \sum_(x : 'I_N | x \notin t) 1%N =
        \sum_(x : 'I_N | d x && (x \notin t)) 1%N + z.
    {
      rewrite (bigID d) /=.
      rewrite /z.
      congr (_ + _).
      - apply: eq_bigl => y.
        by rewrite andbC.
      - apply: eq_bigl => y.
        by rewrite andbC.
    }
    rewrite Hcomp_count /rem in Hsplit.
    rewrite Hrem_count in Hsplit.
    have Hz : z = (rem + z - rem)%N.
    {
      by rewrite addnC addnK.
    }
    change (z = (N - m - rem)%N).
    rewrite Hz.
    rewrite Hsplit.
    reflexivity.
  }
  have Hzero :
      \sum_(x : 'I_N | ~~ d x && (x \notin t))
        (if x \in t then 0 else ((N - m)%:R)^-1) *
          expR (lambda * (((d x)%:R - p) / (N - m.+1)%:R)) =
      (1 - p) * expR (- p * tau).
  {
    transitivity
      (\sum_(x : 'I_N | ~~ d x && (x \notin t))
        (((N - m)%:R)^-1 * expR (- p * tau))).
    - apply: eq_bigr => x.
      move=> /andP [Hdx Hxt].
      move/negPf: Hxt => Hxt.
      move/negPf: Hdx => Hdx.
      rewrite Hxt Hdx.
      rewrite /tau.
      have -> :
          lambda * ((0 - p) / (N - m.+1)%:R) =
          - p * (lambda / (N - m.+1)%:R).
      {
        rewrite sub0r.
        rewrite mulrA.
        rewrite [lambda * - p]mulrC.
        rewrite -mulrA.
        reflexivity.
      }
      reflexivity.
    - rewrite sumr_const_pred.
      rewrite Hzero_count.
      have HnatrB : (((N - m - rem)%N)%:R : R) = (N - m)%:R - rem%:R.
      {
        have Hsub_nat : ((N - m - rem + rem)%N = (N - m)%N).
        {
          exact: subnK Hrem_le.
        }
        have HsubR :=
          congr1 (fun z : nat => z%:R : R) Hsub_nat.
        rewrite natrD in HsubR.
        have Htmp :=
          congr1 (fun z : R => z - rem%:R) HsubR.
        rewrite addrK in Htmp.
        exact Htmp.
      }
      rewrite HnatrB.
      rewrite mulrBl.
      rewrite !mulrA.
      rewrite [comp * comp^-1]mulrC.
      rewrite (mulVf (lt0r_neq0 Hcomp_pos)).
      rewrite [rem%:R * comp^-1]mulrC HpE.
      rewrite -mulrBl.
      rewrite [comp^-1 * rem%:R]mulrC -HpE.
      reflexivity.
  }
  have Hone' :
      \sum_(x : 'I_N | (x \notin t) && d x)
        (if x \in t then 0 else ((N - m)%:R)^-1) *
          expR (lambda * (((d x)%:R - p) / (N - m.+1)%:R)) =
      p * expR ((1 - p) * tau).
  {
    rewrite (eq_bigl (fun x : 'I_N => d x && (x \notin t))).
    - rewrite Hone.
      rewrite -HpE.
      reflexivity.
    - move=> x.
      by rewrite andbC.
  }
  have Hzero' :
      \sum_(x : 'I_N | (x \notin t) && ~~ d x)
        (if x \in t then 0 else ((N - m)%:R)^-1) *
          expR (lambda * (((d x)%:R - p) / (N - m.+1)%:R)) =
      (1 - p) * expR (- p * tau).
  {
    rewrite (eq_bigl (fun x : 'I_N => ~~ d x && (x \notin t))).
    - rewrite Hzero.
      reflexivity.
    - move=> x.
      by rewrite andbC.
  }
  rewrite Hone' Hzero'.
  have Htau_sq :
      tau ^+ 2 / 8%:R = lambda ^+ 2 / (8%:R * ((N - m.+1)%:R)^+2).
  {
    have Hden_pos : 0 < (N - m.+1)%:R :> R.
    {
      rewrite ltr0n subn_gt0.
      exact: Hm1N.
    }
    have Hden_neq : (N - m.+1)%:R != 0 :> R.
    {
      exact: lt0r_neq0 Hden_pos.
    }
    have H8_neq : 8%:R != 0 :> R.
    {
      by rewrite pnatr_eq0.
    }
    have H8_pos : 0 < 8%:R :> R.
    {
      by rewrite ltr0n.
    }
    have Hden2_pos : 0 < ((N - m.+1)%:R)^+2 :> R.
    {
      rewrite expr2.
      apply: mulr_gt0.
      - exact: Hden_pos.
      - exact: Hden_pos.
    }
    have H8_unit : 8%:R \is a GRing.unit := unitf_gt0 H8_pos.
    have Hden2_unit : ((N - m.+1)%:R)^+2 \is a GRing.unit :=
      unitf_gt0 Hden2_pos.
    have HD_pos : 0 < 8%:R * ((N - m.+1)%:R)^+2 :> R.
    {
      apply: mulr_gt0.
      - exact: H8_pos.
      - exact: Hden2_pos.
    }
    pose den2 : R := ((N - m.+1)%:R)^+2.
    have Htau_sq0 : tau ^+ 2 = lambda ^+ 2 / den2.
    {
      have Hden_unit : (N - m.+1)%:R \is a GRing.unit := unitf_gt0 Hden_pos.
      apply: (mulIr Hden2_unit).
      rewrite /den2.
      rewrite (divrK Hden2_unit (lambda ^+ 2)).
      rewrite expr2.
      have Hpair :
          tau ^+ 2 * ((N - m.+1)%:R * (N - m.+1)%:R) =
          (tau * (N - m.+1)%:R) * (tau * (N - m.+1)%:R).
      {
        pose a : R := (N - m.+1)%:R.
        rewrite expr2.
        have Hstep1 : (tau * tau) * (a * a) = tau * (tau * a) * a.
        {
          rewrite /a -!mulrA.
          reflexivity.
        }
        rewrite Hstep1.
        have Hstep2 : tau * (tau * a) * a = tau * (a * tau) * a.
        {
          rewrite [tau * a]mulrC.
          reflexivity.
        }
        rewrite Hstep2.
        rewrite /a -!mulrA mulrA.
        reflexivity.
      }
      rewrite Hpair.
      rewrite /tau !(divrK Hden_unit lambda).
      rewrite expr2.
      reflexivity.
    }
    have Hdiv8 :
        (lambda ^+ 2 / den2) / 8%:R = lambda ^+ 2 / (8%:R * den2).
    {
      have HD_neq : 8%:R * den2 != 0 :> R.
      {
        exact: lt0r_neq0 HD_pos.
      }
      have HD_unit : (8%:R * den2) \is a GRing.unit := unitf_gt0 HD_pos.
      apply: (mulIf HD_neq).
      rewrite divrK ?HD_unit //.
      rewrite mulrA.
      rewrite divrK ?H8_unit //.
      rewrite divrK ?Hden2_unit //.
    }
    rewrite Htau_sq0.
    exact: Hdiv8.
  }
  have Hbern := bernoulli_centered_mgf_le Hp_bounds Htau_nonneg.
  have Hlhs :
      p * expR ((1 - p) * tau) + (1 - p) * expR (- p * tau) <=
      expR (tau ^+ 2 / 8%:R).
  {
    rewrite addrC.
    exact: Hbern.
  }
  have Hrhs :
      expR (tau ^+ 2 / 8%:R) <=
      expR (lambda ^+ 2 / (8%:R * ((N - m.+1)%:R)^+2)).
  {
    rewrite Htau_sq.
    exact: lexx.
  }
  exact: le_trans Hlhs Hrhs.
Qed.

(* tuple_serfling_exp_rconsE *)
(* infra: no tex label — fundamental & reusable (mathcomp-style) *)
(* consumer: tuple_serfling_exp_rconsE is used downstream by the BB84 secrecy proof. *)
(* path: utils:tuple_serfling_exp_rconsE -> utils:tuple_serfling_mgf_step -> *)
(*   utils:tuple_serfling_mgf_bound -> *)
(*   utils:serfling_uniform_tuple_bool_tail -> *)
(*   utils:serfling_uniform_perm_pair_deviation_tail -> bb84:bb84_bbkey -> *)
(*   bb84:stat -> bb84:bb84_secret *)
Local Lemma tuple_serfling_exp_rconsE m (d : bitstr N)
  (t : m.-tuple 'I_N) (x : 'I_N) (lambda : R) :
  (m.+1 < N)%N ->
  expR (lambda * tuple_serfling_Zstar d [tuple of rcons t x]) =
    expR (lambda * tuple_serfling_Zstar d t) *
    expR (lambda *
      (((d x)%:R - tuple_prefix_mean d t) / (N - m.+1)%:R)).
Proof.
  move=> Hm1N.
  rewrite tuple_serfling_Zstar_rconsE //.
  rewrite mulrDr -expRD.
  reflexivity.
Qed.

(* tuple_serfling_mgf_step *)
(* infra: no tex label — fundamental & reusable (mathcomp-style) *)
(* consumer: tuple_serfling_mgf_step is used downstream by the BB84 secrecy proof. *)
(* path: utils:tuple_serfling_mgf_step -> utils:tuple_serfling_mgf_bound -> *)
(*   utils:serfling_uniform_tuple_bool_tail -> *)
(*   utils:serfling_uniform_perm_pair_deviation_tail -> bb84:bb84_bbkey -> *)
(*   bb84:stat -> bb84:bb84_secret *)
Local Lemma tuple_serfling_mgf_step m (d : bitstr N) (lambda : R) :
  (m.+1 < N)%N ->
  0 <= lambda ->
  \sum_(u : m.+1.-tuple 'I_N)
    tuple_uniform_mu_m u * expR (lambda * tuple_serfling_Zstar d u) <=
    expR (lambda ^+ 2 / (8%:R * ((N - m.+1)%:R)^+2)) *
      \sum_(t : m.-tuple 'I_N)
        tuple_uniform_mu_m t * expR (lambda * tuple_serfling_Zstar d t).
Proof.
  move=> Hm1N Hlambda.
  rewrite tuple_uniform_mu_m_stepE exchange_big.
  rewrite mulr_sumr.
  apply: ler_sum => t _.
  have Hinner :
      \sum_(x : 'I_N)
        (tuple_uniform_mu_m t *
          (if x \in t then 0 else ((N - m)%:R)^-1)) *
          expR (lambda * tuple_serfling_Zstar d [tuple of rcons t x]) <=
      expR (lambda ^+ 2 / (8%:R * ((N - m.+1)%:R)^+2)) *
        (tuple_uniform_mu_m t * expR (lambda * tuple_serfling_Zstar d t)).
  {
    case Huniq_t : (uniq t).
    - have Hmid :
          \sum_(x : 'I_N)
            (tuple_uniform_mu_m t *
              (if x \in t then 0 else ((N - m)%:R)^-1)) *
              expR (lambda * tuple_serfling_Zstar d [tuple of rcons t x]) =
          (tuple_uniform_mu_m t * expR (lambda * tuple_serfling_Zstar d t)) *
            \sum_(x : 'I_N)
              (if x \in t then 0 else ((N - m)%:R)^-1) *
                expR (lambda *
                  (((d x)%:R - tuple_prefix_mean d t) / (N - m.+1)%:R)).
      {
        rewrite mulr_sumr.
        apply: eq_bigr => x _.
        rewrite tuple_serfling_exp_rconsE //.
        have Hterm :
            (tuple_uniform_mu_m t *
              (if x \in t then 0 else ((N - m)%:R)^-1)) *
              (expR (lambda * tuple_serfling_Zstar d t) *
               expR
                 (lambda *
                  (((d x)%:R - tuple_prefix_mean d t) / (N - m.+1)%:R))) =
            (tuple_uniform_mu_m t * expR (lambda * tuple_serfling_Zstar d t)) *
              ((if x \in t then 0 else ((N - m)%:R)^-1) *
               expR
                  (lambda *
                  (((d x)%:R - tuple_prefix_mean d t) / (N - m.+1)%:R))).
        {
          pose mu0 : R := tuple_uniform_mu_m t.
          pose w0 : R := if x \in t then 0 else ((N - m)%:R)^-1.
          pose ez : R := expR (lambda * tuple_serfling_Zstar d t).
          pose ei : R :=
            expR (lambda *
              (((d x)%:R - tuple_prefix_mean d t) / (N - m.+1)%:R)).
          change ((mu0 * w0) * (ez * ei) = (mu0 * ez) * (w0 * ei)).
          have Hstep1 : (mu0 * w0) * (ez * ei) = mu0 * (w0 * ez) * ei.
          {
            rewrite -!mulrA.
            reflexivity.
          }
          rewrite Hstep1.
          have Hstep2 : mu0 * (w0 * ez) * ei = mu0 * (ez * w0) * ei.
          {
            rewrite [w0 * ez]mulrC.
            reflexivity.
          }
          rewrite Hstep2.
          rewrite !mulrA.
          reflexivity.
        }
        rewrite Hterm.
        reflexivity.
      }
      rewrite Hmid.
      rewrite [X in _ <= X]mulrC.
      have Huniq_tP : uniq t.
      {
        by rewrite Huniq_t.
      }
      have Hstep :
          \sum_(x : 'I_N)
            (if x \in t then 0 else ((N - m)%:R)^-1) *
              expR (lambda *
                (((d x)%:R - tuple_prefix_mean d t) / (N - m.+1)%:R)) <=
          expR (lambda ^+ 2 / (8%:R * ((N - m.+1)%:R)^+2)).
      {
        exact: (@tuple_step_mgf_le m d t lambda Huniq_tP Hm1N Hlambda).
      }
      exact: (ler_wpM2l
        (mulr_ge0 (tuple_uniform_mu_m_nonneg t) (ltW (expR_gt0 _)))
        Hstep).
    - rewrite /tuple_uniform_mu_m Huniq_t /=.
      rewrite !mul0r.
      rewrite [X in _ <= X]mulr0.
      have Hzero_sum :
          \sum_(x : 'I_N)
            0 * (if x \in t then 0 else ((N - m)%:R)^-1) *
              expR (lambda * tuple_serfling_Zstar d [tuple of rcons t x]) = 0.
      {
        apply: big1 => x _.
        rewrite [0 * _]mul0r.
        rewrite mul0r.
        reflexivity.
      }
      rewrite Hzero_sum.
      by rewrite lexx.
  }
  exact: Hinner.
Qed.

(* tuple_serfling_mgf_bound *)
(* infra: no tex label — fundamental & reusable (mathcomp-style) *)
(* consumer: tuple_serfling_mgf_bound is used downstream by the BB84 secrecy proof. *)
(* path: utils:tuple_serfling_mgf_bound -> *)
(*   utils:serfling_uniform_tuple_bool_tail -> *)
(*   utils:serfling_uniform_perm_pair_deviation_tail -> bb84:bb84_bbkey -> *)
(*   bb84:stat -> bb84:bb84_secret *)
Local Lemma tuple_serfling_mgf_bound m (d : bitstr N) (lambda : R) :
  (m <= n)%N ->
  (0 < k)%N ->
  0 <= lambda ->
  \sum_(t : m.-tuple 'I_N)
    tuple_uniform_mu_m t * expR (lambda * tuple_serfling_Zstar d t) <=
    expR (\sum_(i < m)
      lambda ^+ 2 / (8%:R * (((N - i).-1)%N%:R)^+2)).
Proof.
  elim: m => [|m IH] Hmn Hk_pos Hlambda.
  - have Hlhs0 :
        \sum_(t : 0.-tuple 'I_N)
          tuple_uniform_mu_m t * expR (lambda * tuple_serfling_Zstar d t) = 1.
    {
      apply: eq_trans.
      + apply: eq_bigr => t _.
        have Hzt : tuple_serfling_Zstar d t = 0.
        {
          rewrite /tuple_serfling_Zstar /tuple_bool_holdout_count_m.
          rewrite big_ord0 mul0r.
          have Hdiv0 : (0 / N%:R : R) = 0.
          {
            rewrite [0 / _]mul0r.
            reflexivity.
          }
          rewrite Hdiv0 subrr.
          rewrite subn0 Hdiv0.
          reflexivity.
        }
        rewrite Hzt mulr0 expR0 mulr1.
        reflexivity.
      + rewrite tuple_uniform_mu_m_sum1 ?leq0n //.
    }
    rewrite Hlhs0 big_ord0 expR0.
    exact: lexx.
  - have HmN : (m.+1 < N)%N.
    {
      have HnN : (n < N)%N.
      {
        rewrite -[n]add0n /N ltn_add2r.
        exact: Hk_pos.
      }
      exact: leq_ltn_trans Hmn HnN.
    }
    have Hm_le_n : (m <= n)%N.
    {
      exact: leq_trans (ltnW (ltnSn m)) Hmn.
    }
    have Hstep := @tuple_serfling_mgf_step m d lambda HmN Hlambda.
    have Hih := IH Hm_le_n Hk_pos Hlambda.
    have Hmult :
        (expR (lambda ^+ 2 / (8%:R * ((N - m.+1)%:R)^+2)) *
          \sum_(t : m.-tuple 'I_N)
            tuple_uniform_mu_m t * expR (lambda * tuple_serfling_Zstar d t)) <=
        (expR (lambda ^+ 2 / (8%:R * ((N - m.+1)%:R)^+2)) *
          expR
            (\sum_(i < m)
               lambda ^+ 2 / (8%:R * (((N - i).-1)%N%:R)^+2))).
    {
      exact: (ler_wpM2l (ltW (expR_gt0 _)) Hih).
    }
    apply: (le_trans Hstep).
    apply: (le_trans Hmult).
    rewrite -expRD ler_expR.
    rewrite big_ord_recr /=.
    rewrite addrC.
    have Hlast :
        (((N - m).-1)%N)%:R = ((N - m.+1)%N)%:R :> R.
    {
      have Hlast_nat : (N - m).-1 = (N - m.+1)%N.
      {
        have Hm_lt_N : (m < N)%N.
        {
          exact: ltn_trans (ltnSn m) HmN.
        }
        have Htmp : (N - m)%N = (N - m.+1).+1.
        {
          symmetry.
          exact: subnSK Hm_lt_N.
        }
        rewrite Htmp.
        reflexivity.
      }
      have HlastR := congr1 (fun z : nat => z%:R : R) Hlast_nat.
      exact: HlastR.
    }
    rewrite Hlast.
    by rewrite lexx.
Qed.

(* tuple_serfling_terminalE *)
(* infra: no tex label — fundamental & reusable (mathcomp-style) *)
(* consumer: tuple_serfling_terminalE is used downstream by the BB84 secrecy proof. *)
(* path: utils:tuple_serfling_terminalE -> *)
(*   utils:serfling_uniform_tuple_bool_tail -> *)
(*   utils:serfling_uniform_perm_pair_deviation_tail -> bb84:bb84_bbkey -> *)
(*   bb84:stat -> bb84:bb84_secret *)
Local Lemma tuple_serfling_terminalE (d : bitstr N) (t : n.-tuple 'I_N) :
  tuple_serfling_Zstar d t = tuple_bool_centered_over_k d t.
Proof.
  rewrite /tuple_serfling_Zstar /tuple_bool_centered_over_k.
  rewrite /tuple_bool_holdout_count_m /tuple_bool_holdout_count.
  rewrite /N addnK.
  reflexivity.
Qed.

(* serfling_inv_square_step *)
(* infra: no tex label — fundamental & reusable (mathcomp-style) *)
(* consumer: serfling_inv_square_step is used downstream by the BB84 secrecy proof. *)
(* path: utils:serfling_inv_square_step -> utils:serfling_square_sum_bound -> *)
(*   utils:serfling_uniform_tuple_bool_tail -> *)
(*   utils:serfling_uniform_perm_pair_deviation_tail -> bb84:bb84_bbkey -> *)
(*   bb84:stat -> bb84:bb84_secret *)
Local Lemma serfling_inv_square_step i :
  (0 < k)%N ->
  ((((k + i)%N)%:R : R)^-2 <=
    (k.+1)%:R / k%:R *
      ((((k + i)%N)%:R : R)^-1 - ((k + i.+1)%N)%:R^-1)).
Proof.
  move=> Hk_pos.
  pose s := (k + i)%N.
  have Hs_ge_k : (k <= s)%N.
  {
    rewrite /s leq_addr.
    reflexivity.
  }
  have HkR_pos : 0 < k%:R :> R by rewrite ltr0n.
  have HsR_pos : 0 < s%:R :> R.
  {
    rewrite /s ltr0n.
    exact: leq_trans Hk_pos (leq_addr i k).
  }
  have Hs1R_pos : 0 < s.+1%:R :> R by rewrite ltr0n.
  have Hss1_pos : 0 < (s%:R * s.+1%:R) :> R.
  {
    exact: mulr_gt0 HsR_pos Hs1R_pos.
  }
  have Hk_unit : k%:R \is a GRing.unit := unitf_gt0 HkR_pos.
  have Hs_unit : s%:R \is a GRing.unit := unitf_gt0 HsR_pos.
  have Hs1_unit : s.+1%:R \is a GRing.unit := unitf_gt0 Hs1R_pos.
  have Hss1_unit : (s%:R * s.+1%:R) \is a GRing.unit := unitf_gt0 Hss1_pos.
  rewrite -(ler_pM2r Hss1_pos).
  have Hlhs_mul :
      ((((s%:R : R)^-2) * (s%:R * s.+1%:R)) : R) =
      (s.+1)%:R / s%:R.
  {
    have Hlhs1 :
        ((((s%:R : R)^-2) * s%:R) : R) = (s%:R)^-1.
    {
      rewrite -exprVn expr2 -mulrA.
      rewrite [s%:R^-1 * s%:R]mulVr //.
      rewrite mulr1.
      reflexivity.
    }
    rewrite mulrA.
    rewrite Hlhs1.
    rewrite mulrC.
    reflexivity.
  }
  have Hdiff_mul :
      (((s%:R)^-1 - (s.+1)%:R^-1) *
        (s%:R * s.+1%:R) : R) = 1.
  {
    rewrite mulrBl.
    have Hterm1 :
        ((s%:R)^-1 * (s%:R * s.+1%:R) : R) = s.+1%:R.
    {
      rewrite mulrA.
      rewrite (mulVr Hs_unit).
      rewrite mul1r.
      reflexivity.
    }
    have Hterm2 :
        ((s.+1)%:R^-1 * (s%:R * s.+1%:R) : R) = s%:R.
    {
      rewrite mulrCA.
      rewrite (mulVr Hs1_unit).
      rewrite mulr1.
      reflexivity.
    }
    rewrite Hterm1 Hterm2.
    rewrite -addn1 natrD.
    rewrite [s%:R + 1]addrC.
    rewrite addrK.
    reflexivity.
  }
  have Hdiff_eq :
      (((s%:R)^-1 - (s.+1)%:R^-1) : R) = (s%:R * s.+1%:R)^-1.
  {
    have Htmp :=
      congr1 (fun x : R => x * (s%:R * s.+1%:R)^-1) Hdiff_mul.
    rewrite mul1r in Htmp.
    rewrite -mulrA (mulrV Hss1_unit) mulr1 in Htmp.
    exact: Htmp.
  }
  rewrite Hlhs_mul.
  have HsE : (((k + i)%N)%:R : R) = s%:R.
  {
    rewrite /s.
    reflexivity.
  }
  have Hs1E : (((k + i.+1)%N)%:R : R) = s.+1%:R.
  {
    rewrite /s addnS.
    reflexivity.
  }
  rewrite HsE Hs1E.
  set d := (((s%:R)^-1 - (s.+1)%:R^-1) : R).
  have Hd : d = (s%:R * s.+1%:R)^-1.
  {
    rewrite /d.
    exact: Hdiff_eq.
  }
  rewrite Hd.
  rewrite divrK //.
  rewrite -(ler_pM2r HsR_pos).
  have Hlhs_last :
      (((s.+1)%:R / s%:R) * s%:R : R) = s.+1%:R.
  {
    rewrite divrK //.
  }
  rewrite Hlhs_last.
  rewrite -(ler_pM2r HkR_pos).
  rewrite mulrC -natrM.
  have Hrhs_last :
      (((k.+1)%:R / k%:R) * s%:R * k%:R : R) =
      (k.+1 * s)%:R.
  {
    rewrite -mulrA.
    rewrite [s%:R * k%:R]mulrC.
    rewrite mulrA.
    rewrite (divrK Hk_unit ((k.+1)%:R)).
    rewrite natrM.
    reflexivity.
  }
  rewrite Hrhs_last.
  rewrite ler_nat.
  rewrite mulnS mulSn.
  have Hrhs_nat : (s + k * s = k * s + s)%N.
  {
    rewrite addnC.
    reflexivity.
  }
  rewrite Hrhs_nat.
  have Hlhs_nat : (k + k * s = k * s + k)%N.
  {
    rewrite addnC.
    reflexivity.
  }
  rewrite Hlhs_nat.
  rewrite leq_add2l.
  exact: Hs_ge_k.
Qed.

(* serfling_inv_telescope *)
(* infra: no tex label — fundamental & reusable (mathcomp-style) *)
(* consumer: serfling_inv_telescope is used downstream by the BB84 secrecy proof. *)
(* path: utils:serfling_inv_telescope -> utils:serfling_square_sum_bound -> *)
(*   utils:serfling_uniform_tuple_bool_tail -> *)
(*   utils:serfling_uniform_perm_pair_deviation_tail -> bb84:bb84_bbkey -> *)
(*   bb84:stat -> bb84:bb84_secret *)
Local Lemma serfling_inv_telescope m :
  \sum_(i < m)
    ((((k + i)%N)%:R : R)^-1 - ((k + i.+1)%N)%:R^-1) =
    k%:R^-1 - (k + m)%:R^-1.
Proof.
  elim: m => [|m IH].
  - rewrite big_ord0 addn0 subrr.
    reflexivity.
  - rewrite big_ord_recr /= IH.
    rewrite addrA.
    rewrite subrK.
    reflexivity.
Qed.

(* serfling_square_sum_bound *)
(* infra: no tex label — fundamental & reusable (mathcomp-style) *)
(* consumer: serfling_square_sum_bound is used downstream by the BB84 secrecy proof. *)
(* path: utils:serfling_square_sum_bound -> *)
(*   utils:serfling_uniform_tuple_bool_tail -> *)
(*   utils:serfling_uniform_perm_pair_deviation_tail -> bb84:bb84_bbkey -> *)
(*   bb84:stat -> bb84:bb84_secret *)
Local Lemma serfling_square_sum_bound :
  (0 < k)%N ->
  \sum_(i < n) ((((N - i).-1)%N)%:R : R)^-2 <=
    n%:R * (k.+1)%:R / (N%:R * (k%:R)^+2).
Proof.
  move=> Hk_pos.
  have Hsum :
      \sum_(i < n) ((((N - i).-1)%N)%:R : R)^-2 =
      \sum_(i < n) (((k + i)%N)%:R : R)^-2.
  {
    rewrite big_ord_rev /=.
    apply: eq_bigr => i _.
    have Hnat :
        (N - rev_ord i).-1 = (k + i)%N.
    {
      have Hrev : (i.+1 + rev_ord i = n)%N.
      {
        rewrite subnKC ?ltn_ord //.
      }
      have HN_sub : (N - rev_ord i = k + i.+1)%N.
      {
        have HauxN :
            (N - rev_ord i + rev_ord i = k + i.+1 + rev_ord i)%N.
        {
          rewrite /N.
          rewrite addnC.
          have Hrev_leN : (rev_ord i <= k + n)%N.
          {
            have Hn_leN : (n <= k + n)%N.
            {
              rewrite addnC.
              exact: leq_addr k n.
            }
            exact: leq_trans (ltnW (ltn_ord (rev_ord i))) Hn_leN.
          }
          rewrite subnKC //.
          rewrite -addnA.
          rewrite Hrev.
          reflexivity.
        }
        exact: addIn HauxN.
      }
      rewrite HN_sub.
      rewrite addnS.
      reflexivity.
    }
    rewrite Hnat.
    reflexivity.
  }
  rewrite Hsum.
  have Hstep_sum :
      \sum_(i < n) (((k + i)%N)%:R : R)^-2 <=
      \sum_(i < n)
        ((k.+1)%:R / k%:R *
          ((((k + i)%N)%:R : R)^-1 - ((k + i.+1)%N)%:R^-1)).
  {
    apply: ler_sum => i _.
    have Hstep_i :
        ((((k + i)%N)%:R : R)^-2 <=
          (k.+1)%:R / k%:R *
            ((((k + i)%N)%:R : R)^-1 - ((k + i.+1)%N)%:R^-1)) :=
      serfling_inv_square_step i Hk_pos.
    exact Hstep_i.
  }
  have Htail :
      \sum_(i < n)
        ((k.+1)%:R / k%:R *
          ((((k + i)%N)%:R : R)^-1 - ((k + i.+1)%N)%:R^-1)) <=
      n%:R * (k.+1)%:R / (N%:R * (k%:R)^+2).
  {
    rewrite -mulr_sumr.
    rewrite (serfling_inv_telescope n).
    have HkR_pos : 0 < k%:R :> R by rewrite ltr0n.
    have HNR_pos : 0 < N%:R :> R.
    {
      rewrite ltr0n /N.
      exact: leq_trans Hk_pos (leq_addr n k).
    }
    have Hk_unit : k%:R \is a GRing.unit := unitf_gt0 HkR_pos.
    have HNR_unit : N%:R \is a GRing.unit := unitf_gt0 HNR_pos.
    have Hdiff :
        (k%:R^-1 - N%:R^-1 : R) = n%:R / (N%:R * k%:R).
    {
      apply: (mulIf (lt0r_neq0 (mulr_gt0 HNR_pos HkR_pos))).
      rewrite mulrBl.
      have H1 :
          (k%:R^-1 * (N%:R * k%:R) : R) = N%:R.
      {
        rewrite mulrCA.
        rewrite (mulVr Hk_unit).
        rewrite mulr1.
        reflexivity.
      }
      have H2 :
          (N%:R^-1 * (N%:R * k%:R) : R) = k%:R.
      {
        rewrite mulrA.
        rewrite (mulVr HNR_unit).
        rewrite mul1r.
        reflexivity.
      }
      rewrite H1 H2.
      rewrite /N natrD.
      rewrite [k%:R + n%:R]addrC.
      rewrite addrK.
      have HNk_pos : 0 < (N%:R * k%:R : R).
      {
        exact: mulr_gt0 HNR_pos HkR_pos.
      }
      have HNk_unit : (N%:R * k%:R) \is a GRing.unit := unitf_gt0 HNk_pos.
      have Hq_pos : 0 < ((n%:R + k%:R) * k%:R : R).
      {
        rewrite -natrD.
        have Hsum_pos : 0 < (n + k)%:R :> R.
        {
          rewrite ltr0n.
          rewrite addn_gt0.
          apply/orP.
          right.
          exact: Hk_pos.
        }
        exact: mulr_gt0 Hsum_pos HkR_pos.
      }
      have Hq_unit :
          ((n%:R + k%:R) * k%:R : R) \is a GRing.unit := unitf_gt0 Hq_pos.
      rewrite (divrK Hq_unit (n%:R)).
      reflexivity.
    }
    rewrite Hdiff.
    have Hsplit :
        (((k.+1)%:R / k%:R) * (n%:R / (N%:R * k%:R)) : R) =
        (n%:R * (k.+1)%:R / (N%:R * (k%:R)^+2) : R).
    {
      set den := (N%:R * (k%:R)^+2 : R).
      have Hk2_pos : 0 < ((k%:R)^+2 : R).
      {
        have HkR_pos' : 0 < k%:R :> R := HkR_pos.
        rewrite expr2.
        exact: mulr_gt0 HkR_pos HkR_pos'.
      }
      have Hden_pos : 0 < den.
      {
        rewrite /den.
        exact: mulr_gt0 HNR_pos Hk2_pos.
      }
      have HNk_pos : 0 < (N%:R * k%:R : R).
      {
        exact: mulr_gt0 HNR_pos HkR_pos.
      }
      have HNk_unit : (N%:R * k%:R) \is a GRing.unit := unitf_gt0 HNk_pos.
      have Hden_neq : den != 0 :> R := lt0r_neq0 Hden_pos.
      have Hclear :
          (((k.+1)%:R / k%:R) * (n%:R / (N%:R * k%:R))) * den =
          (n%:R * (k.+1)%:R / den) * den.
      {
        rewrite /den expr2.
        rewrite [N%:R * (k%:R * k%:R)]mulrA.
        have Hlhs_mid :
            ((n%:R / (N%:R * k%:R)) * ((N%:R * k%:R) * k%:R) : R) =
            n%:R * k%:R.
        {
          rewrite mulrA.
          rewrite (divrK HNk_unit (n%:R)).
          reflexivity.
        }
        rewrite -mulrA.
        rewrite Hlhs_mid.
        set lhs := (((k.+1)%:R / k%:R) * (n%:R * k%:R) : R).
        have Hlhs_fin :
            lhs = n%:R * (k.+1)%:R.
        {
          rewrite /lhs.
          rewrite mulrCA.
          rewrite (divrK Hk_unit ((k.+1)%:R)).
          rewrite mulrC.
          reflexivity.
        }
        rewrite Hlhs_fin.
        have Hden3_pos : 0 < (N%:R * k%:R * k%:R : R).
        {
          exact: mulr_gt0 HNk_pos HkR_pos.
        }
        have Hden3_unit :
            (N%:R * k%:R * k%:R) \is a GRing.unit := unitf_gt0 Hden3_pos.
        have Hrhs_fin :
            (n%:R * (k.+1)%:R / (N%:R * k%:R * k%:R) *
              (N%:R * k%:R * k%:R) : R) =
            n%:R * (k.+1)%:R.
        {
          rewrite (divrK Hden3_unit (n%:R * (k.+1)%:R)).
          reflexivity.
        }
        rewrite Hrhs_fin.
        reflexivity.
      }
      apply: (mulIf Hden_neq).
      exact Hclear.
    }
    rewrite Hsplit.
    exact: lexx.
  }
  exact: le_trans Hstep_sum Htail.
Qed.

(* Local: Chernoff coefficient simplification inside                      *)
(* serfling_uniform_tuple_bool_tail.                                       *)
(* serfling_chernoff_coeffE *)
(* infra: no tex label — fundamental & reusable (mathcomp-style) *)
(* consumer: serfling_chernoff_coeffE is used downstream by the BB84 secrecy proof. *)
(* path: utils:serfling_chernoff_coeffE -> *)
(*   utils:serfling_uniform_tuple_bool_tail -> *)
(*   utils:serfling_uniform_perm_pair_deviation_tail -> bb84:bb84_bbkey -> *)
(*   bb84:stat -> bb84:bb84_secret *)
Local Lemma serfling_chernoff_coeffE (mu : R) :
  (0 < k)%N ->
  (((4%:R * (k%:R)^+2 * mu / (k.+1)%:R)^+2 / 8%:R) *
      (n%:R * (k.+1)%:R / (N%:R * (k%:R)^+2)) -
    (4%:R * (k%:R)^+2 * mu / (k.+1)%:R) * (n%:R * mu / N%:R)) =
    - 2%:R * (((k * n)%:R / N%:R) * (k%:R / k.+1%:R) * mu ^+ 2).
Proof.
  move=> Hk_pos.
  have HNR_pos : 0 < N%:R :> R.
  {
    rewrite ltr0n /N.
    exact: leq_trans Hk_pos (leq_addr n k).
  }
  have HkR_pos : 0 < k%:R :> R by rewrite ltr0n.
  have Hk1_pos : 0 < (k.+1)%:R :> R by rewrite ltr0n.
  have Hk2_pos : 0 < ((k%:R)^+2 : R).
  {
    rewrite expr2.
    have HkR_pos' : 0 < k%:R :> R := HkR_pos.
    exact: mulr_gt0 HkR_pos HkR_pos'.
  }
  have HNk1_pos : 0 < (N%:R * (k.+1)%:R : R).
  {
    exact: mulr_gt0 HNR_pos Hk1_pos.
  }
  have H8_pos : 0 < 8%:R :> R by rewrite ltr0n.
  have Hk1_unit : (k.+1)%:R \is a GRing.unit := unitf_gt0 Hk1_pos.
  have Hk2_unit : (k%:R)^+2 \is a GRing.unit := unitf_gt0 Hk2_pos.
  have HN_unit : N%:R \is a GRing.unit := unitf_gt0 HNR_pos.
  have HNk1_unit : (N%:R * (k.+1)%:R) \is a GRing.unit := unitf_gt0 HNk1_pos.
  have H8_unit : 8%:R \is a GRing.unit := unitf_gt0 H8_pos.
  apply: (mulIf (lt0r_neq0 HNk1_pos)).
  rewrite mulrBl.
  have Hlhs1 :
      ((((4%:R * (k%:R)^+2 * mu / (k.+1)%:R)^+2 / 8%:R) *
         (n%:R * (k.+1)%:R / (N%:R * (k%:R)^+2))) *
        (N%:R * (k.+1)%:R) : R) =
      2%:R * (n%:R * (k%:R)^+2 * mu ^+ 2).
  {
    set u : R := 4%:R * (k%:R)^+2 * mu / (k.+1)%:R.
    set v : R := n%:R * (k.+1)%:R / (N%:R * (k%:R)^+2).
    have HdivN :
        (v * N%:R : R) =
        n%:R * (k.+1)%:R / (k%:R)^+2.
    {
      rewrite /v.
      have HNk2_pos : 0 < (N%:R * (k%:R)^+2 : R).
      {
        exact: mulr_gt0 HNR_pos Hk2_pos.
      }
      have HNk2_unit :
          (N%:R * (k%:R)^+2) \is a GRing.unit := unitf_gt0 HNk2_pos.
      apply: (mulIf (lt0r_neq0 Hk2_pos)).
      have -> :
          (((n%:R * (k.+1)%:R / (N%:R * (k%:R)^+2)) * N%:R) *
            (k%:R)^+2 : R) =
          (n%:R * (k.+1)%:R / (N%:R * (k%:R)^+2)) *
            (N%:R * (k%:R)^+2).
      {
        rewrite mulrA.
        reflexivity.
      }
      rewrite (divrK HNk2_unit (n%:R * (k.+1)%:R)).
      rewrite (divrK Hk2_unit (n%:R * (k.+1)%:R)).
      reflexivity.
    }
    have HdivN_big :
        ((((u ^+ 2 / 8%:R) * v) * (N%:R * (k.+1)%:R)) : R) =
        ((((u ^+ 2 / 8%:R) *
          (n%:R * (k.+1)%:R / (k%:R)^+2)) * (k.+1)%:R) : R).
    {
      transitivity
        ((u ^+ 2 / 8%:R) * (v * (N%:R * (k.+1)%:R)) : R).
      - rewrite -mulrA.
        reflexivity.
      rewrite [v * (N%:R * (k.+1)%:R)]mulrA.
      rewrite HdivN.
      rewrite mulrA.
      reflexivity.
    }
    rewrite HdivN_big expr2.
    have Hdivk1 :
        ((u * u) * (k.+1)%:R : R) =
        (16%:R * (k%:R)^+4 * mu ^+ 2) / (k.+1)%:R.
    {
      set A : R := 4%:R * (k%:R)^+2 * mu.
      have Hu : (u : R) = A / (k.+1)%:R.
      {
        rewrite /u /A.
        reflexivity.
      }
      rewrite Hu expr2.
      have -> :
          (((A / (k.+1)%:R) * (A / (k.+1)%:R)) * (k.+1)%:R : R) =
          (A / (k.+1)%:R) * ((A / (k.+1)%:R) * (k.+1)%:R).
      {
        rewrite -mulrA.
        reflexivity.
      }
      have Hcancel :
          ((A / (k.+1)%:R) * (k.+1)%:R : R) = A.
      {
        rewrite (divrK Hk1_unit A).
        reflexivity.
      }
      rewrite Hcancel.
      have Hprod_div :
          (((A / (k.+1)%:R) * A) : R) = ((A * A) / (k.+1)%:R).
      {
        apply: (mulIf (lt0r_neq0 Hk1_pos)).
        have Hlhs :
            ((((A / (k.+1)%:R) * A) * (k.+1)%:R) : R) = A * A.
        {
          rewrite -mulrA.
          rewrite [A * (k.+1)%:R]mulrC.
          rewrite mulrA.
          rewrite (divrK Hk1_unit A).
          reflexivity.
        }
        have Hrhs :
            ((((A * A) / (k.+1)%:R) * (k.+1)%:R) : R) = A * A.
        {
          rewrite (divrK Hk1_unit (A * A)).
          reflexivity.
        }
        rewrite Hlhs Hrhs.
        reflexivity.
      }
      rewrite Hprod_div.
      set a : R := (k%:R)^+2.
      have Hnum :
          ((A * A) : R) =
          16%:R * (a * a) * mu ^+ 2.
      {
        have H16 : (16%:R : R) = 4%:R * 4%:R.
        {
          rewrite -natrM.
          reflexivity.
        }
        rewrite H16.
        rewrite /A /a.
        have -> :
            ((4%:R * a * mu) * (4%:R * a * mu) : R) =
            (4%:R * (a * (mu * (4%:R * a * mu))) : R).
        {
          rewrite -!mulrA.
          reflexivity.
        }
        have Hmid :
            (a * (mu * (4%:R * a * mu)) : R) =
            (4%:R * (a * a) * mu ^+ 2 : R).
        {
          rewrite [mu * (4%:R * a * mu)]mulrC.
          rewrite expr2.
          rewrite !mulrA.
          rewrite [a * 4%:R]mulrC.
          rewrite !mulrA.
          reflexivity.
        }
        rewrite Hmid.
        have -> :
            (4%:R * (4%:R * (a * a) * mu ^+ 2) : R) =
            ((4%:R * 4%:R) * (a * a) * mu ^+ 2 : R).
        {
          rewrite !mulrA.
          reflexivity.
        }
        reflexivity.
      }
      rewrite Hnum.
      rewrite /a.
      have Hk4_local :
          ((((k%:R)^+2) * ((k%:R)^+2) : R) = (k%:R)^+4).
      {
        rewrite -expr2.
        have -> : 4%N = (2 * 2)%N by [].
        rewrite exprM.
        reflexivity.
      }
      rewrite Hk4_local.
      reflexivity.
    }
    have Hreassoc :
        ((((u * u / 8%:R) * (n%:R * (k.+1)%:R / (k%:R)^+2)) * (k.+1)%:R) : R) =
        (((((u * u) * (k.+1)%:R) / 8%:R) *
          (n%:R * (k.+1)%:R / (k%:R)^+2)) : R).
    {
      set C : R := n%:R * (k.+1)%:R / (k%:R)^+2.
      have H1 :
          ((((u * u / 8%:R) * C) * (k.+1)%:R) : R) =
          (((u * u / 8%:R) * (C * (k.+1)%:R)) : R).
      {
        rewrite mulrA.
        reflexivity.
      }
      have H2 :
          (((u * u / 8%:R) * (C * (k.+1)%:R)) : R) =
          (((u * u / 8%:R) * ((k.+1)%:R * C)) : R).
      {
        rewrite [C * (k.+1)%:R]mulrC.
        reflexivity.
      }
      have H3 :
          (((u * u / 8%:R) * ((k.+1)%:R * C)) : R) =
          ((((u * u / 8%:R) * (k.+1)%:R) * C) : R).
      {
        rewrite -!mulrA.
        reflexivity.
      }
      have H4 :
          ((((u * u / 8%:R) * (k.+1)%:R) * C) : R) =
          (((((u * u) * (k.+1)%:R) / 8%:R) * C) : R).
      {
        have H4a :
            (((u * u / 8%:R) * (k.+1)%:R) : R) =
            ((((u * u) * (k.+1)%:R) / 8%:R) : R).
        {
          rewrite -!mulrA.
          rewrite [8%:R^-1 * (k.+1)%:R]mulrC.
          rewrite !mulrA.
          reflexivity.
        }
        rewrite H4a.
        reflexivity.
      }
      rewrite /C H1 H2 H3 H4.
      reflexivity.
    }
    rewrite Hreassoc.
    rewrite Hdivk1.
    set A1 : R := 16%:R * (k%:R)^+4 * mu ^+ 2.
    set B1 : R := n%:R * (k.+1)%:R.
    have Hk4 :
        ((((k%:R)^+2) * ((k%:R)^+2) : R) = (k%:R)^+4).
    {
      rewrite -expr2.
      have -> : 4%N = (2 * 2)%N by [].
      rewrite exprM.
      reflexivity.
    }
    have Htail :
        ((((A1 / (k.+1)%:R) / 8%:R) * (B1 / (k%:R)^+2)) : R) =
        2%:R * (n%:R * (k%:R)^+2 * mu ^+ 2).
    {
      have H8k2_pos : 0 < (8%:R * (k%:R)^+2 : R).
      {
        exact: mulr_gt0 H8_pos Hk2_pos.
      }
      apply: (mulIf (lt0r_neq0 H8k2_pos)).
      have Hlhs_scaled :
          (((((A1 / (k.+1)%:R) / 8%:R) * (B1 / (k%:R)^+2)) *
            (8%:R * (k%:R)^+2)) : R) =
          A1 * n%:R.
      {
        have -> :
            (((((A1 / (k.+1)%:R) / 8%:R) * (B1 / (k%:R)^+2)) *
              (8%:R * (k%:R)^+2)) : R) =
            ((((A1 / (k.+1)%:R / 8%:R) * 8%:R) *
              ((B1 / (k%:R)^+2) * (k%:R)^+2)) : R).
        {
          rewrite mulrACA.
          reflexivity.
        }
        have HX :
            (((A1 / (k.+1)%:R / 8%:R) * 8%:R) : R) =
            (A1 / (k.+1)%:R : R).
        {
          rewrite (divrK H8_unit (A1 / (k.+1)%:R)).
          reflexivity.
        }
        rewrite HX.
        have HY :
            ((((B1 / (k%:R)^+2) * (k%:R)^+2) : R)) = B1.
        {
          rewrite (divrK Hk2_unit B1).
          reflexivity.
        }
        rewrite HY.
        have Hfinalk1 :
            (((A1 / (k.+1)%:R) * B1) : R) = A1 * n%:R.
        {
          rewrite /B1.
          rewrite [n%:R * (k.+1)%:R]mulrC.
          rewrite mulrA.
          rewrite (divrK Hk1_unit A1).
          reflexivity.
        }
        exact: Hfinalk1.
      }
      have Hrhs_scaled :
          (((2%:R * (n%:R * (k%:R)^+2 * mu ^+ 2)) *
            (8%:R * (k%:R)^+2)) : R) =
          A1 * n%:R.
      {
        rewrite /A1.
        have H16 : (16%:R : R) = 2%:R * 8%:R.
        {
          rewrite -natrM.
          reflexivity.
        }
        set K := ((((k%:R)^+2) * ((k%:R)^+2)) * mu ^+ 2 : R).
        have Hlhs_norm :
            (((2%:R * (n%:R * (k%:R)^+2 * mu ^+ 2)) *
              (8%:R * (k%:R)^+2)) : R) =
            (2%:R * 8%:R * n%:R * K : R).
        {
          have -> :
              ((((2%:R * (n%:R * (k%:R)^+2 * mu ^+ 2)) *
                 (8%:R * (k%:R)^+2)) : R)) =
              (((2%:R * 8%:R) *
                ((n%:R * (k%:R)^+2 * mu ^+ 2) * (k%:R)^+2)) : R).
          {
            rewrite mulrACA.
            reflexivity.
          }
          have -> :
              ((((n%:R * (k%:R)^+2 * mu ^+ 2) * (k%:R)^+2) : R)) =
              (n%:R * K : R).
          {
            rewrite /K.
            rewrite -mulrA.
            rewrite [mu ^+ 2 * (k%:R)^+2]mulrC.
            rewrite !mulrA.
            reflexivity.
          }
          rewrite -!mulrA.
          reflexivity.
        }
        have Hswap :
            ((((2%:R * 8%:R) * K) * n%:R) : R) =
            (2%:R * 8%:R * n%:R * K : R).
        {
          have -> :
              ((((2%:R * 8%:R) * K) * n%:R) : R) =
              (((2%:R * 8%:R) * (K * n%:R)) : R).
          {
            rewrite -mulrA.
            reflexivity.
          }
          rewrite [K * n%:R]mulrC.
          rewrite -!mulrA.
          reflexivity.
        }
        rewrite Hlhs_norm.
        symmetry.
        rewrite H16 -Hk4.
        have -> :
            (((((2%:R * 8%:R) * ((k%:R)^+2 * (k%:R)^+2)) * mu ^+ 2)) : R) =
            (((2%:R * 8%:R) * K) : R).
        {
          rewrite /K -mulrA.
          reflexivity.
        }
        exact: Hswap.
      }
      rewrite Hlhs_scaled Hrhs_scaled.
      reflexivity.
    }
    exact: Htail.
  }
  have Hlhs2 :
      (((4%:R * (k%:R)^+2 * mu / (k.+1)%:R) *
         (n%:R * mu / N%:R)) *
        (N%:R * (k.+1)%:R) : R) =
      4%:R * (n%:R * (k%:R)^+2 * mu ^+ 2).
  {
    set A : R := 4%:R * (k%:R)^+2 * mu.
    set B : R := n%:R * mu.
    have -> :
        (((A / (k.+1)%:R) * (B / N%:R)) * (N%:R * (k.+1)%:R) : R) =
        ((((A * B) / ((k.+1)%:R * N%:R)) * (N%:R * (k.+1)%:R)) : R).
    {
      rewrite mulf_div.
      reflexivity.
    }
    rewrite [((k.+1)%:R * N%:R)]mulrC.
    rewrite (divrK HNk1_unit (A * B)).
    rewrite /A /B !expr2.
    set a := (k%:R * k%:R : R).
    have -> :
        ((4%:R * a * mu) * (n%:R * mu) : R) =
        (4%:R * (a * (mu * (n%:R * mu))) : R).
    {
      rewrite -!mulrA.
      reflexivity.
    }
    have Hinner :
        (a * (mu * (n%:R * mu)) : R) =
        (n%:R * a * mu ^+ 2 : R).
    {
      rewrite [mu * (n%:R * mu)]mulrC.
      rewrite expr2.
      rewrite !mulrA.
      rewrite [a * n%:R]mulrC.
      rewrite !mulrA.
      reflexivity.
    }
    rewrite Hinner.
    reflexivity.
  }
  rewrite Hlhs1 Hlhs2.
  have Hrhs :
      ((- 2%:R * (((k * n)%:R / N%:R) * (k%:R / k.+1%:R) * mu ^+ 2)) *
        (N%:R * (k.+1)%:R) : R) =
      - 2%:R * (n%:R * (k%:R)^+2 * mu ^+ 2).
  {
    have Hkn : (k * n)%:R = k%:R * n%:R :> R.
    {
      rewrite natrM.
      reflexivity.
    }
    rewrite Hkn.
    rewrite -mulrA.
    set c := (k%:R * n%:R / N%:R * (k%:R / (k.+1)%:R) : R).
    have Hcoef :
        ((c * (N%:R * (k.+1)%:R)) : R) =
        n%:R * (k%:R)^+2.
    {
      rewrite /c.
      have -> :
          ((((k%:R * n%:R / N%:R) * (k%:R / (k.+1)%:R)) *
            (N%:R * (k.+1)%:R) : R)) =
          (((((k%:R * n%:R) * k%:R) / (N%:R * (k.+1)%:R)) *
            (N%:R * (k.+1)%:R)) : R).
      {
        rewrite mulf_div.
        reflexivity.
      }
      rewrite (divrK HNk1_unit ((k%:R * n%:R) * k%:R)).
      rewrite [k%:R * n%:R]mulrC.
      rewrite expr2.
      rewrite mulrA.
      reflexivity.
    }
    have Hcoefmu :
        ((c * mu ^+ 2 * (N%:R * (k.+1)%:R)) : R) =
        (n%:R * (k%:R)^+2 * mu ^+ 2 : R).
    {
      have -> :
          ((c * mu ^+ 2 * (N%:R * (k.+1)%:R)) : R) =
          ((c * ((N%:R * (k.+1)%:R) * mu ^+ 2)) : R).
      {
        rewrite -mulrA.
        rewrite [mu ^+ 2 * (N%:R * (k.+1)%:R)]mulrC.
        reflexivity.
      }
      have -> :
          ((c * ((N%:R * (k.+1)%:R) * mu ^+ 2)) : R) =
          ((c * (N%:R * (k.+1)%:R) * mu ^+ 2) : R).
      {
        rewrite mulrA.
        reflexivity.
      }
      rewrite Hcoef.
      reflexivity.
    }
    rewrite [X in (- 2%:R * X = _)]Hcoefmu.
    reflexivity.
  }
  rewrite Hrhs.
  set x := (n%:R * (k%:R)^+2 * mu ^+ 2 : R).
  rewrite -mulrBl.
  have H24 : (4%:R : R) = 2%:R + 2%:R.
  {
    rewrite -natrD.
    reflexivity.
  }
  have Hconst : (2%:R - (2%:R + 2%:R) = - 2%:R :> R).
  {
    rewrite opprD.
    rewrite addrA.
    rewrite addrN.
    rewrite add0r.
    reflexivity.
  }
  rewrite H24 Hconst.
  reflexivity.
Qed.

(* serfling_uniform_tuple_bool_tail *)
(* infra: no tex label — fundamental & reusable (mathcomp-style) *)
(* consumer: serfling_uniform_tuple_bool_tail is used downstream by the BB84 secrecy proof. *)
(* path: utils:serfling_uniform_tuple_bool_tail -> *)
(*   utils:serfling_uniform_perm_pair_deviation_tail -> bb84:bb84_bbkey -> *)
(*   bb84:stat -> bb84:bb84_secret *)
Local Lemma serfling_uniform_tuple_bool_tail (d : bitstr N) (mu : R) :
  (0 < n)%N ->
  (0 < k)%N ->
  0 <= mu ->
  Pr_event (@tuple_uniform_mu n k) (@tuple_bool_deviation_event n k d mu) <=
    expR (- 2%:R * (((k * n)%:R / N%:R) * (k%:R / k.+1%:R) * mu ^+ 2)).
Proof.
  move=> Hn_pos Hk_pos Hmu_nonneg.
  pose alpha : R := n%:R * mu / N%:R.
  pose lambda0 : R := 4%:R * (k%:R)^+2 * mu / (k.+1)%:R.
  pose coeff : R := n%:R * (k.+1)%:R / (N%:R * (k%:R)^+2).
  pose target : R := ((k * n)%:R / N%:R) * (k%:R / k.+1%:R) * mu ^+ 2.
  have HNR_pos : 0 < N%:R :> R.
  {
    rewrite ltr0n /N.
    exact: leq_trans Hk_pos (leq_addr n k).
  }
  have HkR_pos : 0 < k%:R :> R by rewrite ltr0n.
  have Hk1_pos : 0 < (k.+1)%:R :> R by rewrite ltr0n.
  have HnR_pos : 0 < n%:R :> R by rewrite ltr0n.
  have Halpha_nonneg : 0 <= alpha.
  {
    rewrite /alpha.
    apply: mulr_ge0.
    - apply: mulr_ge0; first by rewrite ler0n.
      exact: Hmu_nonneg.
    - by rewrite invr_ge0.
  }
  have Hlambda_nonneg : 0 <= lambda0.
  {
    rewrite /lambda0.
    - apply: mulr_ge0.
      + apply: mulr_ge0.
        * apply: mulr_ge0.
          -- by rewrite ler0n.
          -- rewrite expr2.
             exact: mulr_ge0 (ltW HkR_pos) (ltW HkR_pos).
        * exact: Hmu_nonneg.
    - by rewrite invr_ge0.
  }
  have Hmarkov :
      Pr_event (@tuple_uniform_mu n k) (@tuple_bool_deviation_event n k d mu) <=
      (\sum_(t : n.-tuple 'I_N)
         tuple_uniform_mu t *
         expR (lambda0 * tuple_bool_centered_over_k d t)) /
        expR (lambda0 * alpha).
  {
    apply: (@markov_event_bound (n.-tuple 'I_N)
      (@tuple_uniform_mu n k)
      (fun t => expR (lambda0 * tuple_bool_centered_over_k d t))
      (@tuple_bool_deviation_event n k d mu)
      (expR (lambda0 * alpha))).
    - exact: expR_gt0.
    - exact: tuple_uniform_mu_nonneg.
    - move=> t.
      exact: ltW (expR_gt0 _).
    - move=> t.
      rewrite /tuple_bool_deviation_event inE.
      move=> /andP [_ Hbad].
      rewrite ler_expR.
      exact: (ler_wpM2l Hlambda_nonneg Hbad).
  }
  have Hmgf :
      \sum_(t : n.-tuple 'I_N)
        tuple_uniform_mu t * expR (lambda0 * tuple_bool_centered_over_k d t) <=
      expR (\sum_(i < n)
        lambda0 ^+ 2 / (8%:R * (((N - i).-1)%N%:R)^+2)).
  {
    have Hmgf0 :=
      tuple_serfling_mgf_bound (m := n) (lambda := lambda0) d
        (leqnn n) Hk_pos Hlambda_nonneg.
    rewrite /tuple_uniform_mu_m /tuple_uniform_mu in Hmgf0.
    rewrite (eq_bigr
      (fun t : n.-tuple 'I_N =>
        tuple_uniform_mu t * expR (lambda0 * tuple_bool_centered_over_k d t))) in Hmgf0.
    2:{
      move=> t _.
      rewrite tuple_serfling_terminalE.
      reflexivity.
    }
    exact Hmgf0.
  }
  have Hsum_eq :
      \sum_(i < n) lambda0 ^+ 2 / (8%:R * (((N - i).-1)%N%:R)^+2) =
      (lambda0 ^+ 2 / 8%:R) *
        \sum_(i < n) ((((N - i).-1)%N%:R : R)^-2).
  {
    have Hrhs_sum :
        ((lambda0 ^+ 2 / 8%:R) *
          \sum_(i < n) ((((N - i).-1)%N%:R : R)^-2)) =
        (\sum_(i < n)
          ((lambda0 ^+ 2 / 8%:R) * ((((N - i).-1)%N%:R : R)^-2))).
    {
      rewrite -mulr_sumr.
      reflexivity.
    }
    rewrite Hrhs_sum.
    apply: eq_bigr => i _.
    pose a : R := (((N - i).-1)%N)%:R.
    have Ha_pos : 0 < a.
    {
      rewrite /a ltr0n.
      have Hi_lt_n : (i < n)%N := ltn_ord i.
      have Hn_lt_N : (n < N)%N.
      {
        rewrite /N -(add0n n) ltn_add2r.
        exact: Hk_pos.
      }
      have Hi_lt_N : (i < N)%N.
      {
        exact: ltn_trans Hi_lt_n Hn_lt_N.
      }
      have Hi1_lt_N : (i.+1 < N)%N.
      {
        exact: leq_ltn_trans Hi_lt_n Hn_lt_N.
      }
      have Hsub : (N - i)%N = (N - i.+1).+1.
      {
        symmetry.
        exact: subnSK Hi_lt_N.
      }
      rewrite Hsub /=.
      by rewrite subn_gt0.
    }
    have Ha2_pos : 0 < a ^+ 2.
    {
      rewrite /a expr2.
      have Ha_pos' : 0 < a := Ha_pos.
      exact: mulr_gt0 Ha_pos Ha_pos'.
    }
    have H8_pos : 0 < 8%:R :> R by rewrite ltr0n.
    have H8_unit : 8%:R \is a GRing.unit := unitf_gt0 H8_pos.
    have Ha2_unit : a ^+ 2 \is a GRing.unit := unitf_gt0 Ha2_pos.
    have Hden_pos : 0 < (8%:R * a ^+ 2 : R).
    {
      exact: mulr_gt0 H8_pos Ha2_pos.
    }
    apply: (mulIf (lt0r_neq0 Hden_pos)).
    have Hlhs_fin :
        (((lambda0 ^+ 2) / (8%:R * a ^+ 2)) * (8%:R * a ^+ 2) : R) =
        lambda0 ^+ 2.
    {
      exact: (divrK (unitf_gt0 Hden_pos) (lambda0 ^+ 2)).
    }
    rewrite Hlhs_fin.
    have Hrhs_fin :
        (((lambda0 ^+ 2 / 8%:R) * a^-2) * (8%:R * a ^+ 2) : R) =
        lambda0 ^+ 2.
    {
      pose c : R := lambda0 ^+ 2 / 8%:R.
      rewrite /c.
      rewrite [8%:R * a ^+ 2]mulrC.
      rewrite mulrA.
      have Hdiva : (((c * a^-2) * a ^+ 2) : R) = c.
      {
        have Ha_unit : a \is a GRing.unit := unitf_gt0 Ha_pos.
        rewrite expr2.
        rewrite mulrA.
        have Hstep : ((a^-2 * a : R)) = a^-1.
        {
          rewrite -exprVn expr2 -mulrA.
          rewrite [a^-1 * a]mulVr //.
          rewrite mulr1.
          reflexivity.
        }
        have Hstep2 : ((((c * a^-2) * a) : R)) = c * a^-1.
        {
          rewrite -mulrA.
          rewrite Hstep.
          reflexivity.
        }
        rewrite Hstep2.
        rewrite -mulrA.
        rewrite [a^-1 * a]mulVr //.
        rewrite mulr1.
        reflexivity.
      }
      rewrite Hdiva.
      rewrite /c.
      rewrite [((lambda0 ^+ 2 / 8%:R) * 8%:R)](divrK H8_unit (lambda0 ^+ 2)).
      reflexivity.
    }
    rewrite Hrhs_fin.
    reflexivity.
  }
  have Hquad_nonneg : 0 <= lambda0 ^+ 2 / 8%:R.
  {
    apply: divr_ge0.
    - rewrite expr2.
      apply: mulr_ge0.
      + exact: Hlambda_nonneg.
      + exact: Hlambda_nonneg.
    - exact: ler0n.
  }
  have Hcoeff_bound :
      ((lambda0 ^+ 2 / 8%:R) *
        \sum_(i < n) ((((N - i).-1)%N%:R : R)^-2)) <=
      (lambda0 ^+ 2 / 8%:R) * coeff.
  {
    exact: (ler_wpM2l Hquad_nonneg (serfling_square_sum_bound Hk_pos)).
  }
  have Hmgf_coeff :
      \sum_(t : n.-tuple 'I_N)
        tuple_uniform_mu t * expR (lambda0 * tuple_bool_centered_over_k d t) <=
      expR ((lambda0 ^+ 2 / 8%:R) * coeff).
  {
    apply: (le_trans Hmgf).
    rewrite Hsum_eq.
    rewrite ler_expR.
    exact: Hcoeff_bound.
  }
  have Hquot_bound :
      (\sum_(t : n.-tuple 'I_N)
         tuple_uniform_mu t * expR (lambda0 * tuple_bool_centered_over_k d t)) /
        expR (lambda0 * alpha) <=
      expR ((lambda0 ^+ 2 / 8%:R) * coeff) / expR (lambda0 * alpha).
  {
    rewrite ler_pdivrMr ?expR_gt0 //.
    rewrite divrK ?unitf_gt0 ?expR_gt0 //.
  }
  have Hcoeff_exact :
      (lambda0 ^+ 2 / 8%:R) * coeff - lambda0 * alpha =
      - 2%:R * target.
  {
    rewrite /alpha /lambda0 /coeff /target.
    exact: serfling_chernoff_coeffE.
  }
  apply: (le_trans Hmarkov).
  apply: (le_trans Hquot_bound).
  rewrite -expRB Hcoeff_exact.
  exact: lexx.
Qed.

(* The fiber of `perm_bool_holdout_tuple` is easiest to analyze by acting on the
   domain positions: a permutation of the first `k` slots leaves the last `n`
   holdout slots unchanged pointwise, hence preserves the extracted tuple. *)
(* base_holdout_tuple *)
(* infra: no tex label — fundamental & reusable (mathcomp-style) *)
(* consumer: base_holdout_tuple is used downstream by the BB84 secrecy proof. *)
Local Definition base_holdout_tuple : n.-tuple 'I_N :=
  [tuple @rshift k n i | i < n].

(* perm_bool_holdout_tuple_baseE *)
(* infra: no tex label — fundamental & reusable (mathcomp-style) *)
(* consumer: perm_bool_holdout_tuple_baseE is used downstream by the BB84 secrecy proof. *)
(* path: utils:perm_bool_holdout_tuple_baseE -> *)
(*   utils:card_base_holdout_tuple_fiber -> *)
(*   utils:card_perm_bool_holdout_tuple_fiber -> *)
(*   utils:uniform_perm_key_tuple_pushforward -> *)
(*   utils:serfling_uniform_perm_pair_deviation_tail -> bb84:bb84_bbkey -> *)
(*   bb84:stat -> bb84:bb84_secret *)
Local Lemma perm_bool_holdout_tuple_baseE :
  perm_bool_holdout_tuple (1%g : 'S_N) = base_holdout_tuple.
Proof.
  apply: eq_from_tnth => i.
  rewrite /perm_bool_holdout_tuple /base_holdout_tuple !tnth_mktuple.
  by rewrite perm1.
Qed.

(* left_block_perm_fun *)
(* infra: no tex label — fundamental & reusable (mathcomp-style) *)
(* consumer: left_block_perm_fun is used downstream by the BB84 secrecy proof. *)
Local Definition left_block_perm_fun (s : 'S_k) (i : 'I_N) : 'I_N :=
  unsplit match split i with
          | inl j => inl _ (s j)
          | inr l => inr _ l
          end.

(* left_block_perm_fun_inj *)
(* infra: no tex label — fundamental & reusable (mathcomp-style) *)
(* consumer: left_block_perm_fun_inj is used downstream by the BB84 secrecy proof. *)
(* path: utils:left_block_perm_fun_inj -> *)
(*   utils:serfling_uniform_perm_pair_deviation_tail -> bb84:bb84_bbkey -> *)
(*   bb84:stat -> bb84:bb84_secret *)
Local Lemma left_block_perm_fun_inj (s : 'S_k) :
  injective (left_block_perm_fun s).
Proof.
  move=> i j.
  case: (split_ordP i)=> [a ->|a ->];
    case: (split_ordP j)=> [b ->|b ->].
  - rewrite /left_block_perm_fun !splitEl.
    have -> : unsplit (inl 'I_n (s a)) = lshift n (s a).
    {
      apply: (can_inj splitK).
      rewrite splitEl.
      reflexivity.
    }
    have -> : unsplit (inl 'I_n (s b)) = lshift n (s b).
    {
      apply: (can_inj splitK).
      rewrite splitEl.
      reflexivity.
    }
    move=> /lshift_inj Hs.
    have Hab : s a = s b := Hs.
    have -> : a = b.
    {
      apply: perm_inj.
      apply: Hab.
    }
    reflexivity.
  - rewrite /left_block_perm_fun splitEl splitEr.
    have -> : unsplit (inl 'I_n (s a)) = lshift n (s a).
    {
      apply: (can_inj splitK).
      rewrite splitEl.
      reflexivity.
    }
    have -> : unsplit (inr 'I_k b) = rshift k b.
    {
      apply: (can_inj splitK).
      rewrite splitEr.
      reflexivity.
    }
    move=> /eqP.
    rewrite eq_lrshift.
    done.
  - rewrite /left_block_perm_fun splitEr splitEl.
    have -> : unsplit (inr 'I_k a) = rshift k a.
    {
      apply: (can_inj splitK).
      rewrite splitEr.
      reflexivity.
    }
    have -> : unsplit (inl 'I_n (s b)) = lshift n (s b).
    {
      apply: (can_inj splitK).
      rewrite splitEl.
      reflexivity.
    }
    move=> /eqP.
    rewrite eq_rlshift.
    done.
  - rewrite /left_block_perm_fun !splitEr.
    have -> : unsplit (inr 'I_k a) = rshift k a.
    {
      apply: (can_inj splitK).
      rewrite splitEr.
      reflexivity.
    }
    have -> : unsplit (inr 'I_k b) = rshift k b.
    {
      apply: (can_inj splitK).
      rewrite splitEr.
      reflexivity.
    }
    move=> /rshift_inj ->.
    reflexivity.
Qed.

(* left_block_perm *)
(* infra: no tex label — fundamental & reusable (mathcomp-style) *)
(* consumer: left_block_perm is used downstream by the BB84 secrecy proof. *)
Local Definition left_block_perm (s : 'S_k) : 'S_N :=
  perm (@left_block_perm_fun_inj s).

(* left_block_perm_lshift *)
(* infra: no tex label — fundamental & reusable (mathcomp-style) *)
(* consumer: left_block_perm_lshift is used downstream by the BB84 secrecy proof. *)
(* path: utils:left_block_perm_lshift -> utils:base_holdout_tuple_fiberP -> *)
(*   utils:card_base_holdout_tuple_fiber -> *)
(*   utils:card_perm_bool_holdout_tuple_fiber -> *)
(*   utils:uniform_perm_key_tuple_pushforward -> *)
(*   utils:serfling_uniform_perm_pair_deviation_tail -> bb84:bb84_bbkey -> *)
(*   bb84:stat -> bb84:bb84_secret *)
Local Lemma left_block_perm_lshift (s : 'S_k) (i : 'I_k) :
  left_block_perm s (lshift n i) = lshift n (s i).
Proof.
  rewrite permE /left_block_perm_fun.
  by rewrite (unsplitK (inl 'I_n i)).
Qed.

(* left_block_perm_rshift *)
(* infra: no tex label — fundamental & reusable (mathcomp-style) *)
(* consumer: left_block_perm_rshift is used downstream by the BB84 secrecy proof. *)
(* path: utils:left_block_perm_rshift -> utils:base_holdout_tuple_fiberP -> *)
(*   utils:card_base_holdout_tuple_fiber -> *)
(*   utils:card_perm_bool_holdout_tuple_fiber -> *)
(*   utils:uniform_perm_key_tuple_pushforward -> *)
(*   utils:serfling_uniform_perm_pair_deviation_tail -> bb84:bb84_bbkey -> *)
(*   bb84:stat -> bb84:bb84_secret *)
Local Lemma left_block_perm_rshift (s : 'S_k) (i : 'I_n) :
  left_block_perm s (rshift k i) = rshift k i.
Proof.
  rewrite permE /left_block_perm_fun.
  by rewrite (unsplitK (inr 'I_k i)).
Qed.

(* perm_bool_holdout_tuple_left_block *)
(* infra: no tex label — fundamental & reusable (mathcomp-style) *)
(* consumer: perm_bool_holdout_tuple_left_block is used downstream by the BB84 secrecy proof. *)
(* path: utils:perm_bool_holdout_tuple_left_block -> *)
(*   utils:card_base_holdout_tuple_fiber -> *)
(*   utils:card_perm_bool_holdout_tuple_fiber -> *)
(*   utils:uniform_perm_key_tuple_pushforward -> *)
(*   utils:serfling_uniform_perm_pair_deviation_tail -> bb84:bb84_bbkey -> *)
(*   bb84:stat -> bb84:bb84_secret *)
Local Lemma perm_bool_holdout_tuple_left_block (s : 'S_k) (pi : 'S_N) :
  perm_bool_holdout_tuple (left_block_perm s * pi) = perm_bool_holdout_tuple pi.
Proof.
  apply: eq_from_tnth => i.
  rewrite /perm_bool_holdout_tuple !tnth_mktuple permM.
  rewrite left_block_perm_rshift.
  reflexivity.
Qed.

(* perm_bool_holdout_tuple_mul_right *)
(* infra: no tex label — fundamental & reusable (mathcomp-style) *)
(* consumer: perm_bool_holdout_tuple_mul_right is used downstream by the BB84 secrecy proof. *)
(* path: utils:perm_bool_holdout_tuple_mul_right -> *)
(*   utils:card_perm_bool_holdout_tuple_fiber -> *)
(*   utils:uniform_perm_key_tuple_pushforward -> *)
(*   utils:serfling_uniform_perm_pair_deviation_tail -> bb84:bb84_bbkey -> *)
(*   bb84:stat -> bb84:bb84_secret *)
Local Lemma perm_bool_holdout_tuple_mul_right (pi q : 'S_N) :
  perm_bool_holdout_tuple (pi * q) =
    [tuple q (tnth (perm_bool_holdout_tuple pi) i) | i < n].
Proof.
  apply: eq_from_tnth => i.
  rewrite /perm_bool_holdout_tuple !tnth_mktuple permM.
  reflexivity.
Qed.

(* left_block_perm_inj *)
(* infra: no tex label — fundamental & reusable (mathcomp-style) *)
(* consumer: left_block_perm_inj is used downstream by the BB84 secrecy proof. *)
(* path: utils:left_block_perm_inj -> utils:card_base_holdout_tuple_fiber -> *)
(*   utils:card_perm_bool_holdout_tuple_fiber -> *)
(*   utils:uniform_perm_key_tuple_pushforward -> *)
(*   utils:serfling_uniform_perm_pair_deviation_tail -> bb84:bb84_bbkey -> *)
(*   bb84:stat -> bb84:bb84_secret *)
Local Lemma left_block_perm_inj :
  injective (@left_block_perm).
Proof.
  move=> s1 s2 Hs.
  apply/permP => i.
  apply: lshift_inj.
  have Hl :
      left_block_perm s1 (@lshift k n i) =
      left_block_perm s2 (@lshift k n i).
  {
    exact: (congr1 (fun p : 'S_N => p (@lshift k n i)) Hs).
  }
  rewrite !left_block_perm_lshift in Hl.
  exact: Hl.
Qed.

(* base_holdout_tuple_fiberP *)
(* infra: no tex label — fundamental & reusable (mathcomp-style) *)
(* consumer: base_holdout_tuple_fiberP is used downstream by the BB84 secrecy proof. *)
(* path: utils:base_holdout_tuple_fiberP -> *)
(*   utils:card_base_holdout_tuple_fiber -> *)
(*   utils:card_perm_bool_holdout_tuple_fiber -> *)
(*   utils:uniform_perm_key_tuple_pushforward -> *)
(*   utils:serfling_uniform_perm_pair_deviation_tail -> bb84:bb84_bbkey -> *)
(*   bb84:stat -> bb84:bb84_secret *)
Local Lemma base_holdout_tuple_fiberP (pi : 'S_N) :
  perm_bool_holdout_tuple pi = base_holdout_tuple ->
  exists s : 'S_k, pi = left_block_perm s.
Proof.
  move=> Hpi.
  have Hpi_r (i : 'I_n) : pi (@rshift k n i) = @rshift k n i.
  {
    move: (congr1 (fun t : n.-tuple 'I_N => tnth t i) Hpi).
    by rewrite /perm_bool_holdout_tuple /base_holdout_tuple !tnth_mktuple.
  }
  pose h (i : 'I_k) : 'I_k :=
    match split (pi (@lshift k n i)) with
    | inl j => j
    | inr _ => i
    end.
  have HhE (i : 'I_k) : pi (@lshift k n i) = @lshift k n (h i).
  {
    rewrite /h.
    case E: (split (pi (@lshift k n i))) => [j|j].
    - apply: (can_inj splitK).
      by rewrite E splitEl.
    - have Hpj : pi (@rshift k n j) = @rshift k n j := Hpi_r j.
      have Hbad :
          pi (@lshift k n i) = pi (@rshift k n j).
      {
        rewrite Hpj.
        apply: (can_inj splitK).
        by rewrite E splitEr.
      }
      move/eqP: (perm_inj Hbad).
      by rewrite eq_lrshift.
  }
  have Hh_inj : injective h.
  {
    move=> i j Hij.
    have Hpi_eq : pi (@lshift k n i) = pi (@lshift k n j).
    {
      rewrite !HhE Hij.
      reflexivity.
    }
    exact: lshift_inj (perm_inj Hpi_eq).
  }
  pose s := perm Hh_inj.
  exists s.
  apply/permP => y.
  case: (split_ordP y) => [i ->|j ->].
  - rewrite left_block_perm_lshift HhE.
    by rewrite permE.
  - rewrite left_block_perm_rshift.
    exact: Hpi_r.
Qed.

(* card_base_holdout_tuple_fiber *)
(* infra: no tex label — fundamental & reusable (mathcomp-style) *)
(* consumer: card_base_holdout_tuple_fiber is used downstream by the BB84 secrecy proof. *)
(* path: utils:card_base_holdout_tuple_fiber -> *)
(*   utils:card_perm_bool_holdout_tuple_fiber -> *)
(*   utils:uniform_perm_key_tuple_pushforward -> *)
(*   utils:serfling_uniform_perm_pair_deviation_tail -> bb84:bb84_bbkey -> *)
(*   bb84:stat -> bb84:bb84_secret *)
Local Lemma card_base_holdout_tuple_fiber :
  #|[set pi in [pred pi : 'S_N | perm_bool_holdout_tuple pi == base_holdout_tuple]]| =
    #|'S_k|.
Proof.
  pose A : {set 'S_N} :=
    [set pi in [pred pi : 'S_N | perm_bool_holdout_tuple pi == base_holdout_tuple]].
  pose B : {set 'S_N} := left_block_perm @: [set: 'S_k].
  have HsubAB : A \subset B.
  {
    apply/mathcomp.boot.fintype.subsetP => pi.
    move=> Hpi.
    move: Hpi.
    rewrite /A inE.
    move/eqP=> Hpi.
    move: (base_holdout_tuple_fiberP Hpi) => [s ->].
    apply/imsetP.
    exists s.
    - by rewrite inE.
    - reflexivity.
  }
  have HsubBA : B \subset A.
  {
    apply/mathcomp.boot.fintype.subsetP => pi.
    move=> /imsetP [s _ ->].
    rewrite /A inE.
    apply/eqP.
    rewrite -perm_bool_holdout_tuple_baseE.
    have -> : left_block_perm s = (left_block_perm s * 1)%g.
    {
      by rewrite mulg1.
    }
    rewrite perm_bool_holdout_tuple_left_block.
    reflexivity.
  }
  have Hcard_eq : #|A| = #|B|.
  {
    apply/eqP.
    rewrite eqn_leq.
    apply/andP.
    split.
    - exact: subset_leq_card HsubAB.
    - exact: subset_leq_card HsubBA.
  }
  have HcardB : #|B| = #|'S_k|.
  {
    have Himg : #|B| = #|[set: 'S_k]|.
    {
      rewrite /B.
      exact: card_imset left_block_perm_inj.
    }
    have Hfull : #|[set: 'S_k]| = #|'S_k|.
    {
      rewrite eq_cardT.
      - rewrite cardT.
        reflexivity.
      - move=> s.
        exact: in_setT.
    }
    exact: (eq_trans Himg Hfull).
  }
  rewrite /A in Hcard_eq.
  apply: (eq_trans Hcard_eq).
  exact: HcardB.
Qed.

(* perm_bool_holdout_tuple_exists *)
(* infra: no tex label — fundamental & reusable (mathcomp-style) *)
(* consumer: perm_bool_holdout_tuple_exists is used downstream by the BB84 secrecy proof. *)
(* path: utils:perm_bool_holdout_tuple_exists -> *)
(*   utils:card_perm_bool_holdout_tuple_fiber -> *)
(*   utils:uniform_perm_key_tuple_pushforward -> *)
(*   utils:serfling_uniform_perm_pair_deviation_tail -> bb84:bb84_bbkey -> *)
(*   bb84:stat -> bb84:bb84_secret *)
Local Lemma perm_bool_holdout_tuple_exists (t : n.-tuple 'I_N) :
  uniq t -> exists q : 'S_N, perm_bool_holdout_tuple q = t.
Proof.
  move=> Huniq.
  have Htnth_inj : injective (tnth t).
  {
    move/(tuple_uniqP t): Huniq.
    exact.
  }
  have Hcast : (n + (N - n) = N)%N.
  {
    by rewrite /N addnC addnK.
  }
  move: (@inj_ord_perm n N (tnth t) Hcast Htnth_inj) => [s Hs].
  pose q : 'S_N := ((@perm_ord k n)^-1%g * s)%g.
  exists q.
  apply: eq_from_tnth => i.
  rewrite /perm_bool_holdout_tuple /q !tnth_mktuple permM.
  have Hord :
      (@perm_ord k n)^-1%g (@rshift k n i) =
      cast_ord Hcast (lshift (N - n) i).
  {
    have Hord0 :
        (@perm_ord k n)^-1%g (@rshift k n i) =
        cast_ord (addnC n k) (lshift k i).
    {
      rewrite -[(@rshift k n i)](@perm_ordEl k n (addnC n k) i).
      exact: permK.
    }
    apply: (eq_trans Hord0).
    apply: val_inj => /=.
    reflexivity.
  }
  rewrite Hord.
  have Hti := congr1 (fun f : 'I_n -> 'I_N => f i) Hs.
  rewrite /= in Hti.
  symmetry.
  exact: Hti.
Qed.

(* card_perm_bool_holdout_tuple_fiber *)
(* infra: no tex label — fundamental & reusable (mathcomp-style) *)
(* consumer: card_perm_bool_holdout_tuple_fiber is used downstream by the BB84 secrecy proof. *)
(* path: utils:card_perm_bool_holdout_tuple_fiber -> *)
(*   utils:uniform_perm_key_tuple_pushforward -> *)
(*   utils:serfling_uniform_perm_pair_deviation_tail -> bb84:bb84_bbkey -> *)
(*   bb84:stat -> bb84:bb84_secret *)
Local Lemma card_perm_bool_holdout_tuple_fiber (t : n.-tuple 'I_N) :
  #|[pred pi : 'S_N | perm_bool_holdout_tuple pi == t]| =
    if uniq t then #|'S_k| else 0.
Proof.
  case Huniq: (uniq t).
  - move: (perm_bool_holdout_tuple_exists Huniq) => [q Hq].
    pose A : {set 'S_N} :=
      [set pi in [pred pi : 'S_N | perm_bool_holdout_tuple pi == base_holdout_tuple]].
    pose B : {set 'S_N} :=
      [set pi in [pred pi : 'S_N | perm_bool_holdout_tuple pi == t]].
    pose C := imset (fun pi : 'S_N => (pi * q)%g) (mem A).
    have HCsub : C \subset B.
    {
      apply/mathcomp.boot.fintype.subsetP => r.
      move=> /imsetP [pi Hpi ->].
      rewrite /B inE.
      move: Hpi.
      rewrite /A inE.
      move/eqP=> Hpi.
      apply/eqP.
      rewrite perm_bool_holdout_tuple_mul_right Hpi.
      apply: eq_from_tnth => i.
      have Hi :=
        congr1 (fun tt : n.-tuple 'I_N => tnth tt i) Hq.
      rewrite /perm_bool_holdout_tuple /base_holdout_tuple !tnth_mktuple in Hi.
      rewrite /base_holdout_tuple !tnth_mktuple.
      exact: Hi.
    }
    have HBsub : B \subset C.
    {
      apply/mathcomp.boot.fintype.subsetP => r.
      move=> Hr.
      apply/imsetP.
      exists (r * q^-1)%g.
      - rewrite /A inE.
        move: Hr.
        rewrite /B inE.
        move/eqP=> Hr.
        apply/eqP.
        rewrite perm_bool_holdout_tuple_mul_right Hr.
        apply: eq_from_tnth => i.
        have Hi :=
          congr1 (fun tt : n.-tuple 'I_N => q^-1%g (tnth tt i)) Hq.
        rewrite /perm_bool_holdout_tuple /base_holdout_tuple !tnth_mktuple in Hi.
        rewrite permK in Hi.
        rewrite /base_holdout_tuple !tnth_mktuple.
        exact: (esym Hi).
      - apply/permP => y.
        rewrite !permM.
        rewrite permKV.
        reflexivity.
    }
    have HcardC : #|C| = #|A|.
    {
      rewrite /C.
      apply: card_imset => pi1 pi2 Hmul.
      apply/permP => y.
      have Hy := congr1 (fun r : 'S_N => r y) Hmul.
      rewrite !permM in Hy.
      exact: perm_inj Hy.
    }
    have HcardB : #|B| = #|A|.
    {
      have HcardBC : #|B| = #|C|.
      {
        apply/eqP.
        rewrite eqn_leq.
        apply/andP.
        split.
        - exact: subset_leq_card HBsub.
        - exact: subset_leq_card HCsub.
      }
      rewrite HcardBC HcardC.
      reflexivity.
    }
    have HBcardE :
        #|[pred pi : 'S_N | perm_bool_holdout_tuple pi == t]| = #|B|.
    {
      rewrite /B cardsE.
      reflexivity.
    }
    rewrite HBcardE HcardB /A card_base_holdout_tuple_fiber.
    reflexivity.
  - have Hcard0 :
        #|[set pi in [pred pi : 'S_N | perm_bool_holdout_tuple pi == t]]| = 0.
    {
      apply/eqP.
      rewrite eqn0Ngt.
      apply/negP => Hcard_pos.
      move/card_gt0P: Hcard_pos => [pi].
      rewrite inE.
      move/eqP=> Hpi.
      move: Huniq.
      by rewrite -Hpi perm_bool_holdout_tuple_uniq.
    }
    have Hcard0E :
        #|[pred pi : 'S_N | perm_bool_holdout_tuple pi == t]| =
        #|[set pi in [pred pi : 'S_N | perm_bool_holdout_tuple pi == t]]|.
    {
      rewrite cardsE.
      reflexivity.
    }
    rewrite Hcard0E.
    exact: Hcard0.
Qed.

(* uniform_perm_key_tuple_pushforward *)
(* infra: no tex label — fundamental & reusable (mathcomp-style) *)
(* consumer: uniform_perm_key_tuple_pushforward is used downstream by the BB84 secrecy proof. *)
(* path: utils:uniform_perm_key_tuple_pushforward -> *)
(*   utils:serfling_uniform_perm_pair_deviation_tail -> bb84:bb84_bbkey -> *)
(*   bb84:stat -> bb84:bb84_secret *)
Local Lemma uniform_perm_key_tuple_pushforward (d : bitstr N) (mu : R) :
  (0 < n)%N ->
  (0 < k)%N ->
  Pr_event (fun pi : 'S_N => @uniform_perm_mu N pi) (perm_bool_deviation_event d mu) =
  Pr_event (@tuple_uniform_mu n k) (@tuple_bool_deviation_event n k d mu).
Proof.
  move=> Hn_pos Hk_pos.
  rewrite /Pr_event.
  transitivity
    (\sum_(t : n.-tuple 'I_N)
      \sum_(pi : 'S_N |
        (pi \in perm_bool_deviation_event d mu) && (perm_bool_holdout_tuple pi == t))
        @uniform_perm_mu N pi).
  {
    rewrite (partition_big (fun pi : 'S_N => perm_bool_holdout_tuple pi)
      (predT : pred (n.-tuple 'I_N))) //=.
  }
  transitivity
    (\sum_(t : n.-tuple 'I_N)
      if t \in tuple_bool_deviation_event d mu then tuple_uniform_mu t else 0).
  - apply: eq_bigr => t _.
    pose fiber_mass :=
      \sum_(pi : 'S_N | perm_bool_holdout_tuple pi == t) @uniform_perm_mu N pi.
    have Hfiber_mass : fiber_mass = tuple_uniform_mu t.
    {
      rewrite /fiber_mass /uniform_perm_mu.
      rewrite sumr_const_pred.
      rewrite sum1dep_card cardsE.
      rewrite card_perm_bool_holdout_tuple_fiber.
      case Huniq: (uniq t).
      - rewrite /tuple_uniform_mu Huniq.
        have HcardSk : (((#|'S_k|)%:R : R) = (k`!)%:R).
        {
          rewrite card_Sn.
          reflexivity.
        }
        have HcardSN : (((#|'S_N|)%:R : R) = (N`!)%:R).
        {
          rewrite card_Sn.
          reflexivity.
        }
        rewrite HcardSk HcardSN.
        have Hfall_pos : 0 < (N ^_ n)%:R :> R.
        {
          rewrite ltr0n ffact_gt0.
          have Hle : (n <= (k + n))%N.
          {
            rewrite addnC.
            exact: leq_addr.
          }
          exact: Hle.
        }
        have HNfact_pos : 0 < (N`!)%:R :> R.
        {
          by rewrite ltr0n fact_gt0.
        }
        have Hfact_nat : (N ^_ n * k`! = N`!)%N.
        {
          have Hn_le_N : (n <= N)%N.
          {
            have Hn_le_N' : (n <= (k + n))%N.
            {
              rewrite addnC.
              exact: leq_addr.
            }
            exact: Hn_le_N'.
          }
          have Hkfact : k`! = (N - n)`!.
          {
            rewrite /N addnK.
            reflexivity.
          }
          rewrite Hkfact.
          apply: ffact_fact.
          exact: Hn_le_N.
        }
        have HfactR :
            (((N ^_ n)%:R * (k`!)%:R : R) = (N`!)%:R).
        {
          have HfactR0 := congr1 (fun z : nat => z%:R : R) Hfact_nat.
          rewrite natrM in HfactR0.
          exact: HfactR0.
        }
        have Hscaled :=
          congr1 (fun z : R => z * (N`!)%:R^-1) HfactR.
        rewrite -mulrA (mulfV (lt0r_neq0 HNfact_pos)) in Hscaled.
        apply: (mulIf (lt0r_neq0 Hfall_pos)).
        rewrite [((k`!)%:R * (N`!)%:R^-1) * (N ^_ n)%:R]mulrC.
        rewrite [((N ^_ n)%:R)^-1 * (N ^_ n)%:R]mulVf ?lt0r_neq0 //.
      - rewrite /tuple_uniform_mu Huniq.
        by rewrite mul0r.
    }
    case Hbad_t : (t \in tuple_bool_deviation_event d mu).
    +
      have Heq_pred :
          \sum_(pi : 'S_N | perm_bool_holdout_tuple pi == t) @uniform_perm_mu N pi =
          \sum_(pi : 'S_N |
            (pi \in perm_bool_deviation_event d mu) && (perm_bool_holdout_tuple pi == t))
            @uniform_perm_mu N pi.
      {
        symmetry.
        apply: eq_bigl => pi.
        case Hholdout: (perm_bool_holdout_tuple pi == t); last by rewrite !andbF.
        move/eqP: Hholdout => HholdoutE.
        rewrite (perm_bool_deviation_event_tupleE d mu pi Hn_pos Hk_pos).
        by rewrite HholdoutE Hbad_t.
      }
      rewrite -Heq_pred.
      exact: Hfiber_mass.
    + have Heq0 :
          \sum_(pi : 'S_N |
            (pi \in perm_bool_deviation_event d mu) && (perm_bool_holdout_tuple pi == t))
            @uniform_perm_mu N pi = 0.
      {
        apply: big1 => pi.
        case Hholdout: (perm_bool_holdout_tuple pi == t); last by rewrite andbF.
        move/eqP: Hholdout => HholdoutE.
        rewrite (perm_bool_deviation_event_tupleE d mu pi Hn_pos Hk_pos).
        by rewrite HholdoutE Hbad_t.
      }
      rewrite Heq0.
      reflexivity.
  - rewrite -big_mkcond.
    reflexivity.
Qed.

(* serfling_uniform_perm_pair_deviation_tail *)
(* infra: no tex label — fundamental & reusable (mathcomp-style) *)
(* consumer: serfling_uniform_perm_pair_deviation_tail is used downstream by the BB84 secrecy proof. *)
(* path: utils:serfling_uniform_perm_pair_deviation_tail -> bb84:bb84_bbkey -> *)
(*   bb84:stat -> bb84:bb84_secret *)
Lemma serfling_uniform_perm_pair_deviation_tail
  (z z' : bitstr N) (mu : R) :
  (0 < n)%N ->
  (0 < k)%N ->
  0 <= mu ->
  Pr_event (fun pi : 'S_N => @uniform_perm_mu N pi) (perm_pair_deviation_event z z' mu) <=
    expR (- 2%:R * (((k * n)%:R / N%:R) * (k%:R / k.+1%:R) * mu ^+ 2)).
Proof.
  move=> Hn_pos Hk_pos Hmu_nonneg.
  (* Reduce the pair bad event to the Boolean-population bad event on xor z z' *)
  rewrite (@perm_pair_deviation_eventE n k z z' mu).
  (* Pushforward: uniform permutation distribution factors through the key-tuple *)
  rewrite uniform_perm_key_tuple_pushforward //.
  (* Tuple-level Serfling tail: Markov on the MGF + Chernoff on the centered sum *)
  exact: serfling_uniform_tuple_bool_tail Hn_pos Hk_pos Hmu_nonneg.
Qed.

(* ================================================================== *)
(* Serfling bound                                                       *)
(* tex: eqn:serfling (Serfling sampling-without-replacement bound; Nat. Commun. 3:634 (2012) Suppl. Lemma 3)                               *)
(* ================================================================== *)

(* Serfling sampling-without-replacement bound                            *)
(* tex: eqn:serfling (Serfling sampling-without-replacement bound; Nat. Commun. 3:634 (2012) Suppl. Lemma 3)                           *)
(* math: Pr[Err_key ≥ err_tot + δ | Err_tot = err_tot]                     *)
(*       ≤ exp(-2 · n · (n+k)/(k+1) · δ²).                                 *)

(* path: utils:serfling_bound -> *)
(*   utils:serfling_uniform_perm_pair_deviation_tail -> bb84:bb84_bbkey -> *)
(*   bb84:stat -> bb84:bb84_secret *)
Lemma serfling_bound (z z' : bitstr N) (errtot delta : R) :
  (0 < n)%N -> (0 < k)%N ->
  0 <= delta ->
  Pr_cond
    (fun pi : 'S_(k + n) => @uniform_perm_mu (k + n) pi)
    [set pi : 'S_(k + n) |
      @perm_pair_holdout_err n k z z' pi >= errtot + delta]%SET
    [set pi : 'S_(k + n) |
      @perm_pair_total_err n k z z' pi == errtot]%SET <=
      expR (- (2%:R * n%:R * (n + k)%:R / (k + 1)%:R * delta^2)).
Proof.
  move=> Hn_pos Hk_pos Hdelta_nonneg.
  set mu := ((n + k)%:R / k%:R) * delta.
  set bad_event : {set 'S_(k + n)} := @perm_pair_deviation_event n k z z' mu.
  set holdout_event : {set 'S_(k + n)} :=
    [set pi : 'S_(k + n) |
      @perm_pair_holdout_err n k z z' pi >= errtot + delta]%SET.
  set cond_event : {set 'S_(k + n)} :=
    [set pi : 'S_(k + n) |
      @perm_pair_total_err n k z z' pi == errtot]%SET.
  pose mu_perm := fun pi : 'S_(k + n) => @uniform_perm_mu (k + n) pi.
  pose tot := @perm_pair_total_err n k z z' (1%g : 'S_(k + n)).
  have HnR_pos : 0 < n%:R :> R by rewrite ltr0n.
  have HkR_pos : 0 < k%:R :> R by rewrite ltr0n.
  have HNR_pos : 0 < (k + n)%:R :> R.
  {
    rewrite ltr0n addn_gt0.
    by rewrite Hk_pos.
  }
  have Hmu_nonneg : 0 <= mu.
  {
    rewrite /mu.
    apply: mulr_ge0.
    - by rewrite divr_ge0 ?ler0n.
    - exact: Hdelta_nonneg.
  }
  case Htot : (tot == errtot).
  - have Hcond_setT : cond_event = [set: 'S_(k + n)]%SET.
    {
      apply/setP=> pi.
      rewrite !inE /cond_event /tot /perm_pair_total_err /=.
      by rewrite Htot.
    }
    have HsumT :
        \sum_(pi in [set: 'S_(k + n)]%SET) mu_perm pi =
        \sum_(pi : 'S_(k + n)) mu_perm pi.
    {
      apply: eq_bigl => pi.
      by rewrite inE.
    }
    have HholdoutI : (holdout_event :&: [set: 'S_(k + n)]%SET) = holdout_event.
    {
      apply/setP=> pi.
      by rewrite !inE andbT.
    }
    rewrite /Pr_cond Hcond_setT /=.
    rewrite /Pr_event HsumT uniform_perm_mu_sum1 oner_eq0 /= HholdoutI divr1.
    have Hsub pi :
        @perm_pair_holdout_err n k z z' pi >= errtot + delta ->
        @perm_pair_sample_err n k z z' pi + mu <= @perm_pair_holdout_err n k z z' pi.
    {
      rewrite /mu.
      move=> Hholdout.
      have Htot_eq : tot = errtot by exact/eqP.
      have Htot_pi : @perm_pair_total_err n k z z' pi = errtot.
      {
        rewrite /tot /perm_pair_total_err in Htot_eq |- *.
        exact: Htot_eq.
      }
      pose x : R := (@perm_pair_sample_count n k z z' pi)%:R.
      pose y : R := (@perm_pair_holdout_count n k z z' pi)%:R.
      have Hpart : ((@perm_pair_total_count n k z z')%:R : R) = x + y.
      {
        rewrite /x /y (@perm_pair_partition_countE n k z z' pi) natrD.
        reflexivity.
      }
      have Hholdout0 : @perm_pair_total_err n k z z' pi + delta <= y / n%:R.
      {
        move: Hholdout.
        rewrite Htot_pi /y /perm_pair_holdout_err.
        done.
      }
      have H1 : (((x + y) / (k + n)%:R) + delta <= y / n%:R).
      {
        move: Hholdout0.
        rewrite /perm_pair_total_err Hpart.
        done.
      }
      have H2 :
          ((((x + y) / (k + n)%:R) + delta) * (k + n)%:R <=
            (y / n%:R) * (k + n)%:R).
      {
        rewrite (ler_pM2r HNR_pos).
        exact: H1.
      }
      have Hleft :
          ((((x + y) / (k + n)%:R) + delta) * (k + n)%:R) =
            x + y + (k + n)%:R * delta :> R.
      {
        have HN_unit : (k + n)%:R \is a GRing.unit := unitf_gt0 HNR_pos.
        rewrite mulrDl.
        rewrite (divrK HN_unit (x + y)).
        by rewrite [delta * (k + n)%:R]mulrC.
      }
      have Hright :
          (y / n%:R) * (k + n)%:R = (y / n%:R) * k%:R + y :> R.
      {
        have Hn_unit : n%:R \is a GRing.unit := unitf_gt0 HnR_pos.
        rewrite natrD mulrDr.
        by rewrite (divrK Hn_unit y).
      }
      have H3 : x + (k + n)%:R * delta <= (y / n%:R) * k%:R.
      {
        move: H2.
        rewrite Hleft Hright.
        have -> : x + y + (k + n)%:R * delta = (x + (k + n)%:R * delta) + y :> R.
        {
          by rewrite -addrA [y + _]addrC addrA.
        }
        by rewrite lerD2r.
      }
      have H4 : (x + (k + n)%:R * delta) / k%:R <= y / n%:R.
      {
        have Htmp := H3.
        rewrite -ler_pdivrMr in Htmp; last exact: HkR_pos.
        exact: Htmp.
      }
      have HdivE :
          (x + (k + n)%:R * delta) / k%:R =
            x / k%:R + ((k + n)%:R / k%:R) * delta.
      {
        change (((x + (k + n)%:R * delta) * k%:R^-1) =
          x / k%:R + ((k + n)%:R / k%:R) * delta).
        rewrite mulrDl.
        rewrite -mulrA [delta * k%:R^-1]mulrC mulrA.
        reflexivity.
      }
      have H4sum := H4.
      rewrite HdivE /x /y addnC in H4sum.
      exact: H4sum.
    }
    have Hholdout_prob :
        Pr_event mu_perm holdout_event <= Pr_event mu_perm bad_event.
    {
      have HleftE :
          Pr_event mu_perm holdout_event =
          \sum_(pi in bad_event | pi \in holdout_event) mu_perm pi.
      {
        rewrite /Pr_event.
        apply: eq_bigl => pi.
        rewrite !inE.
        apply/idP/idP.
        - move=> Hpi.
          move: Hpi.
          rewrite /holdout_event.
          move=> Hpi.
          apply/andP; split.
          + rewrite /bad_event /perm_pair_deviation_event /mu.
            exact: (Hsub pi Hpi).
          + exact: Hpi.
        - by move=> /andP[].
      }
      rewrite HleftE /Pr_event.
      rewrite [X in _ <= X](bigID (mem holdout_event)) /=.
      have Hrest_ge0 :
          0 <= \sum_(pi in bad_event | ~~ (pi \in holdout_event)) mu_perm pi.
      {
        apply: sumr_ge0 => pi _.
        exact: uniform_perm_mu_nonneg.
      }
      apply: le_trans (ler_wpDr Hrest_ge0 (lexx _)).
      exact: lexx.
    }
    have Htail :=
      @serfling_uniform_perm_pair_deviation_tail z z' mu Hn_pos Hk_pos Hmu_nonneg.
    apply: (le_trans Hholdout_prob).
    apply: (le_trans Htail).
    have Hk_unit : k%:R \is a GRing.unit := unitf_gt0 HkR_pos.
    have HN_unit : (k + n)%:R \is a GRing.unit := unitf_gt0 HNR_pos.
    have Hk1_pos : 0 < k.+1%:R :> R by rewrite ltr0Sn.
    have Hk1_unit : k.+1%:R \is a GRing.unit := unitf_gt0 Hk1_pos.
    rewrite /mu expr2.
    have Hcancel :
        (((k * n)%:R / (n + k)%:R) * (k%:R / k.+1%:R) *
          ((((n + k)%:R / k%:R) * delta) ^+ 2)) =
        n%:R * (n + k)%:R / k.+1%:R * delta ^+ 2 :> R.
    {
      set A : R := (k * n)%:R / (n + k)%:R.
      set B : R := k%:R / k.+1%:R.
      set C : R := (n + k)%:R / k%:R.
      set D : R := delta.
      have HNR'_pos : 0 < (n + k)%:R :> R by rewrite addnC.
      have HAC : A * C = n%:R.
      {
        rewrite /A /C.
        rewrite -mulrA.
        rewrite [((n + k)%:R^-1 * ((n + k)%:R / k%:R))]mulrA.
        rewrite [((n + k)%:R^-1 * (n + k)%:R)]mulrC.
        rewrite mulfV.
        - rewrite mul1r.
          have -> : (k * n)%:R = n%:R * k%:R :> R by rewrite natrM mulrC.
          rewrite -mulrA.
          rewrite [k%:R * k%:R^-1]mulrC.
          rewrite mulVf.
          + by rewrite mulr1.
          + exact: lt0r_neq0 HkR_pos.
        - exact: lt0r_neq0 HNR'_pos.
      }
      have HBC : B * C = (n + k)%:R / k.+1%:R.
      {
        rewrite /B /C mulrC -mulrA.
        rewrite [(k%:R^-1 * (k%:R / k.+1%:R))]mulrA.
        rewrite [(k%:R^-1 * k%:R)]mulrC.
        rewrite mulfV.
        - by rewrite mul1r.
        - exact: lt0r_neq0 HkR_pos.
      }
      have Hsq : ((C * D) * (C * D)) = (C * C) * (D * D).
      {
        by rewrite mulrACA.
      }
      rewrite !expr2.
      rewrite Hsq.
      rewrite [A * B * (C * C * (D * D))]mulrACA.
      have HACC : A * (C * C) = n%:R * C.
      {
        have -> : A * (C * C) = (A * C) * C by rewrite -mulrA.
        by rewrite HAC.
      }
      rewrite HACC mulrA.
      rewrite [((n%:R * C) * (k%:R / k.+1%:R)) * (D * D)]mulrA.
      rewrite -!mulrA.
      have -> :
          k%:R^-1 * (k%:R * (k.+1%:R^-1 * (D * D))) =
          k.+1%:R^-1 * (D * D) :> R.
      {
        rewrite mulrA.
        rewrite [k%:R^-1 * k%:R]mulrC mulfV.
        - by rewrite mul1r.
        - exact: lt0r_neq0 HkR_pos.
      }
      by [].
    }
    have Hcancel_goal :
        (((k * n)%:R / (k + n)%:R) * (k%:R / k.+1%:R) *
          ((((n + k)%:R / k%:R) * delta) ^+ 2)) =
        n%:R * (n + k)%:R / k.+1%:R * delta ^+ 2 :> R.
    {
      have Htmp := Hcancel.
      rewrite addnC in Htmp.
      have -> : (n + k)%:R = (k + n)%:R :> R by rewrite addnC.
      exact: Htmp.
    }
    have HX :
        (((k * n)%:R / (k + n)%:R) * (k%:R / k.+1%:R) *
          (((n + k)%:R / k%:R * delta) * ((n + k)%:R / k%:R * delta))) =
        n%:R * (n + k)%:R / k.+1%:R * delta ^+ 2 :> R.
    {
      rewrite -[(((n + k)%:R / k%:R * delta) * ((n + k)%:R / k%:R * delta))]expr2.
      exact: Hcancel_goal.
    }
    rewrite [X in expR (-2%:R * X) <= _]HX.
    rewrite [delta ^+ 2]expr2.
    rewrite mulNr.
    rewrite [X in _ <= expR (- (2%:R * n%:R * (n + k)%:R / (k + 1)%:R * X))]expr2.
    have Hr :
        2%:R * n%:R * (n + k)%:R / (k + 1)%:R * (delta * delta) =
        2%:R * (n%:R * (n + k)%:R / (k + 1)%:R * (delta * delta)) :> R.
    {
      by rewrite -!mulrA.
    }
    rewrite ler_expR.
    rewrite lerN2.
    have -> : k.+1%:R = (k + 1)%:R :> R by rewrite addn1.
    by rewrite -!mulrA.
  - have Hcond_set0 : cond_event = [set pi : 'S_(k + n) | false]%SET.
    {
      apply/setP=> pi.
      rewrite !inE /cond_event /tot /perm_pair_total_err /=.
      by rewrite Htot.
    }
    rewrite /Pr_cond Hcond_set0 /=.
    rewrite /Pr_event big_set0 eqxx.
    exact: ltW (expR_gt0 _).
Qed.

End SerflingTail.

End UniformPermutationSampling.

(* ================================================================== *)
(* Q-distribution construction (lemma:stat, Nat. Commun. 3:634 (2012) Suppl. Lemma 3 proof)       *)
(* Given a distribution mu and a "good" event A with Pr[A] > 0, define  *)
(*   Q(t) := mu t / Pr[A]  if t ∈ A,  else 0.                          *)
(* This is the distribution obtained by conditioning on A.              *)
(* ================================================================== *)

(* tex: Nat. Commun. 3:634 (2012), Suppl. (Lemma 3 proof) (Q distribution)                             *)
(* math: Q(t) := mu(t) / Pr[A] if t ∈ A, else 0                          *)

(* tex: Nat. Commun. 3:634 (2012), Suppl. (Lemma 3 proof) (Bhattacharyya fidelity identity)          *)
(* math: F(P, Q) = Σ_t sqrt(mu(t) * Q(t)) = sqrt(Pr[A])                  *)

(* tex: Nat. Commun. 3:634 (2012), Suppl. (Lemma 3 proof) (purified-distance of P and Q is eps')          *)
(* math: for a normalized distribution mu and event A with                  *)
(*        1 - Pr[A] ≤ eps'^2, the classical purified distance               *)
(*        sqrt(1 - F^2) = sqrt(1 - Pr[A]) is bounded by eps'.               *)

End FvqkdReal.
