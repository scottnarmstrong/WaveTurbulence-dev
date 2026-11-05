/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.XChain.CplDraft.CoupleLimit
public import WaveTurbulence.Foundations.XChain.CumulantMultilinear
public import WaveTurbulence.Foundations.XChain.TreeCumulantPartitionCarrier
public import WaveTurbulence.Foundations.XChain.TopPartitionErrorConvergence

/-!
# CPL-2, step 2: the couple identity for a family of tree terms

Let `𝒮 ⊆ truncatedTrees M` be a finite family of trees, and let `famTerm 𝒮 = ∑_{𝒯 ∈ 𝒮} 𝒥_𝒯`. It is written
over INDUCT's index `TrTree M` with the indicator of `𝒮`, so that every sum below is indexed exactly as in
INDUCT. For `𝒮 = truncatedTrees N` this is `a^tr` (CPL-1); for `𝒮 = l0Trees N` it is `ℒ₀` (CPL-2).

**Statements.**
1. `cumulant_famTerm_eq` (all-order moments, as in INDUCT):
   `𝕂(famTerm^{ζ_j}) = famKernelExpansion + famError`. The two sides are INDUCT's per-forest kernel series and
   input errors, summed over the forests of `𝒮`.
2. `integral_norm_famTerm_sq_eq` (under `AnsatzAt` alone, with `2(2M+1) ≤ 2R_p`):
   `∫_{F_p} |famTerm_n(t)|² = famKernelExpansion + famError` for `a(p)`, and the integrand is integrable.

**Proof.** As in CPL-1 (`CoupleLimit`):
- apply 1 to the mode cutoff `c_K`;
- the left side is `∫|famTerm(c_K)|²`, since `𝔼 𝒥_𝒯(c_K) = 0` for every `+` tree;
- let `K → ∞`, by dominated convergence (envelope `aTrEnvelope M`) and Tannery's theorem
  (`tendsto_topPartitionError_truncArr`).
-/

@[expose] public section

namespace WaveTurbulence.Cpl

open Finset MeasureTheory Set Filter Topology Induct
open scoped ENNReal Classical

/-! ## The family term and its expansion -/

section Defs

variable (L γ δ : ℝ) {d : ℕ}

/-- `∑_{𝒯 ∈ 𝒮} 𝒥_𝒯`, indexed by `TrTree M`. -/
noncomputable def famTerm (p M : ℕ) (𝒮 : Finset TTree) (b : (Fin d → ℤ) → ℂ) (t : ℝ)
    (n : Fin d → ℤ) : ℂ :=
  ∑ T : TrTree M, if T.1 ∈ 𝒮 then treeTerm L γ δ p T.1 b t n else 0

theorem famTerm_eq_sum (p M : ℕ) {𝒮 : Finset TTree} (hS : 𝒮 ⊆ truncatedTrees M)
    (b : (Fin d → ℤ) → ℂ) (t : ℝ) (n : Fin d → ℤ) :
    famTerm L γ δ p M 𝒮 b t n = ∑ T ∈ 𝒮, treeTerm L γ δ p T b t n := by
  classical
  unfold famTerm
  rw [Finset.sum_coe_sort (truncatedTrees M) (fun T => if T ∈ 𝒮 then treeTerm L γ δ p T b t n else 0),
    ← sum_filter, filter_mem_eq_inter, Finset.inter_eq_right.mpr hS]

/-- The family's kernel series (INDUCT's per-forest `topPartitionKernelIntegrand` series). -/
noncomputable def famKernelExpansion {w : ℕ} (F : ℕ → Mom d → ℝ) (sig : Fin w → ℤˣ)
    (p M Natt : ℕ) (𝒮 : Finset TTree) (t : ℝ) (n : Fin w → (Fin d → ℤ)) : ℂ :=
  ∑ top : Fin w → TrTree M, if ∀ j, (top j).1 ∈ 𝒮 then
    (∏ j, zpowSign (sig j) (SysAPI.treePrefactor L γ δ d (top j).1)) *
      ∑ P : {P : Finpartition (univ : Finset (GLeaf (fun j => (top j).1))) //
          TopPartitionIrreducible (fun j => (top j).1) P},
        ∑' κ : ForestDecoration (fun j => (top j).1) d n,
          topPartitionKernelIntegrand L γ δ F sig (fun j => (top j).1) P.1 p Natt t n κ
    else 0

/-- The family's input error (INDUCT's per-forest `topPartitionError`). -/
noncomputable def famError {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) {w : ℕ}
    (F : ℕ → Mom d → ℝ) (sig : Fin w → ℤˣ) (c : Ω → (Fin d → ℤ) → ℂ) (p M Natt : ℕ)
    (𝒮 : Finset TTree) (t : ℝ) (n : Fin w → (Fin d → ℤ)) : ℂ :=
  ∑ top : Fin w → TrTree M, if ∀ j, (top j).1 ∈ 𝒮 then
    (∏ j, zpowSign (sig j) (SysAPI.treePrefactor L γ δ d (top j).1)) *
      ∑ P : {P : Finpartition (univ : Finset (GLeaf (fun j => (top j).1))) //
          TopPartitionIrreducible (fun j => (top j).1) P},
        topPartitionError μ L γ δ F sig (fun j => (top j).1) P.1 c p Natt t n
    else 0

end Defs

theorem zpowSign_ite (ζ : ℤˣ) (P : Prop) [Decidable P] (z : ℂ) :
    zpowSign ζ (if P then z else 0) = if P then zpowSign ζ z else 0 := by
  split_ifs
  · rfl
  · exact zpowSign_zero ζ

section Generic

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsFiniteMeasure μ] {w d : ℕ}
    (L γ δ : ℝ) (c : Ω → (Fin d → ℤ) → ℂ)
    (hc : ∀ n, ∀ q : ℕ, 1 ≤ q → MemLp (fun ω => c ω n) (q : ℝ≥0∞) μ)
    (hcs : ∀ᵐ ω ∂μ, Summable fun n => ‖c ω n‖)
    (hM : ∀ q : ℕ, 1 ≤ q → MemLp (fun ω => ∑' n, ‖c ω n‖) (q : ℝ≥0∞) μ)

include hc hcs hM in
/-- **The family cumulant** (all-order moments): kernel series plus input error. -/
theorem cumulant_famTerm_eq (F : ℕ → Mom d → ℝ) (sig : Fin w → ℤˣ) (p M Natt : ℕ)
    (𝒮 : Finset TTree) (t : ℝ) (hpt : (p : ℝ) ≤ t) (htp : t ≤ (p : ℝ) + 1) (n : Fin w → (Fin d → ℤ))
    (hF : ∀ q, Summable fun m : Fin d → ℤ => |F q (latticePoint L m)|) :
    cumulant μ (fun j ω => zpowSign (sig j) (famTerm L γ δ p M 𝒮 (c ω) t (n j))) univ =
      famKernelExpansion L γ δ F sig p M Natt 𝒮 t n + famError L γ δ μ F sig c p M Natt 𝒮 t n := by
  classical
  have hcm (m : Fin d → ℤ) : AEStronglyMeasurable (fun ω => c ω m) μ :=
    (hc m 1 le_rfl).aestronglyMeasurable
  let X : Fin w → TrTree M → Ω → ℂ := fun i T ω =>
    if T.1 ∈ 𝒮 then zpowSign (sig i) (treeTerm L γ δ p T.1 (c ω) t (n i)) else 0
  have hX : ∀ i T, ∀ q : ℕ, 1 ≤ q → MemLp (X i T) (q : ℝ≥0∞) μ := by
    intro i T q hq
    by_cases h : T.1 ∈ 𝒮
    · have hm := memLp_treeTerm L γ δ p T.1 c hcm hcs hM t (n i) q hq
      simp only [X, h, ite_true]
      unfold zpowSign
      split_ifs
      · exact hm
      · exact hm.star
    · simp only [X, h, ite_false]
      exact MemLp.zero
  have hsum : (fun j ω => zpowSign (sig j) (famTerm L γ δ p M 𝒮 (c ω) t (n j))) =
      fun j ω => ∑ T, X j T ω := by
    funext j ω
    simp only [famTerm, zpowSign_sum, zpowSign_ite, X]
  rw [hsum, cumulant_fintype_sum μ X hX]
  unfold famKernelExpansion famError
  rw [← sum_add_distrib]
  refine sum_congr rfl fun top _ => ?_
  by_cases h : ∀ j, (top j).1 ∈ 𝒮
  · rw [ite_eq_left h, ite_eq_left h, ← mul_add, ← sum_add_distrib]
    have hXt : (fun i ω => X i (top i) ω) =
        fun i ω => zpowSign (sig i) (treeTerm L γ δ p (top i).1 (c ω) t (n i)) := by
      funext i ω
      simp only [X, h i, ite_true]
    rw [hXt, cumulant_forest_eq_partition_carrier L γ δ p (fun j => (top j).1) c hc hcs hM t n sig]
    exact congrArg (fun z => (∏ j, zpowSign (sig j) (SysAPI.treePrefactor L γ δ d (top j).1)) * z)
      (sum_congr rfl fun P _ => topPartitionCumulant_eq_kernel_add_error L γ δ sig
        (fun j => (top j).1) P.1 c hc hcs hM p t n F Natt P.2 hpt htp hF)
  · rw [ite_eq_right h, ite_eq_right h, add_zero]
    push Not at h
    obtain ⟨j, hj⟩ := h
    exact cumulant_eq_zero_of_mem_zero μ _ univ (mem_univ j) fun ω => by simp only [X, hj, ite_false]

end Generic

/-! ## Under `AnsatzAt` -/

section Ansatz

variable (P : WTParams) {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (g : (Fin P.d → ℤ) → Ω → ℂ) (hG : IsGaussianData μ g)
    (a : Ω → ℝ → (Fin P.d → ℤ) → ℂ) (Fev : ℕ → Set Ω) (R : ℕ → Mom P.d → ℝ)
    (E : ℕ → (Fin P.d → ℤ) → ℝ)
    (Et : ℕ → (m : ℕ) → (Fin (2 * m) → ℤˣ) → (Fin (2 * m) → (Fin P.d → ℤ)) → ℂ) (p : ℕ)
    (ha : AnsatzAt P μ g a Fev R E Et p)
    (hrapid : ∀ ω ∈ Fev p, IsRapidDecay (initialCoeff P.L P.φin g ω))
    (hL : 1 ≤ P.L) (hδ : 0 < P.δ) (hsmall : P.δ ^ P.ν ≤ 1 / 2) (C : ℝ) (hC : 2 ≤ C)
    (hF : ∀ n, |inputsF P R p (latticePoint P.L n)| ≤
      C * jbr (latticePoint P.L n) ^ (-(P.Lambda p : ℝ)))
    (hsumF : ∀ q, Summable fun m : Fin P.d → ℤ => |inputsF P R q (latticePoint P.L m)|)
    (hΛ : (P.d : ℝ) + 1 ≤ (P.Lambda p : ℝ) / 2)

include hG ha hrapid in
/-- **`𝔼_p 𝒥_𝒯(c_K) = 0`** for every tree. -/
theorem integral_treeTerm_truncArr_eq_zero (hL0 : 0 < P.L) (K : ℕ) (T : TTree) (t : ℝ)
    (n : Fin P.d → ℤ) :
    ∫ ω in Fev p, treeTerm P.L P.γ P.δ p T (truncArr K (a ω p)) t n ∂μ = 0 := by
  classical
  have hc := memLp_truncInput P μ g a Fev R E Et p ha K
  have hcs : ∀ᵐ ω ∂μ.restrict (Fev p), Summable fun n => ‖truncArr K (a ω p) n‖ :=
    Eventually.of_forall fun ω => summable_norm_truncArr K (a ω p)
  have hM := memLp_l1_truncInput P μ g a Fev R E Et p ha K
  have h := cumulant_forest_eq_partition_carrier P.L P.γ P.δ p (fun _ : Fin 1 => T)
    (fun ω => truncArr K (a ω p)) hc hcs hM t (fun _ => n) (fun _ => 1)
  have hu : (univ : Finset (Fin 1)) = {0} := rfl
  rw [hu, cumulant_singleton] at h
  have hz1 (z : ℂ) : zpowSign 1 z = z := ite_eq_left rfl
  simp only [hz1] at h
  rw [h]
  refine mul_eq_zero_of_right _ (sum_eq_zero fun Q _ => ?_)
  refine (tsum_congr fun κ => ?_).trans tsum_zero
  rw [topPartitionCumulantIntegrand_truncArr]
  split_ifs
  · have hs : ∑ j, ((fun _ : Fin 1 => (1 : ℤˣ)) j : ℤ) ≠ 0 := by simp
    obtain ⟨B, hB⟩ := exists_unbalanced_leaf_block (fun _ : Fin 1 => T) (fun _ : Fin 1 => (1 : ℤˣ))
      hs Q.1
    unfold topPartitionCumulantIntegrand
    rw [prod_eq_zero (mem_univ B) (ansatz_unbalanced_topBlock_zero P μ g hG hL0 a Fev R E Et p ha hrapid
      (fun _ : Fin 1 => (1 : ℤˣ)) (fun _ : Fin 1 => T) Q.1 κ B hB 0).1, mul_zero]
  · rfl

theorem aestronglyMeasurable_famTerm (M : ℕ) (𝒮 : Finset TTree) (c : Ω → (Fin P.d → ℤ) → ℂ)
    (ν : Measure Ω) (hcm : ∀ n, AEStronglyMeasurable (fun ω => c ω n) ν)
    (hcs : ∀ᵐ ω ∂ν, Summable fun n => ‖c ω n‖) (t : ℝ) (n : Fin P.d → ℤ) :
    AEStronglyMeasurable (fun ω => famTerm P.L P.γ P.δ p M 𝒮 (c ω) t n) ν := by
  classical
  unfold famTerm
  refine Finset.aestronglyMeasurable_fun_sum _ fun (T : TrTree M) _ => ?_
  by_cases h : T.1 ∈ 𝒮
  · simp only [h, ite_true]
    exact aestronglyMeasurable_treeTerm P.L P.γ P.δ p T.1 c hcm hcs t n
  · simp only [h, ite_false]
    exact aestronglyMeasurable_const

theorem norm_famTerm_le_envelope (M : ℕ) (𝒮 : Finset TTree) {b : (Fin P.d → ℤ) → ℂ}
    (hb : Summable fun m => ‖b m‖) (t : ℝ) (n : Fin P.d → ℤ) :
    ‖famTerm P.L P.γ P.δ p M 𝒮 b t n‖ ≤ aTrEnvelope P p M t * (1 + ∑' m, ‖b m‖) ^ (2 * M + 1) := by
  classical
  have hS : 0 ≤ ∑' m, ‖b m‖ := tsum_nonneg fun _ => norm_nonneg _
  unfold famTerm aTrEnvelope
  rw [sum_mul]
  refine (norm_sum_le _ _).trans (sum_le_sum fun T _ => ?_)
  have hcard : Fintype.card (GLeaf (single T.1)) ≤ 2 * M + 1 := by
    have h := forest_card_leaves_le (single T.1) (N := M) (fun _ => mem_truncatedTrees.mp T.2)
    simpa only [one_mul] using h
  have hpow : (∑' m, ‖b m‖) ^ Fintype.card (GLeaf (single T.1)) ≤ (1 + ∑' m, ‖b m‖) ^ (2 * M + 1) :=
    (pow_le_pow_left₀ hS (by linarith) _).trans (pow_le_pow_right₀ (by linarith) hcard)
  have h0 : 0 ≤ ‖SysAPI.treePrefactor P.L P.γ P.δ P.d T.1‖ * SysAPI.boxVol T.1 p t :=
    mul_nonneg (norm_nonneg _) (SysAPI.boxVol_nonneg _ _ _)
  split_ifs
  · exact (norm_treeTerm_le_l1 P.L P.γ P.δ p T.1 hb t n).trans (mul_le_mul_of_nonneg_left hpow h0)
  · rw [norm_zero]
    exact mul_nonneg h0 (pow_nonneg (by linarith) _)

theorem tendsto_famTerm_truncArr (M : ℕ) (𝒮 : Finset TTree) {b : (Fin P.d → ℤ) → ℂ}
    (hb : Summable fun m => ‖b m‖) (t : ℝ) (n : Fin P.d → ℤ) :
    Tendsto (fun K : ℕ => famTerm P.L P.γ P.δ p M 𝒮 (truncArr K b) t n) atTop
      (𝓝 (famTerm P.L P.γ P.δ p M 𝒮 b t n)) := by
  classical
  unfold famTerm
  refine tendsto_finsetSum _ fun T _ => ?_
  split_ifs
  · exact tendsto_treeTerm_truncArr P.L P.γ P.δ p T.1 hb t n
  · exact tendsto_const_nhds

include hG ha hrapid hL in
theorem integral_famTerm_truncArr_eq_zero (M : ℕ) (𝒮 : Finset TTree) (K : ℕ) (t : ℝ)
    (n : Fin P.d → ℤ) :
    ∫ ω in Fev p, famTerm P.L P.γ P.δ p M 𝒮 (truncArr K (a ω p)) t n ∂μ = 0 := by
  classical
  have hcm (m : Fin P.d → ℤ) : AEStronglyMeasurable (fun ω => truncArr K (a ω p) m)
      (μ.restrict (Fev p)) := (memLp_truncInput P μ g a Fev R E Et p ha K m 1 le_rfl).aestronglyMeasurable
  have hcs : ∀ᵐ ω ∂μ.restrict (Fev p), Summable fun n => ‖truncArr K (a ω p) n‖ :=
    Eventually.of_forall fun ω => summable_norm_truncArr K (a ω p)
  unfold famTerm
  rw [integral_finsetSum _ fun T _ => ?_]
  · refine sum_eq_zero fun T _ => ?_
    split_ifs
    · exact integral_treeTerm_truncArr_eq_zero P μ g hG a Fev R E Et p ha hrapid
        (zero_lt_one.trans_le hL) K T.1 t n
    · exact integral_zero _ _
  · split_ifs
    · have hm := memLp_treeTerm P.L P.γ P.δ p T.1 (fun ω => truncArr K (a ω p)) hcm hcs
        (memLp_l1_truncInput P μ g a Fev R E Et p ha K) t n 1 le_rfl
      rw [Nat.cast_one] at hm
      exact hm.integrable le_rfl
    · exact integrable_zero _ _ _

include hG ha hrapid hL hδ hsmall hC hF hΛ in
theorem integrable_norm_famTerm_sq (M : ℕ) (𝒮 : Finset TTree) (hNR : 2 * (2 * M + 1) ≤ 2 * P.R p)
    (t : ℝ) (n : Fin P.d → ℤ) :
    Integrable (fun ω => ‖famTerm P.L P.γ P.δ p M 𝒮 (a ω p) t n‖ ^ 2) (μ.restrict (Fev p)) := by
  have hcs := ansatz_input_summable ha (zero_lt_one.trans_le hL)
  have hm := aestronglyMeasurable_famTerm P p M 𝒮 (fun ω => a ω p) (μ.restrict (Fev p))
    (fun n => (measurable_input P μ g a Fev R E Et p ha n).aestronglyMeasurable) hcs t n
  refine (integrable_envelope_sq P μ g hG a Fev R E Et p ha hrapid hL hδ hsmall C hC hF hΛ M hNR t).mono'
    (hm.norm.pow 2) ?_
  filter_upwards [hcs] with ω hω
  rw [Real.norm_of_nonneg (by positivity)]
  exact pow_le_pow_left₀ (norm_nonneg _) (norm_famTerm_le_envelope P p M 𝒮 hω t n) 2

include hG ha hrapid hL hδ hsmall hC hF hΛ in
theorem tendsto_integral_norm_famTerm_truncArr_sq (M : ℕ) (𝒮 : Finset TTree)
    (hNR : 2 * (2 * M + 1) ≤ 2 * P.R p) (t : ℝ) (n : Fin P.d → ℤ) :
    Tendsto (fun K : ℕ => ∫ ω in Fev p, ‖famTerm P.L P.γ P.δ p M 𝒮 (truncArr K (a ω p)) t n‖ ^ 2 ∂μ)
      atTop (𝓝 (∫ ω in Fev p, ‖famTerm P.L P.γ P.δ p M 𝒮 (a ω p) t n‖ ^ 2 ∂μ)) := by
  have hcs := ansatz_input_summable ha (zero_lt_one.trans_le hL)
  have hmeasK (K : ℕ) : AEStronglyMeasurable
      (fun ω => ‖famTerm P.L P.γ P.δ p M 𝒮 (truncArr K (a ω p)) t n‖ ^ 2) (μ.restrict (Fev p)) :=
    (aestronglyMeasurable_famTerm P p M 𝒮 (fun ω => truncArr K (a ω p)) (μ.restrict (Fev p))
      (fun n => (memLp_truncInput P μ g a Fev R E Et p ha K n 1 le_rfl).aestronglyMeasurable)
      (Eventually.of_forall fun ω => summable_norm_truncArr K (a ω p)) t n).norm.pow 2
  have hboundK (K : ℕ) : ∀ᵐ ω ∂μ.restrict (Fev p),
      ‖‖famTerm P.L P.γ P.δ p M 𝒮 (truncArr K (a ω p)) t n‖ ^ 2‖ ≤
        (aTrEnvelope P p M t * (1 + ∑' m, ‖a ω p m‖) ^ (2 * M + 1)) ^ 2 := by
    filter_upwards [hcs] with ω hω
    rw [Real.norm_of_nonneg (by positivity)]
    refine pow_le_pow_left₀ (norm_nonneg _) ((norm_famTerm_le_envelope P p M 𝒮
      (summable_norm_truncArr K (a ω p)) t n).trans ?_) 2
    refine mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) ?_ _)
      (sum_nonneg fun T _ => mul_nonneg (norm_nonneg _) (SysAPI.boxVol_nonneg _ _ _))
    linarith [tsum_norm_truncArr_le K hω]
  have hlim : ∀ᵐ ω ∂μ.restrict (Fev p), Tendsto
      (fun K : ℕ => ‖famTerm P.L P.γ P.δ p M 𝒮 (truncArr K (a ω p)) t n‖ ^ 2) atTop
      (𝓝 (‖famTerm P.L P.γ P.δ p M 𝒮 (a ω p) t n‖ ^ 2)) := by
    filter_upwards [hcs] with ω hω
    exact ((tendsto_famTerm_truncArr P p M 𝒮 hω t n).norm).pow 2
  exact tendsto_integral_of_dominated_convergence _ hmeasK
    (integrable_envelope_sq P μ g hG a Fev R E Et p ha hrapid hL hδ hsmall C hC hF hΛ M hNR t)
    hboundK hlim

include hG ha hrapid hL hδ hsmall hC hF hsumF hΛ in
theorem tendsto_famError_truncArr (M : ℕ) (𝒮 : Finset TTree) (sig : Fin 2 → ℤˣ)
    (hNR : 2 * (2 * M + 1) ≤ 2 * P.R p) (t : ℝ) (hpt : (p : ℝ) ≤ t) (htp : t ≤ (p : ℝ) + 1)
    (n : Fin 2 → (Fin P.d → ℤ)) :
    Tendsto (fun K : ℕ => famError P.L P.γ P.δ (μ.restrict (Fev p)) (inputsF P R) sig
        (fun ω => truncArr K (a ω p)) p M (P.N p) 𝒮 t n) atTop
      (𝓝 (famError P.L P.γ P.δ (μ.restrict (Fev p)) (inputsF P R) sig (fun ω => a ω p) p M (P.N p)
        𝒮 t n)) := by
  classical
  unfold famError
  refine tendsto_finsetSum _ fun top _ => ?_
  split_ifs
  · refine Tendsto.const_mul _ (tendsto_finsetSum _ fun Q _ => ?_)
    have hT (j : Fin 2) : (top j).1.order ≤ M := mem_truncatedTrees.mp (top j).2
    exact tendsto_topPartitionError_truncArr P μ g hG a Fev R E Et p ha hrapid hL hδ hsmall C hC hF
      hsumF hΛ sig (fun j => (top j).1) Q.1 Q.2 (fun B => (topBlock_card_le _ hT Q.1 B).trans hNR) t hpt
      htp n
  · exact tendsto_const_nhds

include hG ha hrapid hL hδ hsmall hC hF hsumF hΛ in
/-- **The family couple identity for `a(p)`, under `AnsatzAt`.** -/
theorem integral_norm_famTerm_sq_eq (M : ℕ) (𝒮 : Finset TTree) (hNR : 2 * (2 * M + 1) ≤ 2 * P.R p)
    (t : ℝ) (hpt : (p : ℝ) ≤ t) (htp : t ≤ (p : ℝ) + 1) (n : Fin P.d → ℤ) :
    (((∫ ω in Fev p, ‖famTerm P.L P.γ P.δ p M 𝒮 (a ω p) t n‖ ^ 2 ∂μ : ℝ)) : ℂ) =
      famKernelExpansion P.L P.γ P.δ (inputsF P R) ![1, -1] p M (P.N p) 𝒮 t (fun _ => n) +
        famError P.L P.γ P.δ (μ.restrict (Fev p)) (inputsF P R) ![1, -1] (fun ω => a ω p) p M (P.N p)
          𝒮 t (fun _ => n) := by
  classical
  have hK (K : ℕ) :
      (((∫ ω in Fev p, ‖famTerm P.L P.γ P.δ p M 𝒮 (truncArr K (a ω p)) t n‖ ^ 2 ∂μ : ℝ)) : ℂ) =
      famKernelExpansion P.L P.γ P.δ (inputsF P R) ![1, -1] p M (P.N p) 𝒮 t (fun _ => n) +
        famError P.L P.γ P.δ (μ.restrict (Fev p)) (inputsF P R) ![1, -1]
          (fun ω => truncArr K (a ω p)) p M (P.N p) 𝒮 t (fun _ => n) := by
    have h := cumulant_famTerm_eq (μ := μ.restrict (Fev p)) P.L P.γ P.δ (fun ω => truncArr K (a ω p))
      (memLp_truncInput P μ g a Fev R E Et p ha K)
      (Eventually.of_forall fun ω => summable_norm_truncArr K (a ω p))
      (memLp_l1_truncInput P μ g a Fev R E Et p ha K) (inputsF P R) ![1, -1] p M (P.N p) 𝒮 t hpt htp
      (fun _ => n) hsumF
    rw [cumulant_fin_two] at h
    have h0 := integral_famTerm_truncArr_eq_zero P μ g hG a Fev R E Et p ha hrapid hL M 𝒮 K t n
    have hz1 (z : ℂ) : zpowSign ((![1, -1] : Fin 2 → ℤˣ) 0) z = z := ite_eq_left rfl
    have hz2 (z : ℂ) : zpowSign ((![1, -1] : Fin 2 → ℤˣ) 1) z = (starRingEnd ℂ) z :=
      ite_eq_right (by decide)
    simp only [hz1, hz2, Complex.mul_conj, Complex.normSq_eq_norm_sq] at h
    rw [h0, zero_mul, sub_zero, integral_complex_ofReal] at h
    push_cast at h ⊢
    exact h
  have hl := (Complex.continuous_ofReal.tendsto _).comp
    (tendsto_integral_norm_famTerm_truncArr_sq P μ g hG a Fev R E Et p ha hrapid hL hδ hsmall C hC hF hΛ
      M 𝒮 hNR t n)
  have hr := (tendsto_famError_truncArr P μ g hG a Fev R E Et p ha hrapid hL hδ hsmall C hC hF hsumF hΛ
    M 𝒮 ![1, -1] hNR t hpt htp (fun _ => n)).const_add
    (famKernelExpansion P.L P.γ P.δ (inputsF P R) ![1, -1] p M (P.N p) 𝒮 t (fun _ => n))
  simp only [Function.comp_def, hK] at hl
  exact tendsto_nhds_unique hl hr

end Ansatz

end WaveTurbulence.Cpl
