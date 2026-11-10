/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.VineEst.VineEstS4.SplitFubiniInputs
public import WaveTurbulence.Foundations.VineEst.VineEstS4.Rg5SSum

/-! # Linearity of the S-side in the lower factor (V5 Step 4b, step 4, WP-E, part 1)

`integrable_tsum_of_summable_integral_norm`: the pointwise sum of a family of integrable functions with summable `L¹` norms is
integrable.  `SOK`: the integrand of `sSum` is integrable in `σ` for every `xS` and its `L¹` norms are summable in `xS`.
`sSum_finsetSum`: for a finite family of lower factors with `SOK`, `sSum` of the pointwise sum is the sum of the `sSum`.
-/

@[expose] public section
variable {rowSelU : Unit} [rowSel : WaveTurbulence.VineEst.RowSel rowSelU]
set_option autoImplicit false
open WaveTurbulence.VineParamContract
namespace WaveTurbulence.VineEstS4
open WaveTurbulence WaveTurbulence.Twist WaveTurbulence.LFTwist WaveTurbulence.RegRed WaveTurbulence.Reg.Skeleton TTree
  MeasureTheory Filter Topology
open scoped ENNReal NNReal

theorem ae_summable_of_summable_integral_norm {α ι E : Type*} [MeasurableSpace α] {μ : Measure α} [Countable ι]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {F : ι → α → E} (hF_int : ∀ i, Integrable (F i) μ) (hF_sum : Summable fun i ↦ ∫ a, ‖F i a‖ ∂μ) :
    ∑' i, ∫⁻ a, ‖F i a‖ₑ ∂μ ≠ ∞ ∧ ∫⁻ a, ∑' i, ‖F i a‖ₑ ∂μ = ∑' i, ∫⁻ a, ‖F i a‖ₑ ∂μ ∧
      ∀ᵐ a ∂μ, Summable fun i => ‖F i a‖ := by
  have hfin : ∑' i, ∫⁻ a, ‖F i a‖ₑ ∂μ ≠ ∞ := by
    have (i : ι) : ∫⁻ a, ‖F i a‖ₑ ∂μ = ‖∫ a, ‖F i a‖ ∂μ‖ₑ := by
      dsimp [enorm]
      rw [lintegral_coe_eq_integral _ (hF_int i).norm, ENNReal.coe_nnreal_eq, coe_nnnorm,
        Real.norm_of_nonneg (integral_nonneg (fun a ↦ norm_nonneg (F i a)))]
      simp only [coe_nnnorm]
    rw [funext this]
    exact ENNReal.tsum_coe_ne_top_iff_summable.2 <| NNReal.summable_coe.1 hF_sum.abs
  have hl : ∫⁻ a, ∑' i, ‖F i a‖ₑ ∂μ = ∑' i, ∫⁻ a, ‖F i a‖ₑ ∂μ :=
    lintegral_tsum (fun i => (hF_int i).1.enorm)
  have hae : ∀ᵐ a ∂μ, ∑' i, ‖F i a‖ₑ < ∞ := by
    have : ∫⁻ a, ∑' i, ‖F i a‖ₑ ∂μ ≠ ∞ := hl ▸ hfin
    exact ae_lt_top' (AEMeasurable.ennreal_tsum (fun i => (hF_int i).1.enorm)) this
  refine ⟨hfin, hl, ?_⟩
  filter_upwards [hae] with a ha
  have h1 : ∑' i, ‖F i a‖ₑ ≠ ∞ := ha.ne
  have := (ENNReal.tsum_coe_ne_top_iff_summable.1 (by simpa [enorm] using h1) : Summable fun i => ‖F i a‖₊)
  exact NNReal.summable_coe.2 this

theorem integrable_tsum_of_summable_integral_norm {α ι E : Type*} [MeasurableSpace α] {μ : Measure α} [Countable ι]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {F : ι → α → E} (hF_int : ∀ i, Integrable (F i) μ) (hF_sum : Summable fun i ↦ ∫ a, ‖F i a‖ ∂μ) :
    Integrable (fun a => ∑' i, F i a) μ := by
  obtain ⟨hfin, hl, hsum⟩ := ae_summable_of_summable_integral_norm hF_int hF_sum
  refine ⟨?_, ?_⟩
  · refine aestronglyMeasurable_of_tendsto_ae (u := (atTop : Filter (Finset ι)))
      (f := fun (s : Finset ι) a => ∑ i ∈ s, F i a) (fun s => ?_) ?_
    · exact Finset.aestronglyMeasurable_fun_sum s (fun i _ => (hF_int i).1)
    · filter_upwards [hsum] with a ha
      exact (Summable.of_norm ha).hasSum
  · refine lt_of_le_of_lt (lintegral_mono_ae ?_) (hl ▸ hfin.lt_top)
    filter_upwards [hsum] with a ha
    exact enorm_tsum_le_tsum_enorm

/-- `∫ ‖∑' F‖ ≤ ∑' ∫ ‖F‖`. -/
theorem integral_norm_tsum_le {α ι E : Type*} [MeasurableSpace α] {μ : Measure α} [Countable ι]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {F : ι → α → E} (hF_int : ∀ i, Integrable (F i) μ) (hF_sum : Summable fun i ↦ ∫ a, ‖F i a‖ ∂μ) :
    ∫ a, ‖∑' i, F i a‖ ∂μ ≤ ∑' i, ∫ a, ‖F i a‖ ∂μ := by
  obtain ⟨_, _, hsum⟩ := ae_summable_of_summable_integral_norm hF_int hF_sum
  have hN : ∀ i, Integrable (fun a => ‖F i a‖) μ := fun i => (hF_int i).norm
  have hNs : Summable fun i ↦ ∫ a, ‖(‖F i a‖)‖ ∂μ := by simpa only [norm_norm] using hF_sum
  have hint : Integrable (fun a => ∑' i, ‖F i a‖) μ := integrable_tsum_of_summable_integral_norm hN hNs
  have hint2 : Integrable (fun a => ‖∑' i, F i a‖) μ := (integrable_tsum_of_summable_integral_norm hF_int hF_sum).norm
  calc ∫ a, ‖∑' i, F i a‖ ∂μ ≤ ∫ a, ∑' i, ‖F i a‖ ∂μ := by
        refine integral_mono_ae hint2 hint ?_
        filter_upwards [hsum] with a ha
        exact norm_tsum_le_tsum_norm ha
    _ = ∑' i, ∫ a, ‖F i a‖ ∂μ := (integral_tsum_of_summable_integral_norm hN hNs).symm

section SOK
variable {w d : ℕ} {G : Garden w} {S : Finset (GBranch G.tree)} {a b : GBranch G.tree} (RS : CLRegionData G S a b)
  (D : ReconstructionData G) (hG : G.IsPlain) (L γ δ : ℝ) (F : ℕ → Mom d → ℝ) (layer : GNode (D.forest hG) → ℕ)
  (hLayer : IsLayering (D.garden hG) layer) (base : Mom d) (t0 t1 t2 : ℝ) (e f : Mom d) (n0 n1 : GNode G.tree)

/-- The integrand of `sSum` at `xS`. -/
@[expose] noncomputable def sInt (Φ : ℝ → Mom d → Mom d → ℂ) (xS : ExtS RS L base e f) : CLInternalTime RS → ℂ :=
  fun σ => spart D hG L γ δ F layer hLayer base S a b xS.1 (clLocalClock RS ![t0, t1, t2] σ) *
    Φ (clLocalClock RS ![t0, t1, t2] σ b) (base + latticePoint L (xS.1 n0)) (base + latticePoint L (xS.1 n1))

/-- Integrability and summability of the integrand of `sSum`. -/
@[expose] def SOK (Φ : ℝ → Mom d → Mom d → ℂ) : Prop :=
  (∀ xS, Integrable (sInt RS D hG L γ δ F layer hLayer base t0 t1 t2 e f n0 n1 Φ xS)) ∧
    Summable fun xS => ∫ σ, ‖sInt RS D hG L γ δ F layer hLayer base t0 t1 t2 e f n0 n1 Φ xS σ‖

theorem sSum_eq (Φ : ℝ → Mom d → Mom d → ℂ) :
    sSum RS D hG L γ δ F layer hLayer base t0 t1 t2 e f n0 n1 Φ =
      (coupling d L γ δ : ℂ) ^ clLocalOrder1 RS * clLocalZeta RS *
        ∑' xS : ExtS RS L base e f, ∫ σ, sInt RS D hG L γ δ F layer hLayer base t0 t1 t2 e f n0 n1 Φ xS σ := rfl

theorem SOK.summable_int {Φ : ℝ → Mom d → Mom d → ℂ}
    (h : SOK RS D hG L γ δ F layer hLayer base t0 t1 t2 e f n0 n1 Φ) :
    Summable fun xS => ∫ σ, sInt RS D hG L γ δ F layer hLayer base t0 t1 t2 e f n0 n1 Φ xS σ :=
  Summable.of_norm_bounded h.2 (fun xS => norm_integral_le_integral_norm _)

/-- **Linearity of the S-side in the lower factor.** -/
theorem sSum_finsetSum {β : Type*} (s : Finset β) (Φ : β → ℝ → Mom d → Mom d → ℂ)
    (h : ∀ i ∈ s, SOK RS D hG L γ δ F layer hLayer base t0 t1 t2 e f n0 n1 (Φ i)) :
    sSum RS D hG L γ δ F layer hLayer base t0 t1 t2 e f n0 n1 (fun t E F' => ∑ i ∈ s, Φ i t E F') =
      ∑ i ∈ s, sSum RS D hG L γ δ F layer hLayer base t0 t1 t2 e f n0 n1 (Φ i) := by
  rw [sSum_eq]
  simp_rw [sSum_eq]
  rw [← Finset.mul_sum]
  congr 1
  have hint : ∀ xS, sInt RS D hG L γ δ F layer hLayer base t0 t1 t2 e f n0 n1 (fun t E F' => ∑ i ∈ s, Φ i t E F') xS =
      fun σ => ∑ i ∈ s, sInt RS D hG L γ δ F layer hLayer base t0 t1 t2 e f n0 n1 (Φ i) xS σ := by
    intro xS
    funext σ
    simp only [sInt, Finset.mul_sum]
  have hx : ∀ xS, ∫ σ, sInt RS D hG L γ δ F layer hLayer base t0 t1 t2 e f n0 n1 (fun t E F' => ∑ i ∈ s, Φ i t E F') xS σ =
      ∑ i ∈ s, ∫ σ, sInt RS D hG L γ δ F layer hLayer base t0 t1 t2 e f n0 n1 (Φ i) xS σ := by
    intro xS
    rw [hint xS]
    exact integral_finset_sum s (fun i hi => (h i hi).1 xS)
  simp_rw [hx]
  exact Summable.tsum_finsetSum (fun i hi => (h i hi).summable_int RS D hG L γ δ F layer hLayer base t0 t1 t2 e f n0 n1)

end SOK

end WaveTurbulence.VineEstS4
