/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Mathlib.Analysis.Calculus.DSlope
public import Mathlib.MeasureTheory.Integral.DominatedConvergence
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Measure.Haar.Unique
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
import Mathlib.MeasureTheory.Group.Integral

/-!
# One-dimensional principal-value cancellation

The scalar cancellation used in DH21 Lemma 6.3 (L1338–L1347): an even cutoff
allows replacement of `f(u)/u` by `(f(u)-f(-u))/(2u)`. The latter has a
continuous extension at zero and is integrable for a compactly supported test
function differentiable at zero. These are analytic helpers, not the
frequency-uniform estimate of Lemma 6.3.
-/

public section

open MeasureTheory Filter Topology Set

namespace WaveTurbulence.Resonant

/-- A scalar cutoff equal to one near zero. Smooth cutoffs of DH21 §2 satisfy
these hypotheses; differentiability of the cutoff is unnecessary here. -/
structure IsPVCutoff (χ : ℝ → ℝ) : Prop where
  cont : Continuous χ
  compact : HasCompactSupport χ
  even : ∀ u, χ (-u) = χ u
  near : χ =ᶠ[𝓝 0] fun _ => 1

/-- Finite truncation by `χ∞(μu) = 1 - χ(μu)`. -/
@[expose] noncomputable def pvTruncation (χ : ℝ → ℝ) (μ : ℝ) (f : ℝ → ℝ) : ℝ :=
  ∫ u, ((1 - χ (μ * u)) / u) * f u

/-- The continuous symmetric quotient, with its derivative value at zero. -/
@[expose] noncomputable def pvQuotient (f : ℝ → ℝ) (u : ℝ) : ℝ :=
  2⁻¹ * dslope (fun v => f v - f (-v)) 0 u

theorem pvQuotient_of_ne (f : ℝ → ℝ) {u : ℝ} (hu : u ≠ 0) :
    pvQuotient f u = (f u - f (-u)) / (2 * u) := by
  simp [pvQuotient, dslope_of_ne _ hu, slope_def_field]
  ring

theorem continuous_pvQuotient {f : ℝ → ℝ} (hc : Continuous f)
    (hd : DifferentiableAt ℝ f 0) : Continuous (pvQuotient f) := by
  have hg : Continuous (fun u => f u - f (-u)) := hc.sub (hc.comp continuous_neg)
  have hgd : DifferentiableAt ℝ (fun u => f u - f (-u)) 0 := by
    exact hd.sub (by
      have hdf : DifferentiableAt ℝ f (- (0 : ℝ)) := by simpa using hd
      exact hdf.comp 0 differentiableAt_id.neg)
  have hh := (continuousOn_dslope (f := fun u => f u - f (-u)) (a := 0)
    (s := Set.univ) Filter.univ_mem).mpr ⟨hg.continuousOn, hgd⟩
  exact continuous_const.mul (continuousOn_univ.mp hh)

theorem hasCompactSupport_pvQuotient {f : ℝ → ℝ} (hf : HasCompactSupport f) :
    HasCompactSupport (pvQuotient f) := by
  have hn := hf.comp_homeomorph (Homeomorph.neg ℝ)
  rw [hasCompactSupport_iff_eventuallyEq, Filter.coclosedCompact_eq_cocompact] at hf hn ⊢
  filter_upwards [hf, hn, (isCompact_singleton (x := (0 : ℝ))).compl_mem_cocompact]
    with u hu hnu h0
  have hne : u ≠ 0 := by simpa using h0
  change f (-u) = 0 at hnu
  change f u = 0 at hu
  rw [pvQuotient_of_ne f hne, hu, hnu]
  simp

theorem integrable_pvQuotient {f : ℝ → ℝ} (hc : Continuous f)
    (hd : DifferentiableAt ℝ f 0) (hf : HasCompactSupport f) :
    Integrable (pvQuotient f) :=
  (continuous_pvQuotient hc hd).integrable_of_hasCompactSupport
    (hasCompactSupport_pvQuotient hf)

namespace IsPVCutoff

variable {χ : ℝ → ℝ}

theorem continuous_div (hχ : IsPVCutoff χ) (μ : ℝ) :
    Continuous (fun u : ℝ => (1 - χ (μ * u)) / u) := by
  rw [continuous_iff_continuousAt]
  intro u
  by_cases hu : u = 0
  · subst u
    have ht : Tendsto (fun u : ℝ => μ * u) (𝓝 0) (𝓝 0) := by
      exact tendsto_const_nhds.mul tendsto_id |>.trans
        (by simp)
    have he : (fun u : ℝ => (1 - χ (μ * u)) / u) =ᶠ[𝓝 0] fun _ => 0 := by
      filter_upwards [ht.eventually hχ.near] with u hu
      simp only [hu, sub_self, zero_div]
    exact continuousAt_const.congr he.symm
  · exact (continuous_const.sub (hχ.cont.comp
      (continuous_const.mul continuous_id))).continuousAt.div continuousAt_id hu

theorem integrable_truncation (hχ : IsPVCutoff χ) (μ : ℝ) {f : ℝ → ℝ}
    (hc : Continuous f) (hf : HasCompactSupport f) :
    Integrable (fun u : ℝ => ((1 - χ (μ * u)) / u) * f u) :=
  ((hχ.continuous_div μ).mul hc).integrable_of_hasCompactSupport (hf.mul_left)

/-- Exact symmetric cancellation for every finite truncation. -/
theorem pvTruncation_eq (hχ : IsPVCutoff χ) (μ : ℝ) {f : ℝ → ℝ}
    (hc : Continuous f) (hf : HasCompactSupport f) :
    pvTruncation χ μ f = ∫ u, (1 - χ (μ * u)) * pvQuotient f u := by
  let q : ℝ → ℝ := fun u => (1 - χ (μ * u)) / u
  have hi := hχ.integrable_truncation μ hc hf
  have hni : Integrable (fun u => q u * f (-u)) :=
    hχ.integrable_truncation μ (hc.comp continuous_neg)
      (hf.comp_homeomorph (Homeomorph.neg ℝ))
  have heven : ∀ u, q (-u) = -q u := by
    intro u
    dsimp [q]
    rw [mul_neg, hχ.even]
    ring
  have href : (∫ u, q u * f (-u)) = -(∫ u, q u * f u) := by
    have hr := integral_neg_eq_self (fun u => q u * f (-u)) volume
    simp only [heven, neg_neg, neg_mul, integral_neg] at hr
    exact hr.symm
  have heq : (∫ u, (1 - χ (μ * u)) * pvQuotient f u) =
      2⁻¹ * ((∫ u, q u * f u) - ∫ u, q u * f (-u)) := by
    rw [← integral_sub hi hni, ← integral_const_mul]
    refine integral_congr_ae ?_
    filter_upwards [compl_mem_ae_iff.mpr (measure_singleton (0 : ℝ))] with u hu
    have hne : u ≠ 0 := by simpa using hu
    rw [pvQuotient_of_ne f hne]
    dsimp [q]
    ring
  rw [heq, href]
  dsimp [pvTruncation, q]
  ring

/-- The cutoff disappears at every nonzero point as its scale tends to infinity. -/
theorem eventually_comp_eq_zero (hχ : IsPVCutoff χ) {u : ℝ} (hu : u ≠ 0) :
    (fun μ : ℝ => χ (μ * u)) =ᶠ[atTop] fun _ => 0 := by
  have he := hasCompactSupport_iff_eventuallyEq.mp hχ.compact
  rw [Filter.coclosedCompact_eq_cocompact] at he
  exact (Filter.tendsto_cocompact_mul_right₀ hu).comp
    (tendsto_id.mono_right atTop_le_cocompact) |>.eventually he

/-- Existence of the cutoff limit, proved before defining a principal value. -/
theorem tendsto_pvTruncation (hχ : IsPVCutoff χ) {f : ℝ → ℝ}
    (hc : Continuous f) (hd : DifferentiableAt ℝ f 0) (hf : HasCompactSupport f) :
    Tendsto (fun μ => pvTruncation χ μ f) atTop (𝓝 (∫ u, pvQuotient f u)) := by
  obtain ⟨C, hC⟩ := hχ.cont.bounded_above_of_compact_support hχ.compact
  have hi := integrable_pvQuotient hc hd hf
  have ht : Tendsto (fun μ : ℝ => ∫ u, (1 - χ (μ * u)) * pvQuotient f u)
      atTop (𝓝 (∫ u, pvQuotient f u)) := by
    refine tendsto_integral_filter_of_dominated_convergence
      (fun u => (1 + C) * ‖pvQuotient f u‖) ?_ ?_ (hi.norm.const_mul _) ?_
    · exact Eventually.of_forall fun μ =>
        ((continuous_const.sub (hχ.cont.comp (continuous_const.mul continuous_id))).mul
          (continuous_pvQuotient hc hd)).aestronglyMeasurable
    · refine Eventually.of_forall fun μ => Eventually.of_forall fun u => ?_
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_right
        ((norm_sub_le 1 (χ (μ * u))).trans (by simpa using add_le_add_left (hC (μ * u)) 1))
        (norm_nonneg _)
    · filter_upwards [compl_mem_ae_iff.mpr (measure_singleton (0 : ℝ))] with u hu
      have hne : u ≠ 0 := by simpa using hu
      have he := hχ.eventually_comp_eq_zero hne
      apply tendsto_const_nhds.congr'
      filter_upwards [he] with μ hμ
      simp only [hμ, sub_zero, one_mul]
  exact ht.congr (fun μ => (hχ.pvTruncation_eq μ hc hf).symm)

end IsPVCutoff

/-- Existence statement used in the definition below. -/
theorem exists_pvTruncation_limit {χ : ℝ → ℝ} (hχ : IsPVCutoff χ) {f : ℝ → ℝ}
    (hc : Continuous f) (hd : DifferentiableAt ℝ f 0) (hf : HasCompactSupport f) :
    ∃ v : ℝ, Tendsto (fun μ => pvTruncation χ μ f) atTop (𝓝 v) :=
  ⟨∫ u, pvQuotient f u, hχ.tendsto_pvTruncation hc hd hf⟩

/-- The one-dimensional principal value, selected only after proving the cutoff
limit exists. Its characterization and independence of cutoff are proved below. -/
@[expose] noncomputable def principalValueOneDim (χ : ℝ → ℝ) (hχ : IsPVCutoff χ)
    (f : ℝ → ℝ) (hc : Continuous f) (hd : DifferentiableAt ℝ f 0)
    (hf : HasCompactSupport f) : ℝ :=
  (exists_pvTruncation_limit hχ hc hd hf).choose

theorem tendsto_principalValueOneDim {χ : ℝ → ℝ} (hχ : IsPVCutoff χ)
    {f : ℝ → ℝ} (hc : Continuous f) (hd : DifferentiableAt ℝ f 0)
    (hf : HasCompactSupport f) :
    Tendsto (fun μ => pvTruncation χ μ f) atTop
      (𝓝 (principalValueOneDim χ hχ f hc hd hf)) :=
  (exists_pvTruncation_limit hχ hc hd hf).choose_spec

/-- Full characterization by an absolutely integrable symmetric quotient. -/
theorem principalValueOneDim_eq_integral {χ : ℝ → ℝ} (hχ : IsPVCutoff χ)
    {f : ℝ → ℝ} (hc : Continuous f) (hd : DifferentiableAt ℝ f 0)
    (hf : HasCompactSupport f) :
    principalValueOneDim χ hχ f hc hd hf = ∫ u, pvQuotient f u :=
  tendsto_nhds_unique (tendsto_principalValueOneDim hχ hc hd hf)
    (hχ.tendsto_pvTruncation hc hd hf)

/-- Independence of the particular even cutoff. -/
theorem principalValueOneDim_cutoff_independent {χ ψ : ℝ → ℝ}
    (hχ : IsPVCutoff χ) (hψ : IsPVCutoff ψ) {f : ℝ → ℝ}
    (hc : Continuous f) (hd : DifferentiableAt ℝ f 0) (hf : HasCompactSupport f) :
    principalValueOneDim χ hχ f hc hd hf = principalValueOneDim ψ hψ f hc hd hf := by
  rw [principalValueOneDim_eq_integral, principalValueOneDim_eq_integral]

/-- An absolute bound for the principal value, without Fourier-frequency uniformity. -/
theorem abs_principalValueOneDim_le {χ : ℝ → ℝ} (hχ : IsPVCutoff χ)
    {f : ℝ → ℝ} (hc : Continuous f) (hd : DifferentiableAt ℝ f 0)
    (hf : HasCompactSupport f) :
    |principalValueOneDim χ hχ f hc hd hf| ≤ ∫ u, |pvQuotient f u| := by
  rw [principalValueOneDim_eq_integral, ← Real.norm_eq_abs]
  exact norm_integral_le_integral_norm _

end WaveTurbulence.Resonant
