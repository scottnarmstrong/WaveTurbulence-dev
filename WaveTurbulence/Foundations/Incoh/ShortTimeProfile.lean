/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Incoh.ShortTime
public import WaveTurbulence.Foundations.Incoh.ShortTimeMoments
public import WaveTurbulence.Foundations.Incoh.DifferenceBox

/-!
# Nonnegative frequency profile of an actual short-time link

TARGET (incohproof14)–(incohproof15). Restrict the literal lattice factor
in frequency; the constants are the finite zeroth and first bracket moments.
-/

public section
noncomputable section
open MeasureTheory Set
open scoped ENNReal

namespace WaveTurbulence.Incoh

/-- The actual short-frequency part of a Wick link, as a nonnegative profile. -/
@[expose] def shortLinkProfile {d : ℕ} (L : ℝ) (A : LinkParameters d) (s : ℝ) : ℝ≥0∞ :=
  (Icc (-L) L).indicator (fun s => ‖linkLatticeSum L s A‖ₑ) s

theorem measurable_shortLinkProfile {d : ℕ} {L : ℝ} (hL : 0 < L) (A : LinkParameters d) :
    Measurable (shortLinkProfile L A) :=
  (continuous_linkLatticeSum hL A).measurable.enorm.indicator measurableSet_Icc

/-- Uniform pointwise domination of the short-frequency profile by the integrable bracket kernel. -/
theorem exists_shortLinkProfile_bound (d : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ L : ℝ, 1 ≤ L → ∀ A : LinkParameters d, ∀ s : ℝ,
      shortLinkProfile L A s ≤
        ENNReal.ofReal (C * L ^ (2 * d)) * ENNReal.ofReal (Fourier.inverseBracketPower d s) := by
  obtain ⟨C, hC, hb⟩ := exists_shortTime_link_bound d
  refine ⟨C, hC, ?_⟩
  intro L hL A s
  by_cases hs : s ∈ Icc (-L) L
  · rw [shortLinkProfile, Set.indicator_of_mem (s := Icc (-L) L) hs]
    have hbound := hb L hL s (abs_le.mpr hs) A
    have heq : C * L ^ (2 * d) / Real.sqrt (1 + s ^ 2) ^ d =
        (C * L ^ (2 * d)) * Fourier.inverseBracketPower d s := by
      rw [Fourier.inverseBracketPower, Real.rpow_neg (Real.sqrt_nonneg _), Real.rpow_natCast,
        div_eq_mul_inv]
    rw [heq] at hbound
    rw [← ofReal_norm, ← ENNReal.ofReal_mul (by positivity : 0 ≤ C * L ^ (2 * d))]
    exact ENNReal.ofReal_le_ofReal hbound
  · rw [shortLinkProfile, Set.indicator_of_notMem (s := Icc (-L) L) hs]
    exact bot_le

/-- Both frequency moments have a common dimensional constant, before all link parameters. -/
theorem exists_shortLinkProfile_moments_bound (d : ℕ) (hd : 3 ≤ d) :
    ∃ C : ℝ, 0 < C ∧ ∀ L : ℝ, 1 ≤ L → ∀ A : LinkParameters d,
      (∫⁻ s, shortLinkProfile L A s) ≤ ENNReal.ofReal (C * L ^ (2 * d)) ∧
      (∫⁻ s, shortLinkProfile L A s * ENNReal.ofReal |s|) ≤ ENNReal.ofReal (C * L ^ (2 * d)) := by
  obtain ⟨C, hC, hb⟩ := exists_shortLinkProfile_bound d
  have hd₀ : 1 < (d : ℝ) := by exact_mod_cast (show 1 < d by omega)
  have hd₁ : 2 < (d : ℝ) := by exact_mod_cast (show 2 < d by omega)
  have hi₀ := Fourier.integrable_inverseBracketPower hd₀
  have hi₁ := integrable_firstMoment_inverseBracketPower hd₁
  let m₀ : ℝ := ∫ s : ℝ, Fourier.inverseBracketPower d s
  let m₁ : ℝ := ∫ s : ℝ, |s| * Fourier.inverseBracketPower d s
  let M : ℝ := 1 + |m₀| + |m₁|
  have hM : 0 < M := by dsimp [M]; positivity
  have hm₀ : m₀ ≤ M := by dsimp [M]; linarith [le_abs_self m₀, abs_nonneg m₁]
  have hm₁ : m₁ ≤ M := by dsimp [M]; linarith [le_abs_self m₁, abs_nonneg m₀]
  have he₀ : (∫⁻ s : ℝ, ENNReal.ofReal (Fourier.inverseBracketPower d s)) = ENNReal.ofReal m₀ :=
    (ofReal_integral_eq_lintegral_ofReal hi₀
      (Filter.Eventually.of_forall fun s => Fourier.inverseBracketPower_nonneg d s)).symm
  have he₁ : (∫⁻ s : ℝ, ENNReal.ofReal (|s| * Fourier.inverseBracketPower d s)) = ENNReal.ofReal m₁ :=
    (ofReal_integral_eq_lintegral_ofReal hi₁
      (Filter.Eventually.of_forall fun s => mul_nonneg (abs_nonneg _) (Fourier.inverseBracketPower_nonneg d s))).symm
  have hmeas₀ : AEMeasurable (fun s : ℝ => ENNReal.ofReal (Fourier.inverseBracketPower d s)) :=
    ENNReal.measurable_ofReal.comp_aemeasurable hi₀.aemeasurable
  have hmeas₁ : AEMeasurable (fun s : ℝ => ENNReal.ofReal (|s| * Fourier.inverseBracketPower d s)) :=
    ENNReal.measurable_ofReal.comp_aemeasurable hi₁.aemeasurable
  refine ⟨C * M, mul_pos hC hM, ?_⟩
  intro L hL A
  have hCL : 0 ≤ C * L ^ (2 * d) := by positivity
  have hfinish (m : ℝ) (hm : m ≤ M) :
      ENNReal.ofReal (C * L ^ (2 * d)) * ENNReal.ofReal m ≤ ENNReal.ofReal (C * M * L ^ (2 * d)) := by
    rw [← ENNReal.ofReal_mul hCL]
    apply ENNReal.ofReal_le_ofReal
    calc
      _ ≤ (C * L ^ (2 * d)) * M := mul_le_mul_of_nonneg_left hm hCL
      _ = _ := by ring
  constructor
  · calc
      _ ≤ ∫⁻ s, ENNReal.ofReal (C * L ^ (2 * d)) * ENNReal.ofReal (Fourier.inverseBracketPower d s) :=
        lintegral_mono (hb L hL A)
      _ = ENNReal.ofReal (C * L ^ (2 * d)) * ENNReal.ofReal m₀ := by
        rw [lintegral_const_mul'' _ hmeas₀, he₀]
      _ ≤ _ := hfinish m₀ hm₀
  · calc
      _ ≤ ∫⁻ s, ENNReal.ofReal (C * L ^ (2 * d)) *
          ENNReal.ofReal (|s| * Fourier.inverseBracketPower d s) := by
        apply lintegral_mono
        intro s
        dsimp only
        rw [ENNReal.ofReal_mul (abs_nonneg s)]
        simpa only [mul_assoc, mul_comm, mul_left_comm] using
          mul_le_mul' (hb L hL A s) (le_refl (ENNReal.ofReal |s|))
      _ = ENNReal.ofReal (C * L ^ (2 * d)) * ENNReal.ofReal m₁ := by
        rw [lintegral_const_mul'' _ hmeas₁, he₁]
      _ ≤ _ := hfinish m₁ hm₁

end WaveTurbulence.Incoh
