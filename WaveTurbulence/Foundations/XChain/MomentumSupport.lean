/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.XChain.SignedTranslation
/-! Exact integer momentum support of conditional solution cumulants, TARGET S2. -/
@[expose] public section
namespace WaveTurbulence.Induct
open MeasureTheory Set Finset

noncomputable def momentumCharges {d : ℕ} {ι : Type*} (L : ℝ)
    (ζ : ι → ℤˣ) (n : ι → (Fin d → ℤ)) (j : ι) (l : Fin d) : ℝ :=
  (-2 * Real.pi / L) * (((ζ j : ℤ) : ℝ) * (n j l : ℝ))

theorem momentumCharges_sum_ne_zero {d : ℕ} {ι : Type*} [DecidableEq ι] {L : ℝ} (hL : L ≠ 0)
    (ζ : ι → ℤˣ) (n : ι → (Fin d → ℤ)) (s : Finset ι)
    (hn : (∑ j ∈ s, (ζ j : ℤ) • n j) ≠ 0) : (∑ j ∈ s, momentumCharges L ζ n j) ≠ 0 := by
  intro h
  apply hn
  funext l
  have hl := congrFun h l
  simp only [Finset.sum_apply, Pi.zero_apply] at hl
  have hc : (-2 * Real.pi / L) ≠ 0 := div_ne_zero (mul_ne_zero (by norm_num) Real.pi_ne_zero) hL
  have hz : (∑ j ∈ s, ((ζ j : ℤ) : ℝ) * (n j l : ℝ)) = 0 := by
    have he : (-2 * Real.pi / L) * (∑ j ∈ s, ((ζ j : ℤ) : ℝ) * (n j l : ℝ)) = 0 := by
      simpa only [mul_sum, momentumCharges] using hl
    exact (mul_eq_zero.mp he).resolve_left hc
  have hi : (∑ j ∈ s, (ζ j : ℤ) * n j l) = 0 := by exact_mod_cast hz
  simpa only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] using hi

theorem signed_translation_angle_eq {d : ℕ} {ι : Type*} (L : ℝ)
    (ζ : ι → ℤˣ) (n : ι → (Fin d → ℤ)) (x : Fin d → ℝ) (j : ι) :
    ((ζ j : ℤ) : ℝ) * (-(2 * Real.pi * inner ℝ (latticePoint L (n j)) (WithLp.toLp 2 x))) =
      ∑ l, momentumCharges L ζ n j l * x l := by
  simp only [PiLp.inner_apply, Real.inner_apply, latticePoint]
  simp only [mul_sum, ← sum_neg_distrib, momentumCharges]
  apply Finset.sum_congr rfl
  intro l _
  ring

/-- Nonzero integer total momentum forces the literal unnormalized conditional cumulant to vanish. -/
theorem cumulant_signed_solution_eq_zero_of_momentum {d : ℕ} {Ω ι : Type*}
    [MeasurableSpace Ω] [DecidableEq ι] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {L γ δ T : ℝ} (hL : 0 < L) (φ : Mom d → ℝ)
    {g : (Fin d → ℤ) → Ω → ℂ} (hG : IsGaussianData μ g)
    (F : Set Ω) (hFm : MeasurableSet F) (hF : IsSymmetricEvent L φ g F)
    (a : Ω → ℝ → (Fin d → ℤ) → ℂ)
    (ha : ∀ ω ∈ F, IsASolution L γ δ T (initialCoeff L φ g ω) (a ω))
    (hrapid : ∀ ω ∈ F, IsRapidDecay (initialCoeff L φ g ω))
    (hmeas : ∀ t ∈ Icc 0 T, ∀ n, Measurable fun ω => a ω t n)
    (t : ι → Icc (0 : ℝ) T) (n : ι → (Fin d → ℤ)) (ζ : ι → ℤˣ) (s : Finset ι)
    (hq : (∑ j ∈ s, (ζ j : ℤ) • n j) ≠ 0) :
    cumulant (μ.restrict F) (fun j ω => zpowSign (ζ j) (a ω (t j) (n j))) s = 0 := by
  apply cumulant_eq_zero_of_translation_invariant (q := momentumCharges L ζ n)
  · intro j
    have hj := hmeas _ (t j).2 (n j)
    unfold zpowSign
    split_ifs
    · exact hj
    · exact Complex.continuous_conj.measurable.comp hj
  · intro x
    have h := signed_solution_joint_map_translation hL φ hG F hFm hF a ha hrapid hmeas t n ζ
      (WithLp.toLp 2 x)
    simpa only [signed_translation_angle_eq] using h
  · exact momentumCharges_sum_ne_zero hL.ne' ζ n s hq

end WaveTurbulence.Induct
