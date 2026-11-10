/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Incoh.CoupleExtension
public import WaveTurbulence.Foundations.Incoh.RootCutoff
public import WaveTurbulence.Foundations.Incoh.RootCumulativeLocal
public import WaveTurbulence.Foundations.Incoh.TwoTimeBoxIntegral

/-! # Exact couple source agreement on external boxes above the root layers -/

public section
noncomputable section
open MeasureTheory Set

namespace WaveTurbulence.Incoh

/-- A cutoff which is one throughout the local integration rectangle leaves the primitive exact. -/
theorem cutoffDoubleIntegral_eq_on_rectangle {χ : ℝ → ℝ} (F : (Fin 2 → ℝ) → ℂ)
    (t : Fin 2 → ℝ) (ht : 0 ≤ t)
    (hχ : ∀ j : Fin 2, ∀ s ∈ Icc (0 : ℝ) (t j), χ s = 1) :
    Fourier.cutoffDoubleIntegral χ F t = ∫ u in (0 : ℝ)..t 0, ∫ v in (0 : ℝ)..t 1, F ![u, v] := by
  have ht₀ : (0 : ℝ) ≤ t 0 := ht 0
  have ht₁ : (0 : ℝ) ≤ t 1 := ht 1
  rw [Fourier.cutoffDoubleIntegral, hχ 0 _ ⟨ht 0, le_rfl⟩, hχ 1 _ ⟨ht 1, le_rfl⟩]
  simp only [Complex.ofReal_one, one_mul]
  apply intervalIntegral.integral_congr
  intro u hu
  have hu' : u ∈ Icc (0 : ℝ) (t 0) := by simpa only [uIcc_of_le ht₀] using hu
  apply intervalIntegral.integral_congr
  intro v hv
  have hv' : v ∈ Icc (0 : ℝ) (t 1) := by simpa only [uIcc_of_le ht₁] using hv
  dsimp only
  simp only [hχ 0 u hu', hχ 1 v hv', Complex.ofReal_one, one_mul]

/-- The scalar extension agrees with the literal source for every external time above the
actual root layers. Its cutoff may span the entire finite layer range. -/
theorem RootCoordinates.coupleExtension_agrees_above {d n : ℕ} (R : RootCoordinates n)
    {L : ℝ} (hL : 0 < L) (γ δ : ℝ) (Q : Fin n → LayerLink d)
    {I : Set (Fin n → Fin 2 → ℝ)} (hI : MeasurableSet I)
    (hbox : I ⊆ univ.pi (fun i => linkBox (Q i))) {χ : ℝ → ℝ}
    (t : Fin 2 → ℝ) (ht : R.baseRootTimes Q ≤ t)
    (hχ : ∀ j : Fin 2, ∀ s ∈ Icc (0 : ℝ) ((t - R.baseRootTimes Q) j), χ s = 1) :
    R.coupleExtension χ L γ δ Q I t = R.cumulativeKernel L γ δ Q I t := by
  let τ := t - R.baseRootTimes Q
  have hτ : 0 ≤ τ := sub_nonneg.mpr ht
  have hF := R.integrable_localLinkDensity hL γ δ Q hI hbox
  have hrect := integral_twoTimeBox_eq_doubleInterval hF 0 (τ 0) 0 (τ 1) (hτ 0) (hτ 1)
  have hvec : ![τ 0, τ 1] = τ := by ext i; fin_cases i <;> rfl
  have hzero : ![(0 : ℝ), 0] = (0 : Fin 2 → ℝ) := by ext i; fin_cases i <;> rfl
  rw [hvec, hzero] at hrect
  change Fourier.cutoffDoubleIntegral χ (R.localLinkDensity L γ δ Q I) τ = _
  rw [cutoffDoubleIntegral_eq_on_rectangle _ τ hτ hχ, ← hrect]
  exact (R.cumulativeKernel_eq_localBoxIntegral hL γ δ Q hI hbox t).symm

end WaveTurbulence.Incoh
