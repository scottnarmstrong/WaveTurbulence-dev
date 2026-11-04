/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Incoh.CoupleExtensionAgreement

/-!
# A wider canonical cutoff for degenerate one-clock couples

TARGET L1049 (P-1). The auxiliary clock is integrated over its entire
source layer interval. Its shifted external clock lies in `[1,2]`, where
the wider cutoff is exactly one.
-/

public section
noncomputable section
open MeasureTheory Set
open scoped ContDiff

namespace WaveTurbulence.Incoh

/-- A fixed smooth cutoff equal to one on `[-2,2]` and supported in `[-4,4]`. -/
@[expose] def wideRootCutoff (t : ℝ) : ℝ := Fourier.chi0 (t / 4)

@[fun_prop] theorem contDiff_wideRootCutoff : ContDiff ℝ ∞ wideRootCutoff :=
  Fourier.chi0_contDiff.comp (by fun_prop)

theorem hasCompactSupport_wideRootCutoff : HasCompactSupport wideRootCutoff := by
  apply HasCompactSupport.intro (isCompact_Icc (a := (-4 : ℝ)) (b := 4))
  intro t ht
  apply Fourier.chi0_eq_zero
  by_contra h
  have hh : |t / 4| < 1 := lt_of_not_ge h
  rw [abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 4)] at hh
  exact ht (abs_le.mp (by linarith : |t| ≤ 4))

theorem wideRootCutoff_eq_one_on_doubleUnit {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 2) :
    wideRootCutoff t = 1 := by
  apply Fourier.chi0_eq_one
  rw [abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 4), abs_of_nonneg ht.1]
  linarith only [ht.2]

/-- The wider cutoff leaves the cumulative double integral unchanged on `[0,2]²`. -/
theorem cutoffDoubleIntegral_wideRootCutoff_eq (F : (Fin 2 → ℝ) → ℂ) (t : Fin 2 → ℝ)
    (ht : t ∈ Icc (0 : Fin 2 → ℝ) 2) :
    Fourier.cutoffDoubleIntegral wideRootCutoff F t =
      ∫ u in (0 : ℝ)..t 0, ∫ v in (0 : ℝ)..t 1, F ![u, v] := by
  have ht₀ : t 0 ∈ Icc (0 : ℝ) 2 := ⟨ht.1 0, ht.2 0⟩
  have ht₁ : t 1 ∈ Icc (0 : ℝ) 2 := ⟨ht.1 1, ht.2 1⟩
  rw [Fourier.cutoffDoubleIntegral, wideRootCutoff_eq_one_on_doubleUnit ht₀,
    wideRootCutoff_eq_one_on_doubleUnit ht₁]
  simp only [Complex.ofReal_one, one_mul]
  apply intervalIntegral.integral_congr
  intro u hu
  have hu' : u ∈ Icc (0 : ℝ) (t 0) := by simpa only [uIcc_of_le ht₀.1] using hu
  apply intervalIntegral.integral_congr
  intro v hv
  have hv' : v ∈ Icc (0 : ℝ) (t 1) := by simpa only [uIcc_of_le ht₁.1] using hv
  dsimp only
  simp only [wideRootCutoff_eq_one_on_doubleUnit ⟨hu'.1, hu'.2.trans ht₀.2⟩,
    wideRootCutoff_eq_one_on_doubleUnit ⟨hv'.1, hv'.2.trans ht₁.2⟩, Complex.ofReal_one, one_mul]

/-- The actual density extension agrees with the cumulative source on the enlarged clock box. -/
theorem RootCoordinates.coupleExtension_wide_agrees {d n : ℕ} (R : RootCoordinates n)
    {L : ℝ} (hL : 0 < L) (γ δ : ℝ) (Q : Fin n → LayerLink d)
    {I : Set (Fin n → Fin 2 → ℝ)} (hI : MeasurableSet I)
    (hbox : I ⊆ univ.pi (fun i => linkBox (Q i))) {t : Fin 2 → ℝ}
    (ht : t - R.baseRootTimes Q ∈ Icc (0 : Fin 2 → ℝ) 2) :
    R.coupleExtension wideRootCutoff L γ δ Q I t = R.cumulativeKernel L γ δ Q I t := by
  let τ := t - R.baseRootTimes Q
  have hF := R.integrable_localLinkDensity hL γ δ Q hI hbox
  have hrect := integral_twoTimeBox_eq_doubleInterval hF 0 (τ 0) 0 (τ 1) (ht.1 0) (ht.1 1)
  have hvec : ![τ 0, τ 1] = τ := by ext i; fin_cases i <;> rfl
  have hzero : ![(0 : ℝ), 0] = (0 : Fin 2 → ℝ) := by ext i; fin_cases i <;> rfl
  rw [hvec, hzero] at hrect
  change Fourier.cutoffDoubleIntegral wideRootCutoff (R.localLinkDensity L γ δ Q I) τ = _
  rw [cutoffDoubleIntegral_wideRootCutoff_eq _ τ ht, ← hrect]
  exact (R.cumulativeKernel_eq_localBoxIntegral hL γ δ Q hI hbox t).symm

end WaveTurbulence.Incoh
