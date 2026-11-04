/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Fourier.Chi0
public import WaveTurbulence.Foundations.WeylSums.SmoothCutoff

/-!
# A positive cutoff majorizing an interval

The fixed cutoff `χ₀(x/2)` equals one on `[-1,1]`, vanishes off `(-2,2)`,
and is nonnegative. Positive Fourier-moment monotonicity can therefore
majorize the sharp interval sums of DH21 Lemma A.5 by this smooth cutoff.
-/

public section

open scoped ContDiff

namespace WaveTurbulence.WeylSums

/-- Fixed positive majorant for the interval `[0,1]`. -/
@[expose] noncomputable def huaCutoff (x : ℝ) : ℝ := Fourier.chi0 (x / 2)

theorem huaCutoff_nonneg (x : ℝ) : 0 ≤ huaCutoff x := Fourier.chi0_nonneg _

theorem huaCutoff_eq_one {x : ℝ} (hx : |x| ≤ 1) : huaCutoff x = 1 := by
  apply Fourier.chi0_eq_one
  rw [abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
  linarith only [hx]

theorem huaCutoff_eq_zero {x : ℝ} (hx : 2 ≤ |x|) : huaCutoff x = 0 := by
  apply Fourier.chi0_eq_zero
  rw [abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
  linarith only [hx]

theorem huaCutoff_hasCompactSupport : HasCompactSupport huaCutoff := by
  apply HasCompactSupport.intro (isCompact_Icc (a := (-2 : ℝ)) (b := 2))
  intro x hx
  apply huaCutoff_eq_zero
  by_contra hh
  have hh' := abs_lt.mp (lt_of_not_ge hh)
  exact hx ⟨hh'.1.le, hh'.2.le⟩

theorem huaCutoff_contDiff : ContDiff ℝ ∞ huaCutoff :=
  (Fourier.chi0_contDiff (n := ⊤)).comp (contDiff_id.div_const 2)

theorem huaCutoff_complex_hasCompactSupport :
    HasCompactSupport (fun x : ℝ => (huaCutoff x : ℂ)) :=
  huaCutoff_hasCompactSupport.comp_left (show ((0 : ℝ) : ℂ) = 0 from rfl)

theorem huaCutoff_complex_contDiff : ContDiff ℝ ∞ (fun x : ℝ => (huaCutoff x : ℂ)) :=
  Complex.ofRealCLM.contDiff.comp huaCutoff_contDiff

end WaveTurbulence.WeylSums
