/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.SumintPar.SourceLinearMass
public import WaveTurbulence.Foundations.SumintPar.ExponentMargins

/-!
# One uniform bound for the better distinguished linear branch

The constant precedes delta. The exponent relative to the ordinary
linear scale is gammaBase in both ranges: use the trivial estimate
below one half and F23 above one half. The stationary first-pair term
still uses the separate trivial bound.
-/

@[expose] public section
set_option autoImplicit false

open Set ENNReal

namespace WaveTurbulence.SumintPar

/-- A fixed dimension constant dominating both actual source linear branches. -/
@[expose] noncomputable def sourceLinearBranchConstant (d : ℕ) : ℝ :=
  max (3*(12:ℝ)^d) (scaledLinearConstant d)

/-- The better source linear branch has loss gammaBase relative to d-gamma. -/
theorem linearFactorMass_le_best_branch {d : ℕ} (D : SumintDatum d) {L γ η δ : ℝ}
    (hL : 1 ≤ L) (hδ : 0 < δ) (hδsmall : δ ≤ 1/16) (hγη : γ+η ≤ 1)
    (p : D.S.VIdx → Fin d → ℝ) (ν : D.S.VIdx → Mom d) (r : Mom d)
    (hr : 1/L ≤ ‖r‖) (hrupper : ‖r‖ ≤ L^(-γ+η)) (t c : ℝ) {h : ℝ}
    (hh : h ∈ Icc (0:ℝ) 1) (i : Fin D.S.I) :
    linearFactorMass D L γ δ p ν r t c h i ≤
      ENNReal.ofReal (sourceLinearBranchConstant d*δ⁻¹*L^((d:ℝ)-γ+gammaBase γ)) := by
  have hLp : 0 < L := zero_lt_one.trans_le hL
  by_cases hg : γ ≤ 1/2
  · have he : (d:ℝ)-γ+gammaBase γ = d := by
      rw [gammaBase,min_eq_left (by linarith only [hg])]
      ring
    rw [he]
    apply (linearFactorMass_le_trivial D hL hδ γ p ν r t c hh i).trans
    apply ENNReal.ofReal_le_ofReal
    apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg hLp.le _)
    have hδinv : 1 ≤ δ⁻¹ := by
      rw [← one_div,le_div_iff₀ hδ]
      linarith only [hδsmall]
    have hK : 3*(12:ℝ)^d ≤ sourceLinearBranchConstant d := le_max_left _ _
    have hK0 : 0 ≤ sourceLinearBranchConstant d := (by positivity : 0 ≤ 3*(12:ℝ)^d).trans hK
    exact hK.trans ((le_mul_of_one_le_right hK0 hδinv))
  · have he : (d:ℝ)-γ+gammaBase γ = (d:ℝ)+1-2*γ := by
      rw [gammaBase,min_eq_right (by linarith only [hg])]
      ring
    rw [he]
    apply (linearFactorMass_le_f23 D hL hδ hδsmall hγη p ν r hr hrupper t c hh i).trans
    apply ENNReal.ofReal_le_ofReal
    have hK : scaledLinearConstant d ≤ sourceLinearBranchConstant d := le_max_right _ _
    calc
      _ = scaledLinearConstant d*δ⁻¹*L^((d:ℝ)+1-2*γ) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hK (inv_nonneg.mpr hδ.le))
        (Real.rpow_nonneg hLp.le _)

end WaveTurbulence.SumintPar
