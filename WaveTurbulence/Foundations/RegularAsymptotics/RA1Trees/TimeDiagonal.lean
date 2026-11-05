/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.RegularAsymptotics.RA1Trees.TimeHomogeneity
public import WaveTurbulence.Foundations.RegularAsymptotics.RA1Trees.TimePointwiseBound

/-! # Source diagonal couple factors are monomials on positive time -/

public section
noncomputable section
namespace WaveTurbulence.RegAsymp

/-- The scalar in every diagonal source time monomial has a geometric bound. -/
theorem norm_couple_JB_diagonal_coefficient_le (Q : RegCpl) :
    ‖Q.JB 0 1 1‖ ≤ (2 : ℝ) ^ coupleTimeDegree Q :=
  norm_couple_JB_le Q 1 1 ⟨by norm_num, le_rfl⟩ ⟨by norm_num, le_rfl⟩

/-- Homogeneity identifies the actual diagonal source time factor without using J4 as a premise. -/
theorem couple_JB_diagonal_eq (Q : RegCpl) {t : ℝ} (ht : 0 < t) :
    Q.JB 0 t t = t ^ coupleTimeDegree Q * Q.JB 0 1 1 := by
  simpa only [mul_one] using couple_JB_scale t ht Q 1 1

end WaveTurbulence.RegAsymp
