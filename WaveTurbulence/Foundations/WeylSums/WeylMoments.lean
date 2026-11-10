/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.WeylSums.WeylGlobalMoment
public import WaveTurbulence.Foundations.WeylSums.WeylLocalMoment

/-!
# The global and localized Weyl moment estimates

TARGET L1567–L1590, with `p=3d/2>4`. The supremum is inside each
integral. Constants depend only on `p` and the fixed cutoff. The localized
bound is stated for any window `T≥0`, which includes `T=A L^(2γ−2)`.
-/

public section
open MeasureTheory
namespace WaveTurbulence.WeylSums

theorem moment_scale_identity {L : ℝ} (hL : 0 < L) (C p M Z T : ℝ) (hC : 0 ≤ C) :
    (C * L)^p * (4 * M / L^2 * T * Z) =
      (4 * C^p * M * Z) * L^(p-2) * T := by
  rw [Real.mul_rpow hC hL.le, Real.rpow_sub hL, Real.rpow_two]
  field_simp

/-- The paper's global and localized moment estimates, uniformly in real scale.
Taking `p=3*d/2` and `T=A*L^(2*γ-2)` gives the exact exponents in TARGET. -/
theorem weyl_moment_bounds (p : ℝ) (hp : 4 < p) :
    ∃ C : ℝ, 0 < C ∧
      (∀ L : ℝ, 1 ≤ L →
        (∫ t : ℝ in 0..1, weylSupremum L t ^ p) ≤ C * L^(p-2)) ∧
      (∀ L T : ℝ, 2 ≤ L → 0 ≤ T →
        (∫ t : ℝ in {t : ℝ | 1/L ≤ |t| ∧ |t| ≤ T}, weylSupremum L t ^ p) ≤
          C * L^(p-2) * T) := by
  obtain ⟨C₁, hC₁, hb₁⟩ := exists_weylSupremum_integral_bound
  obtain ⟨C₂, hC₂, hb₂⟩ := exists_weylSupremum_local_integral_bound
  let M := arcProfileMass (p/2)
  let Z := ∑' q : ℕ, (q : ℝ)^(1-p/2)
  let A := 4 * C₁^p * M * Z
  let B := 4 * C₂^p * M * Z
  have hM : 0 ≤ M := arcProfileMass_nonneg _
  have hZ : 0 ≤ Z := tsum_nonneg (fun q => Real.rpow_nonneg (Nat.cast_nonneg q) _)
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have hB : 0 ≤ B := by dsimp [B]; positivity
  refine ⟨A+B+1, by linarith, ?_, ?_⟩
  · intro L hL
    have hLpos : 0 < L := by linarith
    have hh := (hb₁ L p hL hp).2
    have heq : (C₁ * L)^p * (4 * M / L^2 * Z) = A * L^(p-2) := by
      simpa only [mul_one] using moment_scale_identity hLpos C₁ p M Z 1 hC₁.le
    change _ ≤ (C₁ * L)^p * (4 * M / L^2 * Z) at hh
    rw [heq] at hh
    exact hh.trans (mul_le_mul_of_nonneg_right (by linarith : A ≤ A+B+1)
      (Real.rpow_nonneg hLpos.le _))
  · intro L T hL hT
    have hLpos : 0 < L := by linarith
    have hh := (hb₂ L p T hL hp hT).2
    change _ ≤ (C₂ * L)^p * (4 * M / L^2 * T * Z) at hh
    rw [moment_scale_identity hLpos C₂ p M Z T hC₂.le] at hh
    exact hh.trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (by linarith : B ≤ A+B+1) (Real.rpow_nonneg hLpos.le _)) hT)

end WaveTurbulence.WeylSums
