/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.WeylSums.RefinedMoments
public import WaveTurbulence.Foundations.WeylSums.WeylMoments

/-! # The refined Hua window exponent, in normalized form -/

public section
open MeasureTheory
namespace WaveTurbulence.WeylSums

/-- Inversion of the large-denominator threshold. -/
theorem denominator_threshold_power {T : ℝ} (hT : 0 < T) (σ ε : ℝ) :
    (1/(2*T))^(2-σ+ε) = (2 : ℝ)^(σ-2-ε) * T^(σ-2-ε) := by
  rw [one_div, Real.inv_rpow (by positivity), show (2-σ+ε : ℝ) = -(σ-2-ε) by ring,
    Real.rpow_neg (by positivity : 0 ≤ 2*T), inv_inv, Real.mul_rpow (by norm_num) hT.le]

/-- The small-loss sharp window power `T^(p/2-1-ε)`. -/
theorem window_threshold_power {T : ℝ} (hT : 0 < T) (p ε : ℝ) :
    T*(1/(2*T))^(2-p/2+ε) = (2 : ℝ)^(p/2-2-ε) * T^(p/2-1-ε) := by
  rw [denominator_threshold_power hT]
  calc
    _ = (2 : ℝ)^(p/2-2-ε) * (T^((1 : ℝ)) * T^(p/2-2-ε)) := by rw [Real.rpow_one]; ring
    _ = (2 : ℝ)^(p/2-2-ε) * T^(1+(p/2-2-ε)) := by rw [Real.rpow_add hT]
    _ = _ := by congr 2; ring

/-- Refined Hua estimate used in DH23 Lemma 6.6(2). It bounds the full
supremum, at real scale, with any loss `ε>0` below `p/2-2`. -/
theorem exists_weylSupremum_refined_moment (p ε : ℝ) (hp : 4 < p)
    (hε : 0 < ε) (hεp : ε < p/2-2) :
    ∃ C : ℝ, 0 < C ∧ ∀ L T : ℝ, 2 ≤ L → 0 < T →
      IntegrableOn (fun t : ℝ => weylSupremum L t ^ p)
        {t : ℝ | 1/L ≤ |t| ∧ |t| ≤ T} ∧
      (∫ t : ℝ in {t : ℝ | 1/L ≤ |t| ∧ |t| ≤ T}, weylSupremum L t ^ p) ≤
        C * L^(p-2) * T^(p/2-1-ε) := by
  obtain ⟨C, hC, hb⟩ := exists_weylSupremum_refined_integral_bound
  let M := arcProfileMass (p/2)
  let Z := ∑' q : ℕ, (q : ℝ)^(-1-ε)
  let A := (4*C^p*M*Z) * (2 : ℝ)^(p/2-2-ε)
  have hM : 0 ≤ M := arcProfileMass_nonneg _
  have hZ : 0 ≤ Z := tsum_nonneg (fun q => Real.rpow_nonneg (Nat.cast_nonneg q) _)
  have hA : 0 ≤ A := by dsimp [A]; positivity
  refine ⟨A+1, by positivity, ?_⟩
  intro L T hL hT
  have hLp : 0 < L := by linarith only [hL]
  obtain ⟨hi, hh⟩ := hb L p ε T hL hp hε hεp hT
  refine ⟨hi, hh.trans ?_⟩
  have heq : (C*L)^p * (4*M/L^2*T*(1/(2*T))^(2-p/2+ε)*Z) =
      A*L^(p-2)*T^(p/2-1-ε) := by
    calc
      _ = (C*L)^p * (4*M/L^2*(T*(1/(2*T))^(2-p/2+ε))*Z) := by ring
      _ = (4*C^p*M*Z)*L^(p-2)*(T*(1/(2*T))^(2-p/2+ε)) :=
        moment_scale_identity hLp C p M Z _ hC.le
      _ = _ := by rw [window_threshold_power hT]; dsimp [A]; ring
  change (C*L)^p * (4*M/L^2*T*(1/(2*T))^(2-p/2+ε)*Z) ≤ _
  rw [heq]
  exact mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right (by linarith : A ≤ A+1) (Real.rpow_nonneg hLp.le _))
    (Real.rpow_nonneg hT.le _)

end WaveTurbulence.WeylSums
