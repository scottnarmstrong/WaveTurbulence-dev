/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.WeylSums.ZeroWeylMoments
public import WaveTurbulence.Foundations.WeylSums.WindowMomentInterpolation

/-! # The subcritical zero-arc moment in dimension three -/

public section
open MeasureTheory Set
namespace WaveTurbulence.WeylSums

/-- A slightly supercritical zero-arc moment controls the required
subcritical moment. This avoids a separate singular-power integration. -/
theorem exists_zeroWeylPart_lower_moment_bound (ε : ℝ) (hε : 0 < ε) (hε1 : ε < 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ M T : ℝ, 2 ≤ M → 0 < T → T ≤ 1 →
      IntegrableOn (fun t => zeroWeylPart M t^(1-ε)) {t : ℝ | |t| ≤ T} ∧
      (∫ t in {t : ℝ | |t| ≤ T}, zeroWeylPart M t^(1-ε)) ≤ C*M^(-1+3*ε) := by
  let ℓ := 1+ε
  let k := 1-ε
  let θ := k/ℓ
  have hℓ : 1 < ℓ := by dsimp [ℓ]; linarith
  have hℓp : 0 < ℓ := by linarith
  have hk : 0 < k := by dsimp [k]; linarith
  have hkl : k < ℓ := by dsimp [k,ℓ]; linarith
  have hθ : θ ∈ Ioo (0 : ℝ) 1 := ⟨div_pos hk hℓp,(div_lt_one hℓp).mpr hkl⟩
  obtain ⟨C,hC,hbound⟩ := exists_zeroWeylPart_moment_bound ℓ hℓ
  let K := C^θ*(2 : ℝ)^(1-θ)
  refine ⟨K,by dsimp [K]; positivity,?_⟩
  intro M T hM hT hT1
  have hMp : 0 < M := by linarith
  obtain ⟨hi,hb⟩ := hbound M (by linarith)
  have hmoment : (∫ t in {t : ℝ | |t| ≤ T}, zeroWeylPart M t^ℓ) ≤ C*M^(ℓ-2) :=
    (setIntegral_le_integral hi (Filter.Eventually.of_forall (fun t => Real.rpow_nonneg (zeroWeylPart_nonneg hMp t) _))).trans hb
  obtain ⟨hilow,hlow⟩ := window_moment_interpolation (zeroWeylPart M) (measurable_zeroWeylPart hMp)
    (zeroWeylPart_nonneg hMp) ℓ k T hk hkl hT.le hi.restrict
  refine ⟨hilow,?_⟩
  have hmpow := Real.rpow_le_rpow (integral_nonneg (fun t => Real.rpow_nonneg (zeroWeylPart_nonneg hMp t) _))
    hmoment hθ.1.le
  have hTpow : (2*T)^(1-θ) ≤ (2 : ℝ)^(1-θ) := Real.rpow_le_rpow (by positivity)
    (by linarith only [hT1]) (by linarith only [hθ.2])
  have hexp : (ℓ-2)*θ ≤ -1+3*ε := by
    dsimp [ℓ,θ,k]
    rw [← mul_div_assoc]
    apply (div_le_iff₀ (by linarith : 0 < 1+ε)).mpr
    nlinarith only [sq_nonneg ε]
  have halg : (C*M^(ℓ-2))^θ*(2 : ℝ)^(1-θ) = K*M^((ℓ-2)*θ) := by
    rw [Real.mul_rpow hC.le (by positivity),← Real.rpow_mul hMp.le]
    dsimp [K]
    ring
  calc
    _ ≤ (∫ t in {t : ℝ | |t| ≤ T}, zeroWeylPart M t^ℓ)^θ*(2*T)^(1-θ) := hlow
    _ ≤ (C*M^(ℓ-2))^θ*(2 : ℝ)^(1-θ) := mul_le_mul hmpow hTpow (by positivity) (by positivity)
    _ = K*M^((ℓ-2)*θ) := halg
    _ ≤ K*M^(-1+3*ε) := mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_exponent_le (by linarith) hexp) (by dsimp [K]; positivity)

end WaveTurbulence.WeylSums
