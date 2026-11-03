/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.WeylSums.NonzeroWeylMoments
public import WaveTurbulence.Foundations.WeylSums.WindowMomentInterpolation

/-! # Lower nonzero-arc moments needed in dimensions three and four -/

public section
open MeasureTheory Set
namespace WaveTurbulence.WeylSums

/-- The sharp window factor survives interpolation below order `2+ε`.
The arbitrarily small scale loss `M^ε` is uniform on `0<T≤1`. -/
theorem exists_nonzeroWeylPart_lower_moment_bound (ε b : ℝ) (hε : 0 < ε)
    (hb : 0 < b) (hba : b < 2+ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ M T : ℝ, 2 ≤ M → 0 < T → T ≤ 1 →
      IntegrableOn (fun t => nonzeroWeylPart M t^b) {t : ℝ | |t| ≤ T} ∧
      (∫ t in {t : ℝ | |t| ≤ T}, nonzeroWeylPart M t^b) ≤ C*M^ε*T := by
  let a := 2+ε
  let θ := b/a
  have ha : 0 < a := by dsimp [a]; linarith
  have hθ : θ ∈ Ioo (0 : ℝ) 1 := ⟨div_pos hb ha,(div_lt_one ha).mpr hba⟩
  obtain ⟨C,hC,hbound⟩ := exists_nonzeroWeylPart_moment_bound a (ε/2) (by dsimp [a]; linarith)
    (by positivity) (by dsimp [a]; linarith)
  let K := C^θ*(2 : ℝ)^(1-θ)
  have hK : 0 < K := by dsimp [K]; positivity
  refine ⟨K,hK,?_⟩
  intro M T hM hT hT1
  have hMp : 0 < M := by linarith
  obtain ⟨hi,hbnd⟩ := hbound M T hM hT
  obtain ⟨hilo,hlo⟩ := window_moment_interpolation (nonzeroWeylPart M)
    (measurable_nonzeroWeylPart hMp) (nonzeroWeylPart_nonneg hMp) a b T hb hba hT.le hi
  refine ⟨hilo,?_⟩
  have hbnd' : (∫ t in {t : ℝ | |t| ≤ T}, nonzeroWeylPart M t^a) ≤ C*M^ε*T^(1+ε/2) := by
    have h₁ : a-2 = ε := by dsimp [a]; ring
    have h₂ : a-1-ε/2 = 1+ε/2 := by dsimp [a]; ring
    simpa only [h₁,h₂] using hbnd
  have hsmall := Real.rpow_le_rpow (integral_nonneg (fun t => Real.rpow_nonneg (nonzeroWeylPart_nonneg hMp t) _))
    hbnd' hθ.1.le
  have hscale : (C*M^ε*T^(1+ε/2))^θ*(2*T)^(1-θ) =
      K*M^(ε*θ)*T^(1+ε*θ/2) := by
    rw [Real.mul_rpow (by positivity : (0 : ℝ) ≤ C*M^ε) (by positivity),
      Real.mul_rpow hC.le (by positivity),Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 2) hT.le,
      ← Real.rpow_mul hMp.le,← Real.rpow_mul hT.le]
    calc
      _ = K*M^(ε*θ)*(T^((1+ε/2)*θ)*T^(1-θ)) := by dsimp [K]; ring
      _ = _ := by rw [← Real.rpow_add hT]; congr 2; ring
  have hMsmall : M^(ε*θ) ≤ M^ε := Real.rpow_le_rpow_of_exponent_le (by linarith)
    (by nlinarith only [hε,hθ.2])
  have hTsmall : T^(1+ε*θ/2) ≤ T := Real.rpow_le_self_of_le_one hT.le hT1 (by nlinarith only [hε,hθ.1])
  calc
    _ ≤ (∫ t in {t : ℝ | |t| ≤ T}, nonzeroWeylPart M t^a)^θ*(2*T)^(1-θ) := hlo
    _ ≤ (C*M^ε*T^(1+ε/2))^θ*(2*T)^(1-θ) := mul_le_mul_of_nonneg_right hsmall (by positivity)
    _ = K*M^(ε*θ)*T^(1+ε*θ/2) := hscale
    _ ≤ K*M^ε*T := mul_le_mul (mul_le_mul_of_nonneg_left hMsmall hK.le) hTsmall
      (by positivity) (by positivity)

end WaveTurbulence.WeylSums
