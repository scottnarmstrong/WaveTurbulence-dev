/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.WeylSums.CubicStarMinIntegral
public import WaveTurbulence.Foundations.WeylSums.NonzeroWeylLowerMoments
public import WaveTurbulence.Foundations.WeylSums.NonzeroWeylHigherMoments
public import WaveTurbulence.Foundations.WeylSums.ZeroWeylLowerMoment

/-! # The shared-vertex Weyl minimum in dimension three -/

public section
open MeasureTheory
namespace WaveTurbulence.WeylSums

/-- The two terms correspond to nonzero/nonzero and nonzero/zero arc pairs. -/
theorem exists_cubicStar_weyl_integral_bound_three (ε : ℝ) (hε : 0 < ε) (hε1 : ε < 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ M A T : ℝ, 2 ≤ M → 1/M < A → 0 < T → T ≤ 1 →
      IntegrableOn (fun xy : ℝ × ℝ => min (normalizedWeyl M xy.1^3) (normalizedWeyl M xy.2^3))
        (timeSquareWindow A T) ∧
      (∫ xy : ℝ × ℝ in timeSquareWindow A T,
        min (normalizedWeyl M xy.1^3) (normalizedWeyl M xy.2^3)) ≤
        C*(M^(2*ε)*T^2+M^(-1+4*ε)*T) := by
  obtain ⟨C₁,hC₁,hb₁⟩ := exists_nonzeroWeylPart_lower_moment_bound ε ((3 : ℝ)/2) hε
    (by norm_num) (by linarith)
  obtain ⟨C₂,hC₂,hb₂⟩ := exists_nonzeroWeylPart_higher_moment_bound ε (2+ε) hε le_rfl
  obtain ⟨C₃,hC₃,hb₃⟩ := exists_zeroWeylPart_lower_moment_bound ε hε hε1
  let C := 2*C₁^2+2*C₂*C₃
  refine ⟨C,by dsimp [C]; positivity,?_⟩
  intro M A T hM hA hT hT1
  have hMp : 0 < M := by linarith
  obtain ⟨hi₁,h₁⟩ := hb₁ M T hM hT hT1
  obtain ⟨hi₂,h₂⟩ := hb₂ M T hM hT hT1
  obtain ⟨hi₃,h₃⟩ := hb₃ M T hM hT hT1
  have hia : IntegrableOn (fun t => zeroWeylPart M t^((3 : ℝ)-(2+ε))) {t : ℝ | |t| ≤ T} := by
    simpa only [show (3 : ℝ)-(2+ε) = 1-ε by ring] using hi₃
  obtain ⟨hi,hb⟩ := integral_normalizedWeyl_min_le_moments 3 (by omega) M A T (2+ε) hMp hA
    (by linarith) (by norm_num only [Nat.cast_ofNat]; linarith) hi₁ hi₂ hia
  refine ⟨hi,?_⟩
  norm_num only [Nat.cast_ofNat] at hb
  rw [show (3 : ℝ)-(2+ε) = 1-ε by ring] at hb
  have h₁sq : (∫ t in {t : ℝ | |t| ≤ T}, nonzeroWeylPart M t^((3 : ℝ)/2))^2 ≤ (C₁*M^ε*T)^2 :=
    (sq_le_sq₀ (integral_nonneg (fun t => Real.rpow_nonneg (nonzeroWeylPart_nonneg hMp t) _)) (by positivity)).mpr h₁
  have hcross : (∫ t in {t : ℝ | |t| ≤ T}, nonzeroWeylPart M t^(2+ε))*
      (∫ t in {t : ℝ | |t| ≤ T}, zeroWeylPart M t^(1-ε)) ≤
      (C₂*M^ε*T)*(C₃*M^(-1+3*ε)) := by
    have h₂' : (∫ t in {t : ℝ | |t| ≤ T}, nonzeroWeylPart M t^(2+ε)) ≤ C₂*M^ε*T := by
      simpa only [show (2+ε)-2 = ε by ring] using h₂
    exact mul_le_mul h₂' h₃ (integral_nonneg (fun t => Real.rpow_nonneg (zeroWeylPart_nonneg hMp t) _)) (by positivity)
  have halg : 2*(C₁*M^ε*T)^2+2*(C₂*M^ε*T)*(C₃*M^(-1+3*ε)) =
      (2*C₁^2)*(M^(2*ε)*T^2)+(2*C₂*C₃)*(M^(-1+4*ε)*T) := by
    have hs : (M^ε)^2 = M^(2*ε) := by rw [← Real.rpow_two,← Real.rpow_mul hMp.le]; congr 1; ring
    have ht : M^ε*M^(-1+3*ε) = M^(-1+4*ε) := by rw [← Real.rpow_add hMp]; congr 1; ring
    calc
      _ = (2*C₁^2)*((M^ε)^2*T^2)+(2*C₂*C₃)*((M^ε*M^(-1+3*ε))*T) := by ring
      _ = _ := by rw [hs,ht]
  calc
    _ ≤ 2*(C₁*M^ε*T)^2+2*(C₂*M^ε*T)*(C₃*M^(-1+3*ε)) := by linarith only [hb,h₁sq,hcross]
    _ = _ := halg
    _ ≤ C*(M^(2*ε)*T^2+M^(-1+4*ε)*T) := by
      dsimp [C]
      have hnn : 0 ≤ M^(2*ε)*T^2 := by positivity
      have hnz : 0 ≤ M^(-1+4*ε)*T := by positivity
      nlinarith only [hnn,hnz,hC₁,hC₂,hC₃,sq_nonneg C₁,
        mul_nonneg (mul_nonneg hC₂.le hC₃.le) hnn,mul_nonneg (sq_nonneg C₁) hnz]

end WaveTurbulence.WeylSums
