/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.CountLemmas.FullMinimum
public import WaveTurbulence.Foundations.WeylSums.NonzeroWeylLowerMoments
public import WaveTurbulence.Foundations.WeylSums.NonzeroWeylHigherMoments
public import WaveTurbulence.Foundations.WeylSums.ZeroWeylLowerMoment

/-! # Full-square shared-vertex Weyl moments -/

public section
open MeasureTheory
open WaveTurbulence.WeylSums
namespace WaveTurbulence.CountLemmas

/-- The three terms retain nonzero/nonzero, mixed, and zero/zero arc pairs. -/
theorem exists_full_star_moment_bound (ε : ℝ) (hε : 0 < ε) (hε1 : ε < 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ M T : ℝ, 2 ≤ M → 0 < T → T ≤ 1 →
      IntegrableOn (fun xy : ℝ × ℝ => min (normalizedWeyl M xy.1^3) (normalizedWeyl M xy.2^3))
        ({t : ℝ | |t| ≤ T} ×ˢ {t : ℝ | |t| ≤ T}) ∧
      (∫ xy : ℝ × ℝ in ({t : ℝ | |t| ≤ T} ×ˢ {t : ℝ | |t| ≤ T}),
        min (normalizedWeyl M xy.1^3) (normalizedWeyl M xy.2^3)) ≤
        C*(M^(2*ε)*T^2+M^(-1+4*ε)*T+M^(-1 : ℝ)) := by
  obtain ⟨C₁,hC₁,hb₁⟩ := exists_nonzeroWeylPart_lower_moment_bound ε ((3 : ℝ)/2) hε
    (by norm_num) (by linarith)
  obtain ⟨C₂,hC₂,hb₂⟩ := exists_nonzeroWeylPart_higher_moment_bound ε (2+ε) hε le_rfl
  obtain ⟨C₃,hC₃,hb₃⟩ := exists_zeroWeylPart_lower_moment_bound ε hε hε1
  obtain ⟨C₄,hC₄,hb₄⟩ := exists_zeroWeylPart_moment_bound ((3 : ℝ)/2) (by norm_num)
  let C := 2*C₁^2+2*C₂*C₃+C₄^2
  refine ⟨C,by dsimp [C]; positivity,?_⟩
  intro M T hM hT hT1
  have hMp : 0 < M := by linarith
  obtain ⟨hi₁,h₁⟩ := hb₁ M T hM hT hT1
  obtain ⟨hi₂,h₂⟩ := hb₂ M T hM hT hT1
  obtain ⟨hi₃,h₃⟩ := hb₃ M T hM hT hT1
  have hia : IntegrableOn (fun t => zeroWeylPart M t^((3 : ℝ)-(2+ε))) {t : ℝ | |t| ≤ T} := by
    simpa only [show (3 : ℝ)-(2+ε) = 1-ε by ring] using hi₃
  obtain ⟨hi₄,h₄⟩ := hb₄ M (by linarith only [hM])
  have hi₄W := hi₄.integrableOn (s := {t : ℝ | |t| ≤ T})
  have h₄W : (∫ t in {t : ℝ | |t| ≤ T}, zeroWeylPart M t^((3 : ℝ)/2)) ≤
      C₄*M^(-1/2 : ℝ) := by
    apply (setIntegral_le_integral hi₄ (Filter.Eventually.of_forall (fun t =>
      Real.rpow_nonneg (zeroWeylPart_nonneg hMp t) _))).trans
    simpa only [show (3 : ℝ)/2-2 = -1/2 by norm_num] using h₄
  obtain ⟨hi,hb⟩ := integral_full_minimum_le M T (2+ε) hMp
    (by linarith only [hε]) (by linarith only [hε1]) hi₁ hi₂ hia hi₄W
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
  have h₄sq : (∫ t in {t : ℝ | |t| ≤ T}, zeroWeylPart M t^((3 : ℝ)/2))^2 ≤
      C₄^2*M^(-1 : ℝ) := by
    have hh := (sq_le_sq₀ (integral_nonneg (fun t =>
      Real.rpow_nonneg (zeroWeylPart_nonneg hMp t) _)) (by positivity)).mpr h₄W
    have he : (M^(-1/2 : ℝ))^2 = M^(-1 : ℝ) := by
      rw [← Real.rpow_two,← Real.rpow_mul hMp.le]
      norm_num
    simpa only [mul_pow,he] using hh
  have hNN : 0 ≤ (C₁*M^ε*T)^2 := sq_nonneg _
  have hbound : (∫ xy : ℝ × ℝ in ({t : ℝ | |t| ≤ T} ×ˢ {t : ℝ | |t| ≤ T}),
      min (normalizedWeyl M xy.1^3) (normalizedWeyl M xy.2^3)) ≤
      (2*C₁^2)*(M^(2*ε)*T^2)+(2*C₂*C₃)*(M^(-1+4*ε)*T)+C₄^2*M^(-1 : ℝ) := by
    rw [← halg]
    linarith only [hb,h₁sq,hcross,h₄sq,hNN]
  apply hbound.trans
  dsimp only [C]
  have hnn : 0 ≤ M^(2*ε)*T^2 := by positivity
  have hnz : 0 ≤ M^(-1+4*ε)*T := by positivity
  have hzz : 0 ≤ M^(-1 : ℝ) := by positivity
  have hconst : 0 ≤ 2*C₁^2 ∧ 0 ≤ 2*C₂*C₃ ∧ 0 ≤ C₄^2 := by constructor; positivity; constructor <;> positivity
  nlinarith only [mul_nonneg hconst.1 hnz,mul_nonneg hconst.1 hzz,
    mul_nonneg hconst.2.1 hnn,mul_nonneg hconst.2.1 hzz,
    mul_nonneg hconst.2.2 hnn,mul_nonneg hconst.2.2 hnz]

end WaveTurbulence.CountLemmas
