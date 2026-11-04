/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.RegAsymp.SingularIntegralSize
public import WaveTurbulence.Foundations.RegAsymp.Normalization

/-! # Natural normalized size of the actual leading approximation -/

public section
noncomputable section
namespace WaveTurbulence.RegAsymp
open MeasureTheory ApproxNT Finset
open scoped ENNReal

/-- The source prefactor cancels every power of L in the leading term;
only the symbol L1 mass and the linear amplitude mass remain. -/
theorem exists_normalized_app_size_bound (d : ℕ) (hd : 3 ≤ d) :
    ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, 0 < n →
      ∀ (lt : Fin n → Fin n → Prop) [IsStrictOrder (Fin n) lt] (xs ys : Fin n → Shift n),
      (∀ j, (xs j).Below lt j) → (∀ j, (ys j).Below lt j) →
      ∀ (a b : Fin n → Mom d) (lam : Fin n → ℝ), (∀ j, 1 ≤ lam j) →
      ∀ W : (Fin n → Mom d) → (Fin n → Mom d) → ℂ, Continuous (Function.uncurry W) →
      (∀ x y, W x y ≠ 0 → (x,y) ∈ supportSet xs ys a b lam) →
      ∀ H : ℝ, 0 ≤ H →
      (∫⁻ τ : (Fin n → Mom d) × (Fin n → Mom d), ‖fourierW W τ.1 τ.2‖ₑ *
        ENNReal.ofReal (1+2*Real.pi*freqNorm τ.1 τ.2)) ≤ ENNReal.ofReal H →
      ∀ (J : Finset (Fin n)) (Ψ : EuclideanSpace ℝ {j // j ∉ J} → ℂ),
      ∀ D0 : ℝ, (∫ Ω, ‖Ψ Ω‖) ≤ D0 → ∀ L δ γ : ℝ, 0 < L → 0 < δ →
      ‖(((δ/(2*L^((d:ℝ)-γ)))^(2*n):ℝ):ℂ) * approxApp L δ γ J Ψ W‖ ≤
        (∏ j, lam j)^(2*d)*(C*δ/4)^n*D0*H := by
  obtain ⟨C,hC,hS⟩ := exists_singular_integral_size_bound d hd
  refine ⟨C,hC,?_⟩
  intro n hn lt _ xs ys hxs hys a b lam hlam W hWc hWs H hH hW J Ψ D0 hΨ L δ γ hL hδ
  have hsing := hS n hn lt xs ys hxs hys a b lam hlam W hWc hWs H hH hW J
  have hD0 : 0 ≤ D0 := (integral_nonneg (fun _ => norm_nonneg _)).trans hΨ
  have hnorm : ‖∫ Ω, Ψ Ω‖ ≤ D0 := (norm_integral_le_integral_norm _).trans hΨ
  let q : ℝ := (δ/(2*L^((d:ℝ)-γ)))^(2*n)
  let X : ℝ := L^(2*(d:ℝ)-2*γ)*δ⁻¹
  have hq : 0 ≤ q := by dsimp only [q]; positivity
  have hX : 0 ≤ X := by dsimp only [X]; positivity
  change ‖(q:ℂ)*approxApp L δ γ J Ψ W‖ ≤ _
  rw [approxApp,norm_mul,norm_mul,norm_mul,norm_pow,Complex.norm_real,Complex.norm_real,
    Real.norm_eq_abs,Real.norm_eq_abs,abs_of_nonneg hq,abs_of_nonneg hX]
  change q*(X^n*‖∫ Ω, Ψ Ω‖*‖singInt J W‖) ≤ _
  calc
    _ ≤ q*(X^n*D0*((∏ j, lam j)^(2*d)*C^n*H)) :=
      mul_le_mul_of_nonneg_left (mul_le_mul (mul_le_mul_of_nonneg_left hnorm (by positivity)) hsing
        (norm_nonneg _) (by positivity)) hq
    _ = _ := by
      have hs0 := normalized_scale (γ := γ) n d hL hδ.ne' C
      have hs : q*(C*X)^n = (C*δ/4)^n := by simpa only [q,X,mul_assoc] using hs0
      rw [mul_pow] at hs
      calc
        _ = (∏ j, lam j)^(2*d)*(q*(C^n*X^n))*D0*H := by ring
        _ = _ := by rw [hs]

end WaveTurbulence.RegAsymp
