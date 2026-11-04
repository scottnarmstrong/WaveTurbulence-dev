/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.RegAsymp.ContinuousIntegralSize
public import WaveTurbulence.Foundations.RegAsymp.Normalization

/-! # Natural normalized size of the actual continuous NT term -/

public section
noncomputable section
namespace WaveTurbulence.RegAsymp
open MeasureTheory ApproxNT Finset
open scoped ENNReal ContDiff

/-- The source prefactor cancels all powers of L without a temporal moment. -/
theorem exists_normalized_continuous_size_bound (d : ℕ) (hd : 3 ≤ d) :
    ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, 0 < n →
      ∀ (lt : Fin n → Fin n → Prop) [IsStrictOrder (Fin n) lt] (xs ys : Fin n → Shift n),
      (∀ j, (xs j).Below lt j) → (∀ j, (ys j).Below lt j) →
      ∀ (a b : Fin n → Mom d) (lam : Fin n → ℝ), (∀ j, 1 ≤ lam j) →
      ∀ W : (Fin n → Mom d) → (Fin n → Mom d) → ℂ, Continuous (Function.uncurry W) →
      (∀ x y, W x y ≠ 0 → (x,y) ∈ supportSet xs ys a b lam) →
      ∀ H : ℝ, 0 ≤ H →
      (∫⁻ τ : (Fin n → Mom d) × (Fin n → Mom d), ‖fourierW W τ.1 τ.2‖ₑ *
        ENNReal.ofReal (1+2*Real.pi*freqNorm τ.1 τ.2)) ≤ ENNReal.ofReal H →
      ∀ (J : Finset (Fin n)) (Ψ : EuclideanSpace ℝ {j // j ∉ J} → ℂ) (D : ℕ → ℝ),
      ContDiff ℝ ∞ Ψ → WordDerivL1 Ψ D → (∀ k, 0 ≤ D k) →
      ∀ D0 : ℝ, (∫ Ω, ‖Ψ Ω‖) ≤ D0 → ∀ L δ γ : ℝ, 0 < L → 0 < δ → 1 < L^(2*γ)*δ →
      ‖(((δ/(2*L^((d:ℝ)-γ)))^(2*n):ℝ):ℂ) * (L:ℂ)^(2*d*n) * approxInt (L^(2*γ)*δ) W (resProfile J Ψ)‖ ≤
        (∏ j, lam j)^(2*d)*(C*δ/4)^n*D0*H := by
  obtain ⟨C,hC,hS⟩ := exists_continuous_integral_size_bound d hd
  refine ⟨C,hC,?_⟩
  intro n hn lt _ xs ys hxs hys a b lam hlam W hWc hWs H hH hW J Ψ D hΨ hD hD0 D0 hΨ0 L δ γ hL hδ hμ
  have hInt := hS n hn lt xs ys hxs hys a b lam hlam W hWc hWs H hH hW J Ψ D hΨ hD hD0 D0 hΨ0
    (L^(2*γ)*δ) hμ
  have hD00 : 0 ≤ D0 := (integral_nonneg (fun _ => norm_nonneg _)).trans hΨ0
  let q : ℝ := (δ/(2*L^((d:ℝ)-γ)))^(2*n)
  have hq : 0 ≤ q := by dsimp only [q]; positivity
  change ‖(q:ℂ)*(L:ℂ)^(2*d*n)*approxInt (L^(2*γ)*δ) W (resProfile J Ψ)‖ ≤ _
  rw [norm_mul,norm_mul,norm_pow,Complex.norm_real,Complex.norm_real,
    Real.norm_eq_abs,Real.norm_eq_abs,abs_of_nonneg hq,abs_of_pos hL]
  calc
    _ ≤ (q*L^(2*d*n))*((∏ j, lam j)^(2*d)*(C/(L^(2*γ)*δ))^n*D0*H) :=
      mul_le_mul_of_nonneg_left hInt (by positivity)
    _ = _ := by
      have he : L^(2*d)*(C/(L^(2*γ)*δ)) = C*(L^(2*(d:ℝ)-2*γ)*δ⁻¹) := by
        calc _ = C*(L^(2*d)/(L^(2*γ)*δ)) := by ring
             _ = _ := by rw [Lpow_div_mu hL]
      have hs := normalized_scale (γ := γ) n d hL hδ.ne' C
      change q*(C*L^(2*(d:ℝ)-2*γ)*δ⁻¹)^n = (C*δ/4)^n at hs
      calc
        _ = (∏ j, lam j)^(2*d)*(q*(L^(2*d)*(C/(L^(2*γ)*δ)))^n)*D0*H := by
          rw [mul_pow,← pow_mul]; ring
        _ = _ := by rw [he,show C*(L^(2*(d:ℝ)-2*γ)*δ⁻¹)=C*L^(2*(d:ℝ)-2*γ)*δ⁻¹ by ring,hs]

end WaveTurbulence.RegAsymp
