/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.RegAsymp.NormalizedApproximation

/-! # Linear dependence on the actual amplitude Fourier budget

The nth root is chosen only as an input parameter to NT. The resulting
remainder is linear in the actual Fourier mass, so integrating one
frequency moment does not require the nth frequency moment.
-/

public section
noncomputable section
namespace WaveTurbulence.RegAsymp
open MeasureTheory Finset ApproxNT
open scoped ContDiff ENNReal
variable {d : ℕ}

/-- Positive-order NT approximation with its true linear amplitude budget. -/
theorem normalized_approximation_linear_budget (hd : 3 ≤ d) {γ : ℝ} (hγ : γ ∈ Set.Ioo (0 : ℝ) 1) {η : ℝ}
    (hη0 : 0 < η) (hη : η ≤ 1 / 20) (hηγ : η ≤ ((d : ℝ) - 1) * (1 - γ)) (hηγ' : η ≤ γ) {C₀ : ℝ}
    (hC₀ : 1 ≤ C₀) :
    ∃ C₁ : ℝ, 0 < C₁ ∧ ∀ A : ℝ, ∃ L₀ : ℝ, ∀ L : ℝ, L₀ ≤ L → ∀ δ : ℝ, L ^ (-(η / 2)) ≤ δ →
      δ ≤ 1 → ∀ n : ℕ, 0 < n → (n : ℝ) ≤ Real.log L ^ A → ∀ H : ℝ, 0 ≤ H →
      ∀ (lt : Fin n → Fin n → Prop) [IsStrictOrder (Fin n) lt] (xs ys : Fin n → Shift n),
      (∀ j, (xs j).Below lt j) → (∀ j, (ys j).Below lt j) →
      ∀ (a b : Fin n → Mom d) (lam : Fin n → ℝ), (∀ j, 1 ≤ lam j) →
      ∀ W : (Fin n → Mom d) → (Fin n → Mom d) → ℂ, Continuous (Function.uncurry W) →
      (∀ x y, W x y ≠ 0 → (x, y) ∈ supportSet xs ys a b lam) →
      ∫⁻ τ : (Fin n → Mom d) × (Fin n → Mom d), ‖fourierW W τ.1 τ.2‖ₑ *
          ENNReal.ofReal (1 + 2 * Real.pi * freqNorm τ.1 τ.2) ≤ ENNReal.ofReal H →
      ∀ (J : Finset (Fin n)) (Ψ₁ : EuclideanSpace ℝ {j // j ∉ J} → ℂ), ContDiff ℝ ∞ Ψ₁ →
      WordDerivL1 Ψ₁ (fun k => C₀ ^ n * ((4 * k).factorial : ℝ)) →
      ∫⁻ Ω, ENNReal.ofReal (wmax (1 - η / 2) (fun i => Ω i)) * ‖Ψ₁ Ω‖ₑ ≤
        ENNReal.ofReal (C₀ ^ n) →
      ‖(((δ / (2 * L ^ ((d : ℝ) - γ))) ^ (2 * n) : ℝ) : ℂ) *
        (approxSum L (L ^ (2 * γ) * δ) W (resProfile J Ψ₁) - approxApp L δ γ J Ψ₁ W)‖ ≤
        (∏ j, lam j) ^ (2 * d) * ((C₁ * δ / 4) ^ n * H) * L ^ (-gamma1 d γ + η) := by
  obtain ⟨C₁,hC₁,hNT⟩ := normalized_approximation hd hγ hη0 hη hηγ hηγ' hC₀
  refine ⟨C₁,hC₁,fun A => ?_⟩
  obtain ⟨L₀,hL₀⟩ := hNT A
  refine ⟨L₀,fun L hL δ hδ hδ1 n hnp hn H hH lt _ xs ys hxs hys a b lam hlam W hWc hWs hW
    J Ψ₁ hΨ hD hM => ?_⟩
  let Cp : ℝ := H ^ ((n:ℝ)⁻¹)
  have hCp : 0 ≤ Cp := Real.rpow_nonneg hH _
  have hpow : Cp^n=H := Real.rpow_inv_natCast_pow hH (Nat.ne_of_gt hnp)
  have hW' : (∫⁻ τ : (Fin n → Mom d) × (Fin n → Mom d), ‖fourierW W τ.1 τ.2‖ₑ *
      ENNReal.ofReal (1+2*Real.pi*freqNorm τ.1 τ.2)) ≤ ENNReal.ofReal (Cp^n) := by
    rwa [hpow]
  have hh := hL₀ L hL δ hδ hδ1 n hn Cp hCp lt xs ys hxs hys a b lam hlam W hWc hWs hW'
    J Ψ₁ hΨ hD hM
  have hscale : (C₁*Cp*δ/4)^n = (C₁*δ/4)^n*H := by
    rw [show C₁*Cp*δ/4 = (C₁*δ/4)*Cp by ring,mul_pow,hpow]
  rwa [hscale] at hh

end WaveTurbulence.RegAsymp
