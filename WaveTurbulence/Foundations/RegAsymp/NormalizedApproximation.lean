/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.ApproxNT.Prop64
public import WaveTurbulence.Foundations.RegAsymp.Normalization

/-! # Normalized DH23 Prop6.4 in the large-order regular-couple range

DH23 (KQZdef) to (KQZapprox). This is the localized, fixed-frequency
analytic step. Its hypotheses are exactly the Prop6.4 amplitude/profile
premises; the actual regular-couple localization is a separate proof.
-/

public section
noncomputable section
open MeasureTheory Finset
open scoped ContDiff ENNReal
namespace WaveTurbulence.RegAsymp
open ApproxNT
variable {d : ℕ}

/-- The Prop6.4 remainder after multiplication by the actual order2n
couple prefactor. Valid for every fixed logarithmic order exponent A. -/
theorem normalized_approximation (hd : 3 ≤ d) {γ : ℝ} (hγ : γ ∈ Set.Ioo (0 : ℝ) 1) {η : ℝ}
    (hη0 : 0 < η) (hη : η ≤ 1 / 20) (hηγ : η ≤ ((d : ℝ) - 1) * (1 - γ)) (hηγ' : η ≤ γ) {C₀ : ℝ}
    (hC₀ : 1 ≤ C₀) :
    ∃ C₁ : ℝ, 0 < C₁ ∧ ∀ A : ℝ, ∃ L₀ : ℝ, ∀ L : ℝ, L₀ ≤ L → ∀ δ : ℝ, L ^ (-(η / 2)) ≤ δ →
      δ ≤ 1 → ∀ n : ℕ, (n : ℝ) ≤ Real.log L ^ A → ∀ Cplus : ℝ, 0 ≤ Cplus →
      ∀ (lt : Fin n → Fin n → Prop) [IsStrictOrder (Fin n) lt] (xs ys : Fin n → Shift n),
      (∀ j, (xs j).Below lt j) → (∀ j, (ys j).Below lt j) →
      ∀ (a b : Fin n → Mom d) (lam : Fin n → ℝ), (∀ j, 1 ≤ lam j) →
      ∀ W : (Fin n → Mom d) → (Fin n → Mom d) → ℂ, Continuous (Function.uncurry W) →
      (∀ x y, W x y ≠ 0 → (x, y) ∈ supportSet xs ys a b lam) →
      ∫⁻ τ : (Fin n → Mom d) × (Fin n → Mom d), ‖fourierW W τ.1 τ.2‖ₑ *
          ENNReal.ofReal (1 + 2 * Real.pi * freqNorm τ.1 τ.2) ≤ ENNReal.ofReal (Cplus ^ n) →
      ∀ (J : Finset (Fin n)) (Ψ₁ : EuclideanSpace ℝ {j // j ∉ J} → ℂ), ContDiff ℝ ∞ Ψ₁ →
      WordDerivL1 Ψ₁ (fun k => C₀ ^ n * ((4 * k).factorial : ℝ)) →
      ∫⁻ Ω, ENNReal.ofReal (wmax (1 - η / 2) (fun i => Ω i)) * ‖Ψ₁ Ω‖ₑ ≤
        ENNReal.ofReal (C₀ ^ n) →
      ‖(((δ / (2 * L ^ ((d : ℝ) - γ))) ^ (2 * n) : ℝ) : ℂ) *
        (approxSum L (L ^ (2 * γ) * δ) W (resProfile J Ψ₁) - approxApp L δ γ J Ψ₁ W)‖ ≤
        (∏ j, lam j) ^ (2 * d) * (C₁ * Cplus * δ / 4) ^ n * L ^ (-gamma1 d γ + η) := by
  obtain ⟨C₁,hC₁,hNT⟩ := dh23_prop_6_4 hd hγ hη0 hη hηγ hηγ' hC₀
  refine ⟨C₁,hC₁,fun A => ?_⟩
  obtain ⟨L₀,hL₀⟩ := hNT A
  refine ⟨max L₀ 2,fun L hL δ hδ hδ1 n hn Cplus hCp lt _ xs ys hxs hys a b lam hlam W hWc hWs hW J Ψ₁ hΨ hD hH => ?_⟩
  have hL0 : 0 < L := lt_of_lt_of_le (by norm_num : (0 : ℝ) < 2) ((le_max_right _ _).trans hL)
  have hδ0 : 0 < δ := (Real.rpow_pos_of_pos hL0 _).trans_le hδ
  obtain ⟨_,_,herror⟩ := hL₀ L ((le_max_left _ _).trans hL) δ hδ hδ1 n hn Cplus hCp
    lt xs ys hxs hys a b lam hlam W hWc hWs hW J Ψ₁ hΨ hD hH
  let q : ℝ := (δ / (2 * L ^ ((d : ℝ) - γ))) ^ (2 * n)
  have hq : 0 ≤ q := pow_nonneg (div_nonneg hδ0.le (by positivity)) _
  change ‖(q : ℂ) * _‖ ≤ _
  rw [norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg hq]
  calc q * ‖_‖ ≤ q * ((∏ j, lam j) ^ (2 * d) *
        (C₁ * Cplus * L ^ (2 * (d : ℝ) - 2 * γ) * δ⁻¹) ^ n * L ^ (-gamma1 d γ + η)) :=
      mul_le_mul_of_nonneg_left herror hq
    _ = (∏ j, lam j) ^ (2 * d) * (C₁ * Cplus * δ / 4) ^ n * L ^ (-gamma1 d γ + η) := by
      have hscale := normalized_scale (γ := γ) n d hL0 hδ0.ne' (C₁ * Cplus)
      change q * (C₁ * Cplus * L ^ (2 * (d : ℝ) - 2 * γ) * δ⁻¹) ^ n = _ at hscale
      calc
        _ = (∏ j, lam j) ^ (2 * d) *
          (q * (C₁ * Cplus * L ^ (2 * (d : ℝ) - 2 * γ) * δ⁻¹) ^ n) * L ^ (-gamma1 d γ + η) := by ring
        _ = _ := by rw [hscale]

end WaveTurbulence.RegAsymp
