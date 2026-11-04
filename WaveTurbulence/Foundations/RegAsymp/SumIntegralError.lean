/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.ApproxNT.Conclusion1
public import WaveTurbulence.Foundations.RegAsymp.Normalization

/-! # Normalized sum-to-integral error using derivatives alone -/

public section
noncomputable section
namespace WaveTurbulence.RegAsymp
open MeasureTheory ApproxNT Finset
open scoped ENNReal ContDiff

/-- NT conclusion1 retains a linear amplitude budget without imposing
a temporal maximum moment. The order range is arbitrary logarithmic order. -/
theorem normalized_sum_integral_error {d : ℕ} (hd : 3 ≤ d) {γ η : ℝ}
    (hγ : γ ∈ Set.Ioo (0:ℝ) 1) (hη0 : 0 < η) (hη : η ≤ 1/20)
    (hηγ : η ≤ ((d:ℝ)-1)*(1-γ)) :
    ∃ C : ℝ, 0 < C ∧ ∀ A : ℝ, ∃ L₀ : ℝ, ∀ L : ℝ, L₀ ≤ L →
      ∀ δ : ℝ, 0 < δ → δ ≤ 1 → ∀ n : ℕ, 0 < n → (n:ℝ) ≤ Real.log L ^ A →
      ∀ H : ℝ, 0 ≤ H →
      ∀ (lt : Fin n → Fin n → Prop) [IsStrictOrder (Fin n) lt] (xs ys : Fin n → Shift n),
      (∀ j, (xs j).Below lt j) → (∀ j, (ys j).Below lt j) →
      ∀ (a b : Fin n → Mom d) (lam : Fin n → ℝ), (∀ j, 1 ≤ lam j) →
      ∀ W : (Fin n → Mom d) → (Fin n → Mom d) → ℂ, Continuous (Function.uncurry W) →
      (∀ x y, W x y ≠ 0 → (x,y) ∈ supportSet xs ys a b lam) →
      (∫⁻ τ : (Fin n → Mom d) × (Fin n → Mom d), ‖fourierW W τ.1 τ.2‖ₑ *
        ENNReal.ofReal (1+2*Real.pi*freqNorm τ.1 τ.2)) ≤ ENNReal.ofReal H →
      ∀ (J : Finset (Fin n)) (Ψ : EuclideanSpace ℝ {j // j ∉ J} → ℂ),
      ContDiff ℝ ∞ Ψ → WordDerivL1 Ψ (fun k => ((4*k).factorial:ℝ)) →
      ‖(((δ/(2*L^((d:ℝ)-γ)))^(2*n):ℝ):ℂ) *
        (approxSum L (L^(2*γ)*δ) W (resProfile J Ψ) -
          (L:ℂ)^(2*d*n)*approxInt (L^(2*γ)*δ) W (resProfile J Ψ))‖ ≤
        (∏ j, lam j)^(2*d)*(C*δ/4)^n*H*L^(-gamma1 d γ+η) := by
  obtain ⟨C,hC,hNT⟩ := approxnt_conclusion1 hd hγ hη0 hη hηγ (le_refl (1:ℝ))
  refine ⟨C,hC,fun A => ?_⟩
  obtain ⟨L₀,hL₀⟩ := hNT A
  refine ⟨max L₀ 2,?_⟩
  intro L hL δ hδ hδ1 n hnp hn H hH lt _ xs ys hxs hys a b lam hlam W hWc hWs hW J Ψ hΨ hD
  have hL0 : 0 < L := lt_of_lt_of_le (by norm_num : (0:ℝ)<2) ((le_max_right _ _).trans hL)
  let Cp : ℝ := H^((n:ℝ)⁻¹)
  have hCp : 0 ≤ Cp := Real.rpow_nonneg hH _
  have hpow : Cp^n=H := Real.rpow_inv_natCast_pow hH (Nat.ne_of_gt hnp)
  have hW' : (∫⁻ τ : (Fin n → Mom d) × (Fin n → Mom d), ‖fourierW W τ.1 τ.2‖ₑ *
      ENNReal.ofReal (1+2*Real.pi*freqNorm τ.1 τ.2)) ≤ ENNReal.ofReal (Cp^n) := by rwa [hpow]
  have herr := hL₀ L ((le_max_left _ _).trans hL) δ ⟨hδ,hδ1⟩ n hn Cp hCp lt xs ys hxs hys
    a b lam hlam W hWc hWs hW' J Ψ hΨ (by simpa only [one_pow,one_mul] using hD)
  let q : ℝ := (δ/(2*L^((d:ℝ)-γ)))^(2*n)
  have hq : 0 ≤ q := by dsimp only [q]; positivity
  change ‖(q:ℂ)*_‖ ≤ _
  rw [norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg hq]
  apply (mul_le_mul_of_nonneg_left herr hq).trans_eq
  have hs := normalized_scale (γ := γ) n d hL0 hδ.ne' (C*Cp)
  change q*(C*Cp*L^(2*(d:ℝ)-2*γ)*δ⁻¹)^n = (C*Cp*δ/4)^n at hs
  have hp : (C*Cp*δ/4)^n = (C*δ/4)^n*H := by
    rw [show C*Cp*δ/4=(C*δ/4)*Cp by ring,mul_pow,hpow]
  calc
    _ = (∏ j, lam j)^(2*d)*(q*(C*Cp*L^(2*(d:ℝ)-2*γ)*δ⁻¹)^n)*L^(-gamma1 d γ+η) := by ring
    _ = _ := by rw [hs,hp]; ring

end WaveTurbulence.RegAsymp
