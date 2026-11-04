/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.ApproxNT.Conclusion2

/-! # Fourier inversion with the actual linear amplitude budget -/

public section
noncomputable section
namespace WaveTurbulence.RegAsymp
open MeasureTheory ApproxNT
open scoped ENNReal

/-- The exact NT Fourier setup, retaining the actual mass H rather than
an nth power of a frequency-dependent bound. -/
theorem fourierAmplitude_setup {d n : ℕ} (hn : 0 < n)
    {lt : Fin n → Fin n → Prop} [IsStrictOrder (Fin n) lt]
    {xs ys : Fin n → Shift n} (hxs : ∀ j, (xs j).Below lt j) (hys : ∀ j, (ys j).Below lt j)
    {a b : Fin n → Mom d} {lam : Fin n → ℝ}
    {W : (Fin n → Mom d) → (Fin n → Mom d) → ℂ}
    (hWc : Continuous (Function.uncurry W))
    (hWs : ∀ x y, W x y ≠ 0 → (x,y) ∈ supportSet xs ys a b lam)
    {H : ℝ} (hH : 0 ≤ H)
    (hW : (∫⁻ τ : (Fin n → Mom d) × (Fin n → Mom d), ‖fourierW W τ.1 τ.2‖ₑ *
      ENNReal.ofReal (1+2*Real.pi*freqNorm τ.1 τ.2)) ≤ ENNReal.ofReal H) :
    Integrable (fun τ : (Fin n → Mom d) × (Fin n → Mom d) => fourierW W τ.1 τ.2) ∧
      (∀ x y, W x y = ∫ τ, fourierW W τ.1 τ.2*wPhase x y τ) ∧
      Integrable (fun τ : (Fin n → Mom d) × (Fin n → Mom d) =>
        ‖fourierW W τ.1 τ.2‖*(1+2*Real.pi*freqNorm τ.1 τ.2)) ∧
      (∫ τ : (Fin n → Mom d) × (Fin n → Mom d),
        ‖fourierW W τ.1 τ.2‖*(1+2*Real.pi*freqNorm τ.1 τ.2)) ≤ H := by
  let Cp : ℝ := H ^ ((n:ℝ)⁻¹)
  have hCp : 0 ≤ Cp := Real.rpow_nonneg hH _
  have hpow : Cp^n=H := Real.rpow_inv_natCast_pow hH (Nat.ne_of_gt hn)
  have hW' : (∫⁻ τ : (Fin n → Mom d) × (Fin n → Mom d), ‖fourierW W τ.1 τ.2‖ₑ *
      ENNReal.ofReal (1+2*Real.pi*freqNorm τ.1 τ.2)) ≤ ENNReal.ofReal (Cp^n) := by rwa [hpow]
  obtain ⟨hF,hinv,hI,hb⟩ := fourierW_setup hxs hys hWc hWs hW' hCp
  exact ⟨hF,hinv,hI,by simpa only [hpow] using hb⟩

/-- Discarding the positive Fourier weight retains the same linear budget. -/
theorem integral_norm_fourierW_le {d n : ℕ}
    {W : (Fin n → Mom d) → (Fin n → Mom d) → ℂ}
    (hF : Integrable (fun τ : (Fin n → Mom d) × (Fin n → Mom d) => fourierW W τ.1 τ.2))
    (hI : Integrable (fun τ : (Fin n → Mom d) × (Fin n → Mom d) =>
      ‖fourierW W τ.1 τ.2‖*(1+2*Real.pi*freqNorm τ.1 τ.2))) {H : ℝ}
    (hB : (∫ τ : (Fin n → Mom d) × (Fin n → Mom d),
      ‖fourierW W τ.1 τ.2‖*(1+2*Real.pi*freqNorm τ.1 τ.2)) ≤ H) :
    (∫ τ : (Fin n → Mom d) × (Fin n → Mom d), ‖fourierW W τ.1 τ.2‖) ≤ H := by
  apply (integral_mono hF.norm hI (fun τ => ?_)).trans hB
  have hf := freqNorm_nonneg τ.1 τ.2
  exact le_mul_of_one_le_right (norm_nonneg _) (by nlinarith [Real.pi_pos])

end WaveTurbulence.RegAsymp
