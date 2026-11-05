/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.RegularAsymptotics.RegAsympDraft.LeafHalfCellSpectrum
public import WaveTurbulence.Foundations.RegularAsymptotics.RegAsympDraft.ShiftedSpectralMoment

/-! # One spatial first moment pays the actual leaf-only modulations

No moment order depends on the number of links. The only additional
factor is the polynomial source row loss, already bounded geometrically.
-/

public section
noncomputable section
namespace WaveTurbulence.RegAsymp
open MeasureTheory Links Incoh WithLp
open scoped ENNReal

/-- The exact moment appearing in the localized time bound. -/
theorem leaf_modulation_weight_le {G : Garden 2} {Q : RegCpl}
    (hQ : Q.Decodes G) (hG : IsCouple G) {d : ℕ}
    (α : Fin (2*Q.links.length+1) → Fin d → ℝ) :
    1+((∑ j, ‖sourceFrequencyPullback hQ hG (fun a => toLp 2 (α a)) (some (j,0))‖)+
      (∑ j, ‖sourceFrequencyPullback hQ hG (fun a => toLp 2 (α a)) (some (j,1))‖)) ≤
    spectralFrequencyLoss Q*(1+∑ a, ‖toLp 2 (α a)‖) := by
  let S := ∑ a, ‖toLp 2 (α a)‖
  let A := 1+(Q.size:ℝ)
  have hs (i : Fin 2) : (∑ j, ‖sourceFrequencyPullback hQ hG
      (fun a => toLp 2 (α a)) (some (j,i))‖) ≤ (Q.links.length:ℝ)*(A*S) := by
    calc
      _ ≤ ∑ _j : Fin Q.links.length, A*S := Finset.sum_le_sum
        (fun j _ => norm_sourceFrequencyPullback_le hQ hG _ _)
      _ = _ := by simp
  have hS : 0 ≤ S := Finset.sum_nonneg (fun a _ => norm_nonneg _)
  have hA : 0 ≤ A := by dsimp only [A]; positivity
  have hn : 0 ≤ (Q.links.length:ℝ) := Nat.cast_nonneg _
  have hp : 1 ≤ 2*Real.pi := by linarith [Real.pi_gt_three]
  have hmul : 2*(Q.links.length:ℝ)*A*S ≤ 4*Real.pi*(Q.links.length:ℝ)*A*S :=
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (by linarith : (2:ℝ) ≤ 4*Real.pi) hn) hA) hS
  have hpos : 0 ≤ 4*Real.pi*(Q.links.length:ℝ)*A := by positivity
  have h0 := hs 0
  have h1 := hs 1
  change 1+(_+_) ≤ spectralFrequencyLoss Q*(1+S)
  change 1+(_+_) ≤ (1+4*Real.pi*(Q.links.length:ℝ)*A)*(1+S)
  nlinarith

/-- All leaf centers and independent leaf frequencies are summable with
precisely the first modulation moment required by the NT remainder. -/
theorem tsum_leaf_modulation_firstMoment_le {G : Garden 2} {Q : RegCpl}
    (hQ : Q.Decodes G) (hG : IsCouple G) {d K M : ℕ} {F : Mom d → ℂ} {B : ℝ}
    (hK : d+2 ≤ K) (hM : 2*d ≤ M) (hB : 0 ≤ B)
    (hF : Fourier.spatialNorm K M F ≤ ENNReal.ofReal B) :
    (∑' c : Fin (2*Q.links.length+1) → Fin d → ℤ,
      ∫⁻ α : Fin (2*Q.links.length+1) → Fin d → ℝ,
        ENNReal.ofReal (1+((∑ j, ‖sourceFrequencyPullback hQ hG (fun a => toLp 2 (α a)) (some (j,0))‖)+
          (∑ j, ‖sourceFrequencyPullback hQ hG (fun a => toLp 2 (α a)) (some (j,1))‖))) *
            ∏ a, ‖Fourier.timeFourier (fun y : Fin d → ℝ => leafCell F (c a) (toLp 2 y)) (α a)‖ₑ) ≤
      ENNReal.ofReal (spectralFrequencyLoss Q)*
        ENNReal.ofReal (leafFirstMomentConstant d M*B)^(2*Q.links.length+1) := by
  calc
    _ ≤ ∑' c : Fin (2*Q.links.length+1) → Fin d → ℤ,
      ∫⁻ α : Fin (2*Q.links.length+1) → Fin d → ℝ,
        ENNReal.ofReal (spectralFrequencyLoss Q)*
          (ENNReal.ofReal (1+∑ a, ‖toLp 2 (α a)‖)*
            ∏ a, ‖Fourier.timeFourier (fun y : Fin d → ℝ => leafCell F (c a) (toLp 2 y)) (α a)‖ₑ) := by
      apply ENNReal.tsum_le_tsum
      intro c
      apply lintegral_mono
      intro α
      have hh := ENNReal.ofReal_le_ofReal (leaf_modulation_weight_le hQ hG α)
      rw [ENNReal.ofReal_mul (spectralFrequencyLoss_pos Q).le] at hh
      simpa only [mul_assoc] using mul_le_mul' hh (le_refl
        (∏ a, ‖Fourier.timeFourier (fun y : Fin d → ℝ => leafCell F (c a) (toLp 2 y)) (α a)‖ₑ))
    _ = ENNReal.ofReal (spectralFrequencyLoss Q)*
      (∑' c : Fin (2*Q.links.length+1) → Fin d → ℤ,
        ∫⁻ α : Fin (2*Q.links.length+1) → Fin d → ℝ,
          ENNReal.ofReal (1+∑ a, ‖toLp 2 (α a)‖)*
            ∏ a, ‖Fourier.timeFourier (fun y : Fin d → ℝ => leafCell F (c a) (toLp 2 y)) (α a)‖ₑ) := by
      simp_rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,ENNReal.tsum_mul_left]
    _ ≤ _ := mul_le_mul' le_rfl (tsum_leafFrequency_firstMoment_le hK hM hB hF)

end WaveTurbulence.RegAsymp
