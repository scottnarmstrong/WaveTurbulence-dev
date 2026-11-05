/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.RegularAsymptotics.RegAsympDraft.SourceSpectralShift
public import WaveTurbulence.Foundations.RegularAsymptotics.RegAsympDraft.SpectralFirstMoment
public import WaveTurbulence.Foundations.RegAsymp.FrequencyArrayNorm

/-! # The actual NT frequency weight is paid by the common spectral moment -/

public section
noncomputable section
namespace WaveTurbulence.RegAsymp
open Links Incoh WithLp MeasureTheory
open scoped ENNReal

/-- Computed frequency loss of the actual C2 transpose map. -/
@[expose] def spectralFrequencyLoss (Q : RegCpl) : ℝ :=
  1+4*Real.pi*(Q.links.length:ℝ)*(1+(Q.size:ℝ))

theorem spectralFrequencyLoss_pos (Q : RegCpl) : 0 < spectralFrequencyLoss Q := by
  unfold spectralFrequencyLoss
  positivity

/-- Pointwise control of precisely the Fourier weight in NT (propertyw1). -/
theorem actual_spectralShift_frequency_weight_le {G : Garden 2} {Q : RegCpl}
    (hQ : Q.Decodes G) (hG : IsCouple G) {d : ℕ}
    (ξ : LocalizedCellIndex Q.links.length (2*Q.links.length+1) → Fin d → ℝ) :
    1+2*Real.pi*ApproxNT.freqNorm
      (fun j => (coupleMomentumData hQ hG).spectralShift ξ (some (j,0)))
      (fun j => (coupleMomentumData hQ hG).spectralShift ξ (some (j,1))) ≤
      spectralFrequencyLoss Q * (1+∑ i, ‖toLp 2 (ξ i)‖) := by
  let S := ∑ i, ‖toLp 2 (ξ i)‖
  let A := 1+(Q.size:ℝ)
  have hS : 0 ≤ S := Finset.sum_nonneg (fun i _ => norm_nonneg _)
  have hA : 0 ≤ A := by dsimp only [A]; positivity
  have hh := freqNorm_le_sum
    (fun j => (coupleMomentumData hQ hG).spectralShift ξ (some (j,0)))
    (fun j => (coupleMomentumData hQ hG).spectralShift ξ (some (j,1)))
  have hs : (∑ j, (‖(coupleMomentumData hQ hG).spectralShift ξ (some (j,0))‖+
      ‖(coupleMomentumData hQ hG).spectralShift ξ (some (j,1))‖)) ≤
      (Q.links.length:ℝ)*(2*(A*S)) := by
    calc
      _ ≤ ∑ _j : Fin Q.links.length, (A*S+A*S) := Finset.sum_le_sum (fun j _ =>
        add_le_add (norm_actual_spectralShift_link_le hQ hG ξ (j,0))
          (norm_actual_spectralShift_link_le hQ hG ξ (j,1)))
      _ = _ := by simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]; ring
  have hp := Real.pi_pos
  have hn : 0 ≤ (Q.links.length:ℝ) := Nat.cast_nonneg _
  have hbound := hh.trans hs
  have hm := mul_le_mul_of_nonneg_left hbound (by positivity : 0 ≤ 2*Real.pi)
  have hB : 0 ≤ 4*Real.pi*(Q.links.length:ℝ)*A := by positivity
  change 1+2*Real.pi*_ ≤ spectralFrequencyLoss Q*(1+S)
  unfold spectralFrequencyLoss
  dsimp only [A] at hbound hA hm hB
  nlinarith

/-- The actual NT modulation moment has a finite total common envelope,
after summing every source leaf localization. -/
theorem tsum_actual_spectralShift_weighted_reference_le {G : Garden 2} {Q : RegCpl}
    (hQ : Q.Decodes G) (hG : IsCouple G) {d K M : ℕ} {F : Mom d → ℂ} {B : ℝ}
    (hK : d+2 ≤ K) (hM : 2*d ≤ M) (hB : 0 ≤ B)
    (hF : Fourier.spatialNorm K M F ≤ ENNReal.ofReal B) :
    (∑' c : Fin (2*Q.links.length+1) → Fin d → ℤ,
      ∫⁻ ξ : LocalizedCellIndex Q.links.length (2*Q.links.length+1) → Fin d → ℝ,
        ENNReal.ofReal (1+2*Real.pi*ApproxNT.freqNorm
          (fun j => (coupleMomentumData hQ hG).spectralShift ξ (some (j,0)))
          (fun j => (coupleMomentumData hQ hG).spectralShift ξ (some (j,1)))) *
          ‖localizedSpectralReference (n := Q.links.length) (fun _ => F) c ξ‖ₑ) ≤
      ENNReal.ofReal (spectralFrequencyLoss Q) *
        (ENNReal.ofReal (leafFirstMomentConstant d M * B) ^ (2*Q.links.length+1) *
          ENNReal.ofReal (halfLinkFirstMomentConstant d) ^ (2*Q.links.length)) := by
  have hD := (spectralFrequencyLoss_pos Q).le
  calc
    _ ≤ ∑' c : Fin (2*Q.links.length+1) → Fin d → ℤ,
        ∫⁻ ξ : LocalizedCellIndex Q.links.length (2*Q.links.length+1) → Fin d → ℝ,
          ENNReal.ofReal (spectralFrequencyLoss Q) *
            (ENNReal.ofReal (1+∑ i, ‖toLp 2 (ξ i)‖) *
              ‖localizedSpectralReference (n := Q.links.length) (fun _ => F) c ξ‖ₑ) := by
      apply ENNReal.tsum_le_tsum
      intro c
      apply lintegral_mono
      intro ξ
      have hh := ENNReal.ofReal_le_ofReal (actual_spectralShift_frequency_weight_le hQ hG ξ)
      rw [ENNReal.ofReal_mul hD] at hh
      simpa only [mul_assoc] using mul_le_mul' hh (le_refl
        ‖localizedSpectralReference (n := Q.links.length) (fun _ => F) c ξ‖ₑ)
    _ = ENNReal.ofReal (spectralFrequencyLoss Q) *
        (∑' c : Fin (2*Q.links.length+1) → Fin d → ℤ,
          ∫⁻ ξ : LocalizedCellIndex Q.links.length (2*Q.links.length+1) → Fin d → ℝ,
            ENNReal.ofReal (1+∑ i, ‖toLp 2 (ξ i)‖) *
              ‖localizedSpectralReference (n := Q.links.length) (fun _ => F) c ξ‖ₑ) := by
      simp_rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,ENNReal.tsum_mul_left]
    _ ≤ _ := mul_le_mul' le_rfl (tsum_localizedSpectralReference_firstMoment_le hK hM hB hF)

end WaveTurbulence.RegAsymp
