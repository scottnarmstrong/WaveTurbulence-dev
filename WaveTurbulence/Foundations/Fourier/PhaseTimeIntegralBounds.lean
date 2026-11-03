/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Fourier.PhaseOperatorMoments
public import WaveTurbulence.Foundations.Fourier.ThreeMomentNorm
import Mathlib.Tactic

/-!
# TARGET A.3: phase-modulated time integrals in the mixed Fourier norm

Owner ruling (2026-11-03): use smooth compactly supported time slices,
as in the proof, rather than the printed arbitrary-complex-function claim.
The zero-order mixed norm retains time integrability and imposes no
momentum regularity. Both phase functions are completely arbitrary.

The proof localizes before using mixed-derivative control. It does not use
the printed unlocalized weak-decay assertion or the globally Schwartz
assertion for the remaining tail integrals in the fourfold proof.
-/

public section

open MeasureTheory
open scoped ContDiff ENNReal

namespace WaveTurbulence.Fourier

/-- Explicit twofold time-integral factor for declared cutoff control data. -/
@[expose] noncomputable def triangularTimeFactor (R C : ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal (8 * jointFrequencyConstant) * orderedFourMomentFactor R C * triangularAmplitudeFactor R C

/-- Explicit fourfold time-integral factor for the same cutoff control data. -/
@[expose] noncomputable def fourfoldTimeFactor (R C : ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal (8 * jointFrequencyConstant) * orderedFourMomentFactor R C * fourfoldAmplitudeFactor R C

/-- The two explicit source constants are finite. -/
theorem phaseTimeFactors_ne_top (R C : ℝ) :
    triangularTimeFactor R C ≠ ⊤ ∧ fourfoldTimeFactor R C ≠ ⊤ := by
  constructor
  · unfold triangularTimeFactor
    exact ENNReal.mul_ne_top (ENNReal.mul_ne_top ENNReal.ofReal_ne_top
      (orderedFourMomentFactor_ne_top R C)) (phaseAmplitudeFactors_ne_top R C).1
  · unfold fourfoldTimeFactor
    exact ENNReal.mul_ne_top (ENNReal.mul_ne_top ENNReal.ofReal_ne_top
      (orderedFourMomentFactor_ne_top R C)) (phaseAmplitudeFactors_ne_top R C).2

/-- TARGET A.3's triangular estimate, uniform in arbitrary momentum phases. -/
theorem mixedFourierNorm_cutoffU_le {d : ℕ} {χ : ℝ → ℝ} (hχ : ContDiff ℝ ∞ χ)
    (h : CutoffControl χ) (Γ : Mom d → ℝ) {F : (Fin 2 → ℝ) → Mom d → ℂ}
    (hF : ∀ k, ContDiff ℝ ∞ (fun t => F t k))
    (hc : ∀ k, HasCompactSupport (fun t => F t k)) :
    mixedFourierNorm (1 / 4) 0 0 (cutoffU χ Γ F) ≤ triangularTimeFactor h.radius h.bound *
      uniformTimeL1 (fun t k => mixedTimePartial (fun u => F u k) t) := by
  let M := uniformTimeL1 (fun t k => mixedTimePartial (fun u => F u k) t)
  have hOut (k : Mom d) : ContDiff ℝ ∞ (fun t => cutoffU χ Γ F t k) := by
    rw [cutoffU_eq_balanced]
    exact weightedOrderedIntegral_contDiff hχ hχ
      (balancedCutoffAmplitude_contDiff hχ (hF k) ![Γ k, -Γ k] 0 1)
  have hcOut (k : Mom d) : HasCompactSupport (fun t => cutoffU χ Γ F t k) := by
    rw [cutoffU_eq_balanced]
    exact weightedOrderedIntegral_hasCompactSupport h.endpointBounds h.endpointBounds _
  have hL1 (k : Mom d) : (∫⁻ x, ‖mixedTimePartial (fun t => F t k) x‖ₑ) ≤ M := by
    change (∫⁻ x, ‖mixedTimePartial (fun t => F t k) x‖ₑ) ≤
      ⨆ k, eLpNorm (mixedTimePartial (fun u => F u k)) 1
    exact lintegral_enorm_le_eLpNorm_one.trans
      (le_iSup (fun k : Mom d => eLpNorm (mixedTimePartial (fun u => F u k)) 1) k)
  have hSup : (⨆ k, ENNReal.ofReal (threeTimeMomentSum (fun t => cutoffU χ Γ F t k))) ≤
      orderedFourMomentFactor h.radius h.bound * triangularAmplitudeFactor h.radius h.bound * M := by
    apply iSup_le
    intro k
    exact (threeTimeMomentSum_cutoffU_le hχ h Γ F k (hF k) (hc k)).trans
      (mul_le_mul' le_rfl (hL1 k))
  apply (mixedFourierNorm_quarter_le_three_moments hOut hcOut).trans
  exact (mul_le_mul' le_rfl hSup).trans_eq (by unfold triangularTimeFactor; dsimp [M]; ring)

/-- TARGET A.3's fourfold estimate, uniform in both arbitrary momentum phases. -/
theorem mixedFourierNorm_cutoffV_le {d : ℕ} {χ : ℝ → ℝ} (hχ : ContDiff ℝ ∞ χ)
    (h : CutoffControl χ) (Γ₁ Γ₂ : Mom d → ℝ) {F : (Fin 2 → ℝ) → Mom d → ℂ}
    (hF : ∀ k, ContDiff ℝ ∞ (fun t => F t k))
    (hc : ∀ k, HasCompactSupport (fun t => F t k)) :
    mixedFourierNorm (1 / 4) 0 0 (cutoffV χ Γ₁ Γ₂ F) ≤ fourfoldTimeFactor h.radius h.bound *
      uniformTimeL1 (fun t k => mixedTimePartial (fun u => F u k) t) := by
  let M := uniformTimeL1 (fun t k => mixedTimePartial (fun u => F u k) t)
  have hOut (k : Mom d) : ContDiff ℝ ∞ (fun t => cutoffV χ Γ₁ Γ₂ F t k) := by
    rw [cutoffV_eq_balanced]
    exact weightedOrderedIntegral_contDiff hχ hχ
      (balancedCutoffAmplitude_contDiff hχ (hF k) ![Γ₁ k, -Γ₁ k, Γ₂ k, -Γ₂ k] 1 2)
  have hcOut (k : Mom d) : HasCompactSupport (fun t => cutoffV χ Γ₁ Γ₂ F t k) := by
    rw [cutoffV_eq_balanced]
    exact weightedOrderedIntegral_hasCompactSupport h.endpointBounds h.endpointBounds _
  have hL1 (k : Mom d) : (∫⁻ x, ‖mixedTimePartial (fun t => F t k) x‖ₑ) ≤ M := by
    change (∫⁻ x, ‖mixedTimePartial (fun t => F t k) x‖ₑ) ≤
      ⨆ k, eLpNorm (mixedTimePartial (fun u => F u k)) 1
    exact lintegral_enorm_le_eLpNorm_one.trans
      (le_iSup (fun k : Mom d => eLpNorm (mixedTimePartial (fun u => F u k)) 1) k)
  have hSup : (⨆ k, ENNReal.ofReal (threeTimeMomentSum (fun t => cutoffV χ Γ₁ Γ₂ F t k))) ≤
      orderedFourMomentFactor h.radius h.bound * fourfoldAmplitudeFactor h.radius h.bound * M := by
    apply iSup_le
    intro k
    exact (threeTimeMomentSum_cutoffV_le hχ h Γ₁ Γ₂ F k (hF k) (hc k)).trans
      (mul_le_mul' le_rfl (hL1 k))
  apply (mixedFourierNorm_quarter_le_three_moments hOut hcOut).trans
  exact (mul_le_mul' le_rfl hSup).trans_eq (by unfold fourfoldTimeFactor; dsimp [M]; ring)

/-- TARGET Lemma A.3 with the owner-approved source class and a positive constant
that depends only on the smooth compact cutoff, uniformly in dimension and both phases. -/
theorem exists_cutoff_phase_mixedNorm_bound {χ : ℝ → ℝ} (hχ : ContDiff ℝ ∞ χ)
    (hcχ : HasCompactSupport χ) : ∃ C : ℝ, 0 < C ∧ ∀ (d : ℕ) (Γ₁ Γ₂ : Mom d → ℝ)
      (F : (Fin 2 → ℝ) → Mom d → ℂ),
      (∀ k, ContDiff ℝ ∞ (fun t => F t k)) → (∀ k, HasCompactSupport (fun t => F t k)) →
      mixedFourierNorm (1 / 4) 0 0 (cutoffU χ Γ₁ F) ≤ ENNReal.ofReal C *
        uniformTimeL1 (fun t k => mixedTimePartial (fun u => F u k) t) ∧
      mixedFourierNorm (1 / 4) 0 0 (cutoffV χ Γ₁ Γ₂ F) ≤ ENNReal.ofReal C *
        uniformTimeL1 (fun t k => mixedTimePartial (fun u => F u k) t) := by
  obtain ⟨h⟩ := exists_cutoffControl hχ hcχ
  let K := max (triangularTimeFactor h.radius h.bound) (fourfoldTimeFactor h.radius h.bound)
  have hKt : K ≠ ⊤ := by
    have hs := phaseTimeFactors_ne_top h.radius h.bound
    exact (max_lt (lt_top_iff_ne_top.mpr hs.1) (lt_top_iff_ne_top.mpr hs.2)).ne
  let C : ℝ := 1 + K.toReal
  have hC : 0 < C := by
    have h0 : 0 ≤ K.toReal := ENNReal.toReal_nonneg
    dsimp [C]
    linarith
  have hKC : K ≤ ENNReal.ofReal C := by
    calc
      _ = ENNReal.ofReal K.toReal := (ENNReal.ofReal_toReal hKt).symm
      _ ≤ _ := ENNReal.ofReal_le_ofReal (by dsimp [C]; linarith)
  refine ⟨C, hC, ?_⟩
  intro d Γ₁ Γ₂ F hF hc
  constructor
  · exact (mixedFourierNorm_cutoffU_le hχ h Γ₁ hF hc).trans
      (mul_le_mul' ((le_max_left _ _).trans hKC) le_rfl)
  · exact (mixedFourierNorm_cutoffV_le hχ h Γ₁ Γ₂ hF hc).trans
      (mul_le_mul' ((le_max_right _ _).trans hKC) le_rfl)

end WaveTurbulence.Fourier
