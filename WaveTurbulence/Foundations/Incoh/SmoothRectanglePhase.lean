/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Incoh.SmoothRectangleMass
public import WaveTurbulence.Foundations.Fourier.PhaseTimeIntegralBounds

/-!
# Phase estimates uniform in rectangular fibers

TARGET (incohproof27)–(incohproof28). Both phases and interval endpoints may
vary arbitrarily with momentum. The bound is independent of the smoothing
width and retains the momentum supremum inside the frequency integral.
-/

public section
noncomputable section
open MeasureTheory
open scoped ENNReal ContDiff

namespace WaveTurbulence.Incoh

/-- The landed phase lemma applies uniformly to all smoothed rectangular fibers. -/
theorem exists_smoothRectangle_phase_bound {χ : ℝ → ℝ} (hχ : ContDiff ℝ ∞ χ)
    (hcχ : HasCompactSupport χ) : ∃ C : ℝ, 0 < C ∧
    ∀ (d : ℕ) (Γ₁ Γ₂ : Mom d → ℝ) (a b : Mom d → Fin 2 → ℝ),
      (∀ k, a k ≤ b k) → ∀ ε : ℝ, 0 < ε →
      Fourier.mixedFourierNorm (1 / 4) 0 0
        (Fourier.cutoffU χ Γ₁ (fun t k => smoothRectangle ε (a k) (b k) t)) ≤ ENNReal.ofReal C ∧
      Fourier.mixedFourierNorm (1 / 4) 0 0
        (Fourier.cutoffV χ Γ₁ Γ₂ (fun t k => smoothRectangle ε (a k) (b k) t)) ≤ ENNReal.ofReal C := by
  obtain ⟨C, hC, hb⟩ := Fourier.exists_cutoff_phase_mixedNorm_bound hχ hcχ
  refine ⟨C * 4, mul_pos hC (by norm_num), ?_⟩
  intro d Γ₁ Γ₂ a b hab ε hε
  have hd (k : Mom d) := contDiff_smoothRectangle ε (a k) (b k)
  have hc (k : Mom d) := hasCompactSupport_smoothRectangle hε (a k) (b k) (hab k)
  have hm : Fourier.uniformTimeL1 (fun t k =>
      Fourier.mixedTimePartial (smoothRectangle ε (a k) (b k)) t) ≤ 4 := by
    apply iSup_le
    intro k
    rw [eLpNorm_one_eq_lintegral_enorm]
    · exact lintegral_mixedTimePartial_smoothRectangle_le hε (a k) (b k) (hab k)
    · exact (WaveTurbulence.contDiff_infty_partialDeriv
        (WaveTurbulence.contDiff_infty_partialDeriv (hd k) 1) 0).continuous.aestronglyMeasurable
  have hs := hb d Γ₁ Γ₂ (fun t k => smoothRectangle ε (a k) (b k) t) hd hc
  have he : ENNReal.ofReal C * 4 = ENNReal.ofReal (C * 4) := by
    rw [ENNReal.ofReal_mul hC.le]; norm_num
  exact ⟨hs.1.trans ((mul_le_mul' le_rfl hm).trans_eq he),
    hs.2.trans ((mul_le_mul' le_rfl hm).trans_eq he)⟩

end WaveTurbulence.Incoh
