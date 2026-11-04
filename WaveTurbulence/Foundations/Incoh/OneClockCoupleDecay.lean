/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Incoh.OneClockCouple

/-!
# The final temporal norm bound for degenerate one-clock couples

TARGET L1049, audit P-1. The actual one-clock source kernel has a
canonical two-time extension and the full printed incoherence exponent.
Either external clock can be active; the auxiliary branching clock need
not be a root of any source tree.
-/

public section
noncomputable section
open MeasureTheory Set
open scoped ENNReal

namespace WaveTurbulence.Incoh

/-- Translation of the passive external clock preserves the complete weighted Fourier norm. -/
theorem RootCoordinates.timeFourierNorm_oneClockExtension {d n : ℕ} (R : RootCoordinates n)
    (a : Fin 2) (L γ δ η : ℝ) (Q : Fin n → LayerLink d)
    (I : Set (Fin n → Fin 2 → ℝ)) (b : ℝ) :
    Fourier.timeFourierNorm η (R.oneClockExtension a L γ δ Q I b) =
      Fourier.timeFourierNorm η (R.coupleExtension wideRootCutoff L γ δ Q I) :=
  Fourier.timeFourierNorm_translate η (R.coupleExtension wideRootCutoff L γ δ Q I) (R.oneClockShift a Q b)

/-- TARGET's missing degenerate couple case: the literal one-clock kernel satisfies `𝔛^η`. -/
theorem exists_oneClockKernel_timeRestriction_bound (d : ℕ) (hd : 3 ≤ d)
    (η : ℝ) (hη : 0 < η) (hη₁ : η ≤ 1 / 3) :
    ∃ C₀ : ℝ, 0 < C₀ ∧ ∀ γ : ℝ, γ ∈ Ioo (0 : ℝ) 1 → η < incoherenceExponent d γ →
      ∀ δ : ℝ, 0 < δ → δ ≤ 1 → ∀ D : ℝ, 0 < D →
      ∃ L₀ : ℝ, 1 ≤ L₀ ∧ ∀ L ≥ L₀, ∀ n : ℕ, ∀ Q : Fin n → LayerLink d,
        1 ≤ incoherenceCount Q →
        (∀ i, |((Q i).leftLayer : ℝ) - (Q i).rightLayer| + 1 ≤ D) →
        ∀ I : Set (Fin n → Fin 2 → ℝ), MeasurableSet I → I ⊆ univ.pi (fun i => linkBox (Q i)) →
        ∀ R : RootCoordinates n, ∀ a : Fin 2, ∀ b : ℝ,
        Fourier.timeRestrictionNorm η (R.oneClockBox a Q b)
          (fun t => R.oneClockKernel a L γ δ Q I t) ≤
          ENNReal.ofReal ((C₀ * δ) ^ n *
            L ^ (-(incoherenceExponent d γ - 100 * (d : ℝ) * η) * incoherenceCount Q)) := by
  obtain ⟨C₀, hC₀, hb⟩ := exists_coupleExtension_timeFourier_bound d hd η hη hη₁
    contDiff_wideRootCutoff hasCompactSupport_wideRootCutoff
  refine ⟨C₀, hC₀, ?_⟩
  intro γ hγ hηγ δ hδ hδ₁ D hD
  obtain ⟨L₀, hL₀, hb⟩ := hb γ hγ hηγ δ hδ hδ₁ D hD
  refine ⟨L₀, hL₀, ?_⟩
  intro L hL n Q hg hspan I hI hbox R a b
  have hLp := zero_lt_one.trans_le (hL₀.trans hL)
  apply (Fourier.timeRestrictionNorm_le_extension (R.oneClockExtension a L γ δ Q I b)
    (fun t => R.oneClockExtension_agrees a hLp γ δ Q hI hbox b t.property)).trans
  rw [R.timeFourierNorm_oneClockExtension]
  exact hb L hL n Q hg hspan I hI hbox R

end WaveTurbulence.Incoh
