/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Incoh.LayerLink

/-!
# Literal source temporal phase and squared Wick coefficient

TARGET (incohproof2). The source factor has no localization cutoff or
Fourier shift; its time dependence is continuous on the full clock space.
-/

public section
noncomputable section
open MeasureTheory Set

namespace WaveTurbulence.Incoh

/-- Actual Wick-corrected temporal factor at fixed free lattice momenta. -/
@[expose] def sourceTemporalPhase {d n : ℕ} (L γ δ : ℝ) (Q : Fin n → LayerLink d)
    (p : (Fin n × Fin 2) → Fin d → ℤ) (t : Fin n → Fin 2 → ℝ) : ℂ :=
  ∏ i, (linkWickFactor (p (i, 0)) (p (i, 1)) : ℂ) *
    WeylSums.e ((((Q i).orientation : ℤ) : ℝ) * δ * L ^ (2 * γ) *
      (t i 0 - t i 1) * inner ℝ (latticePoint L (p (i, 0))) (latticePoint L (p (i, 1))))

/-- Literal source phases are continuous in all vertex clocks. -/
theorem continuous_sourceTemporalPhase {d n : ℕ} (L γ δ : ℝ) (Q : Fin n → LayerLink d)
    (p : (Fin n × Fin 2) → Fin d → ℤ) : Continuous (sourceTemporalPhase L γ δ Q p) := by
  unfold sourceTemporalPhase
  apply continuous_finsetProd
  intro i _
  unfold WeylSums.e
  fun_prop

/-- The true squared Wick coefficient does not increase the source phase amplitude. -/
theorem norm_sourceTemporalPhase_le_one {d n : ℕ} (L γ δ : ℝ) (Q : Fin n → LayerLink d)
    (p : (Fin n × Fin 2) → Fin d → ℤ) (t : Fin n → Fin 2 → ℝ) :
    ‖sourceTemporalPhase L γ δ Q p t‖ ≤ 1 := by
  rw [sourceTemporalPhase, norm_prod]
  apply Finset.prod_le_one₀
  · intro _ _; exact norm_nonneg _
  · intro i _
    rw [norm_mul, WeylSums.norm_e, mul_one, Complex.norm_real, Real.norm_eq_abs]
    exact abs_linkWickFactor_le _ _

/-- Every actual source phase is integrable on any source time subdomain of the layer box. -/
theorem integrableOn_sourceTemporalPhase {d n : ℕ} (L γ δ : ℝ) (Q : Fin n → LayerLink d)
    (p : (Fin n × Fin 2) → Fin d → ℤ) {I : Set (Fin n → Fin 2 → ℝ)}
    (hI : I ⊆ univ.pi (fun i => linkBox (Q i))) :
    IntegrableOn (sourceTemporalPhase L γ δ Q p) I := by
  exact ((continuous_sourceTemporalPhase L γ δ Q p).continuousOn.integrableOn_compact
    (isCompact_univ_pi (fun i => isCompact_Icc))).mono_set hI

end WaveTurbulence.Incoh
