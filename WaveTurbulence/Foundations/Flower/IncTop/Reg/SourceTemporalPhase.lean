/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Incoh.LayerLink

/-! Ported by source from C2-B-TOP `Cut2BReg.SourceTemporalPhase` (sha256 in COPIED-SHA256SUMS); mechanical edits only.

R66 spatially modulated scratch copy. Original SHA256 recorded in REG-COPIES.json.

# Literal source temporal phase and squared Wick coefficient

TARGET (incohproof2). The source factor includes time-independent spatial characters in the internal paired
coordinates; its root-momentum dependence stays in the leaf profile product.
-/

public section
noncomputable section
open MeasureTheory Set

namespace WaveTurbulence.Flower.IncTop
open WaveTurbulence.Incoh
/-- Actual Wick-corrected temporal factor at fixed free lattice momenta. -/
@[expose] def sourceTemporalPhaseSpatial {d n : ℕ} (L γ δ : ℝ) (Q : Fin n → LayerLink d)
    (p : (Fin n × Fin 2) → Fin d → ℤ) (t : Fin n → Fin 2 → ℝ) : ℂ :=
  ∏ i, (linkWickFactor (p (i, 0)) (p (i, 1)) : ℂ) *
    WeylSums.e ((((Q i).orientation : ℤ) : ℝ) * δ * L ^ (2 * γ) *
      (t i 0 - t i 1) * inner ℝ (latticePoint L (p (i, 0))) (latticePoint L (p (i, 1))) +
      inner ℝ (latticePoint L (p (i, 0))) (Q i).leftShift +
      inner ℝ (latticePoint L (p (i, 1))) (Q i).rightShift)

/-- Literal source phases are continuous in all vertex clocks. -/
theorem continuous_sourceTemporalPhaseSpatial {d n : ℕ} (L γ δ : ℝ) (Q : Fin n → LayerLink d)
    (p : (Fin n × Fin 2) → Fin d → ℤ) : Continuous (sourceTemporalPhaseSpatial L γ δ Q p) := by
  unfold sourceTemporalPhaseSpatial
  apply continuous_finsetProd
  intro i _
  unfold WeylSums.e
  fun_prop

/-- The true squared Wick coefficient does not increase the source phase amplitude. -/
theorem norm_sourceTemporalPhase_le_oneSpatial {d n : ℕ} (L γ δ : ℝ) (Q : Fin n → LayerLink d)
    (p : (Fin n × Fin 2) → Fin d → ℤ) (t : Fin n → Fin 2 → ℝ) :
    ‖sourceTemporalPhaseSpatial L γ δ Q p t‖ ≤ 1 := by
  rw [sourceTemporalPhaseSpatial, norm_prod]
  apply Finset.prod_le_one₀
  · intro _ _; exact norm_nonneg _
  · intro i _
    rw [norm_mul, WeylSums.norm_e, mul_one, Complex.norm_real, Real.norm_eq_abs]
    exact abs_linkWickFactor_le _ _

/-- Every actual source phase is integrable on any source time subdomain of the layer box. -/
theorem integrableOn_sourceTemporalPhaseSpatial {d n : ℕ} (L γ δ : ℝ) (Q : Fin n → LayerLink d)
    (p : (Fin n × Fin 2) → Fin d → ℤ) {I : Set (Fin n → Fin 2 → ℝ)}
    (hI : I ⊆ univ.pi (fun i => linkBox (Q i))) :
    IntegrableOn (sourceTemporalPhaseSpatial L γ δ Q p) I := by
  exact ((continuous_sourceTemporalPhaseSpatial L γ δ Q p).continuousOn.integrableOn_compact
    (isCompact_univ_pi (fun i => isCompact_Icc))).mono_set hI

end WaveTurbulence.Flower.IncTop