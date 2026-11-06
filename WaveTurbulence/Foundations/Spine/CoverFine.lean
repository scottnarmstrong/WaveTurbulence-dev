/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.Spine.CoverBudget
public import WaveTurbulence.Foundations.Spine.SplicedCoverChoiceScaleBound
public import WaveTurbulence.Foundations.Spine.SourceSplicedBounds
/-! TARGET finalsbest2 (L2078) for the spliced kernel of an actual choice datum `Cs`, from the
literal gates `ladderl1old` and `finalcount1` (RULINGS R7). All names are conditional helpers:
`Cs` and `SubproConclusions` (subpro and the C1 half of L2116) are hypotheses; the construction
of `Cs` is S2a and `subpro` is S4. -/
public section
set_option autoImplicit false
namespace WaveTurbulence.LGSpine.Cover
open WaveTurbulence.Induct
open SourceVine Set Finset WaveTurbulence.LGSpine
open scoped Classical

theorem exp_form_eq_fine {R : ℕ} (G : Garden (2 * R)) (P : WTParams) (hL : 0 < P.L)
    (hC₁ : 0 < P.C₁) (hδ : 0 < P.δ) (hinges : ℕ) :
    P.C₁ * Real.exp (G.order * (Real.log P.C₁ - 10 * P.ν * Real.log P.δ) +
        (-P.η ^ 6 * (G.molecule.rho + hinges) - ((R : ℝ) - 1) * (1 / 4 + 1 / 50)) * Real.log P.L) =
      P.C₁ * (P.C₁ * P.δ ^ (-10 * P.ν)) ^ G.order *
        P.L ^ (-P.η ^ 6 * (G.molecule.rho + hinges)) *
          P.L ^ (-((R : ℝ) - 1) * (1 / 4 + 1 / 50)) := by
  have hpos : 0 < P.C₁ * P.δ ^ (-10 * P.ν) := mul_pos hC₁ (Real.rpow_pos_of_pos hδ _)
  have hlog : Real.log (P.C₁ * P.δ ^ (-10 * P.ν)) = Real.log P.C₁ - 10 * P.ν * Real.log P.δ := by
    rw [Real.log_mul hC₁.ne' (Real.rpow_pos_of_pos hδ _).ne', Real.log_rpow hδ]; ring
  have h1 : Real.exp (G.order * (Real.log P.C₁ - 10 * P.ν * Real.log P.δ)) =
      (P.C₁ * P.δ ^ (-10 * P.ν)) ^ G.order := by
    rw [Real.exp_nat_mul, ← hlog, Real.exp_log hpos]
  rw [Real.exp_add, h1, Real.rpow_def_of_pos hL, Real.rpow_def_of_pos hL]
  have : (-P.η ^ 6 * (G.molecule.rho + hinges) - ((R : ℝ) - 1) * (1 / 4 + 1 / 50)) * Real.log P.L =
      Real.log P.L * (-P.η ^ 6 * (G.molecule.rho + hinges)) +
        Real.log P.L * (-((R : ℝ) - 1) * (1 / 4 + 1 / 50)) := by ring
  rw [this, Real.exp_add]
  ring

end WaveTurbulence.LGSpine.Cover
