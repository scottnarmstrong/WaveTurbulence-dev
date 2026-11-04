/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.WaveB.FrozenB1
import Mathlib.Tactic

/-!
# Translation of the geometric sumint phase

After removing the time modulation parameters, simultaneous translation
of the output time and every input time leaves the literal phase
unchanged, including the case (c) multipliers.
-/

public section

namespace WaveTurbulence.Sumint

/-- The source phase with its time modulation parameters set to zero. -/
@[expose] noncomputable def geometricPhase {d : ℕ} (D : SumintDatum d)
    (L γ δ η : ℝ) (x : D.S.VIdx → Fin d → ℤ) (r : Mom d) (t : ℝ)
    (τ : D.S.TVar → ℝ) : ℂ :=
  ({D with param := fun _ => 0} : SumintDatum d).phase L γ δ η x r t τ

/-- Simultaneous time translation removes all output-time dependence from the geometric integrand. -/
theorem geometricPhase_translate {d : ℕ} (D : SumintDatum d)
    (L γ δ η : ℝ) (x : D.S.VIdx → Fin d → ℤ) (r : Mom d) (t a : ℝ)
    (τ : D.S.TVar → ℝ) :
    geometricPhase D L γ δ η x r (t + a) (fun v => τ v + a) =
      geometricPhase D L γ δ η x r t τ := by
  simp only [geometricPhase, SumintDatum.phase, add_sub_add_right_eq_sub, zero_mul]

end WaveTurbulence.Sumint
