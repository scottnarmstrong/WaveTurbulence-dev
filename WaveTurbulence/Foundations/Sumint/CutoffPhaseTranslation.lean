/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Sumint.CutoffPhaseSum
public import WaveTurbulence.Foundations.Sumint.PhaseModulation

/-!
# Exact simultaneous time translation of the actual cutoff phase sum

The inserted spatial cutoffs and input characters are independent of
the time variables. The already proved source phase translation thus
extracts precisely the same common output modulation from the full sum.
-/

public section
open MeasureTheory
namespace WaveTurbulence.Sumint

/-- Translating all native input times and the output time extracts exactly the original parameter modulation. -/
theorem cutoffPhaseSum_translate {d : ℕ} (D : SumintDatum d) (L γ δ η : ℝ)
    (p : D.S.VIdx → Fin d → ℝ) (ν : D.S.VIdx → Mom d) (r : Mom d) (t a : ℝ)
    (τ : D.S.TVar → ℝ) :
    cutoffPhaseSum D L γ δ η p ν r (t+a) (fun v => τ v+a) =
      Complex.exp ((Real.pi*(∑ v, D.param v)*a:ℝ)*Complex.I)*cutoffPhaseSum D L γ δ η p ν r t τ := by
  unfold cutoffPhaseSum
  simp_rw [phase_translate]
  rw [← tsum_mul_left]
  apply tsum_congr
  intro x
  ring

end WaveTurbulence.Sumint
