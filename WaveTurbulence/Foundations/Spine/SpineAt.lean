/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.Spine.SpineInputs
/-! Literal fixed-parameter bodies of the exported L3+L4 gates. -/
@[expose] public section
open WaveTurbulence.Induct
set_option autoImplicit false
namespace WaveTurbulence.LGSpine
open MeasureTheory Set Finset
open scoped ENNReal Classical

/-- Exact body of CoherentTaylorGate at P; no premise is changed. -/
abbrev SourceCoherentTaylorAt (P : WTParams) : Prop :=
  ∀ p : ℕ, p < P.D → ∀ R : ℕ → Mom P.d → ℝ,
    (∀ r ≤ p, InputRemainder P (R r) r) →
  ∀ n : ℕ, n ≤ P.N (p + 1) ^ 4 → ∀ t ∈ Icc (p : ℝ) (p + 1), ∀ k : Mom P.d,
    ‖(∑ᶠ (Q : RegCpl) (_ : Q.wf = true ∧ Q.size = 2 * n),
        Q.app P.δ p (inputsF P R p) t t k) -
      (wkeTaylorTerm (P.φ (P.δ * p)) P.δ p n t k : ℂ)‖ ≤
      P.C₁ * (P.C₁ * P.δ) ^ n * jbr k ^ (-(30 * P.d : ℝ)) *
        P.L ^ (-(P.theta (p + 1) + 4 * P.theta p) / 5)

end WaveTurbulence.LGSpine
