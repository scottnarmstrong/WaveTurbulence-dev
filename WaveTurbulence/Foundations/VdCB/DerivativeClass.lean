/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
public import Mathlib.Analysis.Calculus.ContDiff.Defs

/-!
# Quantitative derivative bounds on a dyadic interval

This is the literal derivative-comparability predicate used in individual
analytic estimates. Derivatives are taken within the closed source
interval, so no off-interval smooth extension is assumed. For exponent-pair
B-closure it must be supplemented by a stable model derivative profile:
absolute comparability alone also admits resonant positive-power phases.
-/

public section

namespace WaveTurbulence.VdCB

/-- Smoothness and actual derivative comparability up to order `R` on
`[N,2N]`. The bounds are `c F N⁻ʳ ≤ |f⁽ʳ⁾| ≤ C F N⁻ʳ` for `1≤r≤R`.
The natural domain assumptions `N≥1`, `F≥N`, `0<c≤C` are supplied by
consumers, rather than encoded as fallback branches in this predicate. -/
@[expose] def HasDerivativeBounds (f : ℝ → ℝ) (N F : ℝ) (R : ℕ) (c C : ℝ) : Prop :=
  ContDiffOn ℝ R f (Set.Icc N (2 * N)) ∧
    ∀ r : ℕ, 1 ≤ r → r ≤ R → ∀ x ∈ Set.Icc N (2 * N),
      c * F / N ^ r ≤ |iteratedDerivWithin r f (Set.Icc N (2 * N)) x| ∧
      |iteratedDerivWithin r f (Set.Icc N (2 * N)) x| ≤ C * F / N ^ r

/-- Restricting the derivative order retains the same quantitative bounds. -/
theorem HasDerivativeBounds.mono_order {f : ℝ → ℝ} {N F c C : ℝ} {R S : ℕ}
    (hf : HasDerivativeBounds f N F R c C) (hSR : S ≤ R) : HasDerivativeBounds f N F S c C := by
  refine ⟨hf.1.of_le (by exact_mod_cast hSR), ?_⟩
  intro r hr hSr x hx
  exact hf.2 r hr (hSr.trans hSR) x hx

end WaveTurbulence.VdCB
