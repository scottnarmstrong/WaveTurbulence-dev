/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.VdCB.DerivativeClass
public import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Stable decreasing-power phase profiles

The model is `f′(x)=(F/N)(x/N)^(-s)` with `s>0`. Its successive derivatives
have falling coefficients `(-s)(-s-1)…`. An absolute normalized error `δ`
is permitted in each of finitely many derivatives. This profile, rather
than bare derivative comparability, is used by the exponent-pair API.
The circle arc is treated separately through its explicit dual phase.
-/

public section

namespace WaveTurbulence.VdCB

/-- Coefficients of successive derivatives of `u^(-s)`. -/
@[expose] def powerDerivativeCoefficient (s : ℝ) : ℕ → ℝ
  | 0 => 1
  | r + 1 => powerDerivativeCoefficient s r * (-s - r)

/-- A derivative-controlled perturbation of the decreasing-power model,
with all smoothness and derivatives relative to the actual source interval. -/
@[expose] def HasPowerProfile (f : ℝ → ℝ) (N F s : ℝ) (R : ℕ) (δ : ℝ) : Prop :=
  ContDiffOn ℝ (R + 1) f (Set.Icc N (2 * N)) ∧
    ∀ r : ℕ, r ≤ R → ∀ x ∈ Set.Icc N (2 * N),
      |iteratedDerivWithin (r + 1) f (Set.Icc N (2 * N)) x -
        F / N ^ (r + 1) * powerDerivativeCoefficient s r * (x / N) ^ (-s - r)| ≤
          δ * F / N ^ (r + 1)

/-- Restricting a controlled profile to fewer derivatives. -/
theorem HasPowerProfile.mono_order {f : ℝ → ℝ} {N F s δ : ℝ} {R S : ℕ}
    (hf : HasPowerProfile f N F s R δ) (hSR : S ≤ R) : HasPowerProfile f N F s S δ := by
  refine ⟨hf.1.of_le (by exact_mod_cast Nat.add_le_add_right hSR 1), ?_⟩
  intro r hr x hx
  exact hf.2 r (hr.trans hSR) x hx

end WaveTurbulence.VdCB
