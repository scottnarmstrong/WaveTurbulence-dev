/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.VdCB.ModelPhase
public import WaveTurbulence.Foundations.VdCB.FiniteSums
public import WaveTurbulence.Foundations.VdCB.ExponentCoordinates

/-!
# Quantitative exponent pairs for decreasing-power phase profiles

For every fixed model exponent `s>0`, the derivative order, perturbation
allowance and estimate constant are chosen before the scales, phase and
summation interval. Thus no sum estimate is a field of the phase class.
The analytic A/B-closure theorems are separate results, not constructors
or assumptions hidden in this predicate.
-/

public section

namespace WaveTurbulence.VdCB

/-- The quantitative exponent-pair property. The constants and derivative
order depend on `s,κ,λ` only; the bound is uniform in the model perturbation,
scales `F≥N≥1` and all subintervals of `[N,2N]`. -/
@[expose] def IsExponentPair (κ lam : ℝ) : Prop :=
  AdmissibleCoordinates (κ, lam) ∧
    ∀ s : ℝ, 0 < s → ∃ R : ℕ, 1 ≤ R ∧ ∃ δ : ℝ, 0 < δ ∧ ∃ C : ℝ, 0 < C ∧
      ∀ (N F : ℝ) (f : ℝ → ℝ) (a b : ℝ),
        1 ≤ N → N ≤ F → HasPowerProfile f N F s R δ → N ≤ a → a ≤ b → b ≤ 2 * N →
          ‖exponentialSum f a b‖ ≤ C * (F / N) ^ κ * N ^ lam

/-- The trivial exponent pair, from counting the actual lattice interval. -/
theorem isExponentPair_zero_one : IsExponentPair 0 1 := by
  refine ⟨?_, ?_⟩
  · norm_num [AdmissibleCoordinates]
  · intro s _hs
    refine ⟨1, by norm_num, 1, by norm_num, 2, by norm_num, ?_⟩
    intro N F f a b hN _hF _hprofile ha hab hb
    simpa only [Real.rpow_zero, Real.rpow_one, mul_one] using
      norm_exponentialSum_le_two_mul hN ha hab hb f

end WaveTurbulence.VdCB
