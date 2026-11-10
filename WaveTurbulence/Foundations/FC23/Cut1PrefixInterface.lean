/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.FC23.FlowerClipping
public import WaveTurbulence.Foundations.FC23.ExtractionThresholds
public import WaveTurbulence.Foundations.FC23.PrefixTools
/-! The explicit FC3 family budget for the exact cut1-only frozen clause.
The high input budget is evaluated with L replaced by 1, so it is fixed before
L and may depend on the stage count and high profile constants. -/
@[expose] public section
set_option autoImplicit false
noncomputable section
open scoped Classical
namespace WaveTurbulence.FC23
open Set

def flowerRootBudget (Pm : ℕ) (P : WTParams) (p : ℕ) (ζ : ℤˣ) (n n' : Fin P.d → ℤ) : ℝ :=
  jbr (latticePoint P.L n - (ζ : ℤ) • latticePoint P.L n') ^ (-(4 * P.Lambda (p + 1) * Pm : ℝ))

def flowerLExponent (Pm : ℕ) (P : WTParams) (pat : Fin (2 * Pm) → FixPat) : ℝ :=
  (if ∀ j, pat j = .plain then 1 else 2) * (100 * P.d : ℝ) ^ 3 * Pm

end WaveTurbulence.FC23
