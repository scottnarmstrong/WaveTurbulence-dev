/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.FC23.FlowerClipping
public import WaveTurbulence.Foundations.FC23.Cut1ScaleBound
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

/-- The approved unsliced uniform-family interface with its explicit
pre-extraction budget. It contains no cut1 estimate, convergence or polynomial
extraction premise. Production of this analytic bound is the remaining FC3 task. -/
def FC23UniformCut1At (C : ℕ → ℝ) (U : WTParams → ℕ → ℝ) (Pm : ℕ) (P : WTParams) : Prop :=
  1 / 2 < P.γ → ∀ p : ℕ, p < P.D → ∀ R : ℕ → Mom P.d → ℝ, RemainderBound P R p →
    ∀ t ∈ Ioo (p : ℝ) (p + 1), ∀ s ∈ Ioo (p : ℝ) t, ∀ n n' : Fin P.d → ℤ, ∀ ζ : ℤˣ,
    ∀ N ≤ P.N (p + 1) ^ 4, ∀ (kind : FlowerKind) (pat : Fin (2 * Pm) → FixPat)
      (dagger : Option (Fin (2 * Pm) → Fin 3 → Mom P.d)) (j : ℕ),
    FC23UniformFlowerFamily P (inputsF P R) p N kind pat dagger ζ t s n n'
      (2 ^ j * P.L) ((2 ^ j * P.L) / (4 * (2 * N + 1 : ℕ)))
      (fun _ => extractionRadius (40 * P.d) N (C P.d) (U {P with L := 1} p) (2 ^ j * P.L))
      (flowerRootBudget Pm P p ζ n n' *
        P.L ^ (flowerLExponent Pm P pat - ((40 * P.d) * (2 * Pm) : ℕ) - (2 * Pm : ℕ)) *
        P.δ ^ (8 * P.ν * N))

/-- Exactly the cut1-present, cut2-absent flower clause of frozen v3. -/
def FC23Cut1At (Pm : ℕ) (P : WTParams) : Prop :=
  1 / 2 < P.γ → ∀ p : ℕ, p < P.D → ∀ R : ℕ → Mom P.d → ℝ, RemainderBound P R p →
    ∀ t ∈ Ioo (p : ℝ) (p + 1), ∀ s ∈ Ioo (p : ℝ) t, ∀ n n' : Fin P.d → ℤ, ∀ ζ : ℤˣ,
    ∀ N ≤ P.N (p + 1) ^ 4, ∀ (kind : FlowerKind) (pat : Fin (2 * Pm) → FixPat)
      (dagger : Option (Fin (2 * Pm) → Fin 3 → Mom P.d)) (j : ℕ),
    ‖flowerSumP P (inputsF P R) p N kind pat dagger (some j) none ζ t s n n'‖ ≤
      jbr (latticePoint P.L n - (ζ : ℤ) • latticePoint P.L n') ^
        (-(4 * P.Lambda (p + 1) * Pm : ℝ)) *
      P.L ^ ((if ∀ j, pat j = .plain then 1 else 2) * (100 * P.d : ℝ) ^ 3 * Pm) *
      P.δ ^ (2 * P.ν * N) * (2 ^ j * P.L) ^ (-(80 * P.d * Pm : ℝ))
end WaveTurbulence.FC23
