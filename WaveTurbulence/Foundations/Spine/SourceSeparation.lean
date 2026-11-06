/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.WaveB.MoleculeStatements
/-! The separated-factor assertion of TARGET Prop 6.1, for a fixed explicit source approximation.
The approximation itself is never a free witness in a spine input. -/
@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.LGSpine
open Set
open scoped ENNReal

/-- TARGET L1103–1110, (layerregest4–6). The momentum factors are real, as in regref1-3–4;
complex special-subset coefficients are included in the time factors. -/
def SourceSeparated (P : WTParams) (n W : ℕ) (B : Set (Fin 2 → ℝ))
    (f : (Fin 2 → ℝ) → Mom P.d → ℂ) : Prop :=
  ∃ (m : ℕ) (J : Fin m → (Fin 2 → ℝ) → ℂ) (M : Fin m → Mom P.d → ℝ),
    m ≤ 2 ^ n ∧
    (∀ ts ∈ B, ∀ k, f ts k = ∑ i, (P.δ ^ n : ℂ) * J i ts * (M i k : ℂ)) ∧
    (∀ i, XNorm00Restr (V := Unit) (1 - P.η) B Set.univ (fun ts _ => J i ts) ≤
      ENNReal.ofReal (P.C₁ * P.C₁ ^ n)) ∧
    ∀ i, SNormR (30 * P.d) W (M i) ≤ ENNReal.ofReal (P.C₁ * P.C₁ ^ n)

end WaveTurbulence.LGSpine
