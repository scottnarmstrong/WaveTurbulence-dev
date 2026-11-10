/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.Spine.AnchorTypes
public import WaveTurbulence.Foundations.Spine.ExplicitCoherentApps
public import WaveTurbulence.Foundations.Spine.CoherentConjugacyData
/-! Exported literal source interfaces for LG-SPINE consumers and producer packets.
No theorem is assumed here, and no arbitrary approximation functions occur in these input types.
The full minimal conjunction is added only after every source interface is stated. -/
@[expose] public section
open WaveTurbulence.Induct
set_option autoImplicit false
namespace WaveTurbulence.LGSpine
open MeasureTheory Set Finset
open scoped ENNReal Classical

/-- TARGET Prop 6.2, L1112–1117 (layerregest7–8), with the explicit uniform-layer approximation
(regref1-3), L1156–1160: RegCpl.app. The regular-couple sum uses its unique well-formed structure
code (TARGET propstructure; proved REG-STRUCT). Non-dominant app terms are zero by definition.
Standing input hypothesis: TARGET L951, with Lambda replaced by 40d, exactly as in B2.1/B2.2.
This is the exported L3 statement; it has no free approximation-family argument. -/
abbrev CoherentTaylorGate : Prop := WTPrefix fun P =>
  ∀ p : ℕ, p < P.D → ∀ R : ℕ → Mom P.d → ℝ,
    (∀ r ≤ p, InputRemainder P (R r) r) →
  ∀ n : ℕ, n ≤ P.N (p + 1) ^ 4 → ∀ t ∈ Icc (p : ℝ) (p + 1), ∀ k : Mom P.d,
    ‖(∑ᶠ (Q : RegCpl) (_ : Q.wf = true ∧ Q.size = 2 * n),
        Q.app P.δ p (inputsF P R p) t t k) -
      (wkeTaylorTerm (P.φ (P.δ * p)) P.δ p n t k : ℂ)‖ ≤
      P.C₁ * (P.C₁ * P.δ) ^ n * jbr k ^ (-(30 * P.d : ℝ)) *
        P.L ^ (-(P.theta (p + 1) + 4 * P.theta p) / 5)

end WaveTurbulence.LGSpine
