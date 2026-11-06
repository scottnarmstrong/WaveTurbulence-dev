/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.Spine.WkeTaylor
public import WaveTurbulence.Foundations.Spine.PrefixMap
/-! The exact high-order Taylor bound is a proved input, not a new spine assumption. -/
@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.LGSpine
open Set
open scoped ENNReal

abbrev TaylorBoundAt (P : WTParams) : Prop :=
  ∀ p : ℕ, p < P.D → ∀ n : ℕ, ∀ t ∈ Icc (p : ℝ) (p + 1),
    SNormR (4 * P.Lambda (p + 1)) (4 * P.Lambda (p + 1))
      (wkeTaylorTerm (P.φ (P.δ * p)) P.δ p n t) ≤
      ENNReal.ofReal (P.C₂ * (P.C₁ * P.δ) ^ n)

theorem taylorBound_prefix : WTPrefix TaylorBoundAt :=
  prefix_map (fun _ h p hp => (h p hp).2.2) WkeTaylorGate.wkeTaylor

end WaveTurbulence.LGSpine
