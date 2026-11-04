/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.WeylSums.CubicChainPointwise

/-!
# Joint continuity of all cubic phase parameters

Fixed compact cutoff amplitudes give continuous dependence on both
quadratic times and all three linear modulations. This supplies genuine
compact-box integrability for the normal factors with third-time modulations.
-/

public section

namespace WaveTurbulence.Sumint

/-- Arbitrary continuous dependence of both times and all modulations preserves continuity. -/
theorem continuous_cubicLatticeSum_parameters {X : Type*} [TopologicalSpace X]
    {d : ℕ} {L : ℝ} (hL : 0 < L) (sel : Bool) (a b c : Mom d)
    (t s : X → ℝ) (ξ ζ ω : X → Mom d) (ht : Continuous t) (hs : Continuous s)
    (hξ : Continuous ξ) (hζ : Continuous ζ) (hω : Continuous ω) :
    Continuous (fun x => WeylSums.cubicLatticeSum L (t x) (s x) sel a b c (ξ x) (ζ x) (ω x)) := by
  let A := fun q : (Fin d → ℤ) × (Fin d → ℤ) × (Fin d → ℤ) =>
    ((WeylSums.latticeCutoff (latticePoint L q.1-a)*
      WeylSums.latticeCutoff (latticePoint L q.2.1-b)*
      WeylSums.latticeCutoff (latticePoint L q.2.2-c):ℝ):ℂ)
  have hA : (Function.support A).Finite := by
    simpa only [mul_one] using WeylSums.finite_support_cubic hL a b c (fun _ => 1)
  exact WeylSums.continuous_finite_amplitude_sum A hA
    (fun x q => t x*inner ℝ (latticePoint L q.1) (latticePoint L q.2.1)+
      s x*WeylSums.cubicQuadraticForm sel (latticePoint L q.1) (latticePoint L q.2.1) (latticePoint L q.2.2)+
      inner ℝ (ξ x) (latticePoint L q.1)+inner ℝ (ζ x) (latticePoint L q.2.1)+
      inner ℝ (ω x) (latticePoint L q.2.2)) (fun _ => by fun_prop)

end WaveTurbulence.Sumint
