/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.WeylSums.BilinearPointwise

/-!
# Joint continuity of the bilinear time and spatial modulations

The landed single-time continuity theorem extends directly using the
same fixed finite cutoff amplitude. This supplies measurability for
source integrals whose linear modulations vary with their outer time.
-/

public section

namespace WaveTurbulence.Sumint

/-- Arbitrary continuous dependence of all bilinear phase parameters preserves continuity. -/
theorem continuous_bilinearLatticeSum_parameters {X : Type*} [TopologicalSpace X]
    {d : ℕ} {L : ℝ} (hL : 0 < L) (a b : Mom d)
    (s : X → ℝ) (ξ ζ : X → Mom d) (hs : Continuous s)
    (hξ : Continuous ξ) (hζ : Continuous ζ) :
    Continuous (fun x => WeylSums.bilinearLatticeSum L (s x) a b (ξ x) (ζ x)) := by
  let A := fun q : (Fin d → ℤ) × (Fin d → ℤ) =>
    ((WeylSums.latticeCutoff (latticePoint L q.1-a)*
      WeylSums.latticeCutoff (latticePoint L q.2-b):ℝ):ℂ)
  have hA : (Function.support A).Finite := by
    simpa only [mul_one] using WeylSums.finite_support_bilinear hL a b (fun _ => 1)
  exact WeylSums.continuous_finite_amplitude_sum A hA
    (fun x q => inner ℝ (latticePoint L q.1) (ξ x)+inner ℝ (latticePoint L q.2) (ζ x)+
      s x*inner ℝ (latticePoint L q.1) (latticePoint L q.2))
    (fun q => ((continuous_const.inner hξ).add (continuous_const.inner hζ)).add
      (hs.mul continuous_const))

end WaveTurbulence.Sumint
