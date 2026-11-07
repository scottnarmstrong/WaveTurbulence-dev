/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.Vine.A.VineOperationReindex
public import WaveTurbulence.Foundations.Vine.A.VineStateOrbits
/-! Projection of LF orbits to actual layered gardens respects enumeration
and rebasing at every reachable family state. -/
@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.VineA
open WaveTurbulence.Stage1 WaveTurbulence.LFTwist
variable {w p : ℕ} {kind : Bool} {ι κ : Type*} [Fintype ι] [Fintype κ]

/-- Changing family enumeration leaves the actual garden output set unchanged. -/
theorem allCoreOutputs_reindex (A : FamilyReconstruction w ι) (e : κ ≃ ι) :
    (stateReindex A e).allCoreOutputs (p := p) (kind := kind) = A.allCoreOutputs (p := p) (kind := kind) := by
  ext LG
  rw [congruent_layered_iff, congruent_layered_iff]
  constructor
  · rintro ⟨B, hB, he⟩
    have hb := congruent_reindex hB e.symm
    rw [stateReindex_symm] at hb
    exact ⟨stateReindex B e.symm, hb, he⟩
  · rintro ⟨B, hB, he⟩
    exact ⟨stateReindex B e, congruent_reindex hB e, he⟩

/-- Reachable states give the same set of actual layered garden outputs. -/
theorem congruent_allCoreOutputs_eq {A B : FamilyReconstruction w ι}
    (h : Congruent p kind A B) :
    A.allCoreOutputs (p := p) (kind := kind) = B.allCoreOutputs (p := p) (kind := kind) := by
  classical
  rw [← stateOrbit_image A, ← stateOrbit_image B, (stateOrbit_eq_iff A B).mpr h]

end WaveTurbulence.VineA
