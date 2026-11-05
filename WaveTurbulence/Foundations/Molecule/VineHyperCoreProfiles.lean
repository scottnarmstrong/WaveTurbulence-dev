/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Molecule.VineHyperCoreMasks
public import WaveTurbulence.Foundations.Molecule.VineCoreMaskMembership
import Mathlib.Tactic

/-! # The actual cap core in each possible hyper-block subset -/

public section
namespace WaveTurbulence.Vine

/-- The nonempty old-core selections allowed by a two-edge cut away from
the outer joints. Entries are literal label sets, with no claim that fresh
rung membership is already determined. -/
@[expose] def hyperCoreSets : VineType → List (Finset ℕ)
  | .I | .II | .III | .IV => []
  | .V => [{6,7,8},{4,5,6,7,8},{2,3,4,5,6,7,8}]
  | .VI => [{10,11,12},{8,9,10,11,12}]
  | .VII => [{4,5,6}]
  | .VIII => [{8,9,10},{6,7,8,9,10}]

/-- The checked finite vectors encode exactly the listed literal cap cores. -/
theorem core_hyper_masks_sets (X : VineType) : ∀ m ∈ coreMaskCandidates X .hyper,
    ∃ W ∈ hyperCoreSets X,m=coreMaskVector X (membershipMask W) := by
  cases X <;> decide

variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]

/-- TARGET subsetvc: the old atoms of an arbitrary-rung actual hyper-block
subset are exactly one of the explicitly listed cap cores. This is obtained
from source incidence and boundary data, not a cap-shape hypothesis. -/
theorem hyperBlock_core_profile (M : Molecule V D) (hM : M.IsMolecule)
    {X : VineType} {S A : Finset V} {a b x y : V}
    (R : VineRealization M X S a b) (hS : M.IsBlock S a b)
    (hAS : A ⊆ S) (hH : Mole.IsHyperBlock M A x y) :
    ∃ W ∈ hyperCoreSets X,∀ v ∈ S,R.f v<X.template.n → (v ∈ A ↔ R.f v ∈ W) := by
  have hm := hyperBlock_core_mask_exhaustive M hM R hS hAS hH
  obtain ⟨W,hW,he⟩ := core_hyper_masks_sets X _ hm
  exact ⟨W,hW,R.core_membership_profile hAS W he⟩

end WaveTurbulence.Vine
