/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Molecule.VineMaskCardinality
import Mathlib.Tactic

/-! # Proper subsets of zero-extra-rung vine cores -/

public section
namespace WaveTurbulence.Vine
open Finset
variable {V D : Type*} [DecidableEq V] [Fintype D]

/-- The finite block tables consist of the full mask and masks with two,
three or five selected atoms. This statement concerns counts only. -/
theorem core_block_mask_sizes (X : VineType) :
    ∀ m ∈ coreMaskCandidates X .block,
      m=List.replicate X.template.n 1 ∨ m.sum=2 ∨ m.sum=3 ∨ m.sum=5 := by
  cases X <;> decide

/-- Every proper actual block in an unexpanded vine has two, three or five
atoms. This follows from the checked masks of the actual induced subgroup. -/
theorem base_proper_block_card {M : Molecule V D} {X : VineType}
    {S : Finset V} {a b : V} (R : VineRealization M X S a b)
    (hk : R.k=List.replicate X.template.slots.length 0)
    {A : Finset V} {x y : V} (hAS : A ⊆ S) (hA : M.IsBlock A x y) (hne : A ≠ S) :
    A.card=2 ∨ A.card=3 ∨ A.card=5 := by
  have hm := base_block_mask_exhaustive R hk hAS hA
  have hc := R.base_mask_sum hk hAS
  rcases core_block_mask_sizes X _ hm with hfull | h2 | h3 | h5
  · exact False.elim (hne (R.base_eq_of_full_mask hk hAS hfull))
  · exact Or.inl (hc.symm.trans h2)
  · exact Or.inr (Or.inl (hc.symm.trans h3))
  · exact Or.inr (Or.inr (hc.symm.trans h5))

/-- In the core types without a proper three/five-atom block, every
proper actual block is a single double-bond-sized set. -/
theorem base_proper_block_card_two {M : Molecule V D} {X : VineType}
    (hX : X=.I ∨ X=.II ∨ X=.III ∨ X=.V ∨ X=.VI ∨ X=.VIII)
    {S : Finset V} {a b : V} (R : VineRealization M X S a b)
    (hk : R.k=List.replicate X.template.slots.length 0)
    {A : Finset V} {x y : V} (hAS : A ⊆ S) (hA : M.IsBlock A x y) (hne : A ≠ S) :
    A.card=2 := by
  have hm := base_block_mask_exhaustive R hk hAS hA
  have hc := R.base_mask_sum hk hAS
  have htable : ∀ m ∈ coreMaskCandidates X .block,m=List.replicate X.template.n 1 ∨ m.sum=2 := by
    rcases hX with rfl | rfl | rfl | rfl | rfl | rfl <;> decide
  rcases htable _ hm with hfull | h2
  · exact False.elim (hne (R.base_eq_of_full_mask hk hAS hfull))
  · exact hc.symm.trans h2

end WaveTurbulence.Vine
