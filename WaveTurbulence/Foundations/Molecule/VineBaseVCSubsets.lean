/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Molecule.VineBaseSubsetSizes
public import WaveTurbulence.Foundations.Molecule.VineMaskBranching
import Mathlib.Tactic

/-! # Proper VC subsets of all eight zero-extra-rung cores -/

public section
namespace WaveTurbulence.Vine
open Finset
variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]

/-- Only core VII admits a five-atom proper block mask, and that mask
selects exactly the explicitly listed side piece. -/
theorem core_five_mask (X : VineType) :
    ∀ m ∈ coreMaskCandidates X .block,m.sum=5 → X=.VII ∧
      m=coreMaskVector .VII (membershipMask ({4,5,6,7,8} : Finset ℕ)) := by
  cases X <;> decide

/-- A proper VC in any unexpanded core has only two or three atoms. -/
theorem base_proper_VC_card {M : Molecule V D} {X : VineType}
    {S : Finset V} {a b : V} (R : VineRealization M X S a b)
    (hk : R.k=List.replicate X.template.slots.length 0)
    {A : Finset V} {x y : V} (hAS : A ⊆ S) (hVC : IsVC M A x y) (hne : A ≠ S) :
    A.card=2 ∨ A.card=3 := by
  rcases base_proper_block_card R hk hAS hVC.1 hne with h2 | h3 | h5
  · exact Or.inl h2
  · exact Or.inr h3
  · have hm := base_block_mask_exhaustive R hk hAS hVC.1
    have hsum := R.base_mask_sum hk hAS
    obtain ⟨hX,hmask⟩ := core_five_mask X _ hm (hsum.trans h5)
    subst X
    have himage := R.base_image_eq_of_mask hk hAS ({4,5,6,7,8} : Finset ℕ) (by decide) hmask
    exact False.elim (coreVII_five_not_isVC R hk hAS himage hVC)

/-- TARGET subsetvc, zero-extra-rung VC case: every proper VC inside any
of the eight base vines is one double bond or two concatenated double bonds.
The excluded five-atom degree mask is rejected using its actual neighbors. -/
theorem base_proper_VC_doubleChain {M : Molecule V D} {X : VineType}
    {S : Finset V} {a b : V} (R : VineRealization M X S a b)
    (hk : R.k=List.replicate X.template.slots.length 0)
    {A : Finset V} {x y : V} (hAS : A ⊆ S) (hVC : IsVC M A x y) (hne : A ≠ S) :
    DoubleChain M A x y 1 ∨ DoubleChain M A x y 2 := by
  have hc := base_proper_VC_card R hk hAS hVC hne
  obtain ⟨_hB,n,hC⟩ := hVC
  have hD := chain_doubleChain_of_card_lt_four hC (by omega)
  have hcount := doubleChain_card hD
  have hn : n=1 ∨ n=2 := by omega
  rcases hn with rfl | rfl
  · exact Or.inl hD
  · exact Or.inr hD

end WaveTurbulence.Vine
