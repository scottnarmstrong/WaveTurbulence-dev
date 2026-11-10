/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.RegularAsymptotics.RA1Trees.TreeSpecialTransport

/-! # Original chosen-node subsets and coefficient subsets correspond bijectively -/

@[expose] public section
noncomputable section
namespace WaveTurbulence.RegAsymp
open Finset Links MainCoef

/-- The original finite chosen-node subset, placed at its coefficient sign root. -/
def treeCoefficientSubsetMap (X : RegChain) (ζ : ℤˣ)
    (Z : (WaveTurbulence.chosenSet (X.treeLinks ζ)).powerset) :
    (ClassJR.chosenSet ((toJRc X).linksAt ζ (rootT ζ))).powerset := by
  classical
  refine ⟨Z.val.image (treeCoefficientAddress ζ),?_⟩
  rw [tree_chosenSet_coefficient_image,mem_powerset]
  exact image_subset_image (mem_powerset.mp Z.property)

theorem treeCoefficientSubsetMap_injective (X : RegChain) (ζ : ℤˣ) :
    Function.Injective (treeCoefficientSubsetMap X ζ) := by
  intro Z W he
  apply Subtype.ext
  exact image_injective (treeCoefficientAddress_injective ζ) (congrArg Subtype.val he)

theorem treeCoefficientSubsetMap_surjective (X : RegChain) (ζ : ℤˣ) :
    Function.Surjective (treeCoefficientSubsetMap X ζ) := by
  classical
  intro Z
  have hZ : Z.val ∈ (WaveTurbulence.chosenSet (X.treeLinks ζ)).powerset.image
      (fun W => W.image (treeCoefficientAddress ζ)) := by
    simpa only [tree_chosenSet_coefficient_image,powerset_image] using Z.property
  obtain ⟨W,hW,hWZ⟩ := mem_image.mp hZ
  refine ⟨⟨W,hW⟩,?_⟩
  exact Subtype.ext hWZ

/-- Exact original and ClassJR subset enumerations, preserving all empty-order conventions. -/
def treeCoefficientSubsetEquiv (X : RegChain) (ζ : ℤˣ) :
    (WaveTurbulence.chosenSet (X.treeLinks ζ)).powerset ≃
      (ClassJR.chosenSet ((toJRc X).linksAt ζ (rootT ζ))).powerset :=
  Equiv.ofBijective (treeCoefficientSubsetMap X ζ)
    ⟨treeCoefficientSubsetMap_injective X ζ,treeCoefficientSubsetMap_surjective X ζ⟩

end WaveTurbulence.RegAsymp
