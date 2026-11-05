/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.RegularAsymptotics.RA1Trees.TreeCoefficientSubsets

/-! # Exact cardinality of the original finite tree coefficient family -/

public section
noncomputable section
namespace WaveTurbulence.RegAsymp
open Finset Links MainCoef

/-- The actual chosen-node set has one element per original independent tree link. -/
theorem tree_coefficient_chosen_card (X : RegChain) (ζ : ℤˣ) :
    (ClassJR.chosenSet ((toJRc X).linksAt ζ (rootT ζ))).card=(X.treeLinks ζ).length := by
  rw [tree_chosenSet_coefficient_image,card_image_of_injective _ (treeCoefficientAddress_injective ζ)]
  unfold WaveTurbulence.chosenSet
  rw [List.toFinset_card_of_nodup (tree_chosen_nodup X ζ),List.length_map]

/-- The complete original coefficient family has exactly2^n members, including n0. -/
theorem tree_coefficient_subset_count (X : RegChain) (ζ : ℤˣ) :
    Fintype.card (ClassJR.chosenSet ((toJRc X).linksAt ζ (rootT ζ))).powerset =
      2^(X.treeLinks ζ).length := by
  rw [Fintype.card_coe,card_powerset,tree_coefficient_chosen_card]

end WaveTurbulence.RegAsymp
