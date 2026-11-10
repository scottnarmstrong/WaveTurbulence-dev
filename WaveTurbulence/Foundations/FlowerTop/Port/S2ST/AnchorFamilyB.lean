/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.FlowerTop.Port.TypeFamilyST
public import WaveTurbulence.Foundations.Spine.RootWeightOps
/-! R97: the both-member anchored family.

`typeProfilesAnchB` masks BOTH members of every anchored pair (the leaf's own tree or its partner's tree lies in
the anchor set `J`). `BoundedAnchB` and the leaf size exempt both members. With `J = ∅` everything is the plain
`TypeFamily` data (`toLeafFamilyAnchB_empty`, `boundedAnchB_empty_iff`). -/
@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.S2ST
open LGSpine MeasureTheory Set Finset
open scoped Classical

/-- Pair-type profiles, both-member convention: a leaf whose own tree or whose partner's tree is an anchor has
profile `1`. -/
noncomputable def typeProfilesAnchB {w d : ℕ} (J : Finset (Fin w)) (LG : LayeredGarden w)
    (h : ℕ → Fin w → Fin w → Mom d → ℝ) : LeafProfiles w d := fun a =>
  if (pairTrees LG.garden a).1 ∈ J ∨ (pairTrees LG.garden a).2 ∈ J then (fun _ => 1)
  else typeProfiles LG h a

theorem typeProfilesAnchB_leaf {w d : ℕ} (J : Finset (Fin w)) (LG : LayeredGarden w)
    (h : ℕ → Fin w → Fin w → Mom d → ℝ) (ℓ : GLeaf LG.garden.tree) :
    typeProfilesAnchB J LG h ℓ.1 =
      if ℓ.1.1 ∈ J ∨ (LG.garden.pair ℓ).1.1 ∈ J then (fun _ => 1)
      else h (LG.layer ℓ.toNode) ℓ.1.1 (LG.garden.pair ℓ).1.1 := by
  unfold typeProfilesAnchB
  rw [pairTrees_leaf, typeProfiles_leaf]

end WaveTurbulence.S2ST
