/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Molecule.TwistSpliceSlots

/-! # The designated unit twist preserves core CL vine status

TARGET GAP.twistTable (T1): the connected expanded-template vine, its CL
orientation, and the internal retained leaf are all preserved.
-/

public section
namespace WaveTurbulence.Twist
open TTree
variable {w : ℕ} (G : Garden w) (P : CorePlacement G)

/-- A designated retained leaf excludes every source (II-e) witness in the same group. -/
theorem not_typeIIE_of_placement {S : Finset (GBranch G.tree)} {a : GBranch G.tree}
    (hB : G.molecule.IsBlock S a P.lower) (hCL : Mole.CLParentPattern G S a P.lower)
    (hP : IsPlacementAt G S P.lower P) :
    ¬ ∃ p ∈ S, ∃ q ∈ S, Molecpl.IsTypeIIE G a P.lower p q := by
  rintro ⟨_p,_hp,q,hq,hE⟩
  obtain ⟨hn,hparent⟩ := hE.2.1
  obtain ⟨i,hi,_houter,hslots⟩ := Molecpl.lower_child_retained G hB hCL hq hn hparent
  have he := (hP.2 i).mp ((hslots i).mpr rfl)
  have hnode : q.toNode = P.retained.toNode := by
    rw [hi,he]
    exact P.child.symm
  exact Mole.branch_toNode_ne_leaf q P.retained hnode

/-- The designated core vine remains a core CL vine in the actual twisted garden. -/
theorem isCoreCLVine_twistedAtoms {X : VineType} {S : Finset (GBranch G.tree)} {a : GBranch G.tree}
    (hcore : IsCoreCLVine G X S a P.lower) (hP : IsPlacementAt G S P.lower P) :
    IsCoreCLVine (unitTwistGarden G P) X (twistedAtoms G P S)
      (coreBranchEquiv G P a) (coreBranchEquiv G P P.lower) := by
  have hV := isVine_twistedAtoms G P hcore.1
  have hCL := clParentPattern_twistedAtoms G P hcore.1.1 hcore.2.1 hP
  have hat := reversePlacement_at_twistedAtoms G P hcore.1.1 hcore.2.1 hP
  refine ⟨hV,hCL,?_⟩
  rcases hcore.2.2 with hx | ⟨hx,_hnotE⟩
  · exact Or.inl hx
  · exact Or.inr ⟨hx,not_typeIIE_of_placement (unitTwistGarden G P) (reversePlacement G P) hV.1 hCL hat⟩

end WaveTurbulence.Twist
