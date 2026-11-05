/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Molecule.LeafAncestorParent
public import WaveTurbulence.Foundations.Molecule.LowerTerminal

/-! # Producing actual unit-twist placements from core vines

TARGET twist: u23 is an outer child leaf, and its paired leaf u0 is
outside the lower subtree. Both facts are proved from the vine premises.
-/

public section
namespace WaveTurbulence.Twist
open TTree
variable {w : ℕ} (G : Garden w)

/-- Concrete placement data for the subtree exchange, including actual paired leaves. -/
structure CorePlacement where
  lower : GBranch G.tree
  retained : GLeaf G.tree
  nonroot : lower.1.2 ≠ []
  paired_nonroot : (G.pair retained).1.2 ≠ []
  keep : Fin 3
  unmarked : G.mark retained = none
  child : retained.toNode = lower.child keep
  outer : keep ≠ 1
  paired_outside : ¬ lower.toNode.IsDesc (G.pair retained).toNode

/-- A type-I CL vine supplies the actual unit-twist placement. -/
theorem typeI_corePlacement {S : Finset (GBranch G.tree)} {a b : GBranch G.tree}
    (hV : G.molecule.IsVine .I S a b) (hCL : Mole.CLParentPattern G S a b) :
    ∃ P : CorePlacement G, P.lower = b := by
  obtain ⟨l,i,j,hm,hl,hr,hi⟩ := Molecpl.typeI_leaf_pair G hV hCL
  have hout : ¬ b.toNode.IsDesc (G.pair l).toNode := by
    intro hd
    have hba := branch_desc_leaf_parent G hr hd
    have hlen := hba.2.length_le
    have hab := Mole.cl_parent_strict_descendant G hV.1 hCL
    dsimp [GBranch.toNode] at hlen
    omega
  have hpair : (G.pair l).1.2 ≠ [] := by
    change (G.pair l).toNode.1.2 ≠ []
    rw [hr]
    exact Mole.child_nonroot G _ _
  exact ⟨⟨b,l,hCL.2.choose,hpair,i,hm,hl,hi,hout⟩,rfl⟩

/-- A core type-II local placement supplies the actual unit-twist placement. -/
theorem typeII_corePlacement {S : Finset (GBranch G.tree)} {a b : GBranch G.tree}
    (hV : G.molecule.IsVine .II S a b) (hCL : Mole.CLParentPattern G S a b)
    (R : Molecpl.EndRungData G.molecule S a b) (hlp : Molecpl.LowerLP G R) :
    ∃ P : CorePlacement G, P.lower = b := by
  obtain ⟨l,i,j,hm,hl,hr,hi,_⟩ := Molecpl.lower_LP_retained G hV.1 hCL R hlp
  have hout := child_leaf_outside_of_terminal G R.right_mem R.right_ne_lower
    (Molecpl.lower_LP_terminal G hV.1 hCL R hlp) hr
  have hpair : (G.pair l).1.2 ≠ [] := by
    change (G.pair l).toNode.1.2 ≠ []
    rw [hr]
    exact Mole.child_nonroot G _ _
  exact ⟨⟨b,l,hCL.2.choose,hpair,i,hm,hl,hi,hout⟩,rfl⟩

/-- The two insertion slots have opposite root signs, derived from the paired outer leaf. -/
theorem CorePlacement.hole_signs (P : CorePlacement G) :
    nodeSign G.sig (commonOutsideLeaf G P.lower (G.pair P.retained) P.paired_outside).1 =
      -nodeSign G.sig (collapsedRoot G P.lower).1 := by
  have hp := G.pair_sign P.retained (Garden.pair_ne_of_unmarked P.unmarked)
  have hc : G.sign P.retained.toNode = G.sign P.lower.toNode := by
    rw [P.child]
    exact Mole.outer_child_sign G P.lower P.keep P.outer
  change nodeSign G.sig (G.pair P.retained).1 = -nodeSign G.sig P.lower.1
  change nodeSign G.sig (G.pair P.retained).1 = -nodeSign G.sig P.retained.1 at hp
  change nodeSign G.sig P.retained.1 = nodeSign G.sig P.lower.1 at hc
  rw [hp,hc]

end WaveTurbulence.Twist
