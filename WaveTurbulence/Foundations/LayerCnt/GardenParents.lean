/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.LayerCnt.Interior
public import WaveTurbulence.Foundations.Molecule.LFTwist.BranchLayering
public import WaveTurbulence.Foundations.Molecule.GardenMoleculeAxioms

/-! # Parents in the molecule of a garden (TARGET layerlad, L1507; T.L1463)

Every atom of degree `4` of `𝕄(𝒢)` is a non-root branching node; its parent is adjacent by a PC bond, has
smaller depth, and (for a pre-layering) a layer at least as large. This is the monotonicity along parent chains
that TARGET uses implicitly.
-/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.LayerCnt
open TTree
variable {w : ℕ}

/-- The depth of a branching node (length of its address). -/
@[expose] def depthB (G : Garden w) (x : GBranch G.tree) : ℕ := x.1.2.length

theorem garden_parent_step (G : Garden w) {f : GBranch G.tree → ℕ}
    (hf : LFTwist.IsBranchPrelayering G f) (x : GBranch G.tree) (hx : 4 ≤ G.molecule.deg x) :
    ∃ d, G.molecule.atom d = x ∧
      depthB G (G.molecule.atom (G.molecule.mate d)) < depthB G x ∧
      f x ≤ f (G.molecule.atom (G.molecule.mate d)) := by
  by_cases hroot : x.1.2 = []
  · have := Mole.root_degree_le_three G x hroot
    omega
  · refine ⟨Sum.inl (⟨x, hroot⟩, false), rfl, ?_, ?_⟩
    · show (GNode.parent x.toNode hroot).1.2.length < x.1.2.length
      simp only [GNode.parent, GBranch.toNode]
      rw [List.length_dropLast]
      have := List.length_pos_of_ne_nil hroot
      omega
    · show f x ≤ f (GNode.parent x.toNode hroot)
      apply hf (GNode.parent x.toNode hroot) x (x.1.2.getLast hroot)
      apply Subtype.ext
      simp only [GBranch.toNode, GBranch.child, GNode.parent]
      exact Prod.ext rfl (List.dropLast_append_getLast hroot).symm

/-- A non-root branching node has a layer at most that of its parent. -/
theorem garden_parent_step_le (G : Garden w) {f : GBranch G.tree → ℕ}
    (hf : LFTwist.IsBranchPrelayering G f) (x : GBranch G.tree) (hx : x.1.2 ≠ []) :
    f x ≤ f (GNode.parent x.toNode hx) := by
  apply hf (GNode.parent x.toNode hx) x (x.1.2.getLast hx)
  apply Subtype.ext
  simp only [GBranch.toNode, GBranch.child, GNode.parent]
  exact Prod.ext rfl (List.dropLast_append_getLast hx).symm

end WaveTurbulence.LayerCnt
