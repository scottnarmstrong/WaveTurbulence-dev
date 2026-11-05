/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Molecule.TypeIILocalCases
public import WaveTurbulence.Foundations.Molecule.BranchDescendants

/-! # The retained lower LP child excludes further selected descendants

TARGET molecpl (II-a)--(II-d): the lower leaf is exactly u23.
-/

public section
namespace WaveTurbulence.Molecpl
open TTree
variable {w : ℕ} (G : Garden w)

/-- The lower LP incidence occupies the unique retained outer child slot. -/
theorem lower_LP_retained {S : Finset (GBranch G.tree)} {a b : GBranch G.tree}
    (hB : G.molecule.IsBlock S a b) (hCL : Mole.CLParentPattern G S a b)
    (R : EndRungData G.molecule S a b) (hlp : LowerLP G R) :
    ∃ (l : GLeaf G.tree) (i j : Fin 3), G.mark l = none ∧
      l.toNode = b.child i ∧ (G.pair l).toNode = R.right.child j ∧ i ≠ 1 ∧
      ∀ t : Fin 3, t.succ ∈ Mole.internalPositions G S b ↔ t = i := by
  let x := G.molecule.mate (R.right_row.dart 2)
  have ha : G.molecule.atom x = b := R.right_row.neighbor_eq 2
  have hb : G.molecule.atom (G.molecule.mate x) = R.right := by
    dsimp [x]; rw [G.molecule.mate_mate]; exact R.right_row.atom_eq 2
  obtain ⟨l,i,j,hm,hl,hr,hpos,_⟩ := dart_leaf_pair_positions G hlp ha hb
  have hin : i.succ ∈ Mole.internalPositions G S b :=
    (Mole.mem_internalPositions G).mpr ⟨x,ha,by
      change G.molecule.atom x ∈ S ∧ G.molecule.atom (G.molecule.mate x) ∈ S
      rw [ha,hb]; exact ⟨hB.2.2.1,R.right_mem⟩,hpos⟩
  obtain ⟨k,hk,hslots⟩ := Mole.with_parent_joint_retained_child G hB.2.2.1
    hB.2.2.2.2.2.2.1 hB.2.2.2.2.2.2.2.1 hCL.2
  have hi := (hslots i).mp hin
  subst k
  exact ⟨l,i,j,hm,hl,hr,hk,hslots⟩

/-- No selected branching node lies strictly below the lower joint in the core cases. -/
theorem lower_LP_terminal {S : Finset (GBranch G.tree)} {a b : GBranch G.tree}
    (hB : G.molecule.IsBlock S a b) (hCL : Mole.CLParentPattern G S a b)
    (R : EndRungData G.molecule S a b) (hlp : LowerLP G R) :
    ∀ z ∈ S, b.toNode.IsDesc z.toNode → z = b := by
  obtain ⟨l,i,_j,_hm,hl,_hr,_hi,hslots⟩ := lower_LP_retained G hB hCL R hlp
  apply cl_terminal_branch G hB hCL hB.2.2.1
  intro t ht
  have he := (hslots t).mp ht
  subst t
  exact ⟨l,hl⟩

end WaveTurbulence.Molecpl
