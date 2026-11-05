/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Molecule.TypeIAtomSet

/-!
# The actual parent edge of an oriented type-I CL vine

TARGET molecpl (1). The lower joint's internal parent must be the upper
joint, since the vine has only those two atoms and a tree has no self parent.
-/

public section
namespace WaveTurbulence.Molecpl
open TTree Finset
variable {w : ℕ} (G : Garden w)

/-- The lower joint of an actual type-I CL vine is an immediate child of the upper joint. -/
theorem typeI_parent {S : Finset (GBranch G.tree)} {a b : GBranch G.tree}
    (hV : G.molecule.IsVine .I S a b) (hCL : Mole.CLParentPattern G S a b) :
    ∃ (hn : b.1.2 ≠ []), GNode.parent b.toNode hn = a := by
  obtain ⟨hn,hp⟩ := hCL.2
  rw [typeI_atoms G.molecule hV] at hp
  rcases mem_insert.mp hp with hp | hp
  · exact ⟨hn,hp⟩
  · have he := congrArg (fun c : GBranch G.tree => c.1.2.length) (mem_singleton.mp hp)
    change b.1.2.dropLast.length = b.1.2.length at he
    rw [List.length_dropLast] at he
    have hpos := List.length_pos_of_ne_nil hn
    omega

/-- The exact positional child relation, retaining all three ordered child slots. -/
theorem typeI_child {S : Finset (GBranch G.tree)} {a b : GBranch G.tree}
    (hV : G.molecule.IsVine .I S a b) (hCL : Mole.CLParentPattern G S a b) :
    ∃ i : Fin 3, a.child i = b.toNode := by
  obtain ⟨hn,hp⟩ := typeI_parent G hV hCL
  exact ⟨b.1.2.getLast hn,hp ▸ Mole.parent_child_eq_node b.toNode hn⟩

end WaveTurbulence.Molecpl
