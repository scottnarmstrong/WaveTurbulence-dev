/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Molecule.LowerTerminal

/-! # The retained lower child in scenario (II-e)

TARGET molecpl (2e): the other rung atom is precisely the outer child u23.
-/

public section
namespace WaveTurbulence.Molecpl
open TTree
variable {w : ℕ} (G : Garden w)

/-- A selected actual child of the lower joint occupies its unique retained outer slot. -/
theorem lower_child_retained {S : Finset (GBranch G.tree)} {a b q : GBranch G.tree}
    (hB : G.molecule.IsBlock S a b) (hCL : Mole.CLParentPattern G S a b) (hq : q ∈ S)
    (hn : q.1.2 ≠ []) (hp : GNode.parent q.toNode hn = b) :
    ∃ i : Fin 3, q.toNode = b.child i ∧ i ≠ 1 ∧
      ∀ t : Fin 3, t.succ ∈ Mole.internalPositions G S b ↔ t = i := by
  let i := q.1.2.getLast hn
  let x : GardenDart G := .inl (⟨q,hn⟩,true)
  have ha : G.molecule.atom x = b := hp
  have hin : i.succ ∈ Mole.internalPositions G S b :=
    (Mole.mem_internalPositions G).mpr ⟨x,ha,by
      change GNode.parent q.toNode hn ∈ S ∧ q ∈ S
      rw [hp]; exact ⟨hB.2.2.1,hq⟩,rfl⟩
  obtain ⟨k,hk,hslots⟩ := Mole.with_parent_joint_retained_child G hB.2.2.1
    hB.2.2.2.2.2.2.1 hB.2.2.2.2.2.2.2.1 hCL.2
  have hi := (hslots i).mp hin
  subst k
  refine ⟨i,?_,hk,hslots⟩
  have hh := (Mole.parent_child_eq_node q.toNode hn).symm
  rw [hp] at hh
  simpa only [GBranch.toNode] using hh

end WaveTurbulence.Molecpl
