/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Molecule.OrientedEndRung

/-! # The second lower bond: a retained child or an actual leaf pair

TARGET molecpl (2). This separates (II-e) from the four core cases.
-/

public section
namespace WaveTurbulence.Molecpl
open TTree
variable {w : ℕ} (G : Garden w)

/-- A child paired to a selected internal neighbor is the retained outer lower child. -/
theorem lower_leaf_outer {S : Finset (GBranch G.tree)} {a b c : GBranch G.tree}
    (hB : G.molecule.IsBlock S a b) (hCL : Mole.CLParentPattern G S a b)
    (hc : c ∈ S) {l : GLeaf G.tree} {i j : Fin 3} (hm : G.mark l = none)
    (hl : l.toNode = b.child i) (hr : (G.pair l).toNode = c.child j) : i ≠ 1 := by
  have hn := Mole.child_nonroot G b i
  have hn' := Mole.child_nonroot G c j
  have hln : l.1.2 ≠ [] := by
    change l.toNode.1.2 ≠ []
    rw [hl]
    exact hn
  have hrn : (G.pair l).1.2 ≠ [] := by
    change (G.pair l).toNode.1.2 ≠ []
    rw [hr]
    exact hn'
  let x : GardenDart G := .inr ⟨l,hm,hln,hrn⟩
  have ha : G.molecule.atom x = b := by
    change GNode.parent l.toNode hln = b
    apply Subtype.ext
    change (l.1.1,l.1.2.dropLast) = b.1
    have hh : l.1 = (b.1.1,b.1.2 ++ [i]) := congrArg Subtype.val hl
    rw [hh]
    simp
  have hb : G.molecule.atom (G.molecule.mate x) = c := by
    change GNode.parent (G.pair l).toNode hrn = c
    apply Subtype.ext
    change ((G.pair l).1.1,(G.pair l).1.2.dropLast) = c.1
    have hh : (G.pair l).1 = (c.1.1,c.1.2 ++ [j]) := congrArg Subtype.val hr
    rw [hh]
    simp
  have hi : Mole.dartPosition G x = i.succ := by
    apply Fin.ext
    change (l.1.2.getLast hln).val+1 = i.val+1
    have hh := congrArg (fun n : GNode G.tree => n.1.2) hl
    change l.1.2 = b.1.2 ++ [i] at hh
    simp [hh]
  obtain ⟨k,hk,hslots⟩ := Mole.with_parent_joint_retained_child G hB.2.2.1
    hB.2.2.2.2.2.2.1 hB.2.2.2.2.2.2.2.1 hCL.2
  have hin : i.succ ∈ Mole.internalPositions G S b :=
    (Mole.mem_internalPositions G).mpr ⟨x,ha,by
      change G.molecule.atom x ∈ S ∧ G.molecule.atom (G.molecule.mate x) ∈ S
      rw [ha,hb]; exact ⟨hB.2.2.1,hc⟩,hi⟩
  exact fun he => hk (((hslots i).mp hin).symm.trans he)

end WaveTurbulence.Molecpl
