/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Molecule.TypeIParent

/-!
# The leaf-pair bond of an actual type-I CL vine

TARGET molecpl (1). One of the two incidences at the lower joint is its
parent edge. The other cannot be a child edge without making a tree cycle,
so it is precisely the paired-leaf bond in the source scenarios.
-/

public section
namespace WaveTurbulence.Molecpl
open TTree Finset
variable {w : ℕ} (G : Garden w)

/-- The remaining internal bond is a paired pair of actual child leaves;
the lower leaf occupies an outer child slot, as required for u23. -/
theorem typeI_leaf_pair {S : Finset (GBranch G.tree)} {a b : GBranch G.tree}
    (hV : G.molecule.IsVine .I S a b) (hCL : Mole.CLParentPattern G S a b) :
    ∃ (l : GLeaf G.tree) (i j : Fin 3), G.mark l = none ∧
      l.toNode = b.child i ∧ (G.pair l).toNode = a.child j ∧ i ≠ 1 := by
  classical
  obtain ⟨hn,hp⟩ := typeI_parent G hV hCL
  obtain ⟨R⟩ := typeI_twoIncidences G.molecule hV
  let Q := R.mates
  let x0 : GardenDart G := .inl (⟨b,hn⟩,false)
  have he : ∃ i : Fin 2, Q.dart i ≠ x0 := by
    by_contra! h
    have hi := Q.injective ((h 0).trans (h 1).symm)
    exact (by decide : (0:Fin 2) ≠ 1) hi
  obtain ⟨i,hi⟩ := he
  have ha := Q.atom_eq i
  have hb := Q.neighbor_eq i
  have hlen := congrArg (fun c : GBranch G.tree => c.1.2.length) hp
  change b.1.2.dropLast.length = a.1.2.length at hlen
  rw [List.length_dropLast] at hlen
  have hbn := List.length_pos_of_ne_nil hn
  cases hx : Q.dart i with
  | inl c =>
    rcases c with ⟨c,side⟩
    cases side
    · rw [hx] at ha
      change c.1 = b at ha
      have hc : c = ⟨b,hn⟩ := Subtype.ext ha
      exact (hi (hx.trans (congrArg (fun t => (Sum.inl (t,false):GardenDart G)) hc))).elim
    · rw [hx] at ha hb
      have hpa := congrArg (fun c : GBranch G.tree => c.1.2.length) ha
      have hcb := congrArg (fun c : GBranch G.tree => c.1.2.length) hb
      change c.1.1.2.dropLast.length = b.1.2.length at hpa
      change c.1.1.2.length = a.1.2.length at hcb
      rw [List.length_dropLast] at hpa
      have hcpos := List.length_pos_of_ne_nil c.2
      omega
  | inr l =>
    rw [hx] at ha hb
    let k := l.1.1.2.getLast l.2.2.1
    let j := (G.pair l.1).1.2.getLast l.2.2.2
    have hkp : Mole.dartPosition G (.inr l) = k.succ := rfl
    change GNode.parent l.1.toNode l.2.2.1 = b at ha
    change GNode.parent (G.pair l.1).toNode l.2.2.2 = a at hb
    have hq : l.1.toNode = b.child k := by
      rw [← ha]
      exact (Mole.parent_child_eq_node l.1.toNode l.2.2.1).symm
    have hq' : (G.pair l.1).toNode = a.child j := by
      rw [← hb]
      exact (Mole.parent_child_eq_node (G.pair l.1).toNode l.2.2.2).symm
    obtain ⟨kept,hkept,hslots⟩ := Mole.with_parent_joint_retained_child G hV.1.2.2.1
      hV.1.2.2.2.2.2.2.1 hV.1.2.2.2.2.2.2.2.1 hCL.2
    have hIn : G.molecule.InGroup S (.inr l) := by
      change GNode.parent l.1.toNode l.2.2.1 ∈ S ∧ GNode.parent (G.pair l.1).toNode l.2.2.2 ∈ S
      rw [ha,hb]
      exact ⟨hV.1.2.2.1,hV.1.2.1⟩
    have hk : k.succ ∈ Mole.internalPositions G S b :=
      (Mole.mem_internalPositions G).mpr ⟨.inr l,ha,hIn,hkp⟩
    have hke : k = kept := (hslots k).mp hk
    exact ⟨l.1,k,j,l.2.1,hq,hq',fun hk1 => hkept (hke.symm.trans hk1)⟩

end WaveTurbulence.Molecpl
