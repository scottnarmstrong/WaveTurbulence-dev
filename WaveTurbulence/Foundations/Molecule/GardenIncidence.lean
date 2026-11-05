/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Molecule.GardenMoleculeDefs
public import WaveTurbulence.Foundations.Molecule.MoleculeBasic
import Mathlib.Tactic

/-!
# Garden incidence positions 0–3

TARGET `defcplmol` L1297–L1302 and DH21-2 Proposition 6.4: the four
positions at a branching node are its parent position and its three child
positions. A dart is determined by its atom and this actual position.
-/

public section

namespace WaveTurbulence.Mole
open TTree
variable {w : ℕ} {tree : Fin w → TTree}

theorem parent_child_eq_node (a : GNode tree) (ha : a.1.2 ≠ []) :
    (GNode.parent a ha).child (a.1.2.getLast ha) = a := by
  apply Subtype.ext
  change (a.1.1,a.1.2.dropLast++[a.1.2.getLast ha]) = a.1
  rw [List.dropLast_append_getLast]

theorem node_eq_of_parent_and_last {a b : GNode tree} (ha : a.1.2 ≠ []) (hb : b.1.2 ≠ [])
    (hp : GNode.parent a ha = GNode.parent b hb)
    (hl : a.1.2.getLast ha = b.1.2.getLast hb) : a = b := by
  rw [← parent_child_eq_node a ha,← parent_child_eq_node b hb,hp,hl]

theorem branch_toNode_injective : Function.Injective (GBranch.toNode (tree := tree)) := by
  intro a b h
  exact Subtype.ext (congrArg (fun x : GNode tree => x.1) h)

theorem leaf_toNode_injective : Function.Injective (GLeaf.toNode (tree := tree)) := by
  intro a b h
  exact Subtype.ext (congrArg (fun x : GNode tree => x.1) h)

theorem branch_toNode_ne_leaf (b : GBranch tree) (l : GLeaf tree) : b.toNode ≠ l.toNode := by
  intro he
  have hval := congrArg Subtype.val he
  have hl : b.1.2 ∈ (tree b.1.1).leaves := hval.symm ▸ l.2
  exact TTree.not_mem_branching_of_mem_leaves _ hl b.2

/-- Actual parent/left/middle/right incidence code (0,1,2,3). -/
@[expose] def dartPosition (G : Garden w) : GardenDart G → Fin 4
  | .inl (_c,false) => 0
  | .inl (c,true) => (c.1.1.2.getLast c.2).succ
  | .inr l => (l.1.1.2.getLast l.2.2.1).succ

/-- The actual garden dart is determined by its atom and incidence position. -/
theorem atom_position_injective (G : Garden w) :
    Function.Injective (fun x : GardenDart G => (G.molecule.atom x,dartPosition G x)) := by
  rintro (⟨a,ba⟩|la) (⟨b,bb⟩|lb) he
  · have hA := congrArg Prod.fst he
    have hP := congrArg Prod.snd he
    cases ba <;> cases bb
    · change a.1 = b.1 at hA
      have hab : a = b := Subtype.ext hA
      subst b
      rfl
    · change (0 : Fin 4) = (b.1.1.2.getLast b.2).succ at hP
      exact False.elim (Fin.succ_ne_zero _ hP.symm)
    · change (a.1.1.2.getLast a.2).succ = (0 : Fin 4) at hP
      exact False.elim (Fin.succ_ne_zero _ hP)
    · change GNode.parent a.1.toNode a.2 = GNode.parent b.1.toNode b.2 at hA
      change (a.1.1.2.getLast a.2).succ = (b.1.1.2.getLast b.2).succ at hP
      have hn := node_eq_of_parent_and_last a.2 b.2 hA (Fin.succ_inj.mp hP)
      have hab : a = b := Subtype.ext (branch_toNode_injective hn)
      subst b
      rfl
  · have hA := congrArg Prod.fst he
    have hP := congrArg Prod.snd he
    cases ba
    · change (0 : Fin 4) = (lb.1.1.2.getLast lb.2.2.1).succ at hP
      exact False.elim (Fin.succ_ne_zero _ hP.symm)
    · change GNode.parent a.1.toNode a.2 = GNode.parent lb.1.toNode lb.2.2.1 at hA
      change (a.1.1.2.getLast a.2).succ = (lb.1.1.2.getLast lb.2.2.1).succ at hP
      have hn := node_eq_of_parent_and_last a.2 lb.2.2.1 hA (Fin.succ_inj.mp hP)
      exact False.elim (branch_toNode_ne_leaf a.1 lb.1 hn)
  · have hA := congrArg Prod.fst he
    have hP := congrArg Prod.snd he
    cases bb
    · change (la.1.1.2.getLast la.2.2.1).succ = (0 : Fin 4) at hP
      exact False.elim (Fin.succ_ne_zero _ hP)
    · change GNode.parent la.1.toNode la.2.2.1 = GNode.parent b.1.toNode b.2 at hA
      change (la.1.1.2.getLast la.2.2.1).succ = (b.1.1.2.getLast b.2).succ at hP
      have hn := node_eq_of_parent_and_last la.2.2.1 b.2 hA (Fin.succ_inj.mp hP)
      exact False.elim (branch_toNode_ne_leaf b.1 la.1 hn.symm)
  · have hA := congrArg Prod.fst he
    have hP := congrArg Prod.snd he
    change GNode.parent la.1.toNode la.2.2.1 = GNode.parent lb.1.toNode lb.2.2.1 at hA
    change (la.1.1.2.getLast la.2.2.1).succ = (lb.1.1.2.getLast lb.2.2.1).succ at hP
    have hn := node_eq_of_parent_and_last la.2.2.1 lb.2.2.1 hA (Fin.succ_inj.mp hP)
    have hl : la = lb := Subtype.ext (leaf_toNode_injective hn)
    subst lb
    rfl

/-- Every atom in the actual garden molecule has degree at most four. -/
theorem garden_molecule_deg_le_four (G : Garden w) (v : GBranch G.tree) : G.molecule.deg v ≤ 4 := by
  have hinj : Function.Injective (fun x : {x : GardenDart G // x ∈ G.molecule.dartsAt v} => dartPosition G x.1) := by
    intro x y hxy
    apply Subtype.ext
    apply atom_position_injective G
    apply Prod.ext
    · exact ((mem_dartsAt G.molecule v x.1).mp x.2).trans ((mem_dartsAt G.molecule v y.1).mp y.2).symm
    · exact hxy
  have hh := Fintype.card_le_of_injective _ hinj
  simpa only [Fintype.card_coe,Fintype.card_fin,Molecule.deg] using hh

end WaveTurbulence.Mole
