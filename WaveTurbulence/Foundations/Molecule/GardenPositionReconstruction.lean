/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Molecule.GardenSlots
import Mathlib.Tactic

/-!
# Recovering PC and LP data from the actual position codes

DH21-2 Proposition 6.4: code zero detects the parent position, and two
nonzero codes detect the paired child positions. These lemmas recover the
actual tree and pairing relations from the encoded directed multigraph.
-/

public section
namespace WaveTurbulence.Mole
open TTree
variable {w : ℕ} (G : Garden w)

/-- Position zero is exactly the child-end incidence of a PC bond. -/
theorem position_zero_iff (x : GardenDart G) :
    dartPosition G x = 0 ↔ ∃ c : {c : GBranch G.tree // c.1.2 ≠ []}, x = .inl (c,false) := by
  rcases x with ⟨c,b⟩ | l
  · cases b
    · exact ⟨fun _ => ⟨c,rfl⟩,fun _ => rfl⟩
    · constructor
      · intro h
        exact (Fin.succ_ne_zero _ h).elim
      · rintro ⟨c',he⟩
        cases he
  · constructor
    · intro h
      exact (Fin.succ_ne_zero _ h).elim
    · rintro ⟨c,he⟩
      cases he

/-- A zero/nonzero pair of codes recovers the actual parent-child relation. -/
theorem position_recovers_child (x : GardenDart G) (i : Fin 3)
    (hx : dartPosition G x = i.succ) (hm : dartPosition G (G.molecule.mate x) = 0) :
    (G.molecule.atom x).child i = (G.molecule.atom (G.molecule.mate x)).toNode := by
  obtain ⟨c,hc⟩ := (position_zero_iff G (G.molecule.mate x)).mp hm
  have he : x = .inl (c,true) := by
    have hh := congrArg G.molecule.mate hc
    rw [G.molecule.mate_mate] at hh
    exact hh
  subst x
  change (c.1.1.2.getLast c.2).succ = i.succ at hx
  have hi := Fin.succ_inj.mp hx
  change (GNode.parent c.1.toNode c.2).child i = c.1.toNode
  have hh := parent_child_eq_node (tree := G.tree) c.1.toNode c.2
  exact (congrArg (GNode.parent c.1.toNode c.2).child hi).symm.trans hh

/-- Two nonzero codes recover actual paired leaves and their child slots. -/
theorem positions_recovers_leaf_pair (x : GardenDart G) (i j : Fin 3)
    (hx : dartPosition G x = i.succ) (hm : dartPosition G (G.molecule.mate x) = j.succ) :
    ∃ l : GLeaf G.tree, l.toNode = (G.molecule.atom x).child i ∧
      (G.pair l).toNode = (G.molecule.atom (G.molecule.mate x)).child j := by
  rcases x with ⟨c,b⟩ | l
  · cases b
    · exact (Fin.succ_ne_zero i hx.symm).elim
    · exact (Fin.succ_ne_zero j hm.symm).elim
  · refine ⟨l.1,?_,?_⟩
    · change (l.1.1.2.getLast l.2.2.1).succ = i.succ at hx
      change l.1.toNode = (GNode.parent l.1.toNode l.2.2.1).child i
      have hh := parent_child_eq_node (tree := G.tree) l.1.toNode l.2.2.1
      exact hh.symm.trans (congrArg (GNode.parent l.1.toNode l.2.2.1).child (Fin.succ_inj.mp hx))
    · change ((G.pair l.1).1.2.getLast l.2.2.2).succ = j.succ at hm
      change (G.pair l.1).toNode = (GNode.parent (G.pair l.1).toNode l.2.2.2).child j
      have hh := parent_child_eq_node (tree := G.tree) (G.pair l.1).toNode l.2.2.2
      exact hh.symm.trans (congrArg (GNode.parent (G.pair l.1).toNode l.2.2.2).child (Fin.succ_inj.mp hm))

/-- Branching roots are detected as the atoms without a position-zero dart. -/
theorem branch_root_iff_no_zero (v : GBranch G.tree) :
    v.1.2 = [] ↔ ¬ ∃ x : GardenDart G, G.molecule.atom x = v ∧ dartPosition G x = 0 := by
  constructor
  · intro hv
    rintro ⟨x,hx,hp⟩
    obtain ⟨c,rfl⟩ := (position_zero_iff G x).mp hp
    exact c.2 (congrArg (fun b : GBranch G.tree => b.1.2) hx |>.trans hv)
  · intro hn
    by_contra hv
    exact hn ⟨.inl (⟨v,hv⟩,false),rfl,rfl⟩

end WaveTurbulence.Mole
