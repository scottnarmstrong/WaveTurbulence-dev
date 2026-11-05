/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Molecule.GardenBondGeometry

/-! # Read actual garden darts as tree relations and paired leaves

TARGET defcplmol and molecpl. All witnesses refer to the actual garden.
-/

public section
namespace WaveTurbulence.Molecpl
open TTree
variable {w : ℕ} (G : Garden w)

/-- A paired pair of actual child leaves, with both ordered slots retained. -/
@[expose] def LeafPairAt (a b : GBranch G.tree) : Prop :=
  ∃ (l : GLeaf G.tree) (i j : Fin 3), G.mark l = none ∧
    l.toNode = a.child i ∧ (G.pair l).toNode = b.child j

/-- Every LP incidence supplies the paired child leaves stated in TARGET. -/
theorem dart_leaf_pair {x : GardenDart G} (h : ¬ IsPCDart G x)
    {a b : GBranch G.tree} (ha : G.molecule.atom x = a)
    (hb : G.molecule.atom (G.molecule.mate x) = b) : LeafPairAt G a b := by
  cases x with
  | inl c => exact (h ⟨c.1,c.2,rfl⟩).elim
  | inr l =>
    let i := l.1.1.2.getLast l.2.2.1
    let j := (G.pair l.1).1.2.getLast l.2.2.2
    change GNode.parent l.1.toNode l.2.2.1 = a at ha
    change GNode.parent (G.pair l.1).toNode l.2.2.2 = b at hb
    refine ⟨l.1,i,j,l.2.1,?_,?_⟩
    · rw [← ha]
      exact (Mole.parent_child_eq_node l.1.toNode l.2.2.1).symm
    · rw [← hb]
      exact (Mole.parent_child_eq_node (G.pair l.1).toNode l.2.2.2).symm

/-- The two possible orientations of an actual PC incidence. -/
theorem pc_dart_parent {x : GardenDart G} (h : IsPCDart G x)
    {a b : GBranch G.tree} (ha : G.molecule.atom x = a)
    (hb : G.molecule.atom (G.molecule.mate x) = b) :
    (∃ hn : a.1.2 ≠ [], GNode.parent a.toNode hn = b) ∨
      (∃ hn : b.1.2 ≠ [], GNode.parent b.toNode hn = a) := by
  obtain ⟨c,side,rfl⟩ := h
  cases side
  · change c.1 = a at ha
    subst a
    exact Or.inl ⟨c.2,hb⟩
  · change c.1 = b at hb
    subst b
    exact Or.inr ⟨c.2,ha⟩

end WaveTurbulence.Molecpl
