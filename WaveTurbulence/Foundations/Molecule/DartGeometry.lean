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
