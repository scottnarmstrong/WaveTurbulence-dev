/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Molecule.ChildSigns
public import WaveTurbulence.Foundations.Molecule.VineDoublePairClosure

/-!
# Actual PC and LP bond geometry in gardens

TARGET defcplmol and molecpl. These facts interpret actual half-edges as
ordered parent-child relations or as paired child leaves. A fixed pair of
branching atoms supports at most one PC bond, since a tree has no cycles.
-/

public section
namespace WaveTurbulence.Molecpl
open TTree
variable {w : ℕ} (G : Garden w)

/-- The parent of a nonroot node has path length exactly one less. -/
theorem parent_length (n : GNode G.tree) (hn : n.1.2 ≠ []) :
    (GNode.parent n hn).1.2.length+1 = n.1.2.length := by
  change n.1.2.dropLast.length+1 = n.1.2.length
  rw [List.length_dropLast]
  have hh := List.length_pos_of_ne_nil hn
  omega

/-- A PC incidence is one of the actual branch-parent incidences. -/
@[expose] def IsPCDart (x : GardenDart G) : Prop :=
  ∃ c : {c : GBranch G.tree // c.1.2 ≠ []}, ∃ side : Bool, x = .inl (c,side)

/-- A PC bond is uniquely determined by its two ordered endpoint atoms. -/
theorem pc_dart_unique {x y : GardenDart G} (hx : IsPCDart G x) (hy : IsPCDart G y)
    (ha : G.molecule.atom x = G.molecule.atom y)
    (hb : G.molecule.atom (G.molecule.mate x) = G.molecule.atom (G.molecule.mate y)) : x = y := by
  obtain ⟨c,sc,rfl⟩ := hx
  obtain ⟨d,sd,rfl⟩ := hy
  cases sc <;> cases sd
  · have hc : c = d := Subtype.ext ha
    exact congrArg (fun z => (Sum.inl (z,false):GardenDart G)) hc
  · have h1 := congrArg (fun b : GBranch G.tree => b.1.2.length) ha
    have h2 := congrArg (fun b : GBranch G.tree => b.1.2.length) hb
    have hc := parent_length G c.1.toNode c.2
    have hd := parent_length G d.1.toNode d.2
    change c.1.1.2.length = (GNode.parent d.1.toNode d.2).1.2.length at h1
    change (GNode.parent c.1.toNode c.2).1.2.length = d.1.1.2.length at h2
    dsimp [GBranch.toNode, GNode.parent] at h1 h2 hc hd
    omega
  · have h1 := congrArg (fun b : GBranch G.tree => b.1.2.length) ha
    have h2 := congrArg (fun b : GBranch G.tree => b.1.2.length) hb
    have hc := parent_length G c.1.toNode c.2
    have hd := parent_length G d.1.toNode d.2
    change (GNode.parent c.1.toNode c.2).1.2.length = d.1.1.2.length at h1
    change c.1.1.2.length = (GNode.parent d.1.toNode d.2).1.2.length at h2
    dsimp [GBranch.toNode, GNode.parent] at h1 h2 hc hd
    omega
  · have hc : c = d := Subtype.ext hb
    exact congrArg (fun z => (Sum.inl (z,true):GardenDart G)) hc

/-- At least one incidence in any doubled pair is an LP incidence. -/
theorem doubled_has_lp {a b : GBranch G.tree} (R : Vine.TwoIncidences G.molecule a b) :
    ∃ i : Fin 2, ¬ IsPCDart G (R.dart i) := by
  by_contra! h
  have he := pc_dart_unique G (h 0) (h 1)
    ((R.atom_eq 0).trans (R.atom_eq 1).symm)
    ((R.neighbor_eq 0).trans (R.neighbor_eq 1).symm)
  exact (by decide : (0:Fin 2) ≠ 1) (R.injective he)

end WaveTurbulence.Molecpl
