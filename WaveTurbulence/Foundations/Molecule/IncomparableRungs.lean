/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Molecule.IncidenceTriples
public import WaveTurbulence.Foundations.Molecule.LowerTerminal

/-! # Incomparable rung branches in scenarios (II-a) and (II-b)

TARGET molecpl (2a,b): derive incomparability from actual child leaves,
the retained lower leaf, and the CL descendant exclusions.
-/

public section
namespace WaveTurbulence.Molecpl
open TTree
variable {w : ℕ} (G : Garden w)

/-- The parent rung has the lower branch as one child and leaves as its other two children. -/
theorem parent_rung_children {S : Finset (GBranch G.tree)} {a b : GBranch G.tree}
    (hB : G.molecule.IsBlock S a b) (R : EndRungData G.molecule S a b)
    (hn : b.1.2 ≠ []) (hp : GNode.parent b.toNode hn = R.left) (hall : RungAllLP G R) :
    ∀ i : Fin 3, b.toNode = R.left.child i ∨ ∃ l : GLeaf G.tree, l.toNode = R.left.child i := by
  obtain ⟨l₀,i₀,_j₀,_hm₀,hl₀,_hr₀,hpos₀,_hq₀⟩ :=
    dart_leaf_pair_positions G (hall 0) (R.left_row.atom_eq 0) (R.left_row.neighbor_eq 0)
  obtain ⟨l₁,i₁,_j₁,_hm₁,hl₁,_hr₁,hpos₁,_hq₁⟩ :=
    dart_leaf_pair_positions G (hall 1) (R.left_row.atom_eq 1) (R.left_row.neighbor_eq 1)
  let D : Fin 3 → GardenDart G := ![R.left_row.dart 0,R.left_row.dart 1,R.left_row.dart 2]
  let p : Fin 3 → Fin 3 := ![i₀,i₁,b.1.2.getLast hn]
  have hinj : Function.Injective D := triple_injective
    (R.left_row.injective.ne (by decide)) (R.left_row.injective.ne (by decide))
    (R.left_row.injective.ne (by decide))
  have ha : ∀ t, G.molecule.atom (D t) = R.left := by
    intro t; fin_cases t
    · exact R.left_row.atom_eq 0
    · exact R.left_row.atom_eq 1
    · exact R.left_row.atom_eq 2
  have hpos : ∀ t, Mole.dartPosition G (D t) = (p t).succ := by
    intro t; fin_cases t
    · exact hpos₀
    · exact hpos₁
    · change Mole.dartPosition G (R.left_row.dart 2) = _
      rw [lower_parent_reverse_dart G hB R hn hp]
      rfl
  have hs := three_child_positions G D hinj ha p hpos
  intro i
  obtain ⟨t,ht⟩ := hs i
  rw [← ht]
  fin_cases t
  · exact Or.inr ⟨l₀,hl₀⟩
  · exact Or.inr ⟨l₁,hl₁⟩
  · apply Or.inl
    change b.toNode = R.left.child (b.1.2.getLast hn)
    have hh := (Mole.parent_child_eq_node b.toNode hn).symm
    rw [hp] at hh
    simpa only [GBranch.toNode] using hh

/-- The two rung branches in the two-LP core case are incomparable. -/
theorem two_LP_rungs_incomparable {S : Finset (GBranch G.tree)} {a b : GBranch G.tree}
    (hB : G.molecule.IsBlock S a b) (hCL : Mole.CLParentPattern G S a b)
    (R : EndRungData G.molecule S a b) (hn : b.1.2 ≠ [])
    (hp : GNode.parent b.toNode hn = R.left) (hall : RungAllLP G R) (hlp : LowerLP G R) :
    ¬ R.left.toNode.IsDesc R.right.toNode ∧ ¬ R.right.toNode.IsDesc R.left.toNode := by
  constructor
  · intro hd
    have hne : R.left.toNode ≠ R.right.toNode := fun he => R.distinct (Mole.branch_toNode_injective he)
    obtain ⟨i,hi⟩ := strict_descendant_child G hd hne
    rcases parent_rung_children G hB R hn hp hall i with hb | ⟨l,hl⟩
    · rw [← hb] at hi
      exact R.right_ne_lower (lower_LP_terminal G hB hCL R hlp R.right R.right_mem hi)
    · exact leaf_not_ancestor_branch G l R.right (hl ▸ hi)
  · intro hd
    have hne : R.right.toNode ≠ R.left.toNode := fun he => R.distinct (Mole.branch_toNode_injective he).symm
    obtain ⟨i,hi⟩ := strict_descendant_child G hd hne
    obtain ⟨l,hl⟩ := other_rung_all_children_leaves G R hall hlp i
    exact leaf_not_ancestor_branch G l R.left (hl ▸ hi)

end WaveTurbulence.Molecpl
