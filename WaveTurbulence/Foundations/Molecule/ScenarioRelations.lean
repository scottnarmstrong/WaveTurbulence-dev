/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Molecule.IncomparableRungs
public import WaveTurbulence.Foundations.Molecule.LowerRetainedBranch

/-! # Tree and leaf-pair relations used by the five type-II scenarios -/

public section
namespace WaveTurbulence.Molecpl
open TTree
variable {w : ℕ} (G : Garden w)

/-- Immediate parenthood in the actual garden. -/
@[expose] def IsParent (p c : GBranch G.tree) : Prop :=
  ∃ hn : c.1.2 ≠ [], GNode.parent c.toNode hn = p

/-- Actual immediate parenthood gives a child slot. -/
theorem isParent_child {p c : GBranch G.tree} (h : IsParent G p c) :
    ∃ i : Fin 3, c.toNode = p.child i := by
  obtain ⟨hn,hp⟩ := h
  refine ⟨c.1.2.getLast hn,?_⟩
  have hh := (Mole.parent_child_eq_node c.toNode hn).symm
  rw [hp] at hh
  simpa only [GBranch.toNode] using hh

/-- Actual immediate parenthood implies the ancestor relation. -/
theorem isParent_desc {p c : GBranch G.tree} (h : IsParent G p c) :
    p.toNode.IsDesc c.toNode := by
  obtain ⟨i,hi⟩ := isParent_child G h
  rw [hi]
  exact ⟨rfl,[i],rfl⟩

/-- An actual branch has at most one immediate parent. -/
theorem isParent_unique {p q c : GBranch G.tree} (hp : IsParent G p c) (hq : IsParent G q c) : p = q := by
  obtain ⟨_hn,hp⟩ := hp
  obtain ⟨_hn',hq⟩ := hq
  exact hp.symm.trans hq

/-- The paired lower leaf is the retained outer child u23. -/
@[expose] def OuterLeafPairAt (b q : GBranch G.tree) : Prop :=
  ∃ (l : GLeaf G.tree) (i j : Fin 3), G.mark l = none ∧
    l.toNode = b.child i ∧ (G.pair l).toNode = q.child j ∧ i ≠ 1

/-- Two paired child leaves at each atom, with distinct ordered slots. -/
@[expose] def DoubleLeafPairAt (p q : GBranch G.tree) : Prop :=
  ∃ (l₀ l₁ : GLeaf G.tree) (i₀ i₁ j₀ j₁ : Fin 3),
    G.mark l₀ = none ∧ G.mark l₁ = none ∧
    l₀.toNode = p.child i₀ ∧ (G.pair l₀).toNode = q.child j₀ ∧
    l₁.toNode = p.child i₁ ∧ (G.pair l₁).toNode = q.child j₁ ∧ i₀ ≠ i₁ ∧ j₀ ≠ j₁

/-- Every core lower LP row supplies the source outer-leaf relation. -/
theorem lower_outerLeafPairAt {S : Finset (GBranch G.tree)} {a b : GBranch G.tree}
    (hB : G.molecule.IsBlock S a b) (hCL : Mole.CLParentPattern G S a b)
    (R : EndRungData G.molecule S a b) (hlp : LowerLP G R) : OuterLeafPairAt G b R.right := by
  obtain ⟨l,i,j,hm,hl,hr,hi,_⟩ := lower_LP_retained G hB hCL R hlp
  exact ⟨l,i,j,hm,hl,hr,hi⟩

end WaveTurbulence.Molecpl
