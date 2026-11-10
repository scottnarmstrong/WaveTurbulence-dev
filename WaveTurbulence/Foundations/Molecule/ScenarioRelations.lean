/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Molecule.LowerRetainedBranch

/-! # Tree and leaf-pair relations used by the five type-II scenarios -/

public section
namespace WaveTurbulence.Molecpl
open TTree
variable {w : ℕ} (G : Garden w)

/-- Immediate parenthood in the actual garden. -/
@[expose] def IsParent (p c : GBranch G.tree) : Prop :=
  ∃ hn : c.1.2 ≠ [], GNode.parent c.toNode hn = p

/-- Two paired child leaves at each atom, with distinct ordered slots. -/
@[expose] def DoubleLeafPairAt (p q : GBranch G.tree) : Prop :=
  ∃ (l₀ l₁ : GLeaf G.tree) (i₀ i₁ j₀ j₁ : Fin 3),
    G.mark l₀ = none ∧ G.mark l₁ = none ∧
    l₀.toNode = p.child i₀ ∧ (G.pair l₀).toNode = q.child j₀ ∧
    l₁.toNode = p.child i₁ ∧ (G.pair l₁).toNode = q.child j₁ ∧ i₀ ≠ i₁ ∧ j₀ ≠ j₁

end WaveTurbulence.Molecpl
