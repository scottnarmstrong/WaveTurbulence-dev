/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Molecule.ScenarioRelations

/-! # The five actual-garden type-II scenarios

TARGET Proposition molecpl (2), L1405--L1415. All parent relations,
paired leaves, ordered outer slots, and ancestor relations refer to the
actual Garden. The one-rung Q-block is included by the end-rung producer.
-/

public section
namespace WaveTurbulence.Molecpl
open TTree Vine
variable {w : ℕ} (G : Garden w)

/-- TARGET scenario (II-e), including the identity q=u23 in its retained outer slot. -/
@[expose] def IsTypeIIE (a b p q : GBranch G.tree) : Prop :=
  IsParent G p b ∧ IsParent G b q ∧ DoubleLeafPairAt G p q ∧
    (∃ i : Fin 3, q.toNode = b.child i ∧ i ≠ 1) ∧ a.toNode.IsDesc p.toNode

end WaveTurbulence.Molecpl
