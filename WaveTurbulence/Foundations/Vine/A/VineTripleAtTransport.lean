/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.Vine.A.VineCollectionGeometry
/-! Actual molecular maps preserve the literal ordered triple-pair predicate. -/
@[expose] public section
open WaveTurbulence.Induct
set_option autoImplicit false
namespace WaveTurbulence.VineA
open Stage1 LGSpine.SourceVine
variable {w : ℕ} {G H : Garden w}

/-- Transport the actual incidences, distinct bonds and opposite directions. -/
theorem tripleAt_image (E : MolIso G.molecule H.molecule) {v : GBranch G.tree}
    {x y : GardenDart G} (h : TripleAt G v x y) : TripleAt H (E.e v) (E.d x) (E.d y) := by
  refine ⟨(E.atom_comm x).trans (congrArg E.e h.1),
    (E.atom_comm y).trans (congrArg E.e h.2.1), ?_, ?_⟩
  · intro he
    apply h.2.2.1
    exact E.d.injective (he.trans (E.mate_comm x))
  · intro he
    exact h.2.2.2 ((E.out_comm x).symm.trans (he.trans (E.out_comm y)))

end WaveTurbulence.VineA
