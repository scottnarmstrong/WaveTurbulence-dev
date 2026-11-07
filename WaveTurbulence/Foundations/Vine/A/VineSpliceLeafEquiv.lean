/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.Vine.A.VineSpliceLeafRange
/-! The full old-leaf correspondence of two actual splices with the same
merge classes preserves pairing, marks, signs and trivial-root addresses. -/
@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.VineA
open WaveTurbulence.RedSplice
variable {w : ℕ} {G : Garden w}

/-- Canonical correspondence of all actual surviving leaves, including boundary leaves. -/
noncomputable def spliceFoldLeafEquiv (l m : List (CLBlock G))
    (hc : (spliceFold G l).cls = (spliceFold G m).cls) :
    GLeaf (spliceFold G l).G.tree ≃ GLeaf (spliceFold G m).G.tree :=
  equivOfSameRange (spliceFoldLeafTrace l).leaf (spliceFoldLeafTrace m).leaf
    (spliceFoldLeafTrace l).injective (spliceFoldLeafTrace m).injective (spliceFold_leaf_same_range l m hc)

/-- The leaf correspondence fixes literal original names. -/
theorem spliceFoldLeafEquiv_comm (l m : List (CLBlock G))
    (hc : (spliceFold G l).cls = (spliceFold G m).cls) (q : GLeaf (spliceFold G l).G.tree) :
    (spliceFoldLeafTrace m).leaf (spliceFoldLeafEquiv l m hc q) = (spliceFoldLeafTrace l).leaf q :=
  equivOfSameRange_comm (spliceFoldLeafTrace l).leaf (spliceFoldLeafTrace m).leaf
    (spliceFoldLeafTrace l).injective (spliceFoldLeafTrace m).injective (spliceFold_leaf_same_range l m hc) q

/-- The entire leaf pairing, including trivial roots, is respected. -/
theorem spliceFoldLeafEquiv_pair (l m : List (CLBlock G))
    (hc : (spliceFold G l).cls = (spliceFold G m).cls) (q : GLeaf (spliceFold G l).G.tree) :
    spliceFoldLeafEquiv l m hc ((spliceFold G l).G.pair q) = (spliceFold G m).G.pair (spliceFoldLeafEquiv l m hc q) := by
  apply (spliceFoldLeafTrace m).injective
  rw [spliceFoldLeafEquiv_comm, (spliceFoldLeafTrace l).pair,
    (spliceFoldLeafTrace m).pair, spliceFoldLeafEquiv_comm]

/-- Actual retained marks agree. -/
theorem spliceFoldLeafEquiv_mark (l m : List (CLBlock G))
    (hc : (spliceFold G l).cls = (spliceFold G m).cls) (q : GLeaf (spliceFold G l).G.tree) :
    (spliceFold G m).G.mark (spliceFoldLeafEquiv l m hc q) = (spliceFold G l).G.mark q := by
  rw [(spliceFoldLeafTrace m).mark, (spliceFoldLeafTrace l).mark, spliceFoldLeafEquiv_comm]

/-- The full actual leaf signs agree. -/
theorem spliceFoldLeafEquiv_sign (l m : List (CLBlock G))
    (hc : (spliceFold G l).cls = (spliceFold G m).cls) (q : GLeaf (spliceFold G l).G.tree) :
    (spliceFold G m).G.sign (spliceFoldLeafEquiv l m hc q).toNode = (spliceFold G l).G.sign q.toNode := by
  rw [(spliceFoldLeafTrace m).sign, (spliceFoldLeafTrace l).sign, spliceFoldLeafEquiv_comm]

end WaveTurbulence.VineA
