/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Molecule.LFTwist.TreeErasureCoherence

/-! # A source-class index for the two canonical object kinds

This records the original G/C kind so that finite coherent-erasure arguments
preserve both classes without assuming an abstract canonicity-closure axiom.
-/

public section
namespace WaveTurbulence.LFTwist
open TTree Reg Reg.Skeleton

inductive CanonicalObject (p : ℕ) : Bool → {w : ℕ} → LayeredGarden w → Prop
  | garden {w : ℕ} {LG : LayeredGarden w} (hc : IsCanonG (p+1) LG) : CanonicalObject p true LG
  | couple {LG : LayeredGarden 2} (hc : IsCanonC (p+1) LG) : CanonicalObject p false LG

theorem CanonicalObject.criterion {p : ℕ} {kind : Bool} {w : ℕ} {LG : LayeredGarden w}
    (hc : CanonicalObject p kind LG) : LG.CanonCriterion p := by
  cases hc with
  | garden hc => exact hc.2.2.2
  | couple hc => exact hc.2

theorem CanonicalObject.plain {p : ℕ} {kind : Bool} {w : ℕ} {LG : LayeredGarden w}
    (hc : CanonicalObject p kind LG) : LG.garden.IsPlain := by
  cases hc with
  | garden hc => exact hc.2.1
  | couple hc => exact hc.1.1

end WaveTurbulence.LFTwist
