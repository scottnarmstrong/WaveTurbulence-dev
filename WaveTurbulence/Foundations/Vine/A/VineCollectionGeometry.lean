/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.Vine.A.VineObjectGeometry
public import WaveTurbulence.Foundations.Vine.A.VineGapTransport
/-! Actual C1 indexed geometry: supports determine the shape tag and unordered joints. -/
@[expose] public section
open WaveTurbulence.Induct
set_option autoImplicit false
namespace WaveTurbulence.VineA
open Finset Stage1 RedSplice LGSpine.SourceVine LFTwist
variable {w p : ℕ} {kind : Bool} {ι : Type*} {L : List ι}
variable {A B : FamilyReconstruction w ι} {F : MolIso A.skeleton.molecule B.skeleton.molecule}

/-- Mapping the chosen object never rechooses its ordinary/hyper constructor. -/
theorem mapObject_hyperTag {V D V' D' : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]
    [DecidableEq V'] [Fintype D'] [DecidableEq D'] {M : Molecule V D} {N : Molecule V' D'}
    (E : MolIso M N) (O : Object M) : objectHyperTag (mapObject E O) = objectHyperTag O := by
  rcases O with ⟨S, a, b, shape⟩
  cases shape <;> rfl

end WaveTurbulence.VineA
