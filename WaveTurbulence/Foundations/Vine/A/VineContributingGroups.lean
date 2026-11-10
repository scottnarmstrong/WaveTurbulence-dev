/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.Vine.A.VinePrescribedPartition
public import WaveTurbulence.Foundations.Vine.A.VineBatchSplice
/-! Intrinsic classification of the maximal groups contributing actual C1 objects. -/
@[expose] public section
open WaveTurbulence.Induct
set_option autoImplicit false
namespace WaveTurbulence.VineA
open Finset Stage1 RedSplice LGSpine.SourceVine
variable {w : ℕ} {G : Garden w}

/-- The group has one of the three whole-group vine-like shapes. -/
def VineLikeGroup (G : Garden w) (S : Finset (GBranch G.tree)) : Prop :=
  ∃ a b, IsHV G.molecule S a b ∨ IsVC G.molecule S a b ∨ IsHVC G.molecule S a b

end WaveTurbulence.VineA
