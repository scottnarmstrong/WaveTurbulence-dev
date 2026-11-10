/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.Vine.A.VineGapJointChoice
/-! Actual designated whole-group objects of VC/HV/HVC groups have fixed support.
For ordinary VC groups their shape is necessarily ordinary. -/
@[expose] public section
open WaveTurbulence.Induct
set_option autoImplicit false
namespace WaveTurbulence.VineA
open Finset Stage1 RedSplice LGSpine.SourceVine
variable {w : ℕ} {G : Garden w}

/-- An object supported on an ordinary block cannot be a hyper object. -/
theorem object_tag_of_block {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]
    {M : Molecule V D} (O : Object M) {a b : V} (hB : M.IsBlock O.atoms a b) :
    objectHyperTag O = false := by
  cases hs : O.shape with
  | vc hv => simp only [objectHyperTag, hs]
  | hyper R => exact (block_not_hyper hB R.added R.ends_eq R.adjoint.1).elim

end WaveTurbulence.VineA
