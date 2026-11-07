/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.VineEst.VineEstS2.HeavySuccessor

/-! # Terminating search for the next same-sign heavy-path branch -/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.VineEstS2
open TTree
variable {w : ℕ} {tree : Fin w → TTree}

/-- The visited branches (including the start, excluding the next same-sign
branch) and that next branch if one exists. No sign change of a physical
momentum or its weight is made. Finite source depth proves termination. -/
noncomputable def signHeavySearch (sig : Fin w → ℤˣ) (ζ : ℤˣ) (v : GBranch tree) :
    List (GBranch tree) × Option (GBranch tree) :=
  match _h : nextHeavyBranch v with
  | none => ([v],none)
  | some u => if nodeSign sig u.1 = ζ then ([v],some u)
      else let q := signHeavySearch sig ζ u; (v::q.1,q.2)
termination_by branchDepthBound tree-v.1.2.length
decreasing_by exact nextHeavyBranch_measure_lt _h

noncomputable def signPredecessor (sig : Fin w → ℤˣ) (v : GBranch tree) : Option (GBranch tree) :=
  (signHeavySearch sig (nodeSign sig v.1) v).2

noncomputable def signPredecessorRoute (sig : Fin w → ℤˣ) (v : GBranch tree) : Finset (GBranch tree) := by
  classical
  exact (signHeavySearch sig (nodeSign sig v.1) v).1.toFinset

end WaveTurbulence.VineEstS2
