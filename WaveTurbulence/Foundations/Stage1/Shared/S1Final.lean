/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Stage1.Shared.S1Dia16
public import WaveTurbulence.Foundations.Stage1.Shared.S1VInvFamily
import Mathlib.Tactic

/-!
# Congruence is an equivalence relation on `IsVFamily` states (GAP.congEquiv)
-/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.Stage1
open TTree Reg Reg.Skeleton Twist Links RegRed WaveTurbulence.LFTwist

variable {w p : ℕ} {kind : Bool} {ι : Type*}

/-- The Diamond for any two admissible operations at distinct members (all four choice combinations). -/
theorem diamond_all : DiamondProp p kind w ι :=
  diamondProp_of_TT (fun _ _ _ P con hj => P.diamond_TT con hj)

/-- **`OpsCommute`** (locality of LF operations at distinct members). -/
theorem opsCommute_all : OpsCommute p kind w ι := opsCommute_of_diamond diamond_all

/-- **Congruence is an equivalence relation** (on all states). -/
theorem congruent_equivalence [Fintype ι] [DecidableEq ι] :
    Equivalence (Congruent (w := w) (ι := ι) p kind) :=
  congruent_equivalence_of_commute opsCommute_all

end WaveTurbulence.Stage1
