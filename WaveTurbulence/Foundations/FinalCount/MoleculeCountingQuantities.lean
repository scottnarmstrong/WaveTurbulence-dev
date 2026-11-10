/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.FinalCount.MoleculeRestrictedCount
public import Mathlib.Basic.ENNReal.Inv
public import Mathlib.Basic.Real.ENatENNReal
import Mathlib.Tactic

/-!
# Finiteness and algebra of E, A and operation deviations

TARGET (defcounta2), (defdev), L2129–L2137. The positive lattice scale
makes E and A finite. The explicit ratio convention has the stated least
bound property for finite nonzero denominators; zero denominators require
separate operation compatibility, and are not silently cancelled.
-/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.Mole
open scoped ENNReal

variable {V D : Type*} [DecidableEq V] [Fintype D] (M : Molecule V D)

/-- A verified draft edge case: the ratio convention is not an unconditional
operation bound when its denominator is zero. -/
theorem deviation_zero_denominator_counterexample :
    ¬ (1 : ℝ≥0∞) ≤ deviation 1 0*0 := by
  norm_num [deviation]

end WaveTurbulence.Mole
