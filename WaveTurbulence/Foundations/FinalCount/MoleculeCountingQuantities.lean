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

/-- The exact normalized counting quantity A is finite at positive lattice scale. -/
theorem countA_ne_top {d : ℕ} {L : ℝ} (hL : 0 < L) (gamma delta C1 : ℝ) (w : Mom d)
    (Adm : (D → (Fin d → ℤ)) → Prop) (P : Finset V → ℝ) :
    M.countA L gamma delta C1 w Adm P ≠ ⊤ := by
  unfold Molecule.countA
  exact ENNReal.mul_ne_top (ENat.toENNReal_ne_top.mpr (countE_ne_top M hL gamma delta w Adm))
    ENNReal.ofReal_ne_top

/-- The ratio gives an actual deviation bound for every finite nonzero
post-operation count. -/
theorem deviation_mul_eq {Apre Apos : ℝ≥0∞} (h0 : Apos ≠ 0) (htop : Apos ≠ ⊤) :
    deviation Apre Apos*Apos = Apre := ENNReal.div_mul_cancel h0 htop

/-- Exact least-bound characterization with the necessary denominator conditions. -/
theorem deviation_le_iff {Apre Apos I : ℝ≥0∞} (h0 : Apos ≠ 0) (htop : Apos ≠ ⊤) :
    deviation Apre Apos ≤ I ↔ Apre ≤ I*Apos := ENNReal.div_le_iff h0 htop

/-- Two actual operation ratios compose when the intermediate count is
finite and nonzero. -/
theorem deviation_compose {Apre Amid Apos : ℝ≥0∞} (h0 : Amid ≠ 0) (htop : Amid ≠ ⊤) :
    deviation Apre Amid*deviation Amid Apos = deviation Apre Apos :=
  ENNReal.div_mul_div_cancel h0 htop

/-- A verified draft edge case: the ratio convention is not an unconditional
operation bound when its denominator is zero. -/
theorem deviation_zero_denominator_counterexample :
    ¬ (1 : ℝ≥0∞) ≤ deviation 1 0*0 := by
  norm_num [deviation]

end WaveTurbulence.Mole
