/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.WeylSums.BilinearPointwise

/-!
# Literal localized lattice link factors

TARGET (incohproof10)–(incohproof12). F62: the per-link Wick coefficient is the square of the single-node
coefficient. It removes the two punctured coordinate axes. No estimate is stored
in the link data.
-/

public section

noncomputable section

open Set

namespace WaveTurbulence.Incoh

variable {d : ℕ}

/-- The four center and Fourier-shift parameters of one localized link. -/
structure LinkParameters (d : ℕ) where
  leftCenter : Mom d
  rightCenter : Mom d
  leftShift : Mom d
  rightShift : Mom d

/-- The Wick coefficient is `1`, `0`, or `-1` according to the number of zero vectors. -/
@[expose] def linkEpsilon (x y : Fin d → ℤ) : ℝ :=
  1 - (if x = 0 then 1 else 0) - (if y = 0 then 1 else 0)

theorem abs_linkEpsilon_le (x y : Fin d → ℤ) : |linkEpsilon x y| ≤ 1 := by
  classical
  by_cases hx : x = 0 <;> by_cases hy : y = 0 <;> norm_num [linkEpsilon, hx, hy]

/-- The single-node coefficient has the source three cases; F62 requires its square per paired link. -/
theorem linkEpsilon_eq_source (x y : Fin d → ℤ) :
    linkEpsilon x y = if x = 0 ∧ y = 0 then -1 else if x = 0 ∨ y = 0 then 0 else 1 := by
  classical
  by_cases hx : x = 0 <;> by_cases hy : y = 0 <;> norm_num [linkEpsilon, hx, hy]

/-- F62: both branching endpoints contribute the same coefficient, so the literal link uses its square. -/
@[expose] def linkWickFactor (x y : Fin d → ℤ) : ℝ := (linkEpsilon x y) ^ 2

theorem abs_linkWickFactor_le (x y : Fin d → ℤ) : |linkWickFactor x y| ≤ 1 := by
  classical
  by_cases hx : x = 0 <;> by_cases hy : y = 0 <;> norm_num [linkWickFactor, linkEpsilon, hx, hy]

/-- The true paired factor is `1,0,1`, including `1` at the double-zero lattice point. -/
theorem linkWickFactor_eq_cases (x y : Fin d → ℤ) :
    linkWickFactor x y = if x = 0 ∧ y = 0 then 1 else if x = 0 ∨ y = 0 then 0 else 1 := by
  classical
  by_cases hx : x = 0 <;> by_cases hy : y = 0 <;> norm_num [linkWickFactor, linkEpsilon, hx, hy]

/-- The uncorrected compact lattice amplitude. -/
@[expose] def cutoffAmplitude (L : ℝ) (A : LinkParameters d)
    (p : (Fin d → ℤ) × (Fin d → ℤ)) : ℂ :=
  ((WeylSums.latticeCutoff (latticePoint L p.1 - A.leftCenter) *
    WeylSums.latticeCutoff (latticePoint L p.2 - A.rightCenter) : ℝ) : ℂ)

/-- The actual Wick-corrected compact amplitude. -/
@[expose] def linkAmplitude (L : ℝ) (A : LinkParameters d)
    (p : (Fin d → ℤ) × (Fin d → ℤ)) : ℂ :=
  (linkWickFactor p.1 p.2 : ℂ) * cutoffAmplitude L A p

/-- The source's real bilinear phase, including both linear Fourier shifts. -/
@[expose] def linkPhase (L s : ℝ) (A : LinkParameters d)
    (p : (Fin d → ℤ) × (Fin d → ℤ)) : ℝ :=
  inner ℝ (latticePoint L p.1) A.leftShift + inner ℝ (latticePoint L p.2) A.rightShift +
    s * inner ℝ (latticePoint L p.1) (latticePoint L p.2)

/-- TARGET (incohproof10), with the frequency variable `s` not yet rescaled in time. -/
@[expose] def linkLatticeSum (L s : ℝ) (A : LinkParameters d) : ℂ :=
  ∑' p, linkAmplitude L A p * WeylSums.e (linkPhase L s A p)

theorem finite_support_cutoffAmplitude {L : ℝ} (hL : 0 < L) (A : LinkParameters d) :
    (Function.support (cutoffAmplitude L A)).Finite := by
  refine ((WeylSums.finite_latticeCutoff hL A.leftCenter).prod
    (WeylSums.finite_latticeCutoff hL A.rightCenter)).subset ?_
  intro p hp
  have H : WeylSums.latticeCutoff (latticePoint L p.1 - A.leftCenter) *
      WeylSums.latticeCutoff (latticePoint L p.2 - A.rightCenter) ≠ 0 :=
    Complex.ofReal_ne_zero.1 hp
  exact mul_ne_zero_iff.1 H

theorem finite_support_linkAmplitude {L : ℝ} (hL : 0 < L) (A : LinkParameters d) :
    (Function.support (linkAmplitude L A)).Finite := by
  apply (finite_support_cutoffAmplitude hL A).subset
  intro p hp hzero
  exact hp (by simp only [linkAmplitude, hzero, mul_zero])

/-- Every link is an actual finite-frequency sum and therefore continuous in time frequency. -/
theorem continuous_linkLatticeSum {L : ℝ} (hL : 0 < L) (A : LinkParameters d) :
    Continuous (fun s => linkLatticeSum L s A) :=
  WeylSums.continuous_finite_amplitude_sum _ (finite_support_linkAmplitude hL A)
    (fun s p => linkPhase L s A p) (fun _ => by unfold linkPhase; fun_prop)

end WaveTurbulence.Incoh
