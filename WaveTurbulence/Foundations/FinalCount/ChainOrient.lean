/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.ChainStruct
import Mathlib.Tactic

/-! # Prop 9.6: a chain of `in = out` atoms leaves with opposite orientations at its two ends -/

@[expose] public section
set_option autoImplicit false
open Finset
namespace WaveTurbulence.FinalCountG8
open WaveTurbulence.MoleProp4

variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]

omit [DecidableEq D] in
/-- Signed degree: the dart signs at an atom add up to `outdeg - indeg`. -/
theorem sum_dartSign_dartsAt (M : Molecule V D) (v : V) :
    ∑ x ∈ M.dartsAt v, M.dartSign x = (M.outdeg v : ℝ) - (M.indeg v : ℝ) := by
  simp only [Molecule.dartSign]
  rw [Finset.sum_ite]
  simp only [sum_const, nsmul_eq_mul, mul_one, mul_neg, sub_eq_add_neg, Molecule.outdeg, Molecule.indeg,
    Bool.not_eq_true]

/-- **Opposite orientations.** Two cross darts of a balanced atom set point in opposite directions. -/
theorem chain_cross_opposite (M : Molecule V D) (K : Finset V) (hbal : ∀ v ∈ K, M.outdeg v = M.indeg v)
    {y₁ y₂ : D} (hne : y₁ ≠ y₂) (hcross : crossDarts M K = {y₁, y₂}) : M.out y₁ ≠ M.out y₂ := by
  have h := sum_stars_eq_cross M K (fun x => M.dartSign x) (dartSign_mate M)
  have h0 : ∑ v ∈ K, ∑ x ∈ M.dartsAt v, M.dartSign x = 0 :=
    sum_eq_zero fun v hv => by rw [sum_dartSign_dartsAt, hbal v hv, sub_self]
  rw [h0, hcross, sum_pair hne] at h
  intro he
  unfold Molecule.dartSign at h
  cases hx : M.out y₁ <;> have hy := hx.symm.trans he <;>
    simp only [hx, hy.symm, Bool.false_eq_true, ite_false, ite_true] at h <;> norm_num at h

end WaveTurbulence.FinalCountG8
