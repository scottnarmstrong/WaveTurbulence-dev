/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.AppBDegreeThree
public import WaveTurbulence.Foundations.FinalCount.AppBDegreeCountTransport
public import WaveTurbulence.Foundations.FinalCount.AppBAddedDegreeThree
import Mathlib.Tactic

/-! # Uniform bounded changes of V3 from actual local graph edits -/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.Mole.AppbAlgorithm
open Finset
variable {V D E : Type*} [DecidableEq V] [Fintype D] [DecidableEq D] [Fintype E]

private theorem indicator_difference_bound (A B : Prop) [Decidable A] [Decidable B] :
    -(1 : ℤ) ≤ (if A then 1 else 0)-(if B then 1 else 0) ∧
      (if A then (1 : ℤ) else 0)-(if B then 1 else 0) ≤ 1 := by
  by_cases hA : A <;> by_cases hB : B <;> simp only [hA,hB,ite_true,ite_false] <;> norm_num

theorem sum_indicator_difference_abs_le {ι : Type*} (S : Finset ι) (A B : ι → Prop)
    [DecidablePred A] [DecidablePred B] :
    |∑ a ∈ S,((if A a then (1 : ℤ) else 0)-(if B a then 1 else 0))| ≤ S.card := by
  apply abs_le.mpr
  constructor
  · have hh := sum_le_sum (s := S) (fun a ha => (indicator_difference_bound (A a) (B a)).1)
    simpa only [sum_const,nsmul_eq_mul,Int.natCast_mul,Int.natCast_one,mul_neg,mul_one] using hh
  · have hh := sum_le_sum (s := S) (fun a ha => (indicator_difference_bound (A a) (B a)).2)
    simpa only [sum_const,nsmul_eq_mul,mul_one] using hh

theorem deletion_degreeThree_change_abs_le {M : Molecule V D} {P : AppbPattern}
    (r : AppbRealization M P) :
    |((appbDegreeAtoms r.post 3).card : ℤ)-(appbDegreeAtoms M 3).card| ≤ P.vertices.card := by
  classical
  rw [r.post_degreeThree_difference]
  exact sum_indicator_difference_abs_le P.vertices
    (fun a => a ∉ P.removed ∧ M.deg (r.vertex a) = 3+P.localDegree a)
    (fun a => M.deg (r.vertex a) = 3)

theorem same_atoms_degreeThree_change_abs_le (M : Molecule V D) (N : Molecule V E)
    (hatoms : N.atoms = M.atoms) (S : Finset V) (hS : S ⊆ M.atoms)
    (hdeg : ∀ v ∈ M.atoms,v ∉ S → N.deg v = M.deg v) :
    |((appbDegreeAtoms N 3).card : ℤ)-(appbDegreeAtoms M 3).card| ≤ S.card := by
  classical
  rw [appb_degreeCount_difference_of_local_change M N hatoms S hS hdeg 3]
  exact sum_indicator_difference_abs_le S (fun v => N.deg v = 3) (fun v => M.deg v = 3)

theorem insertion_degreeThree_change_abs_le (M : Molecule V D) (a b : V)
    (ha : a ∈ M.atoms) (hb : b ∈ M.atoms) (hab : a ≠ b) :
    |((appbDegreeAtoms (addBond M a b) 3).card : ℤ)-(appbDegreeAtoms M 3).card| ≤ 2 := by
  classical
  rw [appb_addBond_degreeThree_difference M a b ha hb hab]
  have h1 := indicator_difference_bound (M.deg a = 2) (M.deg a = 3)
  have h2 := indicator_difference_bound (M.deg b = 2) (M.deg b = 3)
  apply abs_le.mpr
  omega

end WaveTurbulence.Mole.AppbAlgorithm
