/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Mathlib.Data.Fin.Tuple.Basic
public import Mathlib.Data.Int.Basic
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Basic.Real.Basic
public import Mathlib.Logic.Equiv.Basic
import Mathlib.Tactic

/-!
# Exact coordinate splittings of integer vectors

The first two coordinates and their complement are split by a genuine
bijection, used to lift the planar density argument in DH23 `estcross`.
-/

public section

namespace WaveTurbulence.Counting

/-- Separate the first two integer coordinates from the remaining coordinates. -/
@[expose] def latticeSplitTwo (d : ℕ) :
    (Fin (d+2) → ℤ) ≃ (Fin 2 → ℤ) × (Fin d → ℤ) where
  toFun n := (![n 0,n 1],fun i => n i.succ.succ)
  invFun p := Fin.cons (p.1 0) (Fin.cons (p.1 1) p.2)
  left_inv n := by
    funext i
    refine Fin.cases ?_ (fun j => ?_) i
    · rfl
    · refine Fin.cases ?_ (fun k => ?_) j
      · rfl
      · rfl
  right_inv p := by
    apply Prod.ext
    · funext i
      fin_cases i <;> rfl
    · funext i
      rfl

/-- Splitting the first two summands in a real coordinate dot product. -/
theorem sum_coordinate_mul_split_two {d : ℕ} (x : Fin (d+2) → ℝ) (n : Fin (d+2) → ℤ) :
    (∑ i, x i*(n i:ℝ)) = x 0*(n 0:ℝ)+x 1*(n 1:ℝ)+
      ∑ i : Fin d, x i.succ.succ*(n i.succ.succ:ℝ) := by
  rw [Fin.sum_univ_succ,Fin.sum_univ_succ]
  have he : Fin.succ (0 : Fin (d+1)) = (1 : Fin (d+2)) := by apply Fin.ext; rfl
  rw [he]
  ring

/-- Separate the first coordinate and the final `d` coordinates from the
second and third coordinates. This is the exact counting layout for estcross. -/
@[expose] def latticeSplitThree (d : ℕ) :
    (Fin (d+3) → ℤ) ≃ (Fin (d+1) → ℤ) × (Fin 2 → ℤ) where
  toFun n := (Fin.cons (n 0) (fun i => n i.succ.succ.succ),![n 1,n 2])
  invFun p := Fin.cons (p.1 0) (Fin.cons (p.2 0) (Fin.cons (p.2 1) (fun i => p.1 i.succ)))
  left_inv n := by
    funext i
    refine Fin.cases ?_ (fun j => ?_) i
    · rfl
    · refine Fin.cases ?_ (fun k => ?_) j
      · rfl
      · refine Fin.cases ?_ (fun l => ?_) k
        · rfl
        · rfl
  right_inv p := by
    apply Prod.ext
    · funext i
      refine Fin.cases ?_ (fun j => ?_) i <;> rfl
    · funext i
      fin_cases i <;> rfl

/-- Permute integer coordinates by an actual equivalence of their indices. -/
@[expose] def latticePermute {D : ℕ} (e : Fin D ≃ Fin D) :
    (Fin D → ℤ) ≃ (Fin D → ℤ) where
  toFun n i := n (e i)
  invFun n i := n (e.symm i)
  left_inv n := by funext i; simp only [e.apply_symm_apply]
  right_inv n := by funext i; simp only [e.symm_apply_apply]

/-- The coordinate dot product is unchanged when both vectors undergo the
same coordinate permutation. -/
theorem sum_coordinate_mul_permute {D : ℕ} (e : Fin D ≃ Fin D)
    (x : Fin D → ℝ) (n : Fin D → ℤ) :
    (∑ i, x (e i)*(n (e i):ℝ)) = ∑ i, x i*(n i:ℝ) := by
  simpa only using! Equiv.sum_comp e (fun i => x i*(n i:ℝ))

end WaveTurbulence.Counting
