/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Molecule.CatalanGeneration
public import Mathlib.Data.Fin.Tuple.Basic

/-! # Literal concatenation of ordered pair partitions -/

@[expose] public section
namespace WaveTurbulence.Reg.PairPartition
open TTree

/-- Concatenate two partner involutions on their actual successive index blocks. -/
def append {n m : ℕ} (P : PairPartition n) (Q : PairPartition m) : PairPartition (n+m) where
  pair := Fin.addCases (fun i => Fin.castAdd m (P.pair i)) (fun j => Fin.natAdd n (Q.pair j))
  involutive := by
    intro i
    refine Fin.addCases (fun i => ?_) (fun j => ?_) i
    · simp only [Fin.addCases_left]
      rw [P.involutive]
    · simp only [Fin.addCases_right]
      rw [Q.involutive]
  no_fixed := by
    intro i
    refine Fin.addCases (fun i => ?_) (fun j => ?_) i
    · simp only [Fin.addCases_left]
      intro h
      have hv := congrArg Fin.val h
      exact P.no_fixed i (Fin.ext hv)
    · simp only [Fin.addCases_right]
      intro h
      exact Q.no_fixed j (Fin.ext (Nat.add_left_cancel (congrArg Fin.val h)))

/-- Literal transport of a partner in the first block. -/
theorem append_pair_left {n m : ℕ} (P : PairPartition n) (Q : PairPartition m) (i : Fin n) :
    (P.append Q).pair (Fin.castAdd m i) = Fin.castAdd m (P.pair i) := by
  simp only [append,Fin.addCases_left]

/-- Literal transport of a partner in the second block. -/
theorem append_pair_right {n m : ℕ} (P : PairPartition n) (Q : PairPartition m) (i : Fin m) :
    (P.append Q).pair (Fin.natAdd n i) = Fin.natAdd n (Q.pair i) := by
  simp only [append,Fin.addCases_right]

/-- Partners in the initial block stay in that block. -/
theorem append_pair_first_iff {n m : ℕ} (P : PairPartition n) (Q : PairPartition m) (i : Fin (n+m)) :
    ((P.append Q).pair i).val < n ↔ i.val < n := by
  refine Fin.addCases (fun i => ?_) (fun j => ?_) i
  · rw [append_pair_left]
    exact iff_of_true (P.pair i).isLt i.isLt
  · rw [append_pair_right]
    change n + (Q.pair j).val < n ↔ n + j.val < n
    omega

end WaveTurbulence.Reg.PairPartition
