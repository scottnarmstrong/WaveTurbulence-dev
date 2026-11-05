/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Molecule.VineInsertedSequence
public import WaveTurbulence.Foundations.Molecule.VineNeighborPreservation
import Mathlib.Tactic

/-! # Full-rung sequences survive insertions at other slots -/

public section
namespace WaveTurbulence.Vine

/-- A sequence remains full when later slot insertions avoid all its rung
atoms. Its rail endpoints may be touched; the local rung rows are unchanged. -/
@[expose] def LiteralFullRungSequence.afterInsertions {T : VineTemplate} {n : ℕ}
    (L : LiteralFullRungSequence T n) (xs : List (((ℕ×ℕ)×(ℕ×ℕ))×ℕ))
    (hu : ∀ sk ∈ xs, ∀ i,1 ≤ i → i ≤ n →
      sk.1.1.1 ≠ (L.u i).1 ∧ sk.1.1.2 ≠ (L.u i).1 ∧
      sk.1.2.1 ≠ (L.u i).1 ∧ sk.1.2.2 ≠ (L.u i).1)
    (hv : ∀ sk ∈ xs, ∀ i,1 ≤ i → i ≤ n →
      sk.1.1.1 ≠ (L.v i).1 ∧ sk.1.1.2 ≠ (L.v i).1 ∧
      sk.1.2.1 ≠ (L.v i).1 ∧ sk.1.2.2 ≠ (L.v i).1) :
    LiteralFullRungSequence (xs.foldl (fun U sk => insertRungs U sk.1 sk.2) T) n where
  u := fun i => ⟨(L.u i).1,by rw [fold_insertRungs_atoms]; have := (L.u i).2; omega⟩
  v := fun i => ⟨(L.v i).1,by rw [fold_insertRungs_atoms]; have := (L.v i).2; omega⟩
  distinct := by
    intro i j hij
    apply L.distinct
    apply Fin.ext
    have he := congrArg Fin.val hij
    cases i <;> cases j <;> exact he
  upper := by
    intro i hi hin
    exact (fold_insertRungs_neighbors xs T (L.u i).1 (L.u i).2
      (fun sk hsk => hu sk hsk i hi hin)).trans (L.upper i hi hin)
  lower := by
    intro i hi hin
    exact (fold_insertRungs_neighbors xs T (L.v i).1 (L.v i).2
      (fun sk hsk => hv sk hsk i hi hin)).trans (L.lower i hi hin)

end WaveTurbulence.Vine
