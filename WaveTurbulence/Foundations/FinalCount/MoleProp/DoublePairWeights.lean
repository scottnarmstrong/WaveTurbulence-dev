/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.MoleProp.CellDeletionGeometry
public import WaveTurbulence.Foundations.FinalCount.MoleProp.FreeNormalization
import Mathlib.Tactic

/-! # The exact ladder-position factor removed by a double-rung operation -/

@[expose] public section
set_option autoImplicit false
open Finset
namespace WaveTurbulence.MoleProp
variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]

/-- In an affected operation(b) the actual lost-cell family is the
singleton consisting of its actual source cell. -/
theorem lost_cells_double_pair_eq_singleton (M : Molecule V D) (hM : M.IsMolecule)
    {a b : V} (hab : a ≠ b) (hdeg : M.deg a = 3) (hdouble : M.bondsBetween a b = 2)
    {S : Finset V} (hS : S ∈ ladderCells M) (haS : a ∈ S) :
    (ladderCells M).filter (fun T => ¬ Disjoint T {a,b}) = {S} := by
  classical
  have hcard := card_cells_lost_double_pair_le_one M hM hab hdeg hdouble
  have hmem : S ∈ (ladderCells M).filter (fun T => ¬ Disjoint T {a,b}) := by
    refine mem_filter.mpr ⟨hS,?_⟩
    intro hd
    exact disjoint_left.mp hd haS (by simp)
  ext T
  constructor
  · intro hT
    exact mem_singleton.mpr (card_le_one.mp hcard T hT S hmem)
  · intro hT
    have he : T = S := mem_singleton.mp hT
    exact he.symm ▸ hmem

/-- DH23 laddersharp: deleting this double pair removes exactly ONE
per-position factor, at its own actual gap parameter P S. -/
theorem cellProduct_double_pair_eq (M : Molecule V D) (hM : M.IsMolecule)
    {a b : V} (hab : a ≠ b) (hdeg : M.deg a = 3) (hdouble : M.bondsBetween a b = 2)
    {S : Finset V} (hS : S ∈ ladderCells M) (haS : a ∈ S)
    (L γ δ : ℝ) (P : Finset V → ℝ) :
    cellProduct M L γ δ P = cellProduct (Degen.eraseAtoms M {a,b}) L γ δ P *
      Molecule.ladderWeight L γ δ (P S) := by
  classical
  have he := lost_cells_double_pair_eq_singleton M hM hab hdeg hdouble hS haS
  have hp := prod_filter_mul_prod_filter_not (ladderCells M) (fun T => Disjoint T {a,b})
    (fun T => Molecule.ladderWeight L γ δ (P T))
  rw [he,prod_singleton] at hp
  unfold cellProduct
  rw [ladderCells_erase_eq_filter]
  exact hp.symm

/-- Every actual post-cell scale remains the same literal P parameter. -/
theorem nonnegative_scales_erase (M : Molecule V D) (Y : Finset V) (P : Finset V → ℝ)
    (hP : ∀ S ∈ ladderCells M, 0 ≤ P S) :
    ∀ S ∈ ladderCells (Degen.eraseAtoms M Y), 0 ≤ P S := by
  classical
  rw [ladderCells_erase_eq_filter]
  intro S hS
  exact hP S (mem_filter.mp hS).1

end WaveTurbulence.MoleProp
