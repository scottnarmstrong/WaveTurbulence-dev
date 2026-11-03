/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Counting.LatticeDisc
import Mathlib.Tactic

/-!
# Coordinate interchange for translated lattice discs

Swapping both coordinates preserves the Euclidean disc and interchanges
its horizontal and vertical caps, including their closed circular edges.
-/

public section

namespace WaveTurbulence.Counting

/-- Coordinate interchange of the real planar center. -/
@[expose] noncomputable def planeSwapCenter (c : EuclideanSpace ℝ (Fin 2)) :
    EuclideanSpace ℝ (Fin 2) := WithLp.toLp 2 ![c 1,c 0]

/-- Coordinate interchange of an integer lattice point. -/
@[expose] def planeSwapLattice (n : Fin 2 → ℤ) : Fin 2 → ℤ := ![n 1,n 0]

@[simp] theorem planeSwapLattice_involutive (n : Fin 2 → ℤ) :
    planeSwapLattice (planeSwapLattice n) = n := by
  ext i
  fin_cases i <;> rfl

/-- The frozen lattice embedding commutes with coordinate interchange at
the level of actual Euclidean distance. -/
theorem norm_planeSwap_lattice_sub_center (c : EuclideanSpace ℝ (Fin 2)) (n : Fin 2 → ℤ) :
    ‖WaveTurbulence.latticePoint 1 (planeSwapLattice n)-planeSwapCenter c‖ =
      ‖WaveTurbulence.latticePoint 1 n-c‖ := by
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  simp only [EuclideanSpace.real_norm_sq_eq,Fin.sum_univ_two]
  simp [planeSwapCenter,planeSwapLattice,WaveTurbulence.latticePoint,add_comm]

/-- Exact equality of the horizontal cap count and the vertical cap count
for the interchanged center. -/
theorem card_latticeDisc_horizontal_caps_eq_swap
    (c : EuclideanSpace ℝ (Fin 2)) {R : ℝ} (hR : 0 ≤ R) (T : ℝ) :
    ((latticeDisc c R).filter (fun n => T < |(n 1:ℝ)-c 1|)).card =
      ((latticeDisc (planeSwapCenter c) R).filter
        (fun n => T < |(n 0:ℝ)-(planeSwapCenter c) 0|)).card := by
  classical
  apply Finset.card_bij (fun n _ => planeSwapLattice n)
  · intro n hn
    obtain ⟨hn,hcut⟩ := Finset.mem_filter.mp hn
    apply Finset.mem_filter.mpr
    constructor
    · rw [mem_latticeDisc hR,norm_planeSwap_lattice_sub_center]
      exact (mem_latticeDisc hR).mp hn
    · exact hcut
  · intro n hn m hm he
    have hh := congrArg planeSwapLattice he
    simpa only [planeSwapLattice_involutive] using hh
  · intro n hn
    obtain ⟨hn,hcut⟩ := Finset.mem_filter.mp hn
    refine ⟨planeSwapLattice n,Finset.mem_filter.mpr ⟨?_,?_⟩,planeSwapLattice_involutive n⟩
    · have he := norm_planeSwap_lattice_sub_center c (planeSwapLattice n)
      rw [planeSwapLattice_involutive] at he
      rw [mem_latticeDisc hR,← he]
      exact (mem_latticeDisc hR).mp hn
    · exact hcut

end WaveTurbulence.Counting
