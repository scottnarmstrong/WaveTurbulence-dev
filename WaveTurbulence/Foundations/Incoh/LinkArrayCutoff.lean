/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Incoh.LocalizedLatticeSupport

/-!
# Exact analytic cutoff insertion in the link array

The finite lattice cover supports the literal analytic cutoff array.
Multiplication by this array leaves every half-cell product unchanged.
-/

public section
noncomputable section

namespace WaveTurbulence.Incoh

/-- The actual analytic cutoff product at the half-cell centers. -/
@[expose] def linkArrayCutoff {d : ℕ} {I : Type*} [Fintype I]
    (z : I → Fin d → ℤ) (x : I → Mom d) : ℂ :=
  ∏ i, (WeylSums.latticeCutoff (x i - halfCellCenter (z i)) : ℂ)

/-- Exact insertion of all analytic link cutoffs in the actual smooth partition term. -/
theorem halfCellArrayWeight_mul_linkArrayCutoff {d : ℕ} {I : Type*} [Fintype I]
    (z : I → Fin d → ℤ) (x : I → Mom d) :
    halfCellArrayWeight z x * linkArrayCutoff z x = halfCellArrayWeight z x := by
  unfold halfCellArrayWeight linkArrayCutoff
  rw [← Finset.prod_mul_distrib]
  exact Finset.prod_congr rfl (fun i _ => halfLinkCell_mul_latticeCutoff (z i) (x i))

/-- A point outside the common finite lattice set annihilates the analytic cutoff array. -/
theorem linkArrayCutoff_eq_zero_of_not_mem {d : ℕ} {I : Type*} [Fintype I]
    (L : ℝ) (z p : I → Fin d → ℤ) (hp : p ∉ linkCellLatticeSet L z) :
    linkArrayCutoff z (latticeMomentumArray L p) = 0 := by
  classical
  by_contra hn
  apply hp
  intro i _
  have hi := (Finset.prod_ne_zero_iff.mp hn) i (Finset.mem_univ i)
  exact Complex.ofReal_ne_zero.mp hi

end WaveTurbulence.Incoh
