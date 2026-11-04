/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Incoh.FiniteSpectralDecomposition

/-!
# Actual finite lattice support of localized source pieces

Half-width link cells lie where the analytic cutoff is one. Consequently
the lattice sum of each localized source piece is an actual finite sum,
independent of time and of the spectral variables used in inversion.
-/

public section
noncomputable section
open Set

namespace WaveTurbulence.Incoh

/-- Literal lattice array evaluated at physical lattice momenta. -/
@[expose] def latticeMomentumArray {d : ℕ} {I : Type*} (L : ℝ)
    (p : I → Fin d → ℤ) : I → Mom d := fun i => latticePoint L (p i)

/-- Product of the actual compact analytic cutoff lattice supports. -/
@[expose] def linkCellLatticeSet {d : ℕ} {I : Type*} (L : ℝ)
    (z : I → Fin d → ℤ) : Set (I → Fin d → ℤ) :=
  univ.pi (fun i => {p | WeylSums.latticeCutoff (latticePoint L p - halfCellCenter (z i)) ≠ 0})

/-- The support set is finite before introducing any time or Fourier variables. -/
theorem finite_linkCellLatticeSet {d : ℕ} {I : Type*} [Finite I] {L : ℝ}
    (hL : 0 < L) (z : I → Fin d → ℤ) : (linkCellLatticeSet L z).Finite :=
  Set.Finite.pi (fun i => WeylSums.finite_latticeCutoff hL (halfCellCenter (z i)))

/-- Every nonzero actual link-cell lattice weight belongs to this common finite set. -/
theorem mem_linkCellLatticeSet_of_halfCellArrayWeight_ne_zero {d : ℕ} {I : Type*} [Fintype I]
    (L : ℝ) (z p : I → Fin d → ℤ)
    (hp : halfCellArrayWeight z (latticeMomentumArray L p) ≠ 0) : p ∈ linkCellLatticeSet L z := by
  classical
  intro i _
  have hi := (Finset.prod_ne_zero_iff.mp hp) i (Finset.mem_univ i)
  change halfLinkCell (z i) (latticePoint L (p i)) ≠ 0 at hi
  change WeylSums.latticeCutoff (latticePoint L (p i) - halfCellCenter (z i)) ≠ 0
  rw [latticeCutoff_eq_one_of_halfLinkCell_ne_zero hi]
  exact one_ne_zero

/-- The actual array of half-cell weights has finite lattice support. -/
theorem finite_support_halfCellArrayWeight_lattice {d : ℕ} {I : Type*} [Fintype I]
    {L : ℝ} (hL : 0 < L) (z : I → Fin d → ℤ) :
    (Function.support (fun p : I → Fin d → ℤ =>
      halfCellArrayWeight z (latticeMomentumArray L p))).Finite :=
  (finite_linkCellLatticeSet hL z).subset (fun p hp =>
    mem_linkCellLatticeSet_of_halfCellArrayWeight_ne_zero L z p hp)

end WaveTurbulence.Incoh
