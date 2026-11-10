/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Molecule.MoleculeBondEdits
public import WaveTurbulence.Foundations.Molecule.Degen.Removal
import Mathlib.Tactic

/-! # DH23 Appendix B: exact graph statistics

All differences are post minus pre. The special-bond predicate is the
one stated in DH23 section B.2.7, not a count supplied as operation data.
-/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.Mole
open Finset
variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]

/-- DH23 Appendix B: atoms of degree j. -/
def appbDegreeAtoms (M : Molecule V D) (j : ℕ) : Finset V :=
  M.atoms.filter fun v => M.deg v = j

/-- DH23 Appendix B: nu = 4V - 2E - 4F. -/
noncomputable def appbNu (M : Molecule V D) : ℤ :=
  4 * (M.atoms.card : ℤ) - 2 * M.bonds.card - 4 * M.numComponents

/-- A special bond joins degree-three atoms each with a double bond to
other, distinct atoms (DH23 B.2.7). -/
def AppbSpecial (M : Molecule V D) (x : D) : Prop :=
  M.out x = true ∧ M.deg (M.atom x) = 3 ∧ M.deg (M.atom (M.mate x)) = 3 ∧
  ∃ a ∈ M.atoms, ∃ b ∈ M.atoms,
    a ≠ b ∧ a ≠ M.atom x ∧ a ≠ M.atom (M.mate x) ∧
    b ≠ M.atom x ∧ b ≠ M.atom (M.mate x) ∧
    M.bondsBetween (M.atom x) (M.atom (M.mate x)) = 1 ∧
    M.bondsBetween (M.atom x) a = 2 ∧ M.bondsBetween (M.atom (M.mate x)) b = 2

noncomputable def appbSpecialBonds (M : Molecule V D) : Finset D := by
  classical
  exact univ.filter (AppbSpecial M)

/-- The graph identity underlying every operation's nu calculation. -/
theorem appbNu_eq_rank (M : Molecule V D) :
    appbNu M = 2 * (M.atoms.card : ℤ) - 2 * M.circuitRank - 2 * M.numComponents := by
  unfold appbNu Molecule.circuitRank
  ring

/-- Survivor degree plus the removed incidences is exactly the old degree. -/
theorem appb_eraseAtoms_degree (M : Molecule V D) (Y : Finset V) {v : V} (hv : v ∉ Y) :
    (Degen.eraseAtoms M Y).deg v + (Degen.removedDartsAt M Y v).card = M.deg v := by
  have h := Degen.sum_dartsAt_split M Y hv (fun _ => (1 : ℕ))
  simpa only [sum_const, smul_eq_mul, mul_one, Molecule.deg] using h.symm

/-- Exact surviving vertex set; deletion retains isolated survivors. -/
theorem appb_eraseAtoms_card (M : Molecule V D) (Y : Finset V) (hY : Y ⊆ M.atoms) :
    (Degen.eraseAtoms M Y).atoms.card + Y.card = M.atoms.card := by
  exact card_sdiff_add_card_eq_card hY

end WaveTurbulence.Mole
