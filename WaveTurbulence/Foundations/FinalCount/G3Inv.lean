/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.FinalCount.G3Steps
/-! **FINALCOUNT-G3, part 3: the invariants of the algorithm** and elementary degree facts. -/
@[expose] public section
set_option autoImplicit false
set_option linter.unusedSectionVars false
open Finset Classical
namespace WaveTurbulence.FinalCountG3
open WaveTurbulence WaveTurbulence.FinalCount

universe u
variable {V : Type*} [DecidableEq V] {D₀ : Type*}

section deg
variable {D : Type*} [Fintype D] [DecidableEq D] (M : Molecule V D)

theorem deg_eq (a : V) : M.deg a = M.outdeg a + M.indeg a := by
  unfold Molecule.deg Molecule.outdeg Molecule.indeg
  rw [← Finset.card_filter_add_card_filter_not (s := M.dartsAt a) (fun x => M.out x = true)]
  congr 2

theorem deg_le_four {a : V} (h : M.outdeg a ≤ 2 ∧ M.indeg a ≤ 2) : M.deg a ≤ 4 := by
  rw [deg_eq]; omega

/-- The degrees add up to the number of darts. -/
theorem sum_deg_eq : ∑ a ∈ M.atoms, M.deg a = Fintype.card D := by
  have := Finset.card_eq_sum_card_fiberwise (f := M.atom) (s := (Finset.univ : Finset D)) (t := M.atoms)
    (fun x _ => M.atom_mem x)
  rw [Finset.card_univ] at this
  rw [this]
  rfl

end deg

end WaveTurbulence.FinalCountG3
