/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.AppBTripleFrameSignCap
import Mathlib.Tactic

/-! # Uniform orientation caps for any three actual incidences -/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.Mole
variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]

theorem appb_not_all_frame_signs {M : Molecule V D} {P : AppbPattern}
    (r : AppbRealization M P) (hM : M.IsMolecule) (v : V) (hv : v ∈ M.atoms)
    (e : Fin 3 ↪ Fin P.edges.length) (hinc : ∀ j,appbIncidence M v (r.edge (e j)).val = 1) (a : ℤˣ) :
    ¬∀ j,appbIncidenceSign M v (r.edge (e j)).val = a := by
  rcases Int.units_eq_one_or a with rfl | rfl
  · exact r.not_all_positive_frame_signs hM e hv
  · exact r.not_all_negative_frame_signs hM e hv hinc

end WaveTurbulence.Mole
