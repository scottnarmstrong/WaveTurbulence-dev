/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.AppBCutExternalSign
import Mathlib.Tactic

/-! # The cut sign is the incidence sign at its internal endpoint -/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.Mole
variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]

theorem appb_cutSign_eq_internal (M : Molecule V D) (Y : Finset V) (x : D) (a b : V)
    (he : M.ends x = s(a,b)) (ha : a ∈ Y) (hb : b ∉ Y) :
    appbCutSign M Y x = appbIncidenceSign M a x := by
  have hne : b ≠ a := fun h => hb (h.symm ▸ ha)
  rcases Sym2.eq_iff.mp he with h | h
  all_goals simp [appbCutSign,appbIncidenceSign,h.1,ha,hb,hne]

end WaveTurbulence.Mole
