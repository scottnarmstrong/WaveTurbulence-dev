/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.AppBCutPair
public import WaveTurbulence.Foundations.FinalCount.AppBIncidenceSigns
import Mathlib.Tactic

/-! # Opposite orientation at the two sides of an actual cut bond -/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.Mole
variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]

theorem appb_cutSign_eq_neg_external (M : Molecule V D) (Y : Finset V) (x : D) (a b : V)
    (he : M.ends x = s(a,b)) (ha : a ∈ Y) (hb : b ∉ Y) :
    appbCutSign M Y x = -appbIncidenceSign M b x := by
  have hne : a ≠ b := fun h => hb (h ▸ ha)
  rcases Sym2.eq_iff.mp he with h | h
  all_goals simp [appbCutSign,appbIncidenceSign,h.1,ha,hb,hne,hne.symm]

end WaveTurbulence.Mole
