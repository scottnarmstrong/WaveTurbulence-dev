/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.Algorithm.Termination
public import WaveTurbulence.Foundations.FinalCount.Algorithm.GeometricMass
import Mathlib.Tactic

/-! # Nonempty actual operation sequences strictly decrease the forest measures -/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.Mole.AppbAlgorithm
universe u v
variable {V : Type v} [DecidableEq V]

theorem Trace.atomPotential_le {s t : State.{u,v} V} {n : ℕ} (h : Trace s t n) :
    t.atomPotential ≤ s.atomPotential := by
  induction h with
  | nil s => exact le_rfl
  | cons hs ht ih => exact ih.trans hs.atomPotential_le

theorem Trace.bondPotential_lt {s t : State.{u,v} V} {n : ℕ}
    (h : Trace s t n) (hn : 0 < n) : t.bondPotential < s.bondPotential := by
  have hh := h.bond_budget
  omega

theorem Trace.mass_lt {s t : State.{u,v} V} {n : ℕ}
    (h : Trace s t n) (hn : 0 < n) : t.mass < s.mass := by
  have he := h.bondPotential_lt hn
  have hv := h.atomPotential_le
  change t.bondPotential+t.atomPotential < s.bondPotential+s.atomPotential
  omega

end WaveTurbulence.Mole.AppbAlgorithm
