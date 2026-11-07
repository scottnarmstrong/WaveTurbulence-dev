/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.AppBIncidenceCounts
public import WaveTurbulence.Foundations.FinalCount.AppBLocalConservation
import Mathlib.Tactic

/-! # Exact orientation signs in local conservation coordinates -/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.Mole
open Finset
variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]

/-- Orientation of an outgoing representative as seen at an incident atom. -/
noncomputable def appbIncidenceSign (M : Molecule V D) (v : V) (x : D) : ℤˣ :=
  if M.atom x = v then 1 else -1

/-- A single actual incidence carries its prescribed unit sign. -/
theorem appb_incidence_sign_eq (M : Molecule V D) (v : V) (x : D)
    (hx : appbIncidence M v x = 1) {E : Type*} [AddCommGroup E] (a : E) :
    ((if M.atom x = v then a else 0)-(if M.atom (M.mate x) = v then a else 0)) =
      (appbIncidenceSign M v x : ℤ) • a := by
  by_cases h1 : M.atom x = v <;> by_cases h2 : M.atom (M.mate x) = v
  all_goals simp only [appbIncidence,h1,h2,ite_true,ite_false] at hx
  all_goals simp [appbIncidenceSign,h1,h2] <;> omega

/-- The actual sign predicate is precisely the source's opposite direction
predicate viewed from the chosen vertex. -/
theorem appb_incidence_sign_opposite (M : Molecule V D) (v : V) (x y : D) :
    appbIncidenceSign M v x ≠ appbIncidenceSign M v y ↔
      (M.atom x = v ↔ M.atom y ≠ v) := by
  by_cases hx : M.atom x = v <;> by_cases hy : M.atom y = v
  all_goals simp [appbIncidenceSign,hx,hy]

end WaveTurbulence.Mole
