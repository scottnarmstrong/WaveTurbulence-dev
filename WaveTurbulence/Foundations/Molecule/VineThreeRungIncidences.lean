/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Molecule.VineBlockMarkers
public import WaveTurbulence.Foundations.Molecule.VineRungEndpoints
import Mathlib.Tactic

/-! # Matched membership on three actual full rungs (TARGET subsetvc)

The hypothesis records actual darts and their neighbors. Degree at most four
then derives the recurrence. The two-joint budget is derived from the actual
joint set, rather than supplied as a separate estimate.
-/

public section
namespace WaveTurbulence.Vine
open Finset
variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]

/-- Three successive full rungs and the two neighboring rail positions.
Only the six internal rung atoms must be distinct. -/
structure ThreeRungIncidences (M : Molecule V D) where
  u : ℕ → V
  v : ℕ → V
  distinct : Function.Injective ![u 1,u 2,u 3,v 1,v 2,v 3]
  d1 : FourIncidences M (u 1) ![v 1,v 1,u 0,u 2]
  d2 : FourIncidences M (u 2) ![v 2,v 2,u 1,u 3]
  d3 : FourIncidences M (u 3) ![v 3,v 3,u 2,u 4]
  e1 : FourIncidences M (v 1) ![u 1,u 1,v 0,v 2]
  e2 : FourIncidences M (v 2) ![u 2,u 2,v 1,v 3]
  e3 : FourIncidences M (v 3) ![u 3,u 3,v 2,v 4]

/-- Actual block and incidence data derive all six recurrence equations. -/
@[expose] def blockStrip_of_incidences (M : Molecule V D) (hM : M.IsMolecule)
    {S : Finset V} {a b : V} (hB : M.IsBlock S a b) (R : ThreeRungIncidences M) : BlockStrip where
  b := fun i => jointIndicator S (R.u i)
  c := fun i => jointIndicator S (R.v i)
  j := fun i => jointIndicator ({a,b} : Finset V) (R.u i)
  k := fun i => jointIndicator ({a,b} : Finset V) (R.v i)
  bBound := fun i _hi => jointIndicator_le_one S (R.u i)
  cBound := fun i _hi => jointIndicator_le_one S (R.v i)
  jBound := fun i _hi => jointIndicator_le_one {a,b} (R.u i)
  kBound := fun i _hi => jointIndicator_le_one {a,b} (R.v i)
  budget := three_rung_joint_budget {a,b} (by rw [card_pair hB.2.2.2.1])
    (R.u 1) (R.u 2) (R.u 3) (R.v 1) (R.v 2) (R.v 3) R.distinct
  d1 := fun h => rung_degree_marker M hM hB R.d1 ((jointIndicator_eq_one_iff S _).mp h)
  d2 := fun h => rung_degree_marker M hM hB R.d2 ((jointIndicator_eq_one_iff S _).mp h)
  d3 := fun h => rung_degree_marker M hM hB R.d3 ((jointIndicator_eq_one_iff S _).mp h)
  e1 := fun h => rung_degree_marker M hM hB R.e1 ((jointIndicator_eq_one_iff S _).mp h)
  e2 := fun h => rung_degree_marker M hM hB R.e2 ((jointIndicator_eq_one_iff S _).mp h)
  e3 := fun h => rung_degree_marker M hM hB R.e3 ((jointIndicator_eq_one_iff S _).mp h)

/-- In an actual molecule, a block cannot split either atom pair of a
three-rung full strip. No hypothesis assumes matched rung membership. -/
theorem block_three_rungs_membership (M : Molecule V D) (hM : M.IsMolecule)
    {S : Finset V} {a b : V} (hB : M.IsBlock S a b) (R : ThreeRungIncidences M) :
    (R.u 1 ∈ S ↔ R.v 1 ∈ S) ∧ (R.u 2 ∈ S ↔ R.v 2 ∈ S) ∧
      (R.u 3 ∈ S ↔ R.v 3 ∈ S) := by
  have h := three_rungs_equal (blockStrip_of_incidences M hM hB R)
  exact ⟨(jointIndicator_eq_iff S _ _).mp h.1,
    (jointIndicator_eq_iff S _ _).mp h.2.1,(jointIndicator_eq_iff S _ _).mp h.2.2⟩

end WaveTurbulence.Vine
