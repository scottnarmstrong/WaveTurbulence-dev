/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Molecule.VineCoreMasks
public import WaveTurbulence.Foundations.Molecule.VineIncidence
import Mathlib.Tactic

/-! # Degree masks are the actual degrees of induced template subsets -/

public section
namespace WaveTurbulence.Vine

/-- The 0/1 membership mask of a finite atom set. -/
@[expose] def membershipMask (S : Finset ℕ) (v : ℕ) : ℕ := if v ∈ S then 1 else 0

/-- Counting selected endpoints agrees with the induced edge-list degree. -/
theorem masked_degree_eq (es : List (ℕ×ℕ)) (S : Finset ℕ) (v : ℕ) (hv : v ∈ S) :
    edgeDegree (es.filter (fun e => decide (e.1 ∈ S ∧ e.2 ∈ S))) v =
      (es.map (fun e => if e.1=v then membershipMask S e.2 else 0)).sum +
      (es.map (fun e => if e.2=v then membershipMask S e.1 else 0)).sum := by
  induction es with
  | nil => rfl
  | cons e es ih =>
    rcases e with ⟨a,b⟩
    by_cases ha : a=v <;> by_cases hb : b=v <;>
      by_cases haS : a ∈ S <;> by_cases hbS : b ∈ S
    all_goals simp_all [edgeDegree,membershipMask,List.map_cons,List.sum_cons]
    all_goals omega

/-- The matrix used for finite-core classification is exactly the induced
template degree, with no additional graph assumptions. -/
theorem coreDegree_membershipMask (X : VineType) (S : Finset ℕ) (v : ℕ) (hv : v ∈ S) :
    coreDegree X (membershipMask S) v =
      edgeDegree (X.template.bonds.filter (fun e => decide (e.1 ∈ S ∧ e.2 ∈ S))) v :=
  (masked_degree_eq X.template.bonds S v hv).symm

end WaveTurbulence.Vine
