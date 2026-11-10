/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Molecule.VineHyperGapObjects
import Mathlib.Tactic

/-! # Source vine-like objects retain the data needed to specify their gap

Owner reading 2026-11-04: hyper objects retain their designated adjoint bond;
equal hyper atom groups are nested only for the same bond up to mates.
-/

public section
namespace WaveTurbulence.Vine
variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]

/-- A source VC, HV or HVC with the actual designation retained in the
hyper case. The ordinary and hyper cases have exactly their source meanings. -/
inductive VineLikeObject (M : Molecule V D) (S : Finset V) (a b : V)
  | vc : IsVC M S a b → VineLikeObject M S a b
  | hyper : HyperLikeRealization M S a b → VineLikeObject M S a b

namespace VineLikeObject
variable {M : Molecule V D} {S A : Finset V} {a b x y : V}

/-- TARGET defdiff: an ordinary gap uses its block; a hyper gap uses its
specified adjoint with integer labels restricted to the surviving darts. -/
@[expose] def IsGap (C : VineLikeObject M S a b) {d : ℕ}
    (L : ℝ) (w : Mom d) (κ : D → (Fin d → ℤ)) (r : Mom d) : Prop :=
  match C with
  | .vc _ => M.IsBlockGap L w κ S a r
  | .hyper R => R.IsGap L w κ r

/-- TARGET subsetvc containment, with the explicit owner reading for equal
hyper groups. All other object pairs use ordinary atom-set inclusion. -/
@[expose] def IsContained (P : VineLikeObject M A x y) (C : VineLikeObject M S a b) : Prop :=
  match P,C with
  | .hyper P,.hyper C => P.IsContained C
  | _,_ => A ⊆ S

/-- Every designated-object containment includes the actual atom containment. -/
theorem atoms_subset (P : VineLikeObject M A x y) (C : VineLikeObject M S a b)
    (h : P.IsContained C) : A ⊆ S := by
  cases P <;> cases C
  · exact h
  · exact h
  · exact h
  · exact h.1

end VineLikeObject
end WaveTurbulence.Vine
