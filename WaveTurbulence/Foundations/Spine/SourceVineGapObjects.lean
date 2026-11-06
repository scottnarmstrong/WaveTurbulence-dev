/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.Spine.SourceVineObjects
/-! Literal designated vine gaps and containment for the subpro/finalcount source inputs.
The designated hyper-adjoint convention is copied from the completed VINES interface. -/
@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.LGSpine.SourceVine
variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]
namespace HyperLikeRealization
variable {M : Molecule V D} {S : Finset V} {a b : V}
/-- TARGET defdiff: the hyper-object gap is the actual gap of this
specified adjoint, with lattice labels restricted to its surviving darts. -/
@[expose] def IsGap (R : HyperLikeRealization M S a b) {d : ℕ} (L : ℝ) (w : Mom d) (κ : D → (Fin d → ℤ)) (r : Mom d) : Prop :=
  (Molecule.eraseBond M R.added).IsBlockGap L w (fun x => κ x.1) S a r

/-- Owner reading 2026-11-04, flagged for source audit: hyper-object
containment uses atom-set inclusion, and equal atom groups require the same
designated deleted bond up to mates. Different designations of one group
are distinct non-nested objects (see the triple-bond audit example). -/
@[expose] def IsContained {A : Finset V} {x y : V} (P : HyperLikeRealization M A x y)
    (R : HyperLikeRealization M S a b) : Prop :=
  A ⊆ S ∧ (A=S → P.added=R.added ∨ P.added=M.mate R.added)

end HyperLikeRealization
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

end VineLikeObject
end WaveTurbulence.LGSpine.SourceVine
