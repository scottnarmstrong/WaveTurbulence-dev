/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.Vine.A.VineGapTransport
/-! Literal equality of objects from support, ordered joints and added dart. -/
@[expose] public section
open WaveTurbulence.Induct
set_option autoImplicit false
namespace WaveTurbulence.VineA
open WaveTurbulence.Stage1 WaveTurbulence.LGSpine.SourceVine
variable {V V' D D' : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]
  [DecidableEq V'] [Fintype D'] [DecidableEq D']
  {M : Molecule V D} {N : Molecule V' D'}

/-- The optional added dart records both the shape tag and its hyper designation. -/
def objectAdded (O : Object M) : Option D := match O.shape with
  | .vc _ => none
  | .hyper R => some R.added

/-- These four data fields determine the actual object, including its shape. -/
theorem object_eq_of_data (O P : Object M) (hA : O.atoms = P.atoms)
    (hU : O.upper = P.upper) (hL : O.lower = P.lower)
    (hD : objectAdded O = objectAdded P) : O = P := by
  rcases O with ⟨A, a, b, C⟩
  rcases P with ⟨B, c, d, E⟩
  change A = B at hA
  change a = c at hU
  change b = d at hL
  subst B c d
  cases C with
  | vc h =>
    cases E with
    | vc k => rfl
    | hyper R => cases hD
  | hyper R =>
    cases E with
    | vc k => cases hD
    | hyper T =>
      have he : R.added = T.added := Option.some.inj hD
      cases R
      cases T
      cases he
      rfl

/-- Added darts are carried by the literal object transport. -/
theorem mapObject_added (F : MolIso M N) (O : Object M) :
    objectAdded (mapObject F O) = (objectAdded O).map F.d := by
  rcases O with ⟨A, a, b, C⟩
  cases C <;> rfl

end WaveTurbulence.VineA
