/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.Spine.SourceVineData
public import Mathlib.Data.Fintype.Powerset
/-! Finite designated source objects retain the deleted hyper bond in their encoding. -/
@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.LGSpine.SourceVine
variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]

namespace VineLikeObject

def designation {M : Molecule V D} {S : Finset V} {a b : V} :
    VineLikeObject M S a b → Option D
  | .vc _ => none
  | .hyper R => some R.added

theorem designation_injective {M : Molecule V D} {S : Finset V} {a b : V} :
    Function.Injective (@designation V D _ _ _ M S a b) := by
  intro P Q he
  cases P with
  | vc hP =>
    cases Q with
    | vc hQ => rfl
    | hyper R => cases he
  | hyper R =>
    cases Q with
    | vc hQ => cases he
    | hyper T =>
      cases R with
      | mk e he₁ ha₁ =>
        cases T with
        | mk f he₂ ha₂ =>
          have hef : e = f := Option.some.inj he
          subst f
          rfl

end VineLikeObject

namespace Object

def finiteCode {M : Molecule V D} (P : Object M) : Finset V × V × V × Option D :=
  (P.atoms, P.upper, P.lower, P.shape.designation)

theorem finiteCode_injective {M : Molecule V D} :
    Function.Injective (@finiteCode V D _ _ _ M) := by
  rintro ⟨S, a, b, P⟩ ⟨T, x, y, Q⟩ he
  simp only [finiteCode, Prod.mk.injEq] at he
  obtain ⟨rfl, rfl, rfl, h⟩ := he
  have hPQ := VineLikeObject.designation_injective h
  cases hPQ
  rfl

instance [Fintype V] {M : Molecule V D} : Finite (Object M) :=
  Finite.of_injective finiteCode finiteCode_injective

end Object
end WaveTurbulence.LGSpine.SourceVine
