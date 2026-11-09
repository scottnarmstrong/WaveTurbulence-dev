/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.Spine.SourceObjectFinite
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Spine.SourceVineData
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Api
/-! **L6-H port of main `WaveTurbulence.Foundations.Spine.SourceObjectFinite`** (sha256 in H/COPIED-SHA256SUMS): only the declarations that
depend on the vine-family carrier, re-stated over the low family `Src … Src.γL` (and L6-STEP1's
`Step1.VineCut Src.γL`); everything else is main's, by import.

 Finite designated source objects retain the deleted hyper bond in their encoding. -/
@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.GammaLow.FinalCount.H
open WaveTurbulence.LGSpine.SourceVine
variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]

namespace Src.VineLikeObject
open Src.VineLikeObject

def designation {M : Molecule V D} {S : Finset V} {a b : V} :
    Src.VineLikeObject Src.γL M S a b → Option D
  | .vc _ => none
  | .hyper R => some R.added

alias _root_.WaveTurbulence.GammaLow.FinalCount.Src.VineLikeObject.designation := _root_.WaveTurbulence.GammaLow.FinalCount.H.Src.VineLikeObject.designation
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

alias _root_.WaveTurbulence.GammaLow.FinalCount.Src.VineLikeObject.designation_injective := _root_.WaveTurbulence.GammaLow.FinalCount.H.Src.VineLikeObject.designation_injective
end Src.VineLikeObject

namespace Src.Object
open Src.Object

def finiteCode {M : Molecule V D} (P : Src.Object Src.γL M) : Finset V × V × V × Option D :=
  (P.atoms, P.upper, P.lower, P.shape.designation)

alias _root_.WaveTurbulence.GammaLow.FinalCount.Src.Object.finiteCode := _root_.WaveTurbulence.GammaLow.FinalCount.H.Src.Object.finiteCode
theorem finiteCode_injective {M : Molecule V D} :
    Function.Injective (@finiteCode V D _ _ _ M) := by
  rintro ⟨S, a, b, P⟩ ⟨T, x, y, Q⟩ he
  simp only [finiteCode, Prod.mk.injEq] at he
  obtain ⟨rfl, rfl, rfl, h⟩ := he
  have hPQ := Src.VineLikeObject.designation_injective h
  cases hPQ
  rfl

alias _root_.WaveTurbulence.GammaLow.FinalCount.Src.Object.finiteCode_injective := _root_.WaveTurbulence.GammaLow.FinalCount.H.Src.Object.finiteCode_injective
instance [Fintype V] {M : Molecule V D} : Finite (Src.Object Src.γL M) :=
  Finite.of_injective finiteCode finiteCode_injective

end Src.Object
end WaveTurbulence.GammaLow.FinalCount.H
