/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.GammaLow.Famc.Cover.Base
public import WaveTurbulence.Foundations.GammaLow.FinalCount.Src.Objects
public import WaveTurbulence.Foundations.Spine.SourceVineData
public import Mathlib.Data.Fintype.Powerset
/-! Finite designated source objects retain the deleted hyper bond in their encoding. -/
@[expose] public section
set_option autoImplicit false
-- Ported from main `Spine.SourceObjectFinite` (sha256 82f5e14dd5817a50f5798c53994f8c4ae226c946d65d6b71a1f042a5e925dfc6) to L6's `𝒱_γ` carrier `FinalCount.Src` (family parameter `γv`).
namespace WaveTurbulence.GammaLow.Famc
open WaveTurbulence.LGSpine WaveTurbulence.GammaLow.FinalCount.Src
open WaveTurbulence.LGSpine.SourceVine (TripleAt HasChosenPair atomGapKind IsDyadicScale InternalParent disjointF_of_subset disjointF_union)
set_option linter.unusedSectionVars false
variable {γv : ℝ}
variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]

namespace VineLikeObject

def designation {M : Molecule V D} {S : Finset V} {a b : V} :
    VineLikeObject γv M S a b → Option D
  | .vc _ => none
  | .hyper R => some R.added

theorem designation_injective {M : Molecule V D} {S : Finset V} {a b : V} :
    Function.Injective (designation (γv := γv) (M := M) (S := S) (a := a) (b := b)) := by
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

def finiteCode {M : Molecule V D} (P : Object γv M) : Finset V × V × V × Option D :=
  (P.atoms, P.upper, P.lower, VineLikeObject.designation P.shape)

theorem finiteCode_injective {M : Molecule V D} :
    Function.Injective (finiteCode (γv := γv) (M := M)) := by
  rintro ⟨S, a, b, P⟩ ⟨T, x, y, Q⟩ he
  simp only [finiteCode, Prod.mk.injEq] at he
  obtain ⟨rfl, rfl, rfl, h⟩ := he
  have hPQ := VineLikeObject.designation_injective h
  cases hPQ
  rfl

instance [Fintype V] {M : Molecule V D} : Finite (Object γv M) :=
  Finite.of_injective finiteCode finiteCode_injective

end Object

end WaveTurbulence.GammaLow.Famc
