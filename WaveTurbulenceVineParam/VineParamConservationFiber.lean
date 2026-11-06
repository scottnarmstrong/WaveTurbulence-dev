/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulenceVineParam.VineParamCurrentBlocks

public import WaveTurbulenceVineParam.VineParamIntegerMatrices
import Mathlib.Tactic

/-! # From full integer coordinate certificates to fixed-gap conservation fibers

The full vector consists of the free coordinates, one fixed gap, and zero
internal divergences. The zero entries are the actual source momentum
conservation equations, not a value assigned outside a valid locus.
-/

public section
namespace WaveTurbulence.Vine.Param
variable {E : Type*} [AddCommGroup E] {n q : ℕ}

/-- Free coordinates, followed by the joint gap and the zero internal divergences. -/
@[expose] def packCoordinates (_hq : q<n) (x : Fin q → E) (r : E) : Fin n → E :=
  fun i => if hi : i.1<q then x ⟨i.1,hi⟩ else if i.1=q then r else 0

/-- Read the free-coordinate block of a full coordinate vector. -/
@[expose] def freeCoordinates (hq : q<n) (y : Fin n → E) : Fin q → E :=
  fun i => y ⟨i.1,lt_trans i.2 hq⟩

/-- Packing followed by reading recovers all free coordinates. -/
theorem free_pack (hq : q<n) (x : Fin q → E) (r : E) :
    freeCoordinates hq (packCoordinates hq x r)=x := by
  funext i
  simp only [freeCoordinates,packCoordinates,dite_eq_left i.2]

/-- The packed vector has precisely the prescribed joint gap. -/
theorem pack_gap (hq : q<n) (x : Fin q → E) (r : E) :
    packCoordinates hq x r ⟨q,hq⟩=r := by
  simp only [packCoordinates,dite_eq_right (Nat.lt_irrefl q),ite_true]

/-- Actual internal momentum equations and a fixed gap determine the rest
of a coordinate vector after its free block is specified. -/
theorem pack_of_conservation (hq : q<n) (y : Fin n → E) (r : E)
    (hgap : y ⟨q,hq⟩=r) (hzero : ∀ i : Fin n, q < i.1 → y i=0) :
    packCoordinates hq (freeCoordinates hq y) r=y := by
  funext i
  by_cases hi : i.1<q
  · simp only [packCoordinates,dite_eq_left hi,freeCoordinates]
  · simp only [packCoordinates,dite_eq_right hi]
    by_cases he : i.1=q
    · have hei : i=⟨q,hq⟩ := Fin.ext he
      subst i
      simp only [ite_true,hgap]
    · rw [ite_eq_right he,hzero i (by omega)]

/-- A produced inverse certificate reconstructs all source labels from their
free coordinates and gap. This generic assembly helper is not a source result. -/
theorem reconstruct_of_integer_certificate (hq : q<n)
    (A B : Matrix (Fin n) (Fin n) ℤ) (hBA : B*A=1) (k : Fin n → E) (r : E)
    (hgap : intEval A k ⟨q,hq⟩=r)
    (hzero : ∀ i : Fin n, q < i.1 → intEval A k i=0) :
    intEval B (packCoordinates hq (freeCoordinates hq (intEval A k)) r)=k := by
  rw [pack_of_conservation hq _ r hgap hzero,← intEval_mul,hBA,intEval_one]

/-- Conversely, arbitrary free coordinates reconstruct a full vector with
exactly those free coordinates, the prescribed gap, and zero divergences. -/
theorem coordinates_of_integer_certificate (hq : q<n)
    (A B : Matrix (Fin n) (Fin n) ℤ) (hAB : A*B=1) (x : Fin q → E) (r : E) :
    intEval A (intEval B (packCoordinates hq x r))=packCoordinates hq x r := by
  rw [← intEval_mul,hAB,intEval_one]

end WaveTurbulence.Vine.Param
