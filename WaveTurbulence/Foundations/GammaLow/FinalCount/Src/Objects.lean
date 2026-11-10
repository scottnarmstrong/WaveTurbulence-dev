/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.TVine.Defs
public import WaveTurbulence.Foundations.Spine.SourceVineData
/-! # The source vine-like objects over the family `𝒱_γ` (packet L6, FINALCOUNT-LOW)

A literal copy of main's `LGSpine.SourceVine` object layer (`SourceVineObjects`, `SourceVineGapObjects`,
`SourceVineData`; sha256 in `COPIED-SHA256SUMS`) with exactly one change: the vine family is the γ-dependent family
`𝒱_γ` of ruling D11 (`Molecule.IsVineGamma`, `TVine/Defs.lean`) instead of the eight drawn types, and the double vine
`DV` is `DV′` (`Molecule.IsDVPrime`). For `γ ≤ 1/2` the family is (I), (II) and the T-vines.

Main's `SourceVine.Object` cannot represent a T-vine, so the γ ≤ 1/2 final-count gate is stated over this carrier.
Family-free source helpers (`InternalParent`, `IsBlockGap`) are main's, by import. -/
@[expose] public section
set_option autoImplicit false
set_option linter.unusedSectionVars false
namespace WaveTurbulence.GammaLow.FinalCount.Src
open Finset
variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]

/-- One ingredient of `𝒱_γ` with ordered joints (ruling D11). Main: `∃ X : VineType, M.IsVine X S a b`. -/
def IsSomeVine (γ : ℝ) (M : Molecule V D) (S : Finset V) (a b : V) : Prop :=
  M.IsVineGamma γ S a b

/-- Every member of `𝒱_γ` is a block with its two joints. -/
theorem isBlock_of_isSomeVine {γ : ℝ} {M : Molecule V D} {S : Finset V} {a b : V}
    (h : IsSomeVine γ M S a b) : M.IsBlock S a b := by
  rcases h with ⟨-, h | h | h⟩ | ⟨-, X, h⟩
  · exact h.1
  · exact h.1
  · exact h.1
  · exact h.1

/-- Ordered concatenation of `𝒱_γ` vines, sharing just the joining joint at each step. -/
inductive Chain (γ : ℝ) (M : Molecule V D) : Finset V → V → V → ℕ → Prop
  | single {S a b} : IsSomeVine γ M S a b → Chain γ M S a b 1
  | append {S T a b c n} : Chain γ M S a b n → IsSomeVine γ M T b c →
      S ∩ T = {b} → a ≠ c → Chain γ M (S ∪ T) a c (n+1)

/-- TARGET defvine with `𝒱_γ`: a VC is a block formed by one or more vine ingredients. -/
def IsVC (γ : ℝ) (M : Molecule V D) (S : Finset V) (a b : V) : Prop :=
  M.IsBlock S a b ∧ ∃ n, Chain γ M S a b n

/-- TARGET defvine with `𝒱_γ`: an HV is the adjoint of a single vine (the deleted bond is remembered). -/
def IsHV (γ : ℝ) (M : Molecule V D) (S : Finset V) (a b : V) : Prop :=
  ∃ e : D, M.ends e = s(a,b) ∧ IsSomeVine γ (Molecule.eraseBond M e) S a b

/-- TARGET defvine with `𝒱_γ`: an HVC is an adjoint VC with at least two ingredients. -/
def IsHVC (γ : ℝ) (M : Molecule V D) (S : Finset V) (a b : V) : Prop :=
  ∃ e : D, M.ends e = s(a,b) ∧
    (Molecule.eraseBond M e).IsBlock S a b ∧
    ∃ n, 2 ≤ n ∧ Chain γ (Molecule.eraseBond M e) S a b n

/-- `DV′` (D11, note 3 Sec. 4.3; replaces "two vines (V)", TARGET `vinechainlem` L1930). -/
def IsDV (γ : ℝ) (M : Molecule V D) (S : Finset V) (a b : V) : Prop :=
  M.IsDVPrime γ S a b

/-- Source data for a hyper-vine-like object, retaining the bond which defines its adjoint VC. -/
structure HyperLikeRealization (γ : ℝ) (M : Molecule V D) (S : Finset V) (a b : V) where
  added : D
  ends_eq : M.ends added = s(a,b)
  adjoint : IsVC γ (Molecule.eraseBond M added) S a b

namespace HyperLikeRealization
variable {γ : ℝ} {M : Molecule V D} {S : Finset V} {a b : V}

/-- TARGET defdiff: the hyper-object gap is the gap of the specified adjoint. -/
def IsGap (R : HyperLikeRealization γ M S a b) {d : ℕ} (L : ℝ) (w : Mom d) (κ : D → (Fin d → ℤ))
    (r : Mom d) : Prop :=
  (Molecule.eraseBond M R.added).IsBlockGap L w (fun x => κ x.1) S a r

/-- Hyper-object containment: atom-set inclusion; equal atom groups require the same designated bond up to mates. -/
def IsContained {A : Finset V} {x y : V} (P : HyperLikeRealization γ M A x y)
    (R : HyperLikeRealization γ M S a b) : Prop :=
  A ⊆ S ∧ (A = S → P.added = R.added ∨ P.added = M.mate R.added)

end HyperLikeRealization

/-- A source VC, HV or HVC over `𝒱_γ`, with the designation retained in the hyper case. -/
inductive VineLikeObject (γ : ℝ) (M : Molecule V D) (S : Finset V) (a b : V)
  | vc : IsVC γ M S a b → VineLikeObject γ M S a b
  | hyper : HyperLikeRealization γ M S a b → VineLikeObject γ M S a b

namespace VineLikeObject
variable {γ : ℝ} {M : Molecule V D} {S A : Finset V} {a b x y : V}

/-- TARGET defdiff: an ordinary gap uses its block; a hyper gap uses its specified adjoint. -/
def IsGap (C : VineLikeObject γ M S a b) {d : ℕ}
    (L : ℝ) (w : Mom d) (κ : D → (Fin d → ℤ)) (r : Mom d) : Prop :=
  match C with
  | .vc _ => M.IsBlockGap L w κ S a r
  | .hyper R => R.IsGap L w κ r

/-- TARGET subsetvc containment, with the owner reading for equal hyper groups. -/
def IsContained (P : VineLikeObject γ M A x y) (C : VineLikeObject γ M S a b) : Prop :=
  match P, C with
  | .hyper P, .hyper C => P.IsContained C
  | _, _ => A ⊆ S

end VineLikeObject

/-- A designated vine-like object over `𝒱_γ`, including its atom set and ordered joints. -/
structure Object (γ : ℝ) (M : Molecule V D) where
  atoms : Finset V
  upper : V
  lower : V
  shape : VineLikeObject γ M atoms upper lower

namespace Object
variable {γ : ℝ} {M : Molecule V D}

/-- TARGET defdiff: the gap kind of an object (hyper-objects use the designated adjoint). -/
def HasGapKind {d : ℕ} (C : Object γ M) (L γ' η : ℝ) (w : Mom d)
    (κ : D → (Fin d → ℤ)) (kind : Molecule.GapKind) : Prop :=
  ∃ r, C.shape.IsGap L w κ r ∧ Molecule.gapKind L γ' η r = kind

/-- Source containment (retains a hyper-object's deleted bond when atom sets coincide). -/
def IsContained (A B : Object γ M) : Prop := A.shape.IsContained B.shape

/-- Membership of a bond in the object; a hyper-object excludes both darts of its deleted bond. -/
def ContainsDart (C : Object γ M) (x : D) : Prop :=
  match C.shape with
  | .vc _ => M.InGroup C.atoms x
  | .hyper R => x ≠ R.added ∧ x ≠ M.mate R.added ∧ M.InGroup C.atoms x

/-- Interior atoms exclude both joints. -/
def IsInterior (P : Object γ M) (v : V) : Prop :=
  v ∈ P.atoms ∧ v ≠ P.upper ∧ v ≠ P.lower

/-- The object of a single `𝒱_γ` vine. -/
noncomputable def ofVine {S : Finset V} {a b : V} (h : IsSomeVine γ M S a b) : Object γ M :=
  ⟨S, a, b, .vc ⟨isBlock_of_isSomeVine h, 1, Chain.single h⟩⟩

end Object

/-- TARGET subpro(2), L2043, with `𝒱_γ`: an HV, a CN vine, or a root CL vine (joint degrees sum ≤ 6, TARGET L1368). -/
def AllowedCollectionObject {w : ℕ} (γ : ℝ) (G : Garden w) (C : Object γ G.molecule) : Prop :=
  match C.shape with
  | .hyper R => IsSomeVine γ (Molecule.eraseBond G.molecule R.added) C.atoms C.upper C.lower
  | .vc _ => IsSomeVine γ G.molecule C.atoms C.upper C.lower ∧
      ((¬ LGSpine.SourceVine.InternalParent G C.atoms C.upper ∧
          ¬ LGSpine.SourceVine.InternalParent G C.atoms C.lower) ∨
        ((¬ LGSpine.SourceVine.InternalParent G C.atoms C.upper ∧
            LGSpine.SourceVine.InternalParent G C.atoms C.lower) ∨
          (¬ LGSpine.SourceVine.InternalParent G C.atoms C.lower ∧
            LGSpine.SourceVine.InternalParent G C.atoms C.upper)) ∧
          G.molecule.deg C.upper + G.molecule.deg C.lower ≤ 6)

end WaveTurbulence.GammaLow.FinalCount.Src
