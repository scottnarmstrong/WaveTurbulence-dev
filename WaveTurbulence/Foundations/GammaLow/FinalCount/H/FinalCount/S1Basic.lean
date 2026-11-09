/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.FinalCount.S1Basic
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.FinalCount.SourceVinePartitionInput
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Molecule.VineObjects
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Spine.SourceObjectUnion
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Api
/-! **L6-H port of main `WaveTurbulence.Foundations.FinalCount.S1Basic`** (sha256 in H/COPIED-SHA256SUMS): only the declarations that
depend on the vine-family carrier, re-stated over the low family `Src … Src.γL` (and L6-STEP1's
`Step1.VineCut Src.γL`); everything else is main's, by import.


# Stage 1 combinatorics: atomic groups of vinechainlem

Basic dictionary between the atomic groups of TARGET vinechainlem (L1930-L1933, DH23 Lemma 8.1)
and the designated vine-like objects of the spine (`SourceVine.Object`).  Every HV, VC or HVC atom
set is the atom set of an actual `Object`, and conversely.  A double vine (DV) is the union of
two type-V vines meeting exactly in their joints.
-/
@[expose] public section
set_option autoImplicit false
set_option linter.unusedSectionVars false
namespace WaveTurbulence.GammaLow.FinalCount.H
open WaveTurbulence.Stage1
open Finset WaveTurbulence.LGSpine WaveTurbulence.LGSpine.SourceVine

variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]

/-- An atom set that is an HV, VC or HVC (the vine-like objects of TARGET `defvine`). -/
@[expose] def IsVineLikeSet (M : Molecule V D) (S : Finset V) : Prop :=
  ∃ a b, Src.IsHV Src.γL M S a b ∨ Src.IsVC Src.γL M S a b ∨ Src.IsHVC Src.γL M S a b

/-- An atomic group allowed in the collection of TARGET vinechainlem: HV, VC, HVC or DV. -/
@[expose] def IsStage1Group (M : Molecule V D) (S : Finset V) : Prop :=
  ∃ a b, Src.IsHV Src.γL M S a b ∨ Src.IsVC Src.γL M S a b ∨ Src.IsHVC Src.γL M S a b ∨ Src.IsDV Src.γL M S a b

theorem chain_pos_S1Basic {M : Molecule V D} {S : Finset V} {a b : V} {n : ℕ}
    (h : Src.Chain Src.γL M S a b n) : 1 ≤ n := by
  induction h with
  | single => exact le_rfl
  | append _ _ _ _ _ => omega

theorem isVineLikeSet_of_object {M : Molecule V D} (P : Src.Object Src.γL M) : IsVineLikeSet M P.atoms := by
  rcases P with ⟨S, a, b, shape⟩
  cases shape with
  | vc h => exact ⟨a, b, Or.inr (Or.inl h)⟩
  | hyper R =>
    obtain ⟨n, hn⟩ := R.adjoint.2
    have hpos := chain_pos_S1Basic hn
    by_cases h1 : n = 1
    · subst h1
      cases hn with
      | single hv => exact ⟨a, b, Or.inl ⟨R.added, R.ends_eq, hv⟩⟩
      | append hS _ _ _ => exact absurd (chain_pos_S1Basic hS) (by omega)
    · exact ⟨a, b, Or.inr (Or.inr ⟨R.added, R.ends_eq, R.adjoint.1, n, by omega, hn⟩)⟩

theorem object_of_isVineLikeSet {M : Molecule V D} {S : Finset V} (h : IsVineLikeSet M S) :
    ∃ P : Src.Object Src.γL M, P.atoms = S := by
  obtain ⟨a, b, h | h | h⟩ := h
  · obtain ⟨e, he, hX⟩ := h
    exact ⟨⟨S, a, b, .hyper ⟨e, he, ⟨hX.block, 1, Src.Chain.single hX⟩⟩⟩, rfl⟩
  · exact ⟨⟨S, a, b, .vc h⟩, rfl⟩
  · obtain ⟨e, he, hb, n, _, hn⟩ := h
    exact ⟨⟨S, a, b, .hyper ⟨e, he, ⟨hb, n, hn⟩⟩⟩, rfl⟩

theorem isVineLikeSet_iff_object {M : Molecule V D} {S : Finset V} :
    IsVineLikeSet M S ↔ ∃ P : Src.Object Src.γL M, P.atoms = S :=
  ⟨object_of_isVineLikeSet, fun ⟨P, hP⟩ => hP ▸ isVineLikeSet_of_object P⟩

theorem isStage1Group_of_vineLike {M : Molecule V D} {S : Finset V} (h : IsVineLikeSet M S) :
    IsStage1Group M S := by
  obtain ⟨a, b, h | h | h⟩ := h
  · exact ⟨a, b, Or.inl h⟩
  · exact ⟨a, b, Or.inr (Or.inl h)⟩
  · exact ⟨a, b, Or.inr (Or.inr (Or.inl h))⟩

theorem isVC_of_isVine {M : Molecule V D} {X : VineType} {S : Finset V} {a b : V}
    (h : M.IsVine X S a b) : Src.IsVC Src.γL M S a b := ⟨h.1, 1, Src.Chain.single (Src.isSomeVine_of_isVine' h)⟩

/-- The atom set of a type-V vine is vine-like. -/
theorem isVineLikeSet_of_isVine {M : Molecule V D} {X : VineType} {S : Finset V} {a b : V}
    (h : M.IsVine X S a b) : IsVineLikeSet M S := ⟨a, b, Or.inr (Or.inl (isVC_of_isVine h))⟩

/-- A member of the low family is a VC (low-range form of `isVC_of_isVine`). -/
theorem isVC_of_isSomeVine {M : Molecule V D} {S : Finset V} {a b : V}
    (h : Src.IsSomeVine Src.γL M S a b) : Src.IsVC Src.γL M S a b := ⟨h.block, 1, Src.Chain.single h⟩

/-- The atom set of a member of the low family is vine-like (low-range form of `isVineLikeSet_of_isVine`). -/
theorem isVineLikeSet_of_isSomeVine {M : Molecule V D} {S : Finset V} {a b : V}
    (h : Src.IsSomeVine Src.γL M S a b) : IsVineLikeSet M S := ⟨a, b, Or.inr (Or.inl (isVC_of_isSomeVine h))⟩

theorem isStage1Group_iff {M : Molecule V D} {S : Finset V} :
    IsStage1Group M S ↔ IsVineLikeSet M S ∨ ∃ a b, Src.IsDV Src.γL M S a b := by
  constructor
  · rintro ⟨a, b, h | h | h | h⟩
    · exact Or.inl ⟨a, b, Or.inl h⟩
    · exact Or.inl ⟨a, b, Or.inr (Or.inl h)⟩
    · exact Or.inl ⟨a, b, Or.inr (Or.inr h)⟩
    · exact Or.inr ⟨a, b, h⟩
  · rintro (h | ⟨a, b, h⟩)
    · exact isStage1Group_of_vineLike h
    · exact ⟨a, b, Or.inr (Or.inr (Or.inr h))⟩

theorem IsVineLikeSet.nonempty {M : Molecule V D} {S : Finset V} (h : IsVineLikeSet M S) :
    S.Nonempty := by
  obtain ⟨P, hP⟩ := object_of_isVineLikeSet h
  rcases P with ⟨T, a, b, shape⟩
  subst hP
  cases shape with
  | vc hv => exact ⟨a, hv.1.2.1⟩
  | hyper R => exact ⟨a, R.adjoint.1.2.1⟩

theorem Src.IsDV.nonempty {M : Molecule V D} {S : Finset V} {a b : V} (h : Src.IsDV Src.γL M S a b) :
    S.Nonempty := by
  obtain ⟨-, A, B, hA, _, _, rfl⟩ := h
  exact ⟨a, mem_union_left _ (Src.isBlock_of_isSomeVine hA).2.1⟩

alias _root_.WaveTurbulence.GammaLow.FinalCount.Src.IsDV.nonempty := _root_.WaveTurbulence.GammaLow.FinalCount.H.Src.IsDV.nonempty
theorem IsStage1Group.nonempty {M : Molecule V D} {S : Finset V} (h : IsStage1Group M S) :
    S.Nonempty := by
  rcases isStage1Group_iff.mp h with h | ⟨a, b, h⟩
  · exact IsVineLikeSet.nonempty h
  · exact Src.IsDV.nonempty h

end WaveTurbulence.GammaLow.FinalCount.H
