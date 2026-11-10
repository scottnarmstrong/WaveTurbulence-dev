/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.FinalCount.SourceVinePartitionInput
public import WaveTurbulence.Foundations.Spine.SourceObjectUnion
public import WaveTurbulence.Foundations.Molecule.VineObjects
import Mathlib.Tactic

/-!
# Stage 1 combinatorics: atomic groups of vinechainlem

Basic dictionary between the atomic groups of TARGET vinechainlem (L1930-L1933, DH23 Lemma 8.1)
and the designated vine-like objects of the spine (`SourceVine.Object`).  Every HV, VC or HVC atom
set is the atom set of an actual `Object`, and conversely.  A double vine (DV) is the union of
two type-V vines meeting exactly in their joints.
-/

@[expose] public section
set_option autoImplicit false
set_option linter.unusedSectionVars false
namespace WaveTurbulence.Stage1
open Finset WaveTurbulence.LGSpine WaveTurbulence.LGSpine.SourceVine

variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]

/-- An atom set that is an HV, VC or HVC (the vine-like objects of TARGET `defvine`). -/
@[expose] def IsVineLikeSet (M : Molecule V D) (S : Finset V) : Prop :=
  ∃ a b, IsHV M S a b ∨ IsVC M S a b ∨ IsHVC M S a b

/-- An atomic group allowed in the collection of TARGET vinechainlem: HV, VC, HVC or DV. -/
@[expose] def IsStage1Group (M : Molecule V D) (S : Finset V) : Prop :=
  ∃ a b, IsHV M S a b ∨ IsVC M S a b ∨ IsHVC M S a b ∨ IsDV M S a b

theorem chain_pos {M : Molecule V D} {S : Finset V} {a b : V} {n : ℕ}
    (h : Chain M S a b n) : 1 ≤ n := by
  induction h with
  | single => exact le_rfl
  | append _ _ _ _ _ => omega

theorem isVineLikeSet_of_object {M : Molecule V D} (P : Object M) : IsVineLikeSet M P.atoms := by
  rcases P with ⟨S, a, b, shape⟩
  cases shape with
  | vc h => exact ⟨a, b, Or.inr (Or.inl h)⟩
  | hyper R =>
    obtain ⟨n, hn⟩ := R.adjoint.2
    have hpos := chain_pos hn
    by_cases h1 : n = 1
    · subst h1
      cases hn with
      | single hv => exact ⟨a, b, Or.inl ⟨R.added, R.ends_eq, hv⟩⟩
      | append hS _ _ _ => exact absurd (chain_pos hS) (by omega)
    · exact ⟨a, b, Or.inr (Or.inr ⟨R.added, R.ends_eq, R.adjoint.1, n, by omega, hn⟩)⟩

theorem object_of_isVineLikeSet {M : Molecule V D} {S : Finset V} (h : IsVineLikeSet M S) :
    ∃ P : Object M, P.atoms = S := by
  obtain ⟨a, b, h | h | h⟩ := h
  · obtain ⟨e, he, X, hX⟩ := h
    exact ⟨⟨S, a, b, .hyper ⟨e, he, ⟨hX.1, 1, Chain.single ⟨X, hX⟩⟩⟩⟩, rfl⟩
  · exact ⟨⟨S, a, b, .vc h⟩, rfl⟩
  · obtain ⟨e, he, hb, n, _, hn⟩ := h
    exact ⟨⟨S, a, b, .hyper ⟨e, he, ⟨hb, n, hn⟩⟩⟩, rfl⟩

theorem isStage1Group_of_vineLike {M : Molecule V D} {S : Finset V} (h : IsVineLikeSet M S) :
    IsStage1Group M S := by
  obtain ⟨a, b, h | h | h⟩ := h
  · exact ⟨a, b, Or.inl h⟩
  · exact ⟨a, b, Or.inr (Or.inl h)⟩
  · exact ⟨a, b, Or.inr (Or.inr (Or.inl h))⟩

theorem isVC_of_isVine {M : Molecule V D} {X : VineType} {S : Finset V} {a b : V}
    (h : M.IsVine X S a b) : IsVC M S a b := ⟨h.1, 1, Chain.single ⟨X, h⟩⟩

/-- The atom set of a type-V vine is vine-like. -/
theorem isVineLikeSet_of_isVine {M : Molecule V D} {X : VineType} {S : Finset V} {a b : V}
    (h : M.IsVine X S a b) : IsVineLikeSet M S := ⟨a, b, Or.inr (Or.inl (isVC_of_isVine h))⟩

theorem isStage1Group_iff {M : Molecule V D} {S : Finset V} :
    IsStage1Group M S ↔ IsVineLikeSet M S ∨ ∃ a b, IsDV M S a b := by
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

theorem IsDV.nonempty {M : Molecule V D} {S : Finset V} {a b : V} (h : IsDV M S a b) :
    S.Nonempty := by
  obtain ⟨A, B, hA, _, _, rfl⟩ := h
  exact ⟨a, mem_union_left _ hA.1.2.1⟩

theorem IsStage1Group.nonempty {M : Molecule V D} {S : Finset V} (h : IsStage1Group M S) :
    S.Nonempty := by
  rcases isStage1Group_iff.mp h with h | ⟨a, b, h⟩
  · exact IsVineLikeSet.nonempty h
  · exact IsDV.nonempty h

end WaveTurbulence.Stage1
