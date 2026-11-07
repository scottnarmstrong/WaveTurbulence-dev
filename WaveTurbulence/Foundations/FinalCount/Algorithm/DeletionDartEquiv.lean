/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.AppBStatistics
public import WaveTurbulence.Foundations.Molecule.Degen.ComponentQuotient
import Mathlib.Tactic

/-! # Literal dart flattening for successive atom deletions

The generic equivalence proofs are ported from G6 DoublePairCircuit,
L17–60 and L71–87; its source hash is pinned separately.
-/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.Mole.AppbAlgorithm
open Finset
open WaveTurbulence.Degen
variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]

theorem numComponents_and_circuitRank_eq_of_dart_equiv {E : Type*} [Fintype E] [DecidableEq E]
    (M : Molecule V D) (N : Molecule V E) (f : D ≃ E)
    (hA : M.atoms = N.atoms) (ha : ∀ x, N.atom (f x) = M.atom x)
    (hm : ∀ x, N.mate (f x) = f (M.mate x)) (ho : ∀ x, N.out (f x) = M.out x) :
    M.numComponents = N.numComponents ∧ M.circuitRank = N.circuitRank := by
  classical
  have hE : M.bonds.card = N.bonds.card := by
    apply card_bij (fun x _ => f x)
    · intro x hx
      exact mem_filter.mpr ⟨mem_univ _,(ho x).trans (mem_filter.mp hx).2⟩
    · intro x _ y _ h
      exact f.injective h
    · intro y hy
      refine ⟨f.symm y,?_,f.apply_symm_apply y⟩
      apply mem_filter.mpr
      refine ⟨mem_univ _,?_⟩
      have hh := ho (f.symm y)
      rw [f.apply_symm_apply] at hh
      exact hh.symm.trans (mem_filter.mp hy).2
  have hAdj (a b : V) : M.Adj a b ↔ N.Adj a b := by
    constructor
    · rintro ⟨x,hx,hxm⟩
      refine ⟨f x,(ha x).trans hx,?_⟩
      rw [hm,ha]
      exact hxm
    · rintro ⟨y,hy,hym⟩
      obtain ⟨x,rfl⟩ := f.surjective y
      refine ⟨x,(ha x).symm.trans hy,?_⟩
      rw [hm,ha] at hym
      exact hym
  have hSame (a b : V) : M.SameComponent a b ↔ N.SameComponent a b :=
    ⟨fun h => Relation.EqvGen.mono (fun a b h => (hAdj a b).mp h) a b h,
      fun h => Relation.EqvGen.mono (fun a b h => (hAdj a b).mpr h) a b h⟩
  have hset : componentSet M = componentSet N := by
    funext a
    ext b
    simp only [mem_componentSet,hA,hSame]
  have hF : M.numComponents = N.numComponents := by
    rw [numComponents_eq_card_componentSets,numComponents_eq_card_componentSets]
    unfold componentSets
    rw [hA,hset]
  refine ⟨hF,?_⟩
  unfold Molecule.circuitRank
  rw [hE,hA,hF]

def eraseDartUnionEquiv (M : Molecule V D) (Y Z : Finset V) :
    RetainedDart (eraseAtoms M Y) Z ≃ RetainedDart M (Y ∪ Z) where
  toFun x := ⟨x.val.val,by
    constructor
    · intro h
      rcases mem_union.mp h with h | h
      · exact x.val.property.1 h
      · exact x.property.1 h
    · intro h
      rcases mem_union.mp h with h | h
      · exact x.val.property.2 h
      · exact x.property.2 h⟩
  invFun x := ⟨⟨x.val,fun h => x.property.1 (mem_union_left _ h),
      fun h => x.property.2 (mem_union_left _ h)⟩,
    fun h => x.property.1 (mem_union_right _ h),fun h => x.property.2 (mem_union_right _ h)⟩
  left_inv x := Subtype.ext (Subtype.ext rfl)
  right_inv x := Subtype.ext rfl


theorem appbNu_eq_of_dart_equiv {E : Type*} [Fintype E] [DecidableEq E]
    (M : Molecule V D) (N : Molecule V E) (f : D ≃ E)
    (hA : M.atoms = N.atoms) (ha : ∀ x,N.atom (f x) = M.atom x)
    (hm : ∀ x,N.mate (f x) = f (M.mate x)) (ho : ∀ x,N.out (f x) = M.out x) :
    appbNu M = appbNu N := by
  have hh := numComponents_and_circuitRank_eq_of_dart_equiv M N f hA ha hm ho
  rw [appbNu_eq_rank M,appbNu_eq_rank N,hA,hh.1,hh.2]

theorem appbNu_erase_erase_eq_union (M : Molecule V D) (Y Z : Finset V) :
    appbNu (eraseAtoms (eraseAtoms M Y) Z) = appbNu (eraseAtoms M (Y ∪ Z)) := by
  apply appbNu_eq_of_dart_equiv _ _ (eraseDartUnionEquiv M Y Z)
  · ext a
    change (a ∈ (M.atoms \ Y) \ Z) ↔ a ∈ M.atoms \ (Y ∪ Z)
    simp only [mem_sdiff,mem_union,not_or]
    tauto
  · intro x; rfl
  · intro x; exact Subtype.ext rfl
  · intro x; rfl

def eraseEmptyDartEquiv (M : Molecule V D) : RetainedDart M ∅ ≃ D where
  toFun := Subtype.val
  invFun x := ⟨x,by simp⟩
  left_inv x := Subtype.ext rfl
  right_inv x := rfl

theorem appbNu_erase_empty (M : Molecule V D) : appbNu (eraseAtoms M ∅) = appbNu M := by
  apply appbNu_eq_of_dart_equiv _ _ (eraseEmptyDartEquiv M)
  · exact sdiff_empty
  · intro x; rfl
  · intro x; rfl
  · intro x; rfl

end WaveTurbulence.Mole.AppbAlgorithm
