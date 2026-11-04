/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.RegStruct.NormalizeRetraction

/-! # Substitution at an oriented leaf pair (DH21 Proposition 4.8, case 1)

Intermediate codes permit redundant outer constructors; normalization is
separate. A nonmatching trivial slot is unchanged, and every matching slot is
filled by the input couple. The actual pairing relation is tracked below.
-/

@[expose] public section
namespace WaveTurbulence.Reg
open TTree

mutual
/-- Substitute a couple at a specified oriented pair of global leaf addresses. -/
def substituteCouplePair {w : ℕ} : RegCpl → (Fin w × Path) → (Fin w × Path) →
    (Fin w × Path) → (Fin w × Path) → RegCpl → RegCpl
  | .triv, a, b, x, y, S => if a = x ∧ b = y then S else .triv
  | .type1 c r g d, a, b, x, y, S =>
    .type1 c
      (substituteCouplePair r (addrExt a [0]) (addrExt b [c.partner 0]) x y S)
      (substituteCouplePair g (addrExt b [1]) (addrExt a [1]) x y S)
      (substituteCouplePair d (addrExt a [2]) (addrExt b [c.partner 2]) x y S)
  | .type2 p m q, a, b, x, y, S =>
    .type2 (substituteChainPair p 1 a x y S) (substituteChainPair m (-1) b x y S)
      (substituteCouplePair q (addrExt a p.lonePath) (addrExt b m.lonePath) x y S)

/-- Substitute into the side couples of a chain, retaining its spine. -/
def substituteChainPair {w : ℕ} : RegChain → ℤˣ → (Fin w × Path) →
    (Fin w × Path) → (Fin w × Path) → RegCpl → RegChain
  | .nil, _, _, _, _, _ => .nil
  | .pair m r g i s, ζ, a, x, y, S =>
    .pair m
      (if slotSign ζ m.red.1 = 1 then
        substituteCouplePair r (addrExt a [m.red.1])
          (addrExt a ([m.c] ++ i.lonePath ++ [m.red.2])) x y S
      else substituteCouplePair r (addrExt a ([m.c] ++ i.lonePath ++ [m.red.2]))
        (addrExt a [m.red.1]) x y S)
      (if slotSign ζ m.green.1 = 1 then
        substituteCouplePair g (addrExt a [m.green.1])
          (addrExt a ([m.c] ++ i.lonePath ++ [m.green.2])) x y S
      else substituteCouplePair g (addrExt a ([m.c] ++ i.lonePath ++ [m.green.2]))
        (addrExt a [m.green.1]) x y S)
      (substituteChainPair i (slotSign ζ m.c) (addrExt a [m.c]) x y S)
      (substituteChainPair s (slotSign (slotSign ζ m.c) m.lone)
        (addrExt a ([m.c] ++ i.lonePath ++ [m.lone])) x y S)
end

/-- Side-couple substitution preserves the actual lone path. -/
theorem substituteChainPair_lonePath {w : ℕ} (X : RegChain) (ζ : ℤˣ)
    (a x y : Fin w × Path) (S : RegCpl) :
    (substituteChainPair X ζ a x y S).lonePath = X.lonePath := by
  cases X with
  | nil => rfl
  | pair m r g i s =>
    simp only [substituteChainPair, RegChain.lonePath, substituteChainPair_lonePath i,
      substituteChainPair_lonePath s]
termination_by structural X

/-- Replace every occurrence of one listed pair by a prescribed list. -/
def splicePairs {α : Type*} [DecidableEq α] (P : List α) (t : α) (S : List α) : List α :=
  P.flatMap fun p => if p = t then S else [p]

theorem splicePairs_append {α : Type*} [DecidableEq α] (P Q : List α) (t : α) (S : List α) :
    splicePairs (P ++ Q) t S = splicePairs P t S ++ splicePairs Q t S := by
  simp only [splicePairs, List.flatMap_append]

mutual
/-- Substitution acts on the literal ordered pair list by splicing at the chosen pair. -/
theorem substituteCouplePair_pairsAt {w : ℕ} (Q : RegCpl) (a b x y : Fin w × Path) (S : RegCpl) :
    (substituteCouplePair Q a b x y S).pairsAt a b =
      splicePairs (Q.pairsAt a b) (x,y) (S.pairsAt x y) := by
  cases Q with
  | triv =>
    by_cases h : a = x ∧ b = y
    · obtain ⟨rfl,rfl⟩ := h
      simp [substituteCouplePair, RegCpl.pairsAt, splicePairs]
    · have hp : (a,b) ≠ (x,y) := fun he => h (Prod.mk.inj he)
      simp [substituteCouplePair, h, RegCpl.pairsAt, splicePairs, hp]
  | type1 c r g d =>
    simp only [substituteCouplePair, RegCpl.pairsAt, splicePairs_append,
      substituteCouplePair_pairsAt r, substituteCouplePair_pairsAt g, substituteCouplePair_pairsAt d]
  | type2 p m q =>
    simp only [substituteCouplePair, RegCpl.pairsAt, substituteChainPair_lonePath,
      splicePairs_append, substituteChainPair_pairsAt p, substituteChainPair_pairsAt m,
      substituteCouplePair_pairsAt q]
termination_by structural Q

/-- The literal list-splicing identity in a chain's side couples. -/
theorem substituteChainPair_pairsAt {w : ℕ} (X : RegChain) (ζ : ℤˣ) (a x y : Fin w × Path)
    (S : RegCpl) :
    (substituteChainPair X ζ a x y S).pairsAt ζ a =
      splicePairs (X.pairsAt ζ a) (x,y) (S.pairsAt x y) := by
  cases X with
  | nil => simp only [substituteChainPair, RegChain.pairsAt, splicePairs, List.flatMap_nil]
  | pair m r g i s =>
    by_cases hr : slotSign ζ m.red.1 = 1 <;>
      by_cases hg : slotSign ζ m.green.1 = 1 <;>
      simp only [substituteChainPair, RegChain.pairsAt, substituteChainPair_lonePath,
        hr, hg, ite_true, ite_false, splicePairs_append, substituteCouplePair_pairsAt r,
        substituteCouplePair_pairsAt g, substituteChainPair_pairsAt i, substituteChainPair_pairsAt s]
termination_by structural X
end

/-- Generic membership rule for splicing, proved independently of code expressions. -/
theorem mem_splicePairs {α : Type*} [DecidableEq α] (P : List α) (t : α) (S : List α) (z : α) :
    z ∈ splicePairs P t S ↔ (z ∈ P ∧ z ≠ t) ∨ (t ∈ P ∧ z ∈ S) := by
  simp only [splicePairs, List.mem_flatMap]
  constructor
  · rintro ⟨p,hp,hz⟩
    by_cases he : p = t
    · subst p
      simp only [ite_true] at hz
      exact Or.inr ⟨hp,hz⟩
    · simp only [he,ite_false,List.mem_singleton] at hz
      subst p
      exact Or.inl ⟨hp,he⟩
  · rintro (⟨hz,hne⟩ | ⟨ht,hz⟩)
    · exact ⟨z,hz,by simp only [hne,ite_false,List.mem_singleton]⟩
    · exact ⟨t,ht,by simpa only [ite_true] using hz⟩

/-- Exact pair-relation surgery for couple substitution. -/
theorem mem_substituteCouplePair {w : ℕ} (Q : RegCpl) (a b x y : Fin w × Path) (S : RegCpl)
    (z : (Fin w × Path) × (Fin w × Path)) :
    z ∈ (substituteCouplePair Q a b x y S).pairsAt a b ↔
      (z ∈ Q.pairsAt a b ∧ z ≠ (x,y)) ∨
      ((x,y) ∈ Q.pairsAt a b ∧ z ∈ S.pairsAt x y) := by
  rw [substituteCouplePair_pairsAt, mem_splicePairs]

/-- Exact pair-relation surgery for substitution in a chain's side couples. -/
theorem mem_substituteChainPair {w : ℕ} (X : RegChain) (ζ : ℤˣ) (a x y : Fin w × Path)
    (S : RegCpl) (z : (Fin w × Path) × (Fin w × Path)) :
    z ∈ (substituteChainPair X ζ a x y S).pairsAt ζ a ↔
      (z ∈ X.pairsAt ζ a ∧ z ≠ (x,y)) ∨
      ((x,y) ∈ X.pairsAt ζ a ∧ z ∈ S.pairsAt x y) := by
  rw [substituteChainPair_pairsAt, mem_splicePairs]

end WaveTurbulence.Reg
