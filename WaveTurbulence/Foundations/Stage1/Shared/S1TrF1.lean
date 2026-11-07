/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Stage1.Shared.S1Cnt1
public import WaveTurbulence.Foundations.Stage1.Shared.S1CongTrans
import Mathlib.Tactic

/-!
# Transport across an operation at another member: disjointness of the slots
-/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.Stage1
open TTree Reg Reg.Skeleton Twist Links RegRed WaveTurbulence.LFTwist

variable {w : ℕ}

theorem pairOfLeaf_eq_cases (G : Garden w) (hG : G.IsPlain) {l l' : GLeaf G.tree}
    (h : pairOfLeaf G hG l = pairOfLeaf G hG l') : l = l' ∨ l = G.pair l' := by
  rcases pairOfLeaf_first_or_partner G hG l with h1 | h1 <;>
    rcases pairOfLeaf_first_or_partner G hG l' with h2 | h2 <;>
    have e : (pairOfLeaf G hG l).firstLeaf hG = (pairOfLeaf G hG l').firstLeaf hG := by rw [h]
  · exact Or.inl (h1.symm.trans (e.trans h2))
  · exact Or.inr (h1.symm.trans (e.trans h2))
  · right
    have := (h1.symm.trans (e.trans h2))
    have h3 := congrArg G.pair this
    rw [G.pair_pair] at h3
    exact h3
  · left
    have := (h1.symm.trans (e.trans h2))
    have h3 := congrArg G.pair this
    rw [G.pair_pair, G.pair_pair] at h3
    exact h3

variable {ι : Type*} {G : Garden w}

theorem CoreFamily.lower_ne_of_ne (F : CoreFamily G ι) {i j : ι} (hij : i ≠ j) :
    (F.placement i).lower ≠ (F.placement j).lower := fun he => hij (F.lower_injective he)

theorem CoreFamily.exceptional_ne (F : CoreFamily G ι) (hG : G.IsPlain) {i j : ι} (hij : i ≠ j) :
    pairOfLeaf G hG (F.placement i).retained ≠ pairOfLeaf G hG (F.placement j).retained := by
  intro he
  have D := F.pairData j i hij.symm
  rcases pairOfLeaf_eq_cases G hG he with h | h
  · exact retained_ne_of_lower_ne G _ _ (CoreFamily.lower_ne_of_ne F hij) h
  · exact separated_retained_ne_pair G _ _ D.blockLeft D.clLeft D.atLeft D.blockRight D.clRight D.atRight
      D.separated h

end WaveTurbulence.Stage1
