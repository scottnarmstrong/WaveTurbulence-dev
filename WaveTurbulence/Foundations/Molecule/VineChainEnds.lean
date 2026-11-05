/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Molecule.VineChainCounts
import Mathlib.Tactic

/-! # Small chains have double-bond end ingredients (TARGET subsetvc) -/

public section
namespace WaveTurbulence.Vine
open Finset
variable {V D : Type*} [DecidableEq V] [Fintype D]

/-- The first ingredient retains the chain's first joint. -/
theorem chain_first_ingredient {M : Molecule V D} {S : Finset V} {a b : V} {n : ℕ}
    (h : Chain M S a b n) :
    ∃ X A x, M.IsVine X A a x ∧ A ⊆ S := by
  induction h with
  | single h => obtain ⟨X,hX⟩ := h; exact ⟨X,_,_,hX,subset_refl _⟩
  | append _ _ _ _ ih =>
    obtain ⟨X,A,x,hX,hA⟩ := ih
    exact ⟨X,A,x,hX,hA.trans subset_union_left⟩

/-- Unless it is a single ingredient, a chain on fewer than seven atoms
has a type-I ingredient at one of its two ends. -/
theorem chain_small_end_typeI {M : Molecule V D} {S : Finset V} {a b : V} {n : ℕ}
    (h : Chain M S a b n) (hc : S.card<7) : n=1 ∨
      (∃ A x, M.IsVine .I A a x ∧ A ⊆ S) ∨
      (∃ A x, M.IsVine .I A x b ∧ A ⊆ S) := by
  cases h with
  | single => exact Or.inl rfl
  | @append S T a b c n hS hT hi _hne =>
    obtain ⟨X,A,x,hX,hA⟩ := chain_first_ingredient hS
    obtain ⟨Y,hY⟩ := hT
    by_cases hXI : X=.I
    · subst X
      exact Or.inr (Or.inl ⟨A,x,hX,hA.trans subset_union_left⟩)
    · by_cases hYI : Y=.I
      · subst Y
        exact Or.inr (Or.inr ⟨T,b,hY,subset_union_right⟩)
      · have hAc : 4 ≤ A.card := by
          by_contra hh
          exact hXI (isVine_typeI_of_card_lt_four hX (by omega))
        have hTc : 4 ≤ T.card := by
          by_contra hh
          exact hYI (isVine_typeI_of_card_lt_four hY (by omega))
        have hinter : A ∩ T ⊆ ({b} : Finset V) := by
          intro v hv
          rw [← hi]
          exact mem_inter.mpr ⟨hA (mem_inter.mp hv).1,(mem_inter.mp hv).2⟩
        have hci := card_le_card hinter
        rw [card_singleton] at hci
        have hU : A ∪ T ⊆ S ∪ T := by
          intro v hv
          rcases mem_union.mp hv with hv | hv
          · exact mem_union_left T (hA hv)
          · exact mem_union_right S hv
        have hcu := card_le_card hU
        have hsum := card_union_add_card_inter A T
        omega

/-- No single vine has seven atoms: type II has even cardinality, and
normal vines have at least nine atoms. -/
theorem not_isVine_card_seven {M : Molecule V D} {X : VineType} {S : Finset V} {a b : V}
    (hc : S.card=7) : ¬M.IsVine X S a b := by
  intro h
  obtain ⟨k,hk,hs,_hb⟩ := isVine_counts h
  cases X <;> norm_num [VineType.template] at hs hk <;> omega

end WaveTurbulence.Vine
