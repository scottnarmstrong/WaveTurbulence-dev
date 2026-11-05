/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Molecule.VineChainConnected
public import WaveTurbulence.Foundations.Molecule.VineRealizationCounts
import Mathlib.Tactic

/-! # Ingredient and atom counts of vine chains (TARGET defvine, subsetvc) -/

public section
namespace WaveTurbulence.Vine
open Finset
variable {V D : Type*} [DecidableEq V] [Fintype D]

/-- Every vine has at least two atoms. -/
theorem isVine_card_ge_two {M : Molecule V D} {X : VineType} {S : Finset V} {a b : V}
    (h : M.IsVine X S a b) : 2 ≤ S.card := by
  have hp : ({a,b} : Finset V) ⊆ S := by
    intro v hv
    rcases mem_insert.mp hv with rfl | hv
    · exact h.1.2.1
    · have he := mem_singleton.mp hv
      subst v
      exact h.1.2.2.1
  have hh := card_le_card hp
  rw [card_pair h.1.2.2.2.1] at hh
  exact hh

/-- A chain of n nonempty vine ingredients has at least n+1 atoms. -/
theorem chain_card_ge {M : Molecule V D} {S : Finset V} {a b : V} {n : ℕ}
    (h : Chain M S a b n) : n+1 ≤ S.card := by
  induction h with
  | single h => obtain ⟨X,hX⟩ := h; exact isVine_card_ge_two hX
  | @append S T a b c n hS hT hi _hne ih =>
    obtain ⟨X,hX⟩ := hT
    have htwo := isVine_card_ge_two hX
    have hc := card_union_add_card_inter S T
    rw [hi,card_singleton] at hc
    omega

/-- The only vine with fewer than four atoms is type I. -/
theorem isVine_typeI_of_card_lt_four {M : Molecule V D} {X : VineType}
    {S : Finset V} {a b : V} (h : M.IsVine X S a b) (hc : S.card<4) : X=.I := by
  obtain ⟨k,_hk,hcount,_hb⟩ := isVine_counts h
  cases X <;> norm_num [VineType.template] at hcount ⊢ <;> omega

/-- An actual type-I vine consists of exactly its two joints. -/
theorem typeI_atoms {M : Molecule V D} {S : Finset V} {a b : V}
    (h : M.IsVine .I S a b) : S={a,b} := by
  obtain ⟨k,hk,hc,_hb⟩ := isVine_counts h
  have hk0 : k=[] := List.length_eq_zero_iff.mp hk
  subst k
  have hc2 : S.card=2 := hc
  symm
  apply eq_of_subset_of_card_le ?_ ?_
  · intro v hv
    rcases mem_insert.mp hv with rfl | hv
    · exact h.1.2.1
    · have he := mem_singleton.mp hv
      subst v
      exact h.1.2.2.1
  · rw [hc2,card_pair h.1.2.2.2.1]

/-- A chain whose every ingredient is a double bond. -/
inductive DoubleChain (M : Molecule V D) : Finset V → V → V → ℕ → Prop
  | single {S a b} : M.IsVine .I S a b → DoubleChain M S a b 1
  | append {S T a b c n} : DoubleChain M S a b n → M.IsVine .I T b c →
      S ∩ T={b} → a ≠ c → DoubleChain M (S ∪ T) a c (n+1)

/-- A double chain has exactly one more atom than ingredients. -/
theorem doubleChain_card {M : Molecule V D} {S : Finset V} {a b : V} {n : ℕ}
    (h : DoubleChain M S a b n) : S.card=n+1 := by
  induction h with
  | single h => rw [typeI_atoms h,card_pair h.1.2.2.2.1]
  | @append S T a b c n _hS hT hi _hne ih =>
    have hc := card_union_add_card_inter S T
    have hTcard : T.card=2 := by rw [typeI_atoms hT,card_pair hT.1.2.2.2.1]
    rw [hi,card_singleton,hTcard] at hc
    omega

/-- Every small chain consists only of double-bond ingredients. -/
theorem chain_doubleChain_of_card_lt_four {M : Molecule V D} {S : Finset V}
    {a b : V} {n : ℕ} (h : Chain M S a b n) (hc : S.card<4) : DoubleChain M S a b n := by
  induction h with
  | single h =>
    obtain ⟨X,hX⟩ := h
    have he := isVine_typeI_of_card_lt_four hX hc
    subst X
    exact DoubleChain.single hX
  | @append S T a b c n hS hT hi hne ih =>
    have hcS : S.card<4 := (card_le_card (subset_union_left : S ⊆ S ∪ T)).trans_lt hc
    have hcT : T.card<4 := (card_le_card (subset_union_right : T ⊆ S ∪ T)).trans_lt hc
    obtain ⟨X,hX⟩ := hT
    have he := isVine_typeI_of_card_lt_four hX hcT
    subst X
    exact DoubleChain.append (ih hcS) hX hi hne

end WaveTurbulence.Vine
