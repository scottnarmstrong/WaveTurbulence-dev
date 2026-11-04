/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.WaveB.Lemmas

/-! # Tree counts, signs and induction (TARGET Definition 3.1, L625–L631)

The snapshot definitions are unchanged. Counting proofs are adapted from the
snapshot's audited non-vacuity probes into the packet namespace.
-/

public section

namespace WaveTurbulence.Comb
open TTree Finset

theorem card_pre (i : Fin 3) (S : Finset Path) : (pre i S).card = S.card :=
  Finset.card_image_of_injective _ (List.cons_injective)

theorem pre_disjoint {i j : Fin 3} (hij : i ≠ j) (S T : Finset Path) :
    Disjoint (pre i S) (pre j T) := by
  rw [Finset.disjoint_left]
  intro p hp hq
  obtain ⟨q, -, rfl⟩ := mem_pre.1 hp
  exact hij (cons_mem_pre.1 hq).1.symm

/-- `|𝒩| = n(𝒯)`. -/
theorem card_branching : ∀ t : TTree, t.branching.card = t.order
  | .leaf => rfl
  | .node l m r => by
    rw [branching, Finset.card_insert_of_notMem (by simp [nil_notMem_pre]),
      Finset.card_union_of_disjoint, Finset.card_union_of_disjoint, card_pre, card_pre, card_pre,
      card_branching l, card_branching m, card_branching r, order]
    · exact pre_disjoint (by decide) _ _
    · exact Finset.disjoint_union_left.2 ⟨pre_disjoint (by decide) _ _, pre_disjoint (by decide) _ _⟩

/-- `|ℒ| = 2 n(𝒯) + 1` (T L630). -/
theorem card_leaves : ∀ t : TTree, t.leaves.card = 2 * t.order + 1
  | .leaf => rfl
  | .node l m r => by
    rw [leaves, Finset.card_union_of_disjoint, Finset.card_union_of_disjoint, card_pre, card_pre,
      card_pre, card_leaves l, card_leaves m, card_leaves r, order]
    · ring
    · exact pre_disjoint (by decide) _ _
    · exact Finset.disjoint_union_left.2 ⟨pre_disjoint (by decide) _ _, pre_disjoint (by decide) _ _⟩

/-! ### Finiteness of layered gardens of bounded order and depth -/

theorem finite_order_le : ∀ n : ℕ, {T : TTree | T.order ≤ n}.Finite
  | 0 => by
    refine (Set.finite_singleton TTree.leaf).subset ?_
    intro T hT
    cases T with
    | leaf => rfl
    | node l m r => simp [order] at hT
  | n + 1 => by
    have ih := finite_order_le n
    refine ((Set.finite_singleton TTree.leaf).union
      (((ih.prod (ih.prod ih)).image fun x => TTree.node x.1 x.2.1 x.2.2))).subset ?_
    intro T hT
    cases T with
    | leaf => exact Or.inl rfl
    | node l m r =>
      simp only [Set.mem_ofPred_eq, order] at hT
      refine Or.inr ⟨(l, m, r), ⟨?_, ?_, ?_⟩, rfl⟩ <;> simp only [Set.mem_ofPred_eq] <;> omega


/-- The root carries the sign of the tree (TARGET L629). -/
theorem pathSign_nil (ζ : ℤˣ) : pathSign ζ [] = ζ := by simp [pathSign]

/-- Signs compose along paths (TARGET L629). -/
theorem pathSign_append (ζ : ℤˣ) (p q : Path) :
    pathSign ζ (p ++ q) = pathSign (pathSign ζ p) q := by
  simp only [pathSign, List.count_append, pow_add, mul_assoc]

/-- A left child has its parent's sign (TARGET L629). -/
theorem pathSign_left (ζ : ℤˣ) (p : Path) : pathSign ζ (p ++ [0]) = pathSign ζ p := by
  rw [pathSign_append]
  simp [pathSign]

/-- A middle child has the opposite sign (TARGET L629). -/
theorem pathSign_mid (ζ : ℤˣ) (p : Path) : pathSign ζ (p ++ [1]) = -pathSign ζ p := by
  rw [pathSign_append]
  simp [pathSign]

/-- A right child has its parent's sign (TARGET L629). -/
theorem pathSign_right (ζ : ℤˣ) (p : Path) : pathSign ζ (p ++ [2]) = pathSign ζ p := by
  rw [pathSign_append]
  simp [pathSign]

/-- Conjugating a signed tree reverses every node sign (TARGET L631). -/
theorem pathSign_neg (ζ : ℤˣ) (p : Path) : pathSign (-ζ) p = -pathSign ζ p := by
  simp [pathSign]

/-- The tree phase ζ(𝒯), with its sign supplied separately (TARGET L630). -/
@[expose] noncomputable def treeZeta (t : TTree) (ζ : ℤˣ) : ℂ :=
  ∏ p ∈ t.branching, Complex.I * (((pathSign ζ p : ℤˣ) : ℤ) : ℂ)

/-- Strong induction in the branching order, convenient for later combinatorics. -/
theorem tree_order_induction {P : TTree → Prop}
    (h : ∀ t, (∀ s, s.order < t.order → P s) → P t) (t : TTree) : P t := by
  have hh : ∀ n, ∀ t : TTree, t.order = n → P t := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro t ht
      apply h t
      intro s hs
      exact ih s.order (by omega) s rfl
  exact hh t.order t rfl

/-- Bounded-order trees form a finite type (TARGET L628). -/
instance finite_boundedOrder (n : ℕ) : Finite {t : TTree // t.order ≤ n} :=
  (finite_order_le n).to_subtype

/-- A Fintype interface for sums over bounded-order trees. -/
noncomputable instance fintype_boundedOrder (n : ℕ) : Fintype {t : TTree // t.order ≤ n} :=
  Fintype.ofFinite _

/-- Conjugating a signed tree conjugates its phase (TARGET L630–L631). -/
theorem treeZeta_neg (t : TTree) (ζ : ℤˣ) :
    treeZeta t (-ζ) = (starRingEnd ℂ) (treeZeta t ζ) := by
  unfold treeZeta
  rw [map_prod]
  apply Finset.prod_congr rfl
  intro p hp
  rw [pathSign_neg]
  simp

end WaveTurbulence.Comb
