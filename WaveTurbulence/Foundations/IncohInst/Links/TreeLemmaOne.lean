/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.IncohInst.Links.TreeLemma

/-!
# TARGET Lemma `treelemma` (1): short differences along heavy children (packet C2)

For every branching node `𝔫` of a ternary tree let `h(𝔫)` be a child with the most leaves. If `h(𝔫)`
is branching, `k_{h(𝔫)} - ζ k_𝔫` (`ζ = ±1` the slot sign of `h(𝔫)`) is the algebraic sum of the
leaves of the two other children; if all children of `𝔫` are leaves, `k_𝔫` itself is the algebraic
sum of its three leaves. The number `Λ_𝔫` of these leaves is at most `3 μ°_𝔫`, so by DH21 Lemma 6.6
`∏_𝔫 Λ_𝔫 ≤ 3^n ∏_𝔫 μ°_𝔫 ≤ 9^n` (`treelemma_one`). Ordering the branching nodes by decreasing depth
puts each `h(𝔫)` before `𝔫`.
-/

@[expose] public section

namespace WaveTurbulence.Links

open TTree

/-! ### The leaf expansion -/

theorem sum_leaves_node {V : Type*} [AddCommGroup V] (l m r : TTree) (f : Path → V) :
    ∑ p ∈ (TTree.node l m r).leaves, f p =
      ∑ q ∈ l.leaves, f (0 :: q) + ∑ q ∈ m.leaves, f (1 :: q) + ∑ q ∈ r.leaves, f (2 :: q) := by
  have inj : ∀ i : Fin 3, Set.InjOn (List.cons i) (Set.univ : Set Path) := fun i a _ b _ h =>
    List.cons_injective h
  have disj : ∀ {i j : Fin 3} (S T : Finset Path), i ≠ j → Disjoint (pre i S) (pre j T) :=
    fun S T hij => Finset.disjoint_left.mpr fun p hp hq => by
      simp only [pre, Finset.mem_image] at hp hq
      obtain ⟨a, -, rfl⟩ := hp
      obtain ⟨b, -, hb⟩ := hq
      exact hij (List.cons.inj hb).1.symm
  rw [TTree.leaves, Finset.sum_union, Finset.sum_union]
  · simp only [pre, Finset.sum_image fun a _ b _ h => List.cons_injective h]
  · exact disj _ _ (by decide)
  · rw [Finset.disjoint_union_left]; exact ⟨disj _ _ (by decide), disj _ _ (by decide)⟩

/-- **The leaf expansion** `k_𝔯 = ∑_ℓ ζ_ℓ k_ℓ` of a tree decoration (signs `(-1)^{#mid steps}`). -/
theorem treeDec_root {V : Type*} [AddCommGroup V] :
    ∀ (t : TTree) (k : Path → V), TreeDec t k → k [] = ∑ p ∈ t.leaves, ((pathSign 1 p : ℤ)) • k p
  | .leaf, k, _ => by simp [TTree.leaves, pathSign]
  | .node l m r, k, h => by
    obtain ⟨h0, d₀, d₁, d₂⟩ := treeDec_child h
    rw [sum_leaves_node, h0, treeDec_root l _ d₀, treeDec_root m _ d₁, treeDec_root r _ d₂]
    have s0 : ∀ q, pathSign 1 ((0 : Fin 3) :: q) = pathSign 1 q := fun q => by simp [pathSign]
    have s1 : ∀ q, pathSign 1 ((1 : Fin 3) :: q) = -pathSign 1 q := fun q => by
      simp [pathSign, pow_succ]
    have s2 : ∀ q, pathSign 1 ((2 : Fin 3) :: q) = pathSign 1 q := fun q => by simp [pathSign]
    simp only [s0, s1, s2, Units.val_neg, neg_smul, Finset.sum_neg_distrib]
    abel

/-! ### The relation at each branching node -/

/-! ### The product bound -/

end WaveTurbulence.Links
