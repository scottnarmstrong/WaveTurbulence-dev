/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.XChain.TruncatedTreeExpansion
public import WaveTurbulence.Foundations.XChain.SysDraft.Final

/-!
# CPL-2, step 1: `ℒ₀` is a sum of tree terms

**Statement** (`Lop_zero_eq_sum_l0Trees`). For `∑_k |a_k(p)| < ∞` and `t ≥ p`,
`ℒ₀(t)_n = ∑_{𝒯 ∈ l0Trees N} (𝒥_𝒯)_n(t)`, where `N = N_{p+1}` and `l0Trees N` is the set of trees
`𝒯 = node(l, m, r)` with `n(l), n(m), n(r) ≤ N` and `n(l) + n(m) + n(r) ≥ N`. Equivalently, `n(𝒯) > N` and
each child of the root has order `≤ N` (T L2312, the kind `ℒ₀`).

**Proof.**
- In `ℒ₀ = ∑_{(N₁,N₂,N₃), N ≤ ∑ N_i} ∫_p^t 𝒞₊(𝒥_{N₁}, 𝒥̄_{N₂}, 𝒥_{N₃})`, expand `𝒥_{N_i} = ∑_{n(𝒯) = N_i} 𝒥_𝒯`
  (`aNonlin_sum`).
- Use the Duhamel form `𝒥_{node(l,m,r)} = ∫_p^t 𝒞₊(𝒥_l, 𝒥̄_m, 𝒥_r)` (`treeTerm_node`).
-/

@[expose] public section

namespace WaveTurbulence.Cpl

open Finset Induct SysAPI

/-! ## The family -/

/-- The child triples `(l, m, r)` of the trees of `ℒ₀`, grouped by their orders. -/
noncomputable def l0Triples (N : ℕ) : Finset (TTree × TTree × TTree) :=
  ((univ : Finset (Fin (N + 1) × Fin (N + 1) × Fin (N + 1))).filter
    (fun y => N ≤ (y.1 : ℕ) + y.2.1 + y.2.2)).biUnion
      fun y => treesOfOrder y.1 ×ˢ treesOfOrder y.2.1 ×ˢ treesOfOrder y.2.2

/-- The trees of `ℒ₀`. -/
noncomputable def l0Trees (N : ℕ) : Finset TTree :=
  (l0Triples N).image fun x => TTree.node x.1 x.2.1 x.2.2

theorem mem_l0Triples {N : ℕ} {x : TTree × TTree × TTree} :
    x ∈ l0Triples N ↔ x.1.order ≤ N ∧ x.2.1.order ≤ N ∧ x.2.2.order ≤ N ∧
      N ≤ x.1.order + x.2.1.order + x.2.2.order := by
  simp only [l0Triples, mem_biUnion, mem_filter, mem_univ, true_and, mem_product, mem_treesOfOrder]
  constructor
  · rintro ⟨y, hy, h1, h2, h3⟩
    rw [h1, h2, h3]
    exact ⟨by omega, by omega, by omega, hy⟩
  · rintro ⟨h1, h2, h3, h⟩
    exact ⟨(⟨x.1.order, by omega⟩, ⟨x.2.1.order, by omega⟩, ⟨x.2.2.order, by omega⟩), h, rfl, rfl, rfl⟩

theorem mem_l0Trees {N : ℕ} {T : TTree} :
    T ∈ l0Trees N ↔ ∃ l m r : TTree, T = TTree.node l m r ∧ l.order ≤ N ∧ m.order ≤ N ∧
      r.order ≤ N ∧ N ≤ l.order + m.order + r.order := by
  simp only [l0Trees, mem_image, mem_l0Triples]
  constructor
  · rintro ⟨⟨l, m, r⟩, h, rfl⟩
    exact ⟨l, m, r, rfl, h⟩
  · rintro ⟨l, m, r, rfl, h⟩
    exact ⟨⟨l, m, r⟩, h, rfl⟩

theorem order_le_of_mem_l0Trees {N : ℕ} {T : TTree} (h : T ∈ l0Trees N) : T.order ≤ 3 * N + 1 := by
  obtain ⟨l, m, r, rfl, h1, h2, h3, -⟩ := mem_l0Trees.mp h
  simp only [TTree.order]
  omega

theorem lt_order_of_mem_l0Trees {N : ℕ} {T : TTree} (h : T ∈ l0Trees N) : N < T.order := by
  obtain ⟨l, m, r, rfl, -, -, -, h⟩ := mem_l0Trees.mp h
  simp only [TTree.order]
  omega

theorem l0Trees_subset (N : ℕ) : l0Trees N ⊆ truncatedTrees (3 * N + 1) :=
  fun _ h => mem_truncatedTrees.mpr (order_le_of_mem_l0Trees h)

/-- `∑_{𝒯 ∈ l0Trees} f 𝒯`, grouped by the orders of the children. -/
theorem sum_l0Trees {M : Type*} [AddCommMonoid M] (N : ℕ) (f : TTree → M) :
    ∑ T ∈ l0Trees N, f T =
      ∑ y ∈ (univ : Finset (Fin (N + 1) × Fin (N + 1) × Fin (N + 1))).filter
          (fun y => N ≤ (y.1 : ℕ) + y.2.1 + y.2.2),
        ∑ l ∈ treesOfOrder y.1, ∑ m ∈ treesOfOrder y.2.1, ∑ r ∈ treesOfOrder y.2.2,
          f (TTree.node l m r) := by
  classical
  unfold l0Trees
  rw [sum_image (fun x _ y _ h => by
    simp only [TTree.node.injEq] at h
    exact Prod.ext h.1 (Prod.ext h.2.1 h.2.2))]
  unfold l0Triples
  rw [sum_biUnion]
  · refine sum_congr rfl fun y _ => ?_
    rw [sum_product, sum_congr rfl fun l _ => sum_product _ _ _]
  · intro y _ y' _ hne
    simp only [Function.onFun]
    rw [disjoint_left]
    rintro ⟨l, m, r⟩ h h'
    simp only [mem_product, mem_treesOfOrder] at h h'
    apply hne
    exact Prod.ext (Fin.ext (h.1.symm.trans h'.1)) (Prod.ext (Fin.ext (h.2.1.symm.trans h'.2.1))
      (Fin.ext (h.2.2.symm.trans h'.2.2)))

/-! ## The slot triples of `ℒ₀` -/

theorem slotTriple_filter_eq (N : ℕ) :
    (univ : Finset (Slot N × Slot N × Slot N)).filter
        (fun x => slotCountB x = 0 ∧ (0 = 0 → N ≤ slotOrder x)) =
      ((univ : Finset (Fin (N + 1) × Fin (N + 1) × Fin (N + 1))).filter
          (fun y => N ≤ (y.1 : ℕ) + y.2.1 + y.2.2)).image
        fun y => (some y.1, some y.2.1, some y.2.2) := by
  ext ⟨o₁, o₂, o₃⟩
  simp only [mem_filter, mem_univ, true_and, mem_image, forall_const]
  rcases o₁ with _ | a <;> rcases o₂ with _ | b <;> rcases o₃ with _ | c <;>
    simp [slotCountB, slotOrder, Prod.ext_iff, add_assoc]

variable (L γ δ : ℝ) {d : ℕ}

theorem integral_aNonlin_treeTermN (p N₁ N₂ N₃ : ℕ) {aP : (Fin d → ℤ) → ℂ}
    (haP : Summable fun k => ‖aP k‖) {t : ℝ} (ht : (p : ℝ) ≤ t) (n : Fin d → ℤ) :
    ∫ s in (p : ℝ)..t, aNonlin L γ δ 1 s (treeTermN L γ δ p N₁ aP s)
        (fun k => (starRingEnd ℂ) (treeTermN L γ δ p N₂ aP s k)) (treeTermN L γ δ p N₃ aP s) n =
      ∑ l ∈ treesOfOrder N₁, ∑ m ∈ treesOfOrder N₂, ∑ r ∈ treesOfOrder N₃,
        treeTerm L γ δ p (TTree.node l m r) aP t n := by
  have hexp : (fun s => aNonlin L γ δ 1 s (treeTermN L γ δ p N₁ aP s)
      (fun k => (starRingEnd ℂ) (treeTermN L γ δ p N₂ aP s k)) (treeTermN L γ δ p N₃ aP s) n) =
      fun s => ∑ l ∈ treesOfOrder N₁, ∑ m ∈ treesOfOrder N₂, ∑ r ∈ treesOfOrder N₃,
        aNonlin L γ δ 1 s (treeTerm L γ δ p l aP s)
          (fun k => (starRingEnd ℂ) (treeTerm L γ δ p m aP s k)) (treeTerm L γ δ p r aP s) n := by
    funext s
    have h1 : treeTermN L γ δ p N₁ aP s = fun k => ∑ l ∈ treesOfOrder N₁, treeTerm L γ δ p l aP s k :=
      funext fun k => treeTermN_eq_sum L γ δ p _ aP s k
    have h2 : (fun k => (starRingEnd ℂ) (treeTermN L γ δ p N₂ aP s k)) =
        fun k => ∑ m ∈ treesOfOrder N₂, (starRingEnd ℂ) (treeTerm L γ δ p m aP s k) :=
      funext fun k => by rw [treeTermN_eq_sum, map_sum]
    have h3 : treeTermN L γ δ p N₃ aP s = fun k => ∑ r ∈ treesOfOrder N₃, treeTerm L γ δ p r aP s k :=
      funext fun k => treeTermN_eq_sum L γ δ p _ aP s k
    rw [h1, h2, h3]
    exact aNonlin_sum L γ δ 1 s _ _ _ (fun l => treeTerm L γ δ p l aP s)
      (fun m k => (starRingEnd ℂ) (treeTerm L γ δ p m aP s k)) (fun r => treeTerm L γ δ p r aP s)
      (fun l => summable_norm_treeTerm L γ δ p l haP s)
      (fun m => by simpa using summable_norm_treeTerm L γ δ p m haP s)
      (fun r => summable_norm_treeTerm L γ δ p r haP s) n
  have hsum : ∀ {ι : Type} (S : Finset ι) (F : ι → ℝ → ℂ),
      (∀ i ∈ S, IntervalIntegrable (F i) MeasureTheory.volume p t) →
        IntervalIntegrable (fun s => ∑ i ∈ S, F i s) MeasureTheory.volume p t := by
    intro ι S F hF
    have h := IntervalIntegrable.sum S hF
    convert h using 1
    funext s
    simp [Finset.sum_apply]
  rw [hexp]
  rw [intervalIntegral.integral_finsetSum fun l _ =>
    hsum _ _ fun m _ => hsum _ _ fun r _ => intervalIntegrable_treeTriple L γ δ p l m r haP t n]
  refine sum_congr rfl fun l _ => ?_
  rw [intervalIntegral.integral_finsetSum fun m _ =>
    hsum _ _ fun r _ => intervalIntegrable_treeTriple L γ δ p l m r haP t n]
  refine sum_congr rfl fun m _ => ?_
  rw [intervalIntegral.integral_finsetSum fun r _ =>
    intervalIntegrable_treeTriple L γ δ p l m r haP t n]
  exact sum_congr rfl fun r _ => (treeTerm_node l m r L γ δ p haP ht n).symm

/-- **`ℒ₀` as a sum of tree terms.** -/
theorem Lop_zero_eq_sum_l0Trees (p N : ℕ) {aP : (Fin d → ℤ) → ℂ} (haP : Summable fun k => ‖aP k‖)
    {t : ℝ} (ht : (p : ℝ) ≤ t) (n : Fin d → ℤ) :
    Lop L γ δ p N aP 0 (fun _ _ => 0) t n = ∑ T ∈ l0Trees N, treeTerm L γ δ p T aP t n := by
  classical
  unfold Lop
  rw [slotTriple_filter_eq, sum_image (fun y _ y' _ h => by
    simp only [Prod.mk.injEq, Option.some.injEq] at h
    exact Prod.ext h.1 (Prod.ext h.2.1 h.2.2)), sum_l0Trees]
  exact sum_congr rfl fun y _ => integral_aNonlin_treeTermN L γ δ p y.1 y.2.1 y.2.2 haP ht n

end WaveTurbulence.Cpl
