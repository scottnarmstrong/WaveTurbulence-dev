/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.XChain.SysDraft.Duhamel

/-!
# D2 SYS-DEFS API, part 4: the tree recursion from its tree-level form (scratch, snapshot 4)

`TreeRecursion` (`𝒥_{K+1} = ∑_{N₁+N₂+N₃=K} ∫_p^t 𝒞₊(𝒥_{N₁}, 𝒥̄_{N₂}, 𝒥_{N₃})`) is proved here from two
statements about single trees:

* the root splitting `𝒥_{node l m r}(t) = ∫_p^t 𝒞₊(𝒥_l, 𝒥̄_m, 𝒥_r)(s) ds` (obligation O-TR1);
* interval integrability of `s ↦ 𝒞₊(𝒥_l, 𝒥̄_m, 𝒥_r)(s)_n` (obligation O-TR2).

The proof:
- the trees of order `K + 1` are the trees `node l m r` with `n(l) + n(m) + n(r) = K`
  (`sum_treesOfOrder_succ`);
- `aNonlin` is multilinear over the finite sums `𝒥_N = ∑_{n(𝒯) = N} 𝒥_𝒯`.

O-TR1 is `treeTerm_node` (`Duh-Node.lean`) and O-TR2 is `intervalIntegrable_treeTriple` (`Duh-Meas.lean`);
`treeRecursion` is in `Sys-Final.lean`.
-/

@[expose] public section

open MeasureTheory Finset Set

namespace WaveTurbulence.SysAPI

/-- The trees of order `K + 1` are the `node l m r` with `n(l) + n(m) + n(r) = K`. -/
theorem sum_treesOfOrder_succ {M : Type*} [AddCommMonoid M] (K : ℕ) (f : TTree → M) :
    ∑ T ∈ treesOfOrder (K + 1), f T =
      ∑ y ∈ (range (K + 1) ×ˢ range (K + 1) ×ˢ range (K + 1)).filter
          (fun y => y.1 + y.2.1 + y.2.2 = K),
        ∑ l ∈ treesOfOrder y.1, ∑ m ∈ treesOfOrder y.2.1, ∑ r ∈ treesOfOrder y.2.2,
          f (TTree.node l m r) := by
  classical
  set B := (Canon.finite_order_le K).toFinset
  set U := (B ×ˢ B ×ˢ B).filter
    (fun x : TTree × TTree × TTree => x.1.order + x.2.1.order + x.2.2.order = K)
  have hB : ∀ T, T ∈ B ↔ T.order ≤ K := fun T => by simp [B]
  have hmaps : ∀ x ∈ U, (fun x : TTree × TTree × TTree => (x.1.order, x.2.1.order, x.2.2.order)) x ∈
      (range (K + 1) ×ˢ range (K + 1) ×ˢ range (K + 1)).filter (fun y => y.1 + y.2.1 + y.2.2 = K) := by
    intro x hx
    simp only [U, Finset.mem_filter, Finset.mem_product, hB] at hx
    simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_range]
    omega
  have hR : ∑ y ∈ (range (K + 1) ×ˢ range (K + 1) ×ˢ range (K + 1)).filter
          (fun y => y.1 + y.2.1 + y.2.2 = K),
        ∑ l ∈ treesOfOrder y.1, ∑ m ∈ treesOfOrder y.2.1, ∑ r ∈ treesOfOrder y.2.2,
          f (TTree.node l m r) = ∑ x ∈ U, f (TTree.node x.1 x.2.1 x.2.2) := by
    rw [← Finset.sum_fiberwise_of_maps_to hmaps]
    refine Finset.sum_congr rfl fun y hy => ?_
    simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_range] at hy
    have hset : U.filter (fun x => (x.1.order, x.2.1.order, x.2.2.order) = y) =
        treesOfOrder y.1 ×ˢ treesOfOrder y.2.1 ×ˢ treesOfOrder y.2.2 := by
      ext x
      simp only [U, Finset.mem_filter, Finset.mem_product, hB, mem_treesOfOrder, Prod.ext_iff]
      omega
    rw [hset]
    simp only [Finset.sum_product]
  rw [hR]
  refine Finset.sum_nbij'
    (fun T => match T with
      | .leaf => (.leaf, .leaf, .leaf)
      | .node l m r => (l, m, r))
    (fun x => TTree.node x.1 x.2.1 x.2.2) ?_ ?_ ?_ ?_ ?_
  · intro T hT
    rw [mem_treesOfOrder] at hT
    cases T with
    | leaf => simp [TTree.order] at hT
    | node l m r =>
      simp only [TTree.order] at hT
      simp only [U, Finset.mem_filter, Finset.mem_product, hB]
      omega
  · intro x hx
    simp only [U, Finset.mem_filter, Finset.mem_product, hB] at hx
    rw [mem_treesOfOrder, TTree.order]
    omega
  · intro T hT
    rw [mem_treesOfOrder] at hT
    cases T with
    | leaf => simp [TTree.order] at hT
    | node l m r => rfl
  · intro x _
    rfl
  · intro T hT
    rw [mem_treesOfOrder] at hT
    cases T with
    | leaf => simp [TTree.order] at hT
    | node l m r => rfl

variable (L γ δ : ℝ) {d : ℕ}

/-- **The tree recursion from its tree-level form.** Given the root splitting (O-TR1) and the
integrability of the tree triples (O-TR2) at `(t, n)`, `TreeRecursion` holds at `(t, n)`. -/
theorem treeRecursion_of (p : ℕ) {aP : (Fin d → ℤ) → ℂ} (haP : Summable fun k => ‖aP k‖) (t : ℝ)
    (n : Fin d → ℤ)
    (hnode : ∀ l m r : TTree, treeTerm L γ δ p (TTree.node l m r) aP t n =
      ∫ s in (p : ℝ)..t, aNonlin L γ δ 1 s (treeTerm L γ δ p l aP s)
        (fun k => (starRingEnd ℂ) (treeTerm L γ δ p m aP s k)) (treeTerm L γ δ p r aP s) n)
    (hint : ∀ l m r : TTree, IntervalIntegrable (fun s => aNonlin L γ δ 1 s
      (treeTerm L γ δ p l aP s) (fun k => (starRingEnd ℂ) (treeTerm L γ δ p m aP s k))
      (treeTerm L γ δ p r aP s) n) volume p t) :
    TreeRecursion L γ δ p aP t n := by
  intro K
  rw [treeTermN_eq_sum, sum_treesOfOrder_succ]
  refine Finset.sum_congr rfl fun y _ => ?_
  have hexp : ∀ s, aNonlin L γ δ 1 s (treeTermN L γ δ p y.1 aP s)
      (fun k => (starRingEnd ℂ) (treeTermN L γ δ p y.2.1 aP s k)) (treeTermN L γ δ p y.2.2 aP s) n =
      ∑ l ∈ treesOfOrder y.1, ∑ m ∈ treesOfOrder y.2.1, ∑ r ∈ treesOfOrder y.2.2,
        aNonlin L γ δ 1 s (treeTerm L γ δ p l aP s)
          (fun k => (starRingEnd ℂ) (treeTerm L γ δ p m aP s k)) (treeTerm L γ δ p r aP s) n := by
    intro s
    have h1 : treeTermN L γ δ p y.1 aP s = fun k => ∑ l ∈ treesOfOrder y.1, treeTerm L γ δ p l aP s k :=
      funext fun k => treeTermN_eq_sum L γ δ p _ aP s k
    have h2 : (fun k => (starRingEnd ℂ) (treeTermN L γ δ p y.2.1 aP s k)) =
        fun k => ∑ m ∈ treesOfOrder y.2.1, (starRingEnd ℂ) (treeTerm L γ δ p m aP s k) :=
      funext fun k => by rw [treeTermN_eq_sum, map_sum]
    have h3 : treeTermN L γ δ p y.2.2 aP s =
        fun k => ∑ r ∈ treesOfOrder y.2.2, treeTerm L γ δ p r aP s k :=
      funext fun k => treeTermN_eq_sum L γ δ p _ aP s k
    rw [h1, h2, h3]
    exact aNonlin_sum L γ δ 1 s _ _ _ (fun l => treeTerm L γ δ p l aP s)
      (fun m k => (starRingEnd ℂ) (treeTerm L γ δ p m aP s k)) (fun r => treeTerm L γ δ p r aP s)
      (fun l => summable_norm_treeTerm L γ δ p l haP s)
      (fun m => by simpa using summable_norm_treeTerm L γ δ p m haP s)
      (fun r => summable_norm_treeTerm L γ δ p r haP s) n
  have hsum : ∀ {ι : Type} (S : Finset ι) (F : ι → ℝ → ℂ),
      (∀ i ∈ S, IntervalIntegrable (F i) volume p t) →
        IntervalIntegrable (fun s => ∑ i ∈ S, F i s) volume p t := by
    intro ι S F hF
    have h := IntervalIntegrable.sum S hF
    convert h using 1
    funext s
    simp [Finset.sum_apply]
  rw [intervalIntegral.integral_congr fun s _ => hexp s,
    intervalIntegral.integral_finsetSum fun l _ => hsum _ _ fun m _ => hsum _ _ fun r _ => hint l m r]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [intervalIntegral.integral_finsetSum fun m _ => hsum _ _ fun r _ => hint l m r]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [intervalIntegral.integral_finsetSum fun r _ => hint l m r]
  exact Finset.sum_congr rfl fun r _ => hnode l m r

end WaveTurbulence.SysAPI
