/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.XChain.SysDraft.Final

/-!
# Flower trees and the classes of `𝒳`, `𝒴`, `𝒲` (packet X1)

DH21 Def 11.1 (Inventiones L2651–L2653): "a flower tree of height `n` is formed by attaching two sub-trees
each time, and repeating `n` times, starting from a single node". We take this as the definition:

* `FTree.flower` is the single flower `𝔣`;
* `FTree.node i F T₁ T₂` has a new root whose `i`-th child is the flower tree `F` (the stem continues there);
  its other two children are the ordinary trees `T₁, T₂`, in order.

Root and flower-end decompositions:
- `rootOf (i, F, T₁, T₂) = node i F T₁ T₂` (root attachment, `ℒ₁` applied after `𝒳`);
- `bottomOf (F, i, T₁, T₂) = F.graft (node i flower T₁ T₂)` (flower attachment, `ℒ₁` applied before `𝒳`).

Each nontrivial flower tree has exactly one decomposition of each kind.

The classes (T L2270–L2273; DH23 L2000; FINDINGS F39):
- `Xset N`: the flower trees of order `1, …, N`. The trivial tree is the identity term of `𝒳 = 1 + ∑ 𝒥̃`.
- `Yind N`: the `(i, F, T₁, T₂)` with `F, T₁, T₂` of order `≤ N` and `n(node i F T₁ T₂) > N`, i.e. (Y-1), (Y-2).
- `Wind N`: the `(F, i, T₁, T₂)` with `F, T₁, T₂` of order `≤ N` and `n(F.graft (node i 𝔣 T₁ T₂)) > N`,
  i.e. (W-1), (W-2) (the siblings `T₁, T₂` of `𝔣`), and (W-3) (replacing `𝔣^pr` by a flower gives `F`).
-/

@[expose] public section

open Finset

namespace WaveTurbulence.SysAPI

/-- **Flower trees** (DH21 Def 11.1). See the module docstring. -/
inductive FTree : Type
  | flower : FTree
  | node (i : Fin 3) (F : FTree) (T₁ T₂ : TTree) : FTree
  deriving DecidableEq

namespace FTree

/-- The order: the number of branching nodes. -/
def order : FTree → ℕ
  | flower => 0
  | node _ F T₁ T₂ => F.order + T₁.order + T₂.order + 1

/-- The sign of the flower, the root having sign `+`. Each middle step reverses it. -/
def sign : FTree → ℤˣ
  | flower => 1
  | node i F _ _ => (if i = 1 then -1 else 1) * F.sign

/-- Grafting `H` in place of the flower of `F`. -/
def graft : FTree → FTree → FTree
  | flower, H => H
  | node i F T₁ T₂, H => node i (F.graft H) T₁ T₂

theorem order_graft (F H : FTree) : (F.graft H).order = F.order + H.order := by
  induction F with
  | flower => simp [graft, order]
  | node i F T₁ T₂ ih => simp only [graft, order, ih]; omega

theorem graft_ne_flower {F H : FTree} (hH : H ≠ flower) : F.graft H ≠ flower := by
  cases F with
  | flower => exact hH
  | node => simp [graft]

/-- The decomposition at the flower end: `(F, i, T₁, T₂)` with `G = F.graft (node i flower T₁ T₂)` for
`G ≠ flower`. -/
def bottom : FTree → FTree × Fin 3 × TTree × TTree
  | flower => (flower, 0, .leaf, .leaf)
  | node i F T₁ T₂ => if F = flower then (flower, i, T₁, T₂) else (node i (bottom F).1 T₁ T₂, (bottom F).2)

end FTree

open FTree

/-- Root attachment. -/
def rootOf (x : Fin 3 × FTree × TTree × TTree) : FTree := node x.1 x.2.1 x.2.2.1 x.2.2.2

/-- Flower-end attachment. -/
def bottomOf (x : FTree × Fin 3 × TTree × TTree) : FTree :=
  x.1.graft (node x.2.1 flower x.2.2.1 x.2.2.2)

theorem bottom_bottomOf (x : FTree × Fin 3 × TTree × TTree) : (bottomOf x).bottom = x := by
  obtain ⟨F, i, T₁, T₂⟩ := x
  induction F with
  | flower => simp [bottomOf, graft, bottom]
  | node j F T₃ T₄ ih =>
    have hne : F.graft (node i flower T₁ T₂) ≠ flower := graft_ne_flower (by simp)
    simp only [bottomOf, graft, bottom, hne, ↓reduceIte] at ih ⊢
    rw [ih]

theorem bottomOf_bottom {G : FTree} (hG : G ≠ flower) : bottomOf G.bottom = G := by
  induction G with
  | flower => exact absurd rfl hG
  | node i F T₁ T₂ ih =>
    by_cases hF : F = flower
    · subst hF
      simp [bottom, bottomOf, graft]
    · have := ih hF
      simp only [bottom, hF, ↓reduceIte, bottomOf, graft] at this ⊢
      rw [this]

theorem order_bottomOf (x : FTree × Fin 3 × TTree × TTree) :
    (bottomOf x).order = x.1.order + x.2.2.1.order + x.2.2.2.order + 1 := by
  simp only [bottomOf, order_graft, order]
  omega

/-! ### Finiteness -/

theorem finite_order_le_ftree : ∀ M : ℕ, {F : FTree | F.order ≤ M}.Finite
  | 0 => (Set.finite_singleton flower).subset fun F hF => by
      cases F with
      | flower => rfl
      | node => simp [order] at hF
  | M + 1 => by
      have hT := Canon.finite_order_le M
      have hF := finite_order_le_ftree M
      refine ((Set.finite_singleton flower).union
        ((((Set.finite_univ (α := Fin 3)).prod hF).prod (hT.prod hT)).image
          fun x => node x.1.1 x.1.2 x.2.1 x.2.2)).subset ?_
      intro G hG
      cases G with
      | flower => exact Or.inl rfl
      | node i F T₁ T₂ =>
        simp only [Set.mem_ofPred_eq, order] at hG
        refine Or.inr ⟨((i, F), (T₁, T₂)), ?_, rfl⟩
        simp only [Set.mem_prod, Set.mem_univ, Set.mem_ofPred_eq, true_and]
        omega

/-- The flower trees of order `≤ M`. -/
noncomputable def ftreesLE (M : ℕ) : Finset FTree := (finite_order_le_ftree M).toFinset

theorem mem_ftreesLE {M : ℕ} {F : FTree} : F ∈ ftreesLE M ↔ F.order ≤ M := by simp [ftreesLE]

/-- The trees of order `≤ M`. -/
noncomputable def treesLE (M : ℕ) : Finset TTree := (Canon.finite_order_le M).toFinset

theorem mem_treesLE {M : ℕ} {T : TTree} : T ∈ treesLE M ↔ T.order ≤ M := by simp [treesLE]

/-! ### The classes -/

/-- `𝒳`'s flower trees without the trivial one: orders `1, …, N`. -/
noncomputable def Xset (N : ℕ) : Finset FTree := (ftreesLE N).filter (· ≠ flower)

/-- All root attachments `(i, F, T₁, T₂)` with `F, T₁, T₂` of order `≤ N`. -/
noncomputable def Rind (N : ℕ) : Finset (Fin 3 × FTree × TTree × TTree) :=
  univ ×ˢ ftreesLE N ×ˢ treesLE N ×ˢ treesLE N

/-- `𝒴`'s flower trees: (Y-1) order `> N`, (Y-2) the children of the root have order `≤ N`. -/
noncomputable def Yind (N : ℕ) : Finset (Fin 3 × FTree × TTree × TTree) :=
  (Rind N).filter fun x => N < (rootOf x).order

/-- All flower attachments `(F, i, T₁, T₂)` with `F, T₁, T₂` of order `≤ N`. -/
noncomputable def Wind' (N : ℕ) : Finset (FTree × Fin 3 × TTree × TTree) :=
  ftreesLE N ×ˢ univ ×ˢ treesLE N ×ˢ treesLE N

/-- `𝒲`'s flower trees:
- (W-1) order `> N`;
- (W-2) the siblings `T₁, T₂` of `𝔣` have order `≤ N`;
- (W-3) the tree with `𝔣^pr` replaced by a flower, `F`, has order `≤ N`. -/
noncomputable def Wind (N : ℕ) : Finset (FTree × Fin 3 × TTree × TTree) :=
  (Wind' N).filter fun x => N < (bottomOf x).order

/-- The root attachments of order `≤ N` are `𝒳`'s trees; the rest are `𝒴`'s. -/
theorem sum_Rind {M : Type*} [AddCommMonoid M] (N : ℕ) (f : FTree → M) :
    ∑ x ∈ Rind N, f (rootOf x) = ∑ G ∈ Xset N, f G + ∑ x ∈ Yind N, f (rootOf x) := by
  rw [← Finset.sum_filter_not_add_sum_filter (Rind N) (fun x => N < (rootOf x).order)]
  congr 1
  refine Finset.sum_nbij' rootOf
    (fun G => match G with
      | flower => (0, flower, .leaf, .leaf)
      | node i F T₁ T₂ => (i, F, T₁, T₂)) ?_ ?_ ?_ ?_ ?_
  · rintro ⟨i, F, T₁, T₂⟩ hx
    simp only [Rind, Finset.mem_filter, Finset.mem_product, Finset.mem_univ, true_and, mem_ftreesLE,
      mem_treesLE, not_lt, rootOf, order] at hx
    simp only [Xset, Finset.mem_filter, mem_ftreesLE, rootOf, order, ne_eq, reduceCtorEq,
      not_false_eq_true, and_true]
    omega
  · intro G hG
    simp only [Xset, Finset.mem_filter, mem_ftreesLE] at hG
    cases G with
    | flower => exact absurd rfl hG.2
    | node i F T₁ T₂ =>
      simp only [order] at hG
      simp only [Rind, Finset.mem_filter, Finset.mem_product, Finset.mem_univ, true_and,
        mem_ftreesLE, mem_treesLE, not_lt, rootOf, order]
      omega
  · intro x _
    rfl
  · intro G hG
    simp only [Xset, Finset.mem_filter] at hG
    cases G with
    | flower => exact absurd rfl hG.2
    | node => rfl
  · intro x _
    rfl

/-- The flower attachments of order `≤ N` are `𝒳`'s trees; the rest are `𝒲`'s. -/
theorem sum_Wind' {M : Type*} [AddCommMonoid M] (N : ℕ) (f : FTree → M) :
    ∑ x ∈ Wind' N, f (bottomOf x) = ∑ G ∈ Xset N, f G + ∑ x ∈ Wind N, f (bottomOf x) := by
  rw [← Finset.sum_filter_not_add_sum_filter (Wind' N) (fun x => N < (bottomOf x).order)]
  congr 1
  refine Finset.sum_nbij' bottomOf FTree.bottom ?_ ?_ ?_ ?_ ?_
  · rintro ⟨F, i, T₁, T₂⟩ hx
    simp only [Wind', Finset.mem_filter, Finset.mem_product, Finset.mem_univ, true_and, mem_ftreesLE,
      mem_treesLE, not_lt] at hx
    simp only [Xset, Finset.mem_filter, mem_ftreesLE]
    exact ⟨hx.2, graft_ne_flower (by simp)⟩
  · intro G hG
    simp only [Xset, Finset.mem_filter, mem_ftreesLE] at hG
    have h1 := bottomOf_bottom hG.2
    have h2 := order_bottomOf G.bottom
    rw [h1] at h2
    simp only [Wind', Finset.mem_filter, Finset.mem_product, Finset.mem_univ, true_and,
      mem_ftreesLE, mem_treesLE, not_lt, h1]
    omega
  · intro x _
    exact bottom_bottomOf x
  · intro G hG
    simp only [Xset, Finset.mem_filter] at hG
    exact bottomOf_bottom hG.2
  · intro x _
    rfl

end WaveTurbulence.SysAPI
