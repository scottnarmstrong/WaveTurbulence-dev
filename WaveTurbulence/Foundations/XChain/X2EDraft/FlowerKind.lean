/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.XChain.X2EDraft.FlowerSumTops
public import WaveTurbulence.Foundations.XChain.X2EDraft.RandK

/-!
# X2E-3, step 8: the kinds of flower trees by counts

`cntBelow T q`: the number of branching nodes of `T` at or below the address `q`.

**Statements** (flower trees `F ≠ 𝔣`, with flower parent path `fp = F.flowerPath.dropLast`):
- `mem_Xset_iff`: `F ∈ 𝒳_N ↔ F.order ≤ N`;
- `mem_Ytrees_iff`: `F ∈ 𝒴_N ↔ N < F.order ∧ ∀ k, cntBelow F.toTree [k] ≤ N`;
- `mem_Wtrees_iff`: `F ∈ 𝒲_N ↔ N < F.order ∧ (∀ k, fp ++ [k] ≠ F.flowerPath → cntBelow F.toTree (fp ++ [k]) ≤ N) ∧
  F.order − cntBelow F.toTree fp ≤ N`.
-/

@[expose] public section

namespace WaveTurbulence.X2E

open Finset Induct SysAPI
open scoped Classical

/-! ## Counting branching nodes below an address -/

/-- The branching nodes of `T` at or below the address `q`. -/
noncomputable def cntBelow (T : TTree) (q : TTree.Path) : ℕ := (T.branching.filter (q <+: ·)).card

theorem cntBelow_nil (T : TTree) : cntBelow T [] = T.order := by
  unfold cntBelow
  rw [filter_true_of_mem (fun a _ => List.nil_prefix), TTree.card_branching_eq]

theorem cntBelow_node_cons (l m r : TTree) (i : Fin 3) (q : TTree.Path) :
    cntBelow (.node l m r) (i :: q) = cntBelow (![l, m, r] i) q := by
  unfold cntBelow
  have hpre (j : Fin 3) (S : Finset TTree.Path) :
      (TTree.pre j S).filter (fun a => i :: q <+: a) = if i = j then TTree.pre j (S.filter (q <+: ·)) else ∅ := by
    unfold TTree.pre
    rw [filter_image]
    split_ifs with h
    · subst h
      congr 1
      exact filter_congr fun a _ => List.cons_prefix_cons.trans (and_iff_right rfl)
    · rw [filter_false_of_mem fun a _ ha => h (List.cons_prefix_cons.mp ha).1, image_empty]
  have hcard (j : Fin 3) (S : Finset TTree.Path) : (TTree.pre j S).card = S.card :=
    card_image_of_injective _ List.cons_injective
  have hnil : ¬ (i :: q <+: ([] : TTree.Path)) := fun h => by simpa using h.length_le
  simp only [TTree.branching, filter_insert, hnil, ite_false, filter_union, hpre]
  fin_cases i <;> simp [hcard]

/-! ## Flower trees -/

open FTree in
/-- The children of the root of `node i F T₁ T₂`. -/
theorem toTree_node (i : Fin 3) (F : FTree) (T₁ T₂ : TTree) :
    (node i F T₁ T₂).toTree = .node (if i = 0 then F.toTree else T₁) (if i = 0 then T₁ else if i = 1 then F.toTree
      else T₂) (if i = 2 then F.toTree else T₂) := by
  fin_cases i <;> rfl

open FTree in
theorem cntBelow_node_self (i : Fin 3) (F : FTree) (T₁ T₂ : TTree) (q : TTree.Path) :
    cntBelow (node i F T₁ T₂).toTree (i :: q) = cntBelow F.toTree q := by
  rw [toTree_node, cntBelow_node_cons]
  fin_cases i <;> rfl

open FTree in
theorem flowerPath_graft : ∀ F H : FTree, (F.graft H).flowerPath = F.flowerPath ++ H.flowerPath
  | flower, _ => rfl
  | node i F _ _, H => by
    change i :: (F.graft H).flowerPath = i :: (F.flowerPath ++ H.flowerPath)
    rw [flowerPath_graft F H]

open FTree in
theorem cntBelow_graft : ∀ (F H : FTree) (q : TTree.Path),
    cntBelow (F.graft H).toTree (F.flowerPath ++ q) = cntBelow H.toTree q
  | flower, _, _ => rfl
  | node i F T₁ T₂, H, q => by
    change cntBelow (node i (F.graft H) T₁ T₂).toTree (i :: (F.flowerPath ++ q)) = _
    rw [cntBelow_node_self, cntBelow_graft F H q]

theorem order_eq_toTree (F : FTree) : F.order = F.toTree.order := (order_toTree F).symm

/-- `F ∈ 𝒳_N`. -/
theorem mem_Xset_iff {N : ℕ} {F : FTree} (hF : F ≠ FTree.flower) : F ∈ Xset N ↔ F.order ≤ N := by
  simp [Xset, mem_ftreesLE, hF]

/-- The children orders of `node i F T₁ T₂`. -/
theorem forall_cntBelow_child_iff (i : Fin 3) (F : FTree) (T₁ T₂ : TTree) (N : ℕ) :
    (∀ k : Fin 3, cntBelow (FTree.node i F T₁ T₂).toTree [k] ≤ N) ↔
      F.order ≤ N ∧ T₁.order ≤ N ∧ T₂.order ≤ N := by
  rw [toTree_node, order_eq_toTree]
  simp only [cntBelow_node_cons, cntBelow_nil]
  constructor
  · intro h
    have h0 := h 0
    have h1 := h 1
    have h2 := h 2
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
      Matrix.tail_cons] at h0 h1 h2
    fin_cases i <;> simp_all
  · rintro ⟨hF, h1, h2⟩ k
    fin_cases i <;> fin_cases k <;> simp_all

/-- `F ∈ 𝒴_N`. -/
theorem mem_Ytrees_iff {N : ℕ} {F : FTree} (hF : F ≠ FTree.flower) :
    F ∈ (Yind N).image rootOf ↔ N < F.order ∧ ∀ k : Fin 3, cntBelow F.toTree [k] ≤ N := by
  cases F with
  | flower => exact absurd rfl hF
  | node i F T₁ T₂ =>
    rw [forall_cntBelow_child_iff]
    constructor
    · intro h
      obtain ⟨⟨i', F', T₁', T₂'⟩, hx, he⟩ := mem_image.mp h
      simp only [rootOf, FTree.node.injEq] at he
      obtain ⟨rfl, rfl, rfl, rfl⟩ := he
      obtain ⟨hR, hN⟩ := mem_filter.mp hx
      obtain ⟨-, hR⟩ := mem_product.mp hR
      obtain ⟨hF', hR⟩ := mem_product.mp hR
      obtain ⟨h1, h2⟩ := mem_product.mp hR
      exact ⟨hN, mem_ftreesLE.mp hF', mem_treesLE.mp h1, mem_treesLE.mp h2⟩
    · rintro ⟨hN, hF', h1, h2⟩
      exact mem_image.mpr ⟨(i, F, T₁, T₂), mem_filter.mpr ⟨mem_product.mpr ⟨mem_univ _, mem_product.mpr
        ⟨mem_ftreesLE.mpr hF', mem_product.mpr ⟨mem_treesLE.mpr h1, mem_treesLE.mpr h2⟩⟩⟩, hN⟩, rfl⟩

theorem mem_Wtrees_iff_bottom {N : ℕ} {G : FTree} (hG : G ≠ FTree.flower) :
    G ∈ (Wind N).image bottomOf ↔ G.bottom ∈ Wind N := by
  constructor
  · intro h
    obtain ⟨x, hx, rfl⟩ := mem_image.mp h
    rwa [bottom_bottomOf]
  · intro h
    exact mem_image.mpr ⟨G.bottom, h, bottomOf_bottom hG⟩

/-- `G ∈ 𝒲_N`. -/
theorem mem_Wtrees_iff {N : ℕ} {G : FTree} (hG : G ≠ FTree.flower) :
    G ∈ (Wind N).image bottomOf ↔ N < G.order ∧
      (∀ k : Fin 3, G.flowerPath.dropLast ++ [k] ≠ G.flowerPath →
        cntBelow G.toTree (G.flowerPath.dropLast ++ [k]) ≤ N) ∧
      G.order - cntBelow G.toTree G.flowerPath.dropLast ≤ N := by
  rw [mem_Wtrees_iff_bottom hG]
  rcases hb : G.bottom with ⟨F, i, T₁, T₂⟩
  have hG' : G = F.graft (FTree.node i FTree.flower T₁ T₂) := by
    rw [← bottomOf_bottom hG, hb]
    rfl
  have hfp : G.flowerPath = F.flowerPath ++ [i] := by
    rw [hG', flowerPath_graft]
    rfl
  have hdl : G.flowerPath.dropLast = F.flowerPath := by
    rw [hfp, List.dropLast_concat]
  have hcnt (q : TTree.Path) : cntBelow G.toTree (F.flowerPath ++ q) =
      cntBelow (FTree.node i FTree.flower T₁ T₂).toTree q := by
    rw [hG', cntBelow_graft]
  have hord : G.order = F.order + (T₁.order + T₂.order + 1) := by
    rw [hG', FTree.order_graft]
    simp only [FTree.order]
    omega
  rw [hdl, hfp]
  have hfp0 : cntBelow G.toTree F.flowerPath = T₁.order + T₂.order + 1 := by
    have h := hcnt []
    rw [List.append_nil, cntBelow_nil, ← order_eq_toTree] at h
    rw [h]
    simp only [FTree.order]
    omega
  have hsib : (∀ k : Fin 3, F.flowerPath ++ [k] ≠ F.flowerPath ++ [i] →
      cntBelow G.toTree (F.flowerPath ++ [k]) ≤ N) ↔ T₁.order ≤ N ∧ T₂.order ≤ N := by
    simp only [hcnt, ne_eq, List.append_cancel_left_eq, List.cons.injEq, and_true]
    rw [toTree_node]
    simp only [cntBelow_node_cons, cntBelow_nil]
    constructor
    · intro h
      fin_cases i
      · exact ⟨by simpa using h 1 (by decide), by simpa using h 2 (by decide)⟩
      · exact ⟨by simpa using h 0 (by decide), by simpa using h 2 (by decide)⟩
      · exact ⟨by simpa using h 0 (by decide), by simpa using h 1 (by decide)⟩
    · rintro ⟨h1, h2⟩ k hk
      fin_cases i <;> fin_cases k <;> simp_all
  rw [hsib, hfp0]
  constructor
  · intro h
    obtain ⟨hW, hN⟩ := mem_filter.mp h
    obtain ⟨hF, hW⟩ := mem_product.mp hW
    obtain ⟨-, hW⟩ := mem_product.mp hW
    obtain ⟨h1, h2⟩ := mem_product.mp hW
    have hN' : N < G.order := by
      rw [hG']
      exact hN
    have hF' : F.order ≤ N := mem_ftreesLE.mp hF
    refine ⟨hN', ⟨mem_treesLE.mp h1, mem_treesLE.mp h2⟩, ?_⟩
    rw [hord]
    omega
  · rintro ⟨hN, ⟨h1, h2⟩, h3⟩
    have hF' : F.order ≤ N := by
      rw [hord] at h3
      omega
    refine mem_filter.mpr ⟨mem_product.mpr ⟨mem_ftreesLE.mpr hF', mem_product.mpr ⟨mem_univ _,
      mem_product.mpr ⟨mem_treesLE.mpr h1, mem_treesLE.mpr h2⟩⟩⟩, ?_⟩
    change N < (F.graft (FTree.node i FTree.flower T₁ T₂)).order
    rw [← hG']
    exact hN

end WaveTurbulence.X2E
