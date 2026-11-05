/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.XChain.CplDraft.L0Rep
public import WaveTurbulence.Foundations.XChain.CplDraft.FamKernel
public import WaveTurbulence.Foundations.XChain.LayerCutOrder
public import WaveTurbulence.Foundations.XChain.TreeCutBranches
public import WaveTurbulence.Foundations.XChain.FlowerDraft.GateProbes

/-!
# CPL-2, step 4: the kind `ℒ₀` of B1.12 is the family `l0Trees`

**Statements.**
1. `treeKindOK_L0_iff`: for a layered garden with all layers `≤ p`, B1.12's `TreeKindOK p N .L0` holds iff
   every top tree `layerCutForest LG p j` is in `l0Trees N`. The source condition reads: top order `> N`,
   and each child of the root has `≤ N` layer-`p` branching nodes below it.
2. `coupleSum_L0_eq`: B1.12's `coupleSum_N` of kind `ℒ₀` without `∂_t` is the `l0Trees`-weighted sum of
   `K_𝒬` over `𝒬 ∈ 𝒞_{p+1}` of order `N`, with truncation `(3N_{p+1}+1, N_p)`.

**Proof.**
- The layer-`p` branching nodes below the `i`-th child of the root correspond to the branching paths of
  the cut tree that start with `i` (INDUCT `layerCut_branch_mem_iff`). For `node(l, m, r)` they number
  `n(l)`, `n(m)`, `n(r)` (`card_branching_prefix`).
- The kernel is `K_𝒬 = KG` (`kernelKgen_noFix`, `KG_eq_KQ`), as in the bridge `coupleSum_tr`.
-/

@[expose] public section

namespace WaveTurbulence.Cpl

open Finset Induct
open scoped Classical

/-! ## Branching paths below a child of the root -/

theorem card_branching_prefix (l m r : TTree) (i : Fin 3) :
    ((TTree.node l m r).branching.filter (fun a => [i] <+: a)).card = (![l, m, r] i).order := by
  have hpre (j : Fin 3) (S : Finset TTree.Path) :
      (TTree.pre j S).filter (fun a => [i] <+: a) = if i = j then TTree.pre j S else ∅ := by
    unfold TTree.pre
    rw [filter_image]
    split_ifs with h
    · subst h
      rw [filter_true_of_mem fun q _ => List.cons_prefix_cons.mpr ⟨rfl, List.nil_prefix⟩]
    · rw [filter_false_of_mem fun q _ hq => h (List.cons_prefix_cons.mp hq).1, image_empty]
  have hcard (j : Fin 3) (S : Finset TTree.Path) : (TTree.pre j S).card = S.card :=
    card_image_of_injective _ List.cons_injective
  have hnil : ¬ ([i] <+: ([] : TTree.Path)) := fun h => by simpa using h.length_le
  simp only [TTree.branching, filter_insert, hnil, ite_false, filter_union, hpre]
  fin_cases i <;>
    simp [hcard, TTree.card_branching_eq]

/-- The layer-`p` branching nodes below the `i`-th child of the root of tree `j`, counted on the cut tree. -/
theorem topCountBelow_child_eq {w : ℕ} (LG : LayeredGarden w) (p : ℕ) (hbound : ∀ a, LG.layer a ≤ p)
    (b : GBranch LG.garden.tree) {j : Fin w} (hb : b.1 = (j, [])) (i : Fin 3) :
    LG.topCountBelow p (b.child i) =
      ((layerCutForest LG p j).branching.filter (fun a => [i] <+: a)).card := by
  unfold LayeredGarden.topCountBelow
  symm
  refine card_bij (fun a ha => (⟨(j, a), cutTree_branching_subset _ _ (mem_filter.mp ha).1⟩ :
    GBranch LG.garden.tree)) ?_ ?_ ?_
  · intro a ha
    obtain ⟨ha1, ha2⟩ := mem_filter.mp ha
    refine mem_filter.mpr ⟨mem_univ _, ⟨?_, ?_⟩, ?_⟩
    · change b.1.1 = j
      rw [hb]
    · change b.1.2 ++ [i] <+: a
      rw [hb]
      exact ha2
    · exact (layerCut_branch_mem_iff LG p hbound ⟨(j, a), _⟩).mp ha1
  · intro a _ a' _ h
    exact congrArg (fun z : GBranch LG.garden.tree => z.1.2) h
  · intro b' hb'
    obtain ⟨-, ⟨hj, hpfx⟩, hl⟩ := mem_filter.mp hb'
    have hj' : b'.1.1 = j := by
      have h1 : (b.child i).1.1 = b.1.1 := rfl
      have h2 : b'.toNode.1.1 = b'.1.1 := rfl
      rw [← h2, ← hj, h1, hb]
    have hmem : b'.1.2 ∈ (layerCutForest LG p j).branching := by
      rw [← hj']
      exact (layerCut_branch_mem_iff LG p hbound b').mpr hl
    refine ⟨b'.1.2, mem_filter.mpr ⟨hmem, ?_⟩, ?_⟩
    · have : (b.child i).1.2 = b.1.2 ++ [i] := rfl
      rw [this, hb] at hpfx
      exact hpfx
    · exact Subtype.ext (Prod.ext hj'.symm rfl)

/-- **The kind `ℒ₀` is the family `l0Trees`.** -/
theorem treeKindOK_L0_iff {w : ℕ} (LG : LayeredGarden w) (p N : ℕ) (hbound : ∀ a, LG.layer a ≤ p) :
    LG.TreeKindOK p N .L0 ↔ ∀ j, layerCutForest LG p j ∈ l0Trees N := by
  simp only [LayeredGarden.TreeKindOK]
  refine forall_congr' fun j => ?_
  rw [← layerCutForest_order LG p hbound j]
  constructor
  · rintro ⟨hN, hch⟩
    cases hT : layerCutForest LG p j with
    | leaf =>
      rw [hT] at hN
      simp [TTree.order] at hN
    | node l m r =>
      have hroot : ([] : TTree.Path) ∈ (LG.garden.tree j).branching := by
        have h0 : ([] : TTree.Path) ∈ (layerCutForest LG p j).branching := by
          rw [hT]; simp [TTree.branching]
        exact cutTree_branching_subset _ _ h0
      let b : GBranch LG.garden.tree := ⟨(j, []), hroot⟩
      have hc (i : Fin 3) : (![l, m, r] i).order ≤ N := by
        have h := hch b rfl i
        rw [topCountBelow_child_eq LG p hbound b rfl i, hT, card_branching_prefix] at h
        exact h
      rw [hT] at hN
      have h0 := hc 0
      have h1 := hc 1
      have h2 := hc 2
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
        Matrix.tail_cons] at h0 h1 h2
      refine mem_l0Trees.mpr ⟨l, m, r, rfl, h0, h1, h2, ?_⟩
      simp only [TTree.order] at hN
      omega
  · intro h
    obtain ⟨l, m, r, hT, h0, h1, h2, hs⟩ := mem_l0Trees.mp h
    refine ⟨?_, fun b hb i => ?_⟩
    · rw [hT]
      simp only [TTree.order]
      omega
    · rw [topCountBelow_child_eq LG p hbound b hb i, hT, card_branching_prefix]
      fin_cases i <;> simpa

/-! ## The couple sum of kind `ℒ₀` -/

/-- **`coupleSum` of kind `ℒ₀`** (no `∂_t`) as the `l0Trees`-weighted garden sum. -/
theorem coupleSum_L0_eq (P : WTParams) (F : ℕ → Mom P.d → ℝ) (p N : ℕ) (t : ℝ) (n : Fin P.d → ℤ) :
    coupleSum P F p N .L0 false t (latticePoint P.L n) =
      ∑ᶠ LG : {LG : LayeredGarden 2 // (IsCanonC (p + 1) LG ∧
          LG.IsTrunc p (3 * P.N (p + 1) + 1) (P.N p)) ∧ LG.garden.order = N},
        if ∀ j, layerCutForest LG.1 p j ∈ l0Trees (P.N (p + 1)) then
          KG P.L P.γ P.δ F LG.1 t (fun _ => n) else 0 := by
  unfold coupleSum
  rw [finsum_subtype_eq_finsum_cond (f := fun LG : LayeredGarden 2 =>
    if ∀ j, layerCutForest LG p j ∈ l0Trees (P.N (p + 1)) then KG P.L P.γ P.δ F LG t (fun _ => n) else 0)
    (fun LG => (IsCanonC (p + 1) LG ∧ LG.IsTrunc p (3 * P.N (p + 1) + 1) (P.N p)) ∧
      LG.garden.order = N)]
  refine finsum_congr fun LG => ?_
  rw [finsum_eq_if, finsum_eq_if]
  by_cases hcan : IsCanonC (p + 1) LG
  · have hbound : ∀ a, LG.layer a ≤ p := Canon.layer_le_of_isCanonC hcan
    have hkind := treeKindOK_L0_iff LG p (P.N (p + 1)) hbound
    by_cases hc : (∀ u ∈ LG.attachNodes p, LG.attachedOrder p u ≤ P.N p) ∧ LG.garden.order = N ∧
        ∀ j, layerCutForest LG p j ∈ l0Trees (P.N (p + 1))
    · obtain ⟨hatt, hord, hl0⟩ := hc
      have h1 : IsCanonC (p + 1) LG ∧ (∀ u ∈ LG.attachNodes p, LG.attachedOrder p u ≤ P.N p) ∧
          LG.garden.order = N ∧ LG.TreeKindOK p (P.N (p + 1)) .L0 ∧
          (false = true → ∀ j : Fin 2, ∃ b : GBranch LG.garden.tree, b.1 = (j, []) ∧ LG.layer b.toNode = p) :=
        ⟨hcan, hatt, hord, hkind.mpr hl0, fun h => absurd h (by decide)⟩
      have h2 : (IsCanonC (p + 1) LG ∧ LG.IsTrunc p (3 * P.N (p + 1) + 1) (P.N p)) ∧
          LG.garden.order = N := by
        refine ⟨⟨hcan, fun j => ?_, hatt⟩, hord⟩
        rw [← layerCutForest_order LG p hbound j]
        exact order_le_of_mem_l0Trees (hl0 j)
      rw [ite_eq_left h1, ite_eq_left h2, ite_eq_left hl0]
      have hfix : (fun b : GBranch LG.garden.tree =>
          if false = true ∧ b.1.2 = [] then some t else none) = fun _ => none := by
        funext b
        simp
      rw [hfix, FlowerProbes.kernelKgen_noFix P.L P.γ P.δ F LG hcan.1.1 _ 0,
        Canon.KG_eq_KQ _ _ _ F LG (Canon.isCouple_of_isCanonC hcan).1 t n]
      unfold KQ KQstar
      simp only [ite_self]
    · have h1 : ¬ (IsCanonC (p + 1) LG ∧ (∀ u ∈ LG.attachNodes p, LG.attachedOrder p u ≤ P.N p) ∧
          LG.garden.order = N ∧ LG.TreeKindOK p (P.N (p + 1)) .L0 ∧
          (false = true → ∀ j : Fin 2, ∃ b : GBranch LG.garden.tree, b.1 = (j, []) ∧ LG.layer b.toNode = p)) :=
        fun h => hc ⟨h.2.1, h.2.2.1, hkind.mp h.2.2.2.1⟩
      rw [ite_eq_right h1]
      by_cases h2 : (IsCanonC (p + 1) LG ∧ LG.IsTrunc p (3 * P.N (p + 1) + 1) (P.N p)) ∧
          LG.garden.order = N
      · rw [ite_eq_left h2, ite_eq_right (fun hl0 => hc ⟨h2.1.2.2, h2.2, hl0⟩)]
      · rw [ite_eq_right h2]
  · rw [ite_eq_right (fun h => hcan h.1), ite_eq_right (fun h => hcan h.1.1)]

end WaveTurbulence.Cpl
