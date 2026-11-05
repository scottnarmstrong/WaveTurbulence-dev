/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.XChain.CplDraft.DtKernel
public import WaveTurbulence.Foundations.XChain.CplDraft.L0Kind
public import WaveTurbulence.Foundations.XChain.LayerCutOrder
public import WaveTurbulence.Foundations.XChain.TreeCutBranches

/-!
# CPL-3, step 7: `coupleSum` with `∂_t` as a family garden sum

**Statements.**
1. `kernelKgen_rootShift`: for a plain garden, the general kernel with root vector `n/L` and root labels `0`
   equals the one with root vector `0` and root labels `n` (the shift `shiftDec`, as in Canon's `KG_eq_KQ`).
2. `exists_layer_root_iff`: if every layer is `≤ p`, the root of tree `j` is a layer-`p` branching node iff the
   `j`-th tree of the layer-`p` cut is not `•` (snapshot 8's `dt` clause, CL-22).
3. `coupleSum_trDt_eq`, `coupleSum_L0Dt_eq`: B1.12's `coupleSum_N` with `∂_t`, of kind `tr` and `ℒ₀`, as the
   weighted garden sums of the family `(truncatedTrees N_{p+1}).erase •` (resp. `l0Trees N_{p+1}`), with the
   kernel `kernelKgen(roots at t)` and root labels `n`.
4. `aTrDt_eq_famGenTerm_erase`: `∂_t a^tr` is the family over the non-trivial truncated trees (`∂_t 𝒥_• = 0`).
-/

@[expose] public section

open WaveTurbulence.X2E
namespace WaveTurbulence.Cpl

open Finset Induct SysAPI
open scoped Classical

section Shift

variable (L γ δ : ℝ) {d w : ℕ}

/-- **The root shift** of the general kernel. -/
theorem kernelKgen_rootShift (F : ℕ → Mom d → ℝ) (LG : LayeredGarden w) (hP : LG.garden.IsPlain)
    (fix : GBranch LG.garden.tree → Option ℝ) (off : Finset (GBranch LG.garden.tree))
    (wt : (GNode LG.garden.tree → Mom d) → ℝ) (up : GBranch LG.garden.tree → ℝ) (n : Fin d → ℤ) :
    kernelKgen L γ δ F LG fix off wt up (latticePoint L n) (fun _ => 0) 0 =
      kernelKgen L γ δ F LG fix off wt up 0 (fun _ => n) 0 := by
  unfold kernelKgen
  congr 1
  rw [← (Canon.shiftDec LG.garden hP n (nroot := fun _ => 0) (nroot' := fun _ => n)
    (fun _ => (zero_add n).symm)).tsum_eq]
  refine tsum_congr fun κ => ?_
  have hcos : cosetDecoration LG.garden L 0 (fun a => κ.1 a + n) =
      cosetDecoration LG.garden L (latticePoint L n) κ.1 := by
    funext a
    simp only [cosetDecoration, Canon.latticePoint_add]
    abel
  have heps : epsDec LG.garden (fun a => κ.1 a + n) = epsDec LG.garden κ.1 := by
    unfold epsDec
    exact Finset.prod_congr rfl fun b _ => Canon.epsCoef_add _ _ _ n
  have hk : ((Canon.shiftDec LG.garden hP n (nroot := fun _ => 0) (nroot' := fun _ => n)
      (fun _ => (zero_add n).symm)) κ).1 = fun a => κ.1 a + n := rfl
  rw [hk, hcos, heps]

end Shift

/-- **Layer-`p` roots** are the roots of non-trivial cut trees. -/
theorem exists_layer_root_iff {w : ℕ} (LG : LayeredGarden w) (p : ℕ) (hbound : ∀ a, LG.layer a ≤ p)
    (j : Fin w) :
    (∃ b : GBranch LG.garden.tree, b.1 = (j, []) ∧ LG.layer b.toNode = p) ↔ layerCutForest LG p j ≠ .leaf := by
  rw [← nil_mem_branching_iff]
  constructor
  · rintro ⟨b, hb, hl⟩
    have h := (layerCut_branch_mem_iff LG p hbound b).mpr hl
    rw [hb] at h
    exact h
  · intro h
    have hmem : ([] : TTree.Path) ∈ (LG.garden.tree j).branching :=
      cutTree_branching_subset (LG.garden.tree j) (layerCutStop LG p j) h
    exact ⟨⟨(j, []), hmem⟩, rfl, (layerCut_branch_mem_iff LG p hbound ⟨(j, []), hmem⟩).mp h⟩

theorem ne_leaf_of_mem_l0Trees {N : ℕ} {T : TTree} (h : T ∈ l0Trees N) : T ≠ .leaf := by
  obtain ⟨l, m, r, hT, -⟩ := mem_l0Trees.mp h
  rw [hT]
  exact TTree.noConfusion

theorem rootFix_eq_dt {w : ℕ} {tree : Fin w → TTree} (t : ℝ) :
    (fun b : GBranch tree => if true = true ∧ b.1.2 = [] then some t else none) = rootFix t := by
  funext b
  simp [rootFix]

/-! ## The couple sums with `∂_t` -/

/-- **`coupleSum` of kind `tr` with `∂_t`** as the weighted garden sum over the non-trivial truncated trees. -/
theorem coupleSum_trDt_eq (P : WTParams) (F : ℕ → Mom P.d → ℝ) (p N : ℕ) (t : ℝ) (n : Fin P.d → ℤ) :
    coupleSum P F p N .tr true t (latticePoint P.L n) =
      ∑ᶠ LG : {LG : LayeredGarden 2 // (IsCanonC (p + 1) LG ∧
          LG.IsTrunc p (P.N (p + 1)) (P.N p)) ∧ LG.garden.order = N},
        if ∀ j, layerCutForest LG.1 p j ∈ (truncatedTrees (P.N (p + 1))).erase .leaf then
          kernelKgen P.L P.γ P.δ F LG.1 (rootFix t) ∅ (fun _ => 1) (fun _ => t) 0 (fun _ => n) 0 else 0 := by
  unfold coupleSum
  rw [finsum_subtype_eq_finsum_cond (f := fun LG : LayeredGarden 2 =>
    if ∀ j, layerCutForest LG p j ∈ (truncatedTrees (P.N (p + 1))).erase .leaf then
      kernelKgen P.L P.γ P.δ F LG (rootFix t) ∅ (fun _ => 1) (fun _ => t) 0 (fun _ => n) 0 else 0)
    (fun LG => (IsCanonC (p + 1) LG ∧ LG.IsTrunc p (P.N (p + 1)) (P.N p)) ∧ LG.garden.order = N)]
  refine finsum_congr fun LG => ?_
  rw [finsum_eq_if, finsum_eq_if]
  by_cases hcan : IsCanonC (p + 1) LG
  · have hbound : ∀ a, LG.layer a ≤ p := Canon.layer_le_of_isCanonC hcan
    have hcut : ∀ j, layerCutForest LG p j ∈ (truncatedTrees (P.N (p + 1))).erase .leaf ↔
        LG.topOrder p j ≤ P.N (p + 1) ∧ ∃ b : GBranch LG.garden.tree, b.1 = (j, []) ∧ LG.layer b.toNode = p := by
      intro j
      rw [mem_erase, mem_truncatedTrees, layerCutForest_order LG p hbound j, exists_layer_root_iff LG p hbound j]
      exact and_comm
    have hiff : (IsCanonC (p + 1) LG ∧ (∀ u ∈ LG.attachNodes p, LG.attachedOrder p u ≤ P.N p) ∧
        LG.garden.order = N ∧ LG.TreeKindOK p (P.N (p + 1)) .tr ∧
        (true = true → ∀ j : Fin 2, ∃ b : GBranch LG.garden.tree, b.1 = (j, []) ∧ LG.layer b.toNode = p)) ↔
        ((IsCanonC (p + 1) LG ∧ LG.IsTrunc p (P.N (p + 1)) (P.N p)) ∧ LG.garden.order = N) ∧
          ∀ j, layerCutForest LG p j ∈ (truncatedTrees (P.N (p + 1))).erase .leaf := by
      constructor
      · rintro ⟨hc, hatt, hord, hk, hroot⟩
        exact ⟨⟨⟨hc, hk, hatt⟩, hord⟩, fun j => (hcut j).mpr ⟨hk j, hroot rfl j⟩⟩
      · rintro ⟨⟨⟨hc, hk, hatt⟩, hord⟩, hS⟩
        exact ⟨hc, hatt, hord, hk, fun _ j => ((hcut j).mp (hS j)).2⟩
    by_cases h : ((IsCanonC (p + 1) LG ∧ LG.IsTrunc p (P.N (p + 1)) (P.N p)) ∧ LG.garden.order = N) ∧
        ∀ j, layerCutForest LG p j ∈ (truncatedTrees (P.N (p + 1))).erase .leaf
    · rw [ite_eq_left (hiff.mpr h), ite_eq_left h.1, ite_eq_left h.2, rootFix_eq_dt,
        kernelKgen_rootShift P.L P.γ P.δ F LG (Canon.isCouple_of_isCanonC hcan).1]
    · rw [ite_eq_right (fun h' => h (hiff.mp h'))]
      by_cases h1 : (IsCanonC (p + 1) LG ∧ LG.IsTrunc p (P.N (p + 1)) (P.N p)) ∧ LG.garden.order = N
      · rw [ite_eq_left h1, ite_eq_right (fun h2 => h ⟨h1, h2⟩)]
      · rw [ite_eq_right h1]
  · rw [ite_eq_right (fun h => hcan h.1), ite_eq_right (fun h => hcan h.1.1)]

/-- **`coupleSum` of kind `ℒ₀` with `∂_t`** as the `l0Trees`-weighted garden sum. -/
theorem coupleSum_L0Dt_eq (P : WTParams) (F : ℕ → Mom P.d → ℝ) (p N : ℕ) (t : ℝ) (n : Fin P.d → ℤ) :
    coupleSum P F p N .L0 true t (latticePoint P.L n) =
      ∑ᶠ LG : {LG : LayeredGarden 2 // (IsCanonC (p + 1) LG ∧
          LG.IsTrunc p (3 * P.N (p + 1) + 1) (P.N p)) ∧ LG.garden.order = N},
        if ∀ j, layerCutForest LG.1 p j ∈ l0Trees (P.N (p + 1)) then
          kernelKgen P.L P.γ P.δ F LG.1 (rootFix t) ∅ (fun _ => 1) (fun _ => t) 0 (fun _ => n) 0 else 0 := by
  unfold coupleSum
  rw [finsum_subtype_eq_finsum_cond (f := fun LG : LayeredGarden 2 =>
    if ∀ j, layerCutForest LG p j ∈ l0Trees (P.N (p + 1)) then
      kernelKgen P.L P.γ P.δ F LG (rootFix t) ∅ (fun _ => 1) (fun _ => t) 0 (fun _ => n) 0 else 0)
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
          (true = true → ∀ j : Fin 2, ∃ b : GBranch LG.garden.tree, b.1 = (j, []) ∧ LG.layer b.toNode = p) :=
        ⟨hcan, hatt, hord, hkind.mpr hl0, fun _ j =>
          (exists_layer_root_iff LG p hbound j).mpr (ne_leaf_of_mem_l0Trees (hl0 j))⟩
      have h2 : (IsCanonC (p + 1) LG ∧ LG.IsTrunc p (3 * P.N (p + 1) + 1) (P.N p)) ∧
          LG.garden.order = N := by
        refine ⟨⟨hcan, fun j => ?_, hatt⟩, hord⟩
        rw [← layerCutForest_order LG p hbound j]
        exact order_le_of_mem_l0Trees (hl0 j)
      rw [ite_eq_left h1, ite_eq_left h2, ite_eq_left hl0, rootFix_eq_dt,
        kernelKgen_rootShift P.L P.γ P.δ F LG (Canon.isCouple_of_isCanonC hcan).1]
    · have h1 : ¬ (IsCanonC (p + 1) LG ∧ (∀ u ∈ LG.attachNodes p, LG.attachedOrder p u ≤ P.N p) ∧
          LG.garden.order = N ∧ LG.TreeKindOK p (P.N (p + 1)) .L0 ∧
          (true = true → ∀ j : Fin 2, ∃ b : GBranch LG.garden.tree, b.1 = (j, []) ∧ LG.layer b.toNode = p)) :=
        fun h => hc ⟨h.2.1, h.2.2.1, hkind.mp h.2.2.2.1⟩
      rw [ite_eq_right h1]
      by_cases h2 : (IsCanonC (p + 1) LG ∧ LG.IsTrunc p (3 * P.N (p + 1) + 1) (P.N p)) ∧
          LG.garden.order = N
      · rw [ite_eq_left h2, ite_eq_right (fun hl0 => hc ⟨h2.1.2.2, h2.2, hl0⟩)]
      · rw [ite_eq_right h2]
  · rw [ite_eq_right (fun h => hcan h.1), ite_eq_right (fun h => hcan h.1.1)]

/-! ## `∂_t a^tr` over the non-trivial trees -/

theorem genTerm_dtCoef_leaf {d : ℕ} (L γ δ : ℝ) (p : ℕ) (t : ℝ) (b : (Fin d → ℤ) → ℂ) (n : Fin d → ℤ) :
    genTerm TTree.leaf (dtCoef L γ δ p t TTree.leaf) b n = 0 := by
  simp [genTerm, genSummand, dtCoef, dtTimeCoef]

theorem truncatedTrees_erase_subset (N : ℕ) : (truncatedTrees N).erase .leaf ⊆ truncatedTrees N :=
  erase_subset _ _

/-- **`∂_t a^tr` over the non-trivial truncated trees.** -/
theorem aTrDt_eq_famGenTerm_erase {d : ℕ} (L γ δ : ℝ) (p Ntr : ℕ) {b : (Fin d → ℤ) → ℂ}
    (hb : Summable fun k => ‖b k‖) (t : ℝ) (n : Fin d → ℤ) :
    aTrDt L γ δ p Ntr b t n = famGenTerm Ntr ((truncatedTrees Ntr).erase .leaf) (dtCoef L γ δ p t) b n := by
  rw [aTrDt_eq_famGenTerm L γ δ p Ntr hb t n, famGenTerm_eq_sum_of_subset subset_rfl,
    famGenTerm_eq_sum_of_subset (truncatedTrees_erase_subset Ntr)]
  exact (sum_erase (truncatedTrees Ntr) (f := fun T => genTerm T (dtCoef L γ δ p t T) b n) (a := .leaf)
    (genTerm_dtCoef_leaf L γ δ p t b n)).symm

end WaveTurbulence.Cpl
