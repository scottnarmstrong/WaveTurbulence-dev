/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.XChain.ProductCut.ProdCut
public import WaveTurbulence.Foundations.XChain.ProductCut.FlowerSumP

/-!
# FC1: properties of the product-form garden weights

The properties the flower-gate consumers use, proved for `cutWeight1P`, `cutWeight2P` (FC1 consumer analysis):
- `0 ≤ w ≤ 1` (`cutWeight1P_nonneg`, `cutWeight1P_le_one`, and the same for `cutWeight2P`);
- the upper support (`cutWeight1P_support`, `cutWeight2P_support`) and, for `j ≥ 1`, the lower support, the source
  of the gain (`exists_gt_of_cutWeight1P_ne_zero`, `exists_gt_of_cutWeight2P_ne_zero`);
- the dependency separation: `cutWeight1P` depends only on the top leaves, `cutWeight2P` only on the stem `Ω`'s
  (`cutWeight1P_congr`, `cutWeight2P_congr`);
- the product over trees (the definition), whose factors are `prodDyadicCut`, with `∑_j Ψ_j = 1`
  (`XChain.ProductCut.hasSum_prodDyadicCut`).

Note: the partition of unity `∑_j Ψ_j = 1` holds per tree (the factor of one tree), which is how the consumers use
it (X3 works with one flower tree at a time). The garden weight, with one index `j` for all trees, is not a
partition of unity (nor is the frozen `cutWeight1`).
-/

@[expose] public section

open Finset

namespace WaveTurbulence.LayeredGarden

variable {w : ℕ} (LG : LayeredGarden w) {d : ℕ}

section Bounds

theorem cutWeight1P_nonneg {L : ℝ} (hL : 0 < L) (p j₁ : ℕ) (k : GNode LG.garden.tree → Mom d) :
    0 ≤ LG.cutWeight1P p L j₁ k :=
  Finset.prod_nonneg fun _ _ => XChain.ProductCut.prodDyadicCut_nonneg _ hL (fun _ _ => norm_nonneg _) _

theorem cutWeight1P_le_one {L : ℝ} (hL : 0 < L) (p j₁ : ℕ) (k : GNode LG.garden.tree → Mom d) :
    LG.cutWeight1P p L j₁ k ≤ 1 :=
  Finset.prod_le_one₀ (fun _ _ => XChain.ProductCut.prodDyadicCut_nonneg _ hL (fun _ _ => norm_nonneg _) _) fun _ _ =>
    XChain.ProductCut.prodDyadicCut_le_one _ _

theorem cutWeight2P_nonneg {L : ℝ} (hL : 0 < L) (j₂ : ℕ) (k : GNode LG.garden.tree → Mom d) :
    0 ≤ LG.cutWeight2P L j₂ k :=
  Finset.prod_nonneg fun _ _ => XChain.ProductCut.prodDyadicCut_nonneg _ hL (fun _ _ => abs_nonneg _) _

theorem cutWeight2P_le_one {L : ℝ} (hL : 0 < L) (j₂ : ℕ) (k : GNode LG.garden.tree → Mom d) :
    LG.cutWeight2P L j₂ k ≤ 1 :=
  Finset.prod_le_one₀ (fun _ _ => XChain.ProductCut.prodDyadicCut_nonneg _ hL (fun _ _ => abs_nonneg _) _) fun _ _ =>
    XChain.ProductCut.prodDyadicCut_le_one _ _

end Bounds

section Support

open Classical in
/-- Upper support of the `M₁` weight: every non-flower top leaf is below `2^{j₁} L`. -/
theorem cutWeight1P_support {p : ℕ} {L : ℝ} (hL : 0 < L) {j₁ : ℕ} {k : GNode LG.garden.tree → Mom d}
    (h : LG.cutWeight1P p L j₁ k ≠ 0) (a : GNode LG.garden.tree) (ha : LG.IsTopLeaf p a)
    (hf : ¬ LG.IsFlowerNode a) : ‖k a‖ < 2 ^ j₁ * L := by
  have hj := (Finset.prod_ne_zero_iff.1 h) a.1.1 (Finset.mem_univ _)
  exact XChain.ProductCut.lt_of_prodDyadicCut_ne_zero _ hL (fun _ _ => norm_nonneg _) hj a
    (Finset.mem_filter.2 ⟨Finset.mem_univ _, rfl, ha, hf⟩)

open Classical in
/-- Lower support of the `M₁` weight (`j₁ ≥ 1`): every tree has a non-flower top leaf above `2^{j₁} L / 4`. -/
theorem exists_gt_of_cutWeight1P_ne_zero {p : ℕ} {L : ℝ} (hL : 0 < L) {j₁ : ℕ} (hj₁ : 1 ≤ j₁)
    {k : GNode LG.garden.tree → Mom d} (h : LG.cutWeight1P p L j₁ k ≠ 0) (j : Fin w) :
    ∃ a : GNode LG.garden.tree, a.1.1 = j ∧ LG.IsTopLeaf p a ∧ ¬ LG.IsFlowerNode a ∧
      2 ^ j₁ * L / 4 < ‖k a‖ := by
  have hj := (Finset.prod_ne_zero_iff.1 h) j (Finset.mem_univ _)
  obtain ⟨a, ha, hlt⟩ := XChain.ProductCut.exists_gt_of_prodDyadicCut_ne_zero _ hL (fun _ _ => norm_nonneg _) hj₁ hj
  obtain ⟨-, h1, h2, h3⟩ := Finset.mem_filter.1 ha
  exact ⟨a, h1, h2, h3, hlt⟩

open Classical in
/-- Upper support of the `M₂` weight: every stem `|Ω_b|`, `b ≠ 𝔣^pr`, is below `2^{j₂} L`. -/
theorem cutWeight2P_support {L : ℝ} (hL : 0 < L) {j₂ : ℕ} {k : GNode LG.garden.tree → Mom d}
    (h : LG.cutWeight2P L j₂ k ≠ 0) (b : GBranch LG.garden.tree) (hb : LG.OnStem b.toNode)
    (hf : ¬ LG.garden.IsFlowerParent b) : |omegaNode LG.garden k b| < 2 ^ j₂ * L := by
  have hj := (Finset.prod_ne_zero_iff.1 h) b.1.1 (Finset.mem_univ _)
  exact XChain.ProductCut.lt_of_prodDyadicCut_ne_zero _ hL (fun _ _ => abs_nonneg _) hj b
    (Finset.mem_filter.2 ⟨Finset.mem_univ _, rfl, hb, hf⟩)

open Classical in
/-- Lower support of the `M₂` weight (`j₂ ≥ 1`): every tree has a stem `|Ω_b|`, `b ≠ 𝔣^pr`, above `2^{j₂} L / 4`. -/
theorem exists_gt_of_cutWeight2P_ne_zero {L : ℝ} (hL : 0 < L) {j₂ : ℕ} (hj₂ : 1 ≤ j₂)
    {k : GNode LG.garden.tree → Mom d} (h : LG.cutWeight2P L j₂ k ≠ 0) (j : Fin w) :
    ∃ b : GBranch LG.garden.tree, b.1.1 = j ∧ LG.OnStem b.toNode ∧ ¬ LG.garden.IsFlowerParent b ∧
      2 ^ j₂ * L / 4 < |omegaNode LG.garden k b| := by
  have hj := (Finset.prod_ne_zero_iff.1 h) j (Finset.mem_univ _)
  obtain ⟨b, hb, hlt⟩ := XChain.ProductCut.exists_gt_of_prodDyadicCut_ne_zero _ hL (fun _ _ => abs_nonneg _) hj₂ hj
  obtain ⟨-, h1, h2, h3⟩ := Finset.mem_filter.1 hb
  exact ⟨b, h1, h2, h3, hlt⟩

end Support

section Separation

open Classical in
/-- The `M₁` weight depends only on the top leaves. -/
theorem cutWeight1P_congr (p : ℕ) (L : ℝ) (j₁ : ℕ) {k k' : GNode LG.garden.tree → Mom d}
    (h : ∀ a, LG.IsTopLeaf p a → ¬ LG.IsFlowerNode a → k a = k' a) :
    LG.cutWeight1P p L j₁ k = LG.cutWeight1P p L j₁ k' :=
  Finset.prod_congr rfl fun _ _ => XChain.ProductCut.prodDyadicCut_congr _ L j₁ fun a ha => by
    obtain ⟨-, -, h2, h3⟩ := Finset.mem_filter.1 ha
    simp only [h a h2 h3]

open Classical in
/-- The `M₂` weight depends only on the stem `Ω`'s. -/
theorem cutWeight2P_congr (L : ℝ) (j₂ : ℕ) {k k' : GNode LG.garden.tree → Mom d}
    (h : ∀ b : GBranch LG.garden.tree, LG.OnStem b.toNode → ¬ LG.garden.IsFlowerParent b →
      omegaNode LG.garden k b = omegaNode LG.garden k' b) :
    LG.cutWeight2P L j₂ k = LG.cutWeight2P L j₂ k' :=
  Finset.prod_congr rfl fun _ _ => XChain.ProductCut.prodDyadicCut_congr _ L j₂ fun b hb => by
    obtain ⟨-, -, h2, h3⟩ := Finset.mem_filter.1 hb
    simp only [h b h2 h3]

end Separation

end WaveTurbulence.LayeredGarden
