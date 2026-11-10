/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.XChain.FixedptDraft.X3DerivFl
public import WaveTurbulence.Foundations.XChain.FlowerDraft.OFKFubini

/-!
# X3 DyadicReduction: the `M₁`, `M₂` decompositions (T L2318–L2324)

**Statement.** Let `0 < L`. Then:
1. The product-form cutoff `prodDyadicCut` (FC1; `cutWeight1P`, `cutWeight2P` of the successor gate
   `layergardenFlower_v3`). For `L > 0` and nonnegative entries `y_a`, `a ∈ s`:
   - `0 ≤ Ψ_j ≤ 1` (`XChain.ProductCut.prodDyadicCut_nonneg`, `XChain.ProductCut.prodDyadicCut_le_one`);
   - `∑_{j ≤ J} Ψ_j = ∏_a χ₀(y_a/(2^J L))` (`XChain.ProductCut.sum_prodDyadicCut`);
   - `HasSum (Ψ_·) 1` (`XChain.ProductCut.hasSum_prodDyadicCut`);
   - `Ψ_j ≠ 0` implies `y_a < 2^j L` for all `a` (`XChain.ProductCut.lt_of_prodDyadicCut_ne_zero`).
2. The kernel decompositions (`hasSum_randFlowerKernel_cut1`, `hasSum_randFlowerKernel_cut2`). For summable
   `a(p)`, any kind, pattern, `†`, `ζ`, `t`, `s`, `k`, `k'`:
   - `HasSum (j₁ ↦ 𝒦[cut1 := j₁]) 𝒦[cut1 := none]`, for any `cut2`;
   - `HasSum (j₂ ↦ 𝒦[cut2 := j₂]) 𝒦[cut2 := none]`, for any `cut1`.
3. Momentum support (`flowerKernelGen_cut1_eq_zero`). For one flower tree `F`: if
   `|k/L − ζ_F k'/L| ≥ #leaves(F) · 2^{j₁} L`, then `𝒦_F[cut1 := j₁](k, k') = 0`. This holds because all
   non-flower leaves have `|k_ℓ/L| < 2^{j₁} L`, and `k = ζ_F k' + ∑_{ℓ ≠ 𝔣} ζ_ℓ k_ℓ` (`sum_rule`).

The proof of (2): the weights `w` of `flowerKernelGen` satisfy `w[cut := none] = ∑_j w[cut := j]`, by (1).
The interchange of `∑_j` with the decoration sum is Fubini for `tsum` on `ℕ × decorations`, with the bound
`‖term_{j,κ}‖ ≤ dyadicCut_j(κ)·‖∏_{ℓ≠𝔣} a_{κ_ℓ}‖`.
-/

@[expose] public section

namespace WaveTurbulence.Fixedpt

open MeasureTheory Set SysAPI FTree

/-! ## Decompositions of the kernels -/

section Decomp

variable (L γ δ : ℝ) {d : ℕ} (hL : 0 < L) (p : ℕ) {aP : (Fin d → ℤ) → ℂ} (haP : Summable fun k => ‖aP k‖)

theorem norm_split_term_le {F : FTree} (hF : F ≠ flower) (pat : FixPat) (dagger : Option (Fin 3 → Mom d))
    (cut1 cut2 : Option ℕ) (t s : ℝ) (off : Finset (GBranch (single F.toTree)))
    (wj : ℕ → (GNode (single F.toTree) → (Fin d → ℤ)) → ℝ) (hwj0 : ∀ j κ, 0 ≤ wj j κ)
    (κ : GNode (single F.toTree) → (Fin d → ℤ)) (j : ℕ) :
    ‖epsProd F.toTree κ * ((wj j κ * treeWeight L F hF dagger cut1 cut2 κ : ℝ) : ℂ) *
      TIpat L γ δ hF p off κ pat t s * restP F aP κ‖ ≤ wj j κ * ‖restP F aP κ‖ := by
  have h1 := norm_epsProd_le F.toTree κ
  have h2 := abs_treeWeight_le_one L hF dagger cut1 cut2 κ
  have h3 := norm_TIpat_le_one L γ δ hF p off κ pat t s
  have h4 := hwj0 j κ
  rw [norm_mul, norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_mul, abs_of_nonneg h4]
  calc ‖epsProd F.toTree κ‖ * (wj j κ * |treeWeight L F hF dagger cut1 cut2 κ|) *
        ‖TIpat L γ δ hF p off κ pat t s‖ * ‖restP F aP κ‖
      ≤ 1 * (wj j κ * 1) * 1 * ‖restP F aP κ‖ := by gcongr
    _ = _ := by ring

include haP in
/-- **Fubini for a weight split**: if `w κ = ∑_j w_j κ` with `0 ≤ w_j`, `|other factors| ≤ 1`, the decoration sum
splits. -/
theorem hasSum_flowerKernelGen_split {F : FTree} (hF : F ≠ flower) (pat : FixPat)
    (dagger : Option (Fin 3 → Mom d)) (cut1 cut2 : Option ℕ) (t s : ℝ) (k k' : Fin d → ℤ)
    (wj : ℕ → (GNode (single F.toTree) → (Fin d → ℤ)) → ℝ) (hwj0 : ∀ j κ, 0 ≤ wj j κ)
    (hwj : ∀ κ, HasSum (fun j => wj j κ) 1) (Kj : ℕ → ℂ)
    (hKj : ∀ j, Kj j = treePrefactor L γ δ d F.toTree * ∑' κ : FlowerDecoration F d k k',
      epsProd F.toTree κ.1.1 * (wj j κ.1.1 * treeWeight L F hF dagger cut1 cut2 κ.1.1 : ℝ) *
        TIpat L γ δ hF p (if dagger.isSome then {F.flowerParent hF} else ∅) κ.1.1 pat t s * restP F aP κ.1.1) :
    HasSum Kj (flowerKernelGen L γ δ p F aP pat dagger cut1 cut2 t s k k') := by
  set off : Finset (GBranch (single F.toTree)) := if dagger.isSome then {F.flowerParent hF} else ∅
  set g : FlowerDecoration F d k k' × ℕ → ℂ := fun x =>
    epsProd F.toTree x.1.1.1 * (wj x.2 x.1.1.1 * treeWeight L F hF dagger cut1 cut2 x.1.1.1 : ℝ) *
      TIpat L γ δ hF p off x.1.1.1 pat t s * restP F aP x.1.1.1
  have hR := summable_restP F haP k k'
  have hgle : ∀ x : FlowerDecoration F d k k' × ℕ, ‖g x‖ ≤ wj x.2 x.1.1.1 * ‖restP F aP x.1.1.1‖ :=
    fun x => norm_split_term_le L γ δ p hF pat dagger cut1 cut2 t s off wj hwj0 x.1.1.1 x.2
  have hbsum : Summable fun x : FlowerDecoration F d k k' × ℕ => wj x.2 x.1.1.1 * ‖restP F aP x.1.1.1‖ := by
    refine (summable_prod_of_nonneg (fun x => mul_nonneg (hwj0 _ _) (norm_nonneg _))).2 ⟨fun κ => ?_, ?_⟩
    · beta_reduce
      exact ((hwj κ.1.1).mul_right ‖restP F aP κ.1.1‖).summable
    · refine hR.congr fun κ => ?_
      beta_reduce
      rw [((hwj κ.1.1).mul_right ‖restP F aP κ.1.1‖).tsum_eq, one_mul]
  have hg : Summable g := Summable.of_norm_bounded hbsum hgle
  -- the two fiberwise sums
  have hfib1 : ∀ κ : FlowerDecoration F d k k', HasSum (fun j => g (κ, j))
      (epsProd F.toTree κ.1.1 * (treeWeight L F hF dagger cut1 cut2 κ.1.1 : ℝ) *
        TIpat L γ δ hF p off κ.1.1 pat t s * restP F aP κ.1.1) := fun κ => by
    have h := Complex.hasSum_ofReal.2 ((hwj κ.1.1).mul_right (treeWeight L F hF dagger cut1 cut2 κ.1.1))
    have h2 := ((h.mul_left (epsProd F.toTree κ.1.1)).mul_right (TIpat L γ δ hF p off κ.1.1 pat t s)).mul_right
      (restP F aP κ.1.1)
    simp only [g]
    convert h2 using 1
    all_goals push_cast; ring
  have hS1 : HasSum (fun κ : FlowerDecoration F d k k' => epsProd F.toTree κ.1.1 *
      (treeWeight L F hF dagger cut1 cut2 κ.1.1 : ℝ) * TIpat L γ δ hF p off κ.1.1 pat t s * restP F aP κ.1.1)
      (∑' x, g x) :=
    hg.hasSum.prod_fiberwise hfib1
  have hg' : Summable (g ∘ (Equiv.prodComm ℕ (FlowerDecoration F d k k'))) :=
    (Equiv.prodComm ℕ (FlowerDecoration F d k k')).summable_iff.2 hg
  have hS2 : HasSum (fun j => ∑' κ : FlowerDecoration F d k k', g (κ, j)) (∑' x, g x) := by
    have h : HasSum (g ∘ (Equiv.prodComm ℕ (FlowerDecoration F d k k'))) (∑' x, g x) :=
      (Equiv.prodComm ℕ (FlowerDecoration F d k k')).hasSum_iff.2 hg.hasSum
    exact h.prod_fiberwise fun j => (hg'.prod_factor j).hasSum
  have hK : flowerKernelGen L γ δ p F aP pat dagger cut1 cut2 t s k k' =
      treePrefactor L γ δ d F.toTree * ∑' x, g x := by
    rw [flowerKernelGen_eq L γ δ hF p, hS1.tsum_eq]
  rw [hK]
  convert hS2.mul_left (treePrefactor L γ δ d F.toTree) using 1
  funext j
  rw [hKj j]

theorem treeWeight_cut1 {F : FTree} (hF : F ≠ flower) (dagger : Option (Fin 3 → Mom d)) (cut2 : Option ℕ) (j : ℕ)
    (κ : GNode (single F.toTree) → (Fin d → ℤ)) :
    treeWeight L F hF dagger (some j) cut2 κ = treeCut1 L F j κ * treeWeight L F hF dagger none cut2 κ := by
  simp only [treeWeight, Option.elim]
  ring

theorem treeWeight_cut2 {F : FTree} (hF : F ≠ flower) (dagger : Option (Fin 3 → Mom d)) (cut1 : Option ℕ) (j : ℕ)
    (κ : GNode (single F.toTree) → (Fin d → ℤ)) :
    treeWeight L F hF dagger cut1 (some j) κ = treeCut2 L F hF j κ * treeWeight L F hF dagger cut1 none κ := by
  simp only [treeWeight, Option.elim]
  ring

include hL haP in
theorem hasSum_flowerKernelGen_cut1 (F : FTree) (pat : FixPat) (dagger : Option (Fin 3 → Mom d)) (cut2 : Option ℕ)
    (t s : ℝ) (k k' : Fin d → ℤ) :
    HasSum (fun j => flowerKernelGen L γ δ p F aP pat dagger (some j) cut2 t s k k')
      (flowerKernelGen L γ δ p F aP pat dagger none cut2 t s k k') := by
  by_cases hF : F = flower
  · simp only [flowerKernelGen, hF, ↓reduceDIte]
    exact hasSum_zero
  refine hasSum_flowerKernelGen_split L γ δ p haP hF pat dagger none cut2 t s k k' (fun j κ => treeCut1 L F j κ)
    (fun j κ => XChain.ProductCut.prodDyadicCut_nonneg _ hL (fun _ _ => norm_nonneg _) j)
    (fun κ => XChain.ProductCut.hasSum_prodDyadicCut _ hL (fun _ _ => norm_nonneg _))
    _ fun j => ?_
  rw [flowerKernelGen_eq L γ δ hF p]
  simp only [treeWeight_cut1]

include hL haP in
theorem hasSum_flowerKernelGen_cut2 (F : FTree) (pat : FixPat) (dagger : Option (Fin 3 → Mom d)) (cut1 : Option ℕ)
    (t s : ℝ) (k k' : Fin d → ℤ) :
    HasSum (fun j => flowerKernelGen L γ δ p F aP pat dagger cut1 (some j) t s k k')
      (flowerKernelGen L γ δ p F aP pat dagger cut1 none t s k k') := by
  by_cases hF : F = flower
  · simp only [flowerKernelGen, hF, ↓reduceDIte]
    exact hasSum_zero
  refine hasSum_flowerKernelGen_split L γ δ p haP hF pat dagger cut1 none t s k k' (fun j κ => treeCut2 L F hF j κ)
    (fun j κ => XChain.ProductCut.prodDyadicCut_nonneg _ hL (fun _ _ => abs_nonneg _) j)
    (fun κ => XChain.ProductCut.hasSum_prodDyadicCut _ hL (fun _ _ => abs_nonneg _))
    _ fun j => ?_
  rw [flowerKernelGen_eq L γ δ hF p]
  simp only [treeWeight_cut2]

variable (Ntr : ℕ) (kind : FlowerKind) (pat : FixPat) (dagger : Option (Fin 3 → Mom d)) (ζ : ℤˣ)

include hL haP in
/-- **The `M₁` decomposition** of the random kernel of a kind. -/
theorem hasSum_randFlowerKernel_cut1 (cut2 : Option ℕ) (t s : ℝ) (k k' : Fin d → ℤ) :
    HasSum (fun j => randFlowerKernel L γ δ p Ntr aP kind pat dagger (some j) cut2 ζ t s k k')
      (randFlowerKernel L γ δ p Ntr aP kind pat dagger none cut2 ζ t s k k') := by
  unfold randFlowerKernel
  exact hasSum_sum fun F _ => hasSum_flowerKernelGen_cut1 L γ δ hL p haP F pat dagger cut2 t s k k'

include hL haP in
/-- **The `M₂` decomposition** of the random kernel of a kind. -/
theorem hasSum_randFlowerKernel_cut2 (cut1 : Option ℕ) (t s : ℝ) (k k' : Fin d → ℤ) :
    HasSum (fun j => randFlowerKernel L γ δ p Ntr aP kind pat dagger cut1 (some j) ζ t s k k')
      (randFlowerKernel L γ δ p Ntr aP kind pat dagger cut1 none ζ t s k k') := by
  unfold randFlowerKernel
  exact hasSum_sum fun F _ => hasSum_flowerKernelGen_cut2 L γ δ hL p haP F pat dagger cut1 t s k k'

end Decomp

/-! ## Momentum support -/

section Support

variable {d : ℕ}

theorem latticePoint_add (L : ℝ) (a b : Fin d → ℤ) : latticePoint L (a + b) = latticePoint L a + latticePoint L b := by
  ext j; simp [latticePoint, add_div]

theorem latticePoint_zsmul (L : ℝ) (n : ℤ) (a : Fin d → ℤ) : latticePoint L (n • a) = n • latticePoint L a := by
  ext j; simp [latticePoint, mul_div_assoc]

theorem latticePoint_sum (L : ℝ) {ι : Type*} (S : Finset ι) (f : ι → (Fin d → ℤ)) :
    latticePoint L (∑ i ∈ S, f i) = ∑ i ∈ S, latticePoint L (f i) := by
  classical
  induction S using Finset.induction_on with
  | empty => ext j; simp [latticePoint]
  | insert a S ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, latticePoint_add, ih]

/-- **Momentum conservation** for a flower decoration: `k = ζ_𝔣 k' + ∑_{ℓ ≠ 𝔣} ζ_ℓ k_ℓ`. -/
theorem flowerDecoration_root {F : FTree} {k k' : Fin d → ℤ} (κ : FlowerDecoration F d k k') :
    k = (F.sign : ℤ) • k' + ∑ ℓ ∈ Finset.univ.erase F.flowerLeaf,
      ((treeSign F.toTree ℓ.toNode : ℤˣ) : ℤ) • κ.1.1 ℓ.toNode := by
  classical
  have h := sum_rule (fun _ : Fin 1 => (1 : ℤˣ)) κ.1.1 κ.1.2.1 (GNode.root (single F.toTree) 0)
  have hroot : ((nodeSign (fun _ : Fin 1 => (1 : ℤˣ)) (GNode.root (single F.toTree) 0).1 : ℤˣ) : ℤ) = 1 := by
    have := treeSign_root F.toTree
    unfold treeSign at this
    rw [this]; rfl
  rw [hroot, one_smul, κ.1.2.2] at h
  have hall : (GNode.root (single F.toTree) 0).leavesBelow = Finset.univ := by
    ext ℓ
    simp only [GNode.leavesBelow, Finset.mem_filter, Finset.mem_univ, true_and, iff_true]
    exact ⟨Subsingleton.elim _ _, List.nil_prefix⟩
  rw [hall, ← Finset.add_sum_erase _ _ (Finset.mem_univ F.flowerLeaf)] at h
  refine h.trans ?_
  congr 1
  rw [κ.2]
  congr 1
  have hs := treeSign_flowerLeaf F
  unfold treeSign at hs
  exact congrArg (fun u : ℤˣ => (u : ℤ)) hs

/-- **Support of the `M₁` weight**: if `Ψ_j` of the non-flower leaves is nonzero, their largest norm is below
`2^j L`. -/
theorem sup_lt_of_treeCut1_ne_zero {L : ℝ} (hL : 0 < L) {F : FTree} {j : ℕ}
    {κ : GNode (single F.toTree) → (Fin d → ℤ)} (h : treeCut1 L F j κ ≠ 0) :
    (((Finset.univ.erase F.flowerLeaf).sup fun ℓ => ‖latticePoint L (κ ℓ.toNode)‖₊ : NNReal) : ℝ) <
      2 ^ j * L := by
  classical
  have hlt : ∀ ℓ ∈ Finset.univ.erase F.flowerLeaf, ‖latticePoint L (κ ℓ.toNode)‖ < 2 ^ j * L :=
    XChain.ProductCut.lt_of_prodDyadicCut_ne_zero _ hL (fun _ _ => norm_nonneg _) h
  have hpos : (0 : ℝ) < 2 ^ j * L := by positivity
  have hs : ((Finset.univ.erase F.flowerLeaf).sup fun ℓ => ‖latticePoint L (κ ℓ.toNode)‖₊ : NNReal) <
      Real.toNNReal (2 ^ j * L) :=
    (Finset.sup_lt_iff (by simpa using hpos)).2 fun ℓ hℓ => by
      rw [← NNReal.coe_lt_coe, coe_nnnorm, Real.coe_toNNReal _ hpos.le]
      exact hlt ℓ hℓ
  have := NNReal.coe_lt_coe.2 hs
  rwa [Real.coe_toNNReal _ hpos.le] at this

variable (L γ δ : ℝ) (hL : 0 < L) (p : ℕ)

include hL in
/-- **The `M₁` piece vanishes off `|k/L − ζ k'/L| < #leaves · 2^{j₁} L`.** -/
theorem flowerKernelGen_cut1_eq_zero {F : FTree} (aP : (Fin d → ℤ) → ℂ) (pat : FixPat)
    (dagger : Option (Fin 3 → Mom d)) (cut2 : Option ℕ) (j : ℕ) (t s : ℝ) {k k' : Fin d → ℤ}
    (hk : (Fintype.card (GLeaf (single F.toTree)) : ℝ) * (2 ^ j * L) ≤
      ‖latticePoint L k - (F.sign : ℤ) • latticePoint L k'‖) :
    flowerKernelGen L γ δ p F aP pat dagger (some j) cut2 t s k k' = 0 := by
  classical
  unfold flowerKernelGen
  by_cases hF : F = flower
  · simp only [hF, ↓reduceDIte]
  simp only [hF, ↓reduceDIte]
  refine mul_eq_zero_of_right _ ((tsum_congr fun κ => ?_).trans tsum_zero)
  -- zero weight
  suffices hw : treeCut1 L F j κ.1.1 = 0 by
    simp [treeWeight, hw]
  by_contra hw
  have hlt : ∀ ℓ ∈ Finset.univ.erase F.flowerLeaf, ‖latticePoint L (κ.1.1 ℓ.toNode)‖ < 2 ^ j * L :=
    XChain.ProductCut.lt_of_prodDyadicCut_ne_zero _ hL (fun _ _ => norm_nonneg _) hw
  have hmom := congrArg (latticePoint L) (flowerDecoration_root κ)
  rw [latticePoint_add, latticePoint_zsmul, latticePoint_sum] at hmom
  have hdiff : latticePoint L k - (F.sign : ℤ) • latticePoint L k' = ∑ ℓ ∈ Finset.univ.erase F.flowerLeaf,
      latticePoint L (((treeSign F.toTree ℓ.toNode : ℤˣ) : ℤ) • κ.1.1 ℓ.toNode) := by
    rw [hmom]; abel
  have hsum : ‖latticePoint L k - (F.sign : ℤ) • latticePoint L k'‖ ≤
      ((Finset.univ.erase F.flowerLeaf).card : ℝ) * (2 ^ j * L) := by
    rw [hdiff]
    refine (norm_sum_le _ _).trans ?_
    have hb : ∀ ℓ ∈ Finset.univ.erase F.flowerLeaf,
        ‖latticePoint L (((treeSign F.toTree ℓ.toNode : ℤˣ) : ℤ) • κ.1.1 ℓ.toNode)‖ ≤ 2 ^ j * L := fun ℓ hℓ => by
      calc ‖latticePoint L (((treeSign F.toTree ℓ.toNode : ℤˣ) : ℤ) • κ.1.1 ℓ.toNode)‖
          = ‖((treeSign F.toTree ℓ.toNode : ℤˣ) : ℤ) • latticePoint L (κ.1.1 ℓ.toNode)‖ := by
            simp only [latticePoint_zsmul]
        _ = ‖latticePoint L (κ.1.1 ℓ.toNode)‖ := by
            rcases Int.units_eq_one_or (treeSign F.toTree ℓ.toNode) with h | h <;> simp [h]
        _ ≤ 2 ^ j * L := (hlt ℓ hℓ).le
    have := Finset.sum_le_card_nsmul _ _ _ hb
    rwa [nsmul_eq_mul] at this
  have hcard : ((Finset.univ.erase F.flowerLeaf).card : ℝ) + 1 = Fintype.card (GLeaf (single F.toTree)) := by
    have := Finset.card_erase_add_one (Finset.mem_univ F.flowerLeaf)
    rw [Finset.card_univ] at this
    exact_mod_cast this
  have h2 : (0 : ℝ) < 2 ^ j * L := by positivity
  nlinarith

end Support

end WaveTurbulence.Fixedpt
