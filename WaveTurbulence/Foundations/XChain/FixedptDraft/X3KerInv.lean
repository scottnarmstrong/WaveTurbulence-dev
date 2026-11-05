/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.XChain.FixedptDraft.X3DaggerExpansion

/-!
# X3 KerInv: the kernel at a representative (T L2328)

**Statement** (`flowerKernelGen_shift_eq`). Let `F` be a flower tree with flower sign `ζ`, `D ∈ ℤ^d`, and
`k_* = k + D`, `k'_* = k' + ζ D`. Consider the kernel with `†` label `c`, `M₁` cut `j₁` and `M₂` cut `j₂`, for
any pattern, `t`, `s`. Assume:
* `|k/L|, |k_*/L| ≥ R`, with `R` large in terms of `M₁ = 2^{j₁}L`, `M₂ = 2^{j₂}L` and the number of leaves;
* `k_*` represents `k` at radius `M` (`finitelem`), with `M ≥ 2B₀` and `2M ≥ M₂ + 4B₀²`, where
  `B₀ = 2ℓ_max M₁`.
Then `𝒦(t, s, k, k') = 𝒦(t, s, k_*, k'_*)`.

The proof:
* `stemShift D` adds `ζ_a D` at the stem nodes `a` (the ancestors of the flower). It is an equivalence of
  flower decorations `(k, k') ≃ (k + D, k' + ζD)` (`stemShiftEquiv`).
* At a stem branch whose stem child is in slot `0` or `2`, `Ω` changes by `2⟨y, D/L⟩` (`omega_shift_02`), where
  `y` is built from the other two children. At slot `1`, `|Ω| ≳ |k|²` (`omega_shift_1`), so the `M₂` cutoff
  vanishes on both sides.
* The `ε` factors, the `M₁`/`†` weights, the leaf factor and `Ω` off the stem do not change.
-/

@[expose] public section

namespace WaveTurbulence.Fixedpt

open MeasureTheory Set SysAPI FTree

variable {d : ℕ}

/-! ## The stem shift -/

section Shift

variable {F : FTree}

/-- `a` is on the stem: its path is a prefix of the flower path. -/
def OnStem (F : FTree) (a : GNode (single F.toTree)) : Prop := a.1.2 <+: F.flowerPath

instance (F : FTree) (a : GNode (single F.toTree)) : Decidable (OnStem F a) :=
  inferInstanceAs (Decidable (a.1.2 <+: F.flowerPath))

/-- Add `ζ_a D` at the stem nodes. -/
def stemShift (F : FTree) (D : Fin d → ℤ) (κ : GNode (single F.toTree) → (Fin d → ℤ)) :
    GNode (single F.toTree) → (Fin d → ℤ) :=
  fun a => if OnStem F a then κ a + ((treeSign F.toTree a : ℤˣ) : ℤ) • D else κ a

theorem onStem_of_child {b : GBranch (single F.toTree)} {i : Fin 3} (h : OnStem F (b.child i)) :
    OnStem F b.toNode :=
  (List.prefix_append _ _).trans h

/-- A stem branch has a stem child. -/
theorem exists_stem_child {b : GBranch (single F.toTree)} (h : OnStem F b.toNode) :
    ∃ i, OnStem F (b.child i) := by
  obtain ⟨u, hu⟩ := h
  rcases u with _ | ⟨i, u⟩
  · exfalso
    simp only [List.append_nil] at hu
    have hb : b.1.2 ∈ F.toTree.branching := b.2
    exact TTree.not_mem_branching_of_mem_leaves _ (hu ▸ F.flowerPath_mem_leaves) hb
  · have hu' : b.1.2 ++ i :: u = F.flowerPath := hu
    refine ⟨i, ⟨u, ?_⟩⟩
    show b.1.2 ++ [i] ++ u = F.flowerPath
    rw [List.append_assoc, List.singleton_append]
    exact hu'

theorem stem_child_unique {b : GBranch (single F.toTree)} {i j : Fin 3} (hi : OnStem F (b.child i))
    (hj : OnStem F (b.child j)) : i = j := by
  have h := List.prefix_of_prefix_length_le hi hj (by simp [GBranch.child])
  have h2 : b.1.2 ++ [i] = b.1.2 ++ [j] := h.eq_of_length (by simp [GBranch.child])
  simpa using h2

theorem stemShift_branch (D : Fin d → ℤ) {κ : GNode (single F.toTree) → (Fin d → ℤ)}
    (hκ : IsBranchConsistent κ) : IsBranchConsistent (stemShift F D κ) := by
  intro b
  obtain ⟨h0, h1, h2⟩ := nodeSign_child (fun _ : Fin 1 => (1 : ℤˣ)) b
  have hκb := hκ b
  by_cases hb : OnStem F b.toNode
  · obtain ⟨r, hr⟩ := exists_stem_child hb
    have hne : ∀ i, i ≠ r → ¬ OnStem F (b.child i) := fun i hi h => hi (stem_child_unique h hr)
    unfold stemShift treeSign
    have hbn : (b.toNode).1 = b.1 := rfl
    fin_cases r
    · have hr0 : OnStem F (b.child 0) := hr
      simp only [hb, hr0, hne 1 (by decide), hne 2 (by decide), ↓reduceIte]
      rw [hκb, h0]; simp only [hbn]; abel
    · have hr0 : OnStem F (b.child 1) := hr
      simp only [hb, hr0, hne 0 (by decide), hne 2 (by decide), ↓reduceIte]
      rw [hκb, h1]; simp only [hbn, Units.val_neg, neg_smul]; abel
    · have hr0 : OnStem F (b.child 2) := hr
      simp only [hb, hr0, hne 0 (by decide), hne 1 (by decide), ↓reduceIte]
      rw [hκb, h2]; simp only [hbn]; abel
  · have hc : ∀ i, ¬ OnStem F (b.child i) := fun i h => hb (onStem_of_child h)
    unfold stemShift
    simp only [hb, hc, ↓reduceIte]
    exact hκb

theorem onStem_root : OnStem F (GNode.root (single F.toTree) 0) := List.nil_prefix

theorem onStem_flowerLeaf : OnStem F F.flowerLeaf.toNode := List.prefix_refl _

theorem stemShift_stemShift (D D' : Fin d → ℤ) (κ : GNode (single F.toTree) → (Fin d → ℤ)) :
    stemShift F D' (stemShift F D κ) = stemShift F (D + D') κ := by
  funext a
  unfold stemShift
  split_ifs <;> simp [smul_add, add_assoc]

theorem stemShift_zero (κ : GNode (single F.toTree) → (Fin d → ℤ)) : stemShift F 0 κ = κ := by
  funext a
  unfold stemShift
  split_ifs <;> simp

theorem stemShift_root (D : Fin d → ℤ) (κ : GNode (single F.toTree) → (Fin d → ℤ)) :
    stemShift F D κ (GNode.root (single F.toTree) 0) = κ (GNode.root (single F.toTree) 0) + D := by
  unfold stemShift
  simp [onStem_root, treeSign_root]

theorem stemShift_flowerLeaf (D : Fin d → ℤ) (κ : GNode (single F.toTree) → (Fin d → ℤ)) :
    stemShift F D κ F.flowerLeaf.toNode = κ F.flowerLeaf.toNode + (F.sign : ℤ) • D := by
  unfold stemShift
  simp [onStem_flowerLeaf, treeSign_flowerLeaf]

/-- **The stem shift as an equivalence of flower decorations.** -/
def stemShiftEquiv (F : FTree) (D : Fin d → ℤ) (k k' : Fin d → ℤ) :
    FlowerDecoration F d k k' ≃ FlowerDecoration F d (k + D) (k' + (F.sign : ℤ) • D) where
  toFun κ := ⟨⟨stemShift F D κ.1.1, stemShift_branch D κ.1.2.1, by rw [stemShift_root, κ.1.2.2]⟩, by
      show stemShift F D κ.1.1 F.flowerLeaf.toNode = _
      rw [stemShift_flowerLeaf, κ.2]⟩
  invFun κ := ⟨⟨stemShift F (-D) κ.1.1, stemShift_branch (-D) κ.1.2.1, by
      rw [stemShift_root, κ.1.2.2]; abel⟩, by
      show stemShift F (-D) κ.1.1 F.flowerLeaf.toNode = _
      rw [stemShift_flowerLeaf, κ.2, smul_neg]; abel⟩
  left_inv κ := by
    apply Subtype.ext; apply Subtype.ext
    show stemShift F (-D) (stemShift F D κ.1.1) = κ.1.1
    rw [stemShift_stemShift, add_neg_cancel, stemShift_zero]
  right_inv κ := by
    apply Subtype.ext; apply Subtype.ext
    show stemShift F D (stemShift F (-D) κ.1.1) = κ.1.1
    rw [stemShift_stemShift, neg_add_cancel, stemShift_zero]

end Shift

/-! ## `Ω` under the shift -/

section Omega

theorem resFactor_shift0 (x0 x1 x2 v : Mom d) :
    resFactor (x0 + v) x1 x2 (x0 - x1 + x2 + v) = resFactor x0 x1 x2 (x0 - x1 + x2) + 2 * inner ℝ (x1 - x2) v := by
  unfold resFactor
  simp only [norm_add_sq_real, inner_sub_left, inner_add_left]
  ring

theorem resFactor_shift2 (x0 x1 x2 v : Mom d) :
    resFactor x0 x1 (x2 + v) (x0 - x1 + x2 + v) = resFactor x0 x1 x2 (x0 - x1 + x2) + 2 * inner ℝ (x1 - x0) v := by
  unfold resFactor
  simp only [norm_add_sq_real, inner_sub_left, inner_add_left]
  ring

theorem resFactor_shift1 (x0 x1 x2 v : Mom d) :
    resFactor x0 (x1 - v) x2 (x0 - x1 + x2 + v) = resFactor x0 x1 x2 (x0 - x1 + x2) +
      2 * inner ℝ (x1 - x0) v + 2 * inner ℝ (x1 - x2) v - 2 * ‖v‖ ^ 2 := by
  unfold resFactor
  simp only [norm_add_sq_real, norm_sub_sq_real, inner_sub_left, inner_add_left]
  ring

variable (L : ℝ) {F : FTree}

theorem latticePoint_sub (a b : Fin d → ℤ) : latticePoint L (a - b) = latticePoint L a - latticePoint L b := by
  ext j; simp [latticePoint, sub_div]

/-- `Ω_b` after the shift, for a stem branch `b` with stem child `r`: the three cases. -/
theorem omegaT_stemShift (D : Fin d → ℤ) {κ : GNode (single F.toTree) → (Fin d → ℤ)} (hκ : IsBranchConsistent κ)
    {b : GBranch (single F.toTree)} (hb : OnStem F b.toNode) {r : Fin 3} (hr : OnStem F (b.child r)) :
    let x := fun i => latticePoint L (κ (b.child i))
    let v := ((treeSign F.toTree b.toNode : ℤˣ) : ℤ) • latticePoint L D
    omegaT L F.toTree (stemShift F D κ) b = omegaT L F.toTree κ b +
      (if r = 0 then 2 * inner ℝ (x 1 - x 2) v else if r = 2 then 2 * inner ℝ (x 1 - x 0) v else
        2 * inner ℝ (x 1 - x 0) v + 2 * inner ℝ (x 1 - x 2) v - 2 * ‖v‖ ^ 2) := by
  intro x v
  have hne : ∀ i, i ≠ r → ¬ OnStem F (b.child i) := fun i hi h => hi (stem_child_unique h hr)
  obtain ⟨h0, h1, h2⟩ := nodeSign_child (fun _ : Fin 1 => (1 : ℤˣ)) b
  have hnode : latticePoint L (κ b.toNode) = x 0 - x 1 + x 2 := by
    rw [hκ b, latticePoint_add, latticePoint_sub]
  unfold omegaT stemShift treeSign
  have hbn : (b.toNode).1 = b.1 := rfl
  fin_cases r
  · have hr0 : OnStem F (b.child 0) := hr
    simp only [hb, hr0, hne 1 (by decide), hne 2 (by decide), ↓reduceIte, Fin.isValue]
    rw [latticePoint_add, latticePoint_add, latticePoint_zsmul, latticePoint_zsmul, hnode, h0]
    simp only [hbn]
    exact resFactor_shift0 _ _ _ _
  · have hr0 : OnStem F (b.child 1) := hr
    simp only [hb, hr0, hne 0 (by decide), hne 2 (by decide), ↓reduceIte, Fin.isValue]
    rw [latticePoint_add, latticePoint_add, latticePoint_zsmul, latticePoint_zsmul, hnode, h1]
    simp only [hbn, Units.val_neg, neg_smul, ← sub_eq_add_neg]
    rw [ite_eq_right_of_eq_false _ _ (eq_false (by decide)), ite_eq_right_of_eq_false _ _ (eq_false (by decide)),
      resFactor_shift1]
    simp only [x, v, treeSign, hbn]
    ring
  · have hr0 : OnStem F (b.child 2) := hr
    simp only [hb, hr0, hne 0 (by decide), hne 1 (by decide), ↓reduceIte, Fin.isValue]
    rw [latticePoint_add, latticePoint_add, latticePoint_zsmul, latticePoint_zsmul, hnode, h2]
    simp only [hbn]
    exact resFactor_shift2 _ _ _ _

theorem omegaT_stemShift_off (D : Fin d → ℤ) (κ : GNode (single F.toTree) → (Fin d → ℤ))
    {b : GBranch (single F.toTree)} (hb : ¬ OnStem F b.toNode) :
    omegaT L F.toTree (stemShift F D κ) b = omegaT L F.toTree κ b := by
  have hc : ∀ i, ¬ OnStem F (b.child i) := fun i h => hb (onStem_of_child h)
  unfold omegaT stemShift
  simp only [hb, hc, ↓reduceIte]

end Omega

/-! ## Bounds on the base decoration -/

section Bounds

variable (L : ℝ) {F : FTree}

theorem eq_flowerLeaf_of_onStem (ℓ : GLeaf (single F.toTree)) (h : OnStem F ℓ.toNode) : ℓ = F.flowerLeaf := by
  by_contra hne
  have hpath : ℓ.1.2 ≠ F.flowerPath := fun e => hne (GLeaf.ext_path e)
  obtain ⟨u, hu⟩ := h
  rcases u with _ | ⟨i, u⟩
  · rw [List.append_nil] at hu
    exact hpath hu
  · have hpre : ℓ.1.2 ++ [i] <+: F.flowerPath := ⟨u, by rw [← hu]; simp; rfl⟩
    have hnode : ℓ.1.2 ++ [i] ∈ F.toTree.nodes :=
      TTree.mem_nodes_of_prefix _ (TTree.leaves_subset_nodes _ F.flowerPath_mem_leaves) hpre
    have hbr := TTree.branching_of_append_mem _ hnode
    exact TTree.not_mem_branching_of_mem_leaves _ ℓ.2 hbr

theorem norm_units_zsmul {E : Type*} [SeminormedAddCommGroup E] (u : ℤˣ) (v : E) : ‖((u : ℤ) • v)‖ = ‖v‖ := by
  rcases Int.units_eq_one_or u with h | h <;> simp [h]

theorem latticePoint_neg (a : Fin d → ℤ) : latticePoint L (-a) = -latticePoint L a := by
  ext j; simp [latticePoint, neg_div]

theorem stemShift_leaf (D : Fin d → ℤ) (κ : GNode (single F.toTree) → (Fin d → ℤ)) {ℓ : GLeaf (single F.toTree)}
    (hℓ : ℓ ≠ F.flowerLeaf) : stemShift F D κ ℓ.toNode = κ ℓ.toNode := by
  unfold stemShift
  rw [ite_eq_right_of_eq_false _ _ (eq_false fun h => hℓ (eq_flowerLeaf_of_onStem ℓ h))]

/-- A node is bounded by the sum of its leaves. -/
theorem norm_node_le {δ : GNode (single F.toTree) → (Fin d → ℤ)} (hδ : IsBranchConsistent δ)
    (a : GNode (single F.toTree)) :
    ‖latticePoint L (δ a)‖ ≤ ∑ ℓ : GLeaf (single F.toTree), ‖latticePoint L (δ ℓ.toNode)‖ := by
  classical
  have h := sum_rule (fun _ : Fin 1 => (1 : ℤˣ)) δ hδ a
  have hl := congrArg (latticePoint L) h
  rw [latticePoint_zsmul, latticePoint_sum] at hl
  have hunit : ∀ (u : ℤˣ) (v : Mom d), ‖((u : ℤ) • v)‖ = ‖v‖ := fun u v => by
    rcases Int.units_eq_one_or u with h | h <;> simp [h]
  calc ‖latticePoint L (δ a)‖ = ‖((nodeSign (fun _ : Fin 1 => (1 : ℤˣ)) a.1 : ℤˣ) : ℤ) • latticePoint L (δ a)‖ :=
        (hunit _ _).symm
    _ = ‖∑ ℓ ∈ a.leavesBelow, latticePoint L
          (((nodeSign (fun _ : Fin 1 => (1 : ℤˣ)) ℓ.1 : ℤˣ) : ℤ) • δ ℓ.toNode)‖ := by rw [hl]
    _ ≤ ∑ ℓ ∈ a.leavesBelow, ‖latticePoint L (δ ℓ.toNode)‖ := by
        refine (norm_sum_le _ _).trans (le_of_eq (Finset.sum_congr rfl fun ℓ _ => ?_))
        rw [latticePoint_zsmul, hunit]
    _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) fun _ _ _ => norm_nonneg _

/-- **The base decoration is small**: `|κ⁰_a/L| ≤ B₀ = 2 ℓ_max M₁`. -/
theorem norm_base_le (hL : 0 < L) {j : ℕ} {k k' : Fin d → ℤ} (κ : FlowerDecoration F d k k')
    (hcut : treeCut1 L F j κ.1.1 ≠ 0)
    (hsupp : ‖latticePoint L k - (F.sign : ℤ) • latticePoint L k'‖ <
      (Fintype.card (GLeaf (single F.toTree)) : ℝ) * (2 ^ j * L))
    (a : GNode (single F.toTree)) :
    ‖latticePoint L (stemShift F (-k) κ.1.1 a)‖ ≤
      2 * (Fintype.card (GLeaf (single F.toTree)) : ℝ) * (2 ^ j * L) := by
  classical
  set n := (Fintype.card (GLeaf (single F.toTree)) : ℝ)
  set x : NNReal := (Finset.univ.erase F.flowerLeaf).sup fun ℓ => ‖latticePoint L (κ.1.1 ℓ.toNode)‖₊
  have hx : (x : ℝ) < 2 ^ j * L := lt_of_dyadicCut_ne_zero hL (NNReal.coe_nonneg _) hcut
  refine (norm_node_le L (stemShift_branch (-k) κ.1.2.1) a).trans ?_
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ F.flowerLeaf)]
  have hf : ‖latticePoint L (stemShift F (-k) κ.1.1 F.flowerLeaf.toNode)‖ < n * (2 ^ j * L) := by
    rw [stemShift_flowerLeaf, κ.2, latticePoint_add, latticePoint_zsmul, latticePoint_neg]
    have : latticePoint L k' + (F.sign : ℤ) • -latticePoint L k =
        -((F.sign : ℤ) • (latticePoint L k - (F.sign : ℤ) • latticePoint L k')) := by
      rcases Int.units_eq_one_or F.sign with h | h <;> simp [h]; abel
    rw [this, norm_neg, norm_units_zsmul]
    exact hsupp
  have hrest : ∑ ℓ ∈ Finset.univ.erase F.flowerLeaf, ‖latticePoint L (stemShift F (-k) κ.1.1 ℓ.toNode)‖ ≤
      n * (2 ^ j * L) := by
    have hb : ∀ ℓ ∈ Finset.univ.erase F.flowerLeaf,
        ‖latticePoint L (stemShift F (-k) κ.1.1 ℓ.toNode)‖ ≤ 2 ^ j * L := fun ℓ hℓ => by
      rw [stemShift_leaf (-k) κ.1.1 (Finset.ne_of_mem_erase hℓ)]
      have hle := Finset.le_sup (f := fun ℓ => ‖latticePoint L (κ.1.1 ℓ.toNode)‖₊) hℓ
      exact (show ‖latticePoint L (κ.1.1 ℓ.toNode)‖ ≤ x by exact_mod_cast hle).trans hx.le
    refine (Finset.sum_le_card_nsmul _ _ _ hb).trans ?_
    rw [nsmul_eq_mul]
    have hc : ((Finset.univ.erase F.flowerLeaf).card : ℝ) ≤ n := by
      simp only [n]
      exact_mod_cast Finset.card_le_univ (Finset.univ.erase F.flowerLeaf)
    exact mul_le_mul_of_nonneg_right hc (by positivity)
  linarith

/-- **Stem momenta are large**: `|κ_a/L| ≥ |k/L| − B₀` at the stem nodes, `|κ_a/L| ≤ B₀` off the stem. -/
theorem norm_stem_ge {k : Fin d → ℤ} (κ₀ : GNode (single F.toTree) → (Fin d → ℤ)) {B₀ : ℝ}
    (hB : ∀ a, ‖latticePoint L (κ₀ a)‖ ≤ B₀) {a : GNode (single F.toTree)} (ha : OnStem F a) :
    ‖latticePoint L k‖ - B₀ ≤ ‖latticePoint L (stemShift F k κ₀ a)‖ := by
  unfold stemShift
  rw [ite_eq_left_of_eq_true _ _ (eq_true ha), latticePoint_add, latticePoint_zsmul]
  have hu : ‖((treeSign F.toTree a : ℤˣ) : ℤ) • latticePoint L k‖ = ‖latticePoint L k‖ := by
    rcases Int.units_eq_one_or (treeSign F.toTree a) with h | h <;> simp [h]
  have := norm_sub_norm_le (((treeSign F.toTree a : ℤˣ) : ℤ) • latticePoint L k)
    (-(latticePoint L (κ₀ a)))
  rw [hu, norm_neg, sub_neg_eq_add, add_comm] at this
  linarith [hB a]

end Bounds

/-! ## The `Ω` dichotomy -/

section Dichotomy

variable (L : ℝ) {F : FTree}

theorem abs_resFactor_le {x0 x1 x2 xb : Mom d} {B : ℝ} (h0 : ‖x0‖ ≤ B) (h1 : ‖x1‖ ≤ B) (h2 : ‖x2‖ ≤ B)
    (hb : ‖xb‖ ≤ B) : |resFactor x0 x1 x2 xb| ≤ 4 * B ^ 2 := by
  unfold resFactor
  have hB : 0 ≤ B := (norm_nonneg _).trans h0
  have e0 : ‖x0‖ ^ 2 ≤ B ^ 2 := pow_le_pow_left₀ (norm_nonneg _) h0 2
  have e1 : ‖x1‖ ^ 2 ≤ B ^ 2 := pow_le_pow_left₀ (norm_nonneg _) h1 2
  have e2 : ‖x2‖ ^ 2 ≤ B ^ 2 := pow_le_pow_left₀ (norm_nonneg _) h2 2
  have eb : ‖xb‖ ^ 2 ≤ B ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hb 2
  rw [abs_le]
  constructor <;> nlinarith [sq_nonneg ‖x0‖, sq_nonneg ‖x1‖, sq_nonneg ‖x2‖, sq_nonneg ‖xb‖]

/-- `Ω_b` at `stemShift K κ₀` for a small base `κ₀` and a stem branch `b`: unchanged by `K` up to a linear form
in `K/L` (slots `0, 2`), or larger than `M₂` (slot `1`, `|K/L| ≥ R`). -/
theorem omega_dichotomy {κ₀ : GNode (single F.toTree) → (Fin d → ℤ)} (hκ₀ : IsBranchConsistent κ₀) {B₀ M M₂ : ℝ}
    (hB : ∀ a, ‖latticePoint L (κ₀ a)‖ ≤ B₀) (hM1 : 2 * B₀ ≤ M) (hM2 : M₂ + 4 * B₀ ^ 2 ≤ 2 * M) (hM₂ : 0 ≤ M₂)
    {K K' : Fin d → ℤ} (hK : 8 * B₀ + 4 * B₀ ^ 2 + M₂ + 1 ≤ ‖latticePoint L K‖)
    (hK' : 8 * B₀ + 4 * B₀ ^ 2 + M₂ + 1 ≤ ‖latticePoint L K'‖)
    (hrep : ∀ z : Fin d → ℤ, ‖latticePoint L z‖ ≤ M →
      (|ipL L K z| ≤ M ↔ |ipL L K' z| ≤ M) ∧ (|ipL L K z| ≤ M → ipL L K z = ipL L K' z))
    {b : GBranch (single F.toTree)} (hb : OnStem F b.toNode) :
    omegaT L F.toTree (stemShift F K' κ₀) b = omegaT L F.toTree (stemShift F K κ₀) b ∨
      (M₂ ≤ |omegaT L F.toTree (stemShift F K κ₀) b| ∧ M₂ ≤ |omegaT L F.toTree (stemShift F K' κ₀) b|) := by
  obtain ⟨r, hr⟩ := exists_stem_child hb
  have hB0 : 0 ≤ B₀ := (norm_nonneg _).trans (hB b.toNode)
  set x := fun i => latticePoint L (κ₀ (b.child i)) with hx
  have hxb : ∀ i, ‖x i‖ ≤ B₀ := fun i => hB _
  have hΩ0 : |omegaT L F.toTree κ₀ b| ≤ 4 * B₀ ^ 2 := abs_resFactor_le (hB _) (hB _) (hB _) (hB _)
  set σ : ℤ := ((treeSign F.toTree b.toNode : ℤˣ) : ℤ)
  have hσ : |(σ : ℝ)| = 1 := by
    rcases Int.units_eq_one_or (treeSign F.toTree b.toNode) with h | h <;> simp [σ, h]
  have hform := fun (KK : Fin d → ℤ) => omegaT_stemShift L KK hκ₀ hb hr
  -- `⟪lp z, σ • lp KK⟫ = σ · ipL KK z`
  have hip : ∀ (z KK : Fin d → ℤ), inner ℝ (latticePoint L z) ((σ : ℤ) • latticePoint L KK) =
      (σ : ℝ) * ipL L KK z := fun z KK => by
    rw [← Int.cast_smul_eq_zsmul ℝ, real_inner_smul_right, ipL, real_inner_comm]
  -- the linear cases
  have hlin : ∀ z : Fin d → ℤ, ‖latticePoint L z‖ ≤ 2 * B₀ →
      (∀ KK, omegaT L F.toTree (stemShift F KK κ₀) b = omegaT L F.toTree κ₀ b + 2 * ((σ : ℝ) * ipL L KK z)) →
      omegaT L F.toTree (stemShift F K' κ₀) b = omegaT L F.toTree (stemShift F K κ₀) b ∨
      (M₂ ≤ |omegaT L F.toTree (stemShift F K κ₀) b| ∧ M₂ ≤ |omegaT L F.toTree (stemShift F K' κ₀) b|) := by
    intro z hz hΩ
    obtain ⟨hiff, heq⟩ := hrep z (hz.trans hM1)
    by_cases hsmall : |ipL L K z| ≤ M
    · left
      rw [hΩ K, hΩ K', heq hsmall]
    · right
      have hbig' : M < |ipL L K' z| := lt_of_not_ge fun h => hsmall (hiff.2 h)
      have hbig : M < |ipL L K z| := lt_of_not_ge hsmall
      have key : ∀ KK, M < |ipL L KK z| → M₂ ≤ |omegaT L F.toTree (stemShift F KK κ₀) b| := fun KK hKK => by
        rw [hΩ KK]
        have h1 : |2 * ((σ : ℝ) * ipL L KK z)| = 2 * |ipL L KK z| := by
          rw [abs_mul, abs_mul, hσ]; norm_num
        have := abs_sub_abs_le_abs_sub (2 * ((σ : ℝ) * ipL L KK z)) (-omegaT L F.toTree κ₀ b)
        rw [abs_neg, sub_neg_eq_add, h1, add_comm] at this
        linarith
      exact ⟨key K hbig, key K' hbig'⟩
  fin_cases r
  · -- slot 0
    refine hlin (κ₀ (b.child 1) - κ₀ (b.child 2)) ?_ fun KK => ?_
    · rw [latticePoint_sub]
      exact (norm_sub_le _ _).trans (by linarith [hxb 1, hxb 2])
    · have h := hform KK
      dsimp only at h
      rw [ite_eq_left_of_eq_true _ _ (eq_true (by decide))] at h
      rw [h, ← hip, latticePoint_sub]
  · -- slot 1: both large
    right
    have key : ∀ KK : Fin d → ℤ, 8 * B₀ + 4 * B₀ ^ 2 + M₂ + 1 ≤ ‖latticePoint L KK‖ →
        M₂ ≤ |omegaT L F.toTree (stemShift F KK κ₀) b| := fun KK hKK => by
      have h := hform KK
      dsimp only at h
      rw [ite_eq_right_of_eq_false _ _ (eq_false (by decide)), ite_eq_right_of_eq_false _ _ (eq_false (by decide))]
        at h
      set v := (σ : ℤ) • latticePoint L KK
      have hv : ‖v‖ = ‖latticePoint L KK‖ := norm_units_zsmul _ _
      set X := ‖latticePoint L KK‖
      have hi1 : |inner ℝ (x 1 - x 0) v| ≤ 2 * B₀ * X := by
        refine (abs_real_inner_le_norm _ _).trans ?_
        rw [hv]
        gcongr
        exact (norm_sub_le _ _).trans (by linarith [hxb 1, hxb 0])
      have hi2 : |inner ℝ (x 1 - x 2) v| ≤ 2 * B₀ * X := by
        refine (abs_real_inner_le_norm _ _).trans ?_
        rw [hv]
        gcongr
        exact (norm_sub_le _ _).trans (by linarith [hxb 1, hxb 2])
      rw [h, hv]
      have hX1 : 1 ≤ X := by nlinarith [sq_nonneg B₀]
      have hX8 : 8 * B₀ ≤ X := by nlinarith [sq_nonneg B₀]
      have hX0 : (0 : ℝ) ≤ X := by linarith
      rw [abs_le] at hi1 hi2 hΩ0
      rw [le_abs]
      right
      nlinarith [mul_le_mul_of_nonneg_right hX8 hX0, mul_le_mul_of_nonneg_right hX1 hX0]
    exact ⟨key K hK, key K' hK'⟩
  · -- slot 2
    refine hlin (κ₀ (b.child 1) - κ₀ (b.child 0)) ?_ fun KK => ?_
    · rw [latticePoint_sub]
      exact (norm_sub_le _ _).trans (by linarith [hxb 1, hxb 0])
    · have h := hform KK
      dsimp only at h
      rw [ite_eq_right_of_eq_false _ _ (eq_false (by decide)), ite_eq_left_of_eq_true _ _ (eq_true (by decide))] at h
      rw [h, ← hip, latticePoint_sub]

end Dichotomy

/-! ## Invariance of the summands -/

section Invariance

variable (L γ δ : ℝ) {F : FTree} (hF : F ≠ flower)

theorem treeCut1_stemShift (j : ℕ) (D : Fin d → ℤ) (κ : GNode (single F.toTree) → (Fin d → ℤ)) :
    treeCut1 L F j (stemShift F D κ) = treeCut1 L F j κ := by
  unfold treeCut1
  congr 2
  exact Finset.sup_congr rfl fun ℓ hℓ => by rw [stemShift_leaf D κ (Finset.ne_of_mem_erase hℓ)]

theorem restP_stemShift (aP : (Fin d → ℤ) → ℂ) (D : Fin d → ℤ) (κ : GNode (single F.toTree) → (Fin d → ℤ)) :
    restP F aP (stemShift F D κ) = restP F aP κ := by
  unfold restP
  exact Finset.prod_congr rfl fun ℓ hℓ => by rw [stemShift_leaf D κ (Finset.ne_of_mem_erase hℓ)]

include hF in
theorem not_onStem_flowerParent_child {i : Fin 3}
    (hi : ((F.flowerParent hF).child i).1.2 ≠ F.flowerPath) : ¬ OnStem F ((F.flowerParent hF).child i) := by
  intro h
  refine hi (h.eq_of_length ?_)
  rw [flowerParent_child_path]
  have hpos := List.length_pos_of_ne_nil (flowerPath_ne_nil hF)
  simp only [List.length_append, List.length_singleton, List.length_dropLast]
  omega

theorem treeSib_stemShift (c : Fin 3 → Mom d) (D : Fin d → ℤ) (κ : GNode (single F.toTree) → (Fin d → ℤ)) :
    treeSib L F hF c (stemShift F D κ) = treeSib L F hF c κ := by
  unfold treeSib
  refine Finset.prod_congr rfl fun i _ => ?_
  by_cases hi : ((F.flowerParent hF).child i).1.2 = F.flowerPath
  · simp [hi]
  · have hns := not_onStem_flowerParent_child hF hi
    simp only [hi, ↓reduceIte, stemShift, hns]

theorem TIpat_congr (p : ℕ) (off : Finset (GBranch (single F.toTree))) {κ κ' : GNode (single F.toTree) → (Fin d → ℤ)}
    (h : ∀ c ∉ off, omegaT L F.toTree κ c = omegaT L F.toTree κ' c) (pat : FixPat) (t s : ℝ) :
    TIpat L γ δ hF p off κ pat t s = TIpat L γ δ hF p off κ' pat t s := by
  unfold TIpat
  congr 1
  funext τ
  congr 1
  funext x
  unfold phaseOffT
  refine Finset.prod_congr rfl fun c _ => ?_
  split_ifs with hc
  · rfl
  · rw [h c hc]

theorem epsCoef_of_ne01 {n0 n1 n2 : Fin d → ℤ} (h : n0 ≠ n1) :
    epsCoef n0 n1 n2 = if n1 ≠ n2 then 1 else 0 := by
  unfold epsCoef
  by_cases h12 : n1 = n2
  · subst h12; simp [h, Ne.symm h]
  · simp [h12, Ne.symm h]

theorem epsCoef_of_ne21 {n0 n1 n2 : Fin d → ℤ} (h : n2 ≠ n1) :
    epsCoef n0 n1 n2 = if n1 ≠ n0 then 1 else 0 := by
  unfold epsCoef
  by_cases h10 : n1 = n0
  · subst h10; simp [Ne.symm h]
  · simp [h10, Ne.symm h]

theorem epsCoef_of_ne1 {n0 n1 n2 : Fin d → ℤ} (h0 : n1 ≠ n0) (h2 : n1 ≠ n2) : epsCoef n0 n1 n2 = 1 := by
  unfold epsCoef
  simp [h0, h2]

/-- Two vectors with lattice norms on opposite sides of `B₀` differ. -/
theorem ne_of_norm_lt {B₀ : ℝ} {a b : Fin d → ℤ} (ha : ‖latticePoint L a‖ ≤ B₀) (hb : B₀ < ‖latticePoint L b‖) :
    a ≠ b := by
  rintro rfl
  linarith

/-- **`ε` is unchanged** when the stem momenta are large and the others small. -/
theorem epsProd_stemShift {κ₀ : GNode (single F.toTree) → (Fin d → ℤ)} {B₀ : ℝ}
    (hB : ∀ a, ‖latticePoint L (κ₀ a)‖ ≤ B₀) {K K' : Fin d → ℤ} (hK : 2 * B₀ < ‖latticePoint L K‖)
    (hK' : 2 * B₀ < ‖latticePoint L K'‖) :
    epsProd F.toTree (stemShift F K' κ₀) = epsProd F.toTree (stemShift F K κ₀) := by
  unfold epsProd
  refine Finset.prod_congr rfl fun b _ => ?_
  congr 1
  by_cases hb : OnStem F b.toNode
  · obtain ⟨r, hr⟩ := exists_stem_child hb
    have hne : ∀ i, i ≠ r → ¬ OnStem F (b.child i) := fun i hi h => hi (stem_child_unique h hr)
    have hoff : ∀ (KK : Fin d → ℤ) i, i ≠ r → stemShift F KK κ₀ (b.child i) = κ₀ (b.child i) :=
      fun KK i hi => by unfold stemShift; rw [ite_eq_right_of_eq_false _ _ (eq_false (hne i hi))]
    have hbig : ∀ KK : Fin d → ℤ, 2 * B₀ < ‖latticePoint L KK‖ → B₀ < ‖latticePoint L (stemShift F KK κ₀ (b.child r))‖ :=
      fun KK hKK => by have := norm_stem_ge L (k := KK) κ₀ hB hr; linarith
    have hsep : ∀ (KK : Fin d → ℤ), 2 * B₀ < ‖latticePoint L KK‖ → ∀ i, i ≠ r →
        stemShift F KK κ₀ (b.child i) ≠ stemShift F KK κ₀ (b.child r) := fun KK hKK i hi => by
      rw [hoff KK i hi]
      exact ne_of_norm_lt L (hB _) (hbig KK hKK)
    obtain rfl | rfl | rfl : r = 0 ∨ r = 1 ∨ r = 2 := by fin_cases r <;> simp
    · have s1 := hsep K hK 1 (by decide); have s1' := hsep K' hK' 1 (by decide)
      rw [epsCoef_of_ne01 (Ne.symm s1), epsCoef_of_ne01 (Ne.symm s1'), hoff K 1 (by decide), hoff K 2 (by decide),
        hoff K' 1 (by decide), hoff K' 2 (by decide)]
    · have s0 := hsep K hK 0 (by decide); have s0' := hsep K' hK' 0 (by decide)
      have s2 := hsep K hK 2 (by decide); have s2' := hsep K' hK' 2 (by decide)
      rw [epsCoef_of_ne1 (Ne.symm s0) (Ne.symm s2), epsCoef_of_ne1 (Ne.symm s0') (Ne.symm s2')]
    · have s1 := hsep K hK 1 (by decide); have s1' := hsep K' hK' 1 (by decide)
      rw [epsCoef_of_ne21 (Ne.symm s1), epsCoef_of_ne21 (Ne.symm s1'), hoff K 0 (by decide), hoff K 1 (by decide),
        hoff K' 0 (by decide), hoff K' 1 (by decide)]
  · have hc : ∀ i, ¬ OnStem F (b.child i) := fun i h => hb (onStem_of_child h)
    unfold stemShift
    simp only [hc, ↓reduceIte]

end Invariance

/-! ## The kernel at a representative -/

section Kernel

variable (L γ δ : ℝ) (p : ℕ)

/-- `B₀ = 2 ℓ_max M₁`. -/
noncomputable def kerB0 (L : ℝ) (F : FTree) (j₁ : ℕ) : ℝ :=
  2 * (Fintype.card (GLeaf (single F.toTree)) : ℝ) * (2 ^ j₁ * L)

/-- `R = 8B₀ + 4B₀² + M₂ + 1`. -/
noncomputable def kerR (L : ℝ) (F : FTree) (j₁ j₂ : ℕ) : ℝ :=
  8 * kerB0 L F j₁ + 4 * kerB0 L F j₁ ^ 2 + 2 ^ j₂ * L + 1

theorem treeCut2_eq_zero_of {F : FTree} (hF : F ≠ flower) (hL : 0 < L) (j : ℕ)
    (κ : GNode (single F.toTree) → (Fin d → ℤ)) {b : GBranch (single F.toTree)} (hb : OnStem F b.toNode)
    (hbf : b ≠ F.flowerParent hF) (hΩ : 2 ^ j * L ≤ |omegaT L F.toTree κ b|) : treeCut2 L F hF j κ = 0 := by
  classical
  unfold treeCut2
  by_contra h
  have hlt := lt_of_dyadicCut_ne_zero hL (NNReal.coe_nonneg _) h
  have hle := Finset.le_sup (s := Finset.univ.filter fun b => OnStemT F b ∧ b ≠ F.flowerParent hF)
    (f := fun b => ‖omegaT L F.toTree κ b‖₊) (Finset.mem_filter.2 ⟨Finset.mem_univ b, hb, hbf⟩)
  have h2 : ‖omegaT L F.toTree κ b‖ ≤ (((Finset.univ.filter fun b => OnStemT F b ∧ b ≠ F.flowerParent hF).sup
      fun b => ‖omegaT L F.toTree κ b‖₊ : NNReal) : ℝ) := by exact_mod_cast hle
  rw [Real.norm_eq_abs] at h2
  linarith

/-- **KerInv: the kernel at `k_* = k + D`, `k'_* = k' + ζD`.** -/
theorem flowerKernelGen_shift_eq (hL : 0 < L) {F : FTree} (aP : (Fin d → ℤ) → ℂ) (pat : FixPat)
    (c : Fin 3 → Mom d) (j₁ j₂ : ℕ) (t s : ℝ) {k k' D : Fin d → ℤ} {M : ℝ}
    (hk : kerR L F j₁ j₂ ≤ ‖latticePoint L k‖) (hkD : kerR L F j₁ j₂ ≤ ‖latticePoint L (k + D)‖)
    (hM1 : 2 * kerB0 L F j₁ ≤ M) (hM2 : 2 ^ j₂ * L + 4 * kerB0 L F j₁ ^ 2 ≤ 2 * M)
    (hrep : ∀ z : Fin d → ℤ, ‖latticePoint L z‖ ≤ M →
      (|ipL L k z| ≤ M ↔ |ipL L (k + D) z| ≤ M) ∧ (|ipL L k z| ≤ M → ipL L k z = ipL L (k + D) z)) :
    flowerKernelGen L γ δ p F aP pat (some c) (some j₁) (some j₂) t s (k + D) (k' + (F.sign : ℤ) • D) =
      flowerKernelGen L γ δ p F aP pat (some c) (some j₁) (some j₂) t s k k' := by
  classical
  by_cases hF : F = flower
  · simp [flowerKernelGen, hF]
  set n : ℝ := (Fintype.card (GLeaf (single F.toTree)) : ℝ)
  set B₀ := kerB0 L F j₁
  have hB0 : 0 ≤ B₀ := by unfold B₀ kerB0; positivity
  have hM₂ : (0 : ℝ) ≤ 2 ^ j₂ * L := by positivity
  have hdiff : latticePoint L (k + D) - (F.sign : ℤ) • latticePoint L (k' + (F.sign : ℤ) • D) =
      latticePoint L k - (F.sign : ℤ) • latticePoint L k' := by
    rw [latticePoint_add, latticePoint_add, latticePoint_zsmul, smul_add, smul_smul]
    rcases Int.units_eq_one_or F.sign with h | h <;> simp [h]
  by_cases hsupp : ‖latticePoint L k - (F.sign : ℤ) • latticePoint L k'‖ < n * (2 ^ j₁ * L)
  swap
  · push Not at hsupp
    rw [flowerKernelGen_cut1_eq_zero L γ δ hL p aP pat (some c) (some j₂) j₁ t s hsupp,
      flowerKernelGen_cut1_eq_zero L γ δ hL p aP pat (some c) (some j₂) j₁ t s (by rw [hdiff]; exact hsupp)]
  have hkB : 2 * B₀ < ‖latticePoint L k‖ := by unfold kerR at hk; nlinarith [sq_nonneg B₀]
  have hkDB : 2 * B₀ < ‖latticePoint L (k + D)‖ := by unfold kerR at hkD; nlinarith [sq_nonneg B₀]
  rw [flowerKernelGen_eq L γ δ hF p, flowerKernelGen_eq L γ δ hF p]
  congr 1
  rw [← (stemShiftEquiv F D k k').tsum_eq]
  refine tsum_congr fun κ => ?_
  show epsProd F.toTree (stemShift F D κ.1.1) * (treeWeight L F hF (some c) (some j₁) (some j₂)
      (stemShift F D κ.1.1) : ℂ) * TIpat L γ δ hF p _ (stemShift F D κ.1.1) pat t s * restP F aP (stemShift F D κ.1.1) =
    epsProd F.toTree κ.1.1 * (treeWeight L F hF (some c) (some j₁) (some j₂) κ.1.1 : ℂ) *
      TIpat L γ δ hF p _ κ.1.1 pat t s * restP F aP κ.1.1
  have hw : ∀ X, treeWeight L F hF (some c) (some j₁) (some j₂) X = treeCut1 L F j₁ X * treeCut2 L F hF j₂ X *
      treeSib L F hF c X := fun X => rfl
  by_cases hcut : treeCut1 L F j₁ κ.1.1 = 0
  · simp only [hw, treeCut1_stemShift, hcut, zero_mul, Complex.ofReal_zero, mul_zero, zero_mul]
  -- the base decoration
  set κ₀ := stemShift F (-k) κ.1.1
  have hB : ∀ a, ‖latticePoint L (κ₀ a)‖ ≤ B₀ := fun a => by
    have := norm_base_le L hL κ hcut hsupp a
    unfold B₀ kerB0
    linarith
  have hκ₀ : IsBranchConsistent κ₀ := stemShift_branch (-k) κ.1.2.1
  have e1 : κ.1.1 = stemShift F k κ₀ := by
    rw [stemShift_stemShift, neg_add_cancel, stemShift_zero]
  have e2 : stemShift F D κ.1.1 = stemShift F (k + D) κ₀ := by
    rw [e1, stemShift_stemShift]
  have hdich := fun (b : GBranch (single F.toTree)) (hb : OnStem F b.toNode) =>
    omega_dichotomy L hκ₀ hB hM1 hM2 hM₂ hk hkD hrep hb
  rw [e2, e1]
  rw [e1] at hcut
  by_cases hall : ∀ b : GBranch (single F.toTree), OnStem F b.toNode → b ≠ F.flowerParent hF →
      omegaT L F.toTree (stemShift F (k + D) κ₀) b = omegaT L F.toTree (stemShift F k κ₀) b
  · -- all relevant `Ω` agree
    have hcut2 : treeCut2 L F hF j₂ (stemShift F (k + D) κ₀) = treeCut2 L F hF j₂ (stemShift F k κ₀) := by
      unfold treeCut2
      congr 2
      refine Finset.sup_congr rfl fun b hb => ?_
      obtain ⟨-, hbs, hbf⟩ := Finset.mem_filter.1 hb
      rw [hall b hbs hbf]
    have hTI : ∀ off', (F.flowerParent hF ∈ off') →
        TIpat L γ δ hF p off' (stemShift F (k + D) κ₀) pat t s = TIpat L γ δ hF p off' (stemShift F k κ₀) pat t s := by
      intro off' hoff
      refine TIpat_congr L γ δ hF p off' (fun b hb => ?_) pat t s
      by_cases hbs : OnStem F b.toNode
      · exact hall b hbs (fun e => hb (e ▸ hoff))
      · rw [omegaT_stemShift_off L (k + D) κ₀ hbs, omegaT_stemShift_off L k κ₀ hbs]
    have hoff : F.flowerParent hF ∈ (if (some c).isSome then {F.flowerParent hF} else ∅ :
        Finset (GBranch (single F.toTree))) := by simp
    rw [hw, hw, hcut2, epsProd_stemShift L hB hkB hkDB, hTI _ hoff]
    simp only [treeCut1_stemShift, treeSib_stemShift, restP_stemShift]
  · -- some `Ω ≥ M₂` on both sides: both weights vanish
    push Not at hall
    obtain ⟨b, hbs, hbf, hne⟩ := hall
    rcases hdich b hbs with heq | ⟨h1, h2⟩
    · exact absurd heq hne
    · rw [hw, hw, treeCut2_eq_zero_of L hF hL j₂ _ hbs hbf h1, treeCut2_eq_zero_of L hF hL j₂ _ hbs hbf h2]
      simp

end Kernel

end WaveTurbulence.Fixedpt
