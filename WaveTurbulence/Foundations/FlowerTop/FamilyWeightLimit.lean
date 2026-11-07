/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.FlowerTop.KernelWeightLimit
public import WaveTurbulence.Foundations.FC23.FlowerFamily
public import WaveTurbulence.Foundations.XChain.ProductCut.ProdCut

/-! The FC23 family weight at `tail = small = false`, `z = 0` is a product of `chi0` factors in `[0,1]` that equals one
for all large scales `M = 2^j L`. -/
@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.FlowerTop
open Filter Topology WaveTurbulence.FC23
open scoped Classical

/-- The sibling weight is `0` or `1`. -/
theorem sibWeight_mem {w d : ℕ} (LG : LayeredGarden w) (c : Fin w → Fin 3 → Mom d)
    (k : GNode LG.garden.tree → Mom d) : 0 ≤ LG.sibWeight c k ∧ LG.sibWeight c k ≤ 1 := by
  unfold LayeredGarden.sibWeight
  have h : ∀ b : GBranch LG.garden.tree, 0 ≤ (if LG.garden.IsFlowerParent b then
      ∏ i : Fin 3, (if LG.IsFlowerNode (b.child i) then (1 : ℝ) else
        if k (b.child i) = c b.1.1 i then 1 else 0) else 1) ∧ (if LG.garden.IsFlowerParent b then
      ∏ i : Fin 3, (if LG.IsFlowerNode (b.child i) then (1 : ℝ) else
        if k (b.child i) = c b.1.1 i then 1 else 0) else 1) ≤ 1 := by
    intro b
    split_ifs
    · refine ⟨Finset.prod_nonneg fun i _ => ?_, Finset.prod_le_one₀ (fun i _ => ?_) fun i _ => ?_⟩ <;>
        split_ifs <;> norm_num
    · norm_num
  exact ⟨Finset.prod_nonneg fun b _ => (h b).1, Finset.prod_le_one₀ (fun b _ => (h b).1) fun b _ => (h b).2⟩

theorem eventually_chi0_one (x L : ℝ) (hL : 0 < L) :
    ∀ᶠ j : ℕ in atTop, chi0 (x / (2 ^ j * L)) = 1 ∧ chi0 (x / (2 ^ j * L / 2)) = 1 := by
  have ht : Tendsto (fun j : ℕ => (2 : ℝ) ^ j * L) atTop atTop :=
    (tendsto_pow_atTop_atTop_of_one_lt one_lt_two).atTop_mul_const hL
  filter_upwards [ht.eventually_ge_atTop (4 * |x| + 1)] with j hj
  have hM : 0 < (2 : ℝ) ^ j * L := by positivity
  have h1 : |x / (2 ^ j * L)| ≤ 1 / 2 := by
    rw [abs_div, abs_of_pos hM, div_le_iff₀ hM]; nlinarith [abs_nonneg x]
  have h2 : |x / (2 ^ j * L / 2)| ≤ 1 / 2 := by
    have : 0 < (2 : ℝ) ^ j * L / 2 := by positivity
    rw [abs_div, abs_of_pos this, div_le_iff₀ this]; nlinarith [abs_nonneg x]
  exact ⟨XChain.ProductCut.chi0_eq_one h1, XChain.ProductCut.chi0_eq_one h2⟩

/-- The family weight at `tail = small = false`, `z = 0`, as an explicit product of `chi0` factors. -/
theorem family_weight_eq {w d : ℕ} (LG : LayeredGarden w) (p : ℕ) (M A : ℝ)
    (k : GNode LG.garden.tree → Mom d) :
    flowerFamilyWeight LG p M A (fun _ => false) (fun _ => false) (fun _ => 0) k =
      (∏ a : GNode LG.garden.tree,
        if LG.IsTopLeaf p a ∧ LG.layer a < p ∧ ¬LG.IsFlowerNode a then chi0 (‖k a‖ / M) else 1) *
      ∏ l : GLeaf LG.garden.tree, if LG.garden.IsFlower l then 1 else
        if LG.layer l.toNode = p then chi0 (‖k l.toNode‖ / (M / 2)) else 1 := by
  unfold flowerFamilyWeight endpointFactor
  simp

theorem family_weight_mem {w d : ℕ} (LG : LayeredGarden w) (p : ℕ) (M A : ℝ)
    (k : GNode LG.garden.tree → Mom d) :
    0 ≤ flowerFamilyWeight LG p M A (fun _ => false) (fun _ => false) (fun _ => 0) k ∧
      flowerFamilyWeight LG p M A (fun _ => false) (fun _ => false) (fun _ => 0) k ≤ 1 := by
  rw [family_weight_eq]
  have c0 := XChain.ProductCut.chi0_nonneg
  have c1 := XChain.ProductCut.chi0_le_one
  have hA : 0 ≤ ∏ a : GNode LG.garden.tree,
        (if LG.IsTopLeaf p a ∧ LG.layer a < p ∧ ¬LG.IsFlowerNode a then chi0 (‖k a‖ / M) else 1) ∧
      ∏ a : GNode LG.garden.tree,
        (if LG.IsTopLeaf p a ∧ LG.layer a < p ∧ ¬LG.IsFlowerNode a then chi0 (‖k a‖ / M) else 1) ≤ 1 := by
    refine ⟨Finset.prod_nonneg fun a _ => ?_, Finset.prod_le_one₀ (fun a _ => ?_) fun a _ => ?_⟩ <;>
      split_ifs <;> first | exact c0 _ | exact c1 _ | norm_num
  have hB : 0 ≤ ∏ l : GLeaf LG.garden.tree, (if LG.garden.IsFlower l then (1 : ℝ) else
        if LG.layer l.toNode = p then chi0 (‖k l.toNode‖ / (M / 2)) else 1) ∧
      ∏ l : GLeaf LG.garden.tree, (if LG.garden.IsFlower l then (1 : ℝ) else
        if LG.layer l.toNode = p then chi0 (‖k l.toNode‖ / (M / 2)) else 1) ≤ 1 := by
    refine ⟨Finset.prod_nonneg fun a _ => ?_, Finset.prod_le_one₀ (fun a _ => ?_) fun a _ => ?_⟩ <;>
      split_ifs <;> first | exact c0 _ | exact c1 _ | norm_num
  exact ⟨mul_nonneg hA.1 hB.1, (mul_le_mul hA.2 hB.2 hB.1 zero_le_one).trans_eq (one_mul 1)⟩

theorem family_weight_eventually_one {w d : ℕ} (LG : LayeredGarden w) (p : ℕ) (L : ℝ) (hL : 0 < L)
    (N : ℕ) (k : GNode LG.garden.tree → Mom d) :
    ∀ᶠ j : ℕ in atTop, flowerFamilyWeight LG p (2 ^ j * L) ((2 ^ j * L) / (4 * (2 * N + 1 : ℕ)))
      (fun _ => false) (fun _ => false) (fun _ => 0) k = 1 := by
  have hA : ∀ᶠ j : ℕ in atTop, ∀ a : GNode LG.garden.tree, chi0 (‖k a‖ / (2 ^ j * L)) = 1 :=
    eventually_all.mpr fun a => (eventually_chi0_one _ L hL).mono fun _ h => h.1
  have hB : ∀ᶠ j : ℕ in atTop, ∀ l : GLeaf LG.garden.tree, chi0 (‖k l.toNode‖ / (2 ^ j * L / 2)) = 1 :=
    eventually_all.mpr fun a => (eventually_chi0_one _ L hL).mono fun _ h => h.2
  filter_upwards [hA, hB] with j hjA hjB
  rw [family_weight_eq]
  have e1 : (∏ a : GNode LG.garden.tree, if LG.IsTopLeaf p a ∧ LG.layer a < p ∧ ¬LG.IsFlowerNode a then
      chi0 (‖k a‖ / (2 ^ j * L)) else 1) = 1 :=
    Finset.prod_eq_one fun a _ => by split_ifs <;> simp [hjA a]
  have e2 : (∏ l : GLeaf LG.garden.tree, if LG.garden.IsFlower l then (1 : ℝ) else
      if LG.layer l.toNode = p then chi0 (‖k l.toNode‖ / (2 ^ j * L / 2)) else 1) = 1 :=
    Finset.prod_eq_one fun l _ => by split_ifs <;> simp [hjB l]
  rw [e1, e2, one_mul]

end WaveTurbulence.FlowerTop
