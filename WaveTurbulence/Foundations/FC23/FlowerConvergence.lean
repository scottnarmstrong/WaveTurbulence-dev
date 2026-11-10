/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.FC23.FlowerSlices
public import WaveTurbulence.Foundations.XChain.GraftGenDraft.KernelGenGraft
/-! Absolute convergence for the literal flower kernels with bounded
polynomial-family weights. No uniform-family bound is used for convergence. -/
@[expose] public section
set_option autoImplicit false
noncomputable section
open scoped Classical
namespace WaveTurbulence.FC23
open Finset GraftGen

private theorem abs_chi0_le (x : ℝ) : |chi0 x| ≤ 1 := by
  rw [frozen_chi0_eq, abs_of_nonneg (Fourier.chi0_nonneg x)]
  exact Fourier.chi0_le_one x

theorem endpointFactor_abs_le (p q : ℕ) (tail : Bool) (M A z r : ℝ) :
    |endpointFactor p q tail M A z r| ≤ 1 + 2 * |z| := by
  have h1 := abs_chi0_le (r / (M / 2))
  have h2 := abs_chi0_le (r / M)
  have h3 := abs_chi0_le (r / A)
  have ht : |1 - chi0 (r / A)| ≤ 2 := (abs_sub _ _).trans (by rw [abs_one]; linarith)
  have hd : |chi0 (r / M) - chi0 (r / (M / 2))| ≤ 2 :=
    (abs_sub _ _).trans (by linarith)
  cases tail <;> by_cases hq : q = p
  · simp only [endpointFactor, Bool.false_eq_true, ite_false, hq, ite_true]
    exact (abs_add_le _ _).trans (by rw [abs_mul]; nlinarith [mul_le_mul_of_nonneg_left hd (abs_nonneg z)])
  · simp only [endpointFactor, Bool.false_eq_true, ite_false, hq, abs_one]
    linarith [abs_nonneg z]
  · simp only [endpointFactor, ite_true, hq, abs_mul]
    apply (mul_le_mul h1 ((abs_add_le _ _).trans ?_) (abs_nonneg _) (by positivity)).trans_eq (one_mul _)
    rw [abs_one, abs_mul]
    nlinarith [mul_le_mul_of_nonneg_left ht (abs_nonneg z)]
  · simp only [endpointFactor, ite_true, hq, ite_false, one_mul]
    apply (abs_add_le _ _).trans
    rw [abs_one, abs_mul]
    nlinarith [mul_le_mul_of_nonneg_left ht (abs_nonneg z)]

theorem sibWeight_abs_le {w d : ℕ} (LG : LayeredGarden w) (c : Fin w → Fin 3 → Mom d)
    (k : GNode LG.garden.tree → Mom d) : |LG.sibWeight c k| ≤ 1 := by
  unfold LayeredGarden.sibWeight
  rw [abs_prod]
  apply prod_le_one₀ (fun _ _ => abs_nonneg _)
  intro b _
  split_ifs
  · rw [abs_prod]
    apply prod_le_one₀ (fun _ _ => abs_nonneg _)
    intro i _
    split_ifs <;> norm_num
  · norm_num

theorem flowerFamilyWeight_abs_le {w d : ℕ} (LG : LayeredGarden w) (p : ℕ) (M A : ℝ)
    (tail small : Fin w → Bool) (z : Fin w → ℝ) (k : GNode LG.garden.tree → Mom d) :
    |flowerFamilyWeight LG p M A tail small z k| ≤
      (1 + 2 * ∑ j, |z j|) ^ Fintype.card (GLeaf LG.garden.tree) := by
  have hC : 1 ≤ 1 + 2 * ∑ j, |z j| := by
    linarith [sum_nonneg (fun j (_ : j ∈ univ) => abs_nonneg (z j))]
  have hb : |∏ a : GNode LG.garden.tree,
      if LG.IsTopLeaf p a ∧ LG.layer a < p ∧ ¬LG.IsFlowerNode a then
        chi0 (‖k a‖ / (if tail a.1.1 && small a.1.1 then M / 2 else M)) else 1| ≤ 1 := by
    rw [abs_prod]
    apply prod_le_one₀ (fun _ _ => abs_nonneg _)
    intro a _
    split_ifs <;> first | exact abs_chi0_le _ | norm_num
  unfold flowerFamilyWeight
  rw [abs_mul]
  apply (mul_le_mul_of_nonneg_right hb (abs_nonneg _)).trans
  rw [one_mul, abs_prod]
  calc
    _ ≤ ∏ _l : GLeaf LG.garden.tree, (1 + 2 * ∑ j, |z j|) := by
      apply prod_le_prod₀ (fun _ _ => abs_nonneg _)
      intro l _
      split_ifs
      · simpa only [abs_one] using hC
      · apply (endpointFactor_abs_le _ _ _ _ _ _ _).trans
        have h := single_le_sum (fun j _ => abs_nonneg (z j)) (mem_univ l.1.1)
        linarith
    _ = _ := by rw [prod_const, card_univ]

/-- Bounded weights of any finite size preserve absolute convergence. -/
theorem summable_kernelGenFactor_bounded {d w : ℕ} (L γ δ : ℝ)
    (F : ℕ → Mom d → ℝ) (LG : LayeredGarden w)
    (fix : GBranch LG.garden.tree → Option ℝ) (off : Finset (GBranch LG.garden.tree))
    (wt : (GNode LG.garden.tree → Mom d) → ℝ) {C : ℝ} (_hC : 0 ≤ C)
    (hwt : ∀ k, |wt k| ≤ C) (up : GBranch LG.garden.tree → ℝ)
    (k₀ : Mom d) (nroot : Fin w → (Fin d → ℤ)) (nfl : Fin d → ℤ)
    (hn : ∀ l, LG.garden.mark l ≠ some MarkTag.lower)
    (hF : ∀ q, Summable fun m : Fin d → ℤ => |F q (k₀ + latticePoint L m)|) :
    Summable (kernelGenFactor L γ δ F LG fix off wt up k₀ (n := nroot) (nfl := nfl)) := by
  have hs := summable_kernelGenFactor L γ δ F LG fix off (fun _ => 1)
    (fun _ => by norm_num) up k₀ nroot nfl hn hF
  apply Summable.of_norm_bounded (hs.norm.mul_left C)
  intro κ
  have he : kernelGenFactor L γ δ F LG fix off wt up k₀ κ =
      (wt (cosetDecoration LG.garden L k₀ κ.1) : ℂ) *
        kernelGenFactor L γ δ F LG fix off (fun _ => 1) up k₀ κ := by
    unfold kernelGenFactor
    push_cast
    ring
  rw [he, norm_mul, Complex.norm_real, Real.norm_eq_abs]
  exact mul_le_mul_of_nonneg_right (hwt _) (norm_nonneg _)

end WaveTurbulence.FC23
