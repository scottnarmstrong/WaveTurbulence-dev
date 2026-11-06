/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.Spine.Kinds
/-! # Support lemmas for the rung weights (S3b LADDER-DECAY)

`cutW L 0 0` is bounded by one and equals one on the box `|x_j|, |y_j| ≤ 2L`; rung sums do not
depend on the finite index set once it contains the support of the weight. -/
@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.LadderDecay
open Finset WaveTurbulence WaveTurbulence.WeylSums WaveTurbulence.Sumint

variable {d : ℕ}

lemma norm_cutW_le (L : ℝ) (a b : Fin d → ℝ) (p : Pt d) : ‖cutW L a b p‖ ≤ 1 := by
  unfold cutW
  rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (inputCutoff_nonneg _ _)
    (inputCutoff_nonneg _ _))]
  exact mul_le_one₀ (inputCutoff_le_one _ _) (inputCutoff_nonneg _ _) (inputCutoff_le_one _ _)

lemma cutW_eq_one {L : ℝ} (hL : 0 < L) (a b : Fin d → ℝ) (p : Pt d)
    (hx : ∀ j, |(p.1 j : ℝ) / L - a j| ≤ 2) (hy : ∀ j, |(p.2 j : ℝ) / L - b j| ≤ 2) :
    cutW L a b p = 1 := by
  have h1 : ∀ (c : Fin d → ℝ) (q : Fin d → ℤ), (∀ j, |(q j : ℝ) / L - c j| ≤ 2) →
      inputCutoff c (latticePoint L q) = 1 := by
    intro c q hq
    unfold inputCutoff
    apply Fourier.chi0Tensor_eq_one
    intro j
    have := hq j
    simp only [latticePoint]
    rw [abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 4)]
    rw [div_le_iff₀ (by norm_num : (0 : ℝ) < 4)]
    linarith
  unfold cutW
  rw [h1 a _ hx, h1 b _ hy]; simp

lemma cutW_ne_zero_x {L : ℝ} (hL : 0 < L) (a b : Fin d → ℝ) (p : Pt d) (h : cutW L a b p ≠ 0) :
    p.1 ∈ Counting.latticeBox (fun j => L * a j) (4 * L) ∧
      p.2 ∈ Counting.latticeBox (fun j => L * b j) (4 * L) := by
  unfold cutW at h
  have h' : inputCutoff a (latticePoint L p.1) * inputCutoff b (latticePoint L p.2) ≠ 0 := by
    intro h0; apply h; rw [h0]; simp
  exact ⟨inputCutoff_mem_integerBox hL a _ (left_ne_zero_of_mul h'),
    inputCutoff_mem_integerBox hL b _ (right_ne_zero_of_mul h')⟩

/-- The rung sum depends only on the support of the weight. -/
lemma rungSum_congr_support (L c : ℝ) (w : Pt d → ℂ) (S S' : Finset (Pt d))
    (hS : ∀ p, w p ≠ 0 → p ∈ S) (hS' : ∀ p, w p ≠ 0 → p ∈ S') (lam ν : Pt d →+ ℝ) (t : ℝ × ℝ) :
    rungSum L c w S lam ν t = rungSum L c w S' lam ν t := by
  unfold rungSum
  classical
  have key : ∀ T : Finset (Pt d), (∀ p, w p ≠ 0 → p ∈ T) → ∀ U : Finset (Pt d), T ⊆ U →
      ∑ p ∈ T, w p * e (c * (t.2 - t.1) * bil L p + (t.2 * lam p + ν p)) =
      ∑ p ∈ U, w p * e (c * (t.2 - t.1) * bil L p + (t.2 * lam p + ν p)) := by
    intro T hT U hTU
    refine Finset.sum_subset hTU (fun p _ hpT => ?_)
    have : w p = 0 := by by_contra h; exact hpT (hT p h)
    simp [this]
  rw [key S hS (S ∪ S') Finset.subset_union_left, key S' hS' (S ∪ S') Finset.subset_union_right]

end WaveTurbulence.LadderDecay
