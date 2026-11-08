/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Incoh.CutoffMass
public import WaveTurbulence.Foundations.XChain.LatticeBracketBounds
public import WaveTurbulence.Foundations.XChain.JbrBounds

/-! # D3 PROT-PIN: the sharp lattice-coset sum

`Σ_{n ∈ ℤ^d} ⟨k + n/L⟩^{-(d+1)} ≤ C_d L^d`, uniformly in `k` (main's `tsum_jbr_coset_le` gives `L^{d+1}`). Each lattice
point is charged to its nearest integer point `a` with the unit cutoff `∏ χ₀(x_i - a_i) = 1`, and the cutoff mass of a
coset is at most `(5L)^d` (main `tsum_latticeCutoff_le`). It pays the exceptional-pair sums of D3 at cost `L^{2d}`,
which `coupling²` cancels. -/

@[expose] public section
set_option autoImplicit false
noncomputable section
open WaveTurbulence Set Finset MeasureTheory
open scoped ENNReal

namespace WaveTurbulence.Flower.ProtPin

variable {d : ℕ}

/-- The constant of the sharp coset sum. -/
def latC (d : ℕ) : ℝ :=
  (Real.sqrt 2 * Real.sqrt (1 + d)) ^ (d + 1) * 5 ^ d * ∑' a : Fin d → ℤ, jbr (latticePoint 1 a) ^ (-((d : ℝ) + 1))

theorem latC_nonneg (d : ℕ) : 0 ≤ latC d := by
  unfold latC
  refine mul_nonneg (by positivity) (tsum_nonneg fun _ => Real.rpow_nonneg (Induct.jbr_pos _).le _)

theorem jbr_le_sqrt_of_abs_le {x : Mom d} (h : ∀ i, |x i| ≤ 1 / 2) : jbr x ≤ Real.sqrt (1 + d) := by
  unfold jbr
  apply Real.sqrt_le_sqrt
  have : ‖x‖ ^ 2 ≤ d := by
    rw [EuclideanSpace.norm_sq_eq]
    calc ∑ i, ‖x i‖ ^ 2 ≤ ∑ _i : Fin d, (1 : ℝ) := by
          apply Finset.sum_le_sum
          intro i _
          have := h i
          rw [Real.norm_eq_abs]
          nlinarith [abs_nonneg (x i), sq_abs (x i)]
      _ = d := by simp
  linarith

/-- The nearest integer point. -/
def nearInt (x : Mom d) : Fin d → ℤ := fun i => round (x i)

theorem near_abs (x : Mom d) (i : Fin d) : |(x - latticePoint 1 (nearInt x)) i| ≤ 1 / 2 := by
  simp only [PiLp.sub_apply, latticePoint, nearInt, div_one]
  exact abs_sub_round (x i)

/-- One term is charged to its nearest integer point. -/
theorem term_le (x : Mom d) :
    jbr x ^ (-((d : ℝ) + 1)) ≤
      (Real.sqrt 2 * Real.sqrt (1 + d)) ^ (d + 1) * jbr (latticePoint 1 (nearInt x)) ^ (-((d : ℝ) + 1)) *
        WeylSums.latticeCutoff (x - latticePoint 1 (nearInt x)) := by
  set a := latticePoint 1 (nearInt x)
  have hcut : WeylSums.latticeCutoff (x - a) = 1 := by
    unfold WeylSums.latticeCutoff
    exact Finset.prod_eq_one fun i _ => Fourier.chi0_eq_one (near_abs x i)
  rw [hcut, mul_one]
  have hxa : jbr (a - x) ≤ Real.sqrt (1 + d) := by
    rw [← Induct.jbr_neg, neg_sub]
    exact jbr_le_sqrt_of_abs_le (near_abs x)
  have hp := Induct.jbr_add_le x (a - x)
  rw [add_sub_cancel] at hp
  have hx := Induct.jbr_pos x
  have ha := Induct.jbr_pos a
  have hc : jbr a ≤ (Real.sqrt 2 * Real.sqrt (1 + d)) * jbr x := by
    calc jbr a ≤ Real.sqrt 2 * jbr x * jbr (a - x) := hp
      _ ≤ Real.sqrt 2 * jbr x * Real.sqrt (1 + d) := by gcongr
      _ = _ := by ring
  rw [show ((d : ℝ) + 1) = ((d + 1 : ℕ) : ℝ) by push_cast; ring]
  simp only [Real.rpow_neg hx.le, Real.rpow_neg ha.le, Real.rpow_natCast]
  rw [← inv_pow, ← inv_pow, ← mul_pow]
  apply pow_le_pow_left₀ (inv_nonneg.2 hx.le)
  rw [← div_eq_mul_inv, le_div_iff₀ ha, inv_mul_eq_div, div_le_iff₀ hx]
  linarith

/-- **The sharp coset sum.** -/
theorem tsum_jbr_coset_sharp {L : ℝ} (hL : 1 ≤ L) (k : Mom d) :
    ∑' n : Fin d → ℤ, ENNReal.ofReal (jbr (k + latticePoint L n) ^ (-((d : ℝ) + 1))) ≤
      ENNReal.ofReal (latC d * L ^ d) := by
  set c := (Real.sqrt 2 * Real.sqrt (1 + d)) ^ (d + 1) with hc
  have hc0 : 0 ≤ c := by positivity
  set f : (Fin d → ℤ) → ℝ := fun a => jbr (latticePoint 1 a) ^ (-((d : ℝ) + 1)) with hf
  have hf0 : ∀ a, 0 ≤ f a := fun a => Real.rpow_nonneg (Induct.jbr_pos _).le _
  have hfs : Summable f := Induct.summable_jbr_rpow_neg le_rfl
  have hLp : 0 < L := by linarith
  -- each term is below the cutoff sum over integer points
  have h1 : ∀ n : Fin d → ℤ, ENNReal.ofReal (jbr (k + latticePoint L n) ^ (-((d : ℝ) + 1))) ≤
      ∑' a, ENNReal.ofReal (c * f a) * ENNReal.ofReal (WeylSums.latticeCutoff (latticePoint L n - (latticePoint 1 a - k))) := by
    intro n
    set x := k + latticePoint L n
    refine le_trans ?_ (ENNReal.le_tsum (nearInt x))
    rw [← ENNReal.ofReal_mul (mul_nonneg hc0 (hf0 _))]
    refine ENNReal.ofReal_le_ofReal ((term_le x).trans (le_of_eq ?_))
    congr 2
    simp only [x]
    abel
  refine (ENNReal.tsum_le_tsum h1).trans ?_
  rw [ENNReal.tsum_comm]
  have h2 : ∀ a : Fin d → ℤ, ∑' n : Fin d → ℤ, ENNReal.ofReal (c * f a) *
      ENNReal.ofReal (WeylSums.latticeCutoff (latticePoint L n - (latticePoint 1 a - k))) ≤
      ENNReal.ofReal (c * f a) * ENNReal.ofReal ((5 * L) ^ d) := by
    intro a
    rw [ENNReal.tsum_mul_left]
    refine mul_le_mul' le_rfl ?_
    rw [← ENNReal.ofReal_tsum_of_nonneg (fun _ => Incoh.latticeCutoff_nonneg _)
      (summable_of_hasFiniteSupport (WeylSums.finite_latticeCutoff hLp _))]
    exact ENNReal.ofReal_le_ofReal (Incoh.tsum_latticeCutoff_le hL _)
  refine (ENNReal.tsum_le_tsum h2).trans ?_
  rw [ENNReal.tsum_mul_right, ← ENNReal.ofReal_tsum_of_nonneg (fun a => mul_nonneg hc0 (hf0 a)) (hfs.mul_left c),
    ← ENNReal.ofReal_mul (tsum_nonneg fun a => mul_nonneg hc0 (hf0 a))]
  refine ENNReal.ofReal_le_ofReal (le_of_eq ?_)
  rw [tsum_mul_left, mul_pow]
  unfold latC
  ring

end WaveTurbulence.Flower.ProtPin
