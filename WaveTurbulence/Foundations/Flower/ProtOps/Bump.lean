/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import Mathlib
public import WaveTurbulence.Frozen.Defs.Mom

/-! # PROT-OPS: the fixed lattice bump of o73 (13.4)

`psi d` is a fixed smooth compactly supported bump on momentum space, equal to `1` at `0` and supported in the open
ball of radius `1/3`. Its rescaled translates `psi d (L • (· - a))` have iterated derivatives of order `n` bounded by
`L ^ n` times a fixed constant. -/

@[expose] public section
set_option autoImplicit false
noncomputable section
open WaveTurbulence
open scoped ContDiff

namespace WaveTurbulence.Flower.ProtOps

/-- The bump datum: inner radius `1/6`, outer radius `1/3`. -/
def bumpDatum (d : ℕ) : ContDiffBump (0 : Mom d) := ⟨1 / 6, 1 / 3, by norm_num, by norm_num⟩

/-- The fixed bump. -/
def psi (d : ℕ) (x : Mom d) : ℝ := bumpDatum d x

theorem psi_zero (d : ℕ) : psi d 0 = 1 := (bumpDatum d).one_of_mem_closedBall (Metric.mem_closedBall_self (by norm_num [bumpDatum]))

theorem psi_eq_zero_of_far (d : ℕ) {x : Mom d} (hx : 1 / 3 ≤ ‖x‖) : psi d x = 0 := by
  apply (bumpDatum d).zero_of_le_dist
  simpa [bumpDatum, dist_zero_right] using hx

theorem psi_contDiff (d : ℕ) {n : ℕ∞} : ContDiff ℝ n (psi d) := (bumpDatum d).contDiff

theorem psi_hasCompactSupport (d : ℕ) : HasCompactSupport (psi d) := (bumpDatum d).hasCompactSupport

/-- A uniform bound for the iterated derivatives of `psi d` of order at most `N`. -/
theorem exists_psi_bound (d N : ℕ) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ n ≤ N, ∀ x, ‖iteratedFDeriv ℝ n (psi d) x‖ ≤ B := by
  have h : ∀ n : ℕ, ∃ C : ℝ, ∀ x, ‖iteratedFDeriv ℝ n (psi d) x‖ ≤ C := fun n =>
    ((psi_contDiff d).continuous_iteratedFDeriv (m := n) (by exact_mod_cast le_top)).bounded_above_of_compact_support
      ((psi_hasCompactSupport d).iteratedFDeriv n)
  choose C hC using h
  refine ⟨∑ n ∈ Finset.range (N + 1), |C n|, Finset.sum_nonneg fun _ _ => abs_nonneg _, fun n hn x => ?_⟩
  calc ‖iteratedFDeriv ℝ n (psi d) x‖ ≤ C n := hC n x
    _ ≤ |C n| := le_abs_self _
    _ ≤ _ := Finset.single_le_sum (f := fun n => |C n|) (fun _ _ => abs_nonneg _)
        (Finset.mem_range.2 (Nat.lt_succ_of_le hn))

/-- The rescaled translate has iterated derivatives of order `n` at most `L ^ n` times those of `psi d`. -/
theorem norm_iteratedFDeriv_bump_le {d N : ℕ} {B : ℝ} (hB : ∀ n ≤ N, ∀ x, ‖iteratedFDeriv ℝ n (psi d) x‖ ≤ B)
    {L : ℝ} (hL : 1 ≤ L) (a : Mom d) {n : ℕ} (hn : n ≤ N) (x : Mom d) :
    ‖iteratedFDeriv ℝ n (fun y => psi d (L • (y - a))) x‖ ≤ L ^ N * B := by
  have h1 := iteratedFDeriv_comp_sub (𝕜 := ℝ) (f := fun z => psi d (L • z)) n a x
  have h2 := congrFun (iteratedFDeriv_comp_const_smul (𝕜 := ℝ) (f := psi d) (i := n) L
    (psi_contDiff d)) (x - a)
  have hB0 : 0 ≤ B := (norm_nonneg _).trans (hB 0 (Nat.zero_le _) 0)
  rw [h1.trans h2, norm_smul, Real.norm_eq_abs, abs_pow, abs_of_nonneg (zero_le_one.trans hL)]
  calc L ^ n * ‖iteratedFDeriv ℝ n (psi d) (L • (x - a))‖ ≤ L ^ n * B :=
        mul_le_mul_of_nonneg_left (hB n hn _) (by positivity)
    _ ≤ L ^ N * B := mul_le_mul_of_nonneg_right (pow_le_pow_right₀ hL hn) hB0

end WaveTurbulence.Flower.ProtOps
