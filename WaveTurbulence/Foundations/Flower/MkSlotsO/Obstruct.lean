/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Stage1.RepAnalytic.Partition

/-! # B3s-HELPER8 (STOP S1): no ball-localized summable family represents a function bounded below

`MkSlotsI.GenSlotObligationAt` (SlotObl.lean, sha256 7163863b…) asks, on EVERY outer slot, for amplitudes supported in
unit balls around lattice points (`amp l k ≠ 0 → ‖k - latPt d (c l)‖ ≤ 1`) with summable weights, and, on every slot
that is not a cap pair, for the superposition at EVERY momentum `k`. On a chain slot whose native chain is nil the
general slot kernel is identically `1` (see `MkSlotsO/PROGRESS.md`, S1), and such a family cannot exist:

* **`not_localized_of_norm_ge`**: if `f : Mom d → ℂ` (`d ≥ 1`) satisfies `ε ≤ ‖f k‖` for every `k`, no family with
  `0 ≤ wt`, `Summable wt`, `‖amp‖ ≤ 1`, unit-ball supports and phases of modulus `≤ 1` has
  `HasSum (fun l => wt l * amp l k * ph l) (f k)` for every `k`.

Proof: at the points `k_n = n • 3e₀` the balls meeting `k_n` are pairwise disjoint, each carries weight `≥ ε`, so
`N ε ≤ Σ wt` for every `N`. -/

@[expose] public section
set_option autoImplicit false
noncomputable section
open scoped Classical
open WaveTurbulence WaveTurbulence.RepAnalytic Finset

namespace WaveTurbulence.Flower.MkSlotsO

/-- The test points `n • 3e₀`. -/
def testPt {d : ℕ} (hd : 1 ≤ d) (n : ℕ) : Mom d :=
  (n : ℝ) • EuclideanSpace.single (⟨0, hd⟩ : Fin d) (3 : ℝ)

theorem testPt_sep {d : ℕ} (hd : 1 ≤ d) {n m : ℕ} (h : n ≠ m) : 3 ≤ ‖testPt hd n - testPt hd m‖ := by
  unfold testPt
  rw [← sub_smul, norm_smul, PiLp.norm_single, Real.norm_eq_abs, Real.norm_eq_abs,
    abs_of_pos (by norm_num : (0 : ℝ) < 3)]
  have h1 : (1 : ℝ) ≤ |(n : ℝ) - m| := by
    rcases Nat.lt_or_gt_of_ne h with hlt | hlt
    · have : (n : ℝ) + 1 ≤ m := by exact_mod_cast hlt
      rw [abs_sub_comm, abs_of_nonneg (by linarith)]
      linarith
    · have : (m : ℝ) + 1 ≤ n := by exact_mod_cast hlt
      rw [abs_of_nonneg (by linarith)]
      linarith
  linarith

/-- **No ball-localized summable family represents a function bounded below at every momentum.** -/
theorem not_localized_of_norm_ge {d : ℕ} (hd : 1 ≤ d) {Λ : Type} (wt : Λ → ℝ) (c : Λ → Fin d → ℤ)
    (amp : Λ → Mom d → ℂ) (ph : Λ → ℂ) (hph : ∀ l, ‖ph l‖ ≤ 1) (hw0 : ∀ l, 0 ≤ wt l) (hws : Summable wt)
    (hamp1 : ∀ l k, ‖amp l k‖ ≤ 1) (hsupp : ∀ l k, amp l k ≠ 0 → ‖k - latPt d (c l)‖ ≤ 1)
    (f : Mom d → ℂ) {ε : ℝ} (hε : 0 < ε) (hf : ∀ k, ε ≤ ‖f k‖)
    (hsum : ∀ k, HasSum (fun l => (wt l : ℂ) * amp l k * ph l) (f k)) : False := by
  set ind : ℕ → Λ → ℝ := fun n l => if ‖testPt hd n - latPt d (c l)‖ ≤ 1 then wt l else 0 with hind
  have hind_le : ∀ n l, ind n l ≤ wt l := fun n l => by
    simp only [hind]; split_ifs <;> simp [hw0 l]
  have hind0 : ∀ n l, 0 ≤ ind n l := fun n l => by
    simp only [hind]; split_ifs <;> simp [hw0 l]
  have hinds : ∀ n, Summable (ind n) := fun n => hws.of_nonneg_of_le (hind0 n) (hind_le n)
  -- each test point carries weight `≥ ε` on the balls meeting it
  have hbound : ∀ n, ε ≤ ∑' l, ind n l := fun n => by
    refine (hf (testPt hd n)).trans ((hsum (testPt hd n)).norm_le_of_bounded (hinds n).hasSum fun l => ?_)
    by_cases h0 : amp l (testPt hd n) = 0
    · rw [h0, mul_zero, zero_mul, norm_zero]; exact hind0 n l
    · have hin : ‖testPt hd n - latPt d (c l)‖ ≤ 1 := hsupp l _ h0
      simp only [hind, if_pos hin]
      rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_of_nonneg (hw0 l)]
      have h2 : wt l * ‖amp l (testPt hd n)‖ ≤ wt l * 1 := mul_le_mul_of_nonneg_left (hamp1 l _) (hw0 l)
      calc wt l * ‖amp l (testPt hd n)‖ * ‖ph l‖ ≤ wt l * 1 * 1 :=
            mul_le_mul h2 (hph l) (norm_nonneg _) (by linarith [hw0 l])
        _ = wt l := by ring
  -- a ball meets at most one test point
  have hdisj : ∀ (N : ℕ) (l : Λ), ∑ n ∈ range N, ind n l ≤ wt l := fun N l => by
    have hcard : ((range N).filter fun n => ‖testPt hd n - latPt d (c l)‖ ≤ 1).card ≤ 1 := by
      refine Finset.card_le_one.mpr fun a ha b hb => ?_
      by_contra hab
      have h3 := testPt_sep hd hab
      have ha' := (Finset.mem_filter.mp ha).2
      have hb' := (Finset.mem_filter.mp hb).2
      have : ‖testPt hd a - testPt hd b‖ ≤ 2 := by
        calc ‖testPt hd a - testPt hd b‖ = ‖(testPt hd a - latPt d (c l)) - (testPt hd b - latPt d (c l))‖ := by
              congr 1; abel
          _ ≤ ‖testPt hd a - latPt d (c l)‖ + ‖testPt hd b - latPt d (c l)‖ := norm_sub_le _ _
          _ ≤ 2 := by linarith
      linarith
    calc ∑ n ∈ range N, ind n l
        = ∑ n ∈ (range N).filter (fun n => ‖testPt hd n - latPt d (c l)‖ ≤ 1), wt l := by
          rw [Finset.sum_filter]
      _ = ((range N).filter fun n => ‖testPt hd n - latPt d (c l)‖ ≤ 1).card * wt l := by
          rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ 1 * wt l := by
          gcongr
          · exact hw0 l
          · exact_mod_cast hcard
      _ = wt l := one_mul _
  have hN : ∀ N : ℕ, (N : ℝ) * ε ≤ ∑' l, wt l := fun N => by
    calc (N : ℝ) * ε = ∑ n ∈ range N, ε := by rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
      _ ≤ ∑ n ∈ range N, ∑' l, ind n l := Finset.sum_le_sum fun n _ => hbound n
      _ = ∑' l, ∑ n ∈ range N, ind n l := (Summable.tsum_finsetSum fun n _ => hinds n).symm
      _ ≤ ∑' l, wt l :=
          Summable.tsum_le_tsum (fun l => hdisj N l) (summable_sum fun n _ => hinds n) hws
  obtain ⟨N, hNgt⟩ := exists_nat_gt ((∑' l, wt l) / ε)
  have := hN N
  rw [div_lt_iff₀ hε] at hNgt
  linarith

end WaveTurbulence.Flower.MkSlotsO
