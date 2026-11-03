/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.CountLemmas.DotStrip

/-! # Elementary product-ball counts for terminal lattice scales -/

public section
open Finset
namespace WaveTurbulence.CountLemmas

/-- Two source spatial constraints give a product of actual translated
integer boxes, independently of any energy conditions. -/
theorem card_pair_balls_le {d : ℕ} (s : Finset ((Fin d → ℤ) × (Fin d → ℤ)))
    {L R : ℝ} (hL : 0 < L) (hR : 0 ≤ R) (a b : Mom d)
    (hs : ∀ q ∈ s, ‖latticePoint L q.1-a‖ ≤ R ∧ NearLattice L b q.2) :
    (s.card : ℝ) ≤ (2*(L*R)+1)^d*(2*L+1)^d := by
  classical
  let A := Counting.latticeBox (fun i => L*a i) (L*R)
  let B := Counting.latticeBox (fun i => L*b i) L
  have hsub : s ⊆ A ×ˢ B := by
    intro q hq
    apply mem_product.mpr
    exact ⟨(Counting.mem_latticeBox _ _ _).mpr (fun i => coordinate_bound_of_ball hL a q.1 (hs q hq).1 i),
      nearLattice_mem_box hL b q.2 (hs q hq).2⟩
  have hc : (s.card : ℝ) ≤ (A.card : ℝ)*(B.card : ℝ) := by
    exact_mod_cast (by simpa only [card_product] using card_le_card hsub)
  exact hc.trans (mul_le_mul (Counting.card_latticeBox_le _ (mul_nonneg hL.le hR))
    (Counting.card_latticeBox_le _ hL.le) (Nat.cast_nonneg _) (by positivity))

/-- A ball at most two lattice spacings across in radius contains only a
fixed number of first coordinates, leaving at most `O(L^d)` pairs. -/
theorem card_pair_terminal_ball_le {d : ℕ} (s : Finset ((Fin d → ℤ) × (Fin d → ℤ)))
    {L R : ℝ} (hL : 1 ≤ L) (hR : 0 ≤ R) (hscale : L*R ≤ 2) (b : Mom d)
    (hs : ∀ q ∈ s, ‖latticePoint L q.1‖ ≤ R ∧ NearLattice L b q.2) :
    (s.card : ℝ) ≤ 15^d*L^d := by
  have hLp : 0 < L := lt_of_lt_of_le zero_lt_one hL
  have hc := card_pair_balls_le s hLp hR 0 b (by
    intro q hq
    simpa only [sub_zero] using hs q hq)
  have hx : (2*(L*R)+1)^d ≤ (5 : ℝ)^d :=
    pow_le_pow_left₀ (by positivity) (by linarith only [hscale]) d
  have hy : (2*L+1)^d ≤ (3 : ℝ)^d*L^d := by
    rw [← mul_pow]
    exact pow_le_pow_left₀ (by positivity) (by linarith only [hL]) d
  apply hc.trans
  calc
    _ ≤ 5^d*(3^d*L^d) := mul_le_mul hx hy (by positivity) (by positivity)
    _ = _ := by rw [← mul_assoc,← mul_pow]; norm_num

end WaveTurbulence.CountLemmas
