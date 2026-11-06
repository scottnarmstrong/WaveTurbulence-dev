/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.Spine.IncoherentSumBound
public import WaveTurbulence.Foundations.Spine.IncoherentGeometricBound
public import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
/-! The finite source incoherent contribution after code counts, canonical layerings and the g-sum. -/
public section
namespace WaveTurbulence.LGSpine
open WaveTurbulence.Induct
open Set Filter
open scoped Topology

theorem incoherentCoupleSum_geometric (P : WTParams) (hdecay : IncoherentDecayAt P)
    (hd : 1 ≤ P.d) (hL : 1 ≤ P.L) (hη : 0 ≤ P.η) (hC₁ : 0 ≤ P.C₁) (hδ : 0 ≤ P.δ)
    {p n : ℕ} (hp : p < P.D) (R : ℕ → Mom P.d → ℝ) (hR : RemainderBound P R p)
    (hn : n ≤ P.N (p + 1) ^ 4) (t : ℝ) (ht : t ∈ Icc (p : ℝ) (p + 1)) (k : Mom P.d)
    (hr : (2 : ℝ) ^ (9 * p) * P.L ^ (-(P.gamma1 - Real.sqrt P.η)) ≤ 1 / 2) :
    ‖incoherentCoupleSum P (inputsF P R) (p + 1) (2 * n) t k‖ ≤
      2 * P.C₁ * ((12 ^ 9 : ℝ) * 4 * P.C₁ * P.δ) ^ n * (2 : ℝ) ^ (9 * p) *
        P.L ^ (-(P.gamma1 - Real.sqrt P.η)) :=
  (norm_incoherentCoupleSum_le_counted P hdecay hd hL hη hC₁ hδ hp R hR hn t ht k).trans
    (counted_incoherent_sum_le (by linarith : 0 ≤ P.L) hC₁ hδ p n hr)

/-- The ratio condition above follows uniformly in all stages once L is large enough,
with threshold depending on D and the positive decay exponent only. -/
theorem eventually_uniform_incoherent_ratio (D : ℕ) {a : ℝ} (ha : 0 < a) :
    ∀ᶠ L : ℝ in atTop, ∀ p ≤ D, (2 : ℝ) ^ (9 * p) * L ^ (-a) ≤ 1 / 2 := by
  have hlim : Tendsto (fun L : ℝ => (2 : ℝ) ^ (9 * D) * L ^ (-a)) atTop (𝓝 0) := by
    simpa only [mul_zero] using (tendsto_rpow_neg_atTop ha).const_mul ((2 : ℝ) ^ (9 * D))
  have hsmall : ∀ᶠ L : ℝ in atTop, (2 : ℝ) ^ (9 * D) * L ^ (-a) < 1 / 2 :=
    hlim.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1 / 2))
  filter_upwards [hsmall, eventually_ge_atTop (0 : ℝ)] with L hL hL0
  intro p hp
  exact (mul_le_mul_of_nonneg_right
    (pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) (Nat.mul_le_mul_left 9 hp))
    (Real.rpow_nonneg hL0 _)).trans hL.le

end WaveTurbulence.LGSpine
