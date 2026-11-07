/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.Spine.IncoherentAssembly
/-! FLOWER-REG: the large-`L` thresholds of the regular-couple leg (finitely many conditions, one per stage). -/
@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.FlowerReg
open Filter Topology
open WaveTurbulence.LGSpine

theorem eventually_regular_thresholds {a e : ℝ} (ha : 0 < a) (he : 0 < e) (D : ℕ)
    (H G : Fin D → ℝ) :
    ∀ᶠ L : ℝ in atTop, 2 ≤ L ∧ (∀ p : Fin D, H p * L ^ (-a) ≤ 1) ∧ (∀ p : Fin D, G p ≤ L ^ e) ∧
      ∀ p ≤ D, (2 : ℝ) ^ (9 * p) * L ^ (-a) ≤ 1 / 2 := by
  have h1 : ∀ᶠ L : ℝ in atTop, 2 ≤ L := eventually_ge_atTop 2
  have h2 : ∀ᶠ L : ℝ in atTop, ∀ p : Fin D, H p * L ^ (-a) ≤ 1 := by
    rw [Filter.eventually_all]
    intro p
    have hlim : Tendsto (fun L : ℝ => H p * L ^ (-a)) atTop (𝓝 0) := by
      simpa only [mul_zero] using (tendsto_rpow_neg_atTop ha).const_mul (H p)
    exact hlim.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1)) |>.mono fun _ h => h.le
  have h3 : ∀ᶠ L : ℝ in atTop, ∀ p : Fin D, G p ≤ L ^ e := by
    rw [Filter.eventually_all]
    intro p
    exact (tendsto_rpow_atTop he).eventually_ge_atTop (G p)
  have h4 := eventually_uniform_incoherent_ratio D ha
  filter_upwards [h1, h2, h3, h4] with L hL1 hL2 hL3 hL4
  exact ⟨hL1, hL2, hL3, hL4⟩

end WaveTurbulence.FlowerReg
