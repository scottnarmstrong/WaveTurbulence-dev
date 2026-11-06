/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.Spine.CoherentParameterSlack
/-! Simultaneous final large-L choices for all coherent stages, with reserve for the three-way sum. -/
public section
set_option autoImplicit false
namespace WaveTurbulence.LGSpine
open WaveTurbulence.Induct
open Filter

theorem eventually_coherent_stage_thresholds (P : WTParams) (hη : 0 < P.η)
    {a C : ℝ} (ha : 2 * P.η ^ 20 < a)
    (H : Fin P.D → ℝ) (hH : ∀ p, 0 ≤ H p) :
    ∀ᶠ L : ℝ in atTop, 2 ≤ L ∧ C ≤ L ∧ ∀ p : Fin P.D,
      H p ≤ L ∧
      2 * (((3 * P.theta (p.1 + 1) + 2 * P.theta p.1) / 5 + 1) + 1) + 1 ≤ Real.log L ∧
      H p * (L ^ (-a) + L ^ (-P.theta p.1)) ≤
        L ^ (-((3 * P.theta (p.1 + 1) + 2 * P.theta p.1) / 5)) ∧
      3 * L ^ (-((3 * P.theta (p.1 + 1) + 2 * P.theta p.1) / 5)) ≤
        L ^ (-((4 * P.theta (p.1 + 1) + P.theta p.1) / 5)) := by
  have hp (p : Fin P.D) : ∀ᶠ L : ℝ in atTop,
      H p ≤ L ∧
      2 * (((3 * P.theta (p.1 + 1) + 2 * P.theta p.1) / 5 + 1) + 1) + 1 ≤ Real.log L ∧
      H p * (L ^ (-a) + L ^ (-P.theta p.1)) ≤
        L ^ (-((3 * P.theta (p.1 + 1) + 2 * P.theta p.1) / 5)) ∧
      3 * L ^ (-((3 * P.theta (p.1 + 1) + 2 * P.theta p.1) / 5)) ≤
        L ^ (-((4 * P.theta (p.1 + 1) + P.theta p.1) / 5)) := by
    have hs := theta_step_lt P hη p.1
    have h₀ := theta_le_two_eta_pow P p.1
    have h₁ := theta_le_two_eta_pow P (p.1 + 1)
    have hdec := eventually_fixed_cost_two_decays (hH p)
      (a := a) (c := P.theta p.1) (b := (3 * P.theta (p.1 + 1) + 2 * P.theta p.1) / 5)
      (by linarith) (by linarith)
    have hsum := CountLemmas.eventually_monomial_log_le
      (a := -((3 * P.theta (p.1 + 1) + 2 * P.theta p.1) / 5))
      (b := -((4 * P.theta (p.1 + 1) + P.theta p.1) / 5))
      (C := 3) (by linarith) (by norm_num) 0
    have hlog := Real.tendsto_log_atTop.eventually (eventually_ge_atTop
      (2 * (((3 * P.theta (p.1 + 1) + 2 * P.theta p.1) / 5 + 1) + 1) + 1))
    filter_upwards [eventually_ge_atTop (H p), hlog, hdec, hsum] with L hL hl hd hh
    exact ⟨hL, hl, hd, by simpa only [pow_zero, mul_one] using hh⟩
  filter_upwards [eventually_ge_atTop (2 : ℝ), eventually_ge_atTop C,
    Filter.eventually_all.mpr hp] with L hL hC hp
  exact ⟨hL, hC, hp⟩

end WaveTurbulence.LGSpine
