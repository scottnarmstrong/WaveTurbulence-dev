/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Analysis.CausalIntegrationTree

/-!
# Feasible endpoints for gapped time integrals

A causal tree on the unit time interval either vanishes or agrees with
the cutoff analytic tree whose lower endpoints are the feasible thresholds.
This proves the endpoint substitution needed for nonnegative source gaps.
-/

public section

open MeasureTheory Set

namespace WaveTurbulence.Analysis.IntegrationTree

/-- Replace every auxiliary lower endpoint by its feasible threshold. -/
@[expose] def withThresholds : IntegrationTree → IntegrationTree
  | .leaf => .leaf
  | T@(.node _ α σ₁ σ₂ σ₃ l m r) =>
      .node T.threshold α σ₁ σ₂ σ₃ l.withThresholds m.withThresholds r.withThresholds

private theorem edge_threshold_le (a α σ₁ σ₂ σ₃ : ℝ) (l m r : IntegrationTree) :
    σ₁ + l.threshold ≤ (node a α σ₁ σ₂ σ₃ l m r).threshold ∧
    σ₂ + m.threshold ≤ (node a α σ₁ σ₂ σ₃ l m r).threshold ∧
    σ₃ + r.threshold ≤ (node a α σ₁ σ₂ σ₃ l m r).threshold := by
  change σ₁ + l.threshold ≤ max 0 (max (σ₁ + l.threshold) (max (σ₂ + m.threshold) (σ₃ + r.threshold))) ∧
    σ₂ + m.threshold ≤ max 0 (max (σ₁ + l.threshold) (max (σ₂ + m.threshold) (σ₃ + r.threshold))) ∧
    σ₃ + r.threshold ≤ max 0 (max (σ₁ + l.threshold) (max (σ₂ + m.threshold) (σ₃ + r.threshold)))
  exact ⟨(le_max_left _ _).trans (le_max_right _ _),
    (le_max_left _ _).trans ((le_max_right _ _).trans (le_max_right _ _)),
    (le_max_right _ _).trans ((le_max_right _ _).trans (le_max_right _ _))⟩

/-- Feasibility at the root puts every lower endpoint in `[0,1]`. -/
theorem admissible_withThresholds (T : IntegrationTree) (h : T.ValidGaps)
    (ht : T.threshold ≤ 1) : T.withThresholds.Admissible := by
  induction T with
  | leaf => trivial
  | node a α σ₁ σ₂ σ₃ l m r hl hm hr =>
      have he := edge_threshold_le a α σ₁ σ₂ σ₃ l m r
      exact ⟨⟨threshold_nonneg _, ht⟩,
        hl h.2.2.2.1 (by linarith [h.1.1, he.1]),
        hm h.2.2.2.2.1 (by linarith [h.2.1.1, he.2.1]),
        hr h.2.2.2.2.2 (by linarith [h.2.2.1.1, he.2.2])⟩

/-- On feasible times, the actual causal iterated integral agrees with
its constructed cutoff representation. The cutoff is only assumed to
be one on the source time interval; no spectral premise occurs here. -/
theorem causalValue_eq_value_withThresholds {χ : ℝ → ℂ}
    (hχ : ∀ t ∈ Icc (0 : ℝ) 1, χ t = 1) (T : IntegrationTree) (h : T.ValidGaps)
    {t : ℝ} (ht : t ∈ Icc T.threshold 1) :
    T.causalValue t = T.withThresholds.value χ t := by
  induction T generalizing t with
  | leaf => exact (hχ t ht).symm
  | node a α σ₁ σ₂ σ₃ l m r hl hm hr =>
      let T := node a α σ₁ σ₂ σ₃ l m r
      have hn : 0 ≤ T.threshold := threshold_nonneg T
      have ht0 : 0 ≤ t := hn.trans ht.1
      have he := edge_threshold_le a α σ₁ σ₂ σ₃ l m r
      let F : ℝ → ℂ := fun s => timePhase α s *
        ((l.causalValue (s - σ₁) * m.causalValue (s - σ₂)) * r.causalValue (s - σ₃))
      have hc : Continuous F := (contDiff_timePhase α).continuous.mul
        ((((continuous_causalValue l).comp (continuous_id.sub continuous_const)).mul
          ((continuous_causalValue m).comp (continuous_id.sub continuous_const))).mul
            ((continuous_causalValue r).comp (continuous_id.sub continuous_const)))
      have hz : (∫ s in (0 : ℝ)..T.threshold, F s) = 0 := by
        have hh := causalValue_eq_zero_of_le_threshold T h (by change node a α σ₁ σ₂ σ₃ l m r ≠ leaf; intro hh; cases hh) T.threshold le_rfl
        simpa only [T, causalValue, max_eq_right hn] using hh
      have hsplt := intervalIntegral.integral_add_adjacent_intervals
        (hc.intervalIntegrable (μ := volume) 0 T.threshold) (hc.intervalIntegrable (μ := volume) T.threshold t)
      rw [hz, zero_add] at hsplt
      change (∫ s in (0 : ℝ)..max 0 t, F s) = _
      rw [max_eq_right ht0, ← hsplt]
      change (∫ s in T.threshold..t, F s) = χ t * _
      rw [hχ t ⟨ht0, ht.2⟩, one_mul]
      apply intervalIntegral.integral_congr
      intro s hs
      rw [uIcc_of_le ht.1] at hs
      have hl' : s - σ₁ ∈ Icc l.threshold 1 :=
        ⟨by linarith [hs.1, he.1], by linarith [hs.2, ht.2, h.1.1]⟩
      have hm' : s - σ₂ ∈ Icc m.threshold 1 :=
        ⟨by linarith [hs.1, he.2.1], by linarith [hs.2, ht.2, h.2.1.1]⟩
      have hr' : s - σ₃ ∈ Icc r.threshold 1 :=
        ⟨by linarith [hs.1, he.2.2], by linarith [hs.2, ht.2, h.2.2.1.1]⟩
      dsimp only [F]
      rw [hl h.2.2.2.1 hl', hm h.2.2.2.2.1 hm', hr h.2.2.2.2.2 hr']

end WaveTurbulence.Analysis.IntegrationTree
