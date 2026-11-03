/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Analysis.IntegrationTree
public import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
# Causal iterated integrals and feasible lower endpoints

The causal integral clips every upper endpoint at zero. A shifted child
therefore contributes zero when its available time is negative. The
feasible lower endpoint at a vertex is the maximum of zero and the three
shifted child endpoints; leaf edges have no gap and no integration variable.
-/

public section

open MeasureTheory Set

namespace WaveTurbulence.Analysis.IntegrationTree

/-- The actual causal iterated integral. The auxiliary lower-endpoint
labels of `IntegrationTree` are ignored by this definition. -/
@[expose] noncomputable def causalValue : IntegrationTree → ℝ → ℂ
  | .leaf, _ => 1
  | .node _ α σ₁ σ₂ σ₃ l m r, t =>
      ∫ s in (0 : ℝ)..max 0 t, timePhase α s *
        ((l.causalValue (s - σ₁) * m.causalValue (s - σ₂)) * r.causalValue (s - σ₃))

/-- Earliest feasible parent time at a branch. -/
@[expose] def threshold : IntegrationTree → ℝ
  | .leaf => 0
  | .node _ _ σ₁ σ₂ σ₃ l m r =>
      max 0 (max (σ₁ + l.threshold) (max (σ₂ + m.threshold) (σ₃ + r.threshold)))

/-- Source gaps are nonnegative, and leaf edges carry no gap. -/
@[expose] def ValidGaps : IntegrationTree → Prop
  | .leaf => True
  | .node _ _ σ₁ σ₂ σ₃ l m r =>
      (0 ≤ σ₁ ∧ (l = .leaf → σ₁ = 0)) ∧
      (0 ≤ σ₂ ∧ (m = .leaf → σ₂ = 0)) ∧
      (0 ≤ σ₃ ∧ (r = .leaf → σ₃ = 0)) ∧
      l.ValidGaps ∧ m.ValidGaps ∧ r.ValidGaps

theorem threshold_nonneg (T : IntegrationTree) : 0 ≤ T.threshold := by
  cases T with
  | leaf => exact le_rfl
  | node => exact le_max_left _ _

/-- Causal iterated integrals are continuous, so every finite time integral
used in their recursive definition is integrable. -/
theorem continuous_causalValue (T : IntegrationTree) : Continuous T.causalValue := by
  induction T with
  | leaf => exact continuous_const
  | node a α σ₁ σ₂ σ₃ l m r hl hm hr =>
      have hc : Continuous (fun s : ℝ => timePhase α s *
          ((l.causalValue (s - σ₁) * m.causalValue (s - σ₂)) * r.causalValue (s - σ₃))) :=
        (contDiff_timePhase α).continuous.mul
          (((hl.comp (continuous_id.sub continuous_const)).mul
            (hm.comp (continuous_id.sub continuous_const))).mul
              (hr.comp (continuous_id.sub continuous_const)))
      exact (intervalIntegral.continuous_primitive (fun a b => hc.intervalIntegrable a b) 0).comp
        (continuous_const.max continuous_id)

/-- Every branch integral vanishes when it has no positive available time. -/
theorem causalValue_node_eq_zero_of_nonpos (a α σ₁ σ₂ σ₃ : ℝ) (l m r : IntegrationTree)
    {t : ℝ} (ht : t ≤ 0) :
    (node a α σ₁ σ₂ σ₃ l m r).causalValue t = 0 := by
  simp only [causalValue, max_eq_left ht, intervalIntegral.integral_same]

private theorem child_causalValue_eq_zero (T : IntegrationTree) {σ s : ℝ}
    (hleaf : T = .leaf → σ = 0) (hs : 0 < s) (he : s < σ + T.threshold)
    (hz : T ≠ .leaf → ∀ t, t ≤ T.threshold → T.causalValue t = 0) :
    T.causalValue (s - σ) = 0 := by
  by_cases hT : T = .leaf
  · rw [hT, threshold, hleaf hT, add_zero] at he
    exact False.elim ((not_lt_of_ge hs.le) he)
  · exact hz hT _ (by linarith)

/-- A branch vanishes up to its feasible lower endpoint. This fact
justifies replacing zero by that endpoint in its outer time integral. -/
theorem causalValue_eq_zero_of_le_threshold (T : IntegrationTree) (h : T.ValidGaps)
    (hne : T ≠ .leaf) (t : ℝ) (ht : t ≤ T.threshold) : T.causalValue t = 0 := by
  induction T generalizing t with
  | leaf => exact False.elim (hne rfl)
  | node a α σ₁ σ₂ σ₃ l m r hl hm hr =>
      by_cases ht0 : t ≤ 0
      · exact causalValue_node_eq_zero_of_nonpos a α σ₁ σ₂ σ₃ l m r ht0
      have htpos : 0 < t := lt_of_not_ge ht0
      rw [causalValue, max_eq_right htpos.le]
      calc
        _ = ∫ s in (0 : ℝ)..t, (0 : ℂ) := by
          apply intervalIntegral.integral_congr_Ioo_of_le htpos.le
          intro s hs
          have hst : s < (node a α σ₁ σ₂ σ₃ l m r).threshold := hs.2.trans_le ht
          change s < max 0 (max (σ₁ + l.threshold) (max (σ₂ + m.threshold) (σ₃ + r.threshold))) at hst
          have he := (lt_max_iff.mp hst).resolve_left (not_lt_of_ge hs.1.le)
          rcases lt_max_iff.mp he with he | he
          · have hz := child_causalValue_eq_zero l h.1.2 hs.1 he
              (fun hne u hu => hl h.2.2.2.1 hne u hu)
            simp only [hz, zero_mul, mul_zero]
          · rcases lt_max_iff.mp he with he | he
            · have hz := child_causalValue_eq_zero m h.2.1.2 hs.1 he
                (fun hne u hu => hm h.2.2.2.2.1 hne u hu)
              simp only [hz, mul_zero, zero_mul]
            · have hz := child_causalValue_eq_zero r h.2.2.1.2 hs.1 he
                (fun hne u hu => hr h.2.2.2.2.2 hne u hu)
              simp only [hz, mul_zero]
        _ = 0 := intervalIntegral.integral_zero

end WaveTurbulence.Analysis.IntegrationTree
