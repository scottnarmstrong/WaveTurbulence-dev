/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.XChain.ZBanach
public import Mathlib.Topology.MetricSpace.Contracting
/-! The Banach contraction step in TARGET S1, in the exact draft ZSpace carriers. -/
public section
namespace WaveTurbulence.Induct
open Set
open scoped ENNReal NNReal BoundedContinuousFunction

/-- The mapping and contraction clauses of fixedpoint imply an actual fixed point in Z.
The relation will be instantiated by the displayed Lop equation, not by an assumed fixed point. -/
theorem exists_Z_fixedPoint {d p : ℕ} (L Λ r : ℝ) (hr : 0 ≤ r)
    (R : (ZTime p → (Fin d → ℤ) → ℂ) → (ZTime p → (Fin d → ℤ) → ℂ) → Prop)
    (hmaps : ∀ b ∈ ZSpace L Λ p, ZNorm L Λ b ≤ ENNReal.ofReal r →
      ∃ c ∈ ZSpace L Λ p, R b c ∧ ZNorm L Λ c ≤ ENNReal.ofReal r)
    (hlip : ∀ b ∈ ZSpace L Λ p, ∀ b' ∈ ZSpace L Λ p,
      ∀ c ∈ ZSpace L Λ p, ∀ c' ∈ ZSpace L Λ p,
      ZNorm L Λ b ≤ ENNReal.ofReal r → ZNorm L Λ b' ≤ ENNReal.ofReal r →
      R b c → R b' c' →
      ZNorm L Λ (c - c') ≤ ENNReal.ofReal (1 / 2) * ZNorm L Λ (b - b')) :
    ∃ b ∈ ZSpace L Λ p, ZNorm L Λ b ≤ ENNReal.ofReal r ∧ R b b := by
  classical
  have hdist (g h : ZModel d p) : dist g h = ‖g - h‖ := dist_eq_norm g h
  let S := Metric.closedBall (0 : ZModel d p) r
  have hS : IsClosed S := Metric.isClosed_closedBall
  let : CompleteSpace S := hS.completeSpace_coe
  let : Nonempty S := ⟨⟨0, by simpa only [S, Metric.mem_closedBall, dist_self] using hr⟩⟩
  have hball (x : S) : ZNorm L Λ (zDecode L Λ x.1) ≤ ENNReal.ofReal r := by
    rw [ZNorm_zDecode, ← ofReal_norm]
    exact ENNReal.ofReal_le_ofReal (by
      simpa only [S, Metric.mem_closedBall, BoundedContinuousFunction.norm_def] using x.2)
  have hex (x : S) := hmaps (zDecode L Λ x.1) (zDecode_mem_ZSpace L Λ x.1) (hball x)
  choose c hcZ hcR hcB using hex
  let Φ : S → S := fun x => ⟨zEncode L Λ (c x) (hcZ x), by
    change dist (zEncode L Λ (c x) (hcZ x)) 0 ≤ r
    rw [← BoundedContinuousFunction.norm_def]
    apply (ENNReal.ofReal_le_ofReal_iff hr).mp
    rw [ofReal_norm, enorm_zEncode]
    exact hcB x⟩
  have hcontract : ContractingWith (1 / 2 : ℝ≥0) Φ := by
    refine ⟨by norm_num, LipschitzWith.of_dist_le_mul ?_⟩
    intro x y
    have h := hlip _ (zDecode_mem_ZSpace L Λ x.1) _ (zDecode_mem_ZSpace L Λ y.1)
      _ (hcZ x) _ (hcZ y) (hball x) (hball y) (hcR x) (hcR y)
    have he : ZNorm L Λ (c x - c y) =
        ‖zEncode L Λ (c x) (hcZ x) - zEncode L Λ (c y) (hcZ y)‖ₑ := by
      rw [← ZNorm_zDecode_sub, zDecode_zEncode, zDecode_zEncode]
    rw [he, ZNorm_zDecode_sub] at h
    change dist (zEncode L Λ (c x) (hcZ x)) (zEncode L Λ (c y) (hcZ y)) ≤
      (1 / 2 : ℝ) * dist x.1 y.1
    rw [hdist, hdist]
    have h0 : (0 : ℝ) ≤ (1 / 2 : ℝ) * ‖x.1 - y.1‖ :=
      mul_nonneg (by norm_num) (norm_nonneg (x.1 - y.1))
    exact (ENNReal.ofReal_le_ofReal_iff h0).mp (by
      rw [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 1 / 2)]
      convert h using 1
      · exact ofReal_norm (zEncode L Λ (c x) (hcZ x) - zEncode L Λ (c y) (hcZ y))
      · exact congrArg (ENNReal.ofReal (1 / 2 : ℝ) * ·) (ofReal_norm (x.1 - y.1)))
  let x : S := ContractingWith.fixedPoint Φ hcontract
  have hx : Φ x = x := ContractingWith.fixedPoint_isFixedPt hcontract
  have hcx : c x = zDecode L Λ x.1 := by
    calc
      _ = zDecode L Λ (Φ x).1 := (zDecode_zEncode L Λ (c x) (hcZ x)).symm
      _ = _ := congrArg (fun y : S => zDecode L Λ y.1) hx
  refine ⟨zDecode L Λ x.1, zDecode_mem_ZSpace L Λ x.1, hball x, ?_⟩
  simpa only [hcx] using hcR x

end WaveTurbulence.Induct
