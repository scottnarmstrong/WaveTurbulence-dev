/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.WeylSums.IntegralCoverBound
public import Mathlib.Analysis.SpecificLimits.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Algebra.Order.Archimedean.Basic

/-! # Summing weighted time tails from cumulative interval bounds -/

public section
open MeasureTheory Set
namespace WaveTurbulence.WeylSums

/-- A cumulative power bound and geometric decay on dyadic annuli imply a
weighted integral bound. The measure may already be restricted to minor arcs. -/
theorem dyadic_weighted_integral_bound (μ : Measure ℝ) (g w : ℝ → ℝ)
    (hg : ∀ s, 0 ≤ g s) (hw : ∀ s, 0 ≤ w s) (hmw : Measurable w)
    (B K r a : ℝ) (hB : 0 < B) (hK : 0 ≤ K) (ha : 0 ≤ a)
    (hq : a*(2 : ℝ)^r < 1)
    (hi : ∀ U : ℝ, 0 < U → IntegrableOn g {s : ℝ | |s| ≤ U} μ)
    (hb : ∀ U : ℝ, 0 < U → (∫ s in {s : ℝ | |s| ≤ U}, g s ∂μ) ≤ K*U^r)
    (hwone : ∀ s, w s ≤ 1)
    (hwdecay : ∀ n : ℕ, ∀ s : ℝ, B*(2 : ℝ)^n ≤ |s| → w s ≤ a^n) :
    Integrable (fun s => w s*g s) μ ∧
      (∫ s, w s*g s ∂μ) ≤ K*B^r*(1+(2 : ℝ)^r/(1-a*(2 : ℝ)^r)) := by
  let q := a*(2 : ℝ)^r
  have hq0 : 0 ≤ q := by dsimp [q]; positivity
  let S : ℕ → Set ℝ
    | 0 => {s | |s| ≤ B}
    | n+1 => {s | B*(2 : ℝ)^n ≤ |s| ∧ |s| ≤ B*(2 : ℝ)^(n+1)}
  let b : ℕ → ℝ
    | 0 => K*B^r
    | n+1 => K*B^r*(2 : ℝ)^r*q^n
  have hcover : (⋃ n, S n) = univ := by
    apply eq_univ_of_forall
    intro s
    by_cases hs : |s| ≤ B
    · exact mem_iUnion.mpr ⟨0,hs⟩
    · have hsB : 1 ≤ |s|/B := (le_div_iff₀ hB).mpr (by linarith)
      obtain ⟨n,hlo,hhi⟩ := exists_nat_pow_near hsB (by norm_num : (1 : ℝ) < 2)
      apply mem_iUnion.mpr
      refine ⟨n+1,?_,?_⟩
      · have hh := (le_div_iff₀ hB).mp hlo
        nlinarith only [hh]
      · have hh := (div_lt_iff₀ hB).mp hhi
        nlinarith only [hh]
  have hbn (n : ℕ) : 0 ≤ b n := by cases n <;> dsimp [b] <;> positivity
  have hbs : Summable b := by
    apply (summable_nat_add_iff 1).mp
    exact (summable_geometric_of_lt_one hq0 hq).mul_left (K*B^r*(2 : ℝ)^r)
  have hlocal (n : ℕ) : IntegrableOn (fun s => w s*g s) (S n) μ ∧
      (∫ s in S n, w s*g s ∂μ) ≤ b n := by
    cases n with
    | zero =>
      have hgi := hi B hB
      have hwi : IntegrableOn (fun s => w s*g s) (S 0) μ := by
        apply hgi.mono' (hmw.aestronglyMeasurable.mul hgi.aestronglyMeasurable)
        filter_upwards [] with s
        change ‖w s*g s‖ ≤ _
        rw [Real.norm_of_nonneg (mul_nonneg (hw s) (hg s))]
        exact mul_le_of_le_one_left (hg s) (hwone s)
      refine ⟨hwi,?_⟩
      exact (integral_mono_ae hwi hgi (Filter.Eventually.of_forall
        (fun s => mul_le_of_le_one_left (hg s) (hwone s)))).trans (hb B hB)
    | succ n =>
      let U := B*(2 : ℝ)^(n+1)
      have hU : 0 < U := by dsimp [U]; positivity
      have hsub : S (n+1) ⊆ {s : ℝ | |s| ≤ U} := fun s hs => hs.2
      have hgi : IntegrableOn g (S (n+1)) μ := (hi U hU).mono_set hsub
      have hpoint : ∀ᵐ s ∂μ.restrict (S (n+1)), w s*g s ≤ a^n*g s := by
        filter_upwards [ae_restrict_mem (by dsimp [S]; measurability)] with s hs
        exact mul_le_mul_of_nonneg_right (hwdecay n s hs.1) (hg s)
      have hwi : IntegrableOn (fun s => w s*g s) (S (n+1)) μ := by
        apply (hgi.const_mul (a^n)).mono' (hmw.aestronglyMeasurable.mul hgi.aestronglyMeasurable)
        filter_upwards [hpoint] with s hs
        change ‖w s*g s‖ ≤ _
        rwa [Real.norm_of_nonneg (mul_nonneg (hw s) (hg s))]
      refine ⟨hwi,?_⟩
      calc
        _ ≤ ∫ s in S (n+1), a^n*g s ∂μ := integral_mono_ae hwi (hgi.const_mul _) hpoint
        _ = a^n * ∫ s in S (n+1), g s ∂μ := integral_const_mul _ _
        _ ≤ a^n*(K*U^r) := mul_le_mul_of_nonneg_left
          ((setIntegral_mono_set (hi U hU) (Filter.Eventually.of_forall hg) (Filter.Eventually.of_forall hsub)).trans (hb U hU))
          (pow_nonneg ha _)
        _ = b (n+1) := by
          dsimp [U,b,q]
          have hp : ((2 : ℝ)^(n+1))^r = ((2 : ℝ)^r)^(n+1) := by
            rw [← Real.rpow_natCast_mul (by norm_num : (0 : ℝ) ≤ 2),
              ← Real.rpow_mul_natCast (by norm_num : (0 : ℝ) ≤ 2)]
            congr 1
            ring
          rw [Real.mul_rpow hB.le (by positivity), hp, pow_succ, mul_pow]
          ring
  obtain ⟨hint,hbound⟩ := integrable_integral_le_of_cover μ (fun s => w s*g s)
    (fun s => mul_nonneg (hw s) (hg s)) S hcover (fun n => (hlocal n).1) b hbn hbs (fun n => (hlocal n).2)
  refine ⟨hint,?_⟩
  have hsum : (∑' n, b n) = K*B^r*(1+(2 : ℝ)^r/(1-q)) := by
    rw [hbs.tsum_eq_zero_add]
    change K*B^r + (∑' n : ℕ, K*B^r*(2 : ℝ)^r*q^n) = _
    rw [tsum_mul_left, tsum_geometric_of_lt_one hq0 hq]
    ring
  exact hbound.trans_eq hsum

end WaveTurbulence.WeylSums
