/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.XChain.InductContext
public import WaveTurbulence.Foundations.XChain.PrefixExtension
public import WaveTurbulence.Foundations.XChain.NextHigherCumulantError
public import WaveTurbulence.Foundations.XChain.NextVarianceError
public import WaveTurbulence.Foundations.XChain.NextOrderBound
/-! Actual quantitative estimates on the single fixedpoint extension, with all side conditions discharged. -/
public section
namespace WaveTurbulence.Induct
open MeasureTheory Set
open scoped ENNReal
universe u

section
variable {P : WTParams} (H : InductContext.{u} P)
    {Ω : Type u} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (g : (Fin P.d → ℤ) → Ω → ℂ) (hG : IsGaussianData μ g)
    {p : ℕ} (hp : p < P.D) (S : AnsatzPrefixData P μ g p) (T : PrefixExtension S)
include H hp

theorem prefix_input_bound : ∀ n, |inputsF P S.R p (latticePoint P.L n)| ≤
    (H.B + 1) * jbr (latticePoint P.L n) ^ (-(P.Lambda p : ℝ)) := by
  have hφ := phi_stage_input_weight P p H.B (zero_le_one.trans H.B_ge_one)
    (H.phi_stage (by omega : p ≤ P.D) ⟨Nat.cast_nonneg p, le_rfl⟩)
  exact fun n => ansatz_inputsF_bracket_bound P μ g S.a S.Fev S.R S.E S.Et p
    (S.ansatz p le_rfl) H.L_ge_one H.B hφ _

theorem prefix_next_remainder_bound (t : ℝ) (ht : t ∈ Ioc (p : ℝ) (p + 1)) :
    SNormR (P.Lambda (p + 1)) (P.Lambda (p + 1))
      (nextRemainder P S.R p (P.N (p + 1) ^ 4) t) ≤ ENNReal.ofReal (P.L ^ (-P.theta (p + 1))) := by
  obtain ⟨hN, _, _, _, hθ, hlog, hA, hgap⟩ := H.sizes.2.2.2 p hp
  exact nextRemainder_ansatz_SNormR_bound P H.layergarden H.taylor S.R p hp S.remainderBound
    H.dimension (zero_lt_one.trans_le H.L_ge_one) H.delta_pos H.C2_nonneg H.geometric_small.2.2.1
    H.taylor_nonneg H.taylor_lt_one H.small_taylor (by omega) hθ hlog hA hgap t ht

include hG

theorem prefix_next_higher_error (m : ℕ) (hm : 2 ≤ m) (hmR : m ≤ P.R (p + 1))
    (sig : Fin (2 * m) → ℤˣ) (hbal : IsBalancedSig sig) (n : Fin (2 * m) → (Fin P.d → ℤ))
    (t : ℝ) (ht : t ∈ Ioc (p : ℝ) (p + 1)) :
    ‖cumulant (μ.restrict T.F) (fun j ω => zpowSign (sig j) (T.a ω t (n j))) Finset.univ -
      ∑ N ∈ Finset.range (P.N (p + 1) + 1), truncSum P (inputsF P S.R) (p + 1) N t sig n‖ ≤
      (∏ j, jbr (latticePoint P.L (n j))) ^ (-(P.Lambda (p + 1) : ℝ)) *
        Real.exp (-(P.N (p + 1) : ℝ)) := by
  obtain ⟨hN, hNd, hΛ, hRs, _, _, _, _⟩ := H.sizes.2.2.2 p hp
  have hrest := (H.remainder_constant hp).trans
    (Real.rpow_le_one_of_one_le_of_nonpos H.L_ge_one (neg_nonpos.mpr (theta_nonneg P _)))
  exact ansatz_next_higher_cumulant_error_bound P μ g hG S.a S.Fev S.R S.E S.Et p (S.ansatz p le_rfl)
    S.rapid_at (S.l1_moments p le_rfl) H.layergarden H.taylor S.remainderBound H.C2_nonneg
    H.taylor_nonneg H.taylor_lt_one H.geometric_small.2.2.1 H.geometric_small.2.1
    H.delta_pos H.geometric_small.1 H.L_ge_one (H.B + 1) (by have h := H.B_ge_one; linarith)
    (prefix_input_bound H μ g hp S) (S.inputs_summable (by omega) H.dimension H.L_ge_one)
    m hm hmR sig hbal n H.dimension hp hN hNd H.L_ge_exp_two H.sizes.2.1 hΛ H.sizes.2.2.1
    H.small_delta H.gamma_le_dimension H.delta_le_one t ht H.B (zero_le_one.trans H.B_ge_one)
    (H.phi_stage (by omega) ⟨(Nat.cast_nonneg p).trans ht.1.le, by simpa only [Nat.cast_add, Nat.cast_one] using ht.2⟩) hrest H.Cmom H.Cmom_ge
    T.F T.measurable T.subset (fun ω => T.a ω t)
    (T.measurable_a t ⟨(Nat.cast_nonneg p).trans ht.1.le, ht.2⟩)
    (fun ω hω n => T.remainder ω hω t ⟨ht.1.le, ht.2⟩ n) T.deleted hRs H.geometric_small.2.2.2

theorem prefix_next_variance_error (n : Fin P.d → ℤ) (t : ℝ) (ht : t ∈ Ioc (p : ℝ) (p + 1)) :
    |(∫ ω in T.F, ‖T.a ω t n‖ ^ 2 ∂μ) -
      (P.φ (P.δ * t) (latticePoint P.L n) +
        nextRemainder P S.R p (P.N (p + 1) ^ 4) t (latticePoint P.L n))| ≤
      jbr (latticePoint P.L n) ^ (-(P.Lambda (p + 1) : ℝ)) * Real.exp (-(P.N (p + 1) : ℝ)) := by
  obtain ⟨hN, hNd, hΛ, hRs, _, _, _, _⟩ := H.sizes.2.2.2 p hp
  have hrest := (H.remainder_constant hp).trans
    (Real.rpow_le_one_of_one_le_of_nonpos H.L_ge_one (neg_nonpos.mpr (theta_nonneg P _)))
  exact ansatz_next_variance_error_bound P μ g hG S.a S.Fev S.R S.E S.Et p (S.ansatz p le_rfl)
    S.rapid_at (S.l1_moments p le_rfl) H.layergarden H.taylor S.remainderBound H.C2_nonneg
    H.taylor_nonneg H.taylor_lt_one H.geometric_small.2.2.1 H.geometric_small.2.1
    H.delta_pos H.geometric_small.1 H.L_ge_one (H.B + 1) (by have h := H.B_ge_one; linarith)
    (prefix_input_bound H μ g hp S) (S.inputs_summable (by omega) H.dimension H.L_ge_one)
    n H.dimension hp hN hNd H.L_ge_exp_two H.sizes.2.1 hΛ H.sizes.2.2.1 H.small_delta
    H.gamma_le_dimension H.delta_le_one t ht H.B (zero_le_one.trans H.B_ge_one)
    (H.phi_stage (by omega) ⟨(Nat.cast_nonneg p).trans ht.1.le, by simpa only [Nat.cast_add, Nat.cast_one] using ht.2⟩) hrest H.Cmom H.Cmom_ge
    T.F T.measurable T.subset T.a T.measurable_a
    (fun ω hω n => T.remainder ω hω t ⟨ht.1.le, ht.2⟩ n) T.deleted hRs T.symmetric T.solution

end
end WaveTurbulence.Induct
