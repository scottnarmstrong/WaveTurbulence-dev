/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.XChain.PrefixStepQuantitative
public import WaveTurbulence.Foundations.XChain.VarianceEndpoint
/-! The actual next-stage variance bound on the entire closed time interval. -/
public section
namespace WaveTurbulence.Induct
open MeasureTheory Set
universe u

theorem prefix_next_variance_bound {P : WTParams} (H : InductContext.{u} P)
    {Ω : Type u} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (g : (Fin P.d → ℤ) → Ω → ℂ) (hG : IsGaussianData μ g)
    {p : ℕ} (hp : p < P.D) (S : AnsatzPrefixData P μ g p) (T : PrefixExtension S)
    (n : Fin P.d → ℤ) :
    ∀ t ∈ Icc (p : ℝ) (p + 1),
      |(∫ ω in T.F, ‖T.a ω t n‖ ^ 2 ∂μ) - P.φ (P.δ * t) (latticePoint P.L n)| ≤
        2 * P.L ^ (-P.theta (p + 1)) := by
  have hcont := continuousOn_solution_variance (zero_lt_one.trans_le H.L_ge_one) P.φin H.initial_nonneg
    g (fun n => ⟨(hG.1 n).aemeasurable, hG.2.2 n⟩) T.F T.measurable T.a T.solution T.measurable_a n
  have hsub : Icc (p : ℝ) (p + 1) ⊆ Icc (0 : ℝ) (p + 1) :=
    fun _ ht => ⟨(Nat.cast_nonneg p).trans ht.1, ht.2⟩
  have htime : ∀ t ∈ Icc (p : ℝ) (p + 1), P.δ * t ∈ Icc 0 P.τstar := by
    intro t ht
    have hpD : (p : ℝ) + 1 ≤ P.D := by exact_mod_cast (show p + 1 ≤ P.D by omega)
    exact ⟨mul_nonneg H.delta_pos.le ((Nat.cast_nonneg p).trans ht.1),
      (mul_le_mul_of_nonneg_left (ht.2.trans hpD) H.delta_pos.le).trans H.time_range⟩
  have hcurve : ContinuousOn (fun t => P.φ (P.δ * t)) (Icc (p : ℝ) (p + 1)) :=
    H.wke.1.comp (continuous_const.mul continuous_id).continuousOn htime
  have heval : Continuous (fun f : SchwartzMap (Mom P.d) ℝ => f (latticePoint P.L n)) :=
    ((BoundedContinuousFunction.evalCLM ℝ (latticePoint P.L n)).comp
      (SchwartzMap.toBoundedContinuousFunctionCLM ℝ (Mom P.d) ℝ)).continuous
  have hphi : ContinuousOn (fun t => P.φ (P.δ * t) (latticePoint P.L n)) (Icc (p : ℝ) (p + 1)) :=
    heval.comp_continuousOn hcurve
  apply variance_bound_closed_left (hcont.mono hsub) hphi
  intro t ht
  have hw : jbr (latticePoint P.L n) ^ (-(P.Lambda (p + 1) : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (one_le_jbr _) (neg_nonpos.mpr (Nat.cast_nonneg _))
  have herr := prefix_next_variance_error H μ g hG hp S T n t ht
  have herr' : |(∫ ω in T.F, ‖T.a ω t n‖ ^ 2 ∂μ) -
      (P.φ (P.δ * t) (latticePoint P.L n) +
        nextRemainder P S.R p (P.N (p + 1) ^ 4) t (latticePoint P.L n))| ≤ P.L ^ (-P.theta (p + 1)) :=
    herr.trans ((mul_le_of_le_one_left (Real.exp_pos _).le hw).trans (H.exp_le_scale (p + 1)))
  have hnorm := prefix_next_remainder_bound H μ g hp S t ht
  have hpoint := SNormR_pointwise (nextRemainder P S.R p (P.N (p + 1) ^ 4) t)
    (P.L ^ (-P.theta (p + 1))) (Real.rpow_nonneg (zero_le_one.trans H.L_ge_one) _) hnorm (latticePoint P.L n)
  have hpoint' : |nextRemainder P S.R p (P.N (p + 1) ^ 4) t (latticePoint P.L n)| ≤
      P.L ^ (-P.theta (p + 1)) :=
    hpoint.trans (mul_le_of_le_one_right (Real.rpow_nonneg (zero_le_one.trans H.L_ge_one) _) hw)
  exact variance_error_le_remainder_add_error herr' hpoint'

end WaveTurbulence.Induct
