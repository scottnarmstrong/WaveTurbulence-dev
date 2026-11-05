/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.XChain.SolutionMomentIntegrability
public import Mathlib.Topology.Order.DenselyOrdered
/-! Dominated continuity extends the intermediate variance estimate to the left endpoint. -/
public section
namespace WaveTurbulence.Induct
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

theorem continuousOn_solution_variance {d : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {L γ δ T : ℝ} (hL : 0 < L)
    (φ : SchwartzMap (Mom d) ℝ) (hφ : ∀ k, 0 ≤ φ k)
    (g : (Fin d → ℤ) → Ω → ℂ) (hg : ∀ n, HasLaw (g n) stdComplexGaussian μ)
    (F : Set Ω) (hF : MeasurableSet F) (a : Ω → ℝ → (Fin d → ℤ) → ℂ)
    (ha : ∀ ω ∈ F, IsASolution L γ δ T (initialCoeff L φ g ω) (a ω))
    (hmeas : ∀ t ∈ Icc 0 T, ∀ n, Measurable fun ω => a ω t n) (n : Fin d → ℤ) :
    ContinuousOn (fun t => ∫ ω in F, ‖a ω t n‖ ^ 2 ∂μ) (Icc 0 T) := by
  let mass := fun ω => ∑' m, φ (latticePoint L m) * ‖g m ω‖ ^ 2
  have hm : MemLp mass (1 : ℝ≥0∞) μ := by
    simpa only [Nat.cast_one] using memLp_gaussian_mass g hg _ (fun k => hφ _)
      (MainGlue.summable_schwartz_lattice φ hL) 1 le_rfl
  apply continuousOn_of_dominated (bound := mass)
  · intro t ht
    exact ((hmeas t ht n).norm.pow_const 2).aestronglyMeasurable
  · intro t ht
    filter_upwards [ae_restrict_mem hF] with ω hω
    rw [Real.norm_of_nonneg (sq_nonneg _)]
    have h := solution_norm_sq_le_initial_mass hL (ha ω hω) ht n
    have he : (∑' m, ‖initialCoeff L φ g ω m‖ ^ 2) = mass ω := by
      apply tsum_congr
      intro m
      rw [initialCoeff, norm_mul, mul_pow, Complex.norm_real,
        Real.norm_of_nonneg (Real.sqrt_nonneg _), Real.sq_sqrt (hφ _)]
    exact h.trans_eq he
  · exact (hm.integrable le_rfl).restrict
  · filter_upwards [ae_restrict_mem hF] with ω hω
    exact (SysAPI.IsASolution.continuousOn (ha ω hω) n).norm.pow 2

end WaveTurbulence.Induct
