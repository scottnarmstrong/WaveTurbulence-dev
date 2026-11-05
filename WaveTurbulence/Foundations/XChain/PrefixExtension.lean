/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.XChain.AnsatzPrefixAPI
public import WaveTurbulence.Foundations.XChain.FixedpointBoundedAnalyticStep
public import WaveTurbulence.Foundations.XChain.FixedpointL1Invariant
public import WaveTurbulence.Foundations.XChain.FixedpointFinalWeight
public import WaveTurbulence.Foundations.XChain.InductProbability
/-! One fixedpoint event and one measurable classed solution extension, retaining all internal bounds. -/
@[expose] public section
namespace WaveTurbulence.Induct
open MeasureTheory Set
open scoped ENNReal
universe u

structure PrefixExtension {P : WTParams} {Ω : Type u} [MeasurableSpace Ω]
    {μ : Measure Ω} {g : (Fin P.d → ℤ) → Ω → ℂ} {p : ℕ} (S : AnsatzPrefixData P μ g p) where
  F : Set Ω
  a : Ω → ℝ → (Fin P.d → ℤ) → ℂ
  subset : F ⊆ S.Fev p
  measurable : MeasurableSet F
  symmetric : IsSymmetricEvent P.L P.φin g F
  deleted : μ.real (S.Fev p \ F) ≤ Real.exp (-(4 * P.N (p + 1) : ℝ))
  probability : 1 - Real.exp (-(P.N (p + 1) : ℝ)) ≤ μ.real F
  history : ∀ ω t, t ≤ (p : ℝ) → a ω t = S.a ω t
  measurable_a : ∀ t ∈ Icc (0 : ℝ) (p + 1), ∀ n, Measurable fun ω => a ω t n
  solution : ∀ ω ∈ F, IsASolution P.L P.γ P.δ (p + 1) (initialCoeff P.L P.φin g ω) (a ω)
  unique_solution : ∀ ω ∈ F, ∀ b,
    IsASolution P.L P.γ P.δ (p + 1) (initialCoeff P.L P.φin g ω) b →
      ∀ t ∈ Icc (0 : ℝ) (p + 1), b t = a ω t
  products : ∀ (r : ℕ) (t : Fin r → Icc (0 : ℝ) (p + 1))
    (n : Fin r → (Fin P.d → ℤ)) (sig : Fin r → ℤˣ),
    Integrable (fun ω => ∏ j, zpowSign (sig j) (a ω (t j) (n j))) (μ.restrict F)
  remainder : ∀ ω ∈ F, ∀ t ∈ Icc (p : ℝ) (p + 1), ∀ n,
    ‖a ω t n - aTr P.L P.γ P.δ p (P.N (p + 1)) (S.a ω p) t n‖ ≤
      Real.exp (-(10 * P.N (p + 1) : ℝ)) * jbr (latticePoint P.L n) ^ (-(P.Lambda (p + 1) : ℝ))
  l1_moments : ∀ t ∈ Icc (p : ℝ) (p + 1), ∀ q : ℕ, 1 ≤ q →
    MemLp (fun ω => ∑' n, ‖a ω t n‖) (q : ℝ≥0∞) (μ.restrict F)

theorem exists_prefix_extension (P : WTParams) (hFixed : FixedpointBody.{u} P)
    (hd : 1 ≤ P.d) (hL : Real.exp 2 ≤ P.L) (hφ : ∀ k, 0 ≤ P.φin k)
    {Ω : Type u} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (g : (Fin P.d → ℤ) → Ω → ℂ) (hG : IsGaussianData μ g)
    {p : ℕ} (hp : p < P.D) (S : AnsatzPrefixData P μ g p) : Nonempty (PrefixExtension S) := by
  have hLone : 1 ≤ P.L := (by linarith [Real.add_one_le_exp (2 : ℝ)] : (1 : ℝ) ≤ Real.exp 2).trans hL
  obtain ⟨F, A, hsub, hmeas, hsym, hdel, hprob, hhist, hAm, hsol, hpoint, hprod⟩ :=
    fixedpoint_bounded_analytic_step P hFixed hd (zero_lt_one.trans_le hLone) hφ Ω μ g hG p hp
      S.a S.Fev S.R S.E S.Et S.ansatz S.rapid
  refine ⟨⟨F, A, hsub, hmeas, hsym, hdel, probability_step_lower P hd hL hp hprob,
    hhist, hAm, fun ω hω => (hsol ω hω).1, fun ω hω => (hsol ω hω).2, hprod, ?_, ?_⟩⟩
  · intro ω hω t ht n
    exact fixedpoint_remainder_final_weight _ _ _ (Nat.cast_nonneg _) ((hpoint ω hω).2 t ht n)
  · intro t ht q _hq
    exact fixedpoint_bounds_memLp_l1 P μ F hmeas p hp hd hLone S.a A t
      (hAm t ⟨(Nat.cast_nonneg p).trans ht.1, ht.2⟩)
      (fun ω hω n => (hpoint ω hω).1 t ht n) (fun ω hω n => (hpoint ω hω).2 t ht n) q

end WaveTurbulence.Induct
