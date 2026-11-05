/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.XChain.FixedpointAnalyticStep
public import WaveTurbulence.Foundations.XChain.FixedpointBoundedExtension
public import WaveTurbulence.Foundations.XChain.MeasurableExtension
public import WaveTurbulence.Foundations.XChain.SolutionMomentIntegrability
/-! The analytic S1 step: one symmetric event, measurable extension, actual pointwise remainder and all moments. -/
public section
namespace WaveTurbulence.Induct
open MeasureTheory ProbabilityTheory Set
universe u

/-- The entire analytic extension is derived from fixedpoint and the approved rapid-data base
reading. The remaining probability absorption and cumulant estimates are separate steps. -/
theorem fixedpoint_bounded_analytic_step (P : WTParams) (hF : FixedpointBody.{u} P)
    (hd : 1 ≤ P.d) (hL : 0 < P.L) (hφ : ∀ k, 0 ≤ P.φin k)
    (Ω : Type u) [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (g : (Fin P.d → ℤ) → Ω → ℂ) (hG : IsGaussianData μ g)
    (p : ℕ) (hp : p < P.D)
    (a : Ω → ℝ → (Fin P.d → ℤ) → ℂ) (Fev : ℕ → Set Ω)
    (R : ℕ → Mom P.d → ℝ) (E : ℕ → (Fin P.d → ℤ) → ℝ)
    (Et : ℕ → (m : ℕ) → (Fin (2 * m) → ℤˣ) → (Fin (2 * m) → (Fin P.d → ℤ)) → ℂ)
    (hA : ∀ q ≤ p, AnsatzAt P μ g a Fev R E Et q)
    (hbase : ∀ ω ∈ Fev 0, IsRapidDecay (initialCoeff P.L P.φin g ω)) :
    ∃ (F' : Set Ω) (A : Ω → ℝ → (Fin P.d → ℤ) → ℂ),
      F' ⊆ Fev p ∧ MeasurableSet F' ∧ IsSymmetricEvent P.L P.φin g F' ∧
      μ.real (Fev p \ F') ≤ Real.exp (-(4 * P.N (p + 1) : ℝ)) ∧
      1 - Real.exp (-(P.N p : ℝ)) - Real.exp (-(4 * P.N (p + 1) : ℝ)) ≤ μ.real F' ∧
      (∀ ω t, t ≤ (p : ℝ) → A ω t = a ω t) ∧
      (∀ t ∈ Icc (0 : ℝ) (p + 1), ∀ n, Measurable fun ω => A ω t n) ∧
      (∀ ω ∈ F', IsASolution P.L P.γ P.δ (p + 1) (initialCoeff P.L P.φin g ω) (A ω) ∧
        ∀ b, IsASolution P.L P.γ P.δ (p + 1) (initialCoeff P.L P.φin g ω) b →
          ∀ t ∈ Icc (0 : ℝ) (p + 1), b t = A ω t) ∧
      (∀ ω ∈ F',
        (∀ t ∈ Icc (p : ℝ) (p + 1), ∀ n,
          ‖aTr P.L P.γ P.δ p (P.N (p + 1)) (a ω p) t n‖ ≤
            jbr (latticePoint P.L n) ^ (-(3 / 2 * P.Lambda (p + 1) : ℝ)) *
              Real.exp (3 * P.N (p + 1))) ∧
        ∀ t ∈ Icc (p : ℝ) (p + 1), ∀ n,
          ‖A ω t n - aTr P.L P.γ P.δ p (P.N (p + 1)) (a ω p) t n‖ ≤
            jbr (latticePoint P.L n) ^ (-(5 / 4 * P.Lambda (p + 1) : ℝ)) *
              Real.exp (-(10 * P.N (p + 1) : ℝ))) ∧
      ∀ (r : ℕ) (t : Fin r → Icc (0 : ℝ) (p + 1))
        (n : Fin r → (Fin P.d → ℤ)) (ζ : Fin r → ℤˣ),
        Integrable (fun ω => ∏ j, zpowSign (ζ j) (A ω (t j) (n j))) (μ.restrict F') := by
  obtain ⟨F', hsub, hmeas, hsym, hprob, hpoint⟩ :=
    fixedpoint_gate_bounded_solution_extension P hF hd hL Ω μ g hG p hp a Fev R E Et hA
  have hzero : Fev p ⊆ Fev 0 := nested_event_subset_zero Fev p
    (fun q hq hq1 => SysAPI.AnsatzAt.nested (hA q hq) hq1)
  have hrapid : ∀ ω ∈ F', IsRapidDecay (initialCoeff P.L P.φin g ω) :=
    fun ω hω => hbase ω (hzero (hsub hω))
  obtain ⟨A, hhist, hmeasA, hsol⟩ := exists_measurable_solution_extension hL P.φin hG.1 F' hmeas a
    (fun t ht n => SysAPI.AnsatzAt.measurable (hA p le_rfl) ht n) hrapid
    (fun ω hω => by obtain ⟨_, B, hb, hhist, _⟩ := hpoint ω hω; exact ⟨B, hb, hhist⟩)
  have hmeasure := measureReal_sdiff (μ := μ) hsub hmeas
  have hprev := SysAPI.AnsatzAt.prob_ge (hA p le_rfl)
  have hlaw (n : Fin P.d → ℤ) : HasLaw (g n) stdComplexGaussian μ :=
    ⟨(hG.1 n).aemeasurable, hG.2.2 n⟩
  refine ⟨F', A, hsub, hmeas, hsym, hprob, by linarith, hhist, hmeasA,
    fun ω hω => ⟨hsol ω hω, fun b hb => SysAPI.IsASolution.unique hL hb (hsol ω hω)⟩, ?_, ?_⟩
  · intro ω hω
    obtain ⟨htr, B, hB, _, herr⟩ := hpoint ω hω
    refine ⟨htr, fun t ht n => ?_⟩
    have he := SysAPI.IsASolution.unique hL (hsol ω hω) hB t
      (show t ∈ Icc (0 : ℝ) (p + 1) from ⟨(Nat.cast_nonneg p).trans ht.1, ht.2⟩)
    rw [he]
    exact herr t ht n
  · exact integrable_signed_prod_of_solutions hL P.φin hφ g hlaw F' hmeas A hsol hmeasA

end WaveTurbulence.Induct
