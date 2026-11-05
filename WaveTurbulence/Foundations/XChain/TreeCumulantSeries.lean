/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.XChain.CumulantAbsoluteSeries
public import WaveTurbulence.Foundations.XChain.TreeProductMoments
public import WaveTurbulence.Foundations.XChain.SignedSeries
/-! Literal tree cumulants expand into their decoration series with all interchange bounds proved. -/
public section
namespace WaveTurbulence.Induct
open Finset MeasureTheory
open SysAPI
open scoped ENNReal

theorem cumulant_treeTerms_eq_decoration_series {Ω ι : Type*} [MeasurableSpace Ω] [DecidableEq ι]
    {μ : Measure Ω} [IsFiniteMeasure μ] {d : ℕ} (L γ δ : ℝ) (p : ℕ) (T : ι → TTree)
    (c : Ω → (Fin d → ℤ) → ℂ)
    (hc : ∀ n, ∀ q : ℕ, 1 ≤ q → MemLp (fun ω => c ω n) (q : ℝ≥0∞) μ)
    (hcs : ∀ᵐ ω ∂μ, Summable fun n => ‖c ω n‖)
    (hM : ∀ q : ℕ, 1 ≤ q → MemLp (fun ω => ∑' n, ‖c ω n‖) (q : ℝ≥0∞) μ)
    (t : ι → ℝ) (n : ι → (Fin d → ℤ)) (ζ : ι → ℤˣ) (s : Finset ι) :
    cumulant μ (fun i ω => zpowSign (ζ i) (treeTerm L γ δ p (T i) (c ω) (t i) (n i))) s =
      (∏ i ∈ s, zpowSign (ζ i) (treePrefactor L γ δ d (T i))) *
      ∑' a : (i : ↥s) → TreeDecoration (T i.1) d (n i.1),
        cumulant μ (assignedFamily
          (fun i κ ω => zpowSign (ζ i) (treeSummand L γ δ p (T i) (c ω) (t i) (n i) κ)) s a) s := by
  have he : (fun i ω => zpowSign (ζ i) (treeTerm L γ δ p (T i) (c ω) (t i) (n i))) =
      fun i ω => zpowSign (ζ i) (treePrefactor L γ δ d (T i)) *
        ∑' κ, zpowSign (ζ i) (treeSummand L γ δ p (T i) (c ω) (t i) (n i) κ) := by
    funext i ω
    rw [treeTerm_eq, zpowSign_mul, zpowSign_tsum]
  rw [he, cumulant_mul]
  apply congrArg (fun z : ℂ => (∏ i ∈ s, zpowSign (ζ i) (treePrefactor L γ δ d (T i))) * z)
  apply cumulant_pi_tsum_of_absolute_moments
  · intro J _ a
    have h := memLp_prod_signed_treeSummands L γ δ p (fun i : ↥J => T i.1) c hc
      (fun i => t i.1) (fun i => n i.1) (fun i => ζ i.1) a 1 (by omega)
    simp only [Nat.cast_one] at h
    exact memLp_one_iff_integrable.mp h
  · intro J _
    exact summable_integral_norm_prod_signed_treeSummands L γ δ p (fun i : ↥J => T i.1) c hc hcs hM
      (fun i => t i.1) (fun i => n i.1) (fun i => ζ i.1)

end WaveTurbulence.Induct
