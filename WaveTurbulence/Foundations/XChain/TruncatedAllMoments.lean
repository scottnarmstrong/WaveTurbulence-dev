/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.XChain.TreeRandomMoments
public import WaveTurbulence.Foundations.XChain.TruncatedTreeExpansion
public import WaveTurbulence.Foundations.XChain.AllMomentProducts
/-! Every actual truncated coefficient and signed finite product has all finite moments from the internal l1 invariant. -/
public section
namespace WaveTurbulence.Induct
open Finset MeasureTheory
open scoped ENNReal

theorem memLp_aTr {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsFiniteMeasure μ]
    {d : ℕ} (L γ δ : ℝ) (p N : ℕ) (c : Ω → (Fin d → ℤ) → ℂ)
    (hcm : ∀ n, AEStronglyMeasurable (fun ω => c ω n) μ)
    (hcs : ∀ᵐ ω ∂μ, Summable fun n => ‖c ω n‖)
    (hM : ∀ q : ℕ, 1 ≤ q → MemLp (fun ω => ∑' n, ‖c ω n‖) (q : ℝ≥0∞) μ)
    (t : ℝ) (n : Fin d → ℤ) (q : ℕ) (hq : 1 ≤ q) :
    MemLp (fun ω => aTr L γ δ p N (c ω) t n) (q : ℝ≥0∞) μ := by
  have h := memLp_finsetSum (univ : Finset (TrTree N))
    (fun T _ => memLp_treeTerm L γ δ p T.1 c hcm hcs hM t n q hq)
  have he : (fun ω => ∑ T : TrTree N, treeTerm L γ δ p T.1 (c ω) t n) =
      fun ω => aTr L γ δ p N (c ω) t n := by
    funext ω
    exact (aTr_eq_sum_TrTree L γ δ p N (c ω) t n).symm
  rw [← he]
  exact h

theorem memLp_signed_prod_aTr {Ω ι : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsFiniteMeasure μ]
    {d : ℕ} (L γ δ : ℝ) (p N : ℕ) (c : Ω → (Fin d → ℤ) → ℂ)
    (hcm : ∀ n, AEStronglyMeasurable (fun ω => c ω n) μ)
    (hcs : ∀ᵐ ω ∂μ, Summable fun n => ‖c ω n‖)
    (hM : ∀ q : ℕ, 1 ≤ q → MemLp (fun ω => ∑' n, ‖c ω n‖) (q : ℝ≥0∞) μ)
    (t : ℝ) (sig : ι → ℤˣ) (n : ι → (Fin d → ℤ)) (s : Finset ι) (q : ℕ) (hq : 1 ≤ q) :
    MemLp (fun ω => ∏ j ∈ s, zpowSign (sig j) (aTr L γ δ p N (c ω) t (n j))) (q : ℝ≥0∞) μ := by
  apply memLp_prod_of_all_memLp
  · intro j _ r hr
    have h := memLp_aTr L γ δ p N c hcm hcs hM t (n j) r hr
    unfold zpowSign
    split_ifs
    · exact h
    · exact h.star
  · exact hq

end WaveTurbulence.Induct
