/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.XChain.TreeRandomSummands
public import WaveTurbulence.Foundations.XChain.FiniteProductEnvelope
public import WaveTurbulence.Foundations.XChain.SummableMomentEnvelope
public import WaveTurbulence.Foundations.XChain.AllMomentPowers
/-! Absolute block moments of the actual signed decoration summands are summable. -/
public section
namespace WaveTurbulence.Induct
open Finset MeasureTheory
open SysAPI
open scoped ENNReal

theorem memLp_prod_signed_treeSummands {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι]
    {μ : Measure Ω} [IsFiniteMeasure μ] {d : ℕ} (L γ δ : ℝ) (p : ℕ) (T : ι → TTree)
    (c : Ω → (Fin d → ℤ) → ℂ)
    (hc : ∀ n, ∀ q : ℕ, 1 ≤ q → MemLp (fun ω => c ω n) (q : ℝ≥0∞) μ)
    (t : ι → ℝ) (n : ι → (Fin d → ℤ)) (ζ : ι → ℤˣ)
    (a : (i : ι) → TreeDecoration (T i) d (n i)) (q : ℕ) (hq : 1 ≤ q) :
    MemLp (fun ω => ∏ i, zpowSign (ζ i) (treeSummand L γ δ p (T i) (c ω) (t i) (n i) (a i)))
      (q : ℝ≥0∞) μ := by
  apply memLp_prod_of_all_memLp
  · intro i _ r hr
    unfold zpowSign
    split_ifs
    · exact memLp_treeSummand L γ δ p (T i) c hc (t i) (n i) (a i) r hr
    · exact (memLp_treeSummand L γ δ p (T i) c hc (t i) (n i) (a i) r hr).star
  · exact hq

theorem sum_norm_prod_signed_treeSummands_le {ι : Type*} [Fintype ι] {d : ℕ}
    (L γ δ : ℝ) (p : ℕ) (T : ι → TTree) {c : (Fin d → ℤ) → ℂ}
    (hc : Summable fun n => ‖c n‖) (t : ι → ℝ) (n : ι → (Fin d → ℤ)) (ζ : ι → ℤˣ)
    (u : Finset ((i : ι) → TreeDecoration (T i) d (n i))) :
    (∑ a ∈ u, ‖∏ i, zpowSign (ζ i) (treeSummand L γ δ p (T i) c (t i) (n i) (a i))‖) ≤
      (∏ i, boxVol (T i) p (t i)) *
        (∑' m, ‖c m‖) ^ (∑ i, Fintype.card (GLeaf (single (T i)))) := by
  simp_rw [norm_prod, norm_zpowSign]
  have h := sum_prod_le_prod_finite_sum_bounds
    (fun i a => ‖treeSummand L γ δ p (T i) c (t i) (n i) a‖)
    (fun _ _ => norm_nonneg _)
    (fun i => boxVol (T i) p (t i) * (∑' m, ‖c m‖) ^ Fintype.card (GLeaf (single (T i))))
    (fun i v => sum_norm_treeSummand_le_l1 L γ δ p (T i) hc (t i) (n i) v) u
  rw [prod_mul_distrib, prod_pow_eq_pow_sum] at h
  exact h

theorem summable_integral_norm_prod_signed_treeSummands {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι]
    {μ : Measure Ω} [IsFiniteMeasure μ] {d : ℕ} (L γ δ : ℝ) (p : ℕ) (T : ι → TTree)
    (c : Ω → (Fin d → ℤ) → ℂ)
    (hc : ∀ n, ∀ q : ℕ, 1 ≤ q → MemLp (fun ω => c ω n) (q : ℝ≥0∞) μ)
    (hcs : ∀ᵐ ω ∂μ, Summable fun n => ‖c ω n‖)
    (hM : ∀ q : ℕ, 1 ≤ q → MemLp (fun ω => ∑' n, ‖c ω n‖) (q : ℝ≥0∞) μ)
    (t : ι → ℝ) (n : ι → (Fin d → ℤ)) (ζ : ι → ℤˣ) :
    Summable (fun a : (i : ι) → TreeDecoration (T i) d (n i) =>
      ∫ ω, ‖∏ i, zpowSign (ζ i) (treeSummand L γ δ p (T i) (c ω) (t i) (n i) (a i))‖ ∂μ) := by
  let M : Ω → ℝ := fun ω => (∏ i, boxVol (T i) p (t i)) *
    (∑' n, ‖c ω n‖) ^ (∑ i, Fintype.card (GLeaf (single (T i))))
  have hMI : Integrable M μ := by
    have hpow := memLp_pow_of_all (fun ω => ∑' n, ‖c ω n‖) hM
      (fun ω => tsum_nonneg (fun n => norm_nonneg _))
      (∑ i, Fintype.card (GLeaf (single (T i)))) 1 (by omega)
    simp only [Nat.cast_one] at hpow
    exact (memLp_one_iff_integrable.mp hpow).const_mul _
  apply summable_integral_norm_of_finite_sum_bound μ _
    (fun a => by
      have h := memLp_prod_signed_treeSummands L γ δ p T c hc t n ζ a 1 (by omega)
      simp only [Nat.cast_one] at h
      exact memLp_one_iff_integrable.mp h) M hMI
  intro u
  exact hcs.mono (fun ω hω => sum_norm_prod_signed_treeSummands_le L γ δ p T hω t n ζ u)

end WaveTurbulence.Induct
