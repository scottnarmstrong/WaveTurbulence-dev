/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.XChain.AllMomentProducts
public import WaveTurbulence.Foundations.XChain.AllMomentPowers
public import WaveTurbulence.Foundations.XChain.FiniteProductEnvelope
public import WaveTurbulence.Foundations.XChain.SummableMomentEnvelope
public import WaveTurbulence.Foundations.XChain.SignedSeries
public import WaveTurbulence.Foundations.XChain.SysDraft.Final
/-! Absolute lattice moment series are controlled by moments of the data's absolute lattice sum. -/
public section
namespace WaveTurbulence.Induct
open Finset MeasureTheory
open SysAPI
open scoped ENNReal

theorem summable_lattice_product_moments {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι]
    {μ : Measure Ω} [IsFiniteMeasure μ] {d : ℕ} (c : Ω → (Fin d → ℤ) → ℂ)
    (hc : ∀ n, ∀ q : ℕ, 1 ≤ q → MemLp (fun ω => c ω n) (q : ℝ≥0∞) μ)
    (hcs : ∀ᵐ ω ∂μ, Summable fun n => ‖c ω n‖)
    (hM : ∀ q : ℕ, 1 ≤ q → MemLp (fun ω => ∑' n, ‖c ω n‖) (q : ℝ≥0∞) μ)
    (sig : ι → ℤˣ) :
    Summable (fun a : ι → (Fin d → ℤ) => ∫ ω, ‖∏ i, zpowSign (sig i) (c ω (a i))‖ ∂μ) := by
  have hI (a : ι → (Fin d → ℤ)) : Integrable (fun ω => ∏ i, zpowSign (sig i) (c ω (a i))) μ := by
    have h : MemLp (fun ω => ∏ i, zpowSign (sig i) (c ω (a i))) ((1 : ℕ) : ℝ≥0∞) μ := by
      apply memLp_prod_of_all_memLp
      · intro i _ q hq
        unfold zpowSign
        split_ifs
        · exact hc _ q hq
        · exact (hc _ q hq).star
      · exact Nat.le_refl 1
    simp only [Nat.cast_one] at h
    exact memLp_one_iff_integrable.mp h
  have hpow := memLp_pow_of_all (fun ω => ∑' n, ‖c ω n‖) hM
    (fun ω => tsum_nonneg (fun n => norm_nonneg _)) (Fintype.card ι) 1 (by omega)
  simp only [Nat.cast_one] at hpow
  apply summable_integral_norm_of_finite_sum_bound μ _ hI
    (fun ω => (∑' n, ‖c ω n‖) ^ Fintype.card ι) (memLp_one_iff_integrable.mp hpow)
  intro u
  filter_upwards [hcs] with ω hω
  simp_rw [norm_prod, norm_zpowSign]
  have h := sum_prod_le_prod_finite_sum_bounds (fun (_ : ι) n => ‖c ω n‖)
    (fun _ _ => norm_nonneg _) (fun _ => ∑' n, ‖c ω n‖)
    (fun _ v => hω.sum_le_tsum v (fun _ _ => norm_nonneg _)) u
  simpa only [prod_const, card_univ] using h

end WaveTurbulence.Induct
