/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.XChain.CumulantRemainderExpansion
public import WaveTurbulence.Foundations.XChain.SmallCumulantBound
/-! The complete finite combinatorial loss in the S6 remainder error. -/
public section
namespace WaveTurbulence.Induct
open MeasureTheory Finset
open scoped ENNReal

/-- Summing all remainder-bearing cumulants keeps one small factor and costs an explicit
exponential times factorial in the number of roots. -/
theorem norm_cumulant_add_error_le {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι] [DecidableEq ι]
    (μ : Measure Ω) [IsFiniteMeasure μ] (X Y : ι → Ω → ℂ)
    (hX : ∀ i, ∀ p : ℕ, 1 ≤ p → MemLp (X i) (p : ℝ≥0∞) μ)
    (hY : ∀ i, ∀ p : ℕ, 1 ≤ p → MemLp (Y i) (p : ℝ≥0∞) μ)
    (C : ℕ) (M : ι → ℝ) (hM : ∀ j, 0 ≤ M j) {ε : ℝ} (hε : 0 ≤ ε)
    (hmom : ∀ f : ι → Bool, ∀ J : Finset ι, J.Nonempty →
      ‖∫ ω, ∏ j ∈ J, (if f j then Y j ω else X j ω) ∂μ‖ ≤
        (C * J.card).factorial * ∏ j ∈ J, M j)
    (hsmall : ∀ f : ι → Bool, ∀ i, f i = true → ∀ J : Finset ι, i ∈ J →
      ‖∫ ω, ∏ j ∈ J, (if f j then Y j ω else X j ω) ∂μ‖ ≤
        ε * ((C * J.card).factorial * ∏ j ∈ J, M j)) :
    ‖cumulant μ (fun i ω => X i ω + Y i ω) univ - cumulant μ X univ‖ ≤
      ε * 2 ^ Fintype.card ι * ((C + 2) * Fintype.card ι).factorial * ∏ j, M j := by
  classical
  let E : Finset (ι → Bool) := univ.erase (fun _ => false)
  let K : ℝ := ((C + 2) * Fintype.card ι).factorial * ∏ j, M j
  have hK : 0 ≤ K := mul_nonneg (Nat.cast_nonneg _) (prod_nonneg fun j _ => hM j)
  have hterm (f : ι → Bool) (hf : f ∈ E) :
      ‖cumulant μ (fun i ω => if f i then Y i ω else X i ω) univ‖ ≤ ε * K := by
    obtain ⟨i, hi⟩ := remainder_choice_has_true hf
    have h := norm_cumulant_le_of_small_variable μ (fun i ω => if f i then Y i ω else X i ω)
      univ (mem_univ i) C M hM hε (fun J _ hJ => hmom f J hJ)
      (fun J _ hJ => hsmall f i hi J hJ)
    simpa only [card_univ, K, mul_assoc] using h
  have hcard : E.card ≤ 2 ^ Fintype.card ι := by
    calc
      _ ≤ (univ : Finset (ι → Bool)).card := card_le_card (erase_subset _ _)
      _ = _ := by simp
  rw [cumulant_add_error_terms μ X Y hX hY]
  calc
    _ ≤ ∑ f ∈ E, ‖cumulant μ (fun i ω => if f i then Y i ω else X i ω) univ‖ := norm_sum_le _ _
    _ ≤ ∑ _f ∈ E, ε * K := sum_le_sum fun f hf => hterm f hf
    _ = (E.card : ℝ) * (ε * K) := by rw [sum_const, nsmul_eq_mul]
    _ ≤ (2 ^ Fintype.card ι : ℝ) * (ε * K) :=
      mul_le_mul_of_nonneg_right (by exact_mod_cast hcard) (mul_nonneg hε hK)
    _ = _ := by dsimp only [K]; ring

end WaveTurbulence.Induct
