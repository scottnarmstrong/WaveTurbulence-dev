/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.XChain.UnbalancedInputBlock
public import WaveTurbulence.Foundations.XChain.TruncatedCumulantPartitionCarrier
/-! Unbalanced actual truncated cumulants vanish by an unbalanced input block in every leaf partition. -/
public section
namespace WaveTurbulence.Induct
open Finset MeasureTheory Set
open scoped ENNReal

theorem ansatz_cumulant_aTr_eq_zero_of_unbalanced (Q : WTParams) {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (g : (Fin Q.d → ℤ) → Ω → ℂ)
    (hG : IsGaussianData μ g) (hL : 0 < Q.L)
    (a : Ω → ℝ → (Fin Q.d → ℤ) → ℂ) (Fev : ℕ → Set Ω)
    (R : ℕ → Mom Q.d → ℝ) (E : ℕ → (Fin Q.d → ℤ) → ℝ)
    (Et : ℕ → (m : ℕ) → (Fin (2 * m) → ℤˣ) → (Fin (2 * m) → (Fin Q.d → ℤ)) → ℂ)
    (p : ℕ) (ha : AnsatzAt Q μ g a Fev R E Et p)
    (hrapid : ∀ ω ∈ Fev p, IsRapidDecay (initialCoeff Q.L Q.φin g ω))
    (hM : ∀ q : ℕ, 1 ≤ q → MemLp (fun ω => ∑' n, ‖a ω p n‖) (q : ℝ≥0∞) (μ.restrict (Fev p)))
    {w : ℕ} (sig : Fin w → ℤˣ) (hs : ∑ j, (sig j : ℤ) ≠ 0)
    (Ntop : ℕ) (t : ℝ) (n : Fin w → (Fin Q.d → ℤ)) :
    cumulant (μ.restrict (Fev p))
      (fun j ω => zpowSign (sig j) (aTr Q.L Q.γ Q.δ p Ntop (a ω p) t (n j))) univ = 0 := by
  classical
  have hcs : ∀ᵐ ω ∂μ.restrict (Fev p), Summable (fun n => ‖a ω p n‖) := by
    filter_upwards [ae_restrict_mem ha.1.1] with ω hω
    exact SysAPI.IsASolution.summable_norm hL (ha.1.2.2.2.2.1 ω hω).1 ⟨Nat.cast_nonneg _, le_rfl⟩
  have hc (n : Fin Q.d → ℤ) (q : ℕ) (hq : 1 ≤ q) :
      MemLp (fun ω => a ω p n) (q : ℝ≥0∞) (μ.restrict (Fev p)) := by
    apply (hM q hq).mono' (ha.1.2.2.2.2.2.1 p ⟨Nat.cast_nonneg _, le_rfl⟩ n).aestronglyMeasurable
    filter_upwards [hcs] with ω hω
    exact hω.le_tsum n (fun m _ => norm_nonneg _)
  rw [cumulant_aTr_eq_partition_carrier Q.L Q.γ Q.δ p Ntop (fun ω => a ω p) hc hcs hM t n sig]
  apply sum_eq_zero
  intro top _
  apply mul_eq_zero_of_right
  apply sum_eq_zero
  intro P _
  obtain ⟨B, hB⟩ := exists_unbalanced_leaf_block (fun j => (top j).1) sig hs P.1
  apply Eq.trans (tsum_congr (g := fun _ : ForestDecoration (fun j => (top j).1) Q.d n => (0 : ℂ)) ?_) tsum_zero
  intro κ
  unfold topPartitionCumulantIntegrand
  apply mul_eq_zero_of_right
  exact prod_eq_zero (mem_univ B)
    (ansatz_unbalanced_topBlock_zero Q μ g hG hL a Fev R E Et p ha hrapid sig
      (fun j => (top j).1) P.1 κ B hB 0).1

end WaveTurbulence.Induct
