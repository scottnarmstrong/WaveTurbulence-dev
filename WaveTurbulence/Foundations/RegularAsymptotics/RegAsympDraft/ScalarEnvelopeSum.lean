/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.RegularAsymptotics.RegAsympDraft.ErrorCoefficientBudget

/-! # Finite sums of the two original scalar source envelopes -/

public section
noncomputable section
namespace WaveTurbulence.RegAsymp
open MeasureTheory ClassJR
open scoped ENNReal

/-- The literal finite envelope sum pays twice the original source index
count and preserves the original weighted frequency mass. -/
theorem weighted_scalar_envelope_sum_le {I : Type*} [Fintype I]
    (η : ℝ) (BN BW : I → (ℝ × ℝ) → ℝ)
    (hmN : ∀ i, Measurable (BN i)) (hmW : ∀ i, Measurable (BW i))
    (hpN : ∀ i lam, 0 ≤ BN i lam) (hpW : ∀ i lam, 0 ≤ BW i lam)
    {R : ℝ≥0∞}
    (hbN : ∀ i, (∫⁻ lam, wL η lam*ENNReal.ofReal (BN i lam)) ≤ R)
    (hbW : ∀ i, (∫⁻ lam, wL η lam*ENNReal.ofReal (BW i lam)) ≤ R) :
    (∫⁻ lam, wL η lam*ENNReal.ofReal (∑ i, (BN i lam+BW i lam))) ≤
      (Fintype.card I:ℝ≥0∞)*(R+R) := by
  classical
  have he (lam : ℝ × ℝ) : ENNReal.ofReal (∑ i, (BN i lam+BW i lam)) =
      ∑ i, (ENNReal.ofReal (BN i lam)+ENNReal.ofReal (BW i lam)) := by
    rw [ENNReal.ofReal_sum_of_nonneg (fun i _ => add_nonneg (hpN i lam) (hpW i lam))]
    apply Finset.sum_congr rfl
    intro i _
    exact ENNReal.ofReal_add (hpN i lam) (hpW i lam)
  have hsum (lam : ℝ × ℝ) : wL η lam*ENNReal.ofReal (∑ i, (BN i lam+BW i lam)) =
      ∑ i, (wL η lam*ENNReal.ofReal (BN i lam)+wL η lam*ENNReal.ofReal (BW i lam)) := by
    rw [he,Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    ring
  simp_rw [hsum]
  rw [lintegral_finsetSum (f := fun i (lam : ℝ × ℝ) =>
    wL η lam*ENNReal.ofReal (BN i lam)+wL η lam*ENNReal.ofReal (BW i lam)) Finset.univ (fun i _ =>
    ((measurable_wL η).mul (ENNReal.measurable_ofReal.comp (hmN i))).add
      ((measurable_wL η).mul (ENNReal.measurable_ofReal.comp (hmW i))))]
  calc
    _ = ∑ i : I, ((∫⁻ lam, wL η lam*ENNReal.ofReal (BN i lam))+
        (∫⁻ lam, wL η lam*ENNReal.ofReal (BW i lam))) := by
      apply Finset.sum_congr rfl
      intro i _
      exact lintegral_add_left ((measurable_wL η).mul (ENNReal.measurable_ofReal.comp (hmN i))) _
    _ ≤ ∑ _i : I, (R+R) := Finset.sum_le_sum (fun i _ => add_le_add (hbN i) (hbW i))
    _ = _ := by rw [Finset.sum_const,Finset.card_univ,nsmul_eq_mul]

/-- A powerset-sized family of the two errors fits one geometric factor,
with no factorial or order-dependent fixed constant. -/
theorem powerset_error_mass_le {n : ℕ} (hn : 0 < n) {C : ℝ}
    (D : ℝ≥0∞) :
    (2:ℝ≥0∞)^n*(D*ENNReal.ofReal C^n+D*ENNReal.ofReal C^n) ≤
      D*ENNReal.ofReal (4*C)^n := by
  have hp : (2:ℝ≥0∞) ≤ (2:ℝ≥0∞)^n := le_self_pow₀ (by norm_num) hn.ne'
  calc
    _ = D*((2:ℝ≥0∞)^n*2*ENNReal.ofReal C^n) := by ring
    _ ≤ D*((2:ℝ≥0∞)^n*(2:ℝ≥0∞)^n*ENNReal.ofReal C^n) :=
      mul_le_mul' le_rfl (mul_le_mul' (mul_le_mul' le_rfl hp) le_rfl)
    _ = _ := by
      rw [← mul_pow,← mul_pow,ENNReal.ofReal_mul (by norm_num : (0:ℝ) ≤ 4),ENNReal.ofReal_ofNat]
      norm_num

end WaveTurbulence.RegAsymp
