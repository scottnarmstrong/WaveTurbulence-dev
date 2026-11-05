/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.XChain.TruncatedL2WeakBound
public import WaveTurbulence.Foundations.XChain.SignedRemainder
/-! S6 for the actual signed fixedpoint remainders and truncated coefficients. -/
public section
namespace WaveTurbulence.Induct
open Finset MeasureTheory Set
open scoped ENNReal

theorem ansatz_truncated_remainder_cumulant_bound (Q : WTParams) {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (g : (Fin Q.d → ℤ) → Ω → ℂ)
    (hGaussian : IsGaussianData μ g)
    (a : Ω → ℝ → (Fin Q.d → ℤ) → ℂ) (Fev : ℕ → Set Ω)
    (R : ℕ → Mom Q.d → ℝ) (E : ℕ → (Fin Q.d → ℤ) → ℝ)
    (Et : ℕ → (m : ℕ) → (Fin (2 * m) → ℤˣ) → (Fin (2 * m) → (Fin Q.d → ℤ)) → ℂ)
    (p : ℕ) (ha : AnsatzAt Q μ g a Fev R E Et p)
    (hrapid : ∀ ω ∈ Fev p, IsRapidDecay (initialCoeff Q.L Q.φin g ω))
    (hM : ∀ q : ℕ, 1 ≤ q → MemLp (fun ω => ∑' n, ‖a ω p n‖) (q : ℝ≥0∞) (μ.restrict (Fev p)))
    (hGarden : LayergardenBody Q) (hTaylor : WkeTaylorBody Q) (hR : RemainderBound Q R p)
    (hC2 : 0 ≤ Q.C₂) (hr : 0 ≤ Q.C₁ * Q.δ) (hr1 : Q.C₁ * Q.δ < 1)
    (hsmall2 : Q.δ ^ (2 * Q.ν) ≤ 1 / 2)
    (hsmall0 : Q.δ ^ Q.ν ≤ 1 / 2)
    (hδ : 0 < Q.δ) (hsmall : Q.δ ^ (Q.ν / 2) ≤ 1 / 2) (hLone : 1 ≤ Q.L)
    (C : ℝ) (hC : 2 ≤ C)
    (hF : ∀ n, |inputsF Q R p (latticePoint Q.L n)| ≤
      C * jbr (latticePoint Q.L n) ^ (-(Q.Lambda p : ℝ)))
    (hsumF : ∀ q, Summable fun m : Fin Q.d → ℤ => |inputsF Q R q (latticePoint Q.L m)|)
    (w : ℕ) (hwidth : 2 * w ≤ 20 * Q.R (p + 1))
    (sig : Fin w → ℤˣ) (n : Fin w → (Fin Q.d → ℤ))
    (hd : 1 ≤ Q.d) (hp : p < Q.D)
    (hN : 2000000 ≤ Q.N (p + 1)) (hNdim : 2 * Q.d + 4 ≤ Q.N (p + 1))
    (hLexp : Real.exp 2 ≤ Q.L) (hCL : C ≤ Q.L)
    (hbN : (Q.Lambda p : ℝ) / 4 ≤ Q.N (p + 1)) (hbase : baseLatticeSum Q.d ≤ Q.L)
    (hq : Q.δ ^ (Q.ν / 2) ≤ Real.exp (-4000000))
    (hγ : Q.γ ≤ (Q.d : ℝ)) (hδ1 : Q.δ ≤ 1)
    (t : ℝ) (ht : t ∈ Ioc (p : ℝ) (p + 1)) (B : ℝ) (hB : 0 ≤ B)
    (hφ : ∀ k, |Q.φ (Q.δ * t) k| ≤ B * jbr k ^ (-(4 * Q.Lambda (p + 1) : ℝ)))
    (hrest : 2 * Q.L ^ (-(4 * Q.theta (p + 1) + Q.theta p) / 5) +
      Q.C₂ * (Q.C₁ * Q.δ) ^ (Q.N (p + 1) ^ 4 / 2 + 1) / (1 - Q.C₁ * Q.δ) ≤ 1)
    (Cmom : ℕ) (hCmom : B + 4 ≤ Cmom)
    (Fnew : Set Ω) (hnew : MeasurableSet Fnew) (hsub : Fnew ⊆ Fev p)
    (Anew : Ω → (Fin Q.d → ℤ) → ℂ) (hAnew : ∀ n, Measurable (fun ω => Anew ω n))
    (hrem : ∀ ω ∈ Fnew, ∀ n,
      ‖Anew ω n - aTr Q.L Q.γ Q.δ p (Q.N (p + 1)) (a ω p) t n‖ ≤
        Real.exp (-(10 * Q.N (p + 1) : ℝ)) *
          jbr (latticePoint Q.L n) ^ (-(Q.Lambda (p + 1) : ℝ))) :
    ‖cumulant (μ.restrict Fnew) (fun j ω => zpowSign (sig j) (Anew ω (n j))) univ -
      cumulant (μ.restrict Fnew) (fun j ω => zpowSign (sig j)
        (aTr Q.L Q.γ Q.δ p (Q.N (p + 1)) (a ω p) t (n j))) univ‖ ≤
      Real.exp (-(10 * Q.N (p + 1) : ℝ)) * 2 ^ w *
        (((2 * (Cmom + 2) + 2) * w).factorial : ℝ) *
        ∏ j, jbr (latticePoint Q.L (n j)) ^ (-(Q.Lambda (p + 1) : ℝ)) := by
  let X := fun j ω => zpowSign (sig j)
    (aTr Q.L Q.γ Q.δ p (Q.N (p + 1)) (a ω p) t (n j))
  let Y := fun j ω => zpowSign (sig j)
    (Anew ω (n j) - aTr Q.L Q.γ Q.δ p (Q.N (p + 1)) (a ω p) t (n j))
  let M := fun j => jbr (latticePoint Q.L (n j)) ^ (-(Q.Lambda (p + 1) : ℝ))
  have hmem (J : Finset (Fin w)) : MemLp (fun ω => ∏ j ∈ J, X j ω) 2 (μ.restrict (Fev p)) :=
    memLp_signed_prod_aTr Q.L Q.γ Q.δ p (Q.N (p + 1)) (fun ω => a ω p)
      (fun n => (ha.1.2.2.2.2.2.1 p ⟨Nat.cast_nonneg _, le_rfl⟩ n).aestronglyMeasurable)
      (ansatz_input_summable ha (lt_of_lt_of_le zero_lt_one hLone)) hM t sig n J 2 (by omega)
  have h2 (J : Finset (Fin w)) : (∫ ω in Fev p, ‖∏ j ∈ J, X j ω‖ ^ 2 ∂μ) ≤
      (((2 * (Cmom + 2) * J.card).factorial : ℝ) * ∏ j ∈ J, M j) ^ 2 := by
    exact ansatz_truncated_L2_weak_bound Q μ g hGaussian a Fev R E Et p ha hrapid hM
      hGarden hTaylor hR hC2 hr hr1 hsmall2 hsmall0 hδ hsmall hLone C hC hF hsumF
      J (le_trans (Nat.mul_le_mul_left 2 (by simpa using card_le_univ J)) hwidth) sig n
      hd hp hN hNdim hLexp hCL hbN hbase hq hγ hδ1 t ht B hB hφ hrest Cmom hCmom
  have hX (j : Fin w) (q : ℕ) (hq : 1 ≤ q) : MemLp (X j) (q : ℝ≥0∞) (μ.restrict Fnew) := by
    have h := memLp_signed_prod_aTr Q.L Q.γ Q.δ p (Q.N (p + 1)) (fun ω => a ω p)
      (fun n => (ha.1.2.2.2.2.2.1 p ⟨Nat.cast_nonneg _, le_rfl⟩ n).aestronglyMeasurable)
      (ansatz_input_summable ha (lt_of_lt_of_le zero_lt_one hLone)) hM t sig n {j} q hq
    simpa only [Finset.prod_singleton] using h.mono_measure (Measure.restrict_mono hsub le_rfl)
  have hY (j : Fin w) (q : ℕ) (_hq : 1 ≤ q) : MemLp (Y j) (q : ℝ≥0∞) (μ.restrict Fnew) := by
    have htr := memLp_aTr Q.L Q.γ Q.δ p (Q.N (p + 1)) (fun ω => a ω p)
      (fun n => (ha.1.2.2.2.2.2.1 p ⟨Nat.cast_nonneg _, le_rfl⟩ n).aestronglyMeasurable)
      (ansatz_input_summable ha (lt_of_lt_of_le zero_lt_one hLone)) hM t (n j) 2 (by omega)
    apply memLp_signed_bounded_remainder (K := Real.exp (-(10 * Q.N (p + 1) : ℝ)) * M j)
      (hAnew (n j)).aestronglyMeasurable
      (htr.mono_measure (Measure.restrict_mono hsub le_rfl)).aestronglyMeasurable (sig j) _ (q : ℝ≥0∞)
    filter_upwards [ae_restrict_mem hnew] with ω hω
    exact hrem ω hω (n j)
  have he : (fun j ω => X j ω + Y j ω) = (fun j ω => zpowSign (sig j) (Anew ω (n j))) := by
    funext j ω
    dsimp [X, Y]
    rw [zpowSign_sub]
    ring
  have h := norm_cumulant_add_error_le_of_L2 (ε := Real.exp (-(10 * Q.N (p + 1) : ℝ))) hnew hsub X Y hX hY (2 * (Cmom + 2)) M
    (fun j => Real.rpow_nonneg (le_of_lt (jbr_pos _)) _) (Real.exp_pos _).le
    (Real.exp_le_one_iff.mpr (neg_nonpos.mpr (by positivity))) hmem h2 (by
      filter_upwards [ae_restrict_mem hnew] with ω hω j
      dsimp [Y, M]
      rw [norm_zpowSign]
      exact hrem ω hω (n j))
  rw [he] at h
  simpa only [Fintype.card_fin] using h

end WaveTurbulence.Induct
