/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.XChain.NextPairCumulantError
public import WaveTurbulence.Foundations.XChain.RealCovarianceError
/-! The actual real two-point error relative to the next spatial remainder. -/
public section
namespace WaveTurbulence.Induct
open Finset MeasureTheory Set
open scoped ENNReal

theorem ansatz_next_variance_error_bound (Q : WTParams) {Ω : Type*} [MeasurableSpace Ω]
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
    (n : Fin Q.d → ℤ)
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
    (Anew : Ω → ℝ → (Fin Q.d → ℤ) → ℂ)
    (hAnew : ∀ s ∈ Icc (0 : ℝ) (p + 1), ∀ n, Measurable (fun ω => Anew ω s n))
    (hrem : ∀ ω ∈ Fnew, ∀ n,
      ‖Anew ω t n - aTr Q.L Q.γ Q.δ p (Q.N (p + 1)) (a ω p) t n‖ ≤
        Real.exp (-(10 * Q.N (p + 1) : ℝ)) *
          jbr (latticePoint Q.L n) ^ (-(Q.Lambda (p + 1) : ℝ)))
    (hprob : μ.real (Fev p \ Fnew) ≤ Real.exp (-(4 * Q.N (p + 1) : ℝ)))
    (hRsize : 1000 * ((2 * (Cmom + 2) + 2) ^ 2 + 1) ≤ Q.R (p + 1))

    (hsym : IsSymmetricEvent Q.L Q.φin g Fnew)
    (hsol : ∀ ω ∈ Fnew, IsASolution Q.L Q.γ Q.δ (p + 1)
      (initialCoeff Q.L Q.φin g ω) (Anew ω)) :
    |(∫ ω in Fnew, ‖Anew ω t n‖ ^ 2 ∂μ) -
      (Q.φ (Q.δ * t) (latticePoint Q.L n) +
        nextRemainder Q R p (Q.N (p + 1) ^ 4) t (latticePoint Q.L n))| ≤
      jbr (latticePoint Q.L n) ^ (-(Q.Lambda (p + 1) : ℝ)) *
        Real.exp (-(Q.N (p + 1) : ℝ)) := by
  have htt : t ∈ Icc (0 : ℝ) (p + 1) := ⟨(Nat.cast_nonneg p).trans ht.1.le, ht.2⟩
  have h := ansatz_next_pair_cumulant_error_bound Q μ g hGaussian a Fev R E Et p ha hrapid hM
    hGarden hTaylor hR hC2 hr hr1 hsmall2 hsmall0 hδ hsmall hLone C hC hF hsumF
    (fun _ => n) hd hp hN hNdim hLexp hCL hbN hbase hq hγ hδ1 t ht B hB hφ hrest Cmom hCmom
    Fnew hnew hsub (fun ω => Anew ω t) (hAnew t htt) hrem hprob hRsize
  have hm := solution_mean_zero (zero_lt_one.trans_le hLone) Q.φin hGaussian Fnew hnew hsym Anew hsol
    (fun ω hω => hrapid ω (hsub hω)) hAnew t htt n
  rw [pair_cumulant_eq_complex_variance (μ.restrict Fnew) (fun ω => Anew ω t n) hm] at h
  simp_rw [Canon.truncSum_couple_eq_truncSumC] at h
  have hreal := variance_error_le_complex_error h
  have hremEq := nextRemainder_eq_real_kernel_sum_sub_phi Q hTaylor R p hp (Q.N (p + 1) ^ 4)
    t ⟨ht.1.le, ht.2⟩ (latticePoint Q.L n)
  rw [hremEq]
  have hbase : (∏ _j : Fin 2, jbr (latticePoint Q.L n)) ^ (-(Q.Lambda (p + 1) : ℝ)) ≤
      jbr (latticePoint Q.L n) ^ (-(Q.Lambda (p + 1) : ℝ)) := by
    rw [Fin.prod_univ_two, Real.mul_rpow (jbr_pos _).le (jbr_pos _).le]
    apply mul_le_of_le_one_right (Real.rpow_nonneg (jbr_pos _).le _)
    exact Real.rpow_le_one_of_one_le_of_nonpos (one_le_jbr _)
      (neg_nonpos.mpr (Nat.cast_nonneg _))
  have hb := mul_le_mul_of_nonneg_right hbase (Real.exp_pos (-(Q.N (p + 1) : ℝ))).le
  have he (v f m : ℝ) : |v - (f + (m - f))| = |v - m| := by
    congr 1
    ring
  rw [he]
  exact hreal.trans hb

end WaveTurbulence.Induct
