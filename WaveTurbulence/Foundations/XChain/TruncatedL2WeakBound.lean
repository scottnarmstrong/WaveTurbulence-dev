/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.XChain.TruncatedL2MomentBound
/-! An all-subsets version of the actual L2 bound at the final ansatz weight. -/
public section
namespace WaveTurbulence.Induct
open Finset MeasureTheory Set
open scoped ENNReal

theorem ansatz_truncated_L2_weak_bound (Q : WTParams) {Ω : Type*} [MeasurableSpace Ω]
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
    {ι : Type*} [DecidableEq ι] (s : Finset ι)
    (hwidth : 2 * s.card ≤ 20 * Q.R (p + 1)) (sig : ι → ℤˣ) (n : ι → (Fin Q.d → ℤ))
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
    (Cmom : ℕ) (hCmom : B + 4 ≤ Cmom) :
    (∫ ω in Fev p, ‖∏ j ∈ s, zpowSign (sig j)
      (aTr Q.L Q.γ Q.δ p (Q.N (p + 1)) (a ω p) t (n j))‖ ^ 2 ∂μ) ≤
      (((((2 * (Cmom + 2)) * s.card).factorial : ℝ) *
        ∏ j ∈ s, jbr (latticePoint Q.L (n j)) ^ (-(Q.Lambda (p + 1) : ℝ))) ^ 2) := by
  classical
  by_cases hs : s.Nonempty
  · have h := ansatz_truncated_L2_moment_bound Q μ g hGaussian a Fev R E Et p ha hrapid hM
      hGarden hTaylor hR hC2 hr hr1 hsmall2 hsmall0 hδ hsmall hLone C hC hF hsumF
      s hs hwidth sig n hd hp hN hNdim hLexp hCL hbN hbase hq hγ hδ1 t ht B hB hφ hrest Cmom hCmom
    apply h.trans
    apply pow_le_pow_left₀ (mul_nonneg (Nat.cast_nonneg _)
      (prod_nonneg fun j _ => Real.rpow_nonneg (le_of_lt (jbr_pos _)) _))
    apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
    apply prod_le_prod₀
    · intro j _
      exact Real.rpow_nonneg (le_of_lt (jbr_pos _)) _
    · intro j _
      apply Real.rpow_le_rpow_of_exponent_le (one_le_jbr _)
      have hΛ : (0 : ℝ) ≤ Q.Lambda (p + 1) := Nat.cast_nonneg _
      push_cast
      linarith
  · have he : s = ∅ := not_nonempty_iff_eq_empty.mp hs
    subst s
    simpa using (measureReal_le_one (μ := μ) (s := Fev p))

end WaveTurbulence.Induct
