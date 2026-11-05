/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.XChain.TruncatedL2MomentBound
public import WaveTurbulence.Foundations.XChain.EventChangeL2
/-! S7 for the actual truncated coefficients on the fixedpoint event. -/
public section
namespace WaveTurbulence.Induct
open Finset MeasureTheory Set
open scoped ENNReal

theorem ansatz_truncated_event_change_bound (Q : WTParams) {Ω : Type*} [MeasurableSpace Ω]
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
    {ι : Type*} [DecidableEq ι] (s : Finset ι) (hs : s.Nonempty)
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
    (Cmom : ℕ) (hCmom : B + 4 ≤ Cmom)
    (Anew : Set Ω) (hnew : MeasurableSet Anew) (hsub : Anew ⊆ Fev p) :
    ‖cumulant (μ.restrict Anew)
        (fun j ω => zpowSign (sig j) (aTr Q.L Q.γ Q.δ p (Q.N (p + 1)) (a ω p) t (n j))) s -
      cumulant (μ.restrict (Fev p))
        (fun j ω => zpowSign (sig j) (aTr Q.L Q.γ Q.δ p (Q.N (p + 1)) (a ω p) t (n j))) s‖ ≤
      Real.sqrt (μ.real (Fev p \ Anew)) * 2 ^ s.card *
        (((2 * (Cmom + 2) + 2) * s.card).factorial : ℝ) *
        ∏ j ∈ s, jbr (latticePoint Q.L (n j)) ^ (-(2 * Q.Lambda (p + 1) : ℝ)) := by
  apply norm_cumulant_event_change_le_of_L2 μ _ s hnew hsub (2 * (Cmom + 2))
    (fun j => jbr (latticePoint Q.L (n j)) ^ (-(2 * Q.Lambda (p + 1) : ℝ)))
  · intro j
    exact Real.rpow_nonneg (le_of_lt (jbr_pos _)) _
  · intro J hJ
    exact memLp_signed_prod_aTr Q.L Q.γ Q.δ p (Q.N (p + 1)) (fun ω => a ω p)
      (fun n => (ha.1.2.2.2.2.2.1 p ⟨Nat.cast_nonneg _, le_rfl⟩ n).aestronglyMeasurable)
      (ansatz_input_summable ha (lt_of_lt_of_le zero_lt_one hLone)) hM t sig n J 2 (by omega)
  · intro J hJ hne
    exact ansatz_truncated_L2_moment_bound Q μ g hGaussian a Fev R E Et p ha hrapid hM
      hGarden hTaylor hR hC2 hr hr1 hsmall2 hsmall0 hδ hsmall hLone C hC hF hsumF
      J hne (le_trans (Nat.mul_le_mul_left 2 (Finset.card_le_card hJ)) hwidth) sig n
      hd hp hN hNdim hLexp hCL hbN hbase hq hγ hδ1 t ht B hB hφ hrest Cmom hCmom

end WaveTurbulence.Induct
