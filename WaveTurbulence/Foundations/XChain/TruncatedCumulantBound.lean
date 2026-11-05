/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.XChain.TruncatedPairCumulantBound
public import WaveTurbulence.Foundations.XChain.CumulantPairOrientation
public import WaveTurbulence.Foundations.XChain.UnbalancedTruncatedCumulant
/-! Every actual nonempty truncated cumulant in range has a uniform individual spatial-weight bound. -/
public section
namespace WaveTurbulence.Induct
open Finset MeasureTheory Set
open scoped ENNReal

theorem ansatz_truncated_cumulant_bound (Q : WTParams) {Ω : Type*} [MeasurableSpace Ω]
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
    {w : ℕ} (hw : 1 ≤ w) (hwR : w ≤ 20 * Q.R (p + 1))
    (sig : Fin w → ℤˣ) (n : Fin w → (Fin Q.d → ℤ)) (hd : 1 ≤ Q.d) (hp : p < Q.D)
    (hN : 2000000 ≤ Q.N (p + 1)) (hNdim : 2 * Q.d + 4 ≤ Q.N (p + 1))
    (hLexp : Real.exp 2 ≤ Q.L) (hCL : C ≤ Q.L)
    (hbN : (Q.Lambda p : ℝ) / 4 ≤ Q.N (p + 1)) (hbase : baseLatticeSum Q.d ≤ Q.L)
    (hq : Q.δ ^ (Q.ν / 2) ≤ Real.exp (-4000000))
    (hγ : Q.γ ≤ (Q.d : ℝ)) (hδ1 : Q.δ ≤ 1)
    (t : ℝ) (ht : t ∈ Ioc (p : ℝ) (p + 1)) (B : ℝ) (hB : 0 ≤ B)
    (hφ : ∀ k, |Q.φ (Q.δ * t) k| ≤ B * jbr k ^ (-(4 * Q.Lambda (p + 1) : ℝ)))
    (hrest : 2 * Q.L ^ (-(4 * Q.theta (p + 1) + Q.theta p) / 5) +
      Q.C₂ * (Q.C₁ * Q.δ) ^ (Q.N (p + 1) ^ 4 / 2 + 1) / (1 - Q.C₁ * Q.δ) ≤ 1) :
    ‖cumulant (μ.restrict (Fev p))
      (fun j ω => zpowSign (sig j) (aTr Q.L Q.γ Q.δ p (Q.N (p + 1)) (a ω p) t (n j))) univ‖ ≤
      (B + 4) * (∏ j, jbr (latticePoint Q.L (n j))) ^ (-(2 * Q.Lambda (p + 1) : ℝ)) := by
  classical
  have hweight {v : ℕ} (m : Fin v → (Fin Q.d → ℤ)) :
      0 ≤ (∏ j, jbr (latticePoint Q.L (m j))) ^ (-(2 * Q.Lambda (p + 1) : ℝ)) :=
    Real.rpow_nonneg (zero_le_one.trans (one_le_jbrProd Q.L m)) _
  by_cases hbal : ∑ j, (sig j : ℤ) = 0
  · have heven : Even w := by
      simpa only [card_univ, Fintype.card_fin] using even_card_of_balanced_units sig univ hbal
    obtain ⟨m, hm⟩ := heven
    have he : w = 2 * m := by omega
    clear hm
    subst w
    by_cases hm1 : m = 1
    · subst m
      have hcanonical (n' : Fin 2 → (Fin Q.d → ℤ)) := ansatz_canonical_pair_truncated_cumulant_bound
        Q μ g hGaussian a Fev R E Et p ha hrapid hM hGarden hTaylor hR hC2 hr hr1 hsmall2 hsmall0
        hδ hsmall hLone C hC hF hsumF n' hd hp hN hNdim hLexp hCL hbN hbase hq hγ hδ1 t ht B hB hφ hrest
      rcases balanced_pair_sign_cases sig hbal with rfl | rfl
      · exact (hcanonical n).trans (mul_le_mul_of_nonneg_right (by linarith) (hweight n))
      · rw [cumulant_signed_pair_reverse]
        have hnprod : (∏ j : Fin 2, jbr (latticePoint Q.L (n j.rev))) =
            ∏ j : Fin 2, jbr (latticePoint Q.L (n j)) := by
          simp only [Fin.prod_univ_two]
          change jbr (latticePoint Q.L (n 1)) * jbr (latticePoint Q.L (n 0)) =
            jbr (latticePoint Q.L (n 0)) * jbr (latticePoint Q.L (n 1))
          ring
        have h := hcanonical (fun j => n j.rev)
        rw [hnprod] at h
        exact h.trans (mul_le_mul_of_nonneg_right (by linarith) (hweight n))
    · have hm2 : 2 ≤ m := by omega
      have hmR : m ≤ 10 * Q.R (p + 1) := by omega
      have h := ansatz_higher_truncated_cumulant_bound Q μ g hGaussian a Fev R E Et p ha hrapid hM
        hGarden hR hsmall0 hδ hsmall hLone C hC hF hsumF m hm2 hmR sig hbal n hd hp hN hNdim
        hLexp hCL hbN hbase hq hγ hδ1 t ht
      exact h.trans (mul_le_mul_of_nonneg_right (by linarith) (hweight n))
  · rw [ansatz_cumulant_aTr_eq_zero_of_unbalanced Q μ g hGaussian (zero_lt_one.trans_le hLone)
      a Fev R E Et p ha hrapid hM sig hbal (Q.N (p + 1)) t n, norm_zero]
    exact mul_nonneg (by linarith) (hweight n)

end WaveTurbulence.Induct
