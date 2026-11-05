/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.XChain.TruncatedHigherCumulantBound
public import WaveTurbulence.Foundations.XChain.CoupleAbsorbedTail
public import WaveTurbulence.Foundations.XChain.CmattrCoupleOrderSplit
public import WaveTurbulence.Foundations.XChain.CoupleMainSumBound
/-! The actual canonical two-point truncated cumulant has the individual momentum weights needed by S6/S7. -/
public section
namespace WaveTurbulence.Induct
open Finset MeasureTheory Set
open scoped ENNReal

theorem ansatz_canonical_pair_truncated_cumulant_bound (Q : WTParams) {Ω : Type*} [MeasurableSpace Ω]
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
    (n : Fin 2 → (Fin Q.d → ℤ)) (hd : 1 ≤ Q.d) (hp : p < Q.D)
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
      (fun j ω => zpowSign (![1, -1] j) (aTr Q.L Q.γ Q.δ p (Q.N (p + 1)) (a ω p) t (n j))) univ‖ ≤
      (B + 3) * (∏ j, jbr (latticePoint Q.L (n j))) ^ (-(2 * Q.Lambda (p + 1) : ℝ)) := by
  classical
  have hL : 0 < Q.L := zero_lt_one.trans_le hLone
  have hR2 : (2 : ℝ) ≤ Q.R (p + 1) :=
    ((Real.le_log_iff_exp_le hL).mpr hLexp).trans (log_le_Rdown Q hd hLexp (Q.D - (p + 1)))
  have hR2nat : 2 ≤ Q.R (p + 1) := by exact_mod_cast hR2
  have hw : 2 ≤ 100 * Q.R (p + 1) := by omega
  have hc := ansatz_input_all_memLp ha hL hM
  have hcs := ansatz_input_summable ha hL
  have heq := cumulant_aTr_couple_eq_order_sum_add_tail_add_error Q (inputsF Q R) (fun ω => a ω p)
    hc hcs hM p (Q.N (p + 1) ^ 4) t ht.1.le ht.2 n hsumF
  have hmain := couple_main_lattice_sum_bound Q hGarden hTaylor R p hp hR hd hL hδ hC2 hsmall2 hr hr1
    (Q.N (p + 1) ^ 4) le_rfl t ht B hB hφ hrest n
  have htail := couple_tail_exp_bound Q μ g a Fev R E Et p ha hδ hsmall hLone C hC hF hsumF
    n hd hp hw hN hNdim hLexp hCL hbN hbase hq hγ hδ1 t ht.1.le ht.2
  have herr := cmattr_error_exp_bound Q μ g hGaussian a Fev R E Et p ha hrapid hδ hsmall0 hLone C hC hF
    ![1, -1] n hd hp hw hN hNdim hLexp hCL hbN hbase hγ hδ1 t ht.1.le ht.2
  let W : ℝ := (∏ j, jbr (latticePoint Q.L (n j))) ^ (-(2 * Q.Lambda (p + 1) : ℝ))
  have hW : 0 ≤ W := Real.rpow_nonneg (zero_le_one.trans (one_le_jbrProd Q.L n)) _
  have heweight : (∏ j, jbr (latticePoint Q.L (n j))) ^ (-((Q.Lambda p : ℝ) / 4)) ≤ W :=
    Real.rpow_le_rpow_of_exponent_le (one_le_jbrProd Q.L n)
      (neg_le_neg (lambda_quarter_ge_twice_succ Q hd hp))
  have hexp : Real.exp (-(20 * (Q.N (p + 1) : ℝ))) ≤ 1 :=
    Real.exp_le_one_iff.mpr (neg_nonpos.mpr (mul_nonneg (by norm_num) (Nat.cast_nonneg _)))
  have heW := mul_le_mul hexp heweight (Real.rpow_nonneg (zero_le_one.trans (one_le_jbrProd Q.L n)) _) zero_le_one
  simp only [one_mul] at heW
  rw [heq]
  exact ((norm_add_le _ _).trans (add_le_add ((norm_add_le _ _).trans (add_le_add hmain htail)) herr)).trans
    (by nlinarith)

end WaveTurbulence.Induct
