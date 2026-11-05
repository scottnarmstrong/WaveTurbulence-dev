/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.XChain.CmattrAbsorbedError
public import WaveTurbulence.Foundations.XChain.CanonicalAbsorbedTail
public import WaveTurbulence.Foundations.XChain.CmattrOrderSplit
public import WaveTurbulence.Foundations.XChain.HigherGardenSumBound
public import WaveTurbulence.Foundations.XChain.AnsatzInputMoments
/-! Actual balanced higher truncated cumulants have the weighted size needed by S6/S7. -/
public section
namespace WaveTurbulence.Induct
open Finset MeasureTheory Set
open scoped ENNReal

theorem ansatz_higher_truncated_cumulant_bound (Q : WTParams) {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (g : (Fin Q.d → ℤ) → Ω → ℂ)
    (hGaussian : IsGaussianData μ g)
    (a : Ω → ℝ → (Fin Q.d → ℤ) → ℂ) (Fev : ℕ → Set Ω)
    (R : ℕ → Mom Q.d → ℝ) (E : ℕ → (Fin Q.d → ℤ) → ℝ)
    (Et : ℕ → (m : ℕ) → (Fin (2 * m) → ℤˣ) → (Fin (2 * m) → (Fin Q.d → ℤ)) → ℂ)
    (p : ℕ) (ha : AnsatzAt Q μ g a Fev R E Et p)
    (hrapid : ∀ ω ∈ Fev p, IsRapidDecay (initialCoeff Q.L Q.φin g ω))
    (hM : ∀ q : ℕ, 1 ≤ q → MemLp (fun ω => ∑' n, ‖a ω p n‖) (q : ℝ≥0∞) (μ.restrict (Fev p)))
    (hGarden : LayergardenBody Q) (hR : RemainderBound Q R p)
    (hsmall0 : Q.δ ^ Q.ν ≤ 1 / 2)
    (hδ : 0 < Q.δ) (hsmall : Q.δ ^ (Q.ν / 2) ≤ 1 / 2) (hLone : 1 ≤ Q.L)
    (C : ℝ) (hC : 2 ≤ C)
    (hF : ∀ n, |inputsF Q R p (latticePoint Q.L n)| ≤
      C * jbr (latticePoint Q.L n) ^ (-(Q.Lambda p : ℝ)))
    (hsumF : ∀ q, Summable fun m : Fin Q.d → ℤ => |inputsF Q R q (latticePoint Q.L m)|)
    (m : ℕ) (hm : 2 ≤ m) (hmR : m ≤ 10 * Q.R (p + 1))
    (sig : Fin (2 * m) → ℤˣ) (hbal : IsBalancedSig sig) (n : Fin (2 * m) → (Fin Q.d → ℤ))
    (hd : 1 ≤ Q.d) (hp : p < Q.D)
    (hN : 2000000 ≤ Q.N (p + 1)) (hNdim : 2 * Q.d + 4 ≤ Q.N (p + 1))
    (hLexp : Real.exp 2 ≤ Q.L) (hCL : C ≤ Q.L)
    (hbN : (Q.Lambda p : ℝ) / 4 ≤ Q.N (p + 1)) (hbase : baseLatticeSum Q.d ≤ Q.L)
    (hq : Q.δ ^ (Q.ν / 2) ≤ Real.exp (-4000000))
    (hγ : Q.γ ≤ (Q.d : ℝ)) (hδ1 : Q.δ ≤ 1)
    (t : ℝ) (ht : t ∈ Ioc (p : ℝ) (p + 1)) :
    ‖cumulant (μ.restrict (Fev p))
      (fun j ω => zpowSign (sig j) (aTr Q.L Q.γ Q.δ p (Q.N (p + 1)) (a ω p) t (n j))) univ‖ ≤
      4 * (∏ j, jbr (latticePoint Q.L (n j))) ^ (-(2 * Q.Lambda (p + 1) : ℝ)) := by
  classical
  have hw4 : 4 ≤ 2 * m := by omega
  have hw : 2 * m ≤ 100 * Q.R (p + 1) := by omega
  have hL : 0 < Q.L := zero_lt_one.trans_le hLone
  have hc := ansatz_input_all_memLp ha hL hM
  have hcs := ansatz_input_summable ha hL
  have heq := cumulant_aTr_eq_order_sum_add_tail_add_error Q (inputsF Q R) sig hw4 (fun ω => a ω p)
    hc hcs hM p (Q.N (p + 1) ^ 4) t ht.1.le ht.2 n hsumF
  have hmain := layergarden_higher_sum_bound Q hGarden R p hp hR hLone hδ hsmall0
    m hm hmR sig hbal (Q.N (p + 1) ^ 4) le_rfl t ht n
  have htail := canonical_tail_exp_bound Q μ g a Fev R E Et p ha hδ hsmall hLone C hC hF hsumF
    hw4 sig n hd hp hw hN hNdim hLexp hCL hbN hbase hq hγ hδ1 t ht.1.le ht.2
  have herr := cmattr_error_exp_bound Q μ g hGaussian a Fev R E Et p ha hrapid hδ hsmall0 hLone C hC hF
    sig n hd hp hw hN hNdim hLexp hCL hbN hbase hγ hδ1 t ht.1.le ht.2
  let W : ℝ := (∏ j, jbr (latticePoint Q.L (n j))) ^ (-(2 * Q.Lambda (p + 1) : ℝ))
  have hW : 0 ≤ W := Real.rpow_nonneg (zero_le_one.trans (one_le_jbrProd Q.L n)) _
  have hmweight : jbrProd Q.L n ^ (-(4 * Q.Lambda (p + 1) : ℝ)) ≤ W :=
    Real.rpow_le_rpow_of_exponent_le (one_le_jbrProd Q.L n) (by
      have hΛ : (0 : ℝ) ≤ Q.Lambda (p + 1) := Nat.cast_nonneg _
      linarith)
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
