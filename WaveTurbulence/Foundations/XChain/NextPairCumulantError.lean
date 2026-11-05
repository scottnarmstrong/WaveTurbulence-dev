/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.XChain.TruncatedRemainderCumulantBound
public import WaveTurbulence.Foundations.XChain.TruncatedEventChangeBound
public import WaveTurbulence.Foundations.XChain.HigherTailAbsorption
public import WaveTurbulence.Foundations.XChain.CmattrCoupleOrderSplit
public import WaveTurbulence.Foundations.XChain.CoupleAbsorbedTail
public import WaveTurbulence.Foundations.XChain.FiniteRangeCutoff
public import WaveTurbulence.Foundations.XChain.InductErrorBudget
/-! The actual five error contributions give the next higher-cumulant ansatz error. -/
public section
namespace WaveTurbulence.Induct
open Finset MeasureTheory Set
open scoped ENNReal

theorem ansatz_next_pair_cumulant_error_bound (Q : WTParams) {Ω : Type*} [MeasurableSpace Ω]
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
    (n : Fin 2 → (Fin Q.d → ℤ))
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
          jbr (latticePoint Q.L n) ^ (-(Q.Lambda (p + 1) : ℝ)))
    (hprob : μ.real (Fev p \ Fnew) ≤ Real.exp (-(4 * Q.N (p + 1) : ℝ)))
    (hRsize : 1000 * ((2 * (Cmom + 2) + 2) ^ 2 + 1) ≤ Q.R (p + 1))
 :
    ‖cumulant (μ.restrict Fnew) (fun j ω => zpowSign (![1, -1] j) (Anew ω (n j))) univ -
      ∑ N ∈ range (Q.N (p + 1) ^ 4 + 1), truncSum Q (inputsF Q R) (p + 1) N t ![1, -1] n‖ ≤
      (∏ j, jbr (latticePoint Q.L (n j))) ^ (-(Q.Lambda (p + 1) : ℝ)) *
        Real.exp (-(Q.N (p + 1) : ℝ)) := by
  classical
  let sig : Fin 2 → ℤˣ := ![1, -1]
  let W := (∏ j, jbr (latticePoint Q.L (n j))) ^ (-(Q.Lambda (p + 1) : ℝ))
  let K := (2 : ℝ) ^ 2 * (((2 * (Cmom + 2) + 2) * 2).factorial : ℝ)
  let X := fun j ω => zpowSign (sig j) (aTr Q.L Q.γ Q.δ p (Q.N (p + 1)) (a ω p) t (n j))
  let Z := cumulant (μ.restrict Fnew) (fun j ω => zpowSign (sig j) (Anew ω (n j))) univ
  let M := ∑ N ∈ range (Q.N (p + 1) ^ 4 + 1), truncSum Q (inputsF Q R) (p + 1) N t sig n
  let Mlow := ∑ N ∈ range (Q.N (p + 1) ^ 4 + 1), truncSum Q (inputsF Q R) (p + 1) N t sig n
  have hW : 0 ≤ W := Real.rpow_nonneg (zero_le_one.trans (one_le_jbrProd Q.L n)) _
  have hprod : (∏ j, jbr (latticePoint Q.L (n j)) ^ (-(Q.Lambda (p + 1) : ℝ))) = W :=
    Real.finsetProd_rpow univ _ (fun j _ => (jbr_pos _).le) _
  have hw : 2 ≤ 100 * Q.R (p + 1) := by nlinarith
  have hwidth : 2 * 2 ≤ 20 * Q.R (p + 1) := by nlinarith
  have hK : K ≤ Real.exp ((Q.N (p + 1) : ℝ) / 4) :=
    factorial_stage_loss_le_exp_quarter Q hd (p + 1) 2 (2 * (Cmom + 2)) (by omega) hRsize
  have hK0 : 0 ≤ K := mul_nonneg (by positivity) (Nat.cast_nonneg _)
  have h6 := ansatz_truncated_remainder_cumulant_bound Q μ g hGaussian a Fev R E Et p ha hrapid hM
    hGarden hTaylor hR hC2 hr hr1 hsmall2 hsmall0 hδ hsmall hLone C hC hF hsumF
    2 hwidth sig n hd hp hN hNdim hLexp hCL hbN hbase hq hγ hδ1 t ht B hB hφ hrest
    Cmom hCmom Fnew hnew hsub Anew hAnew hrem
  rw [hprod] at h6
  have h6' : ‖Z - cumulant (μ.restrict Fnew) X univ‖ ≤ Real.exp (-(39 / 4 * (Q.N (p + 1) : ℝ))) * W := by
    exact h6.trans (by simpa only [K, mul_assoc] using
      mul_le_mul_of_nonneg_right (remainder_cumulant_budget hK) hW)
  have h7 := ansatz_truncated_event_change_bound Q μ g hGaussian a Fev R E Et p ha hrapid hM
    hGarden hTaylor hR hC2 hr hr1 hsmall2 hsmall0 hδ hsmall hLone C hC hF hsumF
    (univ : Finset (Fin 2)) ⟨⟨0, by omega⟩, mem_univ _⟩ (by simpa using hwidth) sig n
    hd hp hN hNdim hLexp hCL hbN hbase hq hγ hδ1 t ht B hB hφ hrest Cmom hCmom Fnew hnew hsub
  have hW2 : (∏ j, jbr (latticePoint Q.L (n j)) ^ (-(2 * Q.Lambda (p + 1) : ℝ))) ≤ W := by
    rw [Real.finsetProd_rpow univ _ (fun j _ => (jbr_pos _).le) _]
    apply Real.rpow_le_rpow_of_exponent_le (one_le_jbrProd Q.L n)
    have hΛ : (0 : ℝ) ≤ Q.Lambda (p + 1) := Nat.cast_nonneg _
    linarith
  simp only [card_univ, Fintype.card_fin] at h7
  have h7' : ‖cumulant (μ.restrict Fnew) X univ - cumulant (μ.restrict (Fev p)) X univ‖ ≤
      Real.exp (-(7 / 4 * (Q.N (p + 1) : ℝ))) * W := by
    have hh := mul_le_mul (event_change_budget hprob hK0 hK) hW2
      (prod_nonneg fun j _ => Real.rpow_nonneg (jbr_pos _).le _) (Real.exp_pos _).le
    exact h7.trans (by simpa only [K, mul_assoc] using hh)
  have hc := ansatz_input_all_memLp ha (zero_lt_one.trans_le hLone) hM
  have hcs := ansatz_input_summable ha (zero_lt_one.trans_le hLone)
  have heq := cumulant_aTr_couple_eq_order_sum_add_tail_add_error Q (inputsF Q R)
    (fun ω => a ω p) hc hcs hM p (Q.N (p + 1) ^ 4) t ht.1.le ht.2 n hsumF
  have herr := cmattr_error_exp_bound Q μ g hGaussian a Fev R E Et p ha hrapid hδ hsmall0 hLone C hC hF
    sig n hd hp hw hN hNdim hLexp hCL hbN hbase hγ hδ1 t ht.1.le ht.2
  have htail := couple_tail_exp_bound Q μ g a Fev R E Et p ha hδ hsmall hLone C hC hF hsumF
    n hd hp hw hN hNdim hLexp hCL hbN hbase hq hγ hδ1 t ht.1.le ht.2
  have hwe : (∏ j, jbr (latticePoint Q.L (n j))) ^ (-((Q.Lambda p : ℝ) / 4)) ≤ W := by
    apply Real.rpow_le_rpow_of_exponent_le (one_le_jbrProd Q.L n)
    have hLambdaCompare := lambda_quarter_ge_twice_succ Q hd hp
    have hΛ : (0 : ℝ) ≤ Q.Lambda (p + 1) := Nat.cast_nonneg _
    linarith
  have hexp0 : 0 ≤ Real.exp (-(20 * (Q.N (p + 1) : ℝ))) := (Real.exp_pos _).le
  have hcore : ‖cumulant (μ.restrict (Fev p)) X univ - M‖ ≤
      2 * Real.exp (-(20 * (Q.N (p + 1) : ℝ))) * W := by
    dsimp only [X]
    rw [heq]
    change ‖(M + _ + _) - M‖ ≤ _
    have he (a b c : ℂ) : (a + b + c) - a = b + c := by ring
    rw [he]
    have hbound := mul_le_mul_of_nonneg_left hwe hexp0
    exact (norm_add_le _ _).trans ((add_le_add htail herr).trans (by nlinarith))
  have h3' : ‖M - Mlow‖ ≤ Real.exp (-(20 * (Q.N (p + 1) : ℝ))) * W := by
    change ‖M - M‖ ≤ _
    rw [sub_self, norm_zero]
    exact mul_nonneg hexp0 hW
  have htotal : ‖Z - Mlow‖ ≤
      (Real.exp (-(39 / 4 * (Q.N (p + 1) : ℝ))) +
       Real.exp (-(7 / 4 * (Q.N (p + 1) : ℝ))) +
       3 * Real.exp (-(20 * (Q.N (p + 1) : ℝ)))) * W := by
    have he : Z - Mlow = (Z - cumulant (μ.restrict Fnew) X univ) +
      (cumulant (μ.restrict Fnew) X univ - cumulant (μ.restrict (Fev p)) X univ) +
      (cumulant (μ.restrict (Fev p)) X univ - M) + (M - Mlow) := by ring
    rw [he]
    have hn := (norm_add_le _ _).trans (add_le_add ((norm_add_le _ _).trans
      (add_le_add ((norm_add_le _ _).trans (add_le_add h6' h7')) hcore)) h3')
    exact hn.trans_eq (by ring)
  have hN0 : (0 : ℝ) ≤ Q.N (p + 1) := Nat.cast_nonneg _
  have hN4 : (4 : ℝ) ≤ Q.N (p + 1) := by exact_mod_cast (show 4 ≤ Q.N (p + 1) by omega)
  have he6 : Real.exp (-(39 / 4 * (Q.N (p + 1) : ℝ))) ≤ Real.exp (-(7 / 4 * (Q.N (p + 1) : ℝ))) :=
    Real.exp_le_exp.mpr (by linarith)
  have he20 : Real.exp (-(20 * (Q.N (p + 1) : ℝ))) ≤ Real.exp (-(7 / 4 * (Q.N (p + 1) : ℝ))) :=
    Real.exp_le_exp.mpr (by linarith)
  have hb := five_errors_budget hN4
  exact htotal.trans (by nlinarith [mul_le_mul_of_nonneg_right he6 hW,
    mul_le_mul_of_nonneg_right he20 hW, mul_le_mul_of_nonneg_right hb hW])

end WaveTurbulence.Induct
