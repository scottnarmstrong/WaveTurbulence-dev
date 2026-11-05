/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.XChain.TruncatedMomentBound
public import WaveTurbulence.Foundations.XChain.SignedNormSquare
public import WaveTurbulence.Foundations.XChain.TruncatedAllMoments
/-! The actual weighted squared-product moment bound needed by conditional Cauchy-Schwarz. -/
public section
namespace WaveTurbulence.Induct
open Finset MeasureTheory Set
open scoped ENNReal

theorem ansatz_truncated_L2_moment_bound (Q : WTParams) {Ω : Type*} [MeasurableSpace Ω]
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
    (Cmom : ℕ) (hCmom : B + 4 ≤ Cmom) :
    (∫ ω in Fev p, ‖∏ j ∈ s, zpowSign (sig j)
      (aTr Q.L Q.γ Q.δ p (Q.N (p + 1)) (a ω p) t (n j))‖ ^ 2 ∂μ) ≤
      (((((2 * (Cmom + 2)) * s.card).factorial : ℝ) *
        ∏ j ∈ s, jbr (latticePoint Q.L (n j)) ^ (-(2 * Q.Lambda (p + 1) : ℝ))) ^ 2) := by
  classical
  let τ : Fin 2 × ↥s → ℤˣ := fun x => if x.1 = 0 then sig x.2.1 else -sig x.2.1
  let labels : Fin 2 × ↥s → (Fin Q.d → ℤ) := fun x => n x.2.1
  let z := fun ω j => aTr Q.L Q.γ Q.δ p (Q.N (p + 1)) (a ω p) t (n j)
  let weight := fun j => jbr (latticePoint Q.L (n j)) ^ (-(2 * Q.Lambda (p + 1) : ℝ))
  obtain ⟨j0, hj0⟩ := hs
  have hne : (univ : Finset (Fin 2 × ↥s)).Nonempty := ⟨(0, ⟨j0, hj0⟩), mem_univ _⟩
  have hcard : (univ : Finset (Fin 2 × ↥s)).card = 2 * s.card := by simp
  have hm := ansatz_truncated_moment_bound Q μ g hGaussian a Fev R E Et p ha hrapid hM
    hGarden hTaylor hR hC2 hr hr1 hsmall2 hsmall0 hδ hsmall hLone C hC hF hsumF
    (univ : Finset (Fin 2 × ↥s)) hne (by simpa only [hcard] using hwidth) τ labels
    hd hp hN hNdim hLexp hCL hbN hbase hq hγ hδ1 t ht B hB hφ hrest Cmom hCmom
  have hpoint (ω : Ω) : ((‖∏ j ∈ s, zpowSign (sig j) (z ω j)‖ ^ 2 : ℝ) : ℂ) =
      ∏ x : Fin 2 × ↥s, zpowSign (τ x) (z ω x.2.1) := by
    have hp := signed_product_norm_sq (fun j : ↥s => sig j.1) (fun j : ↥s => z ω j.1)
    have he := prod_coe_sort s (fun j => zpowSign (sig j) (z ω j))
    rw [he] at hp
    simpa only [Complex.ofReal_pow] using hp
  have hint : ((∫ ω in Fev p, ‖∏ j ∈ s, zpowSign (sig j) (z ω j)‖ ^ 2 ∂μ : ℝ) : ℂ) =
      ∫ ω in Fev p, ∏ x : Fin 2 × ↥s, zpowSign (τ x) (z ω x.2.1) ∂μ := by
    rw [← integral_complex_ofReal]
    exact integral_congr_ae (Filter.Eventually.of_forall hpoint)
  have hw : (∏ x : Fin 2 × ↥s, weight x.2.1) = (∏ j ∈ s, weight j) ^ 2 := by
    rw [Fintype.prod_prod_type, Fin.prod_univ_two]
    rw [prod_coe_sort s weight]
    ring
  have hfactor : (Cmom + 2) * (2 * s.card) = (2 * (Cmom + 2)) * s.card := by ring
  simp only [hcard, hfactor] at hm
  change ‖∫ ω in Fev p, ∏ x : Fin 2 × ↥s, zpowSign (τ x) (z ω x.2.1) ∂μ‖ ≤
    ((((2 * (Cmom + 2)) * s.card).factorial : ℝ) * ∏ x : Fin 2 × ↥s, weight x.2.1) at hm
  rw [hw, ← hint, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (integral_nonneg (fun ω => sq_nonneg _))] at hm
  have hF : 1 ≤ ((((2 * (Cmom + 2)) * s.card).factorial : ℕ) : ℝ) := by
    exact_mod_cast (Nat.succ_le_of_lt (Nat.factorial_pos _))
  have hF' : ((((2 * (Cmom + 2)) * s.card).factorial : ℕ) : ℝ) ≤
      (((((2 * (Cmom + 2)) * s.card).factorial : ℕ) : ℝ)) ^ 2 := by nlinarith
  exact hm.trans ((mul_le_mul_of_nonneg_right hF' (sq_nonneg (∏ j ∈ s, weight j))).trans_eq (by ring))

end WaveTurbulence.Induct
