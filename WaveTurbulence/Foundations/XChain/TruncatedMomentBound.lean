/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.XChain.TruncatedCumulantBound
public import WaveTurbulence.Foundations.XChain.WeightedMomentFromCumulants
public import WaveTurbulence.Foundations.XChain.OrderedBlockProducts
/-! Actual aTr moments retain every individual spatial weight, with only the proved factorial loss. -/
public section
namespace WaveTurbulence.Induct
open Finset MeasureTheory Set
open scoped ENNReal

theorem ansatz_truncated_moment_bound (Q : WTParams) {Ω : Type*} [MeasurableSpace Ω]
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
    (hwidth : s.card ≤ 20 * Q.R (p + 1)) (sig : ι → ℤˣ) (n : ι → (Fin Q.d → ℤ))
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
    ‖∫ ω in Fev p, ∏ j ∈ s, zpowSign (sig j)
      (aTr Q.L Q.γ Q.δ p (Q.N (p + 1)) (a ω p) t (n j)) ∂μ‖ ≤
      (((Cmom + 2) * s.card).factorial : ℝ) *
        ∏ j ∈ s, jbr (latticePoint Q.L (n j)) ^ (-(2 * Q.Lambda (p + 1) : ℝ)) := by
  classical
  let X : ι → Ω → ℂ := fun j ω => zpowSign (sig j)
    (aTr Q.L Q.γ Q.δ p (Q.N (p + 1)) (a ω p) t (n j))
  apply norm_moment_le_of_weighted_cumulants (μ.restrict (Fev p)) X s hs Cmom
    (fun j => jbr (latticePoint Q.L (n j)) ^ (-(2 * Q.Lambda (p + 1) : ℝ)))
    (fun j => Real.rpow_nonneg (jbr_pos _).le _)
  intro A hAs hA
  have hcard : 1 ≤ A.card := hA.card_pos
  have hcardR : A.card ≤ 20 * Q.R (p + 1) := (Finset.card_le_card hAs).trans hwidth
  have hc := ansatz_truncated_cumulant_bound Q μ g hGaussian a Fev R E Et p ha hrapid hM
    hGarden hTaylor hR hC2 hr hr1 hsmall2 hsmall0 hδ hsmall hLone C hC hF hsumF
    hcard hcardR (fun j => sig (A.equivFin.symm j).1) (fun j => n (A.equivFin.symm j).1)
    hd hp hN hNdim hLexp hCL hbN hbase hq hγ hδ1 t ht B hB hφ hrest
  have he := cumulant_ordered_block (μ.restrict (Fev p)) X A
  have hp := prod_ordered_block A (fun j => jbr (latticePoint Q.L (n j)))
  rw [he, hp] at hc
  have hw := Real.finsetProd_rpow A (fun j => jbr (latticePoint Q.L (n j)))
    (fun j _ => (jbr_pos _).le) (-(2 * Q.Lambda (p + 1) : ℝ))
  rw [← hw] at hc
  have hmul : Cmom ≤ Cmom * A.card := by
    simpa only [mul_one] using Nat.mul_le_mul_left Cmom hcard
  have hfactorNat : Cmom ≤ (Cmom * A.card).factorial := hmul.trans (Nat.self_le_factorial _)
  have hfactor : B + 4 ≤ ((Cmom * A.card).factorial : ℝ) :=
    hCmom.trans (by exact_mod_cast hfactorNat)
  exact hc.trans (mul_le_mul_of_nonneg_right hfactor
    (prod_nonneg (fun j _ => Real.rpow_nonneg (jbr_pos _).le _)))

end WaveTurbulence.Induct
