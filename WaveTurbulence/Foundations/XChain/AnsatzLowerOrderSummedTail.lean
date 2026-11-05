/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.XChain.AnsatzLowerOrderTail
public import WaveTurbulence.Foundations.XChain.LowerOrderTail
public import WaveTurbulence.Foundations.XChain.ForestWeightedNormSum
public import WaveTurbulence.Foundations.XChain.InductDecayParameters
public import WaveTurbulence.Foundations.XChain.FiniteProductTailBound
public import WaveTurbulence.Foundations.XChain.PartitionWeightProduct
public import WaveTurbulence.Foundations.XChain.OrderedBlockProducts
public import WaveTurbulence.Foundations.XChain.TopPartitionError
/-! The actual attached-order tail retains geometric and external-momentum decay after decoration summation. -/
public section
namespace WaveTurbulence.Induct
open Finset MeasureTheory Set

theorem ansatz_lower_order_tail_bound (Q : WTParams) {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (g : (Fin Q.d → ℤ) → Ω → ℂ)
    (a : Ω → ℝ → (Fin Q.d → ℤ) → ℂ) (Fev : ℕ → Set Ω)
    (R : ℕ → Mom Q.d → ℝ) (E : ℕ → (Fin Q.d → ℤ) → ℝ)
    (Et : ℕ → (m : ℕ) → (Fin (2 * m) → ℤˣ) → (Fin (2 * m) → (Fin Q.d → ℤ)) → ℂ)
    (p : ℕ) (ha : AnsatzAt Q μ g a Fev R E Et p)
    (hδ : 0 < Q.δ) (hsmall : Q.δ ^ (Q.ν / 2) ≤ 1 / 2) (hLone : 1 ≤ Q.L)
    (C : ℝ) (hC : 2 ≤ C)
    (hF : ∀ n, |inputsF Q R p (latticePoint Q.L n)| ≤
      C * jbr (latticePoint Q.L n) ^ (-(Q.Lambda p : ℝ)))
    {w : ℕ} (sig : Fin w → ℤˣ) (top : Fin w → TTree)
    (P : Finpartition (univ : Finset (GLeaf top)))
    (n : Fin w → (Fin Q.d → ℤ)) (hd : 1 ≤ Q.d) (hp : p < Q.D) (t : ℝ)
    (J : ℕ) (hR : ∀ B : P.parts, B.1.card ≤ 2 * Q.R p) :
    ‖lowerOrderTail Q.L Q.γ Q.δ (inputsF Q R) sig top P p (Q.N p) J t n‖ ≤
      ((∏ j, SysAPI.boxVol (top j) p t) * C ^ P.parts.card *
        ((Q.δ ^ (Q.ν / 2)) ^ J * 2 ^ P.parts.card)) *
          ((2 ^ Fintype.card (GLeaf top) : ℝ) ^ ((Q.Lambda p : ℝ) / 4) *
            (∏ j, jbr (latticePoint Q.L (n j))) ^ (-((Q.Lambda p : ℝ) / 4)) *
              (∑' m : Fin Q.d → ℤ, jbr (latticePoint Q.L m) ^ (-((Q.Lambda p : ℝ) / 4))) ^
                Fintype.card (GLeaf top)) := by
  classical
  have hC0 : 0 ≤ C := by linarith
  have hbox : 0 ≤ ∏ j, SysAPI.boxVol (top j) p t :=
    prod_nonneg (fun j _ => SysAPI.boxVol_nonneg (top j) p t)
  have htail : 0 ≤ (Q.δ ^ (Q.ν / 2)) ^ J * 2 ^ P.parts.card :=
    mul_nonneg (pow_nonneg (Real.rpow_nonneg hδ.le _) _) (by positivity)
  apply norm_tsum_le_of_forest_bracket_bound top n Q.L ((Q.Lambda p : ℝ) / 4)
    ((∏ j, SysAPI.boxVol (top j) p t) * C ^ P.parts.card *
      ((Q.δ ^ (Q.ν / 2)) ^ J * 2 ^ P.parts.card)) hLone
    (lambda_quarter_ge_dimension Q hd hp)
    (mul_nonneg (mul_nonneg hbox (pow_nonneg hC0 _)) htail)
    (lowerOrderTailIntegrand Q.L Q.γ Q.δ (inputsF Q R) sig top P p (Q.N p) J t n)
  intro κ
  have he := ansatz_lower_order_product_tail_bound Q μ g a Fev R E Et p ha hδ hsmall hLone
    C hC hF sig top P κ J hR
  have hc := norm_prod_topTreeCoefficient_le Q.L Q.γ Q.δ p top sig n κ (fun _ => t)
  unfold lowerOrderTailIntegrand
  rw [norm_mul]
  have h := mul_le_mul hc he (norm_nonneg _) hbox
  exact h.trans_eq (by
    have hexp : -(2 * ((Q.Lambda p : ℝ) / 4)) = -(Q.Lambda p : ℝ) / 2 := by ring
    rw [hexp]
    ring)

end WaveTurbulence.Induct
