/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.XChain.AnsatzBlockKernelBound
public import WaveTurbulence.Foundations.XChain.AnsatzBlockResidual
public import WaveTurbulence.Foundations.XChain.TopPartitionBracketBound
public import WaveTurbulence.Foundations.XChain.InductDecayParameters
public import WaveTurbulence.Foundations.XChain.OrderedBlockProducts
public import WaveTurbulence.Foundations.XChain.TopPartitionError
/-! Actual source input errors give the externally weighted decoration-summed cmattr error. -/
public section
namespace WaveTurbulence.Induct
open Finset MeasureTheory Set

theorem ansatz_partition_error_bound (Q : WTParams) {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (g : (Fin Q.d → ℤ) → Ω → ℂ)
    (hG : IsGaussianData μ g)
    (a : Ω → ℝ → (Fin Q.d → ℤ) → ℂ) (Fev : ℕ → Set Ω)
    (R : ℕ → Mom Q.d → ℝ) (E : ℕ → (Fin Q.d → ℤ) → ℝ)
    (Et : ℕ → (m : ℕ) → (Fin (2 * m) → ℤˣ) → (Fin (2 * m) → (Fin Q.d → ℤ)) → ℂ)
    (p : ℕ) (ha : AnsatzAt Q μ g a Fev R E Et p)
    (hrapid : ∀ ω ∈ Fev p, IsRapidDecay (initialCoeff Q.L Q.φin g ω))
    (hδ : 0 < Q.δ) (hsmall : Q.δ ^ Q.ν ≤ 1 / 2) (hLone : 1 ≤ Q.L)
    (C : ℝ) (hC : 2 ≤ C)
    (hF : ∀ n, |inputsF Q R p (latticePoint Q.L n)| ≤
      C * jbr (latticePoint Q.L n) ^ (-(Q.Lambda p : ℝ)))
    {w : ℕ} (sig : Fin w → ℤˣ) (top : Fin w → TTree)
    (P : Finpartition (univ : Finset (GLeaf top)))
    (n : Fin w → (Fin Q.d → ℤ)) (hd : 1 ≤ Q.d) (hp : p < Q.D)
    (t : ℝ) (hR : ∀ B : P.parts, B.1.card ≤ 2 * Q.R p) :
    ‖topPartitionError (μ.restrict (Fev p)) Q.L Q.γ Q.δ (inputsF Q R)
      sig top P (fun ω => a ω p) p (Q.N p) t n‖ ≤
      (∏ j, SysAPI.boxVol (top j) p t) *
        (2 ^ P.parts.card * Real.exp (-(Q.N p : ℝ)) * C ^ P.parts.card *
          (2 ^ Fintype.card (GLeaf top) : ℝ) ^ ((Q.Lambda p : ℝ) / 4) *
            (∏ j, jbr (latticePoint Q.L (n j))) ^ (-((Q.Lambda p : ℝ) / 4)) *
              (∑' m : Fin Q.d → ℤ, jbr (latticePoint Q.L m) ^ (-((Q.Lambda p : ℝ) / 4))) ^
                Fintype.card (GLeaf top)) := by
  classical
  have hexp : -(2 * ((Q.Lambda p : ℝ) / 4)) = -(Q.Lambda p : ℝ) / 2 := by ring
  apply norm_topPartitionError_le_of_bracket_weights (μ.restrict (Fev p)) Q.L Q.γ Q.δ
    (inputsF Q R) sig top P (fun ω => a ω p) p (Q.N p) t n
    ((Q.Lambda p : ℝ) / 4) hLone (lambda_quarter_ge_dimension Q hd hp)
    C (Real.exp (-(Q.N p : ℝ))) (by linarith) (Real.exp_pos _).le
    (Real.exp_le_one_iff.mpr (neg_nonpos.mpr (Nat.cast_nonneg _)))
  · intro κ B
    rw [hexp]
    exact ansatz_topBlock_kernel_bound Q μ g a Fev R E Et p ha hδ hsmall hLone C hC hF
      sig top P κ B (hR B)
  · intro κ B
    rw [hexp]
    have he := ansatz_topBlock_residual_bound Q μ g hG (zero_lt_one.trans_le hLone)
      a Fev R E Et p ha hrapid sig top P κ B (hR B)
    have hw : 0 ≤ (∏ l ∈ B.1, jbr (latticePoint Q.L (κ.1 l.toNode))) ^
        (-(Q.Lambda p : ℝ) / 2) := Real.rpow_nonneg
      (prod_nonneg (fun l _ => (jbr_pos _).le)) _
    have hcW : (∏ l ∈ B.1, jbr (latticePoint Q.L (κ.1 l.toNode))) ^ (-(Q.Lambda p : ℝ) / 2) ≤
        C * (∏ l ∈ B.1, jbr (latticePoint Q.L (κ.1 l.toNode))) ^ (-(Q.Lambda p : ℝ) / 2) := by
      nlinarith
    exact he.trans (by
      rw [mul_comm _ (Real.exp (-(Q.N p : ℝ)))]
      exact mul_le_mul_of_nonneg_left hcW (Real.exp_pos _).le)

end WaveTurbulence.Induct
