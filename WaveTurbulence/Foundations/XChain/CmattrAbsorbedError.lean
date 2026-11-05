/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.XChain.CmattrEnvelopeBound
public import WaveTurbulence.Foundations.XChain.GraftStageEnvelope
public import WaveTurbulence.Foundations.XChain.InductDecayParameters
/-! The actual cmattr input error has the required exponentially small stagewise size. -/
public section
namespace WaveTurbulence.Induct
open Finset MeasureTheory Set

theorem cmattr_error_exp_bound (Q : WTParams) {Ω : Type*} [MeasurableSpace Ω]
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
    {w : ℕ} (sig : Fin w → ℤˣ) (n : Fin w → (Fin Q.d → ℤ))
    (hd : 1 ≤ Q.d) (hp : p < Q.D)
    (hw : w ≤ 100 * Q.R (p + 1))
    (hN : 2000000 ≤ Q.N (p + 1)) (hNdim : 2 * Q.d + 4 ≤ Q.N (p + 1))
    (hLexp : Real.exp 2 ≤ Q.L) (hCL : C ≤ Q.L)
    (hbN : (Q.Lambda p : ℝ) / 4 ≤ Q.N (p + 1)) (hbase : baseLatticeSum Q.d ≤ Q.L)
    (hγ : Q.γ ≤ (Q.d : ℝ)) (hδ1 : Q.δ ≤ 1)
    (t : ℝ) (hpt : (p : ℝ) ≤ t) (htp : t ≤ (p : ℝ) + 1) :
    ‖cmattrError (μ.restrict (Fev p)) Q.L Q.γ Q.δ (inputsF Q R) sig
      (fun ω => a ω p) p (Q.N (p + 1)) (Q.N p) t n‖ ≤
      Real.exp (-(20 * (Q.N (p + 1) : ℝ))) *
        (∏ j, jbr (latticePoint Q.L (n j))) ^ (-((Q.Lambda p : ℝ) / 4)) := by
  have hwidth := top_leaf_count_le_previous_range Q hd hp (by omega) hw
  have henv := stage_graftEnvelope_bound Q hd p hLexp C ((Q.Lambda p : ℝ) / 4)
    (by linarith) hCL (lambda_quarter_ge_dimension Q hd hp) hbN hbase hNdim hw
  have hsmall' := envelope_times_input_error_le_exp Q hd hp hN henv
  have he := cmattr_error_envelope_bound Q μ g hG a Fev R E Et p ha hrapid hδ hsmall hLone C hC hF
    sig n hd hp (Q.N (p + 1)) hwidth hγ hδ1 t hpt htp
  exact he.trans (mul_le_mul_of_nonneg_right hsmall'
    (Real.rpow_nonneg (zero_le_one.trans (one_le_jbrProd Q.L n)) _))

end WaveTurbulence.Induct
