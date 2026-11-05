/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.XChain.CmattrFiniteErrorBound
public import WaveTurbulence.Foundations.XChain.GraftEnvelope
/-! The actual cmattr error in explicit-envelope form, ready for eventual absorption. -/
public section
namespace WaveTurbulence.Induct
open Finset MeasureTheory Set

theorem cmattr_error_envelope_bound (Q : WTParams) {Ω : Type*} [MeasurableSpace Ω]
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
    (hd : 1 ≤ Q.d) (hp : p < Q.D) (Ntop : ℕ)
    (hwidth : w * (2 * Ntop + 1) ≤ 2 * Q.R p)
    (hγ : Q.γ ≤ (Q.d : ℝ)) (hδ1 : Q.δ ≤ 1)
    (t : ℝ) (hpt : (p : ℝ) ≤ t) (htp : t ≤ (p : ℝ) + 1) :
    ‖cmattrError (μ.restrict (Fev p)) Q.L Q.γ Q.δ (inputsF Q R) sig
      (fun ω => a ω p) p Ntop (Q.N p) t n‖ ≤
      graftEnvelope Q.d w Ntop Q.L ((Q.Lambda p : ℝ) / 4) C * Real.exp (-(Q.N p : ℝ)) *
        (∏ j, jbr (latticePoint Q.L (n j))) ^ (-((Q.Lambda p : ℝ) / 4)) := by
  have h := ansatz_cmattr_error_bound Q μ g hG a Fev R E Et p ha hrapid hδ hsmall hLone C hC hF
    sig n hd hp Ntop hwidth hγ hδ1 t hpt htp
  exact h.trans_eq (by unfold graftEnvelope; ring)

end WaveTurbulence.Induct
