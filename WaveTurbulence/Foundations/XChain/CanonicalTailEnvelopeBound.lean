/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.XChain.CanonicalFiniteTailBound
public import WaveTurbulence.Foundations.XChain.GraftEnvelope
/-! The actual proper-garden cutoff tail in explicit-envelope form, ready for eventual absorption. -/
public section
namespace WaveTurbulence.Induct
open Finset MeasureTheory Set

theorem canonical_tail_envelope_bound (Q : WTParams) {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (g : (Fin Q.d → ℤ) → Ω → ℂ)
    (a : Ω → ℝ → (Fin Q.d → ℤ) → ℂ) (Fev : ℕ → Set Ω)
    (R : ℕ → Mom Q.d → ℝ) (E : ℕ → (Fin Q.d → ℤ) → ℝ)
    (Et : ℕ → (m : ℕ) → (Fin (2 * m) → ℤˣ) → (Fin (2 * m) → (Fin Q.d → ℤ)) → ℂ)
    (p : ℕ) (ha : AnsatzAt Q μ g a Fev R E Et p)
    (hδ : 0 < Q.δ) (hsmall : Q.δ ^ (Q.ν / 2) ≤ 1 / 2) (hLone : 1 ≤ Q.L)
    (C : ℝ) (hC : 2 ≤ C)
    (hF : ∀ n, |inputsF Q R p (latticePoint Q.L n)| ≤
      C * jbr (latticePoint Q.L n) ^ (-(Q.Lambda p : ℝ)))
    (hsumF : ∀ q, Summable fun m : Fin Q.d → ℤ => |inputsF Q R q (latticePoint Q.L m)|)
    {w : ℕ} (hw : 4 ≤ w) (sig : Fin w → ℤˣ) (n : Fin w → (Fin Q.d → ℤ))
    (hd : 1 ≤ Q.d) (hp : p < Q.D) (Ntop Ncut : ℕ)
    (hwidth : w * (2 * Ntop + 1) ≤ 2 * Q.R p)
    (hγ : Q.γ ≤ (Q.d : ℝ)) (hδ1 : Q.δ ≤ 1)
    (t : ℝ) (hpt : (p : ℝ) ≤ t) (htp : t ≤ (p : ℝ) + 1) :
    ‖∑ᶠ LG : {LG : LayeredGarden w // IsCanonG (p + 1) LG ∧ LG.garden.sig = sig ∧
      LG.IsTrunc p Ntop (Q.N p)},
        if Ncut < LG.1.garden.order then KG Q.L Q.γ Q.δ (inputsF Q R) LG.1 t n else 0‖ ≤
      graftEnvelope Q.d w Ntop Q.L ((Q.Lambda p : ℝ) / 4) C *
        (Q.δ ^ (Q.ν / 2)) ^ ((Ncut + 1) - w * Ntop) *
          (∏ j, jbr (latticePoint Q.L (n j))) ^ (-((Q.Lambda p : ℝ) / 4)) := by
  have h := ansatz_canonical_kernel_tail_bound Q μ g a Fev R E Et p ha hδ hsmall hLone C hC hF hsumF
    hw sig n hd hp Ntop Ncut hwidth hγ hδ1 t hpt htp
  exact h.trans_eq (by unfold graftEnvelope; ring)

end WaveTurbulence.Induct
