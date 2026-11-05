/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.XChain.CoupleFiniteTailBound
public import WaveTurbulence.Foundations.XChain.GraftEnvelope
/-! The actual couple cutoff tail in explicit-envelope form. -/
public section
namespace WaveTurbulence.Induct
open Finset MeasureTheory Set

theorem couple_tail_envelope_bound (Q : WTParams) {Ω : Type*} [MeasurableSpace Ω]
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
    (n : Fin 2 → (Fin Q.d → ℤ))
    (hd : 1 ≤ Q.d) (hp : p < Q.D) (Ntop Ncut : ℕ)
    (hwidth : 2 * (2 * Ntop + 1) ≤ 2 * Q.R p)
    (hγ : Q.γ ≤ (Q.d : ℝ)) (hδ1 : Q.δ ≤ 1)
    (t : ℝ) (hpt : (p : ℝ) ≤ t) (htp : t ≤ (p : ℝ) + 1) :
    ‖∑ᶠ LG : {LG : LayeredGarden 2 // IsCanonC (p + 1) LG ∧
      LG.IsTrunc p Ntop (Q.N p)},
        if Ncut < LG.1.garden.order then KG Q.L Q.γ Q.δ (inputsF Q R) LG.1 t n else 0‖ ≤
      graftEnvelope Q.d 2 Ntop Q.L ((Q.Lambda p : ℝ) / 4) C *
        (Q.δ ^ (Q.ν / 2)) ^ ((Ncut + 1) - 2 * Ntop) *
          (∏ j, jbr (latticePoint Q.L (n j))) ^ (-((Q.Lambda p : ℝ) / 4)) := by
  have h := ansatz_couple_kernel_tail_bound Q μ g a Fev R E Et p ha hδ hsmall hLone C hC hF hsumF
    n hd hp Ntop Ncut hwidth hγ hδ1 t hpt htp
  exact h.trans_eq (by unfold graftEnvelope; ring)

end WaveTurbulence.Induct
