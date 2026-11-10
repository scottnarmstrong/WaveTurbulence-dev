/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.RegAsymp.GevreyEnvelope
public import WaveTurbulence.Foundations.ClassJR.MCSRep

/-! # Frequency envelopes from the exact J3 main-coefficient estimate

DH23 (maincoef2): its integrated Gevrey bound gives a single finite
frequency envelope for all orders required by the localized NT theorem.
This consumes the author's literal SymReg/dnorm/gev objects.
-/

public section
namespace WaveTurbulence.RegAsymp
open MeasureTheory ClassJR
open scoped ENNReal

/-- The common derivative envelope is integrable in frequency. This is
an analytic consequence of the maincoef2 field, not an extra RA1 premise. -/
theorem coefficient_derivative_envelope_le {ι : Type} [Fintype ι]
    {C : (ι → ℝ) → ℝ × ℝ → ℂ} (hC : SymReg C) {θ N A : ℝ}
    (hN : 0 ≤ N)
    (hmain : ∀ k, ∫⁻ α, ∫⁻ lam, wL θ lam * dnorm k C α lam ≤ gev N A k) :
    ∫⁻ lam, (∑' k : ℕ, ENNReal.ofReal (1 / ((4*k).factorial : ℝ)) *
      ∫⁻ α, wL θ lam * dnorm k C α lam) ≤
      ENNReal.ofReal N * ∑' k : ℕ, ENNReal.ofReal (A ^ k * ((2*k).factorial : ℝ) / (4*k).factorial) := by
  let G : ℕ → (ℝ × ℝ) → ℝ≥0∞ := fun k lam => ∫⁻ α, wL θ lam * dnorm k C α lam
  have hm (k : ℕ) : Measurable (fun z : (ι → ℝ) × (ℝ × ℝ) =>
      wL θ z.2 * dnorm k C z.1 z.2) :=
    ((measurable_wL θ).comp measurable_snd).mul (measurable_dnorm hC.smooth hC.meas k)
  have hGm (k : ℕ) : Measurable (G k) := (hm k).lintegral_prod_left'
  apply lintegral_gevrey_envelope_le G hGm hN
  intro k
  change (∫⁻ lam, ∫⁻ α, wL θ lam * dnorm k C α lam) ≤ _
  rw [← lintegral_lintegral_swap (hm k).aemeasurable]
  exact hmain k

end WaveTurbulence.RegAsymp
