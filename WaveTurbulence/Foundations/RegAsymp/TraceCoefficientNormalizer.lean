/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.RegAsymp.TraceCoefficientEnvelope
public import WaveTurbulence.Foundations.RegAsymp.DerivativeCoefficientNormalizer

/-! # The Wick coefficient trace has an actual strongly weighted NT normalizer -/

public section
noncomputable section
namespace WaveTurbulence.RegAsymp
open MeasureTheory ClassJR WithLp
open scoped ContDiff ENNReal

/-- The source maincoef2 field alone supplies every derivative budget
needed by the lower-dimensional Wick correction, with a quantitative
strong-frequency mass and no dimension-to-the-order loss. -/
theorem trace_coefficient_NT_normalizer {ι : Type} [Fintype ι] [DecidableEq ι]
    {C : (Option ι → ℝ) → ℝ × ℝ → ℂ} (hC : SymReg C) {θ N A : ℝ}
    (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1) (hN : 0 ≤ N) (hA : 0 ≤ A)
    (hmain : ∀ k, ∫⁻ α, ∫⁻ lam, wL θ lam*dnorm k C α lam ≤ gev N A k) :
    ∃ g : (ℝ × ℝ) → ℝ, Measurable g ∧ Integrable g ∧ (∀ lam, 0 < g lam) ∧
      (∫⁻ lam, wL θ lam*ENNReal.ofReal (g lam)) < ⊤ ∧
      (∫⁻ lam, wL θ lam*ENNReal.ofReal (g lam)) ≤
        ENNReal.ofReal N*((∑' k : ℕ, ENNReal.ofReal (A^k*((2*k).factorial:ℝ)/(4*k).factorial))+
          (∑' k : ℕ, ENNReal.ofReal (A^(k+1)*((2*(k+1)).factorial:ℝ)/(4*k).factorial)))+
            (∫⁻ lam, wL θ lam*ENNReal.ofReal (frequencyGaussian lam)) ∧
      ∀ᵐ lam : ℝ × ℝ,
        ContDiff ℝ ∞ (fun x : EuclideanSpace ℝ ι => (g lam)⁻¹ • traceSymbol C (ofLp x) lam) ∧
        ApproxNT.WordDerivL1 (fun x : EuclideanSpace ℝ ι => (g lam)⁻¹ • traceSymbol C (ofLp x) lam)
          (fun k => ((4*k).factorial:ℝ)) := by
  obtain ⟨g,hgm,hgi,hgp,hgf,hmass,hgood⟩ := derivative_NT_normalizer_of_envelope_mass
    (symReg_traceSymbol hC) hθ0 hθ1 (derivativeCoefficientEnvelope_trace_mass_lt_top hC hN hA hmain)
  refine ⟨g,hgm,hgi,hgp,hgf,?_,hgood⟩
  rw [hmass]
  exact add_le_add (derivativeCoefficientEnvelope_trace_mass_le hC hN hmain) le_rfl

end WaveTurbulence.RegAsymp
