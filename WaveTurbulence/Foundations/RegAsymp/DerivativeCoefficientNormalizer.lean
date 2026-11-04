/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.RegAsymp.CoefficientNormalizer

/-! # Strongly time-weighted normalizer from derivative bounds alone -/

public section
noncomputable section
namespace WaveTurbulence.RegAsymp
open MeasureTheory ClassJR WithLp
open scoped ENNReal ContDiff

/-- Finite mass of the literal derivative envelope supplies a positive NT
normalizer. This form also applies to coefficient traces, whose bounds
contain a fixed derivative shift rather than a single Gevrey model. -/
theorem derivative_NT_normalizer_of_envelope_mass {ι : Type} [Fintype ι] [DecidableEq ι]
    {C : (ι → ℝ) → ℝ × ℝ → ℂ} (hC : SymReg C) {θ : ℝ}
    (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1)
    (hfin : (∫⁻ lam, wL θ lam*derivativeCoefficientEnvelope C lam) < ⊤) :
    ∃ g : (ℝ × ℝ) → ℝ, Measurable g ∧ Integrable g ∧ (∀ lam, 0 < g lam) ∧
      (∫⁻ lam, wL θ lam*ENNReal.ofReal (g lam)) < ⊤ ∧
      (∫⁻ lam, wL θ lam*ENNReal.ofReal (g lam)) =
        (∫⁻ lam, wL θ lam*derivativeCoefficientEnvelope C lam)+
          (∫⁻ lam, wL θ lam*ENNReal.ofReal (frequencyGaussian lam)) ∧
      ∀ᵐ lam : ℝ × ℝ,
        ContDiff ℝ ∞ (fun x : EuclideanSpace ℝ ι => (g lam)⁻¹ • C (ofLp x) lam) ∧
        ApproxNT.WordDerivL1 (fun x : EuclideanSpace ℝ ι => (g lam)⁻¹ • C (ofLp x) lam)
          (fun k => ((4*k).factorial:ℝ)) := by
  obtain ⟨g,hgm,hgi,hgp,hdom,hmass⟩ := exists_positive_weighted_envelope
    (measurable_derivativeCoefficientEnvelope hC) (measurable_wL θ) (one_le_wL hθ0) hfin
    measurable_frequencyGaussian integrable_frequencyGaussian frequencyGaussian_pos
  refine ⟨g,hgm,hgi,hgp,?_,?_,?_⟩
  · rw [hmass]
    exact ENNReal.add_lt_top.mpr ⟨hfin,lintegral_wL_frequencyGaussian_lt_top hθ1⟩
  · exact hmass
  · filter_upwards [hdom] with lam hd
    have hder (k : ℕ) : (∫⁻ α, dnorm k C α lam) ≤ ENNReal.ofReal (g lam*(4*k).factorial) := by
      calc
        _ ≤ ENNReal.ofReal ((4*k).factorial:ℝ)*derivativeCoefficientEnvelope C lam :=
          derivativeCoefficientEnvelope_dominates C k lam
        _ ≤ ENNReal.ofReal ((4*k).factorial:ℝ)*ENNReal.ofReal (g lam) := mul_le_mul' le_rfl hd
        _ = _ := by rw [← ENNReal.ofReal_mul (by positivity)]; congr 1; ring
    exact ⟨normalized_symbol_contDiff (hC.smooth lam) (g lam),
      normalized_symbol_wordDeriv (hC.smooth lam) (hgp lam) hder⟩


/-- The high-frequency branch retains J3's stronger θ weight because
its normalizer uses only maincoef2, never the weaker moment field. -/
theorem derivative_coefficient_NT_normalizer {ι : Type} [Fintype ι] [DecidableEq ι]
    {C : (ι → ℝ) → ℝ × ℝ → ℂ} (hC : SymReg C) {θ N A : ℝ}
    (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1) (hN : 0 ≤ N) (hA : 0 ≤ A)
    (hmain : ∀ k, ∫⁻ α, ∫⁻ lam, wL θ lam*dnorm k C α lam ≤ gev N A k) :
    ∃ g : (ℝ × ℝ) → ℝ, Measurable g ∧ Integrable g ∧ (∀ lam, 0 < g lam) ∧
      (∫⁻ lam, wL θ lam*ENNReal.ofReal (g lam)) < ⊤ ∧
      (∫⁻ lam, wL θ lam*ENNReal.ofReal (g lam)) ≤
        ENNReal.ofReal N*(∑' k : ℕ, ENNReal.ofReal (A^k*((2*k).factorial:ℝ)/(4*k).factorial)) +
          ∫⁻ lam, wL θ lam*ENNReal.ofReal (frequencyGaussian lam) ∧
      ∀ᵐ lam : ℝ × ℝ,
        ContDiff ℝ ∞ (fun x : EuclideanSpace ℝ ι => (g lam)⁻¹ • C (ofLp x) lam) ∧
        ApproxNT.WordDerivL1 (fun x : EuclideanSpace ℝ ι => (g lam)⁻¹ • C (ofLp x) lam)
          (fun k => ((4*k).factorial:ℝ)) := by
  have hbound := derivativeCoefficientEnvelope_mass_le hC hN hmain
  have hR := (summable_gevrey_ratio A hA).tsum_ofReal_lt_top
  have hfin : (∫⁻ lam, wL θ lam*derivativeCoefficientEnvelope C lam) < ⊤ :=
    hbound.trans_lt (ENNReal.mul_lt_top ENNReal.ofReal_lt_top hR)
  obtain ⟨g,hgm,hgi,hgp,hfg,hmass,hgood⟩ := derivative_NT_normalizer_of_envelope_mass hC hθ0 hθ1 hfin
  refine ⟨g,hgm,hgi,hgp,hfg,?_,hgood⟩
  rw [hmass]
  exact add_le_add hbound le_rfl

end WaveTurbulence.RegAsymp
