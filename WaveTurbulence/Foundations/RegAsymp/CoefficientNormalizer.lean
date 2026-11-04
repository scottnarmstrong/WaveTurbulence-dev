/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.RegAsymp.CoefficientEnvelopeMass
public import WaveTurbulence.Foundations.RegAsymp.WeightedPositiveEnvelope
public import WaveTurbulence.Foundations.RegAsymp.FrequencyGaussian
public import WaveTurbulence.Foundations.RegAsymp.NormalizeSymbol

/-! # The actual J3 symbol supplies normalized NT temporal profiles

A single positive frequency normalizer pays every derivative order and
the NT maximum moment, with explicit weighted mass and no dimensional
loss in the derivative order. All inputs are literal MCRep fields.
-/

public section
noncomputable section
namespace WaveTurbulence.RegAsymp
open MeasureTheory ClassJR WithLp
open scoped ENNReal ContDiff

/-- From the exact J3 fields, construct profiles satisfying every NT
symbol premise almost everywhere, and retain the scalar outside NT. -/
theorem coefficient_NT_normalizer {ι : Type} [Fintype ι] [DecidableEq ι]
    {C : (ι → ℝ) → ℝ × ℝ → ℂ} (hC : SymReg C)
    {a θ b N A : ℝ} (ha0 : 0 ≤ a) (ha1 : a ≤ 1) (haθ : a ≤ θ) (hb : 0 ≤ b)
    (hN : 0 ≤ N) (hA : 0 ≤ A)
    (hmain : ∀ k, ∫⁻ α, ∫⁻ lam, wL θ lam*dnorm k C α lam ≤ gev N A k)
    (hper : ∀ i : ι, ∫⁻ α, ∫⁻ lam, wL a lam*(1+‖α i‖ₑ)^b*‖C α lam‖ₑ ≤ ENNReal.ofReal N) :
    ∃ g : (ℝ × ℝ) → ℝ, Measurable g ∧ Integrable g ∧ (∀ lam, 0 < g lam) ∧
      (∫⁻ lam, wL a lam*ENNReal.ofReal (g lam)) < ⊤ ∧
      (∫⁻ lam, wL a lam*ENNReal.ofReal (g lam)) ≤
        (ENNReal.ofReal N*(∑' k : ℕ, ENNReal.ofReal (A^k*((2*k).factorial:ℝ)/(4*k).factorial)) +
          Fintype.card ι*ENNReal.ofReal N) +
            ∫⁻ lam, wL a lam*ENNReal.ofReal (frequencyGaussian lam) ∧
      ∀ᵐ lam : ℝ × ℝ,
        ContDiff ℝ ∞ (fun x : EuclideanSpace ℝ ι => (g lam)⁻¹ • C (ofLp x) lam) ∧
        ApproxNT.WordDerivL1 (fun x : EuclideanSpace ℝ ι => (g lam)⁻¹ • C (ofLp x) lam)
          (fun k => ((4*k).factorial:ℝ)) ∧
        (∫⁻ x : EuclideanSpace ℝ ι, ENNReal.ofReal (ApproxNT.wmax b (ofLp x)) *
          ‖(g lam)⁻¹ • C (ofLp x) lam‖ₑ) ≤ 1 := by
  let E := fun lam => derivativeCoefficientEnvelope C lam+momentCoefficientEnvelope b C lam
  have hmE : Measurable E := (measurable_derivativeCoefficientEnvelope hC).add
    (measurable_momentCoefficientEnvelope b hC)
  have hbound := combinedCoefficientEnvelope_mass_le hC haθ hN hmain hper
  have hR := (summable_gevrey_ratio A hA).tsum_ofReal_lt_top
  have hefin : (∫⁻ lam, wL a lam*E lam) < ⊤ := hbound.trans_lt (by
    apply ENNReal.add_lt_top.mpr
    constructor
    · exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top hR
    · exact ENNReal.mul_lt_top (by finiteness) ENNReal.ofReal_lt_top)
  obtain ⟨g,hgm,hgi,hgp,hdom,hmass⟩ := exists_positive_weighted_envelope hmE (measurable_wL a)
    (one_le_wL ha0) hefin measurable_frequencyGaussian integrable_frequencyGaussian frequencyGaussian_pos
  refine ⟨g,hgm,hgi,hgp,?_,?_,?_⟩
  · rw [hmass]
    exact ENNReal.add_lt_top.mpr ⟨hefin,lintegral_wL_frequencyGaussian_lt_top ha1⟩
  · rw [hmass]
    exact add_le_add hbound le_rfl
  · filter_upwards [hdom] with lam hdom
    have hd : derivativeCoefficientEnvelope C lam ≤ ENNReal.ofReal (g lam) := le_self_add.trans hdom
    have hm : momentCoefficientEnvelope b C lam ≤ ENNReal.ofReal (g lam) := le_add_self.trans hdom
    have hder (k : ℕ) : (∫⁻ α, dnorm k C α lam) ≤ ENNReal.ofReal (g lam*(4*k).factorial) := by
      calc
        _ ≤ ENNReal.ofReal ((4*k).factorial:ℝ)*derivativeCoefficientEnvelope C lam :=
          derivativeCoefficientEnvelope_dominates C k lam
        _ ≤ ENNReal.ofReal ((4*k).factorial:ℝ)*ENNReal.ofReal (g lam) := mul_le_mul' le_rfl hd
        _ = _ := by rw [← ENNReal.ofReal_mul (by positivity)]; congr 1; ring
    have hmom := (momentCoefficientEnvelope_dominates hb hC lam).trans hm
    refine ⟨normalized_symbol_contDiff (hC.smooth lam) (g lam),?_,
      normalized_symbol_moment (hgp lam) hmom⟩
    exact normalized_symbol_wordDeriv (hC.smooth lam) (hgp lam) hder

end WaveTurbulence.RegAsymp
