/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.RegAsymp.SurvivingEnergyCoordinates
public import WaveTurbulence.Foundations.RegAsymp.DerivativeCoefficientNormalizer

/-! # Quantitative source envelopes in the surviving NT enumeration -/

public section
noncomputable section
namespace WaveTurbulence.RegAsymp
open MeasureTheory ClassJR WithLp
open scoped ENNReal ContDiff

/-- Relabelling active variables preserves the literal derivative envelope
pointwise in source frequency. -/
theorem derivativeCoefficientEnvelope_reindex {ι κ : Type} [Fintype ι] [Fintype κ]
    (e : ι ≃ κ) (C : (ι → ℝ) → ℝ × ℝ → ℂ) (lam : ℝ × ℝ) :
    derivativeCoefficientEnvelope (fun β lam => C (fun i => β (e i)) lam) lam =
      derivativeCoefficientEnvelope C lam := by
  unfold derivativeCoefficientEnvelope
  apply tsum_congr
  intro k
  congr 1
  simp_rw [dnorm_reindex]
  exact lintegral_reindex e (F := fun α => dnorm k C α lam)

/-- The actual finite NT relabelling has exactly the simultaneous trace
cost, with no cost depending on the number of surviving variables. -/
theorem survivingTraceCoefficient_mass_le {n : ℕ} (T J : Finset (Fin n))
    (h : Disjoint T J) (hT : T.Nonempty)
    {C : ({j : Fin n // j ∉ J} → ℝ) → ℝ × ℝ → ℂ} (hC : SymReg C)
    {θ N A : ℝ} (hN : 0 ≤ N) (hA : 0 ≤ A)
    (hmain : ∀ k, ∫⁻ α, ∫⁻ lam, wL θ lam*dnorm k C α lam ≤ gev N A k) :
    (∫⁻ lam, wL θ lam*derivativeCoefficientEnvelope (survivingTraceCoefficient T J h C) lam) ≤
      ENNReal.ofReal ((4*max 1 (4*A))^T.card*(T.card:ℝ)^T.card*((2*T.card).factorial:ℝ))*
        (ENNReal.ofReal N * ∑' k : ℕ,
          ENNReal.ofReal ((4*A)^k*((2*k).factorial:ℝ)/(4*k).factorial)) := by
  unfold survivingTraceCoefficient
  simp_rw [derivativeCoefficientEnvelope_reindex]
  exact energyTraceCoefficient_mass_le T J h hT hC hN hA hmain

/-- The actual lower-dimensional coefficient has a positive NT normalizer,
with the precise simultaneous-trace factorial cost retained once. -/
theorem surviving_trace_NT_normalizer {n : ℕ} (T J : Finset (Fin n))
    (h : Disjoint T J) (hT : T.Nonempty)
    {C : ({j : Fin n // j ∉ J} → ℝ) → ℝ × ℝ → ℂ} (hC : SymReg C)
    {θ N A : ℝ} (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1) (hN : 0 ≤ N) (hA : 0 ≤ A)
    (hmain : ∀ k, ∫⁻ α, ∫⁻ lam, wL θ lam*dnorm k C α lam ≤ gev N A k) :
    ∃ g : (ℝ × ℝ) → ℝ, Measurable g ∧ Integrable g ∧ (∀ lam, 0 < g lam) ∧
      (∫⁻ lam, wL θ lam*ENNReal.ofReal (g lam)) < ⊤ ∧
      (∫⁻ lam, wL θ lam*ENNReal.ofReal (g lam)) ≤
        ENNReal.ofReal ((4*max 1 (4*A))^T.card*(T.card:ℝ)^T.card*((2*T.card).factorial:ℝ))*
          (ENNReal.ofReal N * ∑' k : ℕ,
            ENNReal.ofReal ((4*A)^k*((2*k).factorial:ℝ)/(4*k).factorial)) +
          (∫⁻ lam, wL θ lam*ENNReal.ofReal (frequencyGaussian lam)) ∧
      ∀ᵐ lam : ℝ × ℝ,
        ContDiff ℝ ∞ (fun x : EuclideanSpace ℝ
          {i : Fin (Fintype.card {j : Fin n // j ∉ T}) // i ∉ survivingSpecial T J} =>
          (g lam)⁻¹ • survivingTraceCoefficient T J h C (ofLp x) lam) ∧
        ApproxNT.WordDerivL1 (fun x : EuclideanSpace ℝ
          {i : Fin (Fintype.card {j : Fin n // j ∉ T}) // i ∉ survivingSpecial T J} =>
          (g lam)⁻¹ • survivingTraceCoefficient T J h C (ofLp x) lam)
          (fun k => ((4*k).factorial:ℝ)) := by
  have hb := survivingTraceCoefficient_mass_le T J h hT hC hN hA hmain
  have hratio := (summable_gevrey_ratio (4*A) (by positivity)).tsum_ofReal_lt_top
  have hf : (∫⁻ lam, wL θ lam*derivativeCoefficientEnvelope (survivingTraceCoefficient T J h C) lam) < ⊤ :=
    hb.trans_lt (ENNReal.mul_lt_top ENNReal.ofReal_lt_top
      (ENNReal.mul_lt_top ENNReal.ofReal_lt_top hratio))
  obtain ⟨g,hgm,hgi,hgp,hgf,hmass,hgood⟩ := derivative_NT_normalizer_of_envelope_mass
    (symReg_survivingTraceCoefficient T J h hC) hθ0 hθ1 hf
  refine ⟨g,hgm,hgi,hgp,hgf,?_,hgood⟩
  rw [hmass]
  exact add_le_add hb le_rfl

end WaveTurbulence.RegAsymp
