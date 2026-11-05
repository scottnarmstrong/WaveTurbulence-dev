/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.RegularAsymptotics.RegAsympDraft.MaskedSpatialEnvelope
public import WaveTurbulence.Foundations.RegularAsymptotics.RegAsympDraft.LeafSpatialHigherEnvelope
public import WaveTurbulence.Foundations.RegAsymp.SeparatedEnvelope

/-! # Separated mass of the actual spatial derivative envelope -/

public section
noncomputable section
namespace WaveTurbulence.RegAsymp
open MeasureTheory Incoh Links WithLp ClassJR
open scoped ENNReal

variable {G : Garden 2} {Q : RegCpl} (hQ : Q.Decodes G) (hG : IsCouple G)
  {d : ℕ} (N W : ℕ) (L δ γ : ℝ) (J : Finset (Fin Q.links.length))
  (C : ({j : Fin Q.links.length // j ∉ J} → ℝ) → ℝ × ℝ → ℂ) (F : Mom d → ℂ)
  (S : (Fin (2*Q.links.length+1) → Fin d → ℤ) → Finset ((Fin Q.links.length × Fin 2) → Fin d → ℤ))

/-- The finite link cover and individual higher leaf moments dominate the
literal real derivative envelope, before source-frequency integration. -/
theorem ofReal_maskedSpatialDerivativeEnvelope_le
    (lam : ℝ × ℝ) {R B : ℝ} (hR : 0 ≤ R) (hB : 0 ≤ B)
    (hb : ∀ z β γ', ‖localRemainder (d := d) L δ γ J C β γ' lam z‖ ≤
      ((1+2*Real.pi)*(1+((∑ i, ‖β i‖)+(∑ i, ‖γ' i‖)))*R)*B)
    (p : LeafSpatialSample d Q.links.length (2*Q.links.length+1)) :
    ENNReal.ofReal (maskedSpatialDerivativeEnvelope hQ hG N W L δ γ J C F S (lam,p)) ≤
      ENNReal.ofReal (maskedSourceSpatialConstant d (2*Q.links.length+1) N W *
        ((1+2*Real.pi)*R*spectralFrequencyLoss Q)) * ENNReal.ofReal B *
        leafSpatialHigherEnvelope (N+1) W F S p := by
  classical
  by_cases hm : p.1.2 ∈ S p.1.1
  · have hh := ENNReal.ofReal_le_ofReal
      (maskedSpatialDerivativeEnvelope_le hQ hG N W L δ γ J C F S (lam,p) hR hB hb)
    apply hh.trans_eq
    simp only [leafSpatialHigherEnvelope,hm,ite_true,leafHigherMomentWeight]
    have hcenter : 0 ≤ ∏ a, Fourier.momentumBracket (NTSP.intVec (p.1.1 a))^W :=
      Finset.prod_nonneg (fun _ _ => pow_nonneg (zero_le_one.trans (one_le_momentumBracket _)) W)
    have hD : 0 ≤ maskedSourceSpatialConstant d (2*Q.links.length+1) N W := by
      unfold maskedSourceSpatialConstant
      have hmask := zero_le_one.trans (one_le_rootMaskDerivativeConstant d N)
      positivity
    have hK : 0 ≤ (1+2*Real.pi)*R*spectralFrequencyLoss Q := by
      unfold spectralFrequencyLoss; positivity
    rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_mul (by positivity),
      ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_mul (by positivity),ofReal_norm]
    ac_rfl
  · simp only [maskedSpatialDerivativeEnvelope,leafSpatialRemainderDensity,hm,ite_false,
      norm_zero,mul_zero,ENNReal.ofReal_zero,zero_le]

/-- Conditional transport of the local NT scalar envelope into its actual
full spatial sample mass. The source application constructs B from J3. -/
theorem weighted_mass_maskedSpatialDerivativeEnvelope_le
    {K M : ℕ} (hd : 3 ≤ d) (hn : 0 < Q.links.length)
    (hC : SymReg C) {Binput : ℝ} (hK : d+1 ≤ K) (hBi : 0 ≤ Binput)
    (hF : Fourier.spatialNorm K M F ≤ ENNReal.ofReal Binput)
    (η : ℝ) {R : ℝ} (hR : 0 ≤ R) (B : (ℝ × ℝ) → ℝ)
    (hB : Measurable B) (hBn : ∀ lam, 0 ≤ B lam)
    (hb : ∀ᵐ lam : ℝ × ℝ, ∀ z β γ',
      ‖localRemainder (d := d) L δ γ J C β γ' lam z‖ ≤
        ((1+2*Real.pi)*(1+((∑ i, ‖β i‖)+(∑ i, ‖γ' i‖)))*R)*B lam) :
    (∫⁻ q, wL η q.1 * ENNReal.ofReal
      (maskedSpatialDerivativeEnvelope hQ hG N W L δ γ J C F S q)
      ∂volume.prod (leafSpatialMeasure d Q.links.length (2*Q.links.length+1))) ≤
      ENNReal.ofReal (maskedSourceSpatialConstant d (2*Q.links.length+1) N W *
        ((1+2*Real.pi)*R*spectralFrequencyLoss Q)) *
        (∫⁻ lam, wL η lam * ENNReal.ofReal (B lam)) *
        (∫⁻ p, leafSpatialHigherEnvelope (N+1) W F S p
          ∂leafSpatialMeasure d Q.links.length (2*Q.links.length+1)) := by
  let := sFinite_leafSpatialMeasure d Q.links.length (2*Q.links.length+1)
  apply weighted_lintegral_le_separated _ η _
    (measurable_maskedSpatialDerivativeEnvelope hQ hG hd hn N W L δ γ J hC hK hBi hF S)
    _ (measurable_leafSpatialHigherEnvelope (N+1) W hK hBi hF S) B hB
  filter_upwards [hb] with lam hlam
  intro p
  exact ofReal_maskedSpatialDerivativeEnvelope_le hQ hG N W L δ γ J C F S lam hR (hBn lam) hlam p

end WaveTurbulence.RegAsymp
