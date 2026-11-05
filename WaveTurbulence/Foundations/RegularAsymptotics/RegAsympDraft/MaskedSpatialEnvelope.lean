/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.RegularAsymptotics.RegAsympDraft.MaskedLeafSpatialRemainder

/-! # An actual integrable-parameter candidate for the full spatial NT remainder -/

@[expose] public section
noncomputable section
namespace WaveTurbulence.RegAsymp
open MeasureTheory Incoh Links WithLp
open scoped ContDiff ENNReal

/-- The actual scalar remainder norm is included in the derivative envelope.
Thus the bound is pointwise even at exceptional time frequencies. -/
def maskedSpatialDerivativeEnvelope {G : Garden 2} {Q : RegCpl}
    (hQ : Q.Decodes G) (hG : IsCouple G) {d : ℕ} (N W : ℕ)
    (L δ γ : ℝ) (J : Finset (Fin Q.links.length))
    (C : ({j : Fin Q.links.length // j ∉ J} → ℝ) → ℝ × ℝ → ℂ) (F : Mom d → ℂ)
    (S : (Fin (2*Q.links.length+1) → Fin d → ℤ) → Finset ((Fin Q.links.length × Fin 2) → Fin d → ℤ))
    (q : (ℝ × ℝ) × LeafSpatialSample d Q.links.length (2*Q.links.length+1)) : ℝ :=
  maskedSourceSpatialConstant d (2*Q.links.length+1) N W *
    (∏ a, Fourier.momentumBracket (NTSP.intVec (q.2.1.1 a))^W) *
    (1+‖∑ a, toLp 2 (q.2.2 a)‖)^N *
    ‖leafSpatialRemainderDensity hQ hG L δ γ J C F S q.1 q.2 (0:Mom d)‖

/-- The actual real envelope is nonnegative at every sample. -/
theorem maskedSpatialDerivativeEnvelope_nonneg {G : Garden 2} {Q : RegCpl}
    (hQ : Q.Decodes G) (hG : IsCouple G) {d : ℕ} (N W : ℕ)
    (L δ γ : ℝ) (J : Finset (Fin Q.links.length))
    (C : ({j : Fin Q.links.length // j ∉ J} → ℝ) → ℝ × ℝ → ℂ) (F : Mom d → ℂ)
    (S : (Fin (2*Q.links.length+1) → Fin d → ℤ) → Finset ((Fin Q.links.length × Fin 2) → Fin d → ℤ))
    (q : (ℝ × ℝ) × LeafSpatialSample d Q.links.length (2*Q.links.length+1)) :
    0 ≤ maskedSpatialDerivativeEnvelope hQ hG N W L δ γ J C F S q := by
  have hcenter : 0 ≤ ∏ a, Fourier.momentumBracket (NTSP.intVec (q.2.1.1 a))^W :=
    Finset.prod_nonneg (fun _ _ => pow_nonneg (zero_le_one.trans (one_le_momentumBracket _)) W)
  have hmask := zero_le_one.trans (one_le_rootMaskDerivativeConstant d N)
  unfold maskedSpatialDerivativeEnvelope maskedSourceSpatialConstant
  positivity

/-- The actual weighted tensor derivative is dominated by this real envelope. -/
theorem weighted_derivative_maskedLeafSpatialRemainderDensity_le {G : Garden 2} {Q : RegCpl}
    (hQ : Q.Decodes G) (hG : IsCouple G) {d N j W : ℕ} (hj : j ≤ N)
    (L δ γ : ℝ) (J : Finset (Fin Q.links.length))
    (C : ({j : Fin Q.links.length // j ∉ J} → ℝ) → ℝ × ℝ → ℂ) (F : Mom d → ℂ)
    (S : (Fin (2*Q.links.length+1) → Fin d → ℤ) → Finset ((Fin Q.links.length × Fin 2) → Fin d → ℤ))
    (q : (ℝ × ℝ) × LeafSpatialSample d Q.links.length (2*Q.links.length+1)) (k : Mom d) :
    Fourier.momentumBracket k^W *
      ‖iteratedFDeriv ℝ j (maskedLeafSpatialRemainderDensity hQ hG L δ γ J C F S q.1 q.2) k‖ ≤
      maskedSpatialDerivativeEnvelope hQ hG N W L δ γ J C F S q := by
  classical
  rw [derivative_maskedLeafSpatialRemainderDensity]
  by_cases h : q.2.1.2 ∈ S q.2.1.1
  · rw [ite_eq_left h,maskedLeafLocalDensity_eq_maskedModulation]
    have hh := weighted_norm_iteratedFDeriv_maskedModulation_le (W := W) q.2.1.1
      (leafSpectrumCoefficient F q.2.1.1 q.2.2 *
        localRemainder L δ γ J C (leafModulations hQ hG q.2.2).1
          (leafModulations hQ hG q.2.2).2 q.1 q.2.1.2)
      (∑ a, toLp 2 (q.2.2 a)) k hj
    simpa only [maskedSpatialDerivativeEnvelope,leafSpatialRemainderDensity,h,ite_true,
      leafLocalDensity,inner_zero_right,AddChar.map_zero_eq_one,Circle.coe_one,one_mul] using hh
  · rw [ite_eq_right h,norm_zero,mul_zero]
    exact maskedSpatialDerivativeEnvelope_nonneg hQ hG N W L δ γ J C F S q

/-- The literal envelope pays the root frequency with one extra moment
per leaf; the scalar bound is the local NT estimate, before integration. -/
theorem maskedSpatialDerivativeEnvelope_le {G : Garden 2} {Q : RegCpl}
    (hQ : Q.Decodes G) (hG : IsCouple G) {d : ℕ} (N W : ℕ)
    (L δ γ : ℝ) (J : Finset (Fin Q.links.length))
    (C : ({j : Fin Q.links.length // j ∉ J} → ℝ) → ℝ × ℝ → ℂ) (F : Mom d → ℂ)
    (S : (Fin (2*Q.links.length+1) → Fin d → ℤ) → Finset ((Fin Q.links.length × Fin 2) → Fin d → ℤ))
    (q : (ℝ × ℝ) × LeafSpatialSample d Q.links.length (2*Q.links.length+1))
    {R B : ℝ} (hR : 0 ≤ R) (hB : 0 ≤ B)
    (hb : ∀ z β γ', ‖localRemainder (d := d) L δ γ J C β γ' q.1 z‖ ≤
      ((1+2*Real.pi)*(1+((∑ i, ‖β i‖)+(∑ i, ‖γ' i‖)))*R)*B) :
    maskedSpatialDerivativeEnvelope hQ hG N W L δ γ J C F S q ≤
      maskedSourceSpatialConstant d (2*Q.links.length+1) N W *
        ((1+2*Real.pi)*R*spectralFrequencyLoss Q) *
        (∏ a, Fourier.momentumBracket (NTSP.intVec (q.2.1.1 a))^W) *
        (∏ a, (1+‖toLp 2 (q.2.2 a)‖)^(N+1))*‖leafSpectrumCoefficient F q.2.1.1 q.2.2‖*B := by
  classical
  let D := maskedSourceSpatialConstant d (2*Q.links.length+1) N W
  let P := ∏ a, Fourier.momentumBracket (NTSP.intVec (q.2.1.1 a))^W
  let K := (1+2*Real.pi)*R*spectralFrequencyLoss Q
  have hD : 0 ≤ D := by
    dsimp only [D,maskedSourceSpatialConstant]
    have hmask := zero_le_one.trans (one_le_rootMaskDerivativeConstant d N)
    positivity
  have hP : 0 ≤ P := Finset.prod_nonneg (fun _ _ =>
    pow_nonneg (zero_le_one.trans (one_le_momentumBracket _)) W)
  have hK : 0 ≤ K := by dsimp only [K,spectralFrequencyLoss]; positivity
  have hh := norm_leafLocalDensity_le hQ hG L δ γ J C F q.2.1.1 q.2.1.2
    (0:Mom d) q.1 q.2.2 hR hB (hb q.2.1.2)
  have hn : ‖leafSpatialRemainderDensity hQ hG L δ γ J C F S q.1 q.2 (0:Mom d)‖ ≤
      K*((1+∑ a, ‖toLp 2 (q.2.2 a)‖)*‖leafSpectrumCoefficient F q.2.1.1 q.2.2‖)*B := by
    by_cases hm : q.2.1.2 ∈ S q.2.1.1
    · simpa only [leafSpatialRemainderDensity,hm,ite_true] using hh
    · simp only [leafSpatialRemainderDensity,hm,ite_false,norm_zero]
      positivity
  unfold maskedSpatialDerivativeEnvelope
  calc
    _ ≤ D*P*(1+‖∑ a, toLp 2 (q.2.2 a)‖)^N *
        (K*((1+∑ a, ‖toLp 2 (q.2.2 a)‖)*‖leafSpectrumCoefficient F q.2.1.1 q.2.2‖)*B) :=
      mul_le_mul_of_nonneg_left hn (by positivity)
    _ = (D*K*P*‖leafSpectrumCoefficient F q.2.1.1 q.2.2‖*B)*
        ((1+‖∑ a, toLp 2 (q.2.2 a)‖)^N*(1+∑ a, ‖toLp 2 (q.2.2 a)‖)) := by ring
    _ ≤ (D*K*P*‖leafSpectrumCoefficient F q.2.1.1 q.2.2‖*B)*
        (∏ a, (1+‖toLp 2 (q.2.2 a)‖)^(N+1)) :=
      mul_le_mul_of_nonneg_left (root_frequency_moment_mul_le_product (fun a => toLp 2 (q.2.2 a)) N)
        (by positivity)
    _ = _ := by ring

/-- Measurability of the actual real envelope is derived from the source
remainder and input profiles, rather than supplied as an analytic premise. -/
theorem measurable_maskedSpatialDerivativeEnvelope {G : Garden 2} {Q : RegCpl}
    (hQ : Q.Decodes G) (hG : IsCouple G) {d K M : ℕ} (hd : 3 ≤ d) (hn : 0 < Q.links.length)
    (N W : ℕ) (L δ γ : ℝ) (J : Finset (Fin Q.links.length))
    {C : ({j : Fin Q.links.length // j ∉ J} → ℝ) → ℝ × ℝ → ℂ} (hC : ClassJR.SymReg C)
    {F : Mom d → ℂ} {B : ℝ} (hK : d+1 ≤ K) (hB : 0 ≤ B)
    (hF : Fourier.spatialNorm K M F ≤ ENNReal.ofReal B)
    (S : (Fin (2*Q.links.length+1) → Fin d → ℤ) → Finset ((Fin Q.links.length × Fin 2) → Fin d → ℤ)) :
    Measurable (maskedSpatialDerivativeEnvelope hQ hG N W L δ γ J C F S) := by
  have hnorm := (stronglyMeasurable_leafSpatialRemainderDensity hQ hG hd hn L δ γ J hC hK hB hF S (0:Mom d)).norm.measurable
  have hcenter : Measurable (fun c : Fin (2*Q.links.length+1) → Fin d → ℤ =>
      ∏ a, Fourier.momentumBracket (NTSP.intVec (c a))^W) := measurable_of_countable _
  have hfreq : Continuous (fun α : Fin (2*Q.links.length+1) → Fin d → ℝ =>
      (1+‖∑ a, toLp 2 (α a)‖)^N) := by fun_prop
  exact (((measurable_const.mul (hcenter.comp measurable_snd.fst.fst)).mul
    (hfreq.measurable.comp measurable_snd.snd)).mul hnorm)

/-- The actual masked amplitude itself is strongly measurable in the full sample. -/
theorem stronglyMeasurable_maskedLeafSpatialRemainderDensity {G : Garden 2} {Q : RegCpl}
    (hQ : Q.Decodes G) (hG : IsCouple G) {d K M : ℕ} (hd : 3 ≤ d) (hn : 0 < Q.links.length)
    (L δ γ : ℝ) (J : Finset (Fin Q.links.length))
    {C : ({j : Fin Q.links.length // j ∉ J} → ℝ) → ℝ × ℝ → ℂ} (hC : ClassJR.SymReg C)
    {F : Mom d → ℂ} {B : ℝ} (hK : d+1 ≤ K) (hB : 0 ≤ B)
    (hF : Fourier.spatialNorm K M F ≤ ENNReal.ofReal B)
    (S : (Fin (2*Q.links.length+1) → Fin d → ℤ) → Finset ((Fin Q.links.length × Fin 2) → Fin d → ℤ))
    (k : Mom d) :
    StronglyMeasurable (fun q : (ℝ × ℝ) × LeafSpatialSample d Q.links.length (2*Q.links.length+1) =>
      maskedLeafSpatialRemainderDensity hQ hG L δ γ J C F S q.1 q.2 k) := by
  have hm : Measurable (fun c : Fin (2*Q.links.length+1) → Fin d → ℤ => sourceRootMask c k) :=
    measurable_of_countable _
  simp_rw [maskedLeafSpatialRemainderDensity_eq_mask_mul]
  exact (hm.stronglyMeasurable.comp_measurable measurable_snd.fst.fst).mul
    (stronglyMeasurable_leafSpatialRemainderDensity hQ hG hd hn L δ γ J hC hK hB hF S k)

end WaveTurbulence.RegAsymp
