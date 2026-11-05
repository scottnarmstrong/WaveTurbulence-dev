/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.RegularAsymptotics.RegAsympDraft.LeafLocalDensity
public import WaveTurbulence.Foundations.RegAsymp.MaskedModulation
public import WaveTurbulence.Foundations.RegAsymp.RootFrequencyMoment

/-! # Actual spatial derivatives of the masked NT spectral remainder -/

@[expose] public section
noncomputable section
namespace WaveTurbulence.RegAsymp
open MeasureTheory Links Incoh WithLp
open scoped ENNReal ContDiff

/-- Insert the source mask before estimating the actual local remainder. -/
def maskedLeafLocalDensity {G : Garden 2} {Q : RegCpl} (hQ : Q.Decodes G) (hG : IsCouple G) {d : ℕ}
    (L δ γ : ℝ) (J : Finset (Fin Q.links.length))
    (C : ({j : Fin Q.links.length // j ∉ J} → ℝ) → ℝ × ℝ → ℂ) (F : Mom d → ℂ)
    (c : Fin (2*Q.links.length+1) → Fin d → ℤ)
    (z : (Fin Q.links.length × Fin 2) → Fin d → ℤ)
    (lam : ℝ × ℝ) (α : Fin (2*Q.links.length+1) → Fin d → ℝ) (k : Mom d) : ℂ :=
  sourceRootMask c k * leafLocalDensity hQ hG L δ γ J C F c z k lam α

/-- All root dependence is the literal masked modulation. -/
theorem maskedLeafLocalDensity_eq_maskedModulation {G : Garden 2} {Q : RegCpl}
    (hQ : Q.Decodes G) (hG : IsCouple G) {d : ℕ}
    (L δ γ : ℝ) (J : Finset (Fin Q.links.length))
    (C : ({j : Fin Q.links.length // j ∉ J} → ℝ) → ℝ × ℝ → ℂ) (F : Mom d → ℂ)
    (c : Fin (2*Q.links.length+1) → Fin d → ℤ)
    (z : (Fin Q.links.length × Fin 2) → Fin d → ℤ)
    (lam : ℝ × ℝ) (α : Fin (2*Q.links.length+1) → Fin d → ℝ) :
    maskedLeafLocalDensity hQ hG L δ γ J C F c z lam α =
      maskedModulation c (leafSpectrumCoefficient F c α *
        localRemainder L δ γ J C (leafModulations hQ hG α).1 (leafModulations hQ hG α).2 lam z)
        (∑ a, toLp 2 (α a)) := by
  funext k
  unfold maskedLeafLocalDensity leafLocalDensity maskedModulation
  ring

/-- Spatial smoothness uses no extra smoothness of the input profile or
of the NT remainder as a function of its time-frequency parameter. -/
theorem contDiff_maskedLeafLocalDensity {G : Garden 2} {Q : RegCpl}
    (hQ : Q.Decodes G) (hG : IsCouple G) {d : ℕ}
    (L δ γ : ℝ) (J : Finset (Fin Q.links.length))
    (C : ({j : Fin Q.links.length // j ∉ J} → ℝ) → ℝ × ℝ → ℂ) (F : Mom d → ℂ)
    (c : Fin (2*Q.links.length+1) → Fin d → ℤ)
    (z : (Fin Q.links.length × Fin 2) → Fin d → ℤ)
    (lam : ℝ × ℝ) (α : Fin (2*Q.links.length+1) → Fin d → ℝ) :
    ContDiff ℝ ∞ (maskedLeafLocalDensity hQ hG L δ γ J C F c z lam α) := by
  rw [maskedLeafLocalDensity_eq_maskedModulation]
  exact contDiff_maskedModulation _ _ _

/-- The actual local scalar estimate pays all root derivatives with one
fixed higher moment at each leaf, leaving the spatial supremum outside. -/
theorem weighted_derivative_maskedLeafLocalDensity_le {G : Garden 2} {Q : RegCpl}
    (hQ : Q.Decodes G) (hG : IsCouple G) {d N j W : ℕ} (hj : j ≤ N)
    (L δ γ : ℝ) (J : Finset (Fin Q.links.length))
    (C : ({j : Fin Q.links.length // j ∉ J} → ℝ) → ℝ × ℝ → ℂ) (F : Mom d → ℂ)
    (c : Fin (2*Q.links.length+1) → Fin d → ℤ)
    (z : (Fin Q.links.length × Fin 2) → Fin d → ℤ)
    (lam : ℝ × ℝ) (α : Fin (2*Q.links.length+1) → Fin d → ℝ) (k : Mom d)
    {R B : ℝ} (hR : 0 ≤ R) (hB : 0 ≤ B)
    (hb : ∀ β γ', ‖localRemainder L δ γ J C β γ' lam z‖ ≤
      ((1+2*Real.pi)*(1+((∑ i, ‖β i‖)+(∑ i, ‖γ' i‖)))*R)*B) :
    Fourier.momentumBracket k^W *
      ‖iteratedFDeriv ℝ j (maskedLeafLocalDensity hQ hG L δ γ J C F c z lam α) k‖ ≤
      maskedSourceSpatialConstant d (2*Q.links.length+1) N W *
        ((1+2*Real.pi)*R*spectralFrequencyLoss Q) *
        (∏ a, Fourier.momentumBracket (NTSP.intVec (c a))^W) *
        (∏ a, (1+‖toLp 2 (α a)‖)^(N+1))*‖leafSpectrumCoefficient F c α‖*B := by
  let a : ℂ := leafSpectrumCoefficient F c α *
    localRemainder L δ γ J C (leafModulations hQ hG α).1 (leafModulations hQ hG α).2 lam z
  let v : Mom d := ∑ i, toLp 2 (α i)
  let D := maskedSourceSpatialConstant d (2*Q.links.length+1) N W
  let K := (1+2*Real.pi)*R*spectralFrequencyLoss Q
  let P := ∏ i, Fourier.momentumBracket (NTSP.intVec (c i))^W
  have hD : 0 ≤ D := by
    dsimp only [D,maskedSourceSpatialConstant]
    have hmask := zero_le_one.trans (one_le_rootMaskDerivativeConstant d N)
    positivity
  have hK : 0 ≤ K := by dsimp only [K,spectralFrequencyLoss]; positivity
  have hP : 0 ≤ P := Finset.prod_nonneg (fun _ _ =>
    pow_nonneg (zero_le_one.trans (one_le_momentumBracket _)) W)
  have ha : ‖a‖ ≤ K*((1+∑ i, ‖toLp 2 (α i)‖)*‖leafSpectrumCoefficient F c α‖)*B := by
    have hh := norm_leafLocalDensity_le hQ hG L δ γ J C F c z (0:Mom d) lam α hR hB hb
    simpa only [leafLocalDensity,inner_zero_right,AddChar.map_zero_eq_one,Circle.coe_one,one_mul] using hh
  rw [maskedLeafLocalDensity_eq_maskedModulation]
  apply (weighted_norm_iteratedFDeriv_maskedModulation_le c a v k hj).trans
  calc
    _ ≤ D*P*(1+‖v‖)^N*(K*((1+∑ i, ‖toLp 2 (α i)‖)*‖leafSpectrumCoefficient F c α‖)*B) :=
      mul_le_mul_of_nonneg_left ha (by positivity)
    _ = (D*K*P*‖leafSpectrumCoefficient F c α‖*B)*
        ((1+‖v‖)^N*(1+∑ i, ‖toLp 2 (α i)‖)) := by ring
    _ ≤ (D*K*P*‖leafSpectrumCoefficient F c α‖*B)*
        (∏ i, (1+‖toLp 2 (α i)‖)^(N+1)) :=
      mul_le_mul_of_nonneg_left (root_frequency_moment_mul_le_product (fun i => toLp 2 (α i)) N) (by positivity)
    _ = _ := by ring

end WaveTurbulence.RegAsymp
