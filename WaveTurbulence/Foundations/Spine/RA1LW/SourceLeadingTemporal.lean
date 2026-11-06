/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Spine.RA1LW.SourceLeadingFubini

/-! # The literal global leading profile separates time and source space -/

public section
noncomputable section
namespace WaveTurbulence.RA1Leafwise
open WaveTurbulence.RegAsymp
open MeasureTheory Links Incoh ClassJR ApproxNT WithLp

/-- Global leading time factorization uses the original SRep joint mass;
the spatial factor is the SAME masked source-cover mixture. -/
theorem masked_leading_profile_eq {G : Garden 2} {Q : RegCpl}
    (hQ : Q.Decodes G) (hG : IsCouple G) {d : ℕ} {L δ γ : ℝ}
    (hL : 0 < L) (hδ : δ ≠ 0) (J : Finset (Fin Q.links.length))
    (C : ({j : Fin Q.links.length // j ∉ J} → ℝ) → ℝ × ℝ → ℂ)
    {θ a b A N : ℝ} (hθ : 0 ≤ θ) (hS : SRep θ a b A N C)
    (F : Fin (2*Q.links.length+1) → Mom d → ℂ)
    (S : (Fin (2*Q.links.length+1) → Fin d → ℤ) →
      Finset ((Fin Q.links.length × Fin 2) → Fin d → ℤ)) (k : Mom d) (t : Fin 2 → ℝ) :
    pairedInverseProfile (fun lam => ∫ p, maskedLeafScalarDensity hQ hG
      (fun lam β γ' z => (((δ/(2*L^((d:ℝ)-γ)))^(2*Q.links.length):ℝ):ℂ)*
        approxApp L (2*δ) γ J (fun Ω => C (ofLp Ω) lam) (halfCellAmplitude z β γ')) F S (lam,p) k
          ∂leafSpatialMeasure d Q.links.length (2*Q.links.length+1)) t =
    (((δ/8)^Q.links.length:ℝ):ℂ)*(∫ β, ∫ lam, C β lam*e2 lam (t 0) (t 1))*
      leafLeadingSpatialProfile hQ hG J F S k := by
  have hm : (∫⁻ β, ∫⁻ lam, wL θ lam*‖C β lam‖ₑ) ≤ ENNReal.ofReal N := by
    simpa only [dnorm_zero,gev,Nat.mul_zero,Nat.factorial_zero,pow_zero,Nat.cast_one,mul_one]
      using hS.norm 0
  have hiC := integrable_symbol_of_weighted_mass hS.reg hθ hm
  have hden (lam : ℝ × ℝ) (p : LeafSpatialSample d Q.links.length (2*Q.links.length+1)) :
      maskedLeafScalarDensity hQ hG
        (fun lam β γ' z => (((δ/(2*L^((d:ℝ)-γ)))^(2*Q.links.length):ℝ):ℂ)*
          approxApp L (2*δ) γ J (fun Ω => C (ofLp Ω) lam) (halfCellAmplitude z β γ')) F S (lam,p) k =
      ((((δ/8)^Q.links.length:ℝ):ℂ)*(∫ β, C β lam))*
        maskedLeafScalarDensity hQ hG (fun _ β γ' z => singInt J (halfCellAmplitude z β γ')) F S ((0,0),p) k := by
    classical
    simp only [maskedLeafScalarDensity_eq_if]
    split_ifs
    · rw [physical_approxApp_frequency_eq hL hδ]
      ring
    · ring
  simp_rw [hden,integral_const_mul]
  change pairedInverseProfile (fun lam =>
    ((((δ/8)^Q.links.length:ℝ):ℂ)*(∫ β, C β lam))*leafLeadingSpatialProfile hQ hG J F S k) t = _
  unfold pairedInverseProfile
  calc
    _ = ∫ lam, (((δ/8)^Q.links.length:ℝ):ℂ)*
        ((∫ β, C β lam)*e2 lam (t 0) (t 1))*leafLeadingSpatialProfile hQ hG J F S k := by
      apply integral_congr_ae
      apply ae_of_all
      intro lam
      ring
    _ = (((δ/8)^Q.links.length:ℝ):ℂ)*
        (∫ lam, (∫ β, C β lam)*e2 lam (t 0) (t 1))*leafLeadingSpatialProfile hQ hG J F S k := by
      rw [integral_mul_const,integral_const_mul]
    _ = _ := by
      have ht := integral_integral_e2_eq_pairedProfile hiC t
      change (∫ β, ∫ lam, C β lam*e2 lam (t 0) (t 1)) =
        (∫ lam, (∫ β, C β lam)*e2 lam (t 0) (t 1)) at ht
      rw [← ht]

end WaveTurbulence.RA1Leafwise
