/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Spine.RA1LW.SourceDensityIdentities
public import WaveTurbulence.Foundations.RegularAsymptotics.RegAsympDraft.PhysicalLeadingFactor
public import WaveTurbulence.Foundations.Spine.RA1LW.LeadingSpatialProfile

/-! # Joint integrability of the original normalized leading source density -/

public section
noncomputable section
namespace WaveTurbulence.RA1Leafwise
open WaveTurbulence.RegAsymp
open MeasureTheory Links Incoh ClassJR ApproxNT WaveTurbulence.Fourier

/-- The actual leading source density is jointly integrable from the
original coefficient mass and leaf norm, before any order cutoff. -/
theorem source_leading_joint_integrable {d : ℕ} (hd : 3 ≤ d)
    {G : Garden 2} {Q : RegCpl} (hQ : Q.Decodes G) (hG : IsCouple G)
    (hn : 0 < Q.links.length) {L δ γ : ℝ} (hL : 0 < L) (hδ : δ ≠ 0)
    (J : Finset (Fin Q.links.length))
    (C : ({j : Fin Q.links.length // j ∉ J} → ℝ) → ℝ × ℝ → ℂ)
    {θ a b A N : ℝ} (hθ : 0 ≤ θ) (hS : SRep θ a b A N C)
    {K M : ℕ} (hK : d+2 ≤ K) (hM : 2*d ≤ M)
    {Binput Ccover : ℝ} (hBi : 0 ≤ Binput) {F : Fin (2*Q.links.length+1) → Mom d → ℂ}
    (hF : (∀ a, spatialNorm K M (F a) ≤ ENNReal.ofReal Binput))
    (S : (Fin (2*Q.links.length+1) → Fin d → ℤ) →
      Finset ((Fin Q.links.length × Fin 2) → Fin d → ℤ))
    (hcard : ∀ c, ((S c).card:ℝ) ≤ Ccover^Q.links.length) (k : Mom d) :
    Integrable (fun q => maskedLeafScalarDensity hQ hG
      (fun lam β γ' z => (((δ/(2*L^((d:ℝ)-γ)))^(2*Q.links.length):ℝ):ℂ)*
        approxApp L (2*δ) γ J (fun Ω => C (WithLp.ofLp Ω) lam)
          (halfCellAmplitude z β γ')) F S q k)
      (volume.prod (leafSpatialMeasure d Q.links.length (2*Q.links.length+1))) := by
  have hm : (∫⁻ β, ∫⁻ lam, wL θ lam*‖C β lam‖ₑ) ≤ ENNReal.ofReal N := by
    simpa only [dnorm_zero,gev,Nat.mul_zero,Nat.factorial_zero,pow_zero,Nat.cast_one,mul_one]
      using hS.norm 0
  have hiC := integrable_symbol_of_weighted_mass hS.reg hθ hm
  obtain ⟨Mc,hMc,hsp⟩ := leafLeadingSpatialProfile_integrable_spatialNorm hd
  have hiS := (hsp G Q hQ hG hn J 0 0 K M (by omega) (by omega)
    Binput Ccover hBi F hF S hcard).1 k
  have hi := (hiC.integral_prod_right.const_mul (((δ/8)^Q.links.length:ℝ):ℂ)).mul_prod hiS
  apply hi.congr
  apply ae_of_all
  intro q
  dsimp only [Function.uncurry]
  rw [maskedLeafScalarDensity_eq_if,maskedLeafScalarDensity_eq_if]
  split_ifs
  · rw [physical_approxApp_frequency_eq hL hδ]
    ring
  · simp only [mul_zero]

end WaveTurbulence.RA1Leafwise
