/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.RegularAsymptotics.RegAsympDraft.LeadingSpatialProfile
public import WaveTurbulence.Foundations.RegularAsymptotics.RegAsympDraft.LeafSingularOutput

/-! # Exact counting-measure expansion of the actual leading spatial mixture -/

public section
noncomputable section
namespace WaveTurbulence.RegAsymp
open MeasureTheory Incoh Links ApproxNT WithLp Finset

/-- Counting measure retains precisely the original finite link cover in
the leading mixture. Integrability is supplied by the spatial estimate. -/
theorem leafLeadingSpatialProfile_eq_tsum {G : Garden 2} {Q : RegCpl}
    (hQ : Q.Decodes G) (hG : IsCouple G) {d : ℕ}
    (J : Finset (Fin Q.links.length)) (F : Mom d → ℂ)
    (S : (Fin (2*Q.links.length+1) → Fin d → ℤ) →
      Finset ((Fin Q.links.length × Fin 2) → Fin d → ℤ)) (k : Mom d)
    (hi : Integrable (fun p => maskedLeafScalarDensity hQ hG
      (fun _ β γ z => singInt J (halfCellAmplitude z β γ)) F S ((0,0),p) k)
        (leafSpatialMeasure d Q.links.length (2*Q.links.length+1))) :
    leafLeadingSpatialProfile hQ hG J F S k =
      ∑' c : Fin (2*Q.links.length+1) → Fin d → ℤ,
        ∑ z ∈ S c, ∫ α : Fin (2*Q.links.length+1) → Fin d → ℝ,
          sourceRootMask c k *
            ((Real.fourierChar (inner ℝ (∑ a, toLp 2 (α a)) k):ℂ)*leafSpectrumCoefficient F c α *
              singInt J (halfCellAmplitude z (leafModulations hQ hG α).1 (leafModulations hQ hG α).2)) := by
  classical
  unfold leafLeadingSpatialProfile
  unfold leafSpatialMeasure at hi ⊢
  rw [integral_prod _ hi]
  have hcount := integral_countable hi.integral_prod_left
  simp only [Measure.real,Measure.count_singleton,ENNReal.toReal_one,one_smul] at hcount
  have hs := (integrable_count_iff.mp hi.integral_prod_left).of_norm
  rw [hcount,hs.tsum_prod]
  apply tsum_congr
  intro c
  have hz (z : (Fin Q.links.length × Fin 2) → Fin d → ℤ) (hz : z ∉ S c) :
      (∫ α : Fin (2*Q.links.length+1) → Fin d → ℝ,
        maskedLeafScalarDensity hQ hG (fun _ β γ z => singInt J (halfCellAmplitude z β γ)) F S
          ((0,0),((c,z),α)) k) = 0 := by
    simp only [maskedLeafScalarDensity,leafScalarAmplitude,hz,ite_false,maskedModulation,
      zero_mul,mul_zero,integral_zero]
  rw [tsum_eq_sum hz]
  apply sum_congr rfl
  intro z hz'
  apply integral_congr_ae
  apply ae_of_all
  intro α
  dsimp only [maskedLeafScalarDensity,leafScalarAmplitude]
  rw [if_pos hz']
  dsimp only [maskedModulation]
  ring

end WaveTurbulence.RegAsymp
