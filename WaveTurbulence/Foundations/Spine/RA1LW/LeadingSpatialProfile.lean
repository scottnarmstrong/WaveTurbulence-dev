/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Spine.RA1LW.LeafScalarSpatialNorm
public import WaveTurbulence.Foundations.RegularAsymptotics.RegAsympDraft.HalfCellSingularRepresentation

/-! # Full spatial norm of the actual source singular Fourier mixture -/

@[expose] public section
noncomputable section
namespace WaveTurbulence.RA1Leafwise
open WaveTurbulence.RegAsymp
open MeasureTheory Incoh Links ApproxNT

/-- The literal leading spatial mixture with all source masks, leaf
Fourier coefficients and actual half-cell singular integrals. -/
def leafLeadingSpatialProfile {G : Garden 2} {Q : RegCpl}
    (hQ : Q.Decodes G) (hG : IsCouple G) {d : ℕ} (J : Finset (Fin Q.links.length))
    (F : Fin (2*Q.links.length+1) → Mom d → ℂ)
    (S : (Fin (2*Q.links.length+1) → Fin d → ℤ) →
      Finset ((Fin Q.links.length × Fin 2) → Fin d → ℤ)) (k : Mom d) : ℂ :=
  ∫ p, maskedLeafScalarDensity hQ hG
    (fun _ β γ z => singInt J (halfCellAmplitude z β γ)) F S ((0,0),p) k
      ∂leafSpatialMeasure d Q.links.length (2*Q.links.length+1)

/-- A source-leading spatial bound independent of every logarithmic
order exponent. Only one extra leaf-frequency moment is required. -/
theorem leafLeadingSpatialProfile_integrable_spatialNorm {d : ℕ} (hd : 3 ≤ d) :
    ∃ Mcell : ℝ, 1 ≤ Mcell ∧
      ∀ (G : Garden 2) (Q : RegCpl) (hQ : Q.Decodes G) (hG : IsCouple G),
      0 < Q.links.length → ∀ (J : Finset (Fin Q.links.length)),
      ∀ N W K M : ℕ, d+2+N ≤ K → W+2*d ≤ M → ∀ Binput Ccover : ℝ, 0 ≤ Binput →
      ∀ F : Fin (2*Q.links.length+1) → Mom d → ℂ, (∀ a, Fourier.spatialNorm K M (F a) ≤ ENNReal.ofReal Binput) →
      ∀ S : (Fin (2*Q.links.length+1) → Fin d → ℤ) →
        Finset ((Fin Q.links.length × Fin 2) → Fin d → ℤ),
      (∀ c, ((S c).card:ℝ) ≤ Ccover^Q.links.length) →
      (∀ k : Mom d, Integrable (fun p => maskedLeafScalarDensity hQ hG
        (fun _ β γ z => singInt J (halfCellAmplitude z β γ)) F S ((0,0),p) k)
          (leafSpatialMeasure d Q.links.length (2*Q.links.length+1))) ∧
      Fourier.spatialNorm N W (leafLeadingSpatialProfile hQ hG J F S) ≤
        ENNReal.ofReal (maskedSourceSpatialConstant d (2*Q.links.length+1) N W *
          ((1+2*Real.pi)*
            ((((2*max 1 (Real.sqrt d)+5)^(2*d))^Q.links.length*Mcell^Q.links.length*
              halfLinkFirstMomentConstant d^(2*Q.links.length))*spectralFrequencyLoss Q))) *
          (ENNReal.ofReal (Ccover^Q.links.length)*
            ENNReal.ofReal (leafWeightedMomentLocalizationConstant d (N+1) M W*Binput)^(2*Q.links.length+1)) := by
  obtain ⟨Mcell,hMcell,hcell⟩ := exists_cellOp_bound hd
  refine ⟨Mcell,hMcell,?_⟩
  intro G Q hQ hG hn J N W K M hK hM Binput Ccover hBi F hF S hS
  let r := ((2*max 1 (Real.sqrt d)+5)^(2*d))^Q.links.length*Mcell^Q.links.length*
    halfLinkFirstMomentConstant d^(2*Q.links.length)
  have hr : 0 ≤ r := by
    have hD := (halfLinkFirstMomentConstant_pos d).le
    have hMc := zero_le_one.trans hMcell
    dsimp only [r]
    positivity
  have hb (z : (Fin Q.links.length × Fin 2) → Fin d → ℤ) (β γ : Fin Q.links.length → Mom d) :
      ‖singInt J (halfCellAmplitude z β γ)‖ ≤
      (1+2*Real.pi)*(1+((∑ j, ‖β j‖)+(∑ j, ‖γ j‖)))*r := by
    apply (norm_singInt_halfCellAmplitude_le hd hn (zero_le_one.trans hMcell) hcell J z β γ).trans_eq
    dsimp only [r]
    ring
  have hh := leafScalar_spatialNorm_and_integrable_of_envelope hQ hG
    (fun β γ z => singInt J (halfCellAmplitude z β γ))
    (fun z => stronglyMeasurable_singInt_halfCellAmplitude hd hn J z)
    hK hM hBi hF S hS hr hb
  refine ⟨hh.1,?_⟩
  change Fourier.spatialNorm N W (fun k => ∫ p, maskedLeafScalarDensity hQ hG
    (fun _ β γ z => singInt J (halfCellAmplitude z β γ)) F S ((0,0),p) k
      ∂leafSpatialMeasure d Q.links.length (2*Q.links.length+1)) ≤ _
  simpa only [r,mul_assoc] using hh.2

end WaveTurbulence.RA1Leafwise
