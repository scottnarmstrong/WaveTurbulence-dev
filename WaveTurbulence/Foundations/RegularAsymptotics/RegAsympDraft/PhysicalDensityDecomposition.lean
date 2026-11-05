/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.RegularAsymptotics.RegAsympDraft.SourceLeadingFubini
public import WaveTurbulence.Foundations.RegularAsymptotics.RegAsympDraft.SourceRemainderFubini
public import WaveTurbulence.Foundations.RegularAsymptotics.RegAsympDraft.PhysicalLocalSymbol

/-! # The literal physical density and its integrable three-term decomposition -/

public section
noncomputable section
namespace WaveTurbulence.RegAsymp
open MeasureTheory Links Incoh ApproxNT WithLp ClassJR WaveTurbulence.Fourier

/-- The exact local physical decomposition retains every source mask
and Fourier factor in the global sample density. -/
theorem physical_masked_density_decomposition {G : Garden 2} {Q : RegCpl}
    (hQ : Q.Decodes G) (hG : IsCouple G) {d : ℕ} {L : ℝ} (hL : 0 < L)
    (δ γ : ℝ) (J : Finset (Fin Q.links.length))
    (C : ({j : Fin Q.links.length // j ∉ J} → ℝ) → ℝ × ℝ → ℂ)
    (F : Mom d → ℂ)
    (S : (Fin (2*Q.links.length+1) → Fin d → ℤ) →
      Finset ((Fin Q.links.length × Fin 2) → Fin d → ℤ))
    (q : (ℝ × ℝ) × LeafSpatialSample d Q.links.length (2*Q.links.length+1)) (k : Mom d) :
    maskedLeafScalarDensity hQ hG
      (fun lam β γ' z => physicalWeightedCellSymbol L δ γ z β γ' J C lam) F S q k =
    ((4:ℂ)^Q.links.length)⁻¹*maskedLeafScalarDensity hQ hG
      (fun lam β γ' z => localRemainder L (2*δ) γ J C β γ' lam z) F S q k +
    maskedLeafScalarDensity hQ hG
      (fun lam β γ' z => (((δ/(2*L^((d:ℝ)-γ)))^(2*Q.links.length):ℝ):ℂ)*
        approxApp L (2*δ) γ J (fun Ω => C (ofLp Ω) lam) (halfCellAmplitude z β γ')) F S q k +
    ((4:ℂ)^Q.links.length)⁻¹*maskedLeafScalarDensity hQ hG
      (fun lam β γ' z => normalizedWickCorrection L (2*δ) γ z β γ' J C lam) F S q k := by
  classical
  rcases q with ⟨lam,p⟩
  simp only [maskedLeafScalarDensity_eq_if]
  split_ifs
  · rw [physicalWeightedCellSymbol_decomposition hL]
    ring
  · ring

/-- Original SRep and leaf norms imply actual joint integrability of the
physical weighted symbols, including the exact physical2delta normalization. -/
theorem source_physical_symbol_joint_integrable {d : ℕ} (hd : 3 ≤ d) {γ η : ℝ}
    (hγ : γ ∈ Set.Ioo (0:ℝ) 1) (hη0 : 0 < η) (hη : η ≤ 1/20)
    (hηγ : η ≤ ((d:ℝ)-1)*(1-γ)) (hηγ' : η ≤ γ)
    (Agev : ℝ) (hAgev : 0 ≤ Agev) :
    ∀ Aorder : ℝ, ∃ L₀ : ℝ, ∀ L : ℝ, L₀ ≤ L →
      ∀ δ : ℝ, L^(-(η/2)) ≤ 2*δ → 2*δ ≤ 1 →
      ∀ (G : Garden 2) (Q : RegCpl) (hQ : Q.Decodes G) (hG : IsCouple G),
      0 < Q.links.length → (Q.links.length:ℝ) ≤ Real.log L^Aorder →
      ∀ (J : Finset (Fin Q.links.length))
        (C : ({j : Fin Q.links.length // j ∉ J} → ℝ) → ℝ × ℝ → ℂ),
      ∀ N : ℝ, SRep (1-η/8) (η/4) (1-η/2) Agev N C →
      ∀ K M : ℕ, d+2 ≤ K → 2*d ≤ M → ∀ Binput Ccover : ℝ, 0 ≤ Binput →
      ∀ F : Mom d → ℂ, spatialNorm K M F ≤ ENNReal.ofReal Binput →
      ∀ S : (Fin (2*Q.links.length+1) → Fin d → ℤ) →
        Finset ((Fin Q.links.length × Fin 2) → Fin d → ℤ),
      (∀ c, ((S c).card:ℝ) ≤ Ccover^Q.links.length) → ∀ k : Mom d,
      Integrable (fun q => maskedLeafScalarDensity hQ hG
        (fun lam β γ' z => physicalWeightedCellSymbol L δ γ z β γ' J C lam) F S q k)
        (volume.prod (leafSpatialMeasure d Q.links.length (2*Q.links.length+1))) := by
  intro Aorder
  obtain ⟨L₀,hjoint⟩ := source_remainders_joint_integrable hd hγ hη0 hη hηγ hηγ' Agev hAgev Aorder
  refine ⟨max 2 L₀,?_⟩
  intro L hL δ hδ hδ1 G Q hQ hG hn hnlog J C N hS K M hK hM Binput Ccover hBi F hF S hcard k
  have hLpos : 0 < L := lt_of_lt_of_le (by norm_num : (0:ℝ)<2) ((le_max_left _ _).trans hL)
  have hδpos : 0 < δ := by
    have hh := (Real.rpow_pos_of_pos hLpos (-(η/2))).trans_le hδ
    linarith only [hh]
  obtain ⟨hiN,hiW⟩ := hjoint L ((le_max_right _ _).trans hL) (2*δ) hδ hδ1
    G Q hQ hG hn hnlog J C N hS K M hK hM Binput Ccover hBi F hF S hcard k
  have hiA := source_leading_joint_integrable (γ := γ) hd hQ hG hn hLpos (ne_of_gt hδpos) J C
    (by linarith : 0 ≤ 1-η/8) hS hK hM hBi hF S hcard k
  apply (((hiN.const_mul (((4:ℂ)^Q.links.length)⁻¹)).add hiA).add
    (hiW.const_mul (((4:ℂ)^Q.links.length)⁻¹))).congr
  exact ae_of_all _ (fun q => (physical_masked_density_decomposition hQ hG hLpos δ γ J C F S q k).symm)

end WaveTurbulence.RegAsymp
