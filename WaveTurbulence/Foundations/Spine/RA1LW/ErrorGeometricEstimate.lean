/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Spine.RA1LW.Base
public import WaveTurbulence.Foundations.Spine.RA1LW.ErrorCommonConstant

/-! # Geometric full mixed-norm estimate with constants before the order cutoff -/

public section
noncomputable section
namespace WaveTurbulence.RA1Leafwise
open WaveTurbulence.RegAsymp
open MeasureTheory Links Incoh ClassJR ApproxNT WaveTurbulence.Fourier

/-- The actual combined physical source error has one uniform geometric
constant before every logarithmic order exponent. -/
theorem exists_geometric_physical_error_bound {d : ℕ} (hd : 3 ≤ d) {γ η : ℝ}
    (hγ : γ ∈ Set.Ioo (0:ℝ) 1) (hη0 : 0 < η) (hη : η ≤ 1/20)
    (hηγ : η ≤ ((d:ℝ)-1)*(1-γ)) (hηγ' : η ≤ γ)
    {Agev Cbase : ℝ} (hAgev : 0 ≤ Agev) (hCbase : 1 ≤ Cbase)
    {Nsp W K M : ℕ} (hK : d+2+Nsp ≤ K) (hM : W+2*d ≤ M)
    {Binput Ccover : ℝ} (hBi : 0 ≤ Binput) (hCc : 0 ≤ Ccover) :
    ∃ Cerror : ℝ, 1 ≤ Cerror ∧
      ∀ Aorder : ℝ, ∃ L₀ : ℝ, ∀ L : ℝ, L₀ ≤ L →
      ∀ δ : ℝ, L^(-(η/2)) ≤ 2*δ → 2*δ ≤ 1 →
      ∀ (G : Garden 2) (Q : RegCpl) (hQ : Q.Decodes G) (hG : IsCouple G),
      0 < Q.links.length → (Q.links.length:ℝ) ≤ Real.log L^Aorder →
      ∀ C : (Z : (chosenSet Q.links).powerset) →
        ({j : Fin Q.links.length // j ∉ markedLinkIndices Q Z.val} → ℝ) → ℝ × ℝ → ℂ,
      (∀ Z, SRep (1-η/8) (η/4) (1-η/2) Agev (Cbase^(4*Q.links.length+1)) (C Z)) →
      ∀ ζ : ℂ, ‖ζ‖ ≤ 1 →
      ∀ F : Fin (2*Q.links.length+1) → Mom d → ℂ, (∀ a, spatialNorm K M (F a) ≤ ENNReal.ofReal Binput) →
      ∀ S : (Fin (2*Q.links.length+1) → Fin d → ℤ) → Finset ((Fin Q.links.length × Fin 2) → Fin d → ℤ),
      (∀ c, ((S c).card:ℝ) ≤ Ccover^Q.links.length) →
      ∀ T : Set (Fin 2 → ℝ), (∀ t ∈ T, ∀ i, t i ∈ Set.Icc (0:ℝ) 1) →
      mixedRestrictionNorm η Nsp W T Set.univ
        (fun t k => sourceScalarProfile hQ hG (physicalErrorScalar L δ γ Q ζ C) F S t.val k.val) ≤
        ENNReal.ofReal (Cerror*(Cerror*δ)^Q.links.length*L^(-gamma1 d γ+2*η)) := by
  obtain ⟨Kr,Cm,hKr,hCm,hsp⟩ := physical_error_spatial_estimate hd hγ hη0 hη hηγ hηγ' hAgev hCbase
  obtain ⟨Cerror,hCe,hbudget⟩ := exists_common_physical_error_constant d Nsp W M η hKr.le
    (zero_le_one.trans hCm) hCc hBi
  refine ⟨Cerror,hCe,?_⟩
  intro Aorder
  obtain ⟨L₀,hsp⟩ := hsp Aorder
  refine ⟨max 2 L₀,?_⟩
  intro L hL δ hδ hδ1 G Q hQ hG hn hnlog C hC ζ hζ F hF S hcard T hT
  have hLpos : 0 < L := lt_of_lt_of_le (by norm_num : (0:ℝ)<2) ((le_max_left _ _).trans hL)
  have hδpos : 0 < δ := by
    have hh := (Real.rpow_pos_of_pos hLpos (-(η/2))).trans_le hδ
    linarith only [hh]
  exact (hsp L ((le_max_right _ _).trans hL) δ hδ hδ1 G Q hQ hG hn hnlog C hC ζ hζ
    Nsp W K M hK hM Binput Ccover hBi F hF S hcard T hT).trans
      (hbudget Q δ (L^(-gamma1 d γ+2*η)) hδpos.le (Real.rpow_nonneg hLpos.le _))

end WaveTurbulence.RA1Leafwise
