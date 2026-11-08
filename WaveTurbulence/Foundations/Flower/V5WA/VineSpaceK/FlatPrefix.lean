/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Flower.V5WA.VineSpaceK.FlatHalf
public import WaveTurbulence.Foundations.VineEst.VineEstS5C.Step3PrefixH
public import WaveTurbulence.Foundations.Vine.DegenVinePar.SumintMixDoubled

/-! Prefix quantifiers for the weighted flat estimate. The constants retain
R78's order, including the late Kb, and are independent of the multiplier
and its mass. This remains a flat-observable result, not a class export. -/

@[expose] public section
namespace WaveTurbulence.VineSpaceK
open WaveTurbulence WaveTurbulence.LGSpine WaveTurbulence.VineEstS3 WaveTurbulence.VineEstS3.Eng WaveTurbulence.DegenVinePar
  VineParamContract Set
open WaveTurbulence.VineEstS5C WaveTurbulence.VineEstS5C.P4.W13 WaveTurbulence.VineEstS5C.P1 WaveTurbulence.VineEstS5C.P2
open scoped ENNReal
open VineEstS5C.P4.Final

theorem vineFlatC2MX_of_uniformCert (hU : UniformTermCertTargetK) (hG : LeafwiseCoherentApproximationGate)
    (hI : LeafwiseIncoherentDecayGate) (hR : RealityAll) : WTPrefix VineFlatC2MX := by
  intro d hd γ hγ
  obtain ⟨ηU, hηU, hUa⟩ := hU d hd γ hγ
  obtain ⟨ηS, hηS, hSa⟩ := sumintMixParDoubled d hd γ hγ
  obtain ⟨ηG, hηG, hGa⟩ := hG d hd γ hγ
  obtain ⟨ηI, hηI, hIa⟩ := hI d hd γ hγ
  refine ⟨min (min ηU (min ηS (min ηG ηI))) (1 / 5), lt_min (lt_min hηU (lt_min hηS (lt_min hηG hηI))) (by norm_num), ?_⟩
  intro η hη φin hφin τ hτ φ hsol
  have hη0 : 0 < η := hη.1
  have hm : η ≤ min ηU (min ηS (min ηG ηI)) := hη.2.trans (min_le_left _ _)
  have hη5 : η ≤ 1 / 5 := hη.2.trans (min_le_right _ _)
  have hηU' : η ∈ Ioc 0 ηU := ⟨hη0, hm.trans (min_le_left _ _)⟩
  have hηS' : η ∈ Ioc 0 ηS := ⟨hη0, hm.trans ((min_le_right _ _).trans (min_le_left _ _))⟩
  have hηG' : η ∈ Ioc 0 ηG := ⟨hη0, hm.trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))⟩
  have hηI' : η ∈ Ioc 0 ηI := ⟨hη0, hm.trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _)))⟩
  obtain ⟨CS, hCS, νS, hνS, hSb⟩ := hSa η hηS' 6561 (by norm_num) φin hφin τ hτ φ hsol
  obtain ⟨CG, hCG, νG, hνG, hGb⟩ := hGa η hηG' φin hφin τ hτ φ hsol
  obtain ⟨CI, hCI, νI, hνI, hIb⟩ := hIa η hηI' φin hφin τ hτ φ hsol
  set c₀ : ℝ := max (max CS CG) CI with hc₀d
  have hc₀ : 1 ≤ c₀ := hCS.trans ((le_max_left _ _).trans (le_max_left _ _))
  have hCSc : CS ≤ c₀ := (le_max_left _ _).trans (le_max_left _ _)
  have hCGc : CG ≤ c₀ := (le_max_right _ _).trans (le_max_left _ _)
  have hCIc : CI ≤ c₀ := le_max_right _ _
  obtain ⟨Km, Kr, hKm, hKr, hUb⟩ := hUa η hηU' φin hφin τ hτ φ hsol c₀ hc₀
  set C₁ : ℝ := max 1 ((Eng.ccη η + 1).toReal * countKc * engNs η c₀ Km Kr) with hC₁d
  refine ⟨C₁, le_max_left _ _, min νS (min νG νI), lt_min hνS (lt_min hνG hνI), ?_⟩
  intro ν hν
  have hνS' : ν ∈ Ioc 0 νS := ⟨hν.1, hν.2.trans (min_le_left _ _)⟩
  have hνG' : ν ∈ Ioc 0 νG := ⟨hν.1, hν.2.trans ((min_le_right _ _).trans (min_le_left _ _))⟩
  have hνI' : ν ∈ Ioc 0 νI := ⟨hν.1, hν.2.trans ((min_le_right _ _).trans (min_le_right _ _))⟩
  obtain ⟨δS, hδS, hSc⟩ := hSb ν hνS'
  obtain ⟨δG, hδG, hGc⟩ := hGb ν hνG'
  obtain ⟨δI, hδI, hIc⟩ := hIb ν hνI'
  refine ⟨min δS (min δG δI), lt_min hδS (lt_min hδG hδI), ?_⟩
  intro δ hδ D hD htime
  have hδS' : δ ∈ Ioc 0 δS := ⟨hδ.1, hδ.2.trans (min_le_left _ _)⟩
  have hδG' : δ ∈ Ioc 0 δG := ⟨hδ.1, hδ.2.trans ((min_le_right _ _).trans (min_le_left _ _))⟩
  have hδI' : δ ∈ Ioc 0 δI := ⟨hδ.1, hδ.2.trans ((min_le_right _ _).trans (min_le_right _ _))⟩
  obtain ⟨Kb, hKb, hUb'⟩ := hUb ν δ D hδ.1 htime
  obtain ⟨C₂S, hC₂S, LS, hLS, hSd⟩ := hSc δ hδS' D hD htime
  obtain ⟨C₂G, hC₂G, LG, hLG, hGd⟩ := hGc δ hδG' D hD htime
  obtain ⟨C₂I, hC₂I, LI, hLI, hId⟩ := hIc δ hδI' D hD htime
  refine ⟨max (max C₂S (max C₂G C₂I)) (countKp D * Kb), hC₂S.trans ((le_max_left _ _).trans (le_max_left _ _)), max LS (max LG LI),
    hLS.trans (le_max_left _ _), ?_⟩
  intro L hL
  have hLS' : LS ≤ L := (le_max_left _ _).trans hL
  have hLG' : LG ≤ L := ((le_max_left _ _).trans (le_max_right _ _)).trans hL
  have hLI' : LI ≤ L := ((le_max_right _ _).trans (le_max_right _ _)).trans hL
  have hL2 : 2 ≤ L := hLS.trans hLS'
  set C₂ : ℝ := max (max C₂S (max C₂G C₂I)) (countKp D * Kb) with hC₂d
  have hC₂S' : C₂S ≤ C₂ := (le_max_left _ _).trans (le_max_left _ _)
  have hC₂G' : C₂G ≤ C₂ := (le_max_of_le_right (le_max_left _ _)).trans (le_max_left _ _)
  have hC₂I' : C₂I ≤ C₂ := (le_max_of_le_right (le_max_right _ _)).trans (le_max_left _ _)
  have hC₂K : (countKp D : ℝ) * Kb ≤ C₂ := le_max_right _ _
  let PS : WTParams := ⟨d, γ, η, φin, τ, φ, CS, ν, δ, D, C₂S, L⟩
  let PG : WTParams := ⟨d, γ, η, φin, τ, φ, CG, ν, δ, D, C₂G, L⟩
  let PI : WTParams := ⟨d, γ, η, φin, τ, φ, CI, ν, δ, D, C₂I, L⟩
  let Pe : WTParams := ⟨d, γ, η, φin, τ, φ, c₀, ν, δ, D, C₂, L⟩
  have hdb : SumintMixParDoubledAt 6561 Pe :=
    sumintMixPar_mono 6561 PS c₀ C₂ hCS hC₂S hδ.1 hL2 hCSc hC₂S' (hSd L hLS')
  have hgate : CoherentGateH Pe :=
    coherentGateH_of (leafwiseCoherentAt_largeConstantMonotone PG c₀ C₂ hCG hC₂G hδ.1 (hLG.trans hLG') hCGc hC₂G'
      (hGd L hLG'))
  have hinc : IncoherentGateH Pe :=
    incoherentGateH_of (leafwiseIncoherentDecay_largeConstantMonotone PI c₀ C₂ hCI hC₂I hδ.1 (hLI.trans hLI') hCIc hC₂I'
      (hId L hLI'))
  have hη6 : 6 * η ^ 6 ≤ η := by
    have h5 : η ^ 5 ≤ (1 / 5 : ℝ) ^ 5 := pow_le_pow_left₀ hη0.le hη5 5
    calc 6 * η ^ 6 = 6 * η ^ 5 * η := by ring
      _ ≤ 6 * (1 / 5) ^ 5 * η := by gcongr
      _ ≤ η := by nlinarith
  have hAmb : AmbP 6561 Pe :=
    ⟨hdb, by show 0 < L; linarith, hη0, by show η ≤ 1 / 2; linarith, by show η < 1 / 4; linarith,
      by show 0 ≤ c₀; linarith, hδ.1, by show 1 ≤ d; omega, by show 6 * η ^ 6 ≤ 1 - η; linarith, hη6,
      by show 3 * η ≤ 1; linarith⟩
  have hUC : UniformTermCertAtK 6561 Pe Km Kr Kb := hUb' C₂ L hL2 hAmb
  have key : VineFlatC2MX ({Pe with C₁ := C₁} : WTParams) := vineFlatC2MX_core Pe C₁ Km Kr Kb hKm hKr hKb hR hgate hinc hUC hc₀ hη0
    (by show η ≤ 1 / 2; linarith) hL2 (le_max_right _ _) hC₂K
  exact @key

/-- **`WTPrefix VineFlatHalfMX`** from the same inputs (R54 (ii) from (i), modulated). -/
theorem vineFlatHalfMX_of_uniformCert (hU : UniformTermCertTargetK) (hG : LeafwiseCoherentApproximationGate)
    (hI : LeafwiseIncoherentDecayGate) (hR : RealityAll) : WTPrefix VineFlatHalfMX :=
  vineFlatHalfMX_of_C2MX (vineFlatC2MX_of_uniformCert hU hG hI hR)

end WaveTurbulence.VineSpaceK
