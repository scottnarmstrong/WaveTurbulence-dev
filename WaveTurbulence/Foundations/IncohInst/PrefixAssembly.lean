/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.IncohInst.PrefixBounds
public import WaveTurbulence.Foundations.IncohInst.AnchorType
public import WaveTurbulence.Foundations.IncohInst.DecodingObligations

/-! # TARGET Proposition 5.1 at the exact B2.2 parameter prefix -/

public section
noncomputable section
open MeasureTheory Set
namespace WaveTurbulence.IncohInst
open Incoh Links

/-- All B2.2 quantifiers, with the original source kernels and input family. -/
theorem incoherentDecay_core : anchorType := by
  intro d hd γ hγ
  obtain ⟨η₀, hη₀, heta⟩ := exists_source_eta0 d hd γ hγ
  refine ⟨η₀, hη₀, ?_⟩
  intro η hη φin _ τstar _ φ hφ
  obtain ⟨B, hB, hφB⟩ := Regref.exists_SNormR_bound_of_continuousOn hφ.1 (40 * d) (40 * d)
  have hB1 : 0 ≤ B + 1 := by positivity
  obtain ⟨Cc, hCc, hc⟩ := exists_KQstar_decay d hd (B + 1) hB1
  obtain ⟨Ct, hCt, ht⟩ := exists_KTstar_decay d hd (B + 1) hB1
  let C₁ := max 1 (max Cc Ct)
  have hC₁ : 1 ≤ C₁ := le_max_left _ _
  have hcC : Cc ≤ C₁ := (le_max_left _ _).trans (le_max_right _ _)
  have htC : Ct ≤ C₁ := (le_max_right _ _).trans (le_max_right _ _)
  refine ⟨C₁, hC₁, 1, zero_lt_one, ?_⟩
  intro ν _
  refine ⟨1, zero_lt_one, ?_⟩
  intro δ hδ D _ hτ
  obtain ⟨hηsmall, hscale, hηγ⟩ := heta η hη
  obtain ⟨Lc, hLc, hc⟩ := hc η hη.1 (hηsmall.trans (by norm_num)) hscale γ hγ hηγ
    δ hδ.1 hδ.2 D
  obtain ⟨Lt, hLt, ht⟩ := ht η hη.1 hηsmall hscale γ hγ hηγ δ hδ.1 hδ.2 D
  refine ⟨1, le_rfl, max 2 (max Lc Lt), le_max_left _ _, ?_⟩
  intro L hL
  let P : WTParams := ⟨d, γ, η, φin, τstar, φ, C₁, ν, δ, D, 1, L⟩
  have hLtwo : 2 ≤ L := (le_max_left _ _).trans hL
  have hLone : 1 ≤ L := (by norm_num : (1 : ℝ) ≤ 2).trans hLtwo
  have hLcL : Lc ≤ L := ((le_max_left _ _).trans (le_max_right _ _)).trans hL
  have hLtL : Lt ≤ L := ((le_max_right _ _).trans (le_max_right _ _)).trans hL
  intro p hp R hR n _
  change p < D at hp
  have hpD : p ≤ D := Nat.le_of_lt hp
  have hF := inputsF_spatialNorm_le P (by change 1 ≤ d; omega) hLone hδ.1.le hτ hB hφB hpD R hR
  constructor
  · intro Q _ hsize LG hQ hlayers q q' hq hq' hr hr' hg
    have hb := hc L hLcL p hpD Q LG hQ hlayers q q' hq hq' hr hr' hg (inputsF P R) hF
    have hlen : Q.links.length = n := by
      have he : Q.links.length * 2 = Q.size := couple_linksAt_length Q ((0 : Fin 2), []) (1, [])
      omega
    rw [hlen] at hb
    exact hb.trans (componentBound_le_regBound P hCc.le hcC hC₁ hδ.1.le
      (zero_le_one.trans hLone) n _)
  · intro X _ hsize LG hX hlayers q q' hq'q hq _ _ hg
    have hb := ht L hLtL p hpD X LG hX hlayers q q' hq (hq'q.trans hq) hg (inputsF P R) hF
    have hlen : (X.treeLinks (LG.garden.sig 0)).length = n := by
      have he : (X.treeLinks (LG.garden.sig 0)).length * 2 = X.size :=
        chain_linksAt_length X (LG.garden.sig 0) ((0 : Fin 1), [])
      omega
    rw [hlen] at hb
    exact hb.trans (componentBound_le_regBound P hCt.le htC hC₁ hδ.1.le
      (zero_le_one.trans hLone) n _)

end WaveTurbulence.IncohInst
