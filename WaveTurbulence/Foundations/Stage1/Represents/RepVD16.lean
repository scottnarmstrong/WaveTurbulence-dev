/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Stage1.Represents.RepVD15
public import WaveTurbulence.Foundations.Stage1.Represents.RepVC2
public import WaveTurbulence.Foundations.Stage1.Represents.RepS10e
import Mathlib.Tactic

/-!
# S2 REPRESENTS, session 12: the `WTPrefix` of the vine case (B5) and the reduction gate

`vineCase_prefix`: `WTPrefix VineCaseRepresents` from the two leafwise gates, `WTPrefix VineEstCanonLayerHalfMK` (V5) and
`VINEPARAM` (M9); `stage1ReductionGate_of_V5`: `Stage1ReductionGate`.
-/

@[expose] public section
set_option autoImplicit false
open WaveTurbulence.Induct
open WaveTurbulence.VineParamContract
namespace WaveTurbulence.Represents
open WaveTurbulence WaveTurbulence.LGSpine Set VineParamContract

theorem vineCase_prefix (hinc : LeafwiseIncoherentDecayGate) (hcoh : LeafwiseCoherentApproximationGate)
    (hM9 : VINEPARAM) (hV : WTPrefix VineEstCanonLayerHalfMK) : WTPrefix VineCaseRepresents := by
  have hgates : WTPrefix (fun P => LeafwiseIncoherentDecayAt P ∧ LeafwiseCoherentApproximationAt P) :=
    prefix_and hinc hcoh leafwiseIncoherentDecay_largeConstantMonotone
      leafwiseCoherentApproximation30_largeConstantMonotone
  have hboth : WTPrefix (fun P => (LeafwiseIncoherentDecayAt P ∧ LeafwiseCoherentApproximationAt P) ∧
      VineEstCanonLayerHalfMK P) :=
    prefix_and hgates hV (leafwiseIncoherentDecay_largeConstantMonotone.and
      leafwiseCoherentApproximation30_largeConstantMonotone) vineEstHalfMK_mono
  intro d hd γ hγ
  obtain ⟨η₀, hη₀, hη⟩ := hboth d hd γ hγ
  set g1 : ℝ := min (2 * γ) (min 1 (2 * ((d : ℝ) - 1) * (1 - γ))) with hg1
  have hd' : (3 : ℝ) ≤ d := by exact_mod_cast hd
  have hg : 0 < g1 := by
    rw [hg1]
    refine lt_min (by linarith [hγ.1]) (lt_min one_pos ?_)
    have : 0 < 1 - γ := by linarith [hγ.2]
    nlinarith
  refine ⟨min η₀ (min (1 / 2) ((g1 / 2) ^ 2)), lt_min hη₀ (lt_min (by norm_num) (by positivity)), ?_⟩
  intro η hηm φin hφin τ hτ φ hsol
  have hη0 : η ≤ η₀ := hηm.2.trans (min_le_left _ _)
  have hη2 : η ≤ 1 / 2 := hηm.2.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hη3 : η ≤ (g1 / 2) ^ 2 := hηm.2.trans ((min_le_right _ _).trans (min_le_right _ _))
  obtain ⟨C₁g, hC₁g, ν₀, hν₀, hrest⟩ := hη η ⟨hηm.1, hη0⟩ φin hφin τ hτ φ hsol
  refine ⟨max C₁g (CvineF d η C₁g), hC₁g.trans (le_max_left _ _), ν₀, hν₀, ?_⟩
  intro ν hν
  obtain ⟨δ₀, hδ₀, hrest2⟩ := hrest ν hν
  refine ⟨δ₀, hδ₀, ?_⟩
  intro δ hδ D hD htime
  obtain ⟨C₂, hC₂, L₀, hL₀, hrest3⟩ := hrest2 δ hδ D hD htime
  refine ⟨C₂, hC₂, L₀, hL₀, ?_⟩
  intro L hL
  obtain ⟨⟨hincP, hcohP⟩, hVP⟩ := hrest3 L hL
  let Pg : WTParams := ⟨d, γ, η, φin, τ, φ, C₁g, ν, δ, D, C₂, L⟩
  have hL2 : 2 ≤ L := hL₀.trans hL
  have E : GateEnv Pg :=
    { hd1 := by show 1 ≤ d; omega
      hL1 := by show 1 ≤ L; linarith
      hη0 := hηm.1.le
      hη := hη2
      hC1 := hC₁g
      hδ0 := hδ.1.le
      hκ := eta_pow_leN g1 η hg hηm.1 hη3 hη2
      hinc := hincP
      hcoh := hcohP }
  have hV' : VineEstCanonLayerHalfMK (PB Pg (max C₁g (CvineF d η C₁g))) :=
    vineEstHalfMK_mono Pg (max C₁g (CvineF d η C₁g)) C₂ hC₁g hC₂ hδ.1 hL2 (le_max_left _ _) le_rfl hVP
  exact vineCaseRepresents_of_gate Pg (max C₁g (CvineF d η C₁g)) E hηm.1 hδ.1 hL2 hC₂ hM9 (le_max_right _ _) hV'

theorem stage1ReductionGate_of_V5 (hM9 : VINEPARAM) (hinc : LeafwiseIncoherentDecayGate)
    (hcoh : LeafwiseCoherentApproximationGate) (hV : WTPrefix VineEstCanonLayerHalfMK) :
    Stage1ReductionGate :=
  stage1ReductionGate_of_vineCase hinc hcoh (vineCase_prefix hinc hcoh hM9 hV)

end WaveTurbulence.Represents
