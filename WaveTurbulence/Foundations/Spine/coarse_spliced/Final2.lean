/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.Spine.coarse_spliced.Final1
/-! # The coarse spliced estimate: parameter prefix (S3c) -/
@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.CoarseSpliced
open WaveTurbulence WaveTurbulence.LGSpine WaveTurbulence.LadderDecay Set

/-- **The coarse spliced-kernel estimate** (TARGET finalsbest1, L2075-L2077), for the verbatim copy
`CoarseSplicedAtC` of the pinned `CoarseSplicedAt`. -/
theorem coarseSplicedGate : WTPrefix CoarseSplicedAtC := by
  intro d hd γ hγ
  obtain ⟨hγ0, hγ1⟩ := hγ
  obtain ⟨η₀g, hη₀g, hg⟩ := ladderL1Gate d hd γ ⟨hγ0, hγ1⟩
  set g1 : ℝ := min (2 * γ) (min 1 (2 * ((d : ℝ) - 1) * (1 - γ))) with hg1
  have hdR : (3 : ℝ) ≤ d := by exact_mod_cast hd
  have hg1pos : 0 < g1 := by
    simp only [hg1]
    refine lt_min (by linarith) (lt_min one_pos ?_)
    nlinarith
  have hg1le : g1 ≤ 1 := (min_le_right _ _).trans (min_le_left _ _)
  refine ⟨min η₀g ((g1 / 8) ^ 2), lt_min hη₀g (by positivity), ?_⟩
  intro η hη φin hφin τ hτ φ hφ
  obtain ⟨hη0, hηle⟩ := hη
  obtain ⟨Cg, hCg, ν₀g, hν₀g, hg2⟩ := hg η ⟨hη0, hηle.trans (min_le_left _ _)⟩ φin hφin τ hτ φ hφ
  refine ⟨Cg * 3 ^ (2 * d), ?_, ν₀g, hν₀g, ?_⟩
  · have : (1 : ℝ) ≤ 3 ^ (2 * d) := one_le_pow₀ (by norm_num)
    nlinarith
  intro ν hν
  obtain ⟨δ₀g, hδ₀g, hg3⟩ := hg2 ν hν
  refine ⟨min δ₀g 1, lt_min hδ₀g one_pos, ?_⟩
  intro δ hδ Dd hD hτD
  obtain ⟨C₂g, hC₂g, L₀g, hL₀g, hg4⟩ := hg3 δ ⟨hδ.1, hδ.2.trans (min_le_left _ _)⟩ Dd hD hτD
  refine ⟨1, le_rfl, max L₀g 2, le_max_right _ _, ?_⟩
  intro L hL
  have hgate := hg4 L ((le_max_left _ _).trans hL)
  have hL2 : 2 ≤ L := (le_max_right _ _).trans hL
  have hηsq : η ≤ (g1 / 8) ^ 2 := hηle.trans (min_le_right _ _)
  have hsq : Real.sqrt η ≤ g1 / 8 := by
    rw [Real.sqrt_le_left (by positivity)]
    exact hηsq
  have hη4 : 4 * η ≤ g1 - Real.sqrt η := by
    have h1 : η ≤ (g1 / 8) * (g1 / 8) := by nlinarith
    nlinarith
  have hη1 : η ≤ 1 := by nlinarith
  exact coarse_fixed ⟨d, γ, η, φin, τ, φ, Cg, ν, δ, Dd, C₂g, L⟩ hd hγ0 hγ1 hη0
    (by simpa [WTParams.gamma1, hg1] using hη4) hη1 hδ.1 (hδ.2.trans (min_le_right _ _)) (by linarith) hCg
    hgate

end WaveTurbulence.CoarseSpliced
