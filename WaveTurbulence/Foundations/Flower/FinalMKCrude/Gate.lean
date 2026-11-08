/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Flower.FinalMKCrude.Coarse
public import WaveTurbulence.Foundations.Flower.LadFilt.Gate

/-! # C2 FINALMK-CRUDE: the deliverable `CoarseSplicedGateMK`

Copy of Port's `coarseSplicedGateST` (main's `Final2`) with C3's `ladderL1GateFilt` and `coarse_fixedMK`. The prefix
constant is `C₁ := C₁(ladderL1GateFilt) · max 1 (𝔟 ψ₀)² · 3^{2d}` (SCOPE: `C₁(ladderL1GateFilt) · 3^{2d} ·
max 1 𝔟(ψ₀)`; the square comes from the per-ladder factor `(max 1 𝔟 ψ₀)^{2m+2}` being absorbed into
`C₁ (C₁ δ)^m`), `C₂ := 1`. -/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.Flower.FinalMKCrude
open WaveTurbulence WaveTurbulence.LGSpine WaveTurbulence.LadderDecay WaveTurbulence.CoarseSpliced Set
open WaveTurbulence.Flower.LadFilt (LadderL1AtFilt filterB ladderL1GateFilt)
open WaveTurbulence.Flower.FinalMKDefs (CoarseSplicedAtMK CoarseSplicedGateMK)
open scoped Classical

/-- **C2 deliverable**: the crude bound with pins, filters and indicators, for all small parameters. -/
theorem coarseSplicedGateMK : CoarseSplicedGateMK := by
  obtain ⟨ψ₀, hψ₀⟩ := exists_bump
  intro d hd γ hγ
  obtain ⟨hγ0, hγ1⟩ := hγ
  obtain ⟨η₀g, hη₀g, hg⟩ := ladderL1GateFilt d hd γ ⟨hγ0, hγ1⟩
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
  refine ⟨Cg * max 1 (filterB ⇑ψ₀) ^ 2 * 3 ^ (2 * d), ?_, ν₀g, hν₀g, ?_⟩
  · have h3 : (1 : ℝ) ≤ 3 ^ (2 * d) := one_le_pow₀ (by norm_num)
    have h2 : (1 : ℝ) ≤ max 1 (filterB ⇑ψ₀) ^ 2 := one_le_pow₀ (le_max_left _ _)
    have h4 : 1 ≤ Cg * max 1 (filterB ⇑ψ₀) ^ 2 := by nlinarith
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
  exact coarse_fixedMK ⟨d, γ, η, φin, τ, φ, Cg, ν, δ, Dd, C₂g, L⟩ hd hγ0 hγ1 hη0
    (by simpa [WTParams.gamma1, hg1] using hη4) hη1 hδ.1 (hδ.2.trans (min_le_right _ _)) (by linarith) hCg ψ₀ hψ₀
    hgate

end WaveTurbulence.Flower.FinalMKCrude
