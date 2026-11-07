/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Stage1.Represents.RepFinal1
import Mathlib.Tactic

/-!
# S2 REPRESENTS: `noVine_prefix`

The vine-free `RepresentsInt` holds on a `WTPrefix` built from the two leafwise gates.  The parameter ordering
supplies the standing conditions of `GateEnv`: `η` is chosen small depending on `γ₁`, `L ≥ 2`, `d ≥ 3`, `C₁ ≥ 1`.
-/

@[expose] public section
set_option autoImplicit false
open WaveTurbulence.Induct
namespace WaveTurbulence.Represents
open WaveTurbulence WaveTurbulence.LGSpine Set

theorem eta_pow_le (g1 η : ℝ) (hg : 0 < g1) (hη0 : 0 < η) (hη : η ≤ (g1 / 2) ^ 2) (hη1 : η ≤ 1 / 2) :
    η ^ 8 ≤ g1 - Real.sqrt η := by
  have hs : Real.sqrt η ≤ g1 / 2 := by
    calc Real.sqrt η ≤ Real.sqrt ((g1 / 2) ^ 2) := Real.sqrt_le_sqrt hη
      _ = g1 / 2 := Real.sqrt_sq (by linarith)
  have hsq : η ≤ Real.sqrt η := by
    have h1 : Real.sqrt η ≤ 1 := by
      rw [Real.sqrt_le_one]; linarith
    have h2 := Real.sq_sqrt hη0.le
    nlinarith [Real.sqrt_nonneg η]
  have h8 : η ^ 8 ≤ η := by
    have : η ^ 8 ≤ η ^ 1 := pow_le_pow_of_le_one hη0.le (by linarith) (by norm_num)
    simpa using this
  linarith

theorem noVine_prefix (hinc : LeafwiseIncoherentDecayGate) (hcoh : LeafwiseCoherentApproximationGate) :
    WTPrefix NoVineRepresentsAt := by
  have hboth : WTPrefix (fun P => LeafwiseIncoherentDecayAt P ∧ LeafwiseCoherentApproximationAt P) :=
    prefix_and hinc hcoh leafwiseIncoherentDecay_largeConstantMonotone
      leafwiseCoherentApproximation30_largeConstantMonotone
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
  refine ⟨max C₁g (CminF d η C₁g), hC₁g.trans (le_max_left _ _), ν₀, hν₀, ?_⟩
  intro ν hν
  obtain ⟨δ₀, hδ₀, hrest2⟩ := hrest ν hν
  refine ⟨δ₀, hδ₀, ?_⟩
  intro δ hδ D hD htime
  obtain ⟨C₂, hC₂, L₀, hL₀, hrest3⟩ := hrest2 δ hδ D hD htime
  refine ⟨C₂, hC₂, L₀, hL₀, ?_⟩
  intro L hL
  obtain ⟨hincP, hcohP⟩ := hrest3 L hL
  let Pg : WTParams := ⟨d, γ, η, φin, τ, φ, C₁g, ν, δ, D, C₂, L⟩
  have E : GateEnv Pg :=
    { hd1 := by show 1 ≤ d; omega
      hL1 := by show 1 ≤ L; linarith [hL₀.trans hL]
      hη0 := hηm.1.le
      hη := hη2
      hC1 := hC₁g
      hδ0 := hδ.1.le
      hκ := eta_pow_le g1 η hg hηm.1 hη3 hη2
      hinc := hincP
      hcoh := hcohP }
  have h : NoVineRepresentsAt { Pg with C₁ := max C₁g (CminF d η C₁g) } :=
    noVineRepresentsAt_of_gate Pg E (max C₁g (CminF d η C₁g)) (le_max_right _ _)
  exact h

end WaveTurbulence.Represents
