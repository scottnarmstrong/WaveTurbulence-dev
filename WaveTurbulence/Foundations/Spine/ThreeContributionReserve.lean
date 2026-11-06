/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.Spine.CoherentStageThresholds
public import WaveTurbulence.Foundations.Spine.PrefixMap
/-! The final large-L threshold pays for the three genuine couple contributions. -/
@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.LGSpine
open WaveTurbulence.Induct
open Filter

abbrev ThreeContributionReserveAt (P : WTParams) : Prop :=
  ∀ p : ℕ, p < P.D →
    3 * P.L ^ (-((3 * P.theta (p + 1) + 2 * P.theta p) / 5)) ≤
      P.L ^ (-((4 * P.theta (p + 1) + P.theta p) / 5))

theorem prefix_with_three_contribution_reserve {Q : WTParams → Prop} (hQ : WTPrefix Q) :
    WTPrefix (fun P => Q P ∧ ThreeContributionReserveAt P) := by
  intro d hd γ hγ
  obtain ⟨η₀, hη₀, hQ⟩ := hQ d hd γ hγ
  refine ⟨η₀, hη₀, ?_⟩
  intro η hη φin hφin τ hτ φ hsol
  obtain ⟨C₁, hC₁, ν₀, hν₀, hQ⟩ := hQ η hη φin hφin τ hτ φ hsol
  refine ⟨C₁, hC₁, ν₀, hν₀, ?_⟩
  intro ν hν
  obtain ⟨δ₀, hδ₀, hQ⟩ := hQ ν hν
  refine ⟨δ₀, hδ₀, ?_⟩
  intro δ hδ D hD htime
  obtain ⟨C₂, hC₂, Lsource, hLsource, hQ⟩ := hQ δ hδ D hD htime
  let P₀ : WTParams := ⟨d, γ, η, φin, τ, φ, C₁, ν, δ, D, C₂, Lsource⟩
  have hlarge := eventually_coherent_stage_thresholds P₀ hη.1
    (a := 2 * η ^ 20 + 1) (C := C₂) (by change 2 * η ^ 20 < 2 * η ^ 20 + 1; linarith)
    (fun _ => 0) (fun _ => le_rfl)
  obtain ⟨Lfinal, hfinal⟩ := Filter.eventually_atTop.mp hlarge
  refine ⟨C₂, hC₂, max Lsource Lfinal, hLsource.trans (le_max_left _ _), ?_⟩
  intro L hL
  refine ⟨hQ L ((le_max_left _ _).trans hL), ?_⟩
  intro p hp
  exact ((hfinal L ((le_max_right _ _).trans hL)).2.2 ⟨p, hp⟩).2.2.2

end WaveTurbulence.LGSpine
