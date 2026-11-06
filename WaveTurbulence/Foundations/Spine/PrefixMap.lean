/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.WaveB.FrozenB1
/-! Logical mapping of the exact source parameter prefix, preserving constant dependencies. -/
public section
set_option autoImplicit false
namespace WaveTurbulence.LGSpine
open Set

theorem prefix_map {A B : WTParams → Prop} (h : ∀ P, A P → B P)
    (hA : WTPrefix A) : WTPrefix B := by
  intro d hd γ hγ
  obtain ⟨η0, hη0, hη⟩ := hA d hd γ hγ
  refine ⟨η0, hη0, ?_⟩
  intro η hη' φin hφin τ hτ φ hsol
  obtain ⟨C1, hC1, ν0, hν0, hν⟩ := hη η hη' φin hφin τ hτ φ hsol
  refine ⟨C1, hC1, ν0, hν0, ?_⟩
  intro ν hν'
  obtain ⟨δ0, hδ0, hδ⟩ := hν ν hν'
  refine ⟨δ0, hδ0, ?_⟩
  intro δ hδ' D hD htime
  obtain ⟨C2, hC2, L0, hL0, hL⟩ := hδ δ hδ' D hD htime
  exact ⟨C2, hC2, L0, hL0, fun L hL' => h _ (hL L hL')⟩

end WaveTurbulence.LGSpine
