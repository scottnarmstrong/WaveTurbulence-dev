/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.XChain.GateConstants
/-! Aligning the exact three gate prefixes without adding a shared-constants hypothesis. -/
public section
namespace WaveTurbulence.Induct
open Set
universe u

/-- The independent existential constants in the three source gates can be aligned.
C₁ and C₂ are taken from wkeTaylor; the other two assertions do not use them. -/
theorem gates_common_prefix (hL : LayergardenGate) (hF : FixedpointGate.{u}) (hW : WkeTaylorGate) :
    WTPrefix (fun P => LayergardenBody P ∧ FixedpointBody.{u} P ∧ WkeTaylorBody P) := by
  intro d hd γ hγ
  obtain ⟨ηL, hηL, kL⟩ := hL d hd γ hγ
  obtain ⟨ηF, hηF, kF⟩ := hF d hd γ hγ
  obtain ⟨ηW, hηW, kW⟩ := hW d hd γ hγ
  let η₀ := min ηL (min ηF ηW)
  refine ⟨η₀, lt_min hηL (lt_min hηF hηW), ?_⟩
  intro η hη φin hφ τstar hτ φ hsol
  have hηall : η ≤ ηL ∧ η ≤ ηF ∧ η ≤ ηW := by
    simpa only [η₀, le_min_iff] using hη.2
  obtain ⟨CL, _, νL, hνL, rL⟩ := kL η ⟨hη.1, hηall.1⟩ φin hφ τstar hτ φ hsol
  obtain ⟨CF, _, νF, hνF, rF⟩ := kF η ⟨hη.1, hηall.2.1⟩ φin hφ τstar hτ φ hsol
  obtain ⟨CW, hCW, νW, hνW, rW⟩ := kW η ⟨hη.1, hηall.2.2⟩ φin hφ τstar hτ φ hsol
  let ν₀ := min νL (min νF νW)
  refine ⟨CW, hCW, ν₀, lt_min hνL (lt_min hνF hνW), ?_⟩
  intro ν hν
  have hνall : ν ≤ νL ∧ ν ≤ νF ∧ ν ≤ νW := by
    simpa only [ν₀, le_min_iff] using hν.2
  obtain ⟨δL, hδL, sL⟩ := rL ν ⟨hν.1, hνall.1⟩
  obtain ⟨δF, hδF, sF⟩ := rF ν ⟨hν.1, hνall.2.1⟩
  obtain ⟨δW, hδW, sW⟩ := rW ν ⟨hν.1, hνall.2.2⟩
  let δ₀ := min δL (min δF δW)
  refine ⟨δ₀, lt_min hδL (lt_min hδF hδW), ?_⟩
  intro δ hδ D hD htime
  have hδall : δ ≤ δL ∧ δ ≤ δF ∧ δ ≤ δW := by
    simpa only [δ₀, le_min_iff] using hδ.2
  obtain ⟨C₂L, _, LL, hLL, tL⟩ := sL δ ⟨hδ.1, hδall.1⟩ D hD htime
  obtain ⟨C₂F, _, LF, hLF, tF⟩ := sF δ ⟨hδ.1, hδall.2.1⟩ D hD htime
  obtain ⟨C₂W, hC₂W, LW, hLW, tW⟩ := sW δ ⟨hδ.1, hδall.2.2⟩ D hD htime
  let L₀ := max LL (max LF LW)
  refine ⟨C₂W, hC₂W, L₀, hLL.trans (le_max_left _ _), ?_⟩
  intro L hsize
  have hsizeall : LL ≤ L ∧ LF ≤ L ∧ LW ≤ L := by
    simpa only [L₀, max_le_iff] using hsize
  let PL : WTParams := ⟨d, γ, η, φin, τstar, φ, CL, ν, δ, D, C₂L, L⟩
  let PF : WTParams := ⟨d, γ, η, φin, τstar, φ, CF, ν, δ, D, C₂F, L⟩
  refine ⟨?_, ?_, tW L hsizeall.2.2⟩
  · change LayergardenBody {PL with C₁ := CW, C₂ := C₂W}
    rw [layergardenBody_update_aux]
    exact tL L hsizeall.1
  · change FixedpointBody.{u} {PF with C₁ := CW, C₂ := C₂W}
    rw [fixedpointBody_update_aux]
    exact tF L hsizeall.2.1

end WaveTurbulence.Induct
