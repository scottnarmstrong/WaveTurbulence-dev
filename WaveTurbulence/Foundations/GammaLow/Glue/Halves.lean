/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import Mathlib
public import WaveTurbulence.Frozen.Defs.WTPrefix
public import WaveTurbulence.Frozen.Defs.WTPrefixP
public import WaveTurbulence.Foundations.XChain.V2Chain.PrefixS

/-! # L0 GLUE: the two γ-halves give the full prefix (packet L07)

`wtPrefix_of_halves` and `wtPrefixP_of_halves` are copied by source from the audited draft
`gamma-half-scope/drafts/HalvesGlue.lean` (sha256 in `COPIED-SHA256SUMS`; AUDIT-V4 §8: PASS, standard axioms only):
its lines 14–61 verbatim, with the namespace `WaveTurbulence.GammaHalfDraft` replaced by this area's. The split is
`by_cases h : 1 / 2 < γ`, so γ = 1/2 belongs to the low half. `toFull` (ANCHORS-DRAFT §4) is the trivial passage
from `V2Chain.WTPrefixS univ` to the frozen `WTPrefix`. Conditional helpers, not anchors. -/

public section
open Set

namespace WaveTurbulence.GammaLow.Glue

theorem wtPrefix_of_halves {Q : WTParams → Prop}
    (hi : WTPrefix fun P => 1 / 2 < P.γ → Q P) (lo : WTPrefix fun P => P.γ ≤ 1 / 2 → Q P) :
    WTPrefix Q := by
  intro d hd γ hγ
  by_cases h : 1 / 2 < γ
  · obtain ⟨η₀, hη₀, H⟩ := hi d hd γ hγ
    refine ⟨η₀, hη₀, fun η hη φin hφ τ hτ φ hW => ?_⟩
    obtain ⟨C₁, hC₁, ν₀, hν₀, H⟩ := H η hη φin hφ τ hτ φ hW
    refine ⟨C₁, hC₁, ν₀, hν₀, fun ν hν => ?_⟩
    obtain ⟨δ₀, hδ₀, H⟩ := H ν hν
    refine ⟨δ₀, hδ₀, fun δ hδ D hD hτD => ?_⟩
    obtain ⟨C₂, hC₂, L₀, hL₀, H⟩ := H δ hδ D hD hτD
    exact ⟨C₂, hC₂, L₀, hL₀, fun L hL => H L hL h⟩
  · obtain ⟨η₀, hη₀, H⟩ := lo d hd γ hγ
    refine ⟨η₀, hη₀, fun η hη φin hφ τ hτ φ hW => ?_⟩
    obtain ⟨C₁, hC₁, ν₀, hν₀, H⟩ := H η hη φin hφ τ hτ φ hW
    refine ⟨C₁, hC₁, ν₀, hν₀, fun ν hν => ?_⟩
    obtain ⟨δ₀, hδ₀, H⟩ := H ν hν
    refine ⟨δ₀, hδ₀, fun δ hδ D hD hτD => ?_⟩
    obtain ⟨C₂, hC₂, L₀, hL₀, H⟩ := H δ hδ D hD hτD
    exact ⟨C₂, hC₂, L₀, hL₀, fun L hL => H L hL (le_of_not_gt h)⟩

theorem wtPrefixP_of_halves {Q : ℕ → WTParams → Prop}
    (hi : WTPrefixP fun Pm P => 1 / 2 < P.γ → Q Pm P) (lo : WTPrefixP fun Pm P => P.γ ≤ 1 / 2 → Q Pm P) :
    WTPrefixP Q := by
  intro d hd γ hγ
  by_cases h : 1 / 2 < γ
  · obtain ⟨η₀, hη₀, H⟩ := hi d hd γ hγ
    refine ⟨η₀, hη₀, fun η hη φin hφ τ hτ φ hW => ?_⟩
    obtain ⟨C₁, hC₁, ν₀, hν₀, H⟩ := H η hη φin hφ τ hτ φ hW
    refine ⟨C₁, hC₁, ν₀, hν₀, fun ν hν => ?_⟩
    obtain ⟨P₀, H⟩ := H ν hν
    refine ⟨P₀, fun Pm hPm => ?_⟩
    obtain ⟨δ₀, hδ₀, H⟩ := H Pm hPm
    refine ⟨δ₀, hδ₀, fun δ hδ D hD hτD => ?_⟩
    obtain ⟨C₂, hC₂, L₀, hL₀, H⟩ := H δ hδ D hD hτD
    exact ⟨C₂, hC₂, L₀, hL₀, fun L hL => H L hL h⟩
  · obtain ⟨η₀, hη₀, H⟩ := lo d hd γ hγ
    refine ⟨η₀, hη₀, fun η hη φin hφ τ hτ φ hW => ?_⟩
    obtain ⟨C₁, hC₁, ν₀, hν₀, H⟩ := H η hη φin hφ τ hτ φ hW
    refine ⟨C₁, hC₁, ν₀, hν₀, fun ν hν => ?_⟩
    obtain ⟨P₀, H⟩ := H ν hν
    refine ⟨P₀, fun Pm hPm => ?_⟩
    obtain ⟨δ₀, hδ₀, H⟩ := H Pm hPm
    refine ⟨δ₀, hδ₀, fun δ hδ D hD hτD => ?_⟩
    obtain ⟨C₂, hC₂, L₀, hL₀, H⟩ := H δ hδ D hD hτD
    exact ⟨C₂, hC₂, L₀, hL₀, fun L hL => H L hL (le_of_not_gt h)⟩


/-- `WTPrefixS univ Q → WTPrefix Q` (ANCHORS-DRAFT §4): the restriction `γ ∈ univ` is vacuous. -/
theorem toFull {Q : WTParams → Prop} (h : V2Chain.WTPrefixS Set.univ Q) : WTPrefix Q :=
  fun d hd γ hγ => h d hd γ hγ (Set.mem_univ γ)

end WaveTurbulence.GammaLow.Glue
