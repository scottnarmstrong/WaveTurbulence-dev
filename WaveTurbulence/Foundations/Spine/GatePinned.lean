/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.Spine.coarse_spliced.Final2
public import WaveTurbulence.Foundations.Spine.SourceSplicedBounds
/-! Canonical coarse spliced bound with the literal source counting inputs. -/
public section
namespace WaveTurbulence.CoarseSpliced
open WaveTurbulence WaveTurbulence.LGSpine Set Finset
open WaveTurbulence.LGSpine in
theorem coarse_iff (P : WTParams) : CoarseSplicedAt P ↔ CoarseSplicedAtC P := by
  constructor
  · intro h p hp R hR1 hR2 G hpl hir hbal hn1 hn2 D hD hl A base roots hprem
    exact h p hp R hR1 hR2 G hpl hir hbal hn1 hn2 D hD hl
      ⟨A.length, A.upper, A.lower, A.ladder, A.atoms⟩ base roots
      ⟨hprem.molecule, hprem.connected, hprem.atom_count, hprem.bond_count, hprem.subpro⟩
  · intro h p hp R hR1 hR2 G hpl hir hbal hn1 hn2 D hD hl A base roots hprem
    exact h p hp R hR1 hR2 G hpl hir hbal hn1 hn2 D hD hl
      ⟨A.length, A.upper, A.lower, A.ladder, A.atoms⟩ base roots
      ⟨hprem.molecule, hprem.connected, hprem.atom_count, hprem.bond_count, hprem.subpro⟩

/-- The gate transfers: the coarse gate for the copy is the pinned coarse gate. -/
theorem coarseGate_of_copy (h : WTPrefix CoarseSplicedAtC) : CoarseSplicedGate := by
  intro d hd γ hγ
  obtain ⟨η₀, hη₀, hh⟩ := h d hd γ hγ
  refine ⟨η₀, hη₀, fun η hη φin hφin τ hτ φ hφ => ?_⟩
  obtain ⟨C₁, hC₁, ν₀, hν₀, hh2⟩ := hh η hη φin hφin τ hτ φ hφ
  refine ⟨C₁, hC₁, ν₀, hν₀, fun ν hν => ?_⟩
  obtain ⟨δ₀, hδ₀, hh3⟩ := hh2 ν hν
  refine ⟨δ₀, hδ₀, fun δ hδ D hD hτD => ?_⟩
  obtain ⟨C₂, hC₂, L₀, hL₀, hh4⟩ := hh3 δ hδ D hD hτD
  exact ⟨C₂, hC₂, L₀, hL₀, fun L hL => (coarse_iff _).mpr (hh4 L hL)⟩


theorem coarseSplicedGatePinned : CoarseSplicedGate := coarseGate_of_copy coarseSplicedGate
end WaveTurbulence.CoarseSpliced
