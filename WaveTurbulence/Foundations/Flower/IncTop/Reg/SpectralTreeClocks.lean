/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Flower.IncTop.Reg.SpectralLinkParameters
public import WaveTurbulence.Foundations.Incoh.TreeClockFibers

/-! Ported by source from C2-B-TOP `Cut2BReg.SpectralTreeClocks` (sha256 in COPIED-SHA256SUMS); mechanical edits only.

R66 spatially modulated scratch copy. Original SHA256 recorded in REG-COPIES.json.

# The actual source tree clock fibers under spectral localization

Spectral localization changes only momentum centers and shifts. Every
clock, interval, source ordering and literal time domain is retained.
-/

public section
noncomputable section

namespace WaveTurbulence.Flower.IncTop
open WaveTurbulence.Incoh
open WaveTurbulence.Incoh.MomentumTreeData in
/-- The original structural tree fibers with the computed spectral link parameters. -/
@[expose] def MomentumTreeData.spectralTreeClockFibersSpatial {d n m w l : ℕ}
    (P : MomentumTreeData n m w) (Q : Fin n → LayerLink d) (T : TreeClockFibers l Q)
    (z : (Fin n × Fin 2) → Fin d → ℤ) (ξ : LocalizedCellIndex n m → Fin d → ℝ) :
    TreeClockFibers l ((MomentumTreeData.spectralLinksSpatial (P := P)) Q z ξ) where
  selection := T.selection
  remainingDomain := T.remainingDomain
  measurable_remainingDomain := T.measurable_remainingDomain
  lower := T.lower
  upper := T.upper
  measurable_lower := T.measurable_lower
  measurable_upper := T.measurable_upper
  lower_le_upper := T.lower_le_upper
  remaining_mem_box := T.remaining_mem_box
  interval_mem_box := T.interval_mem_box

end WaveTurbulence.Flower.IncTop