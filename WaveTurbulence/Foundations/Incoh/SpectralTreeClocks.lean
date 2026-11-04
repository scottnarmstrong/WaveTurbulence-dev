/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Incoh.SpectralLinkParameters
public import WaveTurbulence.Foundations.Incoh.TreeClockFibers

/-!
# The actual source tree clock fibers under spectral localization

Spectral localization changes only momentum centers and shifts. Every
clock, interval, source ordering and literal time domain is retained.
-/

public section
noncomputable section

namespace WaveTurbulence.Incoh

/-- The original structural tree fibers with the computed spectral link parameters. -/
@[expose] def MomentumTreeData.spectralTreeClockFibers {d n m w l : ℕ}
    (P : MomentumTreeData n m w) (Q : Fin n → LayerLink d) (T : TreeClockFibers l Q)
    (z : (Fin n × Fin 2) → Fin d → ℤ) (ξ : LocalizedCellIndex n m → Fin d → ℝ) :
    TreeClockFibers l (P.spectralLinks Q z ξ) where
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

/-- The literal source time domain is unchanged by spectral localization. -/
theorem MomentumTreeData.timeDomain_spectralTreeClockFibers {d n m w l : ℕ}
    (P : MomentumTreeData n m w) (Q : Fin n → LayerLink d) (T : TreeClockFibers l Q)
    (z : (Fin n × Fin 2) → Fin d → ℤ) (ξ : LocalizedCellIndex n m → Fin d → ℝ) :
    (P.spectralTreeClockFibers Q T z ξ).timeDomain = T.timeDomain := rfl

end WaveTurbulence.Incoh
