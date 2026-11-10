/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.RegularAsymptotics.RegAsympDraft.SourceFrequencyRows
public import WaveTurbulence.Foundations.Incoh.SpectralPhaseFactorization
public import WaveTurbulence.Foundations.RegularAsymptotics.RegAsympDraft.HalfLinkFirstMoment
public import WaveTurbulence.Foundations.Spine.RA1LW.LeafFrequencyMass
public import WaveTurbulence.Foundations.Incoh.LocalizedSpectralMassBound
public import WaveTurbulence.Foundations.RegAsymp.FrequencyArrayNorm

/-! # The actual NT frequency weight is paid by the common spectral moment -/

public section
noncomputable section
namespace WaveTurbulence.RA1Leafwise
open WaveTurbulence.RegAsymp
open Links Incoh WithLp MeasureTheory
open scoped ENNReal

/-- Computed frequency loss of the actual C2 transpose map. -/
@[expose] def spectralFrequencyLoss (Q : RegCpl) : ℝ :=
  1+4*Real.pi*(Q.links.length:ℝ)*(1+(Q.size:ℝ))

theorem spectralFrequencyLoss_pos (Q : RegCpl) : 0 < spectralFrequencyLoss Q := by
  unfold spectralFrequencyLoss
  positivity

end WaveTurbulence.RA1Leafwise
