/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.WaveB.FrozenB1
public import WaveTurbulence.Foundations.XChain.GateTypes
public import WaveTurbulence.Foundations.XChain.V2Chain.GateTypes
public import WaveTurbulence.Frozen.Defs.IsSmoothNLSSolution
public import WaveTurbulence.Frozen.Defs.TorusFourierCoeff
public import WaveTurbulence.Frozen.Defs.KineticTime
/-! Exact draft proposition types, used only as hypotheses of the conditional assembly. -/
@[expose] public section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal
namespace WaveTurbulence.MainGlue

abbrev PropansatzGate.{u} : Prop := Induct.PropansatzGate.{u}

abbrev NlsAkBridgeGate.{u} : Prop := V2Chain.NlsAkBridgeGate.{u}

end WaveTurbulence.MainGlue
