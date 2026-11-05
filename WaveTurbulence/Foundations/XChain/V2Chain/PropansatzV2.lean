/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.XChain.V2Chain.GateTypes
public import WaveTurbulence.Foundations.XChain.V2Chain.PropansatzS

/-!
# V2-CHAIN 2: `propansatz_v2` from the gates

`propansatz_v2_of_gates` is INDUCT's `propansatz_of_gates` re-run for the successor bodies: hypotheses
`layergarden_v2`, `fixedpoint_v2`, `wkeTaylor`; conclusion `propansatz_v2`. Conditional helper.
-/

@[expose] public section

namespace WaveTurbulence.V2Chain

open WaveTurbulence

universe u

theorem propansatz_v2_of_gates (hL : LayergardenV2Gate) (hF : FixedpointV2Gate.{u})
    (hW : WkeTaylorGate) : PropansatzV2Gate.{u} := by
  have hL' : WTPrefix fun P => 1 / 2 < P.γ → Induct.LayergardenBody P := hL
  have hF' : WTPrefix fun P => 1 / 2 < P.γ → Induct.FixedpointBody.{u} P := hF
  have hW' : WTPrefix Induct.WkeTaylorBody := hW
  exact (propansatzS_of_gates (WTPrefixS.ofR hL') (WTPrefixS.ofR hF') (WTPrefixS.ofFull hW')).toR

end WaveTurbulence.V2Chain
