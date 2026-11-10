/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.XChain.V2Chain.GateTypes
public import WaveTurbulence.Foundations.XChain.V2Chain.FixedpointS
public import WaveTurbulence.Foundations.XChain.X2EDraft.OX2Exp

/-!
# V2-CHAIN 1: `fixedpoint_v2` from the closed gates

`fixedpoint_v2_of_closed_gates_v3` (D13 product-cutoff assembly) is X2E's `fixedpoint_of_closed_gates` (X3 `fixedpoint_of_gates` with
O-X2-EXP `oX2Exp` and O-X3-CPL `oX3Cpl` proved) re-run for the successor bodies: the hypotheses are the bodies of
`layergardenFlower_v3`, `layergarden_v2` and `wkeTaylor`, the conclusion is the body of `fixedpoint_v2`.
The restriction `1/2 < γ` is threaded through `V2Chain.WTPrefixS`; the inputs `oX2Exp`, `oX3Cpl` are unconditional.
UNOWNED conditional helper (PORT-PLAN hard rule 6; not a source result); it proves nothing about `fixedpoint_v2` itself.
-/

@[expose] public section

open WaveTurbulence.X2E
namespace WaveTurbulence.V2Chain

open WaveTurbulence WaveTurbulence.Fixedpt

universe u

/-- UNOWNED conditional assembly from the exact D13 flower gate and the unchanged v2 layergarden
and WKE Taylor gates. Its conclusion is the frozen `fixedpoint_v2` body. -/
theorem fixedpoint_v2_of_closed_gates_v3 (hG : LayergardenFlowerV3Gate) (hL : LayergardenV2Gate)
    (hW : WkeTaylorGate) : FixedpointV2Gate.{u} := by
  have hG' : WTPrefixP fun Pm P => 1 / 2 < P.γ → B112Body Pm P := hG
  have hL' : WTPrefix fun P => 1 / 2 < P.γ → Gates.LayergardenBody P := hL
  have hW' : WTPrefix Gates.WkeTaylorBody := hW
  exact (fixedpointS_of_parts
    (cplMomentsS_of_gates (WTPrefixPS.ofR hG') (WTPrefixS.ofR hL') (WTPrefixS.ofFull hW') Cpl.oX3Cpl)
    (part2S_of_X2 (flowerest1S_of_gates (WTPrefixPS.ofR hG') X2E.oX2Exp))).toR

end WaveTurbulence.V2Chain
