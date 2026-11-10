/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.XChain.GateTypes

/-!
# Snapshot-5 gate statements as Props (aliases of the INDUCT gates)

The bodies of B1.2 `layergarden`, B1.3 `fixedpoint`, B1.5 `wkeTaylor` and B1.1 `propansatz`. In the scratch
packet they were verbatim copies of wt-cumul's INDUCT `GateTypes.lean` (sha256
`14422e2b7d5bb0eaaea259a0e3739cb16d91a7382773e6e4b1883b0e0a976bf1`) under the namespace `WaveTurbulence.Gates`.
On main each is an `abbrev` alias of the corresponding `Induct` gate (PORT-PLAN D11): the bodies were textually
identical, so the aliases change no meaning (second-key audit, /home/scott/wt-scratch/audit-b2a).
-/

@[expose] public section
namespace WaveTurbulence.Gates
open MeasureTheory ProbabilityTheory Finset Set
open scoped ENNReal

abbrev LayergardenBody (P : WTParams) : Prop := Induct.LayergardenBody P

abbrev FixedpointBody.{u} (P : WTParams) : Prop := Induct.FixedpointBody.{u} P

abbrev WkeTaylorBody (P : WTParams) : Prop := Induct.WkeTaylorBody P

end WaveTurbulence.Gates
