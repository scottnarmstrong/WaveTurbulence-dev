/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.XChain.GateTypes

/-!
# Snapshot-5 gate statements as Props (copied from INDUCT)

The bodies of B1.2 `layergarden`, B1.3 `fixedpoint`, B1.5 `wkeTaylor` and B1.1 `propansatz`. They are copied
verbatim from wt-cumul's INDUCT `GateTypes.lean` (`/home/scott/wt-scratch/induct/GateTypes.lean`, sha256
`14422e2b7d5bb0eaaea259a0e3739cb16d91a7382773e6e4b1883b0e0a976bf1`). Only the namespace changes (`WaveTurbulence.Gates` instead of `WaveTurbulence.Induct`), so the two
copies never clash. `X2-Probes.lean` checks each body against the snapshot theorem by definitional equality.
-/

@[expose] public section
namespace WaveTurbulence.Gates
open MeasureTheory ProbabilityTheory Finset Set
open scoped ENNReal

abbrev LayergardenBody (P : WTParams) : Prop := Induct.LayergardenBody P

abbrev LayergardenGate : Prop := Induct.LayergardenGate

abbrev FixedpointBody.{u} (P : WTParams) : Prop := Induct.FixedpointBody.{u} P

abbrev FixedpointGate.{u} : Prop := Induct.FixedpointGate.{u}

abbrev WkeTaylorBody (P : WTParams) : Prop := Induct.WkeTaylorBody P

abbrev WkeTaylorGate : Prop := Induct.WkeTaylorGate

abbrev PropansatzBody.{u} (P : WTParams) : Prop := Induct.PropansatzBody.{u} P

abbrev PropansatzGate.{u} : Prop := Induct.PropansatzGate.{u}

end WaveTurbulence.Gates
