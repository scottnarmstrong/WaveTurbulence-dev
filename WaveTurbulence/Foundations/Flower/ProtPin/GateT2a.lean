/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Flower.ProtPin.GateTC
public import WaveTurbulence.Foundations.Flower.ProtPin.TChildT2

/-! # D3 PROT-PIN: `ProtBoundGate` from the (a+) root trace

Every configuration is proved except the root trace of a type-2 side couple with a nonempty chain on the traced tree
`0` (`tcT2a`, the helper's target `tc2a_trace`): `protBoundGate_of_t2a`. -/

@[expose] public section
set_option autoImplicit false
noncomputable section
open WaveTurbulence WaveTurbulence.LGSpine WaveTurbulence.Induct Set Finset MeasureTheory WaveTurbulence.Fourier
open scoped Classical ENNReal

namespace WaveTurbulence.Flower.ProtPin

open WaveTurbulence.Flower.ProtDefs

/-- **The gate from the (a+) case.** -/
theorem protBoundGate_of_t2a
    (h2a : ∀ θ : ℝ, 0 ≤ θ → θ ≤ 1 / 4 → ∃ Ct : ℝ, 0 ≤ Ct ∧ TcTraceOnF θ Ct tcT2a) : ProtBoundGate :=
  protBoundGate_of_termChild (cfgUF_termChild_tree_of_t2a h2a) (cfgUF_termChild_cap_of_t2a h2a)

end WaveTurbulence.Flower.ProtPin
