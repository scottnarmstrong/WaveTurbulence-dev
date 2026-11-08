/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Flower.ProtPin.GateAllF
public import WaveTurbulence.Foundations.Flower.ProtPin.GatePre
public import WaveTurbulence.Foundations.Flower.ProtPin.CapGate

/-! # D3 PROT-PIN: `ProtBoundGate` modulo the `termChild` slices

Every configuration other than `termChild` is proved, for trees and cap couples: `protBoundGate_of_termChild`
reduces the gate to the `termChild` slices for trees (`selTChild`) and cap couples. -/

@[expose] public section
set_option autoImplicit false
noncomputable section
open WaveTurbulence WaveTurbulence.LGSpine WaveTurbulence.Induct Set Finset MeasureTheory WaveTurbulence.Fourier
open scoped Classical ENNReal

namespace WaveTurbulence.Flower.ProtPin

open WaveTurbulence.Flower.ProtDefs WaveTurbulence.Flower.ProtCut

/-- **The gate from the `termChild` slices.** -/
theorem protBoundGate_of_termChild
    (hTree : ∀ θ : ℝ, 0 ≤ θ → θ ≤ 1 / 4 → ∃ Cr : ℝ, 0 ≤ Cr ∧ CfgUF θ Cr selTChild)
    (hCapTC : ∀ θ : ℝ, 0 ≤ θ → θ ≤ 1 / 4 →
      ∃ Ct : ℝ, 0 ≤ Ct ∧ CfgUF θ Ct (fun w _ _ cfg => w = 2 ∧ ∃ i, cfg = .termChild i)) : ProtBoundGate :=
  protBoundGate_ofF (fun θ h0 h1 => cfgU_pen_prefix h0 h1) hTree
    (fun θ h0 h1 => capc_cfgU_cap_of h0 h1 (hCapTC θ h0 h1))

end WaveTurbulence.Flower.ProtPin
