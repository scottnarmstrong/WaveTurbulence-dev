/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Frozen.Defs.XNormRestr

/-! # PROT-TA: the pinned statement `TerminalOperatorBound`

Copied by source from the S-MARKED probe `/home/scott/wt-scratch/flower-core/scope/S-MARKED/probe/MarkedProbe.lean`
(sha256 `94102f8c…`, §6, lines 360-368), namespace changed to `WaveTurbulence.Flower.ProtTa`; see
`COPIED-SHA256SUMS`. The `open`s are those of the probe. -/

@[expose] public section
set_option autoImplicit false
noncomputable section
open WaveTurbulence Set Finset MeasureTheory
open scoped Classical ENNReal

namespace WaveTurbulence.Flower.ProtTa

/-- **TerminalOperatorBound** (o73 Lemma 12.1): `T_A H (t,s) = ∫_s^t e^{πiA(u-s)} H(t,u,s) du` is bounded on the
open unit triangle in the weighted time-Fourier norm (`k`-supremum inside, as T's norm), uniformly in `A`. -/
def TerminalOperatorBound : Prop :=
  ∀ (d : ℕ) (θ : ℝ), 0 ≤ θ → θ ≤ 1 → ∃ C : ℝ, 0 ≤ C ∧
    ∀ (A : ℝ) (H : (Fin 3 → ℝ) → Mom d → ℂ) (K : Set (Mom d)),
      XNormRestr θ 0 0 {ts : Fin 2 → ℝ | 0 < ts 1 ∧ ts 1 < ts 0 ∧ ts 0 < 1} K
        (fun ts k => ∫ u in ts 1..ts 0,
          Complex.exp (((Real.pi * A * (u - ts 1) : ℝ) : ℂ) * Complex.I) * H ![ts 0, u, ts 1] k) ≤
      ENNReal.ofReal C * XNorm θ 0 0 H

end WaveTurbulence.Flower.ProtTa
