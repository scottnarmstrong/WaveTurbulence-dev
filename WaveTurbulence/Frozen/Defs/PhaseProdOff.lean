/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Mathlib
public import WaveTurbulence.Frozen.Defs.GBranch
public import WaveTurbulence.Frozen.Defs.GBranchToNode
public import WaveTurbulence.Frozen.Defs.GNode
public import WaveTurbulence.Frozen.Defs.Garden
public import WaveTurbulence.Frozen.Defs.GardenSign
public import WaveTurbulence.Frozen.Defs.InstDecidableEqGBranch
public import WaveTurbulence.Frozen.Defs.InstFintypeGBranch
public import WaveTurbulence.Frozen.Defs.Mom
public import WaveTurbulence.Frozen.Defs.OmegaNode

/-!
# phaseProdOff

Wave B tier B1 (WaveB1-Flower.lean), source: T L2327. Frozen by ruling D7
(`docs/DECISIONS.md#D7`); do not edit.
-/

@[expose] public section

open MeasureTheory Finset Set
open scoped ENNReal

namespace WaveTurbulence

section General

variable {w : ℕ}
variable (L γ δ : ℝ) {d : ℕ}

/-- The phase product with the phases at the nodes of `off` removed (`𝒥^†`, T L2327). -/
noncomputable def phaseProdOff (G : Garden w) (off : Finset (GBranch G.tree))
    (k : GNode G.tree → Mom d) (τ : GBranch G.tree → ℝ) : ℂ :=
  ∏ b : GBranch G.tree, if b ∈ off then 1 else
    Complex.exp ((Real.pi * ((G.sign b.toNode : ℤˣ) : ℤ) * δ * L ^ (2 * γ) * omegaNode G k b * τ b : ℝ) *
      Complex.I)

end General
end WaveTurbulence
