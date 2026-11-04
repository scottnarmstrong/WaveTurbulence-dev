/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Mathlib
public import WaveTurbulence.Frozen.Defs.GBranch
public import WaveTurbulence.Frozen.Defs.GNode
public import WaveTurbulence.Frozen.Defs.Garden
public import WaveTurbulence.Frozen.Defs.GardenExtendTime
public import WaveTurbulence.Frozen.Defs.GardenFreeBranch
public import WaveTurbulence.Frozen.Defs.InstFintypeFreeBranch
public import WaveTurbulence.Frozen.Defs.Mom
public import WaveTurbulence.Frozen.Defs.PhaseProd

/-!
# phaseIntegral

Wave B tier B1 (WaveB1-System.lean), source: (file) WAVE-B §2.3; T L545–L564; T Def `defcm`. Frozen by ruling D7
(`docs/DECISIONS.md#D7`); do not edit.
-/

@[expose] public section

open MeasureTheory Finset Set
open scoped ENNReal

namespace WaveTurbulence

section Kernels

variable {w : ℕ}
variable (L γ δ : ℝ) {d : ℕ}

/-- The **phase integral** `∫_D ∏ e^{πi ζ_𝔫 δ L^{2γ} Ω_𝔫 t_𝔫} dt` over a time domain
`D ⊆ ℝ^{𝒩}`, integrating the free nodes and setting the flower parents to `s` (without flowers an
ordinary integral over `ℝ^{𝒩}`). -/
noncomputable def phaseIntegral (G : Garden w) (D : Set (GBranch G.tree → ℝ)) (s : ℝ)
    (k : GNode G.tree → Mom d) : ℂ :=
  ∫ τ : G.FreeBranch → ℝ, D.indicator (phaseProd L γ δ G k) (G.extendTime s τ)

end Kernels
end WaveTurbulence
