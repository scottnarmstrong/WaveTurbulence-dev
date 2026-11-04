/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Mathlib
public import WaveTurbulence.Frozen.Defs.CosetDecoration
public import WaveTurbulence.Frozen.Defs.Coupling
public import WaveTurbulence.Frozen.Defs.EpsDec
public import WaveTurbulence.Frozen.Defs.GBranch
public import WaveTurbulence.Frozen.Defs.GLeaf
public import WaveTurbulence.Frozen.Defs.GLeafToNode
public import WaveTurbulence.Frozen.Defs.GNode
public import WaveTurbulence.Frozen.Defs.GNodeRoot
public import WaveTurbulence.Frozen.Defs.Garden
public import WaveTurbulence.Frozen.Defs.GardenIsFlower
public import WaveTurbulence.Frozen.Defs.GardenOrder
public import WaveTurbulence.Frozen.Defs.GardenZeta
public import WaveTurbulence.Frozen.Defs.GenDecoration
public import WaveTurbulence.Frozen.Defs.InputLeaves
public import WaveTurbulence.Frozen.Defs.IsDecoration
public import WaveTurbulence.Frozen.Defs.KDomain
public import WaveTurbulence.Frozen.Defs.LayeredGarden
public import WaveTurbulence.Frozen.Defs.Mom
public import WaveTurbulence.Frozen.Defs.PhaseIntegral

/-!
# kernelK

Wave B tier B1 (WaveB1-System.lean), source: WAVE-B v2 §2.4.1; T Def `defkg`. Frozen by ruling D7
(`docs/DECISIONS.md#D7`); do not edit.
-/

@[expose] public section

open MeasureTheory Finset Set
open scoped ENNReal

namespace WaveTurbulence

section Kernels

variable {w : ℕ}
variable (L γ δ : ℝ) {d : ℕ}

/-- **The one kernel** (WAVE-B v2 §2.4.1; T Def `defkg`, (defkg0), (timecouple), (timepairtree),
(kqflower)): for a layered garden with marked leaves, inputs `F_q`, node upper times `up`, the time
`s` (flower parents fixed to `s`, lone-leaf parents `> s`), a base vector `k₀` (vectors
`k_𝔫 = k₀ + κ_𝔫/L`), root labels `n_j` and flower label `n'`:
`(δ/(2L^{d-γ}))^n ζ(𝒢) ∑_κ ε_κ ∫ ∏ e^{πiζ_𝔫 δL^{2γ}Ω_𝔫 t_𝔫} dt ∏^{(+, unmarked)}_ℓ F_{𝔏_ℓ}(k_ℓ)`.
The `tsum` converges absolutely when every tree has at most one lone-marked leaf (all TARGET
carriers) and the inputs have summable lattice values (`summable_kernelK_summand`, T.defkg.sum). On
gardens with two or more lone leaves in one tree (not TARGET objects) the decorations have a free
direction and the `tsum` is the junk value `0` (stage-2 audit R2, O7). -/
noncomputable def kernelK (F : ℕ → Mom d → ℝ) (LG : LayeredGarden w)
    (up : GBranch LG.garden.tree → ℝ) (s : ℝ) (k₀ : Mom d) (nroot : Fin w → (Fin d → ℤ))
    (nfl : Fin d → ℤ) : ℂ :=
  (coupling d L γ δ : ℂ) ^ LG.garden.order * LG.garden.zeta *
    ∑' κ : GenDecoration LG.garden d nroot nfl,
      (epsDec LG.garden κ.1 : ℂ) *
        phaseIntegral L γ δ LG.garden (kDomain LG up s) s (cosetDecoration LG.garden L k₀ κ.1) *
        ∏ ℓ ∈ inputLeaves LG.garden,
          (F (LG.layer ℓ.toNode) (cosetDecoration LG.garden L k₀ κ.1 ℓ.toNode) : ℂ)

end Kernels
end WaveTurbulence
