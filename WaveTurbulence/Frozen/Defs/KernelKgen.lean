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
public import WaveTurbulence.Frozen.Defs.GardenExtendFix
public import WaveTurbulence.Frozen.Defs.GardenIsFlower
public import WaveTurbulence.Frozen.Defs.GardenOrder
public import WaveTurbulence.Frozen.Defs.GardenZeta
public import WaveTurbulence.Frozen.Defs.GenDecoration
public import WaveTurbulence.Frozen.Defs.InputLeaves
public import WaveTurbulence.Frozen.Defs.InstFintypeGBranch
public import WaveTurbulence.Frozen.Defs.IsDecoration
public import WaveTurbulence.Frozen.Defs.KDomainFix
public import WaveTurbulence.Frozen.Defs.LayeredGarden
public import WaveTurbulence.Frozen.Defs.Mom
public import WaveTurbulence.Frozen.Defs.PhaseProdOff

/-!
# kernelKgen

Wave B tier B1 (WaveB1-Flower.lean), source: (file) T L2327; T L2283–L2285; T L2331. Frozen by ruling D7
(`docs/DECISIONS.md#D7`); do not edit.
-/

@[expose] public section

open MeasureTheory Finset Set
open scoped ENNReal

namespace WaveTurbulence

section General

variable {w : ℕ}
variable (L γ δ : ℝ) {d : ℕ}

/-- **The general kernel** (R8): `kernelK` with designated fixed-time nodes `fix`, removed phases `off`
and a decoration weight `wt`:
`(δ/(2L^{d-γ}))^n ζ(𝒢) ∑_κ ε_κ wt(k) ∫ 1_{kDomainFix} ∏_{𝔫∉off} e^{πiζ_𝔫δL^{2γ}Ω_𝔫t_𝔫}
∏^{(+,unmarked)}_ℓ F_{𝔏_ℓ}(k_ℓ)`. The integral runs over the free times. -/
noncomputable def kernelKgen (F : ℕ → Mom d → ℝ) (LG : LayeredGarden w)
    (fix : GBranch LG.garden.tree → Option ℝ) (off : Finset (GBranch LG.garden.tree))
    (wt : (GNode LG.garden.tree → Mom d) → ℝ) (up : GBranch LG.garden.tree → ℝ) (k₀ : Mom d)
    (nroot : Fin w → (Fin d → ℤ)) (nfl : Fin d → ℤ) : ℂ :=
  (coupling d L γ δ : ℂ) ^ LG.garden.order * LG.garden.zeta *
    ∑' κ : GenDecoration LG.garden d nroot nfl,
      (epsDec LG.garden κ.1 : ℂ) * (wt (cosetDecoration LG.garden L k₀ κ.1) : ℂ) *
        (∫ τ : {b : GBranch LG.garden.tree // fix b = none} → ℝ,
          (kDomainFix LG up fix).indicator
            (phaseProdOff L γ δ LG.garden off (cosetDecoration LG.garden L k₀ κ.1))
            (LG.garden.extendFix fix τ)) *
        ∏ ℓ ∈ inputLeaves LG.garden,
          (F (LG.layer ℓ.toNode) (cosetDecoration LG.garden L k₀ κ.1 ℓ.toNode) : ℂ)

end General
end WaveTurbulence
