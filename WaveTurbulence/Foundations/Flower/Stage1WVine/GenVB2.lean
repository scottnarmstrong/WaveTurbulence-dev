/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Flower.Stage1WVine.GenVB1

/-! # STAGE1W-VINE (T3): VINE-B♯ with an arbitrary regional slot family — bounds and Fubini

Copy-generalization of `Vine/B/{Unit, Fiber1–6}` from the native kernels to an arbitrary slot family `Fs`, under the
abstract regional bound `RegBound` (a pointwise bound of the regional star product by a function `lb j` of the local
decoration, summable over the local decorations of every boundary datum, and measurability of `Fs` in the clocks).
For the native kernels `RegBound` is V5's `localBound` (`summable_tsum_localBound`); for the frontier-weighted kernels
it is `cψ`-powers times the same (row file `WRow*`).
-/

@[expose] public section
set_option autoImplicit false
open WaveTurbulence.Induct
open WaveTurbulence.VineParamContract
set_option linter.unusedSectionVars false
noncomputable section
namespace WaveTurbulence.Flower.Stage1WVine
open TTree WaveTurbulence WaveTurbulence.RegRed WaveTurbulence.RedSplice Finset WaveTurbulence.Represents
  WaveTurbulence.Reg.Skeleton WaveTurbulence.LGSpine WaveTurbulence.RegRedLeaf WaveTurbulence.VineEstS3.FS
  WaveTurbulence.VineEstS5C.Cont WaveTurbulence.VineEstS4 WaveTurbulence.VineEstS5C MeasureTheory
  WaveTurbulence.VineB

variable {w d : ℕ} {S : Garden w} {J : Type} [Fintype J] [DecidableEq J] {blk : J → CLBlock S} {Gsb : Garden w}

/-- **The abstract regional bound** of a slot family on the units `blk`. -/
structure RegBound (blk : J → CLBlock S) (hS : S.IsPlain) (Fs : ReplacementSlot S → (Fin 2 → ℝ) → Mom d → ℂ)
    (L : ℝ) (base : Mom d) where
  lb : J → (GNode S.tree → (Fin d → ℤ)) → ℝ
  lbC : J → ℝ
  nonneg : ∀ j x, 0 ≤ lb j x
  norm_le : ∀ j x top u, ‖starProdG hS Fs L base (blk j).atoms (blk j).upper top x u‖ ≤ lb j x
  summable : ∀ j (β : Fin 4 → Mom d), Summable fun κ : CLLocalDecoration (regionOf (blk j)) L base β =>
    lb j (clExtendIndices (regionOf (blk j)) κ.1)
  tsum_le : ∀ j (β : Fin 4 → Mom d), ∑' κ : CLLocalDecoration (regionOf (blk j)) L base β,
    lb j (clExtendIndices (regionOf (blk j)) κ.1) ≤ lbC j
  meas : ∀ j, RegMeas hS Fs L base (blk j).atoms (blk j).upper

section UnitBounds
variable {hS : S.IsPlain} {Fs : ReplacementSlot S → (Fin 2 → ℝ) → Mom d → ℂ} {L : ℝ} {base : Mom d}

end UnitBounds

section Fiber
variable (Φ : SpliceShape blk Gsb)

variable {hS : S.IsPlain} {Fs : ReplacementSlot S → (Fin 2 → ℝ) → Mom d → ℂ} {L : ℝ} {base : Mom d}

end Fiber

end WaveTurbulence.Flower.Stage1WVine
