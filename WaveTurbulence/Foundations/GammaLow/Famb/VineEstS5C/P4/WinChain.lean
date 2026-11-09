/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.VineEst.VineEstS5C.P4.UnrollR
public import WaveTurbulence.Foundations.VineEst.VineEstS5C.P4.NullSet
public import WaveTurbulence.Foundations.VineEst.VineEstS5C.LevelTop
public import WaveTurbulence.Foundations.GammaLow.Famb.Family
public import WaveTurbulence.Foundations.VineEst.VineEstS5C.P4.WinChain
public import WaveTurbulence.Foundations.GammaLow.Famb.VineEstS5C.LevelTop
public import WaveTurbulence.Foundations.GammaLow.Famb.VineEstS5C.P4.UnrollR
-- L5b port of `WaveTurbulence.Foundations.VineEst.VineEstS5C.P4.WinChain` (sha256 8c25689755cee374…): its chain-dependent declarations only, over 𝒱_γ;
-- see GammaLow/Famb/PROGRESS.md (Design) and COPIED-SHA256SUMS.

/-! # P4: the exterior window at the top level, and the boundary of the clock box (V5 Step 4d part C)

The top level `Lvl.top` has the region of `U`, whose top joint is `a`; its layer is `layer (core a) = qOut 0`.  On the closed box of the
exterior clocks, `tt 0 ∈ [qOut 0, qOut 0 + 1]`; the strict window `ExtOf` of design R holds off the two hyperplanes `tt 0 = qOut 0`,
`tt 0 = qOut 0 + 1`, which are null, and `XNorm00Restr` does not see null sets of times (`XNorm00Restr_le_of_null`).

* `XNorm00Restr_mono_set`: monotonicity in the time set.
* `layOf_top`: the layer of the top joint at the top level is `layer (core a)`.
* **`top_boundR`**, **`top_boundR_prod`**: the recentered class sum of the top level on any box `Bx` whose exterior clock lies in the
  closed window `[layer (core a), layer (core a) + 1]` obeys the finite-Minkowski bound `(cc + 1) (#terms β)` (resp. with the per-vine
  count `∏ wt`), from term bounds `TermBoundR` on `Bx`.
* `kparOf`, `twistedRecentered_eq_clsFnR`: the integrand of `VineEstCanonLayer` is `clsFnR` of the top level.
-/

@[expose] public section
variable {rowSelU : Unit} [rowSel : WaveTurbulence.VineEst.RowSel rowSelU]
set_option autoImplicit false
open WaveTurbulence.VineParamContract
namespace WaveTurbulence.GammaLow.Famb.VineEstS5C.P4
open WaveTurbulence.VineEstS5C WaveTurbulence.VineEstS5C.P4 WaveTurbulence.GammaLow.Famb.VineEstS5C WaveTurbulence.GammaLow.Famb.VineEstS5C.P4
variable {γF : ℝ}
variable {kind : Bool}
open WaveTurbulence WaveTurbulence.Fourier WaveTurbulence.VineEstS3.FS WaveTurbulence.Twist WaveTurbulence.LFTwist
  WaveTurbulence.VineEstS2 WaveTurbulence.VineEstS3 WaveTurbulence.VineEstS4 WaveTurbulence.VineEstS5B WaveTurbulence.Links
  WaveTurbulence.Reg.Skeleton WaveTurbulence.RegRed TTree MeasureTheory WaveTurbulence.GammaLow.Famb.VineEstS2 WaveTurbulence.GammaLow.Famb.VineEstS3 WaveTurbulence.GammaLow.Famb.VineEstS4
open WaveTurbulence.VineEstS5C WaveTurbulence.VineEstS5C.P3 WaveTurbulence.VineEstS5C.P2 WaveTurbulence.GammaLow.Famb.VineEstS5C WaveTurbulence.GammaLow.Famb.VineEstS5C.P3 WaveTurbulence.GammaLow.Famb.VineEstS5C.P2
open scoped ENNReal

set_option linter.unusedSectionVars false

variable {w : ℕ} {G : Garden w} {U : Finset (GBranch G.tree)} {a b : GBranch G.tree} {R : CLRegionData G U a b} {n : ℕ}
  {d : ℕ} {p : ℕ}
variable (B : CLChainAssemblyΓ γF G R n) (RD : ReconstructionData G) (hG : G.IsPlain)
  (layer : GNode (RD.forest hG) → ℕ) (hLayer : IsLayering (RD.garden hG) layer)

theorem stateLayer_startStateΓ : stateLayer (startStateΓ B RD hG layer hLayer) = layer :=
  layeredReconstruction_inj RD hG (l₁ := stateLayer (startStateΓ B RD hG layer hLayer)) (l₂ := layer)
    (h₁ := stateLayer_isLayering (startStateΓ B RD hG layer hLayer)) (h₂ := hLayer) (stateLayer_spec (startStateΓ B RD hG layer hLayer))

/-- The layer of the top joint of the top level is the layer of the core of `a` (`= qOut 0`). -/
theorem layOf_topΓ : layOf ((LvlΓ.top B).state B RD hG layer hLayer) (LvlΓ.top B).c.a = layer (RD.coreBranch hG a).toNode := by
  show stateLayer (startStateΓ B RD hG layer hLayer) (RD.coreBranch hG a).toNode = _
  rw [stateLayer_startStateΓ]

variable {κ0 : KPar d} {hprime : IsPrimeGarden G}
variable (BE : BundleExpFamΓ (p := p) (kind := kind) B RD hG layer hLayer κ0 hprime)

end WaveTurbulence.GammaLow.Famb.VineEstS5C.P4
