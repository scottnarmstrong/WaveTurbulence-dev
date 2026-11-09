/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.VineEst.VineEstS5C.Cont.Member
public import WaveTurbulence.Foundations.VineEst.VineEstS4.Canon
public import WaveTurbulence.Foundations.VineEst.VineEstS4.Statement
public import WaveTurbulence.Foundations.GammaLow.Famb.Family
public import WaveTurbulence.Foundations.VineEst.VineEstS5C.Cont.Class
public import WaveTurbulence.Foundations.GammaLow.Famb.VineEstS4.RowSum
public import WaveTurbulence.Foundations.GammaLow.Famb.VineEstS5C.Step3AtH
public import WaveTurbulence.Foundations.GammaLow.Famb.VineEstS4.RowReach
-- L5b port of `WaveTurbulence.Foundations.VineEst.VineEstS5C.Cont.Class` (sha256 a1fbc47d48d41518…): its chain-dependent declarations only, over 𝒱_γ;
-- see GammaLow/Famb/PROGRESS.md (Design) and COPIED-SHA256SUMS.

/-! # V5-CONT, the class kernel: `twistedRecentered` is continuous in the three clocks

`recentered_class_sum`: for a finite set `Z` of members each reached from `(A, c)` by a batch, `twistedRecentered G a Z` is the
sum of the recentered kernels `clRecenteredLocalKernel` of the members (all at the boundary `sumintBoundary` of the START sign).
`twistedRecentered_continuousOn`: for the canonical class `canonFinsetK p kind (startState B RD hG layer hLayer) (chainStart B)`
(the only place where `kind = true` enters: `mem_canonFinset`; every other step is `member_continuousOn`, generic in `kind`),
`twistedRecentered` is continuous on `cubeSet (step3D …).qOut` for every `E` of `outSet (step3D …)`.
-/

@[expose] public section
variable {rowSelU : Unit} [rowSel : WaveTurbulence.VineEst.RowSel rowSelU]
set_option autoImplicit false
open WaveTurbulence.Induct
open WaveTurbulence.VineParamContract
namespace WaveTurbulence.GammaLow.Famb.VineEstS5C.Cont
open WaveTurbulence.VineEstS5C WaveTurbulence.VineEstS5C.Cont
variable {γF : ℝ}
variable {kind : Bool}
open WaveTurbulence WaveTurbulence.VineEstS2 WaveTurbulence.VineEstS3 WaveTurbulence.VineEstS3.Eng WaveTurbulence.VineEstS4 WaveTurbulence.GammaLow.Famb.VineEstS2 WaveTurbulence.GammaLow.Famb.VineEstS3 WaveTurbulence.GammaLow.Famb.VineEstS4
  WaveTurbulence.Twist WaveTurbulence.LFTwist WaveTurbulence.LGSpine VineParamContract TTree Reg Reg.Skeleton RegRed
  MeasureTheory
open scoped ENNReal

variable {w : ℕ} {ι : Type*}

/-- The layering of the start state is the given layering (copy of `P4.stateLayer_startState`, without the P4 import). -/
theorem stateLayer_startΓ {G : Garden w} {U : Finset (GBranch G.tree)} {a b : GBranch G.tree} {R : CLRegionData G U a b}
    {n : ℕ} (B : CLChainAssemblyΓ γF G R n) (RD : ReconstructionData G) (hG : G.IsPlain)
    (layer : GNode (RD.forest hG) → ℕ) (hLayer : IsLayering (RD.garden hG) layer) :
    stateLayer (startStateΓ B RD hG layer hLayer) = layer :=
  layeredReconstruction_inj RD hG (l₁ := stateLayer (startStateΓ B RD hG layer hLayer)) (l₂ := layer)
    (h₁ := stateLayer_isLayering (startStateΓ B RD hG layer hLayer)) (h₂ := hLayer)
    (stateLayer_spec (startStateΓ B RD hG layer hLayer))

end WaveTurbulence.GammaLow.Famb.VineEstS5C.Cont
