/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.VineEst.VineEstS4.Statement
public import WaveTurbulence.Foundations.GammaLow.Famb.Family
public import WaveTurbulence.Foundations.VineEst.VineEstS4.RowOrder
public import WaveTurbulence.Foundations.GammaLow.Famb.VineEstS4.RowOrder
public import WaveTurbulence.Foundations.GammaLow.Famb.VineEstS3.LeafChild
public import WaveTurbulence.Foundations.GammaLow.Famb.VineEstS3.LeafWire
-- L5b port of `WaveTurbulence.Foundations.VineEst.VineEstS4.RowOrder` (sha256 d2995a9acfe91de5…): its chain-dependent declarations only, over 𝒱_γ;
-- see GammaLow/Famb/PROGRESS.md (Design) and COPIED-SHA256SUMS.

/-! # The standing garden-order bound and the row sizes (V5 Step 4b, ruling on RowSizes)

TARGET's standing bound is on the total garden order `n ≤ N_{p+1}^4` (L806-L810).  Every regular object of a row is
a sub-object of the garden, so its order is at most the garden order: `rowSizes_of_order`.  The LF twists preserve the
total order (`FamilyBatch.order`), hence every member garden of the class satisfies the same bound and its rows
the same `RowSizes` (`Reach.rowSizes`).
-/

@[expose] public section
variable {rowSelU : Unit} [rowSel : WaveTurbulence.VineEst.RowSel rowSelU]
set_option autoImplicit false
open WaveTurbulence.VineParamContract
namespace WaveTurbulence.GammaLow.Famb.VineEstS4
open WaveTurbulence.VineEstS4
variable {γF : ℝ}
open WaveTurbulence WaveTurbulence.VineEstS2 WaveTurbulence.VineEstS3 WaveTurbulence.VineEstS3.Eng WaveTurbulence.GammaLow.Famb.VineEstS2 WaveTurbulence.GammaLow.Famb.VineEstS3
  WaveTurbulence.Twist WaveTurbulence.LFTwist WaveTurbulence.RegRed WaveTurbulence.Reg.Skeleton
  VineParamContract TTree

variable {w : ℕ} {G : Garden w} {U : Finset (GBranch G.tree)} {a b : GBranch G.tree}
variable {R : CLRegionData G U a b} {n : ℕ}

/-- Row sizes of any reconstruction state of bounded garden order, in particular of every member garden of the
twist class (its assembly `B1` from `Reach.exists_asm`). -/
theorem rowSizes_of_stateΓ {ι : Type*} (hM9 : NormalChartSupply γF) (Bs : FamilyReconstruction w ι)
    {U' : Finset (GBranch Bs.skeleton.tree)} {a' b' : GBranch Bs.skeleton.tree}
    {R' : CLRegionData Bs.skeleton U' a' b'} (B' : CLChainAssemblyΓ γF Bs.skeleton R' n) {Nb : ℕ}
    (h : Bs.layered.garden.order ≤ Nb) :
    RowSizesΓ hM9 B' Bs.data Bs.plain Nb := by
  apply rowSizes_of_dataSizeΓ
  have := Bs.data.decoded_order Bs.plain Bs.decodes
  omega

end WaveTurbulence.GammaLow.Famb.VineEstS4
