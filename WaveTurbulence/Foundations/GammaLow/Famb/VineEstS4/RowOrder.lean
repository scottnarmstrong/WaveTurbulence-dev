/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.VineEst.VineEstS4.Statement
public import WaveTurbulence.Foundations.GammaLow.Famb.Family
public import WaveTurbulence.Foundations.VineEst.VineEstS4.RowOrder
public import WaveTurbulence.Foundations.GammaLow.Famb.VineEstS3.BadClause
public import WaveTurbulence.Foundations.GammaLow.Famb.VineEstS3.Step3Final
public import WaveTurbulence.Foundations.GammaLow.Famb.VineEstS4.Class
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
open WaveTurbulence.VineEstS4 WaveTurbulence.GammaLow.Famb.VineEstS4
variable {γF : ℝ}
open WaveTurbulence WaveTurbulence.VineEstS2 WaveTurbulence.VineEstS3 WaveTurbulence.VineEstS3.Eng WaveTurbulence.GammaLow.Famb.VineEstS2 WaveTurbulence.GammaLow.Famb.VineEstS3
  WaveTurbulence.Twist WaveTurbulence.LFTwist WaveTurbulence.RegRed WaveTurbulence.Reg.Skeleton
  VineParamContract TTree

variable {w : ℕ} {G : Garden w} {U : Finset (GBranch G.tree)} {a b : GBranch G.tree}
variable {R : CLRegionData G U a b} {n : ℕ}

/-- Every replacement of a reconstruction has order at most the total replacement order. -/
theorem rowSizes_of_dataSizeΓ (hM9 : NormalChartSupply γF) (B : CLChainAssemblyΓ γF G R n) (RD : ReconstructionData G)
    (hG : G.IsPlain) {Nb : ℕ} (h : RD.size ≤ Nb) : RowSizesΓ hM9 B RD hG Nb := by
  intro v
  constructor
  · have : (rowCoupleΓ hM9 B RD hG v).size ≤ RD.size := by
      unfold ReconstructionData.size
      exact le_trans (Finset.single_le_sum (f := fun p => (RD.couple p).size) (fun _ _ => Nat.zero_le _)
        (Finset.mem_univ _)) (Nat.le_add_left _ _)
    omega
  · have : (rowTreeΓ hM9 B RD v).size ≤ RD.size := by
      unfold ReconstructionData.size
      exact le_trans (Finset.single_le_sum (f := fun b => (RD.tree b).size) (fun _ _ => Nat.zero_le _)
        (Finset.mem_univ _)) (Nat.le_add_right _ _)
    omega

/-- **Garden-order bound gives the row sizes.** -/
theorem rowSizes_of_orderΓ (hM9 : NormalChartSupply γF) (B : CLChainAssemblyΓ γF G R n) (RD : ReconstructionData G)
    (hG : G.IsPlain) {Nb : ℕ} (h : (RD.garden hG).order ≤ Nb) : RowSizesΓ hM9 B RD hG Nb := by
  apply rowSizes_of_dataSizeΓ
  have := RD.decoded_order hG (RD.garden_decodes hG)
  omega

end WaveTurbulence.GammaLow.Famb.VineEstS4
