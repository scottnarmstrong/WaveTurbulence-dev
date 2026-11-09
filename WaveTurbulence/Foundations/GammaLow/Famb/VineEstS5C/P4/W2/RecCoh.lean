/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.VineEst.VineEstS3.IncohDict
public import WaveTurbulence.Foundations.GammaLow.Famb.Family
public import WaveTurbulence.Foundations.VineEst.VineEstS5C.P4.W2.RecCoh
public import WaveTurbulence.Foundations.GammaLow.Famb.VineEstS3.IncohDict
-- L5b port of `WaveTurbulence.Foundations.VineEst.VineEstS5C.P4.W2.RecCoh` (sha256 574d1942b57a4f45…): its chain-dependent declarations only, over 𝒱_γ;
-- see GammaLow/Famb/PROGRESS.md (Design) and COPIED-SHA256SUMS.

/-! # P4-W2 (session 15, step 1): the converse of the incoherency dictionary

`tree_incoherency_zero_of_cohOn`, `couple_incoherency_zero_of_cohOn`: if the source tree / couple at the inflated position is
`CohOn` in the big layered garden, then the native incoherency index is `0` (the converses of
`VineEstS3.tree_cohOn_of_incoherency_zero` / `couple_cohOn_of_incoherency_zero`; the same proof read in the other direction).
`rowTreeG_eq_zero_of_cohOn`, `rowCoupleG_eq_zero_of_cohOn`: the row-level statements.
-/

@[expose] public section
variable {rowSelU : Unit} [rowSel : WaveTurbulence.VineEst.RowSel rowSelU]
set_option autoImplicit false
open WaveTurbulence.Induct
namespace WaveTurbulence.GammaLow.Famb.VineEstS5C.P4.W2
open WaveTurbulence.VineEstS5C WaveTurbulence.VineEstS5C.P4 WaveTurbulence.VineEstS5C.P4.W2
variable {γF : ℝ}
open WaveTurbulence WaveTurbulence.VineEstS2 WaveTurbulence.LGSpine VineParamContract TTree Reg Reg.Skeleton RegRed WaveTurbulence.GammaLow.Famb.VineEstS2
  WaveTurbulence.Links WaveTurbulence.VineEstS3 WaveTurbulence.GammaLow.Famb.VineEstS3

section
variable {w : ℕ} {S : Garden w} (D : ReconstructionData S) (hS : S.IsPlain) (layer : GNode (D.forest hS) → ℕ)
  (hLayer : IsLayering (D.garden hS) layer)

end

section Rows
variable {w : ℕ} {G : Garden w} {U : Finset (GBranch G.tree)} {a b : GBranch G.tree}
  {R : CLRegionData G U a b} {n : ℕ} (hM9 : NormalChartSupply γF) (B : CLChainAssemblyΓ γF G R n) (RD : ReconstructionData G)
  (hG : G.IsPlain) (layer : GNode (RD.forest hG) → ℕ) (hLayer : IsLayering (RD.garden hG) layer)

/-- A `CohOn` source tree at the branch carried by row `v` gives `g' = 0` of the row. -/
theorem rowTreeG_eq_zero_of_cohOnΓ (v : (assemblyShapeΓ hM9 B).VIdx)
    (h : CohOn (layeredReconstruction RD hG layer hLayer)
      ((RD.tree (assemblyBranchOfΓ hM9 B v).1).linksAt (nodeSign G.sig (assemblyBranchOfΓ hM9 B v).1.1)
        (inflatedPosition G RD.tree (assemblyBranchOfΓ hM9 B v).1.toNode))) :
    rowTreeGΓ hM9 B RD hG layer hLayer v = 0 :=
  tree_incoherency_zero_of_cohOn RD hG layer hLayer _ h

/-- A `CohOn` source couple at the pair carried by row `v` gives `g = 0` of the row. -/
theorem rowCoupleG_eq_zero_of_cohOnΓ (v : (assemblyShapeΓ hM9 B).VIdx)
    (h : CohOn (layeredReconstruction RD hG layer hLayer)
      ((RD.couple (assemblyPairOfΓ hM9 B hG v).1).linksAt
        (inflatedPosition G RD.tree ((assemblyPairOfΓ hM9 B hG v).1.firstLeaf hG).toNode)
        (inflatedPosition G RD.tree ((assemblyPairOfΓ hM9 B hG v).1.secondLeaf hG).toNode))) :
    rowCoupleGΓ hM9 B RD hG layer hLayer v = 0 :=
  couple_incoherency_zero_of_cohOn RD hG layer hLayer _ h
end Rows

end WaveTurbulence.GammaLow.Famb.VineEstS5C.P4.W2
