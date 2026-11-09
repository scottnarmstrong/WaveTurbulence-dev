/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.VineEst.VineEstS3.NativeRows
public import WaveTurbulence.Foundations.Molecule.LFTwist.LFSource
public import WaveTurbulence.Foundations.Molecule.LFTwist.LinkNaturality
public import WaveTurbulence.Foundations.GammaLow.Famb.Family
public import WaveTurbulence.Foundations.VineEst.VineEstS3.IncohDict
public import WaveTurbulence.Foundations.GammaLow.Famb.VineEstS3.NativeRows
-- L5b port of `WaveTurbulence.Foundations.VineEst.VineEstS3.IncohDict` (sha256 35d870961ea6197d…): its chain-dependent declarations only, over 𝒱_γ;
-- see GammaLow/Famb/PROGRESS.md (Design) and COPIED-SHA256SUMS.

/-! # The incoherency dictionary (R22 (4))

The incoherency index `rowTreeG` / `rowCoupleG` of a native row (a `LayeredGarden.incoherency` of the layered native
tree/couple) vanishes only if the object is coherent in the sense of `Links.CohOn` for the big layered garden
(`layeredReconstruction`) at the inflated position -- the form of `LFSource.treeCoherent` / `coupleCoherent`.
Hence `¬ CohOn ⟹ 1 ≤ g` (`one_le_rowTreeG_of_not_cohOn`, `one_le_rowCoupleG_of_not_cohOn`).
-/

@[expose] public section
variable {rowSelU : Unit} [rowSel : WaveTurbulence.VineEst.RowSel rowSelU]
set_option autoImplicit false
open WaveTurbulence.Induct
open WaveTurbulence.VineParamContract
namespace WaveTurbulence.GammaLow.Famb.VineEstS3
open WaveTurbulence.VineEstS3 WaveTurbulence.GammaLow.Famb.VineEstS3
variable {γF : ℝ}
open WaveTurbulence WaveTurbulence.VineEstS2 WaveTurbulence.LGSpine VineParamContract TTree Reg Reg.Skeleton RegRed WaveTurbulence.GammaLow.Famb.VineEstS2
  WaveTurbulence.Links

section
variable {w : ℕ} {S : Garden w} (D : ReconstructionData S) (hS : S.IsPlain) (layer : GNode (D.forest hS) → ℕ)
  (hLayer : IsLayering (D.garden hS) layer)

end

section Rows
variable {w : ℕ} {G : Garden w} {U : Finset (GBranch G.tree)} {a b : GBranch G.tree}
  {R : CLRegionData G U a b} {n : ℕ} (hM9 : NormalChartSupply γF) (B : CLChainAssemblyΓ γF G R n) (RD : ReconstructionData G)
  (hG : G.IsPlain) (layer : GNode (RD.forest hG) → ℕ) (hLayer : IsLayering (RD.garden hG) layer)

/-- A non-coherent source tree at the branch carried by row `v` forces `1 ≤ g'` of the row. -/
theorem one_le_rowTreeG_of_not_cohOnΓ (v : (assemblyShapeΓ hM9 B).VIdx)
    (h : ¬ CohOn (layeredReconstruction RD hG layer hLayer)
      ((RD.tree (assemblyBranchOfΓ hM9 B v).1).linksAt (nodeSign G.sig (assemblyBranchOfΓ hM9 B v).1.1)
        (inflatedPosition G RD.tree (assemblyBranchOfΓ hM9 B v).1.toNode))) :
    1 ≤ rowTreeGΓ hM9 B RD hG layer hLayer v :=
  Nat.pos_of_ne_zero fun h0 => h (tree_cohOn_of_incoherency_zero RD hG layer hLayer _ h0)

/-- A non-coherent source couple at the pair carried by row `v` forces `1 ≤ g` of the row. -/
theorem one_le_rowCoupleG_of_not_cohOnΓ (v : (assemblyShapeΓ hM9 B).VIdx)
    (h : ¬ CohOn (layeredReconstruction RD hG layer hLayer)
      ((RD.couple (assemblyPairOfΓ hM9 B hG v).1).linksAt
        (inflatedPosition G RD.tree ((assemblyPairOfΓ hM9 B hG v).1.firstLeaf hG).toNode)
        (inflatedPosition G RD.tree ((assemblyPairOfΓ hM9 B hG v).1.secondLeaf hG).toNode))) :
    1 ≤ rowCoupleGΓ hM9 B RD hG layer hLayer v :=
  Nat.pos_of_ne_zero fun h0 => h (couple_cohOn_of_incoherency_zero RD hG layer hLayer _ h0)

end Rows

end WaveTurbulence.GammaLow.Famb.VineEstS3
