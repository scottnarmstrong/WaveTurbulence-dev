/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.VineEst.VineEstS5C.Step3AtH
public import WaveTurbulence.Foundations.VineEst.VineEstS5C.LayerStatement
public import WaveTurbulence.Foundations.VineEst.VineEstS3.Step3Final
public import WaveTurbulence.Foundations.GammaLow.Famb.Family
public import WaveTurbulence.Foundations.VineEst.VineEstS5C.Step3FinalH
public import WaveTurbulence.Foundations.GammaLow.Famb.VineEstS5C.Step3AtH
-- L5b port of `WaveTurbulence.Foundations.VineEst.VineEstS5C.Step3FinalH` (sha256 22c49f8719cbdb1e…): its chain-dependent declarations only, over 𝒱_γ;
-- see GammaLow/Famb/PROGRESS.md (Design) and COPIED-SHA256SUMS.

/-! # The leaf-cost product of the rows is the region leaf size (Step 3 port, R45)

`prod_rowCostH_eq`: `∏ ρ rowCostH ρ = regionLeafSize` (the rows of the chain are in bijection with the regional pairs and
the interior branches); `step3BoundH_eq`: `step3BoundH = step3Bound * ofReal regionLeafSize`; `step3BoundH_le`: the literal
bound times `regionLeafSize`.
-/

@[expose] public section
variable {rowSelU : Unit} [rowSel : WaveTurbulence.VineEst.RowSel rowSelU]
set_option autoImplicit false
open WaveTurbulence.Induct
namespace WaveTurbulence.GammaLow.Famb.VineEstS5C
open WaveTurbulence.VineEstS5C WaveTurbulence.GammaLow.Famb.VineEstS5C
variable {γF : ℝ}
open WaveTurbulence WaveTurbulence.VineEstS2 WaveTurbulence.VineEstS3 WaveTurbulence.VineEstS3.Eng WaveTurbulence.GammaLow.Famb.VineEstS2 WaveTurbulence.GammaLow.Famb.VineEstS3
  WaveTurbulence.LGSpine VineParamContract TTree Reg Reg.Skeleton RegRed
open scoped ENNReal
variable {w : ℕ} {G : Garden w} {U : Finset (GBranch G.tree)} {a b : GBranch G.tree}
variable {R : CLRegionData G U a b} {n : ℕ}

theorem prod_rowCostH_eqΓ (hM9 : NormalChartSupply γF) (B : CLChainAssemblyΓ γF G R n) (RD : ReconstructionData G) (hG : G.IsPlain)
    (layer : GNode (RD.forest hG) → ℕ) (hLayer : IsLayering (RD.garden hG) layer) (Bh : ℕ → ℝ)
    {d : ℕ} (W : SumintWeightClockData (assemblyShapeΓ hM9 B) d) :
    ∏ ρ : Row (sourceSumintDatumΓ hM9 B hG W), rowCostHΓ hM9 B RD hG layer hLayer Bh W ρ =
      regionLeafSize RD hG R layer hLayer Bh := by
  classical
  have e1 : ∏ p ∈ clRegionalPairs hG U, ∏ ℓ ∈ inputLeaves (nativeCoupleLayered RD hG layer hLayer p).garden,
        Bh ((nativeCoupleLayered RD hG layer hLayer p).layer ℓ.toNode) =
      ∏ v : (assemblyShapeΓ hM9 B).VIdx, layerCost Bh (rowCoupleLGΓ hM9 B RD hG layer hLayer v) := by
    rw [← Finset.prod_coe_sort]
    exact (Equiv.prod_comp ((assemblyRowEquivΓ hM9 B).symm.trans (assemblyPairOrderΓ hG B hM9).symm)
      (fun p : ↥(clRegionalPairs hG U) => ∏ ℓ ∈ inputLeaves (nativeCoupleLayered RD hG layer hLayer p.1).garden,
        Bh ((nativeCoupleLayered RD hG layer hLayer p.1).layer ℓ.toNode))).symm
  have e2 : ∏ v ∈ clInteriorBranches R, ∏ ℓ ∈ inputLeaves (nativeChainLayered RD hG layer hLayer v).garden,
        Bh ((nativeChainLayered RD hG layer hLayer v).layer ℓ.toNode) =
      ∏ v : (assemblyShapeΓ hM9 B).VIdx, layerCost Bh (rowTreeLGΓ hM9 B RD hG layer hLayer v) := by
    rw [← Finset.prod_coe_sort]
    exact (Equiv.prod_comp ((assemblyRowEquivΓ hM9 B).symm.trans (assemblyIntOrderΓ hM9 B).e.symm)
      (fun z : ↥(clInteriorBranches R) => ∏ ℓ ∈ inputLeaves (nativeChainLayered RD hG layer hLayer z.1).garden,
        Bh ((nativeChainLayered RD hG layer hLayer z.1).layer ℓ.toNode))).symm
  unfold Row
  rw [Fintype.prod_sum_type]
  unfold regionLeafSize
  rw [e1, e2]
  rfl

theorem regionLeafSize_nonnegΓ {P : WTParams} {h : ℕ → Mom P.d → ℝ} {Bh : ℕ → ℝ} {p : ℕ}
    (hB : ProfileBound P h Bh p) (hM9 : NormalChartSupply γF) (B : CLChainAssemblyΓ γF G R n) (RD : ReconstructionData G)
    (hG : G.IsPlain) (layer : GNode (RD.forest hG) → ℕ) (hLayer : IsLayering (RD.garden hG) layer)
    (hlay : ∀ x, layer x ≤ p) (W : SumintWeightClockData (assemblyShapeΓ hM9 B) P.d) :
    0 ≤ regionLeafSize RD hG R layer hLayer Bh := by
  rw [← prod_rowCostH_eqΓ hM9 B RD hG layer hLayer Bh W]
  exact Finset.prod_nonneg fun ρ _ => rowCostH_nonnegΓ (hLayer := hLayer) hB hlay W ρ

end WaveTurbulence.GammaLow.Famb.VineEstS5C
