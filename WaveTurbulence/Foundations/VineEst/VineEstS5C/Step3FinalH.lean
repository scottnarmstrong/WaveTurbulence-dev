/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.VineEst.VineEstS5C.Step3AtH
public import WaveTurbulence.Foundations.VineEst.VineEstS5C.LayerStatement
public import WaveTurbulence.Foundations.VineEst.VineEstS3.Step3Final

/-! # The leaf-cost product of the rows is the region leaf size (Step 3 port, R45)

`prod_rowCostH_eq`: `∏ ρ rowCostH ρ = regionLeafSize` (the rows of the chain are in bijection with the regional pairs and
the interior branches); `step3BoundH_eq`: `step3BoundH = step3Bound * ofReal regionLeafSize`; `step3BoundH_le`: the literal
bound times `regionLeafSize`.
-/

@[expose] public section
variable {rowSelU : Unit} [rowSel : WaveTurbulence.VineEst.RowSel rowSelU]
set_option autoImplicit false
open WaveTurbulence.Induct
namespace WaveTurbulence.VineEstS5C
open WaveTurbulence WaveTurbulence.VineEstS2 WaveTurbulence.VineEstS3 WaveTurbulence.VineEstS3.Eng
  WaveTurbulence.LGSpine VineParamContract TTree Reg Reg.Skeleton RegRed
open scoped ENNReal
variable {w : ℕ} {G : Garden w} {U : Finset (GBranch G.tree)} {a b : GBranch G.tree}
variable {R : CLRegionData G U a b} {n : ℕ}

theorem prod_rowCostH_eq (hM9 : VINEPARAM) (B : CLChainAssembly G R n) (RD : ReconstructionData G) (hG : G.IsPlain)
    (layer : GNode (RD.forest hG) → ℕ) (hLayer : IsLayering (RD.garden hG) layer) (Bh : ℕ → ℝ)
    {d : ℕ} (W : SumintWeightClockData (assemblyShape hM9 B) d) :
    ∏ ρ : Row (sourceSumintDatum hM9 B hG W), rowCostH hM9 B RD hG layer hLayer Bh W ρ =
      regionLeafSize RD hG R layer hLayer Bh := by
  classical
  have e1 : ∏ p ∈ clRegionalPairs hG U, ∏ ℓ ∈ inputLeaves (nativeCoupleLayered RD hG layer hLayer p).garden,
        Bh ((nativeCoupleLayered RD hG layer hLayer p).layer ℓ.toNode) =
      ∏ v : (assemblyShape hM9 B).VIdx, layerCost Bh (rowCoupleLG hM9 B RD hG layer hLayer v) := by
    rw [← Finset.prod_coe_sort]
    exact (Equiv.prod_comp ((assemblyRowEquiv hM9 B).symm.trans (assemblyPairOrder hG B hM9).symm)
      (fun p : ↥(clRegionalPairs hG U) => ∏ ℓ ∈ inputLeaves (nativeCoupleLayered RD hG layer hLayer p.1).garden,
        Bh ((nativeCoupleLayered RD hG layer hLayer p.1).layer ℓ.toNode))).symm
  have e2 : ∏ v ∈ clInteriorBranches R, ∏ ℓ ∈ inputLeaves (nativeChainLayered RD hG layer hLayer v).garden,
        Bh ((nativeChainLayered RD hG layer hLayer v).layer ℓ.toNode) =
      ∏ v : (assemblyShape hM9 B).VIdx, layerCost Bh (rowTreeLG hM9 B RD hG layer hLayer v) := by
    rw [← Finset.prod_coe_sort]
    exact (Equiv.prod_comp ((assemblyRowEquiv hM9 B).symm.trans (assemblyIntOrder hM9 B).e.symm)
      (fun z : ↥(clInteriorBranches R) => ∏ ℓ ∈ inputLeaves (nativeChainLayered RD hG layer hLayer z.1).garden,
        Bh ((nativeChainLayered RD hG layer hLayer z.1).layer ℓ.toNode))).symm
  unfold Row
  rw [Fintype.prod_sum_type]
  unfold regionLeafSize
  rw [e1, e2]
  rfl

theorem regionLeafSize_nonneg {P : WTParams} {h : ℕ → Mom P.d → ℝ} {Bh : ℕ → ℝ} {p : ℕ}
    (hB : ProfileBound P h Bh p) (hM9 : VINEPARAM) (B : CLChainAssembly G R n) (RD : ReconstructionData G)
    (hG : G.IsPlain) (layer : GNode (RD.forest hG) → ℕ) (hLayer : IsLayering (RD.garden hG) layer)
    (hlay : ∀ x, layer x ≤ p) (W : SumintWeightClockData (assemblyShape hM9 B) P.d) :
    0 ≤ regionLeafSize RD hG R layer hLayer Bh := by
  rw [← prod_rowCostH_eq hM9 B RD hG layer hLayer Bh W]
  exact Finset.prod_nonneg fun ρ _ => rowCostH_nonneg (hLayer := hLayer) hB hlay W ρ

theorem step3BoundH_eq {P : WTParams} {h : ℕ → Mom P.d → ℝ} {Bh : ℕ → ℝ} {p : ℕ} (hB : ProfileBound P h Bh p)
    (Cfs : ℝ≥0∞) (hM9 : VINEPARAM) (B : CLChainAssembly G R n) (RD : ReconstructionData G) (hG : G.IsPlain)
    (layer : GNode (RD.forest hG) → ℕ) (hLayer : IsLayering (RD.garden hG) layer)
    (hlay : ∀ x, layer x ≤ p) (badKind : Fin (assemblyShape hM9 B).I → Fin 4)
    (qOut : Fin 3 → ℕ) (centre : Fin 4 → Mom P.d) (wBar : Mom P.d)
    (hrb : ∀ ρ, 0 ≤ rowBound hM9 B RD hG layer hLayer P (step3W hM9 B RD hG layer hLayer badKind qOut centre wBar) ρ) :
    step3BoundH P Bh Cfs hM9 B RD hG layer hLayer badKind qOut centre wBar =
      step3Bound P Cfs hM9 B RD hG layer hLayer badKind qOut centre wBar *
        ENNReal.ofReal (regionLeafSize RD hG R layer hLayer Bh) := by
  classical
  set W := step3W hM9 B RD hG layer hLayer badKind qOut centre wBar with hW
  unfold step3BoundH step3Bound
  dsimp only
  have hc := rowCostH_nonneg (hLayer := hLayer) hB hlay W
  have e1 : ∀ ρ : Row (sourceSumintDatum hM9 B hG W),
      Cfs * ENNReal.ofReal (2 * rowBoundH hM9 B RD hG layer hLayer P Bh W ρ) =
        (Cfs * ENNReal.ofReal (2 * rowBound hM9 B RD hG layer hLayer P W ρ)) *
          ENNReal.ofReal (rowCostH hM9 B RD hG layer hLayer Bh W ρ) := by
    intro ρ
    unfold rowBoundH
    have h2 : ENNReal.ofReal (2 * (rowBound hM9 B RD hG layer hLayer P W ρ * rowCostH hM9 B RD hG layer hLayer Bh W ρ)) =
        ENNReal.ofReal (2 * rowBound hM9 B RD hG layer hLayer P W ρ) *
          ENNReal.ofReal (rowCostH hM9 B RD hG layer hLayer Bh W ρ) := by
      rw [← ENNReal.ofReal_mul (by have := hrb ρ; linarith)]; congr 1; ring
    rw [h2, mul_assoc]
  have e3 : ∏ ρ : Row (sourceSumintDatum hM9 B hG W),
        (Cfs * ENNReal.ofReal (2 * rowBoundH hM9 B RD hG layer hLayer P Bh W ρ)) =
      (∏ ρ : Row (sourceSumintDatum hM9 B hG W), (Cfs * ENNReal.ofReal (2 * rowBound hM9 B RD hG layer hLayer P W ρ))) *
        ENNReal.ofReal (regionLeafSize RD hG R layer hLayer Bh) := by
    rw [Finset.prod_congr rfl (fun ρ _ => e1 ρ), Finset.prod_mul_distrib,
      ← ENNReal.ofReal_prod_of_nonneg (fun ρ _ => hc ρ), prod_rowCostH_eq hM9 B RD hG layer hLayer Bh W]
  rw [e3]
  ring

end WaveTurbulence.VineEstS5C
