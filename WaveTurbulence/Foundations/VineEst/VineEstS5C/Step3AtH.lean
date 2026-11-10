/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.VineEst.VineEstS5C.NativeRowsH
public import WaveTurbulence.Foundations.VineEst.VineEstS3.Step3AtLeaf

/-! # Step 3 at a fixed parameter `P` for the layer family `h` with leaf cost (R45 port of `Step3AtLeaf`)

`step3AtLeafH` is `step3AtLeaf` with the common-profile gates replaced by `CoherentGateH`/`IncoherentGateH`, the inputs
`inputsF P Rin` by `h`, and each row bound `rowBound ρ` by `rowBoundH ρ = rowBound ρ * layerCost Bh (garden of ρ)`
(`Bh > 0` on layers `≤ p`, needed for the strict inequality of the engine).
-/

@[expose] public section
variable {rowSelU : Unit} [rowSel : WaveTurbulence.VineEst.RowSel rowSelU]
set_option autoImplicit false
open WaveTurbulence.Induct
open WaveTurbulence.VineParamContract
namespace WaveTurbulence.VineEstS5C
open WaveTurbulence WaveTurbulence.VineEstS2 WaveTurbulence.VineEstS3 WaveTurbulence.VineEstS3.Eng WaveTurbulence.DegenVine WaveTurbulence.LGSpine
  VineParamContract TTree Reg Reg.Skeleton RegRed MeasureTheory
open scoped ENNReal

theorem layerCost_pos {Bh : ℕ → ℝ} {w : ℕ} (LG : LayeredGarden w) (hB : ∀ x, 0 < Bh (LG.layer x)) :
    0 < layerCost Bh LG :=
  Finset.prod_pos fun _ _ => hB _

theorem rowCostH_pos {w d : ℕ} {G : Garden w} {U : Finset (GBranch G.tree)} {a b : GBranch G.tree}
    {R : CLRegionData G U a b} {n : ℕ} {hM9 : VINEPARAM} {B : CLChainAssembly G R n} {RD : ReconstructionData G}
    {hG : G.IsPlain} {layer : GNode (RD.forest hG) → ℕ} {hLayer : IsLayering (RD.garden hG) layer}
    {Bh : ℕ → ℝ} {p : ℕ} (hBpos : ∀ r ≤ p, 0 < Bh r) (hlay : ∀ x, layer x ≤ p)
    (W : SumintWeightClockData (assemblyShape hM9 B) d) (ρ : Row (sourceSumintDatum hM9 B hG W)) :
    0 < rowCostH hM9 B RD hG layer hLayer Bh W ρ := by
  rcases ρ with v | v
  · exact layerCost_pos _ fun x => hBpos _ (rowCouple_layer_le hlay v x)
  · exact layerCost_pos _ fun x => hBpos _ (rowTree_layer_le hlay v x)

end WaveTurbulence.VineEstS5C
