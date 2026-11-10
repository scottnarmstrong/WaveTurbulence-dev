/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.VineEst.RowSel.Bounds
public import WaveTurbulence.Foundations.VineEst.VineEstS3.NativeRows
public import WaveTurbulence.Foundations.VineEst.VineEstS3.TreeClockOrder
public import WaveTurbulence.Foundations.VineEst.VineEstS3.EpsLabels
public import WaveTurbulence.Foundations.VineEst.VineEstS3.ConstraintsOK
public import WaveTurbulence.Foundations.GammaLow.Famb.Family
public import WaveTurbulence.Foundations.VineEst.VineEstS3.Step3Data
public import WaveTurbulence.Foundations.GammaLow.Famb.VineEstS3.EpsLabels
public import WaveTurbulence.Foundations.GammaLow.Famb.VineEstS3.NativeRows
-- L5b port of `WaveTurbulence.Foundations.VineEst.VineEstS3.Step3Data` (sha256 3cad61d1f6834947…): its chain-dependent declarations only, over 𝒱_γ;
-- see GammaLow/Famb/PROGRESS.md (Design) and COPIED-SHA256SUMS.

/-! # Step 3 data: the weight record `W`, continuity and clock membership of the rows -/

@[expose] public section
variable {rowSelU : Unit} [rowSel : WaveTurbulence.VineEst.RowSel rowSelU]
set_option autoImplicit false
open WaveTurbulence.Induct
open WaveTurbulence.VineParamContract
namespace WaveTurbulence.GammaLow.Famb.VineEstS3
open WaveTurbulence.VineEstS3 WaveTurbulence.GammaLow.Famb.VineEstS3
variable {γF : ℝ}
open WaveTurbulence WaveTurbulence.VineEstS2 WaveTurbulence.VineEstS3.Eng WaveTurbulence.LGSpine VineParamContract TTree WaveTurbulence.GammaLow.Famb.VineEstS2
  Reg Reg.Skeleton RegRed MeasureTheory
variable {w d : ℕ} {G : Garden w} {U : Finset (GBranch G.tree)} {a b : GBranch G.tree}
variable {R : CLRegionData G U a b} {n : ℕ}

/-- The `sumint` weight/window record of Step 3: zero weights (overridden by the engine), `g, g'` = incoherency
indices of the native couple/tree of the row, `param = 0`, the source windows and parent-order constraints. -/
noncomputable def step3WΓ (hM9 : NormalChartSupply γF) (B : CLChainAssemblyΓ γF G R n) (RD : ReconstructionData G) (hG : G.IsPlain)
    (layer : GNode (RD.forest hG) → ℕ) (hLayer : IsLayering (RD.garden hG) layer)
    (badKind : Fin (assemblyShapeΓ hM9 B).I → Fin 4) (qOut : Fin 3 → ℕ) (centre : Fin 4 → Mom d) (wBar : Mom d) :
    SumintWeightClockData (assemblyShapeΓ hM9 B) d where
  wK := fun _ _ => 0
  wL := fun _ _ => 0
  g := rowCoupleGΓ hM9 B RD hG layer hLayer
  g' := rowTreeGΓ hM9 B RD hG layer hLayer
  param := fun _ => 0
  q := assemblyTimeQΓ hM9 B (fun v => layer (RD.coreBranch hG v).toNode)
  constraints := assemblyTimeConstraintsΓ hM9 B ∪
    layerOrderPairs (assemblyTimeQΓ hM9 B (fun v => layer (RD.coreBranch hG v).toNode))
  badKind := badKind
  qOut := qOut
  centre := centre
  wBar := wBar

section Rows
variable (hM9 : NormalChartSupply γF) (B : CLChainAssemblyΓ γF G R n) (RD : ReconstructionData G) (hG : G.IsPlain)
  (layer : GNode (RD.forest hG) → ℕ) (hLayer : IsLayering (RD.garden hG) layer)

/-- The time box of a row: `timeBox q q'` for couple rows, `timeBoxGt q q'` for tree rows. -/
noncomputable def rowBxΓ (W : SumintWeightClockData (assemblyShapeΓ hM9 B) d) (L γ δ : ℝ) (F : ℕ → Mom d → ℝ) :
    Row (sourceSumintDatumΓ hM9 B hG W) → Set (Fin 2 → ℝ)
  | Sum.inl v => timeBox ((rowQΓ hM9 B RD hG W L γ δ F layer hLayer (Sum.inl v)).1 : ℝ)
      ((rowQΓ hM9 B RD hG W L γ δ F layer hLayer (Sum.inl v)).2 : ℝ)
  | Sum.inr v => timeBoxGt ((rowQΓ hM9 B RD hG W L γ δ F layer hLayer (Sum.inr v)).1 : ℝ)
      ((rowQΓ hM9 B RD hG W L γ δ F layer hLayer (Sum.inr v)).2 : ℝ)

/-- The lower-left corner of the unit cell of a row. -/
noncomputable def rowQxΓ (W : SumintWeightClockData (assemblyShapeΓ hM9 B) d) (L γ δ : ℝ) (F : ℕ → Mom d → ℝ)
    (ρ : Row (sourceSumintDatumΓ hM9 B hG W)) : Fin 2 → ℝ :=
  ![((rowQΓ hM9 B RD hG W L γ δ F layer hLayer ρ).1 : ℝ), ((rowQΓ hM9 B RD hG W L γ δ F layer hLayer ρ).2 : ℝ)]

/-- The size bound attached to each weight row. -/
noncomputable def rowBoundΓ (P : WTParams) (W : SumintWeightClockData (assemblyShapeΓ hM9 B) P.d) :
    Row (sourceSumintDatumΓ hM9 B hG W) → ℝ
  | Sum.inl v => rowB P ((rowCoupleΓ hM9 B RD hG v).size / 2) (rowCoupleGΓ hM9 B RD hG layer hLayer v)
  | Sum.inr v => rowB P ((rowTreeΓ hM9 B RD v).size / 2) (rowTreeGΓ hM9 B RD hG layer hLayer v)

theorem rowBx_subset_cellΓ (W : SumintWeightClockData (assemblyShapeΓ hM9 B) d) (L γ δ : ℝ) (F : ℕ → Mom d → ℝ)
    (ρ : Row (sourceSumintDatumΓ hM9 B hG W)) :
    rowBxΓ hM9 B RD hG layer hLayer W L γ δ F ρ ⊆ FS.cell (rowQxΓ hM9 B RD hG layer hLayer W L γ δ F ρ) := by
  rcases ρ with v | v
  · exact timeBox_subset_cell _ _
  · exact timeBoxGt_subset_cell _ _

theorem rowBx_closureΓ (W : SumintWeightClockData (assemblyShapeΓ hM9 B) d) (L γ δ : ℝ) (F : ℕ → Mom d → ℝ)
    (hqq : ∀ v, (rowQΓ hM9 B RD hG W L γ δ F layer hLayer (Sum.inr v)).2 ≤
      (rowQΓ hM9 B RD hG W L γ δ F layer hLayer (Sum.inr v)).1)
    (ρ : Row (sourceSumintDatumΓ hM9 B hG W)) :
    rowBxΓ hM9 B RD hG layer hLayer W L γ δ F ρ ⊆ closure (interior (rowBxΓ hM9 B RD hG layer hLayer W L γ δ F ρ)) := by
  rcases ρ with v | v
  · exact timeBox_subset_closure_interior _ _
  · exact timeBoxGt_subset_closure_interior (by exact_mod_cast hqq v)

end Rows

end WaveTurbulence.GammaLow.Famb.VineEstS3
