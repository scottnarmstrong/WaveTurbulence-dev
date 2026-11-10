/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.VineEst.RowSel.Bounds
public import WaveTurbulence.Foundations.VineEst.VineEstS3.NativeRows
public import WaveTurbulence.Foundations.VineEst.VineEstS3.TreeClockOrder
public import WaveTurbulence.Foundations.Spine.SchwartzCosetSummability
public import WaveTurbulence.Foundations.VineEst.VineEstS3.Pointwise
public import WaveTurbulence.Foundations.VineEst.VineEstS3.EpsLabels
public import WaveTurbulence.Foundations.VineEst.VineEstS3.ConstraintsOK

/-! # Step 3 data: the weight record `W`, continuity and clock membership of the rows -/

@[expose] public section
variable {rowSelU : Unit} [rowSel : WaveTurbulence.VineEst.RowSel rowSelU]
set_option autoImplicit false
open WaveTurbulence.Induct
open WaveTurbulence.VineParamContract
namespace WaveTurbulence.VineEstS3
open WaveTurbulence WaveTurbulence.VineEstS2 WaveTurbulence.VineEstS3.Eng WaveTurbulence.LGSpine VineParamContract TTree
  Reg Reg.Skeleton RegRed MeasureTheory
variable {w d : ℕ} {G : Garden w} {U : Finset (GBranch G.tree)} {a b : GBranch G.tree}
variable {R : CLRegionData G U a b} {n : ℕ}

/-- The `sumint` weight/window record of Step 3: zero weights (overridden by the engine), `g, g'` = incoherency
indices of the native couple/tree of the row, `param = 0`, the source windows and parent-order constraints. -/
noncomputable def step3W (hM9 : VINEPARAM) (B : CLChainAssembly G R n) (RD : ReconstructionData G) (hG : G.IsPlain)
    (layer : GNode (RD.forest hG) → ℕ) (hLayer : IsLayering (RD.garden hG) layer)
    (badKind : Fin (assemblyShape hM9 B).I → Fin 4) (qOut : Fin 3 → ℕ) (centre : Fin 4 → Mom d) (wBar : Mom d) :
    SumintWeightClockData (assemblyShape hM9 B) d where
  wK := fun _ _ => 0
  wL := fun _ _ => 0
  g := rowCoupleG hM9 B RD hG layer hLayer
  g' := rowTreeG hM9 B RD hG layer hLayer
  param := fun _ => 0
  q := assemblyTimeQ hM9 B (fun v => layer (RD.coreBranch hG v).toNode)
  constraints := assemblyTimeConstraints hM9 B ∪
    layerOrderPairs (assemblyTimeQ hM9 B (fun v => layer (RD.coreBranch hG v).toNode))
  badKind := badKind
  qOut := qOut
  centre := centre
  wBar := wBar

theorem step3W_ok (hM9 : VINEPARAM) (B : CLChainAssembly G R n) (RD : ReconstructionData G) (hG : G.IsPlain)
    (layer : GNode (RD.forest hG) → ℕ) (hLayer : IsLayering (RD.garden hG) layer)
    (badKind : Fin (assemblyShape hM9 B).I → Fin 4) (qOut : Fin 3 → ℕ) (centre : Fin 4 → Mom d) (wBar : Mom d) :
    ConstraintsOK hM9 B (step3W hM9 B RD hG layer hLayer badKind qOut centre wBar) :=
  constraintsOK_union hM9 B _ rfl

section Rows
variable (hM9 : VINEPARAM) (B : CLChainAssembly G R n) (RD : ReconstructionData G) (hG : G.IsPlain)
  (layer : GNode (RD.forest hG) → ℕ) (hLayer : IsLayering (RD.garden hG) layer)

/-- The time box of a row: `timeBox q q'` for couple rows, `timeBoxGt q q'` for tree rows. -/
noncomputable def rowBx (W : SumintWeightClockData (assemblyShape hM9 B) d) (L γ δ : ℝ) (F : ℕ → Mom d → ℝ) :
    Row (sourceSumintDatum hM9 B hG W) → Set (Fin 2 → ℝ)
  | Sum.inl v => timeBox ((rowQ hM9 B RD hG W L γ δ F layer hLayer (Sum.inl v)).1 : ℝ)
      ((rowQ hM9 B RD hG W L γ δ F layer hLayer (Sum.inl v)).2 : ℝ)
  | Sum.inr v => timeBoxGt ((rowQ hM9 B RD hG W L γ δ F layer hLayer (Sum.inr v)).1 : ℝ)
      ((rowQ hM9 B RD hG W L γ δ F layer hLayer (Sum.inr v)).2 : ℝ)

/-- The lower-left corner of the unit cell of a row. -/
noncomputable def rowQx (W : SumintWeightClockData (assemblyShape hM9 B) d) (L γ δ : ℝ) (F : ℕ → Mom d → ℝ)
    (ρ : Row (sourceSumintDatum hM9 B hG W)) : Fin 2 → ℝ :=
  ![((rowQ hM9 B RD hG W L γ δ F layer hLayer ρ).1 : ℝ), ((rowQ hM9 B RD hG W L γ δ F layer hLayer ρ).2 : ℝ)]

/-- The size bound attached to each weight row. -/
noncomputable def rowBound (P : WTParams) (W : SumintWeightClockData (assemblyShape hM9 B) P.d) :
    Row (sourceSumintDatum hM9 B hG W) → ℝ
  | Sum.inl v => rowB P ((rowCouple hM9 B RD hG v).size / 2) (rowCoupleG hM9 B RD hG layer hLayer v)
  | Sum.inr v => rowB P ((rowTree hM9 B RD v).size / 2) (rowTreeG hM9 B RD hG layer hLayer v)

theorem rowBx_subset_cell (W : SumintWeightClockData (assemblyShape hM9 B) d) (L γ δ : ℝ) (F : ℕ → Mom d → ℝ)
    (ρ : Row (sourceSumintDatum hM9 B hG W)) :
    rowBx hM9 B RD hG layer hLayer W L γ δ F ρ ⊆ FS.cell (rowQx hM9 B RD hG layer hLayer W L γ δ F ρ) := by
  rcases ρ with v | v
  · exact timeBox_subset_cell _ _
  · exact timeBoxGt_subset_cell _ _

theorem rowBx_closure (W : SumintWeightClockData (assemblyShape hM9 B) d) (L γ δ : ℝ) (F : ℕ → Mom d → ℝ)
    (hqq : ∀ v, (rowQ hM9 B RD hG W L γ δ F layer hLayer (Sum.inr v)).2 ≤
      (rowQ hM9 B RD hG W L γ δ F layer hLayer (Sum.inr v)).1)
    (ρ : Row (sourceSumintDatum hM9 B hG W)) :
    rowBx hM9 B RD hG layer hLayer W L γ δ F ρ ⊆ closure (interior (rowBx hM9 B RD hG layer hLayer W L γ δ F ρ)) := by
  rcases ρ with v | v
  · exact timeBox_subset_closure_interior _ _
  · exact timeBoxGt_subset_closure_interior (by exact_mod_cast hqq v)

end Rows

end WaveTurbulence.VineEstS3
