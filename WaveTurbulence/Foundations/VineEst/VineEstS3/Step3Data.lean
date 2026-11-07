/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.VineEst.VineEstS3.NativeRows
public import WaveTurbulence.Foundations.VineEst.VineEstS3.TreeClockOrder
public import WaveTurbulence.Foundations.VineEst.VineEstS3.InputsSummable
public import WaveTurbulence.Foundations.VineEst.VineEstS3.Continuity
public import WaveTurbulence.Foundations.VineEst.VineEstS3.AdmissibleAssembly
public import WaveTurbulence.Foundations.VineEst.VineEstS3.EpsLabels
public import WaveTurbulence.Foundations.VineEst.VineEstS3.ConstraintsOK

/-! # Step 3 data: the weight record `W`, continuity and clock membership of the rows -/

@[expose] public section
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

theorem slotVal_mem (W : SumintWeightClockData (assemblyShape hM9 B) d) (hG' : G.IsPlain)
    (tt : Fin 3 → ℝ)
    (htt : tt ∈ outBox (sourceSumintDatum hM9 B hG' W)) (τ : (assemblyShape hM9 B).TVar → ℝ)
    (hτ : τ ∈ (sourceSumintDatum hM9 B hG' W).timeDom (assemblyShape_I_pos hM9 B) (tt 0) (tt 1) (tt 2))
    (s : Eng.Slot (sourceSumintDatum hM9 B hG' W)) :
    slotVal (sourceSumintDatum hM9 B hG' W) τ tt s ∈
      Set.Icc ((qslot (sourceSumintDatum hM9 B hG' W) s : ℕ) : ℝ) ((qslot (sourceSumintDatum hM9 B hG' W) s : ℕ) + 1) := by
  rcases s with v | c
  · exact ⟨(hτ.1 v).1, (hτ.1 v).2.1⟩
  · exact (htt.1 c)

/-- **`hclock` of the engine**: the clock pair of a row lies in its time box. -/
theorem rows_clock_mem (W : SumintWeightClockData (assemblyShape hM9 B) d)
    (hok : ConstraintsOK hM9 B W) (L γ δ : ℝ) (F : ℕ → Mom d → ℝ)
    (tt : Fin 3 → ℝ) (htt : tt ∈ outBox (sourceSumintDatum hM9 B hG W)) (τ : (assemblyShape hM9 B).TVar → ℝ)
    (hτ : τ ∈ (sourceSumintDatum hM9 B hG W).timeDom (assemblyShape_I_pos hM9 B) (tt 0) (tt 1) (tt 2))
    (ρ : Row (sourceSumintDatum hM9 B hG W)) :
    (assemblyClocked hM9 B RD hG W L γ δ F layer hLayer).clock τ tt ρ ∈
      rowBx hM9 B RD hG layer hLayer W L γ δ F ρ := by
  have hbox : ∀ i : Fin 2, (assemblyClocked hM9 B RD hG W L γ δ F layer hLayer).clock τ tt ρ i ∈
      Set.Icc (((if i = 0 then (rowQ hM9 B RD hG W L γ δ F layer hLayer ρ).1
        else (rowQ hM9 B RD hG W L γ δ F layer hLayer ρ).2 : ℕ)) : ℝ)
        ((if i = 0 then (rowQ hM9 B RD hG W L γ δ F layer hLayer ρ).1
        else (rowQ hM9 B RD hG W L γ δ F layer hLayer ρ).2 : ℕ) + 1) := by
    intro i
    fin_cases i
    · exact slotVal_mem hM9 B W hG tt htt τ hτ _
    · exact slotVal_mem hM9 B W hG tt htt τ hτ _
  rcases ρ with v | v
  · exact ⟨hbox 0, hbox 1⟩
  · refine ⟨⟨hbox 0, hbox 1⟩, ?_⟩
    have hz := clock_lt_parentClock hM9 B hG W hok tt τ hτ (assemblyBranchOf hM9 B v)
    have h3 := nodeSlot_spec hM9 B (assemblyBranchOf hM9 B v).1.toNode
      ((branch_mem_clRealizationNodes (assemblyBranchOf hM9 B v).1).mpr
        (Finset.mem_erase.mp (assemblyBranchOf hM9 B v).2).2)
      (interior_ne (assemblyBranchOf hM9 B v)) tt τ
    have h4 := branchSlot_spec hM9 B (assemblyBranchOf hM9 B v) tt τ
    have e1 : (assemblyClocked hM9 B RD hG W L γ δ F layer hLayer).clock τ tt (Sum.inr v) 1 =
        τ (branchSlot hM9 B (assemblyBranchOf hM9 B v)) := by
      simp [ClockedRows.clock, assemblyClocked, slotVal]
      rfl
    have e0 : (assemblyClocked hM9 B RD hG W L γ δ F layer hLayer).clock τ tt (Sum.inr v) 0 =
        Sum.elim τ tt (nodeSlot hM9 B (assemblyBranchOf hM9 B v).1.toNode) := by
      simp [ClockedRows.clock, assemblyClocked, slotVal]
      rfl
    show (assemblyClocked hM9 B RD hG W L γ δ F layer hLayer).clock τ tt (Sum.inr v) 1 <
      (assemblyClocked hM9 B RD hG W L γ δ F layer hLayer).clock τ tt (Sum.inr v) 0
    rw [e1, e0, ← h3, ← h4]
    exact hz

/-- **`hcont` of the engine**: the starred kernels are continuous in the clock pair. -/
theorem rows_continuous {P : WTParams} {p : ℕ} {Rin : ℕ → Mom P.d → ℝ} (hd : 1 ≤ P.d) (hL : 1 ≤ P.L)
    (hR : ∀ r ≤ p, InputRemainder P (Rin r) r) (hlay : ∀ x, layer x ≤ p)
    (W : SumintWeightClockData (assemblyShape hM9 B) P.d) (ρ : Row (sourceSumintDatum hM9 B hG W)) (k : Mom P.d) :
    Continuous fun t : Fin 2 → ℝ =>
      (assemblyClocked hM9 B RD hG W P.L P.γ P.δ (inputsF P Rin) layer hLayer).W ρ t k := by
  rcases ρ with v | v
  · have hplain : (rowCoupleLG hM9 B RD hG layer hLayer v).garden.IsPlain := by
      unfold rowCoupleLG
      rw [nativeCoupleLayered_garden]
      exact (decodedCouple_decodes _).1.1
    exact continuous_KQstar_time P.L P.γ P.δ (inputsF P Rin) (rowCoupleLG hM9 B RD hG layer hLayer v) hplain k
      (fun ℓ _ => summable_inputsF_of_InputRemainder P Rin hd hL (hR _ (hlay _)) k)
  · have hT : IsPairedTree (rowTreeLG hM9 B RD hG layer hLayer v).garden := by
      unfold rowTreeLG
      exact decodedTree_isPairedTree _ _
    exact continuous_KTstar_time P.L P.γ P.δ (inputsF P Rin) (rowTreeLG hM9 B RD hG layer hLayer v) hT k
      (fun ℓ _ => summable_inputsF_of_InputRemainder P Rin hd hL (hR _ (hlay _)) k)

end Rows

end WaveTurbulence.VineEstS3
