/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.VineEst.VineEstS3.LayerFacts

/-! # Clock membership of the rows on the closed cube of output times

`rows_clock_mem` of `Step3Data` for `tt` in the closed cube `∏ [qOut c, qOut c + 1]` (the `max (t', t'') < t` part of the
output box is not used), needed for continuity of the clocked expression on a closed set (leaf lower children).
-/

@[expose] public section
set_option autoImplicit false
open WaveTurbulence.Induct
open WaveTurbulence.VineParamContract
namespace WaveTurbulence.VineEstS3
open WaveTurbulence WaveTurbulence.VineEstS2 WaveTurbulence.VineEstS3.Eng WaveTurbulence.LGSpine VineParamContract TTree
  Reg Reg.Skeleton RegRed MeasureTheory
variable {w d : ℕ} {G : Garden w} {U : Finset (GBranch G.tree)} {a b : GBranch G.tree}
variable {R : CLRegionData G U a b} {n : ℕ}
section Rows
variable (hM9 : VINEPARAM) (B : CLChainAssembly G R n) (RD : ReconstructionData G) (hG : G.IsPlain)
  (layer : GNode (RD.forest hG) → ℕ) (hLayer : IsLayering (RD.garden hG) layer)

theorem slotVal_mem_cube (W : SumintWeightClockData (assemblyShape hM9 B) d) (hG' : G.IsPlain)
    (tt : Fin 3 → ℝ)
    (htt : ∀ c, (W.qOut c : ℝ) ≤ tt c ∧ tt c ≤ W.qOut c + 1) (τ : (assemblyShape hM9 B).TVar → ℝ)
    (hτ : τ ∈ (sourceSumintDatum hM9 B hG' W).timeDom (assemblyShape_I_pos hM9 B) (tt 0) (tt 1) (tt 2))
    (s : Eng.Slot (sourceSumintDatum hM9 B hG' W)) :
    slotVal (sourceSumintDatum hM9 B hG' W) τ tt s ∈
      Set.Icc ((qslot (sourceSumintDatum hM9 B hG' W) s : ℕ) : ℝ) ((qslot (sourceSumintDatum hM9 B hG' W) s : ℕ) + 1) := by
  rcases s with v | c
  · exact ⟨(hτ.1 v).1, (hτ.1 v).2.1⟩
  · exact htt c

/-- **`hclock` of the engine**: the clock pair of a row lies in its time box. -/
theorem rows_clock_mem_cube (W : SumintWeightClockData (assemblyShape hM9 B) d)
    (hok : ConstraintsOK hM9 B W) (L γ δ : ℝ) (F : ℕ → Mom d → ℝ)
    (tt : Fin 3 → ℝ) (htt : ∀ c, (W.qOut c : ℝ) ≤ tt c ∧ tt c ≤ W.qOut c + 1) (τ : (assemblyShape hM9 B).TVar → ℝ)
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
    · exact slotVal_mem_cube hM9 B W hG tt htt τ hτ _
    · exact slotVal_mem_cube hM9 B W hG tt htt τ hτ _
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


end Rows
end WaveTurbulence.VineEstS3
