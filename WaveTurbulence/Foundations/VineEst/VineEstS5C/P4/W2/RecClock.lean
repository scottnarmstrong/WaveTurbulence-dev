/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.VineEst.VineEstS5C.P4.W2.NatFree
public import WaveTurbulence.Foundations.VineEst.VineEstS5C.P4.W2.DomEng

/-! # P4-W2 (session 13, step 2c): the row clock boxes of the non-exceptional rows

`rows_clock_mem_exc`: the clock pair of a row lies in its time box (`rowBx`) at every `τ` in the unit windows of the datum, with the parent-clock condition
`u v < parentClock t₀ u v` at every interior branch `v` that is not exceptional (`v ∉ Bex`), for every row except the tree rows of exceptional branches
(`rows_clock_mem` of `VineEstS3` is the case `Bex = ∅` from the full source time domain).
-/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.VineEstS5C.P4.W2
open VineParamContract TTree Reg Reg.Skeleton RegRed MeasureTheory WaveTurbulence.VineEstS2 WaveTurbulence.VineEstS5A
  WaveTurbulence.VineEstS5C WaveTurbulence.VineEstS3 WaveTurbulence.VineEstS3.Eng WaveTurbulence.DegenVine WaveTurbulence.DegenVinePar
  WaveTurbulence.VineEstS5C.P2 WaveTurbulence.VineEstS5C.P3 WaveTurbulence.VineEstS5C.P4 WaveTurbulence.VineEstS4
  WaveTurbulence.VineEstS5B

variable {w d : ℕ} {G : Garden w} {U : Finset (GBranch G.tree)} {a b : GBranch G.tree}
variable {R : CLRegionData G U a b} {n : ℕ}
variable (hM9 : VINEPARAM) (B : CLChainAssembly G R n) (RD : ReconstructionData G) (hG : G.IsPlain)

theorem rows_clock_mem_exc (W : SumintWeightClockData (assemblyShape hM9 B) d) (L γ δ : ℝ) (F : ℕ → Mom d → ℝ)
    (layer : GNode (RD.forest hG) → ℕ) (hLayer : IsLayering (RD.garden hG) layer)
    (tt : Fin 3 → ℝ) (htt : tt ∈ outBox (sourceSumintDatum hM9 B hG W)) (τ : (assemblyShape hM9 B).TVar → ℝ)
    (hwin : ∀ s, (W.q s : ℝ) ≤ τ s ∧ τ s ≤ W.q s + 1) (Bex : Finset (GBranch G.tree))
    (hpar : ∀ z : ↥(clInteriorBranches R), z.1 ∉ Bex →
      clLocalClock R tt (assemblyClockEquiv hM9 B τ) z.1 <
        parentClock (tt 0) (clLocalClock R tt (assemblyClockEquiv hM9 B τ)) z.1.toNode)
    (ρ : Row (sourceSumintDatum hM9 B hG W))
    (hρ : ∀ v, ρ = Sum.inr v → (assemblyBranchOf hM9 B v).1 ∉ Bex) :
    (assemblyClocked hM9 B RD hG W L γ δ F layer hLayer).clock τ tt ρ ∈
      rowBx hM9 B RD hG layer hLayer W L γ δ F ρ := by
  have hsl : ∀ s : Eng.Slot (sourceSumintDatum hM9 B hG W),
      slotVal (sourceSumintDatum hM9 B hG W) τ tt s ∈
        Set.Icc ((qslot (sourceSumintDatum hM9 B hG W) s : ℕ) : ℝ) ((qslot (sourceSumintDatum hM9 B hG W) s : ℕ) + 1) := by
    intro s
    rcases s with v | c
    · exact ⟨(hwin v).1, (hwin v).2⟩
    · exact htt.1 c
  have hbox : ∀ i : Fin 2, (assemblyClocked hM9 B RD hG W L γ δ F layer hLayer).clock τ tt ρ i ∈
      Set.Icc (((if i = 0 then (rowQ hM9 B RD hG W L γ δ F layer hLayer ρ).1
        else (rowQ hM9 B RD hG W L γ δ F layer hLayer ρ).2 : ℕ)) : ℝ)
        ((if i = 0 then (rowQ hM9 B RD hG W L γ δ F layer hLayer ρ).1
        else (rowQ hM9 B RD hG W L γ δ F layer hLayer ρ).2 : ℕ) + 1) := by
    intro i
    fin_cases i
    · exact hsl _
    · exact hsl _
  rcases ρ with v | v
  · exact ⟨hbox 0, hbox 1⟩
  · refine ⟨⟨hbox 0, hbox 1⟩, ?_⟩
    have hz := hpar (assemblyBranchOf hM9 B v) (hρ v rfl)
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

end WaveTurbulence.VineEstS5C.P4.W2
