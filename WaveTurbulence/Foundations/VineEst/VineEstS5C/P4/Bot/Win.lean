/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.VineEst.VineEstS5C.P4.Bot.Decomp

/-! # BOT-DECOMP: the windows of the bottom bundle from the frame domain `DomF` (mirror of `P4.Win`, `win_of_domF` analogue)

`botFrame ≠ 0` forces `DomF (layOf A) c0.U c0.a c0.b u`; with the exterior window of `c0.a` (`ExtOf`), every branch of `c0.U` is in its unit layer window.
`bot_window_caseA/M`: the windows `t₁` (resp. `s₁`) `∈ (L₄, L₄+1]`, `t₀ ∈ [L₂, L₂+1]` of `bundle_decomp_bot(_mirror)`.  Here `t₀ = u c0.b` and `c0.b` is the lower joint
of `pstar` (`hb0`).
-/

@[expose] public section
variable {rowSelU : Unit} [rowSel : WaveTurbulence.VineEst.RowSel rowSelU]
set_option autoImplicit false
open WaveTurbulence.Induct
namespace WaveTurbulence.VineEstS5C.P4.Bot
open WaveTurbulence WaveTurbulence.Twist WaveTurbulence.LFTwist WaveTurbulence.VineEstS4 WaveTurbulence.VineEstS5B
  WaveTurbulence.VineEstS5B2 WaveTurbulence.Links WaveTurbulence.Reg.Skeleton WaveTurbulence.RegRed WaveTurbulence.LGSpine
  WaveTurbulence.ConjCoh TTree WaveTurbulence.VineEstS4c WaveTurbulence.VineEstS5C

set_option linter.unusedSectionVars false

section
variable {w : ℕ} {ι : Type*} {d : ℕ} [Fintype ι] [DecidableEq ι] {pstar : ι}
  (A : FamilyReconstruction w ι) (c0 : ChainAt A.skeleton A.family)

/-- `botFrame ≠ 0` forces the frame domain. -/
theorem domF_of_botFrame_ne (κ : KPar d) (x : GNode A.skeleton.tree → (Fin d → ℤ)) (u : GBranch A.skeleton.tree → ℝ)
    (h : botFrame κ A c0 pstar x u ≠ 0) : DomF (layOf A) c0.U c0.a c0.b u := by
  classical
  by_contra hD
  apply h
  unfold botFrame spartFrame
  have hD' : ¬ DomF (fun v => stateLayer A (A.data.coreBranch A.plain v).toNode) c0.U c0.a c0.b u := hD
  rw [if_neg hD', zero_mul]

/-- The windows of all branches of the chain region (given the window of the exterior clock `u a`). -/
theorem bot_win_of_domF (u : GBranch A.skeleton.tree → ℝ) (hD : DomF (layOf A) c0.U c0.a c0.b u)
    (hext : (layOf A c0.a : ℝ) < u c0.a ∧ u c0.a < layOf A c0.a + 1) :
    ∀ v ∈ c0.U, (layOf A v : ℝ) < u v ∧ u v < layOf A v + 1 := by
  intro v hv
  by_cases hva : v = c0.a
  · subst hva; exact hext
  · exact ⟨(hD v (Finset.mem_erase.mpr ⟨hva, hv⟩)).1, (hD v (Finset.mem_erase.mpr ⟨hva, hv⟩)).2.1⟩

variable (hb0 : c0.b = (A.family.placement pstar).lower)
include hb0

theorem bot_qbOf_mem : qbOf (A.family.placement pstar) ∈ c0.U := by
  have hSlow := chain_slow c0 pstar hb0
  have hx : (A.family.placement pstar).lower.toNode ∈ clRealizationNodes A.skeleton c0.U :=
    (branch_mem_clRealizationNodes _).mpr hSlow.lower_mem
  have hne : (A.family.placement pstar).lower.toNode ≠ c0.a.toNode := fun he =>
    c0.block.2.2.2.1 ((Mole.branch_toNode_injective he).symm.trans hSlow.lower.symm)
  exact (cl_realization_parent c0.block (botR A c0) _ hx hne).choose_spec

theorem bot_qrOf_mem : qrOf (A.family.placement pstar) ∈ c0.U := by
  have hSlow := chain_slow c0 pstar hb0
  have hx : (A.skeleton.pair (A.family.placement pstar).retained).toNode ∈ clRealizationNodes A.skeleton c0.U :=
    (leaf_mem_clRealizationNodes _).mpr hSlow.partner_internal
  have hne : (A.skeleton.pair (A.family.placement pstar).retained).toNode ≠ c0.a.toNode :=
    (Mole.branch_toNode_ne_leaf c0.a _).symm
  exact (cl_realization_parent c0.block (botR A c0) _ hx hne).choose_spec

/-- **The windows, case A** (`bundle_decomp_bot` hypotheses) from the frame domain and the exterior window. -/
theorem bot_window_caseA (κ : KPar d)
    (hr : RetParent (pstar := pstar) A) (hq2 : zpQ2 A pstar ≤ layOf A (qrOf (A.family.placement pstar)))
    (hA : CaseA (pstar := pstar) A) (x : GNode A.skeleton.tree → (Fin d → ℤ)) (u : GBranch A.skeleton.tree → ℝ)
    (hD : DomF (layOf A) c0.U c0.a c0.b u)
    (hext : (layOf A c0.a : ℝ) < u c0.a ∧ u c0.a < layOf A c0.a + 1) :
    (zpQ4 A pstar : ℝ) < (botVars κ A c0 pstar x u).2.2.1 ∧ (botVars κ A c0 pstar x u).2.2.1 ≤ zpQ4 A pstar + 1 ∧
      (zpQ2 A pstar : ℝ) ≤ (botVars κ A c0 pstar x u).1 ∧ (botVars κ A c0 pstar x u).1 ≤ zpQ2 A pstar + 1 := by
  have hw := bot_win_of_domF A c0 u hD hext
  have hb00 := hw _ c0.block.2.2.1
  rw [hb0] at hb00
  refine ⟨?_, ?_, ?_, ?_⟩ <;> simp only [botVars, dictT1, hb0, zpQ4_eq_t1 A hr hq2 hA, zpQ2_eq_layOf]
  · by_cases hn : nuOf A pstar = 1
    · simp only [hn, if_true]; exact (hw _ (bot_qbOf_mem A c0 hb0)).1
    · simp only [hn, if_false]; exact (hw _ (bot_qrOf_mem A c0 hb0)).1
  · by_cases hn : nuOf A pstar = 1
    · simp only [hn, if_true]; exact (hw _ (bot_qbOf_mem A c0 hb0)).2.le
    · simp only [hn, if_false]; exact (hw _ (bot_qrOf_mem A c0 hb0)).2.le
  · exact hb00.1.le
  · exact hb00.2.le

/-- **The windows, case M** (`bundle_decomp_bot_mirror` hypotheses). -/
theorem bot_window_caseM (κ : KPar d)
    (hr : RetParent (pstar := pstar) A) (hq2 : zpQ2 A pstar ≤ layOf A (qrOf (A.family.placement pstar)))
    (hM : CaseM (pstar := pstar) A) (x : GNode A.skeleton.tree → (Fin d → ℤ)) (u : GBranch A.skeleton.tree → ℝ)
    (hD : DomF (layOf A) c0.U c0.a c0.b u)
    (hext : (layOf A c0.a : ℝ) < u c0.a ∧ u c0.a < layOf A c0.a + 1) :
    (zpQ4 A pstar : ℝ) < (botVars κ A c0 pstar x u).2.1 ∧ (botVars κ A c0 pstar x u).2.1 ≤ zpQ4 A pstar + 1 ∧
      (zpQ2 A pstar : ℝ) ≤ (botVars κ A c0 pstar x u).1 ∧ (botVars κ A c0 pstar x u).1 ≤ zpQ2 A pstar + 1 := by
  have hw := bot_win_of_domF A c0 u hD hext
  have hb00 := hw _ c0.block.2.2.1
  rw [hb0] at hb00
  refine ⟨?_, ?_, ?_, ?_⟩ <;> simp only [botVars, dictS1, hb0, zpQ4_eq_s1 A hr hq2 hM, zpQ2_eq_layOf]
  · by_cases hn : nuOf A pstar = 1
    · simp only [hn, if_true]; exact (hw _ (bot_qrOf_mem A c0 hb0)).1
    · simp only [hn, if_false]; exact (hw _ (bot_qbOf_mem A c0 hb0)).1
  · by_cases hn : nuOf A pstar = 1
    · simp only [hn, if_true]; exact (hw _ (bot_qrOf_mem A c0 hb0)).2.le
    · simp only [hn, if_false]; exact (hw _ (bot_qbOf_mem A c0 hb0)).2.le
  · exact hb00.1.le
  · exact hb00.2.le

end
end WaveTurbulence.VineEstS5C.P4.Bot
