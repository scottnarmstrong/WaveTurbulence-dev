/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.VineEst.VineEstS5C.P4.Mirror
public import WaveTurbulence.Foundations.VineEst.VineEstS3.BadClauseD
public import WaveTurbulence.Foundations.VineEst.VineEstS5C.LevelLoc

/-! # P4: the windows of the bundle from the frame domain `DomF` (V5 Step 4d part C, `hWin`)

`bundleFrame ≠ 0` forces `DomF` (the spartFrame indicator): the clocks of the interior branches of the S-region lie in their unit layer windows.
For the three branches `b` (lower joint), `qb`, `qr` this gives the windows `t₀ ∈ (L₂, L₂+1)`, and `t₁`, `s₁ ∈ (layer, layer+1)` of their nodes.
Exterior clock: if one of them is the top joint `a` of the region, its window is the hypothesis `hext` (for the top level the exterior clock `tt 0`,
which lies in the CLOSED box, so strictness holds only off the boundary: see `P4.Final`).
`zpQ4_eq_t1` / `zpQ4_eq_s1`: in the static layer case (TARGET `L_{u4} ≤ L_{u3}` resp. its mirror), `zpQ4` is the layer of the node of `t₁` resp. `s₁`.
-/

@[expose] public section
variable {rowSelU : Unit} [rowSel : WaveTurbulence.VineEst.RowSel rowSelU]
set_option autoImplicit false
open WaveTurbulence.Induct
open WaveTurbulence.VineParamContract
namespace WaveTurbulence.VineEstS5C.P4
open WaveTurbulence WaveTurbulence.Twist WaveTurbulence.LFTwist WaveTurbulence.VineEstS4 WaveTurbulence.VineEstS5B
  WaveTurbulence.Links WaveTurbulence.Reg.Skeleton WaveTurbulence.RegRed WaveTurbulence.LGSpine TTree
  WaveTurbulence.VineEstS4c WaveTurbulence.VineEstS5C WaveTurbulence.VineEstS5C.P1

set_option linter.unusedSectionVars false
section
variable {w : ℕ} {ι : Type*} {p : ℕ} {pstar : ι} {J : Set ι} {d : ℕ} [Fintype ι] [DecidableEq ι]

/-- The layer of the core branch of a branch, in the state `A`. -/
noncomputable def layOf (A : FamilyReconstruction w ι) (v : GBranch A.skeleton.tree) : ℕ :=
  stateLayer A (A.data.coreBranch A.plain v).toNode

theorem zpQ2_eq_layOf (A : FamilyReconstruction w ι) :
    zpQ2 A pstar = layOf A (A.family.placement pstar).lower := rfl

theorem zpBranchQ_fst (A : FamilyReconstruction w ι) :
    (zpBranchQ A pstar).1 = layOf A (qbOf (A.family.placement pstar)) := by
  unfold zpBranchQ branchQ parentCoreLayer qbOf layOf
  exact dif_neg (A.family.placement pstar).nonroot

/-- `bundleFrame ≠ 0` forces the frame domain. -/
theorem domF_of_frame_ne (κ : KPar d) (A : FamilyReconstruction w ι) (sp : SplitAt A.skeleton A.family pstar J)
    (x : GNode A.skeleton.tree → (Fin d → ℤ)) (u : GBranch A.skeleton.tree → ℝ) (h : bundleFrame κ A sp x u ≠ 0) :
    DomF (layOf A) sp.sb.U sp.sb.a sp.sb.b u := by
  classical
  by_contra hD
  apply h
  unfold bundleFrame spartFrame
  have hD' : ¬ DomF (fun v => stateLayer A (A.data.coreBranch A.plain v).toNode) sp.sb.U sp.sb.a sp.sb.b u := hD
  rw [if_neg hD', zero_mul]

/-- The windows of all branches of the S-region (given the window of the exterior clock `u a`). -/
theorem win_of_domF (A : FamilyReconstruction w ι) (sp : SplitAt A.skeleton A.family pstar J) (u : GBranch A.skeleton.tree → ℝ)
    (hD : DomF (layOf A) sp.sb.U sp.sb.a sp.sb.b u)
    (hext : (layOf A sp.sb.a : ℝ) < u sp.sb.a ∧ u sp.sb.a < layOf A sp.sb.a + 1) :
    ∀ v ∈ sp.sb.U, (layOf A v : ℝ) < u v ∧ u v < layOf A v + 1 := by
  intro v hv
  by_cases hva : v = sp.sb.a
  · subst hva; exact hext
  · exact ⟨(hD v (Finset.mem_erase.mpr ⟨hva, hv⟩)).1, (hD v (Finset.mem_erase.mpr ⟨hva, hv⟩)).2.1⟩

variable (A : FamilyReconstruction w ι)

/-- The parent layer of the retained leaf (its parent is the lower joint). -/
def RetParent : Prop :=
  parentCoreLayer A.data A.plain (stateLayer A) (A.family.placement pstar).retained.toNode = zpQ2 A pstar

/-- The static layer case A (TARGET `L_{u4} ≤ L_{u3}`): the node of `t₁` has the lower layer. -/
def CaseA : Prop :=
  layOf A (if nuOf A pstar = 1 then qbOf (A.family.placement pstar) else qrOf (A.family.placement pstar)) ≤
    layOf A (if nuOf A pstar = 1 then qrOf (A.family.placement pstar) else qbOf (A.family.placement pstar))


theorem parentCore_partner (A : FamilyReconstruction w ι) :
    parentCoreLayer A.data A.plain (stateLayer A) (A.skeleton.pair (A.family.placement pstar).retained).toNode =
      layOf A (qrOf (A.family.placement pstar)) := by
  unfold parentCoreLayer qrOf layOf
  exact dif_neg (A.family.placement pstar).paired_nonroot

theorem pairQ_max (A : FamilyReconstruction w ι) (hr : RetParent (pstar := pstar) A) :
    max (zpPairQ A pstar).1 (zpPairQ A pstar).2 = max (zpQ2 A pstar) (layOf A (qrOf (A.family.placement pstar))) := by
  unfold zpPairQ pairQ
  have h2 := pair_first_eq_second A.plain (pairOfLeaf A.skeleton A.plain (A.family.placement pstar).retained)
  rcases WaveTurbulence.VineEstS3.firstLeaf_pairOfLeaf A.plain (A.family.placement pstar).retained with h | h
  · rw [← h2, h]
    simp only
    rw [hr, parentCore_partner]
  · rw [← h2, h]
    simp only
    rw [parentCore_partner, A.skeleton.pair_pair]
    rw [hr, max_comm]

/-- `zpQ4 = min (max L₂ layer(qr)) layer(qb)`. -/
theorem zpQ4_eq (A : FamilyReconstruction w ι) (hr : RetParent (pstar := pstar) A) :
    zpQ4 A pstar = min (max (zpQ2 A pstar) (layOf A (qrOf (A.family.placement pstar))))
      (layOf A (qbOf (A.family.placement pstar))) := by
  unfold zpQ4
  rw [pairQ_max A hr, zpBranchQ_fst]

/-- Case A: `zpQ4` is the layer of the node of the clock `t₁`. -/
theorem zpQ4_eq_t1 (A : FamilyReconstruction w ι) (hr : RetParent (pstar := pstar) A)
    (hq2 : zpQ2 A pstar ≤ layOf A (qrOf (A.family.placement pstar))) (hA : CaseA (pstar := pstar) A) :
    zpQ4 A pstar = layOf A (if nuOf A pstar = 1 then qbOf (A.family.placement pstar) else qrOf (A.family.placement pstar)) := by
  rw [zpQ4_eq A hr]
  unfold CaseA at hA
  by_cases hn : nuOf A pstar = 1
  · simp only [hn, if_true] at hA ⊢
    exact min_eq_right (hA.trans (le_max_right _ _))
  · simp only [hn, if_false] at hA ⊢
    rw [max_eq_right hq2]; exact min_eq_left hA

/-- The static layer case M (mirror): the node of `s₁` has the lower layer. -/
def CaseM : Prop :=
  layOf A (if nuOf A pstar = 1 then qrOf (A.family.placement pstar) else qbOf (A.family.placement pstar)) ≤
    layOf A (if nuOf A pstar = 1 then qbOf (A.family.placement pstar) else qrOf (A.family.placement pstar))

/-- Case M: `zpQ4` is the layer of the node of the clock `s₁`. -/
theorem zpQ4_eq_s1 (A : FamilyReconstruction w ι) (hr : RetParent (pstar := pstar) A)
    (hq2 : zpQ2 A pstar ≤ layOf A (qrOf (A.family.placement pstar))) (hM : CaseM (pstar := pstar) A) :
    zpQ4 A pstar = layOf A (if nuOf A pstar = 1 then qrOf (A.family.placement pstar) else qbOf (A.family.placement pstar)) := by
  rw [zpQ4_eq A hr]
  unfold CaseM at hM
  by_cases hn : nuOf A pstar = 1
  · simp only [hn, if_true] at hM ⊢
    rw [max_eq_right hq2]; exact min_eq_left hM
  · simp only [hn, if_false] at hM ⊢
    exact min_eq_right (hM.trans (le_max_right _ _))

/-- One of the two static cases always holds. -/
theorem caseA_or_caseM (A : FamilyReconstruction w ι) : CaseA (pstar := pstar) A ∨ CaseM (pstar := pstar) A := by
  unfold CaseA CaseM
  exact le_total _ _

/-- **The windows, case A** (`bundle_decomp` hypotheses) from the frame domain and the exterior window. -/
theorem window_caseA (κ : KPar d) (A : FamilyReconstruction w ι) (sp : SplitAt A.skeleton A.family pstar J)
    (hr : RetParent (pstar := pstar) A) (hq2 : zpQ2 A pstar ≤ layOf A (qrOf (A.family.placement pstar)))
    (hA : CaseA (pstar := pstar) A) (x : GNode A.skeleton.tree → (Fin d → ℤ)) (u : GBranch A.skeleton.tree → ℝ)
    (hD : DomF (layOf A) sp.sb.U sp.sb.a sp.sb.b u)
    (hext : (layOf A sp.sb.a : ℝ) < u sp.sb.a ∧ u sp.sb.a < layOf A sp.sb.a + 1) :
    (zpQ4 A pstar : ℝ) < (bundleVars κ A sp x u).2.2.1 ∧ (bundleVars κ A sp x u).2.2.1 ≤ zpQ4 A pstar + 1 ∧
      (zpQ2 A pstar : ℝ) ≤ (bundleVars κ A sp x u).1 ∧ (bundleVars κ A sp x u).1 ≤ zpQ2 A pstar + 1 := by
  have hw := win_of_domF A sp u hD hext
  have hb : sp.sb.b = (A.family.placement pstar).lower := sp.joint.trans sp.bk
  have hb0 := hw _ sp.sb.block.2.2.1
  rw [hb] at hb0
  refine ⟨?_, ?_, ?_, ?_⟩ <;> simp only [bundleVars, dictT1, hb, zpQ4_eq_t1 A hr hq2 hA, zpQ2_eq_layOf]
  · by_cases hn : nuOf A pstar = 1
    · simp only [hn, if_true]; exact (hw _ (qbOf_mem A sp)).1
    · simp only [hn, if_false]; exact (hw _ (qrOf_mem A sp)).1
  · by_cases hn : nuOf A pstar = 1
    · simp only [hn, if_true]; exact (hw _ (qbOf_mem A sp)).2.le
    · simp only [hn, if_false]; exact (hw _ (qrOf_mem A sp)).2.le
  · exact hb0.1.le
  · exact hb0.2.le

/-- **The windows, case M** (`bundle_decomp_mirror` hypotheses). -/
theorem window_caseM (κ : KPar d) (A : FamilyReconstruction w ι) (sp : SplitAt A.skeleton A.family pstar J)
    (hr : RetParent (pstar := pstar) A) (hq2 : zpQ2 A pstar ≤ layOf A (qrOf (A.family.placement pstar)))
    (hM : CaseM (pstar := pstar) A) (x : GNode A.skeleton.tree → (Fin d → ℤ)) (u : GBranch A.skeleton.tree → ℝ)
    (hD : DomF (layOf A) sp.sb.U sp.sb.a sp.sb.b u)
    (hext : (layOf A sp.sb.a : ℝ) < u sp.sb.a ∧ u sp.sb.a < layOf A sp.sb.a + 1) :
    (zpQ4 A pstar : ℝ) < (bundleVars κ A sp x u).2.1 ∧ (bundleVars κ A sp x u).2.1 ≤ zpQ4 A pstar + 1 ∧
      (zpQ2 A pstar : ℝ) ≤ (bundleVars κ A sp x u).1 ∧ (bundleVars κ A sp x u).1 ≤ zpQ2 A pstar + 1 := by
  have hw := win_of_domF A sp u hD hext
  have hb : sp.sb.b = (A.family.placement pstar).lower := sp.joint.trans sp.bk
  have hb0 := hw _ sp.sb.block.2.2.1
  rw [hb] at hb0
  refine ⟨?_, ?_, ?_, ?_⟩ <;> simp only [bundleVars, dictS1, hb, zpQ4_eq_s1 A hr hq2 hM, zpQ2_eq_layOf]
  · by_cases hn : nuOf A pstar = 1
    · simp only [hn, if_true]; exact (hw _ (qrOf_mem A sp)).1
    · simp only [hn, if_false]; exact (hw _ (qbOf_mem A sp)).1
  · by_cases hn : nuOf A pstar = 1
    · simp only [hn, if_true]; exact (hw _ (qrOf_mem A sp)).2.le
    · simp only [hn, if_false]; exact (hw _ (qbOf_mem A sp)).2.le
  · exact hb0.1.le
  · exact hb0.2.le

theorem retParent (A : FamilyReconstruction w ι) : RetParent (pstar := pstar) A := by
  unfold RetParent parentCoreLayer zpQ2 zpBranchQ branchQ
  refine (dif_neg (retained_nonroot A.skeleton (A.family.placement pstar))).trans ?_
  have h : ∀ (x : GNode A.skeleton.tree) (hx : x.1.2 ≠ []) (hq : x = (A.family.placement pstar).lower.child (A.family.placement pstar).keep),
      x.parent hx = (A.family.placement pstar).lower := fun x hx hq => by
    subst hq; exact parent_child _ _
  exact congrArg (fun v => stateLayer A (A.data.coreBranch A.plain v).toNode) (h _ _ (A.family.placement pstar).child)

end
end WaveTurbulence.VineEstS5C.P4
