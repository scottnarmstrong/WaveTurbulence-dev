/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.VineEst.VineEstS5C.P4.W13.WinLayers
public import WaveTurbulence.Foundations.VineEst.VineEstS5C.P4.W2.ExcBnd

/-! # P4-W2 (session 7, step 3j): the windows of the clocks of a record

`exc_windows`: if the clocks `u` of the lower joint `bj`, of `qb` and of `qr` lie in the open unit windows of their layers (`DomX`, `win_of_domX`), then
`t₀ = u bj ∈ (L₂, L₂+1)`, and, with `s₁ = dictS1 ν (u qb) (u qr)`, `t₁ = dictT1 ν (u qb) (u qr)`: `s₁ ∈ Wsel L₄ Lₕ (decide CaseA)` and `t₁ ∈ Wsel L₄ Lₕ (!decide CaseA)`
(case A: `t₁` in the `L₄`-window, `s₁` in the `Lₕ`-window; case M: the roles are exchanged), exactly the window hypotheses of `exc_dispatch_k01` / `exc_dispatch_k2`. -/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.VineEstS5C.P4.W2
open WaveTurbulence WaveTurbulence.Twist WaveTurbulence.LFTwist WaveTurbulence.VineEstS4 WaveTurbulence.VineEstS5B
  WaveTurbulence.VineEstS5C WaveTurbulence.VineEstS5C.P1 WaveTurbulence.VineEstS5C.P4 WaveTurbulence.VineEstS5C.P4.W13
  WaveTurbulence.ZpSurj WaveTurbulence.Reg.Skeleton WaveTurbulence.RegRed TTree WaveTurbulence.VineEstS5B

variable {w : ℕ} {ι : Type*} {pstar : ι} [Fintype ι] [DecidableEq ι]

open Classical in
theorem exc_windows (A : FamilyReconstruction w ι)
    (hq2 : zpQ2 A pstar ≤ layOf A (qrOf (A.family.placement pstar))) (u : GBranch A.skeleton.tree → ℝ)
    (hbj : (layOf A (A.family.placement pstar).lower : ℝ) < u (A.family.placement pstar).lower ∧
      u (A.family.placement pstar).lower < layOf A (A.family.placement pstar).lower + 1)
    (hqb : (layOf A (qbOf (A.family.placement pstar)) : ℝ) < u (qbOf (A.family.placement pstar)) ∧
      u (qbOf (A.family.placement pstar)) < layOf A (qbOf (A.family.placement pstar)) + 1)
    (hqr : (layOf A (qrOf (A.family.placement pstar)) : ℝ) < u (qrOf (A.family.placement pstar)) ∧
      u (qrOf (A.family.placement pstar)) < layOf A (qrOf (A.family.placement pstar)) + 1) :
    u (A.family.placement pstar).lower ∈ Set.Ioo (zpQ2 A pstar : ℝ) (zpQ2 A pstar + 1) ∧
    dictS1 (nuOf A pstar) (u (qbOf (A.family.placement pstar))) (u (qrOf (A.family.placement pstar))) ∈
      Wsel (zpQ4 A pstar : ℝ) (zpQh A pstar : ℝ) (decide (CaseA (pstar := pstar) A)) ∧
    dictT1 (nuOf A pstar) (u (qbOf (A.family.placement pstar))) (u (qrOf (A.family.placement pstar))) ∈
      Wsel (zpQ4 A pstar : ℝ) (zpQh A pstar : ℝ) (!decide (CaseA (pstar := pstar) A)) := by
  have hr := retParent (pstar := pstar) A
  have h0 : u (A.family.placement pstar).lower ∈ Set.Ioo (zpQ2 A pstar : ℝ) (zpQ2 A pstar + 1) := by
    rw [zpQ2_eq_layOf]; exact hbj
  refine ⟨h0, ?_⟩
  -- the node of s₁ and of t₁
  have hs1 : dictS1 (nuOf A pstar) (u (qbOf (A.family.placement pstar))) (u (qrOf (A.family.placement pstar))) =
      u (if nuOf A pstar = 1 then qrOf (A.family.placement pstar) else qbOf (A.family.placement pstar)) := by
    unfold dictS1; split_ifs <;> rfl
  have ht1 : dictT1 (nuOf A pstar) (u (qbOf (A.family.placement pstar))) (u (qrOf (A.family.placement pstar))) =
      u (if nuOf A pstar = 1 then qbOf (A.family.placement pstar) else qrOf (A.family.placement pstar)) := by
    unfold dictT1; split_ifs <;> rfl
  have hws : (layOf A (if nuOf A pstar = 1 then qrOf (A.family.placement pstar) else qbOf (A.family.placement pstar)) : ℝ) <
        u (if nuOf A pstar = 1 then qrOf (A.family.placement pstar) else qbOf (A.family.placement pstar)) ∧
      u (if nuOf A pstar = 1 then qrOf (A.family.placement pstar) else qbOf (A.family.placement pstar)) <
        layOf A (if nuOf A pstar = 1 then qrOf (A.family.placement pstar) else qbOf (A.family.placement pstar)) + 1 := by
    split_ifs
    · exact hqr
    · exact hqb
  have hwt : (layOf A (if nuOf A pstar = 1 then qbOf (A.family.placement pstar) else qrOf (A.family.placement pstar)) : ℝ) <
        u (if nuOf A pstar = 1 then qbOf (A.family.placement pstar) else qrOf (A.family.placement pstar)) ∧
      u (if nuOf A pstar = 1 then qbOf (A.family.placement pstar) else qrOf (A.family.placement pstar)) <
        layOf A (if nuOf A pstar = 1 then qbOf (A.family.placement pstar) else qrOf (A.family.placement pstar)) + 1 := by
    split_ifs
    · exact hqb
    · exact hqr
  rw [hs1, ht1]
  by_cases hA : CaseA (pstar := pstar) A
  · have e4 := zpQ4_eq_t1 A hr hq2 hA
    have eh := layer_s1_caseA A hA
    simp only [hA, decide_true, Bool.not_true, Wsel, if_true, if_false]
    refine ⟨?_, ?_⟩
    · rw [← eh]; exact hws
    · rw [e4]; exact hwt
  · have hM : CaseM (pstar := pstar) A := (caseA_or_caseM A).resolve_left hA
    have e4 := zpQ4_eq_s1 A hr hq2 hM
    have eh := layer_t1_caseM A hM
    simp only [hA, decide_false, Bool.not_false, Wsel, if_true, if_false]
    refine ⟨?_, ?_⟩
    · rw [e4]; exact hws
    · rw [← eh]; exact hwt

end WaveTurbulence.VineEstS5C.P4.W2
