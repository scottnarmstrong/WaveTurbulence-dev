/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Spine.SkeletonDraft.MiniBCollapse
public import WaveTurbulence.Foundations.Molecule.SkeletonDraft.CollapseBranchLabels

/-! # The only removed branches of an actual B mini are its upper and lower mini roots -/

public section
namespace WaveTurbulence.Reg.Skeleton
open TTree

/-- Every other branching address of a filled mini lies below its lone slot. -/
theorem miniContext_branch_cases (m : MiniTreeCode) (S : TTree) (p : Path)
    (hp : p ∈ (miniTreeContext m S).branching) :
    p = [] ∨ p = [m.c] ∨ [m.c,m.lone] <+: p := by
  cases p with
  | nil => exact Or.inl rfl
  | cons i p =>
    by_cases hi : i = m.c
    · subst i
      cases p with
      | nil => exact Or.inr (Or.inl rfl)
      | cons j p =>
        have hj : j = m.lone := by
          obtain ⟨c,b⟩ := m
          fin_cases c <;> fin_cases b <;> fin_cases j <;>
            simp [miniTreeContext,node3,MiniTreeCode.lone,TTree.branching,TTree.pre] at hp ⊢
        subst j
        exact Or.inr (Or.inr (by simp))
    · have hfalse : False := by
        obtain ⟨c,b⟩ := m
        fin_cases c <;> fin_cases b <;> fin_cases i <;>
          simp [MiniTreeCode.c] at hi <;>
          simp [miniTreeContext,node3,MiniTreeCode.lone,TTree.branching,TTree.pre] at hp
      exact hfalse.elim

end WaveTurbulence.Reg.Skeleton
