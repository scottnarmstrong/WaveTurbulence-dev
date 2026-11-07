/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.VineEst.RegRedDraft.PairedTreeLowerClock
public import WaveTurbulence.Foundations.VineEst.RegRedDraft.RelativeDecorations

/-! # Original skeleton parent clocks are the exterior clocks of native kernels -/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.RegRed
open TTree Reg Reg.Skeleton

noncomputable def nativeCoreClock {w : ℕ} {S : Garden w} (D : ReconstructionData S)
    (hS : S.IsPlain) (τ : GBranch (D.forest hS) → ℝ) : GBranch S.tree → ℝ :=
  fun b => τ (D.coreBranch hS b)

noncomputable def nativeCoupleClock {w : ℕ} {S : Garden w} (D : ReconstructionData S)
    (hS : S.IsPlain) (τ : GBranch (D.forest hS) → ℝ) (p : SourcePair S) :
    GBranch (nativeCoupleGarden D hS p).tree → ℝ := fun q => τ (coupleContextBranch D hS p q)

noncomputable def nativeCoupleUpper {w : ℕ} {S : Garden w} (D : ReconstructionData S)
    (hS : S.IsPlain) (top : ℝ) (τ : GBranch S.tree → ℝ) (p : SourcePair S) : Fin 2 → ℝ :=
  ![parentClock top τ (p.firstLeaf hS).toNode,parentClock top τ (p.secondLeaf hS).toNode]

theorem couple_parentClock {w : ℕ} {S : Garden w} (D : ReconstructionData S)
    (hS : S.IsPlain) (top : ℝ) (τ : GBranch (D.forest hS) → ℝ) (p : SourcePair S)
    (a : GNode (nativeCoupleGarden D hS p).tree) :
    parentClock top τ ((nativeCoupleForest D hS p).nodeEmbedding a) =
      parentClockWith (nativeCoupleUpper D hS top (nativeCoreClock D hS τ) p)
        (nativeCoupleClock D hS τ p) a := by
  have h := subforest_parentClock (nativeCoupleForest D hS p) top τ a
  have hr : (fun j => parentClock top τ ((nativeCoupleForest D hS p).root j)) =
      nativeCoupleUpper D hS top (nativeCoreClock D hS τ) p := by
    funext j
    fin_cases j
    · exact parentClock_attachedNode D hS top τ (p.firstLeaf hS).toNode
    · exact parentClock_attachedNode D hS top τ (p.secondLeaf hS).toNode
  rw [hr] at h
  exact h

/-- The inherited core times lie in the source skeleton domain. This uses actual
ancestor order through the inserted trees, not an assumed skeleton inequality. -/
theorem fullTimeDomain_core {w : ℕ} {S : Garden w} (D : ReconstructionData S)
    (hS : S.IsPlain) (layer : GNode (D.forest hS) → ℕ) (top : ℝ)
    (τ : GBranch (D.forest hS) → ℝ)
    (hτ : τ ∈ coreTimeDomain (fun b => layer b.toNode) top) :
    nativeCoreClock D hS τ ∈ coreTimeDomain (fun b => layer (D.coreBranch hS b).toNode) top := by
  intro b
  refine ⟨(hτ (D.coreBranch hS b)).1,(hτ (D.coreBranch hS b)).2.1,
    (hτ (D.coreBranch hS b)).2.2.1,?_⟩
  have hd : (attachedNode D hS b.toNode).IsDesc (D.coreBranch hS b).toNode :=
    ⟨rfl,List.prefix_append _ _⟩
  have ht := branchTime_lt_parentClock_of_desc top τ (fun b => (hτ b).2.2.2)
    (attachedNode D hS b.toNode) (D.coreBranch hS b) hd
  exact lt_of_lt_of_eq ht (parentClock_attachedNode D hS top τ b.toNode)

end WaveTurbulence.RegRed
