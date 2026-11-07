/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.VineEst.RegRedDraft.DescendantClocks
public import WaveTurbulence.Foundations.VineEst.RegRedDraft.NativeSigns

/-! # Literal incoming parent clocks on the actual native regular pieces -/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.RegRed
open TTree Reg Reg.Skeleton

def parentClockWith {w : ℕ} {tree : Fin w → TTree} (top : Fin w → ℝ)
    (τ : GBranch tree → ℝ) (a : GNode tree) : ℝ :=
  match nodeToSlot a with
  | .inl j => top j
  | .inr (b,_) => τ b

theorem parentClockWith_root {w : ℕ} (tree : Fin w → TTree) (top : Fin w → ℝ)
    (τ : GBranch tree → ℝ) (j : Fin w) : parentClockWith top τ (GNode.root tree j) = top j := rfl

theorem parentClockWith_child {w : ℕ} {tree : Fin w → TTree} (top : Fin w → ℝ)
    (τ : GBranch tree → ℝ) (b : GBranch tree) (i : Fin 3) :
    parentClockWith top τ (b.child i) = τ b := by
  rw [parentClockWith,nodeToSlot_child]

theorem parentClockWith_const {w : ℕ} {tree : Fin w → TTree} (top : ℝ)
    (τ : GBranch tree → ℝ) (a : GNode tree) : parentClockWith (fun _ => top) τ a = parentClock top τ a := rfl

theorem subforest_parentClock {w v : ℕ} {tree : Fin w → TTree} (E : Comb.RootedSubforest tree v)
    (top : ℝ) (τ : GBranch tree → ℝ) (a : GNode E.shape) :
    parentClock top τ (E.nodeEmbedding a) =
      parentClockWith (fun j => parentClock top τ (E.root j))
        (fun b => τ (subforestBranchEmbedding E b)) a := by
  obtain ⟨s,rfl⟩ := (nodeSlotEquiv E.shape).symm.surjective a
  rcases s with j | ⟨b,i⟩
  · exact congrArg (parentClock top τ) (subforest_node_root E j)
  · exact (congrArg (parentClock top τ) (subforest_node_child E b i)).trans
      ((parentClock_child top τ _ i).trans (parentClockWith_child (fun j => parentClock top τ (E.root j))
        (fun b => τ (subforestBranchEmbedding E b)) b i).symm)

noncomputable def nativeChainClock {w : ℕ} {S : Garden w} (D : ReconstructionData S)
    (hS : S.IsPlain) (τ : GBranch (D.forest hS) → ℝ) (b : GBranch S.tree) :
    GBranch (decodedTree (D.tree b) (nodeSign S.sig b.1)).tree → ℝ :=
  fun q => τ (chainContextBranch D hS b ⟨q.1.2,q.2⟩)

theorem chain_parentClock {w : ℕ} {S : Garden w} (D : ReconstructionData S)
    (hS : S.IsPlain) (top : ℝ) (τ : GBranch (D.forest hS) → ℝ) (b : GBranch S.tree)
    (a : GNode (decodedTree (D.tree b) (nodeSign S.sig b.1)).tree) :
    parentClock top τ (chainContextNode D hS b a) =
      parentClock (parentClock top (fun b => τ (D.coreBranch hS b)) b.toNode)
        (nativeChainClock D hS τ b) a := by
  obtain ⟨s,rfl⟩ := (nodeSlotEquiv (decodedTree (D.tree b) (nodeSign S.sig b.1)).tree).symm.surjective a
  rcases s with j | ⟨q,i⟩
  · fin_cases j
    exact (congrArg (parentClock top τ) (chainContextNode_root D hS b)).trans
      (parentClock_attachedNode D hS top τ b.toNode)
  · exact (congrArg (parentClock top τ) (chainContextNode_child D hS b q i)).trans
      ((parentClock_child top τ _ i).trans (parentClock_child _ (nativeChainClock D hS τ b) q i).symm)

theorem core_parentClock_as_chain_lone {w : ℕ} {S : Garden w} (D : ReconstructionData S)
    (hS : S.IsPlain) (top : ℝ) (τ : GBranch (D.forest hS) → ℝ) (b : GBranch S.tree) :
    parentClock top τ (D.coreBranch hS b).toNode =
      parentClock (parentClock top (fun b => τ (D.coreBranch hS b)) b.toNode)
        (nativeChainClock D hS τ b) (chainLoneLeaf (D.tree b) (nodeSign S.sig b.1)).toNode :=
  (congrArg (parentClock top τ) (chainContextNode_lone D hS b)).symm.trans
    (chain_parentClock D hS top τ b _)

end WaveTurbulence.RegRed
