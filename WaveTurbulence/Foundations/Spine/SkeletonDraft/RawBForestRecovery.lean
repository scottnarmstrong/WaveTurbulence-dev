/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Spine.SkeletonDraft.ForwardBShape
public import WaveTurbulence.Foundations.Spine.SkeletonDraft.RawBPairRecovery

/-! # Exact forest inverse and injectivity of a guarded raw B insertion -/

public section
namespace WaveTurbulence.Reg.Skeleton
open TTree

theorem miniContext_subtree_lone (m : MiniTreeCode) (S : TTree) :
    Comb.subtree (miniTreeContext m S) [m.c,m.lone] = some S := by
  obtain ⟨c,b⟩ := m
  fin_cases c <;> fin_cases b <;> simp [miniTreeContext,node3,MiniTreeCode.lone,Comb.subtree]

theorem Raw.opB_forest_restore {w : ℕ} (R : Raw w) (a : Address w) (m : MiniTreeCode)
    (ha : a.2 ∈ (R.tree a.1).nodes) :
    Function.update (R.opB a m).tree a.1
      (Comb.replaceAt ((R.opB a m).tree a.1) a.2
        (((R.opB a m).tree a.1).subtreeAt (a.2 ++ [m.c,m.lone]))) = R.tree := by
  let A : GNode R.tree := ⟨a,ha⟩
  let S := (R.tree a.1).subtreeAt a.2
  have hs : Comb.subtree ((R.opB a m).tree a.1) (a.2 ++ [m.c,m.lone]) = some S := by
    rw [Comb.subtree_append,R.opB_subtree a m ha]
    exact miniContext_subtree_lone m S
  have ht := subtreeAt_eq_of_subtree _ _ _ hs
  have hS : S = Comb.nodeSubtree A := subtreeAt_eq_of_subtree _ _ _ (Comb.nodeSubtree_spec A)
  funext j
  by_cases hj : j = a.1
  · subst j
    rw [Function.update_self,ht]
    simp only [Raw.opB,Function.update_self,setAt_eq_replaceAt]
    change Comb.replaceAt (Comb.replaceAt (R.tree a.1) a.2 (miniTreeContext m S)) a.2 S = R.tree a.1
    rw [Comb.replaceAt_replaceAt (Comb.nodeSubtree_spec A),hS,
      Comb.replaceAt_self (Comb.nodeSubtree_spec A)]
  · rw [Function.update_of_ne hj]
    change Function.update R.tree a.1 _ j = R.tree j
    exact Function.update_of_ne hj _ _

theorem Raw.opB_tree_injective {w : ℕ} (R T : Raw w) (a : Address w) (m : MiniTreeCode)
    (hR : a.2 ∈ (R.tree a.1).nodes) (hT : a.2 ∈ (T.tree a.1).nodes)
    (he : R.opB a m = T.opB a m) : R.tree = T.tree := by
  have ht := congrArg (fun U : Raw w => Function.update U.tree a.1
    (Comb.replaceAt (U.tree a.1) a.2 ((U.tree a.1).subtreeAt (a.2 ++ [m.c,m.lone])))) he
  exact (R.opB_forest_restore a m hR).symm.trans (ht.trans (T.opB_forest_restore a m hT))

/-- A guarded B insertion is injective on complete literal source data. -/
theorem Raw.opB_injective_at {w : ℕ} (R T : Raw w) (a : Address w) (m : MiniTreeCode)
    (hR : a.2 ∈ (R.tree a.1).nodes) (hT : a.2 ∈ (T.tree a.1).nodes)
    (he : R.opB a m = T.opB a m) : R = T := by
  apply Raw.ext
  · have hs := congrArg Raw.sig he
    exact hs
  · exact Raw.opB_tree_injective R T a m hR hT he
  · exact Raw.opB_pairs_injective R T a m he

end WaveTurbulence.Reg.Skeleton
