/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Molecule.SkeletonDraft.RawPartner

/-! # Strict termination measure for the source skeleton reductions -/

public section
namespace WaveTurbulence.Reg.Skeleton
open TTree

theorem mini_order (m : MiniTreeCode) (S : TTree) :
    (node3 fun i => if i = m.c then node3 (fun j => if j = m.lone then S else .leaf) else .leaf).order =
      S.order + 2 := by
  obtain ⟨c,b⟩ := m
  fin_cases c <;> fin_cases b <;> simp [node3,MiniTreeCode.lone,TTree.order]

/-- Every permitted B expansion adds precisely its two mini-tree branching nodes. -/
theorem Raw.opB_order {w : ℕ} (R : Raw w) (a : Address w) (m : MiniTreeCode)
    (ha : a.2 ∈ (R.tree a.1).nodes) : (R.opB a m).order = R.order + 2 := by
  let A : GNode R.tree := ⟨a,ha⟩
  let S := (R.tree a.1).subtreeAt a.2
  let mini := node3 fun i => if i = m.c then node3 (fun j => if j = m.lone then S else .leaf) else .leaf
  have ht : (R.opB a m).tree = Comb.replaceNodeForest R.tree A mini := by
    funext j
    simp only [Raw.opB,Comb.replaceNodeForest,setAt_eq_replaceAt]
    rfl
  have ho := Comb.replaceNodeForest_order R.tree A mini
  have hs : S = Comb.nodeSubtree A := subtreeAt_eq_of_subtree _ _ _ (Comb.nodeSubtree_spec A)
  have hm : mini.order = S.order+2 := mini_order m S
  rw [hm,← hs,← ht] at ho
  change (R.opB a m).order + S.order = R.order + (S.order+2) at ho
  omega

/-- Every permitted A expansion adds precisely its two mini-couple branching nodes. -/
theorem Raw.opA_order {w : ℕ} (R : Raw w) (hR : R.Valid) (x y : Address w) (c : MiniCplCode)
    (hp : (x,y) ∈ R.pairs) : (R.opA x y c).order = R.order + 2 := by
  have hv := hR.1 _ hp
  let ℓ : GLeaf R.tree := ⟨x,hv.1⟩
  let q : GLeaf R.tree := ⟨y,hv.2.1⟩
  have hn : q ≠ ℓ := by
    intro h
    exact valid_pair_ne R hR _ hp (congrArg Subtype.val h).symm
  let t := TTree.node .leaf .leaf .leaf
  have ht : (R.opA x y c).tree = Comb.graftLeafPairForest R.tree ℓ q hn t t := by
    funext j
    simp only [Raw.opA,Comb.graftLeafPairForest,Comb.graftLeafForest,
      Comb.graftLeafForest_other,setAt_eq_replaceAt]
    rfl
  have ho := Comb.graftLeafPairForest_order R.tree ℓ q hn t t
  rw [← ht] at ho
  change (R.opA x y c).order = R.order + 1 + 1 at ho
  omega

/-- Every inverse source move strictly lowers branching order. -/
theorem Expand.order {w : ℕ} {S R : Raw w} (h : Expand S R) : R.order = S.order + 2 := by
  cases h with
  | opA x y c hS hp => exact Raw.opA_order _ hS x y c hp
  | opB a m _ ha => exact Raw.opB_order _ a m ha

end WaveTurbulence.Reg.Skeleton
