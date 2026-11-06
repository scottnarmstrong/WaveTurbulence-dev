/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Molecule.SkeletonDraft.PairMembership
public import WaveTurbulence.Foundations.Molecule.SkeletonDraft.ReconstructionForest

/-! # The exact source mini shape created by a guarded raw B expansion -/

@[expose] public section
namespace WaveTurbulence.Reg.Skeleton
open TTree

/-- A literal extracted branching subtree gives an actual source branch at the same address. -/
def branchOfExtraction {w : ℕ} (tree : Fin w → TTree) (a : Address w) (f : Fin 3 → TTree)
    (hs : Comb.subtree (tree a.1) a.2 = some (node3 f)) : GBranch tree :=
  ⟨a,by
    have hb := (Comb.subtree_branching_iff hs []).mp (by simp [node3,TTree.branching])
    simpa only [List.append_nil] using hb⟩

theorem Raw.opB_subtree {w : ℕ} (R : Raw w) (a : Address w) (m : MiniTreeCode)
    (ha : a.2 ∈ (R.tree a.1).nodes) :
    Comb.subtree ((R.opB a m).tree a.1) a.2 =
      some (miniTreeContext m ((R.tree a.1).subtreeAt a.2)) := by
  let A : GNode R.tree := ⟨a,ha⟩
  change Comb.subtree (Function.update R.tree a.1
    ((R.tree a.1).setAt a.2 (miniTreeContext m ((R.tree a.1).subtreeAt a.2))) a.1) a.2 = _
  rw [Function.update_self,setAt_eq_replaceAt]
  exact Comb.subtree_replaceAt (Comb.nodeSubtree_spec A) _

theorem miniContext_subtree_continuing (m : MiniTreeCode) (S : TTree) :
    Comb.subtree (miniTreeContext m S) [m.c] =
      some (node3 (fun j => if j = m.lone then S else .leaf)) := by
  obtain ⟨c,b⟩ := m
  fin_cases c <;> simp [miniTreeContext,node3,Comb.subtree]

/-- Both branching nodes created by a raw B insertion are actual target branches at the literal addresses. -/
theorem branches_of_raw_opB {w : ℕ} (R : Raw w) (G : Garden w) (a : Address w) (m : MiniTreeCode)
    (ha : a.2 ∈ (R.tree a.1).nodes) (he : rawOfGarden G = R.opB a m) :
    ∃ b c : GBranch G.tree, b.1 = a ∧ c.1 = addrExt a [m.c] ∧ b.child m.c = c.toNode := by
  let S := (R.tree a.1).subtreeAt a.2
  have ht : G.tree = (R.opB a m).tree := congrArg Raw.tree he
  have hu : Comb.subtree (G.tree a.1) a.2 = some (miniTreeContext m S) := by
    rw [ht]
    exact R.opB_subtree a m ha
  let b : GBranch G.tree := branchOfExtraction G.tree a _ hu
  have hv : Comb.subtree (G.tree a.1) (a.2 ++ [m.c]) =
      some (node3 (fun j => if j = m.lone then S else .leaf)) := by
    rw [Comb.subtree_append,hu]
    exact miniContext_subtree_continuing m S
  let c : GBranch G.tree := branchOfExtraction G.tree (addrExt a [m.c]) _ hv
  exact ⟨b,c,rfl,rfl,Subtype.ext rfl⟩

end WaveTurbulence.Reg.Skeleton
