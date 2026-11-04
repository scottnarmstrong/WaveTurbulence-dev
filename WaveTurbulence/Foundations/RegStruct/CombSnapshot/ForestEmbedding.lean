/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.RegStruct.CombSnapshot.Subtrees
public import WaveTurbulence.Foundations.RegStruct.CombSnapshot.LeafPullback

/-! # Extracting incomparable rooted subforests (TARGET L636, L845–L847) -/

public section

namespace WaveTurbulence.Comb
open TTree Finset

/-- Actual rooted subtrees, with pairwise incomparable roots in the ambient forest. -/
structure RootedSubforest {w : ℕ} (tree : Fin w → TTree) (v : ℕ) where
  root : Fin v → GNode tree
  shape : Fin v → TTree
  subtree_eq : ∀ i, subtree (tree (root i).1.1) (root i).1.2 = some (shape i)
  incomparable : ∀ i j, i ≠ j → (root i).Incomparable (root j)

variable {w v : ℕ} {tree : Fin w → TTree}

/-- Embedding the nodes of an actual rooted subforest by prefixing addresses. -/
@[expose] def RootedSubforest.nodeEmbedding (E : RootedSubforest tree v) :
    GNode E.shape ↪ GNode tree where
  toFun a := ⟨((E.root a.1.1).1.1, (E.root a.1.1).1.2 ++ a.1.2),
    (subtree_nodes_iff (E.subtree_eq a.1.1) a.1.2).mp a.2⟩
  inj' := by
    intro a b hab
    have hv := congrArg Subtype.val hab
    change ((E.root a.1.1).1.1, (E.root a.1.1).1.2 ++ a.1.2) =
      ((E.root b.1.1).1.1, (E.root b.1.1).1.2 ++ b.1.2) at hv
    have hold := congrArg (fun p : Fin w × Path => p.1) hv
    dsimp only at hold
    have hpath := congrArg (fun p : Fin w × Path => p.2) hv
    dsimp only at hpath
    have hj : a.1.1 = b.1.1 := by
      by_contra hne
      have hi : (E.root a.1.1).1.2 <+: (E.root b.1.1).1.2 ++ b.1.2 := by
        rw [← hpath]
        exact List.prefix_append _ _
      have hk : (E.root b.1.1).1.2 <+: (E.root b.1.1).1.2 ++ b.1.2 := List.prefix_append _ _
      rcases List.prefix_or_prefix_of_prefix hi hk with h | h
      · exact (E.incomparable _ _ hne).1 ⟨hold, h⟩
      · exact (E.incomparable _ _ hne).2 ⟨hold.symm, h⟩
    apply Subtype.ext
    refine Prod.ext hj ?_
    rw [hj] at hpath
    exact List.append_cancel_left hpath

/-- The corresponding embedding on leaves. -/
@[expose] def RootedSubforest.leafEmbedding (E : RootedSubforest tree v) :
    GLeaf E.shape ↪ GLeaf tree where
  toFun ℓ := ⟨((E.root ℓ.1.1).1.1, (E.root ℓ.1.1).1.2 ++ ℓ.1.2),
    (subtree_leaves_iff (E.subtree_eq ℓ.1.1) ℓ.1.2).mp ℓ.2⟩
  inj' := by
    intro a b hab
    have he : RootedSubforest.nodeEmbedding E a.toNode = RootedSubforest.nodeEmbedding E b.toNode := by
      apply Subtype.ext
      have hv := congrArg (fun ℓ : GLeaf tree => ℓ.1) hab
      change ((E.root a.1.1).1.1, (E.root a.1.1).1.2 ++ a.1.2) =
        ((E.root b.1.1).1.1, (E.root b.1.1).1.2 ++ b.1.2)
      exact hv
    apply Subtype.ext
    have hn := (RootedSubforest.nodeEmbedding E).injective he
    have hv := congrArg (fun a : GNode E.shape => a.1) hn
    simpa only [GLeaf.toNode] using hv

/-- The signature induced by the signs at the selected roots. -/
@[expose] def RootedSubforest.signature (E : RootedSubforest tree v) (sig : Fin w → ℤˣ) : Fin v → ℤˣ :=
  fun i => nodeSign sig (E.root i).1

/-- Root-relative signs agree with ambient signs at every embedded leaf. -/
theorem RootedSubforest.leaf_sign (E : RootedSubforest tree v) (sig : Fin w → ℤˣ)
    (ℓ : GLeaf E.shape) :
    nodeSign (RootedSubforest.signature E sig) ℓ.1 =
      nodeSign sig (RootedSubforest.leafEmbedding E ℓ).1 := by
  change pathSign (pathSign (sig (E.root ℓ.1.1).1.1) (E.root ℓ.1.1).1.2) ℓ.1.2 =
    pathSign (sig (E.root ℓ.1.1).1.1) ((E.root ℓ.1.1).1.2 ++ ℓ.1.2)
  exact (pathSign_append _ _ _).symm

/-- A pairing-closed rooted subforest carries the actual induced garden. -/
@[expose] noncomputable def RootedSubforest.garden {G : Garden w}
    (E : RootedSubforest G.tree v)
    (hc : ∀ ℓ, ∃ ℓ', RootedSubforest.leafEmbedding E ℓ' = G.pair (RootedSubforest.leafEmbedding E ℓ)) :
    Garden v :=
  gardenOnLeafEmbedding (RootedSubforest.signature E G.sig) (RootedSubforest.leafEmbedding E) hc
    (RootedSubforest.leaf_sign E G.sig)

/-- Extracting a subforest preserves its total tree order literally. -/
theorem RootedSubforest.garden_order {G : Garden w} (E : RootedSubforest G.tree v)
    (hc : ∀ ℓ, ∃ ℓ', RootedSubforest.leafEmbedding E ℓ' = G.pair (RootedSubforest.leafEmbedding E ℓ)) :
    (RootedSubforest.garden E hc).order = ∑ i, (E.shape i).order := rfl

end WaveTurbulence.Comb
