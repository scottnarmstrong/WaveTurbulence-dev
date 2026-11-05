/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.XChain.GraftLeaves
/-! Cutting and recovering the ordered trees at the attachment nodes. -/
@[expose] public section
namespace WaveTurbulence.Induct
open Finset TTree

/-- Subtree at a node address; junk addresses below a leaf return a leaf. -/
def subtreeAt : TTree → TTree.Path → TTree
  | T, [] => T
  | .leaf, _ :: _ => .leaf
  | .node l m r, i :: a => subtreeAt (![l, m, r] i) a

/-- Cut the tree the first time a stopping address is reached. -/
def cutTree : TTree → (TTree.Path → Bool) → TTree
  | .leaf, _ => .leaf
  | .node l m r, stop => if stop [] then .leaf else .node
      (cutTree l (fun a => stop (0 :: a)))
      (cutTree m (fun a => stop (1 :: a)))
      (cutTree r (fun a => stop (2 :: a)))

/-- Cutting loses no information when the subtrees at the cut leaves are retained. -/
theorem graftTree_cutTree (T : TTree) (stop : TTree.Path → Bool) :
    graftTree (cutTree T stop) (subtreeAt T) = T := by
  induction T generalizing stop with
  | leaf => rfl
  | node l m r hl hm hr =>
    by_cases hs : stop [] = true
    · simp [cutTree, hs, graftTree, subtreeAt]
    · simp [cutTree, hs, graftTree, subtreeAt, hl, hm, hr]

/-- The lower tree at a top leaf is recovered by its original address. -/
theorem subtreeAt_graftTree_leaf (T : TTree) (f : TTree.Path → TTree)
    {a : TTree.Path} (ha : a ∈ T.leaves) : subtreeAt (graftTree T f) a = f a := by
  induction T generalizing f a with
  | leaf =>
    have he : a = [] := by simpa only [TTree.leaves, Finset.mem_singleton] using ha
    subst a
    rfl
  | node l m r hl hm hr =>
    simp only [TTree.leaves, Finset.mem_union] at ha
    rcases ha with (ha | ha) | ha
    · obtain ⟨a, hleaf, rfl⟩ := TTree.mem_pre.mp ha
      simpa [graftTree, subtreeAt] using hl (fun a => f (0 :: a)) hleaf
    · obtain ⟨a, hleaf, rfl⟩ := TTree.mem_pre.mp ha
      simpa [graftTree, subtreeAt] using hm (fun a => f (1 :: a)) hleaf
    · obtain ⟨a, hleaf, rfl⟩ := TTree.mem_pre.mp ha
      simpa [graftTree, subtreeAt] using hr (fun a => f (2 :: a)) hleaf

/-- For a fixed top tree the graft operation is injective in the actual lower trees. -/
theorem graftTree_injective_on_leaves (T : TTree) (f g : TTree.Path → TTree)
    (h : graftTree T f = graftTree T g) : ∀ a ∈ T.leaves, f a = g a := by
  intro a ha
  calc
    f a = subtreeAt (graftTree T f) a := (subtreeAt_graftTree_leaf T f ha).symm
    _ = subtreeAt (graftTree T g) a := congrArg (fun S => subtreeAt S a) h
    _ = g a := subtreeAt_graftTree_leaf T g ha

end WaveTurbulence.Induct
