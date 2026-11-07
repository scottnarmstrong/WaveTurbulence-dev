/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.VineEst.CanonicalTopDecomp
/-! Leaf grafting for the concrete ordered ternary trees used in the cumulant expansion.
This module supplies structural operations; the full canonical/kernel bijection is separate. -/
@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.LGSpine
open Finset TTree

/-- Replace each leaf at address a by the prescribed tree f a. -/
def graftTree : TTree → (TTree.Path → TTree) → TTree
  | .leaf, f => f []
  | .node l m r, f => .node
      (graftTree l (fun a => f (0 :: a)))
      (graftTree m (fun a => f (1 :: a)))
      (graftTree r (fun a => f (2 :: a)))

/-- Only the data at actual leaves influence the grafted tree. -/
theorem graftTree_congr (T : TTree) (f g : TTree.Path → TTree)
    (h : ∀ a ∈ T.leaves, f a = g a) : graftTree T f = graftTree T g := by
  induction T generalizing f g with
  | leaf => exact h [] (by simp [TTree.leaves])
  | node l m r hl hm hr =>
    simp only [graftTree, TTree.node.injEq]
    refine ⟨hl _ _ (fun a ha => h (0 :: a) ?_), hm _ _ (fun a ha => h (1 :: a) ?_),
      hr _ _ (fun a ha => h (2 :: a) ?_)⟩ <;> simp [TTree.leaves, TTree.cons_mem_pre, ha]

theorem graftTree_leaf (T : TTree) : graftTree T (fun _ => .leaf) = T := by
  induction T with
  | leaf => rfl
  | node l m r hl hm hr => simp only [graftTree, hl, hm, hr]

/-- Leaf substitution composes by concatenating the two leaf addresses. -/
theorem graftTree_assoc (T : TTree) (f g : TTree.Path → TTree) :
    graftTree (graftTree T f) g =
      graftTree T (fun a => graftTree (f a) (fun b => g (a ++ b))) := by
  induction T generalizing f g with
  | leaf => rfl
  | node l m r hl hm hr =>
    simp only [graftTree, hl, hm, hr, List.cons_append]

/-- Grafting adds orders over the leaves, with no multiplicity or symmetry factor. -/
theorem graftTree_order (T : TTree) (f : TTree.Path → TTree) :
    (graftTree T f).order = T.order + ∑ a ∈ T.leaves, (f a).order := by
  induction T generalizing f with
  | leaf => simp [graftTree, TTree.order, TTree.leaves]
  | node l m r hl hm hr =>
    have hd {i j : Fin 3} (hij : i ≠ j) (S U : Finset TTree.Path) :
        Disjoint (TTree.pre i S) (TTree.pre j U) := by
      rw [Finset.disjoint_left]
      intro a ha hb
      obtain ⟨q, _, rfl⟩ := TTree.mem_pre.mp ha
      exact hij (TTree.cons_mem_pre.mp hb).1.symm
    have hs (i : Fin 3) (S : Finset TTree.Path) :
        (∑ a ∈ TTree.pre i S, (f a).order) = ∑ a ∈ S, (f (i :: a)).order :=
      Finset.sum_image (fun a _ b _ hab => List.cons_injective hab)
    rw [graftTree, TTree.order, hl, hm, hr, TTree.order, TTree.leaves,
      Finset.sum_union (Finset.disjoint_union_left.mpr ⟨hd (by decide) _ _, hd (by decide) _ _⟩),
      Finset.sum_union (hd (by decide) _ _), hs, hs, hs]
    omega

/-- Signs along a grafted branch multiply the top sign and the internal sign. -/
theorem pathSign_append (ζ : ℤˣ) (a b : TTree.Path) :
    TTree.pathSign ζ (a ++ b) = TTree.pathSign (TTree.pathSign ζ a) b := by
  simp only [TTree.pathSign, List.count_append, pow_add, mul_assoc]

end WaveTurbulence.LGSpine
