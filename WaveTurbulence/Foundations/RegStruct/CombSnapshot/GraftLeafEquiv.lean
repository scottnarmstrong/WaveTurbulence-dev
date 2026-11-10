/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.RegStruct.CombSnapshot.ForestGrafting

/-! # Exact leaf bijection for one graft (TARGET L846–L847)

The forward map is literal address transport. Its bijectivity follows from
injectivity and the already proved leaf counts, so no enumeration choices
change the inherited pairing.
-/

public section

namespace WaveTurbulence.Comb
open TTree Finset

variable {w : ℕ} (tree : Fin w → TTree)

/-- The inserted tree's leaves at the grafted address. -/
@[expose] def graftInsertedLeaf (ℓ : GLeaf tree) (s : TTree)
    (x : GLeaf (fun _ : Fin 1 => s)) : GLeaf (graftLeafForest tree ℓ s) :=
  ⟨(ℓ.1.1, ℓ.1.2 ++ x.1.2), by
    rw [graftLeafForest, Function.update_self]
    exact (subtree_leaves_iff (subtree_replaceAt (subtree_of_mem_leaves ℓ.2) s) x.1.2).mp x.2⟩

/-- The inserted-leaf address map is injective. -/
theorem graftInsertedLeaf_injective (ℓ : GLeaf tree) (s : TTree) :
    Function.Injective (graftInsertedLeaf tree ℓ s) := by
  intro x y h
  have hp := congrArg (fun a : GLeaf (graftLeafForest tree ℓ s) => a.1.2) h
  apply Subtype.ext
  exact Prod.ext (Subsingleton.elim _ _) (List.append_cancel_left hp)

/-- New inserted leaves never coincide with surviving old leaves. -/
theorem graftInsertedLeaf_ne_other (ℓ q : GLeaf tree) (hne : q ≠ ℓ) (s : TTree)
    (x : GLeaf (fun _ : Fin 1 => s)) :
    graftInsertedLeaf tree ℓ s x ≠ graftLeafForest_other tree ℓ q hne s := by
  intro h
  have hi := congrArg (fun a : GLeaf (graftLeafForest tree ℓ s) => a.1.1) h
  have hp := congrArg (fun a : GLeaf (graftLeafForest tree ℓ s) => a.1.2) h
  change ℓ.1.1 = q.1.1 at hi
  change ℓ.1.2 ++ x.1.2 = q.1.2 at hp
  have hd : ℓ.toNode.IsDesc q.toNode := by
    refine ⟨hi, ?_⟩
    change ℓ.1.2 <+: q.1.2
    rw [← hp]
    exact List.prefix_append _ _
  exact hne (GLeaf.eq_of_isDesc hd).symm

/-- Address-level forward map from surviving and inserted leaves. -/
@[expose] def graftLeafMap (ℓ : GLeaf tree) (s : TTree) :
    ({q : GLeaf tree // q ≠ ℓ} ⊕ GLeaf (fun _ : Fin 1 => s)) →
      GLeaf (graftLeafForest tree ℓ s)
  | .inl q => graftLeafForest_other tree ℓ q.1 q.2 s
  | .inr x => graftInsertedLeaf tree ℓ s x

/-- The two literal address maps are jointly injective. -/
theorem graftLeafMap_injective (ℓ : GLeaf tree) (s : TTree) :
    Function.Injective (graftLeafMap tree ℓ s) := by
  intro a b hab
  cases a with
  | inl a =>
    cases b with
    | inl b =>
      apply congrArg Sum.inl
      apply Subtype.ext
      apply Subtype.ext
      exact congrArg (fun x : GLeaf (graftLeafForest tree ℓ s) => x.1) hab
    | inr b => exact (graftInsertedLeaf_ne_other tree ℓ a.1 a.2 s b hab.symm).elim
  | inr a =>
    cases b with
    | inl b => exact (graftInsertedLeaf_ne_other tree ℓ b.1 b.2 s a hab).elim
    | inr b => exact congrArg Sum.inr (graftInsertedLeaf_injective tree ℓ s hab)

end WaveTurbulence.Comb
