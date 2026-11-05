/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.XChain.TopLeafGroups
public import WaveTurbulence.Foundations.XChain.SignedComposition
/-! Literal leaf products of a single top tree coincide with its source leaf group. -/
@[expose] public section
namespace WaveTurbulence.Induct
open Finset

noncomputable def singleLeafToForest {w : ℕ} (top : Fin w → TTree) (j : Fin w)
    (l : GLeaf (single (top j))) : GLeaf top := ⟨(j, l.1.2), l.2⟩

noncomputable def topLeafGroupEquiv {w : ℕ} (top : Fin w → TTree) (j : Fin w) :
    GLeaf (single (top j)) ≃ ↥(topLeafGroups top j) where
  toFun l := ⟨singleLeafToForest top j l, mem_filter.mpr ⟨mem_univ _, rfl⟩⟩
  invFun l := ⟨(0, l.1.1.2), by
    have hj := (mem_filter.mp l.2).2
    exact (congrArg (fun k => l.1.1.2 ∈ (top k).leaves) hj).mp l.1.2⟩
  left_inv l := Subtype.ext (Prod.ext (Subsingleton.elim _ _) rfl)
  right_inv l := by
    apply Subtype.ext
    apply Subtype.ext
    exact Prod.ext (mem_filter.mp l.2).2.symm rfl

theorem prod_singleLeaf_eq_group {w : ℕ} (top : Fin w → TTree) (j : Fin w) (f : GLeaf top → ℂ) :
    (∏ l : GLeaf (single (top j)), f (singleLeafToForest top j l)) =
      ∏ l ∈ topLeafGroups top j, f l := by
  have h := Fintype.prod_equiv (topLeafGroupEquiv top j)
    (fun l => f (singleLeafToForest top j l)) (fun l => f l.1) (fun _ => rfl)
  exact h.trans (prod_coe_sort (topLeafGroups top j) f)

end WaveTurbulence.Induct
