/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.WaveB.Lemmas
/-! Relabelling the ordered roots of a forest without changing any internal tree address. -/
@[expose] public section
namespace WaveTurbulence.Induct

noncomputable def rootPathEquiv {v w : ℕ} (tree : Fin w → TTree)
    (S : TTree → Finset TTree.Path) (e : Fin v ≃ Fin w) :
    {a : Fin v × TTree.Path // a.2 ∈ S (tree (e a.1))} ≃
      {a : Fin w × TTree.Path // a.2 ∈ S (tree a.1)} where
  toFun a := ⟨(e a.1.1, a.1.2), a.2⟩
  invFun a := ⟨(e.symm a.1.1, a.1.2), by simpa only [e.apply_symm_apply] using a.2⟩
  left_inv a := Subtype.ext (Prod.ext (e.symm_apply_apply _) rfl)
  right_inv a := Subtype.ext (Prod.ext (e.apply_symm_apply _) rfl)

noncomputable def reindexNodeEquiv {v w : ℕ} (tree : Fin w → TTree) (e : Fin v ≃ Fin w) :
    GNode (fun j => tree (e j)) ≃ GNode tree := rootPathEquiv tree TTree.nodes e

noncomputable def reindexBranchEquiv {v w : ℕ} (tree : Fin w → TTree) (e : Fin v ≃ Fin w) :
    GBranch (fun j => tree (e j)) ≃ GBranch tree := rootPathEquiv tree TTree.branching e

noncomputable def reindexLeafEquiv {v w : ℕ} (tree : Fin w → TTree) (e : Fin v ≃ Fin w) :
    GLeaf (fun j => tree (e j)) ≃ GLeaf tree := rootPathEquiv tree TTree.leaves e

theorem reindexNodeEquiv_isDesc_iff {v w : ℕ} (tree : Fin w → TTree) (e : Fin v ≃ Fin w)
    (a b : GNode (fun j => tree (e j))) :
    (reindexNodeEquiv tree e a).IsDesc (reindexNodeEquiv tree e b) ↔ a.IsDesc b := by
  exact and_congr e.injective.eq_iff Iff.rfl

end WaveTurbulence.Induct
