/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.XChain.ForestDecorationEquiv
public import WaveTurbulence.Foundations.XChain.SysDraft.Final
/-! A forest decoration is determined by its literal leaf labels. -/
@[expose] public section
namespace WaveTurbulence.Induct
open SysAPI

theorem forestDecoration_eq_of_leaves {w d : ℕ} (top : Fin w → TTree)
    (n : Fin w → (Fin d → ℤ)) (κ κ' : ForestDecoration top d n)
    (h : ∀ l : GLeaf top, κ.1 l.toNode = κ'.1 l.toNode) : κ = κ' := by
  apply Subtype.ext
  funext a
  have hj := treeDecoration_eq_of_leaves (forestDecorationEquiv top n κ a.1.1)
    (forestDecorationEquiv top n κ' a.1.1) (fun l => h ⟨(a.1.1, l.1.2), l.2⟩)
  exact congrFun hj ⟨(0, a.1.2), a.2⟩

noncomputable def forestLeafLabelsEmbedding {w d : ℕ} (top : Fin w → TTree)
    (n : Fin w → (Fin d → ℤ)) : ForestDecoration top d n ↪ (GLeaf top → (Fin d → ℤ)) where
  toFun κ l := κ.1 l.toNode
  inj' a b h := forestDecoration_eq_of_leaves top n a b (fun l => congrFun h l)

end WaveTurbulence.Induct
