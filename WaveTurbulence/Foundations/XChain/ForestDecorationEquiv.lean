/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.XChain.GraftBoundaryDecorations
/-! Forest decorations are exactly one ordinary tree decoration at each ordered root. -/
@[expose] public section
namespace WaveTurbulence.Induct

noncomputable def forestDecorationEquiv {w d : ℕ} (top : Fin w → TTree)
    (n : Fin w → (Fin d → ℤ)) :
    ForestDecoration top d n ≃ ((j : Fin w) → TreeDecoration (top j) d (n j)) where
  toFun κ j := ⟨fun a => κ.1 ⟨(j, a.1.2), a.2⟩,
    (fun b => κ.2.1 ⟨(j, b.1.2), b.2⟩), κ.2.2 j⟩
  invFun κ := ⟨fun a => (κ a.1.1).1 ⟨(0, a.1.2), a.2⟩,
    (fun b => (κ b.1.1).2.1 ⟨(0, b.1.2), b.2⟩), fun j => (κ j).2.2⟩
  left_inv κ := by
    apply Subtype.ext
    funext a
    rfl
  right_inv κ := by
    funext j
    apply Subtype.ext
    funext a
    apply congrArg (κ j).1
    exact Subtype.ext (Prod.ext (Subsingleton.elim _ _) rfl)

theorem forestDecorationEquiv_apply_val {w d : ℕ} (top : Fin w → TTree)
    (n : Fin w → (Fin d → ℤ)) (κ : ForestDecoration top d n) (j : Fin w)
    (a : GNode (single (top j))) :
    (forestDecorationEquiv top n κ j).1 a = κ.1 ⟨(j, a.1.2), a.2⟩ := rfl

end WaveTurbulence.Induct
