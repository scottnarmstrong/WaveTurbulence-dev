/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.XChain.GraftAssembleDecoration
/-! The full rooted and flower-labelled decoration bijection for arbitrary grafts. -/
@[expose] public section
namespace WaveTurbulence.Induct
open Finset

theorem split_assembleGenDecoration {d w : ℕ} (sig : Fin w → ℤˣ) (top : Fin w → TTree)
    (P : Finpartition (univ : Finset (GLeaf top))) (low : (B : P.parts) → Garden B.1.card)
    (hsig : ∀ B k, (low B).sig k = nodeSign sig ((blockRootEquiv top P).symm ⟨B, k⟩).1)
    (n : Fin w → (Fin d → ℤ)) (nfl : Fin d → ℤ)
    (x : BoundaryDecorationData top P low d n nfl) :
    splitGenDecoration sig top P low hsig n nfl (assembleGenDecoration sig top P low hsig n nfl x) = x := by
  let labels := (x.1.1, fun B => (x.2 B).1)
  have hx : GraftMatching top P low labels := fun B k => ((x.2 B).2.2.1 k).symm
  have ht : (splitGenDecoration sig top P low hsig n nfl
      (assembleGenDecoration sig top P low hsig n nfl x)).1 = x.1 := by
    apply Subtype.ext
    exact funext (graftAssembleLabels_top top P low labels hx)
  have hl : ∀ B a, ((splitGenDecoration sig top P low hsig n nfl
      (assembleGenDecoration sig top P low hsig n nfl x)).2 B).1 a = (x.2 B).1 a := by
    intro B a
    exact graftAssembleLabels_lower top P low labels B a
  generalize hy : splitGenDecoration sig top P low hsig n nfl
    (assembleGenDecoration sig top P low hsig n nfl x) = y at ht hl ⊢
  rcases x with ⟨kt, kl⟩
  rcases y with ⟨yt, yl⟩
  change yt = kt at ht
  subst yt
  apply congrArg (Sigma.mk kt)
  funext B
  apply Subtype.ext
  exact funext (hl B)

/-- Exact general decorations reindex to top-forest decorations and independently chosen lower
rooted decorations. Both external root labels and every retained flower label are preserved. -/
noncomputable def graftGenDecorationEquiv {d w : ℕ} (sig : Fin w → ℤˣ) (top : Fin w → TTree)
    (P : Finpartition (univ : Finset (GLeaf top))) (low : (B : P.parts) → Garden B.1.card)
    (hsig : ∀ B k, (low B).sig k = nodeSign sig ((blockRootEquiv top P).symm ⟨B, k⟩).1)
    (n : Fin w → (Fin d → ℤ)) (nfl : Fin d → ℤ) :
    GenDecoration (markedGardenGraft sig top P low hsig) d n nfl ≃
      BoundaryDecorationData top P low d n nfl where
  toFun := splitGenDecoration sig top P low hsig n nfl
  invFun := assembleGenDecoration sig top P low hsig n nfl
  left_inv := assemble_splitGenDecoration sig top P low hsig n nfl
  right_inv := split_assembleGenDecoration sig top P low hsig n nfl

end WaveTurbulence.Induct
