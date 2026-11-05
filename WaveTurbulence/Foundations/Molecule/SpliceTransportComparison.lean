/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Molecule.TwistSpliceCrown

/-! # Comparing two literal retained-leaf splicing constructions

This infrastructure theorem consumes a proved leaf-transport diagram;
source applications must derive that diagram from the actual subtree
addresses. Pairings and marks are compared, not merely the forests.
-/

public section
namespace WaveTurbulence.Twist
open TTree

/-- Literal spliced gardens agree when their concrete retained-leaf pullbacks commute. -/
theorem spliceTransport_eq_of_diagram {w : ℕ} (G H : Garden w)
    (L : GLeaf G.tree → Prop) (K : GLeaf H.tree → Prop)
    (hcL : ∀ l, L l → L (G.pair l)) (hcK : ∀ l, K l → K (H.pair l))
    {F₁ F₂ : Fin w → TTree}
    (e₁ : GLeaf F₁ ≃ {l // L l}) (e₂ : GLeaf F₂ ≃ {l // K l})
    (hs₁ : ∀ l : GLeaf F₁, nodeSign G.sig l.1 = nodeSign G.sig (e₁ l).1.1)
    (hs₂ : ∀ l : GLeaf F₂, nodeSign H.sig l.1 = nodeSign H.sig (e₂ l).1.1)
    (hsig : H.sig = G.sig) (hF : F₂ = F₁) (e : GLeaf G.tree ≃ GLeaf H.tree)
    (hpair : ∀ l, H.pair (e l) = e (G.pair l)) (hmark : ∀ l, H.mark (e l) = G.mark l)
    (hdiagram : ∀ l : GLeaf F₁, e (e₁ l).1 = (e₂ (forestLeafCast hF.symm l)).1) :
    Mole.gardenOfLeafTransport H K hcK e₂ hs₂ = Mole.gardenOfLeafTransport G L hcL e₁ hs₁ := by
  apply garden_eq_of_leaf_transport
    (H := Mole.gardenOfLeafTransport H K hcK e₂ hs₂)
    (K := Mole.gardenOfLeafTransport G L hcL e₁ hs₁) hsig hF (forestLeafCast hF.symm)
  · intro l; rfl
  · intro l
    apply e₂.injective
    apply Subtype.ext
    have hL := congrArg Subtype.val (Mole.transportedLeafPair_comm G L hcL e₁ l)
    have hK := congrArg Subtype.val (Mole.transportedLeafPair_comm H K hcK e₂ (forestLeafCast hF.symm l))
    change (e₁ ((Mole.gardenOfLeafTransport G L hcL e₁ hs₁).pair l)).1 = G.pair (e₁ l).1 at hL
    change (e₂ ((Mole.gardenOfLeafTransport H K hcK e₂ hs₂).pair (forestLeafCast hF.symm l))).1 =
      H.pair (e₂ (forestLeafCast hF.symm l)).1 at hK
    exact hK.trans ((congrArg H.pair (hdiagram l).symm).trans
      ((hpair (e₁ l).1).trans ((congrArg e hL.symm).trans (hdiagram _))))
  · intro l
    change H.mark (e₂ (forestLeafCast hF.symm l)).1 = G.mark (e₁ l).1
    exact (congrArg H.mark (hdiagram l).symm).trans (hmark (e₁ l).1)

end WaveTurbulence.Twist
