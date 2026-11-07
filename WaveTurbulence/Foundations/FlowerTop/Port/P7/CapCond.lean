/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.FlowerTop.Port.P7.CapTop
public import WaveTurbulence.Foundations.FlowerTop.Port.P7.CapSum
/-! FLOWER-P7: the conditions of `coupleSum` on the cap, as conditions on the six-tree garden. -/
@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.FlowerP7
open TTree Finset

/-- The conditions of `coupleSum` (roots in layer `p`) read on the decapitated width-six garden `y`. -/
def Y6Cond (P : WTParams) (p N : ℕ) (kind : TreeKind) (y : LayeredGarden (2 * 3)) : Prop :=
  y.garden.IsPlain ∧ y.CanonCriterion p ∧ (∀ u ∈ y.attachNodes p, y.attachedOrder p u ≤ P.N p) ∧
    y.garden.order + 2 = N ∧ VecKindOK (P.N (p + 1)) kind (fun c => y.topOrder p c)

theorem isPlain_cap_iff (G : Garden (2 * 3)) (hsig : ∀ c, G.sig c = childSig c) :
    (capGarden G hsig).IsPlain ↔ G.IsPlain := by
  unfold Garden.IsPlain
  constructor
  · intro h ℓ
    have := h (liftLeaf ℓ)
    rwa [cap_mark_lift] at this
  · intro h ℓ
    obtain ⟨ℓ', rfl⟩ := exists_liftLeaf ℓ
    rw [cap_mark_lift]; exact h ℓ'

theorem coupleCond_cap_iff (P : WTParams) (p N : ℕ) (kind : TreeKind) (y : CapSrc p) :
    CoupleCond P p N kind y.cap ↔ Y6Cond P p N kind y.1 := by
  obtain ⟨LG, hsig, hp⟩ := y
  unfold CoupleCond Y6Cond CapSrc.cap IsCanonC
  simp only
  have hroot : ∀ j : Fin 2, ∃ b : GBranch (capLayered LG hsig p hp).garden.tree,
      b.1 = (j, []) ∧ (capLayered LG hsig p hp).layer b.toNode = p := fun j =>
    ⟨rootBranch LG.garden.tree j, rfl, capLayered_layer_root LG hsig p hp j⟩
  have hord : (capLayered LG hsig p hp).garden.order = LG.garden.order + 2 := order_cap LG.garden hsig
  rw [attach_cond_cap, hord, treeKindOK_cap, canonCriterion_cap]
  have hc : IsCouple (capLayered LG hsig p hp).garden ↔ LG.garden.IsPlain := by
    unfold IsCouple
    exact ⟨fun h => (isPlain_cap_iff _ hsig).1 h.1, fun h => ⟨(isPlain_cap_iff _ hsig).2 h, rfl⟩⟩
  rw [hc]
  constructor
  · rintro ⟨⟨h1, h2⟩, h3, h4, h5, -⟩
    exact ⟨h1, h2, h3, h4, h5⟩
  · rintro ⟨h1, h2, h3, h4, h5⟩
    exact ⟨⟨h1, h2⟩, h3, h4, h5, hroot⟩

end WaveTurbulence.FlowerP7
