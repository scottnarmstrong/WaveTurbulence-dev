/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.FlowerTop.Port.P7.CapCanon
public import WaveTurbulence.Foundations.FlowerTop.Port.P7.EmbSum
/-! FLOWER-P7: attachment nodes, attached orders and top orders of the cap against the six trees. -/
@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.FlowerP7
open TTree Finset

variable {T : Fin (2 * 3) → TTree}

theorem orderBelow_lift (a : GNode T) : (liftNode a).orderBelow = a.orderBelow := by
  classical
  unfold GNode.orderBelow
  have : (Finset.univ.filter fun b : GBranch (capTree T) => (liftNode a).IsDesc b.toNode) =
      (Finset.univ.filter fun b : GBranch T => a.IsDesc b.toNode).image liftBranch := by
    ext b
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image]
    constructor
    · intro h
      by_cases hr : b.1.2 = []
      · exfalso
        obtain ⟨⟨j, p⟩, hb⟩ := b
        simp only at hr
        subst hr
        exact lift_not_isDesc_root j a (by simpa [rootBranch, GBranch.toNode] using h)
      · obtain ⟨b', rfl⟩ := exists_liftBranch b hr
        exact ⟨b', by rwa [liftBranch_toNode, isDesc_lift] at h, rfl⟩
    · rintro ⟨b', h, rfl⟩
      rwa [liftBranch_toNode, isDesc_lift]
  rw [this, Finset.card_image_of_injective _ liftBranch_injective]

theorem mem_attachNodes_iff {w : ℕ} (LG : LayeredGarden w) (p : ℕ) (a : GNode LG.garden.tree) :
    a ∈ LG.attachNodes p ↔ LG.layer a < p ∧ LG.parentLayer p a = p := by
  unfold LayeredGarden.attachNodes
  simp

theorem mem_attachNodes_cap (LG : LayeredGarden (2 * 3)) (hsig : ∀ c, LG.garden.sig c = childSig c) (p : ℕ)
    (hp : ∀ a, LG.layer a ≤ p) (x : GNode (capTree LG.garden.tree)) :
    x ∈ (capLayered LG hsig p hp).attachNodes p ↔ ∃ a ∈ LG.attachNodes p, liftNode a = x := by
  rw [mem_attachNodes_iff]
  obtain ⟨y, rfl⟩ := (capNodeEquiv LG.garden.tree).surjective x
  rcases y with j | y
  · rw [capNodeEquiv_inl, capLayered_layer_root]
    constructor
    · rintro ⟨h, -⟩; exact absurd h (lt_irrefl _)
    · rintro ⟨a, -, ha⟩
      exfalso
      have := congrArg (fun x : GNode (capTree LG.garden.tree) => x.1.2) ha
      simp [liftNode, liftAddr, rootBranch, GBranch.toNode] at this
  · rw [capNodeEquiv_inr, capLayered_layer_lift, parentLayer_cap_lift]
    constructor
    · intro h
      exact ⟨y, (mem_attachNodes_iff LG p y).2 h, rfl⟩
    · rintro ⟨a, h, ha⟩
      have := liftNode_injective ha
      subst this
      exact (mem_attachNodes_iff LG p a).1 h

theorem attachedOrder_cap (LG : LayeredGarden (2 * 3)) (hsig : ∀ c, LG.garden.sig c = childSig c) (p : ℕ)
    (hp : ∀ a, LG.layer a ≤ p) (u : GNode LG.garden.tree) :
    (capLayered LG hsig p hp).attachedOrder p (liftNode u) = LG.attachedOrder p u := by
  classical
  unfold LayeredGarden.attachedOrder
  refine sum_filter_eqvGen_embedding liftNode liftNode_injective _ _ (fun x => ?_)
    _ _ (fun a b => ?_) (fun x y h => ?_) _ _ (fun a => ?_) u
  · rw [mem_attachNodes_cap]
    constructor
    · rintro ⟨a, ha, h⟩
      rwa [← liftNode_injective h]
    · intro h; exact ⟨x, h, rfl⟩
  · unfold LayeredGarden.AttachLinkedOn LayeredGarden.AttachLinked
    simp only [leavesBelow_lift, Finset.mem_image, cap_pair_lift']
    constructor
    · rintro ⟨h1, h2, ℓ, ⟨ℓ0, hℓ0, rfl⟩, ℓ1, hℓ1, e⟩
      rw [cap_pair_lift', liftLeaf_injective.eq_iff] at e
      subst e
      refine ⟨?_, ?_, ℓ0, hℓ0, hℓ1⟩
      · obtain ⟨a', ha', e'⟩ := (mem_attachNodes_cap LG hsig p hp _).1 h1
        rwa [← liftNode_injective e']
      · obtain ⟨a', ha', e'⟩ := (mem_attachNodes_cap LG hsig p hp _).1 h2
        rwa [← liftNode_injective e']
    · rintro ⟨h1, h2, ℓ, hℓ, hp'⟩
      refine ⟨(mem_attachNodes_cap LG hsig p hp _).2 ⟨a, h1, rfl⟩,
        (mem_attachNodes_cap LG hsig p hp _).2 ⟨b, h2, rfl⟩, liftLeaf ℓ, ⟨ℓ, hℓ, rfl⟩, ?_⟩
      exact ⟨LG.garden.pair ℓ, hp', (cap_pair_lift' LG.garden ℓ).symm⟩
  · unfold LayeredGarden.AttachLinkedOn at h
    obtain ⟨a, _, rfl⟩ := (mem_attachNodes_cap LG hsig p hp x).1 h.1
    obtain ⟨b, _, rfl⟩ := (mem_attachNodes_cap LG hsig p hp y).1 h.2.1
    exact ⟨fun _ => ⟨b, rfl⟩, fun _ => ⟨a, rfl⟩⟩
  · exact orderBelow_lift a

/-- The attachment condition of the cap is that of the six trees. -/
theorem attach_cond_cap (LG : LayeredGarden (2 * 3)) (hsig : ∀ c, LG.garden.sig c = childSig c) (p : ℕ)
    (hp : ∀ a, LG.layer a ≤ p) (M : ℕ) :
    (∀ u ∈ (capLayered LG hsig p hp).attachNodes p, (capLayered LG hsig p hp).attachedOrder p u ≤ M) ↔
      ∀ u ∈ LG.attachNodes p, LG.attachedOrder p u ≤ M := by
  constructor
  · intro h u hu
    have := h (liftNode u) ((mem_attachNodes_cap LG hsig p hp _).2 ⟨u, hu, rfl⟩)
    rwa [attachedOrder_cap] at this
  · intro h x hx
    obtain ⟨a, ha, rfl⟩ := (mem_attachNodes_cap LG hsig p hp x).1 hx
    rw [attachedOrder_cap]
    exact h a ha

end WaveTurbulence.FlowerP7
