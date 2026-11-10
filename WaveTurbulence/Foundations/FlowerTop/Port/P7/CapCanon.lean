/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.FlowerTop.Port.P7.CapSurj
/-! FLOWER-P7: the canonicity criterion of the cap is the canonicity criterion of the six trees
(the roots of the six trees read their parent layer as `p`, which is the layer of the cap roots). -/
@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.FlowerP7
open TTree Finset

variable {T : Fin (2 * 3) → TTree}

theorem isDesc_lift (a a' : GNode T) : (liftNode a).IsDesc (liftNode a') ↔ a.IsDesc a' := by
  unfold GNode.IsDesc
  simp only [liftNode, liftAddr, List.cons_prefix_cons, and_assoc]
  constructor
  · rintro ⟨h1, h2, h3⟩
    refine ⟨?_, h3⟩
    rw [← idx_jOf_iOf a.1.1, ← idx_jOf_iOf a'.1.1, h1, h2]
  · rintro ⟨h1, h3⟩
    simp [h1, h3]

theorem incomparable_lift (a a' : GNode T) : (liftNode a).Incomparable (liftNode a') ↔ a.Incomparable a' := by
  unfold GNode.Incomparable
  rw [isDesc_lift, isDesc_lift]

theorem lift_not_isDesc_root (j : Fin 2) (a : GNode T) : ¬ (liftNode a).IsDesc (rootBranch T j).toNode := by
  rintro ⟨-, h⟩
  simp [rootBranch, GBranch.toNode, liftNode, liftAddr] at h

theorem mem_leavesBelow_lift (a : GNode T) (ℓ : GLeaf (capTree T)) :
    ℓ ∈ (liftNode a).leavesBelow ↔ ∃ ℓ' ∈ a.leavesBelow, liftLeaf ℓ' = ℓ := by
  unfold GNode.leavesBelow
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · intro h
    obtain ⟨ℓ', rfl⟩ := exists_liftLeaf ℓ
    exact ⟨ℓ', by rwa [liftLeaf_toNode, isDesc_lift] at h, rfl⟩
  · rintro ⟨ℓ', h, rfl⟩
    rwa [liftLeaf_toNode, isDesc_lift]

theorem leavesBelow_lift (a : GNode T) :
    (liftNode a).leavesBelow = a.leavesBelow.image liftLeaf := by
  ext ℓ
  rw [mem_leavesBelow_lift, Finset.mem_image]

theorem cap_pair_lift (G : Garden (2 * 3)) (hsig : ∀ c, G.sig c = childSig c) (ℓ : GLeaf G.tree) :
    (capGarden G hsig).pair (liftLeaf ℓ) = liftLeaf (G.pair ℓ) := by
  show capLeafEquiv G.tree (G.pair ((capLeafEquiv G.tree).symm (liftLeaf ℓ))) = _
  have : (capLeafEquiv G.tree).symm (liftLeaf ℓ) = ℓ := by
    rw [Equiv.symm_apply_eq]; rfl
  rw [this]; rfl

theorem cap_pair_lift' (G : Garden (2 * 3)) (ℓ : GLeaf G.tree) :
    capLeafEquiv G.tree (G.pair ((capLeafEquiv G.tree).symm (liftLeaf ℓ))) = liftLeaf (G.pair ℓ) := by
  have : (capLeafEquiv G.tree).symm (liftLeaf ℓ) = ℓ := by
    rw [Equiv.symm_apply_eq]; rfl
  rw [this]; rfl

theorem cap_mark_lift (G : Garden (2 * 3)) (hsig : ∀ c, G.sig c = childSig c) (ℓ : GLeaf G.tree) :
    (capGarden G hsig).mark (liftLeaf ℓ) = G.mark ℓ := by
  show G.mark ((capLeafEquiv G.tree).symm (liftLeaf ℓ)) = _
  have : (capLeafEquiv G.tree).symm (liftLeaf ℓ) = ℓ := by
    rw [Equiv.symm_apply_eq]; rfl
  rw [this]

theorem completelyPaired_cap (G : Garden (2 * 3)) (hsig : ∀ c, G.sig c = childSig c) (S : Finset (GLeaf G.tree)) :
    (capGarden G hsig).CompletelyPaired (S.image liftLeaf) ↔ G.CompletelyPaired S := by
  unfold Garden.CompletelyPaired
  constructor
  · intro h ℓ hℓ
    obtain ⟨h1, h2⟩ := h (liftLeaf ℓ) (Finset.mem_image_of_mem _ hℓ)
    rw [cap_pair_lift] at h1 h2
    refine ⟨fun e => h1 (by rw [e]), ?_⟩
    obtain ⟨ℓ'', hℓ'', e⟩ := Finset.mem_image.1 h2
    rwa [liftLeaf_injective e] at hℓ''
  · intro h x hx
    obtain ⟨ℓ, hℓ, rfl⟩ := Finset.mem_image.1 hx
    obtain ⟨h1, h2⟩ := h ℓ hℓ
    rw [cap_pair_lift]
    exact ⟨fun e => h1 (liftLeaf_injective e), Finset.mem_image_of_mem _ h2⟩

theorem capLayered_layer_dropLast (LG : LayeredGarden (2 * 3)) (hsig : ∀ c, LG.garden.sig c = childSig c)
    (p : ℕ) (hp : ∀ a, LG.layer a ≤ p) (c : Fin (2 * 3)) (q : Path) (hq : q ≠ [])
    (hmem : ((jOf c, (iOf c :: q).dropLast)).2 ∈ (capTree LG.garden.tree (jOf c)).nodes)
    (hmem' : (c, q.dropLast).2 ∈ (LG.garden.tree c).nodes) :
    (capLayered LG hsig p hp).layer ⟨(jOf c, (iOf c :: q).dropLast), hmem⟩ =
      LG.layer ⟨(c, q.dropLast), hmem'⟩ := by
  have : (⟨(jOf c, (iOf c :: q).dropLast), hmem⟩ : GNode (capTree LG.garden.tree)) =
      liftNode ⟨(c, q.dropLast), hmem'⟩ :=
    Subtype.ext (by simp [liftNode, liftAddr, List.dropLast_cons_of_ne_nil hq])
  rw [this]
  exact capLayered_layer_lift LG hsig p hp ⟨(c, q.dropLast), hmem'⟩

/-- The parent layer of a lifted node. -/
theorem parentLayer_cap_lift (LG : LayeredGarden (2 * 3)) (hsig : ∀ c, LG.garden.sig c = childSig c) (p : ℕ)
    (hp : ∀ a, LG.layer a ≤ p) (a : GNode LG.garden.tree) :
    (capLayered LG hsig p hp).parentLayer p (liftNode a) = LG.parentLayer p a := by
  unfold LayeredGarden.parentLayer
  by_cases h : a.1.2 = []
  · simp only [liftNode, liftAddr, h, List.cons_ne_nil, ite_false, ite_true]
    exact capLayered_layer_root LG hsig p hp (jOf a.1.1)
  · simp only [liftNode, liftAddr, h, List.cons_ne_nil, ite_false]
    obtain ⟨⟨c, q⟩, hc⟩ := a
    exact capLayered_layer_dropLast LG hsig p hp c q h _ _

theorem parentLayer_cap_root (LG : LayeredGarden (2 * 3)) (hsig : ∀ c, LG.garden.sig c = childSig c) (p : ℕ)
    (hp : ∀ a, LG.layer a ≤ p) (j : Fin 2) :
    (capLayered LG hsig p hp).parentLayer p (rootBranch LG.garden.tree j).toNode = p := by
  simp [LayeredGarden.parentLayer, rootBranch, GBranch.toNode]

/-- **Canonicity of the cap** (finding 3 of session 1): the criterion of the cap is that of the six trees. -/
theorem canonCriterion_cap (LG : LayeredGarden (2 * 3)) (hsig : ∀ c, LG.garden.sig c = childSig c) (p : ℕ)
    (hp : ∀ a, LG.layer a ≤ p) :
    (capLayered LG hsig p hp).CanonCriterion p ↔ LG.CanonCriterion p := by
  unfold LayeredGarden.CanonCriterion
  constructor
  · rintro ⟨-, h⟩
    refine ⟨hp, fun a a' hinc hcp => ?_⟩
    have h1 := h (liftNode a) (liftNode a') ((incomparable_lift a a').2 hinc) (by
      rw [leavesBelow_lift, leavesBelow_lift, ← Finset.image_union]
      exact (completelyPaired_cap LG.garden hsig _).2 hcp)
    rwa [parentLayer_cap_lift, parentLayer_cap_lift, capLayered_layer_lift, capLayered_layer_lift] at h1
  · rintro ⟨-, h⟩
    refine ⟨fun x => ?_, fun x x' hinc hcp => ?_⟩
    · obtain ⟨y, rfl⟩ := (capNodeEquiv LG.garden.tree).surjective x
      rcases y with j | y
      · rw [capNodeEquiv_inl, capLayered_layer_root]
      · rw [capNodeEquiv_inr, capLayered_layer_lift]; exact hp y
    · obtain ⟨y, rfl⟩ := (capNodeEquiv LG.garden.tree).surjective x
      obtain ⟨y', rfl⟩ := (capNodeEquiv LG.garden.tree).surjective x'
      rcases y with j | y
      · rw [capNodeEquiv_inl, parentLayer_cap_root, capLayered_layer_root]
        exact (min_le_left _ _).trans (le_max_left _ _)
      · rcases y' with j' | y'
        · rw [capNodeEquiv_inl, parentLayer_cap_root, capLayered_layer_root]
          exact (min_le_right _ _).trans (le_max_right _ _)
        · rw [capNodeEquiv_inr, capNodeEquiv_inr] at hinc hcp ⊢
          rw [parentLayer_cap_lift, parentLayer_cap_lift, capLayered_layer_lift, capLayered_layer_lift]
          refine h y y' ((incomparable_lift y y').1 hinc) ?_
          rw [leavesBelow_lift, leavesBelow_lift, ← Finset.image_union] at hcp
          exact (completelyPaired_cap LG.garden hsig _).1 hcp

end WaveTurbulence.FlowerP7
