/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.FlowerTop.Port.P7.CapIdentity
/-! FLOWER-P7: every couple with branching roots is a cap, and the cap is injective.  This is the carrier
bijection `Q ↔ decapitated width-six garden`. -/
@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.FlowerP7
open TTree Finset

theorem capTree_injective : Function.Injective capTree := by
  intro T T' h
  funext c
  have h1 := congrFun h (jOf c)
  simp only [capTree, TTree.node.injEq] at h1
  rw [← idx_jOf_iOf c]
  generalize jOf c = j at h1 ⊢
  generalize iOf c = i
  fin_cases i
  · exact h1.1
  · exact h1.2.1
  · exact h1.2.2

theorem exists_capTree (tr : Fin 2 → TTree) (h : ∀ j, tr j ≠ TTree.leaf) : ∃ T6, capTree T6 = tr := by
  refine ⟨fun c => match tr (jOf c) with
    | .node l m r => ![l, m, r] (iOf c)
    | .leaf => .leaf, ?_⟩
  funext j
  rcases hj : tr j with _ | ⟨l, m, r⟩
  · exact absurd hj (h j)
  · simp [capTree, hj]

theorem exists_cap_garden (Gq : Garden 2) (hc : Gq.sig = ![1, -1]) (hroot : ∀ j, Gq.tree j ≠ TTree.leaf) :
    ∃ (G : Garden (2 * 3)) (hsig : ∀ c, G.sig c = childSig c), capGarden G hsig = Gq := by
  obtain ⟨sg, tr, pr, mk, h1, h2, h3⟩ := Gq
  simp only at hc hroot
  obtain ⟨T6, rfl⟩ := exists_capTree tr hroot
  subst hc
  have hs : ∀ c, childSig c = childSig c := fun _ => rfl
  let G : Garden (2 * 3) :=
    { sig := childSig
      tree := T6
      pair := fun ℓ => (capLeafEquiv T6).symm (pr (capLeafEquiv T6 ℓ))
      mark := fun ℓ => mk (capLeafEquiv T6 ℓ)
      pair_pair := fun ℓ => by simp [h1]
      pair_eq_iff := fun ℓ => by
        rw [Equiv.symm_apply_eq]
        exact h2 _
      pair_sign := fun ℓ hℓ => by
        have hne : pr (capLeafEquiv T6 ℓ) ≠ capLeafEquiv T6 ℓ := by
          intro h
          apply hℓ
          rw [h]; simp
        have h4 := h3 _ hne
        obtain ⟨ℓ'', hℓ''⟩ := (capLeafEquiv T6).surjective (pr (capLeafEquiv T6 ℓ))
        rw [← hℓ'', capLeafEquiv_apply] at h4
        have e1 : ((capLeafEquiv T6).symm (pr (capLeafEquiv T6 ℓ))) = ℓ'' := by
          rw [← hℓ'']; simp
        rw [e1]
        rw [capLeafEquiv_apply] at h4
        have := nodeSign_cap (sig6 := childSig) (fun _ => rfl)
        show nodeSign childSig ℓ''.1 = -nodeSign childSig ℓ.1
        rw [← this, ← this]
        exact h4 }
  refine ⟨G, fun c => rfl, ?_⟩
  have hp : (fun ℓ : GLeaf (capTree T6) => capLeafEquiv T6 (G.pair ((capLeafEquiv T6).symm ℓ))) = pr := by
    funext ℓ
    simp [G]
  have hm : (fun ℓ : GLeaf (capTree T6) => G.mark ((capLeafEquiv T6).symm ℓ)) = mk := by
    funext ℓ
    simp [G]
  simp only [capGarden, Garden.mk.injEq]
  exact ⟨trivial, rfl, heq_of_eq hp, heq_of_eq hm⟩


theorem exists_cap_layered (Q : LayeredGarden 2) (hc : Q.garden.sig = ![1, -1])
    (hroot : ∀ j, Q.garden.tree j ≠ TTree.leaf) (p : ℕ) (hp : ∀ x, Q.layer x ≤ p)
    (hl : ∀ (j : Fin 2) (b : GBranch Q.garden.tree), b.1 = (j, []) → Q.layer b.toNode = p) :
    ∃ (LG : LayeredGarden (2 * 3)) (hsig : ∀ c, LG.garden.sig c = childSig c)
      (hp6 : ∀ a, LG.layer a ≤ p), capLayered LG hsig p hp6 = Q := by
  obtain ⟨Gq, layer, hlay⟩ := Q
  simp only at hc hroot hp hl
  obtain ⟨G, hsig, rfl⟩ := exists_cap_garden Gq hc hroot
  let LG : LayeredGarden (2 * 3) :=
    { garden := G
      layer := fun a => layer (liftNode a)
      isLayering := by
        constructor
        · intro b i
          have h := hlay.1 (liftBranch b) i
          rw [liftBranch_child, liftBranch_toNode] at h
          exact h
        · intro ℓ
          have h := hlay.2 (liftLeaf ℓ)
          rw [liftLeaf_toNode] at h
          have e : (capGarden G hsig).pair (liftLeaf ℓ) = liftLeaf (G.pair ℓ) := by
            show capLeafEquiv G.tree (G.pair ((capLeafEquiv G.tree).symm (liftLeaf ℓ))) = _
            have : (capLeafEquiv G.tree).symm (liftLeaf ℓ) = ℓ := by
              rw [Equiv.symm_apply_eq]; rfl
            rw [this]; rfl
          rw [e, liftLeaf_toNode] at h
          exact h }
  have hp6 : ∀ a, LG.layer a ≤ p := fun a => hp _
  refine ⟨LG, hsig, hp6, ?_⟩
  simp only [capLayered, LayeredGarden.mk.injEq]
  refine ⟨rfl, heq_of_eq ?_⟩
  funext x
  obtain ⟨y, rfl⟩ := (capNodeEquiv G.tree).surjective x
  rcases y with j | a
  · rw [capNodeEquiv_inl]
    show ((capNodeEquiv G.tree).symm (rootBranch G.tree j).toNode).elim (fun _ => p) (fun a => layer (liftNode a)) = _
    rw [capNodeEquiv_symm_root]
    exact (hl j (rootBranch G.tree j) rfl).symm
  · rw [capNodeEquiv_inr]
    show ((capNodeEquiv G.tree).symm (liftNode a)).elim (fun _ => p) (fun a => layer (liftNode a)) = _
    rw [capNodeEquiv_symm_lift]
    rfl


theorem capGarden_injective (G G' : Garden (2 * 3)) (hs : ∀ c, G.sig c = childSig c)
    (hs' : ∀ c, G'.sig c = childSig c) (h : capGarden G hs = capGarden G' hs') : G = G' := by
  have ht : G.tree = G'.tree := capTree_injective (congrArg Garden.tree h)
  have hsg : G.sig = G'.sig := funext fun c => (hs c).trans (hs' c).symm
  obtain ⟨sg, tr, pr, mk, a1, a2, a3⟩ := G
  obtain ⟨sg', tr', pr', mk', b1, b2, b3⟩ := G'
  simp only at ht hsg
  subst ht hsg
  simp only [capGarden, Garden.mk.injEq, heq_eq_eq] at h
  obtain ⟨_, _, hp, hm⟩ := h
  have hpr : pr = pr' := by
    funext ℓ
    have := congrFun hp (capLeafEquiv tr ℓ)
    simpa using this
  have hmk : mk = mk' := by
    funext ℓ
    have := congrFun hm (capLeafEquiv tr ℓ)
    simpa using this
  subst hpr hmk
  rfl

theorem capLayered_injective (LG LG' : LayeredGarden (2 * 3)) (hs : ∀ c, LG.garden.sig c = childSig c)
    (hs' : ∀ c, LG'.garden.sig c = childSig c) (p : ℕ) (hp : ∀ a, LG.layer a ≤ p)
    (hp' : ∀ a, LG'.layer a ≤ p) (h : capLayered LG hs p hp = capLayered LG' hs' p hp') : LG = LG' := by
  have hg : LG.garden = LG'.garden :=
    capGarden_injective _ _ hs hs' (congrArg LayeredGarden.garden h)
  obtain ⟨G, layer, hl⟩ := LG
  obtain ⟨G', layer', hl'⟩ := LG'
  simp only at hg
  subst hg
  have hlay : layer = layer' := by
    simp only [capLayered, LayeredGarden.mk.injEq, heq_eq_eq, true_and] at h
    funext a
    have := congrFun h (liftNode a)
    simp only [capNodeEquiv_symm_lift, Sum.elim_inr] at this
    exact this
  subst hlay
  rfl

end WaveTurbulence.FlowerP7
