/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.FlowerTop.Port.P7.CapAttach
/-! FLOWER-P7: top orders of the cap, and the tree-kind condition as a condition on the vector of top orders
of the six child trees. -/
@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.FlowerP7
open TTree Finset

variable {T : Fin (2 * 3) → TTree}

theorem layerElim_lift (LG : LayeredGarden (2 * 3)) (p : ℕ) (a : GNode LG.garden.tree) :
    Sum.elim (fun _ : Fin 2 => p) LG.layer ((capNodeEquiv LG.garden.tree).symm (liftNode a)) = LG.layer a := by
  rw [capNodeEquiv_symm_lift]; rfl

theorem layerElim_root (LG : LayeredGarden (2 * 3)) (p : ℕ) (j : Fin 2) :
    Sum.elim (fun _ : Fin 2 => p) LG.layer ((capNodeEquiv LG.garden.tree).symm (rootBranch LG.garden.tree j).toNode)
      = p := by
  rw [capNodeEquiv_symm_root]; rfl

theorem topCountBelow_cap_lift (LG : LayeredGarden (2 * 3)) (hsig : ∀ c, LG.garden.sig c = childSig c)
    (p : ℕ) (hp : ∀ a, LG.layer a ≤ p) (a : GNode LG.garden.tree) :
    (capLayered LG hsig p hp).topCountBelow p (liftNode a) = LG.topCountBelow p a := by
  classical
  unfold LayeredGarden.topCountBelow
  have : (Finset.univ.filter fun b : GBranch (capTree LG.garden.tree) =>
      (liftNode a).IsDesc b.toNode ∧ (capLayered LG hsig p hp).layer b.toNode = p) =
      (Finset.univ.filter fun b : GBranch LG.garden.tree => a.IsDesc b.toNode ∧ LG.layer b.toNode = p).image
        liftBranch := by
    ext b
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image]
    constructor
    · rintro ⟨h, hl⟩
      by_cases hr : b.1.2 = []
      · exfalso
        obtain ⟨⟨j, q⟩, hb⟩ := b
        simp only at hr
        subst hr
        exact lift_not_isDesc_root j a (by simpa [rootBranch, GBranch.toNode] using h)
      · obtain ⟨b', rfl⟩ := exists_liftBranch b hr
        rw [liftBranch_toNode, isDesc_lift] at h
        rw [liftBranch_toNode, layerElim_lift] at hl
        exact ⟨b', ⟨h, hl⟩, rfl⟩
    · rintro ⟨b', ⟨h, hl⟩, rfl⟩
      rw [liftBranch_toNode, isDesc_lift, layerElim_lift]
      exact ⟨h, hl⟩
  rw [this, Finset.card_image_of_injective _ liftBranch_injective]

theorem topOrder_eq_topCountBelow_root {w : ℕ} (LG : LayeredGarden w) (p : ℕ) (c : Fin w) :
    LG.topOrder p c = LG.topCountBelow p (GNode.root LG.garden.tree c) := by
  classical
  unfold LayeredGarden.topOrder LayeredGarden.topCountBelow
  congr 1
  ext b
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, GNode.IsDesc, GNode.root, GBranch.toNode]
  simp [eq_comm]

/-- The top order of a cap tree: the root and the top orders of the three children. -/
theorem topOrder_cap (LG : LayeredGarden (2 * 3)) (hsig : ∀ c, LG.garden.sig c = childSig c) (p : ℕ)
    (hp : ∀ a, LG.layer a ≤ p) (j : Fin 2) :
    (capLayered LG hsig p hp).topOrder p j = 1 + ∑ i : Fin 3, LG.topOrder p (idx j i) := by
  classical
  unfold LayeredGarden.topOrder
  have hsplit : (Finset.univ.filter fun b : GBranch (capTree LG.garden.tree) =>
      b.1.1 = j ∧ (capLayered LG hsig p hp).layer b.toNode = p) =
      insert (rootBranch LG.garden.tree j)
        ((Finset.univ.filter fun b : GBranch LG.garden.tree =>
          jOf b.1.1 = j ∧ LG.layer b.toNode = p).image liftBranch) := by
    ext b
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert, Finset.mem_image]
    constructor
    · rintro ⟨h1, h2⟩
      by_cases hr : b.1.2 = []
      · left
        obtain ⟨⟨j', q⟩, hb⟩ := b
        simp only at hr h1
        subst hr h1
        rfl
      · right
        obtain ⟨b', rfl⟩ := exists_liftBranch b hr
        rw [liftBranch_toNode, layerElim_lift] at h2
        refine ⟨b', ⟨?_, h2⟩, rfl⟩
        simpa [liftBranch, liftAddr] using h1
    · rintro (rfl | ⟨b', ⟨h1, h2⟩, rfl⟩)
      · exact ⟨rfl, capLayered_layer_root LG hsig p hp j⟩
      · refine ⟨by simpa [liftBranch, liftAddr] using h1, ?_⟩
        rw [liftBranch_toNode, layerElim_lift]; exact h2
  rw [hsplit, Finset.card_insert_of_notMem, Finset.card_image_of_injective _ liftBranch_injective]
  · rw [add_comm]
    congr 1
    -- the branches of the three children
    have : (Finset.univ.filter fun b : GBranch LG.garden.tree => jOf b.1.1 = j ∧ LG.layer b.toNode = p) =
        Finset.univ.biUnion fun i : Fin 3 =>
          (Finset.univ.filter fun b : GBranch LG.garden.tree => b.1.1 = idx j i ∧ LG.layer b.toNode = p) := by
      ext b
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_biUnion]
      constructor
      · rintro ⟨h1, h2⟩
        exact ⟨iOf b.1.1, by rw [← h1, idx_jOf_iOf], h2⟩
      · rintro ⟨i, h1, h2⟩
        exact ⟨by rw [h1]; simp, h2⟩
    rw [this, Finset.card_biUnion]
    intro i _ i' _ hii'
    rw [Function.onFun, Finset.disjoint_left]
    intro b hb hb'
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hb hb'
    exact hii' (by
      have := (idx_injective (hb.1.symm.trans hb'.1))
      exact this.2)
  · simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and, not_exists, not_and]
    intro b' _ h
    exact lift_ne_root b' j h

/-- The tree-kind condition as a condition on the vector of top orders of the six trees. -/
def VecKindOK (Ntr : ℕ) : TreeKind → (Fin (2 * 3) → ℕ) → Prop
  | .tr, v => ∀ j : Fin 2, 1 + ∑ i : Fin 3, v (idx j i) ≤ Ntr
  | .L0, v => ∀ j : Fin 2, Ntr < 1 + ∑ i : Fin 3, v (idx j i) ∧ ∀ i : Fin 3, v (idx j i) ≤ Ntr

theorem treeKindOK_cap (LG : LayeredGarden (2 * 3)) (hsig : ∀ c, LG.garden.sig c = childSig c) (p : ℕ)
    (hp : ∀ a, LG.layer a ≤ p) (Ntr : ℕ) (kind : TreeKind) :
    (capLayered LG hsig p hp).TreeKindOK p Ntr kind ↔ VecKindOK Ntr kind (fun c => LG.topOrder p c) := by
  cases kind with
  | tr =>
    unfold LayeredGarden.TreeKindOK VecKindOK
    simp only [topOrder_cap]
  | L0 =>
    unfold LayeredGarden.TreeKindOK VecKindOK
    simp only [topOrder_cap]
    refine forall_congr' fun j => and_congr_right' ?_
    constructor
    · intro h i
      have := h (rootBranch LG.garden.tree j) rfl i
      rw [rootBranch_child, topCountBelow_cap_lift, ← topOrder_eq_topCountBelow_root] at this
      exact this
    · intro h b hb i
      have hb' : b = rootBranch LG.garden.tree j := Subtype.ext hb
      subst hb'
      rw [rootBranch_child, topCountBelow_cap_lift, ← topOrder_eq_topCountBelow_root]
      exact h i

end WaveTurbulence.FlowerP7
