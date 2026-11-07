/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.FlowerTop.Port.P7.CapGarden
/-! FLOWER-P7: the layered cap.  The two roots are placed in layer `p` (an upper bound for all layers of the
six child trees). -/
@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.FlowerP7
open TTree Finset

variable {T : Fin (2 * 3) → TTree}

theorem capNodeEquiv_inl (j : Fin 2) : capNodeEquiv T (Sum.inl j) = (rootBranch T j).toNode := rfl
theorem capNodeEquiv_inr (a : GNode T) : capNodeEquiv T (Sum.inr a) = liftNode a := rfl
theorem capBranchEquiv_inl (j : Fin 2) : capBranchEquiv T (Sum.inl j) = rootBranch T j := rfl
theorem capBranchEquiv_inr (a : GBranch T) : capBranchEquiv T (Sum.inr a) = liftBranch a := rfl

theorem capNodeEquiv_symm_lift (a : GNode T) : (capNodeEquiv T).symm (liftNode a) = Sum.inr a := by
  rw [Equiv.symm_apply_eq]; rfl

theorem capNodeEquiv_symm_root (j : Fin 2) : (capNodeEquiv T).symm (rootBranch T j).toNode = Sum.inl j := by
  rw [Equiv.symm_apply_eq]; rfl

theorem capLeafEquiv_apply (ℓ : GLeaf T) : capLeafEquiv T ℓ = liftLeaf ℓ := rfl

theorem liftLeaf_toNode (ℓ : GLeaf T) : (liftLeaf ℓ).toNode = liftNode ℓ.toNode := rfl
theorem liftBranch_toNode (b : GBranch T) : (liftBranch b).toNode = liftNode b.toNode := rfl

theorem liftBranch_child (b : GBranch T) (i : Fin 3) : (liftBranch b).child i = liftNode (b.child i) := by
  apply Subtype.ext
  simp [liftBranch, liftNode, liftAddr, GBranch.child]

theorem rootBranch_child (j : Fin 2) (i : Fin 3) :
    (rootBranch T j).child i = liftNode (GNode.root T (idx j i)) := by
  apply Subtype.ext
  simp [rootBranch, liftNode, liftAddr, GBranch.child, GNode.root]

/-- The layered cap. -/
@[reducible] noncomputable def capLayered (LG : LayeredGarden (2 * 3)) (hsig : ∀ c, LG.garden.sig c = childSig c) (p : ℕ)
    (hp : ∀ a, LG.layer a ≤ p) : LayeredGarden 2 where
  garden := capGarden LG.garden hsig
  layer := fun x => ((capNodeEquiv LG.garden.tree).symm x).elim (fun _ => p) LG.layer
  isLayering := by
    constructor
    · intro b i
      obtain ⟨y, rfl⟩ := (capBranchEquiv LG.garden.tree).surjective b
      rcases y with j | b'
      · show ((capNodeEquiv LG.garden.tree).symm ((rootBranch LG.garden.tree j).child i)).elim (fun _ => p) LG.layer ≤
          ((capNodeEquiv LG.garden.tree).symm (rootBranch LG.garden.tree j).toNode).elim (fun _ => p) LG.layer
        rw [rootBranch_child, capNodeEquiv_symm_lift, capNodeEquiv_symm_root]
        exact hp _
      · show ((capNodeEquiv LG.garden.tree).symm ((liftBranch b').child i)).elim (fun _ => p) LG.layer ≤
          ((capNodeEquiv LG.garden.tree).symm (liftBranch b').toNode).elim (fun _ => p) LG.layer
        rw [liftBranch_child, liftBranch_toNode, capNodeEquiv_symm_lift, capNodeEquiv_symm_lift]
        exact LG.isLayering.1 b' i
    · intro ℓ
      obtain ⟨ℓ', rfl⟩ := (capLeafEquiv LG.garden.tree).surjective ℓ
      show ((capNodeEquiv LG.garden.tree).symm (capLeafEquiv LG.garden.tree ℓ').toNode).elim (fun _ => p) LG.layer =
        ((capNodeEquiv LG.garden.tree).symm
          (capLeafEquiv LG.garden.tree (LG.garden.pair ((capLeafEquiv LG.garden.tree).symm
            (capLeafEquiv LG.garden.tree ℓ')))).toNode).elim (fun _ => p) LG.layer
      rw [Equiv.symm_apply_apply, capLeafEquiv_apply, capLeafEquiv_apply, liftLeaf_toNode, liftLeaf_toNode,
        capNodeEquiv_symm_lift, capNodeEquiv_symm_lift]
      exact LG.isLayering.2 ℓ'

theorem capLayered_layer_lift (LG : LayeredGarden (2 * 3)) (hsig : ∀ c, LG.garden.sig c = childSig c) (p : ℕ)
    (hp : ∀ a, LG.layer a ≤ p) (a : GNode LG.garden.tree) :
    (capLayered LG hsig p hp).layer (liftNode a) = LG.layer a := by
  show ((capNodeEquiv LG.garden.tree).symm (liftNode a)).elim (fun _ => p) LG.layer = _
  rw [capNodeEquiv_symm_lift]; rfl

theorem capLayered_layer_root (LG : LayeredGarden (2 * 3)) (hsig : ∀ c, LG.garden.sig c = childSig c) (p : ℕ)
    (hp : ∀ a, LG.layer a ≤ p) (j : Fin 2) :
    (capLayered LG hsig p hp).layer (rootBranch LG.garden.tree j).toNode = p := by
  show ((capNodeEquiv LG.garden.tree).symm (rootBranch LG.garden.tree j).toNode).elim (fun _ => p) LG.layer = _
  rw [capNodeEquiv_symm_root]; rfl

end WaveTurbulence.FlowerP7
