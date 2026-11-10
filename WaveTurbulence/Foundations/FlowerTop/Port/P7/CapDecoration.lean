/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.FlowerTop.Port.P7.CapLayered
/-! FLOWER-P7: decorations of the capped garden.  A decoration of the cap with both root labels `0` is the
same as a decoration of the six-tree garden whose root labels satisfy the two outer constraints
`n (idx j 0) - n (idx j 1) + n (idx j 2) = 0`. -/
@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.FlowerP7
open TTree Finset

variable {d : ℕ}

/-- Restrict a labelling of the capped nodes to the six trees. -/
def lowerDec {T : Fin (2 * 3) → TTree} (κ : GNode (capTree T) → (Fin d → ℤ)) : GNode T → (Fin d → ℤ) :=
  fun a => κ (liftNode a)

/-- Extend a labelling of the six trees by `0` at both roots. -/
noncomputable def upperDec {T : Fin (2 * 3) → TTree} (κ' : GNode T → (Fin d → ℤ)) :
    GNode (capTree T) → (Fin d → ℤ) :=
  fun x => ((capNodeEquiv T).symm x).elim (fun _ => 0) κ'

theorem upperDec_lift {T : Fin (2 * 3) → TTree} (κ' : GNode T → (Fin d → ℤ)) (a : GNode T) :
    upperDec κ' (liftNode a) = κ' a := by
  simp [upperDec, capNodeEquiv_symm_lift]

theorem upperDec_root {T : Fin (2 * 3) → TTree} (κ' : GNode T → (Fin d → ℤ)) (j : Fin 2) :
    upperDec κ' (rootBranch T j).toNode = 0 := by
  simp [upperDec, capNodeEquiv_symm_root]

theorem lower_upper {T : Fin (2 * 3) → TTree} (κ' : GNode T → (Fin d → ℤ)) :
    lowerDec (upperDec κ') = κ' := by
  funext a
  exact upperDec_lift κ' a

theorem upper_lower {T : Fin (2 * 3) → TTree} (κ : GNode (capTree T) → (Fin d → ℤ))
    (h : ∀ j, κ (rootBranch T j).toNode = 0) : upperDec (lowerDec κ) = κ := by
  funext x
  obtain ⟨y, rfl⟩ := (capNodeEquiv T).surjective x
  rcases y with j | a
  · rw [capNodeEquiv_inl, upperDec_root, h]
  · rw [capNodeEquiv_inr, upperDec_lift]; rfl

/-- The outer constraints on the six root labels. -/
def OuterOK {T : Fin (2 * 3) → TTree} (κ' : GNode T → (Fin d → ℤ)) : Prop :=
  ∀ j : Fin 2, κ' (GNode.root T (idx j 0)) - κ' (GNode.root T (idx j 1)) + κ' (GNode.root T (idx j 2)) = 0

/-- The six root labels. -/
def rootLabels {T : Fin (2 * 3) → TTree} (κ' : GNode T → (Fin d → ℤ)) : Fin (2 * 3) → (Fin d → ℤ) :=
  fun c => κ' (GNode.root T c)

theorem isDecoration_lower (G : Garden (2 * 3)) (hsig : ∀ c, G.sig c = childSig c)
    {κ : GNode (capTree G.tree) → (Fin d → ℤ)} (h : IsDecoration (capGarden G hsig) κ) :
    IsDecoration G (lowerDec (T := G.tree) κ) := by
  constructor
  · intro b
    have h1 : κ (liftBranch b).toNode = κ ((liftBranch b).child 0) - κ ((liftBranch b).child 1) +
        κ ((liftBranch b).child 2) := h.1 (liftBranch b)
    rw [liftBranch_child, liftBranch_child, liftBranch_child, liftBranch_toNode] at h1
    exact h1
  · intro ℓ
    have h1 : κ (liftLeaf ℓ).toNode =
        κ ((capLeafEquiv G.tree) (G.pair ((capLeafEquiv G.tree).symm (liftLeaf ℓ)))).toNode := h.2 (liftLeaf ℓ)
    have e : (capLeafEquiv G.tree).symm (liftLeaf ℓ) = ℓ := by
      rw [Equiv.symm_apply_eq]; rfl
    rw [e, capLeafEquiv_apply, liftLeaf_toNode, liftLeaf_toNode] at h1
    exact h1

theorem outerOK_lower (G : Garden (2 * 3)) (hsig : ∀ c, G.sig c = childSig c)
    {κ : GNode (capTree G.tree) → (Fin d → ℤ)} (h : IsDecoration (capGarden G hsig) κ)
    (h0 : ∀ j, κ (rootBranch G.tree j).toNode = 0) :
    OuterOK (lowerDec (T := G.tree) κ) := by
  intro j
  have h1 : κ (rootBranch G.tree j).toNode = κ ((rootBranch G.tree j).child 0) -
      κ ((rootBranch G.tree j).child 1) + κ ((rootBranch G.tree j).child 2) := h.1 (rootBranch G.tree j)
  rw [rootBranch_child, rootBranch_child, rootBranch_child, h0 j] at h1
  exact h1.symm

theorem isDecoration_upper (G : Garden (2 * 3)) (hsig : ∀ c, G.sig c = childSig c)
    {κ' : GNode G.tree → (Fin d → ℤ)} (h : IsDecoration G κ') (ho : OuterOK κ') :
    IsDecoration (capGarden G hsig) (upperDec (T := G.tree) κ') := by
  constructor
  · intro b
    obtain ⟨y, rfl⟩ := (capBranchEquiv G.tree).surjective b
    rcases y with j | b'
    · show upperDec κ' (rootBranch G.tree j).toNode = upperDec κ' ((rootBranch G.tree j).child 0) -
        upperDec κ' ((rootBranch G.tree j).child 1) + upperDec κ' ((rootBranch G.tree j).child 2)
      rw [rootBranch_child, rootBranch_child, rootBranch_child, upperDec_root, upperDec_lift,
        upperDec_lift, upperDec_lift]
      exact (ho j).symm
    · show upperDec κ' (liftBranch b').toNode = upperDec κ' ((liftBranch b').child 0) -
        upperDec κ' ((liftBranch b').child 1) + upperDec κ' ((liftBranch b').child 2)
      rw [liftBranch_child, liftBranch_child, liftBranch_child, liftBranch_toNode, upperDec_lift,
        upperDec_lift, upperDec_lift, upperDec_lift]
      exact h.1 b'
  · intro ℓ
    obtain ⟨ℓ', rfl⟩ := (capLeafEquiv G.tree).surjective ℓ
    show upperDec κ' (capLeafEquiv G.tree ℓ').toNode =
      upperDec κ' (capLeafEquiv G.tree (G.pair ((capLeafEquiv G.tree).symm (capLeafEquiv G.tree ℓ')))).toNode
    rw [Equiv.symm_apply_apply, capLeafEquiv_apply, capLeafEquiv_apply, liftLeaf_toNode, liftLeaf_toNode,
      upperDec_lift, upperDec_lift]
    exact h.2 ℓ'


theorem capGarden_isFlower_iff (G : Garden (2 * 3)) (hsig : ∀ c, G.sig c = childSig c) (ℓ : GLeaf G.tree) :
    (capGarden G hsig).IsFlower (liftLeaf ℓ) ↔ G.IsFlower ℓ := by
  have e : (capLeafEquiv G.tree).symm (liftLeaf ℓ) = ℓ := by
    rw [Equiv.symm_apply_eq]; rfl
  show G.mark ((capLeafEquiv G.tree).symm (liftLeaf ℓ)) = some MarkTag.equal ↔ _
  rw [e]; rfl

/-- The decorations of the six trees with the outer constraints on the root labels. -/
def Dec6 (G : Garden (2 * 3)) (d : ℕ) : Type :=
  {κ' : GNode G.tree → (Fin d → ℤ) // IsDecoration G κ' ∧ OuterOK κ' ∧
    ∀ ℓ : GLeaf G.tree, G.IsFlower ℓ → κ' ℓ.toNode = 0}

/-- Decorations of the cap with root labels `0` are the outer-constrained decorations of the six trees. -/
noncomputable def capDecEquiv (G : Garden (2 * 3)) (hsig : ∀ c, G.sig c = childSig c) (d : ℕ) :
    GenDecoration (capGarden G hsig) d (fun _ => 0) 0 ≃ Dec6 G d where
  toFun κ := ⟨lowerDec (T := G.tree) κ.1, isDecoration_lower G hsig κ.2.1,
    outerOK_lower G hsig κ.2.1 (fun j => κ.2.2.1 j),
    fun ℓ hℓ => κ.2.2.2 (liftLeaf ℓ) ((capGarden_isFlower_iff G hsig ℓ).2 hℓ)⟩
  invFun κ' := ⟨upperDec (T := G.tree) κ'.1, isDecoration_upper G hsig κ'.2.1 κ'.2.2.1,
    fun j => upperDec_root κ'.1 j,
    fun ℓ hℓ => by
      obtain ⟨ℓ', rfl⟩ := (capLeafEquiv G.tree).surjective ℓ
      rw [capLeafEquiv_apply] at hℓ ⊢
      exact (upperDec_lift κ'.1 ℓ'.toNode).trans
        (κ'.2.2.2 ℓ' ((capGarden_isFlower_iff G hsig ℓ').1 hℓ))⟩
  left_inv κ := by
    apply Subtype.ext
    exact upper_lower κ.1 (fun j => κ.2.2.1 j)
  right_inv κ' := by
    apply Subtype.ext
    exact lower_upper κ'.1

end WaveTurbulence.FlowerP7
