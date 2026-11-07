/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.FlowerTop.Port.P7.CapDecoration
/-! FLOWER-P7: bookkeeping of the cap: products over branching nodes, `ε`, `ζ`, the order, the input leaves. -/
@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.FlowerP7
open TTree Finset

variable {d : ℕ}

theorem prod_cap_branch {M : Type*} [CommMonoid M] (T : Fin (2 * 3) → TTree) (f : GBranch (capTree T) → M) :
    ∏ b, f b = (∏ j : Fin 2, f (rootBranch T j)) * ∏ a : GBranch T, f (liftBranch a) := by
  rw [← Equiv.prod_comp (capBranchEquiv T) f, Fintype.prod_sum_type]
  rfl

theorem sum_fin6 {M : Type*} [AddCommMonoid M] (f : Fin (2 * 3) → M) :
    ∑ c, f c = ∑ j : Fin 2, ∑ i : Fin 3, f (idx j i) := by
  calc ∑ c, f c = ∑ x : Fin 2 × Fin 3, f (idx x.1 x.2) := (Equiv.sum_comp finProdFinEquiv f).symm
    _ = _ := Fintype.sum_prod_type' (fun j i => f (idx j i))

theorem order_cap (G : Garden (2 * 3)) (hsig : ∀ c, G.sig c = childSig c) :
    (capGarden G hsig).order = G.order + 2 := by
  unfold Garden.order
  show ∑ j : Fin 2, (capTree G.tree j).order = ∑ c, (G.tree c).order + 2
  rw [sum_fin6]
  simp only [cap_order, Finset.sum_add_distrib, Fin.sum_univ_three, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, smul_eq_mul]

theorem epsDec_cap (G : Garden (2 * 3)) (hsig : ∀ c, G.sig c = childSig c) (κ' : GNode G.tree → (Fin d → ℤ)) :
    epsDec (capGarden G hsig) (upperDec (T := G.tree) κ') =
      (∏ j : Fin 2, epsCoef (κ' (GNode.root G.tree (idx j 0))) (κ' (GNode.root G.tree (idx j 1)))
        (κ' (GNode.root G.tree (idx j 2)))) * epsDec G κ' := by
  unfold epsDec
  rw [prod_cap_branch]
  congr 1
  · refine Finset.prod_congr rfl fun j _ => ?_
    show epsCoef (upperDec κ' ((rootBranch G.tree j).child 0)) (upperDec κ' ((rootBranch G.tree j).child 1))
      (upperDec κ' ((rootBranch G.tree j).child 2)) = _
    rw [rootBranch_child, rootBranch_child, rootBranch_child, upperDec_lift, upperDec_lift, upperDec_lift]
  · refine Finset.prod_congr rfl fun b _ => ?_
    show epsCoef (upperDec κ' ((liftBranch b).child 0)) (upperDec κ' ((liftBranch b).child 1))
      (upperDec κ' ((liftBranch b).child 2)) = _
    rw [liftBranch_child, liftBranch_child, liftBranch_child, upperDec_lift, upperDec_lift, upperDec_lift]

theorem sign_cap_lift (G : Garden (2 * 3)) (hsig : ∀ c, G.sig c = childSig c) (a : GNode G.tree) :
    (capGarden G hsig).sign (liftNode a) = G.sign a := by
  show nodeSign (![1, -1] : Fin 2 → ℤˣ) (liftAddr a.1) = nodeSign G.sig a.1
  exact nodeSign_cap hsig a.1

theorem sign_cap_root (G : Garden (2 * 3)) (hsig : ∀ c, G.sig c = childSig c) (j : Fin 2) :
    (capGarden G hsig).sign (rootBranch G.tree j).toNode = (![1, -1] : Fin 2 → ℤˣ) j := by
  show nodeSign (![1, -1] : Fin 2 → ℤˣ) (j, []) = _
  simp [nodeSign, pathSign]

theorem zeta_cap (G : Garden (2 * 3)) (hsig : ∀ c, G.sig c = childSig c) :
    (capGarden G hsig).zeta = G.zeta := by
  unfold Garden.zeta
  rw [prod_cap_branch]
  have h1 : ∏ j : Fin 2, (Complex.I * ((((capGarden G hsig).sign (rootBranch G.tree j).toNode : ℤˣ) : ℤ) : ℂ)) = 1 := by
    simp only [sign_cap_root, Fin.prod_univ_two]
    simp
  rw [h1, one_mul]
  refine Finset.prod_congr rfl fun b _ => ?_
  rw [liftBranch_toNode, sign_cap_lift]

theorem mark_cap_lift (G : Garden (2 * 3)) (hsig : ∀ c, G.sig c = childSig c) (ℓ : GLeaf G.tree) :
    (capGarden G hsig).mark (liftLeaf ℓ) = G.mark ℓ := by
  show G.mark ((capLeafEquiv G.tree).symm (liftLeaf ℓ)) = _
  have : (capLeafEquiv G.tree).symm (liftLeaf ℓ) = ℓ := by
    rw [Equiv.symm_apply_eq]; rfl
  rw [this]

theorem mem_inputLeaves_cap_lift (G : Garden (2 * 3)) (hsig : ∀ c, G.sig c = childSig c) (ℓ : GLeaf G.tree) :
    liftLeaf ℓ ∈ inputLeaves (capGarden G hsig) ↔ ℓ ∈ inputLeaves G := by
  simp only [inputLeaves, Finset.mem_filter, Finset.mem_univ, true_and]
  rw [liftLeaf_toNode, sign_cap_lift G hsig, mark_cap_lift G hsig]

theorem inputLeaves_cap (G : Garden (2 * 3)) (hsig : ∀ c, G.sig c = childSig c) :
    inputLeaves (capGarden G hsig) = (inputLeaves G).image liftLeaf := by
  ext ℓ
  obtain ⟨ℓ', rfl⟩ := (capLeafEquiv G.tree).surjective ℓ
  rw [capLeafEquiv_apply, mem_inputLeaves_cap_lift, Finset.mem_image]
  constructor
  · intro h
    exact ⟨ℓ', h, rfl⟩
  · rintro ⟨x, hx, hxe⟩
    have := liftLeaf_injective hxe
    rw [← this]; exact hx

end WaveTurbulence.FlowerP7
