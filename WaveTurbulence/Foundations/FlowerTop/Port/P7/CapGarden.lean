/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.FlowerTop.Port.P7.CapTree
public import WaveTurbulence.Foundations.WaveB.FrozenB1
/-! FLOWER-P7: the two-root cap of a width-six garden (as a couple) and of a width-six layered garden.
The six trees carry the alternating signature `(+,-,+,-,+,-)`: root `j` of sign `(-1)^j` has children of
signs `(ζ, -ζ, ζ)`, so the child `idx j i` has sign `pathSign ((-1)^j) [i]`. -/
@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.FlowerP7
open TTree Finset

theorem pathSign_cons (ζ : ℤˣ) (i : Fin 3) (q : Path) :
    pathSign ζ (i :: q) = pathSign (pathSign ζ [i]) q := by
  simp only [pathSign, List.count_cons, List.count_nil, pow_add, mul_assoc]
  simp [mul_comm, mul_left_comm]

/-- The signs of the six child trees of a couple with root signs `(+,-)`. -/
def childSig (c : Fin (2 * 3)) : ℤˣ := pathSign (![1, -1] (jOf c)) [iOf c]

theorem nodeSign_cap {sig6 : Fin (2 * 3) → ℤˣ} (hsig : ∀ c, sig6 c = childSig c) (a : Fin (2 * 3) × Path) :
    nodeSign (![1, -1] : Fin 2 → ℤˣ) (liftAddr a) = nodeSign sig6 a := by
  simp only [nodeSign, liftAddr]
  rw [pathSign_cons, hsig]
  rfl

/-- The capped couple of a width-six garden with the alternating child signatures. -/
@[reducible] noncomputable def capGarden (G : Garden (2 * 3)) (hsig : ∀ c, G.sig c = childSig c) : Garden 2 where
  sig := ![1, -1]
  tree := capTree G.tree
  pair := fun ℓ => capLeafEquiv G.tree (G.pair ((capLeafEquiv G.tree).symm ℓ))
  mark := fun ℓ => G.mark ((capLeafEquiv G.tree).symm ℓ)
  pair_pair := fun ℓ => by
    simp [G.pair_pair]
  pair_eq_iff := fun ℓ => by
    show capLeafEquiv G.tree (G.pair ((capLeafEquiv G.tree).symm ℓ)) = ℓ ↔
      G.mark ((capLeafEquiv G.tree).symm ℓ) ≠ none
    rw [← G.pair_eq_iff]
    constructor
    · intro h
      have := congrArg (capLeafEquiv G.tree).symm h
      simpa using this
    · intro h
      rw [h]
      simp
  pair_sign := fun ℓ hℓ => by
    have hne : G.pair ((capLeafEquiv G.tree).symm ℓ) ≠ (capLeafEquiv G.tree).symm ℓ := by
      intro h
      apply hℓ
      show capLeafEquiv G.tree (G.pair ((capLeafEquiv G.tree).symm ℓ)) = ℓ
      rw [h]; simp
    have h1 := G.pair_sign _ hne
    have e1 : (capLeafEquiv G.tree (G.pair ((capLeafEquiv G.tree).symm ℓ))).1 =
        liftAddr (G.pair ((capLeafEquiv G.tree).symm ℓ)).1 := rfl
    have e2 : ℓ.1 = liftAddr ((capLeafEquiv G.tree).symm ℓ).1 := by
      have := congrArg (fun x : GLeaf (capTree G.tree) => x.1) ((capLeafEquiv G.tree).apply_symm_apply ℓ)
      exact this.symm
    show nodeSign (![1, -1] : Fin 2 → ℤˣ) (capLeafEquiv G.tree (G.pair ((capLeafEquiv G.tree).symm ℓ))).1 =
      -nodeSign (![1, -1] : Fin 2 → ℤˣ) ℓ.1
    rw [e1, e2, nodeSign_cap hsig, nodeSign_cap hsig]
    exact h1

end WaveTurbulence.FlowerP7
