/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Molecule.LeafExchangeInvolution

/-! # Proof-independent address formula for the leaf exchange

The formula records the actual subtree move and free-child switch. Its
restricted involution is proved on valid leaves of the actual inserted
forest, rather than assumed for arbitrary addresses.
-/

public section
namespace WaveTurbulence.Twist
open TTree

/-- The uniform address move at two distinguished slots. -/
@[expose] def exchangeAddress {w : ℕ} (h₀ h₁ : Fin w × Path) (keep : Fin 3) (a : Fin w × Path) : Fin w × Path :=
  if a.1 = h₀.1 ∧ h₀.2 <+: a.2 then
    (h₁.1,h₁.2 ++ switchPath keep (a.2.drop h₀.2.length))
  else if a = h₁ then h₀ else a

variable {w : ℕ} (F : Fin w → TTree) (h₀ h₁ : GLeaf F) (keep : Fin 3) (t : TTree)

/-- The actual leaf bijection has the uniform address formula. -/
theorem exchangeLeafEquiv_address (l : GLeaf (insertLeaf F h₀ t)) :
    (exchangeLeafEquiv F h₀ h₁ keep t l).1 = exchangeAddress h₀.1 h₁.1 keep l.1 := by
  obtain ⟨p,rfl⟩ := (insertionLeafEquiv F h₀ t).surjective l
  change (exchangeLeafEquiv F h₀ h₁ keep t (insertionLeafMap F h₀ t p)).1 = _
  rw [exchangeLeafEquiv_piece]
  cases p with
  | inl l =>
    have hout : ¬ (l.1.1.1 = h₀.1.1 ∧ h₀.1.2 <+: l.1.1.2) := by
      rintro ⟨hi,hp⟩
      have he := leaf_prefix_eq h₀.2 (hi ▸ l.1.2) hp
      exact l.2 (Subtype.ext (Prod.ext hi he.symm))
    change (Equiv.swap h₀ h₁ l.1).1 = exchangeAddress h₀.1 h₁.1 keep l.1.1
    by_cases he : l.1 = h₁
    · have hv : l.1.1 = h₁.1 := congrArg Subtype.val he
      rw [exchangeAddress,ite_eq_right hout,ite_eq_left hv]
      rw [he,Equiv.swap_apply_right]
    · have hv : l.1.1 ≠ h₁.1 := fun hv => he (Subtype.ext hv)
      simp only [exchangeAddress,hout,hv,ite_false]
      rw [Equiv.swap_apply_of_ne_of_ne l.2 he]
  | inr q =>
    change (h₁.1.1,h₁.1.2 ++ switchPath keep q.1) =
      exchangeAddress h₀.1 h₁.1 keep (h₀.1.1,h₀.1.2 ++ q.1)
    simp [exchangeAddress]

/-- The address formula reverses itself on the actual old leaves. -/
theorem exchangeAddress_twice (l : GLeaf (insertLeaf F h₀ t)) :
    exchangeAddress h₁.1 h₀.1 keep (exchangeAddress h₀.1 h₁.1 keep l.1) = l.1 := by
  rw [← exchangeLeafEquiv_address F h₀ h₁ keep t l,
    ← exchangeLeafEquiv_address F h₁ h₀ keep (switchFree keep t)]
  exact exchangeLeafEquiv_twice_val F h₀ h₁ keep t l

end WaveTurbulence.Twist
