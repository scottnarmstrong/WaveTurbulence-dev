/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.XChain.ForestGraft
/-! Transport the actual lower pairing through the concrete leaf grafting bijection. -/
@[expose] public section
namespace WaveTurbulence.Induct

abbrev attachedSign {w : ℕ} {top : Fin w → TTree} {f : Fin w → TTree.Path → TTree}
    (sig : Fin w → ℤˣ) (x : AttachedLeaf top f) : ℤˣ :=
  TTree.pathSign (nodeSign sig x.1.1) x.2.1

/-- A fixed-point-free pairing of lower leaves with opposite inherited signs gives a literal
plain Garden, with the grafted ordered trees and no quotient by tree automorphisms. -/
noncomputable def plainGraftedGarden {w : ℕ} (sig : Fin w → ℤˣ) (top : Fin w → TTree)
    (f : Fin w → TTree.Path → TTree) (pair : AttachedLeaf top f → AttachedLeaf top f)
    (hinv : Function.Involutive pair) (hne : ∀ x, pair x ≠ x)
    (hsign : ∀ x, attachedSign sig (pair x) = -attachedSign sig x) : Garden w where
  sig := sig
  tree := graftForest top f
  pair := fun ℓ => graftForestLeafEquiv top f (pair ((graftForestLeafEquiv top f).symm ℓ))
  mark := fun _ => none
  pair_pair ℓ := by
    simp only [Equiv.symm_apply_apply]
    rw [hinv _, Equiv.apply_symm_apply]
  pair_eq_iff ℓ := by
    simp only [ne_eq, not_true_eq_false, iff_false]
    intro h
    have he := congrArg (graftForestLeafEquiv top f).symm h
    simp only [Equiv.symm_apply_apply] at he
    exact hne _ he
  pair_sign ℓ _ := by
    calc
      _ = attachedSign sig (pair ((graftForestLeafEquiv top f).symm ℓ)) :=
        nodeSign_graftForestLeafEquiv top f sig _
      _ = -attachedSign sig ((graftForestLeafEquiv top f).symm ℓ) := hsign _
      _ = _ := by
        have he := nodeSign_graftForestLeafEquiv top f sig ((graftForestLeafEquiv top f).symm ℓ)
        rw [Equiv.apply_symm_apply] at he
        exact congrArg Neg.neg he.symm

theorem plainGraftedGarden_isPlain {w : ℕ} (sig : Fin w → ℤˣ) (top : Fin w → TTree)
    (f : Fin w → TTree.Path → TTree) (pair : AttachedLeaf top f → AttachedLeaf top f)
    (hinv : Function.Involutive pair) (hne : ∀ x, pair x ≠ x)
    (hsign : ∀ x, attachedSign sig (pair x) = -attachedSign sig x) :
    (plainGraftedGarden sig top f pair hinv hne hsign).IsPlain := fun _ => rfl

end WaveTurbulence.Induct
