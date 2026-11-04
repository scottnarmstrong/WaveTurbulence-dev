/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.RegStruct.CombSnapshot.NodeCounts

/-! # The leaf sum of two ordered trees (TARGET L634–L635) -/

public section

namespace WaveTurbulence.Comb

/-- Place a leaf of either tree at its actual couple index. -/
@[expose] def twoTreeLeafMap (Q : Garden 2) :
    (GLeaf (fun _ : Fin 1 => Q.tree 0) ⊕ GLeaf (fun _ : Fin 1 => Q.tree 1)) → GLeaf Q.tree
  | .inl x => ⟨(0, x.1.2), x.2⟩
  | .inr x => ⟨(1, x.1.2), x.2⟩

theorem twoTreeLeafMap_injective (Q : Garden 2) : Function.Injective (twoTreeLeafMap Q) := by
  intro a b h
  cases a with
  | inl a =>
    cases b with
    | inl b =>
      apply congrArg Sum.inl
      apply Subtype.ext
      exact Prod.ext (Subsingleton.elim _ _) (congrArg (fun ℓ : GLeaf Q.tree => ℓ.1.2) h)
    | inr b =>
      have hi := congrArg (fun ℓ : GLeaf Q.tree => ℓ.1.1) h
      change (0 : Fin 2) = 1 at hi
      exact (by decide : (0 : Fin 2) ≠ 1) hi |>.elim
  | inr a =>
    cases b with
    | inl b =>
      have hi := congrArg (fun ℓ : GLeaf Q.tree => ℓ.1.1) h
      change (1 : Fin 2) = 0 at hi
      exact (by decide : (1 : Fin 2) ≠ 0) hi |>.elim
    | inr b =>
      apply congrArg Sum.inr
      apply Subtype.ext
      exact Prod.ext (Subsingleton.elim _ _) (congrArg (fun ℓ : GLeaf Q.tree => ℓ.1.2) h)

theorem twoTreeLeafMap_card (Q : Garden 2) :
    Fintype.card (GLeaf (fun _ : Fin 1 => Q.tree 0) ⊕ GLeaf (fun _ : Fin 1 => Q.tree 1)) =
      Fintype.card (GLeaf Q.tree) := by
  simp only [Fintype.card_sum, card_gleaf, Fin.sum_univ_one, Fin.sum_univ_two]
  omega

/-- The exact sum decomposition of the two leaf sets. -/
@[expose] noncomputable def twoTreeLeafEquiv (Q : Garden 2) :
    (GLeaf (fun _ : Fin 1 => Q.tree 0) ⊕ GLeaf (fun _ : Fin 1 => Q.tree 1)) ≃ GLeaf Q.tree :=
  Equiv.ofBijective (twoTreeLeafMap Q)
    ((Fintype.bijective_iff_injective_and_card _).mpr
      ⟨twoTreeLeafMap_injective Q, twoTreeLeafMap_card Q⟩)

end WaveTurbulence.Comb
