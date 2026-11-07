/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.OpDW2
public import WaveTurbulence.Foundations.FinalCount.OpCFree
import Mathlib.Tactic

/-! # Dart isomorphisms for the two-chain closure (finalcount-g8, F6-1)

The two chains of a case-(4) component are contracted one after the other (`closureTwo` contracts the first chain
in `eraseAtoms M₀ {b}`, then the second one, and adds the first bond last).  The decoration-level counts follow the
other order (first chain, then the second chain in the post of the first).  This module contains the dart isomorphism
between the two orders (`bondPostEquiv`), the cross darts of an `addBond`, and the equivalence between the darts of a
molecule and the darts of the molecule with one bond erased.
-/

@[expose] public section
set_option autoImplicit false
open Finset
namespace WaveTurbulence.FinalCountG8
open WaveTurbulence.MoleProp4

section
variable {V E : Type*} [DecidableEq V] [Fintype E] [DecidableEq E]

theorem mem_crossDarts_addBond (X : Molecule V E) {a c : V} {Y : Finset V} (ha : a ∉ Y) (hc : c ∉ Y)
    (z : E ⊕ Bool) :
    z ∈ crossDarts (Mole.addBond X a c) Y ↔ ∃ w, z = Sum.inl w ∧ w ∈ crossDarts X Y := by
  rw [mem_crossDarts]
  rcases z with w | t
  · simp only [Sum.inl.injEq, exists_eq_left', mem_crossDarts]; rfl
  · constructor
    · rintro ⟨h1, h2⟩
      exfalso
      cases t
      · exact hc h1
      · exact ha h1
    · rintro ⟨w, h, _⟩; exact absurd h (by simp)

theorem crossDarts_addBond_inl (X : Molecule V E) {a c : V} {Y : Finset V} (ha : a ∉ Y) (hc : c ∉ Y)
    {p q : E} (h : crossDarts X Y = {p, q}) :
    crossDarts (Mole.addBond X a c) Y = {Sum.inl p, Sum.inl q} := by
  ext z
  rw [mem_crossDarts_addBond X ha hc, h]
  simp only [mem_insert, mem_singleton]
  constructor
  · rintro ⟨w, rfl, hw⟩; rcases hw with rfl | rfl <;> simp
  · rintro (rfl | rfl) <;> exact ⟨_, rfl, by simp⟩

end

section Iso
variable {V E : Type*} [DecidableEq V] [Fintype E] [DecidableEq E]
variable (K : Molecule V E) (a₁ c₁ a₂ c₂ : V) (Y : Finset V) (ha₁ : a₁ ∉ Y) (hc₁ : c₁ ∉ Y)

/-- **The two orders of contraction**: erase `Y` from `K + (a₁ → c₁)` and then add `a₂ → c₂`, versus erase `Y` from `K`,
add `a₂ → c₂`, and finally `a₁ → c₁`. -/
def bondPostEquiv : Degen.RetainedDart (Mole.addBond K a₁ c₁) Y ⊕ Bool ≃
    (Degen.RetainedDart K Y ⊕ Bool) ⊕ Bool where
  toFun z := match z with
    | Sum.inl ⟨Sum.inl w, h⟩ => Sum.inl (Sum.inl ⟨w, h⟩)
    | Sum.inl ⟨Sum.inr t, _⟩ => Sum.inr t
    | Sum.inr t => Sum.inl (Sum.inr t)
  invFun z := match z with
    | Sum.inl (Sum.inl ⟨w, h⟩) => Sum.inl ⟨Sum.inl w, h⟩
    | Sum.inl (Sum.inr t) => Sum.inr t
    | Sum.inr t => Sum.inl ⟨Sum.inr t, by cases t <;> simp [Mole.addBond, ha₁, hc₁]⟩
  left_inv z := by
    rcases z with ⟨w | t, h⟩ | t
    · rfl
    · rfl
    · rfl
  right_inv z := by
    rcases z with (w | t) | t
    · rfl
    · rfl
    · rfl

theorem bondPostEquiv_atom (z) : (Mole.addBond (Mole.addBond (Degen.eraseAtoms K Y) a₂ c₂) a₁ c₁).atom
    (bondPostEquiv K a₁ c₁ Y ha₁ hc₁ z) = (Mole.addBond (Degen.eraseAtoms (Mole.addBond K a₁ c₁) Y) a₂ c₂).atom z := by
  rcases z with ⟨w | t, h⟩ | t
  · rfl
  · cases t <;> rfl
  · cases t <;> rfl

theorem bondPostEquiv_out (z) : (Mole.addBond (Mole.addBond (Degen.eraseAtoms K Y) a₂ c₂) a₁ c₁).out
    (bondPostEquiv K a₁ c₁ Y ha₁ hc₁ z) = (Mole.addBond (Degen.eraseAtoms (Mole.addBond K a₁ c₁) Y) a₂ c₂).out z := by
  rcases z with ⟨w | t, h⟩ | t
  · rfl
  · cases t <;> rfl
  · cases t <;> rfl

theorem bondPostEquiv_mate (z) : (Mole.addBond (Mole.addBond (Degen.eraseAtoms K Y) a₂ c₂) a₁ c₁).mate
    (bondPostEquiv K a₁ c₁ Y ha₁ hc₁ z) =
    bondPostEquiv K a₁ c₁ Y ha₁ hc₁ ((Mole.addBond (Degen.eraseAtoms (Mole.addBond K a₁ c₁) Y) a₂ c₂).mate z) := by
  rcases z with ⟨w | t, h⟩ | t
  · rfl
  · cases t <;> rfl
  · cases t <;> rfl

include ha₁ hc₁ in
theorem bondPostEquiv_atoms :
    (Mole.addBond (Degen.eraseAtoms (Mole.addBond K a₁ c₁) Y) a₂ c₂).atoms =
      (Mole.addBond (Mole.addBond (Degen.eraseAtoms K Y) a₂ c₂) a₁ c₁).atoms := by
  change insert a₂ (insert c₂ ((insert a₁ (insert c₁ K.atoms)) \ Y)) =
    insert a₁ (insert c₁ (insert a₂ (insert c₂ (K.atoms \ Y))))
  ext x
  simp only [mem_insert, mem_sdiff]
  have h1 : x = a₁ → x ∉ Y := fun h => h ▸ ha₁
  have h2 : x = c₁ → x ∉ Y := fun h => h ▸ hc₁
  tauto

end Iso

section Without
variable {V D₀ D₂ : Type*} [DecidableEq V]

/-- The darts of `N₂` other than the bond `Φ (inr true)` are the darts `Φ (inl _)`. -/
def withoutEquiv (N₂ : Molecule V D₂) (Φ : D₀ ⊕ Bool ≃ D₂)
    (hmt : N₂.mate (Φ (Sum.inr true)) = Φ (Sum.inr false)) :
    D₀ ≃ MoleProp.WithoutBondDart N₂ (Φ (Sum.inr true)) where
  toFun z := ⟨Φ (Sum.inl z), fun h => by simpa using Φ.injective h,
    fun h => by rw [hmt] at h; simpa using Φ.injective h⟩
  invFun x := match h : Φ.symm x.1 with
    | Sum.inl z => z
    | Sum.inr t => False.elim (by
        have hx : x.1 = Φ (Sum.inr t) := by rw [← h]; simp
        cases t
        · exact x.2.2 (hx.trans hmt.symm)
        · exact x.2.1 hx)
  left_inv z := by
    simp only
    split
    · rename_i z' h
      have := congrArg Φ h
      simp at this
      exact (Sum.inl.inj (Φ.injective (by simpa using this))).symm
    · rename_i t h
      have := congrArg Φ h
      simp at this
  right_inv x := by
    apply Subtype.ext
    simp only
    split
    · rename_i z h
      rw [← h]; simp
    · rename_i t h
      exfalso
      have hx : x.1 = Φ (Sum.inr t) := by rw [← h]; simp
      cases t
      · exact x.2.2 (hx.trans hmt.symm)
      · exact x.2.1 hx

end Without

end WaveTurbulence.FinalCountG8
