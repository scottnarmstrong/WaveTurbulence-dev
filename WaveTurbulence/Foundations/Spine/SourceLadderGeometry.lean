/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.Spine.SourceLocalLadder
/-! Actual cardinality and coupling exponent of a source ladder, reusing the DEGEN proof. -/
public section
set_option autoImplicit false
namespace WaveTurbulence.LGSpine
open Finset
variable {V : Type*} [DecidableEq V]

theorem ladderAtoms_card_of_injective {m : ℕ} {u v : Fin (m + 1) → V}
    (hinj : Function.Injective (Sum.elim u v)) :
    (Molecule.ladderAtoms u v).card = 2 * (m + 1) := by
  obtain ⟨hu,hv,hcross⟩ := Sum.elim_injective.mp hinj
  have hdis : Disjoint (univ.image u) (univ.image v) := by
    apply disjoint_left.mpr
    intro x hx hy
    obtain ⟨i,_,rfl⟩ := mem_image.mp hx
    obtain ⟨j,_,he⟩ := mem_image.mp hy
    exact hcross i j he.symm
  unfold Molecule.ladderAtoms
  rw [card_union_of_disjoint hdis, card_image_of_injective _ hu, card_image_of_injective _ hv]
  simp only [card_univ, Fintype.card_fin]
  omega

theorem ladder_coupling_order {m : ℕ} {u v : Fin (m + 1) → V}
    (hinj : Function.Injective (Sum.elim u v)) :
    (Molecule.ladderAtoms u v).card - 1 = 2 * m + 1 := by
  rw [ladderAtoms_card_of_injective hinj]
  omega

end WaveTurbulence.LGSpine
