/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import Mathlib.Data.Finset.Image
import Mathlib.Tactic

/-! # Labeling a finite indexed atom family with prescribed natural labels -/

public section
namespace WaveTurbulence.Vine
open Finset
variable {I V : Type*} [DecidableEq V]

/-- Assign the prescribed label of an atom's unique family index. The zero
extension outside the family's image is specified but never used as an
available label. -/
@[expose] noncomputable def familyAtomLabel (F : I → V) (label : I → ℕ) (v : V) : ℕ := by
  classical
  exact if h : ∃ i,F i=v then label (Classical.choose h) else 0

omit [DecidableEq V] in
/-- Injectivity of the actual family makes the recovered label exact. -/
theorem familyAtomLabel_apply (F : I → V) (label : I → ℕ) (hF : Function.Injective F)
    (i : I) : familyAtomLabel F label (F i)=label i := by
  have he : ∃ j,F j=F i := ⟨i,rfl⟩
  rw [familyAtomLabel,dite_eq_left he]
  exact congrArg label (hF (Classical.choose_spec he))

variable [Fintype I]

/-- A prescribed injective index labeling is injective on the actual image. -/
theorem familyAtomLabel_injOn (F : I → V) (label : I → ℕ)
    (hF : Function.Injective F) (hl : Function.Injective label) :
    Set.InjOn (familyAtomLabel F label) (univ.image F) := by
  intro u hu v hv he
  obtain ⟨i,_hi,rfl⟩ := mem_image.mp hu
  obtain ⟨j,_hj,rfl⟩ := mem_image.mp hv
  rw [familyAtomLabel_apply F label hF i,familyAtomLabel_apply F label hF j] at he
  exact congrArg F (hl he)

/-- The family label map has exactly the prescribed finite label image. -/
theorem familyAtomLabel_image (F : I → V) (label : I → ℕ) (hF : Function.Injective F) :
    (univ.image F).image (familyAtomLabel F label)=univ.image label := by
  rw [Finset.image_image]
  apply Finset.image_congr
  intro i _hi
  exact familyAtomLabel_apply F label hF i

end WaveTurbulence.Vine
