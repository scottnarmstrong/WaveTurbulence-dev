/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import Mathlib.Data.Finset.Image
import Mathlib.Tactic

/-! # Explicit finite atom families give genuine label maps -/

public section
namespace WaveTurbulence.Vine
open Finset
variable {V : Type*} [DecidableEq V]

/-- The unique available index of an atom in an injectively labeled finite
family. Values outside the family's image use the specified zero extension;
no theorem consumes that extension as an atom label. -/
@[expose] noncomputable def inverseAtomLabel (W : Finset ℕ) (F : ℕ → V) (v : V) : ℕ :=
  if h : ∃ i,i ∈ W ∧ F i=v then Classical.choose h else 0

/-- A finite injective atom family has its prescribed labels under the inverse. -/
theorem inverseAtomLabel_apply (W : Finset ℕ) (F : ℕ → V) (hF : Set.InjOn F W)
    (i : ℕ) (hi : i ∈ W) : inverseAtomLabel W F (F i)=i := by
  have he : ∃ j,j ∈ W ∧ F j=F i := ⟨i,hi,rfl⟩
  rw [inverseAtomLabel,dite_eq_left he]
  have hs := Classical.choose_spec he
  exact hF hs.1 hi hs.2

/-- On the image family, the inverse label is available and reconstructs
exactly the original actual atom. -/
theorem inverseAtomLabel_spec (W : Finset ℕ) (F : ℕ → V) {A : Finset V}
    (himage : W.image F=A) {v : V} (hv : v ∈ A) :
    inverseAtomLabel W F v ∈ W ∧ F (inverseAtomLabel W F v)=v := by
  have he : ∃ i,i ∈ W ∧ F i=v := by
    rw [← himage] at hv
    exact mem_image.mp hv
  rw [inverseAtomLabel,dite_eq_left he]
  exact Classical.choose_spec he

/-- The inverse is injective on the actual finite atomic group. -/
theorem inverseAtomLabel_injOn (W : Finset ℕ) (F : ℕ → V) {A : Finset V}
    (himage : W.image F=A) : Set.InjOn (inverseAtomLabel W F) A := by
  intro u hu v hv he
  have hh := congrArg F he
  rwa [(inverseAtomLabel_spec W F himage hu).2,
    (inverseAtomLabel_spec W F himage hv).2] at hh

/-- An injective finite atom family labels its actual image by exactly W. -/
theorem inverseAtomLabel_image (W : Finset ℕ) (F : ℕ → V) {A : Finset V}
    (hF : Set.InjOn F W) (himage : W.image F=A) :
    A.image (inverseAtomLabel W F)=W := by
  ext i
  constructor
  · intro hi
    obtain ⟨v,hv,rfl⟩ := mem_image.mp hi
    exact (inverseAtomLabel_spec W F himage hv).1
  · intro hi
    refine mem_image.mpr ⟨F i,?_,inverseAtomLabel_apply W F hF i hi⟩
    rw [← himage]
    exact mem_image_of_mem F hi

end WaveTurbulence.Vine
