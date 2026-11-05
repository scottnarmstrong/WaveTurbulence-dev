/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Molecule.VineCapIndices
public import WaveTurbulence.Foundations.Molecule.VineSideLadderData
import Mathlib.Tactic

/-! # Primitive incidence data for a triangle cap and its selected rung prefix

These local data do not assume a cap graph or a vine recognition theorem.
They retain actual dart rows, distinct actual atoms, and the selected atom set.
Source containment results must construct all fields from their vine realization.
-/

public section
namespace WaveTurbulence.Vine
open Finset

/-- Include a shorter cap index family into a longer one. -/
@[expose] def capIndexInclusion (r s : ℕ) (h : r ≤ s) : CapIndex r → CapIndex s :=
  Sum.map id (Sum.map (Fin.castLE h) (Fin.castLE h))

/-- Index inclusion never identifies any of the triangle or rail atoms. -/
theorem capIndexInclusion_injective (r s : ℕ) (h : r ≤ s) :
    Function.Injective (capIndexInclusion r s h) :=
  Sum.map_injective.mpr ⟨Function.injective_id,
    Sum.map_injective.mpr ⟨Fin.castLE_injective h,Fin.castLE_injective h⟩⟩

/-- The actual triangle and the first r atoms of each actual rail. -/
@[expose] def capAtomFamily {V : Type*} (center upper lower : V)
    (u v : ℕ → V) (r : ℕ) : CapIndex r → V
  | .inl i => ![center,upper,lower] i
  | .inr (.inl i) => u (i.1+1)
  | .inr (.inr i) => v (i.1+1)

/-- Enlarging the index type preserves all previously indexed actual atoms. -/
theorem capAtomFamily_inclusion {V : Type*} (center upper lower : V)
    (u v : ℕ → V) (r s : ℕ) (h : r ≤ s) (i : CapIndex r) :
    capAtomFamily center upper lower u v s (capIndexInclusion r s h i)=
      capAtomFamily center upper lower u v r i := by
  cases i with
  | inl i => rfl
  | inr i => cases i <;> rfl

variable {V D : Type*} [DecidableEq V]

/-- Primitive source cap data: a triangle with complete incidence rows,
a full ladder, its selected prefix, and distinctness including both far ports. -/
structure CapPrefixData (M : Molecule V D) (A : Finset V) (n r : ℕ) where
  center : V
  upper : V
  lower : V
  farUpper : V
  farLower : V
  side : SideLadderData M center upper lower farUpper farLower n
  r_le : r ≤ n
  distinct : Function.Injective
    (capAtomFamily center upper lower side.ladder.u side.ladder.v (n+1))
  atoms_eq : (univ : Finset (CapIndex r)).image
    (capAtomFamily center upper lower side.ladder.u side.ladder.v r)=A

namespace CapPrefixData
variable {M : Molecule V D} {A : Finset V} {n r : ℕ} (C : CapPrefixData M A n r)

/-- The selected actual atom family. -/
@[expose] def family : CapIndex r → V :=
  capAtomFamily C.center C.upper C.lower C.side.ladder.u C.side.ladder.v r

/-- The selected family enumerates exactly the actual cap atoms. -/
theorem family_image : (univ : Finset (CapIndex r)).image C.family=A := C.atoms_eq

/-- Distinctness of the complete source family gives distinct selected atoms. -/
theorem family_injective : Function.Injective C.family := by
  intro i j he
  apply capIndexInclusion_injective r (n+1) (by have := C.r_le; omega)
  apply C.distinct
  rw [capAtomFamily_inclusion,capAtomFamily_inclusion]
  exact he

/-- The genuine inverse family label map used in the cap graph realization. -/
@[expose] noncomputable def label : V → ℕ := familyAtomLabel C.family (capIndexLabel 9 r)

/-- Every selected family atom has its prescribed literal cap label. -/
theorem label_family (i : CapIndex r) : C.label (C.family i)=capIndexLabel 9 r i :=
  familyAtomLabel_apply _ _ C.family_injective i

/-- The actual cap labels are injective on the selected atom group. -/
theorem label_injOn : Set.InjOn C.label A := by
  have hh := familyAtomLabel_injOn C.family (capIndexLabel 9 r) C.family_injective
    (capIndexLabel_injective 9 r (by decide))
  simpa only [label,C.family_image] using hh

/-- The inverse family map has exactly the literal cap label set. -/
theorem label_image : A.image C.label=capLabels 9 r := by
  have hh := (familyAtomLabel_image C.family (capIndexLabel 9 r) C.family_injective).trans
    (capIndexLabel_image 9 r)
  simpa only [label,C.family_image] using hh

include C in
/-- The selected cap has three triangle atoms and two atoms per full rung. -/
theorem card_atoms : A.card=3+2*r := by
  have hh := congrArg Finset.card C.family_image
  rw [card_image_of_injective _ C.family_injective,card_univ] at hh
  simp only [CapIndex,Fintype.card_sum,Fintype.card_fin] at hh
  omega

/-- The three triangle atoms are selected. -/
theorem triangle_mem : C.center ∈ A ∧ C.upper ∈ A ∧ C.lower ∈ A := by
  have hmem (i : CapIndex r) : C.family i ∈ A :=
    (Finset.ext_iff.mp C.family_image (C.family i)).mp (mem_image_of_mem C.family (mem_univ i))
  exact ⟨hmem (.inl 0),hmem (.inl 1),hmem (.inl 2)⟩

/-- The triangle receives labels4,5,6 in its incidence order. -/
theorem label_triangle : C.label C.center=4 ∧ C.label C.upper=5 ∧ C.label C.lower=6 :=
  ⟨C.label_family (.inl 0),C.label_family (.inl 1),C.label_family (.inl 2)⟩

/-- Every selected upper rung receives its literal allocated label. -/
theorem label_upper (i : ℕ) (hi : 1 ≤ i) (hir : i ≤ r) :
    C.label (C.side.ladder.u i)=9+(i-1) := by
  have hh := C.label_family (.inr (.inl ⟨i-1,by omega⟩))
  simpa only [family,capAtomFamily,capIndexLabel,show i-1+1=i by omega] using hh

/-- Every selected lower rung receives its literal allocated label. -/
theorem label_lower (i : ℕ) (hi : 1 ≤ i) (hir : i ≤ r) :
    C.label (C.side.ladder.v i)=9+r+(i-1) := by
  have hh := C.label_family (.inr (.inr ⟨i-1,by omega⟩))
  simpa only [family,capAtomFamily,capIndexLabel,show i-1+1=i by omega] using hh

end CapPrefixData
end WaveTurbulence.Vine
