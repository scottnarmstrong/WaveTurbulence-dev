/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Molecule.VineNeighborMultiset
import Mathlib.Tactic

/-! # The exact inverse of a pinned vine realization on its finite atom set -/

public section
namespace WaveTurbulence.Vine
open Finset
variable {V D : Type*} [DecidableEq V] [Fintype D]

/-- Every template atom has an actual preimage in the realized vine. -/
theorem VineRealization.exists_atomAt {M : Molecule V D} {X : VineType}
    {S : Finset V} {a b : V} (R : VineRealization M X S a b)
    (i : Fin (X.expand R.k).n) : ∃ v : S,R.f v=i.1 := by
  have hi : i.1 ∈ S.image R.f := R.image_eq.symm ▸ mem_range.mpr i.2
  obtain ⟨v,hv,he⟩ := mem_image.mp hi
  exact ⟨⟨v,hv⟩,he⟩

/-- Inverse atom map on the finite template range; no ambient choice of
vertices outside the vine enters the construction. -/
@[expose] noncomputable def VineRealization.atomAt {M : Molecule V D} {X : VineType}
    {S : Finset V} {a b : V} (R : VineRealization M X S a b)
    (i : Fin (X.expand R.k).n) : S := Classical.choose (R.exists_atomAt i)

/-- The inverse map has exactly the requested template label. -/
theorem VineRealization.label_atomAt {M : Molecule V D} {X : VineType}
    {S : Finset V} {a b : V} (R : VineRealization M X S a b)
    (i : Fin (X.expand R.k).n) : R.f (R.atomAt i)=i.1 :=
  Classical.choose_spec (R.exists_atomAt i)

/-- The inverse atom map is injective, including as an ambient vertex map. -/
theorem VineRealization.atomAt_injective {M : Molecule V D} {X : VineType}
    {S : Finset V} {a b : V} (R : VineRealization M X S a b) :
    Function.Injective (fun i => (R.atomAt i).1) := by
  intro i j hij
  apply Fin.ext
  have he := congrArg R.f hij
  simpa only [R.label_atomAt] using he

end WaveTurbulence.Vine
