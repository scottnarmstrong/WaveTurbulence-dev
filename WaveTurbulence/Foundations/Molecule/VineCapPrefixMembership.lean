/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Molecule.VineCapPrefixData
import Mathlib.Tactic

/-! # Exact actual rung membership and absent front neighbors in primitive cap data -/

public section
namespace WaveTurbulence.Vine
open Finset
variable {V D : Type*} [DecidableEq V] {M : Molecule V D} {A : Finset V} {n r : ℕ}
namespace CapPrefixData
variable (C : CapPrefixData M A n r)

/-- Upper membership is exactly the selected initial rung interval, even
at the far external port n+1. -/
theorem upper_mem_iff (i : ℕ) (hi : 1 ≤ i) (hin : i ≤ n+1) :
    C.side.ladder.u i ∈ A ↔ i ≤ r := by
  constructor
  · intro hx
    have hx' := (Finset.ext_iff.mp C.family_image _).mpr hx
    obtain ⟨j,_hj,he⟩ := mem_image.mp hx'
    have heindex : capIndexInclusion r (n+1) (by have := C.r_le; omega) j=
        .inr (.inl ⟨i-1,by omega⟩) := by
      apply C.distinct
      rw [capAtomFamily_inclusion]
      change C.family j=C.side.ladder.u (i-1+1)
      simpa only [show i-1+1=i by omega] using he
    cases j with
    | inl j => cases heindex
    | inr j =>
      cases j with
      | inl j =>
        simp only [capIndexInclusion,Sum.map_inr,Sum.map_inl,Sum.inr.injEq,Sum.inl.injEq] at heindex
        have hh := congrArg Fin.val heindex
        change j.1=i-1 at hh
        omega
      | inr j => cases heindex
  · intro hir
    apply (Finset.ext_iff.mp C.family_image _).mp
    refine mem_image.mpr ⟨.inr (.inl ⟨i-1,by omega⟩),mem_univ _,?_⟩
    change C.side.ladder.u (i-1+1)=C.side.ladder.u i
    rw [show i-1+1=i by omega]

/-- Lower membership is exactly the same selected initial rung interval. -/
theorem lower_mem_iff (i : ℕ) (hi : 1 ≤ i) (hin : i ≤ n+1) :
    C.side.ladder.v i ∈ A ↔ i ≤ r := by
  constructor
  · intro hx
    have hx' := (Finset.ext_iff.mp C.family_image _).mpr hx
    obtain ⟨j,_hj,he⟩ := mem_image.mp hx'
    have heindex : capIndexInclusion r (n+1) (by have := C.r_le; omega) j=
        .inr (.inr ⟨i-1,by omega⟩) := by
      apply C.distinct
      rw [capAtomFamily_inclusion]
      change C.family j=C.side.ladder.v (i-1+1)
      simpa only [show i-1+1=i by omega] using he
    cases j with
    | inl j => cases heindex
    | inr j =>
      cases j with
      | inl j => cases heindex
      | inr j =>
        simp only [capIndexInclusion,Sum.map_inr,Sum.inr.injEq] at heindex
        have hh := congrArg Fin.val heindex
        change j.1=i-1 at hh
        omega
  · intro hir
    apply (Finset.ext_iff.mp C.family_image _).mp
    refine mem_image.mpr ⟨.inr (.inr ⟨i-1,by omega⟩),mem_univ _,?_⟩
    change C.side.ladder.v (i-1+1)=C.side.ladder.v i
    rw [show i-1+1=i by omega]

/-- The two source rail atoms immediately after the selected prefix are absent. -/
theorem front_neighbors_absent : C.side.ladder.u (r+1) ∉ A ∧ C.side.ladder.v (r+1) ∉ A := by
  have hr : r+1 ≤ n+1 := by have := C.r_le; omega
  constructor
  · intro h
    have hh := (C.upper_mem_iff (r+1) (by omega) hr).mp h
    omega
  · intro h
    have hh := (C.lower_mem_iff (r+1) (by omega) hr).mp h
    omega

end CapPrefixData
end WaveTurbulence.Vine
