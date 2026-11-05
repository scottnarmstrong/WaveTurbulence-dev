/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Molecule.VineIntrinsicGroups
public import WaveTurbulence.Foundations.Molecule.VineCoreAtoms
import Mathlib.Tactic

/-! # Intrinsically undoubled atoms are exactly the exceptional old core atoms -/

public section
namespace WaveTurbulence.Vine
open Finset
variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]

omit [DecidableEq D] in
/-- An old label identifies its actual core atom. -/
theorem VineRealization.eq_coreAtom_of_label {M : Molecule V D} {X : VineType}
    {S : Finset V} {a b u : V} (R : VineRealization M X S a b)
    (hu : u ∈ S) (i : Fin X.template.n) (hi : R.f u=i.1) :
    u=(R.coreAtom i).1 := R.injOn hu (R.coreAtom i).2 (hi.trans (R.label_coreAtom i).symm)

omit [DecidableEq D] in
/-- A core nonjoint label is an actual nonjoint atom. -/
theorem VineRealization.core_interior {M : Molecule V D} {X : VineType}
    {S : Finset V} {a b : V} (R : VineRealization M X S a b)
    (hB : M.IsBlock S a b) (i : Fin X.template.n) (hi : 2 ≤ i.1) :
    VineInterior S a b (R.coreAtom i).1 := by
  have hh := realization_index_lt_two_iff R hB (R.coreAtom i).2
  have hn : ¬((R.coreAtom i).1=a ∨ (R.coreAtom i).1=b) := by
    intro he
    have ht := hh.mpr he
    rw [R.label_coreAtom] at ht
    omega
  exact ⟨(R.coreAtom i).2,not_or.mp hn⟩

omit [DecidableEq D] in
/-- Undirected doubled core counts provide actual parallel incidences. -/
theorem VineRealization.core_double {M : Molecule V D} {X : VineType}
    {S : Finset V} {a b : V} (R : VineRealization M X S a b)
    (hB : M.IsBlock S a b) (i j : Fin X.template.n)
    (hi : 2 ≤ i.1) (hj : 2 ≤ j.1) (hne : i ≠ j)
    (hc : 2 ≤ X.template.bonds.count (i.1,j.1)+X.template.bonds.count (j.1,i.1)) :
    CoherenceDouble M S a b (R.coreAtom i).1 (R.coreAtom j).1 := by
  refine ⟨R.core_interior hB i hi,R.core_interior hB j hj,?_,?_⟩
  · exact fun he => hne (R.coreAtom_injective he)
  · rcases template_double_oriented X i j hi hj hne hc with hh | hh
    · exact R.core_twoIncidences i j hh
    · obtain ⟨T⟩ := R.core_twoIncidences j i hh
      exact ⟨T.mates⟩

/-- An intrinsically undoubled actual atom has an undoubled old core label. -/
theorem VineRealization.undoubled_core (M : Molecule V D)
    {X : VineType} {S : Finset V} {a b u : V} (R : VineRealization M X S a b)
    (hB : M.IsBlock S a b) (hu : CoherenceUndoubled M S a b u) :
    CoreUndoubled X ⟨R.f u,R.undoubled_old M hB hu⟩ := by
  let i : Fin X.template.n := ⟨R.f u,R.undoubled_old M hB hu⟩
  have he : u=(R.coreAtom i).1 := R.eq_coreAtom_of_label hu.1.1 i rfl
  have hi : 2 ≤ i.1 := by
    have hh := realization_index_lt_two_iff R hB hu.1.1
    have hn : ¬R.f u<2 := fun h => (hh.mp h).elim hu.1.2.1 hu.1.2.2
    exact Nat.le_of_not_gt hn
  change CoreUndoubled X i
  intro j hj hne
  by_contra hc
  have hd := R.core_double hB i j hi hj hne (by omega)
  rw [← he] at hd
  exact hu.2 _ hd

/-- All actual undoubled atoms lie in the same source group. -/
theorem VineRealization.undoubled_same_group (M : Molecule V D)
    {X : VineType} {S : Finset V} {a b u v : V} (R : VineRealization M X S a b)
    (hB : M.IsBlock S a b) (hu : CoherenceUndoubled M S a b u)
    (hv : CoherenceUndoubled M S a b v) : SameRealizedGroup R u v := by
  have hu2 : 2 ≤ R.f u := by
    have hh := realization_index_lt_two_iff R hB hu.1.1
    exact Nat.le_of_not_gt (fun h => (hh.mp h).elim hu.1.2.1 hu.1.2.2)
  have hv2 : 2 ≤ R.f v := by
    have hh := realization_index_lt_two_iff R hB hv.1.1
    exact Nat.le_of_not_gt (fun h => (hh.mp h).elim hv.1.2.1 hv.1.2.2)
  obtain ⟨g,hg,hug,hvg⟩ := template_undoubled_same_group X
    ⟨R.f u,R.undoubled_old M hB hu⟩ ⟨R.f v,R.undoubled_old M hB hv⟩ hu2 hv2
    (R.undoubled_core M hB hu) (R.undoubled_core M hB hv)
  exact ⟨g,template_group_mem_expand X R.k hg,hug,hvg⟩

end WaveTurbulence.Vine
