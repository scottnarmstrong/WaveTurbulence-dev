/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Molecule.VineCoherenceExpansion
import Mathlib.Tactic

/-! # Coherence on actual vine atoms (TARGET cohmol)

The realization data are exactly the witnesses in the unchanged B2 IsVine
predicate. Pulling the groups back uses the finite atom set, so no labels
outside the vine are included.
-/

public section
namespace WaveTurbulence.Vine
open Finset
variable {V D : Type*} [DecidableEq V] [Fintype D]

/-- The explicit undirected realization witnesses of the pinned vine predicate. -/
structure VineRealization (M : Molecule V D) (X : VineType) (S : Finset V) (a b : V) where
  k : List ℕ
  length_eq : k.length=X.template.slots.length
  f : V → ℕ
  injOn : Set.InjOn f S
  image_eq : S.image f=range (X.expand k).n
  joints_eq : ({f a,f b} : Finset ℕ)={0,1}
  bonds_eq : (M.groupBonds S).map (Sym2.map f)=
    ((X.expand k).bonds.map (fun p => s(p.1,p.2)) : Multiset (Sym2 ℕ))

/-- Extracting realization data preserves the exact pinned vine predicate. -/
theorem isVine_iff_realization {M : Molecule V D} {X : VineType} {S : Finset V} {a b : V} :
    M.IsVine X S a b ↔ M.IsBlock S a b ∧ Nonempty (VineRealization M X S a b) := by
  constructor
  · rintro ⟨hB,k,hk,f,hf,hi,hj,he⟩
    exact ⟨hB,⟨⟨k,hk,f,hf,hi,hj,he⟩⟩⟩
  · rintro ⟨hB,⟨R⟩⟩
    exact ⟨hB,R.k,R.length_eq,R.f,R.injOn,R.image_eq,R.joints_eq,R.bonds_eq⟩

/-- The actual groups of atoms, pulled back from the template realization. -/
@[expose] noncomputable def realizedGroups {M : Molecule V D} {X : VineType} {S : Finset V} {a b : V}
    (R : VineRealization M X S a b) : List (List V) :=
  (X.expand R.k).groups.map fun g => S.toList.filter fun v => R.f v ∈ g

/-- Membership in the pulled-back groups is membership in the vine and in
the template's non-joint groups. -/
theorem mem_realizedGroups_iff {M : Molecule V D} {X : VineType} {S : Finset V} {a b : V}
    (R : VineRealization M X S a b) (v : V) :
    v ∈ (realizedGroups R).flatten ↔ v ∈ S ∧ 2 ≤ R.f v ∧ R.f v < (X.expand R.k).n := by
  simp only [realizedGroups,List.mem_flatten,List.mem_map]
  constructor
  · rintro ⟨l,⟨g,hg,rfl⟩,hv⟩
    have hv' : v ∈ S ∧ R.f v ∈ g := by
      simpa only [List.mem_filter,Finset.mem_toList,decide_eq_true_eq] using hv
    exact ⟨hv'.1,(mem_expand_groups_iff X R.k (R.f v)).mp
      (List.mem_flatten.mpr ⟨g,hg,hv'.2⟩)⟩
  · rintro ⟨hv,hi⟩
    obtain ⟨g,hg,hgv⟩ := List.mem_flatten.mp ((mem_expand_groups_iff X R.k (R.f v)).mpr hi)
    refine ⟨_,⟨g,hg,rfl⟩,?_⟩
    simpa only [List.mem_filter,Finset.mem_toList,decide_eq_true_eq] using And.intro hv hgv

/-- TARGET cohmol: count the non-monochromatic actual groups. -/
@[expose] noncomputable def realizedIncoherencyIndex {L : Type*} [DecidableEq L]
    {M : Molecule V D} {X : VineType} {S : Finset V} {a b : V}
    (R : VineRealization M X S a b) (layer : V → L) : ℕ :=
  incoherencyIndex layer (realizedGroups R)

/-- Coherence of actual vine atoms is precisely index zero. -/
theorem realizedIncoherencyIndex_eq_zero_iff {L : Type*} [DecidableEq L]
    {M : Molecule V D} {X : VineType} {S : Finset V} {a b : V}
    (R : VineRealization M X S a b) (layer : V → L) :
    realizedIncoherencyIndex R layer=0 ↔ Coherent layer (realizedGroups R) :=
  incoherencyIndex_eq_zero_iff layer _

end WaveTurbulence.Vine
