/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Molecule.VinePairDegreeCounts
public import WaveTurbulence.Foundations.Molecule.VineCoreDoubleGroups
public import WaveTurbulence.Foundations.Molecule.VineRealizationDegrees
public import WaveTurbulence.Foundations.Molecule.VineDoublePairClosure
import Mathlib.Tactic

/-! # Actual old-core pair degrees cannot exceed the pinned finite-core counts -/

public section
namespace WaveTurbulence.Vine
open Finset
variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]

/-- Two actual parallel incidences give induced degree at least two in
their two-atom group, independently of all other graph incidences. -/
theorem twoIncidences_pair_degree_ge_two (M : Molecule V D) {u v : V}
    (T : TwoIncidences M u v) : 2 ≤ M.degIn {u,v} u := by
  have hsub : univ.image T.dart ⊆ (M.dartsAt u).filter (M.InGroup {u,v}) := by
    intro d hd
    obtain ⟨i,_hi,rfl⟩ := mem_image.mp hd
    exact mem_filter.mpr ⟨(Mole.mem_dartsAt M u _).mpr (T.atom_eq i),
      (T.atom_eq i).symm ▸ mem_insert_self _ _,
      (T.neighbor_eq i).symm ▸ mem_insert_of_mem (mem_singleton_self _)⟩
  have hh := card_le_card hsub
  rw [card_image_of_injective _ T.injective,card_univ,Fintype.card_fin] at hh
  exact hh

omit [DecidableEq D] in
/-- The actual induced degree in a pair of old distinct atom labels is
bounded by the original undirected encoded pair count. Insertion cannot add
old loops or old pair occurrences. -/
theorem VineRealization.old_pair_degree_le {M : Molecule V D} {X : VineType}
    {S : Finset V} {a b : V} (R : VineRealization M X S a b)
    {u v : V} (hu : u ∈ S) (hv : v ∈ S) (huv : u ≠ v)
    (huold : R.f u<X.template.n) (hvold : R.f v<X.template.n) :
    M.degIn {u,v} u ≤ X.template.bonds.count (R.f u,R.f v)+X.template.bonds.count (R.f v,R.f u) := by
  have hsub : ({u,v} : Finset V) ⊆ S := by
    intro w hw
    rcases mem_insert.mp hw with hwu | hwv
    · exact hwu.symm ▸ hu
    · exact (mem_singleton.mp hwv).symm ▸ hv
  have hlabels : R.f u ≠ R.f v := fun he => huv (R.injOn hu hv he)
  have hd := R.subgroup_degree hsub hu
  simp only [image_insert,image_singleton] at hd
  change M.degIn {u,v} u=edgeDegree (restrictBonds {R.f u,R.f v} (X.expand R.k).bonds) (R.f u) at hd
  rw [edgeDegree_restrict_pair _ _ _ hlabels] at hd
  have hloop : (X.expand R.k).bonds.count (R.f u,R.f u)=0 := by
    have hle := expand_old_count_le X R.k (R.f u) (R.f u) huold huold
    have hz := template_no_loop_counts X ⟨R.f u,huold⟩
    change X.template.bonds.count (R.f u,R.f u)=0 at hz
    omega
  have hle1 := expand_old_count_le X R.k (R.f u) (R.f v) huold hvold
  have hle2 := expand_old_count_le X R.k (R.f v) (R.f u) hvold huold
  omega

/-- A doubled old nonjoint pair belongs to a single original coherence group. -/
theorem VineRealization.old_double_same_group (M : Molecule V D) {X : VineType}
    {S : Finset V} {a b : V} (R : VineRealization M X S a b)
    {u v : V} (hu : u ∈ S) (hv : v ∈ S) (huv : u ≠ v)
    (hu2 : 2 ≤ R.f u) (hv2 : 2 ≤ R.f v)
    (huold : R.f u<X.template.n) (hvold : R.f v<X.template.n) (T : TwoIncidences M u v) :
    ∃ q : Fin X.template.groups.length,
      R.f u ∈ X.template.groups[q.1] ∧ R.f v ∈ X.template.groups[q.1] := by
  have hlo := twoIncidences_pair_degree_ge_two M T
  have hhi := R.old_pair_degree_le hu hv huv huold hvold
  apply template_double_same_group X ⟨R.f u,huold⟩ ⟨R.f v,hvold⟩ hu2 hv2 _ (hlo.trans hhi)
  intro he
  exact huv (R.injOn hu hv (congrArg Fin.val he))

end WaveTurbulence.Vine
