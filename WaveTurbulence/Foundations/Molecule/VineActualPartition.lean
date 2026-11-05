/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Molecule.VineRealizationGroups
import Mathlib.Tactic

/-! # Actual vine groups partition the non-joint atoms (TARGET cohmol) -/

public section
namespace WaveTurbulence.Vine
open Finset
variable {V D : Type*} [DecidableEq V] [Fintype D]

/-- A realization sends precisely its two joints to the indices below two. -/
theorem realization_index_lt_two_iff {M : Molecule V D} {X : VineType} {S : Finset V} {a b : V}
    (R : VineRealization M X S a b) (hB : M.IsBlock S a b) {v : V} (hv : v ∈ S) :
    R.f v<2 ↔ v=a ∨ v=b := by
  have ha : R.f a ∈ ({0,1} : Finset ℕ) := R.joints_eq ▸ mem_insert_self _ _
  have hb : R.f b ∈ ({0,1} : Finset ℕ) := R.joints_eq ▸ mem_insert_of_mem (mem_singleton_self _)
  constructor
  · intro hlt
    have hm : R.f v ∈ ({R.f a,R.f b} : Finset ℕ) := by
      rw [R.joints_eq]
      simp only [mem_insert,mem_singleton]
      omega
    rcases mem_insert.mp hm with h | h
    · exact Or.inl (R.injOn hv hB.2.1 h)
    · exact Or.inr (R.injOn hv hB.2.2.1 (mem_singleton.mp h))
  · rintro (rfl | rfl)
    · simp only [mem_insert,mem_singleton] at ha
      omega
    · simp only [mem_insert,mem_singleton] at hb
      omega

/-- The pulled-back groups contain exactly the actual non-joint atoms. -/
theorem mem_actual_groups_iff {M : Molecule V D} {X : VineType} {S : Finset V} {a b : V}
    (R : VineRealization M X S a b) (hB : M.IsBlock S a b) (v : V) :
    v ∈ (realizedGroups R).flatten ↔ v ∈ S ∧ v ≠ a ∧ v ≠ b := by
  rw [mem_realizedGroups_iff]
  constructor
  · rintro ⟨hv,hge,_hlt⟩
    have hh := (realization_index_lt_two_iff R hB hv).not
    have hnot : ¬(v=a ∨ v=b) := hh.mp (by omega)
    exact ⟨hv,not_or.mp hnot⟩
  · rintro ⟨hv,hva,hvb⟩
    have hlt : R.f v < (X.expand R.k).n := mem_range.mp (R.image_eq ▸ mem_image_of_mem R.f hv)
    have hh := realization_index_lt_two_iff R hB hv
    exact ⟨hv,by have : ¬R.f v<2 := fun h => (hh.mp h).elim hva hvb; omega,hlt⟩

/-- No actual atom occurs in two pulled-back groups. -/
theorem actual_groups_nodup {M : Molecule V D} {X : VineType} {S : Finset V} {a b : V}
    (R : VineRealization M X S a b) : (realizedGroups R).flatten.Nodup := by
  have hn := List.nodup_flatten.mp (expand_groups_nodup X R.k)
  apply List.nodup_flatten.mpr
  constructor
  · intro l hl
    obtain ⟨g,_hg,rfl⟩ := List.mem_map.mp hl
    exact S.nodup_toList.filter _
  · apply List.pairwise_map.mpr
    apply hn.2.imp
    intro g h hgh
    rw [List.disjoint_left] at hgh ⊢
    intro v hv hv'
    exact hgh (of_decide_eq_true (List.mem_filter.mp hv).2)
      (of_decide_eq_true (List.mem_filter.mp hv').2)

/-- TARGET cohmol: the actual groups give a disjoint partition of all
non-joint atoms, independently of the order of S.toList. -/
theorem actual_groups_partition {M : Molecule V D} {X : VineType} {S : Finset V} {a b : V}
    (R : VineRealization M X S a b) (hB : M.IsBlock S a b) :
    (realizedGroups R).flatten.Perm (S.toList.filter fun v => v ≠ a ∧ v ≠ b) := by
  apply List.perm_iff_count.mpr
  intro v
  rw [(actual_groups_nodup R).count,(S.nodup_toList.filter _).count]
  simp only [mem_actual_groups_iff R hB,List.mem_filter,Finset.mem_toList,decide_eq_true_eq]

end WaveTurbulence.Vine
