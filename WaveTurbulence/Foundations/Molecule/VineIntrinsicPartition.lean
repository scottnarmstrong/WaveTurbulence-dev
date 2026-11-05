/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Molecule.VineIntrinsicGroupConnected
public import WaveTurbulence.Foundations.Molecule.VineActualGroupSizes
public import WaveTurbulence.Foundations.Molecule.VineIntrinsicEdgeRecognition
import Mathlib.Tactic

/-! # The actual group partition is independent of the vine realization -/

public section
namespace WaveTurbulence.Vine
open Finset
variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]

/-- Two groups in a repetition-free flattened list sharing an atom coincide. -/
theorem groups_eq_of_common {A : Type*} {gs : List (List A)} (hn : gs.flatten.Nodup)
    {g h : List A} (hg : g ∈ gs) (hh : h ∈ gs) {v : A} (hvg : v ∈ g) (hvh : v ∈ h) : g=h := by
  by_contra hne
  have hd := (List.nodup_flatten.mp hn).2.forall hg hh hne
  exact List.disjoint_left.mp hd hvg hvh

/-- Intrinsic paths preserve membership in every prescribed literal group. -/
theorem VineRealization.intrinsic_path_group_iff (M : Molecule V D) (hM : M.IsMolecule)
    {X : VineType} {S : Finset V} {a b u v : V} (R : VineRealization M X S a b)
    (hB : M.IsBlock S a b) (hp : Relation.EqvGen (CoherenceEdge M S a b) u v) :
    ∀ g ∈ (X.expand R.k).groups,R.f u ∈ g ↔ R.f v ∈ g := by
  induction hp with
  | rel u v he =>
    obtain ⟨h,hh,huh,hvh⟩ := R.intrinsic_edge_same_group M hM hB he
    intro g hg
    constructor
    · intro hug
      have he := groups_eq_of_common (expand_groups_nodup X R.k) hg hh hug huh
      exact he.symm ▸ hvh
    · intro hvg
      have he := groups_eq_of_common (expand_groups_nodup X R.k) hg hh hvg hvh
      exact he.symm ▸ huh
  | refl u => exact fun _ _ => Iff.rfl
  | symm u v _ ih => exact fun g hg => (ih g hg).symm
  | trans u v w _ _ ih ih' => exact fun g hg => (ih g hg).trans (ih' g hg)

/-- The unordered collection of actual group atom sets. -/
@[expose] noncomputable def realizedGroupSets {M : Molecule V D} {X : VineType}
    {S : Finset V} {a b : V} (R : VineRealization M X S a b) : Finset (Finset V) :=
  ((realizedGroups R).map List.toFinset).toFinset

/-- TARGET cohmol: every actual group atom set is intrinsic. The statement
allows different template types, rung counts, and atom labels. -/
theorem realizedGroupSets_eq (M : Molecule V D) (hM : M.IsMolecule)
    {X Y : VineType} {S : Finset V} {a b : V}
    (R : VineRealization M X S a b) (T : VineRealization M Y S a b)
    (hB : M.IsBlock S a b) : realizedGroupSets R=realizedGroupSets T := by
  have subset {X Y : VineType} (R : VineRealization M X S a b) (T : VineRealization M Y S a b) :
      realizedGroupSets R ⊆ realizedGroupSets T := by
    intro G hG
    obtain ⟨l,hl,rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp hG)
    obtain ⟨g,hg,rfl⟩ := List.mem_map.mp hl
    have hlen := realized_group_length R hg
    have hsize := expand_group_sizes X R.k g hg
    have hpos : 0<(S.toList.filter fun v => R.f v ∈ g).length := by omega
    obtain ⟨u,hu⟩ := List.exists_mem_of_length_pos hpos
    have hu' : u ∈ S ∧ R.f u ∈ g := by simpa using hu
    have hunon := (mem_actual_groups_iff R hB u).mp
      (List.mem_flatten.mpr ⟨_,List.mem_map.mpr ⟨g,hg,rfl⟩,hu⟩)
    have hTflat := (mem_actual_groups_iff T hB u).mpr hunon
    obtain ⟨l,hl,hul⟩ := List.mem_flatten.mp hTflat
    obtain ⟨h,hh,rfl⟩ := List.mem_map.mp hl
    have huT : T.f u ∈ h := of_decide_eq_true (List.mem_filter.mp hul).2
    have equal : (S.toList.filter fun v => R.f v ∈ g).toFinset=
        (S.toList.filter fun v => T.f v ∈ h).toFinset := by
      ext v
      simp only [List.mem_toFinset,List.mem_filter,Finset.mem_toList,decide_eq_true_eq]
      constructor
      · rintro ⟨hv,hvg⟩
        have hp := R.group_intrinsic_connected M hM hB hg hu'.1 hv hu'.2 hvg
        exact ⟨hv,(T.intrinsic_path_group_iff M hM hB hp h hh).mp huT⟩
      · rintro ⟨hv,hvh⟩
        have hp := T.group_intrinsic_connected M hM hB hh hu'.1 hv huT hvh
        exact ⟨hv,(R.intrinsic_path_group_iff M hM hB hp g hg).mp hu'.2⟩
    rw [equal]
    exact List.mem_toFinset.mpr (List.mem_map.mpr ⟨_,List.mem_map.mpr ⟨h,hh,rfl⟩,rfl⟩)
  exact subset_antisymm (subset R T) (subset T R)

end WaveTurbulence.Vine
