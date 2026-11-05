/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Molecule.VineIntrinsicPartition
public import WaveTurbulence.Foundations.Molecule.VineCoherencePermutation
import Mathlib.Tactic

/-! # TARGET cohmol: coherence and its index are realization independent -/

public section
namespace WaveTurbulence.Vine
open Finset
variable {V D L : Type*} [DecidableEq V] [Fintype D] [DecidableEq D] [DecidableEq L]

/-- Disjoint nonempty groups have no repetitions after passing to atom sets. -/
theorem groupSets_nodup {gs : List (List V)} (hn : gs.flatten.Nodup)
    (hne : ∀ g ∈ gs,g ≠ []) : (gs.map List.toFinset).Nodup := by
  apply List.pairwise_map.mpr
  apply (List.nodup_flatten.mp hn).2.imp_of_mem
  intro g h hg hh hd he
  obtain ⟨v,hv⟩ := List.exists_mem_of_ne_nil g (hne g hg)
  have hv' : v ∈ h := List.mem_toFinset.mp (he ▸ List.mem_toFinset.mpr hv)
  exact List.disjoint_left.mp hd hv hv'

/-- Group-set lists of two realizations differ only by a permutation. -/
theorem realized_groupSets_perm (M : Molecule V D) (hM : M.IsMolecule)
    {X Y : VineType} {S : Finset V} {a b : V}
    (R : VineRealization M X S a b) (T : VineRealization M Y S a b)
    (hB : M.IsBlock S a b) :
    ((realizedGroups R).map List.toFinset).Perm ((realizedGroups T).map List.toFinset) := by
  have hn {X : VineType} (R : VineRealization M X S a b) :
      ((realizedGroups R).map List.toFinset).Nodup := by
    apply groupSets_nodup (actual_groups_nodup R)
    intro g hg he
    have hh := realized_group_sizes R g hg
    rw [he] at hh
    simp only [List.length_nil] at hh
    omega
  exact List.perm_of_nodup_nodup_toFinset_eq (hn R) (hn T) (realizedGroupSets_eq M hM R T hB)

omit [Fintype D] [DecidableEq D] in
/-- Counting nonmonochromatic groups depends only on their atom sets. -/
theorem incoherencyIndex_as_groupSets (layer : V → L) (gs : List (List V)) :
    incoherencyIndex layer gs=
      ((gs.map List.toFinset).filter (fun G => ¬∀ u ∈ G,∀ v ∈ G,layer u=layer v)).length := by
  rw [List.filter_map,List.length_map]
  unfold incoherencyIndex
  congr 1
  apply List.filter_congr
  intro g _hg
  apply Bool.eq_iff_iff.mpr
  simp only [Function.comp_apply,GroupCoherent,List.mem_toFinset]
  rfl

/-- TARGET cohmol: the incoherency index is independent of the template
realization, including all type-II rung counts m≥1 (F72). -/
theorem realizedIncoherencyIndex_eq (M : Molecule V D) (hM : M.IsMolecule)
    {X Y : VineType} {S : Finset V} {a b : V}
    (R : VineRealization M X S a b) (T : VineRealization M Y S a b)
    (hB : M.IsBlock S a b) (layer : V → L) :
    realizedIncoherencyIndex R layer=realizedIncoherencyIndex T layer := by
  change incoherencyIndex layer (realizedGroups R)=incoherencyIndex layer (realizedGroups T)
  rw [incoherencyIndex_as_groupSets,incoherencyIndex_as_groupSets]
  exact ((realized_groupSets_perm M hM R T hB).filter _).length_eq

/-- TARGET cohmol: coherence itself is independent of the realization. -/
theorem realized_coherent_iff (M : Molecule V D) (hM : M.IsMolecule)
    {X Y : VineType} {S : Finset V} {a b : V}
    (R : VineRealization M X S a b) (T : VineRealization M Y S a b)
    (hB : M.IsBlock S a b) (layer : V → L) :
    Coherent layer (realizedGroups R) ↔ Coherent layer (realizedGroups T) := by
  rw [← realizedIncoherencyIndex_eq_zero_iff,← realizedIncoherencyIndex_eq_zero_iff,
    realizedIncoherencyIndex_eq M hM R T hB layer]

end WaveTurbulence.Vine
