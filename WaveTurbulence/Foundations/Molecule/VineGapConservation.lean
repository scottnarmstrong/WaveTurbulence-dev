/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Molecule.VineGroupGaps
public import WaveTurbulence.Foundations.Molecule.MoleculeBlockBarriers
import Mathlib.Tactic

/-! # The gaps at the two joints of a block agree up to sign (TARGET defdiff) -/

public section
namespace WaveTurbulence.Vine
open Finset
variable {V D E : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]
    [AddCommGroup E] [Module ℝ E] (M : Molecule V D)

omit [DecidableEq D] in
/-- Internal signed flows cancel over all atoms of any induced group. -/
theorem sum_groupFlow_eq_zero (S : Finset V) (k : D → E)
    (hk : ∀ x,k (M.mate x)=k x) : ∑ v ∈ S, groupFlow M S k v=0 := by
  have hh := Finset.sum_fiberwise_of_maps_to
    (s := univ.filter (M.InGroup S)) (t := S) (g := M.atom)
    (fun x hx => (mem_filter.mp hx).2.1) (fun x => M.dartSign x • k x)
  have he : ∑ v ∈ S, groupFlow M S k v =
      ∑ x ∈ univ.filter (M.InGroup S), M.dartSign x • k x := by
    simpa only [groupFlow,Molecule.dartsAt,filter_filter,and_comm] using hh
  rw [he]
  exact sum_internal_eq_zero M S k hk

omit [DecidableEq D] in
/-- At a full-degree interior atom, internal flow is the entire local flow. -/
theorem groupFlow_eq_full (hM : M.IsMolecule) {S : Finset V} {v : V}
    (hv : v ∈ S) (hS : S ⊆ M.atoms) (hd : M.degIn S v=4) (k : D → E) :
    groupFlow M S k v=∑ x ∈ M.dartsAt v,M.dartSign x • k x := by
  have hf : (M.dartsAt v).filter (M.InGroup S)=M.dartsAt v := by
    apply filter_eq_self.mpr
    intro x hx
    have hxv := (Mole.mem_dartsAt M v x).mp hx
    exact ⟨hxv.symm ▸ hv,Mole.full_degree_no_exit M hM (hS hv) hd hxv⟩
  unfold groupFlow
  rw [hf]

/-- TARGET defdiff: conservation at all degree-four atoms makes the two
block gaps negatives of each other. No gap-transport hypothesis is used. -/
theorem block_gaps_neg (hM : M.IsMolecule) {S : Finset V} {a b : V}
    (hB : M.IsBlock S a b) (k : D → E) (hk : ∀ x,k (M.mate x)=k x)
    (hc : ∀ v ∈ M.atoms,M.deg v=4 → ∑ x ∈ M.dartsAt v,M.dartSign x • k x=0)
    {r r' : E} (hr : IsGroupGap M S k a r) (hr' : IsGroupGap M S k b r') : r=-r' := by
  have hzero : ∀ v ∈ S,v ∉ ({a,b} : Finset V) → groupFlow M S k v=0 := by
    intro v hv hvj
    have hne : v ≠ a ∧ v ≠ b := by simpa only [mem_insert,mem_singleton,not_or] using hvj
    have hd := hB.2.2.2.2.2.2.2.2.1 v hv hne.1 hne.2
    rw [groupFlow_eq_full M hM hv hB.1 hd]
    exact hc v (hB.1 hv) (by have hi := Mole.degIn_le_deg M S v; have ho := Mole.deg_le_four M hM (hB.1 hv); omega)
  have hsub : ({a,b} : Finset V) ⊆ S := by
    intro v hv
    rcases mem_insert.mp hv with rfl | hv
    · exact hB.2.1
    · have he := mem_singleton.mp hv
      subst v
      exact hB.2.2.1
  have hsum := sum_groupFlow_eq_zero M S k hk
  have he := Finset.sum_subset hsub hzero
  rw [← he,sum_pair hB.2.2.2.1] at hsum
  obtain ⟨ha,hb⟩ := Mole.block_joint_degrees M hB
  rw [← groupGap_eq_flow M ha hr,← groupGap_eq_flow M hb hr'] at hsum
  exact eq_neg_iff_add_eq_zero.mpr hsum

end WaveTurbulence.Vine
