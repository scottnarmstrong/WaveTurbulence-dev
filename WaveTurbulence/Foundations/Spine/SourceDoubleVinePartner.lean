/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.Spine.SourceThreeBlockExclusion
public import WaveTurbulence.Foundations.Molecule.VineInteriorConnected
public import WaveTurbulence.Foundations.Molecule.VineNestedBlockRecognition
/-! Actual double-vine branches have a unique partner: omission choices form a matching. -/
public section
set_option autoImplicit false
namespace WaveTurbulence.LGSpine
open Finset

/-- Three distinct type-V branches at the same joints would saturate a component.
This proves the partner uniqueness used in the source's one-constituent omission. -/
theorem source_doubleVine_partner_unique {V D : Type*} [DecidableEq V] [Fintype D]
    (M : Molecule V D) (hM : M.IsMolecule) {S T U : Finset V} {a b : V}
    (hS : M.IsVine .V S a b) (hT : M.IsVine .V T a b) (hU : M.IsVine .V U a b)
    (hST : S ∩ T = {a,b}) (hSU : S ∩ U = {a,b}) : T = U := by
  by_cases hTU : T ⊆ U
  · exact Vine.nested_blocks_both_joints_eq M hT.1 hU.1
      (Vine.isVine_connected hU) hTU hT.1.2.1 hT.1.2.2.1
  · have hInt := Mole.block_same_joints_intersection M hM hT.1 hU.1 hTU
      (Vine.isVine_interior_connected hT)
    have hp := Vine.isVine_joint_pair_degrees hS
    change M.degIn {a,b} a = 1 ∧ M.degIn {a,b} b = 1 at hp
    exact (no_three_joint_blocks M hM hS.1 hT.1 hU.1 hST hSU hInt (by
      intro v hv
      rcases mem_insert.mp hv with rfl | hv
      · exact hp.1
      · exact (mem_singleton.mp hv).symm ▸ hp.2)).elim

private theorem source_block_swap {V D : Type*} [DecidableEq V] [Fintype D]
    {M : Molecule V D} {S : Finset V} {a b : V} (h : M.IsBlock S a b) :
    M.IsBlock S b a := by
  obtain ⟨hs, ha, hb, hab, hoa, hia, hob, hib, hd, hc⟩ := h
  exact ⟨hs, hb, ha, hab.symm, hob, hib, hoa, hia,
    fun v hv hvb hva => hd v hv hva hvb, hc⟩

/-- Partner uniqueness does not depend on the ordering of the source joints. -/
theorem source_doubleVine_partner_unique_unordered {V D : Type*} [DecidableEq V] [Fintype D]
    (M : Molecule V D) (hM : M.IsMolecule) {S T U : Finset V} {a b c e : V}
    (hS : M.IsVine .V S a b) (hT : M.IsVine .V T a b)
    (hS' : M.IsVine .V S c e) (hU : M.IsVine .V U c e)
    (hST : S ∩ T = {a,b}) (hSU : S ∩ U = {c,e}) : T = U := by
  have hj := Vine.block_joints_unique M hS.1 hS'.1
  have hj' : ({a,b} : Set V) = {c,e} := by
    simpa only [Finset.coe_pair] using congrArg (fun s : Finset V => (s : Set V)) hj
  rcases Set.pair_eq_pair_iff.mp hj' with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact source_doubleVine_partner_unique M hM hS hT hU hST hSU
  · have hUr : M.IsVine .V U a b :=
      Vine.isVine_rejoint hU (source_block_swap hU.1)
    apply source_doubleVine_partner_unique M hM hS hT hUr hST
    simpa only [Finset.pair_comm] using hSU

end WaveTurbulence.LGSpine
