/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Molecule.VineLowDegreeJoints
public import WaveTurbulence.Foundations.Molecule.VineNestedDegreeClosure
public import WaveTurbulence.Foundations.Molecule.VineBlockJoints
public import WaveTurbulence.Foundations.Molecule.VineEmptyRungs
public import WaveTurbulence.Foundations.Molecule.VineBlockSeparator
public import WaveTurbulence.Foundations.Molecule.VineJointPairDegrees
import Mathlib.Tactic

/-! # Recognizing an entire connected block and reordering its joints -/

public section
namespace WaveTurbulence.Vine
open Finset
variable {V D : Type*} [DecidableEq V] [Fintype D]

/-- A nested block containing both joints of a connected outer block is
that entire block: all its selected atoms use the exact outer degree. -/
theorem nested_blocks_both_joints_eq (M : Molecule V D)
    {A S : Finset V} {a b x y : V} (hA : M.IsBlock A x y) (hS : M.IsBlock S a b)
    (hC : GroupConnected M S) (hAS : A ⊆ S) (ha : a ∈ A) (hb : b ∈ A) : A=S := by
  have hSd := Mole.block_joint_degrees M hS
  have hAd := Mole.block_joint_degrees M hA
  have hj := joints_eq_of_two_low_degrees M hAS ha hb hS.2.2.2.1 hA.2.2.2.1
    (by omega) (by omega) hA.2.2.2.2.2.2.2.2.1
  apply nested_degree_eq_of_connected M hAS ⟨a,ha⟩ hC
  intro v hvA
  by_cases hvx : v=x
  · have hvm : v ∈ ({a,b} : Finset V) := hj ▸ (hvx.symm ▸ mem_insert_self x ({y} : Finset V))
    have hdv : M.degIn A v=2 := hvx.symm ▸ hAd.1
    rw [hdv]
    rcases mem_insert.mp hvm with hva | hvb
    · exact (hva ▸ hSd.1).symm
    · exact (mem_singleton.mp hvb ▸ hSd.2).symm
  · by_cases hvy : v=y
    · have hvm : v ∈ ({a,b} : Finset V) := hj ▸ (hvy.symm ▸ mem_insert_of_mem (mem_singleton_self y))
      have hdv : M.degIn A v=2 := hvy.symm ▸ hAd.2
      rw [hdv]
      rcases mem_insert.mp hvm with hva | hvb
      · exact (hva ▸ hSd.1).symm
      · exact (mem_singleton.mp hvb ▸ hSd.2).symm
    · have hvj : v ∉ ({a,b} : Finset V) := by rw [← hj]; simp only [mem_insert,mem_singleton]; exact not_or.mpr ⟨hvx,hvy⟩
      have hvab : v ≠ a ∧ v ≠ b := by simpa only [mem_insert,mem_singleton,not_or] using hvj
      exact (hA.2.2.2.2.2.2.2.2.1 v hvA hvx hvy).trans
        (hS.2.2.2.2.2.2.2.2.1 v (hAS hvA) hvab.1 hvab.2).symm

/-- The unchanged pinned vine predicate depends on the unordered joint
pair, which the actual block degrees determine uniquely. -/
theorem isVine_rejoint {M : Molecule V D} {X : VineType} {S : Finset V} {a b x y : V}
    (hV : M.IsVine X S a b) (hB : M.IsBlock S x y) : M.IsVine X S x y := by
  obtain ⟨hS,⟨R⟩⟩ := isVine_iff_realization.mp hV
  have hj := block_joints_unique M hS hB
  have hh := congrArg (Finset.image R.f) hj
  simp only [image_insert,image_singleton] at hh
  apply isVine_iff_realization.mpr
  exact ⟨hB,⟨⟨R.k,R.length_eq,R.f,R.injOn,R.image_eq,hh.symm.trans R.joints_eq,R.bonds_eq⟩⟩⟩

/-- A nested block selecting an outer joint must select every neighbor
of that joint in the outer block, since both induced degrees equal two. -/
theorem nested_block_joint_adj_mem (M : Molecule V D) {A S : Finset V} {a b x y v z : V}
    (hA : M.IsBlock A x y) (hS : M.IsBlock S a b) (hAS : A ⊆ S)
    (hvA : v ∈ A) (hvj : v=a ∨ v=b) (hzS : z ∈ S) (hvz : M.Adj v z) : z ∈ A := by
  have hdS : M.degIn S v=2 := hvj.elim
    (fun h => h.symm ▸ (Mole.block_joint_degrees M hS).1)
    (fun h => h.symm ▸ (Mole.block_joint_degrees M hS).2)
  have hlow := block_degree_ge_two M hA hvA
  have hle := degIn_mono M hAS v
  have hdA : M.degIn A v=2 := by omega
  have he := internal_darts_eq_of_nested_degree M hAS v (hdA.trans hdS.symm)
  obtain ⟨d,hdv,hdz⟩ := hvz
  have hdS' : d ∈ (M.dartsAt v).filter (M.InGroup S) := mem_filter.mpr
    ⟨(Mole.mem_dartsAt M v d).mpr hdv,hdv.symm ▸ hAS hvA,hdz.symm ▸ hzS⟩
  rw [← he] at hdS'
  exact hdz ▸ (mem_filter.mp hdS').2.2

/-- The two joints of an actual type-V vine share their one actual bond. -/
theorem typeV_joints_adj {M : Molecule V D} {S : Finset V} {a b : V}
    (hV : M.IsVine .V S a b) : M.Adj a b := by
  classical
  have hpair := (isVine_joint_pair_degrees hV).1
  change M.degIn {a,b} a=1 at hpair
  obtain ⟨d,hd⟩ := card_pos.mp (show 0<((M.dartsAt a).filter (M.InGroup {a,b})).card from by change 0<M.degIn {a,b} a; omega)
  obtain ⟨hda,hg⟩ := mem_filter.mp hd
  have had := (Mole.mem_dartsAt M a d).mp hda
  have hloop := connected_degree_two_no_loop M (isVine_connected hV) hV.1.2.1 hV.1.2.2.1
    hV.1.2.2.2.1 (Mole.block_joint_degrees M hV.1).1
  rcases mem_insert.mp hg.2 with he | he
  · exact False.elim (hloop ⟨d,had,he⟩)
  · exact ⟨d,had,mem_singleton.mp he⟩

end WaveTurbulence.Vine
