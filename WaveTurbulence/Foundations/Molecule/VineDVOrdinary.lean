/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Molecule.VineDVMissingJoint
public import WaveTurbulence.Foundations.Molecule.VineFullInteriorSelection
public import WaveTurbulence.Foundations.Molecule.VineVCInTypeV
public import WaveTurbulence.Foundations.Molecule.VineLowDegreeJoints
import Mathlib.Tactic

/-! # Ordinary contained objects in a DV have the subsetvc forms -/

public section
namespace WaveTurbulence.Vine
open Finset
variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]

omit [DecidableEq D] in
/-- TARGET subsetvc, both-joints DV case: any contained ordinary block
containing both DV joints is exactly one of its type-V branches. -/
theorem block_in_DV_both_joints_isVineV (M : Molecule V D) (hM : M.IsMolecule)
    {A U : Finset V} {a b x y : V} (hU : IsDV M U a b) (hA : M.IsBlock A x y)
    (hAU : A ⊆ U) (ha : a ∈ A) (hb : b ∈ A) : M.IsVine .V A x y := by
  have hdU := isDV_degree_profile M hM hU
  obtain ⟨S,T,hS,hT,_hi,rfl⟩ := hU
  have hj := joints_eq_of_two_low_degrees M hAU ha hb hS.1.2.2.2.1 hA.2.2.2.1
    hdU.1.le hdU.2.1.le hA.2.2.2.2.2.2.2.2.1
  have hda : M.degIn A a=2 := by
    have ham : a ∈ ({x,y} : Finset V) := hj.symm ▸ mem_insert_self _ _
    rcases mem_insert.mp ham with hax | hay
    · exact hax.symm ▸ (Mole.block_joint_degrees M hA).1
    · exact (mem_singleton.mp hay).symm ▸ (Mole.block_joint_degrees M hA).2
  have hfull (v : V) (hv : v ∈ A) (hvj : v ∉ ({a,b} : Finset V)) : M.degIn A v=4 := by
    have hvxy : v ∉ ({x,y} : Finset V) := hj.symm ▸ hvj
    have hne : v ≠ x ∧ v ≠ y := by simpa only [mem_insert,mem_singleton,not_or] using hvxy
    exact hA.2.2.2.2.2.2.2.2.1 v hv hne.1 hne.2
  have lower (B : Finset V) (hB : M.IsVine .V B a b) : ({a,b} : Finset V) ⊆ B := by
    intro v hv
    rcases mem_insert.mp hv with hva | hvb
    · exact hva.symm ▸ hB.1.2.1
    · exact (mem_singleton.mp hvb).symm ▸ hB.1.2.2.1
  have fills (B : Finset V) (hB : M.IsVine .V B a b) (u : V) (huA : u ∈ A)
      (huI : u ∈ B \ {a,b}) : B ⊆ A :=
    full_interior_selection M hM hA.1 ha hb (isVine_interior_connected hB)
      (fun v hv hvI => hfull v hv (mem_sdiff.mp hvI).2) huA huI
  have hn : ¬A ⊆ ({a,b} : Finset V) := by
    intro hsub
    have hpairSub : ({a,b} : Finset V) ⊆ A := by
      intro v hv
      rcases mem_insert.mp hv with hva | hvb
      · exact hva.symm ▸ ha
      · exact (mem_singleton.mp hvb).symm ▸ hb
    have heq := Subset.antisymm hsub hpairSub
    have hp := (isVine_joint_pair_degrees hS).1
    change M.degIn {a,b} a=1 at hp
    rw [heq,hp] at hda
    omega
  obtain ⟨u,huA,huj⟩ := Finset.not_subset.mp hn
  obtain ⟨B,C,hB,hC,hUeq,hBA⟩ : ∃ B C,M.IsVine .V B a b ∧ M.IsVine .V C a b ∧
      S ∪ T=B ∪ C ∧ B ⊆ A := by
    rcases mem_union.mp (hAU huA) with huS | huT
    · exact ⟨S,T,hS,hT,rfl,fills S hS u huA (mem_sdiff.mpr ⟨huS,huj⟩)⟩
    · exact ⟨T,S,hT,hS,union_comm S T,fills T hT u huA (mem_sdiff.mpr ⟨huT,huj⟩)⟩
  have hAB : A ⊆ B := by
    intro v hvA
    by_contra hvB
    have hvC : v ∈ C := (mem_union.mp (hUeq ▸ hAU hvA)).resolve_left hvB
    have hvj : v ∉ ({a,b} : Finset V) := fun hh => hvB (lower B hB hh)
    have hCA := fills C hC v hvA (mem_sdiff.mpr ⟨hvC,hvj⟩)
    have hUA : S ∪ T ⊆ A := by rw [hUeq]; exact union_subset hBA hCA
    have heq := Subset.antisymm hAU hUA
    rw [heq,hdU.1] at hda
    omega
  have heq := Subset.antisymm hAB hBA
  subst A
  exact isVine_rejoint hB hA

/-- TARGET Lemma subsetvc, complete ordinary inner-VC classification in
a DV. In fact this structural result needs no decoration or gap hypothesis. -/
theorem VC_in_DV (M : Molecule V D) (hM : M.IsMolecule)
    {A U : Finset V} {a b x y : V} (hU : IsDV M U a b) (hA : IsVC M A x y) (hAU : A ⊆ U) :
    DoubleChain M A x y 1 ∨ DoubleChain M A x y 2 ∨ M.IsVine .V A x y := by
  by_cases hboth : a ∈ A ∧ b ∈ A
  · exact Or.inr (Or.inr (block_in_DV_both_joints_isVineV M hM hU hA.1 hAU hboth.1 hboth.2))
  · obtain ⟨S,T,hS,hT,hi,rfl⟩ := hU
    rcases VC_in_DV_missing_joint_side M hM hS hT hi hA hAU hboth with hAS | hAT
    · exact VC_in_typeV M hM hS hA hAS
    · exact VC_in_typeV M hM hT hA hAT

end WaveTurbulence.Vine
