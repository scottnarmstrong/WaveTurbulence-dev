/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Molecule.VineDVOrdinary
import Mathlib.Tactic

/-! # A contained ordinary block selecting both DV joints is an exact branch -/

public section
namespace WaveTurbulence.Vine
open Finset
variable {V D : Type*} [DecidableEq V] [Fintype D]

/-- The both-joints DV block proof identifies an actual branch atom set,
not merely a type-V realization. This equality is used for removals. -/
theorem block_in_DV_both_joints_eq_branch (M : Molecule V D) (hM : M.IsMolecule)
    {S T A : Finset V} {a b x y : V} (hS : M.IsVine .V S a b) (hT : M.IsVine .V T a b)
    (hi : S ∩ T={a,b}) (hA : M.IsBlock A x y) (hAU : A ⊆ S ∪ T)
    (ha : a ∈ A) (hb : b ∈ A) : A=S ∨ A=T := by
  have hU : IsDV M (S ∪ T) a b := ⟨S,T,hS,hT,hi,rfl⟩
  have hdU := isDV_degree_profile M hM hU
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
  obtain ⟨B,C,hB,hC,hUeq,hBA,hchoice⟩ : ∃ B C,M.IsVine .V B a b ∧ M.IsVine .V C a b ∧
      S ∪ T=B ∪ C ∧ B ⊆ A ∧ (B=S ∨ B=T) := by
    rcases mem_union.mp (hAU huA) with huS | huT
    · exact ⟨S,T,hS,hT,rfl,fills S hS u huA (mem_sdiff.mpr ⟨huS,huj⟩),Or.inl rfl⟩
    · exact ⟨T,S,hT,hS,union_comm S T,fills T hT u huA (mem_sdiff.mpr ⟨huT,huj⟩),Or.inr rfl⟩
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
  exact hchoice

end WaveTurbulence.Vine
