/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Molecule.VineDVBlockBranchEquality
public import WaveTurbulence.Foundations.Molecule.VineLargeVCInTypeV
public import WaveTurbulence.Foundations.Molecule.VineTypeVJointBranching
import Mathlib.Tactic

/-! # Exact ordinary vine pieces in a double type-V outer object -/

public section
namespace WaveTurbulence.Vine
open Finset
variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]

/-- Any actual vine contained in a DV is type I or type V. -/
theorem ordinary_vine_in_DV_shape (M : Molecule V D) (hM : M.IsMolecule)
    {P U : Finset V} {x y a b : V} (hU : IsDV M U a b)
    (hP : IsSomeVine M P x y) (hPU : P ⊆ U) : M.IsVine .I P x y ∨ M.IsVine .V P x y := by
  obtain ⟨Y,hY⟩ := hP
  rcases VC_in_DV M hM hU (isVine_isVC hY) hPU with h | h | h
  · have hc := doubleChain_card h
    have htype := isVine_typeI_of_card_lt_four hY (by omega)
    subst Y
    exact Or.inl hY
  · have hc := doubleChain_card h
    have htype := isVine_typeI_of_card_lt_four hY (by omega)
    subst Y
    exact Or.inl hY
  · exact Or.inr h

/-- A type-V vine in a DV is exactly one of its two actual branches. -/
theorem typeV_in_DV_eq_branch (M : Molecule V D) (hM : M.IsMolecule)
    {S T P : Finset V} {a b x y : V} (hS : M.IsVine .V S a b) (hT : M.IsVine .V T a b)
    (hi : S ∩ T={a,b}) (hP : M.IsVine .V P x y) (hPU : P ⊆ S ∪ T) : P=S ∨ P=T := by
  have hboth : a ∈ P ∧ b ∈ P := by
    by_contra hmiss
    have hconn : ∀ z,z=a ∨ z=b → GroupConnected M (P.erase z) :=
      fun z _hz => isVine_erase_connected hP z
    rcases DV_missing_joint_side M hM hS hT hPU hmiss hconn with hPS | hPT
    · have he := large_VC_in_typeV_eq M hM hS (isVine_isVC hP) hPS (typeV_card_gt_three hP)
      exact hmiss (he.symm ▸ ⟨hS.1.2.1,hS.1.2.2.1⟩)
    · have he := large_VC_in_typeV_eq M hM hT (isVine_isVC hP) hPT (typeV_card_gt_three hP)
      exact hmiss (he.symm ▸ ⟨hT.1.2.1,hT.1.2.2.1⟩)
  exact block_in_DV_both_joints_eq_branch M hM hS hT hi hP.1 hPU hboth.1 hboth.2

/-- A double-bond piece in a DV lies strictly in one branch and is
disjoint from the other. It cannot select either shared branch joint. -/
theorem typeI_in_DV_split_disjoint (M : Molecule V D) (hM : M.IsMolecule)
    {S T P : Finset V} {a b x y : V} (hS : M.IsVine .V S a b) (hT : M.IsVine .V T a b)
    (hi : S ∩ T={a,b}) (hP : M.IsVine .I P x y) (hPU : P ⊆ S ∪ T) :
    (P ⊆ S ∧ Disjoint P T) ∨ (P ⊆ T ∧ Disjoint P S) := by
  have hmiss : ¬(a ∈ P ∧ b ∈ P) := by
    intro hboth
    have hU : IsDV M (S ∪ T) a b := ⟨S,T,hS,hT,hi,rfl⟩
    have hv := block_in_DV_both_joints_isVineV M hM hU hP.1 hPU hboth.1 hboth.2
    have hlarge := typeV_card_gt_three hv
    have hsmall : P.card=2 := by rw [typeI_atoms hP,card_pair hP.1.2.2.2.1]
    omega
  have hconn : ∀ z,z=a ∨ z=b → GroupConnected M (P.erase z) :=
    fun z _hz => isVine_erase_connected hP z
  rcases DV_missing_joint_side M hM hS hT hPU hmiss hconn with hPS | hPT
  · have hab := typeI_in_typeV_joints_absent M hP hS hPS
    apply Or.inl
    refine ⟨hPS,disjoint_left.mpr ?_⟩
    intro v hvP hvT
    have hm := mem_inter.mpr ⟨hPS hvP,hvT⟩
    rw [hi] at hm
    rcases mem_insert.mp hm with he | he
    · exact hab.1 (he ▸ hvP)
    · exact hab.2 (mem_singleton.mp he ▸ hvP)
  · have hab := typeI_in_typeV_joints_absent M hP hT hPT
    apply Or.inr
    refine ⟨hPT,disjoint_left.mpr ?_⟩
    intro v hvP hvS
    have hm := mem_inter.mpr ⟨hvS,hPT hvP⟩
    rw [hi] at hm
    rcases mem_insert.mp hm with he | he
    · exact hab.1 (he ▸ hvP)
    · exact hab.2 (mem_singleton.mp he ▸ hvP)

end WaveTurbulence.Vine
