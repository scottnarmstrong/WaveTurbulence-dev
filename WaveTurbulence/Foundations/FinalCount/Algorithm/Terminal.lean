/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.Algorithm.State
public import WaveTurbulence.Foundations.FinalCount.AppBLinkDegrees
public import WaveTurbulence.Foundations.Molecule.MoleculeComponents
public import WaveTurbulence.Foundations.FinalCount.AppBBridgeComponents
import Mathlib.Tactic

/-! # The actual terminal molecules consist only of isolated atoms -/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.Mole.AppbAlgorithm
universe u v
open Finset
variable {V : Type v} [DecidableEq V]

def Terminal (s : State.{u,v} V) : Prop := s.graph.bonds = ∅

variable {D : Type u} [Fintype D] [DecidableEq D]

theorem isEmpty_darts_of_no_bonds (M : Molecule V D) (h : M.bonds = ∅) : IsEmpty D := by
  have hh := two_mul_card_bonds M
  rw [h,card_empty] at hh
  have hc : Fintype.card D = 0 := by omega
  exact Fintype.card_eq_zero_iff.mp hc

theorem degree_zero_of_no_bonds (M : Molecule V D) (h : M.bonds = ∅) (a : V) : M.deg a = 0 := by
  letI := isEmpty_darts_of_no_bonds M h
  simp only [Molecule.deg,Molecule.dartsAt,Finset.univ_eq_empty,filter_empty,card_empty]

theorem components_eq_atoms_of_no_bonds (M : Molecule V D) (h : M.bonds = ∅) :
    M.numComponents = M.atoms.card := by
  letI := isEmpty_darts_of_no_bonds M h
  let eqv : AppbComponents M ≃ M.atoms := {
    toFun := Quot.lift id (by
      intro a b hab
      obtain ⟨x,hx,hy⟩ := hab
      exact isEmptyElim x)
    invFun := appbComponent M
    left_inv := by
      intro q
      induction q using Quot.inductionOn with | h a => rfl
    right_inv := by intro a; rfl }
  exact (Nat.card_congr eqv).trans (Nat.card_eq_finsetCard M.atoms)

theorem circuitRank_zero_of_no_bonds (M : Molecule V D) (h : M.bonds = ∅) : M.circuitRank = 0 := by
  unfold Molecule.circuitRank
  rw [h,card_empty,components_eq_atoms_of_no_bonds M h]
  push_cast
  ring

theorem links_empty_of_no_bonds (M : Molecule V D) (h : M.bonds = ∅) : appbLinks M = ∅ := by
  classical
  apply eq_empty_iff_forall_notMem.mpr
  intro S hS
  have hlink := (mem_appbLinks M S).mp hS
  obtain ⟨u,v,hL,hset⟩ := hlink
  have hu : u 0 ∈ S := hset ▸ mem_union_left _ (mem_image.mpr ⟨0,mem_univ _,rfl⟩)
  have hh := ((mem_appbLinks M S).mp hS).degree_ge_three hu
  rw [degree_zero_of_no_bonds M h] at hh
  omega

end WaveTurbulence.Mole.AppbAlgorithm
