/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.Algorithm.SingletonNuBound
public import WaveTurbulence.Foundations.FinalCount.Algorithm.DeletionDartEquiv
import Mathlib.Tactic

/-! # Uniform nu cost of deleting any actual finite atom set -/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.Mole.AppbAlgorithm
open Finset
variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]

theorem eraseAtoms_nu_change_abs_le (M : Molecule V D) (hM : M.IsMolecule)
    (Y : Finset V) (hY : Y ⊆ M.atoms) :
    |appbNu (Degen.eraseAtoms M Y)-appbNu M| ≤ 16*(Y.card : ℤ) := by
  classical
  revert hY
  induction Y using Finset.induction_on with
  | empty =>
    intro hY
    rw [appbNu_erase_empty,sub_self,abs_zero,card_empty,Nat.cast_zero,mul_zero]
  | @insert a Y ha ih =>
    intro hY
    have hsub : Y ⊆ M.atoms := fun v hv => hY (mem_insert_of_mem hv)
    have haM : a ∈ M.atoms := hY (mem_insert_self _ _)
    have haPost : a ∈ (Degen.eraseAtoms M Y).atoms := mem_sdiff.mpr ⟨haM,ha⟩
    have hM' := appb_eraseAtoms_isMolecule M hM Y
    have hstep := singleton_nu_change_abs_le (Degen.eraseAtoms M Y) hM' haPost
    have hprev := ih hsub
    have hU : Y ∪ {a} = insert a Y := by ext v; simp only [mem_union,mem_singleton,mem_insert]; tauto
    have heq := appbNu_erase_erase_eq_union M Y {a}
    rw [hU] at heq
    calc
      _ = |(appbNu (Degen.eraseAtoms (Degen.eraseAtoms M Y) {a})-appbNu (Degen.eraseAtoms M Y))+
          (appbNu (Degen.eraseAtoms M Y)-appbNu M)| := by rw [heq]; congr 1; ring
      _ ≤ |appbNu (Degen.eraseAtoms (Degen.eraseAtoms M Y) {a})-appbNu (Degen.eraseAtoms M Y)|+
          |appbNu (Degen.eraseAtoms M Y)-appbNu M| := abs_add_le _ _
      _ ≤ 16+16*(Y.card : ℤ) := add_le_add hstep hprev
      _ = _ := by rw [card_insert_of_notMem ha,Nat.cast_add,Nat.cast_one]; ring

theorem realization_nu_change_abs_le (M : Molecule V D) (hM : M.IsMolecule)
    {P : AppbPattern} (r : AppbRealization M P) :
    |appbNu r.post-appbNu M| ≤ 16*(P.removed.card : ℤ) := by
  have hc : r.removedAtoms.card = P.removed.card := card_image_of_injOn
    (r.vertex_injective.mono (fun a ha => mem_union_left _ ha))
  have hh := eraseAtoms_nu_change_abs_le M hM r.removedAtoms r.removedAtoms_subset
  rw [hc] at hh
  exact hh

end WaveTurbulence.Mole.AppbAlgorithm
