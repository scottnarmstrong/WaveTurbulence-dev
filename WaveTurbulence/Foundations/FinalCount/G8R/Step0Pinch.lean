/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.G8R.Step0Facts
public import WaveTurbulence.Foundations.FinalCount.MoleProp4T.YLem2Y1c3
import Mathlib.Tactic

/-! # The molecule after a (Y1) case 3 sequence

The chain `Y` (all degrees four) is attached by its two exits to `w`. Then `𝕄 ∖ Y` has `E − 2|Y| − 1` bonds, `w` loses
exactly two bonds, and connectivity is kept.
-/

@[expose] public section
set_option autoImplicit false
open Finset
namespace WaveTurbulence.MoleProp4
variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]

namespace Y1End3
variable {M : Molecule V D} {C : YChain M} (E : Y1End3 C)

include E in
theorem erase_bonds (hcap : ∀ v ∈ M.atoms, M.outdeg v ≤ 2 ∧ M.indeg v ≤ 2) :
    ((Degen.eraseAtoms M C.set).bonds.card : ℤ) = M.bonds.card - 2 * C.set.card - 1 := by
  have hY := E.toPinch_Y hcap
  have h1 := two_mul_piece_bonds M (E.toPinch hcap).sub
  rw [(E.toPinch hcap).cross, card_pair (E.toPinch hcap).ne, hY, sum_congr rfl E.deg_four, sum_const,
    smul_eq_mul] at h1
  have h2 := (E.toPinch hcap).bonds_eq
  rw [hY] at h2
  omega

theorem erase_deg_w :
    (Degen.eraseAtoms M C.set).deg (M.atom (M.mate E.x)) + 2 = M.deg (M.atom (M.mate E.x)) := by
  classical
  have hw : M.atom (M.mate E.x) ∉ C.set := E.hxo
  have h := deg_eraseAtoms_add (N := M) C.set hw
  have hrem : Degen.removedDartsAt M C.set (M.atom (M.mate E.x)) = {M.mate E.x, M.mate E.y} := by
    ext z
    simp only [Degen.removedDartsAt, Molecule.dartsAt, mem_filter, mem_univ, true_and, mem_insert, mem_singleton]
    constructor
    · rintro ⟨hz1, hz2⟩
      have hc : M.mate z ∈ crossDarts M C.set := mem_crossDarts.mpr ⟨hz2, by rw [M.mate_mate, hz1]; exact hw⟩
      rw [E.cross_eq] at hc
      rcases mem_insert.mp hc with h | h
      · left; rw [← h, M.mate_mate]
      · right; rw [← mem_singleton.mp h, M.mate_mate]
    · rintro (rfl | rfl)
      · exact ⟨rfl, by rw [M.mate_mate, E.hx]; exact C.a_mem le_rfl⟩
      · exact ⟨E.same.symm, by rw [M.mate_mate, E.hy]; exact C.b_mem le_rfl⟩
  have hne : M.mate E.x ≠ M.mate E.y := fun h => E.x_ne_y (by
    have := congrArg M.mate h; rwa [M.mate_mate, M.mate_mate] at this)
  rw [hrem, card_pair hne] at h
  omega

include E in
omit [DecidableEq D] in
theorem erase_connected (hcap : ∀ v ∈ M.atoms, M.outdeg v ≤ 2 ∧ M.indeg v ≤ 2)
    (hconn : ∀ u ∈ M.atoms, ∀ v ∈ M.atoms, M.SameComponent u v) :
    ∀ u ∈ (Degen.eraseAtoms M C.set).atoms, ∀ v ∈ (Degen.eraseAtoms M C.set).atoms,
      (Degen.eraseAtoms M C.set).SameComponent u v := by
  classical
  intro u hu v hv
  have hY := E.toPinch_Y hcap
  have hu' := mem_sdiff.mp hu
  have hv' := mem_sdiff.mp hv
  have h := (E.toPinch hcap).erase_sameComponent_fold (hconn u hu'.1 v hv'.1)
  rw [hY, ite_of_not hu'.2, ite_of_not hv'.2] at h
  exact h

end Y1End3

omit [DecidableEq D] in
/-- After erasing a set, bond counts only drop. -/
theorem erase_bonds_le (M : Molecule V D) (Y : Finset V) (p q : V) :
    (Degen.eraseAtoms M Y).bondsBetween p q ≤ M.bondsBetween p q := by
  classical
  by_cases hp : p ∈ Y
  · rw [bondsBetween_erase_of_mem M Y hp]; omega
  by_cases hq : q ∈ Y
  · rw [Degen.bondsBetween_comm, bondsBetween_erase_of_mem M Y hq]; omega
  rw [Degen.bondsBetween_erase_eq _ _ hp hq]

end WaveTurbulence.MoleProp4
