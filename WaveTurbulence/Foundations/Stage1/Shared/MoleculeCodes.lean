/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Molecule.MoleculeBasic
public import Mathlib.Data.Fintype.Perm
public import Mathlib.Data.Fintype.Pi
import Mathlib.Tactic

/-!
# The finite local-code count for garden reconstruction

DH21-2 Proposition 6.4 (L824–L830): each dart is assigned one of four
positions, parent or left/middle/right child. This module proves the
exponential count for those actual code assignments. Injective garden
reconstruction from the codes and ordered roots is a separate obligation.
-/

@[expose] public section
set_option autoImplicit false

namespace WaveTurbulence.Mole

/-- Position labels 0–3 on every actual dart (DH21-2 Prop 6.4). -/
abbrev PositionCode (D : Type*) := D → Fin 4

noncomputable instance {D : Type*} [Fintype D] : Fintype (PositionCode D) := by
  classical
  exact inferInstanceAs (Fintype (D → Fin 4))

variable {V D : Type*} [DecidableEq V] [Fintype D] (M : Molecule V D)

/-- A molecule with n atoms has at most 4n actual darts. -/
theorem card_darts_le_four_mul_atoms (hM : M.IsMolecule) :
    Fintype.card D ≤ 4*M.atoms.card := by
  calc
    Fintype.card D = ∑ v ∈ M.atoms, M.deg v := by
      rw [sum_degrees_eq_two_mul_bonds,two_mul_card_bonds]
    _ ≤ ∑ _v ∈ M.atoms, (4:ℕ) := Finset.sum_le_sum (fun v hv => deg_le_four M hM hv)
    _ = _ := by simp only [Finset.sum_const,nsmul_eq_mul,Nat.cast_id,mul_comm]

omit [DecidableEq V] in
/-- The number of local position-code assignments, before any consistency restrictions. -/
theorem card_position_codes : Fintype.card (PositionCode D) = 4^(Fintype.card D) := by
  classical
  simp only [PositionCode,Fintype.card_fun,Fintype.card_fin]

/-- All local incidence codes contribute at most 256 choices per atom. -/
theorem card_position_codes_le (hM : M.IsMolecule) :
    Fintype.card (PositionCode D) ≤ 256^(M.atoms.card) := by
  rw [card_position_codes]
  calc
    _ ≤ 4^(4*M.atoms.card) := Nat.pow_le_pow_right (by norm_num) (card_darts_le_four_mul_atoms M hM)
    _ = _ := by rw [pow_mul]; norm_num

end WaveTurbulence.Mole
