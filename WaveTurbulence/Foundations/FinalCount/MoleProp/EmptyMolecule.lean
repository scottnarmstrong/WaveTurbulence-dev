/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.MoleProp.BridgeSeparation
public import WaveTurbulence.Foundations.FinalCount.MoleProp.LadderCells
public import WaveTurbulence.Foundations.FinalCount.MoleProp.GeneralCircuitDeletion
import Mathlib.Tactic

/-! # The literal empty counting base and nonnegative actual circuit rank -/

@[expose] public section
set_option autoImplicit false
open Finset
open scoped ENNReal
namespace WaveTurbulence.MoleProp
universe u v
variable {V : Type u} {D : Type v} [DecidableEq V] [Fintype D] [DecidableEq D]

theorem circuitRank_eq_zero_of_atoms_empty (M : Molecule V D) (he : M.atoms = ∅) : M.circuitRank = 0 := by
  have hb : M.bonds = ∅ := by
    apply eq_empty_iff_forall_notMem.mpr
    intro x _hx
    have hx := M.atom_mem x
    rw [he] at hx
    simpa using hx
  rw [Molecule.circuitRank,hb,he,Degen.numComponents_eq_card_componentSets]
  simp only [Degen.componentSets,he,image_empty,card_empty,Nat.cast_zero,sub_zero,add_zero]

theorem ladderCells_eq_empty_of_atoms_empty (M : Molecule V D) (he : M.atoms = ∅) : ladderCells M = ∅ := by
  classical
  apply eq_empty_iff_forall_notMem.mpr
  intro S hS
  obtain ⟨u,v,hL,_⟩ := (mem_filter.mp hS).2
  have hx := (hL.2.2.1 (0 : Fin 2)).1
  rw [he] at hx
  simpa using hx

theorem countAFree_le_one_of_atoms_empty (M : Molecule V D) (he : M.atoms = ∅)
    {d : ℕ} {L : ℝ} (hL : L ≠ 0) (γ δ C1 : ℝ) (w : Mom d)
    (Adm : (D → (Fin d → ℤ)) → Prop) (P : Finset V → ℝ) :
    countAFree M L γ δ C1 w Adm P ≤ 1 := by
  have hc := countEFree_le_one_of_all_bridges M hL γ δ w Adm (fun x => by
    have hx := M.atom_mem x
    rw [he] at hx
    simp at hx)
  unfold countAFree cellProduct
  rw [circuitRank_eq_zero_of_atoms_empty M he,ladderCells_eq_empty_of_atoms_empty M he]
  simpa using ENat.toENNReal_mono hc

/-- The actual finite quotient circuit rank is nonnegative, also for
 disconnected graphs and isolated atoms. -/
theorem circuitRank_nonneg (M : Molecule V D) : 0 ≤ M.circuitRank := by
  classical
  have aux : ∀ n : ℕ, ∀ {E : Type v} [Fintype E] [DecidableEq E]
      (N : Molecule V E), N.atoms.card = n → 0 ≤ N.circuitRank := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro E _ _ N hn
      by_cases he : N.atoms = ∅
      · rw [circuitRank_eq_zero_of_atoms_empty N he]
      · obtain ⟨z,hz⟩ := nonempty_iff_ne_empty.mpr he
        have hlt : (Degen.eraseAtoms N {z}).atoms.card < n := by
          have hh := Degen.card_atoms_erase_singleton_add_one N hz
          omega
        have hp := ih _ hlt (Degen.eraseAtoms N {z}) rfl
        exact hp.trans (circuitRank_erase_singleton_le_general N hz)
  exact aux _ M rfl

end WaveTurbulence.MoleProp
