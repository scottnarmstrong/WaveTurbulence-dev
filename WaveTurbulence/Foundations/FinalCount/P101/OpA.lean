/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.P101.OneCircuit
public import WaveTurbulence.Foundations.FinalCount.P101.NoCellOne
public import WaveTurbulence.Foundations.FinalCount.MoleProp.NoCellOperation
public import WaveTurbulence.Foundations.FinalCount.MoleProp.LowDegreeCases
public import WaveTurbulence.Foundations.FinalCount.MoleProp.OperationA
import Mathlib.Tactic

/-! # Prop 10.1': operation (a) with large gap at the removed atom only

Fork of G6 `operation_a_normalized_bound` (moleprop13 `OperationA.lean`, sha in `P101-COPIED-SHA256SUMS`). Changes:
the molecule is loop-free (hypothesis), and large gap is required only at the removed atom `v`, and not at all when
`deg v ≤ 1` (zero circuit loss; a protected leaf is deleted for free).
-/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.FinalCountG8.P101
open WaveTurbulence.MoleProp

theorem operation_a_normalized_bound_at (d : ℕ) (hd : 3 ≤ d) (γ : ℝ) (hγ : γ ∈ Set.Ioo (0 : ℝ) 1)
    (η : ℝ) (hη : 0 < η) (hηmax : η ≤ min γ (1-γ)/2) :
    ∃ Cstar : ℝ, 1 ≤ Cstar ∧ ∀ C1 ≥ Cstar, ∀ δ ∈ Set.Ioc (0 : ℝ) 1,
    ∃ R : ℝ, ∀ L ≥ R, 1 ≤ Real.log L →
    ∀ {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D],
    ∀ (M : Molecule V D), M.IsMolecule → (∀ x, M.atom x ≠ M.atom (M.mate x)) →
    ∀ v ∈ M.atoms, M.deg v ≤ 3 →
    (¬ ∃ a ∈ M.atoms, ∃ b ∈ M.atoms, a ≠ b ∧ M.deg a = 3 ∧
      (M.deg b = 3 ∨ M.deg b = 4) ∧ M.bondsBetween a b = 2) →
    ∀ (Adm : (D → (Fin d → ℤ)) → Prop) (P : Finset V → ℝ),
      (M.deg v ≤ 1 ∨ ∀ κ, Adm κ → LargeGapAt M v L γ η (0 : Mom d) κ) →
      (∀ S ∈ ladderCells M, 0 ≤ P S) →
      countAFree M L γ δ C1 (0 : Mom d) Adm P ≤
        countAFree (Degen.eraseAtoms M {v}) L γ δ C1 (0 : Mom d) (erasedFreeAdmissibility M {v} Adm) P := by
  classical
  obtain ⟨C3,R3,hC3,hThree⟩ := countAFree_erase_three_two_circuits d hd γ hγ
  refine ⟨max C3 1,le_max_right _ _,?_⟩
  intro C1 hC1 δ hδ
  obtain ⟨R1,hOne⟩ := countAFree_erase_one_circuit_at d hd γ hγ η hη hηmax δ hδ
  refine ⟨max (max R3 R1) 1,?_⟩
  intro L hL hlog V D _ _ _ M hM hl v hv hdeg hno Adm P hLG hP
  have hL0 : 0 < L := zero_lt_one.trans_le ((le_max_right (max R3 R1) 1).trans hL)
  rcases low_degree_removal_cases M hl hv hdeg with hzero | hone2 | hone3 | htwo
  · exact countAFree_erase_zero_loss_le M hM hl hv hdeg hno hzero hL0.ne' γ δ C1 (0 : Mom d) Adm P
  · exact hOne L ((le_max_right R3 R1).trans ((le_max_left (max R3 R1) 1).trans hL)) hlog
      C1 ((le_max_right C3 1).trans hC1) M hM v hv (Or.inl hone2.1) hno hone2.2.2 Adm P
      (hLG.resolve_left (by have := hone2.1; omega)) hP
  · exact hOne L ((le_max_right R3 R1).trans ((le_max_left (max R3 R1) 1).trans hL)) hlog
      C1 ((le_max_right C3 1).trans hC1) M hM v hv (Or.inr ⟨hone3.1,hone3.2.1⟩) hno hone3.2.2 Adm P
      (hLG.resolve_left (by have := hone3.1; omega)) hP
  · exact hThree C1 ((le_max_left C3 1).trans hC1)
      L ((le_max_left R3 R1).trans ((le_max_left (max R3 R1) 1).trans hL)) hlog δ hδ
      M hM v hv htwo.1 hno htwo.2.2 Adm P hP

theorem atom_deletion_normalized_bound_of_no_cell_at (d : ℕ) (hd : 3 ≤ d) (γ : ℝ)
    (hγ : γ ∈ Set.Ioo (0 : ℝ) 1)
    (η : ℝ) (hη : 0 < η) (hηmax : η ≤ min γ (1-γ)/2) :
    ∃ Cstar : ℝ, 1 ≤ Cstar ∧ ∀ C1 ≥ Cstar, ∀ δ ∈ Set.Ioc (0 : ℝ) 1,
    ∃ R : ℝ, ∀ L ≥ R, 1 ≤ Real.log L →
    ∀ {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D],
    ∀ (M : Molecule V D), M.IsMolecule → (∀ x, M.atom x ≠ M.atom (M.mate x)) →
    ∀ v ∈ M.atoms, M.deg v ≤ 3 →
    (∀ S ∈ ladderCells M, v ∉ S) →
    ∀ (Adm : (D → (Fin d → ℤ)) → Prop) (P : Finset V → ℝ),
      (M.deg v ≤ 1 ∨ ∀ κ, Adm κ → LargeGapAt M v L γ η (0 : Mom d) κ) →
      (∀ S ∈ ladderCells M, 0 ≤ P S) →
      countAFree M L γ δ C1 (0 : Mom d) Adm P ≤
        countAFree (Degen.eraseAtoms M {v}) L γ δ C1 (0 : Mom d) (erasedFreeAdmissibility M {v} Adm) P := by
  classical
  obtain ⟨C3,R3,hC3,hThree⟩ := countAFree_erase_three_two_circuits_of_no_cell d hd γ hγ
  refine ⟨max C3 1,le_max_right _ _,?_⟩
  intro C1 hC1 δ hδ
  obtain ⟨R1,hOne⟩ := countAFree_erase_one_circuit_of_no_cell_at d hd γ hγ η hη hηmax δ hδ
  refine ⟨max (max R3 R1) 1,?_⟩
  intro L hL hlog V D _ _ _ M hM hl v hv hdeg hcell Adm P hLG hP
  have hL0 : 0 < L := zero_lt_one.trans_le ((le_max_right (max R3 R1) 1).trans hL)
  rcases low_degree_removal_cases M hl hv hdeg with hzero | hone2 | hone3 | htwo
  · exact countAFree_erase_zero_loss_of_no_cell M hl hv hzero hL0.ne' γ δ C1 (0 : Mom d) Adm P hcell
  · exact hOne L ((le_max_right R3 R1).trans ((le_max_left (max R3 R1) 1).trans hL)) hlog
      C1 ((le_max_right C3 1).trans hC1) M hM v hv (Or.inl hone2.1) hcell hone2.2.2 Adm P
      (hLG.resolve_left (by have := hone2.1; omega)) hP
  · exact hOne L ((le_max_right R3 R1).trans ((le_max_left (max R3 R1) 1).trans hL)) hlog
      C1 ((le_max_right C3 1).trans hC1) M hM v hv (Or.inr ⟨hone3.1,hone3.2.1⟩) hcell hone3.2.2 Adm P
      (hLG.resolve_left (by have := hone3.1; omega)) hP
  · exact hThree C1 ((le_max_left C3 1).trans hC1)
      L ((le_max_left R3 R1).trans ((le_max_left (max R3 R1) 1).trans hL)) hlog δ hδ
      M hM v hv htwo.1 hcell htwo.2.2 Adm P hP

end WaveTurbulence.FinalCountG8.P101
