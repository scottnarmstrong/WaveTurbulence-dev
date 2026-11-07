/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.MoleProp.OneCircuitNormalization
public import WaveTurbulence.Foundations.FinalCount.MoleProp.LowDegreeCases
public import WaveTurbulence.Foundations.FinalCount.MoleProp.LargeGapLoops
import Mathlib.Tactic

/-! # DH23 Proposition 10.1: the complete priority-respecting operation(a)

This joins all actual circuit-loss cases. Self-loops give zero LG count;
no numerical deviation or local cardinality estimate is assumed.
-/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.MoleProp

theorem operation_a_normalized_bound (d : ℕ) (hd : 3 ≤ d) (γ : ℝ) (hγ : γ ∈ Set.Ioo (0 : ℝ) 1)
    (η : ℝ) (hη : 0 < η) (hηmax : η ≤ min γ (1-γ)/2) :
    ∃ Cstar : ℝ, 1 ≤ Cstar ∧ ∀ C1 ≥ Cstar, ∀ δ ∈ Set.Ioc (0 : ℝ) 1,
    ∃ R : ℝ, ∀ L ≥ R, 1 ≤ Real.log L →
    ∀ {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D],
    ∀ (M : Molecule V D), M.IsMolecule → ∀ v ∈ M.atoms, M.deg v ≤ 3 →
    (¬ ∃ a ∈ M.atoms, ∃ b ∈ M.atoms, a ≠ b ∧ M.deg a = 3 ∧
      (M.deg b = 3 ∨ M.deg b = 4) ∧ M.bondsBetween a b = 2) →
    ∀ (Adm : (D → (Fin d → ℤ)) → Prop) (P : Finset V → ℝ),
      (∀ κ, Adm κ → LargeGap M L γ η (0 : Mom d) κ) →
      (∀ S ∈ ladderCells M, 0 ≤ P S) →
      countAFree M L γ δ C1 (0 : Mom d) Adm P ≤
        countAFree (Degen.eraseAtoms M {v}) L γ δ C1 (0 : Mom d) (erasedFreeAdmissibility M {v} Adm) P := by
  classical
  obtain ⟨C3,R3,hC3,hThree⟩ := countAFree_erase_three_two_circuits d hd γ hγ
  refine ⟨max C3 1,le_max_right _ _,?_⟩
  intro C1 hC1 δ hδ
  obtain ⟨R1,hOne⟩ := countAFree_erase_one_circuit d hd γ hγ η hη hηmax δ hδ
  refine ⟨max (max R3 R1) 1,?_⟩
  intro L hL hlog V D _ _ _ M hM v hv hdeg hno Adm P hAdm hP
  have hL0 : 0 < L := zero_lt_one.trans_le ((le_max_right (max R3 R1) 1).trans hL)
  by_cases hloop : ∃ x : D, M.atom x = M.atom (M.mate x)
  · obtain ⟨x,hx⟩ := hloop
    rw [countAFree_eq_zero_of_loop M hL0 γ δ C1 η (0 : Mom d) Adm hAdm P x hx]
    exact bot_le
  · have hl : ∀ x, M.atom x ≠ M.atom (M.mate x) := fun x hx => hloop ⟨x,hx⟩
    rcases low_degree_removal_cases M hl hv hdeg with hzero | hone2 | hone3 | htwo
    · exact countAFree_erase_zero_loss_le M hM hl hv hdeg hno hzero hL0.ne' γ δ C1 (0 : Mom d) Adm P
    · exact hOne L ((le_max_right R3 R1).trans ((le_max_left (max R3 R1) 1).trans hL)) hlog
        C1 ((le_max_right C3 1).trans hC1) M hM v hv (Or.inl hone2.1) hno hone2.2.2 Adm P hAdm hP
    · exact hOne L ((le_max_right R3 R1).trans ((le_max_left (max R3 R1) 1).trans hL)) hlog
        C1 ((le_max_right C3 1).trans hC1) M hM v hv (Or.inr ⟨hone3.1,hone3.2.1⟩) hno hone3.2.2 Adm P hAdm hP
    · exact hThree C1 ((le_max_left C3 1).trans hC1)
        L ((le_max_left R3 R1).trans ((le_max_left (max R3 R1) 1).trans hL)) hlog δ hδ
        M hM v hv htwo.1 hno htwo.2.2 Adm P hP

end WaveTurbulence.MoleProp
