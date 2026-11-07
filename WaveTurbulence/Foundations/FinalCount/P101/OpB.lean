/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.P101.DoublePair
public import WaveTurbulence.Foundations.FinalCount.MoleProp.OperationB
public import WaveTurbulence.Foundations.FinalCount.MoleProp.DoublePairThreeNormalization
public import WaveTurbulence.Foundations.FinalCount.MoleProp.DoublePairFixedExtraNormalization
public import WaveTurbulence.Foundations.FinalCount.MoleProp.DoublePairFiveNormalization
import Mathlib.Tactic

/-! # DH23 Proposition 10.1: the complete paired-removal operation (b) -/

@[expose] public section
set_option autoImplicit false
open Finset
namespace WaveTurbulence.FinalCountG8.P101
open WaveTurbulence.MoleProp

theorem operation_b_normalized_bound_at (d : ℕ) (hd : 3 ≤ d) (γ : ℝ)
    (hγ : γ ∈ Set.Ioo (0 : ℝ) 1) (η : ℝ) (hη : 0 < η)
    (hηmax : η ≤ min γ (1-γ)/2) :
    ∃ Cstar : ℝ, 1 ≤ Cstar ∧ ∀ C1 ≥ Cstar, ∀ δ ∈ Set.Ioc (0 : ℝ) 1,
    ∃ R : ℝ, ∀ L ≥ R, 1 ≤ Real.log L →
    ∀ {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D],
    ∀ (M : Molecule V D), M.IsMolecule → (∀ x, M.atom x ≠ M.atom (M.mate x)) →
    ∀ a ∈ M.atoms, ∀ b ∈ M.atoms, a ≠ b → M.deg a = 3 →
      (M.deg b = 3 ∨ M.deg b = 4) → M.bondsBetween a b = 2 →
    ∀ (Adm : (D → (Fin d → ℤ)) → Prop) (P : Finset V → ℝ),
      (∀ κ, Adm κ → LargeGapAt M a L γ η (0 : Mom d) κ) →
      (∀ κ, Adm κ → LargeGapAt M b L γ η (0 : Mom d) κ) →
      (∀ κ, Adm κ → CellGapRestriction M L (0 : Mom d) P (GapScale L) κ) →
      (∀ S ∈ ladderCells M, 0 ≤ P S) →
      countAFree M L γ δ C1 (0 : Mom d) Adm P ≤
        countAFree (Degen.eraseAtoms M {a,b}) L γ δ C1 (0 : Mom d)
          (erasedFreeAdmissibility M {a,b} Adm) P := by
  classical
  obtain ⟨C0,hC0,h0⟩ := operation_b_no_cell_normalized_bound_at d hd γ hγ η hη hηmax
  obtain ⟨C3,hC3,h3⟩ := operation_b_three_three_normalized_bound d hd γ hγ
  obtain ⟨C4,hC4,h4⟩ := operation_b_three_four_fixed_normalized_bound d hd γ hγ
  obtain ⟨C5,hC5,h5⟩ := operation_b_three_four_three_circuits_normalized_bound d hd γ hγ
  refine ⟨max (max C0 C3) (max C4 C5),?_,?_⟩
  · exact hC0.trans ((le_max_left C0 C3).trans (le_max_left _ _))
  intro C1 hC1 δ hδ
  have h01 : C0 ≤ C1 := (le_max_left C0 C3).trans ((le_max_left _ _).trans hC1)
  have h31 : C3 ≤ C1 := (le_max_right C0 C3).trans ((le_max_left _ _).trans hC1)
  have h41 : C4 ≤ C1 := (le_max_left C4 C5).trans ((le_max_right _ _).trans hC1)
  have h51 : C5 ≤ C1 := (le_max_right C4 C5).trans ((le_max_right _ _).trans hC1)
  obtain ⟨R0,hR0⟩ := h0 C1 h01 δ hδ
  obtain ⟨R3,hR3⟩ := h3 C1 h31 δ hδ
  obtain ⟨R4,hR4⟩ := h4 C1 h41 δ hδ
  obtain ⟨R5,hR5⟩ := h5 C1 h51 δ hδ
  refine ⟨max (max R0 R3) (max (max R4 R5) 1),?_⟩
  intro L hL hlog V D _ _ _ M hM hloop a ha b hb hab ha3 hb34 hdouble Adm P hLG hLGb hGap hP
  have hL0 : R0 ≤ L := (le_max_left R0 R3).trans ((le_max_left _ _).trans hL)
  have hL3 : R3 ≤ L := (le_max_right R0 R3).trans ((le_max_left _ _).trans hL)
  have hL4 : R4 ≤ L := (le_max_left R4 R5).trans ((le_max_left _ _).trans ((le_max_right _ _).trans hL))
  have hL5 : R5 ≤ L := (le_max_right R4 R5).trans ((le_max_left _ _).trans ((le_max_right _ _).trans hL))
  have hLp : 0 < L := zero_lt_one.trans_le ((le_max_right _ 1).trans ((le_max_right _ _).trans hL))
  by_cases hnone : ∀ S ∈ ladderCells M, Disjoint S {a,b}
  · convert hR0 L hL0 hlog M hM hloop a ha b hb hab ha3 hb34 hdouble hnone Adm P hLG hLGb hP using 1 <;> simp only [singleton_union]
    congr 1 <;> simp only [singleton_union]
  push Not at hnone
  obtain ⟨S,hS,hmeet⟩ := hnone
  have haS : a ∈ S := by
    by_contra haS
    exact hmeet ((cell_disjoint_double_pair_iff M hM hab hdouble ((mem_filter.mp hS).2)).mpr haS)
  rcases hb34 with hb3 | hb4
  · exact hR3 L hL3 hlog M hM hloop a ha b hb hab ha3 hb3 hdouble S hS haS Adm P hGap hP
  · rcases circuitRank_erase_double_cell_three_four_cases M hM hloop hab ha3 hb4 hdouble
        ((mem_filter.mp hS).2) hmeet with hχ2 | hχ3
    · exact hR4 L hL4 hlog M hM hloop a ha b hb hab ha3 hb4 hdouble hχ2 S hS haS Adm P hGap hP
    · exact hR5 L hL5 hlog M hM a ha b hb hab ha3 hb4 hdouble S hS haS hχ3 Adm P hP

end WaveTurbulence.FinalCountG8.P101
