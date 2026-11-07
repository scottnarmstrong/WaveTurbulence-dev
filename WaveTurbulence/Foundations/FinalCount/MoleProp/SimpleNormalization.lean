/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.MoleProp.LadderCells
import Mathlib.Tactic

/-! # The literal Section 10 normalization on molecules with only single bonds -/

@[expose] public section
set_option autoImplicit false
open Finset
open scoped ENNReal
namespace WaveTurbulence.MoleProp
variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]

theorem ladderCells_eq_empty_of_simple (M : Molecule V D)
    (hsimple : ∀ a b, a ≠ b → M.bondsBetween a b ≤ 1) : ladderCells M = ∅ := by
  classical
  apply eq_empty_iff_forall_notMem.mpr
  intro S hS
  obtain ⟨u,v,hL,_⟩ := (mem_filter.mp hS).2
  have hne : u 0 ≠ v 0 := by
    intro he
    have hh : (Sum.inl (0 : Fin 2) : Fin 2 ⊕ Fin 2) = Sum.inr 0 := hL.2.1 he
    cases hh
  have hh := hsimple (u 0) (v 0) hne
  rw [hL.2.2.2.1 0] at hh
  omega

theorem cellProduct_eq_one_of_simple (M : Molecule V D)
    (hsimple : ∀ a b, a ≠ b → M.bondsBetween a b ≤ 1)
    (L γ δ : ℝ) (P : Finset V → ℝ) : cellProduct M L γ δ P = 1 := by
  simp only [cellProduct,ladderCells_eq_empty_of_simple M hsimple,prod_empty]

theorem countAFree_eq_of_simple (M : Molecule V D)
    (hsimple : ∀ a b, a ≠ b → M.bondsBetween a b ≤ 1)
    {d : ℕ} (L γ δ C1 : ℝ) (w : Mom d)
    (Adm : (D → (Fin d → ℤ)) → Prop) (P : Finset V → ℝ) :
    countAFree M L γ δ C1 w Adm P =
      (countEFree M L γ δ w Adm : ℝ≥0∞) *
        ENNReal.ofReal (L^(-((d : ℝ)-γ)*M.circuitRank)*
          (C1⁻¹*δ^(1/2 : ℝ))^M.circuitRank) := by
  simp only [countAFree,cellProduct_eq_one_of_simple M hsimple,mul_one]

end WaveTurbulence.MoleProp
