/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.FinalCount.GV10
public import WaveTurbulence.Foundations.FinalCount.G3VineLG7
public import WaveTurbulence.Foundations.FinalCount.GM08
/-! **G3-LOWDEG port of `G3VineLG7`** (only the declarations that change: `SubHypL->SubHypL`, `HRunL->HRunL`, `InvL->InvL`, `FinalStructM->FinalStructM`, `Prop95ConclAtL->Prop95ConclAtL`; names get suffix `L`). -/
@[expose] public section
open WaveTurbulence.VineParamContract

set_option autoImplicit false
set_option linter.unusedSectionVars false
open Finset Classical
namespace WaveTurbulence.FinalCountG3
open WaveTurbulence WaveTurbulence.FinalCount
open WaveTurbulence.LGSpine.SourceVine

universe u
variable {V : Type*} [DecidableEq V] {D₀ : Type u} [Fintype D₀] [DecidableEq D₀] {d : ℕ}
variable {L γ η : ℝ} {w : Mom d} {κ : D₀ → (Fin d → ℤ)} {R : ℕ} {Tm : V → Prop}
variable {M₀ : Molecule V D₀} {hf : HSt V D₀} {a₀ j₁ j₂ : V}

/-! ### The double bond and the gap of a joint -/

theorem vine_of_vineOrDoubleL (hC : Prop95ConclAtL L γ η w κ R hf Tm) {a₀ : V} (ha₀ : a₀ ∈ hf.s.M.atoms) (hE : LowFree hf a₀)
    (h : (∃ X j₁ j₂, (compMol hf.s.M a₀).IsVine X (compMol hf.s.M a₀).atoms j₁ j₂) ∨
      ((compMol hf.s.M a₀).atoms.card = 2 ∧ ∀ a ∈ (compMol hf.s.M a₀).atoms, (compMol hf.s.M a₀).deg a = 2)) :
    ∃ X j₁ j₂, (compMol hf.s.M a₀).IsVine X (compMol hf.s.M a₀).atoms j₁ j₂ := by
  rcases h with h | ⟨hcard, hdeg⟩
  · exact h
  · obtain ⟨j₁, j₂, hne, hat⟩ := Finset.card_eq_two.1 hcard
    have hbal : ∀ j ∈ (compMol hf.s.M a₀).atoms, hf.s.M.outdeg j = 1 ∧ hf.s.M.indeg j = 1 := by
      intro j hj
      have hj' := (mem_compMol _ _).1 hj
      have hd := hdeg j hj
      rw [compMol_deg _ _ hj'.2] at hd
      exact hC.bal.2 j hj'.1 (fun hc => by have := hE j (Finset.mem_filter.2 hj') hc; omega) hd
    refine ⟨.I, j₁, j₂, isVine_I _ hne hat ?_ ?_ ?_ ?_ ?_⟩
    all_goals first
      | (intro x; exact hC.noloop x.1)
      | skip
    all_goals
      have hm : ∀ j, j ∈ (compMol hf.s.M a₀).atoms → j ∈ hf.s.M.atoms ∧ hf.s.M.SameComponent a₀ j := fun j hj =>
        (mem_compMol _ _).1 hj
    · have hj := hm j₁ (by rw [hat]; simp)
      have := hbal j₁ (by rw [hat]; simp)
      rw [compMol_outdeg _ _ hj.2]; exact this.1
    · have hj := hm j₁ (by rw [hat]; simp)
      have := hbal j₁ (by rw [hat]; simp)
      rw [compMol_indeg _ _ hj.2]; exact this.2
    · have hj := hm j₂ (by rw [hat]; simp)
      have := hbal j₂ (by rw [hat]; simp)
      rw [compMol_outdeg _ _ hj.2]; exact this.1
    · have hj := hm j₂ (by rw [hat]; simp)
      have := hbal j₂ (by rw [hat]; simp)
      rw [compMol_indeg _ _ hj.2]; exact this.2

end WaveTurbulence.FinalCountG3

