/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.FinalCount.G3VineLG6
public import WaveTurbulence.Foundations.FinalCount.G3MapDec5
/-! **FINALCOUNT-G3: `vineLG`, part 7: `HRunC` and `VineLGAt` from the run.**

`HRunC` is the run of the model with the two extra model facts of TARGET Operation 1 and requirement (e):
* **Step 1 removes the collected objects** (L2101: "In Operation 1, we collect all the SG vine-like objects in `C₁` and `C₂` ... we
  remove `U'`"): after the Step-1 phase no dart of any member of `C₁ ∪ C₂` (`Object.ContainsDart`) is a dart of the state;
* **hinges are cut along their designated bonds** (`DesRec`, `subpro` (5), requirement (e)). -/
@[expose] public section
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

theorem vine_of_vineOrDouble (hC : Prop95ConclAt L γ η w κ R hf Tm) {a₀ : V} (ha₀ : a₀ ∈ hf.s.M.atoms)
    (h : (∃ X j₁ j₂, (compMol hf.s.M a₀).IsVine X (compMol hf.s.M a₀).atoms j₁ j₂) ∨
      ((compMol hf.s.M a₀).atoms.card = 2 ∧ ∀ a ∈ (compMol hf.s.M a₀).atoms, (compMol hf.s.M a₀).deg a = 2)) :
    ∃ X j₁ j₂, (compMol hf.s.M a₀).IsVine X (compMol hf.s.M a₀).atoms j₁ j₂ := by
  rcases h with h | ⟨hcard, hdeg⟩
  · exact h
  · obtain ⟨j₁, j₂, hne, hat⟩ := Finset.card_eq_two.1 hcard
    refine ⟨.I, j₁, j₂, isVine_I _ hne hat ?_ ?_ ?_ ?_ ?_⟩
    all_goals first
      | (intro x; exact hC.noloop x.1)
      | skip
    all_goals
      have hm : ∀ j, j ∈ (compMol hf.s.M a₀).atoms → j ∈ hf.s.M.atoms ∧ hf.s.M.SameComponent a₀ j := fun j hj =>
        (mem_compMol _ _).1 hj
    · have hj := hm j₁ (by rw [hat]; simp)
      have := hC.bal.2 j₁ hj.1 (by rw [← compMol_deg _ _ hj.2]; exact hdeg j₁ (by rw [hat]; simp))
      rw [compMol_outdeg _ _ hj.2]; exact this.1
    · have hj := hm j₁ (by rw [hat]; simp)
      have := hC.bal.2 j₁ hj.1 (by rw [← compMol_deg _ _ hj.2]; exact hdeg j₁ (by rw [hat]; simp))
      rw [compMol_indeg _ _ hj.2]; exact this.2
    · have hj := hm j₂ (by rw [hat]; simp)
      have := hC.bal.2 j₂ hj.1 (by rw [← compMol_deg _ _ hj.2]; exact hdeg j₂ (by rw [hat]; simp))
      rw [compMol_outdeg _ _ hj.2]; exact this.1
    · have hj := hm j₂ (by rw [hat]; simp)
      have := hC.bal.2 j₂ hj.1 (by rw [← compMol_deg _ _ hj.2]; exact hdeg j₂ (by rw [hat]; simp))
      rw [compMol_indeg _ _ hj.2]; exact this.2

end WaveTurbulence.FinalCountG3
