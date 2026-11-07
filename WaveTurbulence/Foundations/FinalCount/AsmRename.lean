/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.FinalCount.AsmPot
/-! **FINALCOUNT-ASSEMBLY: the fresh name of a cut is immaterial.**  `numComponents` of `M.cut v v₂ x₁ x₂` does not depend on the fresh
atom `v₂`, hence neither do `IsAlphaCut` and the `α`/`β` nature of a cut.  This is what lets the cover use one canonical fresh name. -/
@[expose] public section
open WaveTurbulence.VineParamContract
set_option autoImplicit false
set_option linter.unusedSectionVars false
open Finset Classical
namespace WaveTurbulence.FinalCountAsm
open WaveTurbulence WaveTurbulence.FinalCount

variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]

theorem numComponents_cut_congr (M : Molecule V D) {v v₂ v₂' : V} (x₁ x₂ : D) (h₂ : v₂ ∉ M.atoms) (h₂' : v₂' ∉ M.atoms) :
    (M.cut v v₂ x₁ x₂).numComponents = (M.cut v v₂' x₁ x₂).numComponents := by
  set σ : V ≃ V := Equiv.swap v₂ v₂' with hσ
  have hfix : ∀ a ∈ M.atoms, σ a = a := fun a ha =>
    Equiv.swap_apply_of_ne_of_ne (fun e => h₂ (e ▸ ha)) (fun e => h₂' (e ▸ ha))
  have hatom : ∀ x, (M.cut v v₂' x₁ x₂).atom x = σ ((M.cut v v₂ x₁ x₂).atom x) := by
    intro x
    simp only [Molecule.cut]
    split_ifs with hc
    · simp [hσ]
    · rw [hfix _ (M.atom_mem x)]
  have hmem : ∀ u : V, u ∈ (M.cut v v₂ x₁ x₂).atoms ↔ σ u ∈ (M.cut v v₂' x₁ x₂).atoms := by
    intro u
    simp only [Molecule.cut, Finset.mem_insert]
    by_cases hu : u ∈ M.atoms
    · rw [hfix u hu]; simp [hu]
    · by_cases e : u = v₂
      · subst e; simp [hσ]
      · by_cases e' : u = v₂'
        · subst e'; simp [hσ, hu, e]
          exact ⟨fun h => e h.symm, h₂⟩
        · rw [Equiv.swap_apply_of_ne_of_ne e e']; simp [hu, e, e']
  let e := Equiv.subtypeEquiv σ (p := fun u => u ∈ (M.cut v v₂ x₁ x₂).atoms) (q := fun u => u ∈ (M.cut v v₂' x₁ x₂).atoms) hmem
  unfold Molecule.numComponents
  refine Nat.card_congr (Quot.congr e (fun a b => ?_))
  show (M.cut v v₂ x₁ x₂).Adj a.1 b.1 ↔ (M.cut v v₂' x₁ x₂).Adj (σ a.1) (σ b.1)
  unfold Molecule.Adj
  constructor
  · rintro ⟨x, h1, h2⟩
    exact ⟨x, by rw [hatom, h1], by have := hatom (M.mate x); simp only [Molecule.cut] at this ⊢; rw [this]; simpa [Molecule.cut] using congrArg σ h2⟩
  · rintro ⟨x, h1, h2⟩
    refine ⟨x, σ.injective ?_, σ.injective ?_⟩
    · rw [← hatom]; exact h1
    · have := hatom (M.mate x); simp only [Molecule.cut] at this h2 ⊢; rw [← this]; exact h2

theorem isAlphaCut_congr (M : Molecule V D) {v v₂ v₂' : V} (x₁ x₂ : D) (h₂ : v₂ ∉ M.atoms) (h₂' : v₂' ∉ M.atoms) :
    M.IsAlphaCut v v₂ x₁ x₂ ↔ M.IsAlphaCut v v₂' x₁ x₂ := by
  unfold Molecule.IsAlphaCut
  rw [numComponents_cut_congr M x₁ x₂ h₂ h₂']

end WaveTurbulence.FinalCountAsm
