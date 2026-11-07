/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.MoleProp.MoleculeCount
public import WaveTurbulence.Foundations.FinalCount.MoleProp.SimpleNormalization
import Mathlib.Tactic

/-! # The source baseline bound for every simple residual molecule -/

@[expose] public section
set_option autoImplicit false
open Finset
open WaveTurbulence.Degen
namespace WaveTurbulence.MoleProp
variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]

theorem not_sourceLadder_of_simple (M : Molecule V D)
    (hsimple : ∀ a b, a ≠ b → M.bondsBetween a b ≤ 1)
    {m : ℕ} (u v : Fin (m+1) → V) : ¬ SourceLadder M u v := by
  intro hL
  have hne : u 0 ≠ v 0 := by
    intro he
    have hh : (Sum.inl (0 : Fin (m+1)) : Fin (m+1) ⊕ Fin (m+1)) = Sum.inr 0 := hL.2.1 he
    cases hh
  have hh := hsimple (u 0) (v 0) hne
  rw [hL.2.2.2.1 0] at hh
  omega

theorem cellGapRestriction_of_simple (M : Molecule V D)
    (hsimple : ∀ a b, a ≠ b → M.bondsBetween a b ≤ 1)
    {d : ℕ} (L : ℝ) (w : Mom d) (P : Finset V → ℝ) (R : ℝ → ℝ → Prop)
    (κ : D → (Fin d → ℤ)) : CellGapRestriction M L w P R κ := by
  intro u v hL _r _hr
  exact False.elim (not_sourceLadder_of_simple M hsimple u v hL)

/-- DH23 Proposition10.1 on any simple residual graph, with no vacuous
ladder-scale conditions left for its callers to supply. -/
theorem simple_molecule_count_bound (d : ℕ) (hd : 3 ≤ d) (γ : ℝ)
    (hγ : γ ∈ Set.Ioo (0 : ℝ) 1) (η : ℝ) (hη : 0 < η)
    (hηmax : η ≤ min γ (1-γ)/2) :
    ∃ Cstar : ℝ, 1 ≤ Cstar ∧ ∀ C1 ≥ Cstar, ∀ δ ∈ Set.Ioc (0 : ℝ) 1,
    ∃ R : ℝ, ∀ L ≥ R,
    ∀ {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D],
    ∀ (M : Molecule V D), M.IsMolecule →
      (∀ a b, a ≠ b → M.bondsBetween a b ≤ 1) →
    ∀ (Adm : (D → (Fin d → ℤ)) → Prop) (P : Finset V → ℝ),
      (∀ κ, Adm κ → LargeGap M L γ η (0 : Mom d) κ) →
      countAFree M L γ δ C1 (0 : Mom d) Adm P ≤ 1 := by
  obtain ⟨C,hC,hB⟩ := molecule_count_bound d hd γ hγ η hη hηmax
  refine ⟨C,hC,?_⟩
  intro C1 hC1 δ hδ
  obtain ⟨R,hR⟩ := hB C1 hC1 δ hδ
  refine ⟨R,?_⟩
  intro L hL V D _ _ _ M hM hsimp Adm P hAdm
  apply hR L hL M hM Adm P hAdm
  · intro κ _hκ
    exact cellGapRestriction_of_simple M hsimp L (0 : Mom d) P (GapScale L) κ
  · rw [ladderCells_eq_empty_of_simple M hsimp]
    simp

end WaveTurbulence.MoleProp
