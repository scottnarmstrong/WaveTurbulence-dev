/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.MoleProp.InducedAdmissibility
import Mathlib.Tactic

/-! # Neutral selection of an actual union of connected components -/

@[expose] public section
set_option autoImplicit false
open Finset
namespace WaveTurbulence.MoleProp

theorem countAFree_le_induced_closed (d : ℕ) (hd : 3 ≤ d) (γ : ℝ)
    (hγ : γ ∈ Set.Ioo (0 : ℝ) 1) (η : ℝ) (hη : 0 < η)
    (hηmax : η ≤ min γ (1-γ)/2) :
    ∃ Cstar : ℝ, 1 ≤ Cstar ∧ ∀ C1 ≥ Cstar, ∀ δ ∈ Set.Ioc (0 : ℝ) 1,
    ∃ R : ℝ, ∀ L ≥ R, 1 ≤ Real.log L →
    ∀ {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D],
    ∀ (M : Molecule V D), M.IsMolecule →
      (∀ a b, a ≠ b → M.bondsBetween a b ≤ 1) →
    ∀ S : Finset V, S ⊆ M.atoms →
      (∀ a ∈ S, ∀ b, M.SameComponent a b → b ∈ S) →
    ∀ (Adm : (D → (Fin d → ℤ)) → Prop) (P : Finset V → ℝ),
      (∀ κ, Adm κ → LargeGap M L γ η (0 : Mom d) κ) →
      countAFree M L γ δ C1 (0 : Mom d) Adm P ≤
        countAFree (Mole.induced M S) L γ δ C1 (0 : Mom d)
          (inducedFreeAdmissibility M S Adm) P := by
  obtain ⟨C,hC,hB⟩ := countAFree_le_discard_components d hd γ hγ η hη hηmax
  refine ⟨C,hC,?_⟩
  intro C1 hC1 δ hδ
  obtain ⟨R,hR⟩ := hB C1 hC1 δ hδ
  refine ⟨R,?_⟩
  intro L hL hlog V D _ _ _ M hM hsimp S hS hclose Adm P hAdm
  exact (hR L hL hlog M hM hsimp S hS hclose Adm P hAdm).trans
    (countAFree_erase_complement_le_induced M S hS L γ δ C1 (0 : Mom d) Adm P)

end WaveTurbulence.MoleProp
