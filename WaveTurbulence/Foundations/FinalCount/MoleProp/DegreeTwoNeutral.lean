/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.MoleProp.OneCircuitGain
public import WaveTurbulence.Foundations.FinalCount.MoleProp.SimpleErasure
import Mathlib.Tactic

/-! # Neutral degree-two removal for initial-profile preprocessing -/

@[expose] public section
set_option autoImplicit false
open Finset
namespace WaveTurbulence.MoleProp

theorem countAFree_erase_two_neutral (d : ℕ) (hd : 3 ≤ d) (γ : ℝ)
    (hγ : γ ∈ Set.Ioo (0 : ℝ) 1) (η : ℝ) (hη : 0 < η)
    (hηmax : η ≤ min γ (1-γ)/2) (δ : ℝ) (hδ : δ ∈ Set.Ioc (0 : ℝ) 1) :
    ∃ R : ℝ, ∀ L ≥ R, 1 ≤ Real.log L → ∀ C1 ≥ (1 : ℝ),
    ∀ {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D],
    ∀ (M : Molecule V D), M.IsMolecule →
      (∀ a b, a ≠ b → M.bondsBetween a b ≤ 1) → ∀ v ∈ M.atoms, M.deg v=2 →
      (Degen.eraseAtoms M {v}).circuitRank = M.circuitRank-1 →
    ∀ (Adm : (D → (Fin d → ℤ)) → Prop) (P : Finset V → ℝ),
      (∀ κ, Adm κ → LargeGap M L γ η (0 : Mom d) κ) →
      countAFree M L γ δ C1 (0 : Mom d) Adm P ≤
        countAFree (Degen.eraseAtoms M {v}) L γ δ C1 (0 : Mom d) (erasedFreeAdmissibility M {v} Adm) P := by
  obtain ⟨R,hR⟩ := countAFree_erase_one_circuit_gain d hd γ hγ η hη hηmax δ hδ
  refine ⟨max R 1,?_⟩
  intro L hL hlog C1 hC1 V D _ _ _ M hM hsimp v hv hv2 hχ Adm P hAdm
  have hL1 : 1 ≤ L := (le_max_right _ _).trans hL
  have hh := hR L ((le_max_left _ _).trans hL) hlog C1 hC1 M hM v hv (Or.inl hv2)
    (no_operation_b_of_simple M hsimp) hχ Adm P hAdm
    (by rw [ladderCells_eq_empty_of_simple M hsimp]; simp)
  have hs : L^(-(η-η/4)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos hL1 (by linarith only [hη])
  have he : ENNReal.ofReal (L^(-(η-η/4))) ≤ 1 := by
    simpa only [ENNReal.ofReal_one] using ENNReal.ofReal_le_ofReal hs
  exact hh.trans (by
    simpa only [one_mul] using (mul_le_mul_of_nonneg_right he
      (show 0 ≤ countAFree (Degen.eraseAtoms M {v}) L γ δ C1 (0 : Mom d) (erasedFreeAdmissibility M {v} Adm) P from bot_le)))

end WaveTurbulence.MoleProp
