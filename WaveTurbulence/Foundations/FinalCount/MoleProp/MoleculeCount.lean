/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.MoleProp.PropositionOne
public import WaveTurbulence.Foundations.FinalCount.Degen.SourceLadderIntervals
import Mathlib.Tactic

/-! # DH23 Proposition 10.1

This endpoint uses the literal arbitrary-charge source count and one scale
for each ladder position. The source requires only sufficiently large L;
the explicit logarithmic side condition of the deletion lemmas is absorbed
into that threshold. Disconnected molecules are allowed as a strengthening.
-/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.MoleProp

theorem molecule_count_bound (d : ℕ) (hd : 3 ≤ d) (γ : ℝ)
    (hγ : γ ∈ Set.Ioo (0 : ℝ) 1) (η : ℝ) (hη : 0 < η)
    (hηmax : η ≤ min γ (1-γ)/2) :
    ∃ Cstar : ℝ, 1 ≤ Cstar ∧ ∀ C1 ≥ Cstar, ∀ δ ∈ Set.Ioc (0 : ℝ) 1,
    ∃ R : ℝ, ∀ L ≥ R,
    ∀ {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D],
    ∀ (M : Molecule V D), M.IsMolecule →
    ∀ (Adm : (D → (Fin d → ℤ)) → Prop) (P : Finset V → ℝ),
      (∀ κ, Adm κ → LargeGap M L γ η (0 : Mom d) κ) →
      (∀ κ, Adm κ → CellGapRestriction M L (0 : Mom d) P (GapScale L) κ) →
      (∀ S ∈ ladderCells M, 0 ≤ P S) →
      countAFree M L γ δ C1 (0 : Mom d) Adm P ≤ 1 := by
  obtain ⟨C,hC,hB⟩ := proposition_one_normalized_bound d hd γ hγ η hη hηmax
  refine ⟨C,hC,?_⟩
  intro C1 hC1 δ hδ
  obtain ⟨R,hR⟩ := hB C1 hC1 δ hδ
  refine ⟨max R (Real.exp 1),?_⟩
  intro L hL
  have hLR : R ≤ L := (le_max_left _ _).trans hL
  have hexp : Real.exp 1 ≤ L := (le_max_right _ _).trans hL
  have hLp : 0 < L := (Real.exp_pos 1).trans_le hexp
  intro V D _ _ _ M hM Adm P hLG hGap hP
  exact hR L hLR ((Real.le_log_iff_exp_le hLp).mpr hexp) M hM Adm P hLG hGap hP

end WaveTurbulence.MoleProp
