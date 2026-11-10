/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.FinalCount.VCStmt
public import WaveTurbulence.Foundations.FinalCount.VCHyper4
public import WaveTurbulence.Foundations.FinalCount.VCSource
/-! # VINE-COUNT part 30: Prop 9.4 Step 1 for a single vine given by an ordinary VC or by a hyper object, with the
ladder scales taken from the molecule-level restriction of `Adm` (`SourceLadderGaps`, at decorations). -/
@[expose] public section
open WaveTurbulence.VineParamContract
set_option autoImplicit false
set_option linter.unusedSectionVars false
open Finset Classical
open Set (Ioo Ioc Icc)
open scoped ENNReal
namespace WaveTurbulence.VineCount
open WaveTurbulence WaveTurbulence.LGSpine.SourceVine WaveTurbulence.FinalCount WaveTurbulence.CountLemmas

variable {d : ℕ}

section Facts
variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D] {M : Molecule V D}

/-- The numerical facts about the label `R` of the new `α`-atoms and the gap ball, as in `prop94_vine_final`. -/
theorem rho_facts {L γ η R ρ : ℝ} {κ : ℕ} (hL1 : 1 ≤ L) (hRl : L⁻¹ ≤ R) (hRu : R ≤ L ^ (-γ + η)) (hη : 0 < η)
    (hηγ : η ≤ γ) (hρ : (κ = 0 ∧ ρ = 2 * R) ∨ (κ = 50 ∧ ρ = L ^ (-50 * η) * R ∧ L⁻¹ ≤ ρ)) :
    0 < R ∧ 0 ≤ ρ ∧ ρ ≤ 2 ∧ 1 ≤ ρ * L := by
  have hL0 : 0 < L := by linarith
  have hR0 : 0 < R := lt_of_lt_of_le (inv_pos.mpr hL0) hRl
  have hR1 : R ≤ 1 := hRu.trans (Real.rpow_le_one_of_one_le_of_nonpos hL1 (by linarith))
  refine ⟨hR0, ?_, ?_, ?_⟩
  · rcases hρ with ⟨-, rfl⟩ | ⟨-, rfl, -⟩
    · linarith
    · exact mul_nonneg (Real.rpow_nonneg hL0.le _) hR0.le
  · rcases hρ with ⟨-, rfl⟩ | ⟨-, rfl, -⟩
    · linarith
    · have : L ^ (-50 * η) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hL1 (by linarith)
      nlinarith [Real.rpow_nonneg hL0.le (-50 * η)]
  · rcases hρ with ⟨-, rfl⟩ | ⟨-, -, h⟩
    · have : 1 ≤ R * L := by
        have := mul_le_mul_of_nonneg_right hRl hL0.le
        rwa [inv_mul_cancel₀ hL0.ne'] at this
      nlinarith
    · have := mul_le_mul_of_nonneg_right h hL0.le
      rwa [inv_mul_cancel₀ hL0.ne'] at this

/-- Bond count and size of a single vine: `2(|S|-1)` bonds, at least two atoms. -/
theorem vine_bonds_of_vine (hvp : VINEPARAM) {V D : Type} [DecidableEq V] [Fintype D] [DecidableEq D]
    {M : Molecule V D} (hMol : M.IsMolecule) (K : VineCut M) {X : VineType}
    (hX : M.IsVine X K.C.atoms K.C.upper K.C.lower) :
    K.vc.bonds.card = 2 * (K.C.atoms.card - 1) ∧ 2 ≤ K.C.atoms.card := by
  obtain ⟨A⟩ := hvp V D M hMol X _ _ _ hX
  have hcard := card_atoms_eq K A
  have hn1 : 1 ≤ A.indexing.shape.n := by unfold Shape.n; omega
  refine ⟨?_, by omega⟩
  rw [vc_bonds_card K hX.1, A.bond_count]; omega

end Facts


end WaveTurbulence.VineCount
