/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.FinalCount.AsmTerm2b
/-! **FINALCOUNT-ASSEMBLY, `hterm` part 2c: the component count of the Operation-5 molecule.**
`2 F(M₅) = 2 F(M) - 2 J + tch(E) - 2 |E| - 2 iso`, where `J = χ(M) - χ(M - E)` and `iso` counts the dropped atoms. -/
@[expose] public section
set_option autoImplicit false
set_option linter.unusedSectionVars false
open Finset Classical
namespace WaveTurbulence.FinalCountAsm
open WaveTurbulence WaveTurbulence.FinalCount WaveTurbulence.FinalCountG3

variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]

theorem op5_numComponents (M : Molecule V D) (E : Finset V) (hE : E ⊆ M.atoms) :
    2 * ((restrictP (eraseSet M E) (keepM M E) (keepM_closed M E)).numComponents : ℤ) =
      2 * (M.numComponents : ℤ) - 2 * (M.circuitRank - (eraseSet M E).circuitRank) + (tch M E : ℤ) - 2 * (E.card : ℤ) -
        2 * (((eraseSet M E).atoms.filter fun a => ¬ keepM M E a).card : ℤ) := by
  have hno : ∀ x : EDartS M E, keepM M E ((eraseSet M E).atom x) := fun x =>
    Finset.card_pos.2 ⟨x, by simp [Molecule.dartsAt]⟩
  have : IsEmpty (PDart (eraseSet M E) (fun a => ¬ keepM M E a)) := ⟨fun x => x.2 (hno x.1)⟩
  have hF := numComponents_restrictP_add (eraseSet M E) (keepM M E) (keepM_closed M E)
  have hdl := dartless_numComponents (restrictP (eraseSet M E) (fun a => ¬ keepM M E a) (keepM_closed M E).neg)
  have hdl' : (restrictP (eraseSet M E) (fun a => ¬ keepM M E a) (keepM_closed M E).neg).atoms.card =
      ((eraseSet M E).atoms.filter fun a => ¬ keepM M E a).card := rfl
  rw [hdl, hdl'] at hF
  have hB1 := card_darts_eq_two_bonds M
  have hB2 := card_darts_eq_two_bonds (eraseSet M E)
  have hD : Fintype.card (EDartS M E) + tch M E = Fintype.card D := card_edartS M E
  have hn : (eraseSet M E).atoms.card + E.card = M.atoms.card := by
    rw [eraseSet_atoms]; exact Finset.card_sdiff_add_card_eq_card hE
  unfold Molecule.circuitRank
  have hD' : ((Fintype.card (EDartS M E) : ℕ) : ℤ) = 2 * ((eraseSet M E).bonds.card : ℤ) := by exact_mod_cast hB2
  have hD'' : ((Fintype.card D : ℕ) : ℤ) = 2 * (M.bonds.card : ℤ) := by exact_mod_cast hB1
  have hDD : ((Fintype.card (EDartS M E) : ℕ) : ℤ) + (tch M E : ℤ) = (Fintype.card D : ℤ) := by exact_mod_cast hD
  have hnn : ((eraseSet M E).atoms.card : ℤ) + (E.card : ℤ) = (M.atoms.card : ℤ) := by exact_mod_cast hn
  have hFF : ((restrictP (eraseSet M E) (keepM M E) (keepM_closed M E)).numComponents : ℤ) +
      (((eraseSet M E).atoms.filter fun a => ¬ keepM M E a).card : ℤ) = ((eraseSet M E).numComponents : ℤ) := by
    exact_mod_cast hF
  omega

end WaveTurbulence.FinalCountAsm
