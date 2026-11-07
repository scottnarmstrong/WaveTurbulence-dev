/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.FinalCount.AsmVN13
public import WaveTurbulence.Foundations.FinalCount.AsmP1Rho
public import WaveTurbulence.Foundations.FinalCount.VrHyper3
/-! **FINALCOUNT-ASSEMBLY (VineNodeExists, part 14): the `ρ`-loss `hrho` of `VHard`.**
`hrho_of_cls`: for a vine cut `K` of a molecule `M` (a molecule) which is a single vine (ordinary, or the adjoint of the designated bond) or a
double shape (three atoms): `M.rho ≤ K.post.rho + 86` (VINE-RHO `vine_ladderLoss_le`, `hv_ladderLoss_le`: loss `≤ 42`; three atoms: `≤ 3`). -/
@[expose] public section
open WaveTurbulence.Induct
open WaveTurbulence.VineParamContract
set_option autoImplicit false
set_option linter.unusedSectionVars false
open Finset Classical
namespace WaveTurbulence.FinalCountAsm
open WaveTurbulence WaveTurbulence.FinalCount WaveTurbulence.FinalCountG3 WaveTurbulence.LGSpine WaveTurbulence.LGSpine.SourceVine WaveTurbulence.VineCount

variable {V : Type*} [DecidableEq V] {D : Type*} [Fintype D] [DecidableEq D]

theorem hrho_of_cls {M : Molecule V D} (hMol : M.IsMolecule) (K : VineCut M) (hK : SingleVineVC K ∨ Nonempty (DoubleShape K)) :
    M.rho ≤ K.post.rho + 86 := by
  have hdeg : ∀ x ∈ M.atoms, M.deg x ≤ 4 := fun x hx => Mole.deg_le_four M hMol hx
  rcases hK with h | hS
  · unfold SingleVineVC at h
    split at h
    · obtain ⟨X, hX⟩ := h
      have := rho_vine_isVine K hMol hX
      omega
    · rename_i R hsh
      obtain ⟨X, hX⟩ := h
      have hHV : IsHV M K.C.atoms K.C.upper K.C.lower := ⟨R.added, R.ends_eq, X, hX⟩
      have h2 := WaveTurbulence.VineRho.hv_ladderLoss_le M hMol hHV
      have h1 := rho_vine_le K hdeg
      rw [sdiff_eq_filter_atoms] at h2
      omega
  · obtain ⟨S⟩ := hS
    have := rho_vine_card K hdeg (n := 3) (by rw [S.atoms_eq]; exact Finset.card_le_three)
    omega

end WaveTurbulence.FinalCountAsm
