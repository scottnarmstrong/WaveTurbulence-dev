/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.FinalCount.AsmVN14
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.FinalCount.AsmP1Rho
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.FinalCount.AsmVN13
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.FinalCount.VrHyper3
public import WaveTurbulence.Foundations.GammaLow.FinalCount.Step1.Gamma
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Api
/-! **L6-H port of main `WaveTurbulence.Foundations.FinalCount.AsmVN14`** (sha256 in H/COPIED-SHA256SUMS): only the declarations that
depend on the vine-family carrier, re-stated over the low family `Src … Src.γL` (and L6-STEP1's
`Step1.VineCut Src.γL`); everything else is main's, by import.

 **FINALCOUNT-ASSEMBLY (VineNodeExists, part 14): the `ρ`-loss `hrho` of `VHard`.**
`hrho_of_cls`: for a vine cut `K` of a molecule `M` (a molecule) which is a single vine (ordinary, or the adjoint of the designated bond) or a
double shape (three atoms): `M.rho ≤ K.post.rho + 86` (VINE-RHO `vine_ladderLoss_le`, `hv_ladderLoss_le`: loss `≤ 42`; three atoms: `≤ 3`). -/
@[expose] public section
open WaveTurbulence.Induct
open WaveTurbulence.VineParamContract
set_option autoImplicit false
set_option linter.unusedSectionVars false
open Finset Classical
namespace WaveTurbulence.GammaLow.FinalCount.H
open WaveTurbulence.FinalCountAsm
open WaveTurbulence WaveTurbulence.FinalCount WaveTurbulence.FinalCountG3 WaveTurbulence.LGSpine WaveTurbulence.LGSpine.SourceVine WaveTurbulence.VineCount

variable {V : Type*} [DecidableEq V] {D : Type*} [Fintype D] [DecidableEq D]

theorem hrho_of_cls {M : Molecule V D} (hMol : M.IsMolecule) (K : Step1.VineCut Src.γL M) (hK : Step1.SingleVineVCGamma K ∨ Nonempty (Step1.DoubleShape K)) :
    M.rho ≤ K.post.rho + 86 := by
  have hdeg : ∀ x ∈ M.atoms, M.deg x ≤ 4 := fun x hx => Mole.deg_le_four M hMol hx
  rcases hK with h | hS
  · unfold Step1.SingleVineVCGamma at h
    split at h
    · have hX := h
      have := rho_vine_isVine K hMol hX
      omega
    · rename_i R hsh
      have hX := h
      have hHV : Src.IsHV Src.γL M K.C.atoms K.C.upper K.C.lower := ⟨R.added, R.ends_eq, hX⟩
      have h2 := hv_ladderLoss_le M hMol hHV
      have h1 := rho_vine_le K hdeg
      rw [sdiff_eq_filter_atoms] at h2
      omega
  · obtain ⟨S⟩ := hS
    have := rho_vine_card K hdeg (n := 3) (by rw [S.atoms_eq]; exact Finset.card_le_three)
    omega

end WaveTurbulence.GammaLow.FinalCount.H
