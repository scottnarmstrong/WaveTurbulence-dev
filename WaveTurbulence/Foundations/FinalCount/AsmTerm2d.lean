/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.FinalCount.AsmTerm2c
public import WaveTurbulence.Foundations.FinalCount.AsmRho1
public import WaveTurbulence.Foundations.FinalCount.G3LadErase1
/-! **FINALCOUNT-ASSEMBLY, `hterm` part 2d: the `ρ`-loss of Operation 5 is at most `|E| + iso`.** -/
@[expose] public section
set_option autoImplicit false
set_option linter.unusedSectionVars false
open Finset Classical
namespace WaveTurbulence.FinalCountAsm
open WaveTurbulence WaveTurbulence.FinalCount WaveTurbulence.FinalCountG3

variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]

theorem eraseSetTransfer (M : Molecule V D) (E : Finset V) (hE : E ⊆ M.atoms) :
    LadderTransfer M (eraseSet M E) (M.atoms \ E) where
  subM a ha := (Finset.mem_sdiff.1 ha).1
  subM' a ha := by rw [eraseSet_atoms]; exact ha
  bonds a ha b hb := eraseSet_bondsBetween M (Finset.mem_sdiff.1 ha).2 (Finset.mem_sdiff.1 hb).2
  dir a ha b hb := (eraseSet_directed_iff M (Finset.mem_sdiff.1 ha).2 (Finset.mem_sdiff.1 hb).2)
  low x hx hxA := by rw [eraseSet_atoms] at hx; exact absurd hx hxA

theorem rho_op5 (M : Molecule V D) (hM : ∀ x ∈ M.atoms, M.deg x ≤ 4) (E : Finset V) (hE : E ⊆ M.atoms) :
    M.rho ≤ (restrictP (eraseSet M E) (keepM M E) (keepM_closed M E)).rho + E.card +
      ((eraseSet M E).atoms.filter fun a => ¬ keepM M E a).card := by
  have h1 := (eraseSetTransfer M E hE).rho_le
  have h2 := ladderLoss_le_card M hM (M.atoms \ E)
  have hsd : (M.atoms \ (M.atoms \ E)).card = E.card := by
    rw [Finset.sdiff_sdiff_eq_self hE]
  have hN : ∀ x ∈ (eraseSet M E).atoms, (eraseSet M E).deg x ≤ 4 := fun x hx => by
    rw [eraseSet_atoms] at hx
    have := eraseSet_deg_card M E (Finset.mem_sdiff.1 hx).2
    have := hM x (Finset.mem_sdiff.1 hx).1
    omega
  have h3 := (restrictTransfer (eraseSet M E) (keepM M E) (keepM_closed M E)).rho_le
  have h4 := ladderLoss_le_card (eraseSet M E) hN ((eraseSet M E).atoms.filter (keepM M E))
  have hsd2 : ((eraseSet M E).atoms \ (eraseSet M E).atoms.filter (keepM M E)).card =
      ((eraseSet M E).atoms.filter fun a => ¬ keepM M E a).card := by
    congr 1; ext a; simp only [Finset.mem_sdiff, Finset.mem_filter]; tauto
  omega

end WaveTurbulence.FinalCountAsm
