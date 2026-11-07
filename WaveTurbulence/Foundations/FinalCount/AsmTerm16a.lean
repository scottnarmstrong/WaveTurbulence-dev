/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.FinalCount.AsmTerm15d
public import WaveTurbulence.Foundations.FinalCount.AsmFamU
public import WaveTurbulence.Foundations.FinalCount.AsmPotW
/-! **FINALCOUNT-ASSEMBLY, `hterm` part 16a: `ρ ≥ 1` at a good state with `R ≥ 1`, and the final potential comparison.** -/
@[expose] public section
open WaveTurbulence.VineParamContract
set_option autoImplicit false
set_option linter.unusedSectionVars false
open Finset Classical
open scoped ENNReal
namespace WaveTurbulence.FinalCountAsm
open WaveTurbulence WaveTurbulence.FinalCount WaveTurbulence.FinalCountG3

universe u
variable {V : Type*} [DecidableEq V] {D₀ : Type u} [Fintype D₀] [DecidableEq D₀] {d : ℕ}

/-- A molecule with an atom has `ρ ≥ 1` (every atom is free or in a maximal ladder). -/
theorem one_le_rho_of_atom {D : Type*} [Fintype D] [DecidableEq D] (M : Molecule V D) {v : V} (hv : v ∈ M.atoms) :
    1 ≤ M.rho := by
  unfold Molecule.rho Molecule.numFree Molecule.numLadders
  by_cases h : ∀ S ∈ M.maximalLadders, v ∉ S
  · have : 0 < (M.atoms.filter fun v => ∀ S ∈ M.maximalLadders, v ∉ S).card :=
      Finset.card_pos.2 ⟨v, Finset.mem_filter.2 ⟨hv, h⟩⟩
    omega
  · push_neg at h
    obtain ⟨S, hS, -⟩ := h
    have : 0 < M.maximalLadders.card := Finset.card_pos.2 ⟨S, hS⟩
    omega

/-- A good state with `R ≥ 1` has an atom. -/
theorem exists_atom_of_good {R : ℕ} (hR : 1 ≤ R) {s : St.{u} V D₀} (hg : Good R s) : ∃ v, v ∈ s.M.atoms := by
  by_contra hne
  push_neg at hne
  have hD : Fintype.card s.D = 0 := by
    rw [Fintype.card_eq_zero_iff]
    exact ⟨fun x => hne _ (s.M.atom_mem x)⟩
  have h := hg.1.phi
  have hs : s.M.atoms = ∅ := Finset.eq_empty_of_forall_notMem hne
  rw [hs, Finset.sum_empty, hD] at h
  omega

theorem one_le_rho_of_good {R : ℕ} (hR : 1 ≤ R) {s : St.{u} V D₀} (hg : Good R s) : 1 ≤ s.M.rho := by
  obtain ⟨v, hv⟩ := exists_atom_of_good hR hg
  exact one_le_rho_of_atom s.M hv

end WaveTurbulence.FinalCountAsm
