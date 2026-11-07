/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.FinalCount.AsmMaxGap1
public import WaveTurbulence.Foundations.FinalCount.AsmTerm2d
public import WaveTurbulence.Foundations.FinalCount.AsmTerm7
/-! **FINALCOUNT-ASSEMBLY, ladder-gap clauses 2: `MaxLadderGapAdm` for the components** of a state (`hmaxU`) and of its Operation-5
molecule (`hmaxD`), from the class clause `SourceLadderGaps` and `LCtx`.  Operation 5 creates no new ladders: a ladder of
`eraseSet M E` / `restrictP` is a ladder of `M` (`LadderTransfer`), with the same dart pair. -/
@[expose] public section
open WaveTurbulence.VineParamContract
set_option autoImplicit false
set_option linter.unusedSectionVars false
open Finset Classical
namespace WaveTurbulence.FinalCountAsm
open WaveTurbulence WaveTurbulence.FinalCount WaveTurbulence.FinalCountG3 WaveTurbulence.VineCount WaveTurbulence.FinalCountG8

universe u
variable {V : Type*} [DecidableEq V] {D₀ : Type u} [Fintype D₀] [DecidableEq D₀] {d : ℕ}

theorem isLadder_restrictP_up {D : Type*} [Fintype D] [DecidableEq D] (M : Molecule V D) (P : V → Prop) [DecidablePred P]
    (h : PClosed M P) {m : ℕ} {u v : Fin (m + 1) → V} (hL : (restrictP M P h).IsLadder u v) : M.IsLadder u v :=
  ((restrictTransfer M P h).isLadder_iff (fun j => (hL.2.2.1 j).1) (fun j => (hL.2.2.1 j).2)).1 hL

theorem isLadder_comp_up {D : Type*} [Fintype D] [DecidableEq D] (M : Molecule V D) (a : V) {m : ℕ} {u v : Fin (m + 1) → V}
    (hL : (compMol M a).IsLadder u v) : M.IsLadder u v :=
  isLadder_restrictP_up M (compP M a) (compP_closed M a) hL

theorem isLadder_eraseSet_up {D : Type*} [Fintype D] [DecidableEq D] (M : Molecule V D) (E : Finset V) (hE : E ⊆ M.atoms)
    {m : ℕ} {u v : Fin (m + 1) → V} (hL : (eraseSet M E).IsLadder u v) : M.IsLadder u v := by
  refine ((eraseSetTransfer M E hE).isLadder_iff (fun j => ?_) (fun j => ?_)).1 hL
  · have := (hL.2.2.1 j).1; rw [eraseSet_atoms] at this; exact this
  · have := (hL.2.2.1 j).2; rw [eraseSet_atoms] at this; exact this

theorem isLadder_op5_up (hf : HSt V D₀) (Tm : V → Prop) {m : ℕ} {u v : Fin (m + 1) → V}
    (hL : (hf.op5 Tm).s.M.IsLadder u v) : hf.s.M.IsLadder u v := by
  rw [op5_M_eq'] at hL
  exact isLadder_eraseSet_up hf.s.M (tameSet hf Tm) (fun x hx => (tameSet_mem.1 hx).1) (isLadder_restrictP_up _ _ _ hL)

theorem maxGap_comp {M₀ : Molecule V D₀} {P : Finset V → ℝ} {L : ℝ} {A0 A : Set (D₀ → (Fin d → ℤ))} (hMol0 : M₀.IsMolecule)
    (hP : LadderHered M₀ P) (hdec : ∀ k ∈ A0, ∃ c0, M₀.IsDecoration L (0 : Mom d) c0 k ∧ ∀ x ∈ M₀.atoms, M₀.deg x = 4 → c0 x = 0)
    (hsrc : ∀ k ∈ A0, SourceLadderGaps M₀ L (0 : Mom d) P k) (hA : A ⊆ A0) {h : HSt V D₀} (hc : LCtx M₀ h.s) (a : V) :
    MaxLadderGapAdm (compMol h.s.M a) L (0 : Mom d) P (MoleProp.GapScale L) (compAdm h a (fun k => k ∈ A)) := by
  rintro κ' ⟨κ, hκ, rfl⟩ m u v hL hmax r hr
  obtain ⟨c0, hdc, hc0⟩ := hdec κ (hA hκ)
  have hL' : (compMol h.s.M a).IsLadder u v := hL
  exact gapScale_of_embed hc hP hMol0 hdc hc0 (hsrc κ (hA hκ)) (compMol h.s.M a) (fun x => x.1)
    (fun hl => isLadder_comp_up h.s.M a hl) (fun x => rfl) (fun x => rfl) hL' hr

theorem maxGap_comp_op5 {M₀ : Molecule V D₀} {P : Finset V → ℝ} {L : ℝ} {A0 A : Set (D₀ → (Fin d → ℤ))} {Tm : V → Prop}
    (hMol0 : M₀.IsMolecule) (hP : LadderHered M₀ P)
    (hdec : ∀ k ∈ A0, ∃ c0, M₀.IsDecoration L (0 : Mom d) c0 k ∧ ∀ x ∈ M₀.atoms, M₀.deg x = 4 → c0 x = 0)
    (hsrc : ∀ k ∈ A0, SourceLadderGaps M₀ L (0 : Mom d) P k) (hA : A ⊆ A0) {h : HSt V D₀} (hc : LCtx M₀ h.s) (a : V) :
    MaxLadderGapAdm (compMol (h.op5 Tm).s.M a) L (0 : Mom d) P (MoleProp.GapScale L) (compAdm (h.op5 Tm) a (fun k => k ∈ A)) := by
  rintro κ' ⟨κ, hκ, rfl⟩ m u v hL hmax r hr
  obtain ⟨c0, hdc, hc0⟩ := hdec κ (hA hκ)
  have hL' : (compMol (h.op5 Tm).s.M a).IsLadder u v := hL
  exact gapScale_of_embed hc hP hMol0 hdc hc0 (hsrc κ (hA hκ)) (compMol (h.op5 Tm).s.M a) (fun x => x.1.1.1)
    (fun hl => isLadder_op5_up h Tm (isLadder_comp_up _ a hl)) (fun x => rfl) (fun x => rfl) hL' hr

end WaveTurbulence.FinalCountAsm
