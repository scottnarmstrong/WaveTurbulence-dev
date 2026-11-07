/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.VineEst.VineEstS5C.P4.W2.RecEng

/-! # P4-W2 (session 17): replacing finitely many rows of a family of rows

`exists_row_merge`: given a family of rows `Rw` and rows `Rk k` at distinct indices `idx k` (`k ∈ S`), there is a family `Rw'` equal to `Rw` off the indices and to `Rk k` at `idx k`. -/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.VineEstS5C.P4.W2
open WaveTurbulence WaveTurbulence.VineEstS3Par.Eng WaveTurbulence.VineEstS3.FS WaveTurbulence.VineEstS5A WaveTurbulence.VineEstS4c
  WaveTurbulence.DegenVine WaveTurbulence.DegenVinePar WaveTurbulence.VineEstS5C.P2 WaveTurbulence.VineEstS5C.P4 MeasureTheory

open Classical in
theorem exists_row_merge {d : ℕ} {D : SumintPar.SumintDatum d} {θ : ℝ} (Rw : ∀ ρ : Row D, RowData D θ ρ)
    {ι : Type*} (S : Finset ι) (idx : ι → Row D) (hinj : ∀ k ∈ S, ∀ k' ∈ S, idx k = idx k' → k = k')
    (Rk : ∀ k ∈ S, RowData D θ (idx k)) :
    ∃ Rw' : ∀ ρ : Row D, RowData D θ ρ, (∀ ρ, (∀ k ∈ S, idx k ≠ ρ) → Rw' ρ = Rw ρ) ∧
      (∀ k (hk : k ∈ S), Rw' (idx k) = Rk k hk) := by
  let F : ∀ ρ : Row D, RowData D θ ρ := fun ρ =>
    if h : ∃ k, k ∈ S ∧ idx k = ρ then (h.choose_spec.2 ▸ Rk h.choose h.choose_spec.1) else Rw ρ
  refine ⟨F, fun ρ hρ => ?_, fun k hk => ?_⟩
  · have h : ¬ ∃ k, k ∈ S ∧ idx k = ρ := fun ⟨k, hk, hkρ⟩ => hρ k hk hkρ
    simp only [F, dif_neg h]
  · have h : ∃ k', k' ∈ S ∧ idx k' = idx k := ⟨k, hk, rfl⟩
    simp only [F, dif_pos h]
    have key : ∀ (k' : ι) (hk' : k' ∈ S) (e : idx k' = idx k), (e ▸ Rk k' hk') = Rk k hk := by
      intro k' hk' e
      have : k' = k := hinj _ hk' k hk e
      subst this
      rfl
    exact key _ h.choose_spec.1 h.choose_spec.2
end WaveTurbulence.VineEstS5C.P4.W2
