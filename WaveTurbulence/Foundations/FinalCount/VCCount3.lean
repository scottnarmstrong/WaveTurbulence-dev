/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.FinalCount.VCFinal
public import WaveTurbulenceVineParam.Contract
/-! # VINE-COUNT part 21: **the single-vine label count `𝔉`** (DH23 L1799--L1801), from `VINEPARAM`. -/
@[expose] public section
open WaveTurbulence.VineParamContract
set_option autoImplicit false
set_option linter.unusedSectionVars false
open Finset Classical
open Set (Ioo Ioc Icc)
open scoped ENNReal
namespace WaveTurbulence.VineCount
open WaveTurbulence WaveTurbulence.LGSpine.SourceVine WaveTurbulence.FinalCount WaveTurbulence.CountLemmas

variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D] {d : ℕ}

section Aux
variable {M : Molecule V D} (K : VineCut M) {X : VineType} (A : FullVineChart M X K.C.atoms K.C.upper K.C.lower)

theorem card_atoms_eq : K.C.atoms.card = A.indexing.shape.n + 1 := by
  have h1 : Fintype.card (Fin A.indexing.shape.n) = Fintype.card ↥(K.C.atoms.erase K.C.upper) :=
    Fintype.card_congr A.indexing.atom
  simp only [Fintype.card_fin, Fintype.card_coe] at h1
  rw [Finset.card_erase_of_mem K.a_mem] at h1
  have : 0 < K.C.atoms.card := Finset.card_pos.mpr ⟨_, K.a_mem⟩
  omega

theorem shape_n_bad (hbad : X.IsBad = true) : A.indexing.shape.n = 2 * A.indexing.shape.m + 1 := by
  simp [Shape.n, hbad]

theorem shape_n_normal (hn : X.IsBad = false) : A.indexing.shape.n = 2 * A.indexing.shape.m + 4 := by
  simp [Shape.n, hn]

end Aux

theorem labelSet_nonempty_or {M : Molecule V D} (K : VineCut M) {L γ δ : ℝ} {w : Mom d}
    {Adm : (D → (Fin d → ℤ)) → Prop} {c : V → Mom d} {β : V → ℝ} {k0 : D → Mom d} (b : ℝ) (hb : 0 ≤ b)
    (h : (K.labelSet L γ δ w Adm c β k0).Nonempty → (K.labelSet L γ δ w Adm c β k0).encard ≤ ENNReal.ofReal b) :
    (K.labelSet L γ δ w Adm c β k0).encard ≤ ENNReal.ofReal b := by
  by_cases hne : (K.labelSet L γ δ w Adm c β k0).Nonempty
  · exact h hne
  · rw [Set.not_nonempty_iff_eq_empty.mp hne]; simp

theorem encard_le_ofReal_of_ncard {α : Type*} {s : Set α} (hs : s.Finite) {b : ℝ} (h : (s.ncard : ℝ) ≤ b) :
    s.encard ≤ ENNReal.ofReal b := by
  rw [← hs.cast_ncard_eq]
  have : ((s.ncard : ℕ∞) : ℝ≥0∞) = ENNReal.ofReal (s.ncard : ℝ) := by
    rw [ENNReal.ofReal_natCast]; rfl
  rw [this]
  exact ENNReal.ofReal_le_ofReal h

end WaveTurbulence.VineCount
