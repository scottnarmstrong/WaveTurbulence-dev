/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.FinalCount.GL21
public import WaveTurbulence.Foundations.TVine.Struct.UBase
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.FinalCount.GL20
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Api
/-! **L6-H port of main `WaveTurbulence.Foundations.FinalCount.GL21`** (sha256 in H/COPIED-SHA256SUMS): only the declarations that
depend on the vine-family carrier, re-stated over the low family `Src … Src.γL` (and L6-STEP1's
`Step1.VineCut Src.γL`); everything else is main's, by import.

 **G3-LOWDEG (R48), part 21: vines have no loops.**  The expanded vine templates `X.expand k` have no bond `(i, i)`; hence an atom of a
vine, VC (a chain of vines) or of the adjoint of a hyper-object carries no self-loop. 

Low-range addition (L6-HLOW): `isSomeVine_noLoopL`, family members have no loops (main's `isVine_noLoop` at
(I), (II); T-vines by L3's `TVine.Struct.loopless_of_isTVineU`); `chain_noLoop` uses it.-/
@[expose] public section
open WaveTurbulence.VineParamContract
set_option autoImplicit false
set_option linter.unusedSectionVars false
open Finset Classical
namespace WaveTurbulence.GammaLow.FinalCount.H
open WaveTurbulence.FinalCountG3
open WaveTurbulence WaveTurbulence.FinalCount WaveTurbulence.LGSpine.SourceVine

variable {V : Type*} [DecidableEq V] {D : Type*} [Fintype D] [DecidableEq D]

/-- Family members have no loops (low-range addition, L6-HLOW): main's `isVine_noLoop` at (I), (II); for a T-vine a loop
bond of the group (main's argument) contradicts L3's `TVine.Struct.loopless_of_isTVineU`. -/
theorem isSomeVine_noLoopL {M : Molecule V D} {S : Finset V} {a b : V} (h : Src.IsSomeVine Src.γL M S a b) :
    ∀ y : D, M.atom y ∈ S → M.atom y ≠ M.atom (M.mate y) := by
  rcases h.cases with h | h | h
  · exact isVine_noLoop h
  · exact isVine_noLoop h
  intro y hy hloop
  have h0 := TVine.Struct.loopless_of_isTVineU ((TVine.Core.isTVine_iff M).mp h).2 (M.atom y)
  rw [TVine.Core.groupGraph_mult] at h0
  obtain ⟨y', hy'o, hy'a, hy'm⟩ : ∃ y' : D, M.out y' = true ∧ M.atom y' = M.atom y ∧ M.atom (M.mate y') = M.atom y := by
    by_cases ho : M.out y = true
    · exact ⟨y, ho, rfl, hloop.symm⟩
    · refine ⟨M.mate y, ?_, hloop.symm, by rw [M.mate_mate]⟩
      have := M.out_mate y
      simp only [Bool.not_eq_true] at ho
      rw [this, ho]; rfl
  have hmem : (s(M.atom y, M.atom y) : Sym2 V) ∈ M.groupBonds S := by
    unfold Molecule.groupBonds
    refine Multiset.mem_map.2 ⟨y', ?_, ?_⟩
    · simp only [Finset.mem_val, Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨hy'o, by rw [hy'a]; exact hy, by rw [hy'm]; exact hy⟩
    · simp [Molecule.ends, hy'a, hy'm]
  exact (Multiset.count_ne_zero.mpr hmem) h0

theorem chain_noLoop {M : Molecule V D} {S : Finset V} {a b : V} {n : ℕ} (h : Src.Chain Src.γL M S a b n) :
    ∀ y : D, M.atom y ∈ S → M.atom y ≠ M.atom (M.mate y) := by
  induction h with
  | single h =>
    exact isSomeVine_noLoopL h
  | append hc hv hinter hne ih =>
    intro y hy
    rcases Finset.mem_union.1 hy with h | h
    · exact ih y h
    · exact isSomeVine_noLoopL hv y h

theorem isVC_noLoop {M : Molecule V D} {S : Finset V} {a b : V} (h : Src.IsVC Src.γL M S a b) :
    ∀ y : D, M.atom y ∈ S → M.atom y ≠ M.atom (M.mate y) := by
  obtain ⟨-, n, hn⟩ := h
  exact chain_noLoop hn

end WaveTurbulence.GammaLow.FinalCount.H
