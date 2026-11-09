/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.GL21
public import WaveTurbulence.Foundations.TVine.Struct.UBase
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Api

/-! # FLOWER-LOW (packet L8), item I: carrier bridges for the marked Stage 1′ over `𝒱_γ`

Small facts about L6's carrier `Src.IsSomeVine γ` (`γ ≤ 1 / 2`) that main states for its drawn vines and that the
marked chain uses:

* `isSomeVine_noLoopLow`: a member of `𝒱_γ` has no loop at its atoms — main's `FinalCountG3.isVine_noLoop` for the
  types (I), (II); for a T-vine a loop bond of the group contradicts L3's `TVine.Struct.loopless_of_isTVineU`. The
  proof follows L6-HLOW's `FinalCount.H.isSomeVine_noLoopL` (stated there at `Src.γL`; source
  `GammaLow/FinalCount/H/FinalCount/GL21.lean`, sha256 `fbb368dd…c065`), reduced to it through
  `Src.isSomeVine_low_iff` (every family `γ ≤ 1 / 2` is the enlarged family). -/

@[expose] public section
set_option autoImplicit false

open Finset Classical

namespace WaveTurbulence.GammaLow.Flower

open WaveTurbulence WaveTurbulence.FinalCountG3 WaveTurbulence.FinalCount

variable {V : Type*} [DecidableEq V] {D : Type*} [Fintype D] [DecidableEq D]

/-- **Members of `𝒱_γ` have no loops** (`γ ≤ 1 / 2`): main's `isVine_noLoop` for (I), (II); for a T-vine by L3's
`loopless_of_isTVineU`. -/
theorem isSomeVine_noLoopLow {γ : ℝ} [hγ : Fact (γ ≤ 1 / 2)] {M : Molecule V D} {S : Finset V} {a b : V}
    (h : GammaLow.FinalCount.Src.IsSomeVine γ M S a b) :
    ∀ y : D, M.atom y ∈ S → M.atom y ≠ M.atom (M.mate y) := by
  have hE : M.IsVineEnl S a b := (GammaLow.FinalCount.Src.isSomeVine_low_iff hγ.out).mp h
  rcases hE with h | h | h
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

end WaveTurbulence.GammaLow.Flower
