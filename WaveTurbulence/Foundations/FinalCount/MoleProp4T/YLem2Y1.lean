/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.MoleProp4T.YLem2
public import WaveTurbulence.Foundations.FinalCount.MoleProp4T.OneExitBound
import Mathlib.Tactic

/-! # DH23 `ylem2` for a (Y) sequence ending in (Y1), case 2 (L1952)

The last pair has exactly one extra bond (DH23 "at most one extra bond", case 2). The chain is attached by that bond
only, and `𝔄(𝕄) ≤ 𝔄(𝕄′)` with `𝕄′ = 𝕄 ∖ chain` (no loss, same LG parameter).
-/

@[expose] public section
set_option autoImplicit false
open Finset
open scoped ENNReal
namespace WaveTurbulence.MoleProp4
variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]

/-- **The (Y1), case 2 ending**: one extra bond `x` at the last pair, none at its partner. -/
structure Y1End2 {M : Molecule V D} (C : YChain M) where
  x : D
  hx : M.atom x = C.a C.n ∨ M.atom x = C.b C.n
  hxo : M.atom (M.mate x) ∉ C.set
  hdeg : M.deg (C.a C.n) + M.deg (C.b C.n) = 7

namespace Y1End2
variable {M : Molecule V D} {C : YChain M} (E : Y1End2 C)

theorem cross_eq : crossDarts M C.set = {E.x} := by
  classical
  ext z
  simp only [mem_singleton]
  constructor
  · intro hz
    obtain ⟨_, h2⟩ := mem_crossDarts.mp hz
    have ha := C.card_away_last_a
    have hb := C.card_away_last_b
    have hd7 := E.hdeg
    have hxa : ∀ w, M.atom w = C.a C.n → M.atom (M.mate w) ∉ C.set →
        w ∈ (M.dartsAt (C.a C.n)).filter fun z => M.atom (M.mate z) ∉ C.nbA C.n := fun w h1 h2 =>
      mem_filter.mpr ⟨mem_filter.mpr ⟨mem_univ _, h1⟩, fun h => h2 (C.nbA_sub le_rfl h)⟩
    have hxb : ∀ w, M.atom w = C.b C.n → M.atom (M.mate w) ∉ C.set →
        w ∈ (M.dartsAt (C.b C.n)).filter fun z => M.atom (M.mate z) ∉ C.nbB C.n := fun w h1 h2 =>
      mem_filter.mpr ⟨mem_filter.mpr ⟨mem_univ _, h1⟩, fun h => h2 (C.nbB_sub le_rfl h)⟩
    rcases E.hx with hxa' | hxb' <;> rcases C.cross_at_last hz with hza | hzb
    · have hpos := card_pos.mpr ⟨_, hxa E.x hxa' E.hxo⟩
      have hposb := (card_pos.mpr ⟨_, hxa z hza h2⟩)
      have h4 : M.deg (C.a C.n) = 4 := by have := C.card_away_last_b; omega
      exact C.away_last_a_eq h4 hza h2 hxa' E.hxo
    · have hpos := card_pos.mpr ⟨_, hxa E.x hxa' E.hxo⟩
      have hposb := card_pos.mpr ⟨_, hxb z hzb h2⟩
      omega
    · have hpos := card_pos.mpr ⟨_, hxb E.x hxb' E.hxo⟩
      have hposa := card_pos.mpr ⟨_, hxa z hza h2⟩
      omega
    · have hpos := card_pos.mpr ⟨_, hxb E.x hxb' E.hxo⟩
      have h4 : M.deg (C.b C.n) = 4 := by have := C.card_away_last_a; omega
      exact C.away_last_b_eq h4 hzb h2 hxb' E.hxo
  · rintro rfl
    exact mem_crossDarts.mpr ⟨by rcases E.hx with h | h <;> rw [h] <;> [exact C.a_mem le_rfl; exact C.b_mem le_rfl],
      E.hxo⟩

/-- The chain of a (Y1), case 2 ending as a one-exit set. -/
def toOneExit : OneExit M := ⟨C.set, C.set_sub, E.x, E.cross_eq⟩

end Y1End2

/-- **DH23 Lemma `ylem2`, first statement, (Y1) case 2**: `𝔄(𝕄) ≤ 𝔄(𝕄 ∖ chain)`. -/
theorem ylem2_Y1c2 (d : ℕ) (hd : 3 ≤ d) (γ : ℝ) (hγ : γ ∈ Set.Ioo (0 : ℝ) 1) (η : ℝ) (hη : 0 < η)
    (hηmax : η ≤ min γ (1 - γ) / 2) :
    ∃ Cstar : ℝ, 1 ≤ Cstar ∧ ∀ C1 ≥ 2 * Cstar, ∀ δ ∈ Set.Ioc (0 : ℝ) 1, ∃ R : ℝ, ∀ L ≥ R,
    ∀ {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D] (M : Molecule V D),
      (∀ v ∈ M.atoms, M.outdeg v ≤ 2 ∧ M.indeg v ≤ 2) → ∀ (C : YChain M) (_ : Y1End2 C),
      ∀ P : Finset V → ℝ, (∀ S ∈ MoleProp.ladderCells M, 0 ≤ P S) →
        AFree M d L γ δ η C1 P ≤ AFree (Degen.eraseAtoms M C.set) d L γ δ η C1 P := by
  obtain ⟨Cstar, hCstar, hO⟩ := oneExit_bound d hd γ hγ η hη hηmax
  refine ⟨Cstar, hCstar, fun C1 hC1 δ hδ => ?_⟩
  obtain ⟨R, hR⟩ := hO C1 hC1 δ hδ
  refine ⟨R, fun L hL => ?_⟩
  intro V D _ _ _ M hcap C E P hP
  exact hR L hL M hcap E.toOneExit C.piece_connected P hP

end WaveTurbulence.MoleProp4
