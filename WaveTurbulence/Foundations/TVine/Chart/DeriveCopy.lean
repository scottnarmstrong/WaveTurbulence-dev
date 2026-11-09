/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.TVine.Chart.DeriveRung

/-!
# Derivation of the cell decomposition, XIV: the copy cell of a (P-b) triangle

At the (P-b) step the exit port of `Z j` is `{t, α}` and the entry port of `Z (j+1)` is `{t, α'}`; the pendant port is
`{α, α'}`. The copy cell (no atoms) takes `{t, α}` as its input pair and owns `α'` (whose label is that of `α`, by the
2-cut relation of `H 0`, N1 Lemma D). Its chart is `cfgK0` if `α` is the outgoing bond of the exit port and `cfgK1`
otherwise.
-/

@[expose] public section
set_option autoImplicit false

namespace WaveTurbulence.TVine.Chart

open Finset VineParamContract

variable {V D : Type} [DecidableEq V] [Fintype D] [DecidableEq D] {M : Molecule V D} {S : Finset V} {a b : V}

/-- The copy embedding: no atoms, the bonds `e₀, e₁, e₂`. -/
def copyEmb (c : LocalChart 0 0 3) (e₀ e₁ e₂ : Bond M S) (h01 : e₀ ≠ e₁) (h02 : e₀ ≠ e₂) (h12 : e₁ ≠ e₂) :
    LocEmb c.graph M S where
  atom := fun u => u.elim0
  bond := ![e₀, e₁, e₂]
  atom_inj := fun u => u.elim0
  bond_inj := by
    intro i j h
    fin_cases i <;> fin_cases j <;> simp at h <;> first | rfl | exact absurd h ‹_› | exact absurd h.symm ‹_›
  tl_eq := fun _ u _ => u.elim0
  tl_out := fun _ _ u => u.elim0
  hd_eq := fun _ u _ => u.elim0
  hd_out := fun _ _ u => u.elim0
  complete := fun u => u.elim0

/-- **Placing the copy cell.** -/
theorem place_copy {Xx Xe Xb : Finset V} (πx : Port2 M S Xx a b) (πe : Port2 M S Xe a b) (πb : Port2 M S Xb a b)
    (t α α' : Bond M S)
    (hK : (α = πx.out ∧ t = πx.inn ∧ α' = πe.out ∧ t = πe.inn ∧ α = πb.out ∧ α' = πb.inn) ∨
      (α = πx.inn ∧ t = πx.out ∧ α' = πe.inn ∧ t = πe.out ∧ α = πb.inn ∧ α' = πb.out))
    (hα'x : α' ≠ πx.out ∧ α' ≠ πx.inn) :
    ∃ c : LocalChart 0 0 3, (c = cfgK0 ∨ c = cfgK1) ∧ c.Valid ∧ c.Rel 1 1 0 ∧ c.ExtrasOK ∧
      ∃ φ : LocEmb c.graph M S, φ.bond c.eO = πx.out ∧ φ.bond c.eI = πx.inn ∧
        (∃ p, c.outM = some p ∧ φ.bond p.1 = πe.out ∧ φ.bond p.2 = πe.inn) ∧
        (∃ p, c.outB = some p ∧ φ.bond p.1 = πb.out ∧ φ.bond p.2 = πb.inn) ∧
        (∀ x, φ.bond (c.X₁ x) = α' ∧ φ.bond (c.X₂ x) = α) ∧ φ.bond 2 = α' ∧
        ∀ l, ¬ c.IsInput l → l = 2 := by
  have hne := πx.ne
  rcases hK with ⟨h1, h2, h3, h4, h5, h6⟩ | ⟨h1, h2, h3, h4, h5, h6⟩
  · obtain ⟨hv, hrel, hex, hX⟩ := cfgK0_ok
    refine ⟨cfgK0, Or.inl rfl, hv, hrel, hex,
      copyEmb cfgK0 πx.out πx.inn α' hne hα'x.1.symm hα'x.2.symm, rfl, rfl, ⟨(2, 1), rfl, ?_, ?_⟩,
      ⟨(0, 2), rfl, ?_, ?_⟩, ?_, rfl, ?_⟩
    · show α' = πe.out; exact h3
    · show πx.inn = πe.inn; rw [← h2, h4]
    · show πx.out = πb.out; rw [← h1, h5]
    · show α' = πb.inn; exact h6
    · intro x; rw [(hX x).1, (hX x).2]; exact ⟨rfl, h1.symm⟩
    · intro l hl; fin_cases l
      · exact absurd (Or.inl rfl) hl
      · exact absurd (Or.inr rfl) hl
      · rfl
  · obtain ⟨hv, hrel, hex, hX⟩ := cfgK1_ok
    refine ⟨cfgK1, Or.inr rfl, hv, hrel, hex,
      copyEmb cfgK1 πx.out πx.inn α' hne hα'x.1.symm hα'x.2.symm, rfl, rfl, ⟨(0, 2), rfl, ?_, ?_⟩,
      ⟨(2, 1), rfl, ?_, ?_⟩, ?_, rfl, ?_⟩
    · show πx.out = πe.out; rw [← h2, h4]
    · show α' = πe.inn; exact h3
    · show α' = πb.out; exact h6
    · show πx.inn = πb.inn; rw [← h1, h5]
    · intro x; rw [(hX x).1, (hX x).2]; exact ⟨rfl, h1.symm⟩
    · intro l hl; fin_cases l
      · exact absurd (Or.inl rfl) hl
      · exact absurd (Or.inr rfl) hl
      · rfl

end WaveTurbulence.TVine.Chart
