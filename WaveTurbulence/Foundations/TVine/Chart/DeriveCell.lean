/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.TVine.Chart.DerivePorts
public import WaveTurbulence.Foundations.TVine.Chart.Shapes

/-!
# Derivation of the cell decomposition, V: the generic cell builder

Given an undirected piece shape `P`, a table of local charts covering all its balanced orientations, and an
injective placement of its atoms and bonds in `S` (internal bonds between the right atoms, stubs leaving the piece),
the actual orientation bits select a local chart of the table, and the placement is a local embedding of it
(`build_cell`). Completeness at each atom and balance follow by counting (each atom has local degree `4` = its
degree in `S`).
-/

@[expose] public section
set_option autoImplicit false

namespace WaveTurbulence.TVine.Chart

open Finset VineParamContract

variable {V D : Type} [DecidableEq V] [Fintype D] [DecidableEq D] {M : Molecule V D} {S : Finset V}

namespace PShape

variable {nA nB : ℕ} (P : PShape nA nB)

theorem src_or_dst (b : Fin nB → Bool) (l : Fin nB) (u : Fin nA) :
    (P.src b l = some u ∨ P.dst b l = some u) ↔ ((P.ends l).1 = u ∨ (P.ends l).2 = some u) := by
  unfold src dst
  rcases hl : P.ends l with ⟨u', w⟩
  cases b l <;> cases w <;> simp <;> tauto

end PShape

/-- The orientation bits of a placement. -/
def placeBits {nA nB : ℕ} (P : PShape nA nB) (φA : Fin nA → V) (φB : Fin nB → Bond M S) : Fin nB → Bool :=
  fun l => decide (tl (φB l) = φA (P.ends l).1)

section Build

variable {nA nC nB : ℕ} (P : PShape nA nB) (φA : Fin nA → V) (φB : Fin nB → Bond M S)
  (hAinj : Function.Injective φA)
  (hnoloop : ∀ l u w, P.ends l = (u, some w) → u ≠ w)
  (hint : ∀ l u w, P.ends l = (u, some w) →
    (tl (φB l) = φA u ∧ hd (φB l) = φA w) ∨ (tl (φB l) = φA w ∧ hd (φB l) = φA u))
  (hstub : ∀ l u, P.ends l = (u, none) →
    (tl (φB l) = φA u ∧ ∀ u', hd (φB l) ≠ φA u') ∨ (hd (φB l) = φA u ∧ ∀ u', tl (φB l) ≠ φA u'))
include hAinj hnoloop hint hstub

theorem place_src (l : Fin nB) (u : Fin nA) : P.src (placeBits P φA φB) l = some u ↔ tl (φB l) = φA u := by
  unfold PShape.src placeBits
  rcases hl : P.ends l with ⟨u₀, w⟩
  rcases w with _ | w
  · rcases hstub l u₀ hl with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · simp only [hl, h1, decide_true, ite_true, Option.some.injEq]
      exact ⟨fun h => by subst h; rfl, fun h => by first | exact hAinj h | exact (hAinj h).symm | exact hAinj h.symm | exact (hAinj h.symm).symm⟩
    · have : ¬ tl (φB l) = φA u₀ := h2 u₀
      simp only [hl, this, decide_false, Bool.false_eq_true, ite_false, reduceCtorEq, false_iff]
      exact h2 u
  · have hne := hnoloop l u₀ w hl
    rcases hint l u₀ w hl with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · simp only [hl, h1, decide_true, ite_true, Option.some.injEq]
      exact ⟨fun h => by subst h; rfl, fun h => by first | exact hAinj h | exact (hAinj h).symm | exact hAinj h.symm | exact (hAinj h.symm).symm⟩
    · have : ¬ φA w = φA u₀ := fun h => hne (hAinj h).symm
      simp only [hl, h1, this, decide_false, Bool.false_eq_true, ite_false, Option.some.injEq]
      exact ⟨fun h => by subst h; rfl, fun h => by first | exact hAinj h | exact (hAinj h).symm | exact hAinj h.symm | exact (hAinj h.symm).symm⟩

theorem place_dst (l : Fin nB) (u : Fin nA) : P.dst (placeBits P φA φB) l = some u ↔ hd (φB l) = φA u := by
  unfold PShape.dst placeBits
  rcases hl : P.ends l with ⟨u₀, w⟩
  rcases w with _ | w
  · rcases hstub l u₀ hl with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · simp only [hl, h1, decide_true, ite_true, reduceCtorEq, false_iff]
      exact h2 u
    · have : ¬ tl (φB l) = φA u₀ := h2 u₀
      simp only [hl, this, decide_false, Bool.false_eq_true, ite_false, Option.some.injEq, h1]
      exact ⟨fun h => by subst h; rfl, fun h => by first | exact hAinj h | exact (hAinj h).symm | exact hAinj h.symm | exact (hAinj h.symm).symm⟩
  · have hne := hnoloop l u₀ w hl
    rcases hint l u₀ w hl with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · simp only [hl, h1, decide_true, ite_true, Option.some.injEq, h2]
      exact ⟨fun h => by subst h; rfl, fun h => by first | exact hAinj h | exact (hAinj h).symm | exact hAinj h.symm | exact (hAinj h.symm).symm⟩
    · have : ¬ φA w = φA u₀ := fun h => hne (hAinj h).symm
      simp only [hl, h1, this, decide_false, Bool.false_eq_true, ite_false, Option.some.injEq, h2]
      exact ⟨fun h => by subst h; rfl, fun h => by first | exact hAinj h | exact (hAinj h).symm | exact hAinj h.symm | exact (hAinj h.symm).symm⟩

end Build

/-- **The generic cell builder.** -/
theorem build_cell {nA nC nB : ℕ} (P : PShape nA nB) (tab : List (LocalChart nA nC nB))
    (hcov : ∀ b : Fin nB → Bool, P.OK b → ∃ c ∈ tab, c.src = P.src b ∧ c.dst = P.dst b)
    (hM : M.IsMolecule) (φA : Fin nA → V) (φB : Fin nB → Bond M S)
    (hAinj : Function.Injective φA) (hBinj : Function.Injective φB)
    (hmem : ∀ u, φA u ∈ M.atoms) (hdeg : ∀ u, M.degIn S (φA u) = 4)
    (hlocdeg : ∀ u : Fin nA, 4 ≤ (univ.filter fun l => (P.ends l).1 = u ∨ (P.ends l).2 = some u).card)
    (hnoloop : ∀ l u w, P.ends l = (u, some w) → u ≠ w)
    (hint : ∀ l u w, P.ends l = (u, some w) →
      (tl (φB l) = φA u ∧ hd (φB l) = φA w) ∨ (tl (φB l) = φA w ∧ hd (φB l) = φA u))
    (hstub : ∀ l u, P.ends l = (u, none) →
      (tl (φB l) = φA u ∧ ∀ u', hd (φB l) ≠ φA u') ∨ (hd (φB l) = φA u ∧ ∀ u', tl (φB l) ≠ φA u'))
    (hpairs : ∀ ρ ∈ [SRole.inp, SRole.exM, SRole.exB],
      (univ.filter fun l => P.role l = ρ ∧ placeBits P φA φB l = true).card =
        (univ.filter fun l => P.role l = ρ ∧ placeBits P φA φB l = false).card) :
    ∃ c ∈ tab, c.src = P.src (placeBits P φA φB) ∧ c.dst = P.dst (placeBits P φA φB) ∧
      ∃ φ : LocEmb c.graph M S, φ.atom = φA ∧ φ.bond = φB := by
  classical
  set bits := placeBits P φA φB
  have hsrc := place_src P φA φB hAinj hnoloop hint hstub
  have hdst := place_dst P φA φB hAinj hnoloop hint hstub
  -- completeness at each atom
  have hcomp : ∀ u, (univ.filter fun l => (P.ends l).1 = u ∨ (P.ends l).2 = some u).image φB = bondsAt (φA u) := by
    intro u
    apply bondsAt_eq_of_card
    · intro e he
      obtain ⟨l, hl, rfl⟩ := mem_image.mp he
      rw [mem_filter] at hl
      rw [mem_bondsAt, ← hsrc l u, ← hdst l u]
      exact (P.src_or_dst bits l u).mpr hl.2
    · rw [card_image_of_injective _ hBinj, hdeg u]; exact hlocdeg u
  have hcomplete : ∀ u (e : Bond M S), tl e = φA u ∨ hd e = φA u → ∃ l, φB l = e := by
    intro u e he
    have : e ∈ bondsAt (M := M) (S := S) (φA u) := mem_bondsAt.mpr he
    rw [← hcomp u] at this
    obtain ⟨l, -, hl⟩ := mem_image.mp this
    exact ⟨l, hl⟩
  -- balance
  have hbal : ∀ u, M.outIn S (φA u) = 2 ∧ M.inIn S (φA u) = 2 := fun u => balanced_of_deg4 hM (hmem u) (hdeg u)
  have hcountS : ∀ u, (univ.filter fun l => P.src bits l = some u).card = 2 := by
    intro u
    rw [← (hbal u).1, ← card_tl]
    have : (univ.filter fun l => P.src bits l = some u).image φB = univ.filter fun e : Bond M S => tl e = φA u := by
      ext e
      simp only [mem_image, mem_filter, mem_univ, true_and]
      constructor
      · rintro ⟨l, hl, rfl⟩; exact (hsrc l u).mp hl
      · intro he
        obtain ⟨l, rfl⟩ := hcomplete u e (Or.inl he)
        exact ⟨l, (hsrc l u).mpr he, rfl⟩
    rw [← this, card_image_of_injective _ hBinj]
  have hcountD : ∀ u, (univ.filter fun l => P.dst bits l = some u).card = 2 := by
    intro u
    rw [← (hbal u).2, ← card_hd]
    have : (univ.filter fun l => P.dst bits l = some u).image φB = univ.filter fun e : Bond M S => hd e = φA u := by
      ext e
      simp only [mem_image, mem_filter, mem_univ, true_and]
      constructor
      · rintro ⟨l, hl, rfl⟩; exact (hdst l u).mp hl
      · intro he
        obtain ⟨l, rfl⟩ := hcomplete u e (Or.inr he)
        exact ⟨l, (hdst l u).mpr he, rfl⟩
    rw [← this, card_image_of_injective _ hBinj]
  have hOK : P.OK bits := ⟨fun u => ⟨hcountS u, hcountD u⟩, hpairs⟩
  obtain ⟨c, hc, hcs, hcd⟩ := hcov bits hOK
  refine ⟨c, hc, hcs, hcd, ⟨φA, φB, hAinj, hBinj, ?_, ?_, ?_, ?_, ?_⟩, rfl, rfl⟩
  · intro l u h; exact (hsrc l u).mp (by rw [← hcs]; exact h)
  · intro l h u ht
    have : P.src bits l = some u := (hsrc l u).mpr ht
    change c.src l = none at h
    rw [hcs] at h; rw [h] at this; simp at this
  · intro l u h; exact (hdst l u).mp (by rw [← hcd]; exact h)
  · intro l h u ht
    have : P.dst bits l = some u := (hdst l u).mpr ht
    change c.dst l = none at h
    rw [hcd] at h; rw [h] at this; simp at this
  · exact hcomplete

end WaveTurbulence.TVine.Chart
