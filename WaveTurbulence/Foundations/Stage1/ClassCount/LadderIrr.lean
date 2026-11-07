/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.LayerCnt.LadderIncidences
public import WaveTurbulence.Foundations.Molecule.VineFourIncidences
import Mathlib.Tactic

/-!
# CLASSCOUNT: irregular darts at the atoms of a ladder

A ladder `(u, v)` of length `m` in a molecule has *regular pairs*: the rungs `{u_j, v_j}` and the rails
`{u_j, u_{j+1}}`, `{v_j, v_{j+1}}`.  An interior atom has all four of its darts to regular partners; an end atom
has at most one dart to a non-regular partner (degree `≤ 4`, and `2 + 1` darts are accounted for).
-/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.ClassCount
open Finset WaveTurbulence WaveTurbulence.Vine WaveTurbulence.LayerCnt

variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]

/-- The regular pairs of a ladder. -/
def LReg {m : ℕ} (u v : Fin (m + 1) → V) (a b : V) : Prop :=
  (∃ i : Fin (m + 1), (a = u i ∧ b = v i) ∨ (a = v i ∧ b = u i)) ∨
  (∃ i : Fin m, (a = u i.castSucc ∧ b = u i.succ) ∨ (a = u i.succ ∧ b = u i.castSucc) ∨
    (a = v i.castSucc ∧ b = v i.succ) ∨ (a = v i.succ ∧ b = v i.castSucc))

variable (M : Molecule V D) {m : ℕ} {u v : Fin (m + 1) → V}

theorem bb_u_next (hL : M.IsLadder u v) (j jp : Fin (m + 1)) (h : j.1 + 1 = jp.1) :
    M.bondsBetween (u j) (u jp) = 1 := by
  have hj : j.1 < m := by omega
  have := (ladder_rails M hL ⟨j.1, hj⟩).1
  have e : (⟨j.1, hj⟩ : Fin m).succ = jp := Fin.ext (by simp [← h])
  have e' : (⟨j.1, hj⟩ : Fin m).castSucc = j := Fin.ext (by simp)
  rw [e, e'] at this
  exact this

theorem bb_v_next (hL : M.IsLadder u v) (j jp : Fin (m + 1)) (h : j.1 + 1 = jp.1) :
    M.bondsBetween (v j) (v jp) = 1 := by
  have hj : j.1 < m := by omega
  have := (ladder_rails M hL ⟨j.1, hj⟩).2.1
  have e : (⟨j.1, hj⟩ : Fin m).succ = jp := Fin.ext (by simp [← h])
  have e' : (⟨j.1, hj⟩ : Fin m).castSucc = j := Fin.ext (by simp)
  rw [e, e'] at this
  exact this

/-- The darts at `a` to a given partner `b ≠ a`: their number is the number of bonds. -/
theorem card_darts_to (a b : V) (hab : a ≠ b) :
    ((M.dartsAt a).filter (fun x => M.atom (M.mate x) = b)).card = M.bondsBetween a b :=
  (Mole.bondsBetween_eq_card_darts M hab).symm

/-- An atom with a rung-type partner of multiplicity `2` and a rail-type partner of multiplicity `1`
has at most one other dart. -/
theorem other_darts_le_one (hM : M.IsMolecule) {a b c : V} (ha : a ∈ M.atoms) (hab : a ≠ b) (hac : a ≠ c)
    (hbc : b ≠ c) (h1 : M.bondsBetween a b = 2) (h2 : M.bondsBetween a c = 1) :
    ((M.dartsAt a).filter (fun x => M.atom (M.mate x) ≠ b ∧ M.atom (M.mate x) ≠ c)).card ≤ 1 := by
  classical
  have hdeg := Mole.deg_le_four M hM ha
  have e1 := card_darts_to M a b hab
  have e2 := card_darts_to M a c hac
  rw [h1] at e1
  rw [h2] at e2
  have hsplit : (M.dartsAt a).card =
      ((M.dartsAt a).filter (fun x => M.atom (M.mate x) = b)).card +
      ((M.dartsAt a).filter (fun x => M.atom (M.mate x) = c)).card +
      ((M.dartsAt a).filter (fun x => M.atom (M.mate x) ≠ b ∧ M.atom (M.mate x) ≠ c)).card := by
    rw [← Finset.card_union_of_disjoint, ← Finset.card_union_of_disjoint]
    · congr 1
      ext x
      simp only [Finset.mem_union, Finset.mem_filter]
      tauto
    · rw [Finset.disjoint_left]
      intro x hx hx'
      simp only [Finset.mem_union, Finset.mem_filter] at hx hx'
      rcases hx with ⟨_, h⟩ | ⟨_, h⟩
      · exact hx'.2.1 h
      · exact hx'.2.2 h
    · rw [Finset.disjoint_left]
      intro x hx hx'
      simp only [Finset.mem_filter] at hx hx'
      exact hbc (hx.2.symm.trans hx'.2)
  have : M.deg a = (M.dartsAt a).card := rfl
  rw [e1, e2] at hsplit
  omega

variable {M}

theorem LReg_rung_u (j : Fin (m + 1)) : LReg u v (u j) (v j) := Or.inl ⟨j, Or.inl ⟨rfl, rfl⟩⟩
theorem LReg_rung_v (j : Fin (m + 1)) : LReg u v (v j) (u j) := Or.inl ⟨j, Or.inr ⟨rfl, rfl⟩⟩
theorem LReg_rail_u_next (j jp : Fin (m + 1)) (h : j.1 + 1 = jp.1) : LReg u v (u j) (u jp) := by
  have h1 : (⟨j.1, by omega⟩ : Fin m).castSucc = j := Fin.ext rfl
  have h2 : (⟨j.1, by omega⟩ : Fin m).succ = jp := Fin.ext (by simp [h])
  exact Or.inr ⟨⟨j.1, by omega⟩, Or.inl ⟨by rw [h1], by rw [h2]⟩⟩
theorem LReg_rail_u_prev (j jm : Fin (m + 1)) (h : jm.1 + 1 = j.1) : LReg u v (u j) (u jm) := by
  have h1 : (⟨jm.1, by omega⟩ : Fin m).castSucc = jm := Fin.ext rfl
  have h2 : (⟨jm.1, by omega⟩ : Fin m).succ = j := Fin.ext (by simp [h])
  exact Or.inr ⟨⟨jm.1, by omega⟩, Or.inr (Or.inl ⟨by rw [h2], by rw [h1]⟩)⟩
theorem LReg_rail_v_next (j jp : Fin (m + 1)) (h : j.1 + 1 = jp.1) : LReg u v (v j) (v jp) := by
  have h1 : (⟨j.1, by omega⟩ : Fin m).castSucc = j := Fin.ext rfl
  have h2 : (⟨j.1, by omega⟩ : Fin m).succ = jp := Fin.ext (by simp [h])
  exact Or.inr ⟨⟨j.1, by omega⟩, Or.inr (Or.inr (Or.inl ⟨by rw [h1], by rw [h2]⟩))⟩
theorem LReg_rail_v_prev (j jm : Fin (m + 1)) (h : jm.1 + 1 = j.1) : LReg u v (v j) (v jm) := by
  have h1 : (⟨jm.1, by omega⟩ : Fin m).castSucc = jm := Fin.ext rfl
  have h2 : (⟨jm.1, by omega⟩ : Fin m).succ = j := Fin.ext (by simp [h])
  exact Or.inr ⟨⟨jm.1, by omega⟩, Or.inr (Or.inr (Or.inr ⟨by rw [h2], by rw [h1]⟩))⟩

end WaveTurbulence.ClassCount
