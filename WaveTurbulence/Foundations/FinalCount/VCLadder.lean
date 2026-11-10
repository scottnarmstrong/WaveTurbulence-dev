/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.FinalCount.VCShift
/-! # VINE-COUNT part 9: squares of a ladder.

Every pair of adjacent rungs `(u_i, v_i)`, `(u_{i±1}, v_{i±1})` of a ladder of `M` inside `S` carries a `Square`
(rails, rungs, and the opposite-direction clause of the ladder as the incidence relation `hdir`). -/
@[expose] public section
open WaveTurbulence.VineParamContract
set_option autoImplicit false
set_option linter.unusedSectionVars false
open Finset Classical
namespace WaveTurbulence.VineCount
open WaveTurbulence

variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D] {d : ℕ}

theorem atom_cases {M : Molecule V D} {e : D} {a b : V} (he : M.ends e = s(a, b)) :
    (M.atom e = a ∧ M.atom (M.mate e) = b) ∨ (M.atom e = b ∧ M.atom (M.mate e) = a) := Sym2.eq_iff.mp he

theorem incidence_eq_ite {M : Molecule V D} {e : D} {a b : V} (hab : a ≠ b) (he : M.ends e = s(a, b)) :
    incidence M a e = if M.atom e = a then 1 else -1 := by
  rcases atom_cases he with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · simp [incidence, h1, h2, hab, hab.symm]
  · have : M.atom e ≠ a := by rw [h1]; exact hab.symm
    simp [incidence, h1, h2, this, hab, hab.symm]

namespace Square
variable {M : Molecule V D} {S : Finset V} {t s t' s' : V}

/-- The same square seen from the other rung. -/
def flip (Q : Square M S t s t' s') : Square M S t' s' t s where
  p := Q.p
  p' := Q.p'
  ρ := Q.ρ'
  ρ' := Q.ρ
  p_out := Q.p_out
  p'_out := Q.p'_out
  ρ_out := Q.ρ'_out
  ρ'_out := Q.ρ_out
  p_ends := by rw [Q.p_ends, Sym2.eq_swap]
  p'_ends := by rw [Q.p'_ends, Sym2.eq_swap]
  ρ_ends := Q.ρ'_ends
  ρ'_ends := Q.ρ_ends
  hdir := by
    have h1 := incidence_add M Q.hss Q.p'_ends
    have h2 := incidence_add M Q.htt Q.p_ends
    have h3 := Q.hdir
    linarith
  hts := Q.ht's'
  htt := Q.htt.symm
  hts' := Q.hst.symm
  hst := Q.hts'.symm
  hss := Q.hss.symm
  ht's' := Q.hts
  ht := Q.ht'
  hs := Q.hs'
  ht' := Q.ht
  hs' := Q.hs

end Square

section LadderSquare
variable {M : Molecule V D} {S : Finset V} {m : ℕ} {u v : Fin (m + 1) → V}

theorem ladder_square (h : M.IsLadder u v) (hS : ∀ j, u j ∈ S ∧ v j ∈ S) (jj : Fin m) :
    Nonempty (Square M S (u jj.castSucc) (v jj.castSucc) (u jj.succ) (v jj.succ)) := by
  obtain ⟨hm, hinj, -, hrung, hrail⟩ := h
  have hne : ∀ x y : Fin (m + 1), x ≠ y → u x ≠ u y := fun x y hxy he => hxy (by
    have := hinj (show Sum.elim u v (Sum.inl x) = Sum.elim u v (Sum.inl y) from he)
    simpa using this)
  have hnev : ∀ x y : Fin (m + 1), x ≠ y → v x ≠ v y := fun x y hxy he => hxy (by
    have := hinj (show Sum.elim u v (Sum.inr x) = Sum.elim u v (Sum.inr y) from he)
    simpa using this)
  have hnuv : ∀ x y : Fin (m + 1), u x ≠ v y := fun x y he => by
    have := hinj (show Sum.elim u v (Sum.inl x) = Sum.elim u v (Sum.inr y) from he)
    exact Sum.inl_ne_inr this
  have hlh : jj.castSucc ≠ jj.succ := fun e => by
    have := congrArg Fin.val e; simp at this
  obtain ⟨r1, r2, r3⟩ := hrail jj
  have hAA' := hne _ _ hlh
  have hBB' := hnev _ _ hlh
  obtain ⟨p, hp1, hp2⟩ := exists_bond M (by rw [r1]; norm_num : 0 < M.bondsBetween (u jj.castSucc) (u jj.succ))
  obtain ⟨p', hp1', hp2'⟩ := exists_bond M (by rw [r2]; norm_num : 0 < M.bondsBetween (v jj.castSucc) (v jj.succ))
  obtain ⟨ρ, hρ1, hρ2⟩ := exists_bond M (by rw [hrung]; norm_num : 0 < M.bondsBetween (u jj.castSucc) (v jj.castSucc))
  obtain ⟨ρ', hρ1', hρ2'⟩ := exists_bond M (by rw [hrung]; norm_num : 0 < M.bondsBetween (u jj.succ) (v jj.succ))
  have hd1 : M.Directed (u jj.castSucc) (u jj.succ) ↔ M.atom p = u jj.castSucc :=
    directed_iff_atom M hAA' r1 hp1 hp2
  have hd2 : M.Directed (v jj.succ) (v jj.castSucc) ↔ M.atom p' = v jj.succ := by
    have hsym : M.bondsBetween (v jj.succ) (v jj.castSucc) = 1 := by
      rw [Mole.bondsBetween_symm]; exact r2
    refine directed_iff_atom M hBB'.symm hsym hp1' ?_
    rw [hp2', Sym2.eq_swap]
  have hiff : M.atom p = u jj.castSucc ↔ M.atom p' = v jj.succ := by rw [← hd1, ← hd2]; exact r3
  have hdir : incidence M (v jj.castSucc) p' = - incidence M (u jj.castSucc) p := by
    rw [incidence_eq_ite hBB' hp2', incidence_eq_ite hAA' hp2]
    by_cases hA : M.atom p = u jj.castSucc
    · have : ¬ M.atom p' = v jj.castSucc := by
        intro hh
        have := hiff.mp hA
        exact hBB' (hh.symm.trans this)
      simp [hA, this]
    · have : M.atom p' = v jj.castSucc := by
        rcases atom_cases hp2' with ⟨h1, -⟩ | ⟨h1, -⟩
        · exact h1
        · exact absurd (hiff.mpr h1) hA
      simp [hA, this]
  exact ⟨⟨p, p', ρ, ρ', hp1, hp1', hρ1, hρ1', hp2, hp2', hρ2, hρ2', hdir, hnuv _ _, hAA', hnuv _ _,
    (hnuv _ _).symm, hBB', hnuv _ _, (hS _).1, (hS _).2, (hS _).1, (hS _).2⟩⟩

end LadderSquare

end WaveTurbulence.VineCount
