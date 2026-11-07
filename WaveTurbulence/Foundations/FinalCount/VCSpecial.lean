/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.FinalCount.VCLadder
public import WaveTurbulence.Foundations.FinalCount.VCDict
/-! # VINE-COUNT part 10: ladder rungs versus chart rungs.

Every rung `(u_i, v_i)` of a ladder inside the group `S` is either a chart rung (`{rx j, ry j}` of the contract) or
consists of two *special* atoms (the core atoms `u₁,u₂,u₃` of a normal vine and the two atoms of the single-bond
junction pair of VII); there are at most `5` special atoms, so at most `2` disjoint rungs can be of the second kind.
The proof is the degree count: an atom of degree `4` with a double bond to its chart partner and a double bond
to its ladder partner has no room for a rail. -/
@[expose] public section
open WaveTurbulence.VineParamContract
set_option autoImplicit false
set_option linter.unusedSectionVars false
open Finset Classical
namespace WaveTurbulence.VineCount
open WaveTurbulence

variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D] {d : ℕ}

section Deg
variable {M : Molecule V D} {S : Finset V}

theorem rung_partner_eq {t s t' tt : V} (hts : t ∈ S) (hs : s ∈ S) (ht' : t' ∈ S) (htt : tt ∈ S)
    (hdeg : M.degIn S t = 4) (h_ts : t ≠ s) (h_tt' : t ≠ t') (h_st' : s ≠ t') (h_ttt : t ≠ tt)
    (b_ts : M.bondsBetween t s = 2) (b_tt' : M.bondsBetween t t' = 1) (b_ttt : M.bondsBetween t tt = 2) :
    s = tt := by
  by_contra hne
  have h1 : tt ≠ t' := fun e => by rw [e] at b_ttt; omega
  have hZ : ({s, tt, t'} : Finset V) ⊆ S := by
    intro z hz
    simp only [Finset.mem_insert, Finset.mem_singleton] at hz
    rcases hz with rfl | rfl | rfl <;> assumption
  have htZ : t ∉ ({s, tt, t'} : Finset V) := by
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
    exact ⟨h_ts, h_ttt, h_tt'⟩
  have hsum := sum_bondsBetween_le_degIn M hts hZ htZ
  rw [Finset.sum_insert (by simp [hne, h_st']), Finset.sum_insert (by simp [h1]), Finset.sum_singleton] at hsum
  omega

theorem joint_not_ladder {t s t' : V} (hts : t ∈ S) (hs : s ∈ S) (ht' : t' ∈ S) (hdeg : M.degIn S t = 2)
    (h_ts : t ≠ s) (h_tt' : t ≠ t') (h_st' : s ≠ t')
    (b_ts : M.bondsBetween t s = 2) (b_tt' : M.bondsBetween t t' = 1) : False := by
  have hZ : ({s, t'} : Finset V) ⊆ S := by
    intro z hz
    simp only [Finset.mem_insert, Finset.mem_singleton] at hz
    rcases hz with rfl | rfl <;> assumption
  have htZ : t ∉ ({s, t'} : Finset V) := by
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
    exact ⟨h_ts, h_tt'⟩
  have hsum := sum_bondsBetween_le_degIn M hts hZ htZ
  rw [Finset.sum_insert (by simp [h_st']), Finset.sum_singleton] at hsum
  omega

end Deg

section LadderNbr
variable {M : Molecule V D} {m : ℕ} {u v : Fin (m + 1) → V}

theorem ladder_nbr (h : M.IsLadder u v) (i : Fin (m + 1)) :
    ∃ i' : Fin (m + 1), i' ≠ i ∧ M.bondsBetween (u i) (u i') = 1 ∧ M.bondsBetween (v i) (v i') = 1 := by
  have hm : 1 ≤ m := h.1
  by_cases hi : i.val < m
  · obtain ⟨r1, r2, -⟩ := h.2.2.2.2 ⟨i.val, hi⟩
    have : (⟨i.val, hi⟩ : Fin m).castSucc = i := Fin.ext rfl
    rw [this] at r1 r2
    refine ⟨(⟨i.val, hi⟩ : Fin m).succ, fun e => ?_, r1, r2⟩
    have := congrArg Fin.val e; simp at this
  · have hi' : i.val = m := by omega
    have hj : m - 1 < m := by omega
    obtain ⟨r1, r2, -⟩ := h.2.2.2.2 ⟨m - 1, hj⟩
    have : (⟨m - 1, hj⟩ : Fin m).succ = i := Fin.ext (by simp; omega)
    rw [this] at r1 r2
    refine ⟨(⟨m - 1, hj⟩ : Fin m).castSucc, fun e => ?_, ?_, ?_⟩
    · have := congrArg Fin.val e; simp at this; omega
    · rw [Mole.bondsBetween_symm]; exact r1
    · rw [Mole.bondsBetween_symm]; exact r2

theorem ladder_ne (h : M.IsLadder u v) : (∀ x y : Fin (m + 1), x ≠ y → u x ≠ u y) ∧ (∀ x y : Fin (m + 1), x ≠ y → v x ≠ v y) ∧
    ∀ x y : Fin (m + 1), u x ≠ v y := by
  have hinj := h.2.1
  refine ⟨fun x y hxy he => hxy (by
    have := hinj (show Sum.elim u v (Sum.inl x) = Sum.elim u v (Sum.inl y) from he)
    simpa using this), fun x y hxy he => hxy (by
    have := hinj (show Sum.elim u v (Sum.inr x) = Sum.elim u v (Sum.inr y) from he)
    simpa using this), fun x y he => ?_⟩
  have := hinj (show Sum.elim u v (Sum.inl x) = Sum.elim u v (Sum.inr y) from he)
  exact Sum.inl_ne_inr this

end LadderNbr

end WaveTurbulence.VineCount
