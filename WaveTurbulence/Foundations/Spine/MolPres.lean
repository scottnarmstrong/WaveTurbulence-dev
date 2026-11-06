/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.Spine.MolTree
import Mathlib.Tactic
/-! A ladder presentation is determined by its first two upper atoms (used to count the possible
presentations of a maximal ladder). -/
@[expose] public section
open Finset
namespace WaveTurbulence.Ladder
open WaveTurbulence WaveTurbulence.LadderDisjoint
variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]

omit [DecidableEq D] in
theorem exists_single_nbr (M : Molecule V D) {m : ℕ} {u v : Fin (m + 1) → V} (hL : M.IsLadder u v)
    {i : ℕ} (hi : i ≤ m) :
    ∃ k, k ≤ m ∧ k ≠ i ∧ M.bondsBetween (rowN u i) (rowN u k) = 1 := by
  have hm : 1 ≤ m := hL.1
  by_cases h : i < m
  · exact ⟨i + 1, by omega, by omega, (ladderN_rail M hL h).1⟩
  · refine ⟨i - 1, by omega, by omega, ?_⟩
    have hi' : i = m := by omega
    have := (ladderN_rail M hL (show i - 1 < m by omega)).1
    rw [show i - 1 + 1 = i by omega] at this
    rw [LadderDisjoint.bondsBetween_comm]; exact this

omit [DecidableEq D] in
theorem partner_eq (M : Molecule V D) (hM : ∀ x ∈ M.atoms, M.deg x ≤ 4) {m : ℕ}
    {u v u' v' : Fin (m + 1) → V} (hL : M.IsLadder u v) (hL' : M.IsLadder u' v') {i : ℕ} (hi : i ≤ m)
    (hu : rowN u i = rowN u' i) : rowN v i = rowN v' i := by
  obtain ⟨k, hk, hki, hb⟩ := exists_single_nbr M hL hi
  have hat : rowN u i ∈ M.atoms := by rw [rowN_of_le u hi]; exact (hL.2.2.1 _).1
  have := unique_double_partner_of_single_rail M hM hat (ladderN_uv M hL hi hi)
    (ladderN_uu M hL hi hk (Ne.symm hki)) (Ne.symm (ladderN_uv M hL hk hi))
    (ladderN_rung M hL hi) hb
    (by rw [hu]; exact ladderN_uv M hL' hi hi) (by rw [hu]; exact ladderN_rung M hL' hi)
  exact this.symm

theorem ladder_eq_of_two (M : Molecule V D) (hM : ∀ x ∈ M.atoms, M.deg x ≤ 4) {m : ℕ}
    {u v u' v' : Fin (m + 1) → V} (hL : M.IsLadder u v) (hL' : M.IsLadder u' v')
    (h0 : rowN u 0 = rowN u' 0) (h1 : rowN u 1 = rowN u' 1) :
    ∀ i : ℕ, i ≤ m → rowN u i = rowN u' i ∧ rowN v i = rowN v' i := by
  have hm : 1 ≤ m := hL.1
  have hu : ∀ i : ℕ, i ≤ m → rowN u i = rowN u' i := by
    intro i
    induction i using Nat.strong_induction_on with
    | _ i ih =>
      intro hi
      rcases Nat.lt_or_ge i 2 with h | h
      · interval_cases i
        · exact h0
        · exact h1
      · -- i = j + 1 with 1 ≤ j < m
        obtain ⟨j, rfl⟩ : ∃ j, i = j + 1 := ⟨i - 1, by omega⟩
        have hjm : j < m := by omega
        have hj1 : 1 ≤ j := by omega
        have hjj := ih j (by omega) (by omega)
        have hjj1 := ih (j - 1) (by omega) (by omega)
        have hvj := partner_eq M hM hL hL' (show j ≤ m by omega) hjj
        -- neighbours of `u_j` in the molecule
        have hl := ladderN_rail M hL (show j - 1 < m by omega)
        rw [show j - 1 + 1 = j by omega] at hl
        have hr := ladderN_rail M hL hjm
        have hl1 : M.bondsBetween (rowN u j) (rowN u (j - 1)) = 1 := by
          rw [LadderDisjoint.bondsBetween_comm]; exact hl.1
        have hdd := dartsAt_interior M (ladderN_uv M hL (show j ≤ m by omega) (show j ≤ m by omega))
          (ladderN_uu M hL (show j ≤ m by omega) (show j - 1 ≤ m by omega) (by omega))
          (ladderN_uu M hL (show j ≤ m by omega) (show j + 1 ≤ m by omega) (by omega))
          (Ne.symm (ladderN_uv M hL (show j - 1 ≤ m by omega) (show j ≤ m by omega)))
          (Ne.symm (ladderN_uv M hL (show j + 1 ≤ m by omega) (show j ≤ m by omega)))
          (ladderN_uu M hL (show j - 1 ≤ m by omega) (show j + 1 ≤ m by omega) (by omega))
          (ladderN_rung M hL (show j ≤ m by omega)) hl1 hr.1
          (hM _ (by rw [rowN_of_le u (show j ≤ m by omega)]; exact (hL.2.2.1 _).1))
        -- `u'_{j+1}` is a neighbour of `u_j`
        have hr' := ladderN_rail M hL' hjm
        have hne' : rowN u j ≠ rowN u' (j + 1) := by
          rw [hjj]; exact ladderN_uu M hL' (show j ≤ m by omega) (show j + 1 ≤ m by omega) (by omega)
        have hcard := card_neighborDarts M hne'
        have hb1 : M.bondsBetween (rowN u j) (rowN u' (j + 1)) = 1 := by rw [hjj]; exact hr'.1
        rw [hb1] at hcard
        obtain ⟨x, hx⟩ := Finset.card_eq_one.mp hcard
        have hxm : x ∈ neighborDarts M (rowN u j) (rowN u' (j + 1)) := by rw [hx]; exact Finset.mem_singleton_self x
        have hxd : x ∈ M.dartsAt (rowN u j) := (Finset.mem_filter.mp hxm).1
        rw [hdd] at hxd
        have hxa := ((mem_neighborDarts' M _ _ x).mp hxm).2
        simp only [Finset.mem_union, mem_neighborDarts'] at hxd
        rcases hxd with (hxd | hxd) | hxd
        · exfalso
          have : rowN u' (j + 1) = rowN v j := hxa.symm.trans hxd.2
          rw [hvj] at this
          exact ladderN_uv M hL' (show j + 1 ≤ m by omega) (show j ≤ m by omega) this
        · exfalso
          have : rowN u' (j + 1) = rowN u (j - 1) := hxa.symm.trans hxd.2
          rw [hjj1] at this
          exact ladderN_uu M hL' (show j + 1 ≤ m by omega) (show j - 1 ≤ m by omega) (by omega) this
        · exact (hxa.symm.trans hxd.2).symm
  intro i hi
  exact ⟨hu i hi, partner_eq M hM hL hL' hi (hu i hi)⟩

end WaveTurbulence.Ladder
