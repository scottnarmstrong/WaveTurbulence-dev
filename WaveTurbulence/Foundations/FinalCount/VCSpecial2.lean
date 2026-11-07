/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.FinalCount.VCSpecial
/-! # VINE-COUNT part 11: chart classification of ladder rungs (see `VCSpecial`). -/
@[expose] public section
open WaveTurbulence.VineParamContract
set_option autoImplicit false
set_option linter.unusedSectionVars false
open Finset Classical
namespace WaveTurbulence.VineCount
open WaveTurbulence

variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D] {d : ℕ}

section Chart
variable {M : Molecule V D} {X : VineType} {S : Finset V} {a b : V} (A : FullVineChart M X S a b)

/-- The atom of a chart index. -/
def av (i : Fin A.indexing.shape.n) : V := (A.indexing.atom i).1

theorem av_inj : Function.Injective (av A) := fun i j h =>
  A.indexing.atom.injective (Subtype.ext h)

theorem av_mem (i : Fin A.indexing.shape.n) : av A i ∈ S ∧ av A i ≠ a := by
  have := (A.indexing.atom i).2
  exact ⟨(Finset.mem_erase.mp this).2, (Finset.mem_erase.mp this).1⟩

theorem av_x0 : av A A.indexing.shape.x0 = b := A.indexing.lower

/-- The two atoms of the `j`-th chart rung. -/
def rx (j : Fin A.indexing.shape.m) : V := av A (A.indexing.shape.xSlot j)
def ry (j : Fin A.indexing.shape.m) : V := av A (A.indexing.shape.ySlot j)

theorem rx_ne_ry (j : Fin A.indexing.shape.m) : rx A j ≠ ry A j := fun h => by
  have := av_inj A h
  have h2 := congrArg Fin.val this
  simp [Shape.xSlot, Shape.ySlot] at h2
  have := j.2; omega

/-- Core indices and the indices of the junction pair. -/
def specialIdx : Finset (Fin A.indexing.shape.n) :=
  Finset.univ.filter fun i => 2 * A.indexing.shape.m + 1 ≤ i.val ∨
    ∃ j, A.junction = some j ∧ (i = A.indexing.shape.xSlot j ∨ i = A.indexing.shape.ySlot j)

theorem card_specialIdx : (specialIdx A).card ≤ 5 := by
  have hn : A.indexing.shape.n ≤ 2 * A.indexing.shape.m + 4 := by
    unfold Shape.n; split_ifs <;> omega
  let U : Finset (Fin A.indexing.shape.n) := Finset.univ.filter fun i => 2 * A.indexing.shape.m + 1 ≤ i.val
  let J : Finset (Fin A.indexing.shape.n) := Finset.univ.filter fun i =>
    ∃ j, A.junction = some j ∧ (i = A.indexing.shape.xSlot j ∨ i = A.indexing.shape.ySlot j)
  have hsub : specialIdx A ⊆ U ∪ J := by
    intro i hi
    unfold specialIdx at hi
    rcases (Finset.mem_filter.mp hi).2 with h | h
    · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩)
    · exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩)
  have hU : U.card ≤ 3 := by
    have : U.card ≤ (Finset.range 3).card := by
      apply Finset.card_le_card_of_injOn (fun i => i.val - (2 * A.indexing.shape.m + 1))
      · intro i hi
        have h1 := (Finset.mem_filter.mp hi).2
        have h2 := i.2
        rw [Finset.mem_coe, Finset.mem_range]
        show i.val - (2 * A.indexing.shape.m + 1) < 3
        omega
      · intro i hi j hj h
        have h1 := (Finset.mem_filter.mp hi).2
        have h2 := (Finset.mem_filter.mp hj).2
        apply Fin.ext
        simp only at h
        omega
    simpa using this
  have hJ : J.card ≤ 2 := by
    cases hj : A.junction with
    | none =>
      have : J = ∅ := by
        ext i; simp [J, hj]
      rw [this]; simp
    | some j0 =>
      have : J ⊆ {A.indexing.shape.xSlot j0, A.indexing.shape.ySlot j0} := by
        intro i hi
        obtain ⟨j, hj1, hj2⟩ := (Finset.mem_filter.mp hi).2
        rw [hj] at hj1
        have : j = j0 := (Option.some.inj hj1).symm
        subst this
        simpa using hj2
      exact (Finset.card_le_card this).trans (Finset.card_le_two)
  calc (specialIdx A).card ≤ (U ∪ J).card := Finset.card_le_card hsub
    _ ≤ U.card + J.card := Finset.card_union_le _ _
    _ ≤ 5 := by omega

/-- The special atoms. -/
def specialSet : Finset V := (specialIdx A).image (av A)

theorem card_specialSet : (specialSet A).card ≤ 5 :=
  Finset.card_image_le.trans (card_specialIdx A)

theorem fin_classify (i : Fin A.indexing.shape.n) :
    i = A.indexing.shape.x0 ∨ i ∈ specialIdx A ∨
      ∃ j, A.junction ≠ some j ∧ (i = A.indexing.shape.xSlot j ∨ i = A.indexing.shape.ySlot j) := by
  have hn : A.indexing.shape.n = 2 * A.indexing.shape.m + 1 + if X.IsBad then 0 else 3 := rfl
  have hi := i.2
  by_cases h0 : i.val = 0
  · left; exact Fin.ext (by simp [Shape.x0, h0])
  by_cases hu : 2 * A.indexing.shape.m + 1 ≤ i.val
  · right; left
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, Or.inl hu⟩
  right
  have hj : ∃ j : Fin A.indexing.shape.m, i = A.indexing.shape.xSlot j ∨ i = A.indexing.shape.ySlot j := by
    have hm1 : i.val - 1 < A.indexing.shape.m ∨ A.indexing.shape.m + 1 ≤ i.val := by omega
    rcases hm1 with h | h
    · exact ⟨⟨i.val - 1, h⟩, Or.inl (Fin.ext (by simp [Shape.xSlot]; omega))⟩
    · exact ⟨⟨i.val - A.indexing.shape.m - 1, by omega⟩, Or.inr (Fin.ext (by simp [Shape.ySlot]; omega))⟩
  obtain ⟨j, hj⟩ := hj
  by_cases hjn : A.junction = some j
  · left
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, Or.inr ⟨j, hjn, hj⟩⟩
  · right; exact ⟨j, hjn, hj⟩

theorem exists_idx {t : V} (ht : t ∈ S) (hta : t ≠ a) (htb : t ≠ b) :
    ∃ i, av A i = t ∧ i ≠ A.indexing.shape.x0 := by
  refine ⟨A.indexing.atom.symm ⟨t, Finset.mem_erase.mpr ⟨hta, ht⟩⟩, ?_, ?_⟩
  · simp [av]
  · intro h
    have := av_x0 A
    rw [← h] at this
    simp [av] at this
    exact htb this

theorem rung_bonds_nonjunction {j : Fin A.indexing.shape.m} (hj : A.junction ≠ some j) :
    M.bondsBetween (rx A j) (ry A j) = 2 := by
  have := A.rung_bonds j
  rw [if_neg hj] at this
  exact this

/-- **Rung classification.** A ladder rung `(t, s)` with a neighbouring rung `(t', s')` inside the block `S` is either a
chart rung or consists of two special atoms. -/
theorem rung_classify (hB : M.IsBlock S a b) {t s t' s' : V} (ht : t ∈ S) (hs : s ∈ S) (ht' : t' ∈ S)
    (hs' : s' ∈ S) (hta : t ≠ a) (htb : t ≠ b) (hsa : s ≠ a) (hsb : s ≠ b)
    (h_ts : t ≠ s) (h_tt' : t ≠ t') (h_st' : s ≠ t') (h_ss' : s ≠ s') (h_ts' : t ≠ s') (h_t's' : t' ≠ s')
    (hb_ts : M.bondsBetween t s = 2) (hb_tt' : M.bondsBetween t t' = 1) (hb_ss' : M.bondsBetween s s' = 1) :
    (∃ j, A.junction ≠ some j ∧ ((t = rx A j ∧ s = ry A j) ∨ (t = ry A j ∧ s = rx A j))) ∨
      (t ∈ specialSet A ∧ s ∈ specialSet A) := by
  obtain ⟨hS, -, -, -, -, -, -, -, hint, -⟩ := hB
  have hdt : M.degIn S t = 4 := hint t ht hta htb
  have hds : M.degIn S s = 4 := hint s hs hsa hsb
  obtain ⟨it, hit, hit0⟩ := exists_idx A ht hta htb
  obtain ⟨is, his, his0⟩ := exists_idx A hs hsa hsb
  have hb_st : M.bondsBetween s t = 2 := by rw [Mole.bondsBetween_symm]; exact hb_ts
  -- the case where `s` is a chart-rung atom is symmetric to the one for `t`
  have hS_case : ∀ {tt ss t'' : V} (htt : tt ∈ S) (hss : ss ∈ S) (ht'' : t'' ∈ S) (hd : M.degIn S tt = 4)
      (h1 : tt ≠ ss) (h2 : tt ≠ t'') (h3 : ss ≠ t'') (hb1 : M.bondsBetween tt ss = 2)
      (hb2 : M.bondsBetween tt t'' = 1) (i : Fin A.indexing.shape.n) (hi : av A i = tt)
      (hi0 : i ≠ A.indexing.shape.x0),
      (∃ j, A.junction ≠ some j ∧ ((tt = rx A j ∧ ss = ry A j) ∨ (tt = ry A j ∧ ss = rx A j))) ∨ tt ∈ specialSet A := by
    intro tt ss t'' htt hss ht'' hd h1 h2 h3 hb1 hb2 i hi hi0
    rcases fin_classify A i with h | h | ⟨j, hj, h | h⟩
    · exact absurd h hi0
    · right; exact Finset.mem_image.mpr ⟨i, h, hi⟩
    · left
      have hrx : tt = rx A j := by rw [← hi, h]; rfl
      have hr : M.bondsBetween tt (ry A j) = 2 := by rw [hrx]; exact rung_bonds_nonjunction A hj
      have hne : tt ≠ ry A j := by rw [hrx]; exact rx_ne_ry A j
      exact ⟨j, hj, Or.inl ⟨hrx, rung_partner_eq htt hss ht'' (av_mem A _).1 hd h1 h2 h3 hne hb1 hb2 hr⟩⟩
    · left
      have hry : tt = ry A j := by rw [← hi, h]; rfl
      have hr : M.bondsBetween tt (rx A j) = 2 := by
        rw [hry, Mole.bondsBetween_symm]; exact rung_bonds_nonjunction A hj
      have hne : tt ≠ rx A j := by rw [hry]; exact (rx_ne_ry A j).symm
      exact ⟨j, hj, Or.inr ⟨hry, rung_partner_eq htt hss ht'' (av_mem A _).1 hd h1 h2 h3 hne hb1 hb2 hr⟩⟩
  rcases hS_case ht hs ht' hdt h_ts h_tt' h_st' hb_ts hb_tt' it hit hit0 with h | h
  · left; exact h
  · rcases hS_case hs ht hs' hds h_ts.symm h_ss' h_ts' hb_st hb_ss' is his his0 with h' | h'
    · left
      obtain ⟨j, hj, hh⟩ := h'
      exact ⟨j, hj, hh.symm.imp (fun h => ⟨h.2, h.1⟩) (fun h => ⟨h.2, h.1⟩)⟩
    · right; exact ⟨h, h'⟩

end Chart

end WaveTurbulence.VineCount
