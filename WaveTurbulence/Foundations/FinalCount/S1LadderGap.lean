/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.FinalCount.S1Gaps
public import WaveTurbulence.Foundations.Molecule.MoleculeBondsBetween
import Mathlib.Tactic

/-!
# TARGET defdiff (L1940): the gap of a ladder is well defined up to sign

For a ladder of length `m ≥ 1` and a decoration with `c_v = 0` at degree-four atoms, the difference
`k_ℓ - k_ℓ'` of any pair of parallel single bonds (rail `j` between the `j`-th and `(j+1)`-st rung)
has the same norm for all `j`.  This is the statement "the difference must be equal (up to a sign
change)" of the source; it follows from conservation at the two atoms of an interior rung and the
opposite directions of the two rails.
-/

@[expose] public section
set_option autoImplicit false
set_option linter.unusedSectionVars false
namespace WaveTurbulence.Stage1
open Finset

variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D] {M : Molecule V D} {d : ℕ}

/-- The gap of the `j`-th pair of parallel rails (darts based at the lower rung atoms). -/
@[expose] def IsRailGap (M : Molecule V D) {m : ℕ} (L : ℝ) (w : Mom d) (κ : D → (Fin d → ℤ))
    (u v : Fin (m + 1) → V) (j : Fin m) (r : Mom d) : Prop :=
  ∃ x y, M.ends x = s(u j.castSucc, u j.succ) ∧ M.ends y = s(v j.castSucc, v j.succ) ∧
    M.atom x = u j.castSucc ∧ M.atom y = v j.castSucc ∧ r = Molecule.gapAt L w κ x y

theorem uniq_dart {a b : V} (hab : a ≠ b) (h : M.bondsBetween a b = 1) {x x' : D}
    (hx : M.atom x = a) (hx' : M.atom (M.mate x) = b) (hy : M.atom x' = a)
    (hy' : M.atom (M.mate x') = b) : x = x' := by
  rw [Mole.bondsBetween_eq_card_darts M hab] at h
  obtain ⟨z, hz⟩ := Finset.card_eq_one.mp h
  have h1 : x ∈ (M.dartsAt a).filter (fun x => M.atom (M.mate x) = b) :=
    Finset.mem_filter.mpr ⟨(Mole.mem_dartsAt M a x).mpr hx, hx'⟩
  have h2 : x' ∈ (M.dartsAt a).filter (fun x => M.atom (M.mate x) = b) :=
    Finset.mem_filter.mpr ⟨(Mole.mem_dartsAt M a x').mpr hy, hy'⟩
  rw [hz] at h1 h2
  rw [Finset.mem_singleton.mp h1, Finset.mem_singleton.mp h2]

theorem exists_dart {a b : V} (hab : a ≠ b) (h : 0 < M.bondsBetween a b) :
    ∃ x, M.atom x = a ∧ M.atom (M.mate x) = b := by
  rw [Mole.bondsBetween_eq_card_darts M hab] at h
  obtain ⟨x, hx⟩ := Finset.card_pos.mp h
  obtain ⟨h1, h2⟩ := Finset.mem_filter.mp hx
  exact ⟨x, (Mole.mem_dartsAt M a x).mp h1, h2⟩

/-- Conservation at the two atoms of an interior rung: the rung darts cancel. -/
theorem rung_conservation {E : Type*} [AddCommGroup E] [Module ℝ E] {k : D → E}
    (hk : ∀ x, k (M.mate x) = k x) {p q p1 p2 q1 q2 : V}
    (hpq : M.bondsBetween p q = 2) (hp1 : M.bondsBetween p p1 = 1) (hp2 : M.bondsBetween p p2 = 1)
    (hq1 : M.bondsBetween q q1 = 1) (hq2 : M.bondsBetween q q2 = 1)
    (hqp1 : q ≠ p1) (hqp2 : q ≠ p2) (hp12 : p1 ≠ p2) (hpq1 : p ≠ q1) (hpq2 : p ≠ q2) (hq12 : q1 ≠ q2)
    (hpq' : p ≠ q) (hpp1 : p ≠ p1) (hpp2 : p ≠ p2) (hqq1 : q ≠ q1) (hqq2 : q ≠ q2)
    (hdp : M.deg p = 4) (hdq : M.deg q = 4)
    (hcp : ∑ x ∈ M.dartsAt p, M.dartSign x • k x = 0)
    (hcq : ∑ x ∈ M.dartsAt q, M.dartSign x • k x = 0) :
    ∃ x1 x2 y1 y2 : D, M.atom x1 = p ∧ M.atom (M.mate x1) = p1 ∧ M.atom x2 = p ∧
      M.atom (M.mate x2) = p2 ∧ M.atom y1 = q ∧ M.atom (M.mate y1) = q1 ∧ M.atom y2 = q ∧
      M.atom (M.mate y2) = q2 ∧
      M.dartSign x1 • k x1 + M.dartSign x2 • k x2 + M.dartSign y1 • k y1 + M.dartSign y2 • k y2 = 0 := by
  classical
  obtain ⟨x1, hx1, hx1'⟩ := exists_dart hpp1 (by omega : 0 < M.bondsBetween p p1)
  obtain ⟨x2, hx2, hx2'⟩ := exists_dart hpp2 (by omega : 0 < M.bondsBetween p p2)
  obtain ⟨y1, hy1, hy1'⟩ := exists_dart hqq1 (by omega : 0 < M.bondsBetween q q1)
  obtain ⟨y2, hy2, hy2'⟩ := exists_dart hqq2 (by omega : 0 < M.bondsBetween q q2)
  refine ⟨x1, x2, y1, y2, hx1, hx1', hx2, hx2', hy1, hy1', hy2, hy2', ?_⟩
  let f : D → E := fun x => M.dartSign x • k x
  -- decomposition of the darts at an atom `p` by the atom of the mate
  have decomp : ∀ (p a b c : V), M.deg p = 4 → M.bondsBetween p a = 2 → M.bondsBetween p b = 1 →
      M.bondsBetween p c = 1 → a ≠ b → a ≠ c → b ≠ c → p ≠ a → p ≠ b → p ≠ c →
      (M.dartsAt p) = ((M.dartsAt p).filter (fun x => M.atom (M.mate x) = a)) ∪
        ((M.dartsAt p).filter (fun x => M.atom (M.mate x) = b)) ∪
        ((M.dartsAt p).filter (fun x => M.atom (M.mate x) = c)) := by
    intro p a b c hd ha hb hc hab hac hbc hpa hpb hpc
    have ca := (Mole.bondsBetween_eq_card_darts M hpa).symm.trans ha
    have cb := (Mole.bondsBetween_eq_card_darts M hpb).symm.trans hb
    have cc := (Mole.bondsBetween_eq_card_darts M hpc).symm.trans hc
    symm
    apply Finset.eq_of_subset_of_card_le
    · intro x hx
      rcases Finset.mem_union.mp hx with h | h
      · rcases Finset.mem_union.mp h with h | h <;> exact (Finset.mem_filter.mp h).1
      · exact (Finset.mem_filter.mp h).1
    · have hd1 : Disjoint ((M.dartsAt p).filter (fun x => M.atom (M.mate x) = a))
          ((M.dartsAt p).filter (fun x => M.atom (M.mate x) = b)) := by
        rw [Finset.disjoint_left]
        intro x h1 h2
        exact hab ((Finset.mem_filter.mp h1).2.symm.trans (Finset.mem_filter.mp h2).2)
      have hd2 : Disjoint (((M.dartsAt p).filter (fun x => M.atom (M.mate x) = a)) ∪
          ((M.dartsAt p).filter (fun x => M.atom (M.mate x) = b)))
          ((M.dartsAt p).filter (fun x => M.atom (M.mate x) = c)) := by
        rw [Finset.disjoint_left]
        intro x h1 h2
        rcases Finset.mem_union.mp h1 with h | h
        · exact hac ((Finset.mem_filter.mp h).2.symm.trans (Finset.mem_filter.mp h2).2)
        · exact hbc ((Finset.mem_filter.mp h).2.symm.trans (Finset.mem_filter.mp h2).2)
      rw [Finset.card_union_of_disjoint hd2, Finset.card_union_of_disjoint hd1, ca, cb, cc]
      change 2 + 1 + 1 ≥ M.deg p
      omega
  have hP := decomp p q p1 p2 hdp hpq hp1 hp2 hqp1 hqp2 hp12 hpq' hpp1 hpp2
  have hQ := decomp q p q1 q2 hdq (by rw [Mole.bondsBetween_symm M]; exact hpq) hq1 hq2
    hpq1 hpq2 hq12 (Ne.symm hpq') hqq1 hqq2
  -- singleton filters
  have single : ∀ (a b : V) (z : D), a ≠ b → M.bondsBetween a b = 1 → M.atom z = a →
      M.atom (M.mate z) = b → (M.dartsAt a).filter (fun x => M.atom (M.mate x) = b) = {z} := by
    intro a b z hab hb hz hz'
    have := (Mole.bondsBetween_eq_card_darts M hab).symm.trans hb
    obtain ⟨z', hz''⟩ := Finset.card_eq_one.mp this
    have hzmem : z ∈ (M.dartsAt a).filter (fun x => M.atom (M.mate x) = b) :=
      Finset.mem_filter.mpr ⟨(Mole.mem_dartsAt M a z).mpr hz, hz'⟩
    rw [hz''] at hzmem ⊢
    rw [Finset.mem_singleton.mp hzmem]
  have s1 := single p p1 x1 hpp1 hp1 hx1 hx1'
  have s2 := single p p2 x2 hpp2 hp2 hx2 hx2'
  have t1 := single q q1 y1 hqq1 hq1 hy1 hy1'
  have t2 := single q q2 y2 hqq2 hq2 hy2 hy2'
  -- disjointness of the three pieces
  have dsj : ∀ (p a b c : V), a ≠ b → a ≠ c → b ≠ c →
      Disjoint ((M.dartsAt p).filter (fun x => M.atom (M.mate x) = a)) ((M.dartsAt p).filter (fun x => M.atom (M.mate x) = b)) ∧
      Disjoint (((M.dartsAt p).filter (fun x => M.atom (M.mate x) = a)) ∪ ((M.dartsAt p).filter (fun x => M.atom (M.mate x) = b)))
        ((M.dartsAt p).filter (fun x => M.atom (M.mate x) = c)) := by
    intro p a b c hab hac hbc
    refine ⟨?_, ?_⟩
    · rw [Finset.disjoint_left]
      intro x h1 h2
      exact hab ((Finset.mem_filter.mp h1).2.symm.trans (Finset.mem_filter.mp h2).2)
    · rw [Finset.disjoint_left]
      intro x h1 h2
      rcases Finset.mem_union.mp h1 with h | h
      · exact hac ((Finset.mem_filter.mp h).2.symm.trans (Finset.mem_filter.mp h2).2)
      · exact hbc ((Finset.mem_filter.mp h).2.symm.trans (Finset.mem_filter.mp h2).2)
  obtain ⟨dP1, dP2⟩ := dsj p q p1 p2 hqp1 hqp2 hp12
  obtain ⟨dQ1, dQ2⟩ := dsj q p q1 q2 hpq1 hpq2 hq12
  have sumP : ∑ x ∈ M.dartsAt p, f x = ∑ x ∈ (M.dartsAt p).filter (fun x => M.atom (M.mate x) = q), f x +
      f x1 + f x2 := by
    conv_lhs => rw [hP, Finset.sum_union dP2, Finset.sum_union dP1, s1, s2]
    simp [Finset.sum_singleton, add_assoc]
  have sumQ : ∑ x ∈ M.dartsAt q, f x = ∑ x ∈ (M.dartsAt q).filter (fun x => M.atom (M.mate x) = p), f x +
      f y1 + f y2 := by
    conv_lhs => rw [hQ, Finset.sum_union dQ2, Finset.sum_union dQ1, t1, t2]
    simp [Finset.sum_singleton, add_assoc]
  -- the rung darts cancel
  have cancel : ∑ x ∈ (M.dartsAt p).filter (fun x => M.atom (M.mate x) = q), f x +
      ∑ y ∈ (M.dartsAt q).filter (fun x => M.atom (M.mate x) = p), f y = 0 := by
    have himg : ((M.dartsAt p).filter (fun x => M.atom (M.mate x) = q)).image M.mate =
        (M.dartsAt q).filter (fun x => M.atom (M.mate x) = p) := by
      ext y
      simp only [Finset.mem_image, Finset.mem_filter, Mole.mem_dartsAt]
      constructor
      · rintro ⟨x, ⟨hxa, hxb⟩, rfl⟩
        exact ⟨hxb, by rw [M.mate_mate]; exact hxa⟩
      · rintro ⟨hya, hyb⟩
        exact ⟨M.mate y, ⟨hyb, by rw [M.mate_mate]; exact hya⟩, M.mate_mate y⟩
    rw [← himg, Finset.sum_image (fun x _ y _ h => (Mole.mate_injective M) h)]
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_eq_zero
    intro x _
    simp only [f, Molecule.dartSign, M.out_mate, hk]
    cases h : M.out x <;> simp
  have h0 : (∑ x ∈ M.dartsAt p, f x) + ∑ x ∈ M.dartsAt q, f x = 0 := by
    change (∑ x ∈ M.dartsAt p, M.dartSign x • k x) + ∑ x ∈ M.dartsAt q, M.dartSign x • k x = 0
    rw [hcp, hcq, add_zero]
  rw [sumP, sumQ] at h0
  have : f x1 + f x2 + f y1 + f y2 = (∑ x ∈ (M.dartsAt p).filter (fun x => M.atom (M.mate x) = q), f x +
      f x1 + f x2) + (∑ y ∈ (M.dartsAt q).filter (fun x => M.atom (M.mate x) = p), f y + f y1 + f y2) -
      (∑ x ∈ (M.dartsAt p).filter (fun x => M.atom (M.mate x) = q), f x +
        ∑ y ∈ (M.dartsAt q).filter (fun x => M.atom (M.mate x) = p), f y) := by abel
  rw [this, h0, cancel]
  simp

/-- An atom with a double bond to `q` and single bonds to two further atoms has degree four. -/
theorem deg_eq_four_of_counts (hM : M.IsMolecule) {p q p1 p2 : V} (hp : p ∈ M.atoms)
    (hpq : M.bondsBetween p q = 2) (hp1 : M.bondsBetween p p1 = 1) (hp2 : M.bondsBetween p p2 = 1)
    (hqp1 : q ≠ p1) (hqp2 : q ≠ p2) (hp12 : p1 ≠ p2) (hpq' : p ≠ q) (hpp1 : p ≠ p1)
    (hpp2 : p ≠ p2) : M.deg p = 4 := by
  classical
  have ca := (Mole.bondsBetween_eq_card_darts M hpq').symm.trans hpq
  have cb := (Mole.bondsBetween_eq_card_darts M hpp1).symm.trans hp1
  have cc := (Mole.bondsBetween_eq_card_darts M hpp2).symm.trans hp2
  have hd1 : Disjoint ((M.dartsAt p).filter (fun x => M.atom (M.mate x) = q))
      ((M.dartsAt p).filter (fun x => M.atom (M.mate x) = p1)) := by
    rw [Finset.disjoint_left]
    intro x h1 h2
    exact hqp1 ((Finset.mem_filter.mp h1).2.symm.trans (Finset.mem_filter.mp h2).2)
  have hd2 : Disjoint (((M.dartsAt p).filter (fun x => M.atom (M.mate x) = q)) ∪
      ((M.dartsAt p).filter (fun x => M.atom (M.mate x) = p1)))
      ((M.dartsAt p).filter (fun x => M.atom (M.mate x) = p2)) := by
    rw [Finset.disjoint_left]
    intro x h1 h2
    rcases Finset.mem_union.mp h1 with h | h
    · exact hqp2 ((Finset.mem_filter.mp h).2.symm.trans (Finset.mem_filter.mp h2).2)
    · exact hp12 ((Finset.mem_filter.mp h).2.symm.trans (Finset.mem_filter.mp h2).2)
  have hsub : ((M.dartsAt p).filter (fun x => M.atom (M.mate x) = q)) ∪
      ((M.dartsAt p).filter (fun x => M.atom (M.mate x) = p1)) ∪
      ((M.dartsAt p).filter (fun x => M.atom (M.mate x) = p2)) ⊆ M.dartsAt p := by
    intro x hx
    rcases Finset.mem_union.mp hx with h | h
    · rcases Finset.mem_union.mp h with h | h <;> exact (Finset.mem_filter.mp h).1
    · exact (Finset.mem_filter.mp h).1
  have := Finset.card_le_card hsub
  rw [Finset.card_union_of_disjoint hd2, Finset.card_union_of_disjoint hd1, ca, cb, cc] at this
  have h4 := Mole.deg_le_four M hM hp
  change 2 + 1 + 1 ≤ M.deg p at this
  omega

end WaveTurbulence.Stage1
