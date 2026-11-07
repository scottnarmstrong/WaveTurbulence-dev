/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.FinalCount.G3EraseDev1
/-! **FINALCOUNT-G3: the flux dichotomy of an erasure** (R27, research-remtame-i L1, L2).

`sgnC C` is the net signed number of bonds from `v` into the component `C` of `M - v`.  `Pinned M v`: some component meeting `v`
has `sgnC ≠ 0`.  If `deg v = 3` then `v` is pinned; if `deg v = 4` then `v` is pinned or at most two components of `M - v` meet
`v`. -/
@[expose] public section
set_option autoImplicit false
set_option linter.unusedSectionVars false
open Finset Classical
namespace WaveTurbulence.FinalCountG3
open WaveTurbulence WaveTurbulence.FinalCount

variable {V : Type*} [DecidableEq V] {D : Type*} [Fintype D] [DecidableEq D] (M : Molecule V D) (v : V)

/-- The darts of `C` whose bond goes to `v`. -/
noncomputable def crossD (C : Finset V) : Finset D := Finset.univ.filter (fun x => M.atom x ∈ C ∧ M.atom (M.mate x) = v)

/-- The net sign of the bonds between `v` and `C`. -/
noncomputable def sgnC (C : Finset V) : ℝ := ∑ x ∈ crossD M v C, M.dartSign x

/-- **`v` is pinned**: some component of `M - v` meeting `v` receives a nonzero net flux from `v`. -/
def Pinned : Prop := ∃ a ∈ nbr M v, sgnC M v (cmp M v a) ≠ 0

variable {M v}

theorem dartSign_cases (x : D) : M.dartSign x = 1 ∨ M.dartSign x = -1 := by
  unfold Molecule.dartSign; split_ifs <;> simp

theorem dartSign_mate (x : D) : M.dartSign (M.mate x) = - M.dartSign x := by
  unfold Molecule.dartSign
  have := M.out_mate x
  cases h : M.out x <;> cases h2 : M.out (M.mate x) <;> simp_all

theorem crossD_ne_empty (hnl : ∀ x, M.atom x ≠ M.atom (M.mate x)) {a : V} (ha : a ∈ nbr M v) :
    1 ≤ (crossD M v (cmp M v a)).card := by
  obtain ⟨x, hx1, hx2⟩ := (mem_nbr.1 ha).2
  refine Finset.card_pos.2 ⟨M.mate x, ?_⟩
  unfold crossD
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  refine ⟨mem_cmp.2 ⟨(mem_nbr.1 ha).1, Relation.EqvGen.refl _⟩ |> fun h => ?_, ?_⟩
  · rw [hx2]; exact h
  · rw [M.mate_mate]; exact hx1

theorem mem_crossD_nbr (hnl : ∀ x, M.atom x ≠ M.atom (M.mate x)) (hv : v ∈ M.atoms) {x : D}
    (hx : M.atom (M.mate x) = v) : M.atom x ∈ nbr M v := by
  refine mem_nbr.2 ⟨Finset.mem_erase.2 ⟨?_, M.atom_mem _⟩, ⟨M.mate x, hx, by rw [M.mate_mate]⟩⟩
  intro e; exact hnl x (e.trans hx.symm)

theorem crossD_disjoint {C C' : Finset V} (hC : C ∈ Cs M v) (hC' : C' ∈ Cs M v) (hne : C ≠ C') :
    Disjoint (crossD M v C) (crossD M v C') := by
  rw [Finset.disjoint_left]
  intro x hx hx'
  unfold crossD at hx hx'
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx hx'
  unfold Cs at hC hC'
  obtain ⟨a, -, rfl⟩ := Finset.mem_image.1 hC
  obtain ⟨b, -, rfl⟩ := Finset.mem_image.1 hC'
  have h1 := (mem_cmp.1 hx.1).2
  have h2 := (mem_cmp.1 hx'.1).2
  exact hne ((cmp_eq_of_sc h1).trans (cmp_eq_of_sc h2).symm)

theorem biUnion_crossD (hnl : ∀ x, M.atom x ≠ M.atom (M.mate x)) (hv : v ∈ M.atoms) :
    (Cs M v).biUnion (crossD M v) = Finset.univ.filter (fun x => M.atom (M.mate x) = v) := by
  ext x
  simp only [Finset.mem_biUnion, Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨C, -, hx⟩
    unfold crossD at hx
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx
    exact hx.2
  · intro hx
    refine ⟨cmp M v (M.atom x), ?_, ?_⟩
    · unfold Cs; exact Finset.mem_image.2 ⟨_, mem_crossD_nbr hnl hv hx, rfl⟩
    · unfold crossD
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨mem_cmp.2 ⟨(mem_nbr.1 (mem_crossD_nbr hnl hv hx)).1, Relation.EqvGen.refl _⟩, hx⟩

theorem sum_cs_card (hnl : ∀ x, M.atom x ≠ M.atom (M.mate x)) (hv : v ∈ M.atoms) :
    ∑ C ∈ Cs M v, (crossD M v C).card = M.deg v := by
  rw [← Finset.card_biUnion (fun C hC C' hC' hne => crossD_disjoint hC hC' hne), biUnion_crossD hnl hv]
  unfold Molecule.deg
  refine Finset.card_bij (fun x _ => M.mate x) ?_ ?_ ?_
  · intro x hx; simp [Molecule.dartsAt] at hx ⊢; exact hx
  · intro x _ y _ e; simpa [M.mate_mate] using congrArg M.mate e
  · intro y hy
    refine ⟨M.mate y, ?_, M.mate_mate y⟩
    simp [Molecule.dartsAt] at hy ⊢; rw [M.mate_mate]; exact hy

theorem sum_cs_sgn (hnl : ∀ x, M.atom x ≠ M.atom (M.mate x)) (hv : v ∈ M.atoms) :
    ∑ C ∈ Cs M v, sgnC M v C = - ∑ y ∈ M.dartsAt v, M.dartSign y := by
  unfold sgnC
  rw [← Finset.sum_biUnion (fun C hC C' hC' hne => crossD_disjoint hC hC' hne), biUnion_crossD hnl hv]
  rw [← Finset.sum_neg_distrib]
  refine Finset.sum_bij (fun x _ => M.mate x) ?_ ?_ ?_ ?_
  · intro x hx; simp [Molecule.dartsAt] at hx ⊢; exact hx
  · intro x _ y _ e; simpa [M.mate_mate] using congrArg M.mate e
  · intro y hy
    refine ⟨M.mate y, ?_, M.mate_mate y⟩
    simp [Molecule.dartsAt] at hy ⊢; rw [M.mate_mate]; exact hy
  · intro x _; rw [dartSign_mate]; simp

theorem sum_dartSign_dartsAt (a : V) :
    ∑ y ∈ M.dartsAt a, M.dartSign y = (M.outdeg a : ℝ) - M.indeg a := by
  unfold Molecule.outdeg Molecule.indeg
  have h := Finset.sum_filter_add_sum_filter_not (M.dartsAt a) (fun x => M.out x = true) (fun y => M.dartSign y)
  have e1 : ∑ x ∈ (M.dartsAt a).filter (fun x => M.out x = true), M.dartSign x =
      (((M.dartsAt a).filter fun x => M.out x = true).card : ℝ) := by
    rw [Finset.card_eq_sum_ones, Nat.cast_sum]
    refine Finset.sum_congr rfl fun x hx => ?_
    have := (Finset.mem_filter.1 hx).2
    simp [Molecule.dartSign, this]
  have e2 : ∑ x ∈ (M.dartsAt a).filter (fun x => ¬ M.out x = true), M.dartSign x =
      -(((M.dartsAt a).filter fun x => M.out x = false).card : ℝ) := by
    rw [Finset.card_eq_sum_ones, Nat.cast_sum, ← Finset.sum_neg_distrib]
    have hf : (M.dartsAt a).filter (fun x => M.out x = false) = (M.dartsAt a).filter (fun x => ¬ M.out x = true) := by
      ext x; simp
    rw [hf]
    refine Finset.sum_congr rfl fun x hx => ?_
    have := (Finset.mem_filter.1 hx).2
    simp [Molecule.dartSign, this]
  rw [← h, e1, e2]; ring

theorem pinned_of_deg3 (hnl : ∀ x, M.atom x ≠ M.atom (M.mate x)) (hv : v ∈ M.atoms)
    (hb : M.outdeg v ≤ 2 ∧ M.indeg v ≤ 2) (hd : M.deg v = 3) : Pinned M v := by
  by_contra hP
  have h0 : ∀ C ∈ Cs M v, sgnC M v C = 0 := by
    intro C hC
    unfold Cs at hC
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.1 hC
    by_contra hne; exact hP ⟨a, ha, hne⟩
  have hs := sum_cs_sgn hnl hv
  rw [Finset.sum_eq_zero h0, sum_dartSign_dartsAt] at hs
  have hsum : M.outdeg v + M.indeg v = M.deg v := by
    unfold Molecule.outdeg Molecule.indeg Molecule.deg
    have := Finset.card_filter_add_card_filter_not (s := M.dartsAt v) (fun x => M.out x = true)
    have hf : (M.dartsAt v).filter (fun x => M.out x = false) = (M.dartsAt v).filter (fun x => ¬ M.out x = true) := by
      ext x; simp
    rw [hf]; exact this
  have : (M.outdeg v : ℝ) = M.indeg v := by linarith
  have : M.outdeg v = M.indeg v := by exact_mod_cast this
  omega

theorem card_cross_even {C : Finset V} (h : sgnC M v C = 0) : Even (crossD M v C).card := by
  unfold sgnC at h
  set T := crossD M v C
  have hpn := Finset.card_filter_add_card_filter_not (s := T) (fun x => M.dartSign x = 1)
  have e1 : ∑ x ∈ T.filter (fun x => M.dartSign x = 1), M.dartSign x = ((T.filter fun x => M.dartSign x = 1).card : ℝ) := by
    rw [Finset.card_eq_sum_ones, Nat.cast_sum]
    exact Finset.sum_congr rfl fun x hx => by simpa using (Finset.mem_filter.1 hx).2
  have e2 : ∑ x ∈ T.filter (fun x => ¬ M.dartSign x = 1), M.dartSign x = -((T.filter fun x => ¬ M.dartSign x = 1).card : ℝ) := by
    rw [Finset.card_eq_sum_ones, Nat.cast_sum, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun x hx => ?_
    have := (Finset.mem_filter.1 hx).2
    rcases dartSign_cases (M := M) x with h1 | h1
    · exact absurd h1 this
    · simp [h1]
  have h2 := Finset.sum_filter_add_sum_filter_not T (fun x => M.dartSign x = 1) (fun x => M.dartSign x)
  rw [e1, e2, h] at h2
  have : (T.filter fun x => M.dartSign x = 1).card = (T.filter fun x => ¬ M.dartSign x = 1).card := by
    exact_mod_cast (by linarith : ((T.filter fun x => M.dartSign x = 1).card : ℝ) = (T.filter fun x => ¬ M.dartSign x = 1).card)
  exact ⟨(T.filter fun x => M.dartSign x = 1).card, by omega⟩

theorem cs_card_le_two (hnl : ∀ x, M.atom x ≠ M.atom (M.mate x)) (hv : v ∈ M.atoms) (hd : M.deg v = 4)
    (hP : ¬ Pinned M v) : (Cs M v).card ≤ 2 := by
  have h0 : ∀ C ∈ Cs M v, sgnC M v C = 0 := by
    intro C hC
    unfold Cs at hC
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.1 hC
    by_contra hne; exact hP ⟨a, ha, hne⟩
  have h2 : ∀ C ∈ Cs M v, 2 ≤ (crossD M v C).card := by
    intro C hC
    have hev := card_cross_even (h0 C hC)
    unfold Cs at hC
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.1 hC
    have := crossD_ne_empty hnl ha
    obtain ⟨k, hk⟩ := hev
    omega
  have := Finset.card_nsmul_le_sum (Cs M v) (fun C => (crossD M v C).card) 2 h2
  rw [sum_cs_card hnl hv, hd] at this
  simp at this; omega

theorem cs_card_le_deg (hnl : ∀ x, M.atom x ≠ M.atom (M.mate x)) (hv : v ∈ M.atoms) :
    (Cs M v).card ≤ M.deg v := by
  have h1 : ∀ C ∈ Cs M v, 1 ≤ (crossD M v C).card := by
    intro C hC
    unfold Cs at hC
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.1 hC
    exact crossD_ne_empty hnl ha
  have := Finset.card_nsmul_le_sum (Cs M v) (fun C => (crossD M v C).card) 1 h1
  rw [sum_cs_card hnl hv] at this
  simpa using this

theorem cs_card_pos (hnl : ∀ x, M.atom x ≠ M.atom (M.mate x)) (hv : v ∈ M.atoms) (hd : 1 ≤ M.deg v) :
    1 ≤ (Cs M v).card := by
  obtain ⟨a, ha⟩ := exists_nbr hnl hv hd
  exact Finset.card_pos.2 ⟨cmp M v a, Finset.mem_image.2 ⟨a, ha, rfl⟩⟩

end WaveTurbulence.FinalCountG3
