/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.FinalCount.GhostSlab
/-! G2-GHOST part 2: structure of a triangle with ghosts (atoms of degree `2`, already cut).  A ghost leaves
an isolated `f j`; this forces the `α/β` pattern of the cuts (DH23 L1777). -/
@[expose] public section
set_option autoImplicit false
set_option linter.unusedSectionVars false
open Finset Classical
namespace WaveTurbulence.FinalCount
open WaveTurbulence

variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D] {d : ℕ}

/-- The component of a dartless atom is a singleton. -/
theorem sc_isolated {N : Molecule V D} {v : V} (hv : ∀ x, N.atom x ≠ v) {a : V} (h : N.SameComponent a v) :
    a = v := by
  have key : ∀ x y : V, Relation.EqvGen N.Adj x y → (x = y ∨ (x ≠ v ∧ y ≠ v)) := by
    intro x y hxy
    induction hxy with
    | rel x y hxy =>
      right
      obtain ⟨z, hz1, hz2⟩ := hxy
      exact ⟨hz1 ▸ hv z, hz2 ▸ hv _⟩
    | refl => left; rfl
    | symm x y _ ih =>
      rcases ih with h | h
      · left; exact h.symm
      · right; exact ⟨h.2, h.1⟩
    | trans x y z _ _ ih1 ih2 =>
      rcases ih1 with h1 | h1
      · subst h1; exact ih2
      · rcases ih2 with h2 | h2
        · subst h2; right; exact h1
        · right; exact ⟨h1.1, h2.2⟩
  rcases key a v h with h' | h'
  · exact h'
  · exact absurd rfl h'.2

/-- A closed atom set contains the whole component of each of its atoms. -/
theorem IsClosedSet.sc {N : Molecule V D} {S : Finset V} (hS : IsClosedSet N S) {a b : V}
    (ha : a ∈ S) (h : N.SameComponent a b) : b ∈ S := by
  have key : ∀ x y : V, Relation.EqvGen N.Adj x y → (x ∈ S ↔ y ∈ S) := by
    intro x y hxy
    induction hxy with
    | rel x y hxy =>
      obtain ⟨z, hz1, hz2⟩ := hxy
      constructor
      · intro hx; exact hz2 ▸ hS z (hz1 ▸ hx)
      · intro hy
        have h1 : N.atom (N.mate z) ∈ S := hz2 ▸ hy
        have h2 := hS (N.mate z) h1
        rw [N.mate_mate] at h2
        exact hz1 ▸ h2
    | refl => exact Iff.rfl
    | symm x y _ ih => exact ih.symm
    | trans x y z _ _ ih1 ih2 => exact ih1.trans ih2
  exact (key a b h).1 ha

namespace TriData
variable {M : Molecule V D} (T : TriData M)

theorem a_ne_b (j : Fin 3) : T.a j ≠ T.b j := by
  intro e; have h1 := T.out_a j; have h2 := T.out_b j; rw [e] at h1; rw [h1] at h2; exact Bool.false_ne_true h2

/-- An atom of degree `≤ 2` of the triangle has only the two triangle darts. -/
theorem dart_ab_of_deg (j : Fin 3) (hd : M.deg (T.t j) ≤ 2) {x : D} (hx : M.atom x = T.t j) :
    x = T.a j ∨ x = T.b j := by
  by_contra hcon
  push Not at hcon
  have hsub : ({x, T.a j, T.b j} : Finset D) ⊆ M.dartsAt (T.t j) := by
    intro y hy
    rw [mem_dartsAt]
    simp only [Finset.mem_insert, Finset.mem_singleton] at hy
    rcases hy with rfl | rfl | rfl
    exacts [hx, T.atom_a j, T.atom_b j]
  have hc : ({x, T.a j, T.b j} : Finset D).card = 3 := by
    rw [Finset.card_insert_of_notMem, Finset.card_pair (T.a_ne_b j)]
    simp [hcon.1, hcon.2]
  have := Finset.card_le_card hsub
  unfold Molecule.deg at hd
  omega

theorem m1_atom_t (j : Fin 3) (hj : j ≠ 0) (x : D) : T.m1.atom x = T.t j ↔ M.atom x = T.t j := by
  rw [m1_atom]
  split_ifs with hc
  · constructor
    · intro h; exact absurd h (T.f_ne_t 0 j)
    · intro h; exact absurd (hc.1.symm.trans h |> T.t_inj) (Ne.symm hj)
  · exact Iff.rfl

theorem m1_dartless0 (hd : M.deg (T.t 0) ≤ 2) : ∀ x, T.m1.atom x ≠ T.f 0 := by
  intro x
  rw [m1_atom]
  split_ifs with hc
  · exfalso
    rcases T.dart_ab_of_deg 0 hd hc.1 with h | h
    exacts [hc.2.1 h, hc.2.2 h]
  · exact fun e => T.f_fresh 0 (e ▸ M.atom_mem x)

theorem m2_dartless1 (hd : M.deg (T.t 1) ≤ 2) : ∀ x, T.m2.atom x ≠ T.f 1 := by
  intro x
  rw [m2_atom]
  split_ifs with hc
  · exfalso
    have h1 : M.atom x = T.t 1 := (T.m1_atom_t 1 (by decide) x).1 hc.1
    rcases T.dart_ab_of_deg 1 hd h1 with h | h
    exacts [hc.2.1 h, hc.2.2 h]
  · exact fun e => T.f_fresh_m1 (e ▸ T.m1.atom_mem x)

/-- A ghost at `v₁` makes the first cut a `β`-cut. -/
theorem not_isA0_of_ghost (hd : M.deg (T.t 0) ≤ 2) : ¬ T.IsA0 := by
  intro h
  have h1 : T.m1.SameComponent (T.t 0) (T.f 0) := (isAlphaCut_iff M T.cd1).1 h
  exact T.f_ne_t 0 0 (sc_isolated (T.m1_dartless0 hd) h1).symm

/-- A ghost at `v₂` makes the second cut a `β`-cut. -/
theorem not_isA1_of_ghost1 (hd : M.deg (T.t 1) ≤ 2) : ¬ T.IsA1 := by
  intro h
  have h1 : T.m2.SameComponent (T.t 1) (T.f 1) := (isAlphaCut_iff T.m1 T.cd2).1 h
  exact T.f_ne_t 1 1 (sc_isolated (T.m2_dartless1 hd) h1).symm

theorem m2_atom_eq_t (j : Fin 3) (hj : j ≠ 2) (x : D) (h : T.m2.atom x = T.t j) : x = T.a j ∨ x = T.b j := by
  rw [m2_atom] at h
  split_ifs at h with hc
  · exact absurd h (T.f_ne_t 1 j)
  · fin_cases j
    · rw [m1_atom] at h
      split_ifs at h with hc0
      · exact absurd h (T.f_ne_t 0 0)
      · by_contra hcon
        push Not at hcon
        exact hc0 ⟨h, hcon.1, hcon.2⟩
    · by_contra hcon
      push Not at hcon
      exact hc ⟨h, hcon.1, hcon.2⟩
    · exact absurd rfl hj

theorem m2_atom_t2 (x : D) (h : T.m2.atom x = T.t 2) : M.atom x = T.t 2 := by
  rw [m2_atom] at h
  split_ifs at h with hc
  · exact absurd h (T.f_ne_t 1 2)
  · rw [m1_atom] at h
    split_ifs at h with hc0
    · exact absurd h (T.f_ne_t 0 2)
    · exact h

theorem m2_mate (x : D) : T.m2.mate x = M.mate x := rfl

/-- If `v₃` has degree `≤ 2`, the triangle is a closed atom set of `m2`. -/
theorem blob_closed_m2 (hd2 : M.deg (T.t 2) ≤ 2) : IsClosedSet T.m2 (Finset.univ.image T.t) := by
  intro x hx
  rw [Finset.mem_image] at hx ⊢
  obtain ⟨j, -, hj⟩ := hx
  have hx' : x = T.a j ∨ x = T.b j := by
    by_cases hj2 : j = 2
    · subst hj2
      exact T.dart_ab_of_deg 2 hd2 (T.m2_atom_t2 x hj.symm)
    · exact T.m2_atom_eq_t j hj2 x hj.symm
  rcases hx' with rfl | rfl
  · refine ⟨j - 1, Finset.mem_univ _, ?_⟩
    have hm : M.mate (T.a j) = T.b (j - 1) := by
      have := T.mate_a (j - 1); rwa [sub_add_cancel] at this
    rw [T.m2_mate, hm]
    exact (T.m2_atom_tri _ (j - 1) (Or.inr rfl)).symm
  · refine ⟨j + 1, Finset.mem_univ _, ?_⟩
    rw [T.m2_mate, T.mate_b]
    exact (T.m2_atom_tri _ (j + 1) (Or.inl rfl)).symm

/-- A ghost at `v₃` makes the second cut a `β`-cut. -/
theorem not_isA1_of_ghost2 (hd2 : M.deg (T.t 2) ≤ 2) : ¬ T.IsA1 := by
  intro h
  have h1 : T.m2.SameComponent (T.t 1) (T.f 1) := (isAlphaCut_iff T.m1 T.cd2).1 h
  have hB := T.blob_closed_m2 hd2
  have := hB.sc (Finset.mem_image.2 ⟨1, Finset.mem_univ _, rfl⟩) h1
  obtain ⟨j, -, hj⟩ := Finset.mem_image.1 this
  exact T.f_ne_t 1 j hj.symm

/-- A ghost at `v₃` and an `α`-cut at `v₁`: the first fresh atom is connected to the second one in `m2`. -/
theorem sc_f0_f1_of_ghost2 (hd2 : M.deg (T.t 2) ≤ 2) (hA0 : T.IsA0) : T.m2.SameComponent (T.f 0) (T.f 1) := by
  by_contra hn
  have hB := T.blob_closed_m2 hd2
  have hYc : IsClosedSet T.m2 (T.m2.atoms.filter fun a => T.m2.SameComponent a (T.f 0)) :=
    isClosedSet_comp T.m2 (T.f 0)
  set Y := T.m2.atoms.filter fun a => T.m2.SameComponent a (T.f 0) with hY
  have hf0 : T.f 0 ∈ Y := by
    rw [hY, Finset.mem_filter]
    exact ⟨by rw [m2_atoms]; exact Finset.mem_insert_of_mem (Finset.mem_insert_self _ _), Relation.EqvGen.refl _⟩
  have hBY : ∀ j, T.t j ∉ Y := by
    intro j hj
    have h1 : T.m2.SameComponent (T.t j) (T.f 0) := (Finset.mem_filter.1 hj).2
    have := hB.sc (Finset.mem_image.2 ⟨j, Finset.mem_univ _, rfl⟩) h1
    obtain ⟨i, -, hi⟩ := Finset.mem_image.1 this
    exact T.f_ne_t 0 i hi.symm
  have hf1 : T.f 1 ∉ Y := by
    intro h
    exact hn (Relation.EqvGen.symm _ _ (Finset.mem_filter.1 h).2)
  have hYm1 : IsClosedSet T.m1 Y := by
    intro x hx
    have hne1 : T.m1.atom x ≠ T.t 1 := fun e => hBY 1 (e ▸ hx)
    have e1 : T.m2.atom x = T.m1.atom x := by
      rw [m2_atom, if_neg]; intro hc; exact hne1 hc.1
    have hmate := hYc x (e1 ▸ hx)
    by_cases hc : T.m1.atom (T.m1.mate x) = T.t 1 ∧ T.m1.mate x ≠ T.a 1 ∧ T.m1.mate x ≠ T.b 1
    · exfalso
      have : T.m2.atom (T.m2.mate x) = T.f 1 := by
        show T.m2.atom (T.m1.mate x) = T.f 1
        rw [m2_atom, if_pos hc]
      rw [this] at hmate
      exact hf1 hmate
    · have : T.m2.atom (T.m2.mate x) = T.m1.atom (T.m1.mate x) := by
        show T.m2.atom (T.m1.mate x) = _
        rw [m2_atom, if_neg hc]
      rw [← this]; exact hmate
  have h1 : T.m1.SameComponent (T.t 0) (T.f 0) := (isAlphaCut_iff M T.cd1).1 hA0
  have := hYm1.sc hf0 (Relation.EqvGen.symm _ _ h1)
  exact hBY 0 this

end TriData
end WaveTurbulence.FinalCount
