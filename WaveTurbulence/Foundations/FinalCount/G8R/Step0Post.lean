/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.G8R.CoreTheorem
import Mathlib.Tactic

/-! # Step 0 of Prop 10.4(2)′: the post molecule of a (Y2) sequence

* no loops and no cut vertex survive (a path through the chain `Y` becomes the new bond `d → c`);
* after a sequence started at the only triple pair, no triple bond is left (or the post molecule is `Q`);
* `Q` has no pair with exactly three bonds;
* **`YReachesSmallCell`**: some complete (Y2)-route passes through a post molecule with at most four atoms that has a
  ladder cell. Otherwise the good-cell condition of `ylem2_Y2` holds along the route (a connected post molecule with
  at least five atoms has only open cells). The excluded post molecules are, by bond counts, the 4-atom crossed
  molecule `X` (two double bonds joined by four single bonds); this identification is not used.
-/

@[expose] public section
set_option autoImplicit false
open Finset
namespace WaveTurbulence.MoleProp4
universe u v

section
variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]

namespace TwoExit
variable {N : Molecule V D} (T : TwoExit N)

/-- **No loops in the post molecule.** -/
theorem post_loop (hloop : ∀ z, N.atom z ≠ N.atom (N.mate z)) :
    ∀ z, T.post.atom z ≠ T.post.atom (T.post.mate z) := by
  rintro (z | b)
  · exact hloop z.val
  · cases b
    · change T.c ≠ T.d; exact T.c_ne_d
    · change T.d ≠ T.c; exact T.c_ne_d.symm

/-- **No cut vertex in the post molecule.** -/
theorem post_noCut (hcutv : ∀ w ∈ N.atoms, ∀ a ∈ N.atoms, ∀ b ∈ N.atoms, a ≠ w → b ≠ w →
      (Degen.eraseAtoms N {w}).SameComponent a b) :
    ∀ w ∈ T.post.atoms, ∀ a ∈ T.post.atoms, ∀ b ∈ T.post.atoms, a ≠ w → b ≠ w →
      (Degen.eraseAtoms T.post {w}).SameComponent a b := by
  classical
  intro w hw a ha b hb haw hbw
  rw [T.post_atoms] at hw ha hb
  obtain ⟨hwN, hwY⟩ := mem_sdiff.mp hw
  let r : V := if T.c = w then T.d else T.c
  -- the new bond, when `c, d ≠ w`
  have hcd : T.c ≠ w → T.d ≠ w → (Degen.eraseAtoms T.post {w}).SameComponent T.c T.d := fun h1 h2 =>
    Relation.EqvGen.rel _ _ ⟨⟨Sum.inr false, (show T.c ∉ ({w} : Finset V) by simpa using h1),
      (show T.d ∉ ({w} : Finset V) by simpa using h2)⟩, rfl, rfl⟩
  have key : ∀ u v, (Degen.eraseAtoms N {w}).SameComponent u v →
      (Degen.eraseAtoms T.post {w}).SameComponent (if u ∈ T.Y then r else u) (if v ∈ T.Y then r else v) := by
    intro u v h
    induction h with
    | rel a b hab =>
      obtain ⟨z, rfl, rfl⟩ := hab
      have hz1 : N.atom z.val ≠ w := fun h => z.property.1 (by rw [h]; exact mem_singleton_self w)
      have hz2 : N.atom (N.mate z.val) ≠ w := fun h => z.property.2 (by rw [h]; exact mem_singleton_self w)
      show (Degen.eraseAtoms T.post {w}).SameComponent (if N.atom z.val ∈ T.Y then r else N.atom z.val)
        (if N.atom (N.mate z.val) ∈ T.Y then r else N.atom (N.mate z.val))
      have hcY : N.atom (N.mate T.x) ∉ T.Y := T.c_notMem
      have hdY : N.atom (N.mate T.y) ∉ T.Y := T.d_notMem
      rcases T.dart_cases z.val with h | h | h | h | h | h
      · rw [ite_of_pos h.1, ite_of_pos h.2]; exact Relation.EqvGen.refl _
      · rw [ite_of_not h.1, ite_of_not h.2]
        exact Relation.EqvGen.rel _ _ ⟨⟨Sum.inl ⟨z.val, h.1, h.2⟩, z.property.1, z.property.2⟩, rfl, rfl⟩
      · rw [h] at hz2 ⊢
        rw [ite_of_pos T.atom_x, ite_of_not hcY]
        have : r = T.c := by
          change (if T.c = w then T.d else T.c) = T.c; rw [ite_of_not (show ¬ T.c = w from hz2)]
        rw [this]; exact Relation.EqvGen.refl _
      · rw [h] at hz2 ⊢
        rw [ite_of_pos T.atom_y, ite_of_not hdY]
        by_cases hcw : T.c = w
        · have : r = T.d := by change (if T.c = w then T.d else T.c) = T.d; rw [ite_of_pos hcw]
          rw [this]; exact Relation.EqvGen.refl _
        · have : r = T.c := by change (if T.c = w then T.d else T.c) = T.c; rw [ite_of_not hcw]
          rw [this]; exact hcd hcw hz2
      · rw [h, N.mate_mate] at hz2 ⊢
        rw [h] at hz1
        rw [ite_of_not hcY, ite_of_pos T.atom_x]
        have : r = T.c := by
          change (if T.c = w then T.d else T.c) = T.c; rw [ite_of_not (show ¬ T.c = w from hz1)]
        rw [this]; exact Relation.EqvGen.refl _
      · rw [h, N.mate_mate] at hz2 ⊢
        rw [h] at hz1
        rw [ite_of_not hdY, ite_of_pos T.atom_y]
        by_cases hcw : T.c = w
        · have : r = T.d := by change (if T.c = w then T.d else T.c) = T.d; rw [ite_of_pos hcw]
          rw [this]; exact Relation.EqvGen.refl _
        · have : r = T.c := by change (if T.c = w then T.d else T.c) = T.c; rw [ite_of_not hcw]
          rw [this]; exact Relation.EqvGen.symm _ _ (hcd hcw hz1)
    | refl a => exact Relation.EqvGen.refl _
    | symm a b _ ih => exact Relation.EqvGen.symm _ _ ih
    | trans a b c _ _ ih1 ih2 => exact Relation.EqvGen.trans _ _ _ ih1 ih2
  have h := key a b (hcutv w hwN a (mem_sdiff.mp ha).1 b (mem_sdiff.mp hb).1 haw hbw)
  rwa [ite_of_not (mem_sdiff.mp ha).2, ite_of_not (mem_sdiff.mp hb).2] at h

end TwoExit

omit [DecidableEq D] in
/-- Bonds of two different pairs are disjoint. -/
theorem bb_add_bb_le_card (M : Molecule V D) {p q r s : V} (h : s(p, q) ≠ s(r, s)) :
    M.bondsBetween p q + M.bondsBetween r s ≤ M.bonds.card := by
  classical
  unfold Molecule.bondsBetween
  rw [← card_union_of_disjoint]
  · exact card_le_card (union_subset (filter_subset _ _) (filter_subset _ _))
  · rw [disjoint_filter]; intro x _ h1 h2; exact h (h1.symm.trans h2)

omit [DecidableEq D] in
/-- `Q` has no pair with exactly three bonds. -/
theorem IsQ.bb_ne_three {M : Molecule V D} (h : IsQ M) : ∀ p q, M.bondsBetween p q ≠ 3 := by
  obtain ⟨a, b, _, _, h4, hE⟩ := h
  intro p q
  by_cases hs : s(a, b) = s(p, q)
  · have : M.bondsBetween p q = M.bondsBetween a b := by
      rcases Sym2.eq_iff.mp hs with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · rw [h1, h2]
      · rw [h1, h2, Degen.bondsBetween_comm]
    omega
  · have := bb_add_bb_le_card M hs; omega

/-- **No triple bond after the sequence from the only triple pair** (or the post molecule is `Q`). -/
theorem Y2End.post_noTriple {M : Molecule V D} {C : YChain M} (E : Y2End C)
    (hcap : ∀ v ∈ M.atoms, M.outdeg v ≤ 2 ∧ M.indeg v ≤ 2)
    (hconn : ∀ u ∈ M.atoms, ∀ v ∈ M.atoms, M.SameComponent u v) (h4 : ∀ v ∈ M.atoms, M.deg v = 4)
    (hle3 : ∀ p q, M.bondsBetween p q ≤ 3)
    (hone : ∀ p q, 3 ≤ M.bondsBetween p q → s(p, q) = s(C.a 0, C.b 0))
    (hcomp : M.bondsBetween (M.atom (M.mate E.x)) (M.atom (M.mate E.y)) ≠ 2) :
    IsQ (E.toTwoExit hcap).post ∨ ∀ p q, (E.toTwoExit hcap).post.bondsBetween p q ≤ 2 := by
  classical
  set T := E.toTwoExit hcap with hT
  have hTY : T.Y = C.set := E.toTwoExit_Y hcap
  have hcd := E.toTwoExit_cd hcap
  have hcd2 : M.bondsBetween T.d T.c ≠ 2 := by
    rcases hcd with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · rw [h1, h2, Degen.bondsBetween_comm]; exact hcomp
    · rw [h1, h2]; exact hcomp
  have hpdeg : ∀ v ∈ T.post.atoms, T.post.deg v ≤ 4 := by
    intro v hv
    rw [T.post_atoms] at hv
    rw [T.post_deg (mem_sdiff.mp hv).2, h4 v (mem_sdiff.mp hv).1]
  by_cases hq : 3 ≤ M.bondsBetween T.d T.c
  · left
    have hb := T.post_bondsBetween T.d T.c
    rw [ite_of_not (by rintro (h | h) <;> [exact T.d_notMem h; exact T.c_notMem h]), ite_of_pos rfl] at hb
    exact isQ_of_quadruple hpdeg (T.post_connected hconn) T.c_ne_d.symm (by rw [hb]; have := hle3 T.d T.c; omega)
  push Not at hq
  right
  intro p q
  rw [T.post_bondsBetween]
  by_cases hY : p ∈ T.Y ∨ q ∈ T.Y
  · rw [ite_of_pos hY]; split_ifs <;> omega
  · rw [ite_of_not hY]
    push Not at hY
    by_cases hs : s(T.d, T.c) = s(p, q)
    · rw [ite_of_pos hs]
      have : M.bondsBetween p q = M.bondsBetween T.d T.c := by
        rcases Sym2.eq_iff.mp hs with ⟨h1, h2⟩ | ⟨h1, h2⟩
        · rw [← h1, ← h2]
        · rw [← h1, ← h2, Degen.bondsBetween_comm]
      omega
    · rw [ite_of_not hs, add_zero]
      by_contra hlt
      push Not at hlt
      have hpq := hone p q (by omega)
      have ha0 : C.a 0 ∈ T.Y := by rw [hTY]; exact C.a_mem (Nat.zero_le _)
      rcases Sym2.eq_iff.mp hpq with ⟨h1, _⟩ | ⟨_, h2⟩
      · exact hY.1 (h1 ▸ ha0)
      · exact hY.2 (h2 ▸ ha0)

end

/-- **Some complete (Y2)-route reaches a post molecule with at most four atoms and a ladder cell.** -/
inductive YReachesSmallCell : {V : Type u} → {D : Type v} → [DecidableEq V] → [Fintype D] → [DecidableEq D] →
    Molecule V D → Prop where
  | here {V : Type u} {D : Type v} [DecidableEq V] [Fintype D] [DecidableEq D] (M : Molecule V D)
      (hcap : ∀ w ∈ M.atoms, M.outdeg w ≤ 2 ∧ M.indeg w ≤ 2) (C : YChain M) (E : Y2End C) :
      M.bondsBetween (M.atom (M.mate E.x)) (M.atom (M.mate E.y)) ≠ 2 →
      (E.toTwoExit hcap).post.atoms.card ≤ 4 → (MoleProp.ladderCells (E.toTwoExit hcap).post).Nonempty →
      YReachesSmallCell M
  | y2 {V : Type u} {D : Type v} [DecidableEq V] [Fintype D] [DecidableEq D] (M : Molecule V D)
      (hcap : ∀ w ∈ M.atoms, M.outdeg w ≤ 2 ∧ M.indeg w ≤ 2) (C : YChain M) (E : Y2End C) :
      M.bondsBetween (M.atom (M.mate E.x)) (M.atom (M.mate E.y)) ≠ 2 →
      YReachesSmallCell (E.toTwoExit hcap).post → YReachesSmallCell M

variable {V : Type u} {D : Type v} [DecidableEq V] [Fintype D] [DecidableEq D]

/-- **The good-cell condition of `ylem2_Y2`** when no route reaches a small cell. -/
theorem Y2End.good_of_not_small {M : Molecule V D} {C : YChain M} (E : Y2End C)
    (hcap : ∀ v ∈ M.atoms, M.outdeg v ≤ 2 ∧ M.indeg v ≤ 2)
    (hconn : ∀ u ∈ M.atoms, ∀ v ∈ M.atoms, M.SameComponent u v)
    (hcomp : M.bondsBetween (M.atom (M.mate E.x)) (M.atom (M.mate E.y)) ≠ 2) (hns : ¬ YReachesSmallCell M) :
    ∀ S ∈ MoleProp.ladderCells (E.toTwoExit hcap).post, (E.toTwoExit hcap).c ∈ S →
      GoodCell (E.toTwoExit hcap).post S := by
  intro S hS _
  by_cases h5 : 5 ≤ (E.toTwoExit hcap).post.atoms.card
  · exact goodCell_of_connected ((E.toTwoExit hcap).post_connected hconn) h5 hS
  · exact absurd (YReachesSmallCell.here M hcap C E hcomp (by omega) ⟨S, hS⟩) hns

end WaveTurbulence.MoleProp4
