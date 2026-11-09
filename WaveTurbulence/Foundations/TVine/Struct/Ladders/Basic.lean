/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.TVine.Struct.Statement
import Mathlib.Tactic

/-!
# Ladders from runs of rung pieces (packet L3-LAD, N3 Theorem 6 (iv))

N3 (`research-gamma-half-3/NOTES.txt` L291–L305): a ladder step is a digon between two rung pieces whose two bonds
are single, disjoint and anti-parallel. This module turns a **run** (a list of rung pieces, pairwise disjoint, each
consecutive pair a ladder step, `MatchStep`) into a B2 ladder (`Molecule.IsLadder`, `Molecule.IsLadderSet`), and
assembles at most three runs into the conclusion of `LaddersStatement`:

* `run_ladder`: a run of `k + 1` pieces is a "pre-ladder" (`PreLadder`: `IsLadder` without `1 ≤ m`) of length `k`;
* `run_cover`: a run is covered by at most one ladder up to at most 2 atoms;
* `assemble`: three disjoint runs covering `S` up to the joints and at most 5 further atoms give `≤ 3` disjoint
  ladders leaving `≤ 2 + 5 + 3 · 2 = 13` atoms (N3 L302–L303).
-/

@[expose] public section
set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace WaveTurbulence.TVine.Struct.Ladders

open Finset

variable {V : Type*} {D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]

/-! ## Unions of lists of atom sets -/

theorem unionAll_nil' : unionAll ([] : List (Finset V)) = ∅ := rfl

theorem unionAll_cons' (a : Finset V) (l : List (Finset V)) : unionAll (a :: l) = a ∪ unionAll l := rfl

theorem mem_unionAll {l : List (Finset V)} {w : V} : w ∈ unionAll l ↔ ∃ P ∈ l, w ∈ P := by
  induction l with
  | nil => simp [unionAll_nil']
  | cons a l ih => simp [unionAll_cons', ih]

theorem unionAll_append' (l₁ l₂ : List (Finset V)) : unionAll (l₁ ++ l₂) = unionAll l₁ ∪ unionAll l₂ := by
  ext w
  simp only [mem_unionAll, List.mem_append, Finset.mem_union]
  constructor
  · rintro ⟨P, hP | hP, hw⟩
    · exact Or.inl ⟨P, hP, hw⟩
    · exact Or.inr ⟨P, hP, hw⟩
  · rintro (⟨P, hP, hw⟩ | ⟨P, hP, hw⟩)
    · exact ⟨P, Or.inl hP, hw⟩
    · exact ⟨P, Or.inr hP, hw⟩

theorem subset_unionAll {l : List (Finset V)} {P : Finset V} (h : P ∈ l) : P ⊆ unionAll l :=
  fun _ hw => mem_unionAll.mpr ⟨P, h, hw⟩

theorem unionAll_subset {l : List (Finset V)} {S : Finset V} (h : ∀ P ∈ l, P ⊆ S) : unionAll l ⊆ S := by
  intro w hw
  obtain ⟨P, hP, hwP⟩ := mem_unionAll.mp hw
  exact h P hP hwP

theorem disjoint_unionAll {l₁ l₂ : List (Finset V)} (h : ∀ A ∈ l₁, ∀ B ∈ l₂, Disjoint A B) :
    Disjoint (unionAll l₁) (unionAll l₂) := by
  rw [Finset.disjoint_left]
  intro w h1 h2
  obtain ⟨A, hA, hwA⟩ := mem_unionAll.mp h1
  obtain ⟨B, hB, hwB⟩ := mem_unionAll.mp h2
  exact Finset.disjoint_left.mp (h A hA B hB) hwA hwB

/-! ## Ladder steps and runs -/

/-- **A ladder step from `R` to `R'`** (N3 L295–L296): for every ordering `(a', b')` of `R'` there is an ordering
`(a, b)` of `R` such that `a – a'`, `b – b'` are single bonds, oppositely directed (B2's rail clause). -/
def MatchStep (M : Molecule V D) (R R' : Finset V) : Prop :=
  ∀ a' b' : V, a' ≠ b' → R' = {a', b'} → ∃ a b : V, a ≠ b ∧ R = {a, b} ∧ M.bondsBetween a a' = 1 ∧
    M.bondsBetween b b' = 1 ∧ (M.Directed a a' ↔ M.Directed b' b)

/-- **A run**: rung pieces, pairwise disjoint, consecutive ones joined by a ladder step. -/
def IsRun (M : Molecule V D) (l : List (Finset V)) : Prop :=
  (∀ P ∈ l, IsRungPiece M P) ∧ l.Pairwise (fun A B => Disjoint A B) ∧
    ∀ i (h : i + 1 < l.length), MatchStep M (l[i]'(by omega)) l[i + 1]

/-- `Molecule.IsLadder` without the length clause `1 ≤ m`. -/
def PreLadder (M : Molecule V D) {m : ℕ} (u v : Fin (m + 1) → V) : Prop :=
  Function.Injective (Sum.elim u v) ∧ (∀ j, u j ∈ M.atoms ∧ v j ∈ M.atoms) ∧
    (∀ j, M.bondsBetween (u j) (v j) = 2) ∧
    (∀ j : Fin m, M.bondsBetween (u j.castSucc) (u j.succ) = 1 ∧
      M.bondsBetween (v j.castSucc) (v j.succ) = 1 ∧
      (M.Directed (u j.castSucc) (u j.succ) ↔ M.Directed (v j.succ) (v j.castSucc)))

theorem isLadder_of_pre {M : Molecule V D} {m : ℕ} {u v : Fin (m + 1) → V} (hm : 1 ≤ m)
    (h : PreLadder M u v) : M.IsLadder u v :=
  ⟨hm, h⟩

theorem bondsBetween_comm' (M : Molecule V D) (a b : V) : M.bondsBetween a b = M.bondsBetween b a := by
  unfold Molecule.bondsBetween
  rw [Sym2.eq_swap (a := a)]

theorem mem_atoms_of_bondsBetween {M : Molecule V D} {a b : V} (h : M.bondsBetween a b ≠ 0) : a ∈ M.atoms := by
  obtain ⟨x, hx⟩ := Finset.card_ne_zero.mp h
  have h2 := (Finset.mem_filter.mp hx).2
  simp only [Molecule.ends, Sym2.eq_iff] at h2
  rcases h2 with ⟨h, -⟩ | ⟨-, h⟩
  · rw [← h]; exact M.atom_mem x
  · rw [← h]; exact M.atom_mem _

theorem pair_cases {a b c d : V} (hab : a ≠ b) (h : ({a, b} : Finset V) = {c, d}) :
    (a = c ∧ b = d) ∨ (a = d ∧ b = c) := by
  have ha : a ∈ ({c, d} : Finset V) := h ▸ (by simp)
  have hb : b ∈ ({c, d} : Finset V) := h ▸ (by simp)
  simp only [Finset.mem_insert, Finset.mem_singleton] at ha hb
  rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
  · exact absurd rfl hab
  · exact Or.inl ⟨rfl, rfl⟩
  · exact Or.inr ⟨rfl, rfl⟩
  · exact absurd rfl hab

theorem rung_bb {M : Molecule V D} {P : Finset V} (h : IsRungPiece M P) {a b : V} (hab : a ≠ b)
    (hP : P = {a, b}) : M.bondsBetween a b = 2 := by
  obtain ⟨c, d, -, rfl, hcd⟩ := h
  rcases pair_cases hab hP.symm with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact hcd
  · rw [bondsBetween_comm']; exact hcd

theorem rung_card {M : Molecule V D} {P : Finset V} (h : IsRungPiece M P) : P.card = 2 := by
  obtain ⟨a, b, hab, rfl, -⟩ := h
  exact Finset.card_pair hab

theorem IsRun.tail {M : Molecule V D} {R : Finset V} {l : List (Finset V)} (h : IsRun M (R :: l)) :
    IsRun M l := by
  refine ⟨fun P hP => h.1 P (List.mem_cons_of_mem _ hP), (List.pairwise_cons.mp h.2.1).2, fun i hi => ?_⟩
  have := h.2.2 (i + 1) (by simp; omega)
  simpa using this

theorem IsRun.head_step {M : Molecule V D} {R R' : Finset V} {l : List (Finset V)} (h : IsRun M (R :: R' :: l)) :
    MatchStep M R R' := by
  have := h.2.2 0 (by simp)
  simpa using this

/-- A run of `l.length + 1` pieces is a pre-ladder of length `l.length` whose first rung is the first piece. -/
theorem run_ladder (M : Molecule V D) : ∀ (l : List (Finset V)) (R : Finset V), IsRun M (R :: l) →
    ∃ u v : Fin (l.length + 1) → V, PreLadder M u v ∧ Molecule.ladderAtoms u v = unionAll (R :: l) ∧
      u 0 ≠ v 0 ∧ R = {u 0, v 0}
  | [], R, h => by
    obtain ⟨a, b, hab, rfl, h2⟩ := h.1 _ (List.mem_cons_self ..)
    refine ⟨fun _ => a, fun _ => b, ⟨?_, ?_, fun _ => h2, fun j => j.elim0⟩, ?_, hab, rfl⟩
    · have h01 : ∀ i j : Fin ([] : List (Finset V)).length.succ, i = j := fun i j =>
        Fin.ext (by have hi := i.isLt; have hj := j.isLt; simp only [List.length_nil] at hi hj; omega)
      rintro (i | i) (j | j) hij
      · exact congrArg _ (h01 i j)
      · exact absurd hij hab
      · exact absurd hij.symm hab
      · exact congrArg _ (h01 i j)
    · intro _
      exact ⟨mem_atoms_of_bondsBetween (a := a) (b := b) (by omega),
        mem_atoms_of_bondsBetween (a := b) (b := a) (by rw [bondsBetween_comm']; omega)⟩
    · ext x
      simp only [Molecule.ladderAtoms, Finset.mem_union, Finset.mem_image, Finset.mem_univ, true_and,
        unionAll_cons', unionAll_nil', Finset.union_empty, Finset.mem_insert, Finset.mem_singleton]
      constructor
      · rintro (⟨_, rfl⟩ | ⟨_, rfl⟩)
        · exact Or.inl rfl
        · exact Or.inr rfl
      · rintro (rfl | rfl)
        · exact Or.inl ⟨0, rfl⟩
        · exact Or.inr ⟨0, rfl⟩
  | R' :: l, R, h => by
    obtain ⟨u', v', hpre, hat, hne, hR'⟩ := run_ladder M l R' h.tail
    obtain ⟨a, b, hab, hR, h1a, h1b, hdir⟩ := h.head_step (u' 0) (v' 0) hne hR'
    have hrung : M.bondsBetween a b = 2 := rung_bb (h.1 R (List.mem_cons_self ..)) hab hR
    -- the atoms of `R` are not atoms of the pre-ladder of the tail
    have hdisj : Disjoint R (unionAll (R' :: l)) := by
      rw [Finset.disjoint_left]
      intro w hwR hw
      obtain ⟨B, hB, hwB⟩ := mem_unionAll.mp hw
      exact Finset.disjoint_left.mp ((List.pairwise_cons.mp h.2.1).1 B hB) hwR hwB
    have hout : ∀ w ∈ R, ∀ j, u' j ≠ w ∧ v' j ≠ w := by
      intro w hw j
      have hu : u' j ∈ unionAll (R' :: l) := by
        rw [← hat]; exact Finset.mem_union_left _ (Finset.mem_image_of_mem _ (Finset.mem_univ _))
      have hv : v' j ∈ unionAll (R' :: l) := by
        rw [← hat]; exact Finset.mem_union_right _ (Finset.mem_image_of_mem _ (Finset.mem_univ _))
      exact ⟨fun e => Finset.disjoint_left.mp hdisj hw (e ▸ hu),
        fun e => Finset.disjoint_left.mp hdisj hw (e ▸ hv)⟩
    have haR : a ∈ R := by rw [hR]; simp
    have hbR : b ∈ R := by rw [hR]; simp
    refine ⟨Fin.cons a u', Fin.cons b v', ⟨?_, ?_, ?_, ?_⟩, ?_, ?_, ?_⟩
    · -- injectivity
      have hu' : Function.Injective u' := hpre.1.comp Sum.inl_injective
      have hv' : Function.Injective v' := hpre.1.comp Sum.inr_injective
      have huv : ∀ i j, u' i ≠ v' j := fun i j e => by
        have := hpre.1 (a₁ := Sum.inl i) (a₂ := Sum.inr j) e
        exact Sum.inl_ne_inr this
      refine Function.Injective.sumElim ?_ ?_ ?_
      · exact Fin.cons_injective_of_injective (fun ⟨j, hj⟩ => (hout a haR j).1 hj) hu'
      · exact Fin.cons_injective_of_injective (fun ⟨j, hj⟩ => (hout b hbR j).2 hj) hv'
      · intro i j
        refine Fin.cases ?_ (fun i => ?_) i <;> refine Fin.cases ?_ (fun j => ?_) j <;>
          simp only [Fin.cons_zero, Fin.cons_succ]
        · exact hab
        · exact fun e => (hout a haR j).2 e.symm
        · exact (hout b hbR i).1
        · exact huv i j
    · intro j
      refine Fin.cases ?_ (fun j => ?_) j <;> simp only [Fin.cons_zero, Fin.cons_succ]
      · exact ⟨mem_atoms_of_bondsBetween (a := a) (b := b) (by omega),
          mem_atoms_of_bondsBetween (a := b) (b := a) (by rw [bondsBetween_comm']; omega)⟩
      · exact hpre.2.1 j
    · intro j
      refine Fin.cases ?_ (fun j => ?_) j <;> simp only [Fin.cons_zero, Fin.cons_succ]
      · exact hrung
      · exact hpre.2.2.1 j
    · intro j
      refine Fin.cases ?_ (fun j => ?_) j
      · simp only [Fin.castSucc_zero, Fin.cons_zero, Fin.cons_succ]
        exact ⟨h1a, h1b, hdir⟩
      · rw [← Fin.succ_castSucc]
        simp only [Fin.cons_succ]
        exact hpre.2.2.2 j
    · have himg : ∀ (c : V) (w : Fin (l.length + 1) → V),
          Finset.univ.image (Fin.cons c w : Fin (l.length + 2) → V) = insert c (Finset.univ.image w) := by
        intro c w
        ext x
        simp only [Finset.mem_image, Finset.mem_univ, true_and, Finset.mem_insert]
        rw [Fin.exists_fin_succ]
        simp only [Fin.cons_zero, Fin.cons_succ]
        constructor
        · rintro (h | h)
          · exact Or.inl h.symm
          · exact Or.inr h
        · rintro (h | h)
          · exact Or.inl h.symm
          · exact Or.inr h
      rw [unionAll_cons', ← hat, hR]
      unfold Molecule.ladderAtoms
      rw [himg, himg]
      ext x
      simp only [Finset.mem_union, Finset.mem_insert, Finset.mem_singleton]
      tauto
    · simpa using hab
    · simpa using hR

/-- **A run is one ladder up to at most two atoms** (a run of `≥ 2` pieces is a ladder; a run of one piece is two
atoms). -/
theorem run_cover {M : Molecule V D} {l : List (Finset V)} (h : IsRun M l) :
    ∃ ls : List (Finset V), ls.length ≤ 1 ∧ (∀ L ∈ ls, L ⊆ unionAll l ∧ M.IsLadderSet L) ∧
      (unionAll l \ unionAll ls).card ≤ 2 := by
  match l, h with
  | [], _ => exact ⟨[], by simp, by simp, by simp [unionAll_nil']⟩
  | [R], h =>
    refine ⟨[], by simp, by simp, ?_⟩
    simp only [unionAll_cons', unionAll_nil', Finset.union_empty, Finset.sdiff_empty]
    exact (rung_card (h.1 R (List.mem_singleton_self _))).le
  | R :: R' :: l, h =>
    obtain ⟨u, v, hpre, hat, -, -⟩ := run_ladder M (R' :: l) R h
    refine ⟨[unionAll (R :: R' :: l)], by simp, ?_, by simp [unionAll_cons' _ ([] : List (Finset V)), unionAll_nil']⟩
    intro L hL
    rw [List.mem_singleton] at hL
    subst hL
    exact ⟨subset_rfl, _, u, v, isLadder_of_pre (by simp) hpre, hat⟩

theorem pairwise_of_length_le_one {l : List (Finset V)} (hl : l.length ≤ 1) :
    l.Pairwise (fun A B => Disjoint A B) := by
  match l, hl with
  | [], _ => exact List.Pairwise.nil
  | [_], _ => exact List.pairwise_singleton _ _

/-- **Assembly** (N3 L302–L303): three disjoint runs covering `S` up to the joints and a set `X` of at most `5`
atoms give at most three disjoint ladders leaving at most `13` atoms of `S`. -/
theorem assemble {M : Molecule V D} {S X : Finset V} {j₁ j₂ : V} {A B Y : List (Finset V)}
    (hA : IsRun M A) (hB : IsRun M B) (hY : IsRun M Y)
    (hAS : unionAll A ⊆ S) (hBS : unionAll B ⊆ S) (hYS : unionAll Y ⊆ S)
    (dAB : Disjoint (unionAll A) (unionAll B)) (dAY : Disjoint (unionAll A) (unionAll Y))
    (dBY : Disjoint (unionAll B) (unionAll Y))
    (hcov : ∀ w ∈ S, w = j₁ ∨ w = j₂ ∨ w ∈ X ∨ w ∈ unionAll A ∨ w ∈ unionAll B ∨ w ∈ unionAll Y)
    (hX : X.card ≤ 5) :
    ∃ ls : List (Finset V), ls.length ≤ 3 ∧ (∀ L ∈ ls, L ⊆ S ∧ M.IsLadderSet L) ∧
      ls.Pairwise (fun A B => Disjoint A B) ∧ (S \ unionAll ls).card ≤ 13 := by
  obtain ⟨la, hla1, hla2, hla3⟩ := run_cover hA
  obtain ⟨lb, hlb1, hlb2, hlb3⟩ := run_cover hB
  obtain ⟨ly, hly1, hly2, hly3⟩ := run_cover hY
  refine ⟨la ++ lb ++ ly, by simp only [List.length_append]; omega, ?_, ?_, ?_⟩
  · intro L hL
    simp only [List.mem_append] at hL
    rcases hL with (h | h) | h
    · exact ⟨(hla2 L h).1.trans hAS, (hla2 L h).2⟩
    · exact ⟨(hlb2 L h).1.trans hBS, (hlb2 L h).2⟩
    · exact ⟨(hly2 L h).1.trans hYS, (hly2 L h).2⟩
  · rw [List.pairwise_append, List.pairwise_append]
    refine ⟨⟨pairwise_of_length_le_one hla1, pairwise_of_length_le_one hlb1, ?_⟩,
      pairwise_of_length_le_one hly1, ?_⟩
    · intro a ha b hb
      exact Finset.disjoint_of_subset_left (hla2 a ha).1 (Finset.disjoint_of_subset_right (hlb2 b hb).1 dAB)
    · intro a ha b hb
      rw [List.mem_append] at ha
      rcases ha with ha | ha
      · exact Finset.disjoint_of_subset_left (hla2 a ha).1 (Finset.disjoint_of_subset_right (hly2 b hb).1 dAY)
      · exact Finset.disjoint_of_subset_left (hlb2 a ha).1 (Finset.disjoint_of_subset_right (hly2 b hb).1 dBY)
  · have hsub : S \ unionAll (la ++ lb ++ ly) ⊆
        (({j₁, j₂} ∪ X) ∪ (unionAll A \ unionAll la)) ∪ (unionAll B \ unionAll lb) ∪
          (unionAll Y \ unionAll ly) := by
      intro w hw
      rw [Finset.mem_sdiff, unionAll_append', unionAll_append'] at hw
      simp only [Finset.mem_union, not_or] at hw
      obtain ⟨hwS, ⟨hwa, hwb⟩, hwy⟩ := hw
      simp only [Finset.mem_union, Finset.mem_sdiff, Finset.mem_insert, Finset.mem_singleton]
      rcases hcov w hwS with h | h | h | h | h | h
      · exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inl h))))
      · exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inr h))))
      · exact Or.inl (Or.inl (Or.inl (Or.inr h)))
      · exact Or.inl (Or.inl (Or.inr ⟨h, hwa⟩))
      · exact Or.inl (Or.inr ⟨h, hwb⟩)
      · exact Or.inr ⟨h, hwy⟩
    have h0 := Finset.card_le_card hsub
    have h1 := Finset.card_union_le ((({j₁, j₂} ∪ X) ∪ (unionAll A \ unionAll la)) ∪
      (unionAll B \ unionAll lb)) (unionAll Y \ unionAll ly)
    have h2 := Finset.card_union_le (({j₁, j₂} ∪ X) ∪ (unionAll A \ unionAll la)) (unionAll B \ unionAll lb)
    have h3 := Finset.card_union_le ({j₁, j₂} ∪ X) (unionAll A \ unionAll la)
    have h4 := Finset.card_union_le ({j₁, j₂} : Finset V) X
    have h5 : ({j₁, j₂} : Finset V).card ≤ 2 := Finset.card_le_two
    omega

end WaveTurbulence.TVine.Struct.Ladders
