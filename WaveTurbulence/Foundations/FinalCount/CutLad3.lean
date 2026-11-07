/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.FinalCount.CutLad2
/-! Ladders under a cut, part 3 (FINALCOUNT-G2 step 2): sub-ladders and sizes. -/
@[expose] public section
set_option autoImplicit false
set_option linter.unusedSectionVars false
open Finset
namespace WaveTurbulence.FinalCount
open WaveTurbulence WaveTurbulence.LadderDisjoint

variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]

/-- The restriction of a ladder row to the rungs `a, …, a + m'`. -/
def subLad {m : ℕ} (u : Fin (m + 1) → V) (a m' : ℕ) (h : a + m' ≤ m) : Fin (m' + 1) → V :=
  fun i => u ⟨a + i.val, by have := i.isLt; omega⟩

theorem subLad_apply {m : ℕ} (u : Fin (m + 1) → V) (a m' : ℕ) (h : a + m' ≤ m) (i : Fin (m' + 1)) :
    subLad u a m' h i = u ⟨a + i.val, by have := i.isLt; omega⟩ := rfl

theorem IsLadder.sub (N : Molecule V D) {m : ℕ} {u w : Fin (m + 1) → V} (hL : N.IsLadder u w)
    (a m' : ℕ) (hm' : 1 ≤ m') (h : a + m' ≤ m) :
    N.IsLadder (subLad u a m' h) (subLad w a m' h) := by
  obtain ⟨hu, hw, huw⟩ := Sum.elim_injective.mp hL.2.1
  have key : ∀ (f : Fin (m + 1) → V), Function.Injective f → Function.Injective (subLad f a m' h) := by
    intro f hf i j e
    have := hf e
    simp only [Fin.mk.injEq] at this
    exact Fin.ext (by omega)
  refine ⟨hm', Sum.elim_injective.mpr ⟨key u hu, key w hw, fun i j e => huw _ _ e⟩,
    fun j => hL.2.2.1 _, fun j => hL.2.2.2.1 _, ?_⟩
  intro j
  have hj := j.isLt
  obtain ⟨h1, h2, h3⟩ := hL.2.2.2.2 ⟨a + j.val, by omega⟩
  have e1 : (⟨a + (j.castSucc : Fin (m' + 1)).val, by have := (j.castSucc : Fin (m' + 1)).isLt; omega⟩ : Fin (m + 1)) =
      (⟨a + j.val, by omega⟩ : Fin m).castSucc := Fin.ext (by simp)
  have e2 : (⟨a + (j.succ : Fin (m' + 1)).val, by have := (j.succ : Fin (m' + 1)).isLt; omega⟩ : Fin (m + 1)) =
      (⟨a + j.val, by omega⟩ : Fin m).succ := Fin.ext (by simp; omega)
  simp only [subLad_apply]
  rw [e1, e2]
  exact ⟨h1, h2, h3⟩

theorem card_ladderAtoms (N : Molecule V D) {m : ℕ} {u w : Fin (m + 1) → V} (hL : N.IsLadder u w) :
    (Molecule.ladderAtoms u w).card = 2 * (m + 1) := by
  classical
  obtain ⟨hu, hw, huw⟩ := Sum.elim_injective.mp hL.2.1
  unfold Molecule.ladderAtoms
  rw [Finset.card_union_of_disjoint]
  · rw [Finset.card_image_of_injective _ hu, Finset.card_image_of_injective _ hw]; simp; ring
  · rw [Finset.disjoint_left]
    intro a ha hb
    simp only [Finset.mem_image, Finset.mem_univ, true_and] at ha hb
    obtain ⟨i, rfl⟩ := ha
    obtain ⟨j, hj⟩ := hb
    exact huw i j hj.symm

theorem ladderLength_ladderAtoms (N : Molecule V D) {m : ℕ} {u w : Fin (m + 1) → V} (hL : N.IsLadder u w) :
    Molecule.ladderLength (Molecule.ladderAtoms u w) = m := by
  unfold Molecule.ladderLength
  rw [card_ladderAtoms N hL]; omega

theorem ladderLength_ge_of_subset {S P : Finset V} {m' : ℕ} (hP : P.card = 2 * (m' + 1)) (h : P ⊆ S) :
    m' ≤ Molecule.ladderLength S := by
  unfold Molecule.ladderLength
  have := Finset.card_le_card h
  omega

theorem ladderAtoms_sub_subset {m : ℕ} (u w : Fin (m + 1) → V) (a m' : ℕ) (h : a + m' ≤ m) :
    Molecule.ladderAtoms (subLad u a m' h) (subLad w a m' h) ⊆ Molecule.ladderAtoms u w := by
  intro x hx
  obtain ⟨j, hj | hj⟩ := (mem_ladderAtoms _ _ x).1 hx
  · exact (mem_ladderAtoms _ _ x).2 ⟨_, Or.inl hj⟩
  · exact (mem_ladderAtoms _ _ x).2 ⟨_, Or.inr hj⟩

/-- Pieces on disjoint index ranges have disjoint atom sets. -/
theorem ladderAtoms_sub_disjoint {m : ℕ} {u w : Fin (m + 1) → V} (hinj : Function.Injective (Sum.elim u w))
    (a m' b n' : ℕ) (h : a + m' ≤ m) (h' : b + n' ≤ m) (hab : a + m' < b) :
    Disjoint (Molecule.ladderAtoms (subLad u a m' h) (subLad w a m' h))
      (Molecule.ladderAtoms (subLad u b n' h') (subLad w b n' h')) := by
  rw [Finset.disjoint_left]
  intro x hx hy
  obtain ⟨i, hi⟩ := (mem_ladderAtoms _ _ x).1 hx
  obtain ⟨j, hj⟩ := (mem_ladderAtoms _ _ x).1 hy
  have hi' := i.isLt
  have hj' := j.isLt
  simp only [subLad_apply] at hi hj
  have key : ∀ (p q : Fin (m + 1) ⊕ Fin (m + 1)) (hp : Sum.elim u w p = x) (hq : Sum.elim u w q = x),
      p = q := fun p q hp hq => hinj (hp.trans hq.symm)
  have fin_val : ∀ (p q : Fin (m + 1)) , (Sum.inl p : Fin (m + 1) ⊕ Fin (m + 1)) = Sum.inl q → p.val = q.val :=
    fun p q e => by cases e; rfl
  have fin_val' : ∀ (p q : Fin (m + 1)) , (Sum.inr p : Fin (m + 1) ⊕ Fin (m + 1)) = Sum.inr q → p.val = q.val :=
    fun p q e => by cases e; rfl
  rcases hi with hi | hi <;> rcases hj with hj | hj
  · have := fin_val _ _ (key (Sum.inl _) (Sum.inl _) hi hj)
    simp only at this; omega
  · exact absurd (key (Sum.inl _) (Sum.inr _) hi hj) (by simp)
  · exact absurd (key (Sum.inr _) (Sum.inl _) hi hj) (by simp)
  · have := fin_val' _ _ (key (Sum.inr _) (Sum.inr _) hi hj)
    simp only at this; omega

end WaveTurbulence.FinalCount
