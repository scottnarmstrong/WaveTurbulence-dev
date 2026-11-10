/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.WaveB.Molecules
import Mathlib.Tactic

/-! # The half-closure of vine (II), from the B2 template

B2's vine (II) template (F72) is the Q-block `J₁ - (a = b) - J₂` with one slot (the rails into `J₂`); `expand [k]`
has `k + 1` rungs. DH23 L1838 excludes the molecule "formed by removing the two joints (with their bonds) of a vine
(II) and adding one new bond between the two atoms connected to one of the joints". We take the joint `J₁ = 0`, whose
neighbours are `a = 2`, `b = 3` (the other choice gives an isomorphic molecule: reverse the ladder). Here its bond
multiset is computed: a triple bond `2 ≡ 3`, rungs `(4 + i) = (4 + k + i)` and the rails between consecutive pairs.
-/

@[expose] public section
set_option autoImplicit false
open Finset
namespace WaveTurbulence.MoleProp4

/-- **The bonds of the half-closure of vine (II) with `k` inserted rungs** (`k + 1` rungs in all). -/
def halfClosureIIBonds (k : ℕ) : Multiset (Sym2 ℕ) :=
  (((VineType.II.expand [k]).bonds.map fun p => s(p.1, p.2) : Multiset (Sym2 ℕ)).filter
    fun e => (0 : ℕ) ∉ e ∧ (1 : ℕ) ∉ e) + {s(2, 3)}

/-- The label of `a i` (`a 0 = 2`), of `b i` (`b 0 = 3`). -/
def labA (_k i : ℕ) : ℕ := if i = 0 then 2 else 3 + i
def labB (k i : ℕ) : ℕ := if i = 0 then 3 else 3 + k + i

/-- The explicit bond multiset of the ladder with a triple bond at its start. -/
def ladderBonds (k : ℕ) : Multiset (Sym2 ℕ) :=
  3 • {s(2, 3)} + ∑ i ∈ range k, (2 • {s(labA k (i + 1), labB k (i + 1))} + {s(labA k i, labA k (i + 1))} +
    {s(labB k i, labB k (i + 1))})

theorem zip_cons_map_range (z z' : ℕ) (f : ℕ → ℕ) (k : ℕ) :
    List.zip (z :: (List.range k).map f) ((List.range k).map f ++ [z']) =
      (List.range (k + 1)).map fun i => (if i = 0 then z else f (i - 1), if i < k then f i else z') := by
  apply List.ext_getElem
  · simp
  · intro i h1 h2
    simp only [List.getElem_zip, List.getElem_map, List.getElem_range]
    rcases Nat.eq_zero_or_pos i with rfl | hpos
    · simp only [List.getElem_cons_zero, ite_true]
      congr 1
      rcases Nat.eq_zero_or_pos k with rfl | hk
      · simp
      · rw [List.getElem_append_left (by simpa using hk)]; simp [hk]
    · obtain ⟨j, rfl⟩ : ∃ j, i = j + 1 := ⟨i - 1, by omega⟩
      simp only [List.getElem_cons_succ, List.getElem_map, List.getElem_range, Nat.add_one_ne_zero, ite_false,
        Nat.add_sub_cancel]
      congr 1
      by_cases hj : j + 1 < k
      · rw [List.getElem_append_left (by simpa using hj)]; simp [hj]
      · have hjk : j + 1 = k := by simp at h1 h2; omega
        rw [List.getElem_append_right (by simp; omega)]
        simp [hjk]

theorem multiset_range_succ {α : Type*} (g : ℕ → α) (k : ℕ) :
    (((List.range (k + 1)).map g : List α) : Multiset α) = (((List.range k).map g : List α) : Multiset α) + {g k} := by
  rw [List.range_succ, List.map_append, ← Multiset.coe_add, List.map_singleton, Multiset.coe_singleton]

theorem coe_map_range {α : Type*} (g : ℕ → α) (k : ℕ) :
    (((List.range k).map g : List α) : Multiset α) = ∑ i ∈ range k, {g i} := by
  induction k with
  | zero => simp
  | succ k ih => rw [multiset_range_succ, ih, sum_range_succ]

theorem filter_sum_singleton_of_all {α : Type*} (p : α → Prop) [DecidablePred p] (g : ℕ → α) (k : ℕ)
    (h : ∀ i < k, p (g i)) : (∑ i ∈ range k, ({g i} : Multiset α)).filter p = ∑ i ∈ range k, {g i} := by
  rw [Multiset.filter_eq_self]
  intro a ha
  obtain ⟨i, hi, hai⟩ := Multiset.mem_sum.mp ha
  rw [Multiset.mem_singleton.mp hai]
  exact h i (mem_range.mp hi)

theorem notMem01 {x y : ℕ} (hx : 2 ≤ x) (hy : 2 ≤ y) : (0 : ℕ) ∉ s(x, y) ∧ (1 : ℕ) ∉ s(x, y) := by
  simp only [Sym2.mem_iff, not_or]; omega

/-- The vine (II) template with `k ≥ 1` inserted rungs. -/
theorem expand_II_bonds {k : ℕ} (hk : k ≠ 0) :
    (VineType.II.expand [k]).bonds = [(0, 2), (0, 3), (2, 3), (2, 3)] ++
      (List.range (k + 1)).map (fun i => (if i = 0 then 2 else 4 + (i - 1), if i < k then 4 + i else 1)) ++
      (List.range (k + 1)).map (fun i => (if i = 0 then 3 else 4 + k + (i - 1), if i < k then 4 + k + i else 1)) ++
      ((List.range k).map fun i => (4 + i, 4 + k + i)).flatMap (fun p => [p, p]) := by
  have h1 := zip_cons_map_range 2 1 (fun i => 4 + i) k
  have h2 := zip_cons_map_range 3 1 (fun i => 4 + k + i) k
  simp only [VineType.expand, VineType.template, List.zip_cons_cons, List.zip_nil_right, List.foldl_cons,
    List.foldl_nil, insertRungs, hk, ite_false, railBonds]
  rw [h1, h2, List.zip_map']
  rfl

/-- **The template computation**: the half-closure of vine (II) is the triple-ended ladder. -/
theorem halfClosureIIBonds_eq (k : ℕ) : halfClosureIIBonds k = ladderBonds k := by
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · decide
  unfold halfClosureIIBonds ladderBonds
  rw [expand_II_bonds hk.ne']
  simp only [List.map_append, ← Multiset.coe_add, Multiset.filter_add]
  -- the four parts
  have p1 : ((([(0, 2), (0, 3), (2, 3), (2, 3)] : List (ℕ × ℕ)).map fun p => s(p.1, p.2) : List (Sym2 ℕ)) :
      Multiset (Sym2 ℕ)).filter (fun e => (0 : ℕ) ∉ e ∧ (1 : ℕ) ∉ e) = 2 • {s(2, 3)} := by decide
  have p2 : ((((List.range (k + 1)).map (fun i => (if i = 0 then 2 else 4 + (i - 1), if i < k then 4 + i else 1))).map
      fun p => s(p.1, p.2) : List (Sym2 ℕ)) : Multiset (Sym2 ℕ)).filter (fun e => (0 : ℕ) ∉ e ∧ (1 : ℕ) ∉ e) =
      ∑ i ∈ range k, {s(labA k i, labA k (i + 1))} := by
    rw [List.map_map, multiset_range_succ, coe_map_range, Multiset.filter_add, Multiset.filter_singleton]
    simp only [Function.comp, lt_irrefl, ite_false, Sym2.mem_iff, or_true, not_true, and_false,
      Multiset.empty_eq_zero, add_zero]
    rw [filter_sum_singleton_of_all]
    · refine sum_congr rfl fun i hi => ?_
      have hi' := mem_range.mp hi
      simp only [labA, hi', ite_true, Nat.add_one_ne_zero, ite_false]
      congr 2
      · split_ifs <;> omega
      · omega
    · intro i hi
      have h2 : 2 ≤ (if i = 0 then 2 else 4 + (i - 1)) := by split_ifs <;> omega
      simp only [hi, ite_true]
      exact notMem01 h2 (by omega)
  have p3 : ((((List.range (k + 1)).map (fun i => (if i = 0 then 3 else 4 + k + (i - 1),
      if i < k then 4 + k + i else 1))).map fun p => s(p.1, p.2) : List (Sym2 ℕ)) : Multiset (Sym2 ℕ)).filter
      (fun e => (0 : ℕ) ∉ e ∧ (1 : ℕ) ∉ e) = ∑ i ∈ range k, {s(labB k i, labB k (i + 1))} := by
    rw [List.map_map, multiset_range_succ, coe_map_range, Multiset.filter_add, Multiset.filter_singleton]
    simp only [Function.comp, lt_irrefl, ite_false, Sym2.mem_iff, or_true, not_true, and_false,
      Multiset.empty_eq_zero, add_zero]
    rw [filter_sum_singleton_of_all]
    · refine sum_congr rfl fun i hi => ?_
      have hi' := mem_range.mp hi
      simp only [labB, hi', ite_true, Nat.add_one_ne_zero, ite_false]
      congr 2
      · split_ifs <;> omega
      · omega
    · intro i hi
      have h2 : 2 ≤ (if i = 0 then 3 else 4 + k + (i - 1)) := by split_ifs <;> omega
      simp only [hi, ite_true]
      exact notMem01 h2 (by omega)
  have p4 : (((((List.range k).map fun i => (4 + i, 4 + k + i)).flatMap (fun p => [p, p])).map
      fun p => s(p.1, p.2) : List (Sym2 ℕ)) : Multiset (Sym2 ℕ)).filter (fun e => (0 : ℕ) ∉ e ∧ (1 : ℕ) ∉ e) =
      ∑ i ∈ range k, 2 • {s(labA k (i + 1), labB k (i + 1))} := by
    have hlist : ∀ m, (((((List.range m).map fun i => (4 + i, 4 + k + i)).flatMap (fun p => [p, p])).map
        fun p => s(p.1, p.2) : List (Sym2 ℕ)) : Multiset (Sym2 ℕ)) = ∑ i ∈ range m, 2 • {s(4 + i, 4 + k + i)} := by
      intro m
      induction m with
      | zero => simp
      | succ m ih =>
        rw [List.range_succ, List.map_append, List.flatMap_append, List.map_append, ← Multiset.coe_add, ih,
          sum_range_succ]
        congr 1
    rw [hlist, Multiset.filter_eq_self.mpr]
    · refine sum_congr rfl fun i _ => ?_
      simp only [labA, labB, Nat.add_one_ne_zero, ite_false]
      congr 3 <;> omega
    · intro a ha
      obtain ⟨i, _, hai⟩ := Multiset.mem_sum.mp ha
      rw [two_nsmul, Multiset.mem_add, Multiset.mem_singleton, or_self] at hai
      rw [hai]
      exact notMem01 (by omega) (by omega)
  rw [p1, p2, p3, p4, sum_add_distrib, sum_add_distrib]
  abel

end WaveTurbulence.MoleProp4
