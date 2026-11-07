/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.C4ZQ
public import WaveTurbulence.Foundations.FinalCount.C5VineH
import Mathlib.Tactic

/-! # Prop 9.6, case (4): a half-ladder is a half-closure of vine (II)

`lBB` is the bond function of the ladder with a triple first rung and double other rungs (the half-closure
`ladderBonds`). If a molecule has this bond function under an injective labelling `ψ`, its bond multiset is `ladderBonds m`
under `lab m ∘ ψ⁻¹`: `IsVineIIHalfClosure`.
-/

@[expose] public section
set_option autoImplicit false
open Finset
namespace WaveTurbulence.FinalCountG8
universe u v
open WaveTurbulence.MoleProp4

/-- The bond function of the half-ladder: triple first rung, double other rungs, single rails. -/
def lBB (x y : Bool × ℕ) : ℕ :=
  if x.2 = y.2 ∧ x.1 ≠ y.1 then (if x.2 = 0 then 3 else 2)
  else if x.1 = y.1 ∧ (x.2 + 1 = y.2 ∨ y.2 + 1 = x.2) then 1 else 0

/-- The half-ladder bond multiset on the labels `Bool × ℕ`. -/
def zMS (k : ℕ) : Multiset (Sym2 (Bool × ℕ)) :=
  3 • {s((false, 0), (true, 0))} + ∑ i ∈ range k, (2 • {s((false, i + 1), (true, i + 1))} +
    {s((false, i), (false, i + 1))} + {s((true, i), (true, i + 1))})

/-- The numeric label of a ladder position. -/
def lab (k : ℕ) (x : Bool × ℕ) : ℕ := if x.1 then labB k x.2 else labA k x.2

theorem ladderBonds_eq_map (k : ℕ) : ladderBonds k = (zMS k).map (Sym2.map (lab k)) := by
  unfold ladderBonds zMS
  rw [← Multiset.mapAddMonoidHom_apply, map_add, map_sum]
  simp only [Multiset.mapAddMonoidHom_apply, Multiset.map_add, Multiset.map_nsmul, Multiset.map_singleton, Sym2.map_mk]
  simp [lab, labA, labB]

theorem zMS_support (k : ℕ) : ∀ e ∈ zMS k, ∃ x y : Bool × ℕ, x.2 ≤ k ∧ y.2 ≤ k ∧ e = s(x, y) := by
  intro e he
  unfold zMS at he
  rcases Multiset.mem_add.mp he with h | h
  · have := Multiset.mem_of_mem_nsmul h
    rw [Multiset.mem_singleton] at this
    exact ⟨_, _, by simp, by simp, this⟩
  · obtain ⟨i, hi, h⟩ := Multiset.mem_sum.mp h
    have hi' := mem_range.mp hi
    rcases Multiset.mem_add.mp h with h | h
    · rcases Multiset.mem_add.mp h with h | h
      · have := Multiset.mem_of_mem_nsmul h
        rw [Multiset.mem_singleton] at this
        exact ⟨_, _, by simp; omega, by simp; omega, this⟩
      · rw [Multiset.mem_singleton] at h
        exact ⟨_, _, by simp; omega, by simp; omega, h⟩
    · rw [Multiset.mem_singleton] at h
      exact ⟨_, _, by simp; omega, by simp; omega, h⟩

theorem count_zMS (k : ℕ) (x y : Bool × ℕ) :
    (zMS k).count s(x, y) = if x.2 ≤ k ∧ y.2 ≤ k then lBB x y else 0 := by
  induction k with
  | zero =>
    obtain ⟨a, i⟩ := x; obtain ⟨b, j⟩ := y
    simp only [zMS, range_zero, sum_empty, add_zero, Multiset.count_nsmul, Multiset.count_singleton, Sym2.eq_iff,
      Prod.mk.injEq, lBB]
    cases a <;> cases b <;> split_ifs <;> simp_all <;> omega
  | succ k ih =>
    have hz : zMS (k + 1) = zMS k + (2 • {s((false, k + 1), (true, k + 1))} + {s((false, k), (false, k + 1))} +
        {s((true, k), (true, k + 1))}) := by
      unfold zMS; rw [sum_range_succ]; abel
    rw [hz, Multiset.count_add, ih]
    clear ih hz
    obtain ⟨a, i⟩ := x; obtain ⟨b, j⟩ := y
    simp only [Multiset.count_add, Multiset.count_nsmul, Multiset.count_singleton, Sym2.eq_iff, Prod.mk.injEq, lBB]
    cases a <;> cases b <;> simp only [Bool.false_eq_true, Bool.true_eq_false, ne_eq, not_true_eq_false, not_false_eq_true,
      and_false, and_true, false_and, true_and, or_false, false_or, if_false, if_true, ite_false, ite_true,
      Bool.not_eq_true] <;> split_ifs <;> omega

section
variable {V : Type u} {D : Type v} [DecidableEq V] [Fintype D] [DecidableEq D]

theorem groupBonds_eq_zMS {N : Molecule V D} {m : ℕ} {ψ : Bool × ℕ → V}
    (hinj : ∀ x y : Bool × ℕ, x.2 ≤ m → y.2 ≤ m → ψ x = ψ y → x = y)
    (hat : ∀ w, w ∈ N.atoms ↔ ∃ x : Bool × ℕ, x.2 ≤ m ∧ ψ x = w)
    (hbb : ∀ x y : Bool × ℕ, x.2 ≤ m → y.2 ≤ m → N.bondsBetween (ψ x) (ψ y) = lBB x y) :
    N.groupBonds N.atoms = (zMS m).map (Sym2.map ψ) := by
  classical
  ext e
  by_cases he : ∃ x y : Bool × ℕ, x.2 ≤ m ∧ y.2 ≤ m ∧ e = s(ψ x, ψ y)
  · obtain ⟨x, y, hx, hy, rfl⟩ := he
    rw [count_groupBonds_atoms, hbb x y hx hy, Multiset.count_map]
    have hf : (zMS m).filter (fun a => s(ψ x, ψ y) = Sym2.map ψ a) = (zMS m).filter (fun a => s(x, y) = a) := by
      refine Multiset.filter_congr fun a ha => ?_
      obtain ⟨p, q, hp, hq, rfl⟩ := zMS_support m a ha
      simp only [Sym2.map_mk]
      constructor
      · intro h
        rcases Sym2.eq_iff.mp h with ⟨h1, h2⟩ | ⟨h1, h2⟩
        · rw [hinj _ _ hx hp h1, hinj _ _ hy hq h2]
        · rw [hinj _ _ hx hq h1, hinj _ _ hy hp h2, Sym2.eq_swap]
      · intro h; have := congrArg (Sym2.map ψ) h; simpa using this
    rw [hf, ← Multiset.count_eq_card_filter_eq, count_zMS, if_pos ⟨hx, hy⟩]
  · have h1 : e ∉ N.groupBonds N.atoms := by
      intro h
      obtain ⟨a, ha, b, hb, rfl⟩ := mem_groupBonds_atoms h
      obtain ⟨x, hx, rfl⟩ := (hat a).mp ha
      obtain ⟨y, hy, rfl⟩ := (hat b).mp hb
      exact he ⟨x, y, hx, hy, rfl⟩
    have h2 : e ∉ (zMS m).map (Sym2.map ψ) := by
      intro h
      obtain ⟨a, ha, rfl⟩ := Multiset.mem_map.mp h
      obtain ⟨p, q, hp, hq, rfl⟩ := zMS_support m a ha
      exact he ⟨p, q, hp, hq, by simp⟩
    rw [Multiset.count_eq_zero_of_notMem h1, Multiset.count_eq_zero_of_notMem h2]

theorem lab_inj (m : ℕ) {x y : Bool × ℕ} (hx : x.2 ≤ m) (hy : y.2 ≤ m) (h : lab m x = lab m y) : x = y := by
  obtain ⟨a, i⟩ := x; obtain ⟨b, j⟩ := y
  simp only at hx hy
  unfold lab labA labB at h
  cases a <;> cases b <;> simp only [Bool.false_eq_true, ite_false, ite_true] at h <;>
    (split_ifs at h <;> first | (exfalso; omega) | (ext <;> simp <;> omega))

theorem isVineHalf_of_ladder {N : Molecule V D} {m : ℕ} {ψ : Bool × ℕ → V}
    (hinj : ∀ x y : Bool × ℕ, x.2 ≤ m → y.2 ≤ m → ψ x = ψ y → x = y)
    (hat : ∀ w, w ∈ N.atoms ↔ ∃ x : Bool × ℕ, x.2 ≤ m ∧ ψ x = w)
    (hbb : ∀ x y : Bool × ℕ, x.2 ≤ m → y.2 ≤ m → N.bondsBetween (ψ x) (ψ y) = lBB x y) :
    IsVineIIHalfClosure N := by
  classical
  let f : V → ℕ := fun w => if h : ∃ x : Bool × ℕ, x.2 ≤ m ∧ ψ x = w then lab m h.choose else 0
  have hf : ∀ x : Bool × ℕ, x.2 ≤ m → f (ψ x) = lab m x := by
    intro x hx
    have h : ∃ x' : Bool × ℕ, x'.2 ≤ m ∧ ψ x' = ψ x := ⟨x, hx, rfl⟩
    simp only [f, dif_pos h]
    rw [hinj _ _ h.choose_spec.1 hx h.choose_spec.2]
  refine ⟨m, f, ?_, ?_, ?_⟩
  · intro w hw w' hw' hww
    simp only [Finset.mem_coe] at hw hw'
    obtain ⟨x, hx, rfl⟩ := (hat w).mp hw
    obtain ⟨y, hy, rfl⟩ := (hat w').mp hw'
    rw [hf x hx, hf y hy] at hww
    rw [lab_inj m hx hy hww]
  · ext l
    simp only [mem_image, mem_sdiff, mem_range, mem_insert, mem_singleton]
    constructor
    · rintro ⟨w, hw, rfl⟩
      obtain ⟨⟨a, i⟩, hx, rfl⟩ := (hat w).mp hw
      simp only at hx
      rw [hf _ hx]
      unfold lab labA labB
      cases a <;> by_cases hi0 : i = 0 <;> simp [hi0] <;> omega
    · intro hl
      by_cases h2 : l = 2
      · exact ⟨ψ (false, 0), (hat _).mpr ⟨_, by simp, rfl⟩, by rw [hf _ (by simp)]; simp [lab, labA, h2]⟩
      by_cases h3 : l = 3
      · exact ⟨ψ (true, 0), (hat _).mpr ⟨_, by simp, rfl⟩, by rw [hf _ (by simp)]; simp [lab, labB, h3]⟩
      by_cases h4 : l ≤ 3 + m
      · refine ⟨ψ (false, l - 3), (hat _).mpr ⟨_, by simp; omega, rfl⟩, ?_⟩
        rw [hf _ (by simp; omega)]
        simp only [lab, labA, Bool.false_eq_true, ite_false]
        split_ifs <;> omega
      · refine ⟨ψ (true, l - 3 - m), (hat _).mpr ⟨_, by simp; omega, rfl⟩, ?_⟩
        rw [hf _ (by simp; omega)]
        simp only [lab, labB, ite_true]
        split_ifs <;> omega
  · rw [groupBonds_eq_zMS hinj hat hbb, Multiset.map_map, halfClosureIIBonds_eq, ladderBonds_eq_map]
    refine Multiset.map_congr rfl fun e he => ?_
    obtain ⟨p, q, hp, hq, rfl⟩ := zMS_support m e he
    simp only [Function.comp, Sym2.map_map, Sym2.map_mk, hf p hp, hf q hq]

end
end WaveTurbulence.FinalCountG8
