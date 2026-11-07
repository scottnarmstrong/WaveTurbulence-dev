/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.C5VineB
import Mathlib.Tactic

/-! # Prop 9.6, case (5): the joint bonds of the vine (II) template -/

@[expose] public section
set_option autoImplicit false
open Finset
namespace WaveTurbulence.FinalCountG8
open WaveTurbulence.MoleProp4

/-- The undirected bond multiset of the expanded vine (II) template. -/
def Esym (k : ℕ) : Multiset (Sym2 ℕ) :=
  (((VineType.II.expand [k]).bonds.map fun p => s(p.1, p.2) : Multiset (Sym2 ℕ)))

theorem Esym_zero : Esym 0 = {s(0, 2), s(0, 3), s(2, 3), s(2, 3), s(2, 1), s(3, 1)} := by
  simp [Esym, VineType.expand, VineType.template, insertRungs]
  rfl

/-- The bonds of `Esym k` containing a joint. -/
def jointBonds (k : ℕ) : Multiset (Sym2 ℕ) := {s(0, 2), s(0, 3), s(labA k k, 1), s(labB k k, 1)}

theorem filter_rails (c w : ℕ → ℕ) (hc : ∀ i, 2 ≤ c i) (hw : ∀ i, 2 ≤ w i) (k : ℕ) :
    Multiset.filter (fun e : Sym2 ℕ => ¬ ((0 : ℕ) ∉ e ∧ (1 : ℕ) ∉ e))
      ((((List.range (k + 1)).map (fun i => (c i, if i < k then w i else 1)) : List (ℕ × ℕ)).map
        (fun p => s(p.1, p.2)) : List (Sym2 ℕ)) : Multiset (Sym2 ℕ)) = {s(c k, 1)} := by
  rw [List.range_succ, List.map_append, List.map_append, Multiset.filter_coe]
  simp only [List.filter_append]
  have h1 : List.filter (fun e : Sym2 ℕ => decide (¬ ((0 : ℕ) ∉ e ∧ (1 : ℕ) ∉ e)))
      (((List.range k).map (fun i => (c i, if i < k then w i else 1))).map (fun p => s(p.1, p.2))) = [] := by
    rw [List.filter_eq_nil_iff]
    intro e he
    obtain ⟨p, hp, rfl⟩ := List.mem_map.mp he
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hp
    have hik := List.mem_range.mp hi
    have := hc i; have := hw i
    simp only [if_pos hik, Sym2.mem_iff]
    simp; omega
  rw [h1]
  simp only [List.map_cons, List.map_nil, lt_irrefl, if_false, List.nil_append]
  have h2 := hc k
  simp [Sym2.mem_iff]

theorem filter_Esym {k : ℕ} (hk : k ≠ 0) :
    Multiset.filter (fun e : Sym2 ℕ => ¬ ((0 : ℕ) ∉ e ∧ (1 : ℕ) ∉ e)) (Esym k) = jointBonds k := by
  unfold Esym
  rw [expand_II_bonds hk]
  simp only [List.map_append, ← Multiset.coe_add, Multiset.filter_add]
  have hA := filter_rails (fun i => if i = 0 then 2 else 4 + (i - 1)) (fun i => 4 + i)
    (fun i => by split_ifs <;> omega) (fun i => by omega) k
  have hB := filter_rails (fun i => if i = 0 then 3 else 4 + k + (i - 1)) (fun i => 4 + k + i)
    (fun i => by split_ifs <;> omega) (fun i => by omega) k
  rw [hA, hB]
  have hrung : Multiset.filter (fun e : Sym2 ℕ => ¬ ((0 : ℕ) ∉ e ∧ (1 : ℕ) ∉ e))
      ((List.map (fun p : ℕ × ℕ => s(p.1, p.2))
        (List.flatMap (fun p => [p, p]) (List.map (fun i => (4 + i, 4 + k + i)) (List.range k))) : List (Sym2 ℕ)) :
        Multiset (Sym2 ℕ)) = 0 := by
    rw [Multiset.filter_eq_nil]
    intro e he
    obtain ⟨p, hp, rfl⟩ := List.mem_map.mp (Multiset.mem_coe.mp he)
    obtain ⟨q, hq, hpq⟩ := List.mem_flatMap.mp hp
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hq
    have hpq' : p = (4 + i, 4 + k + i) := by simpa using hpq
    subst hpq'
    simp only [Sym2.mem_iff]
    simp
    omega
  rw [hrung]
  have h4 : Multiset.filter (fun e : Sym2 ℕ => ¬ ((0 : ℕ) ∉ e ∧ (1 : ℕ) ∉ e))
      ((List.map (fun p : ℕ × ℕ => s(p.1, p.2)) [(0, 2), (0, 3), (2, 3), (2, 3)] : List (Sym2 ℕ)) : Multiset (Sym2 ℕ))
      = {s(0, 2), s(0, 3)} := by
    simp [Multiset.filter_coe]
    decide
  rw [h4]
  have hc : (if k = 0 then 2 else 4 + (k - 1)) = labA k k := by simp [labA, hk]; omega
  have hc' : (if k = 0 then 3 else 4 + k + (k - 1)) = labB k k := by simp [labB, hk]; omega
  simp only [hc, hc', jointBonds]
  simp only [add_zero, Multiset.insert_eq_cons, Multiset.singleton_add, Multiset.cons_add]

theorem filter_Esym_all (k : ℕ) :
    Multiset.filter (fun e : Sym2 ℕ => ¬ ((0 : ℕ) ∉ e ∧ (1 : ℕ) ∉ e)) (Esym k) = jointBonds k := by
  by_cases hk : k = 0
  · subst hk
    rw [Esym_zero]
    simp [jointBonds, labA, labB]
  · exact filter_Esym hk

/-- `E + {s(2,3)} = H + J`: the full vine bonds are the half-closure bonds with the joint bonds. -/
theorem halfClosure_add_joint (k : ℕ) :
    halfClosureIIBonds k + jointBonds k = Esym k + {s(2, 3)} := by
  have h1 := Multiset.filter_add_not (fun e : Sym2 ℕ => (0 : ℕ) ∉ e ∧ (1 : ℕ) ∉ e) (Esym k)
  rw [filter_Esym_all] at h1
  unfold halfClosureIIBonds
  change (Multiset.filter (fun e : Sym2 ℕ => (0 : ℕ) ∉ e ∧ (1 : ℕ) ∉ e) (Esym k) + {s(2, 3)}) + jointBonds k = _
  rw [add_right_comm, h1]

end WaveTurbulence.FinalCountG8
