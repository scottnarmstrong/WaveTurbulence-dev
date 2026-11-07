/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.WaveB.Molecules
public import WaveTurbulence.Foundations.LayerCnt.TVCount
import Mathlib.Tactic

/-!
# CLASSCOUNT: sizes of expanded vine templates

`(X.expand k).n = X.template.n + 2 Σ k` (for `k` of the length of the slots), the number of bonds is at most
`28 + 3 n`, and the template data are bounded: at most `3` slots, at most `15` atoms.
-/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.ClassCount
open WaveTurbulence

theorem insertRungs_n (T : VineTemplate) (s : (ℕ × ℕ) × (ℕ × ℕ)) (k : ℕ) :
    (insertRungs T s k).n = T.n + 2 * k := by
  unfold insertRungs
  split_ifs with h
  · subst h; simp
  · rfl

theorem insertRungs_slots (T : VineTemplate) (s : (ℕ × ℕ) × (ℕ × ℕ)) (k : ℕ) :
    (insertRungs T s k).slots = T.slots := by
  unfold insertRungs; split_ifs <;> rfl

theorem railBonds_length (z : ℕ) (ws : List ℕ) (z' : ℕ) : (railBonds z ws z').length = ws.length + 1 := by
  unfold railBonds
  rw [List.length_zip]; simp

theorem length_flatMap_dup (Z : List (ℕ × ℕ)) : (Z.flatMap (fun p => [p, p])).length = 2 * Z.length := by
  induction Z with
  | nil => simp
  | cons a Z ih => simp only [List.flatMap_cons, List.length_append, ih, List.length_cons, List.length_nil]; omega

theorem insertRungs_bonds_le (T : VineTemplate) (s : (ℕ × ℕ) × (ℕ × ℕ)) (k : ℕ) (A : ℕ)
    (h : T.bonds.length ≤ A + 3 * T.n) :
    (insertRungs T s k).bonds.length ≤ A + 3 * (insertRungs T s k).n := by
  unfold insertRungs
  split_ifs with hk
  · exact h
  · simp only [List.length_append, railBonds_length, List.length_map, List.length_range,
      length_flatMap_dup, List.length_zip]
    have h1 : ((T.bonds.erase s.1).erase s.2).length ≤ T.bonds.length :=
      (List.length_erase_le).trans List.length_erase_le
    have : 1 ≤ k := Nat.pos_of_ne_zero hk
    simp only [min_self]
    omega

theorem expand_foldl_bonds_le (X : VineType) (A : ℕ) :
    ∀ (L : List (((ℕ × ℕ) × (ℕ × ℕ)) × ℕ)) (T : VineTemplate), T.bonds.length ≤ A + 3 * T.n →
      (L.foldl (fun T sk => insertRungs T sk.1 sk.2) T).bonds.length ≤
        A + 3 * (L.foldl (fun T sk => insertRungs T sk.1 sk.2) T).n
  | [], T, h => h
  | sk :: L, T, h => by
    simp only [List.foldl_cons]
    exact expand_foldl_bonds_le X A L _ (insertRungs_bonds_le T sk.1 sk.2 A h)

theorem expand_bonds_le (X : VineType) (k : List ℕ) :
    (X.expand k).bonds.length ≤ 28 + 3 * (X.expand k).n := by
  unfold VineType.expand
  refine expand_foldl_bonds_le X 28 _ _ ?_
  cases X <;> simp [VineType.template]


theorem foldl_n (L : List (((ℕ × ℕ) × (ℕ × ℕ)) × ℕ)) (T : VineTemplate) :
    (L.foldl (fun T sk => insertRungs T sk.1 sk.2) T).n = T.n + 2 * (L.map Prod.snd).sum := by
  induction L generalizing T with
  | nil => simp
  | cons sk L ih =>
    simp only [List.foldl_cons, ih, insertRungs_n, List.map_cons, List.sum_cons]
    ring

theorem expand_n (X : VineType) (k : List ℕ) (hk : k.length = X.template.slots.length) :
    (X.expand k).n = X.template.n + 2 * k.sum := by
  unfold VineType.expand
  rw [foldl_n]
  congr 2
  have : (X.template.slots.zip k).map Prod.snd = k := by
    rw [List.map_snd_zip]; omega
  rw [this]

theorem template_slots_le (X : VineType) : X.template.slots.length ≤ 3 := by
  cases X <;> simp [VineType.template]

theorem template_n_ge (X : VineType) : 2 ≤ X.template.n := by
  cases X <;> simp [VineType.template]

theorem expand_n_ge (X : VineType) (k : List ℕ) (hk : k.length = X.template.slots.length) :
    2 ≤ (X.expand k).n := by
  rw [expand_n X k hk]; have := template_n_ge X; omega

theorem expand_entry_le (X : VineType) (k : List ℕ) (hk : k.length = X.template.slots.length) {x : ℕ}
    (hx : x ∈ k) : 2 * x + 2 ≤ (X.expand k).n := by
  rw [expand_n X k hk]
  have := List.le_sum_of_mem hx
  have := template_n_ge X
  omega

end WaveTurbulence.ClassCount
