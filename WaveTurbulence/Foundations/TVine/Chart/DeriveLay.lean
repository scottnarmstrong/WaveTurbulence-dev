/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.TVine.Chart.DeriveBase

/-!
# Derivation of the cell decomposition, II: the layout of a T-vine

`Lay M S a b` is N3 Theorem 6 (ii), (iii) for the labelling `v₁ = a` (upper), `v₂ = b` (lower), in ℕ-indexed form:
the extended spine `Z 0 = {b}, Z 1, …, Z r, Z (r+1) = {a}` and the pendant `Y 0, …, Y (s−1)` (`H k = Y k ∪ ⋯`),
with the bond counts of L3's `LayervineStructure`. `lay_of` extracts it from L3's list form.
-/

@[expose] public section
set_option autoImplicit false

namespace WaveTurbulence.TVine.Chart

open Finset VineParamContract Struct

variable {V D : Type} [DecidableEq V] [Fintype D] [DecidableEq D]

theorem mem_unionAll {l : List (Finset V)} {v : V} : v ∈ unionAll l ↔ ∃ P ∈ l, v ∈ P := by
  induction l with
  | nil => simp [unionAll]
  | cons P l ih =>
    change v ∈ P ∪ unionAll l ↔ _
    rw [mem_union, ih]
    simp

/-- **The layout** (N3 Theorem 6 (ii), (iii), ℕ-indexed). -/
structure Lay (M : Molecule V D) (S : Finset V) (a b : V) where
  r : ℕ
  s : ℕ
  Z : ℕ → Finset V
  Y : ℕ → Finset V
  H : ℕ → Finset V
  Z_zero : Z 0 = {b}
  Z_last : Z (r + 1) = {a}
  Z_piece : ∀ i, 1 ≤ i → i ≤ r → Z i ∈ M.pieces S a b
  Y_piece : ∀ k, k < s → Y k ∈ M.pieces S a b
  Z_inj : ∀ i j, 1 ≤ i → i ≤ r → 1 ≤ j → j ≤ r → Z i = Z j → i = j
  Y_inj : ∀ k l, k < s → l < s → Y k = Y l → k = l
  ZY_ne : ∀ i k, 1 ≤ i → i ≤ r → k < s → Z i ≠ Y k
  all : ∀ P ∈ M.pieces S a b, (∃ i, 1 ≤ i ∧ i ≤ r ∧ Z i = P) ∨ (∃ k, k < s ∧ Y k = P)
  mem_H : ∀ k v, v ∈ H k ↔ ∃ l, k ≤ l ∧ l < s ∧ v ∈ Y l
  consec : ∀ i, i ≤ r → crossBonds M (Z i) (Z (i + 1)) = 1 ∨ crossBonds M (Z i) (Z (i + 1)) = 2
  nonconsec : ∀ i j, j ≤ r + 1 → i + 2 ≤ j → crossBonds M (Z i) (Z j) = 0
  one_unique : ∀ i i', i ≤ r → i' ≤ r → crossBonds M (Z i) (Z (i + 1)) = 1 →
    crossBonds M (Z i') (Z (i' + 1)) = 1 → i = i'
  sigma : r = 0 ↔ M.sigma a b = 1
  pend : (s = 0 ∧ ∃ i, 1 ≤ i ∧ i ≤ r ∧ IsCoreBC M (Z i)) ∨
    (1 ≤ s ∧ IsCoreD M (Y (s - 1)) ∧ (∀ k, k + 1 < s → IsRungPiece M (Y k)) ∧
      (∀ k, k + 1 < s → crossBonds M (Y k) (Y (k + 1)) = 2) ∧
      (∀ k l, l < s → k + 2 ≤ l → crossBonds M (Y k) (Y l) = 0) ∧
      (∀ k, k < s → ∃ x x' : V, TwoSingleExits M S (H k) (Y k) x x' ∧
        (k = 0 →
          (∃ i, 1 ≤ i ∧ i ≤ r ∧ x ∈ Z i ∧ x' ∈ Z i ∧ IsJunctionPiece M (Z i) ∧
            crossBonds M (Z i) (S \ Z i) = 6 ∧ ∀ P ∈ M.pieces S a b, crossBonds M P (S \ P) = 6 → P = Z i) ∨
          (∃ i, i ≤ r ∧ crossBonds M (Z i) (Z (i + 1)) = 1 ∧
            ((x ∈ Z i ∧ x' ∈ Z (i + 1)) ∨ (x' ∈ Z i ∧ x ∈ Z (i + 1)))))))

theorem extSpine_getD_succ (a b : V) (sp : List (Finset V)) {i : ℕ} (hi : i < sp.length) :
    (extSpine a b sp).getD (i + 1) ∅ = sp[i] := by
  simp [extSpine, List.getElem?_append_left hi, hi]

theorem extSpine_getD_last (a b : V) (sp : List (Finset V)) : (extSpine a b sp).getD (sp.length + 1) ∅ = {a} := by
  simp [extSpine, List.getD_eq_getElem]

theorem extSpine_length (a b : V) (sp : List (Finset V)) : (extSpine a b sp).length = sp.length + 2 := by
  simp [extSpine]

theorem extSpine_get (a b : V) (sp : List (Finset V)) (i : Fin (extSpine a b sp).length) :
    (extSpine a b sp).get i = (extSpine a b sp).getD i ∅ := by
  simp [List.getD_eq_getElem]

theorem pd_get (pd : List (Finset V)) (k : Fin pd.length) : pd.get k = pd.getD k ∅ := by
  simp [List.getD_eq_getElem]

/-- **Extraction of the layout** from L3's `LayervineStructure` (labelling `v₁ = a`, `v₂ = b`). -/
theorem lay_of {M : Molecule V D} {S : Finset V} {a b : V} (h : LayervineStructure M S a b) :
    Nonempty (Lay M S a b) := by
  obtain ⟨sp, pd, hnd, hpieces, -, -, hcons, hnon, hone, hsig, hpend⟩ := h
  have hlen := extSpine_length a b sp
  let Z : ℕ → Finset V := fun i => (extSpine a b sp).getD i ∅
  let Y : ℕ → Finset V := fun k => pd.getD k ∅
  have hgetZ : ∀ (i : Fin (extSpine a b sp).length), (extSpine a b sp).get i = Z i := extSpine_get a b sp
  have hgetY : ∀ (k : Fin pd.length), pd.get k = Y k := pd_get pd
  have hZsp : ∀ i, (hi : i < sp.length) → Z (i + 1) = sp[i] := fun i hi => extSpine_getD_succ a b sp hi
  have hYpd : ∀ k, (hk : k < pd.length) → Y k = pd[k] := fun k hk => by simp [Y, List.getD_eq_getElem, hk]
  have hmemsp : ∀ P, P ∈ sp ++ pd → P ∈ M.pieces S a b := fun P hP => by
    rw [← hpieces]; exact List.mem_toFinset.mpr hP
  refine ⟨{
    r := sp.length
    s := pd.length
    Z := Z
    Y := Y
    H := fun k => unionAll (pd.drop k)
    Z_zero := rfl
    Z_last := extSpine_getD_last a b sp
    Z_piece := fun i h1 h2 => by
      obtain ⟨i', rfl⟩ : ∃ i', i = i' + 1 := ⟨i - 1, by omega⟩
      rw [hZsp i' (by omega)]
      exact hmemsp _ (List.mem_append_left _ (List.getElem_mem _))
    Y_piece := fun k hk => by
      rw [hYpd k hk]; exact hmemsp _ (List.mem_append_right _ (List.getElem_mem _))
    Z_inj := fun i j h1 h2 h3 h4 he => by
      obtain ⟨i', rfl⟩ : ∃ i', i = i' + 1 := ⟨i - 1, by omega⟩
      obtain ⟨j', rfl⟩ : ∃ j', j = j' + 1 := ⟨j - 1, by omega⟩
      rw [hZsp i' (by omega), hZsp j' (by omega)] at he
      have hnd' := (List.nodup_append.mp hnd).1
      have := (List.Nodup.getElem_inj_iff hnd').mp he
      omega
    Y_inj := fun k l hk hl he => by
      rw [hYpd k hk, hYpd l hl] at he
      have hnd' := (List.nodup_append.mp hnd).2.1
      exact (List.Nodup.getElem_inj_iff hnd').mp he
    ZY_ne := fun i k h1 h2 hk he => by
      obtain ⟨i', rfl⟩ : ∃ i', i = i' + 1 := ⟨i - 1, by omega⟩
      rw [hZsp i' (by omega), hYpd k hk] at he
      have hdis := (List.nodup_append.mp hnd).2.2
      exact hdis _ (List.getElem_mem _) _ (List.getElem_mem _) he
    all := fun P hP => by
      rw [← hpieces, List.mem_toFinset, List.mem_append] at hP
      rcases hP with hP | hP
      · obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hP
        exact Or.inl ⟨i + 1, by omega, by omega, hZsp i hi⟩
      · obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem hP
        exact Or.inr ⟨k, hk, hYpd k hk⟩
    mem_H := fun k v => by
      rw [mem_unionAll]
      constructor
      · rintro ⟨P, hP, hv⟩
        obtain ⟨l, hl, rfl⟩ := List.getElem_of_mem hP
        rw [List.getElem_drop] at hv
        simp only [List.length_drop] at hl
        exact ⟨k + l, by omega, by omega, by rw [hYpd _ (by omega)]; exact hv⟩
      · rintro ⟨l, h1, h2, hv⟩
        refine ⟨pd[l], ?_, by rw [← hYpd l h2]; exact hv⟩
        rw [List.mem_iff_getElem]
        exact ⟨l - k, by simp; omega, by rw [List.getElem_drop]; congr 1; omega⟩
    consec := fun i hi => by
      have := hcons ⟨i, by omega⟩ ⟨i + 1, by omega⟩ rfl
      rwa [hgetZ, hgetZ] at this
    nonconsec := fun i j hj hij => by
      have := hnon ⟨i, by omega⟩ ⟨j, by omega⟩ hij
      rwa [hgetZ, hgetZ] at this
    one_unique := fun i i' hi hi' h1 h2 => by
      have := hone ⟨i, by omega⟩ ⟨i + 1, by omega⟩ ⟨i', by omega⟩ ⟨i' + 1, by omega⟩ rfl rfl
        (by rwa [hgetZ, hgetZ]) (by rwa [hgetZ, hgetZ])
      exact congrArg Fin.val this
    sigma := by rw [← hsig, List.length_eq_zero_iff]
    pend := by
      rcases hpend with ⟨hpd, P, hP, hBC⟩ | ⟨Ys, C, hpdeq, hD, hYs, hc2, hc0, hex⟩
      · left
        refine ⟨by simp [hpd], ?_⟩
        obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hP
        exact ⟨i + 1, by omega, by omega, by rw [hZsp i hi]; exact hBC⟩
      · right
        have hs : pd.length = Ys.length + 1 := by rw [hpdeq]; simp
        refine ⟨by omega, ?_, ?_, ?_, ?_, ?_⟩
        · have : Y (pd.length - 1) = C := by
            rw [hYpd _ (by omega)]; simp only [hpdeq]
            rw [List.getElem_append_right (by first | omega | simp | (simp; omega))]
            simp
          rw [this]; exact hD
        · intro k hk
          rw [hYpd k (by omega)]; simp only [hpdeq]
          rw [List.getElem_append_left (by omega)]
          exact hYs _ (List.getElem_mem _)
        · intro k hk
          have := hc2 ⟨k, by omega⟩ ⟨k + 1, by omega⟩ rfl
          rwa [hgetY, hgetY] at this
        · intro k l hl hkl
          have := hc0 ⟨k, by omega⟩ ⟨l, hl⟩ hkl
          rwa [hgetY, hgetY] at this
        · intro k hk
          obtain ⟨x, x', h2, hatt⟩ := hex ⟨k, hk⟩
          refine ⟨x, x', by rwa [hgetY] at h2, fun hk0 => ?_⟩
          rcases hatt hk0 with ⟨i, h1, h2', h3, h4, h5⟩ | ⟨i, j, hij, h1, h2'⟩
          · left
            refine ⟨i.val + 1, by omega, by omega, ?_⟩
            rw [hZsp i.val i.2]
            simp only [List.get_eq_getElem] at h1 h2' h3 h4 h5
            exact ⟨h1, h2', h3, h4, h5⟩
          · right
            rw [hgetZ, hgetZ] at h1 h2'
            refine ⟨i.val, by omega, ?_⟩
            rw [show (i.val + 1) = j.val from hij]
            exact ⟨h1, h2'⟩ }⟩

end WaveTurbulence.TVine.Chart
