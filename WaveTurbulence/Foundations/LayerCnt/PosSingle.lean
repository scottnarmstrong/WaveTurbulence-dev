/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.LayerCnt.PosCut
import Mathlib.Tactic

/-! # The rail bonds of an inserted ladder are single (TARGET layervine, L1531)
-/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.LayerCnt
open WaveTurbulence.Vine

theorem rail_eq_map (a b k : ℕ) (g : ℕ → ℕ) :
    railBonds a ((List.range k).map g) b =
      (List.range (k + 1)).map (fun m => (railSeq a b k g m, railSeq a b k g (m + 1))) := by
  apply List.ext_getElem
  · simp [railBonds]
  · intro i h1 h2
    have hi : i < k + 1 := by simpa using h2
    simp only [railBonds, List.getElem_zip, List.getElem_map, List.getElem_range]
    congr 1
    · cases i with
      | zero => simp [railSeq]
      | succ j =>
        simp only [railSeq, List.getElem_cons_succ, List.getElem_map, List.getElem_range]
        rw [if_neg (by omega), if_pos (by omega)]
        simp
    · simp only [railSeq, List.getElem_append, List.getElem_map, List.getElem_range]
      by_cases hik : i < k
      · rw [dif_pos (by simpa using hik), if_neg (by omega), if_pos (by omega)]
        simp
      · rw [dif_neg (by simpa using hik), if_neg (by omega), if_neg (by omega)]
        simp

theorem railSeq_inj {a b k n : ℕ} {g : ℕ → ℕ} (hab : a ≠ b) (ha : a < n) (hb : b < n)
    (hg : ∀ i, n ≤ g i ∧ ∀ i', g i = g i' → i = i') {m m' : ℕ} (hm : m ≤ k + 1) (hm' : m' ≤ k + 1)
    (h : railSeq a b k g m = railSeq a b k g m') : m = m' := by
  have hcases : ∀ m, m ≤ k + 1 → m = 0 ∨ (1 ≤ m ∧ m ≤ k) ∨ m = k + 1 := fun m hm => by omega
  rcases hcases m hm with rfl | ⟨h1, h2⟩ | rfl <;> rcases hcases m' hm' with rfl | ⟨h3, h4⟩ | rfl
  · rfl
  · simp only [railSeq, if_true] at h
    rw [if_neg (by omega), if_pos h4] at h
    have := (hg (m' - 1)).1; omega
  · simp only [railSeq, if_true] at h
    rw [if_neg (by omega), if_neg (by omega)] at h
    exact absurd h hab
  · simp only [railSeq, if_true] at h
    rw [if_neg (by omega), if_pos h2] at h
    have := (hg (m - 1)).1; omega
  · simp only [railSeq] at h
    rw [if_neg (by omega), if_pos h2, if_neg (by omega), if_pos h4] at h
    have := (hg (m - 1)).2 _ h; omega
  · simp only [railSeq] at h
    rw [if_neg (by omega), if_pos h2, if_neg (by omega), if_neg (by omega)] at h
    have := (hg (m - 1)).1; omega
  · simp only [railSeq, if_true] at h
    rw [if_neg (by omega), if_neg (by omega)] at h
    exact absurd h.symm hab
  · simp only [railSeq] at h
    rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_pos h4] at h
    have := (hg (m' - 1)).1; omega
  · rfl


theorem count_zero_sep (L : List (ℕ × ℕ)) (e : ℕ × ℕ) (P : ℕ → Prop)
    (h : (∀ p ∈ L, P p.1 ∨ P p.2) ∧ (¬ P e.1 ∧ ¬ P e.2) ∨ (∀ p ∈ L, ¬ P p.1 ∧ ¬ P p.2) ∧ (P e.1 ∨ P e.2)) :
    (L.map (fun p => s(p.1, p.2))).count s(e.1, e.2) = 0 := by
  apply List.count_eq_zero_of_not_mem
  intro hm
  obtain ⟨p, hp, hpe⟩ := List.mem_map.mp hm
  rcases h with ⟨hL, he⟩ | ⟨hL, he⟩
  · have := hL p hp
    rcases Sym2.eq_iff.mp hpe with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> rw [h1, h2] at this <;> tauto
  · have := hL p hp
    rcases Sym2.eq_iff.mp hpe with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> rw [h1, h2] at this <;> tauto

theorem rail_edge_single {a b k n : ℕ} {g : ℕ → ℕ} (hab : a ≠ b) (ha : a < n) (hb : b < n)
    (hg : ∀ i, n ≤ g i ∧ ∀ i', g i = g i' → i = i') {j : ℕ} (hj : j ≤ k) :
    ((railBonds a ((List.range k).map g) b).map (fun p => s(p.1, p.2))).count
      s((railEdge a b k g j).1, (railEdge a b k g j).2) ≤ 1 := by
  rw [rail_eq_map, List.map_map]
  have hnd : ((List.range (k + 1)).map ((fun p : ℕ × ℕ => s(p.1, p.2)) ∘
      (fun m => (railSeq a b k g m, railSeq a b k g (m + 1))))).Nodup := by
    apply List.Nodup.map_on _ (List.nodup_range)
    intro m hm m' hm' h
    have hm1 := List.mem_range.mp hm
    have hm2 := List.mem_range.mp hm'
    simp only [Function.comp] at h
    rcases Sym2.eq_iff.mp h with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact railSeq_inj hab ha hb hg (by omega) (by omega) h1
    · have e1 := railSeq_inj hab ha hb hg (by omega) (by omega) h1
      have e2 := railSeq_inj hab ha hb hg (by omega) (by omega) h2
      omega
  exact List.nodup_iff_count_le_one.mp hnd _


theorem railSeq_cases {a b k : ℕ} {g : ℕ → ℕ} {m : ℕ} (hm : m ≤ k + 1) :
    railSeq a b k g m = a ∨ railSeq a b k g m = b ∨ ∃ i < k, railSeq a b k g m = g i := by
  unfold railSeq
  split_ifs with h1 h2
  · exact Or.inl rfl
  · exact Or.inr (Or.inr ⟨m - 1, by omega, rfl⟩)
  · exact Or.inr (Or.inl rfl)

theorem edge_has_new {a b k : ℕ} {g : ℕ → ℕ} (hk : k ≠ 0) {j : ℕ} (hj : j ≤ k) :
    ∃ i < k, (railEdge a b k g j).1 = g i ∨ (railEdge a b k g j).2 = g i := by
  unfold railEdge railSeq
  by_cases h0 : j = 0
  · subst h0; exact ⟨0, by omega, Or.inr (by simp; omega)⟩
  · exact ⟨j - 1, by omega, Or.inl (by rw [if_neg h0, if_pos hj])⟩

/-- The rail bonds at position `j` of the first rail are single in the inserted template. -/
theorem pos_symsingle1 {T : VineTemplate} {s : (ℕ × ℕ) × (ℕ × ℕ)} {k j : ℕ} (hk : k ≠ 0) (hj : j ≤ k)
    (hbdd : ∀ e ∈ T.bonds, e.1 < T.n ∧ e.2 < T.n) (hends : ∀ v ∈ slotEnds s, v < T.n)
    (hxy : s.1.1 ≠ s.1.2) :
    SymSingle (insertRungs T s k) (railEdge s.1.1 s.1.2 k (fun i => T.n + i) j) := by
  have hxn : s.1.1 < T.n := hends _ (by simp [slotEnds])
  have hyn : s.1.2 < T.n := hends _ (by simp [slotEnds])
  unfold SymSingle
  simp only [insertRungs, hk, ite_false, List.map_append, List.count_append]
  set e := railEdge s.1.1 s.1.2 k (fun i => T.n + i) j with he
  have hB := rail_edge_single (a := s.1.1) (b := s.1.2) (k := k) (n := T.n) (g := fun i => T.n + i)
    hxy hxn hyn (fun i => ⟨by omega, fun i' h => by simpa using h⟩) hj
  obtain ⟨i0, hi0, hnew⟩ := edge_has_new (a := s.1.1) (b := s.1.2) (g := fun i => T.n + i) hk hj
  have hatoms : ∀ x, (x = e.1 ∨ x = e.2) → x < T.n ∨ (T.n ≤ x ∧ x < T.n + k) := by
    intro x hx
    have hc : ∀ m ≤ k + 1, railSeq s.1.1 s.1.2 k (fun i => T.n + i) m < T.n ∨
        (T.n ≤ railSeq s.1.1 s.1.2 k (fun i => T.n + i) m ∧
          railSeq s.1.1 s.1.2 k (fun i => T.n + i) m < T.n + k) := by
      intro m hm
      rcases railSeq_cases (a := s.1.1) (b := s.1.2) (g := fun i => T.n + i) hm with h | h | ⟨i, hi, h⟩
      · left; rw [h]; exact hxn
      · left; rw [h]; exact hyn
      · right; rw [h]; exact ⟨by omega, by omega⟩
    rcases hx with rfl | rfl
    · exact hc j (by omega)
    · exact hc (j + 1) (by omega)
  have hA : (((T.bonds.erase s.1).erase s.2).map (fun p => s(p.1, p.2))).count s(e.1, e.2) = 0 := by
    apply count_zero_sep _ _ (fun x => T.n ≤ x)
    right
    refine ⟨fun p hp => ?_, ?_⟩
    · have := hbdd p (List.mem_of_mem_erase (List.mem_of_mem_erase hp)); omega
    · rcases hnew with h | h
      · left; show T.n ≤ e.1; rw [h]; omega
      · right; show T.n ≤ e.2; rw [h]; omega
  have hC : ((railBonds s.2.1 ((List.range k).map (T.n + k + ·)) s.2.2).map (fun p => s(p.1, p.2))).count
      s(e.1, e.2) = 0 := by
    apply count_zero_sep _ _ (fun x => T.n + k ≤ x ∧ x < T.n + 2 * k)
    left
    refine ⟨fun p hp => ?_, ?_⟩
    · obtain ⟨m, hm, rfl⟩ := mem_railBonds_range hp
      have hv : ∀ m ≤ k + 1, True := fun _ _ => trivial
      by_cases h0 : m = 0
      · subst h0; right; simp only [railSeq]; rw [if_neg (by omega), if_pos (by omega)]; omega
      · left; simp only [railSeq]; rw [if_neg h0, if_pos (by omega)]; omega
    · constructor
      · intro h; have := hatoms e.1 (Or.inl rfl); omega
      · intro h; have := hatoms e.2 (Or.inr rfl); omega
  have hD : (((List.zip ((List.range k).map (T.n + ·)) ((List.range k).map (T.n + k + ·))).flatMap
      (fun p => [p, p])).map (fun p => s(p.1, p.2))).count s(e.1, e.2) = 0 := by
    apply count_zero_sep _ _ (fun x => T.n + k ≤ x ∧ x < T.n + 2 * k)
    left
    refine ⟨fun p hp => ?_, ?_⟩
    · rw [List.mem_flatMap] at hp
      obtain ⟨q, hq, hpq⟩ := hp
      have hpq' : p = q := by simpa using hpq
      subst hpq'
      rw [List.zip_map'] at hq
      obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hq
      right; have := List.mem_range.mp hi; simp only; omega
    · constructor
      · intro h; have := hatoms e.1 (Or.inl rfl); omega
      · intro h; have := hatoms e.2 (Or.inr rfl); omega
  rw [hA, hC, hD]
  simpa using hB


/-- The rail bonds at position `j` of the second rail are single in the inserted template. -/
theorem pos_symsingle2 {T : VineTemplate} {s : (ℕ × ℕ) × (ℕ × ℕ)} {k j : ℕ} (hk : k ≠ 0) (hj : j ≤ k)
    (hbdd : ∀ e ∈ T.bonds, e.1 < T.n ∧ e.2 < T.n) (hends : ∀ v ∈ slotEnds s, v < T.n)
    (hxy : s.2.1 ≠ s.2.2) :
    SymSingle (insertRungs T s k) (railEdge s.2.1 s.2.2 k (fun i => T.n + k + i) j) := by
  have hxn : s.2.1 < T.n := hends _ (by simp [slotEnds])
  have hyn : s.2.2 < T.n := hends _ (by simp [slotEnds])
  unfold SymSingle
  simp only [insertRungs, hk, ite_false, List.map_append, List.count_append]
  set e := railEdge s.2.1 s.2.2 k (fun i => T.n + k + i) j with he
  have hB := rail_edge_single (a := s.2.1) (b := s.2.2) (k := k) (n := T.n) (g := fun i => T.n + k + i)
    hxy hxn hyn (fun i => ⟨by omega, fun i' h => by simpa using h⟩) hj
  obtain ⟨i0, hi0, hnew⟩ := edge_has_new (a := s.2.1) (b := s.2.2) (g := fun i => T.n + k + i) hk hj
  have hatoms : ∀ x, (x = e.1 ∨ x = e.2) → x < T.n ∨ (T.n + k ≤ x ∧ x < T.n + 2 * k) := by
    intro x hx
    have hc : ∀ m ≤ k + 1, railSeq s.2.1 s.2.2 k (fun i => T.n + k + i) m < T.n ∨
        (T.n + k ≤ railSeq s.2.1 s.2.2 k (fun i => T.n + k + i) m ∧
          railSeq s.2.1 s.2.2 k (fun i => T.n + k + i) m < T.n + 2 * k) := by
      intro m hm
      rcases railSeq_cases (a := s.2.1) (b := s.2.2) (g := fun i => T.n + k + i) hm with h | h | ⟨i, hi, h⟩
      · left; rw [h]; exact hxn
      · left; rw [h]; exact hyn
      · right; rw [h]; exact ⟨by omega, by omega⟩
    rcases hx with rfl | rfl
    · exact hc j (by omega)
    · exact hc (j + 1) (by omega)
  have hA : (((T.bonds.erase s.1).erase s.2).map (fun p => s(p.1, p.2))).count s(e.1, e.2) = 0 := by
    apply count_zero_sep _ _ (fun x => T.n ≤ x)
    right
    refine ⟨fun p hp => ?_, ?_⟩
    · have := hbdd p (List.mem_of_mem_erase (List.mem_of_mem_erase hp)); omega
    · rcases hnew with h | h
      · left; show T.n ≤ e.1; rw [h]; omega
      · right; show T.n ≤ e.2; rw [h]; omega
  have hC : ((railBonds s.1.1 ((List.range k).map (T.n + ·)) s.1.2).map (fun p => s(p.1, p.2))).count
      s(e.1, e.2) = 0 := by
    apply count_zero_sep _ _ (fun x => T.n ≤ x ∧ x < T.n + k)
    left
    refine ⟨fun p hp => ?_, ?_⟩
    · obtain ⟨m, hm, rfl⟩ := mem_railBonds_range hp
      by_cases h0 : m = 0
      · subst h0; right; simp only [railSeq]; rw [if_neg (by omega), if_pos (by omega)]; omega
      · left; simp only [railSeq]; rw [if_neg h0, if_pos (by omega)]; omega
    · constructor
      · intro h; have := hatoms e.1 (Or.inl rfl); omega
      · intro h; have := hatoms e.2 (Or.inr rfl); omega
  have hD : (((List.zip ((List.range k).map (T.n + ·)) ((List.range k).map (T.n + k + ·))).flatMap
      (fun p => [p, p])).map (fun p => s(p.1, p.2))).count s(e.1, e.2) = 0 := by
    apply count_zero_sep _ _ (fun x => T.n ≤ x ∧ x < T.n + k)
    left
    refine ⟨fun p hp => ?_, ?_⟩
    · rw [List.mem_flatMap] at hp
      obtain ⟨q, hq, hpq⟩ := hp
      have hpq' : p = q := by simpa using hpq
      subst hpq'
      rw [List.zip_map'] at hq
      obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hq
      left; have := List.mem_range.mp hi; simp only; omega
    · constructor
      · intro h; have := hatoms e.1 (Or.inl rfl); omega
      · intro h; have := hatoms e.2 (Or.inr rfl); omega
  rw [hA, hC, hD]
  simpa using hB

end WaveTurbulence.LayerCnt
