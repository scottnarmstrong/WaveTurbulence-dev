/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.Spine.VineDelInsert
import Mathlib.Tactic
/-! # Deletion connectivity is preserved by rung insertion -/
public section
set_option autoImplicit false
namespace WaveTurbulence.LGSpine
open WaveTurbulence.Vine

theorem mem_usOf {T : VineTemplate} {k v : ℕ} : v ∈ usOf T k ↔ ∃ i, i < k ∧ v = T.n + i := by
  simp only [usOf, List.mem_map, List.mem_range]
  exact ⟨fun ⟨i, hi, h⟩ => ⟨i, hi, h.symm⟩, fun ⟨i, hi, h⟩ => ⟨i, hi, h.symm⟩⟩

theorem mem_vsOf {T : VineTemplate} {k v : ℕ} : v ∈ vsOf T k ↔ ∃ i, i < k ∧ v = T.n + k + i := by
  simp only [vsOf, List.mem_map, List.mem_range]
  exact ⟨fun ⟨i, hi, h⟩ => ⟨i, hi, h.symm⟩, fun ⟨i, hi, h⟩ => ⟨i, hi, h.symm⟩⟩

theorem new_cases {T : VineTemplate} {k v : ℕ} (h1 : T.n ≤ v) (h2 : v < T.n + 2 * k) :
    v ∈ usOf T k ∨ v ∈ vsOf T k := by
  by_cases h : v < T.n + k
  · exact Or.inl (mem_usOf.mpr ⟨v - T.n, by omega, by omega⟩)
  · exact Or.inr (mem_vsOf.mpr ⟨v - (T.n + k), by omega, by omega⟩)

theorem attach_u (T : VineTemplate) (s : (ℕ × ℕ) × (ℕ × ℕ)) {k : ℕ} (hk : k ≠ 0)
    (P : ℕ → Prop) (f : ℕ × ℕ → Bool) (hPus : ∀ x ∈ usOf T k, P x)
    (hf1 : ∀ e ∈ railBonds s.1.1 (usOf T k) s.1.2, f e = true)
    (hr : ∀ i, i < k → f (T.n + i, T.n + k + i) = true) (o : ℕ)
    (ho : o = s.1.1 ∨ o = s.1.2) (hPo : P o) (v : ℕ)
    (hv : v ∈ usOf T k ∨ (v ∈ vsOf T k ∧ P v)) :
    Relation.EqvGen (FAdj P f (insertRungs T s k).bonds) v o := by
  have hu : ∀ u ∈ usOf T k, Relation.EqvGen (FAdj P f (insertRungs T s k).bonds) u o := by
    intro u hu
    rcases ho with rfl | rfl
    · exact Relation.EqvGen.symm _ _ (fpath_mono (fun _ h => h) (fun _ h => h)
        (fun _ h => first_rail_mem T s hk h)
        (rail_fprefix P f s.1.2 (usOf T k) s.1.1 hPo hPus hf1 u hu))
    · exact fpath_mono (fun _ h => h) (fun _ h => h) (fun _ h => first_rail_mem T s hk h)
        (rail_fsuffix P f s.1.2 (usOf T k) s.1.1 hPo hPus hf1 u hu)
  rcases hv with hv | ⟨hv, hPv⟩
  · exact hu v hv
  · obtain ⟨i, hi, rfl⟩ := mem_vsOf.mp hv
    have hui : T.n + i ∈ usOf T k := mem_usOf.mpr ⟨i, hi, rfl⟩
    exact Relation.EqvGen.trans _ _ _
      (Relation.EqvGen.symm _ _ (fpath_edge (hPus _ hui) hPv (rung_mem T s hk hi) (hr i hi)))
      (hu _ hui)

theorem attach_v (T : VineTemplate) (s : (ℕ × ℕ) × (ℕ × ℕ)) {k : ℕ} (hk : k ≠ 0)
    (P : ℕ → Prop) (f : ℕ × ℕ → Bool) (hPvs : ∀ x ∈ vsOf T k, P x)
    (hf2 : ∀ e ∈ railBonds s.2.1 (vsOf T k) s.2.2, f e = true)
    (hr : ∀ i, i < k → f (T.n + i, T.n + k + i) = true) (o : ℕ)
    (ho : o = s.2.1 ∨ o = s.2.2) (hPo : P o) (v : ℕ)
    (hv : v ∈ vsOf T k ∨ (v ∈ usOf T k ∧ P v)) :
    Relation.EqvGen (FAdj P f (insertRungs T s k).bonds) v o := by
  have hu : ∀ u ∈ vsOf T k, Relation.EqvGen (FAdj P f (insertRungs T s k).bonds) u o := by
    intro u hu
    rcases ho with rfl | rfl
    · exact Relation.EqvGen.symm _ _ (fpath_mono (fun _ h => h) (fun _ h => h)
        (fun _ h => second_rail_mem T s hk h)
        (rail_fprefix P f s.2.2 (vsOf T k) s.2.1 hPo hPvs hf2 u hu))
    · exact fpath_mono (fun _ h => h) (fun _ h => h) (fun _ h => second_rail_mem T s hk h)
        (rail_fsuffix P f s.2.2 (vsOf T k) s.2.1 hPo hPvs hf2 u hu)
  rcases hv with hv | ⟨hv, hPv⟩
  · exact hu v hv
  · obtain ⟨i, hi, rfl⟩ := mem_usOf.mp hv
    have hvi : T.n + k + i ∈ vsOf T k := mem_vsOf.mpr ⟨i, hi, rfl⟩
    exact Relation.EqvGen.trans _ _ _
      (fpath_edge hPv (hPvs _ hvi) (rung_mem T s hk hi) (hr i hi)) (hu _ hvi)

theorem conn_of_attach {P : ℕ → Prop} {f : ℕ × ℕ → Bool} {es : List (ℕ × ℕ)} {m n : ℕ}
    (hold : ∀ p q, p < m → q < m → P p → P q → Relation.EqvGen (FAdj P f es) p q)
    (hatt : ∀ v, v < n → P v → ∃ o, o < m ∧ P o ∧ Relation.EqvGen (FAdj P f es) v o) :
    ∀ p q, p < n → q < n → P p → P q → Relation.EqvGen (FAdj P f es) p q := by
  intro p q hp hq hPp hPq
  obtain ⟨o1, h1, hP1, e1⟩ := hatt p hp hPp
  obtain ⟨o2, h2, hP2, e2⟩ := hatt q hq hPq
  exact Relation.EqvGen.trans _ _ _ e1
    (Relation.EqvGen.trans _ _ _ (hold o1 o2 h1 h2 hP1 hP2) (Relation.EqvGen.symm _ _ e2))

/-- Connectivity after deleting the vertex `w`. -/
@[expose] def ConnDel (T : VineTemplate) (w : ℕ) : Prop :=
  ∀ p q, p < T.n → q < T.n → p ≠ w → q ≠ w →
    Relation.EqvGen (FAdj (· ≠ w) (fun _ => true) T.bonds) p q

/-- Connectivity after removing the bond value `e`. -/
@[expose] def ConnAvoid (T : VineTemplate) (e : ℕ × ℕ) : Prop :=
  ∀ p q, p < T.n → q < T.n →
    Relation.EqvGen (FAdj (· < T.n) (fun x => decide (x ≠ e)) T.bonds) p q

/-- Facts about a slot used by insertion. -/
@[expose] def SlotOK (T : VineTemplate) (s : (ℕ × ℕ) × (ℕ × ℕ)) : Prop :=
  s.1.1 < T.n ∧ s.1.2 < T.n ∧ s.2.1 < T.n ∧ s.2.2 < T.n ∧ s.1.1 ≠ s.1.2 ∧ s.2.1 ≠ s.2.2

theorem rail1_new (T : VineTemplate) (s : (ℕ × ℕ) × (ℕ × ℕ)) {k : ℕ} (hk : k ≠ 0) :
    ∀ e ∈ railBonds s.1.1 (usOf T k) s.1.2, T.n ≤ e.1 ∨ T.n ≤ e.2 := by
  have hne : usOf T k ≠ [] := by
    simp only [usOf]; intro h
    have := congrArg List.length h; simp at this; omega
  intro e he
  rcases railBonds_new _ _ _ hne e he with h | h
  · obtain ⟨i, _, hi⟩ := mem_usOf.mp h; omega
  · obtain ⟨i, _, hi⟩ := mem_usOf.mp h; omega

theorem rail2_new (T : VineTemplate) (s : (ℕ × ℕ) × (ℕ × ℕ)) {k : ℕ} (hk : k ≠ 0) :
    ∀ e ∈ railBonds s.2.1 (vsOf T k) s.2.2, T.n ≤ e.1 ∨ T.n ≤ e.2 := by
  have hne : vsOf T k ≠ [] := by
    simp only [vsOf]; intro h
    have := congrArg List.length h; simp at this; omega
  intro e he
  rcases railBonds_new _ _ _ hne e he with h | h
  · obtain ⟨i, _, hi⟩ := mem_vsOf.mp h; omega
  · obtain ⟨i, _, hi⟩ := mem_vsOf.mp h; omega

end WaveTurbulence.LGSpine
