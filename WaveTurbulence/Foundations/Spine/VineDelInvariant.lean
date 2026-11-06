/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.Spine.VineDelStep
import Mathlib.Tactic
/-! # Insertion step for the deletion-connectivity invariant -/
public section
set_option autoImplicit false
namespace WaveTurbulence.LGSpine
open WaveTurbulence.Vine

theorem usOf_ge {T : VineTemplate} {k x : ℕ} (h : x ∈ usOf T k) : T.n ≤ x ∧ x < T.n + k := by
  obtain ⟨i, hi, rfl⟩ := mem_usOf.mp h; omega

theorem vsOf_ge {T : VineTemplate} {k x : ℕ} (h : x ∈ vsOf T k) :
    T.n + k ≤ x ∧ x < T.n + 2 * k := by
  obtain ⟨i, hi, rfl⟩ := mem_vsOf.mp h; omega

theorem connDel_insert_old (T : VineTemplate) (s : (ℕ × ℕ) × (ℕ × ℕ)) {k : ℕ} (hk : k ≠ 0)
    (hs : SlotOK T s) {w : ℕ} (hw : w < T.n) (hc : ConnDel T w) :
    ConnDel (insertRungs T s k) w := by
  have hn : (insertRungs T s k).n = T.n + 2 * k := insertRungs_atoms T s k
  rw [ConnDel, hn]
  have hold : ∀ p q, p < T.n → q < T.n → p ≠ w → q ≠ w →
      Relation.EqvGen (FAdj (· ≠ w) (fun _ => true) (insertRungs T s k).bonds) p q := by
    intro p q hp hq hpw hqw
    refine lift_path T s hk (· ≠ w) (· ≠ w) (fun _ h => h) (fun _ => true) (fun _ => true) (fun _ h => h)
      (fun _ => ⟨fun x hx => by have := usOf_ge hx; omega, fun _ _ => rfl⟩)
      (fun _ => ⟨fun x hx => by have := vsOf_ge hx; omega, fun _ _ => rfl⟩) (hc p q hp hq hpw hqw)
  have hatt : ∀ v, v < T.n + 2 * k → v ≠ w →
      ∃ o, o < T.n ∧ o ≠ w ∧
        Relation.EqvGen (FAdj (· ≠ w) (fun _ => true) (insertRungs T s k).bonds) v o := by
    intro v hv hvw
    by_cases hvo : v < T.n
    · exact ⟨v, hvo, hvw, Relation.EqvGen.refl _⟩
    · have hnew := new_cases (by omega) hv
      have hex : ∃ o, (o = s.1.1 ∨ o = s.1.2) ∧ o ≠ w ∧ o < T.n := by
        by_cases h : s.1.1 = w
        · exact ⟨s.1.2, Or.inr rfl, fun h' => hs.2.2.2.2.1 (h.trans h'.symm), hs.2.1⟩
        · exact ⟨s.1.1, Or.inl rfl, h, hs.1⟩
      obtain ⟨o, ho, how, hoT⟩ := hex
      refine ⟨o, hoT, how, attach_u T s hk (· ≠ w) (fun _ => true)
        (fun x hx => by have := usOf_ge hx; omega) (fun _ _ => rfl) (fun _ _ => rfl) o ho how v ?_⟩
      rcases hnew with h | h
      · exact Or.inl h
      · exact Or.inr ⟨h, hvw⟩
  intro p q hp hq hpw hqw
  exact conn_of_attach (m := T.n) (n := T.n + 2 * k) (fun p q hp hq a b => hold p q hp hq a b)
    (fun v hv hP => hatt v hv hP) p q hp hq hpw hqw

theorem connAvoid_insert (T : VineTemplate) (s : (ℕ × ℕ) × (ℕ × ℕ)) {k : ℕ} (hk : k ≠ 0)
    (hs : SlotOK T s) (t : ℕ × ℕ) (ht : t.1 < T.n ∧ t.2 < T.n) (hc : ConnAvoid T t) :
    ConnAvoid (insertRungs T s k) t := by
  have hn : (insertRungs T s k).n = T.n + 2 * k := insertRungs_atoms T s k
  have hnt : ∀ e : ℕ × ℕ, (T.n ≤ e.1 ∨ T.n ≤ e.2) → decide (e ≠ t) = true := by
    intro e he
    simp only [decide_eq_true_eq]
    intro h; subst h; omega
  unfold ConnAvoid
  simp only [hn]
  have hold : ∀ p q, p < T.n → q < T.n →
      Relation.EqvGen (FAdj (· < T.n + 2 * k) (fun x => decide (x ≠ t))
        (insertRungs T s k).bonds) p q := by
    intro p q hp hq
    exact lift_path T s hk (· < T.n) (· < T.n + 2 * k) (fun x h => by omega) _ _ (fun _ h => h)
      (fun _ => ⟨fun x hx => by have := usOf_ge hx; omega,
        fun e he => hnt e (rail1_new T s hk e he)⟩)
      (fun _ => ⟨fun x hx => by have := vsOf_ge hx; omega,
        fun e he => hnt e (rail2_new T s hk e he)⟩) (hc p q hp hq)
  intro p q hp hq
  refine conn_of_attach (m := T.n) (n := T.n + 2 * k) (fun p q hp hq _ _ => hold p q hp hq)
    (fun v hv _ => ?_) p q hp hq (by omega) (by omega)
  by_cases hvo : v < T.n
  · exact ⟨v, hvo, by omega, Relation.EqvGen.refl _⟩
  · exact ⟨s.1.1, hs.1, by have := hs.1; omega, attach_u T s hk _ _
      (fun x hx => by have := usOf_ge hx; omega)
      (fun e he => hnt e (rail1_new T s hk e he))
      (fun i hi => hnt _ (Or.inl (by omega))) _ (Or.inl rfl) (by have := hs.1; omega) v (by
        rcases new_cases (by omega) (by omega : v < T.n + 2 * k) with h | h
        · exact Or.inl h
        · exact Or.inr ⟨h, by omega⟩)⟩

theorem connDel_insert_u (T : VineTemplate) (s : (ℕ × ℕ) × (ℕ × ℕ)) {k : ℕ} (hk : k ≠ 0)
    (hs : SlotOK T s) {w : ℕ} (hw : w ∈ usOf T k) (hc : ConnAvoid T s.1) :
    ConnDel (insertRungs T s k) w := by
  have hn : (insertRungs T s k).n = T.n + 2 * k := insertRungs_atoms T s k
  have hw' := usOf_ge hw
  rw [ConnDel, hn]
  have hold : ∀ p q, p < T.n → q < T.n →
      Relation.EqvGen (FAdj (· ≠ w) (fun _ => true) (insertRungs T s k).bonds) p q := by
    intro p q hp hq
    exact lift_path T s hk (· < T.n) (· ≠ w) (fun x h => by omega) (fun x => decide (x ≠ s.1))
      (fun _ => true) (fun _ _ => rfl) (fun h => by simp at h)
      (fun _ => ⟨fun x hx => by have := vsOf_ge hx; omega, fun _ _ => rfl⟩) (hc p q hp hq)
  have hatt : ∀ v, v < T.n + 2 * k → v ≠ w →
      ∃ o, o < T.n ∧ o ≠ w ∧
        Relation.EqvGen (FAdj (· ≠ w) (fun _ => true) (insertRungs T s k).bonds) v o := by
    intro v hv hvw
    by_cases hvo : v < T.n
    · exact ⟨v, hvo, by omega, Relation.EqvGen.refl _⟩
    · exact ⟨s.2.1, hs.2.2.1, by have := hs.2.2.1; omega, attach_v T s hk _ _
        (fun x hx => by have := vsOf_ge hx; omega) (fun _ _ => rfl) (fun _ _ => rfl) _
        (Or.inl rfl) (by have := hs.2.2.1; omega) v (by
          rcases new_cases (by omega) hv with h | h
          · exact Or.inr ⟨h, hvw⟩
          · exact Or.inl h)⟩
  intro p q hp hq hpw hqw
  exact conn_of_attach (m := T.n) (n := T.n + 2 * k) (fun p q hp hq a b => hold p q hp hq)
    (fun v hv hP => hatt v hv hP) p q hp hq hpw hqw

theorem connDel_insert_v (T : VineTemplate) (s : (ℕ × ℕ) × (ℕ × ℕ)) {k : ℕ} (hk : k ≠ 0)
    (hs : SlotOK T s) {w : ℕ} (hw : w ∈ vsOf T k) (hc : ConnAvoid T s.2) :
    ConnDel (insertRungs T s k) w := by
  have hn : (insertRungs T s k).n = T.n + 2 * k := insertRungs_atoms T s k
  have hw' := vsOf_ge hw
  rw [ConnDel, hn]
  have hold : ∀ p q, p < T.n → q < T.n →
      Relation.EqvGen (FAdj (· ≠ w) (fun _ => true) (insertRungs T s k).bonds) p q := by
    intro p q hp hq
    exact lift_path T s hk (· < T.n) (· ≠ w) (fun x h => by omega) (fun x => decide (x ≠ s.2))
      (fun _ => true) (fun _ _ => rfl)
      (fun _ => ⟨fun x hx => by have := usOf_ge hx; omega, fun _ _ => rfl⟩)
      (fun h => by simp at h) (hc p q hp hq)
  have hatt : ∀ v, v < T.n + 2 * k → v ≠ w →
      ∃ o, o < T.n ∧ o ≠ w ∧
        Relation.EqvGen (FAdj (· ≠ w) (fun _ => true) (insertRungs T s k).bonds) v o := by
    intro v hv hvw
    by_cases hvo : v < T.n
    · exact ⟨v, hvo, by omega, Relation.EqvGen.refl _⟩
    · exact ⟨s.1.1, hs.1, by have := hs.1; omega, attach_u T s hk _ _
        (fun x hx => by have := usOf_ge hx; omega) (fun _ _ => rfl) (fun _ _ => rfl) _
        (Or.inl rfl) (by have := hs.1; omega) v (by
          rcases new_cases (by omega) hv with h | h
          · exact Or.inl h
          · exact Or.inr ⟨h, hvw⟩)⟩
  intro p q hp hq hpw hqw
  exact conn_of_attach (m := T.n) (n := T.n + 2 * k) (fun p q hp hq a b => hold p q hp hq)
    (fun v hv hP => hatt v hv hP) p q hp hq hpw hqw

end WaveTurbulence.LGSpine
