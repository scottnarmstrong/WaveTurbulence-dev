/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.TVine.Struct.Drawn.Cert

/-!
# Ladders inserted at template slots, as bond multisets (packet L3D)

The expanded template `T_X(k⃗)` (B2 `VineType.expand`) replaces, at each slot `((x, y), (x', y'))`, the two slot bonds by
the rails `x – u₁ – ⋯ – u_k – y`, `x' – v₁ – ⋯ – v_k – y'` and the rungs `u_i = v_i` (`insertRungs`). Here:

* `ladderO s us vs` (ordered pairs) and `ladderMS s us vs` (undirected): the bonds of one such ladder;
* `uN b K k`, `vN b K k`: the rail names at stage `k ≤ K` of a slot whose `K` final rungs are named from `b`
  (`b + K - k, …, b + K - 1` and `b + 2K - k, …, b + 2K - 1`); at `k = K` these are `insertRungs`'s names;
* `ladderMS_split`, `ladderMS_cons_split`: one more rung at the `x`-end is a single rung insertion (`insertRung`);
* crossing counts of ladders (`countP_ladderMS_zero`, `countP_ladderMS_two`).
-/

@[expose] public section
set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace WaveTurbulence.TVine.Struct.Drawn

open TVine WaveTurbulence.TVine.Core

/-- A slot: the two parallel template bonds `x – y`, `x' – y'`. -/
abbrev Slot := (ℕ × ℕ) × (ℕ × ℕ)

/-- An ordered pair as an undirected bond. -/
def mk2 (p : ℕ × ℕ) : Sym2 ℕ := s(p.1, p.2)

/-- The ladder at the slot `s` with rail names `us`, `vs` (ordered pairs, as in `insertRungs`). -/
def ladderO (s : Slot) (us vs : List ℕ) : Multiset (ℕ × ℕ) :=
  ↑(railBonds s.1.1 us s.1.2 ++ railBonds s.2.1 vs s.2.2 ++ (List.zip us vs).flatMap fun p => [p, p])

/-- The ladder at the slot `s` with rail names `us`, `vs`, undirected. -/
def ladderMS (s : Slot) (us vs : List ℕ) : Multiset (Sym2 ℕ) := (ladderO s us vs).map mk2

/-- The two slot bonds. -/
def slotMS (s : Slot) : Multiset (Sym2 ℕ) := {mk2 s.1, mk2 s.2}

/-- `u`-rail names at stage `k`: `b + K - k, …, b + K - 1`. -/
def uN (b K k : ℕ) : List ℕ := (List.range k).map fun j => b + K - k + j

/-- `v`-rail names at stage `k`: `b + 2K - k, …, b + 2K - 1`. -/
def vN (b K k : ℕ) : List ℕ := (List.range k).map fun j => b + 2 * K - k + j

/-! ## Rails -/

/-- The rails after their first bond. -/
def railTail : List ℕ → ℕ → List (ℕ × ℕ)
  | [], _ => []
  | w :: ws, y => railBonds w ws y

theorem railBonds_nil (x y : ℕ) : railBonds x [] y = [(x, y)] := rfl

theorem railBonds_cons (x u : ℕ) (ws : List ℕ) (y : ℕ) : railBonds x (u :: ws) y = (x, u) :: railBonds u ws y := rfl

theorem railBonds_head (x : ℕ) (ws : List ℕ) (y : ℕ) : railBonds x ws y = (x, ws.headD y) :: railTail ws y := by
  cases ws <;> rfl

theorem mem_railBonds {x y : ℕ} {ws : List ℕ} {p : ℕ × ℕ} (h : p ∈ railBonds x ws y) :
    (p.1 = x ∨ p.1 ∈ ws) ∧ (p.2 = y ∨ p.2 ∈ ws) := by
  obtain ⟨p1, p2⟩ := p
  unfold railBonds at h
  have h1 := List.of_mem_zip h
  simp only [List.mem_cons, List.mem_append, List.mem_singleton, List.not_mem_nil, or_false] at h1
  exact ⟨h1.1, h1.2.symm⟩

theorem mem_railTail {y : ℕ} {ws : List ℕ} {p : ℕ × ℕ} (h : p ∈ railTail ws y) :
    p.1 ∈ ws ∧ (p.2 = y ∨ p.2 ∈ ws) := by
  cases ws with
  | nil => simp [railTail] at h
  | cons w ws =>
    have := mem_railBonds h
    refine ⟨?_, ?_⟩
    · rcases this.1 with h1 | h1
      · rw [h1]; exact List.mem_cons_self
      · exact List.mem_cons_of_mem _ h1
    · rcases this.2 with h1 | h1
      · exact Or.inl h1
      · exact Or.inr (List.mem_cons_of_mem _ h1)

theorem mem_flatMap_zip {us vs : List ℕ} {p : ℕ × ℕ} (h : p ∈ (List.zip us vs).flatMap fun p => [p, p]) :
    p.1 ∈ us ∧ p.2 ∈ vs := by
  obtain ⟨⟨q1, q2⟩, hq, hp⟩ := List.mem_flatMap.mp h
  simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false, or_self] at hp
  subst hp
  exact List.of_mem_zip hq

/-- The atoms of a ladder's bonds. -/
theorem mem_ladderO {s : Slot} {us vs : List ℕ} {p : ℕ × ℕ} (h : p ∈ ladderO s us vs) :
    ∀ a, (a = p.1 ∨ a = p.2) → a = s.1.1 ∨ a = s.1.2 ∨ a = s.2.1 ∨ a = s.2.2 ∨ a ∈ us ∨ a ∈ vs := by
  intro a ha
  unfold ladderO at h
  rw [Multiset.mem_coe, List.mem_append, List.mem_append] at h
  rcases h with (h | h) | h
  · have := mem_railBonds h
    rcases ha with rfl | rfl
    · rcases this.1 with h1 | h1
      · exact Or.inl h1
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h1))))
    · rcases this.2 with h1 | h1
      · exact Or.inr (Or.inl h1)
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h1))))
  · have := mem_railBonds h
    rcases ha with rfl | rfl
    · rcases this.1 with h1 | h1
      · exact Or.inr (Or.inr (Or.inl h1))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h1))))
    · rcases this.2 with h1 | h1
      · exact Or.inr (Or.inr (Or.inr (Or.inl h1)))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h1))))
  · have := mem_flatMap_zip h
    rcases ha with rfl | rfl
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl this.1))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr this.2))))

theorem mem_ladderMS {s : Slot} {us vs : List ℕ} {e : Sym2 ℕ} (h : e ∈ ladderMS s us vs) :
    ∀ a ∈ e, a = s.1.1 ∨ a = s.1.2 ∨ a = s.2.1 ∨ a = s.2.2 ∨ a ∈ us ∨ a ∈ vs := by
  obtain ⟨p, hp, rfl⟩ := Multiset.mem_map.mp h
  intro a ha
  exact mem_ladderO hp a (Sym2.mem_iff.mp ha)

/-! ## The ladder with no rung, and one more rung -/

/-- The remainder of a ladder after the two bonds at `x`, `x'`. -/
def ladderRest (s : Slot) (us vs : List ℕ) : Multiset (Sym2 ℕ) :=
  (↑(railTail us s.1.2 ++ railTail vs s.2.2 ++ (List.zip us vs).flatMap fun p => [p, p]) : Multiset (ℕ × ℕ)).map mk2

theorem coe_cons' {α : Type*} (a : α) (l : List α) : (↑(a :: l) : Multiset α) = {a} + ↑l := by
  rw [Multiset.singleton_add, Multiset.cons_coe]

theorem ladderMS_split (s : Slot) (us vs : List ℕ) :
    ladderMS s us vs = {s(s.1.1, us.headD s.1.2), s(s.2.1, vs.headD s.2.2)} + ladderRest s us vs := by
  unfold ladderMS ladderO ladderRest
  rw [railBonds_head s.1.1 us, railBonds_head s.2.1 vs]
  simp only [← Multiset.coe_add, coe_cons', Multiset.map_add, Multiset.map_singleton, mk2, Multiset.insert_eq_cons,
    ← Multiset.singleton_add]
  abel

theorem ladderMS_cons_split (s : Slot) (u v : ℕ) (us vs : List ℕ) :
    ladderMS s (u :: us) (v :: vs) =
      {s(s.1.1, u), s(u, us.headD s.1.2), s(s.2.1, v), s(v, vs.headD s.2.2), s(u, v), s(u, v)} +
        ladderRest s us vs := by
  unfold ladderMS ladderO ladderRest
  rw [railBonds_cons s.1.1 u us, railBonds_cons s.2.1 v vs, railBonds_head u us, railBonds_head v vs,
    List.zip_cons_cons, List.flatMap_cons]
  simp only [← Multiset.coe_add, coe_cons', Multiset.map_add, Multiset.map_singleton, mk2, Multiset.insert_eq_cons,
    ← Multiset.singleton_add, List.cons_append, List.nil_append]
  abel

theorem ladderMS_nil (s : Slot) : ladderMS s [] [] = slotMS s := by
  rw [ladderMS_split]
  simp [ladderRest, railTail, slotMS, mk2]

/-! ## Names -/

theorem mem_uN {b K k a : ℕ} (hk : k ≤ K) : a ∈ uN b K k ↔ b + K - k ≤ a ∧ a < b + K := by
  unfold uN
  simp only [List.mem_map, List.mem_range]
  constructor
  · rintro ⟨j, hj, rfl⟩; omega
  · intro h; exact ⟨a - (b + K - k), by omega, by omega⟩

theorem mem_vN {b K k a : ℕ} (hk : k ≤ K) : a ∈ vN b K k ↔ b + 2 * K - k ≤ a ∧ a < b + 2 * K := by
  unfold vN
  simp only [List.mem_map, List.mem_range]
  constructor
  · rintro ⟨j, hj, rfl⟩; omega
  · intro h; exact ⟨a - (b + 2 * K - k), by omega, by omega⟩

theorem uN_zero (b K : ℕ) : uN b K 0 = [] := rfl

theorem vN_zero (b K : ℕ) : vN b K 0 = [] := rfl

theorem uN_succ {b K k : ℕ} (hk : k < K) : uN b K (k + 1) = (b + K - (k + 1)) :: uN b K k := by
  unfold uN
  rw [List.range_succ_eq_map, List.map_cons, List.map_map]
  refine List.cons_eq_cons.mpr ⟨by omega, ?_⟩
  apply List.map_congr_left
  intro j _
  simp only [Function.comp_apply]
  omega

theorem vN_succ {b K k : ℕ} (hk : k < K) : vN b K (k + 1) = (b + 2 * K - (k + 1)) :: vN b K k := by
  unfold vN
  rw [List.range_succ_eq_map, List.map_cons, List.map_map]
  refine List.cons_eq_cons.mpr ⟨by omega, ?_⟩
  apply List.map_congr_left
  intro j _
  simp only [Function.comp_apply]
  omega

theorem uN_headD {b K k : ℕ} (hk : k ≤ K) (y : ℕ) : (uN b K k).headD y = if k = 0 then y else b + K - k := by
  cases k with
  | zero => rfl
  | succ k => rw [uN_succ (by omega)]; simp

theorem vN_headD {b K k : ℕ} (hk : k ≤ K) (y : ℕ) :
    (vN b K k).headD y = if k = 0 then y else b + 2 * K - k := by
  cases k with
  | zero => rfl
  | succ k => rw [vN_succ (by omega)]; simp

/-! ## Crossing counts -/

theorem countP_map_mk2_zero {X : Finset ℕ} {L : List (ℕ × ℕ)} (h : ∀ p ∈ L, (p.1 ∈ X ↔ p.2 ∈ X)) :
    ((↑L : Multiset (ℕ × ℕ)).map mk2).countP (fun e => crossB X e = true) = 0 := by
  rw [Multiset.countP_eq_zero]
  intro e he
  obtain ⟨p, hp, rfl⟩ := Multiset.mem_map.mp he
  have := h p (Multiset.mem_coe.mp hp)
  simp only [mk2, crossB_mk, bne_iff_ne, ne_eq, decide_eq_decide, not_not]
  exact this

theorem countP_ladderMS_zero (X : Finset ℕ) (s : Slot) (us vs : List ℕ) (P : Prop)
    (h : ∀ a, (a = s.1.1 ∨ a = s.1.2 ∨ a = s.2.1 ∨ a = s.2.2 ∨ a ∈ us ∨ a ∈ vs) → (a ∈ X ↔ P)) :
    (ladderMS s us vs).countP (fun e => crossB X e = true) = 0 := by
  rw [Multiset.countP_eq_zero]
  intro e he
  obtain ⟨p, hp, rfl⟩ := Multiset.mem_map.mp he
  have h1 := h p.1 (mem_ladderO hp p.1 (Or.inl rfl))
  have h2 := h p.2 (mem_ladderO hp p.2 (Or.inr rfl))
  simp only [mk2, crossB_mk, bne_iff_ne, ne_eq, decide_eq_decide, not_not]
  exact h1.trans h2.symm

theorem countP_ladderMS_two (X : Finset ℕ) (s : Slot) (us vs : List ℕ) (hx : s.1.1 ∈ X) (hx' : s.2.1 ∈ X)
    (hy : s.1.2 ∉ X) (hy' : s.2.2 ∉ X) (hus : ∀ a ∈ us, a ∉ X) (hvs : ∀ a ∈ vs, a ∉ X) :
    (ladderMS s us vs).countP (fun e => crossB X e = true) = 2 := by
  rw [ladderMS_split, Multiset.countP_add]
  have hr : (ladderRest s us vs).countP (fun e => crossB X e = true) = 0 := by
    apply countP_map_mk2_zero
    intro p hp
    simp only [List.mem_append] at hp
    rcases hp with (hp | hp) | hp
    · have := mem_railTail hp
      have h1 := hus _ this.1
      have h2 : p.2 ∉ X := by
        rcases this.2 with h | h
        · rw [h]; exact hy
        · exact hus _ h
      simp [h1, h2]
    · have := mem_railTail hp
      have h1 := hvs _ this.1
      have h2 : p.2 ∉ X := by
        rcases this.2 with h | h
        · rw [h]; exact hy'
        · exact hvs _ h
      simp [h1, h2]
    · have := mem_flatMap_zip hp
      simp [hus _ this.1, hvs _ this.2]
  rw [hr]
  have hc : us.headD s.1.2 ∉ X := by
    cases us with
    | nil => exact hy
    | cons a _ => exact hus a List.mem_cons_self
  have hc' : vs.headD s.2.2 ∉ X := by
    cases vs with
    | nil => exact hy'
    | cons a _ => exact hvs a List.mem_cons_self
  have e1 : crossB X s(s.1.1, us.headD s.1.2) = true := by
    rw [crossB_mk, decide_eq_true hx, decide_eq_false hc]; rfl
  have e2 : crossB X s(s.2.1, vs.headD s.2.2) = true := by
    rw [crossB_mk, decide_eq_true hx', decide_eq_false hc']; rfl
  simp only [Multiset.insert_eq_cons, ← Multiset.cons_zero, Multiset.countP_cons, Multiset.countP_zero, e1, e2,
    ite_true]

end WaveTurbulence.TVine.Struct.Drawn
