/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.TVine.Checker.Gen

/-!
# The algebra of (Z1) moves and ladders

* `SameMult`: equality of all multiplicities; it is preserved by `z1` and `ladder` (`z1_congr`,
  `ladder_congr`), and two (Z1) moves on different bonds commute (`z1_comm`, `ladder_z1_comm`).
* The ladder invariants (`ladder_ends`, `ladder_old`, `ladder_newest`, `ladder_le_two`): the ends of a ladder,
  the multiplicities of the old pairs, the newest triple bond, and every other pair at a new atom has
  multiplicity at most 2.
-/

@[expose] public section

namespace WaveTurbulence.TVine.Checker

open TVine

/-- Equality of all multiplicities. -/
def SameMult (es es' : Edges) : Prop := ∀ u v, mult es u v = mult es' u v

theorem SameMult.trans {es es' es'' : Edges} (h : SameMult es es') (h' : SameMult es' es'') :
    SameMult es es'' := fun u v => (h u v).trans (h' u v)

theorem SameMult.symm {es es' : Edges} (h : SameMult es es') : SameMult es' es := fun u v => (h u v).symm

theorem SameMult.refl (es : Edges) : SameMult es es := fun _ _ => rfl

theorem SameMult.inEnds {es es' : Edges} (h : SameMult es es') {x : ℕ} (hx : InEnds es x) : InEnds es' x := by
  obtain ⟨y, hy⟩ := inEnds_iff.mp hx
  exact inEnds_iff.mpr ⟨y, by rw [← h]; exact hy⟩

/-- An isomorphism transported along `SameMult`. -/
def Iso.ofSame {V : Type*} {G : UMultigraph V} {es es' : Edges} (φ : Iso G es) (h : SameMult es es') :
    Iso G es' := φ.trans (Iso.ofSameMult h)

/-! ## Indicator algebra -/

/-- The new multiplicities created by `z1 · x y a b`. -/
def z1New (x y a b u v : ℕ) : ℕ :=
  (if s(u, v) = s(x, a) then 1 else 0) + 3 * (if s(u, v) = s(a, b) then 1 else 0) +
    (if s(u, v) = s(b, y) then 1 else 0)

theorem mult_z1' (es : Edges) (x y a b u v : ℕ) (h : mult es x y ≠ 0) :
    mult (z1 es x y a b) u v + (if s(u, v) = s(x, y) then 1 else 0) = mult es u v + z1New x y a b u v :=
  mult_z1 es x y a b u v h

theorem z1_ne_zero_new (es : Edges) (x y a b : ℕ) (h : mult es x y ≠ 0) : mult (z1 es x y a b) a b ≠ 0 := by
  have := mult_z1' es x y a b a b h
  simp only [z1New, if_true] at this
  split_ifs at this <;> omega

theorem z1_congr {es es' : Edges} (h : SameMult es es') {x y a b : ℕ} (hxy : mult es x y ≠ 0) :
    SameMult (z1 es x y a b) (z1 es' x y a b) := by
  intro u v
  have h1 := mult_z1' es x y a b u v hxy
  have h2 := mult_z1' es' x y a b u v (by rw [← h]; exact hxy)
  rw [h u v] at h1; omega

theorem ladder_congr : ∀ (k : ℕ) {es es' : Edges} (_h : SameMult es es') {x y N : ℕ} (_hxy : mult es x y ≠ 0),
    SameMult (ladder k es x y N) (ladder k es' x y N)
  | 0, _, _, h, _, _, _, _ => h
  | k + 1, es, _, h, x, y, N, hxy => by
    simp only [ladder]
    exact ladder_congr k (z1_congr h hxy) (z1_ne_zero_new es x y N (N + 1) hxy)

/-- Two (Z1) moves on different bonds (or on one bond of multiplicity at least 2) with fresh names commute. -/
theorem z1_comm (E : Edges) (p₁ p₂ q₁ q₂ a b a' b' : ℕ) (hp : mult E p₁ p₂ ≠ 0) (hq : mult E q₁ q₂ ≠ 0)
    (hpq : s(p₁, p₂) = s(q₁, q₂) → 2 ≤ mult E p₁ p₂) (hq' : z1New p₁ p₂ a b q₁ q₂ = 0)
    (hp' : z1New q₁ q₂ a' b' p₁ p₂ = 0) :
    SameMult (z1 (z1 E p₁ p₂ a b) q₁ q₂ a' b') (z1 (z1 E q₁ q₂ a' b') p₁ p₂ a b) := by
  have hq1 : mult (z1 E p₁ p₂ a b) q₁ q₂ ≠ 0 := by
    have hz := mult_z1' E p₁ p₂ a b q₁ q₂ hp
    rw [hq'] at hz
    by_cases he : s(q₁, q₂) = s(p₁, p₂)
    · have h2 := hpq he.symm
      have hqp : mult E q₁ q₂ = mult E p₁ p₂ := by rw [mult_eq_count, he, ← mult_eq_count]
      rw [if_pos he] at hz
      omega
    · rw [if_neg he] at hz; omega
  have hp1 : mult (z1 E q₁ q₂ a' b') p₁ p₂ ≠ 0 := by
    have hz := mult_z1' E q₁ q₂ a' b' p₁ p₂ hq
    rw [hp'] at hz
    by_cases he : s(p₁, p₂) = s(q₁, q₂)
    · have h2 := hpq he
      rw [if_pos he] at hz
      omega
    · rw [if_neg he] at hz; omega
  intro u v
  have l1 := mult_z1' (z1 E p₁ p₂ a b) q₁ q₂ a' b' u v hq1
  have l2 := mult_z1' E p₁ p₂ a b u v hp
  have r1 := mult_z1' (z1 E q₁ q₂ a' b') p₁ p₂ a b u v hp1
  have r2 := mult_z1' E q₁ q₂ a' b' u v hq
  omega

/-! ## Ends -/

theorem inEnds_eraseOne {es : Edges} {x y z : ℕ} (h : InEnds (eraseOne es x y) z) : InEnds es z := by
  induction es with
  | nil => exact h
  | cons e es ih =>
    simp only [eraseOne] at h
    split at h
    · obtain ⟨e', he', hz⟩ := h; exact ⟨e', List.mem_cons_of_mem _ he', hz⟩
    · obtain ⟨e', he', hz⟩ := h
      rcases List.mem_cons.mp he' with rfl | he'
      · exact ⟨e', List.mem_cons_self, hz⟩
      · obtain ⟨e'', he'', hz'⟩ := ih ⟨e', he', hz⟩; exact ⟨e'', List.mem_cons_of_mem _ he'', hz'⟩

theorem inEnds_append {es es' : Edges} {z : ℕ} : InEnds (es ++ es') z ↔ InEnds es z ∨ InEnds es' z := by
  simp only [InEnds, List.mem_append]
  constructor
  · rintro ⟨e, he | he, hz⟩
    · exact Or.inl ⟨e, he, hz⟩
    · exact Or.inr ⟨e, he, hz⟩
  · rintro (⟨e, he, hz⟩ | ⟨e, he, hz⟩)
    · exact ⟨e, Or.inl he, hz⟩
    · exact ⟨e, Or.inr he, hz⟩

theorem inEnds_z1 {es : Edges} {x y a b z : ℕ} (hxy : mult es x y ≠ 0) (h : InEnds (z1 es x y a b) z) :
    InEnds es z ∨ z = a ∨ z = b := by
  rcases inEnds_append.mp h with h | ⟨e, he, hz⟩
  · exact Or.inl (inEnds_eraseOne h)
  · have ⟨hx, hy⟩ := inEnds_of_mult_ne_zero hxy
    simp only [List.mem_cons, List.not_mem_nil, or_false] at he
    rcases he with rfl | rfl | rfl | rfl | rfl <;> rcases hz with rfl | rfl <;> simp_all

theorem inEnds_z1_of {es : Edges} {x y a b z : ℕ} (hxy : mult es x y ≠ 0) (h : InEnds es z ∨ z = a ∨ z = b) :
    InEnds (z1 es x y a b) z := by
  rcases h with h | h | h
  · obtain ⟨w, hw⟩ := inEnds_iff.mp h
    by_cases hzw : s(z, w) = s(x, y)
    · rw [Sym2.eq_iff] at hzw
      rcases hzw with ⟨rfl, _⟩ | ⟨rfl, _⟩
      · exact inEnds_append.mpr (Or.inr ⟨(z, a), by simp, Or.inl rfl⟩)
      · exact inEnds_append.mpr (Or.inr ⟨(b, z), by simp, Or.inr rfl⟩)
    · refine inEnds_iff.mpr ⟨w, ?_⟩
      have := mult_z1' es x y a b z w hxy
      rw [if_neg hzw] at this; omega
  · exact inEnds_append.mpr (Or.inr ⟨(x, a), by simp, Or.inr h.symm⟩)
  · exact inEnds_append.mpr (Or.inr ⟨(b, y), by simp, Or.inl h.symm⟩)

/-! ## Ladders -/

/-- `z` is one of the atoms `N + 4i, N + 4i + 1` (`i < k`) created by a ladder. -/
def IsNew (k N z : ℕ) : Prop := ∃ i < k, z = N + 4 * i ∨ z = N + 4 * i + 1

theorem isNew_succ {k N z : ℕ} : IsNew (k + 1) N z ↔ z = N ∨ z = N + 1 ∨ IsNew k (N + 4) z := by
  constructor
  · rintro ⟨i, hi, h⟩
    cases i with
    | zero => rcases h with h | h <;> simp_all
    | succ i => exact Or.inr (Or.inr ⟨i, by omega, by rcases h with h | h <;> [left; right] <;> omega⟩)
  · rintro (h | h | ⟨i, hi, h⟩)
    · exact ⟨0, by omega, Or.inl (by omega)⟩
    · exact ⟨0, by omega, Or.inr (by omega)⟩
    · exact ⟨i + 1, by omega, by rcases h with h | h <;> [left; right] <;> omega⟩

/-- The names of a ladder are fresh for `es`. -/
def Fresh (k : ℕ) (es : Edges) (N : ℕ) : Prop := ∀ z, IsNew k N z → ¬ InEnds es z

/-- The last move of a ladder of length `k + 1` acts on this pair. -/
def lastPair (k x y N : ℕ) : ℕ × ℕ := if k = 0 then (x, y) else (N + 4 * (k - 1), N + 4 * (k - 1) + 1)

theorem lastPair_succ (k x y N : ℕ) : lastPair k N (N + 1) (N + 4) = lastPair (k + 1) x y N := by
  rcases k with _ | k
  · simp [lastPair]
  · simp only [lastPair, Nat.add_one_ne_zero, if_false, Nat.add_sub_cancel, Prod.mk.injEq]
    omega

theorem ladder_succ : ∀ (k : ℕ) (es : Edges) (x y N : ℕ),
    ladder (k + 1) es x y N = z1 (ladder k es x y N) (lastPair k x y N).1 (lastPair k x y N).2
      (N + 4 * k) (N + 4 * k + 1)
  | 0, es, x, y, N => by simp [ladder, lastPair]
  | k + 1, es, x, y, N => by
    rw [ladder, ladder_succ k (z1 es x y N (N + 1)) N (N + 1) (N + 4), lastPair_succ k x y N,
      show N + 4 + 4 * k = N + 4 * (k + 1) by omega]
    rfl

theorem ladder_ends : ∀ (k : ℕ) {es : Edges} {x y N z : ℕ} (_hxy : mult es x y ≠ 0)
    (_h : InEnds (ladder k es x y N) z), InEnds es z ∨ IsNew k N z
  | 0, _, _, _, _, _, _, h => Or.inl h
  | k + 1, es, x, y, N, z, hxy, h => by
    simp only [ladder] at h
    rcases ladder_ends k (z1_ne_zero_new es x y N (N + 1) hxy) h with h | h
    · rcases inEnds_z1 hxy h with h | rfl | rfl
      · exact Or.inl h
      · exact Or.inr (isNew_succ.mpr (Or.inl rfl))
      · exact Or.inr (isNew_succ.mpr (Or.inr (Or.inl rfl)))
    · exact Or.inr (isNew_succ.mpr (Or.inr (Or.inr h)))

theorem ladder_ends_of : ∀ (k : ℕ) {es : Edges} {x y N z : ℕ} (_hxy : mult es x y ≠ 0)
    (_h : InEnds es z ∨ IsNew k N z), InEnds (ladder k es x y N) z
  | 0, _, _, _, _, _, _, h => h.resolve_right (fun ⟨_, hi, _⟩ => absurd hi (Nat.not_lt_zero _))
  | k + 1, es, x, y, N, z, hxy, h => by
    simp only [ladder]
    apply ladder_ends_of k (z1_ne_zero_new es x y N (N + 1) hxy)
    rcases h with h | h
    · exact Or.inl (inEnds_z1_of hxy (Or.inl h))
    · rcases isNew_succ.mp h with rfl | rfl | h
      · exact Or.inl (inEnds_z1_of hxy (Or.inr (Or.inl rfl)))
      · exact Or.inl (inEnds_z1_of hxy (Or.inr (Or.inr rfl)))
      · exact Or.inr h

theorem mult_eq_zero_of_not_inEnds {es : Edges} {u v : ℕ} (h : ¬ InEnds es u) : mult es u v = 0 := by
  by_contra hh; exact h (inEnds_of_mult_ne_zero hh).1

theorem mult_eq_zero_of_not_inEnds' {es : Edges} {u v : ℕ} (h : ¬ InEnds es v) : mult es u v = 0 := by
  rw [mult_comm]; exact mult_eq_zero_of_not_inEnds h

/-- Multiplicities of old pairs. -/
theorem ladder_old : ∀ (k : ℕ) {es : Edges} {x y N u v : ℕ} (_hxy : mult es x y ≠ 0)
    (_hu : ¬ IsNew k N u) (_hv : ¬ IsNew k N v),
    mult (ladder k es x y N) u v + (if 0 < k ∧ s(u, v) = s(x, y) then 1 else 0) = mult es u v
  | 0, _, _, _, _, _, _, _, _, _ => by simp [ladder]
  | k + 1, es, x, y, N, u, v, hxy, hu, hv => by
    simp only [ladder]
    have hu' : u ≠ N ∧ u ≠ N + 1 ∧ ¬ IsNew k (N + 4) u := by
      refine ⟨fun h => hu (isNew_succ.mpr (Or.inl h)), fun h => hu (isNew_succ.mpr (Or.inr (Or.inl h))),
        fun h => hu (isNew_succ.mpr (Or.inr (Or.inr h)))⟩
    have hv' : v ≠ N ∧ v ≠ N + 1 ∧ ¬ IsNew k (N + 4) v := by
      refine ⟨fun h => hv (isNew_succ.mpr (Or.inl h)), fun h => hv (isNew_succ.mpr (Or.inr (Or.inl h))),
        fun h => hv (isNew_succ.mpr (Or.inr (Or.inr h)))⟩
    have h1 := ladder_old k (x := N) (y := N + 1) (N := N + 4) (z1_ne_zero_new es x y N (N + 1) hxy) hu'.2.2 hv'.2.2
    have hne : ¬ s(u, v) = s(N, N + 1) := by rw [Sym2.eq_iff]; omega
    rw [if_neg (fun h => hne h.2)] at h1
    have h2 := mult_z1' es x y N (N + 1) u v hxy
    have h3 : z1New x y N (N + 1) u v = 0 := by
      simp only [z1New, Sym2.eq_iff]; split_ifs <;> omega
    rw [h3] at h2
    have : (0 < k + 1 ∧ s(u, v) = s(x, y)) ↔ s(u, v) = s(x, y) := by simp
    simp only [this]
    omega

/-- The newest pair of a ladder is a triple bond. -/
theorem ladder_newest : ∀ (k : ℕ) {es : Edges} {x y N : ℕ} (_hxy : mult es x y ≠ 0) (_hf : Fresh (k + 1) es N),
    mult (ladder (k + 1) es x y N) (N + 4 * k) (N + 4 * k + 1) = 3
  | 0, es, x, y, N, hxy, hf => by
    simp only [ladder, Nat.mul_zero, Nat.add_zero]
    have := mult_z1' es x y N (N + 1) N (N + 1) hxy
    have hN : ¬ InEnds es N := hf N ⟨0, by omega, Or.inl (by omega)⟩
    have hN1 : ¬ InEnds es (N + 1) := hf (N + 1) ⟨0, by omega, Or.inr (by omega)⟩
    have hx := (inEnds_of_mult_ne_zero hxy).1
    have hy := (inEnds_of_mult_ne_zero hxy).2
    rw [mult_eq_zero_of_not_inEnds hN] at this
    simp only [z1New, Sym2.eq_iff] at this
    have hxN : x ≠ N := fun h => hN (h ▸ hx)
    have hxN1 : x ≠ N + 1 := fun h => hN1 (h ▸ hx)
    have hyN : y ≠ N := fun h => hN (h ▸ hy)
    have hyN1 : y ≠ N + 1 := fun h => hN1 (h ▸ hy)
    split_ifs at this <;> omega
  | k + 1, es, x, y, N, hxy, hf => by
    rw [ladder]
    have := ladder_newest k (es := z1 es x y N (N + 1)) (x := N) (y := N + 1) (N := N + 4)
      (z1_ne_zero_new es x y N (N + 1) hxy) ?_
    · rw [show N + 4 * (k + 1) = N + 4 + 4 * k by ring]; exact this
    · intro z hz hz'
      rcases inEnds_z1 hxy hz' with h | rfl | rfl
      · exact hf z (isNew_succ.mpr (Or.inr (Or.inr hz))) h
      · obtain ⟨i, _, h⟩ := hz; omega
      · obtain ⟨i, _, h⟩ := hz; omega

end WaveTurbulence.TVine.Checker
