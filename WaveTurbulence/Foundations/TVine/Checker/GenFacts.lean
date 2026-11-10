/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.TVine.Checker.GenAlgebra

/-!
# Structure of the generated closures

* `ladder_le_two`: in a ladder, every pair at a new atom other than the newest pair has multiplicity ≤ 2;
* the ends and the triple bonds of `gen1 k = Z_k(T, ℓ)` and of `genC p`;
* `CParam.Valid`: the parameter conditions of N2 Lemma 1.7 (`ℓ'` a non-triple bond of `Z_k(T, ℓ)`).
-/

@[expose] public section

namespace WaveTurbulence.TVine.Checker

open TVine

/-- The new multiplicities of a (Z1) move at fresh atoms `a ≠ b`: `3` on `a–b`, at most `1` elsewhere. -/
theorem z1New_ab (x y a b u v : ℕ) (hxb : x ≠ b) (hya : y ≠ a) (h : s(u, v) = s(a, b)) :
    z1New x y a b u v = 3 := by
  rw [Sym2.eq_iff] at h
  simp only [z1New, Sym2.eq_iff]
  split_ifs <;> omega

theorem z1New_le (x y a b u v : ℕ) (hxa : x ≠ a) (hxb : x ≠ b) (hya : y ≠ a) (hyb : y ≠ b) (hab : a ≠ b)
    (h : ¬ s(u, v) = s(a, b)) : z1New x y a b u v ≤ 1 := by
  rw [Sym2.eq_iff] at h
  simp only [z1New, Sym2.eq_iff]
  split_ifs <;> omega

theorem ladder_le_two : ∀ (k : ℕ) {es : Edges} {x y N u v : ℕ} (_hxy : mult es x y ≠ 0) (_hf : Fresh k es N)
    (_huv : IsNew k N u ∨ IsNew k N v) (_hne : ∀ j, k = j + 1 → s(u, v) ≠ s(N + 4 * j, N + 4 * j + 1)),
    mult (ladder k es x y N) u v ≤ 2
  | 0, _, _, _, _, _, _, _, _, huv, _ => by
    exfalso; rcases huv with ⟨i, hi, _⟩ | ⟨i, hi, _⟩ <;> omega
  | k + 1, es, x, y, N, u, v, hxy, hf, huv, hne => by
    rw [ladder]
    have hz := z1_ne_zero_new es x y N (N + 1) hxy
    have hf' : Fresh k (z1 es x y N (N + 1)) (N + 4) := by
      intro z hz' hz''
      rcases inEnds_z1 hxy hz'' with h | h | h
      · exact hf z (isNew_succ.mpr (Or.inr (Or.inr hz'))) h
      · obtain ⟨i, _, h'⟩ := hz'; omega
      · obtain ⟨i, _, h'⟩ := hz'; omega
    by_cases hin : IsNew k (N + 4) u ∨ IsNew k (N + 4) v
    · apply ladder_le_two k hz hf' hin
      intro j hj
      have := hne (j + 1) (by omega)
      rwa [show N + 4 * (j + 1) = N + 4 + 4 * j by ring] at this
    · rw [not_or] at hin
      have hold := ladder_old k (x := N) (y := N + 1) (N := N + 4) hz hin.1 hin.2
      have h2 := mult_z1' es x y N (N + 1) u v hxy
      have hN : ¬ InEnds es N := hf N ⟨0, by omega, Or.inl (by omega)⟩
      have hN1 : ¬ InEnds es (N + 1) := hf (N + 1) ⟨0, by omega, Or.inr (by omega)⟩
      have hx := (inEnds_of_mult_ne_zero hxy).1
      have hy := (inEnds_of_mult_ne_zero hxy).2
      have hxN : x ≠ N := fun h => hN (h ▸ hx)
      have hxN1 : x ≠ N + 1 := fun h => hN1 (h ▸ hx)
      have hyN : y ≠ N := fun h => hN (h ▸ hy)
      have hyN1 : y ≠ N + 1 := fun h => hN1 (h ▸ hy)
      have huv' : u = N ∨ u = N + 1 ∨ v = N ∨ v = N + 1 := by
        rcases huv with h | h <;> rcases isNew_succ.mp h with h | h | h
        · exact Or.inl h
        · exact Or.inr (Or.inl h)
        · exact absurd h hin.1
        · exact Or.inr (Or.inr (Or.inl h))
        · exact Or.inr (Or.inr (Or.inr h))
        · exact absurd h hin.2
      have hes0 : mult es u v = 0 := by
        rcases huv' with rfl | rfl | rfl | rfl
        · exact mult_eq_zero_of_not_inEnds hN
        · exact mult_eq_zero_of_not_inEnds hN1
        · exact mult_eq_zero_of_not_inEnds' hN
        · exact mult_eq_zero_of_not_inEnds' hN1
      have hxy0 : ¬ s(u, v) = s(x, y) := by
        rw [Sym2.eq_iff]; rcases huv' with h | h | h | h <;> omega
      rw [if_neg hxy0, hes0] at h2
      by_cases hk : s(u, v) = s(N, N + 1)
      · have hnew := z1New_ab x y N (N + 1) u v hxN1 hyN hk
        rcases k with _ | k
        · exact absurd hk (hne 0 rfl)
        · rw [if_pos ⟨by omega, hk⟩] at hold
          omega
      · have hnew := z1New_le x y N (N + 1) u v hxN hxN1 hyN hyN1 (by omega) hk
        rw [if_neg (fun h => hk h.2)] at hold
        omega

/-! ## The doubled triangle -/

theorem mult_tri_le (u v : ℕ) : mult tri u v ≤ 2 := by
  rw [mult_eq_count]
  generalize s(u, v) = w
  by_cases e1 : w = s(0, 1)
  · subst e1; decide
  by_cases e2 : w = s(1, 2)
  · subst e2; decide
  by_cases e3 : w = s(0, 2)
  · subst e3; decide
  have : List.count w (tri.map fun e => s(e.1, e.2)) = 0 := by
    rw [List.count_eq_zero]
    simp only [tri, List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil, or_false]
    rintro (h | h | h | h | h | h)
    · exact e1 h
    · exact e1 h
    · exact e2 h
    · exact e2 h
    · exact e3 h
    · exact e3 h
  omega

theorem inEnds_tri {z : ℕ} : InEnds tri z ↔ z ≤ 2 := by
  constructor
  · rintro ⟨e, he, h⟩
    simp only [tri, List.mem_cons, List.not_mem_nil, or_false] at he
    rcases he with rfl | rfl | rfl | rfl | rfl | rfl <;> rcases h with rfl | rfl <;> simp
  · intro h
    interval_cases z
    · exact ⟨(0, 1), by simp [tri], Or.inl rfl⟩
    · exact ⟨(0, 1), by simp [tri], Or.inr rfl⟩
    · exact ⟨(1, 2), by simp [tri], Or.inr rfl⟩

theorem mult_tri_01 : mult tri 0 1 ≠ 0 := by decide

/-! ## The first ladder `gen1 k = Z_k(T, ℓ)` -/

theorem fresh_gen1 (k : ℕ) : Fresh k tri 3 := by
  rintro z ⟨i, _, h⟩ hz
  have := inEnds_tri.mp hz; omega

theorem gen1_ends {k z : ℕ} (h : InEnds (gen1 k) z) : z ≤ 2 ∨ IsNew k 3 z := by
  rcases ladder_ends k mult_tri_01 h with h | h
  · exact Or.inl (inEnds_tri.mp h)
  · exact Or.inr h

theorem gen1_ends_of {k z : ℕ} (h : z ≤ 2 ∨ IsNew k 3 z) : InEnds (gen1 k) z := by
  apply ladder_ends_of k mult_tri_01
  rcases h with h | h
  · exact Or.inl (inEnds_tri.mpr h)
  · exact Or.inr h

/-- The triple bond of `gen1 (k + 1)`. -/
theorem gen1_triple (k : ℕ) : mult (gen1 (k + 1)) (4 * k + 3) (4 * k + 4) = 3 := by
  have := ladder_newest k mult_tri_01 (fresh_gen1 (k + 1))
  rw [show 3 + 4 * k = 4 * k + 3 by ring, show 4 * k + 3 + 1 = 4 * k + 4 by ring] at this
  exact this

/-- Every other pair of `gen1 (k + 1)` has multiplicity at most 2. -/
theorem gen1_le_two (k : ℕ) {u v : ℕ} (h : s(u, v) ≠ s(4 * k + 3, 4 * k + 4)) : mult (gen1 (k + 1)) u v ≤ 2 := by
  by_cases hn : IsNew (k + 1) 3 u ∨ IsNew (k + 1) 3 v
  · apply ladder_le_two (k + 1) mult_tri_01 (fresh_gen1 (k + 1)) hn
    intro j hj
    rw [show j = k by omega, show 3 + 4 * k = 4 * k + 3 by ring, show 4 * k + 3 + 1 = 4 * k + 4 by ring]
    exact h
  · rw [not_or] at hn
    have := ladder_old (k + 1) (x := 0) (y := 1) (N := 3) mult_tri_01 hn.1 hn.2
    have := mult_tri_le u v
    unfold gen1; omega

/-! ## Validity and the closures `genC p` -/

/-- **The parameter conditions of N2 Lemma 1.7.** A second ladder starts on a bond `ℓ' = x–y` (`x < y`) of
`Z_k(T, ℓ)` (`k ≥ 1`) that is not a copy of the triple bond, and has length `k' ≥ 1`. -/
def CParam.Valid (p : CParam) : Prop :=
  match p.second with
  | none => True
  | some (x, y, k') => 1 ≤ p.k ∧ 1 ≤ k' ∧ x < y ∧ mult (gen1 p.k) x y ≠ 0 ∧ mult (gen1 p.k) x y ≤ 2

/-- The names of the second ladder are fresh for the first. -/
theorem fresh_second (k k' : ℕ) : Fresh k' (gen1 k) 5 := by
  rintro z ⟨i, _, h⟩ hz
  rcases gen1_ends hz with h' | ⟨j, _, h'⟩ <;> omega

theorem genC_ends {p : CParam} (hp : p.Valid) {z : ℕ} (h : InEnds (genC p) z) :
    z ≤ 2 ∨ IsNew p.k 3 z ∨ IsNew p.k₂ 5 z := by
  rcases p with ⟨k, _ | ⟨x, y, k'⟩⟩
  · rcases gen1_ends h with h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
  · simp only [CParam.Valid] at hp
    simp only [genC, CParam.k₂] at h ⊢
    rcases ladder_ends k' hp.2.2.2.1 h with h | h
    · rcases gen1_ends h with h | h
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr h)

end WaveTurbulence.TVine.Checker
