/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import Mathlib.Tactic

/-! # Counting sequences of bounded total variation (TARGET layerlad, counting step)

Sequences in `{0,…,h}` of length `n` whose total variation is at most `T` number at most `(h+1)·3^(n+T)`.
This replaces TARGET's "at most `2^{m+𝔇+1}` monotone sequences" count; only the exponential shape matters.
-/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.LayerCnt
open Finset

/-- Distance on `ℕ` (truncated subtractions). -/
@[expose] def dst (x y : ℕ) : ℕ := (x - y) + (y - x)

/-- Total variation of a list. -/
@[expose] def tvL : List ℕ → ℕ
  | [] => 0
  | [_] => 0
  | x :: y :: l => dst x y + tvL (y :: l)

/-- Lists of length `k` with entries `≤ h`. -/
@[expose] def bseqs (h : ℕ) : ℕ → Finset (List ℕ)
  | 0 => {[]}
  | k + 1 => ((range (h + 1)) ×ˢ bseqs h k).image (fun p => p.1 :: p.2)

theorem mem_bseqs {h : ℕ} {k : ℕ} {l : List ℕ} : l ∈ bseqs h k ↔ l.length = k ∧ ∀ x ∈ l, x ≤ h := by
  induction k generalizing l with
  | zero =>
    simp only [bseqs, mem_singleton, List.length_eq_zero_iff]
    constructor
    · rintro rfl; simp
    · exact fun h => h.1
  | succ k ih =>
    simp only [bseqs, mem_image, mem_product, mem_range, Prod.exists]
    constructor
    · rintro ⟨a, l', ⟨ha, hl'⟩, rfl⟩
      obtain ⟨h1, h2⟩ := ih.mp hl'
      refine ⟨by simp [h1], ?_⟩
      intro x hx
      rcases List.mem_cons.mp hx with rfl | hx
      · omega
      · exact h2 x hx
    · rintro ⟨hlen, hall⟩
      cases l with
      | nil => simp at hlen
      | cons a l' =>
        refine ⟨a, l', ⟨?_, ih.mpr ⟨by simpa using hlen, fun x hx => hall x (List.mem_cons_of_mem _ hx)⟩⟩, rfl⟩
        have := hall a (List.mem_cons_self ..)
        omega

/-- The geometric-sum step. -/
theorem geom_dst (h x : ℕ) (T : ℕ) :
    ∑ y ∈ range (h + 1), (if dst x y ≤ T then 3 ^ (T - dst x y) else 0) + 1 ≤ 2 * 3 ^ T := by
  induction T with
  | zero =>
    have : ∑ y ∈ range (h + 1), (if dst x y ≤ 0 then 3 ^ (0 - dst x y) else 0) ≤ 1 := by
      calc ∑ y ∈ range (h + 1), (if dst x y ≤ 0 then 3 ^ (0 - dst x y) else 0)
          ≤ ∑ y ∈ range (h + 1), (if y = x then 1 else 0) := by
            apply sum_le_sum
            intro y _
            by_cases hy : y = x
            · subst hy; simp [dst]
            · have : ¬ dst x y ≤ 0 := by unfold dst; omega
              simp [this, hy]
        _ ≤ 1 := by
            rw [← sum_filter]
            have : (range (h+1)).filter (fun y => y = x) ⊆ {x} := by
              intro y hy
              rw [mem_filter] at hy
              exact mem_singleton.mpr hy.2
            calc _ = ∑ y ∈ (range (h+1)).filter (fun y => y = x), 1 := rfl
              _ = ((range (h+1)).filter (fun y => y = x)).card := by simp
              _ ≤ 1 := by simpa using card_le_card this
    omega
  | succ T ih =>
    set H : ℕ → ℕ := fun T => ∑ y ∈ range (h + 1), (if dst x y ≤ T then 3 ^ (T - dst x y) else 0) with hH
    have hstep : H (T+1) ≤ 3 * H T + 2 := by
      have h1 : ∀ y ∈ range (h+1), (if dst x y ≤ T+1 then 3 ^ (T + 1 - dst x y) else 0) ≤
          3 * (if dst x y ≤ T then 3 ^ (T - dst x y) else 0) + (if dst x y = T + 1 then 1 else 0) := by
        intro y _
        by_cases h1 : dst x y ≤ T
        · have : T + 1 - dst x y = (T - dst x y) + 1 := by omega
          have e : (if dst x y = T + 1 then 1 else 0) = 0 := by simp; omega
          rw [if_pos (by omega), if_pos h1, this, e, pow_succ]; omega
        · by_cases h2 : dst x y = T + 1
          · simp [h1, h2]
          · have : ¬ dst x y ≤ T + 1 := by omega
            simp [h1, h2, this]
      calc H (T+1) ≤ ∑ y ∈ range (h+1), (3 * (if dst x y ≤ T then 3 ^ (T - dst x y) else 0)
              + (if dst x y = T + 1 then 1 else 0)) := sum_le_sum h1
        _ = 3 * H T + ∑ y ∈ range (h+1), (if dst x y = T + 1 then 1 else 0) := by
            rw [sum_add_distrib, ← mul_sum]
        _ ≤ 3 * H T + 2 := by
            have hc : ∑ y ∈ range (h+1), (if dst x y = T + 1 then 1 else 0) ≤ 2 := by
              rw [← sum_filter]
              have hs : (range (h+1)).filter (fun y => dst x y = T + 1) ⊆ {x + (T+1), x - (T+1)} := by
                intro y hy
                simp only [mem_filter] at hy
                have := hy.2
                unfold dst at this
                simp only [mem_insert, mem_singleton]
                omega
              calc _ = ((range (h+1)).filter (fun y => dst x y = T + 1)).card := by simp
                _ ≤ ({x + (T+1), x - (T+1)} : Finset ℕ).card := card_le_card hs
                _ ≤ 2 := card_le_two
            omega
    have : H T + 1 ≤ 2 * 3 ^ T := ih
    show H (T+1) + 1 ≤ 2 * 3 ^ (T+1)
    rw [pow_succ]
    omega

/-- The count: lists `x :: l` with `l` of length `k`, entries `≤ h` and `tvL ≤ T` number at most `3^(k+T)`. -/
theorem card_tv_le (h : ℕ) (k : ℕ) : ∀ (x T : ℕ),
    ((bseqs h k).filter (fun l => tvL (x :: l) ≤ T)).card ≤ 3 ^ (k + T) := by
  induction k with
  | zero =>
    intro x T
    have : ((bseqs h 0).filter (fun l => tvL (x :: l) ≤ T)).card ≤ (bseqs h 0).card := card_filter_le _ _
    simp only [bseqs, card_singleton] at this
    calc _ ≤ 1 := this
      _ ≤ 3 ^ (0 + T) := Nat.one_le_pow _ _ (by norm_num)
  | succ k ih =>
    intro x T
    classical
    have himg : (bseqs h (k+1)).filter (fun l => tvL (x :: l) ≤ T) =
        (((range (h + 1)) ×ˢ bseqs h k).filter (fun p => tvL (x :: p.1 :: p.2) ≤ T)).image
          (fun p => p.1 :: p.2) := by
      ext l
      simp only [bseqs, mem_filter, mem_image, mem_product, mem_range, Prod.exists]
      constructor
      · rintro ⟨⟨a, l', ha, rfl⟩, hl⟩
        exact ⟨a, l', ⟨ha, hl⟩, rfl⟩
      · rintro ⟨a, l', ⟨ha, hl⟩, rfl⟩
        exact ⟨⟨a, l', ha, rfl⟩, hl⟩
    rw [himg]
    refine (card_image_le).trans ?_
    rw [card_filter, sum_product]
    have hterm : ∀ y ∈ range (h+1),
        ∑ l ∈ bseqs h k, (if tvL (x :: y :: l) ≤ T then 1 else 0) ≤
          3 ^ k * (if dst x y ≤ T then 3 ^ (T - dst x y) else 0) := by
      intro y _
      by_cases hd : dst x y ≤ T
      · rw [if_pos hd]
        have : ∑ l ∈ bseqs h k, (if tvL (x :: y :: l) ≤ T then 1 else 0) =
            ((bseqs h k).filter (fun l => tvL (y :: l) ≤ T - dst x y)).card := by
          rw [card_filter]
          apply sum_congr rfl
          intro l _
          have : tvL (x :: y :: l) = dst x y + tvL (y :: l) := rfl
          rw [this]
          by_cases hc : tvL (y :: l) ≤ T - dst x y
          · have : dst x y + tvL (y :: l) ≤ T := by omega
            simp [hc, this]
          · have : ¬ dst x y + tvL (y :: l) ≤ T := by omega
            simp [hc, this]
        rw [this]
        calc _ ≤ 3 ^ (k + (T - dst x y)) := ih y _
          _ = 3 ^ k * 3 ^ (T - dst x y) := pow_add _ _ _
      · rw [if_neg hd]
        have : ∀ l ∈ bseqs h k, (if tvL (x :: y :: l) ≤ T then 1 else 0) = 0 := by
          intro l _
          have : tvL (x :: y :: l) = dst x y + tvL (y :: l) := rfl
          rw [this]
          have : ¬ dst x y + tvL (y :: l) ≤ T := by omega
          simp [this]
        rw [sum_congr rfl this]; simp
    calc _ ≤ ∑ y ∈ range (h+1), 3 ^ k * (if dst x y ≤ T then 3 ^ (T - dst x y) else 0) := sum_le_sum hterm
      _ = 3 ^ k * ∑ y ∈ range (h+1), (if dst x y ≤ T then 3 ^ (T - dst x y) else 0) := by rw [← mul_sum]
      _ ≤ 3 ^ k * (3 * 3 ^ T) := by
          apply Nat.mul_le_mul_left
          have := geom_dst h x T
          omega
      _ = 3 ^ (k + 1 + T) := by ring

/-- Lists of length `k+1` with entries `≤ h` and total variation `≤ T` number at most `(h+1)·3^(k+T)`. -/
theorem card_tv_all (h k T : ℕ) :
    ((bseqs h (k+1)).filter (fun l => tvL l ≤ T)).card ≤ (h + 1) * 3 ^ (k + T) := by
  classical
  have himg : (bseqs h (k+1)).filter (fun l => tvL l ≤ T) =
      ((range (h + 1)).sigma (fun x => (bseqs h k).filter (fun l => tvL (x :: l) ≤ T))).image
        (fun p => p.1 :: p.2) := by
    ext l
    simp only [bseqs, mem_filter, mem_image, mem_product, mem_range, mem_sigma, Sigma.exists, Prod.exists]
    constructor
    · rintro ⟨⟨a, l', ha, rfl⟩, hl⟩
      exact ⟨a, l', ⟨ha.1, ⟨ha.2, hl⟩⟩, rfl⟩
    · rintro ⟨a, l', ⟨ha, ha2, hl⟩, rfl⟩
      exact ⟨⟨a, l', ⟨ha, ha2⟩, rfl⟩, hl⟩
  rw [himg]
  refine card_image_le.trans ?_
  rw [card_sigma]
  calc _ ≤ ∑ x ∈ range (h+1), 3 ^ (k + T) := sum_le_sum (fun x _ => card_tv_le h k x T)
    _ = (h+1) * 3 ^ (k + T) := by simp

end WaveTurbulence.LayerCnt
