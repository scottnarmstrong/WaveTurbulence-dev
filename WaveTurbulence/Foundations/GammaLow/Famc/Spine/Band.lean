/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import Mathlib.Data.Fintype.BigOperators
public import Mathlib.Data.Fintype.Pi
import Mathlib.Tactic
/-! # Band codes: an exponential family of arc lists (packet L5a, item H)

The class count (TARGET finalprooffin, L2241–L2247: "at most `C₀ⁿ (C₀ρ̄)!` choices for `𝕄(𝒢_sk)`") encodes every vine
ingredient of a unit by a finite word. Main's codes (`ClassCount.IngCode`) enumerate the eight drawn templates. For
T-vines we use **band codes**: a labelling `0, …, n − 1` of the atoms in which all but at most four bonds join labels
at distance at most `bandW = 6` (N3 Theorem 6: the pieces form a spine and at most one pendant, consecutive pieces are
joined, pieces have at most three atoms; the only long bonds are the two joining the last spine piece to the label-`0`
joint and the two attachment bonds of the pendant). A band code records, for every label `i` and offset
`k ∈ [0, 12]`, the number (`≤ 4`) of arcs `(i, i + k − 6)`, and the list (length `≤ 4`) of the other arcs.

This module is pure combinatorics: the code sets `bandCodesAt n`, their exponential bound `card_bandCodesAt_le`, and
the decomposition `exists_band_code` of every band-admissible arc multiset. -/
@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.GammaLow.Famc.ClassCount
open Finset

/-- The band width. -/
def bandW : ℕ := 6

theorem bandW_eq : bandW = 6 := rfl

/-- A short arc: its endpoints are at distance at most `bandW`. -/
def ShortArc (q : ℕ × ℕ) : Prop := q.2 ≤ q.1 + bandW ∧ q.1 ≤ q.2 + bandW

instance (q : ℕ × ℕ) : Decidable (ShortArc q) := by unfold ShortArc; infer_instance

/-- The short arc from `i` with offset index `k` (target `i + k − bandW`), if the target is a natural number. -/
def shortArcAt (i k : ℕ) : ℕ × ℕ := (i, i + k - bandW)

/-- The arc list of a band code: `mult i k` copies of `shortArcAt i k` (`i < n`, `k ≤ 2 bandW`, `i + k ≥ bandW`),
followed by the long arcs. -/
def bandArcs (n : ℕ) (mult : ℕ → ℕ → ℕ) (long : List (ℕ × ℕ)) : List (ℕ × ℕ) :=
  ((List.range n).flatMap fun i => (List.range (2 * bandW + 1)).flatMap fun k =>
    if bandW ≤ i + k then List.replicate (mult i k) (shortArcAt i k) else []) ++ long

/-- Lists of at most four arcs with endpoints below `n`. -/
noncomputable def longLists (n : ℕ) : Finset (List (ℕ × ℕ)) :=
  (range 5).biUnion fun L => (univ : Finset (Fin L → Fin n × Fin n)).image
    fun g => List.ofFn fun i => ((g i).1.val, (g i).2.val)

/-- The band arc lists of size `n`. -/
noncomputable def bandArcLists (n : ℕ) : Finset (List (ℕ × ℕ)) :=
  ((univ : Finset (Fin n → Fin (2 * bandW + 1) → Fin 5)) ×ˢ longLists n).image fun p =>
    bandArcs n (fun i k => if h : i < n ∧ k < 2 * bandW + 1 then (p.1 ⟨i, h.1⟩ ⟨k, h.2⟩).val else 0) p.2

theorem card_longLists_le (n : ℕ) : (longLists n).card ≤ 5 * (n + 1) ^ 8 := by
  unfold longLists
  refine card_biUnion_le.trans ?_
  calc ∑ L ∈ range 5, ((univ : Finset (Fin L → Fin n × Fin n)).image _).card
      ≤ ∑ L ∈ range 5, (n * n) ^ L := by
        refine sum_le_sum fun L _ => card_image_le.trans ?_
        simp [Fintype.card_fun, Fintype.card_prod, Fintype.card_fin]
    _ ≤ ∑ _L ∈ range 5, (n + 1) ^ 8 := by
        refine sum_le_sum fun L hL => ?_
        have hL4 : L ≤ 4 := by have := mem_range.mp hL; omega
        calc (n * n) ^ L ≤ ((n + 1) ^ 2) ^ L := Nat.pow_le_pow_left (by nlinarith) L
          _ = (n + 1) ^ (2 * L) := by rw [← pow_mul]
          _ ≤ (n + 1) ^ 8 := Nat.pow_le_pow_right (by omega) (by omega)
    _ = 5 * (n + 1) ^ 8 := by simp

theorem card_bandArcLists_le (n : ℕ) : (bandArcLists n).card ≤ 5 ^ (13 * n) * (5 * (n + 1) ^ 8) := by
  unfold bandArcLists
  refine card_image_le.trans ?_
  rw [card_product, card_univ, Fintype.card_fun, Fintype.card_fun, Fintype.card_fin, Fintype.card_fin,
    Fintype.card_fin]
  refine Nat.mul_le_mul (le_of_eq ?_) (card_longLists_le n)
  rw [← pow_mul, show bandW = 6 from rfl]

/-- An exponential bound: `|bandArcLists n| ≤ (2 ^ 100) ^ (n - 1)` for `n ≥ 2`. -/
theorem card_bandArcLists_le' (n : ℕ) (hn : 2 ≤ n) : (bandArcLists n).card ≤ (2 ^ 100) ^ (n - 1) := by
  refine (card_bandArcLists_le n).trans ?_
  have h1 : (n + 1) ^ 8 ≤ (2 ^ 8) ^ n := by
    rw [← pow_mul, mul_comm, pow_mul]
    have : n < 2 ^ n := Nat.lt_two_pow_self
    exact Nat.pow_le_pow_left (by omega) 8
  have h2 : (5 : ℕ) ^ (13 * n) ≤ (2 ^ 39) ^ n := by
    rw [pow_mul, ← pow_mul]
    calc (5 : ℕ) ^ (13 * n) = (5 ^ 13) ^ n := by rw [pow_mul]
      _ ≤ (2 ^ 39) ^ n := Nat.pow_le_pow_left (by norm_num) n
      _ = 2 ^ (39 * n) := by rw [← pow_mul]
      _ = (2 ^ 39) ^ n := by rw [pow_mul]
  calc 5 ^ (13 * n) * (5 * (n + 1) ^ 8) ≤ (2 ^ 39) ^ n * (2 ^ 3 * (2 ^ 8) ^ n) :=
        Nat.mul_le_mul h2 (Nat.mul_le_mul (by norm_num) h1)
    _ = 2 ^ (47 * n + 3) := by
        rw [← pow_mul, ← pow_mul, ← pow_add, ← pow_add]; congr 1; ring
    _ ≤ 2 ^ (100 * (n - 1)) := Nat.pow_le_pow_right (by norm_num) (by omega)
    _ = (2 ^ 100) ^ (n - 1) := by rw [pow_mul]

/-- An arc multiset is band-admissible at size `n`: endpoints below `n`, at most four long arcs, every short arc of
multiplicity at most four. -/
def BandAdmissible (n : ℕ) (m : Multiset (ℕ × ℕ)) : Prop :=
  (∀ q ∈ m, q.1 < n ∧ q.2 < n) ∧ Multiset.card (m.filter fun q => ¬ ShortArc q) ≤ 4 ∧
    ∀ q, ShortArc q → m.count q ≤ 4

theorem count_flatMap_range_single {α : Type*} [DecidableEq α] (n : ℕ) (g : ℕ → List α) (q : α) (j : ℕ)
    (hj : ∀ i, i ≠ j → q ∉ g i) : ((List.range n).flatMap g).count q = if j < n then (g j).count q else 0 := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [List.range_succ, List.flatMap_append, List.count_append, ih]
    simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil]
    by_cases hjn : j = n
    · subst hjn; simp
    · rw [List.count_eq_zero.mpr (hj n (Ne.symm hjn))]
      by_cases h : j < n
      · rw [if_pos h, if_pos (by omega), add_zero]
      · rw [if_neg h, if_neg (by omega)]

/-- The short part of a band code. -/
def bandShort (n : ℕ) (mult : ℕ → ℕ → ℕ) : List (ℕ × ℕ) :=
  (List.range n).flatMap fun i => (List.range (2 * bandW + 1)).flatMap fun k =>
    if bandW ≤ i + k then List.replicate (mult i k) (shortArcAt i k) else []

theorem bandArcs_eq (n : ℕ) (mult : ℕ → ℕ → ℕ) (long : List (ℕ × ℕ)) :
    bandArcs n mult long = bandShort n mult ++ long := rfl

theorem mem_bandShort {n : ℕ} {mult : ℕ → ℕ → ℕ} {q : ℕ × ℕ} (h : q ∈ bandShort n mult) : ShortArc q := by
  obtain ⟨i, hi, h⟩ := List.mem_flatMap.mp h
  obtain ⟨k, hk, h⟩ := List.mem_flatMap.mp h
  split_ifs at h with hik
  · rw [List.eq_of_mem_replicate h]
    have := List.mem_range.mp hk
    simp only [ShortArc, shortArcAt, bandW] at this ⊢; omega
  · simp at h

theorem count_bandShort (n : ℕ) (mult : ℕ → ℕ → ℕ) {q : ℕ × ℕ} (hq : ShortArc q) :
    (bandShort n mult).count q = if q.1 < n then mult q.1 (q.2 + bandW - q.1) else 0 := by
  unfold bandShort
  rw [count_flatMap_range_single n _ q q.1 (by
    intro i hi hmem
    obtain ⟨k, -, h⟩ := List.mem_flatMap.mp hmem
    split_ifs at h
    · exact hi (congrArg Prod.fst (List.eq_of_mem_replicate h)).symm
    · simp at h)]
  have hq6 := hq
  unfold ShortArc at hq6
  rw [bandW_eq] at hq6
  by_cases hqn : q.1 < n
  · rw [if_pos hqn, if_pos hqn]
    have hk : q.2 + bandW - q.1 < 2 * bandW + 1 := by rw [bandW_eq]; omega
    have hq' : shortArcAt q.1 (q.2 + bandW - q.1) = q := by
      simp only [shortArcAt, bandW_eq]; ext <;> simp <;> omega
    rw [count_flatMap_range_single (2 * bandW + 1) _ q (q.2 + bandW - q.1) (by
      intro k hk' hmem
      split_ifs at hmem with hik
      · apply hk'
        have h2 := congrArg Prod.snd (List.eq_of_mem_replicate hmem)
        simp only [shortArcAt, bandW_eq] at h2 hik ⊢
        omega
      · simp at hmem)]
    rw [if_pos hk, if_pos (by simp only [bandW_eq]; omega), hq', List.count_replicate_self]
  · rw [if_neg hqn, if_neg hqn]

/-- **Every band-admissible arc multiset is the arc multiset of a band code.** -/
theorem exists_band_code (n : ℕ) (m : Multiset (ℕ × ℕ)) (hm : BandAdmissible n m) :
    ∃ l ∈ bandArcLists n, (l : Multiset (ℕ × ℕ)) = m := by
  classical
  obtain ⟨hlt, hlong, hmult⟩ := hm
  set lg := (m.filter fun q => ¬ ShortArc q).toList with hlg
  have hlgn : ∀ q ∈ lg, q.1 < n ∧ q.2 < n := fun q hq => hlt q (Multiset.mem_filter.mp (Multiset.mem_toList.mp hq)).1
  have hlgL : lg.length ≤ 4 := by rw [hlg, Multiset.length_toList]; exact hlong
  let F : Fin n → Fin (2 * bandW + 1) → Fin 5 := fun i k =>
    ⟨min 4 (m.count (shortArcAt i.val k.val)), by omega⟩
  have hlgmem : lg ∈ longLists n := by
    unfold longLists
    refine mem_biUnion.mpr ⟨lg.length, mem_range.mpr (by omega), mem_image.mpr ⟨fun i =>
      (⟨(lg.get i).1, (hlgn _ (List.get_mem _ _)).1⟩, ⟨(lg.get i).2, (hlgn _ (List.get_mem _ _)).2⟩),
      mem_univ _, ?_⟩⟩
    exact List.ext_get (by simp) (fun i h1 h2 => by simp)
  set mult : ℕ → ℕ → ℕ := fun i k => if h : i < n ∧ k < 2 * bandW + 1 then (F ⟨i, h.1⟩ ⟨k, h.2⟩).val else 0
  refine ⟨_, mem_image.mpr ⟨(F, lg), mem_product.mpr ⟨mem_univ _, hlgmem⟩, rfl⟩, ?_⟩
  ext q
  rw [Multiset.coe_count, bandArcs_eq, List.count_append]
  by_cases hq : ShortArc q
  · have hlg0 : lg.count q = 0 := List.count_eq_zero.mpr fun h =>
      (Multiset.mem_filter.mp (Multiset.mem_toList.mp h)).2 hq
    rw [hlg0, add_zero, count_bandShort n _ hq]
    by_cases hqn : q.1 < n
    · rw [if_pos hqn]
      have hq6 := hq
      unfold ShortArc at hq6
      rw [bandW_eq] at hq6
      have hk : q.2 + bandW - q.1 < 2 * bandW + 1 := by rw [bandW_eq]; omega
      have hq' : shortArcAt q.1 (q.2 + bandW - q.1) = q := by
        simp only [shortArcAt, bandW_eq]; ext <;> simp <;> omega
      simp only [mult, dif_pos (And.intro hqn hk), F, hq']
      exact min_eq_right (hmult q hq)
    · rw [if_neg hqn]
      symm
      exact Multiset.count_eq_zero.mpr fun h => hqn (hlt q h).1
  · rw [List.count_eq_zero.mpr fun h => hq (mem_bandShort h), zero_add, hlg, ← Multiset.coe_count,
      Multiset.coe_toList, Multiset.count_filter_of_pos (p := fun q => ¬ ShortArc q) hq]

end WaveTurbulence.GammaLow.Famc.ClassCount
