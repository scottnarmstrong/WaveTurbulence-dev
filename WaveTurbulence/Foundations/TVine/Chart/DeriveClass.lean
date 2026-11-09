/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.TVine.Chart.DeriveLay
public import WaveTurbulence.Foundations.TVine.Chart.LemmaD

/-!
# Derivation of the cell decomposition, III: positions, bond classification, prefix regions

For a layout (`Lay`):
* every atom lies in exactly one block (`Z i`, `i ≤ r + 1`, or `Y k`, `k < s`);
* every bond joins two consecutive spine blocks, two consecutive pendant blocks, the pendant top `Y 0` and a spine
  block (an attachment bond, crossing `H 0`), or lies inside one block (N3 Theorem 6 (i), from the bond counts);
* the prefix region `reg i h` (the spine blocks `Z 0 … Z i`, and the pendant if `h`) is crossed exactly by the
  bonds between `Z i` and `Z (i+1)` and by the attachment bonds whose spine end is on the other side.
-/

@[expose] public section
set_option autoImplicit false

namespace WaveTurbulence.TVine.Chart

open Finset VineParamContract Struct

variable {V D : Type} [DecidableEq V] [Fintype D] [DecidableEq D] {M : Molecule V D} {S : Finset V} {a b : V}

namespace Lay

variable (L : Lay M S a b) (hB : M.IsBlock S a b)
include hB

theorem a_ne_b : a ≠ b := hB.2.2.2.1

theorem Z_sub {i : ℕ} (hi : i ≤ L.r + 1) : L.Z i ⊆ S := by
  rcases Nat.eq_zero_or_pos i with rfl | h0
  · rw [L.Z_zero]; exact singleton_subset_iff.mpr hB.2.2.1
  rcases Nat.lt_or_ge i (L.r + 1) with h1 | h1
  · exact fun v hv => mem_of_mem_erase (mem_of_mem_erase (pieces_sub (L.Z_piece i h0 (by omega)) hv))
  · have : i = L.r + 1 := by omega
    subst this; rw [L.Z_last]; exact singleton_subset_iff.mpr hB.2.1

theorem Y_sub {k : ℕ} (hk : k < L.s) : L.Y k ⊆ S :=
  fun v hv => mem_of_mem_erase (mem_of_mem_erase (pieces_sub (L.Y_piece k hk) hv))

omit hB in
theorem Y_interior {k : ℕ} (hk : k < L.s) {v : V} (hv : v ∈ L.Y k) : v ≠ a ∧ v ≠ b := by
  have := pieces_sub (L.Y_piece k hk) hv
  simp only [mem_erase] at this
  exact ⟨this.2.1, this.1⟩

omit hB in
theorem Z_interior {i : ℕ} (h0 : 1 ≤ i) (hi : i ≤ L.r) {v : V} (hv : v ∈ L.Z i) : v ≠ a ∧ v ≠ b := by
  have := pieces_sub (L.Z_piece i h0 hi) hv
  simp only [mem_erase] at this
  exact ⟨this.2.1, this.1⟩

theorem atom_cases {v : V} (hv : v ∈ S) : (∃ i, i ≤ L.r + 1 ∧ v ∈ L.Z i) ∨ (∃ k, k < L.s ∧ v ∈ L.Y k) := by
  by_cases ha : v = a
  · subst ha; exact Or.inl ⟨L.r + 1, le_refl _, by rw [L.Z_last]; exact mem_singleton_self _⟩
  by_cases hb : v = b
  · subst hb; exact Or.inl ⟨0, by omega, by rw [L.Z_zero]; exact mem_singleton_self _⟩
  obtain ⟨P, hP, hvP⟩ := pieces_cover (M := M) hv ha hb
  rcases L.all P hP with ⟨i, h1, h2, rfl⟩ | ⟨k, hk, rfl⟩
  · exact Or.inl ⟨i, by omega, hvP⟩
  · exact Or.inr ⟨k, hk, hvP⟩

theorem Z_unique {i j : ℕ} (hi : i ≤ L.r + 1) (hj : j ≤ L.r + 1) {v : V} (hvi : v ∈ L.Z i) (hvj : v ∈ L.Z j) :
    i = j := by
  have hab : a ≠ b := hB.2.2.2.1
  have key : ∀ i, i ≤ L.r + 1 → v ∈ L.Z i → (i = 0 ↔ v = b) ∧ (i = L.r + 1 ↔ v = a) := by
    intro i hi hv
    rcases Nat.eq_zero_or_pos i with rfl | h0
    · rw [L.Z_zero, mem_singleton] at hv
      subst hv; exact ⟨⟨fun _ => rfl, fun _ => rfl⟩, ⟨fun h => by omega, fun h => absurd h.symm hab⟩⟩
    rcases Nat.lt_or_ge i (L.r + 1) with h1 | h1
    · have := L.Z_interior h0 (by omega) hv
      exact ⟨⟨fun h => by omega, fun h => absurd h this.2⟩, ⟨fun h => by omega, fun h => absurd h this.1⟩⟩
    · have : i = L.r + 1 := by omega
      subst this
      rw [L.Z_last, mem_singleton] at hv
      subst hv
      exact ⟨⟨fun h => by omega, fun h => absurd h hab⟩, ⟨fun _ => rfl, fun _ => rfl⟩⟩
  have ki := key i hi hvi
  have kj := key j hj hvj
  by_cases hb' : v = b
  · have := ki.1.mpr hb'; have := kj.1.mpr hb'; omega
  by_cases ha' : v = a
  · have := ki.2.mpr ha'; have := kj.2.mpr ha'; omega
  have hi0 : 1 ≤ i := by by_contra h; exact hb' (ki.1.mp (by omega))
  have hj0 : 1 ≤ j := by by_contra h; exact hb' (kj.1.mp (by omega))
  have hir : i ≤ L.r := by by_contra h; exact ha' (ki.2.mp (by omega))
  have hjr : j ≤ L.r := by by_contra h; exact ha' (kj.2.mp (by omega))
  exact L.Z_inj i j hi0 hir hj0 hjr
    (pieces_disjoint (L.Z_piece i hi0 hir) (L.Z_piece j hj0 hjr) hvi hvj)

theorem Y_unique {k l : ℕ} (hk : k < L.s) (hl : l < L.s) {v : V} (hvk : v ∈ L.Y k) (hvl : v ∈ L.Y l) : k = l :=
  L.Y_inj k l hk hl (pieces_disjoint (L.Y_piece k hk) (L.Y_piece l hl) hvk hvl)

theorem ZY_disj {i k : ℕ} (hi : i ≤ L.r + 1) (hk : k < L.s) {v : V} (hvi : v ∈ L.Z i) (hvk : v ∈ L.Y k) : False := by
  have hY := L.Y_interior hk hvk
  rcases Nat.eq_zero_or_pos i with rfl | h0
  · rw [L.Z_zero, mem_singleton] at hvi; exact hY.2 hvi
  rcases Nat.lt_or_ge i (L.r + 1) with h1 | h1
  · exact L.ZY_ne i k h0 (by omega) hk
      (pieces_disjoint (L.Z_piece i h0 (by omega)) (L.Y_piece k hk) hvi hvk)
  · have : i = L.r + 1 := by omega
    subst this; rw [L.Z_last, mem_singleton] at hvi; exact hY.1 hvi

omit hB in
theorem Y_sub_H {k : ℕ} (hk : k < L.s) : L.Y k ⊆ L.H k := fun v hv => (L.mem_H k v).mpr ⟨k, le_refl _, hk, hv⟩

theorem H_sub (k : ℕ) : L.H k ⊆ S := by
  intro v hv
  obtain ⟨l, -, hl, hv⟩ := (L.mem_H k v).mp hv
  exact L.Y_sub hB hl hv

theorem not_mem_H_of_Z {i k : ℕ} (hi : i ≤ L.r + 1) {v : V} (hv : v ∈ L.Z i) : v ∉ L.H k := by
  intro h
  obtain ⟨l, -, hl, hvl⟩ := (L.mem_H k v).mp h
  exact L.ZY_disj hB hi hl hv hvl

/-! ## Bond classification -/

/-- Two spine blocks joined by a bond are consecutive. -/
theorem ZZ_consec {e : Bond M S} {i j : ℕ} (hi : i ≤ L.r + 1) (hj : j ≤ L.r + 1) (h1 : tl e ∈ L.Z i)
    (h2 : hd e ∈ L.Z j) (hne : i ≠ j) : j = i + 1 ∨ i = j + 1 := by
  by_contra hc
  push Not at hc
  rcases Nat.lt_or_gt_of_ne hne with hlt | hgt
  · exact not_cross_of_zero (L.Z_sub hB hi) (L.Z_sub hB hj) (L.nonconsec i j hj (by omega)) h1 h2
  · have h0 := L.nonconsec j i hi (by omega)
    rw [← card_cross (L.Z_sub hB hj) (L.Z_sub hB hi), cross_comm, card_cross (L.Z_sub hB hi) (L.Z_sub hB hj)] at h0
    exact not_cross_of_zero (L.Z_sub hB hi) (L.Z_sub hB hj) h0 h1 h2

omit hB in
/-- The pendant data, when there is a pendant. -/
theorem pend_of {k : ℕ} (hk : k < L.s) :
    1 ≤ L.s ∧ IsCoreD M (L.Y (L.s - 1)) ∧ (∀ k, k + 1 < L.s → IsRungPiece M (L.Y k)) ∧
      (∀ k, k + 1 < L.s → crossBonds M (L.Y k) (L.Y (k + 1)) = 2) ∧
      (∀ k l, l < L.s → k + 2 ≤ l → crossBonds M (L.Y k) (L.Y l) = 0) ∧
      (∀ k, k < L.s → ∃ x x' : V, TwoSingleExits M S (L.H k) (L.Y k) x x' ∧
        (k = 0 →
          (∃ i, 1 ≤ i ∧ i ≤ L.r ∧ x ∈ L.Z i ∧ x' ∈ L.Z i ∧ IsJunctionPiece M (L.Z i) ∧
            crossBonds M (L.Z i) (S \ L.Z i) = 6 ∧ ∀ P ∈ M.pieces S a b, crossBonds M P (S \ P) = 6 → P = L.Z i) ∨
          (∃ i, i ≤ L.r ∧ crossBonds M (L.Z i) (L.Z (i + 1)) = 1 ∧
            ((x ∈ L.Z i ∧ x' ∈ L.Z (i + 1)) ∨ (x' ∈ L.Z i ∧ x ∈ L.Z (i + 1)))))) := by
  rcases L.pend with ⟨h0, -⟩ | h
  · omega
  · exact h

/-- Two pendant blocks joined by a bond are consecutive. -/
theorem YY_consec {e : Bond M S} {k l : ℕ} (hk : k < L.s) (hl : l < L.s) (h1 : tl e ∈ L.Y k)
    (h2 : hd e ∈ L.Y l) (hne : k ≠ l) : l = k + 1 ∨ k = l + 1 := by
  obtain ⟨-, -, -, -, hnon, -⟩ := L.pend_of hk
  by_contra hc
  push Not at hc
  rcases Nat.lt_or_gt_of_ne hne with hlt | hgt
  · exact not_cross_of_zero (L.Y_sub hB hk) (L.Y_sub hB hl) (hnon k l hl (by omega)) h1 h2
  · have h0 := hnon l k hk (by omega)
    rw [← card_cross (L.Y_sub hB hl) (L.Y_sub hB hk), cross_comm, card_cross (L.Y_sub hB hk) (L.Y_sub hB hl)] at h0
    exact not_cross_of_zero (L.Y_sub hB hk) (L.Y_sub hB hl) h0 h1 h2

/-- The crossing bonds of `H k` are the bonds `Y (k−1) – Y k` for `k ≥ 1`. -/
theorem cross_H_eq {k : ℕ} (hk : k < L.s) (hk1 : 1 ≤ k) :
    cross (M := M) (S := S) (L.H k) (S \ L.H k) = cross (L.Y (k - 1)) (L.Y k) := by
  obtain ⟨-, -, -, hc2, -, hex⟩ := L.pend_of hk
  obtain ⟨x, x', ⟨hcard, -⟩, -⟩ := hex k hk
  have hsub : cross (M := M) (S := S) (L.Y (k - 1)) (L.Y k) ⊆ cross (L.H k) (S \ L.H k) := by
    intro e he
    rw [mem_cross] at he ⊢
    have hYk : ∀ v, v ∈ L.Y k → v ∈ L.H k := fun v hv => L.Y_sub_H hk hv
    have hYk1 : ∀ v, v ∈ L.Y (k - 1) → v ∈ S \ L.H k := by
      intro v hv
      refine mem_sdiff.mpr ⟨L.Y_sub hB (by omega) hv, fun hH => ?_⟩
      obtain ⟨l, hl1, hl2, hvl⟩ := (L.mem_H k v).mp hH
      have := L.Y_unique hB (by omega) hl2 hv hvl
      omega
    rcases he with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact Or.inr ⟨hYk1 _ h1, hYk _ h2⟩
    · exact Or.inl ⟨hYk _ h1, hYk1 _ h2⟩
  symm
  apply Finset.eq_of_subset_of_card_le hsub
  have hc : crossBonds M (L.Y (k - 1)) (L.Y k) = 2 := by
    have := hc2 (k - 1) (by omega); rwa [show k - 1 + 1 = k by omega] at this
  rw [card_cross (L.H_sub hB k) sdiff_subset, card_cross (L.Y_sub hB (by omega)) (L.Y_sub hB hk), hcard, hc]

/-- A bond from a pendant block to a spine block starts at the pendant top and crosses `H 0` (an attachment bond). -/
theorem YZ_att {e : Bond M S} {k i : ℕ} (hk : k < L.s) (hi : i ≤ L.r + 1)
    (h : (tl e ∈ L.Y k ∧ hd e ∈ L.Z i) ∨ (hd e ∈ L.Y k ∧ tl e ∈ L.Z i)) :
    k = 0 ∧ e ∈ cross (L.H 0) (S \ L.H 0) := by
  have hcrossk : e ∈ cross (M := M) (S := S) (L.H k) (S \ L.H k) := by
    rw [mem_cross]
    rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact Or.inl ⟨L.Y_sub_H hk h1, mem_sdiff.mpr ⟨L.Z_sub hB hi h2, L.not_mem_H_of_Z hB hi h2⟩⟩
    · exact Or.inr ⟨mem_sdiff.mpr ⟨L.Z_sub hB hi h2, L.not_mem_H_of_Z hB hi h2⟩, L.Y_sub_H hk h1⟩
  rcases Nat.eq_zero_or_pos k with rfl | hk1
  · exact ⟨rfl, hcrossk⟩
  exfalso
  rw [L.cross_H_eq hB hk hk1, mem_cross] at hcrossk
  rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> rcases hcrossk with ⟨h3, h4⟩ | ⟨h3, h4⟩
  · have := L.Y_unique hB (by omega) hk h3 h1; omega
  · exact L.ZY_disj hB hi (by omega) h2 h4
  · exact L.ZY_disj hB hi (by omega) h2 h3
  · have := L.Y_unique hB (by omega) hk h4 h1; omega

/-! ## Prefix regions -/

/-- The prefix region: the spine blocks `Z 0, …, Z i`, and the pendant if `h`. -/
def reg (i : ℕ) (h : Bool) : Finset V := (range (i + 1)).biUnion L.Z ∪ (if h then L.H 0 else ∅)

omit hB in
theorem mem_reg {i : ℕ} {h : Bool} {v : V} : v ∈ L.reg i h ↔ (∃ j, j ≤ i ∧ v ∈ L.Z j) ∨ (h = true ∧ v ∈ L.H 0) := by
  unfold reg
  rw [mem_union, mem_biUnion]
  simp only [mem_range, Nat.lt_succ_iff]
  cases h <;> simp

theorem mem_reg_Z {i j : ℕ} {h : Bool} (hi : i ≤ L.r + 1) (hj : j ≤ L.r + 1) {v : V} (hv : v ∈ L.Z j) :
    v ∈ L.reg i h ↔ j ≤ i := by
  rw [L.mem_reg]
  constructor
  · rintro (⟨j', hj', hv'⟩ | ⟨-, hH⟩)
    · rw [L.Z_unique hB hj (by omega) hv hv']; exact hj'
    · exact absurd hH (L.not_mem_H_of_Z hB hj hv)
  · intro hji; exact Or.inl ⟨j, hji, hv⟩

theorem mem_reg_Y {i k : ℕ} {h : Bool} (hi : i ≤ L.r + 1) (hk : k < L.s) {v : V} (hv : v ∈ L.Y k) :
    v ∈ L.reg i h ↔ h = true := by
  rw [L.mem_reg]
  constructor
  · rintro (⟨j', hj', hv'⟩ | ⟨hh, -⟩)
    · exact absurd hv (fun hv => L.ZY_disj hB (by omega) hk hv' hv)
    · exact hh
  · intro hh; exact Or.inr ⟨hh, (L.mem_H 0 v).mpr ⟨k, by omega, hk, hv⟩⟩

theorem reg_sub (i : ℕ) (hi : i ≤ L.r + 1) (h : Bool) : L.reg i h ⊆ S := by
  intro v hv
  rcases L.mem_reg.mp hv with ⟨j, hj, hvj⟩ | ⟨-, hH⟩
  · exact L.Z_sub hB (by omega) hvj
  · exact L.H_sub hB 0 hH

/-- **The crossing bonds of a prefix region.** -/
theorem crosses_reg {i : ℕ} (hi : i ≤ L.r) (h : Bool) (e : Bond M S) :
    Crosses (L.reg i h) e ↔ e ∈ cross (L.Z i) (L.Z (i + 1)) ∨
      (e ∈ cross (L.H 0) (S \ L.H 0) ∧ ∃ j, j ≤ L.r + 1 ∧ (tl e ∈ L.Z j ∨ hd e ∈ L.Z j) ∧ (j ≤ i ↔ h = false)) := by
  unfold Crosses
  rcases L.atom_cases hB (tl_mem e) with ⟨j, hj, htl⟩ | ⟨k, hk, htl⟩ <;>
    rcases L.atom_cases hB (hd_mem e) with ⟨j', hj', hhd⟩ | ⟨k', hk', hhd⟩
  · -- spine – spine
    rw [L.mem_reg_Z hB (by omega) hj htl, L.mem_reg_Z hB (by omega) hj' hhd, mem_cross]
    have hnoatt : ¬ e ∈ cross (M := M) (S := S) (L.H 0) (S \ L.H 0) := by
      rw [mem_cross]
      rintro (⟨h1, -⟩ | ⟨-, h2⟩)
      · exact L.not_mem_H_of_Z hB hj htl h1
      · exact L.not_mem_H_of_Z hB hj' hhd h2
    simp only [hnoatt, false_and, or_false]
    constructor
    · rintro (⟨h1, h2⟩ | ⟨h1, h2⟩)
      · have hne : j ≠ j' := by omega
        rcases L.ZZ_consec hB hj hj' htl hhd hne with h3 | h3
        · left; refine ⟨?_, ?_⟩ <;> [rw [show i = j by omega]; rw [show i + 1 = j' by omega]] <;> assumption
        · omega
      · have hne : j ≠ j' := by omega
        rcases L.ZZ_consec hB hj hj' htl hhd hne with h3 | h3
        · omega
        · right; refine ⟨?_, ?_⟩ <;> [rw [show i + 1 = j by omega]; rw [show i = j' by omega]] <;> assumption
    · rintro (⟨h1, h2⟩ | ⟨h1, h2⟩)
      · have e1 := L.Z_unique hB hj (by omega) htl h1
        have e2 := L.Z_unique hB hj' (by omega) hhd h2
        left; omega
      · have e1 := L.Z_unique hB hj (by omega) htl h1
        have e2 := L.Z_unique hB hj' (by omega) hhd h2
        right; omega
  · -- spine – pendant
    obtain ⟨hk0, hatt⟩ := L.YZ_att hB hk' hj (Or.inr ⟨hhd, htl⟩)
    rw [L.mem_reg_Z hB (by omega) hj htl, L.mem_reg_Y hB (by omega) hk' hhd]
    have hnoZ : ¬ e ∈ cross (M := M) (S := S) (L.Z i) (L.Z (i + 1)) := by
      rw [mem_cross]
      rintro (⟨-, h2⟩ | ⟨-, h2⟩)
      · exact L.ZY_disj hB (by omega) hk' h2 hhd
      · exact L.ZY_disj hB (by omega) hk' h2 hhd
    simp only [hnoZ, hatt, true_and, false_or]
    constructor
    · intro hc
      refine ⟨j, hj, Or.inl htl, ?_⟩
      cases h <;> simp_all
    · rintro ⟨j'', hj'', h3, h4⟩
      rcases h3 with h3 | h3
      · rw [L.Z_unique hB hj hj'' htl h3]; cases h <;> simp_all
      · exact absurd hhd (fun hh => L.ZY_disj hB hj'' hk' h3 hh)
  · -- pendant – spine
    obtain ⟨hk0, hatt⟩ := L.YZ_att hB hk hj' (Or.inl ⟨htl, hhd⟩)
    rw [L.mem_reg_Y hB (by omega) hk htl, L.mem_reg_Z hB (by omega) hj' hhd]
    have hnoZ : ¬ e ∈ cross (M := M) (S := S) (L.Z i) (L.Z (i + 1)) := by
      rw [mem_cross]
      rintro (⟨h1, -⟩ | ⟨h1, -⟩)
      · exact L.ZY_disj hB (by omega) hk h1 htl
      · exact L.ZY_disj hB (by omega) hk h1 htl
    simp only [hnoZ, hatt, true_and, false_or]
    constructor
    · intro hc
      refine ⟨j', hj', Or.inr hhd, ?_⟩
      cases h <;> simp_all
    · rintro ⟨j'', hj'', h3, h4⟩
      rcases h3 with h3 | h3
      · exact absurd htl (fun hh => L.ZY_disj hB hj'' hk h3 hh)
      · rw [L.Z_unique hB hj' hj'' hhd h3]; cases h <;> simp_all
  · -- pendant – pendant
    rw [L.mem_reg_Y hB (by omega) hk htl, L.mem_reg_Y hB (by omega) hk' hhd]
    have hnoZ : ¬ e ∈ cross (M := M) (S := S) (L.Z i) (L.Z (i + 1)) := by
      rw [mem_cross]
      rintro (⟨h1, -⟩ | ⟨h1, -⟩)
      · exact L.ZY_disj hB (by omega) hk h1 htl
      · exact L.ZY_disj hB (by omega) hk h1 htl
    simp only [hnoZ, false_or]
    constructor
    · intro hc; exfalso; tauto
    · rintro ⟨-, j'', hj'', h3, -⟩
      rcases h3 with h3 | h3
      · exact absurd htl (fun hh => L.ZY_disj hB hj'' hk h3 hh)
      · exact absurd hhd (fun hh => L.ZY_disj hB hj'' hk' h3 hh)

end Lay

end WaveTurbulence.TVine.Chart
