/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.TVine.Core.PhiSub

/-!
# The uniform ladder on `ℕ` (for vine (II))

The ladder with `M + 1` rungs on the labels `0` (first joint), `1` (second joint), `2 + 2j`, `3 + 2j` (rung `j`,
`j ≤ M`): rails `0–2`, `0–3`, `2+2j – 4+2j`, `3+2j – 5+2j` (`j < M`), `2+2M – 1`, `3+2M – 1`; rungs doubled.

* `ladRungs`, `ladRails`, `ladMS`;
* `IsLadRung`, `IsLadRail` (arithmetic descriptions), `mem_ladRungs`, `mem_ladRails`;
* `count_ladMS`: the count of `s(x, y)` is `2·[rung] + [rail]`;
* `ladRail_of_rung`, `ladLo_rung`: the rail neighbours of a rung atom;
* `ladSig`: the relabelling after deleting the rung `{r, r + 1}` (straight, or twisted above it), with
  `ladSig_inj`, `ladSig_lt`, `ladSig_surj`, and the count identity `cnt_del`.
-/

@[expose] public section

namespace WaveTurbulence.TVine.Core

open TVine

/-- The rungs of the uniform ladder. -/
def ladRungs (M : ℕ) : List (Sym2 ℕ) := (List.range (M + 1)).map fun j => s(2 + 2 * j, 3 + 2 * j)

/-- The rails of the uniform ladder. -/
def ladRails (M : ℕ) : List (Sym2 ℕ) :=
  [s(0, 2), s(0, 3)] ++ (List.range M).map (fun j => s(2 + 2 * j, 4 + 2 * j)) ++
    (List.range M).map (fun j => s(3 + 2 * j, 5 + 2 * j)) ++ [s(2 + 2 * M, 1), s(3 + 2 * M, 1)]

/-- The bond multiset of the uniform ladder (rungs doubled). -/
def ladMS (M : ℕ) : Multiset (Sym2 ℕ) := (ladRungs M : Multiset (Sym2 ℕ)) + ladRungs M + ladRails M

/-- `x, y` form a rung. -/
def IsLadRung (M x y : ℕ) : Prop :=
  2 ≤ x ∧ 2 ≤ y ∧ x / 2 = y / 2 ∧ x ≠ y ∧ x ≤ 3 + 2 * M ∧ y ≤ 3 + 2 * M

/-- `x, y` form a rail, in this order. -/
def IsLadRail1 (M x y : ℕ) : Prop :=
  (x = 0 ∧ (y = 2 ∨ y = 3)) ∨ (2 ≤ x ∧ y = x + 2 ∧ y ≤ 3 + 2 * M) ∨ (y = 1 ∧ (x = 2 + 2 * M ∨ x = 3 + 2 * M))

/-- `x, y` form a rail. -/
def IsLadRail (M x y : ℕ) : Prop := IsLadRail1 M x y ∨ IsLadRail1 M y x

instance (M x y : ℕ) : Decidable (IsLadRung M x y) := by unfold IsLadRung; infer_instance
instance (M x y : ℕ) : Decidable (IsLadRail1 M x y) := by unfold IsLadRail1; infer_instance
instance (M x y : ℕ) : Decidable (IsLadRail M x y) := by unfold IsLadRail; infer_instance

theorem mem_ladRungs {M x y : ℕ} : s(x, y) ∈ ladRungs M ↔ IsLadRung M x y := by
  unfold ladRungs IsLadRung
  simp only [List.mem_map, List.mem_range]
  constructor
  · rintro ⟨j, hj, h⟩
    rcases Sym2.eq_iff.mp h with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> omega
  · rintro ⟨h1, h2, h3, h4, h5, h6⟩
    refine ⟨x / 2 - 1, by omega, ?_⟩
    rw [Sym2.eq_iff]
    omega

theorem mem_ladRails {M x y : ℕ} : s(x, y) ∈ ladRails M ↔ IsLadRail M x y := by
  constructor
  · intro h
    unfold ladRails at h
    simp only [List.mem_append, List.mem_map, List.mem_range, List.mem_cons, List.mem_singleton,
      List.not_mem_nil, or_false, or_assoc] at h
    unfold IsLadRail IsLadRail1
    rcases h with h | h | ⟨j, hj, h⟩ | ⟨j, hj, h⟩ | h | h <;> rw [Sym2.eq_iff] at h <;> omega
  · intro h
    have hU : ∀ j < M, s(2 + 2 * j, 4 + 2 * j) ∈ ladRails M := fun j hj => by
      unfold ladRails; simp only [List.mem_append, List.mem_map, List.mem_range]
      exact Or.inl (Or.inl (Or.inr ⟨j, hj, rfl⟩))
    have hV : ∀ j < M, s(3 + 2 * j, 5 + 2 * j) ∈ ladRails M := fun j hj => by
      unfold ladRails; simp only [List.mem_append, List.mem_map, List.mem_range]
      exact Or.inl (Or.inr ⟨j, hj, rfl⟩)
    have h02 : s(0, 2) ∈ ladRails M := by unfold ladRails; simp
    have h03 : s(0, 3) ∈ ladRails M := by unfold ladRails; simp
    have h21 : s(2 + 2 * M, 1) ∈ ladRails M := by unfold ladRails; simp
    have h31 : s(3 + 2 * M, 1) ∈ ladRails M := by unfold ladRails; simp
    have hrail : ∀ u v, 2 ≤ u → v = u + 2 → v ≤ 3 + 2 * M → s(u, v) ∈ ladRails M := by
      intro u v hu hv hvM
      by_cases hpar : u % 2 = 0
      · have : s(u, v) = s(2 + 2 * ((u - 2) / 2), 4 + 2 * ((u - 2) / 2)) := by rw [Sym2.eq_iff]; omega
        rw [this]; exact hU _ (by omega)
      · have : s(u, v) = s(3 + 2 * ((u - 3) / 2), 5 + 2 * ((u - 3) / 2)) := by rw [Sym2.eq_iff]; omega
        rw [this]; exact hV _ (by omega)
    unfold IsLadRail IsLadRail1 at h
    rcases h with (⟨rfl, rfl | rfl⟩ | ⟨h1, h2, h3⟩ | ⟨rfl, rfl | rfl⟩) |
      (⟨rfl, rfl | rfl⟩ | ⟨h1, h2, h3⟩ | ⟨rfl, rfl | rfl⟩)
    · exact h02
    · exact h03
    · exact hrail x y h1 h2 h3
    · exact h21
    · exact h31
    · rw [Sym2.eq_swap]; exact h02
    · rw [Sym2.eq_swap]; exact h03
    · rw [Sym2.eq_swap]; exact hrail y x h1 h2 h3
    · rw [Sym2.eq_swap]; exact h21
    · rw [Sym2.eq_swap]; exact h31

theorem nodup_ladRungs (M : ℕ) : (ladRungs M).Nodup := by
  apply List.Nodup.map _ List.nodup_range
  intro i j h
  rcases Sym2.eq_iff.mp h with ⟨h1, _⟩ | ⟨h1, _⟩ <;> omega

theorem nodup_ladRails (M : ℕ) : (ladRails M).Nodup := by
  unfold ladRails
  have hU : ((List.range M).map (fun j => s(2 + 2 * j, 4 + 2 * j))).Nodup := by
    apply List.Nodup.map _ List.nodup_range
    intro i j h; rcases Sym2.eq_iff.mp h with ⟨h1, _⟩ | ⟨h1, _⟩ <;> omega
  have hV : ((List.range M).map (fun j => s(3 + 2 * j, 5 + 2 * j))).Nodup := by
    apply List.Nodup.map _ List.nodup_range
    intro i j h; rcases Sym2.eq_iff.mp h with ⟨h1, _⟩ | ⟨h1, _⟩ <;> omega
  simp only [List.nodup_append, List.mem_append, List.mem_map, List.mem_range, List.mem_cons,
    List.mem_singleton, List.not_mem_nil, or_false, List.nodup_cons, List.nodup_nil]
  refine ⟨⟨⟨⟨?_, ?_⟩, hU, ?_⟩, hV, ?_⟩, ⟨?_, ?_⟩, ?_⟩
  · simp [Sym2.eq_iff]
  · trivial
  · rintro a (rfl | rfl) b ⟨j, hj, rfl⟩ h <;> rcases Sym2.eq_iff.mp h with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> omega
  · rintro a ((rfl | rfl) | ⟨i, hi, rfl⟩) b ⟨j, hj, rfl⟩ h <;>
      rcases Sym2.eq_iff.mp h with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> omega
  · simp [Sym2.eq_iff]; omega
  · trivial
  · rintro a (((rfl | rfl) | ⟨i, hi, rfl⟩) | ⟨i, hi, rfl⟩) b (rfl | rfl) h <;>
      rcases Sym2.eq_iff.mp h with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> omega

theorem count_ladMS (M x y : ℕ) :
    (ladMS M).count s(x, y) = (if IsLadRung M x y then 2 else 0) + (if IsLadRail M x y then 1 else 0) := by
  unfold ladMS
  rw [Multiset.count_add, Multiset.count_add]
  simp only [Multiset.coe_count]
  have h1 : (ladRungs M).count s(x, y) = if IsLadRung M x y then 1 else 0 := by
    split_ifs with h
    · exact List.count_eq_one_of_mem (nodup_ladRungs M) (mem_ladRungs.mpr h)
    · exact List.count_eq_zero_of_not_mem (fun h' => h (mem_ladRungs.mp h'))
  have h2 : (ladRails M).count s(x, y) = if IsLadRail M x y then 1 else 0 := by
    split_ifs with h
    · exact List.count_eq_one_of_mem (nodup_ladRails M) (mem_ladRails.mpr h)
    · exact List.count_eq_zero_of_not_mem (fun h' => h (mem_ladRails.mp h'))
  rw [h1, h2]
  split_ifs <;> rfl

/-! ## Deleting a rung of the uniform ladder -/

/-- The lower rail neighbour of the rung atom `u`. -/
def ladLo (u : ℕ) : ℕ := if u < 4 then 0 else u - 2

/-- The upper rail neighbour of the rung atom `u` (ladder with `M + 1` rungs). -/
def ladHi (M u : ℕ) : ℕ := if 2 * M + 2 ≤ u then 1 else u + 2

/-- The relabelling after deleting the rung `{r, r + 1}`; `tw`: swap the two rails above it. -/
def ladSig (r : ℕ) (tw : Bool) (U : ℕ) : ℕ :=
  if U < r then U else if tw then (if U % 2 = 0 then U - 1 else U - 3) else U - 2

/-- The first bond added when deleting the rung `{r, r + 1}` (crossed if `tw`). -/
def ladAdd₁ (M r : ℕ) (tw : Bool) : Sym2 ℕ := if tw then s(ladLo r, ladHi M (r + 1)) else s(ladLo r, ladHi M r)

/-- The second bond added when deleting the rung `{r, r + 1}` (crossed if `tw`). -/
def ladAdd₂ (M r : ℕ) (tw : Bool) : Sym2 ℕ :=
  if tw then s(ladLo (r + 1), ladHi M r) else s(ladLo (r + 1), ladHi M (r + 1))

theorem ladRail_of_rung {M u w X : ℕ} (huw : IsLadRung M u w) (h : (ladMS M).count s(u, X) = 1) :
    X = ladLo u ∨ X = ladHi M u := by
  rw [count_ladMS] at h
  by_cases h1 : IsLadRung M u X
  · rw [if_pos h1] at h; omega
  by_cases h2 : IsLadRail M u X
  · simp only [IsLadRung, IsLadRail, IsLadRail1, ladLo, ladHi] at huw h1 h2 ⊢
    split_ifs <;> omega
  · rw [if_neg h1, if_neg h2] at h; omega

theorem ladLo_rung {M u w : ℕ} (huw : IsLadRung M u w) (hne : ladLo u ≠ ladLo w) :
    (ladMS M).count s(ladLo u, ladLo w) ≠ 0 := by
  have h : IsLadRung M (ladLo u) (ladLo w) := by
    simp only [IsLadRung, ladLo] at huw hne ⊢; split_ifs at hne ⊢ <;> omega
  rw [count_ladMS, if_pos h]; omega

theorem ladSig_spec_false {r U : ℕ} (hUr : U ≠ r) (hUr' : U ≠ r + 1) :
    (U < r ∧ ladSig r false U = U) ∨ (r + 2 ≤ U ∧ ladSig r false U + 2 = U) := by
  unfold ladSig; simp only [Bool.false_eq_true, if_false]; split_ifs <;> omega

theorem ladSig_spec_true {r U : ℕ} (hUr : U ≠ r) (hUr' : U ≠ r + 1) :
    (U < r ∧ ladSig r true U = U) ∨ (r + 2 ≤ U ∧ U % 2 = 0 ∧ ladSig r true U + 1 = U) ∨
      (r + 2 ≤ U ∧ U % 2 = 1 ∧ ladSig r true U + 3 = U) := by
  unfold ladSig; simp only [if_true]; split_ifs <;> omega

theorem ladSig_inj {r U W : ℕ} (tw : Bool) (hre : r % 2 = 0) (hUr : U ≠ r) (hUr' : U ≠ r + 1)
    (hWr : W ≠ r) (hWr' : W ≠ r + 1) (h : ladSig r tw U = ladSig r tw W) : U = W := by
  cases tw
  · have h1 := ladSig_spec_false hUr hUr'
    have h2 := ladSig_spec_false hWr hWr'
    generalize ladSig r false U = U' at h h1
    generalize ladSig r false W = W' at h h2
    omega
  · have h1 := ladSig_spec_true hUr hUr'
    have h2 := ladSig_spec_true hWr hWr'
    generalize ladSig r true U = U' at h h1
    generalize ladSig r true W = W' at h h2
    omega

theorem ladSig_lt {N r U : ℕ} (tw : Bool) (hre : r % 2 = 0) (hrN : r ≤ 2 * N + 4) (hU : U < 2 * N + 6)
    (hUr : U ≠ r) (hUr' : U ≠ r + 1) : ladSig r tw U < 2 * N + 4 := by
  cases tw
  · have h1 := ladSig_spec_false hUr hUr'
    generalize ladSig r false U = U' at h1
    omega
  · have h1 := ladSig_spec_true hUr hUr'
    generalize ladSig r true U = U' at h1
    omega

theorem ladSig_surj {N r Y : ℕ} (tw : Bool) (hr : 2 ≤ r) (hre : r % 2 = 0) (hrN : r ≤ 2 * N + 4)
    (hY : Y < 2 * N + 4) : ∃ U, U < 2 * N + 6 ∧ U ≠ r ∧ U ≠ r + 1 ∧ ladSig r tw U = Y := by
  by_cases hYr : Y < r
  · exact ⟨Y, by omega, by omega, by omega, by unfold ladSig; rw [if_pos hYr]⟩
  · cases tw
    · exact ⟨Y + 2, by omega, by omega, by omega, by
        unfold ladSig; rw [if_neg (by omega)]; simp⟩
    · by_cases hYe : Y % 2 = 0
      · exact ⟨Y + 3, by omega, by omega, by omega, by
          unfold ladSig; rw [if_neg (by omega)]; simp only [if_true]; rw [if_neg (by omega)]; omega⟩
      · exact ⟨Y + 1, by omega, by omega, by omega, by
          unfold ladSig; rw [if_neg (by omega)]; simp only [if_true]; rw [if_pos (by omega)]; omega⟩

/-- The rail neighbours of the deleted rung `{r, r + 1}` (three regimes: first rung, middle, last rung). -/
def LoHi (N r L1 L2 H1 H2 : ℕ) : Prop :=
  (r = 2 ∧ L1 = 0 ∧ L2 = 0 ∧ H1 = 4 ∧ H2 = 5) ∨
    (4 ≤ r ∧ r < 2 * N + 4 ∧ L1 + 2 = r ∧ L2 + 1 = r ∧ H1 = r + 2 ∧ H2 = r + 3) ∨
    (r = 2 * N + 4 ∧ L1 + 2 = r ∧ L2 + 1 = r ∧ H1 = 1 ∧ H2 = 1)

theorem loHi {N r : ℕ} (hr2 : 2 ≤ r) (hre : r % 2 = 0) (hrN : r ≤ 2 * N + 4) :
    LoHi N r (ladLo r) (ladLo (r + 1)) (ladHi (N + 1) r) (ladHi (N + 1) (r + 1)) := by
  unfold LoHi ladLo ladHi; split_ifs <;> omega

section DelArith

variable {N r U W U' W' L1 L2 H1 H2 : ℕ}

theorem rung_del_false (hr2 : 2 ≤ r) (hre : r % 2 = 0) (hrN : r ≤ 2 * N + 4)
    (hU' : (U < r ∧ U' = U) ∨ (r + 2 ≤ U ∧ U' + 2 = U)) (hW' : (W < r ∧ W' = W) ∨ (r + 2 ≤ W ∧ W' + 2 = W)) :
    IsLadRung (N + 1) U W ↔ IsLadRung N U' W' := by
  unfold IsLadRung
  rcases hU' with ⟨h1, h1'⟩ | ⟨h1, h1'⟩ <;> rcases hW' with ⟨h2, h2'⟩ | ⟨h2, h2'⟩ <;>
    constructor <;> intro h <;> omega

theorem rung_del_true (hr2 : 2 ≤ r) (hre : r % 2 = 0) (hrN : r ≤ 2 * N + 4)
    (hU' : (U < r ∧ U' = U) ∨ (r + 2 ≤ U ∧ U % 2 = 0 ∧ U' + 1 = U) ∨ (r + 2 ≤ U ∧ U % 2 = 1 ∧ U' + 3 = U))
    (hW' : (W < r ∧ W' = W) ∨ (r + 2 ≤ W ∧ W % 2 = 0 ∧ W' + 1 = W) ∨ (r + 2 ≤ W ∧ W % 2 = 1 ∧ W' + 3 = W)) :
    IsLadRung (N + 1) U W ↔ IsLadRung N U' W' := by
  unfold IsLadRung
  rcases hU' with ⟨h1, h1'⟩ | ⟨h1, h1'⟩ | ⟨h1, h1'⟩ <;> rcases hW' with ⟨h2, h2'⟩ | ⟨h2, h2'⟩ | ⟨h2, h2'⟩ <;>
    constructor <;> intro h <;> omega

/-- Try the disjuncts of the goal one at a time, closing each with `omega`. -/
syntax "disj_omega" : tactic
macro_rules
  | `(tactic| disj_omega) => `(tactic| first | (apply Or.inl; disj_omega) | (apply Or.inr; disj_omega) | omega)

theorem rail_del_false_mp (hr2 : 2 ≤ r) (hre : r % 2 = 0) (hrN : r ≤ 2 * N + 4) (hLH : LoHi N r L1 L2 H1 H2)
    (hU' : (U < r ∧ U' = U) ∨ (r + 2 ≤ U ∧ U' + 2 = U)) (hW' : (W < r ∧ W' = W) ∨ (r + 2 ≤ W ∧ W' + 2 = W)) :
    IsLadRail N U' W' → IsLadRail (N + 1) U W ∨ s(U, W) = s(L1, H1) ∨ s(U, W) = s(L2, H2) := by
  unfold LoHi at hLH
  simp only [IsLadRail, IsLadRail1, Sym2.eq_iff]
  intro h
  casesm* _ ∨ _, _ ∧ _ <;> disj_omega

theorem rail_del_false_mpr (hr2 : 2 ≤ r) (hre : r % 2 = 0) (hrN : r ≤ 2 * N + 4) (hLH : LoHi N r L1 L2 H1 H2)
    (hU' : (U < r ∧ U' = U) ∨ (r + 2 ≤ U ∧ U' + 2 = U)) (hW' : (W < r ∧ W' = W) ∨ (r + 2 ≤ W ∧ W' + 2 = W)) :
    (IsLadRail (N + 1) U W ∨ s(U, W) = s(L1, H1) ∨ s(U, W) = s(L2, H2)) → IsLadRail N U' W' := by
  unfold LoHi at hLH
  simp only [IsLadRail, IsLadRail1, Sym2.eq_iff]
  intro h
  casesm* _ ∨ _, _ ∧ _ <;> disj_omega

theorem rail_del_true_mp (hr2 : 2 ≤ r) (hre : r % 2 = 0) (hrN : r ≤ 2 * N + 4) (hLH : LoHi N r L1 L2 H1 H2)
    (hU' : (U < r ∧ U' = U) ∨ (r + 2 ≤ U ∧ U % 2 = 0 ∧ U' + 1 = U) ∨ (r + 2 ≤ U ∧ U % 2 = 1 ∧ U' + 3 = U))
    (hW' : (W < r ∧ W' = W) ∨ (r + 2 ≤ W ∧ W % 2 = 0 ∧ W' + 1 = W) ∨ (r + 2 ≤ W ∧ W % 2 = 1 ∧ W' + 3 = W)) :
    IsLadRail N U' W' → IsLadRail (N + 1) U W ∨ s(U, W) = s(L1, H2) ∨ s(U, W) = s(L2, H1) := by
  unfold LoHi at hLH
  simp only [IsLadRail, IsLadRail1, Sym2.eq_iff]
  intro h
  casesm* _ ∨ _, _ ∧ _ <;> disj_omega

theorem rail_del_true_mpr (hr2 : 2 ≤ r) (hre : r % 2 = 0) (hrN : r ≤ 2 * N + 4) (hLH : LoHi N r L1 L2 H1 H2)
    (hU' : (U < r ∧ U' = U) ∨ (r + 2 ≤ U ∧ U % 2 = 0 ∧ U' + 1 = U) ∨ (r + 2 ≤ U ∧ U % 2 = 1 ∧ U' + 3 = U))
    (hW' : (W < r ∧ W' = W) ∨ (r + 2 ≤ W ∧ W % 2 = 0 ∧ W' + 1 = W) ∨ (r + 2 ≤ W ∧ W % 2 = 1 ∧ W' + 3 = W)) :
    (IsLadRail (N + 1) U W ∨ s(U, W) = s(L1, H2) ∨ s(U, W) = s(L2, H1)) → IsLadRail N U' W' := by
  unfold LoHi at hLH
  simp only [IsLadRail, IsLadRail1, Sym2.eq_iff]
  intro h
  casesm* _ ∨ _, _ ∧ _ <;> disj_omega

theorem rail_del_false (hr2 : 2 ≤ r) (hre : r % 2 = 0) (hrN : r ≤ 2 * N + 4) (hLH : LoHi N r L1 L2 H1 H2)
    (hU' : (U < r ∧ U' = U) ∨ (r + 2 ≤ U ∧ U' + 2 = U)) (hW' : (W < r ∧ W' = W) ∨ (r + 2 ≤ W ∧ W' + 2 = W)) :
    IsLadRail N U' W' ↔ IsLadRail (N + 1) U W ∨ s(U, W) = s(L1, H1) ∨ s(U, W) = s(L2, H2) :=
  ⟨rail_del_false_mp hr2 hre hrN hLH hU' hW', rail_del_false_mpr hr2 hre hrN hLH hU' hW'⟩

theorem rail_del_true (hr2 : 2 ≤ r) (hre : r % 2 = 0) (hrN : r ≤ 2 * N + 4) (hLH : LoHi N r L1 L2 H1 H2)
    (hU' : (U < r ∧ U' = U) ∨ (r + 2 ≤ U ∧ U % 2 = 0 ∧ U' + 1 = U) ∨ (r + 2 ≤ U ∧ U % 2 = 1 ∧ U' + 3 = U))
    (hW' : (W < r ∧ W' = W) ∨ (r + 2 ≤ W ∧ W % 2 = 0 ∧ W' + 1 = W) ∨ (r + 2 ≤ W ∧ W % 2 = 1 ∧ W' + 3 = W)) :
    IsLadRail N U' W' ↔ IsLadRail (N + 1) U W ∨ s(U, W) = s(L1, H2) ∨ s(U, W) = s(L2, H1) :=
  ⟨rail_del_true_mp hr2 hre hrN hLH hU' hW', rail_del_true_mpr hr2 hre hrN hLH hU' hW'⟩

theorem excl_del (hr2 : 2 ≤ r) (hre : r % 2 = 0) (hrN : r ≤ 2 * N + 4) (hLH : LoHi N r L1 L2 H1 H2) :
    ¬(IsLadRail (N + 1) U W ∧ s(U, W) = s(L1, H1)) ∧ ¬(IsLadRail (N + 1) U W ∧ s(U, W) = s(L2, H2)) ∧
      ¬(s(U, W) = s(L1, H1) ∧ s(U, W) = s(L2, H2)) ∧
      ¬(IsLadRail (N + 1) U W ∧ s(U, W) = s(L1, H2)) ∧ ¬(IsLadRail (N + 1) U W ∧ s(U, W) = s(L2, H1)) ∧
      ¬(s(U, W) = s(L1, H2) ∧ s(U, W) = s(L2, H1)) := by
  unfold LoHi at hLH
  simp only [IsLadRail, IsLadRail1, Sym2.eq_iff]
  rcases hLH with ⟨h3, h4, h5, h6, h7⟩ | ⟨h3, h4, h5, h6, h7, h8⟩ | ⟨h3, h4, h5, h6, h7⟩ <;>
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> intro h <;> omega

end DelArith

/-- Six propositions whose indicator sums agree. -/
theorem cnt_eq_of {A B C D A' B' : Prop} [Decidable A] [Decidable B] [Decidable C] [Decidable D] [Decidable A']
    [Decidable B'] (hA : A ↔ A') (hB : B' ↔ B ∨ C ∨ D) (hBC : ¬(B ∧ C)) (hBD : ¬(B ∧ D)) (hCD : ¬(C ∧ D)) :
    (if A then 2 else 0) + (if B then 1 else 0) + (if C then 1 else 0) + (if D then 1 else 0) =
      (if A' then 2 else 0) + (if B' then 1 else 0) := by
  by_cases a : A <;> by_cases b : B <;> by_cases c : C <;> by_cases d : D <;> simp_all

/-- **Deleting the rung `{r, r + 1}`** of the ladder with `N + 2` rungs and adding the two rail bonds gives the
ladder with `N + 1` rungs, relabelled by `ladSig r tw`. -/
theorem cnt_del {N r U W : ℕ} (tw : Bool) (hr2 : 2 ≤ r) (hre : r % 2 = 0) (hrN : r ≤ 2 * N + 4)
    (hUr : U ≠ r) (hUr' : U ≠ r + 1) (hWr : W ≠ r) (hWr' : W ≠ r + 1) :
    (ladMS (N + 1)).count s(U, W) + (if s(U, W) = ladAdd₁ (N + 1) r tw then 1 else 0) +
      (if s(U, W) = ladAdd₂ (N + 1) r tw then 1 else 0) =
      (ladMS N).count s(ladSig r tw U, ladSig r tw W) := by
  rw [count_ladMS, count_ladMS]
  have hLH := loHi hr2 hre hrN
  have hx := excl_del (U := U) (W := W) hr2 hre hrN hLH
  unfold ladAdd₁ ladAdd₂
  generalize ladLo r = L1 at hLH hx ⊢
  generalize ladLo (r + 1) = L2 at hLH hx ⊢
  generalize ladHi (N + 1) r = H1 at hLH hx ⊢
  generalize ladHi (N + 1) (r + 1) = H2 at hLH hx ⊢
  obtain ⟨x1, x2, x3, x4, x5, x6⟩ := hx
  cases tw
  · have hU' := ladSig_spec_false hUr hUr'
    have hW' := ladSig_spec_false hWr hWr'
    generalize ladSig r false U = U' at hU' ⊢
    generalize ladSig r false W = W' at hW' ⊢
    simp only [Bool.false_eq_true, if_false]
    exact cnt_eq_of (rung_del_false hr2 hre hrN hU' hW') (rail_del_false hr2 hre hrN hLH hU' hW') x1 x2 x3
  · have hU' := ladSig_spec_true hUr hUr'
    have hW' := ladSig_spec_true hWr hWr'
    generalize ladSig r true U = U' at hU' ⊢
    generalize ladSig r true W = W' at hW' ⊢
    simp only [if_true]
    exact cnt_eq_of (rung_del_true hr2 hre hrN hU' hW') (rail_del_true hr2 hre hrN hLH hU' hW') x4 x5 x6

end WaveTurbulence.TVine.Core
