/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.TVine.Struct.Drawn.Ladder
public import WaveTurbulence.Foundations.TVine.Struct.Drawn.Bases

/-!
# The expanded templates `T_X(k⃗)` as ladder multisets (packet L3D)

B2's `VineType.expand X k⃗` folds `insertRungs` over the slots: at the `i`-th slot it inserts `k_i` rungs named from
the current size `n` on (`u`-rail `n, …, n + k_i - 1`, `v`-rail `n + k_i, …, n + 2k_i - 1`).

* `fold_insertRungs`: the bonds of the fold are `A + laddersO sl k⃗ n₀` when the template's bonds are `A + slotsO sl`,
  and the size is `n₀ + 2 Σ k⃗`;
* `expand_tvine`: for a template with good slot data (`Good`) whose base is a T-vine, every expansion is a T-vine with
  joints `0, 1`.
-/

@[expose] public section
set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace WaveTurbulence.TVine.Struct.Drawn

open TVine WaveTurbulence.TVine.Core

/-- All slot bonds, as ordered pairs. -/
def slotsO (sl : List Slot) : Multiset (ℕ × ℕ) := (sl.map fun s => ({s.1, s.2} : Multiset (ℕ × ℕ))).sum

theorem ladderO_nil (s : Slot) : ladderO s [] [] = {s.1, s.2} := by
  simp [ladderO, railBonds_nil]; rfl

theorem tmplMS_eq (T : VineTemplate) : tmplMS T = (↑T.bonds : Multiset (ℕ × ℕ)).map mk2 := rfl

/-- One `insertRungs` step, as a multiset identity. -/
theorem insertRungs_bonds (T : VineTemplate) (s : Slot) (k : ℕ) (B : Multiset (ℕ × ℕ))
    (hT : (↑T.bonds : Multiset (ℕ × ℕ)) = {s.1, s.2} + B) :
    (↑(insertRungs T s k).bonds : Multiset (ℕ × ℕ)) = ladderO s (uN T.n k k) (vN T.n k k) + B ∧
      (insertRungs T s k).n = T.n + 2 * k := by
  unfold insertRungs
  split_ifs with hk
  · subst hk
    refine ⟨?_, by simp⟩
    rw [hT, uN_zero, vN_zero, ladderO_nil]
  · refine ⟨?_, rfl⟩
    have hu : (List.range k).map (T.n + ·) = uN T.n k k := by
      unfold uN; apply List.map_congr_left; intro j _; omega
    have hv : (List.range k).map (T.n + k + ·) = vN T.n k k := by
      unfold vN; apply List.map_congr_left; intro j _; omega
    simp only [hu, hv]
    unfold ladderO
    rw [← Multiset.coe_add, ← Multiset.coe_add, ← Multiset.coe_add, ← Multiset.coe_add, ← Multiset.coe_add,
      ← Multiset.coe_erase, ← Multiset.coe_erase, hT]
    rw [Multiset.insert_eq_cons, ← Multiset.cons_zero, Multiset.cons_add, Multiset.cons_add, zero_add,
      Multiset.erase_cons_head, Multiset.erase_cons_head]
    abel

theorem fold_insertRungs : ∀ (sl : List Slot) (Ks : List ℕ) (T : VineTemplate) (A : Multiset (ℕ × ℕ)),
    Ks.length = sl.length → (↑T.bonds : Multiset (ℕ × ℕ)) = A + slotsO sl →
    (↑(List.foldl (fun T sk => insertRungs T sk.1 sk.2) T (sl.zip Ks)).bonds : Multiset (ℕ × ℕ)) =
        A + laddersO sl Ks T.n ∧
      (List.foldl (fun T sk => insertRungs T sk.1 sk.2) T (sl.zip Ks)).n = T.n + 2 * Ks.sum
  | [], Ks, T, A, hl, hT => by
    have hK : Ks = [] := List.eq_nil_of_length_eq_zero (by simpa using hl)
    subst hK
    simp only [List.zip_nil_left, List.foldl_nil, List.sum_nil, mul_zero, add_zero, and_true]
    rw [hT]; simp [slotsO, laddersO]
  | s :: sl, Ks, T, A, hl, hT => by
    obtain ⟨K, Ks', rfl⟩ : ∃ K Ks', Ks = K :: Ks' := by
      cases Ks with
      | nil => simp at hl
      | cons K Ks' => exact ⟨K, Ks', rfl⟩
    have hl' : Ks'.length = sl.length := by simpa using hl
    obtain ⟨h1, h2⟩ := insertRungs_bonds T s K (A + slotsO sl) (by
      rw [hT]; simp only [slotsO, List.map_cons, List.sum_cons]; abel)
    obtain ⟨h3, h4⟩ := fold_insertRungs sl Ks' (insertRungs T s K) (A + ladderO s (uN T.n K K) (vN T.n K K)) hl'
      (by rw [h1]; abel)
    simp only [List.zip_cons_cons, List.foldl_cons]
    refine ⟨?_, ?_⟩
    · rw [h3, h2, laddersO, add_assoc]
    · rw [h4, h2, List.sum_cons]; ring

theorem slotsO_map (sl : List Slot) : (slotsO sl).map mk2 = slotsMS sl := by
  induction sl with
  | nil => simp [slotsO, slotsMS]
  | cons s sl ih =>
    simp only [slotsO, slotsMS, List.map_cons, List.sum_cons, Multiset.map_add] at ih ⊢
    rw [ih]
    simp [slotMS]

/-- **Every expansion of a good template whose base is a T-vine is a T-vine** (joints `0, 1`). -/
theorem expand_tvine (X : VineType) (A₀ : Multiset (ℕ × ℕ)) (ts : List SlotD)
    (h1 : (↑X.template.bonds : Multiset (ℕ × ℕ)) = A₀ + slotsO X.template.slots)
    (h3 : ts.map SlotD.sl = X.template.slots) (h2 : Good X.template.n (A₀.map mk2) ts)
    (hbase : IsTVineU (ofMS (Finset.range X.template.n) (tmplMS X.template)) 0 1)
    (Ks : List ℕ) (hK : Ks.length = X.template.slots.length) :
    IsTVineU (ofMS (Finset.range (X.expand Ks).n) (tmplMS (X.expand Ks))) 0 1 := by
  have hts : Ks.length = ts.length := by rw [hK, ← h3, List.length_map]
  obtain ⟨hb, hn⟩ := fold_insertRungs X.template.slots Ks X.template A₀ hK h1
  have hbase' : IsTVineU (ofMS (Finset.range X.template.n) (A₀.map mk2 + slotsMS (ts.map SlotD.sl))) 0 1 := by
    have : tmplMS X.template = A₀.map mk2 + slotsMS (ts.map SlotD.sl) := by
      rw [h3, ← slotsO_map, ← Multiset.map_add, ← h1, tmplMS_eq]
    rw [← this]; exact hbase
  have hmain := tvine_ladders X.template.n ts (A₀.map mk2) Ks X.template.n hts le_rfl h2 hbase'
  have hV : Finset.range (X.expand Ks).n = Finset.range X.template.n ∪ namesF Ks X.template.n := by
    unfold VineType.expand
    rw [hn]
    ext a; simp only [namesF, Finset.mem_union, Finset.mem_range, Finset.mem_Ico]; omega
  have hM : tmplMS (X.expand Ks) = A₀.map mk2 + ladders (ts.map SlotD.sl) Ks X.template.n := by
    unfold VineType.expand
    rw [tmplMS_eq, hb, Multiset.map_add, h3]
    rfl
  rw [hV, hM]
  exact hmain

end WaveTurbulence.TVine.Struct.Drawn
