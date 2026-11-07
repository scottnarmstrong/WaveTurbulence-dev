/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.LayerCnt.CutBase
import Mathlib.Tactic

/-! # Cut certificates of expanded templates (TARGET layervine, L1531)

`CertAt T A σ`: `σ` is a cut labelling of the bonds of `T` separating the joints `0`, `1`, with level-`1` set
inside `A`.  Certificates of the base cut groups and of the rungs of the base cut slots survive all insertions.
-/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.LayerCnt
open WaveTurbulence.Vine

/-- A cut certificate: values `≤ 2`, the joints on opposite outer sides, no crossing bond, level-`1` set in `A`. -/
@[expose] def CertAt (T : VineTemplate) (A : ℕ → Prop) (σ : ℕ → ℕ) : Prop :=
  (∀ v, σ v ≤ 2) ∧ ((σ 0 = 0 ∧ σ 1 = 2) ∨ (σ 0 = 2 ∧ σ 1 = 0)) ∧ CutOn T.bonds [] σ ∧
    ∀ v < T.n, σ v = 1 → A v

theorem fold_ext (xs : List (((ℕ × ℕ) × (ℕ × ℕ)) × ℕ)) (M : ℕ) :
    ∀ (T : VineTemplate) (E : List (ℕ × ℕ)) (σ : ℕ → ℕ), M ≤ T.n →
      (∀ e ∈ T.bonds, e.1 < T.n ∧ e.2 < T.n) →
      (∀ sk ∈ xs, T.bonds.count sk.1.1 ≤ 1 ∧ T.bonds.count sk.1.2 ≤ 1) →
      (∀ sk ∈ xs, (∀ v ∈ slotEnds sk.1, v < M) ∧ Sides2 σ (slotEnds sk.1)) →
      CutOn T.bonds E σ → (∀ v, σ v ≤ 2) →
      ∃ σ', (∀ v < T.n, σ' v = σ v) ∧ (∀ v, σ' v ≤ 2) ∧
        (∀ v, T.n ≤ v → v < (xs.foldl (fun U sk => insertRungs U sk.1 sk.2) T).n → σ' v ≠ 1) ∧
        CutOn (xs.foldl (fun U sk => insertRungs U sk.1 sk.2) T).bonds E σ' := by
  induction xs with
  | nil =>
    intro T E σ _ _ _ _ h hσ
    exact ⟨σ, fun _ _ => rfl, hσ, fun v h1 h2 => by simp at h2; omega, h⟩
  | cons sk xs ih =>
    intro T E σ hM hbdd hcnt hside h hσ
    have hsk := hside sk List.mem_cons_self
    have hc := hcnt sk List.mem_cons_self
    by_cases hk : sk.2 = 0
    · have hz : insertRungs T sk.1 sk.2 = T := by rw [hk]; exact insertRungs_zero _ _
      simp only [List.foldl_cons, hz]
      obtain ⟨σ', h1, h2, h3, h4⟩ := ih T E σ hM hbdd
        (fun sk' hsk' => hcnt sk' (List.mem_cons_of_mem _ hsk'))
        (fun sk' hsk' => hside sk' (List.mem_cons_of_mem _ hsk')) h hσ
      exact ⟨σ', h1, h2, h3, h4⟩
    · have hends : ∀ v ∈ slotEnds sk.1, v < T.n := fun v hv => lt_of_lt_of_le (hsk.1 v hv) hM
      have hext := ext_insert hk hc.1 hc.2 hends hbdd hsk.2 h
      set σ1 := extσ T.n sk.2 (newSide σ sk.1) σ with hσ1
      have hσ1le : ∀ v, σ1 v ≤ 2 := by
        intro v
        by_cases hv : T.n ≤ v ∧ v < T.n + 2 * sk.2
        · rw [hσ1, extσ_new hv.1 hv.2]; unfold newSide; split_ifs <;> omega
        · rw [hσ1]; unfold extσ; rw [if_neg hv]; exact hσ v
      have hn' : (insertRungs T sk.1 sk.2).n = T.n + 2 * sk.2 := insertRungs_atoms _ _ _
      have hold : ∀ v < T.n, σ1 v = σ v := fun v hv => extσ_old hv
      obtain ⟨σ', h1, h2, h3, h4⟩ := ih (insertRungs T sk.1 sk.2) E σ1 (by omega)
        (bdd_insert hends hbdd)
        (fun sk' hsk' => by
          have hc' := hcnt sk' (List.mem_cons_of_mem _ hsk')
          have he := hside sk' (List.mem_cons_of_mem _ hsk')
          have hb : ∀ p q : ℕ, (p ∈ slotEnds sk'.1) → (q ∈ slotEnds sk'.1) → p < T.n ∧ q < T.n := by
            intro p q hp hq
            exact ⟨lt_of_lt_of_le (he.1 p hp) hM, lt_of_lt_of_le (he.1 q hq) hM⟩
          have hA := hb sk'.1.1.1 sk'.1.1.2 (by simp [slotEnds]) (by simp [slotEnds])
          have hB := hb sk'.1.2.1 sk'.1.2.2 (by simp [slotEnds]) (by simp [slotEnds])
          exact ⟨(count_insert_le (s := sk.1) (k := sk.2) hA).trans hc'.1,
            (count_insert_le (s := sk.1) (k := sk.2) hB).trans hc'.2⟩)
        (fun sk' hsk' => by
          have he := hside sk' (List.mem_cons_of_mem _ hsk')
          refine ⟨he.1, ?_⟩
          intro ⟨⟨v, hv, hv0⟩, ⟨w, hw, hw2⟩⟩
          apply he.2
          refine ⟨⟨v, hv, ?_⟩, ⟨w, hw, ?_⟩⟩
          · rw [← hold v (lt_of_lt_of_le (he.1 v hv) hM)]; exact hv0
          · rw [← hold w (lt_of_lt_of_le (he.1 w hw) hM)]; exact hw2)
        hext hσ1le
      refine ⟨σ', fun v hv => ?_, h2, ?_, ?_⟩
      · rw [h1 v (by omega), hold v hv]
      · intro v hv1 hv2
        simp only [List.foldl_cons] at hv2
        by_cases hvv : v < T.n + 2 * sk.2
        · have := h1 v (by omega)
          rw [this, hσ1, extσ_new hv1 hvv]; unfold newSide; split_ifs <;> omega
        · exact h3 v (by omega) hv2
      · simpa only [List.foldl_cons] using h4

theorem fold_bdd (xs : List (((ℕ × ℕ) × (ℕ × ℕ)) × ℕ)) (M : ℕ) :
    ∀ (T : VineTemplate), M ≤ T.n → (∀ e ∈ T.bonds, e.1 < T.n ∧ e.2 < T.n) →
      (∀ sk ∈ xs, ∀ v ∈ slotEnds sk.1, v < M) →
      ∀ e ∈ (xs.foldl (fun U sk => insertRungs U sk.1 sk.2) T).bonds,
        e.1 < (xs.foldl (fun U sk => insertRungs U sk.1 sk.2) T).n ∧
        e.2 < (xs.foldl (fun U sk => insertRungs U sk.1 sk.2) T).n := by
  induction xs with
  | nil => intro T _ hb _; exact hb
  | cons sk xs ih =>
    intro T hM hb he
    simp only [List.foldl_cons]
    have hends : ∀ v ∈ slotEnds sk.1, v < T.n := fun v hv =>
      lt_of_lt_of_le (he sk List.mem_cons_self v hv) hM
    refine ih _ (by rw [insertRungs_atoms]; omega) (bdd_insert hends hb)
      (fun sk' hsk' => he sk' (List.mem_cons_of_mem _ hsk'))

theorem fold_count (xs : List (((ℕ × ℕ) × (ℕ × ℕ)) × ℕ)) (M : ℕ) :
    ∀ (T : VineTemplate) (e : ℕ × ℕ), e.1 < M → e.2 < M → M ≤ T.n →
      (∀ sk ∈ xs, ∀ v ∈ slotEnds sk.1, v < M) →
      (xs.foldl (fun U sk => insertRungs U sk.1 sk.2) T).bonds.count e ≤ T.bonds.count e := by
  induction xs with
  | nil => intro T e _ _ _ _; exact le_rfl
  | cons sk xs ih =>
    intro T e h1 h2 hM he
    simp only [List.foldl_cons]
    refine (ih _ e h1 h2 (by rw [insertRungs_atoms]; omega)
      (fun sk' hsk' => he sk' (List.mem_cons_of_mem _ hsk'))).trans ?_
    exact count_insert_le (by omega)

end WaveTurbulence.LayerCnt
