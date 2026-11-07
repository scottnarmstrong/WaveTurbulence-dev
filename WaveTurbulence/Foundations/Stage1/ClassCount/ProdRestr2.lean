/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

import Mathlib.Tactic
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Data.Fintype.Pi
public import Mathlib.Data.Fintype.BigOperators
public import Mathlib.Data.Real.Basic

/-!
# CLASSCOUNT: product of restrictions, non-local weights

A sum over a finite family `𝓕` of layerings of a product of weights `w i`, each depending only on the
restriction of the layering to a block `A i` (blocks pairwise disjoint), is bounded by
`(𝔇+1)^{#atoms outside the blocks}` times the product of the suprema of the block sums over subfamilies
that are pairwise distinct on the block (these are the families to which `layerlad`/`layervine` apply).
-/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.ClassCount
open Finset

variable {V : Type*} [Fintype V] [DecidableEq V] {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Restriction to a set, extended by zero. -/
def restr (A : Finset V) (f : V → ℕ) : V → ℕ := fun x => if x ∈ A then f x else 0

theorem restr_apply_of_mem {A : Finset V} {x : V} (f : V → ℕ) (hx : x ∈ A) : restr A f x = f x := by
  simp [restr, hx]

/-- **Product of restrictions, non-local weights.**  The weights `w i` need not depend only on the restriction to the
private block `P i`; the bound `X i` is required for every subfamily that is distinct on `P i`. -/
theorem sum_prod_restr_le' (𝓕 : Finset (V → ℕ)) (𝔇 : ℕ) (hf : ∀ f ∈ 𝓕, ∀ x, f x ≤ 𝔇)
    (A : ι → Finset V) (hA : ∀ i j, i ≠ j → Disjoint (A i) (A j))
    (w : ι → (V → ℕ) → ℝ) (hw0 : ∀ i f, 0 ≤ w i f)
    (X : ι → ℝ)
    (hX : ∀ i, ∀ 𝓖 ⊆ 𝓕, (∀ f ∈ 𝓖, ∀ f' ∈ 𝓖, (∀ x ∈ A i, f x = f' x) → f = f') →
      ∑ f ∈ 𝓖, w i f ≤ X i) :
    ∑ f ∈ 𝓕, ∏ i, w i f ≤ ((𝔇 + 1 : ℕ) : ℝ) ^ (Finset.univ \ Finset.univ.biUnion A).card * ∏ i, X i := by
  classical
  set Rr : Finset V := Finset.univ \ Finset.univ.biUnion A with hRr
  let Φ : (V → ℕ) → (V → ℕ) × (ι → V → ℕ) := fun f => (restr Rr f, fun i => restr (A i) f)
  have hinj : Set.InjOn Φ (𝓕 : Set (V → ℕ)) := by
    intro f _ f' _ h
    have h1 : restr Rr f = restr Rr f' := congrArg Prod.fst h
    have h2 : ∀ i, restr (A i) f = restr (A i) f' := fun i => congrFun (congrArg Prod.snd h) i
    funext x
    by_cases hx : x ∈ Rr
    · have := congrFun h1 x
      simpa [restr, hx] using this
    · have : ∃ i, x ∈ A i := by
        by_contra hne
        push Not at hne
        exact hx (by simp [hRr, hne])
      obtain ⟨i, hi⟩ := this
      have := congrFun (h2 i) x
      simpa [restr, hi] using this
  set ResR : Finset (V → ℕ) := 𝓕.image (restr Rr) with hResR
  set Res : ι → Finset (V → ℕ) := fun i => 𝓕.image (restr (A i)) with hRes
  -- maximizing representatives
  have hmax : ∀ i, ∀ y ∈ Res i, ∃ f ∈ 𝓕, restr (A i) f = y ∧ ∀ f' ∈ 𝓕, restr (A i) f' = y → w i f' ≤ w i f := by
    intro i y hy
    obtain ⟨f0, hf0, rfl⟩ := Finset.mem_image.mp hy
    obtain ⟨f, hf, hmaxf⟩ := Finset.exists_max_image (𝓕.filter (fun f' => restr (A i) f' = restr (A i) f0))
      (w i) ⟨f0, Finset.mem_filter.mpr ⟨hf0, rfl⟩⟩
    obtain ⟨hf1, hf2⟩ := Finset.mem_filter.mp hf
    exact ⟨f, hf1, hf2, fun f' hf' h' => hmaxf f' (Finset.mem_filter.mpr ⟨hf', h'⟩)⟩
  let rep : ι → (V → ℕ) → (V → ℕ) := fun i y =>
    if h : y ∈ Res i then (hmax i y h).choose else y
  have hrep : ∀ i, ∀ y ∈ Res i, rep i y ∈ 𝓕 ∧ restr (A i) (rep i y) = y ∧
      ∀ f' ∈ 𝓕, restr (A i) f' = y → w i f' ≤ w i (rep i y) := by
    intro i y hy
    simp only [rep, dite_eq_left_iff, not_not, hy, not_true_eq_false, dif_pos]
    exact (hmax i y hy).choose_spec
  let ws : ι → (V → ℕ) → ℝ := fun i y => w i (rep i y)
  have hws : ∀ f ∈ 𝓕, ∀ i, w i f ≤ ws i (restr (A i) f) := by
    intro f hf i
    exact (hrep i _ (Finset.mem_image_of_mem _ hf)).2.2 f hf rfl
  have hws0 : ∀ i y, 0 ≤ ws i y := fun i y => hw0 i _
  calc ∑ f ∈ 𝓕, ∏ i, w i f ≤ ∑ f ∈ 𝓕, ∏ i, ws i (restr (A i) f) :=
        Finset.sum_le_sum fun f hf => Finset.prod_le_prod₀ (fun i _ => hw0 i f) (fun i _ => hws f hf i)
    _ = ∑ y ∈ 𝓕.image Φ, ∏ i, ws i (y.2 i) := by
        rw [Finset.sum_image hinj]
    _ ≤ ∑ y ∈ ResR ×ˢ Fintype.piFinset Res, ∏ i, ws i (y.2 i) := by
        apply Finset.sum_le_sum_of_subset_of_nonneg
        · intro y hy
          obtain ⟨f, hf', rfl⟩ := Finset.mem_image.mp hy
          refine Finset.mem_product.mpr ⟨Finset.mem_image_of_mem _ hf', ?_⟩
          rw [Fintype.mem_piFinset]
          intro i
          exact Finset.mem_image_of_mem _ hf'
        · intro y _ _
          exact Finset.prod_nonneg fun i _ => hws0 i _
    _ = (ResR.card : ℝ) * ∏ i, ∑ x ∈ Res i, ws i x := by
        rw [Finset.sum_product, Finset.prod_univ_sum]
        simp
    _ ≤ ((𝔇 + 1 : ℕ) : ℝ) ^ Rr.card * ∏ i, X i := by
        refine mul_le_mul ?_ ?_ (Finset.prod_nonneg fun i _ => Finset.sum_nonneg fun x _ => hws0 i x)
          (by positivity)
        · have hsub : ResR ⊆ Fintype.piFinset (fun x : V => if x ∈ Rr then Finset.range (𝔇 + 1) else {0}) := by
            intro y hy
            obtain ⟨f, hf', rfl⟩ := Finset.mem_image.mp hy
            rw [Fintype.mem_piFinset]
            intro x
            by_cases hx : x ∈ Rr
            · simp only [hx, ite_true, Finset.mem_range, restr]
              exact Nat.lt_succ_of_le (hf f hf' x)
            · simp [hx, restr]
          have h1 := Finset.card_le_card hsub
          rw [Fintype.card_piFinset] at h1
          have h2 : ∏ x : V, (if x ∈ Rr then Finset.range (𝔇 + 1) else {0}).card = (𝔇 + 1) ^ Rr.card := by
            have : ∀ x : V, (if x ∈ Rr then Finset.range (𝔇 + 1) else ({0} : Finset ℕ)).card
                = if x ∈ Rr then 𝔇 + 1 else 1 := by
              intro x; by_cases hx : x ∈ Rr <;> simp [hx]
            simp only [this]
            rw [Finset.prod_ite, Finset.prod_const_one, mul_one, Finset.prod_const]
            simp [Finset.filter_mem_eq_inter]
          rw [h2] at h1
          exact_mod_cast h1
        · refine Finset.prod_le_prod₀ (fun i _ => Finset.sum_nonneg fun x _ => hws0 i x) (fun i _ => ?_)
          have hrinj : Set.InjOn (rep i) (Res i : Set (V → ℕ)) := by
            intro y hy y' hy' h
            rw [← (hrep i y hy).2.1, ← (hrep i y' hy').2.1, h]
          have hG : (Res i).image (rep i) ⊆ 𝓕 := by
            intro f hf'
            obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hf'
            exact (hrep i y hy).1
          have hdist : ∀ f ∈ (Res i).image (rep i), ∀ f' ∈ (Res i).image (rep i),
              (∀ x ∈ A i, f x = f' x) → f = f' := by
            intro f hf' f' hf'' h
            obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hf'
            obtain ⟨y', hy', rfl⟩ := Finset.mem_image.mp hf''
            have : y = y' := by
              rw [← (hrep i y hy).2.1, ← (hrep i y' hy').2.1]
              funext x
              by_cases hx : x ∈ A i
              · simp only [restr, hx, ite_true]; exact h x hx
              · simp [hx, restr]
            rw [this]
          have hsum : ∑ x ∈ Res i, ws i x = ∑ f ∈ (Res i).image (rep i), w i f := by
            rw [Finset.sum_image hrinj]
          rw [hsum]
          exact hX i _ hG hdist

end WaveTurbulence.ClassCount
