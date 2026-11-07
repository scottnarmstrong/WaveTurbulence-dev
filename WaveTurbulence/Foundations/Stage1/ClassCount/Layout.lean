/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Stage1.ClassCount.UnitFamily
import Mathlib.Tactic

/-!
# CLASSCOUNT: the global layout of an atom set with units

Let `V` be a finite type, `F ⊆ V` the *fixed* atoms (unclassed atoms and unit representatives), labelled injectively by
`e : V → ℕ` with image `range n'`, and let `U 0, …, U (q-1)` be disjoint atom sets (the units) whose representatives
`rep i ∈ U i` are in `F`, with unit labellings `lab i` (injective on `U i` with image `range (W i + 1)`).  The *layout*
`pos` agrees with `e` on `F`, and sends `v ∈ U i` to `glob (lab i (rep i)) (e (rep i)) (n' + Σ_{j<i} W j) (lab i v)`.
`layout_inj`: `pos` is injective on `V` with image `range (n' + Σ W)`.
-/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.ClassCount
open Finset

theorem glob_rep (ρ p base : ℕ) : glob ρ p base ρ = p := by simp [glob]

theorem glob_ne (ρ p base j : ℕ) (h : j ≠ ρ) : glob ρ p base j = base + (if j < ρ then j else j - 1) := by
  simp [glob, h]

theorem glob_inj_ne {ρ p base j j' : ℕ} (hj : j ≠ ρ) (hj' : j' ≠ ρ)
    (h : glob ρ p base j = glob ρ p base j') : j = j' := by
  rw [glob_ne _ _ _ _ hj, glob_ne _ _ _ _ hj'] at h
  split_ifs at h <;> omega

theorem glob_range {ρ p base j W : ℕ} (hj : j < W + 1) (hne : j ≠ ρ) (hρ : ρ < W + 1) :
    base ≤ glob ρ p base j ∧ glob ρ p base j < base + W := by
  rw [glob_ne _ _ _ _ hne]; split_ifs <;> omega

theorem glob_surj {ρ base y W : ℕ} (hρ : ρ < W + 1) (hy : y < W) :
    ∃ j, j < W + 1 ∧ j ≠ ρ ∧ ∀ p, glob ρ p base j = base + y := by
  by_cases h : y < ρ
  · exact ⟨y, by omega, by omega, fun p => by rw [glob_ne _ _ _ _ (by omega)]; simp [h]⟩
  · exact ⟨y + 1, by omega, by omega, fun p => by rw [glob_ne _ _ _ _ (by omega)]; simp [show ¬ (y + 1 < ρ) by omega]⟩


theorem exists_block (W : ℕ → ℕ) : ∀ (q z : ℕ), z < ∑ j ∈ range q, W j →
    ∃ i, i < q ∧ ∑ j ∈ range i, W j ≤ z ∧ z < ∑ j ∈ range i, W j + W i
  | 0, z, h => by simp at h
  | q + 1, z, h => by
    rw [Finset.sum_range_succ] at h
    by_cases hz : z < ∑ j ∈ range q, W j
    · obtain ⟨i, hi, h1, h2⟩ := exists_block W q z hz
      exact ⟨i, by omega, h1, h2⟩
    · exact ⟨q, by omega, by omega, by omega⟩

theorem sum_range_mono_add (W : ℕ → ℕ) {i j : ℕ} (hij : i < j) :
    ∑ k ∈ range i, W k + W i ≤ ∑ k ∈ range j, W k := by
  rw [← Finset.sum_range_succ]
  exact Finset.sum_le_sum_of_subset (Finset.range_mono (by omega))

/-- **The global layout.** -/
theorem exists_layout {V : Type*} [Fintype V] [DecidableEq V] (q n' : ℕ) (Fx : Finset V) (e : V → ℕ)
    (heInj : Set.InjOn e Fx) (heImg : Fx.image e = range n')
    (U : ℕ → Finset V) (hUd : ∀ i j, i < q → j < q → i ≠ j → Disjoint (U i) (U j))
    (rep : ℕ → V) (hrep : ∀ i, i < q → rep i ∈ U i) (hrepF : ∀ i, i < q → rep i ∈ Fx)
    (hUF : ∀ i, i < q → ∀ v ∈ U i, v ∈ Fx → v = rep i)
    (hcov : ∀ v, v ∈ Fx ∨ ∃ i, i < q ∧ v ∈ U i)
    (W : ℕ → ℕ) (lab : ℕ → V → ℕ) (hlabInj : ∀ i, i < q → Set.InjOn (lab i) (U i))
    (hlabImg : ∀ i, i < q → (U i).image (lab i) = range (W i + 1)) :
    ∃ pos : V → ℕ, Set.InjOn pos Set.univ ∧ (Finset.univ : Finset V).image pos = range (n' + ∑ j ∈ range q, W j) ∧
      (∀ v ∈ Fx, pos v = e v) ∧
      ∀ i, i < q → ∀ v ∈ U i, pos v = glob (lab i (rep i)) (e (rep i)) (n' + ∑ j ∈ range i, W j) (lab i v) := by
  classical
  let base : ℕ → ℕ := fun i => n' + ∑ j ∈ range i, W j
  let pos : V → ℕ := fun v =>
    if h : ∃ i, i < q ∧ v ∈ U i then
      glob (lab (Classical.choose h) (rep (Classical.choose h))) (e (rep (Classical.choose h)))
        (base (Classical.choose h)) (lab (Classical.choose h) v)
    else e v
  have hunit : ∀ i, i < q → ∀ v ∈ U i, pos v = glob (lab i (rep i)) (e (rep i)) (base i) (lab i v) := by
    intro i hi v hv
    have h : ∃ i, i < q ∧ v ∈ U i := ⟨i, hi, hv⟩
    have hc := Classical.choose_spec h
    have heq : Classical.choose h = i := by
      by_contra hne
      exact Finset.disjoint_left.mp (hUd _ _ hc.1 hi hne) hc.2 hv
    simp only [pos, dif_pos h, heq]
  have hfix : ∀ v ∈ Fx, pos v = e v := by
    intro v hv
    by_cases h : ∃ i, i < q ∧ v ∈ U i
    · obtain ⟨i, hi, hvi⟩ := h
      have := hUF i hi v hvi hv
      subst this
      rw [hunit i hi _ hvi, glob_rep]
    · have : pos v = e v := by simp only [pos, dif_neg h]
      exact this
  have hnonrep : ∀ i, i < q → ∀ v ∈ U i, v ≠ rep i → lab i v ≠ lab i (rep i) := fun i hi v hv hne h =>
    hne (hlabInj i hi hv (hrep i hi) h)
  have hlt : ∀ i, i < q → ∀ v ∈ U i, lab i v < W i + 1 := by
    intro i hi v hv
    have : lab i v ∈ (U i).image (lab i) := Finset.mem_image_of_mem _ hv
    rw [hlabImg i hi, Finset.mem_range] at this; exact this
  -- values
  have hvalF : ∀ v ∈ Fx, pos v < n' := by
    intro v hv
    rw [hfix v hv]
    have : e v ∈ Fx.image e := Finset.mem_image_of_mem _ hv
    rw [heImg, Finset.mem_range] at this; exact this
  have hvalU : ∀ i, i < q → ∀ v ∈ U i, v ≠ rep i → base i ≤ pos v ∧ pos v < base i + W i := by
    intro i hi v hv hne
    rw [hunit i hi v hv]
    exact glob_range (hlt i hi v hv) (hnonrep i hi v hv hne) (hlt i hi _ (hrep i hi))
  refine ⟨pos, ?_, ?_, hfix, hunit⟩
  · intro v _ v' _ hv
    by_cases h1 : v ∈ Fx <;> by_cases h2 : v' ∈ Fx
    · rw [hfix v h1, hfix v' h2] at hv; exact heInj h1 h2 hv
    · obtain ⟨i, hi, hvi⟩ := (hcov v').resolve_left h2
      have hne : v' ≠ rep i := fun h => h2 (h ▸ hrepF i hi)
      have := hvalU i hi v' hvi hne
      have := hvalF v h1
      have : n' ≤ base i := by simp [base]
      omega
    · obtain ⟨i, hi, hvi⟩ := (hcov v).resolve_left h1
      have hne : v ≠ rep i := fun h => h1 (h ▸ hrepF i hi)
      have := hvalU i hi v hvi hne
      have := hvalF v' h2
      have : n' ≤ base i := by simp [base]
      omega
    · obtain ⟨i, hi, hvi⟩ := (hcov v).resolve_left h1
      obtain ⟨j, hj, hvj⟩ := (hcov v').resolve_left h2
      have hne : v ≠ rep i := fun h => h1 (h ▸ hrepF i hi)
      have hne' : v' ≠ rep j := fun h => h2 (h ▸ hrepF j hj)
      by_cases hij : i = j
      · subst hij
        rw [hunit i hi v hvi, hunit i hi v' hvj] at hv
        exact hlabInj i hi hvi hvj (glob_inj_ne (hnonrep i hi v hvi hne) (hnonrep i hi v' hvj hne') hv)
      · exfalso
        have a1 := hvalU i hi v hvi hne
        have a2 := hvalU j hj v' hvj hne'
        rcases lt_or_gt_of_ne hij with h | h
        · have := sum_range_mono_add W h
          have : base j ≥ base i + W i := by simp only [base]; omega
          omega
        · have := sum_range_mono_add W h
          have : base i ≥ base j + W j := by simp only [base]; omega
          omega
  · ext y
    simp only [Finset.mem_image, Finset.mem_univ, true_and, Finset.mem_range]
    constructor
    · rintro ⟨v, rfl⟩
      rcases hcov v with hv | ⟨i, hi, hvi⟩
      · have := hvalF v hv
        have : 0 ≤ ∑ j ∈ range q, W j := Nat.zero_le _
        omega
      · by_cases hne : v = rep i
        · subst hne
          have := hvalF _ (hrepF i hi)
          omega
        · have := hvalU i hi v hvi hne
          have h2 : ∑ j ∈ range i, W j + W i ≤ ∑ j ∈ range q, W j := by
            rcases Nat.lt_or_ge i q with h | h
            · by_cases hq : i + 1 = q
              · rw [← hq, Finset.sum_range_succ]
              · have := sum_range_mono_add W (show i < q by omega)
                exact this
            · omega
          simp only [base] at this
          omega
    · intro hy
      by_cases h : y < n'
      · have : y ∈ Fx.image e := by rw [heImg]; exact Finset.mem_range.mpr h
        obtain ⟨v, hv, hve⟩ := Finset.mem_image.mp this
        exact ⟨v, by rw [hfix v hv, hve]⟩
      · obtain ⟨i, hi, h1, h2⟩ := exists_block W q (y - n') (by omega)
        obtain ⟨j, hj, hjρ, hjg⟩ := glob_surj (ρ := lab i (rep i)) (base := base i) (y := y - n' - ∑ k ∈ range i, W k)
          (hlt i hi _ (hrep i hi)) (by omega)
        have : j ∈ (U i).image (lab i) := by rw [hlabImg i hi]; exact Finset.mem_range.mpr hj
        obtain ⟨v, hv, hvj⟩ := Finset.mem_image.mp this
        refine ⟨v, ?_⟩
        rw [hunit i hi v hv, hvj, hjg]
        simp only [base]; omega

end WaveTurbulence.ClassCount
