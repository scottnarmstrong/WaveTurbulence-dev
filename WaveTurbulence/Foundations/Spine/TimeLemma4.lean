/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.Spine.TimeLemma3
import Mathlib.Tactic
/-! Fubini in head/tail coordinates and the integral against a half-line cut. -/
@[expose] public section
open MeasureTheory Set Finset Function
namespace WaveTurbulence.Ladder

theorem integrable_finCons_iff' {n : ℕ} {F : (Fin (n + 1) → ℝ) → ℂ} :
    Integrable (fun z : ℝ × (Fin n → ℝ) => F (Fin.cons z.1 z.2)) ↔ Integrable F := by
  have h := (volume_preserving_piFinSuccAbove (fun _ : Fin (n + 1) => ℝ) 0).symm.integrable_comp_emb
    (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => ℝ) 0).symm.measurableEmbedding (g := F)
  simpa only [MeasurableEquiv.piFinSuccAbove_symm_apply, Fin.insertNthEquiv,
    Fin.insertNth_zero, Fin.zero_succAbove, cast_eq, Equiv.coe_fn_mk, Function.comp_def] using h

theorem integral_eq_prod_cons {n : ℕ} (F : (Fin (n + 1) → ℝ) → ℂ) :
    (∫ v, F v) = ∫ z : ℝ × (Fin n → ℝ), F (Fin.cons z.1 z.2) := by
  have h := (volume_preserving_piFinSuccAbove (fun _ : Fin (n + 1) => ℝ) 0).symm.integral_comp' F
  simp only [MeasurableEquiv.piFinSuccAbove_symm_apply, Fin.insertNthEquiv,
    Fin.insertNth_zero, Fin.zero_succAbove, cast_eq, Equiv.coe_fn_mk] at h
  exact h.symm

theorem integral_cons_outer {n : ℕ} {F : (Fin (n + 1) → ℝ) → ℂ} (hF : Integrable F) :
    (∫ v, F v) = ∫ s : ℝ, ∫ t : Fin n → ℝ, F (Fin.cons s t) := by
  rw [integral_eq_prod_cons]
  exact integral_prod _ (integrable_finCons_iff'.mpr hF)

theorem integral_cons_inner {n : ℕ} {F : (Fin (n + 1) → ℝ) → ℂ} (hF : Integrable F) :
    (∫ v, F v) = ∫ t : Fin n → ℝ, ∫ s : ℝ, F (Fin.cons s t) := by
  rw [integral_eq_prod_cons]
  exact integral_prod_symm _ (integrable_finCons_iff'.mpr hF)

theorem Fd_zero_of_notmem {n : ℕ} (par : Par n) (l u β : Fin n → ℝ) (t : Fin n → ℝ) (p : Fin n)
    (h : t p ∉ Ioc (l p) (u p)) : Fd par l u β t = 0 := by
  unfold Fd
  rw [Finset.prod_eq_zero (Finset.mem_univ p)]
  unfold Gf; simp [h]

/-- The integral over `s ∈ (l,u]`, `s < τ` of `e^{iβs}`. -/
theorem integral_cut {β : ℝ} (hβ : β ≠ 0) {l u : ℝ} (hlu : l ≤ u) (τ : ℝ) :
    ∫ s : ℝ, ((if s ∈ Ioc l u then (1 : ℂ) else 0) * (if s < τ then 1 else 0)) * ee β s =
      (ee β (max l (min u τ)) - ee β l) / ((β : ℂ) * Complex.I) := by
  have key : ∀ m : ℝ, l ≤ m → (Ioc l m : Set ℝ) =ᵐ[volume]
      ((Ioc l u) ∩ Iio τ : Set ℝ) → ∫ s : ℝ, ((if s ∈ Ioc l u then (1 : ℂ) else 0) *
        (if s < τ then 1 else 0)) * ee β s = (ee β m - ee β l) / ((β : ℂ) * Complex.I) := by
    intro m hlm hae
    rw [← integral_ee_Ioc hβ hlm]
    have e1 : ∀ s : ℝ, ((if s ∈ Ioc l u then (1 : ℂ) else 0) * (if s < τ then 1 else 0)) * ee β s =
        ((Ioc l u) ∩ Iio τ).indicator (fun s => ee β s) s := by
      intro s
      by_cases h1 : s ∈ Ioc l u <;> by_cases h2 : s < τ <;> simp [h1, h2]
    have e2 : ∀ s : ℝ, (if s ∈ Ioc l m then (1 : ℂ) else 0) * ee β s =
        (Ioc l m).indicator (fun s => ee β s) s := by
      intro s; by_cases h : s ∈ Ioc l m <;> simp [h]
    simp_rw [e1, e2]
    rw [integral_indicator (measurableSet_Ioc.inter measurableSet_Iio), integral_indicator measurableSet_Ioc]
    exact (setIntegral_congr_set hae.symm)
  rcases le_or_gt τ l with h1 | h1
  · have hm : max l (min u τ) = l := by
      apply max_eq_left; exact (min_le_right _ _).trans h1
    rw [hm]
    have := key l le_rfl (by
      rw [show ((Ioc l u) ∩ Iio τ : Set ℝ) = ∅ by
        ext s; simp only [mem_inter_iff, Set.mem_Ioc, Set.mem_Iio, mem_empty_iff_false, iff_false]
        rintro ⟨⟨h2, _⟩, h3⟩; linarith [h1, h3, h2]]
      simp)
    rw [this]
  · rcases le_or_gt τ u with h2 | h2
    · have hm : max l (min u τ) = τ := by
        rw [min_eq_right h2]; exact max_eq_right h1.le
      rw [hm]
      refine key τ h1.le ?_
      rw [show ((Ioc l u) ∩ Iio τ : Set ℝ) = Ioo l τ by
        ext s; simp only [mem_inter_iff, Set.mem_Ioc, Set.mem_Iio, Set.mem_Ioo]
        constructor
        · rintro ⟨⟨a, _⟩, c⟩; exact ⟨a, c⟩
        · rintro ⟨a, c⟩; exact ⟨⟨a, by linarith⟩, c⟩]
      exact Ioo_ae_eq_Ioc.symm
    · have hm : max l (min u τ) = u := by
        rw [min_eq_left h2.le]; exact max_eq_right hlu
      rw [hm]
      refine key u hlu ?_
      rw [show ((Ioc l u) ∩ Iio τ : Set ℝ) = Ioc l u by
        ext s; simp only [mem_inter_iff, Set.mem_Ioc, Set.mem_Iio]
        constructor
        · rintro ⟨a, _⟩; exact a
        · rintro ⟨a, b⟩; exact ⟨⟨a, b⟩, by linarith [h2]⟩]

end WaveTurbulence.Ladder
