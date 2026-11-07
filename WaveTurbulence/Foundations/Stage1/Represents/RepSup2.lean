/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Stage1.Represents.RepSup1
public import WaveTurbulence.Foundations.Spine.XNormPointwise
import Mathlib.Tactic

/-!
# S2 REPRESENTS: `XNormRestr ≤ X` gives a superposition of mass `≤ C X`
-/

@[expose] public section
set_option autoImplicit false
open WaveTurbulence.Induct
namespace WaveTurbulence.Represents
open WaveTurbulence WaveTurbulence.RepAnalytic WaveTurbulence.VineEstS3 WaveTurbulence.VineEstS3.FS
open WaveTurbulence.LGSpine
open scoped ENNReal

variable {d r : ℕ}

theorem f_eq_zero_of_xnorm_zero {θ : ℝ} (hθ : 0 ≤ θ) (Λ₁ Λ₂ : ℕ) {B : Set (Fin r → ℝ)}
    (hB : B ⊆ closure (interior B)) {f : (Fin r → ℝ) → Mom d → ℂ}
    (hc : ∀ k, Continuous fun t => f t k) (h : XNormRestr θ Λ₁ Λ₂ B Set.univ f ≤ 0) :
    ∀ t ∈ B, ∀ k, f t k = 0 := by
  intro t ht k
  have := enorm_le_XNormRestr_of_continuous hθ Λ₁ Λ₂ B Set.univ f t k (hB ht) (Set.mem_univ _) (hc k)
  have h0 : ‖f t k‖ₑ ≤ 0 := this.trans h
  simpa using h0

/-- Centred superposition of a function with `XNormRestr ≤ X` (`Λ₂ > d`). -/
theorem exists_cenSup (hd : 1 ≤ d) {θ : ℝ} (hθ : 0 ≤ θ) {Λ₁ Λ₂ : ℕ} (hΛ₁ : Λ₁ ≠ 0) (hΛ₂ : d < Λ₂) :
    ∃ C : ℝ≥0∞, C ≠ ⊤ ∧ ∀ (q : Fin r → ℝ) (B : Set (Fin r → ℝ)) (f : (Fin r → ℝ) → Mom d → ℂ)
      (X : ℝ≥0∞), X ≠ ⊤ → B ⊆ cell q → B ⊆ closure (interior B) →
      (∀ k, Continuous fun t => f t k) → XNormRestr θ Λ₁ Λ₂ B Set.univ f ≤ X →
      CenSup Λ₁ B f (C * X) := by
  obtain ⟨C, hC, h⟩ := fourier_centre_superposition (r := r) (d := d) hd hθ hΛ₁ hΛ₂
  refine ⟨2 * C, ENNReal.mul_ne_top (by simp) hC, fun q B f X hX hBc hBi hfc hn => ?_⟩
  by_cases hX0 : X = 0
  · subst hX0
    exact CenSup.zero _ _ _ (f_eq_zero_of_xnorm_zero hθ Λ₁ Λ₂ hBi hfc hn) _
  · have hlt : XNormRestr θ Λ₁ Λ₂ B Set.univ f < 2 * X := by
      calc _ ≤ X := hn
        _ < X + X := ENNReal.lt_add_right hX hX0
        _ = 2 * X := (two_mul X).symm
    obtain ⟨w, a, h1, h2, h3, h4, h5, h6⟩ :=
      h q B Set.univ f (2 * X) (ENNReal.mul_ne_top (by simp) hX) hBc hBi (fun k _ => hfc k) hlt
    refine ⟨(Fin r → ℤ) × (Fin d → ℤ), inferInstance, w, Prod.fst, Prod.snd, a, h1, h5, h2, h3,
      fun t ht k => h4 t ht k (Set.mem_univ _), ?_⟩
    refine le_trans (ENNReal.tsum_le_tsum fun p => ?_) (h6.trans (le_of_eq (by ring)))
    exact le_mul_of_one_le_left bot_le (RepAnalytic.one_le_maxBracketPow hθ _)

/-- Superposition (no centres) of a function with `XNormRestr ≤ X`. -/
theorem exists_sup {θ : ℝ} (hθ : 0 ≤ θ) {Λ₁ : ℕ} (hΛ₁ : Λ₁ ≠ 0) :
    ∃ C : ℝ≥0∞, C ≠ ⊤ ∧ ∀ (q : Fin r → ℝ) (B : Set (Fin r → ℝ)) (f : (Fin r → ℝ) → Mom d → ℂ)
      (X : ℝ≥0∞), X ≠ ⊤ → B ⊆ cell q → B ⊆ closure (interior B) →
      (∀ k, Continuous fun t => f t k) → XNormRestr θ Λ₁ 0 B Set.univ f ≤ X →
      Sup Λ₁ B f (C * X) := by
  obtain ⟨C, hC, h⟩ := fourier_superposition (r := r) (d := d) hθ hΛ₁ (Λ₂ := 0)
  refine ⟨2 * C, ENNReal.mul_ne_top (by simp) hC, fun q B f X hX hBc hBi hfc hn => ?_⟩
  by_cases hX0 : X = 0
  · subst hX0
    exact Sup.zero _ _ _ (f_eq_zero_of_xnorm_zero hθ Λ₁ 0 hBi hfc hn) _
  · have hlt : XNormRestr θ Λ₁ 0 B Set.univ f < 2 * X := by
      calc _ ≤ X := hn
        _ < X + X := ENNReal.lt_add_right hX hX0
        _ = 2 * X := (two_mul X).symm
    obtain ⟨w, a, h1, h2, h3, h4, h5⟩ :=
      h q B Set.univ f (2 * X) (ENNReal.mul_ne_top (by simp) hX) hBc hBi (fun k _ => hfc k) hlt
    refine ⟨Fin r → ℤ, inferInstance, w, id, a, h1, h4, h2, fun t ht k => h3 t ht k (Set.mem_univ _), ?_⟩
    · refine le_trans (ENNReal.tsum_le_tsum fun p => ?_) (h5.trans (le_of_eq (by ring)))
      exact le_mul_of_one_le_left bot_le (RepAnalytic.one_le_maxBracketPow hθ _)

end WaveTurbulence.Represents
