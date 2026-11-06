/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Spine.PL2330Draft.Triangle
public import Mathlib.Analysis.Calculus.ContDiff.Bounds
public import Mathlib.Data.Nat.Choose.Sum

/-!
# Momentum multipliers with the Leibniz rule (PL23-30D)

For a smooth multiplier `c(k)` independent of time, `(cF)^(ξ,k) = c(k) F̂(ξ,k)` and the Leibniz rule for the
coordinate words gives `𝔛^{θ,Λ,a+b}(cF) ≤ (2d)^Λ ‖c‖_{𝔖^{Λ,a}} 𝔛^{θ,Λ,b}(F)`.

* `dsup`: the weighted supremum of the operator norm of the `i`-th Fréchet derivative;
* `momentumSupNorm_le_dsup`, `dsup_le_sum_words`, `dsup_mul_le`: comparison with the coordinate words and
  Leibniz;
* `mixedFourierNorm_mul_momentum_le`, `restr_mul_momentum_le`.
-/

@[expose] public section

open MeasureTheory Set Filter Finset
open scoped ENNReal ContDiff

namespace WaveTurbulence.PL2330

open WaveTurbulence.Fourier WaveTurbulence.Regref

variable {r d : ℕ}

/-- `sup_k ⟨k⟩^{Λ₂} ‖D^i f(k)‖`, with the Fréchet operator norm. -/
noncomputable def dsup (Λ₂ i : ℕ) (f : Mom d → ℂ) : ℝ≥0∞ :=
  ⨆ k, ENNReal.ofReal (momentumBracket k ^ Λ₂) * ‖iteratedFDeriv ℝ i f k‖ₑ

theorem norm_word_le_frechet {n : ℕ} (ρ : Fin n → Fin d) (f : Mom d → ℂ) (k : Mom d) :
    ‖momentumDerivative ρ f k‖ ≤ ‖iteratedFDeriv ℝ n f k‖ := by
  unfold momentumDerivative
  have h := (iteratedFDeriv ℝ n f k).le_opNorm (fun i => EuclideanSpace.single (ρ i) (1 : ℝ))
  simpa using h

theorem enorm_word_le_enorm_frechet {n : ℕ} (ρ : Fin n → Fin d) (f : Mom d → ℂ) (k : Mom d) :
    ‖momentumDerivative ρ f k‖ₑ ≤ ‖iteratedFDeriv ℝ n f k‖ₑ := by
  rw [← ofReal_norm, ← ofReal_norm]
  exact ENNReal.ofReal_le_ofReal (norm_word_le_frechet ρ f k)

theorem momentumSupNorm_le_dsup (Λ₂ : ℕ) {n : ℕ} (ρ : Fin n → Fin d) (f : Mom d → ℂ) :
    momentumSupNorm Λ₂ (momentumDerivative ρ f) ≤ dsup Λ₂ n f := by
  unfold momentumSupNorm dsup
  exact iSup_mono fun k => mul_le_mul_right (enorm_word_le_enorm_frechet ρ f k) _

theorem dsup_le_sum_words (Λ₂ n : ℕ) (f : Mom d → ℂ) :
    dsup Λ₂ n f ≤ ∑ ρ : Fin n → Fin d, momentumSupNorm Λ₂ (momentumDerivative ρ f) := by
  unfold dsup
  refine iSup_le fun k => ?_
  have h := norm_le_sum_coordWords (iteratedFDeriv ℝ n f k)
  have h1 : ‖iteratedFDeriv ℝ n f k‖ₑ ≤ ∑ ρ : Fin n → Fin d, ‖momentumDerivative ρ f k‖ₑ := by
    calc ‖iteratedFDeriv ℝ n f k‖ₑ = ENNReal.ofReal ‖iteratedFDeriv ℝ n f k‖ := (ofReal_norm _).symm
      _ ≤ ENNReal.ofReal (∑ ρ : Fin n → Fin d, ‖momentumDerivative ρ f k‖) :=
          ENNReal.ofReal_le_ofReal (by simpa [momentumDerivative] using h)
      _ = ∑ ρ : Fin n → Fin d, ‖momentumDerivative ρ f k‖ₑ := by
          rw [ENNReal.ofReal_sum_of_nonneg (fun _ _ => norm_nonneg _)]
          simp only [ofReal_norm]
  calc ENNReal.ofReal (momentumBracket k ^ Λ₂) * ‖iteratedFDeriv ℝ n f k‖ₑ
      ≤ ENNReal.ofReal (momentumBracket k ^ Λ₂) * ∑ ρ : Fin n → Fin d, ‖momentumDerivative ρ f k‖ₑ :=
        mul_le_mul_right h1 _
    _ = ∑ ρ : Fin n → Fin d, ENNReal.ofReal (momentumBracket k ^ Λ₂) * ‖momentumDerivative ρ f k‖ₑ :=
        Finset.mul_sum _ _ _
    _ ≤ _ := Finset.sum_le_sum fun ρ _ =>
        le_iSup (fun k => ENNReal.ofReal (momentumBracket k ^ Λ₂) * ‖momentumDerivative ρ f k‖ₑ) k

theorem enorm_iteratedFDeriv_mul_le {f g : Mom d → ℂ} {Λ : ℕ} (hf : ContDiff ℝ Λ f) (hg : ContDiff ℝ Λ g)
    (x : Mom d) {n : ℕ} (hn : n ≤ Λ) :
    ‖iteratedFDeriv ℝ n (fun y => f y * g y) x‖ₑ ≤ ∑ i ∈ range (n + 1),
      (n.choose i : ℝ≥0∞) * ‖iteratedFDeriv ℝ i f x‖ₑ * ‖iteratedFDeriv ℝ (n - i) g x‖ₑ := by
  have h := norm_iteratedFDeriv_mul_le hf hg x (by exact_mod_cast hn)
  rw [← ofReal_norm]
  refine (ENNReal.ofReal_le_ofReal h).trans_eq ?_
  rw [ENNReal.ofReal_sum_of_nonneg (fun _ _ => by positivity)]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_mul (by positivity), ofReal_norm, ofReal_norm]
  simp

/-- **The Leibniz rule for `dsup`.** -/
theorem dsup_mul_le {f g : Mom d → ℂ} {Λ : ℕ} (hf : ContDiff ℝ Λ f) (hg : ContDiff ℝ Λ g) (a b : ℕ)
    {n : ℕ} (hn : n ≤ Λ) :
    dsup (a + b) n (fun y => f y * g y) ≤
      ∑ i ∈ range (n + 1), (n.choose i : ℝ≥0∞) * dsup a i f * dsup b (n - i) g := by
  unfold dsup
  refine iSup_le fun k => ?_
  have hbr : ENNReal.ofReal (momentumBracket k ^ (a + b)) =
      ENNReal.ofReal (momentumBracket k ^ a) * ENNReal.ofReal (momentumBracket k ^ b) := by
    rw [pow_add, ENNReal.ofReal_mul (pow_nonneg (momentumBracket_nonneg k) _)]
  calc ENNReal.ofReal (momentumBracket k ^ (a + b)) * ‖iteratedFDeriv ℝ n (fun y => f y * g y) k‖ₑ
      ≤ ENNReal.ofReal (momentumBracket k ^ (a + b)) * ∑ i ∈ range (n + 1),
        (n.choose i : ℝ≥0∞) * ‖iteratedFDeriv ℝ i f k‖ₑ * ‖iteratedFDeriv ℝ (n - i) g k‖ₑ :=
        mul_le_mul_right (enorm_iteratedFDeriv_mul_le hf hg k hn) _
    _ = ∑ i ∈ range (n + 1), (n.choose i : ℝ≥0∞) *
          (ENNReal.ofReal (momentumBracket k ^ a) * ‖iteratedFDeriv ℝ i f k‖ₑ) *
          (ENNReal.ofReal (momentumBracket k ^ b) * ‖iteratedFDeriv ℝ (n - i) g k‖ₑ) := by
        rw [Finset.mul_sum, hbr]
        refine Finset.sum_congr rfl fun i _ => ?_
        ring
    _ ≤ _ := Finset.sum_le_sum fun i _ => by
        gcongr
        · exact le_iSup (fun k => ENNReal.ofReal (momentumBracket k ^ a) * ‖iteratedFDeriv ℝ i f k‖ₑ) k
        · exact le_iSup (fun k => ENNReal.ofReal (momentumBracket k ^ b) * ‖iteratedFDeriv ℝ (n - i) g k‖ₑ) k

/-- The `i`-th derivative sup of a smooth `c` is bounded by the `𝔖` norm (`i ≤ Λ`). -/
theorem dsup_le_spatialNorm {Λ a : ℕ} {c : Mom d → ℂ} (hc : ContDiff ℝ Λ c) {i : ℕ} (hi : i ≤ Λ) :
    dsup a i c ≤ (d : ℝ≥0∞) ^ i * spatialNorm Λ a c := by
  have hS : ∀ ρ : Fin i → Fin d, momentumSupNorm a (momentumDerivative ρ c) ≤ spatialNorm Λ a c := by
    intro ρ
    unfold spatialNorm
    simp only [hc, or_true, ↓reduceIte]
    exact le_iSup₂_of_le i hi (le_iSup (fun ρ : Fin i → Fin d => momentumSupNorm a (momentumDerivative ρ c)) ρ)
  refine (dsup_le_sum_words a i c).trans ?_
  calc ∑ ρ : Fin i → Fin d, momentumSupNorm a (momentumDerivative ρ c)
      ≤ ∑ _ρ : Fin i → Fin d, spatialNorm Λ a c := Finset.sum_le_sum fun ρ _ => hS ρ
    _ = (d : ℝ≥0∞) ^ i * spatialNorm Λ a c := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fun, Fintype.card_fin, Fintype.card_fin,
          nsmul_eq_mul]
        simp

end WaveTurbulence.PL2330
