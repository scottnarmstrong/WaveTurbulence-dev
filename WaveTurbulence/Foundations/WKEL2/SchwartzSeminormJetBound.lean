/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.WKEL2.JetWordComponents
public import WaveTurbulence.Foundations.WKEL2.CoordinateMultilinearBound

/-!
# Weighted L² jets control the actual Schwartz topology

The Fréchet derivative norm and the Euclidean moment are expanded in the
standard coordinate basis. Point evaluation of every resulting moment and
derivative word is then bounded by the proved weighted Sobolev estimate.
-/

public section

noncomputable section

open scoped SchwartzMap

namespace WaveTurbulence.WKEL2

variable {d : ℕ}

/-- Euclidean moments and Fréchet derivatives are bounded by the exact finite coordinate sum. -/
theorem norm_pow_mul_iteratedFDeriv_le_word_sum (q n : ℕ) (f : 𝓢(Mom d, ℝ)) (k : Mom d) :
    ‖k‖ ^ q * ‖iteratedFDeriv ℝ n f k‖ ≤
      ∑ α : Fin q → Fin d, ∑ σ : Fin n → Fin d,
        |jetWordCLM (((List.ofFn α).map Sum.inl) ++ ((List.ofFn σ).map Sum.inr)) f k| := by
  have hm : ‖k‖ ^ q ≤ ∑ α : Fin q → Fin d, ∏ j : Fin q, |k (α j)| := by
    exact (pow_le_pow_left₀ (norm_nonneg _) (norm_le_sum_abs_coordinates k) q).trans_eq
      (Fintype.sum_pow (fun i : Fin d => |k i|) q)
  have hD := norm_multilinear_le_coordinate_sum (iteratedFDeriv ℝ n f k)
  apply (mul_le_mul hm hD (norm_nonneg _) (Finset.sum_nonneg fun _ _ =>
    Finset.prod_nonneg fun _ _ => abs_nonneg _)).trans_eq
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro α _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro σ _
  rw [jetWordCLM_append, jetWordCLM_moments, jetWordCLM_derivatives,
    abs_mul, Finset.abs_prod]

/-- Every Schwartz pointwise seminorm expression is controlled by a sufficiently high weighted jet. -/
theorem norm_pow_mul_iteratedFDeriv_le_weightedJet (s : ℝ) (hs : 0 ≤ s)
    (q n : ℕ) (f : 𝓢(Mom d, ℝ)) (k : Mom d) :
    ‖k‖ ^ q * ‖iteratedFDeriv ℝ n f k‖ ≤
      (2 : ℝ) ^ d * (d : ℝ) ^ q * (d : ℝ) ^ n * ‖weightedJetCLM s (q + n + d) f‖ := by
  apply (norm_pow_mul_iteratedFDeriv_le_word_sum q n f k).trans
  calc
    _ ≤ ∑ _α : Fin q → Fin d, ∑ _σ : Fin n → Fin d,
        (2 : ℝ) ^ d * ‖weightedJetCLM s (q + n + d) f‖ := by
      apply Finset.sum_le_sum
      intro α _
      apply Finset.sum_le_sum
      intro σ _
      simpa only [Real.norm_eq_abs] using
        norm_jetWord_apply_le s hs (q + n + d)
          (((List.ofFn α).map Sum.inl) ++ ((List.ofFn σ).map Sum.inr)) (by
            simp only [List.length_append, List.length_map, List.length_ofFn]
            omega) f k
    _ = _ := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fun, Fintype.card_fin,
        nsmul_eq_mul, Nat.cast_pow]
      ring

/-- The actual defining Schwartz seminorms are controlled by the completed weighted jet norm. -/
theorem schwartzSeminorm_le_weightedJet (s : ℝ) (hs : 0 ≤ s) (q n : ℕ) (f : 𝓢(Mom d, ℝ)) :
    SchwartzMap.seminorm ℝ q n f ≤
      (2 : ℝ) ^ d * (d : ℝ) ^ q * (d : ℝ) ^ n * ‖weightedJetCLM s (q + n + d) f‖ := by
  apply SchwartzMap.seminorm_le_bound ℝ q n f (by positivity)
  exact norm_pow_mul_iteratedFDeriv_le_weightedJet s hs q n f

end WaveTurbulence.WKEL2
