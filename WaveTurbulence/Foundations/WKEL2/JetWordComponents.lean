/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.WKEL2.SchwartzPointEvaluation

/-!
# Moment and derivative components of actual Schwartz jet words
-/

public section

noncomputable section

open scoped SchwartzMap LineDeriv

namespace WaveTurbulence.WKEL2

variable {d : ℕ}

/-- Concatenating coordinate words composes the actual Schwartz operators. -/
theorem jetWordCLM_append (v w : List (JetLetter d)) (f : 𝓢(Mom d, ℝ)) :
    jetWordCLM (v ++ w) f = jetWordCLM v (jetWordCLM w f) := by
  induction v with
  | nil => rfl
  | cons a v ih =>
      simp only [List.cons_append, jetWordCLM, ContinuousLinearMap.comp_apply, ih]

/-- A finite directional word agrees with Mathlib's iterated line derivative. -/
theorem derivativeWordCLM_ofFn : ∀ {n : ℕ} (V : Fin n → Mom d) (f : 𝓢(Mom d, ℝ)),
    derivativeWordCLM (List.ofFn V) f = ∂^{V} f
  | 0, V, f => by simp only [List.ofFn_zero, derivativeWordCLM,
      ContinuousLinearMap.id_apply, LineDeriv.iteratedLineDerivOp_fin_zero]
  | n + 1, V, f => by
      rw [List.ofFn_succ, ← Fin.tail_def, derivativeWordCLM, ContinuousLinearMap.comp_apply,
        derivativeWordCLM_ofFn, LineDeriv.lineDerivOpCLM_apply,
        LineDeriv.iteratedLineDerivOp_succ_left]

/-- Coordinate derivative words are the exact components of the Fréchet derivative tensor. -/
theorem jetWordCLM_derivatives {n : ℕ} (σ : Fin n → Fin d) (f : 𝓢(Mom d, ℝ)) (k : Mom d) :
    jetWordCLM ((List.ofFn σ).map Sum.inr) f k =
      iteratedFDeriv ℝ n f k (fun j => EuclideanSpace.single (σ j) (1 : ℝ)) := by
  rw [← derivativeWordCLM_basis, List.map_ofFn, derivativeWordCLM_ofFn,
    SchwartzMap.iteratedLineDerivOp_eq_iteratedFDeriv]
  rfl

/-- Coordinate moment words are the exact monomial multipliers. -/
theorem jetWordCLM_moments : ∀ {n : ℕ} (σ : Fin n → Fin d) (f : 𝓢(Mom d, ℝ)) (k : Mom d),
    jetWordCLM ((List.ofFn σ).map Sum.inl) f k = (∏ j : Fin n, k (σ j)) * f k
  | 0, σ, f, k => by simp only [List.ofFn_zero, List.map_nil, jetWordCLM_nil,
      Fin.prod_univ_zero, one_mul]
  | n + 1, σ, f, k => by
      rw [List.ofFn_succ, ← Fin.tail_def, List.map_cons, jetWordCLM_cons,
        jetLetterCLM, coordinateWeightCLM_apply, jetWordCLM_moments, Fin.prod_univ_succ]
      simp only [Fin.tail_def, mul_assoc]

/-- Taking a finite jet after a word uses only correspondingly higher coordinates of the input. -/
theorem norm_weightedJet_jetWord_le (s : ℝ) (r m : ℕ) (w : List (JetLetter d))
    (hw : r + w.length ≤ m) (f : 𝓢(Mom d, ℝ)) :
    ‖weightedJetCLM s r (jetWordCLM w f)‖ ≤ ‖weightedJetCLM s m f‖ := by
  apply (pi_norm_le_iff_of_nonneg (norm_nonneg _)).2
  intro i
  rw [norm_weightedJetCLM_coordinate, ← jetWordCLM_append]
  apply weightedL2Norm_jetWord_le
  simp only [List.length_append, List.length_ofFn]
  have H := i.1.isLt
  omega

/-- Every differential and moment word has uniform pointwise control by a higher weighted jet. -/
theorem norm_jetWord_apply_le (s : ℝ) (hs : 0 ≤ s) (m : ℕ) (w : List (JetLetter d))
    (hw : d + w.length ≤ m) (f : 𝓢(Mom d, ℝ)) (k : Mom d) :
    ‖jetWordCLM w f k‖ ≤ (2 : ℝ) ^ d * ‖weightedJetCLM s m f‖ := by
  exact (norm_apply_le_weightedJet s hs (jetWordCLM w f) k).trans
    (mul_le_mul_of_nonneg_left (norm_weightedJet_jetWord_le s d m w hw f) (by positivity))

end WaveTurbulence.WKEL2
