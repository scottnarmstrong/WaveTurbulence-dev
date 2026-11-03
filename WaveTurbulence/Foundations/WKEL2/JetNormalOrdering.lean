/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.WKEL2.JetCommutator

/-!
# Normal ordering of coordinate derivative and moment words

Every occurrence of a differentiated coordinate contributes separately;
the list of terms retains all Leibniz multiplicities.
-/

public section

noncomputable section

open scoped SchwartzMap

namespace WaveTurbulence.WKEL2

variable {d : ℕ}

/-- Derivative words created by differentiating a single coordinate multiplier. -/
@[expose] def momentDerivativeTerms (i : Fin d) : List (Fin d) → List (List (Fin d))
  | [] => []
  | a :: w => (if a = i then [w] else []) ++ (momentDerivativeTerms i w).map (List.cons a)

/-- At most one term arises from each derivative in the word. -/
theorem length_momentDerivativeTerms_le (i : Fin d) : ∀ w : List (Fin d),
    (momentDerivativeTerms i w).length ≤ w.length
  | [] => by simp [momentDerivativeTerms]
  | a :: w => by
      have H := length_momentDerivativeTerms_le i w
      by_cases h : a = i <;> simp only [momentDerivativeTerms, h, ite_true, ite_false,
        List.length_append, List.length_map, List.length_nil, List.length_cons] <;> omega

/-- Every correction term has one fewer derivative. -/
theorem length_mem_momentDerivativeTerms (i : Fin d) : ∀ (w v : List (Fin d)),
    v ∈ momentDerivativeTerms i w → v.length + 1 ≤ w.length
  | [], v, h => by simp only [momentDerivativeTerms, List.not_mem_nil] at h
  | a :: w, v, h => by
      simp only [momentDerivativeTerms, List.mem_append, List.mem_map] at h
      rcases h with h | ⟨u, hu, rfl⟩
      · by_cases ha : a = i
        · simp only [ha, ite_true, List.mem_singleton] at h
          subst v
          simp
        · simp only [ha, ite_false, List.not_mem_nil] at h
      · have H := length_mem_momentDerivativeTerms i w u hu
        simp only [List.length_cons]
        omega

/-- Exact Leibniz expansion of a derivative word through one moment. -/
theorem jetWordCLM_derivatives_moment (i : Fin d) : ∀ (w : List (Fin d)) (f : 𝓢(Mom d, ℝ)),
    jetWordCLM (w.map Sum.inr) (jetLetterCLM (.inl i) f) =
      jetLetterCLM (.inl i) (jetWordCLM (w.map Sum.inr) f) +
        ((momentDerivativeTerms i w).map (fun v => jetWordCLM (v.map Sum.inr) f)).sum
  | [], f => by simp only [List.map_nil, jetWordCLM_nil, momentDerivativeTerms, List.sum_nil, add_zero]
  | a :: w, f => by
      rw [List.map_cons, jetWordCLM_cons, jetWordCLM_derivatives_moment, map_add,
        jetLetterCLM_deriv_moment]
      simp only [momentDerivativeTerms, List.map_append, List.sum_append, List.map_map,
        map_list_sum, List.map_cons, jetWordCLM_cons, Function.comp_def]
      by_cases ha : a = i
      · simp only [ha, ite_true, one_smul, List.map_singleton, List.sum_singleton]
        abel
      · simp only [ha, ite_false, zero_smul, List.map_nil, List.sum_nil, add_zero, zero_add]

end WaveTurbulence.WKEL2
