/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.WKEL2.JetNormalOrdering

/-!
# Bounds in the paper's moment-before-derivative convention
-/

public section

noncomputable section

open scoped SchwartzMap

namespace WaveTurbulence.WKEL2

variable {d : ℕ}

/-- The paper's canonical coordinate monomial followed by coordinate derivatives. -/
@[expose] def canonicalJetWordCLM (v w : List (Fin d)) : 𝓢(Mom d, ℝ) →L[ℝ] 𝓢(Mom d, ℝ) :=
  jetWordCLM (v.map Sum.inl ++ w.map Sum.inr)

/-- A common bound for exactly the canonical moments and derivatives of total order at most `m`. -/
@[expose] def IsCanonicalJetBound (s : ℝ) (m : ℕ) (f : 𝓢(Mom d, ℝ)) (B : ℝ) : Prop :=
  ∀ v w : List (Fin d), v.length + w.length ≤ m → ‖weightedToL2CLM s (canonicalJetWordCLM v w f)‖ ≤ B

private theorem norm_map_list_sum_le {E F α : Type*} [AddCommGroup E] [Module ℝ E] [TopologicalSpace E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] (L : E →L[ℝ] F) (G : α → E) (l : List α)
    {B : ℝ} (h : ∀ a ∈ l, ‖L (G a)‖ ≤ B) : ‖L ((l.map G).sum)‖ ≤ (l.length : ℝ) * B := by
  induction l with
  | nil => simp
  | cons a l ih =>
      simp only [List.map_cons, List.sum_cons, map_add, List.length_cons, Nat.cast_add, Nat.cast_one]
      calc
        _ ≤ ‖L (G a)‖ + ‖L ((l.map G).sum)‖ := norm_add_le _ _
        _ ≤ B + (l.length : ℝ) * B := add_le_add (h a (by simp)) (ih (fun x hx => h x (by simp [hx])))
        _ = _ := by ring

/-- Canonical bounds control a coordinate multiplier on the input, with only one order lost. -/
theorem isCanonicalJetBound_moment (s : ℝ) {m : ℕ} {f : 𝓢(Mom d, ℝ)} {B : ℝ}
    (hB : 0 ≤ B) (hf : IsCanonicalJetBound s (m + 1) f B) (i : Fin d) :
    IsCanonicalJetBound s m (jetLetterCLM (.inl i) f) (((m : ℝ) + 2) * B) := by
  intro v w hvw
  let L := (weightedToL2CLM s).comp (jetWordCLM (v.map Sum.inl))
  have hmain : ‖L (jetLetterCLM (.inl i) (jetWordCLM (w.map Sum.inr) f))‖ ≤ B := by
    have H := hf (v ++ [i]) w (by simp only [List.length_append, List.length_singleton]; omega)
    simpa only [canonicalJetWordCLM, List.map_append, List.map_singleton, List.append_assoc,
      jetWordCLM_append, jetWordCLM_cons, jetWordCLM_nil, L, ContinuousLinearMap.comp_apply] using H
  have hterms : ∀ u ∈ momentDerivativeTerms i w, ‖L (jetWordCLM (u.map Sum.inr) f)‖ ≤ B := by
    intro u hu
    have Hlen := length_mem_momentDerivativeTerms i w u hu
    have H := hf v u (by omega)
    simpa only [canonicalJetWordCLM, jetWordCLM_append, L, ContinuousLinearMap.comp_apply] using H
  rw [canonicalJetWordCLM, jetWordCLM_append]
  change ‖L (jetWordCLM (w.map Sum.inr) (jetLetterCLM (.inl i) f))‖ ≤ _
  rw [jetWordCLM_derivatives_moment, map_add]
  calc
    _ ≤ ‖L (jetLetterCLM (.inl i) (jetWordCLM (w.map Sum.inr) f))‖ +
        ‖L (((momentDerivativeTerms i w).map (fun u => jetWordCLM (u.map Sum.inr) f)).sum)‖ := norm_add_le _ _
    _ ≤ B + ((momentDerivativeTerms i w).length : ℝ) * B :=
      add_le_add hmain (norm_map_list_sum_le L _ _ hterms)
    _ ≤ ((m : ℝ) + 2) * B := by
      have hlen : ((momentDerivativeTerms i w).length : ℝ) ≤ m := by
        exact_mod_cast (length_momentDerivativeTerms_le i w).trans (by omega : w.length ≤ m)
      have H := mul_le_mul_of_nonneg_right hlen hB
      linarith only [H, hB]

/-- Canonical bounds control one more coordinate derivative on the input. -/
theorem isCanonicalJetBound_derivative (s : ℝ) {m : ℕ} {f : 𝓢(Mom d, ℝ)} {B : ℝ}
    (hB : 0 ≤ B) (hf : IsCanonicalJetBound s (m + 1) f B) (i : Fin d) :
    IsCanonicalJetBound s m (jetLetterCLM (.inr i) f) (((m : ℝ) + 2) * B) := by
  intro v w hvw
  have H := hf v (w ++ [i]) (by simp only [List.length_append, List.length_singleton]; omega)
  have heq : canonicalJetWordCLM v w (jetLetterCLM (.inr i) f) = canonicalJetWordCLM v (w ++ [i]) f := by
    simp only [canonicalJetWordCLM, List.map_append, List.map_singleton,
      ← List.append_assoc, jetWordCLM_append, jetWordCLM_cons, jetWordCLM_nil]
  rw [heq]
  apply H.trans
  have hm : (1 : ℝ) ≤ (m : ℝ) + 2 := by have H := Nat.cast_nonneg (α := ℝ) m; linarith only [H]
  simpa only [one_mul] using mul_le_mul_of_nonneg_right hm hB

/-- Both kinds of elementary letters preserve canonical bounds at the preceding order. -/
theorem isCanonicalJetBound_letter (s : ℝ) {m : ℕ} {f : 𝓢(Mom d, ℝ)} {B : ℝ}
    (hB : 0 ≤ B) (hf : IsCanonicalJetBound s (m + 1) f B) (a : JetLetter d) :
    IsCanonicalJetBound s m (jetLetterCLM a f) (((m : ℝ) + 2) * B) := by
  cases a with
  | inl i => exact isCanonicalJetBound_moment s hB hf i
  | inr i => exact isCanonicalJetBound_derivative s hB hf i

end WaveTurbulence.WKEL2
