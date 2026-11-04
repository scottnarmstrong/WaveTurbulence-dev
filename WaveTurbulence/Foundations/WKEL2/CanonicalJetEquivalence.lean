/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.WKEL2.CanonicalJetBound

/-!
# Equivalence with the paper's canonical finite weighted moment and derivative norm

The comparison is at the same total order, with a harmless factorial
constant depending only on that order. The canonical convention consists
of all coordinate moments followed by all coordinate derivatives.
-/

public section

noncomputable section

open scoped SchwartzMap

namespace WaveTurbulence.WKEL2

variable {d : ℕ}

/-- Normal ordering bounds every differential and moment word of the same total order. -/
theorem norm_jetWord_le_of_canonical_bound (s : ℝ) : ∀ (m : ℕ) (f : 𝓢(Mom d, ℝ)) (B : ℝ),
    0 ≤ B → IsCanonicalJetBound s m f B → ∀ w : List (JetLetter d), w.length ≤ m →
      ‖weightedToL2CLM s (jetWordCLM w f)‖ ≤ ((m + 1).factorial : ℝ) * B := by
  intro m
  induction m with
  | zero =>
      intro f B hB hf w hw
      have hw₀ : w = [] := List.length_eq_zero_iff.1 (Nat.eq_zero_of_le_zero hw)
      subst w
      simpa only [canonicalJetWordCLM, List.map_nil, List.nil_append, jetWordCLM_nil,
        Nat.zero_add, Nat.factorial_one, Nat.cast_one, one_mul] using hf [] [] (by simp)
  | succ m ih =>
      intro f B hB hf w hw
      induction w using List.reverseRecOn with
      | nil =>
          have H := hf [] [] (by simp)
          change ‖weightedToL2CLM s f‖ ≤ _
          apply H.trans
          have hfac : (1 : ℝ) ≤ ((m + 1 + 1).factorial : ℝ) := by
            exact_mod_cast Nat.factorial_pos (m + 1 + 1)
          simpa only [one_mul] using mul_le_mul_of_nonneg_right hfac hB
      | append_singleton w a _ =>
          have hlen : w.length ≤ m := by
            have H : w.length + 1 ≤ m + 1 := by simpa only [List.length_append, List.length_singleton] using hw
            omega
          have H := ih (jetLetterCLM a f) (((m : ℝ) + 2) * B) (by positivity)
            (isCanonicalJetBound_letter s hB hf a) w hlen
          rw [jetWordCLM_append, jetWordCLM_cons, jetWordCLM_nil]
          apply H.trans_eq
          rw [Nat.factorial_succ (m + 1), Nat.cast_mul]
          simp only [Nat.cast_add, Nat.cast_one]
          ring

/-- A common bound on canonical order-`m` moments and derivatives bounds the whole ordered jet. -/
theorem norm_weightedJet_le_of_canonical_bound (s : ℝ) (m : ℕ) (f : 𝓢(Mom d, ℝ))
    {B : ℝ} (hB : 0 ≤ B) (hf : IsCanonicalJetBound s m f B) :
    ‖weightedJetCLM s m f‖ ≤ ((m + 1).factorial : ℝ) * B := by
  apply (pi_norm_le_iff_of_nonneg (by positivity)).2
  intro i
  exact norm_jetWord_le_of_canonical_bound s m f B hB hf (List.ofFn i.2)
    (by simp only [List.length_ofFn]; have H := i.1.isLt; omega)

/-- Conversely the ordered jet norm bounds every canonical moment and derivative at the same order. -/
theorem isCanonicalJetBound_weightedJet (s : ℝ) (m : ℕ) (f : 𝓢(Mom d, ℝ)) :
    IsCanonicalJetBound s m f ‖weightedJetCLM s m f‖ := by
  intro v w hvw
  rw [norm_weightedToL2CLM]
  exact weightedL2Norm_jetWord_le s m (v.map Sum.inl ++ w.map Sum.inr)
    (by simpa only [List.length_append, List.length_map] using hvw) f

end WaveTurbulence.WKEL2
