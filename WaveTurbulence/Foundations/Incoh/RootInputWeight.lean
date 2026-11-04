/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Incoh.SpatialCenterDecay

/-! # Transfer of the source root weight to an actual leaf input

TARGET Proposition 5.1 Step (1). Only the finite integer row expressing
the root momentum in terms of leaf momenta is used.
-/

public section
noncomputable section

namespace WaveTurbulence.Incoh

/-- The source's integer root relation transfers every root weight to a single leaf weight,
with a polynomial cost in the number of inputs. -/
theorem momentumBracket_pow_le_input_sum {d m : ℕ} (hm : 0 < m)
    (σ : Fin m → ℤ) (hσ : ∀ a, |(σ a : ℝ)| ≤ 1)
    (x : Fin m → Mom d) (k : Mom d) (hk : k = ∑ a, (σ a : ℝ) • x a) (M : ℕ) :
    Fourier.momentumBracket k ^ M ≤ ((m : ℝ) + 1) ^ M *
      ∑ a, Fourier.momentumBracket (x a) ^ M := by
  classical
  obtain ⟨a, _, hmax⟩ := Finset.exists_max_image Finset.univ
    (fun a : Fin m => Fourier.momentumBracket (x a)) ⟨⟨0, hm⟩, Finset.mem_univ _⟩
  have hmax' (b : Fin m) : Fourier.momentumBracket (x b) ≤ Fourier.momentumBracket (x a) :=
    hmax b (Finset.mem_univ _)
  have hx (b : Fin m) : ‖x b‖ ≤ Fourier.momentumBracket (x b) := by
    unfold Fourier.momentumBracket
    exact (Real.le_sqrt (norm_nonneg _) (by positivity)).mpr (by linarith)
  have hn : ‖k‖ ≤ (m : ℝ) * Fourier.momentumBracket (x a) := by
    calc
      _ ≤ ∑ b, ‖(σ b : ℝ) • x b‖ := by rw [hk]; exact norm_sum_le _ _
      _ ≤ ∑ _b : Fin m, Fourier.momentumBracket (x a) := by
        apply Finset.sum_le_sum
        intro b _
        rw [norm_smul, Real.norm_eq_abs]
        exact (mul_le_mul_of_nonneg_right (hσ b) (norm_nonneg _)).trans
          (by rw [one_mul]; exact (hx b).trans (hmax' b))
      _ = _ := by simp
  have hb : Fourier.momentumBracket k ≤ 1 + ‖k‖ := by
    unfold Fourier.momentumBracket
    apply (Real.sqrt_le_left (by positivity)).mpr
    nlinarith [norm_nonneg k]
  have ha := one_le_momentumBracket (x a)
  have hw : Fourier.momentumBracket k ≤ ((m : ℝ) + 1) * Fourier.momentumBracket (x a) := by
    nlinarith only [hb, hn, ha]
  calc
    _ ≤ (((m : ℝ) + 1) * Fourier.momentumBracket (x a)) ^ M :=
      pow_le_pow_left₀ (zero_le_one.trans (one_le_momentumBracket k)) hw M
    _ = ((m : ℝ) + 1) ^ M * Fourier.momentumBracket (x a) ^ M := mul_pow _ _ _
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (Finset.single_le_sum (fun b _ => pow_nonneg (zero_le_one.trans (one_le_momentumBracket (x b))) M)
        (Finset.mem_univ a)) (by positivity)

end WaveTurbulence.Incoh
