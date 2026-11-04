/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Incoh.CausalBoxKernel

/-!
# The causal ordering kills reversed clock integrals

This is why the hard-boundary phase representation and the causal root
marginal use one common extension also outside the source clock box.
-/

public section
noncomputable section
open MeasureTheory Set

namespace WaveTurbulence.Incoh

@[simp] theorem orderedIntegral_zero (n : ℕ) (t s : ℝ) :
    Fourier.orderedIntegral n (fun _ => (0 : ℂ)) t s = 0 := by
  induction n generalizing t s with
  | zero => rfl
  | succ n ih => simp only [Fourier.orderedIntegral, ih, intervalIntegral.integral_zero]

/-- Strict descendant ordering vanishes if its first adjacent pair is reversed. -/
theorem strictOrderingWeight_eq_zero {m : ℕ} {v : Fin (m + 2) → ℝ}
    (hv : v 0 ≤ v (0 : Fin (m + 1)).succ) : strictOrderingWeight (m + 1) v = 0 := by
  classical
  apply Finset.prod_eq_zero (Finset.mem_univ (0 : Fin (m + 1)))
  change (((Ioi (0 : ℝ)).indicator (fun _ => (1 : ℝ))
    (v 0 - v (0 : Fin (m + 1)).succ) : ℝ) : ℂ) = 0
  rw [indicator_of_notMem (s := Ioi (0 : ℝ)) (a := v 0 - v (0 : Fin (m + 1)).succ)
    (not_lt_of_ge (sub_nonpos.mpr hv)), Complex.ofReal_zero]

/-- The hard amplitude retains literal causal support. -/
theorem causalBoxAmplitude_eq_zero {m : ℕ} (χ : ℝ → ℝ) (phase a b : Fin (m + 2) → ℝ)
    {v : Fin (m + 2) → ℝ} (hv : v 0 ≤ v (0 : Fin (m + 1)).succ) :
    causalBoxAmplitude m χ phase a b v = 0 := by
  rw [causalBoxAmplitude, invariantProductAmplitude, strictOrderingWeight_eq_zero hv, mul_zero]

/-- A function supported on strict first-pair ordering integrates to zero for reversed endpoints. -/
theorem orderedIntegral_eq_zero_of_reverse_support (m : ℕ) (F : (Fin (m + 2) → ℝ) → ℂ)
    (hF : ∀ v, v 0 ≤ v (0 : Fin (m + 1)).succ → F v = 0) {t s : ℝ} (ht : t ≤ s) :
    Fourier.orderedIntegral (m + 2) F t s = 0 := by
  change (∫ x in s..t, ∫ y in s..x,
    Fourier.orderedIntegral m (fun v => F (Fin.cons x (Fin.cons y v))) y s) = 0
  have he : (∫ x in s..t, ∫ y in s..x,
      Fourier.orderedIntegral m (fun v => F (Fin.cons x (Fin.cons y v))) y s) = ∫ _x in s..t, (0 : ℂ) := by
    apply intervalIntegral.integral_congr
    intro x hx
    dsimp only
    have hx' : x ∈ Icc t s := by simpa only [uIcc_of_ge ht] using hx
    have hy0 : (∫ y in s..x, Fourier.orderedIntegral m (fun v => F (Fin.cons x (Fin.cons y v))) y s) =
        ∫ _y in s..x, (0 : ℂ) := by
      apply intervalIntegral.integral_congr
      intro y hy
      dsimp only
      have hy' : y ∈ Icc x s := by simpa only [uIcc_of_ge hx'.2] using hy
      have hz : (fun v : Fin m → ℝ => F (Fin.cons x (Fin.cons y v))) = fun _ => 0 := by
        funext v
        exact hF _ hy'.1
      rw [hz, orderedIntegral_zero]
    rw [hy0, intervalIntegral.integral_zero]
  rw [he, intervalIntegral.integral_zero]

/-- The actual phase kernel is causal on all external clock pairs. -/
theorem causalBoxKernel_eq_zero_of_reverse {m : ℕ} (χ : ℝ → ℝ) (phase a b : Fin (m + 2) → ℝ)
    {t : Fin 2 → ℝ} (ht : t 0 ≤ t 1) : causalBoxKernel m χ phase a b t = 0 := by
  rw [causalBoxKernel, Fourier.weightedOrderedIntegral,
    orderedIntegral_eq_zero_of_reverse_support m _ (fun v hv => causalBoxAmplitude_eq_zero χ phase a b hv) ht,
    mul_zero]

end WaveTurbulence.Incoh
