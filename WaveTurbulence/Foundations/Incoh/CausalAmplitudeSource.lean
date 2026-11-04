/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Incoh.CausalBoxKernel

/-!
# Exact source-domain identity for the hard causal amplitude

Cutoffs equal to one on the source interval fiber leave precisely its
indicator and the literal temporal phase. Endpoint conventions are exact.
-/

public section
noncomputable section
open Set

namespace WaveTurbulence.Incoh

/-- The selected-clock interval fiber with strict descendant ordering. -/
@[expose] def causalIntervalFiber (m : ℕ) (a b : Fin (m + 2) → ℝ) : Set (Fin (m + 2) → ℝ) :=
  {v | (∀ j, a j < v j ∧ v j ≤ b j) ∧ ∀ j : Fin (m + 1), v j.succ < v j.castSucc}

/-- The product of step functions is exactly the indicator of strict adjacent ordering. -/
theorem strictOrderingWeight_eq_indicator (n : ℕ) (v : Fin (n + 1) → ℝ) :
    strictOrderingWeight n v =
      {w : Fin (n + 1) → ℝ | ∀ j : Fin n, w j.succ < w j.castSucc}.indicator (fun _ => (1 : ℂ)) v := by
  classical
  by_cases hv : v ∈ {w : Fin (n + 1) → ℝ | ∀ j : Fin n, w j.succ < w j.castSucc}
  · rw [indicator_of_mem hv]
    unfold strictOrderingWeight
    apply Finset.prod_eq_one
    intro i _
    rw [indicator_of_mem (s := Ioi (0 : ℝ)) (a := v i.castSucc - v i.succ)
      (sub_pos.mpr (hv i)), Complex.ofReal_one]
  · rw [indicator_of_notMem hv]
    obtain ⟨i, hi⟩ := not_forall.mp hv
    unfold strictOrderingWeight
    apply Finset.prod_eq_zero (Finset.mem_univ i)
    rw [indicator_of_notMem (s := Ioi (0 : ℝ)) (a := v i.castSucc - v i.succ)
      (fun h => hi (sub_pos.mp h)), Complex.ofReal_zero]

/-- On a source fiber, all artificial internal cutoffs disappear exactly. -/
theorem causalBoxAmplitude_eq_sourceIndicator (m : ℕ) (χ : ℝ → ℝ)
    (phase a b : Fin (m + 2) → ℝ)
    (hχ : ∀ v : Fin (m + 2) → ℝ, (∀ j, a j < v j ∧ v j ≤ b j) → ∀ j, χ (v j) = 1)
    (v : Fin (m + 2) → ℝ) :
    causalBoxAmplitude m χ phase a b v =
      (causalIntervalFiber m a b).indicator (Fourier.linearTimePhase phase) v := by
  classical
  unfold causalBoxAmplitude invariantProductAmplitude
  by_cases hv : ∀ j, a j < v j ∧ v j ≤ b j
  · have hp : coordinateFactorProduct (fun j => hardLocalizedInterval χ (a j) (b j)) v = 1 := by
      apply Finset.prod_eq_one
      intro j _
      simp only [hardLocalizedInterval, indicator_of_mem (show v j ∈ Ioc (a j) (b j) from hv j),
        hχ v hv j, one_mul, Complex.ofReal_one]
    rw [hp, one_mul, strictOrderingWeight_eq_indicator]
    by_cases ho : v ∈ {w : Fin (m + 2) → ℝ | ∀ j : Fin (m + 1), w j.succ < w j.castSucc}
    · rw [indicator_of_mem ho, indicator_of_mem (show v ∈ causalIntervalFiber m a b from ⟨hv, ho⟩), mul_one]
    · rw [indicator_of_notMem ho,
        indicator_of_notMem (show v ∉ causalIntervalFiber m a b from fun h => ho h.2), mul_zero]
  · have hp : coordinateFactorProduct (fun j => hardLocalizedInterval χ (a j) (b j)) v = 0 := by
      obtain ⟨j, hj⟩ := not_forall.mp hv
      apply Finset.prod_eq_zero (Finset.mem_univ j)
      simp only [hardLocalizedInterval, indicator_of_notMem (show v j ∉ Ioc (a j) (b j) from hj),
        mul_zero, Complex.ofReal_zero]
    rw [hp, zero_mul, zero_mul,
      indicator_of_notMem (show v ∉ causalIntervalFiber m a b from fun h => hv h.1)]

end WaveTurbulence.Incoh
