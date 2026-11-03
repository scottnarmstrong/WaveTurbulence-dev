/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.WeylSums.QuadraticDiagonalization

/-! # Removing parity constraints from compact lattice series -/

public section
open Finset
namespace WaveTurbulence.WeylSums

/-- A compact amplitude times any phase is an absolutely summable series. -/
theorem summable_finite_amplitude {ι : Type*} (A : ι → ℂ)
    (hA : (Function.support A).Finite) (φ : ι → ℝ) :
    Summable (fun x => A x * e (φ x)) := by
  apply summable_of_hasFiniteSupport
  apply hA.subset
  intro x hx
  simp only [Function.mem_support] at hx ⊢
  exact fun hz => hx (by rw [hz, zero_mul])

/-- A parity-restricted sum is the average of two unrestricted sums whose
linear frequencies differ by a half integer. -/
theorem tsum_parity_eq (A : ℤ × ℤ → ℂ) (hA : (Function.support A).Finite)
    (φ : ℤ × ℤ → ℝ) :
    (∑' pq : {pq : ℤ × ℤ // Even (pq.1-pq.2)}, A pq.val * e (φ pq.val)) =
      ((∑' pq : ℤ × ℤ, A pq * e (φ pq)) +
        (∑' pq : ℤ × ℤ, A pq * e (φ pq + ((pq.1-pq.2 : ℤ) : ℝ)/2))) / 2 := by
  classical
  have hsub : (∑' pq : {pq : ℤ × ℤ // Even (pq.1-pq.2)}, A pq.val * e (φ pq.val)) =
      ∑' pq : ℤ × ℤ, {pq : ℤ × ℤ | Even (pq.1-pq.2)}.indicator (fun pq => A pq * e (φ pq)) pq :=
    _root_.tsum_subtype {pq : ℤ × ℤ | Even (pq.1-pq.2)} (fun pq => A pq * e (φ pq))
  rw [hsub]
  have heq (pq : ℤ × ℤ) :
      ({pq : ℤ × ℤ | Even (pq.1-pq.2)}.indicator (fun pq => A pq * e (φ pq))) pq =
      (A pq * e (φ pq) + A pq * e (φ pq + ((pq.1-pq.2 : ℤ) : ℝ)/2))/2 := by
    calc
      _ = A pq * ((if Even (pq.1-pq.2) then (1 : ℂ) else 0) * e (φ pq)) := by
        by_cases hp : Even (pq.1-pq.2) <;> simp [hp]
      _ = A pq * ((e (φ pq) + e (φ pq + ((pq.1-pq.2 : ℤ) : ℝ)/2))/2) := by rw [parity_phase]
      _ = _ := by ring
  simp_rw [heq]
  rw [tsum_div_const, (summable_finite_amplitude A hA φ).tsum_add
    (summable_finite_amplitude A hA (fun pq => φ pq + ((pq.1-pq.2 : ℤ) : ℝ)/2))]

/-- The parity constraint costs no factor beyond averaging two linear shifts. -/
theorem norm_tsum_parity_le (A : ℤ × ℤ → ℂ) (hA : (Function.support A).Finite)
    (φ : ℤ × ℤ → ℝ) :
    ‖∑' pq : {pq : ℤ × ℤ // Even (pq.1-pq.2)}, A pq.val * e (φ pq.val)‖ ≤
      (‖∑' pq : ℤ × ℤ, A pq * e (φ pq)‖ +
        ‖∑' pq : ℤ × ℤ, A pq * e (φ pq + ((pq.1-pq.2 : ℤ) : ℝ)/2)‖)/2 := by
  rw [tsum_parity_eq A hA φ, norm_div]
  norm_num only [Complex.norm_ofNat]
  exact div_le_div_of_nonneg_right (norm_add_le _ _) (by norm_num)

end WaveTurbulence.WeylSums
