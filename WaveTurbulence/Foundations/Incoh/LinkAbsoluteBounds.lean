/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Incoh.CutoffMass

/-!
# Absolute convergence and the explicit trivial bound for the link factor

TARGET (incohproof12): the bound `(5L)^(2d)` is uniform in all centers,
linear phases, and the time frequency. All lattice series are genuinely
absolutely summable.
-/

public section

noncomputable section

namespace WaveTurbulence.Incoh

variable {d : ℕ}

theorem norm_cutoffAmplitude (L : ℝ) (A : LinkParameters d)
    (p : (Fin d → ℤ) × (Fin d → ℤ)) :
    ‖cutoffAmplitude L A p‖ = WeylSums.latticeCutoff (latticePoint L p.1 - A.leftCenter) *
      WeylSums.latticeCutoff (latticePoint L p.2 - A.rightCenter) := by
  rw [cutoffAmplitude, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (mul_nonneg (latticeCutoff_nonneg _) (latticeCutoff_nonneg _))]

theorem summable_norm_cutoffAmplitude {L : ℝ} (hL : 0 < L) (A : LinkParameters d) :
    Summable (fun p => ‖cutoffAmplitude L A p‖) := by
  apply summable_of_hasFiniteSupport
  change (Function.support (fun p => ‖cutoffAmplitude L A p‖)).Finite
  simpa only [Function.support, ne_eq, norm_eq_zero] using finite_support_cutoffAmplitude hL A

/-- The absolute double-cutoff mass factors into the two vector masses. -/
theorem tsum_norm_cutoffAmplitude_eq {L : ℝ} (hL : 0 < L) (A : LinkParameters d) :
    (∑' p, ‖cutoffAmplitude L A p‖) =
      (∑' x, WeylSums.latticeCutoff (latticePoint L x - A.leftCenter)) *
      (∑' y, WeylSums.latticeCutoff (latticePoint L y - A.rightCenter)) := by
  rw [(summable_norm_cutoffAmplitude hL A).tsum_prod]
  simp_rw [norm_cutoffAmplitude, tsum_mul_left]
  rw [tsum_mul_right]

/-- Uniform absolute mass, including arbitrary real translations of each cutoff. -/
theorem tsum_norm_cutoffAmplitude_le {L : ℝ} (hL : 1 ≤ L) (A : LinkParameters d) :
    (∑' p, ‖cutoffAmplitude L A p‖) ≤ (5 * L) ^ (2 * d) := by
  rw [tsum_norm_cutoffAmplitude_eq (zero_lt_one.trans_le hL)]
  apply (mul_le_mul (tsum_latticeCutoff_le hL A.leftCenter) (tsum_latticeCutoff_le hL A.rightCenter)
    (tsum_nonneg fun _ => latticeCutoff_nonneg _) (by positivity)).trans_eq
  rw [← pow_add, two_mul]

/-- Correcting by the Wick coefficient and adding any real phase never increases a term's mass. -/
theorem norm_linkTerm_le (L s : ℝ) (A : LinkParameters d)
    (p : (Fin d → ℤ) × (Fin d → ℤ)) :
    ‖linkAmplitude L A p * WeylSums.e (linkPhase L s A p)‖ ≤ ‖cutoffAmplitude L A p‖ := by
  rw [norm_mul, WeylSums.norm_e, mul_one, linkAmplitude, norm_mul,
    Complex.norm_real, Real.norm_eq_abs]
  exact mul_le_of_le_one_left (norm_nonneg _) (abs_linkEpsilon_le _ _)

theorem summable_norm_linkTerm {L : ℝ} (hL : 0 < L) (s : ℝ) (A : LinkParameters d) :
    Summable (fun p => ‖linkAmplitude L A p * WeylSums.e (linkPhase L s A p)‖) :=
  Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (norm_linkTerm_le L s A)
    (summable_norm_cutoffAmplitude hL A)

/-- TARGET's trivial pointwise estimate, with the explicit dimensional factor `5^(2d)`. -/
theorem norm_linkLatticeSum_le {L : ℝ} (hL : 1 ≤ L) (s : ℝ) (A : LinkParameters d) :
    ‖linkLatticeSum L s A‖ ≤ (5 * L) ^ (2 * d) := by
  have hLp := zero_lt_one.trans_le hL
  apply (norm_tsum_le_tsum_norm (summable_norm_linkTerm hLp s A)).trans
  exact (Summable.tsum_le_tsum (norm_linkTerm_le L s A) (summable_norm_linkTerm hLp s A)
    (summable_norm_cutoffAmplitude hLp A)).trans (tsum_norm_cutoffAmplitude_le hL A)

end WaveTurbulence.Incoh
