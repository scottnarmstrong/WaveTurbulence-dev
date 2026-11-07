/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.SumintPar.BilinearPhysicalIntegral
public import WaveTurbulence.Foundations.SumintPar.PairIntegerCoordinates
public import WaveTurbulence.Foundations.SumintPar.PoissonMajorant
public import WaveTurbulence.Foundations.SumintPar.PairKernels
import Mathlib.Tactic

/-!
# The bilinear small-time lattice estimate

Poisson summation and the exact landed `lemlayer1` give the uniform
stationary-phase majorant `C L^(2d) ⟨s⟩^{-d}` for `|s|≤L`.
-/

@[expose] public section
set_option autoImplicit false

open MeasureTheory WithLp

namespace WaveTurbulence.SumintPar

/-- The dual lattice series is exactly the one controlled by `lemlayer1`, after reflection. -/
theorem bilinear_dual_sum_eq {d : ℕ} (L : ℝ) (c : Fin 2 → Fin d → ℝ)
    (s : ℝ) (ξ ζ : Mom d) :
    (∑' m : Fin (2*d) → ℤ,
      ‖Fourier.timeFourier (flatBilinearAmplitude c s ξ ζ) (fun k => L * (m k : ℝ))‖) =
    ∑' p : (Fin d → ℤ) × (Fin d → ℤ),
      ‖Fourier.bilinearPhaseIntegral (Fourier.chi0MomSchwartz d) (Fourier.chi0MomSchwartz d)
        (toLp 2 (c 0)) (toLp 2 (c 1)) (L • NTSP.intVec p.1 + ξ) (L • NTSP.intVec p.2 + ζ) s‖ := by
  rw [← (pairIntegerEquiv d).tsum_eq]
  simp_rw [timeFourier_flatBilinearAmplitude_eq_phaseIntegral,
    flatMomentum_integer_zero, flatMomentum_integer_one]
  rw [← (Equiv.neg ((Fin d → ℤ) × (Fin d → ℤ))).tsum_eq]
  apply tsum_congr
  intro p
  change ‖Fourier.bilinearPhaseIntegral _ _ _ _
    (ξ - L • NTSP.intVec (-p.1)) (ζ - L • NTSP.intVec (-p.2)) s‖ = _
  rw [ntsp_intVec_neg, ntsp_intVec_neg, smul_neg, smul_neg, sub_neg_eq_add,
    sub_neg_eq_add, add_comm ξ, add_comm ζ]

/-- Uniform dual coefficient mass on the small-time region. -/
theorem exists_bilinear_small_dual_bound (d : ℕ) : ∃ C : ℝ, 0 ≤ C ∧
    ∀ {L : ℝ}, 1 ≤ L → ∀ (c : Fin 2 → Fin d → ℝ) (s : ℝ), |s| ≤ L →
      ∀ ξ ζ : Mom d,
      (∑' m : Fin (2*d) → ℤ,
        ‖Fourier.timeFourier (flatBilinearAmplitude c s ξ ζ) (fun k => L * (m k : ℝ))‖) ≤
        C / scalarBracket s^d := by
  obtain ⟨C, hC⟩ := NTSP.lemlayer1 d
  refine ⟨max C 0, le_max_right _ _, ?_⟩
  intro L hL c s hs ξ ζ
  rw [bilinear_dual_sum_eq]
  exact ((hC L hL s hs (toLp 2 (c 0)) (toLp 2 (c 1)) ξ ζ).2).trans
    (div_le_div_of_nonneg_right (le_max_left _ _) (pow_nonneg (Real.sqrt_nonneg _) _))

/-- The actual cutoff lattice sum has the full small-time gain before time integration. -/
theorem exists_bilinear_small_lattice_bound (d : ℕ) : ∃ C : ℝ, 0 ≤ C ∧
    ∀ {L : ℝ}, 1 ≤ L → ∀ (c : Fin 2 → Fin d → ℝ) (s : ℝ), |s| ≤ L →
      ∀ ξ ζ : Mom d,
      ‖∑' m : Fin (2*d) → ℤ, flatBilinearAmplitude c s ξ ζ (fun k => (m k : ℝ) / L)‖ ≤
        C * L^(2*d) / scalarBracket s^d := by
  obtain ⟨C, hC, hb⟩ := exists_bilinear_small_dual_bound d
  refine ⟨C, hC, ?_⟩
  intro L hL c s hs ξ ζ
  have hLp : 0 < L := by linarith
  have hP := norm_lattice_sum_le_poisson_smooth_compact
    (flatBilinearAmplitude_contDiff c s ξ ζ) (flatBilinearAmplitude_hasCompactSupport c s ξ ζ) hLp
  exact hP.trans ((mul_le_mul_of_nonneg_left (hb hL c s hs ξ ζ)
    (pow_nonneg hLp.le _)).trans_eq (by ring))

end WaveTurbulence.SumintPar
