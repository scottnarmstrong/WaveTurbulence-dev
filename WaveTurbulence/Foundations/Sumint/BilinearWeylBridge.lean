/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Sumint.BilinearSmallRegion
public import WaveTurbulence.Foundations.WeylSums.MinorArcSums
import Mathlib.Tactic

/-!
# Exact bridge to the source bilinear lattice sum

The small-region Poisson estimate and the large-region Weyl estimate
are applied to literally the same complex series, with the same 2π
phase convention and the frozen lattice point map.
-/

public section

namespace WaveTurbulence.Sumint

/-- Packing commutes with sampling the scaled integer lattice. -/
theorem pairFlatten_latticePoint {d : ℕ} (L : ℝ) (p : (Fin d → ℤ) × (Fin d → ℤ)) :
    pairFlatten d (latticePoint L p.1, latticePoint L p.2) =
      fun k => (pairIntegerEquiv d p k : ℝ) / L := by
  rw [pairFlatten_apply]
  ext k
  simp only [Fourier.flattenBlocks_apply, pairIntegerEquiv, Equiv.trans_apply,
    Fourier.flattenIntegerBlocks_apply]
  have hb : k.divNat = (0 : Fin 2) ∨ k.divNat = 1 := by omega
  rcases hb with h | h <;> simp [h, latticePoint]

/-- The flattened smooth cutoff series is the landed bilinear lattice sum. -/
theorem flatBilinear_sum_eq_weyl {d : ℕ} (L s : ℝ) (a b ξ ζ : Mom d) :
    (∑' m : Fin (2*d) → ℤ, flatBilinearAmplitude ![WithLp.ofLp a, WithLp.ofLp b] s ξ ζ
      (fun k => (m k : ℝ) / L)) = WeylSums.bilinearLatticeSum L s a b ξ ζ := by
  rw [← (pairIntegerEquiv d).tsum_eq]
  unfold WeylSums.bilinearLatticeSum
  apply tsum_congr
  intro p
  rw [← pairFlatten_latticePoint, flatBilinearAmplitude_pair_eq]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, WithLp.toLp_ofLp,
    Fourier.chi0MomSchwartz_apply, Fourier.chi0TensorComplex, Fourier.chi0Tensor,
    WeylSums.latticeCutoff, Circle.smul_def, smul_eq_mul, Real.fourierChar_apply,
    WeylSums.e, Complex.ofReal_mul]
  rw [mul_comm]

/-- The source lattice sum has the stationary-phase gain uniformly on the small-time region. -/
theorem exists_bilinear_weyl_small_bound (d : ℕ) : ∃ C : ℝ, 0 ≤ C ∧
    ∀ {L : ℝ}, 1 ≤ L → ∀ s : ℝ, |s| ≤ L → ∀ a b ξ ζ : Mom d,
      ‖WeylSums.bilinearLatticeSum L s a b ξ ζ‖ ≤ C * L^(2*d) / scalarBracket s^d := by
  obtain ⟨C, hC, hb⟩ := exists_bilinear_small_lattice_bound d
  refine ⟨C, hC, ?_⟩
  intro L hL s hs a b ξ ζ
  rw [← flatBilinear_sum_eq_weyl]
  exact hb hL ![WithLp.ofLp a, WithLp.ofLp b] s hs ξ ζ

end WaveTurbulence.Sumint
