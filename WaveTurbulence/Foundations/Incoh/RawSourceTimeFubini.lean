/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Incoh.RawSourceIntegral
public import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-! # Exact lattice/time interchange for the original unlocalized source series -/

public section
noncomputable section
open MeasureTheory Set

namespace WaveTurbulence.Incoh

/-- Conditional source Fubini: the original lattice input mass suffices for exact interchange.
The source spatial bounds prove this summability independently. -/
theorem MomentumTreeData.integral_sourceTimeIntegrand_eq_tsum {d n m w : ℕ}
    (P : MomentumTreeData n m w) (ζ : Circle) (L γ δ : ℝ) (Q : Fin n → LayerLink d)
    (I : Set (Fin n → Fin 2 → ℝ)) (hI : I ⊆ univ.pi (fun i => linkBox (Q i)))
    (f : Fin m → Mom d → ℂ) (k : Mom d)
    (hs : Summable (fun p : (Fin n × Fin 2) → Fin d → ℤ =>
      ‖P.sourceLeafWeight f k (fun i j => latticePoint L (p (i, j)))‖)) :
    (∫ t in I, P.sourceTimeIntegrand ζ L γ δ Q f k t) =
      ∑' p : (Fin n × Fin 2) → Fin d → ℤ, ∫ t in I,
        sourceTemporalPhase L γ δ Q p t *
          ((ζ : ℂ) * P.sourceLeafWeight f k (fun i j => latticePoint L (p (i, j)))) := by
  let μ := (volume : Measure (Fin n → Fin 2 → ℝ)).restrict I
  have hfinite : μ univ < ⊤ := by
    rw [Measure.restrict_apply_univ]
    exact (measure_mono hI).trans_lt
      ((isCompact_univ_pi (fun _ => isCompact_Icc)).measure_lt_top)
  let : IsFiniteMeasure μ := ⟨hfinite⟩
  let W := fun p : (Fin n × Fin 2) → Fin d → ℤ =>
    ((ζ : ℂ) * P.sourceLeafWeight f k (fun i j => latticePoint L (p (i, j))))
  let F := fun p t => sourceTemporalPhase L γ δ Q p t * W p
  have hi (p) : Integrable (F p) μ :=
    (integrableOn_sourceTemporalPhase L γ δ Q p hI).mul_const _
  have hnorm (p) (t : Fin n → Fin 2 → ℝ) : ‖F p t‖ ≤
      ‖P.sourceLeafWeight f k (fun i j => latticePoint L (p (i, j)))‖ := by
    simp only [F, W, norm_mul, Circle.norm_coe, one_mul]
    exact (mul_le_mul_of_nonneg_right (norm_sourceTemporalPhase_le_one L γ δ Q p t)
      (norm_nonneg _)).trans_eq (one_mul _)
  have hsum : Summable (fun p => ∫ t, ‖F p t‖ ∂μ) := by
    apply Summable.of_nonneg_of_le (fun p => integral_nonneg (fun _ => norm_nonneg _))
      (fun p => ?_) (hs.mul_left (μ.real univ))
    have hle := integral_mono (hi p).norm (integrable_const
      ‖P.sourceLeafWeight f k (fun i j => latticePoint L (p (i, j)))‖) (hnorm p)
    simpa only [integral_const, smul_eq_mul] using hle
  exact (integral_tsum_of_summable_integral_norm hi hsum).symm

end WaveTurbulence.Incoh
