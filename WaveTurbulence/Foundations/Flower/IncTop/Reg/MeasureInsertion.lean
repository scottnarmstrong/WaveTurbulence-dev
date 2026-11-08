/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Flower.IncTop.Reg.RawModulation
public import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-! Ported by source from C2-B-TOP `Cut2BReg.MeasureInsertion` (sha256 in COPIED-SHA256SUMS); mechanical edits only.
 # Fourier measures inserted in the literal internal lattice sum

The source helper below assumes only absolute lattice convergence. That
premise is separately proved from the source input bounds in
`SourceAbsoluteConvergence`; it is not a weighted norm assumption.
-/

public section
noncomputable section
open MeasureTheory
open scoped ENNReal

namespace WaveTurbulence.Flower.IncTop
open WaveTurbulence.Incoh
open Cut2A

open WaveTurbulence.Incoh.MomentumTreeData in
/-- The actual weighted raw lattice sum. The weight depends only on internal pairs. -/
@[expose] def MomentumTreeData.weightedSourceTimeIntegrand {d n m w : ℕ} {α : Type*}
    [MeasurableSpace α] (P : MomentumTreeData n m w) (F : SpatialMeasure (PairedMomentum d n) α)
    (ζ : Circle) (L γ δ : ℝ) (Q : Fin n → LayerLink d)
    (f : Fin m → Mom d → ℂ) (k : Mom d) (t : Fin n → Fin 2 → ℝ) : ℂ :=
  ∑' p : (Fin n × Fin 2) → Fin d → ℤ,
    F.value (pairedLattice L p) * sourceTemporalPhase L γ δ Q p t *
      ((ζ : ℂ) * P.sourceLeafWeight f k (fun i j => latticePoint L (p (i, j))))

open WaveTurbulence.Incoh.MomentumTreeData in
/-- Literal insertion before clock integration: no external momentum is Fourier expanded. -/
theorem MomentumTreeData.weightedSourceTimeIntegrand_eq_integral_of_summable
    {d n m w : ℕ} {α : Type*} [MeasurableSpace α]
    (P : MomentumTreeData n m w) (F : SpatialMeasure (PairedMomentum d n) α)
    (ζ : Circle) (L γ δ : ℝ) (Q : Fin n → LayerLink d)
    (f : Fin m → Mom d → ℂ) (k : Mom d)
    (hs : Summable (fun p : (Fin n × Fin 2) → Fin d → ℤ =>
      ‖P.sourceLeafWeight f k (fun i j => latticePoint L (p (i, j)))‖))
    (t : Fin n → Fin 2 → ℝ) :
    (MomentumTreeData.weightedSourceTimeIntegrand (P := P)) F ζ L γ δ Q f k t =
      ∫ a, F.amplitude a * (MomentumTreeData.sourceTimeIntegrandSpatial (P := P)) ζ L γ δ
        (spatialFrequencyLinks Q (F.frequency a)) f k t ∂F.μ := by
  let W := fun p : (Fin n × Fin 2) → Fin d → ℤ =>
    (ζ : ℂ) * P.sourceLeafWeight f k (fun i j => latticePoint L (p (i, j)))
  let G := fun p a => F.amplitude a *
    (Real.fourierChar (inner ℝ (F.frequency a) (pairedLattice L p)) : ℂ) *
      (sourceTemporalPhase L γ δ Q p t * W p)
  have hi (p : (Fin n × Fin 2) → Fin d → ℤ) : Integrable (G p) F.μ :=
    (F.integrable_character (pairedLattice L p)).mul_const _
  have hn (p : (Fin n × Fin 2) → Fin d → ℤ) :
      (∫ a, ‖G p a‖ ∂F.μ) ≤ F.mass * ‖P.sourceLeafWeight f k
        (fun i j => latticePoint L (p (i, j)))‖ := by
    simp only [G, norm_mul, Circle.norm_coe, mul_one, W, one_mul,
      integral_mul_const, SpatialMeasure.mass]
    exact mul_le_mul_of_nonneg_left
      ((mul_le_mul_of_nonneg_right (norm_sourceTemporalPhase_le_one L γ δ Q p t)
        (norm_nonneg _)).trans_eq (one_mul _)) F.mass_nonneg
  have hsum : Summable (fun p => ∫ a, ‖G p a‖ ∂F.μ) :=
    (hs.mul_left F.mass).of_nonneg_of_le (fun _ => integral_nonneg (fun _ => norm_nonneg _)) hn
  have he := (hasSum_integral_of_summable_integral_norm hi hsum).tsum_eq
  calc
    _ = ∑' p, ∫ a, G p a ∂F.μ := by
      apply tsum_congr
      intro p
      rw [integral_mul_const, ← SpatialMeasure.value]
      dsimp only [weightedSourceTimeIntegrand, W]
      ring
    _ = ∫ a, ∑' p, G p a ∂F.μ := he
    _ = _ := by
      apply integral_congr_ae
      apply ae_of_all
      intro a
      dsimp only
      unfold sourceTimeIntegrandSpatial
      rw [← tsum_mul_left]
      apply tsum_congr
      intro p
      rw [sourceTemporalPhaseSpatial_eq_character]
      dsimp only [G, W]
      ring

end WaveTurbulence.Flower.IncTop