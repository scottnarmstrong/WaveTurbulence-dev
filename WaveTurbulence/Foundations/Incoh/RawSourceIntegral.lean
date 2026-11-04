/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Incoh.SourceAbsoluteConvergence
public import WaveTurbulence.Foundations.Incoh.SourceTemporalPhase
public import Mathlib.Analysis.Normed.Group.FunctionSeries

/-!
# The literal unlocalized source lattice/time operator

TARGET (incohproof2–3). Actual input spatial bounds give absolute lattice
convergence and continuous time dependence before integrating the source
domain. The coupling normalization and global garden sign are retained.
-/

public section
noncomputable section
open MeasureTheory
open scoped ENNReal

namespace WaveTurbulence.Incoh

/-- The raw source lattice series, before any smooth localization. -/
@[expose] def MomentumTreeData.sourceTimeIntegrand {d n m w : ℕ}
    (P : MomentumTreeData n m w) (ζ : Circle) (L γ δ : ℝ) (Q : Fin n → LayerLink d)
    (f : Fin m → Mom d → ℂ) (k : Mom d) (t : Fin n → Fin 2 → ℝ) : ℂ :=
  ∑' p : (Fin n × Fin 2) → Fin d → ℤ, sourceTemporalPhase L γ δ Q p t *
    ((ζ : ℂ) * P.sourceLeafWeight f k (fun i j => latticePoint L (p (i, j))))

/-- The original unlocalized normalized lattice/time source operator. -/
@[expose] def MomentumTreeData.sourceIntegral {d n m w : ℕ}
    (P : MomentumTreeData n m w) (ζ : Circle) (L γ δ : ℝ) (Q : Fin n → LayerLink d)
    (I : Set (Fin n → Fin 2 → ℝ)) (f : Fin m → Mom d → ℂ) (k : Mom d) : ℂ :=
  ((δ / (2 * L ^ ((d : ℝ) - γ))) ^ (2 * n) : ℝ) * ∫ t in I, P.sourceTimeIntegrand ζ L γ δ Q f k t

/-- Conditional convergence transport: the actual time series is continuous whenever its
raw input lattice weights have summable norms. Source spatial bounds prove that premise. -/
theorem MomentumTreeData.continuous_sourceTimeIntegrand_of_summable {d n m w : ℕ}
    (P : MomentumTreeData n m w) (ζ : Circle) (L γ δ : ℝ) (Q : Fin n → LayerLink d)
    (f : Fin m → Mom d → ℂ) (k : Mom d)
    (hs : Summable (fun p : (Fin n × Fin 2) → Fin d → ℤ =>
      ‖P.sourceLeafWeight f k (fun i j => latticePoint L (p (i, j)))‖)) :
    Continuous (P.sourceTimeIntegrand ζ L γ δ Q f k) := by
  apply continuous_tsum
  · intro p
    exact (continuous_sourceTemporalPhase L γ δ Q p).mul continuous_const
  · exact hs
  · intro p t
    simp only [norm_mul, Circle.norm_coe, one_mul]
    exact (mul_le_mul_of_nonneg_right (norm_sourceTemporalPhase_le_one L γ δ Q p t)
      (norm_nonneg _)).trans_eq (one_mul _)

/-- Input spatial bounds give actual time-integrability of the raw source series on its domain. -/
theorem MomentumTreeData.integrableOn_sourceTimeIntegrand {d n m w K M : ℕ}
    (P : MomentumTreeData n m w) (ζ : Circle) (L γ δ : ℝ) (Q : Fin n → LayerLink d)
    (I : Set (Fin n → Fin 2 → ℝ)) (hI : I ⊆ Set.univ.pi (fun i => linkBox (Q i)))
    (f : Fin m → Mom d → ℂ)
    (S : (Fin m → Fin d → ℤ) → Finset ((Fin n × Fin 2) → Fin d → ℤ))
    (hcover : ∀ c k x, P.inputCellWeight c k x ≠ 0 →
      ∀ z, halfCellArrayWeight z (fun p : Fin n × Fin 2 => x p.1 p.2) ≠ 0 → z ∈ S c)
    {C : ℝ} (hS : ∀ c, ((S c).card : ℝ) ≤ C ^ n) {B : ℝ}
    (hL : 1 ≤ L) (hK : d + 1 ≤ K) (hM : 2 * d ≤ M) (hB : 0 ≤ B)
    (h : ∀ a, Fourier.spatialNorm K M (f a) ≤ ENNReal.ofReal B) (k : Mom d) :
    IntegrableOn (P.sourceTimeIntegrand ζ L γ δ Q f k) I := by
  have hc := P.continuous_sourceTimeIntegrand_of_summable ζ L γ δ Q f k
    (P.summable_norm_sourceLeafWeight_lattice f S hcover hS hL hK hM hB h k)
  exact (hc.continuousOn.integrableOn_compact (isCompact_univ_pi (fun _ => isCompact_Icc))).mono_set hI

end WaveTurbulence.Incoh
