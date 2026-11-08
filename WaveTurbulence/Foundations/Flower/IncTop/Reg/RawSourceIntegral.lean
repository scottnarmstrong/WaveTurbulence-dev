/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Flower.IncTop.Reg.SourceAbsoluteConvergence
public import WaveTurbulence.Foundations.Flower.IncTop.Reg.SourceTemporalPhase
public import Mathlib.Analysis.Normed.Group.FunctionSeries

/-! Ported by source from C2-B-TOP `Cut2BReg.RawSourceIntegral` (sha256 in COPIED-SHA256SUMS); mechanical edits only.

R66 spatially modulated scratch copy. Original SHA256 recorded in REG-COPIES.json.

# The literal unlocalized source lattice/time operator

TARGET (incohproof2–3). Actual input spatial bounds give absolute lattice
convergence and continuous time dependence before integrating the source
domain. The coupling normalization and global garden sign are retained.
-/

public section
noncomputable section
open MeasureTheory
open scoped ENNReal

namespace WaveTurbulence.Flower.IncTop
open WaveTurbulence.Incoh
open WaveTurbulence.Incoh.MomentumTreeData in
/-- The raw source lattice series, before any smooth localization. -/
@[expose] def MomentumTreeData.sourceTimeIntegrandSpatial {d n m w : ℕ}
    (P : MomentumTreeData n m w) (ζ : Circle) (L γ δ : ℝ) (Q : Fin n → LayerLink d)
    (f : Fin m → Mom d → ℂ) (k : Mom d) (t : Fin n → Fin 2 → ℝ) : ℂ :=
  ∑' p : (Fin n × Fin 2) → Fin d → ℤ, sourceTemporalPhaseSpatial L γ δ Q p t *
    ((ζ : ℂ) * P.sourceLeafWeight f k (fun i j => latticePoint L (p (i, j))))

open WaveTurbulence.Incoh.MomentumTreeData in
/-- The original unlocalized normalized lattice/time source operator. -/
@[expose] def MomentumTreeData.sourceIntegralSpatial {d n m w : ℕ}
    (P : MomentumTreeData n m w) (ζ : Circle) (L γ δ : ℝ) (Q : Fin n → LayerLink d)
    (I : Set (Fin n → Fin 2 → ℝ)) (f : Fin m → Mom d → ℂ) (k : Mom d) : ℂ :=
  ((δ / (2 * L ^ ((d : ℝ) - γ))) ^ (2 * n) : ℝ) * ∫ t in I, (MomentumTreeData.sourceTimeIntegrandSpatial (P := P)) ζ L γ δ Q f k t

open WaveTurbulence.Incoh.MomentumTreeData in
/-- Conditional convergence transport: the actual time series is continuous whenever its
raw input lattice weights have summable norms. Source spatial bounds prove that premise. -/
theorem MomentumTreeData.continuous_sourceTimeIntegrand_of_summableSpatial {d n m w : ℕ}
    (P : MomentumTreeData n m w) (ζ : Circle) (L γ δ : ℝ) (Q : Fin n → LayerLink d)
    (f : Fin m → Mom d → ℂ) (k : Mom d)
    (hs : Summable (fun p : (Fin n × Fin 2) → Fin d → ℤ =>
      ‖P.sourceLeafWeight f k (fun i j => latticePoint L (p (i, j)))‖)) :
    Continuous ((MomentumTreeData.sourceTimeIntegrandSpatial (P := P)) ζ L γ δ Q f k) := by
  apply continuous_tsum
  · intro p
    exact (continuous_sourceTemporalPhaseSpatial L γ δ Q p).mul continuous_const
  · exact hs
  · intro p t
    simp only [norm_mul, Circle.norm_coe, one_mul]
    exact (mul_le_mul_of_nonneg_right (norm_sourceTemporalPhase_le_oneSpatial L γ δ Q p t)
      (norm_nonneg _)).trans_eq (one_mul _)

open WaveTurbulence.Incoh.MomentumTreeData in
/-- Input spatial bounds give actual time-integrability of the raw source series on its domain. -/
theorem MomentumTreeData.integrableOn_sourceTimeIntegrandSpatial {d n m w K M : ℕ}
    (P : MomentumTreeData n m w) (ζ : Circle) (L γ δ : ℝ) (Q : Fin n → LayerLink d)
    (I : Set (Fin n → Fin 2 → ℝ)) (hI : I ⊆ Set.univ.pi (fun i => linkBox (Q i)))
    (f : Fin m → Mom d → ℂ)
    (S : (Fin m → Fin d → ℤ) → Finset ((Fin n × Fin 2) → Fin d → ℤ))
    (hcover : ∀ c k x, P.inputCellWeight c k x ≠ 0 →
      ∀ z, halfCellArrayWeight z (fun p : Fin n × Fin 2 => x p.1 p.2) ≠ 0 → z ∈ S c)
    {C : ℝ} (hS : ∀ c, ((S c).card : ℝ) ≤ C ^ n) {B : ℝ}
    (hL : 1 ≤ L) (hK : d + 1 ≤ K) (hM : 2 * d ≤ M) (hB : 0 ≤ B)
    (h : ∀ a, Fourier.spatialNorm K M (f a) ≤ ENNReal.ofReal B) (k : Mom d) :
    IntegrableOn ((MomentumTreeData.sourceTimeIntegrandSpatial (P := P)) ζ L γ δ Q f k) I := by
  have hc := (MomentumTreeData.continuous_sourceTimeIntegrand_of_summableSpatial (P := P)) ζ L γ δ Q f k
    ((MomentumTreeData.summable_norm_sourceLeafWeight_latticeSpatial (P := P)) f S hcover hS hL hK hM hB h k)
  exact (hc.continuousOn.integrableOn_compact (isCompact_univ_pi (fun _ => isCompact_Icc))).mono_set hI

end WaveTurbulence.Flower.IncTop