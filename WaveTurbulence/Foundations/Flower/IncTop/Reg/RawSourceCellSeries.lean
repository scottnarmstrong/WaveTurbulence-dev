/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Flower.IncTop.Reg.RawSourceIntegral

/-! Ported by source from C2-B-TOP `Cut2BReg.RawSourceCellSeries` (sha256 in COPIED-SHA256SUMS); mechanical edits only.

R66 spatially modulated scratch copy. Original SHA256 recorded in REG-COPIES.json.

# Exact cell recombination of the literal raw source time series

Absolute cell/lattice convergence justifies exchanging the actual source
lattice series with the countable smooth cell partition, at every time.
-/

public section
noncomputable section
open MeasureTheory
open scoped ENNReal

namespace WaveTurbulence.Flower.IncTop
open WaveTurbulence.Incoh
open WaveTurbulence.Incoh.MomentumTreeData in
/-- Exact source lattice/cell rearrangement from the proved absolute source majorant. -/
theorem MomentumTreeData.sourceTimeIntegrand_eq_tsum_cells_of_cover_atSpatial {d n m w K M : ℕ}
    (P : MomentumTreeData n m w) (ζ : Circle) (L γ δ : ℝ) (Q : Fin n → LayerLink d)
    (f : Fin m → Mom d → ℂ)
    (S : (Fin m → Fin d → ℤ) → Finset ((Fin n × Fin 2) → Fin d → ℤ))
    (k : Mom d)
    (hcover : ∀ c x, P.inputCellWeight c k x ≠ 0 →
      ∀ z, halfCellArrayWeight z (fun p : Fin n × Fin 2 => x p.1 p.2) ≠ 0 → z ∈ S c)
    {C : ℝ} (hS : ∀ c, ((S c).card : ℝ) ≤ C ^ n) {B : ℝ}
    (hL : 1 ≤ L) (hK : d + 1 ≤ K) (hM : 2 * d ≤ M) (hB : 0 ≤ B)
    (h : ∀ a, Fourier.spatialNorm K M (f a) ≤ ENNReal.ofReal B)
    (t : Fin n → Fin 2 → ℝ) :
    (MomentumTreeData.sourceTimeIntegrandSpatial (P := P)) ζ L γ δ Q f k t =
      ∑' u : SourceCellIndex S, ∑' p : (Fin n × Fin 2) → Fin d → ℤ,
        sourceTemporalPhaseSpatial L γ δ Q p t * ((ζ : ℂ) *
          P.sourceCellWeight f S k (fun i j => latticePoint L (p (i, j))) u) := by
  have hn : Summable (fun q : SourceCellIndex S × ((Fin n × Fin 2) → Fin d → ℤ) =>
      ‖P.sourceCellWeight f S k (fun i j => latticePoint L (q.2 (i, j))) q.1‖) := by
    apply tsum_enorm_ne_top_iff_summable_norm.mp
    rw [ENNReal.tsum_prod']
    exact ((MomentumTreeData.tsum_enorm_sourceCellWeight_lattice_lt_topSpatial (P := P)) f S hS hL hK hM hB h k).ne
  have hs : Summable (fun q : SourceCellIndex S × ((Fin n × Fin 2) → Fin d → ℤ) =>
      sourceTemporalPhaseSpatial L γ δ Q q.2 t * ((ζ : ℂ) *
        P.sourceCellWeight f S k (fun i j => latticePoint L (q.2 (i, j))) q.1)) := by
    apply Summable.of_norm_bounded hn
    intro q
    simp only [norm_mul, Circle.norm_coe, one_mul]
    exact (mul_le_mul_of_nonneg_right (norm_sourceTemporalPhase_le_oneSpatial L γ δ Q q.2 t)
      (norm_nonneg _)).trans_eq (one_mul _)
  calc
    _ = ∑' p : (Fin n × Fin 2) → Fin d → ℤ, ∑' u : SourceCellIndex S,
        sourceTemporalPhaseSpatial L γ δ Q p t * ((ζ : ℂ) *
          P.sourceCellWeight f S k (fun i j => latticePoint L (p (i, j))) u) := by
      unfold sourceTimeIntegrandSpatial
      apply tsum_congr
      intro p
      simp_rw [← mul_assoc]
      rw [tsum_mul_left]
      rw [(P.hasSum_sourceCellWeight_of_cover_at f S k (fun i j => latticePoint L (p (i, j)))
        (fun c => hcover c _)).tsum_eq]
    _ = _ := hs.tsum_comm

open WaveTurbulence.Incoh.MomentumTreeData in
/-- Compatibility form for a cover uniform in every root momentum. -/
theorem MomentumTreeData.sourceTimeIntegrand_eq_tsum_cellsSpatial {d n m w K M : ℕ}
    (P : MomentumTreeData n m w) (ζ : Circle) (L γ δ : ℝ) (Q : Fin n → LayerLink d)
    (f : Fin m → Mom d → ℂ)
    (S : (Fin m → Fin d → ℤ) → Finset ((Fin n × Fin 2) → Fin d → ℤ))
    (hcover : ∀ c k x, P.inputCellWeight c k x ≠ 0 →
      ∀ z, halfCellArrayWeight z (fun p : Fin n × Fin 2 => x p.1 p.2) ≠ 0 → z ∈ S c)
    {C : ℝ} (hS : ∀ c, ((S c).card : ℝ) ≤ C ^ n) {B : ℝ}
    (hL : 1 ≤ L) (hK : d + 1 ≤ K) (hM : 2 * d ≤ M) (hB : 0 ≤ B)
    (h : ∀ a, Fourier.spatialNorm K M (f a) ≤ ENNReal.ofReal B)
    (k : Mom d) (t : Fin n → Fin 2 → ℝ) :
    (MomentumTreeData.sourceTimeIntegrandSpatial (P := P)) ζ L γ δ Q f k t =
      ∑' u : SourceCellIndex S, ∑' p : (Fin n × Fin 2) → Fin d → ℤ,
        sourceTemporalPhaseSpatial L γ δ Q p t * ((ζ : ℂ) *
          P.sourceCellWeight f S k (fun i j => latticePoint L (p (i, j))) u) :=
  (MomentumTreeData.sourceTimeIntegrand_eq_tsum_cells_of_cover_atSpatial (P := P)) ζ L γ δ Q f S k
    (fun c x => hcover c k x) hS hL hK hM hB h t

end WaveTurbulence.Flower.IncTop