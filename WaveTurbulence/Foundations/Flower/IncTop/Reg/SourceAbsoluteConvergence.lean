/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Flower.IncTop.Reg.SourceCellLatticeMajorant
public import WaveTurbulence.Foundations.Flower.IncTop.Reg.SourceCellMassBound

/-! Ported by source from C2-B-TOP `Cut2BReg.SourceAbsoluteConvergence` (sha256 in COPIED-SHA256SUMS); mechanical edits only.

R66 spatially modulated scratch copy. Original SHA256 recorded in REG-COPIES.json.

# Absolute convergence of the literal source lattice sum

Pointwise smooth localization and the actual spectral/cutoff majorants
prove absolute convergence before any source lattice/time rearrangement.
-/

public section
noncomputable section
open MeasureTheory
open scoped ENNReal

namespace WaveTurbulence.Flower.IncTop
open WaveTurbulence.Incoh
open WaveTurbulence.Incoh.MomentumTreeData in
/-- The full cell/lattice absolute mass is finite, directly from source spatial norms. -/
theorem MomentumTreeData.tsum_enorm_sourceCellWeight_lattice_lt_topSpatial {d n m w K M : ℕ}
    (P : MomentumTreeData n m w) (f : Fin m → Mom d → ℂ)
    (S : (Fin m → Fin d → ℤ) → Finset ((Fin n × Fin 2) → Fin d → ℤ))
    {C : ℝ} (hS : ∀ c, ((S c).card : ℝ) ≤ C ^ n)
    {B L : ℝ} (hL : 1 ≤ L) (hK : d + 1 ≤ K) (hM : 2 * d ≤ M) (hB : 0 ≤ B)
    (h : ∀ a, Fourier.spatialNorm K M (f a) ≤ ENNReal.ofReal B) (k : Mom d) :
    (∑' u : SourceCellIndex S, ∑' p : (Fin n × Fin 2) → Fin d → ℤ,
      ‖P.sourceCellWeight f S k (fun i j => latticePoint L (p (i, j))) u‖ₑ) < ⊤ := by
  have hm : (∑' u : SourceCellIndex S,
      ∫⁻ ξ, ‖localizedSpectralReference (n := n) f u.1 ξ‖ₑ) < ⊤ := by
    rw [tsum_sourceCellIndex S (fun c => ∫⁻ ξ, ‖localizedSpectralReference (n := n) f c ξ‖ₑ),
      ← lintegral_sourceCellMeasure S _
      (fun c => (continuous_localizedSpectralReferenceSpatial f c hK hB h).measurable.enorm)]
    exact (lintegral_sourceCellMeasure_reference_leSpatial S hS f hK hM hB h).trans_lt (by finiteness)
  calc
    _ ≤ ∑' u : SourceCellIndex S,
        (∫⁻ ξ, ‖localizedSpectralReference (n := n) f u.1 ξ‖ₑ) *
          ENNReal.ofReal ((5 * L) ^ d) ^ (2 * n) :=
      ENNReal.tsum_le_tsum (fun u => (MomentumTreeData.tsum_enorm_sourceCellWeight_lattice_leSpatial (P := P)) f S hL hK hB h k u)
    _ = (∑' u : SourceCellIndex S, ∫⁻ ξ, ‖localizedSpectralReference (n := n) f u.1 ξ‖ₑ) *
        ENNReal.ofReal ((5 * L) ^ d) ^ (2 * n) := ENNReal.tsum_mul_right
    _ < ⊤ := ENNReal.mul_lt_top hm (by finiteness)

open WaveTurbulence.Incoh.MomentumTreeData in
/-- Absolute convergence of the raw unlocalized source lattice weight, without a Fourier premise. -/
theorem MomentumTreeData.summable_norm_sourceLeafWeight_latticeSpatial {d n m w K M : ℕ}
    (P : MomentumTreeData n m w) (f : Fin m → Mom d → ℂ)
    (S : (Fin m → Fin d → ℤ) → Finset ((Fin n × Fin 2) → Fin d → ℤ))
    (hcover : ∀ c k x, P.inputCellWeight c k x ≠ 0 →
      ∀ z, halfCellArrayWeight z (fun p : Fin n × Fin 2 => x p.1 p.2) ≠ 0 → z ∈ S c)
    {C : ℝ} (hS : ∀ c, ((S c).card : ℝ) ≤ C ^ n)
    {B L : ℝ} (hL : 1 ≤ L) (hK : d + 1 ≤ K) (hM : 2 * d ≤ M) (hB : 0 ≤ B)
    (h : ∀ a, Fourier.spatialNorm K M (f a) ≤ ENNReal.ofReal B) (k : Mom d) :
    Summable (fun p : (Fin n × Fin 2) → Fin d → ℤ =>
      ‖P.sourceLeafWeight f k (fun i j => latticePoint L (p (i, j)))‖) := by
  apply tsum_enorm_ne_top_iff_summable_norm.mp
  apply ne_of_lt
  calc
    _ ≤ ∑' p : (Fin n × Fin 2) → Fin d → ℤ, ∑' u : SourceCellIndex S,
        ‖P.sourceCellWeight f S k (fun i j => latticePoint L (p (i, j))) u‖ₑ := by
      apply ENNReal.tsum_le_tsum
      intro p
      have he := (P.hasSum_sourceCellWeight f S hcover k
        (fun i j => latticePoint L (p (i, j)))).tsum_eq
      rw [← he]
      exact enorm_tsum_le_tsum_enorm
    _ = ∑' u : SourceCellIndex S, ∑' p : (Fin n × Fin 2) → Fin d → ℤ,
        ‖P.sourceCellWeight f S k (fun i j => latticePoint L (p (i, j))) u‖ₑ := ENNReal.tsum_comm
    _ < ⊤ := (MomentumTreeData.tsum_enorm_sourceCellWeight_lattice_lt_topSpatial (P := P)) f S hS hL hK hM hB h k

end WaveTurbulence.Flower.IncTop