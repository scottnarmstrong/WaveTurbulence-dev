/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Flower.IncTop.Reg.RawSourceCellSeries
public import WaveTurbulence.Foundations.Flower.IncTop.Reg.SourceCellTimeIntegrand
public import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-! Ported by source from C2-B-TOP `Cut2BReg.RawSourceCellIntegral` (sha256 in COPIED-SHA256SUMS); mechanical edits only.

R66 spatially modulated scratch copy. Original SHA256 recorded in REG-COPIES.json.

# Exact countable smooth-cell recovery of the raw source operator

The source time-domain integral and the actual countable localization sum
commute by the proved absolute cell/lattice majorant, uniformly in time.
-/

public section
noncomputable section
open MeasureTheory
open scoped ENNReal

namespace WaveTurbulence.Flower.IncTop
open WaveTurbulence.Incoh
open WaveTurbulence.Incoh.MomentumTreeData in
/-- The original normalized source lattice/time operator is exactly its countable smooth
localization, with absolute convergence justified from the actual source input norms. -/
theorem MomentumTreeData.sourceIntegral_eq_tsum_localizedSourceIntegral_of_cover_atSpatial {d n m w K M : ℕ}
    (P : MomentumTreeData n m w) (ζ : Circle) (L γ δ : ℝ) (Q : Fin n → LayerLink d)
    (I : Set (Fin n → Fin 2 → ℝ)) (hI : I ⊆ Set.univ.pi (fun i => linkBox (Q i)))
    (f : Fin m → Mom d → ℂ)
    (S : (Fin m → Fin d → ℤ) → Finset ((Fin n × Fin 2) → Fin d → ℤ))
    (k : Mom d)
    (hcover : ∀ c x, P.inputCellWeight c k x ≠ 0 →
      ∀ z, halfCellArrayWeight z (fun p : Fin n × Fin 2 => x p.1 p.2) ≠ 0 → z ∈ S c)
    {C : ℝ} (hS : ∀ c, ((S c).card : ℝ) ≤ C ^ n) {B : ℝ}
    (hL : 1 ≤ L) (hK : d + 1 ≤ K) (hM : 2 * d ≤ M) (hB : 0 ≤ B)
    (h : ∀ a, Fourier.spatialNorm K M (f a) ≤ ENNReal.ofReal B) :
    (MomentumTreeData.sourceIntegralSpatial (P := P)) ζ L γ δ Q I f k = ∑' u : SourceCellIndex S,
      (MomentumTreeData.localizedSourceIntegralSpatial (P := P)) ζ L γ δ Q I f u.1 u.2.val k := by
  have hLp : 0 < L := zero_lt_one.trans_le hL
  have hvol : volume I < ⊤ := (measure_mono hI).trans_lt
    (isCompact_univ_pi (fun _ : Fin n => isCompact_Icc)).measure_lt_top
  have hmass := (MomentumTreeData.tsum_enorm_sourceCellWeight_lattice_lt_topSpatial (P := P)) f S hS hL hK hM hB h k
  have hsum : (∑' u : SourceCellIndex S, ∫⁻ t in I,
      ‖(MomentumTreeData.sourceCellTimeIntegrandSpatial (P := P)) ζ L γ δ Q f S k u t‖ₑ) < ⊤ := by
    calc
      _ ≤ ∑' u : SourceCellIndex S,
          (∑' p : (Fin n × Fin 2) → Fin d → ℤ,
            ‖P.sourceCellWeight f S k (fun i j => latticePoint L (p (i, j))) u‖ₑ) * volume I := by
        apply ENNReal.tsum_le_tsum
        intro u
        apply (lintegral_mono (fun t => (MomentumTreeData.enorm_sourceCellTimeIntegrand_leSpatial (P := P)) ζ L γ δ Q f S k u t)).trans_eq
        rw [lintegral_const, Measure.restrict_apply_univ]
      _ = (∑' u : SourceCellIndex S, ∑' p : (Fin n × Fin 2) → Fin d → ℤ,
          ‖P.sourceCellWeight f S k (fun i j => latticePoint L (p (i, j))) u‖ₑ) * volume I :=
        ENNReal.tsum_mul_right
      _ < ⊤ := ENNReal.mul_lt_top hmass hvol
  have he : (MomentumTreeData.sourceTimeIntegrandSpatial (P := P)) ζ L γ δ Q f k =
      fun t => ∑' u : SourceCellIndex S, (MomentumTreeData.sourceCellTimeIntegrandSpatial (P := P)) ζ L γ δ Q f S k u t := by
    funext t
    exact (MomentumTreeData.sourceTimeIntegrand_eq_tsum_cells_of_cover_atSpatial (P := P)) ζ L γ δ Q f S k hcover hS hL hK hM hB h t
  unfold sourceIntegralSpatial
  rw [he, integral_tsum (fun u =>
    ((MomentumTreeData.continuous_sourceCellTimeIntegrandSpatial (P := P)) ζ hLp γ δ Q f S k u).aestronglyMeasurable) hsum.ne,
    ← tsum_mul_left]
  apply tsum_congr
  intro u
  unfold localizedSourceIntegralSpatial
  congr 1
  apply integral_congr_ae
  apply ae_of_all
  intro t
  unfold sourceCellTimeIntegrandSpatial
  apply tsum_congr
  intro p
  unfold sourceCellWeight latticeMomentumArray
  ring

open WaveTurbulence.Incoh.MomentumTreeData in
/-- Compatibility form for a cover uniform in every root momentum. -/
theorem MomentumTreeData.sourceIntegral_eq_tsum_localizedSourceIntegralSpatial {d n m w K M : ℕ}
    (P : MomentumTreeData n m w) (ζ : Circle) (L γ δ : ℝ) (Q : Fin n → LayerLink d)
    (I : Set (Fin n → Fin 2 → ℝ)) (hI : I ⊆ Set.univ.pi (fun i => linkBox (Q i)))
    (f : Fin m → Mom d → ℂ)
    (S : (Fin m → Fin d → ℤ) → Finset ((Fin n × Fin 2) → Fin d → ℤ))
    (hcover : ∀ c k x, P.inputCellWeight c k x ≠ 0 →
      ∀ z, halfCellArrayWeight z (fun p : Fin n × Fin 2 => x p.1 p.2) ≠ 0 → z ∈ S c)
    {C : ℝ} (hS : ∀ c, ((S c).card : ℝ) ≤ C ^ n) {B : ℝ}
    (hL : 1 ≤ L) (hK : d + 1 ≤ K) (hM : 2 * d ≤ M) (hB : 0 ≤ B)
    (h : ∀ a, Fourier.spatialNorm K M (f a) ≤ ENNReal.ofReal B) (k : Mom d) :
    (MomentumTreeData.sourceIntegralSpatial (P := P)) ζ L γ δ Q I f k = ∑' u : SourceCellIndex S,
      (MomentumTreeData.localizedSourceIntegralSpatial (P := P)) ζ L γ δ Q I f u.1 u.2.val k :=
  (MomentumTreeData.sourceIntegral_eq_tsum_localizedSourceIntegral_of_cover_atSpatial (P := P)) ζ L γ δ Q I hI f S k
    (fun c x => hcover c k x) hS hL hK hM hB h

end WaveTurbulence.Flower.IncTop