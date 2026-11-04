/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Incoh.RawSourceCellSeries
public import WaveTurbulence.Foundations.Incoh.SourceCellTimeIntegrand
public import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
# Exact countable smooth-cell recovery of the raw source operator

The source time-domain integral and the actual countable localization sum
commute by the proved absolute cell/lattice majorant, uniformly in time.
-/

public section
noncomputable section
open MeasureTheory
open scoped ENNReal

namespace WaveTurbulence.Incoh

/-- The original normalized source lattice/time operator is exactly its countable smooth
localization, with absolute convergence justified from the actual source input norms. -/
theorem MomentumTreeData.sourceIntegral_eq_tsum_localizedSourceIntegral {d n m w K M : ℕ}
    (P : MomentumTreeData n m w) (ζ : Circle) (L γ δ : ℝ) (Q : Fin n → LayerLink d)
    (I : Set (Fin n → Fin 2 → ℝ)) (hI : I ⊆ Set.univ.pi (fun i => linkBox (Q i)))
    (f : Fin m → Mom d → ℂ)
    (S : (Fin m → Fin d → ℤ) → Finset ((Fin n × Fin 2) → Fin d → ℤ))
    (hcover : ∀ c k x, P.inputCellWeight c k x ≠ 0 →
      ∀ z, halfCellArrayWeight z (fun p : Fin n × Fin 2 => x p.1 p.2) ≠ 0 → z ∈ S c)
    {C : ℝ} (hS : ∀ c, ((S c).card : ℝ) ≤ C ^ n) {B : ℝ}
    (hL : 1 ≤ L) (hK : d + 1 ≤ K) (hM : 2 * d ≤ M) (hB : 0 ≤ B)
    (h : ∀ a, Fourier.spatialNorm K M (f a) ≤ ENNReal.ofReal B) (k : Mom d) :
    P.sourceIntegral ζ L γ δ Q I f k = ∑' u : SourceCellIndex S,
      P.localizedSourceIntegral ζ L γ δ Q I f u.1 u.2.val k := by
  have hLp : 0 < L := zero_lt_one.trans_le hL
  have hvol : volume I < ⊤ := (measure_mono hI).trans_lt
    (isCompact_univ_pi (fun _ : Fin n => isCompact_Icc)).measure_lt_top
  have hmass := P.tsum_enorm_sourceCellWeight_lattice_lt_top f S hS hL hK hM hB h k
  have hsum : (∑' u : SourceCellIndex S, ∫⁻ t in I,
      ‖P.sourceCellTimeIntegrand ζ L γ δ Q f S k u t‖ₑ) < ⊤ := by
    calc
      _ ≤ ∑' u : SourceCellIndex S,
          (∑' p : (Fin n × Fin 2) → Fin d → ℤ,
            ‖P.sourceCellWeight f S k (fun i j => latticePoint L (p (i, j))) u‖ₑ) * volume I := by
        apply ENNReal.tsum_le_tsum
        intro u
        apply (lintegral_mono (fun t => P.enorm_sourceCellTimeIntegrand_le ζ L γ δ Q f S k u t)).trans_eq
        rw [lintegral_const, Measure.restrict_apply_univ]
      _ = (∑' u : SourceCellIndex S, ∑' p : (Fin n × Fin 2) → Fin d → ℤ,
          ‖P.sourceCellWeight f S k (fun i j => latticePoint L (p (i, j))) u‖ₑ) * volume I :=
        ENNReal.tsum_mul_right
      _ < ⊤ := ENNReal.mul_lt_top hmass hvol
  have he : P.sourceTimeIntegrand ζ L γ δ Q f k =
      fun t => ∑' u : SourceCellIndex S, P.sourceCellTimeIntegrand ζ L γ δ Q f S k u t := by
    funext t
    exact P.sourceTimeIntegrand_eq_tsum_cells ζ L γ δ Q f S hcover hS hL hK hM hB h k t
  unfold sourceIntegral
  rw [he, integral_tsum (fun u =>
    (P.continuous_sourceCellTimeIntegrand ζ hLp γ δ Q f S k u).aestronglyMeasurable) hsum.ne,
    ← tsum_mul_left]
  apply tsum_congr
  intro u
  unfold localizedSourceIntegral
  congr 1
  apply integral_congr_ae
  apply ae_of_all
  intro t
  unfold sourceCellTimeIntegrand
  apply tsum_congr
  intro p
  unfold sourceCellWeight latticeMomentumArray
  ring

end WaveTurbulence.Incoh
