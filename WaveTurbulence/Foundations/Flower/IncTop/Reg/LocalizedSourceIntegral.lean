/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Incoh.LocalizedLatticeFourierExchange
public import WaveTurbulence.Foundations.Flower.IncTop.Reg.SourceTemporalPhase

/-! Ported by source from C2-B-TOP `Cut2BReg.LocalizedSourceIntegral` (sha256 in COPIED-SHA256SUMS); mechanical edits only.

R66 spatially modulated scratch copy. Original SHA256 recorded in REG-COPIES.json.

# The literal localized source lattice/time integral

TARGET (incohproof2), (incohproof8–9). The normalization, global sign,
squared Wick coefficients, source input functions and temporal phase
all remain in the source operator. Its spectral identity is proved.
-/

public section
noncomputable section
open MeasureTheory
open scoped ENNReal

namespace WaveTurbulence.Flower.IncTop
open WaveTurbulence.Incoh
open WaveTurbulence.Incoh.MomentumTreeData in
/-- Literal normalized localized source operator on a source time domain. -/
@[expose] def MomentumTreeData.localizedSourceIntegralSpatial {d n m w : ℕ}
    (P : MomentumTreeData n m w) (ζ : Circle) (L γ δ : ℝ) (Q : Fin n → LayerLink d)
    (I : Set (Fin n → Fin 2 → ℝ)) (f : Fin m → Mom d → ℂ)
    (c : Fin m → Fin d → ℤ) (z : (Fin n × Fin 2) → Fin d → ℤ) (k : Mom d) : ℂ :=
  ((δ / (2 * L ^ ((d : ℝ) - γ))) ^ (2 * n) : ℝ) *
    ∫ t in I, ∑' p : (Fin n × Fin 2) → Fin d → ℤ,
      sourceTemporalPhaseSpatial L γ δ Q p t * ((ζ : ℂ) * P.localizedLeafWeight f c k
        (fun i j => latticePoint L (p (i, j))) * halfCellArrayWeight z (latticeMomentumArray L p))

open WaveTurbulence.Incoh.MomentumTreeData in
/-- Exact source identity after both lattice and time exchange with the actual spectral density. -/
theorem MomentumTreeData.localizedSourceIntegral_eq_spectralIntegralSpatial {d n m w K M : ℕ}
    (P : MomentumTreeData n m w) (ζ : Circle) (L γ δ : ℝ) (Q : Fin n → LayerLink d)
    (I : Set (Fin n → Fin 2 → ℝ)) (hI : I ⊆ Set.univ.pi (fun i => linkBox (Q i)))
    (f : Fin m → Mom d → ℂ) (c : Fin m → Fin d → ℤ)
    (z : (Fin n × Fin 2) → Fin d → ℤ) {B : ℝ}
    (hL : 0 < L) (hK : d + 1 ≤ K) (hB : 0 ≤ B)
    (h : ∀ a, Fourier.spatialNorm K M (f a) ≤ ENNReal.ofReal B) (k : Mom d) :
    (MomentumTreeData.localizedSourceIntegralSpatial (P := P)) ζ L γ δ Q I f c z k =
      ((δ / (2 * L ^ ((d : ℝ) - γ))) ^ (2 * n) : ℝ) *
        ∫ ξ : LocalizedCellIndex n m → Fin d → ℝ,
          ∑' p : (Fin n × Fin 2) → Fin d → ℤ,
            ((∫ t in I, sourceTemporalPhaseSpatial L γ δ Q p t) *
              linkArrayCutoff z (latticeMomentumArray L p)) *
              P.localizedSourceSpectralDensity ζ f c z k
                (fun i j => latticePoint L (p (i, j))) ξ := by
  classical
  let W := fun p : (Fin n × Fin 2) → Fin d → ℤ =>
    (ζ : ℂ) * P.localizedLeafWeight f c k (fun i j => latticePoint L (p (i, j))) *
      halfCellArrayWeight z (latticeMomentumArray L p)
  let S := (finite_linkCellLatticeSet hL z).toFinset
  have hW (p : (Fin n × Fin 2) → Fin d → ℤ) (hp : p ∉ S) : W p = 0 := by
    have hz : halfCellArrayWeight z (latticeMomentumArray L p) = 0 := by
      by_contra hn
      apply hp
      simpa only [S, Set.Finite.mem_toFinset] using
        mem_linkCellLatticeSet_of_halfCellArrayWeight_ne_zero L z p hn
    exact mul_eq_zero_of_right _ hz
  have hs (t : Fin n → Fin 2 → ℝ) :
      (∑' p, sourceTemporalPhaseSpatial L γ δ Q p t * W p) =
        ∑ p ∈ S, sourceTemporalPhaseSpatial L γ δ Q p t * W p :=
    tsum_eq_sum (s := S) (fun p hp => by rw [hW p hp, mul_zero])
  unfold localizedSourceIntegralSpatial
  congr 1
  change (∫ t in I, ∑' p, sourceTemporalPhaseSpatial L γ δ Q p t * W p) = _
  simp_rw [hs]
  rw [integral_finsetSum S (fun p _ => (integrableOn_sourceTemporalPhaseSpatial L γ δ Q p hI).mul_const (W p))]
  simp_rw [integral_mul_const]
  have ht : (∑' p, (∫ t in I, sourceTemporalPhaseSpatial L γ δ Q p t) * W p) =
      ∑ p ∈ S, (∫ t in I, sourceTemporalPhaseSpatial L γ δ Q p t) * W p :=
    tsum_eq_sum (s := S) (fun p hp => by rw [hW p hp, mul_zero])
  rw [← ht]
  exact P.localized_lattice_sum_eq_spectralIntegral ζ f c z hL hK hB h k
    (fun p => ∫ t in I, sourceTemporalPhaseSpatial L γ δ Q p t)

end WaveTurbulence.Flower.IncTop