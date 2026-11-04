/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Incoh.LinkArrayCutoff

/-!
# Exact lattice/Fourier exchange for an actual localized source term

TARGET (incohproof8–9). The analytic cutoff has a common finite lattice
support, allowing exchange with the actual integrable Fourier density.
The coefficient may include the source Wick factor and temporal phase.
-/

public section
noncomputable section
open MeasureTheory WithLp
open scoped ENNReal

namespace WaveTurbulence.Incoh

/-- The literal localized lattice sum equals its cutoff-supported spectral integral.
The arbitrary coefficient is a transport parameter, not an assumed norm bound. -/
theorem MomentumTreeData.localized_lattice_sum_eq_spectralIntegral {d n m w K M : ℕ}
    (P : MomentumTreeData n m w) (ζ : Circle) (f : Fin m → Mom d → ℂ)
    (c : Fin m → Fin d → ℤ) (z : (Fin n × Fin 2) → Fin d → ℤ)
    {B L : ℝ} (hL : 0 < L) (hK : d + 1 ≤ K) (hB : 0 ≤ B)
    (h : ∀ a, Fourier.spatialNorm K M (f a) ≤ ENNReal.ofReal B)
    (k : Mom d) (a : ((Fin n × Fin 2) → Fin d → ℤ) → ℂ) :
    (∑' p : (Fin n × Fin 2) → Fin d → ℤ,
      a p * ((ζ : ℂ) * P.localizedLeafWeight f c k
        (fun i j => latticePoint L (p (i, j))) * halfCellArrayWeight z (latticeMomentumArray L p))) =
    ∫ ξ : LocalizedCellIndex n m → Fin d → ℝ,
      ∑' p : (Fin n × Fin 2) → Fin d → ℤ,
        (a p * linkArrayCutoff z (latticeMomentumArray L p)) *
          P.localizedSourceSpectralDensity ζ f c z k
            (fun i j => latticePoint L (p (i, j))) ξ := by
  classical
  let S := (finite_linkCellLatticeSet hL z).toFinset
  have hS (p : (Fin n × Fin 2) → Fin d → ℤ) (hp : p ∉ S) :
      linkArrayCutoff z (latticeMomentumArray L p) = 0 :=
    linkArrayCutoff_eq_zero_of_not_mem L z p (by simpa only [S, Set.Finite.mem_toFinset] using hp)
  have hw (p : (Fin n × Fin 2) → Fin d → ℤ) (hp : p ∉ S) :
      halfCellArrayWeight z (latticeMomentumArray L p) = 0 := by
    have he := halfCellArrayWeight_mul_linkArrayCutoff z (latticeMomentumArray L p)
    rw [hS p hp, mul_zero] at he
    exact he.symm
  rw [tsum_eq_sum (s := S) (fun p hp => by rw [hw p hp, mul_zero, mul_zero])]
  have hright : (fun ξ : LocalizedCellIndex n m → Fin d → ℝ =>
      ∑' p : (Fin n × Fin 2) → Fin d → ℤ,
        (a p * linkArrayCutoff z (latticeMomentumArray L p)) *
          P.localizedSourceSpectralDensity ζ f c z k (fun i j => latticePoint L (p (i, j))) ξ) =
      fun ξ => ∑ p ∈ S, (a p * linkArrayCutoff z (latticeMomentumArray L p)) *
          P.localizedSourceSpectralDensity ζ f c z k (fun i j => latticePoint L (p (i, j))) ξ := by
    funext ξ
    exact tsum_eq_sum (s := S) (fun p hp => by rw [hS p hp, mul_zero, zero_mul])
  rw [hright, integral_finsetSum S (fun p _ =>
    (P.integrable_localizedSourceSpectralDensity ζ f c z hK hB h k
      (fun i j => latticePoint L (p (i, j)))).const_mul _)]
  apply Finset.sum_congr rfl
  intro p _
  rw [integral_const_mul, ← P.signed_localizedLeafWeight_eq_spectralIntegral ζ f c z hK hB h k]
  have he := halfCellArrayWeight_mul_linkArrayCutoff z (latticeMomentumArray L p)
  change _ = _ * ((ζ : ℂ) * P.localizedLeafWeight f c k
    (fun i j => latticePoint L (p (i, j))) * halfCellArrayWeight z (latticeMomentumArray L p))
  calc
    _ = a p * ((ζ : ℂ) * P.localizedLeafWeight f c k
        (fun i j => latticePoint L (p (i, j))) *
          (halfCellArrayWeight z (latticeMomentumArray L p) *
            linkArrayCutoff z (latticeMomentumArray L p))) := by rw [he]
    _ = _ := by ring

end WaveTurbulence.Incoh
