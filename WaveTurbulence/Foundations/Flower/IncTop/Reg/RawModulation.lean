/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Flower.IncTop.Reg.RawCoupleAgreement
public import WaveTurbulence.Foundations.Flower.IncTop.Reg.RawTreeAgreement
public import WaveTurbulence.Foundations.Incoh.RawCoupleAgreement
public import WaveTurbulence.Foundations.Incoh.RawTreeAgreement
public import WaveTurbulence.Foundations.Cut2A.FiniteProducts

/-! Ported by source from C2-B-TOP `Cut2BReg.RawModulation` (sha256 in COPIED-SHA256SUMS); mechanical edits only.
 # Internal paired coordinates and literal raw spatial modulation

TARGET (incohproof2–8), R66. The character contains precisely the free paired
momenta. It contains no external root momentum.
-/

public section
noncomputable section
open MeasureTheory
open scoped ENNReal

namespace WaveTurbulence.Flower.IncTop
open WaveTurbulence.Incoh
/-- The `2n` free paired momenta, with their Euclidean inner product. -/
abbrev PairedMomentum (d n : ℕ) := PiLp 2 (fun _ : Fin n × Fin 2 => Mom d)

/-- Pack the free lattice coordinates; this map does not take a root momentum. -/
@[expose] def pairedLattice {d n : ℕ} (L : ℝ) (p : (Fin n × Fin 2) → Fin d → ℤ) :
    PairedMomentum d n := WithLp.toLp 2 (fun i => latticePoint L (p i))

/-- Give the previously auxiliary link shifts their intended raw-source meaning. -/
@[expose] def spatialFrequencyLinks {d n : ℕ} (Q : Fin n → LayerLink d)
    (ν : PairedMomentum d n) (i : Fin n) : LayerLink d :=
  { Q i with leftShift := ν (i, 0), rightShift := ν (i, 1) }

/-- Literal incoherency flags are independent of the character. -/
theorem incoherenceCount_spatialFrequencyLinks {d n : ℕ} (Q : Fin n → LayerLink d)
    (ν : PairedMomentum d n) : incoherenceCount (spatialFrequencyLinks Q ν) = incoherenceCount Q := rfl

/-- R66's actual internal character identity, before either lattice or clock integration. -/
theorem sourceTemporalPhaseSpatial_eq_character {d n : ℕ} (L γ δ : ℝ)
    (Q : Fin n → LayerLink d) (ν : PairedMomentum d n)
    (p : (Fin n × Fin 2) → Fin d → ℤ) (t : Fin n → Fin 2 → ℝ) :
    sourceTemporalPhaseSpatial L γ δ (spatialFrequencyLinks Q ν) p t =
      sourceTemporalPhase L γ δ Q p t *
        (Real.fourierChar (inner ℝ ν (pairedLattice L p)) : ℂ) := by
  classical
  have he (s : ℝ) : (Real.fourierChar s : ℂ) = WeylSums.e s := rfl
  simp only [sourceTemporalPhaseSpatial, sourceTemporalPhase, spatialFrequencyLinks,
    PiLp.inner_apply, pairedLattice, Fintype.sum_prod_type,
    Fin.sum_univ_two, real_inner_comm, he]
  simp only [WeylSums.e_add, WeylSums.e_sum, Finset.prod_mul_distrib]
  ring

/-- Joint continuity in all spatial frequencies and all internal clocks. -/
theorem continuous_sourceTemporalPhaseSpatial_frequency {d n : ℕ} (L γ δ : ℝ)
    (Q : Fin n → LayerLink d) (p : (Fin n × Fin 2) → Fin d → ℤ) :
    Continuous (fun z : PairedMomentum d n × (Fin n → Fin 2 → ℝ) =>
      sourceTemporalPhaseSpatial L γ δ (spatialFrequencyLinks Q z.1) p z.2) := by
  unfold sourceTemporalPhaseSpatial spatialFrequencyLinks
  apply continuous_finsetProd
  intro i _
  dsimp only
  unfold WeylSums.e
  fun_prop

open WaveTurbulence.Incoh.MomentumTreeData in
/-- Absolute lattice convergence gives a character-independent physical bound. -/
theorem MomentumTreeData.norm_sourceTimeIntegrandSpatial_le_of_summable {d n m w : ℕ}
    (P : MomentumTreeData n m w) (ζ : Circle) (L γ δ : ℝ) (Q : Fin n → LayerLink d)
    (f : Fin m → Mom d → ℂ) (k : Mom d)
    (hs : Summable (fun p : (Fin n × Fin 2) → Fin d → ℤ =>
      ‖P.sourceLeafWeight f k (fun i j => latticePoint L (p (i, j)))‖))
    (t : Fin n → Fin 2 → ℝ) :
    ‖(MomentumTreeData.sourceTimeIntegrandSpatial (P := P)) ζ L γ δ Q f k t‖ ≤
      ∑' p : (Fin n × Fin 2) → Fin d → ℤ,
        ‖P.sourceLeafWeight f k (fun i j => latticePoint L (p (i, j)))‖ := by
  have hb (p : (Fin n × Fin 2) → Fin d → ℤ) :
      ‖sourceTemporalPhaseSpatial L γ δ Q p t *
        ((ζ : ℂ) * P.sourceLeafWeight f k (fun i j => latticePoint L (p (i, j))))‖ ≤
      ‖P.sourceLeafWeight f k (fun i j => latticePoint L (p (i, j)))‖ := by
    simp only [norm_mul, Circle.norm_coe, one_mul]
    exact (mul_le_mul_of_nonneg_right (norm_sourceTemporalPhase_le_oneSpatial L γ δ Q p t)
      (norm_nonneg _)).trans_eq (one_mul _)
  exact (norm_tsum_le_tsum_norm (hs.of_nonneg_of_le (fun _ => norm_nonneg _) hb)).trans
    ((hs.of_nonneg_of_le (fun _ => norm_nonneg _) hb).tsum_le_tsum hb hs)

end WaveTurbulence.Flower.IncTop