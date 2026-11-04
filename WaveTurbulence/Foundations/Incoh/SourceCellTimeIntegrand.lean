/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Incoh.RawSourceIntegral

/-!
# Actual time series of one smooth source localization cell

Its lattice support is finite independently of time. The exact phase
bound gives an absolute majorant independent of all vertex clocks.
-/

public section
noncomputable section
open MeasureTheory
open scoped ENNReal

namespace WaveTurbulence.Incoh

/-- Literal signed time series of one actual source cell. -/
@[expose] def MomentumTreeData.sourceCellTimeIntegrand {d n m w : ℕ}
    (P : MomentumTreeData n m w) (ζ : Circle) (L γ δ : ℝ) (Q : Fin n → LayerLink d)
    (f : Fin m → Mom d → ℂ)
    (S : (Fin m → Fin d → ℤ) → Finset ((Fin n × Fin 2) → Fin d → ℤ))
    (k : Mom d) (u : SourceCellIndex S) (t : Fin n → Fin 2 → ℝ) : ℂ :=
  ∑' p : (Fin n × Fin 2) → Fin d → ℤ, sourceTemporalPhase L γ δ Q p t *
    ((ζ : ℂ) * P.sourceCellWeight f S k (fun i j => latticePoint L (p (i, j))) u)

/-- The actual lattice support of one source cell is finite. -/
theorem MomentumTreeData.finite_support_sourceCellWeight_lattice {d n m w : ℕ}
    (P : MomentumTreeData n m w) {L : ℝ} (hL : 0 < L) (f : Fin m → Mom d → ℂ)
    (S : (Fin m → Fin d → ℤ) → Finset ((Fin n × Fin 2) → Fin d → ℤ))
    (k : Mom d) (u : SourceCellIndex S) :
    (Function.support (fun p : (Fin n × Fin 2) → Fin d → ℤ =>
      P.sourceCellWeight f S k (fun i j => latticePoint L (p (i, j))) u)).Finite :=
  (finite_support_halfCellArrayWeight_lattice hL u.2.val).subset
    (fun p hp hz => hp (by
      change halfCellArrayWeight u.2.val (latticeMomentumArray L p) = 0 at hz
      change P.localizedLeafWeight f u.1 k (fun i j => latticePoint L (p (i, j))) *
        halfCellArrayWeight u.2.val (latticeMomentumArray L p) = 0
      exact mul_eq_zero_of_right _ hz))

/-- Every actual cell time series is continuous, by its proved finite lattice support. -/
theorem MomentumTreeData.continuous_sourceCellTimeIntegrand {d n m w : ℕ}
    (P : MomentumTreeData n m w) (ζ : Circle) {L : ℝ} (hL : 0 < L) (γ δ : ℝ)
    (Q : Fin n → LayerLink d) (f : Fin m → Mom d → ℂ)
    (S : (Fin m → Fin d → ℤ) → Finset ((Fin n × Fin 2) → Fin d → ℤ))
    (k : Mom d) (u : SourceCellIndex S) :
    Continuous (P.sourceCellTimeIntegrand ζ L γ δ Q f S k u) := by
  have hs : Summable (fun p : (Fin n × Fin 2) → Fin d → ℤ =>
      ‖P.sourceCellWeight f S k (fun i j => latticePoint L (p (i, j))) u‖) :=
    summable_of_hasFiniteSupport ((P.finite_support_sourceCellWeight_lattice hL f S k u).subset
      (fun p hp hz => hp (by
        dsimp only at hz
        change ‖_‖ = 0
        rw [hz, norm_zero])))
  apply continuous_tsum
  · intro p
    exact (continuous_sourceTemporalPhase L γ δ Q p).mul continuous_const
  · exact hs
  · intro p t
    simp only [norm_mul, Circle.norm_coe, one_mul]
    exact (mul_le_mul_of_nonneg_right (norm_sourceTemporalPhase_le_one L γ δ Q p t)
      (norm_nonneg _)).trans_eq (one_mul _)

/-- A clock-independent absolute bound for every actual source cell time series. -/
theorem MomentumTreeData.enorm_sourceCellTimeIntegrand_le {d n m w : ℕ}
    (P : MomentumTreeData n m w) (ζ : Circle) (L γ δ : ℝ) (Q : Fin n → LayerLink d)
    (f : Fin m → Mom d → ℂ)
    (S : (Fin m → Fin d → ℤ) → Finset ((Fin n × Fin 2) → Fin d → ℤ))
    (k : Mom d) (u : SourceCellIndex S) (t : Fin n → Fin 2 → ℝ) :
    ‖P.sourceCellTimeIntegrand ζ L γ δ Q f S k u t‖ₑ ≤
      ∑' p : (Fin n × Fin 2) → Fin d → ℤ,
        ‖P.sourceCellWeight f S k (fun i j => latticePoint L (p (i, j))) u‖ₑ := by
  apply enorm_tsum_le_tsum_enorm.trans
  apply ENNReal.tsum_le_tsum
  intro p
  have hφ : ‖sourceTemporalPhase L γ δ Q p t‖ₑ ≤ 1 := by
    rw [← ofReal_norm]
    simpa only [ENNReal.ofReal_one] using ENNReal.ofReal_le_ofReal (norm_sourceTemporalPhase_le_one L γ δ Q p t)
  have hζ : ‖(ζ : ℂ)‖ₑ = 1 := by rw [← ofReal_norm, Circle.norm_coe, ENNReal.ofReal_one]
  rw [enorm_mul, enorm_mul, hζ, one_mul]
  exact (mul_le_mul' hφ le_rfl).trans_eq (one_mul _)

end WaveTurbulence.Incoh
