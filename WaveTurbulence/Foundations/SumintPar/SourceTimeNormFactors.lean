/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.SumintPar.SourceTimeFactors
public import WaveTurbulence.Foundations.SumintPar.SourceFactorization
public import WaveTurbulence.Foundations.SumintPar.CaseCAmplitude
public import WaveTurbulence.Foundations.SumintPar.TimeFactorCoordinates

/-!
# Exact nonnegative time-factor decomposition of the source cutoff sum

Case-(c) amplitudes belong to their first pairs. Every remaining factor
is the modulus of its local oscillatory sum. This literal identity is
formed before any time restrictions are discarded or gains estimated.
-/

@[expose] public section
set_option autoImplicit false

namespace WaveTurbulence.SumintPar

/-- Modulus of the oscillatory sum belonging to a single local time factor. -/
@[expose] noncomputable def plainTimeNormFactor {d : ℕ} (D : SumintDatum d) (L γ δ : ℝ)
    (p : D.S.VIdx → Fin d → ℝ) (ν : D.S.VIdx → Mom d) (r : Mom d) (t : ℝ) :
    (a : FactorIdx D.S) → (FactorCoordinate D.S a → ℝ) → ℝ
  | .inl i,z => ‖linearTimeSum D L γ δ p ν r t i (z 0)‖
  | .inr (.inl a),z => ‖pairTimeSum D L γ δ p ν r t a (z 0,z 1)‖
  | .inr (.inr i),z => ‖normalTimeSum D L γ δ p ν r t i z‖

/-- The independent case multiplier, equal to one except at the first case-(c) pair. -/
@[expose] noncomputable def timeGapFactor {d : ℕ} (D : SumintDatum d) (η : ℝ) :
    (a : FactorIdx D.S) → (FactorCoordinate D.S a → ℝ) → ℝ
  | .inl _,_ => 1
  | .inr (.inl a),z => pairGapAmplitude D η a (z 0,z 1)
  | .inr (.inr _),_ => 1

/-- The full nonnegative local factor of the source cutoff sum. -/
@[expose] noncomputable def sourceTimeNormFactor {d : ℕ} (D : SumintDatum d) (L γ δ η : ℝ)
    (p : D.S.VIdx → Fin d → ℝ) (ν : D.S.VIdx → Mom d) (r : Mom d) (t : ℝ)
    (a : FactorIdx D.S) (z : FactorCoordinate D.S a → ℝ) : ℝ :=
  timeGapFactor D η a z * plainTimeNormFactor D L γ δ p ν r t a z

/-- Each oscillatory factor norm is exactly its local-time norm factor. -/
theorem norm_tsum_sourceFactorTerm_eq_plainTimeNormFactor {d : ℕ} (D : SumintDatum d)
    (L γ δ : ℝ) (p : D.S.VIdx → Fin d → ℝ) (ν : D.S.VIdx → Mom d) (r : Mom d) (t : ℝ)
    (τ : D.S.TVar → ℝ) (a : FactorIdx D.S) :
    ‖∑' n : FactorInput D.S (Fin d → ℤ) a, sourceFactorTerm D L γ δ p ν r t τ a n‖ =
      plainTimeNormFactor D L γ δ p ν r t a (timeCoordinateGrouping D.S τ a) := by
  rcases a with i | (a | i)
  · exact congrArg norm (tsum_linearFactorTerm_eq_timeSum D L γ δ p ν r t τ i)
  · exact congrArg norm (tsum_pairFactorTerm_eq_timeSum D L γ δ p ν r t τ a)
  · exact congrArg norm (tsum_normalFactorTerm_eq_timeSum D L γ δ p ν r t τ i)

/-- The product of independent gap factors is exactly the source phase modulus. -/
theorem prod_timeGapFactor_eq_norm_phase {d : ℕ} (D : SumintDatum d) (L γ δ η : ℝ)
    (r : Mom d) (t : ℝ) (τ : D.S.TVar → ℝ) :
    (∏ a : FactorIdx D.S, timeGapFactor D η a (timeCoordinateGrouping D.S τ a)) =
      ‖D.phase L γ δ η (fun _ => 0) r t τ‖ := by
  classical
  rw [norm_phase_eq_pair_gap_product,Fintype.prod_sum_type,Fintype.prod_sum_type]
  simp only [timeGapFactor,Finset.prod_const_one,one_mul,mul_one]
  rfl

/-- TARGET sumint Step 2: exact separation into the nonnegative local time factors. -/
theorem norm_cutoffPhaseSum_eq_time_factor_product {d : ℕ} (D : SumintDatum d)
    {L : ℝ} (hL : 0 < L) (γ δ η : ℝ) (p : D.S.VIdx → Fin d → ℝ)
    (ν : D.S.VIdx → Mom d) (r : Mom d) (t : ℝ) (τ : D.S.TVar → ℝ) :
    ‖cutoffPhaseSum D L γ δ η p ν r t τ‖ =
      ∏ a : FactorIdx D.S, sourceTimeNormFactor D L γ δ η p ν r t a
        (timeCoordinateGrouping D.S τ a) := by
  rw [norm_cutoffPhaseSum_eq_prod_factors D hL γ δ η p ν r t τ]
  simp_rw [norm_tsum_sourceFactorTerm_eq_plainTimeNormFactor]
  simp only [sourceTimeNormFactor,Finset.prod_mul_distrib]
  rw [prod_timeGapFactor_eq_norm_phase]

end WaveTurbulence.SumintPar
