/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.SumintPar.SourceTimeNormFactors

/-!
# Time measurability of the actual independent source factors

Every oscillatory factor has fixed finite lattice support. Its time
dependence is continuous even when the linear momentum modulations vary
with the local times. Gap amplitudes are measurable at every real exponent.
-/

@[expose] public section
set_option autoImplicit false

open MeasureTheory

namespace WaveTurbulence.SumintPar

/-- Each literal lattice summand is continuous in all source input times. -/
theorem continuous_sourceFactorTerm_time {d : ℕ} (D : SumintDatum d) (L γ δ : ℝ)
    (p : D.S.VIdx → Fin d → ℝ) (ν : D.S.VIdx → Mom d) (r : Mom d) (t : ℝ)
    (a : FactorIdx D.S) (n : FactorInput D.S (Fin d → ℤ) a) :
    Continuous (fun τ => sourceFactorTerm D L γ δ p ν r t τ a n) := by
  rcases a with i | (a | i)
  · change Continuous (fun τ => linearFactorTerm D L γ δ p ν r t τ i n)
    unfold linearFactorTerm linearFactorFrequency
    simp_rw [Real.fourierChar_apply]
    fun_prop
  · change Continuous (fun τ => pairFactorTerm D L γ δ p ν r t τ a n)
    unfold pairFactorTerm pairFactorFrequencyX pairFactorFrequencyY pairFactorTime
    simp_rw [Real.fourierChar_apply]
    fun_prop
  · change Continuous (fun τ => normalFactorTerm D L γ δ p ν r t τ i n)
    unfold normalFactorTerm normalFactorFrequency normalFactorTime
    simp_rw [Real.fourierChar_apply]
    fun_prop

/-- The full oscillatory sum of each independent factor is continuous in input times. -/
theorem continuous_tsum_sourceFactorTerm_time {d : ℕ} (D : SumintDatum d) {L : ℝ}
    (hL : 0 < L) (γ δ : ℝ) (p : D.S.VIdx → Fin d → ℝ)
    (ν : D.S.VIdx → Mom d) (r : Mom d) (t : ℝ) (a : FactorIdx D.S) :
    Continuous (fun τ => ∑' n : FactorInput D.S (Fin d → ℤ) a,
      sourceFactorTerm D L γ δ p ν r t τ a n) := by
  classical
  have he : (fun τ => ∑' n : FactorInput D.S (Fin d → ℤ) a,
      sourceFactorTerm D L γ δ p ν r t τ a n) =
      fun τ => ∑ n ∈ sourceFactorSupport D L p a, sourceFactorTerm D L γ δ p ν r t τ a n := by
    funext τ
    exact tsum_eq_sum (fun n hn => sourceFactorTerm_eq_zero_of_not_support D hL γ δ p ν r t τ a n hn)
  rw [he]
  exact continuous_finsetSum _ (fun n _ => continuous_sourceFactorTerm_time D L γ δ p ν r t a n)

/-- Inserting one local coordinate block and setting the others to zero is measurable. -/
theorem measurable_insert_local_times (S : SumintShape) (a : FactorIdx S) :
    Measurable (fun z : FactorCoordinate S a → ℝ =>
      (timeCoordinateGrouping S).symm (Pi.single a z)) := by
  classical
  apply (timeCoordinateGrouping S).symm.measurable.comp
  apply measurable_pi_iff.mpr
  intro b
  by_cases h : b = a
  · subst b
    have he : (fun z : FactorCoordinate S a → ℝ =>
        (Pi.single a z : (b : FactorIdx S) → FactorCoordinate S b → ℝ) a) = id := by
      funext z
      simp only [Pi.single_eq_same,id_eq]
    rw [he]
    exact measurable_id
  · have he : (fun z : FactorCoordinate S a → ℝ => (Pi.single a z : (b : FactorIdx S) → FactorCoordinate S b → ℝ) b) = fun _ => 0 := by
      funext z
      simp [h]
    rw [he]
    exact measurable_const

/-- The local norm factors are measurable under the actual local product Lebesgue measure. -/
theorem measurable_plainTimeNormFactor {d : ℕ} (D : SumintDatum d) {L : ℝ} (hL : 0 < L)
    (γ δ : ℝ) (p : D.S.VIdx → Fin d → ℝ) (ν : D.S.VIdx → Mom d)
    (r : Mom d) (t : ℝ) (a : FactorIdx D.S) :
    Measurable (plainTimeNormFactor D L γ δ p ν r t a) := by
  classical
  have he (z : FactorCoordinate D.S a → ℝ) :
      plainTimeNormFactor D L γ δ p ν r t a z =
      ‖∑' n : FactorInput D.S (Fin d → ℤ) a,
        sourceFactorTerm D L γ δ p ν r t
          ((timeCoordinateGrouping D.S).symm (Pi.single a z)) a n‖ := by
    rw [norm_tsum_sourceFactorTerm_eq_plainTimeNormFactor]
    simp only [MeasurableEquiv.apply_symm_apply,Pi.single_eq_same]
  simp_rw [funext he]
  exact (continuous_tsum_sourceFactorTerm_time D hL γ δ p ν r t a).norm.measurable.comp
    (measurable_insert_local_times D.S a)

/-- The exact source case-(c) assignment is measurable, including negative exponents. -/
theorem measurable_timeGapFactor {d : ℕ} (D : SumintDatum d) (η : ℝ) (a : FactorIdx D.S) :
    Measurable (timeGapFactor D η a) := by
  classical
  rcases a with i | (a | i)
  · exact measurable_const
  · change Measurable (fun z : Fin 2 → ℝ => pairGapAmplitude D η a (z 0,z 1))
    unfold pairGapAmplitude
    split_ifs <;> fun_prop
  · exact measurable_const

/-- All independent factors in the exact source norm product are measurable. -/
theorem measurable_sourceTimeNormFactor {d : ℕ} (D : SumintDatum d) {L : ℝ} (hL : 0 < L)
    (γ δ η : ℝ) (p : D.S.VIdx → Fin d → ℝ) (ν : D.S.VIdx → Mom d)
    (r : Mom d) (t : ℝ) (a : FactorIdx D.S) :
    Measurable (sourceTimeNormFactor D L γ δ η p ν r t a) :=
  (measurable_timeGapFactor D η a).mul (measurable_plainTimeNormFactor D hL γ δ p ν r t a)

end WaveTurbulence.SumintPar
