/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.WeylSums.LocalDenominators
public import WaveTurbulence.Foundations.WeylSums.WeylLocalArcs

/-!
# Refined minor-arc moments

DH23 Lemma 6.6(2), `refinedHua`: retaining the lower denominator bound
gives an arbitrarily small-loss version of the sharp window power.
-/

public section
open MeasureTheory
namespace WaveTurbulence.WeylSums

/-- The rational envelope retains the large-denominator gain. -/
theorem integral_localArcEnvelope_le_refined {L σ T ε : ℝ} (hL : 0 < L)
    (hσ : 1 < σ) (hT : 0 < T) (hε : 0 < ε) (hσε : ε < σ-2) (N : ℕ) :
    (∫ t : ℝ, localArcEnvelope L σ N T t) ≤
      4 * arcProfileMass σ / L^2 * T * (1/(2*T))^(2-σ+ε) *
        ∑' q : ℕ, (q : ℝ)^(-1-ε) := by
  rw [integral_localArcEnvelope hL hσ]
  have hh := mul_le_mul_of_nonneg_left (sum_localNumerators_rpow_le hT hε hσε N)
    (div_nonneg (arcProfileMass_nonneg σ) (sq_nonneg L))
  convert hh using 1
  ring

/-- Refined supremum moment before normalizing its real powers. -/
theorem exists_weylSupremum_refined_integral_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ (L p ε T : ℝ), 2 ≤ L → 4 < p →
      0 < ε → ε < p/2-2 → 0 < T →
      IntegrableOn (fun t : ℝ => weylSupremum L t ^ p)
        {t : ℝ | 1 / L ≤ |t| ∧ |t| ≤ T} ∧
      (∫ t : ℝ in {t : ℝ | 1 / L ≤ |t| ∧ |t| ≤ T}, weylSupremum L t ^ p) ≤
        (C * L) ^ p * (4 * arcProfileMass (p/2) / L^2 * T *
          (1/(2*T))^(2-p/2+ε) * ∑' q : ℕ, (q : ℝ)^(-1-ε)) := by
  obtain ⟨C, hC, hpoint⟩ := exists_weylSupremum_local_arc_bound
  refine ⟨C, hC, ?_⟩
  intro L p ε T hL hp hε hεp hT
  have hLpos : 0 < L := by linarith
  have hσ : 1 < p / 2 := by linarith
  let f : ℝ → ℝ := fun t => weylSupremum L t ^ p
  let g : ℝ → ℝ := fun t => (C * L) ^ p * localArcEnvelope L (p / 2) ⌊L⌋₊ T t
  have hg : Integrable g := (integrable_localArcEnvelope hLpos hσ ⌊L⌋₊ T).const_mul _
  have hg0 (t : ℝ) : 0 ≤ g t := mul_nonneg (Real.rpow_nonneg (by positivity) _)
    (localArcEnvelope_nonneg _ _ _ _ _)
  have hle : f ≤ᵐ[volume.restrict ({t : ℝ | 1 / L ≤ |t| ∧ |t| ≤ T})] g := by
    have hnot (a : ℝ) : ∀ᵐ t : ℝ ∂volume, t ≠ a := by simp [ae_iff]
    have hm : MeasurableSet {t : ℝ | 1 / L ≤ |t| ∧ |t| ≤ T} := by measurability
    filter_upwards [ae_restrict_mem hm,
      ae_restrict_of_ae (hnot (1 / L)), ae_restrict_of_ae (hnot (-(1 / L)))] with t ht hpos hneg
    have hne : |t| ≠ 1 / L := by
      intro heq
      rcases (abs_eq (by positivity : 0 ≤ 1 / L)).mp heq with heq | heq
      · exact hpos heq
      · exact hneg heq
    exact hpoint L p T t hL (by linarith) (lt_of_le_of_ne ht.1 (Ne.symm hne)) ht.2
  have hfm : AEStronglyMeasurable f (volume.restrict ({t : ℝ | 1 / L ≤ |t| ∧ |t| ≤ T})) :=
    ((measurable_weylSupremum hLpos).pow_const p).aestronglyMeasurable
  have hf : Integrable f (volume.restrict ({t : ℝ | 1 / L ≤ |t| ∧ |t| ≤ T})) := by
    apply hg.restrict.mono' hfm
    filter_upwards [hle] with t ht
    change ‖weylSupremum L t ^ p‖ ≤ _
    rw [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (weylSupremum_nonneg hLpos t) _)]
    exact ht
  refine ⟨hf, ?_⟩
  calc
    _ ≤ ∫ t in {t : ℝ | 1 / L ≤ |t| ∧ |t| ≤ T}, g t := integral_mono_ae hf hg.restrict hle
    _ ≤ ∫ t : ℝ, g t := setIntegral_le_integral hg (Filter.Eventually.of_forall hg0)
    _ = (C * L) ^ p * ∫ t : ℝ, localArcEnvelope L (p / 2) ⌊L⌋₊ T t := integral_const_mul _ _
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (integral_localArcEnvelope_le_refined hLpos hσ hT hε hεp ⌊L⌋₊)
      (Real.rpow_nonneg (by positivity) _)

end WaveTurbulence.WeylSums
