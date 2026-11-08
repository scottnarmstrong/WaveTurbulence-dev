/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Flower.FiltProd.Replace
public import WaveTurbulence.Foundations.Flower.FiltProd.Dens
public import WaveTurbulence.Foundations.Incoh.RootEnvelope
public import WaveTurbulence.Foundations.Incoh.RootEnvelopeMass

/-! # D5b-2 FILT-PROD: the root-link envelope (twins of `RootEnvelope`, `RootEnvelopeDominates`, `RootEnvelopeMass`)

Root links receive the trivial bound `K (5L)^{2d}` (`‖φ i‖ ≤ K`); the others keep their filtered absolute values. -/

@[expose] public section
set_option autoImplicit false
noncomputable section
open MeasureTheory Set
open scoped ENNReal

namespace WaveTurbulence.Flower.FiltProd
open WaveTurbulence.Incoh WaveTurbulence.Flower.FiltLink WaveTurbulence.Flower.FiltSrc


/-- The envelope retains every link factor except those touched by the two roots. -/
def RootCoordinates.envelopeFactorFilt {d n : ℕ} {r : ℕ} (R : RootCoordinates n r) (K : ℝ)
    (L γ δ : ℝ) (Q : Fin n → LayerLink d) (φ : Fin n → ℝ → ℂ) (i : Fin n) (t : Fin 2 → ℝ) : ℝ≥0∞ :=
  if i ∈ R.rootLinks then ENNReal.ofReal (K * (5 * L) ^ (2 * d)) else ‖filtLinkTimeFactor L γ δ (Q i) (φ i) t‖ₑ

/-- The literal root-link envelope on the source product of layer boxes. -/
def RootCoordinates.envelopeFilt {d n : ℕ} {r : ℕ} (R : RootCoordinates n r) (K : ℝ)
    (L γ δ : ℝ) (Q : Fin n → LayerLink d) (φ : Fin n → ℝ → ℂ) (t : Fin n → Fin 2 → ℝ) : ℝ≥0∞ :=
  (univ.pi (fun i => linkBox (Q i))).indicator (fun t => ∏ i, RootCoordinates.envelopeFactorFilt R K L γ δ Q φ i (t i)) t

theorem RootCoordinates.measurable_envelopeFilt {d n : ℕ} {r : ℕ} (R : RootCoordinates n r) (K : ℝ)
    {L : ℝ} (hL : 0 < L) (γ δ : ℝ) (Q : Fin n → LayerLink d) (φ : Fin n → ℝ → ℂ) :
    Measurable (RootCoordinates.envelopeFilt R K L γ δ Q φ) := by
  apply Measurable.indicator _ (MeasurableSet.univ_pi fun i => measurableSet_Icc)
  apply Finset.measurable_prod
  intro i _
  by_cases hi : i ∈ R.rootLinks
  · simp only [RootCoordinates.envelopeFactorFilt, hi, ite_true]
    exact measurable_const
  · simp only [RootCoordinates.envelopeFactorFilt, hi, ite_false]
    exact ((continuous_filtLinkTimeFactor hL γ δ (Q i) (φ i)).measurable.comp (measurable_pi_apply i)).enorm

/-- The envelope is exactly independent of the roots on their unit box. -/
theorem RootCoordinates.envelope_factorizationFilt {d n : ℕ} {r : ℕ} (R : RootCoordinates n r) (K : ℝ)
    (L γ δ : ℝ) (Q : Fin n → LayerLink d) (φ : Fin n → ℝ → ℂ) (t : Fin r → ℝ) (u : Fin R.restCount → ℝ) :
    RootCoordinates.envelopeFilt R K L γ δ Q φ (R.equiv.symm (t, u)) =
      (R.rootBox Q).indicator (fun _ => RootCoordinates.envelopeFilt R K L γ δ Q φ (R.equiv.symm (R.baseRootTimes Q, u))) t := by
  by_cases ht : t ∈ R.rootBox Q
  · rw [Set.indicator_of_mem (s := R.rootBox Q) ht]
    by_cases hu : u ∈ R.restBox Q
    · have hB := (R.equiv_symm_mem_linkBoxes Q t u).mpr ⟨ht, hu⟩
      have hB₀ := (R.equiv_symm_mem_linkBoxes Q (R.baseRootTimes Q) u).mpr ⟨R.baseRootTimes_mem Q, hu⟩
      rw [RootCoordinates.envelopeFilt, RootCoordinates.envelopeFilt, Set.indicator_of_mem hB, Set.indicator_of_mem hB₀]
      apply Finset.prod_congr rfl
      intro i _
      by_cases hi : i ∈ R.rootLinks
      · simp only [RootCoordinates.envelopeFactorFilt, hi, ite_true]
      · simp only [RootCoordinates.envelopeFactorFilt, hi, ite_false]
        rw [R.equiv_symm_eq_of_notMem_rootLinks t (R.baseRootTimes Q) u i hi]
    · have hB : R.equiv.symm (t, u) ∉ univ.pi (fun i => linkBox (Q i)) := by
        intro h; exact hu ((R.equiv_symm_mem_linkBoxes Q t u).mp h).2
      have hB₀ : R.equiv.symm (R.baseRootTimes Q, u) ∉ univ.pi (fun i => linkBox (Q i)) := by
        intro h; exact hu ((R.equiv_symm_mem_linkBoxes Q (R.baseRootTimes Q) u).mp h).2
      rw [RootCoordinates.envelopeFilt, RootCoordinates.envelopeFilt, Set.indicator_of_notMem hB, Set.indicator_of_notMem hB₀]
  · have hB : R.equiv.symm (t, u) ∉ univ.pi (fun i => linkBox (Q i)) := by
      intro h; exact ht ((R.equiv_symm_mem_linkBoxes Q t u).mp h).1
    rw [RootCoordinates.envelopeFilt, Set.indicator_of_notMem hB, Set.indicator_of_notMem (s := R.rootBox Q) ht]

/-- Each root fiber of the literal envelope is bounded by its full absolute integral. -/
theorem RootCoordinates.lintegral_envelope_fiber_leFilt {d n : ℕ} {r : ℕ} (R : RootCoordinates n r) (K : ℝ)
    {L : ℝ} (hL : 0 < L) (γ δ : ℝ) (Q : Fin n → LayerLink d) (φ : Fin n → ℝ → ℂ) (t : Fin r → ℝ) :
    (∫⁻ u, RootCoordinates.envelopeFilt R K L γ δ Q φ (R.equiv.symm (t, u))) ≤ ∫⁻ v, RootCoordinates.envelopeFilt R K L γ δ Q φ v := by
  have hG := (RootCoordinates.measurable_envelopeFilt R K hL γ δ Q φ).comp R.equiv.symm.measurable
  have h := lintegral_fiber_le_of_unit_box_factorization measurableSet_Icc (R.volume_rootBox Q)
    hG (RootCoordinates.envelope_factorizationFilt R K L γ δ Q φ) t
  exact h.trans_eq (R.measurePreserving.symm.lintegral_comp_emb R.equiv.symm.measurableEmbedding
    (RootCoordinates.envelopeFilt R K L γ δ Q φ))



/-- Root-link removal dominates the literal indicator times the oscillatory product. -/
theorem RootCoordinates.enorm_indicator_product_le_envelopeFilt {d n : ℕ} {r : ℕ} (R : RootCoordinates n r) (K : ℝ)
    {L : ℝ} (hL : 1 ≤ L) (γ δ : ℝ) (Q : Fin n → LayerLink d) (φ : Fin n → ℝ → ℂ)
    (hK : 0 ≤ K) (hB : ∀ i u, ‖φ i u‖ ≤ K)
    {I : Set (Fin n → Fin 2 → ℝ)} (hbox : I ⊆ univ.pi (fun i => linkBox (Q i)))
    (t : Fin n → Fin 2 → ℝ) :
    ‖I.indicator (fun t => ∏ i, filtLinkTimeFactor L γ δ (Q i) (φ i) (t i)) t‖ₑ ≤ RootCoordinates.envelopeFilt R K L γ δ Q φ t := by
  by_cases ht : t ∈ I
  · rw [Set.indicator_of_mem (s := I) ht, RootCoordinates.envelopeFilt, Set.indicator_of_mem (hbox ht)]
    rw [← ofReal_norm, norm_prod, ENNReal.ofReal_prod_of_nonneg (fun _ _ => norm_nonneg _)]
    apply Finset.prod_le_prod
    intro i _
    by_cases hi : i ∈ R.rootLinks
    · rw [RootCoordinates.envelopeFactorFilt, ite_eq_left hi]
      apply ENNReal.ofReal_le_ofReal
      exact norm_filtLinkLatticeSum_le hL _ _ (φ i) hK (hB i)
    · rw [RootCoordinates.envelopeFactorFilt, ite_eq_right hi, ofReal_norm]
  · rw [Set.indicator_of_notMem (s := I) ht, enorm_zero]
    exact bot_le

/-- The actual normalized root marginal is bounded by the integral of its root-link envelope. -/
theorem RootCoordinates.enorm_linkDensity_le_envelopeFilt {d n : ℕ} {r : ℕ} (R : RootCoordinates n r) (K : ℝ)
    {L δ : ℝ} (hL : 1 ≤ L) (hδ : 0 < δ) (γ : ℝ) (Q : Fin n → LayerLink d) (φ : Fin n → ℝ → ℂ)
    (hK : 0 ≤ K) (hB : ∀ i u, ‖φ i u‖ ≤ K)
    {I : Set (Fin n → Fin 2 → ℝ)} (hbox : I ⊆ univ.pi (fun i => linkBox (Q i)))
    (t : Fin r → ℝ) :
    ‖RootCoordinates.linkDensityFilt R L γ δ Q φ I t‖ₑ ≤
      ENNReal.ofReal ((δ / (2 * L ^ ((d : ℝ) - γ))) ^ (2 * n)) * ∫⁻ v, RootCoordinates.envelopeFilt R K L γ δ Q φ v := by
  have hLp := zero_lt_one.trans_le hL
  have hc : 0 ≤ (δ / (2 * L ^ ((d : ℝ) - γ))) ^ (2 * n) := by positivity
  have hnorm : ‖((((δ / (2 * L ^ ((d : ℝ) - γ))) ^ (2 * n) : ℝ) : ℂ))‖ₑ =
      ENNReal.ofReal ((δ / (2 * L ^ ((d : ℝ) - γ))) ^ (2 * n)) := by
    rw [← ofReal_norm]
    simp only [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hc]
  calc
    _ ≤ ∫⁻ u, ‖normalizedLinkIntegrandFilt L γ δ Q φ I (R.equiv.symm (t, u))‖ₑ :=
      enorm_integral_le_lintegral_enorm _
    _ ≤ ∫⁻ u, ENNReal.ofReal ((δ / (2 * L ^ ((d : ℝ) - γ))) ^ (2 * n)) *
        RootCoordinates.envelopeFilt R K L γ δ Q φ (R.equiv.symm (t, u)) := by
      apply lintegral_mono
      intro u
      dsimp only
      rw [normalizedLinkIntegrandFilt, enorm_mul, hnorm]
      exact mul_le_mul' le_rfl (RootCoordinates.enorm_indicator_product_le_envelopeFilt R K hL γ δ Q φ hK hB hbox _)
    _ = ENNReal.ofReal ((δ / (2 * L ^ ((d : ℝ) - γ))) ^ (2 * n)) *
        ∫⁻ u, RootCoordinates.envelopeFilt R K L γ δ Q φ (R.equiv.symm (t, u)) :=
      lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    _ ≤ _ := mul_le_mul' le_rfl (RootCoordinates.lintegral_envelope_fiber_leFilt R K hLp γ δ Q φ t)



private def envelopeComplexFactor {d n : ℕ} {r : ℕ} (R : RootCoordinates n r) (K : ℝ) (L γ δ : ℝ)
    (Q : Fin n → LayerLink d) (φ : Fin n → ℝ → ℂ) (i : Fin n) (t : Fin 2 → ℝ) : ℂ :=
  if i ∈ R.rootLinks then (((K * (5 * L) ^ (2 * d) : ℝ) : ℂ)) else filtLinkTimeFactor L γ δ (Q i) (φ i) t

private theorem enorm_envelopeComplexFactor {d n : ℕ} {r : ℕ} (R : RootCoordinates n r) (K : ℝ) {L : ℝ}
    (hL : 1 ≤ L) (γ δ : ℝ) (Q : Fin n → LayerLink d) (φ : Fin n → ℝ → ℂ) (hK : 0 ≤ K) (i : Fin n)
    (t : Fin 2 → ℝ) :
    ‖envelopeComplexFactor R K L γ δ Q φ i t‖ₑ = RootCoordinates.envelopeFactorFilt R K L γ δ Q φ i t := by
  by_cases hi : i ∈ R.rootLinks
  · simp only [envelopeComplexFactor, RootCoordinates.envelopeFactorFilt, hi, ite_true]
    rw [← ofReal_norm, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hK (by positivity))]
  · simp only [envelopeComplexFactor, RootCoordinates.envelopeFactorFilt, hi, ite_false]

/-- The root envelope has only the selected trivial masses, with all other link masses unchanged. -/
theorem RootCoordinates.lintegral_envelope_le_replacedMassFilt {d n : ℕ} {r : ℕ} (R : RootCoordinates n r) (K : ℝ)
    {L : ℝ} (hL : 1 ≤ L) (γ δ : ℝ) (Q : Fin n → LayerLink d) (φ : Fin n → ℝ → ℂ) (hK : 0 ≤ K) :
    (∫⁻ t, RootCoordinates.envelopeFilt R K L γ δ Q φ t) ≤ ∏ i, replacedLinkMassFilt K L γ δ Q φ R.rootLinks i := by
  have hLp := zero_lt_one.trans_le hL
  let f := envelopeComplexFactor R K L γ δ Q φ
  have hf (i : Fin n) : IntegrableOn (f i) (linkBox (Q i)) := by
    change IntegrableOn (fun t : Fin 2 → ℝ => if i ∈ R.rootLinks then
      (((K * (5 * L) ^ (2 * d) : ℝ) : ℂ)) else filtLinkTimeFactor L γ δ (Q i) (φ i) t) (linkBox (Q i))
    by_cases hi : i ∈ R.rootLinks
    · simp only [hi, ite_true]
      exact continuous_const.integrableOn_Icc
    · simpa only [hi, ite_false] using integrableOn_filtLinkTimeFactor hLp γ δ (Q i) (φ i)
  have heq (t : Fin n → Fin 2 → ℝ) :
      RootCoordinates.envelopeFilt R K L γ δ Q φ t = (univ.pi (fun i => linkBox (Q i))).indicator (fun t => ‖∏ i, f i (t i)‖ₑ) t := by
    unfold RootCoordinates.envelopeFilt
    by_cases ht : t ∈ univ.pi (fun i => linkBox (Q i))
    · rw [Set.indicator_of_mem ht, Set.indicator_of_mem ht]
      rw [← ofReal_norm, norm_prod, ENNReal.ofReal_prod_of_nonneg (fun _ _ => norm_nonneg _)]
      apply Finset.prod_congr rfl
      intro i _
      exact (enorm_envelopeComplexFactor R K hL γ δ Q φ hK i (t i)).symm.trans (ofReal_norm _).symm
    · rw [Set.indicator_of_notMem ht, Set.indicator_of_notMem ht]
  simp_rw [heq]
  have hbox : MeasurableSet (univ.pi (fun i => linkBox (Q i))) :=
    MeasurableSet.univ_pi fun i => (show MeasurableSet (linkBox (Q i)) from measurableSet_Icc)
  rw [lintegral_indicator hbox]
  apply (lintegral_pi_product_enorm_le (μ := fun _ => volume) (Subset.rfl) hf).trans_eq
  apply Finset.prod_congr rfl
  intro i _
  by_cases hi : i ∈ R.rootLinks
  · simp only [f, envelopeComplexFactor, replacedLinkMassFilt, hi, ite_true]
    rw [← ofReal_norm, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hK (by positivity)),
      lintegral_const, Measure.restrict_apply_univ, volume_linkBox, mul_one]
  · simp only [f, envelopeComplexFactor, replacedLinkMassFilt, hi, ite_false]
    rw [filtLayerLinkMass_eq_ofReal_integral hLp γ δ (Q i) (φ i)]
    simp_rw [← ofReal_norm]
    exact (ofReal_integral_eq_lintegral_ofReal (integrableOn_filtLinkTimeFactor hLp γ δ (Q i) (φ i)).norm
      (Filter.Eventually.of_forall fun _ => norm_nonneg _)).symm


end WaveTurbulence.Flower.FiltProd
