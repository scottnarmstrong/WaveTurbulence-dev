/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.RegAsymp.TreeRootLeafMixture
public import Mathlib.MeasureTheory.Integral.Bochner.SumMeasure

/-! # Actual integrability and counting-measure Fubini for the moving-root tree scalar -/

public section
noncomputable section
namespace WaveTurbulence.RegAsymp
open MeasureTheory Incoh

/-- Actual derivative measurability at order zero gives the literal single-root amplitude. -/
theorem stronglyMeasurable_treeRootLeafAmplitude_slice {d n m K M : ℕ}
    (f : Fin m → Mom d → ℂ) {B : ℝ} (hK : d+1 ≤ K)
    (hf : ∀ a, Fourier.spatialNorm K M (f a) ≤ ENNReal.ofReal B)
    (S : (Fin (m+1) → Fin d → ℤ) → Finset ((Fin n × Fin 2) → Fin d → ℤ))
    (q : Fin d → ℤ) (k : Mom d) : StronglyMeasurable (treeRootLeafAmplitude f S q k) := by
  have h := (continuousMultilinearCurryFin0 ℝ (Mom d) ℂ).continuous.comp_stronglyMeasurable
    (stronglyMeasurable_treeRootLeafAmplitude_derivative f hK hf S q k 0)
  simpa only [iteratedFDeriv_zero_eq_comp, Function.comp_apply,
    LinearIsometryEquiv.apply_symm_apply] using h

/-- The actual locally finite moving-root sum is strongly measurable at every momentum. -/
theorem stronglyMeasurable_rootAmplitudeSum_treeRootLeaf {d n m K M : ℕ}
    (f : Fin m → Mom d → ℂ) {B : ℝ} (hK : d+1 ≤ K)
    (hf : ∀ a, Fourier.spatialNorm K M (f a) ≤ ENNReal.ofReal B)
    (S : (Fin (m+1) → Fin d → ℤ) → Finset ((Fin n × Fin 2) → Fin d → ℤ))
    (k : Mom d) : StronglyMeasurable (rootAmplitudeSum (treeRootLeafAmplitude f S) k) := by
  have he := (rootAmplitudeSum_eventuallyEq_model (treeRootLeafAmplitude f S)
    (treeRootLeafAmplitude_eq_zero f S) k).self_of_nhds
  change StronglyMeasurable (fun u => rootAmplitudeSum (treeRootLeafAmplitude f S) k u)
  simp_rw [he,rootAmplitudeModel]
  exact Finset.stronglyMeasurable_fun_sum _ (fun q _ =>
    stronglyMeasurable_treeRootLeafAmplitude_slice f hK hf S q k)

/-- The actual original leaf moments give integrability of each single-root density
against every uniformly bounded measurable scalar. -/
theorem integrable_treeRootLeafAmplitude_mul_scalar {d n m K M : ℕ}
    (f : Fin m → Mom d → ℂ) {B C D : ℝ}
    (hK : d+2 ≤ K) (hM : 2*d ≤ M) (hB : 0 ≤ B)
    (hf : ∀ a, Fourier.spatialNorm K M (f a) ≤ ENNReal.ofReal B)
    (S : (Fin (m+1) → Fin d → ℤ) → Finset ((Fin n × Fin 2) → Fin d → ℤ))
    (hS : ∀ c, ((S c).card:ℝ) ≤ C^n)
    (R : (SourceCellIndex S × (Fin (m+1) → Fin d → ℝ)) → ℂ)
    (hR : StronglyMeasurable R) (hbR : ∀ u, ‖R u‖ ≤ D)
    (q : Fin d → ℤ) (k : Mom d) :
    Integrable (fun u => treeRootLeafAmplitude f S q k u*R u) (treeLeafCellMeasure S) := by
  have ha := stronglyMeasurable_treeRootLeafAmplitude_slice f (by omega) hf S q k
  have hv := integrable_treeRootLeafEnvelope 0 f (by omega) hM hB hf S hS q
  have hi : Integrable (treeRootLeafAmplitude f S q k) (treeLeafCellMeasure S) := by
    apply hv.mono' ha.aestronglyMeasurable
    apply ae_of_all
    intro u
    simpa only [norm_iteratedFDeriv_zero] using
      norm_iteratedFDeriv_treeRootLeafAmplitude_le f S q (j := 0) (J := 0) (by omega) k u
  exact hi.mul_bdd hR.aestronglyMeasurable (ae_of_all _ hbR)

/-- The locally finite root sum preserves actual integrability of the original density. -/
theorem integrable_rootAmplitudeSum_treeRootLeaf_mul_scalar {d n m K M : ℕ}
    (f : Fin m → Mom d → ℂ) {B C D : ℝ}
    (hK : d+2 ≤ K) (hM : 2*d ≤ M) (hB : 0 ≤ B)
    (hf : ∀ a, Fourier.spatialNorm K M (f a) ≤ ENNReal.ofReal B)
    (S : (Fin (m+1) → Fin d → ℤ) → Finset ((Fin n × Fin 2) → Fin d → ℤ))
    (hS : ∀ c, ((S c).card:ℝ) ≤ C^n)
    (R : (SourceCellIndex S × (Fin (m+1) → Fin d → ℝ)) → ℂ)
    (hR : StronglyMeasurable R) (hbR : ∀ u, ‖R u‖ ≤ D) (k : Mom d) :
    Integrable (fun u => rootAmplitudeSum (treeRootLeafAmplitude f S) k u*R u)
      (treeLeafCellMeasure S) := by
  have he := (rootAmplitudeSum_eventuallyEq_model (treeRootLeafAmplitude f S)
    (treeRootLeafAmplitude_eq_zero f S) k).self_of_nhds
  simp_rw [he,rootAmplitudeModel,Finset.sum_mul]
  exact integrable_finsetSum _ (fun q _ =>
    integrable_treeRootLeafAmplitude_mul_scalar f hK hM hB hf S hS R hR hbR q k)

/-- Actual integrability justifies unfolding the counted cells into their original
Lebesgue leaf-frequency integrals. -/
theorem integral_treeLeafCellMeasure_eq_tsum {d n m : ℕ}
    (S : (Fin m → Fin d → ℤ) → Finset ((Fin n × Fin 2) → Fin d → ℤ))
    (A : (SourceCellIndex S × (Fin m → Fin d → ℝ)) → ℂ)
    (hi : Integrable A (treeLeafCellMeasure S)) :
    (∫ u, A u ∂treeLeafCellMeasure S) =
      ∑' c : SourceCellIndex S, ∫ α : Fin m → Fin d → ℝ, A (c,α) := by
  rw [treeLeafCellMeasure] at hi ⊢
  rw [integral_prod _ hi]
  simpa only [Measure.real, Measure.count_singleton, ENNReal.toReal_one, one_smul] using integral_countable hi.integral_prod_left

end WaveTurbulence.RegAsymp
