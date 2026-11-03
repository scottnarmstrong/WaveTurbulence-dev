/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Fourier.ProductFourier
public import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Tactic

/-!
# Flattening finite blocks of real coordinates

Currying and coordinate permutations preserve product Lebesgue measure.
This identifies the block Fourier norm with the ordinary coordinate Fourier
norm before applying an arbitrary unimodular change of variables.
-/

public section

open MeasureTheory Set

namespace WaveTurbulence.Fourier

/-- Flatten `n` vector blocks of dimension `d` into `n*d` scalar coordinates. -/
@[expose] def flattenBlocks (n d : ℕ) :
    (Fin n → Fin d → ℝ) ≃ᵐ (Fin (n * d) → ℝ) :=
  (MeasurableEquiv.curry (Fin n) (Fin d) ℝ).symm.trans
    (MeasurableEquiv.piCongrLeft (fun _ : Fin (n * d) => ℝ) finProdFinEquiv)

private theorem uncurry_measurePreserving (n d : ℕ) :
    MeasurePreserving (MeasurableEquiv.curry (Fin n) (Fin d) ℝ).symm := by
  let e := (MeasurableEquiv.curry (Fin n) (Fin d) ℝ).symm
  refine ⟨e.measurable, ?_⟩
  change Measure.map e volume = Measure.pi (fun _ : Fin n × Fin d => (volume : Measure ℝ))
  refine (Measure.pi_eq (fun s hs => ?_)).symm
  rw [e.map_apply]
  have he : e ⁻¹' (univ.pi s) = univ.pi (fun i : Fin n => univ.pi (fun j : Fin d => s (i, j))) := by
    ext x
    simp [e, MeasurableEquiv.coe_curry_symm, Function.uncurry_def, Prod.forall]
  rw [he, volume_pi_pi]
  simp only [volume_pi_pi]
  exact (Fintype.prod_prod_type (fun p : Fin n × Fin d => volume (s p))).symm

/-- Block flattening preserves the standard product Lebesgue measure. -/
theorem flattenBlocks_measurePreserving (n d : ℕ) :
    MeasurePreserving (flattenBlocks n d) := by
  apply (uncurry_measurePreserving n d).trans
  exact measurePreserving_piCongrLeft (fun _ : Fin (n * d) => (volume : Measure ℝ)) finProdFinEquiv

private theorem flattenBlocks_pairing {n d : ℕ} (x ξ : Fin n → Fin d → ℝ) :
    (∑ i, timePairing d (x i) (ξ i)) =
      timePairing (n * d) (flattenBlocks n d x) (flattenBlocks n d ξ) := by
  change (∑ i, ∑ j, x i j * ξ i j) =
    ∑ k, flattenBlocks n d x k * flattenBlocks n d ξ k
  rw [← Fintype.sum_prod_type (fun p : Fin n × Fin d => x p.1 p.2 * ξ p.1 p.2)]
  simpa [flattenBlocks, MeasurableEquiv.piCongrLeft, Equiv.piCongrLeft_apply_apply, Function.uncurry_def] using
    finProdFinEquiv.sum_comp (fun k => flattenBlocks n d x k * flattenBlocks n d ξ k)

/-- Fourier covariance under block flattening. -/
theorem blockFourier_eq_flattened {n d : ℕ}
    (F : (Fin n → Fin d → ℝ) → ℂ) (ξ : Fin n → Fin d → ℝ) :
    blockFourier F ξ = timeFourier
      (fun z => F ((flattenBlocks n d).symm z)) (flattenBlocks n d ξ) := by
  have hi := (flattenBlocks_measurePreserving n d).integral_comp
    (flattenBlocks n d).measurableEmbedding
    (fun z => Real.fourierChar (-timePairing (n * d) z (flattenBlocks n d ξ)) •
      F ((flattenBlocks n d).symm z))
  simp only [MeasurableEquiv.symm_apply_apply] at hi
  change _ = ∫ z, Real.fourierChar (-timePairing (n * d) z (flattenBlocks n d ξ)) •
    F ((flattenBlocks n d).symm z)
  rw [← hi]
  apply integral_congr_ae
  exact ae_of_all _ fun x => by
    change Real.fourierChar (-(∑ i, timePairing d (x i) (ξ i))) • F x = _
    rw [flattenBlocks_pairing]

/-- The block and scalar-coordinate Fourier-L¹ norms agree. -/
theorem blockFourierL1_eq_flattened {n d : ℕ}
    (F : (Fin n → Fin d → ℝ) → ℂ) :
    blockFourierL1 F = timeFourierNorm 0 (fun z => F ((flattenBlocks n d).symm z)) := by
  classical
  have hi := (flattenBlocks_measurePreserving n d).symm.integrable_comp_emb
    (flattenBlocks n d).symm.measurableEmbedding (g := F)
  simp only [Function.comp_def] at hi
  unfold blockFourierL1 timeFourierNorm
  rw [hi]
  split_ifs
  · simp only [timeWeight, Real.rpow_zero, ENNReal.ofReal_one, one_mul]
    rw [← (flattenBlocks_measurePreserving n d).lintegral_comp_emb
      (flattenBlocks n d).measurableEmbedding
      (fun z => ‖timeFourier (fun z => F ((flattenBlocks n d).symm z)) z‖ₑ)]
    apply lintegral_congr
    intro ξ
    rw [blockFourier_eq_flattened]
  · rfl

end WaveTurbulence.Fourier
