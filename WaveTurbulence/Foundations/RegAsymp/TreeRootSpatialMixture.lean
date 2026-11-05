/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.RegAsymp.TreeZeroTimeNorm
public import WaveTurbulence.Foundations.RegAsymp.TreeRootLeafMixture

/-! # Spatial transport for the actual moving-root tree leaf mixture -/

public section
noncomputable section
namespace WaveTurbulence.RegAsymp
open MeasureTheory Incoh
open scoped ENNReal

/-- The literal root-partition leaf mixture has the full spatial bound from one uniform
scalar bound. Only the original input norms supply spatial derivative mass. -/
theorem spatialNorm_treeRootLeafMixture_le {d n m K M J : ℕ}
    (f : Fin m → Mom d → ℂ) {B C Q : ℝ}
    (hK : d+2+J ≤ K) (hM : 2*d ≤ M) (hB : 0 ≤ B)
    (hf : ∀ a, Fourier.spatialNorm K M (f a) ≤ ENNReal.ofReal B)
    (S : (Fin (m+1) → Fin d → ℤ) → Finset ((Fin n × Fin 2) → Fin d → ℤ))
    (hS : ∀ c, ((S c).card:ℝ) ≤ C^n)
    (R : (SourceCellIndex S × (Fin (m+1) → Fin d → ℝ)) → ℂ)
    (hR : StronglyMeasurable R) (hbR : ∀ u, ‖R u‖ ≤ Q) :
    Fourier.spatialNorm J 0
      (fun k => ∫ u, rootAmplitudeSum (treeRootLeafAmplitude f S) k u * R u
        ∂treeLeafCellMeasure S) ≤
      (ENNReal.ofReal (rootLocalOverlapConstant d) *
        (ENNReal.ofReal (treeRootLeafDerivativeConstant d J) * (ENNReal.ofReal (C^n) *
          ENNReal.ofReal (leafMomentLocalizationConstant d (J+1) M *
            treeAugmentedInputBound d K M B)^(m+1)))) * ENNReal.ofReal Q := by
  let G := fun (_ : Fin 0 → ℝ) u => R u
  have hi (u) : Integrable (fun t => G t u) := by
    rw [Measure.volume_pi_eq_dirac (x := (Fin.elim0 : Fin 0 → ℝ))]
    exact integrable_const _
  have hp (u) : eLpNorm (fun t => G t u) 1 ≤ ENNReal.ofReal Q := by
    rw [eLpNorm_one_eq_lintegral_enorm (hi u).aestronglyMeasurable]
    simp only [Measure.volume_pi_eq_dirac (x := (Fin.elim0 : Fin 0 → ℝ)), lintegral_dirac]
    exact (ofReal_norm _).symm.trans_le (ENNReal.ofReal_le_ofReal (hbR u))
  have h := mixedFourierNorm_treeRootLeafMixture_le (r := 0) 0 f hK hM hB hf S hS G
    (hR.comp_measurable measurable_snd) hi ENNReal.ofReal_lt_top hp
  unfold treeRootLeafMixture at h
  dsimp only [G] at h
  rw [tree_mixedFourierNorm_zero_time, tree_mixedFourierNorm00_zero_time] at h
  exact h.trans (mul_le_mul' le_rfl (iSup_le (fun u =>
    (ofReal_norm _).symm.trans_le (ENNReal.ofReal_le_ofReal (hbR u)))))

end WaveTurbulence.RegAsymp
