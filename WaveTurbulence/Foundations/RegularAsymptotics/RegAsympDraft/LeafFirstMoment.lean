/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.RegAsymp.FourierFirstMoment
public import WaveTurbulence.Foundations.Incoh.LeafCellFourierDecay

/-! # First Fourier moments of the actual source leaf cells -/

public section
noncomputable section
namespace WaveTurbulence.RegAsymp
open MeasureTheory Incoh
open scoped FourierTransform ContDiff ENNReal

/-- One extra spatial derivative supplies the first frequency moment,
with the same summable decay in the actual leaf-cell center. -/
theorem leafCell_firstMoment_integrable_and_bound {d K M : ℕ} {f : Mom d → ℂ} {B : ℝ}
    (hK : d + 2 ≤ K) (hB : 0 ≤ B) (hF : Fourier.spatialNorm K M f ≤ ENNReal.ofReal B)
    (c : Fin d → ℤ) :
    Integrable (fun ξ : Mom d => (1+‖ξ‖) * ‖𝓕 (leafCell f c) ξ‖) ∧
      (∫ ξ : Mom d, (1+‖ξ‖) * ‖𝓕 (leafCell f c) ξ‖) ≤
        firstMomentFourierConstant (Mom d) (d+2) * leafCellSobolevConstant d (d+2) M *
          B * cellCenterWeight M c := by
  have hKpos : 0 < K := by omega
  have hf := contDiff_leafCell (contDiff_of_spatialNorm_le hKpos hF) c
  have hfc := hasCompactSupport_leafCell f c
  have hs : ContDiff ℝ (d+2) (leafCell f c) :=
    hf.of_le (show ((d+2 : ℕ) : ℕ∞ω) ≤ K by exact_mod_cast hK)
  have hi (j : ℕ) (hj : j ≤ d+2) : Integrable (iteratedFDeriv ℝ j (leafCell f c)) :=
    (hf.continuous_iteratedFDeriv (m := j) (by exact_mod_cast hj.trans hK)).integrable_of_hasCompactSupport
      (hfc.iteratedFDeriv j)
  have hN : Module.finrank ℝ (Mom d) + 1 < d+2 := by simp
  obtain ⟨hInt,hBound⟩ := fourier_firstMoment_integrable_and_bound hN hs hi
  refine ⟨hInt,hBound.trans ?_⟩
  have hC : 0 ≤ firstMomentFourierConstant (Mom d) (d+2) := by
    unfold firstMomentFourierConstant
    positivity
  have hsob := derivativeL1Sum_leafCell_le hKpos hK hB hF c
  calc
    _ ≤ firstMomentFourierConstant (Mom d) (d+2) *
        (leafCellSobolevConstant d (d+2) M * B / Fourier.momentumBracket (NTSP.intVec c)^M) :=
      mul_le_mul_of_nonneg_left hsob hC
    _ = _ := by simp only [cellCenterWeight,div_eq_mul_inv]; ring

/-- The same first-moment estimate in the coordinate measure used by NT. -/
theorem leafCell_coordinate_firstMoment_integrable_and_bound {d K M : ℕ} {f : Mom d → ℂ} {B : ℝ}
    (hK : d+2 ≤ K) (hB : 0 ≤ B) (hF : Fourier.spatialNorm K M f ≤ ENNReal.ofReal B)
    (c : Fin d → ℤ) :
    Integrable (fun ξ : Fin d → ℝ => (1+‖WithLp.toLp 2 ξ‖) *
      ‖Fourier.timeFourier (fun y : Fin d → ℝ => leafCell f c (WithLp.toLp 2 y)) ξ‖) ∧
      (∫ ξ : Fin d → ℝ, (1+‖WithLp.toLp 2 ξ‖) *
        ‖Fourier.timeFourier (fun y : Fin d → ℝ => leafCell f c (WithLp.toLp 2 y)) ξ‖) ≤
        firstMomentFourierConstant (Mom d) (d+2) * leafCellSobolevConstant d (d+2) M *
          B * cellCenterWeight M c := by
  obtain ⟨hi,hb⟩ := leafCell_firstMoment_integrable_and_bound hK hB hF c
  let g : (Fin d → ℝ) → ℝ := fun ξ => (1+‖WithLp.toLp 2 ξ‖) *
    ‖Fourier.timeFourier (fun y : Fin d → ℝ => leafCell f c (WithLp.toLp 2 y)) ξ‖
  have he : (fun x : Mom d => g (WithLp.ofLp x)) =
      (fun x : Mom d => (1+‖x‖) * ‖𝓕 (leafCell f c) x‖) := by
    funext x
    simp only [g,Fourier.timeFourier_eq_euclidean,WithLp.toLp_ofLp]
  have hm := PiLp.volume_preserving_ofLp (Fin d)
  have hemb := (MeasurableEquiv.toLp 2 (Fin d → ℝ)).symm.measurableEmbedding
  refine ⟨(hm.integrable_comp_emb hemb (g := g)).mp (by simpa only [Function.comp_def,he] using hi),?_⟩
  have hh := hm.integral_comp hemb g
  change (∫ ξ, g ξ) ≤ _
  rw [← hh]
  simpa only [he] using hb

/-- Lower-integral form of the actual first-moment bound. -/
theorem leafCell_coordinate_firstMoment_lintegral_le {d K M : ℕ} {f : Mom d → ℂ} {B : ℝ}
    (hK : d+2 ≤ K) (hB : 0 ≤ B) (hF : Fourier.spatialNorm K M f ≤ ENNReal.ofReal B)
    (c : Fin d → ℤ) :
    (∫⁻ ξ : Fin d → ℝ, ENNReal.ofReal (1+‖WithLp.toLp 2 ξ‖) *
      ‖Fourier.timeFourier (fun y : Fin d → ℝ => leafCell f c (WithLp.toLp 2 y)) ξ‖ₑ) ≤
        ENNReal.ofReal (firstMomentFourierConstant (Mom d) (d+2) * leafCellSobolevConstant d (d+2) M *
          B * cellCenterWeight M c) := by
  obtain ⟨hi,hb⟩ := leafCell_coordinate_firstMoment_integrable_and_bound hK hB hF c
  have hh := ofReal_integral_eq_lintegral_ofReal hi (ae_of_all _ (fun ξ => by positivity))
  have he : (∫⁻ ξ : Fin d → ℝ, ENNReal.ofReal (1+‖WithLp.toLp 2 ξ‖) *
      ‖Fourier.timeFourier (fun y : Fin d → ℝ => leafCell f c (WithLp.toLp 2 y)) ξ‖ₑ) =
      ENNReal.ofReal (∫ ξ : Fin d → ℝ, (1+‖WithLp.toLp 2 ξ‖) *
      ‖Fourier.timeFourier (fun y : Fin d → ℝ => leafCell f c (WithLp.toLp 2 y)) ξ‖) := by
    rw [hh]
    apply lintegral_congr
    intro ξ
    rw [← ofReal_norm,ENNReal.ofReal_mul (by positivity)]
  exact he.le.trans (ENNReal.ofReal_le_ofReal hb)

end WaveTurbulence.RegAsymp
