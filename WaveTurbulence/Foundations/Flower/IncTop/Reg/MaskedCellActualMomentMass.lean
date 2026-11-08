/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Flower.IncTop.Reg.MaskedCellEnvelope
public import WaveTurbulence.Foundations.Incoh.LeafFourierMomentMass

/-! Ported by source from C2-B-TOP `Cut2BReg.MaskedCellActualMomentMass` (sha256 in COPIED-SHA256SUMS); mechanical edits only.

R66 spatially modulated scratch copy. Original SHA256 recorded in REG-COPIES.json.
 # Actual individual moment totals control the unweighted all-cell derivative envelope -/

public section
noncomputable section
open MeasureTheory
open scoped ENNReal

namespace WaveTurbulence.Flower.IncTop
open WaveTurbulence.Incoh
/-- The full unweighted envelope is controlled by actual individual moment totals, with no
source spatial-bound size entering the conclusion. The spatial hypothesis is used only for
Fourier integrability and measurability. -/
theorem lintegral_maskedCellEnvelope_zero_le_actual_totalsSpatial {d n m K M : ℕ} (J : ℕ)
    (f : Fin m → Mom d → ℂ)
    (S : (Fin m → Fin d → ℤ) → Finset ((Fin n × Fin 2) → Fin d → ℤ))
    {C : ℝ} (hS : ∀ c, ((S c).card : ℝ) ≤ C ^ n) {B : ℝ}
    (hK : d + 1 + J ≤ K) (hB : 0 ≤ B)
    (hf : ∀ a, Fourier.spatialNorm K M (f a) ≤ ENNReal.ofReal B) :
    (∫⁻ u, ENNReal.ofReal (maskedCellEnvelopeSpatial J 0 f S u) ∂sourceCellMeasure S) ≤
      ENNReal.ofReal (maskedSourceSpatialConstantSpatial d m J 0) * ENNReal.ofReal (C ^ n) *
        ((∏ a : Fin m, leafFourierMomentTotal J (f a)) *
          ENNReal.ofReal (halfCellFourierConstant d) ^ (2 * n)) := by
  have hm (c : Fin m → Fin d → ℤ) : Measurable (fun ξ : LocalizedCellIndex n m → Fin d → ℝ =>
      ‖localizedSpectralMomentReference J f c ξ‖ₑ) :=
    (continuous_localizedSpectralMomentReference J f c (by omega) hB hf).measurable.enorm
  have hjoint : Measurable (fun u : SourceCellIndex S × (LocalizedCellIndex n m → Fin d → ℝ) =>
      ‖localizedSpectralMomentReference J f u.1.1 u.2‖ₑ) :=
    measurable_from_prod_countable_right (fun u => hm u.1)
  have he (u : SourceCellIndex S × (LocalizedCellIndex n m → Fin d → ℝ)) :
      ENNReal.ofReal (maskedCellEnvelopeSpatial J 0 f S u) =
        ENNReal.ofReal (maskedSourceSpatialConstantSpatial d m J 0) *
          ‖localizedSpectralMomentReference J f u.1.1 u.2‖ₑ := by
    simp only [maskedCellEnvelopeSpatial, pow_zero, Finset.prod_const_one, mul_one,
      ENNReal.ofReal_mul (maskedSourceSpatialConstant_nonnegSpatial _ _ _ _), ofReal_norm]
  simp_rw [he]
  rw [lintegral_const_mul _ hjoint, lintegral_sourceCellMeasure S _ hm, mul_assoc]
  apply mul_le_mul' le_rfl
  calc
    _ ≤ ∑' c : Fin m → Fin d → ℤ, ENNReal.ofReal (C ^ n) *
        ∫⁻ ξ, ‖localizedSpectralMomentReference (n := n) J f c ξ‖ₑ := by
      apply ENNReal.tsum_le_tsum
      intro c
      apply mul_le_mul' _ le_rfl
      simpa only [ENNReal.ofReal_natCast] using ENNReal.ofReal_le_ofReal (hS c)
    _ = ENNReal.ofReal (C ^ n) * ∑' c : Fin m → Fin d → ℤ,
        ∫⁻ ξ, ‖localizedSpectralMomentReference (n := n) J f c ξ‖ₑ := ENNReal.tsum_mul_left
    _ ≤ _ := mul_le_mul' le_rfl (tsum_lintegral_spectralMomentReference_le_product_actual_totals J f hK hB hf)

end WaveTurbulence.Flower.IncTop