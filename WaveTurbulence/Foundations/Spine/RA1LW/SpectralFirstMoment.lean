/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.RegularAsymptotics.RegAsympDraft.HalfLinkFirstMoment
public import WaveTurbulence.Foundations.Spine.RA1LW.LeafFrequencyMass
public import WaveTurbulence.Foundations.Incoh.LocalizedSpectralMassBound

/-! # A common spectral envelope with its complete first frequency moment -/

public section
noncomputable section
namespace WaveTurbulence.RA1Leafwise
open WaveTurbulence.RegAsymp
open MeasureTheory Incoh WithLp
open scoped ENNReal

/-- The actual single-leaf first-moment mass. -/
@[expose] def leafCellFrequencyMass {d : ℕ} (F : Mom d → ℂ) (c : Fin d → ℤ) : ℝ≥0∞ :=
  ∫⁻ ξ : Fin d → ℝ, ENNReal.ofReal (1+‖toLp 2 ξ‖) *
    ‖Fourier.timeFourier (fun y : Fin d → ℝ => leafCell F c (toLp 2 y)) ξ‖ₑ

/-- One reference density pays one first moment for each fixed-dimensional
profile. This bound precedes any supremum over source momenta. -/
theorem localizedSpectralReference_firstMoment_le {d n m K M : ℕ} {F : Fin m → Mom d → ℂ} {B : ℝ}
    (hK : d+2 ≤ K) (hB : 0 ≤ B) (hF : (∀ a, Fourier.spatialNorm K M (F a) ≤ ENNReal.ofReal B))
    (c : Fin m → Fin d → ℤ) :
    (∫⁻ ξ : LocalizedCellIndex n m → Fin d → ℝ,
      ENNReal.ofReal (1+∑ i, ‖toLp 2 (ξ i)‖) *
        ‖localizedSpectralReference (n := n) F c ξ‖ₑ) ≤
      (∏ a, leafCellFrequencyMass (F a) (c a)) *
        ENNReal.ofReal (halfLinkFirstMomentConstant d) ^ (2*n) := by
  have hm (i : LocalizedCellIndex n m) : Measurable (fun ξ : Fin d → ℝ =>
      ‖Fourier.timeFourier (localizedCellProfiles F c (fun _ => 0) i) ξ‖ₑ) := by
    have hi := Fourier.integrable_of_timeFourierNorm_lt_top
      (timeFourierNorm_localizedCellProfiles_lt_top (n := n) F c (fun _ => 0)
        (by omega : d+1 ≤ K) hB hF i)
    exact (Fourier.timeFourier_continuous hi).measurable.enorm
  calc
    _ ≤ ∏ i : LocalizedCellIndex n m, ∫⁻ ξ : Fin d → ℝ, ENNReal.ofReal (1+‖toLp 2 ξ‖) *
        ‖Fourier.timeFourier (localizedCellProfiles F c (fun _ => 0) i) ξ‖ₑ := by
      simp only [localizedSpectralReference,ApproxNT.enorm_finset_prod]
      exact lintegral_sum_frequency_moment_le (fun ξ : Fin d → ℝ => ‖toLp 2 ξ‖)
        (PiLp.continuous_toLp 2 _).norm.measurable (fun _ => norm_nonneg _) _ hm
    _ ≤ _ := by
      rw [Fintype.prod_sum_type]
      apply mul_le_mul' le_rfl
      calc
        _ ≤ ∏ _p : Fin n × Fin 2, ENNReal.ofReal (halfLinkFirstMomentConstant d) :=
          Finset.prod_le_prod (fun _ _ => halfLinkCell_firstMoment_lintegral_le 0)
        _ = _ := by simp [Nat.mul_comm]

/-- Summing all source leaf centers retains a dimensional exponential bound
for the complete leaf-and-link first moment. -/
theorem tsum_localizedSpectralReference_firstMoment_le {d n m K M : ℕ} {F : Fin m → Mom d → ℂ} {B : ℝ}
    (hK : d+2 ≤ K) (hM : 2*d ≤ M) (hB : 0 ≤ B)
    (hF : (∀ a, Fourier.spatialNorm K M (F a) ≤ ENNReal.ofReal B)) :
    (∑' c : Fin m → Fin d → ℤ, ∫⁻ ξ : LocalizedCellIndex n m → Fin d → ℝ,
      ENNReal.ofReal (1+∑ i, ‖toLp 2 (ξ i)‖) *
        ‖localizedSpectralReference (n := n) F c ξ‖ₑ) ≤
      ENNReal.ofReal (leafFirstMomentConstant d M * B) ^ m *
        ENNReal.ofReal (halfLinkFirstMomentConstant d) ^ (2*n) := by
  calc
    _ ≤ ∑' c : Fin m → Fin d → ℤ, (∏ a, leafCellFrequencyMass (F a) (c a)) *
        ENNReal.ofReal (halfLinkFirstMomentConstant d) ^ (2*n) :=
      ENNReal.tsum_le_tsum (fun c => localizedSpectralReference_firstMoment_le hK hB hF c)
    _ = (∏ a : Fin m, ∑' c : Fin d → ℤ, leafCellFrequencyMass (F a) c) *
        ENNReal.ofReal (halfLinkFirstMomentConstant d) ^ (2*n) := by
      rw [ENNReal.tsum_mul_right,tsum_fin_product_ennreal m (fun (a : Fin m) c => leafCellFrequencyMass (F a) c)]
    _ ≤ _ := by
      apply mul_le_mul' _ le_rfl
      calc
        _ ≤ ∏ _a : Fin m, ENNReal.ofReal (leafFirstMomentConstant d M * B) :=
          Finset.prod_le_prod (fun a _ => tsum_leafCell_firstMoment_le hK hM hB (hF a))
        _ = _ := by simp

end WaveTurbulence.RA1Leafwise
