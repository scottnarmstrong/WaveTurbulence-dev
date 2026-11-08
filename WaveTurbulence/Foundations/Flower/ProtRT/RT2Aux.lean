/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Flower.ProtRT.CplDefs
public import WaveTurbulence.Foundations.Flower.ProtPin.Pointwise

/-! # RT-GATE (ii), both roots pinned: auxiliary facts

* `rt2_lint_le_rn`: the integral of a function over a part of a unit window is at most its restricted norm (no
  continuity: the continuous representative of a near-optimal extension, main's `Regref.rep_props`, is a.e. equal to the
  extension and bounded by its Fourier norm);
* `rt2_ambS`: the windowed ambient `MkSlotsO.CplAmbient p p p` is D3's `TcCplAmbS p`. -/

@[expose] public section
set_option autoImplicit false
noncomputable section
open WaveTurbulence WaveTurbulence.LGSpine Set Finset MeasureTheory WaveTurbulence.Fourier
open scoped ENNReal

namespace WaveTurbulence.Flower.ProtRT

open WaveTurbulence.Flower.ProtDefs WaveTurbulence.Flower.ProtCut WaveTurbulence.Flower.ProtPin
open TTree WaveTurbulence.Links WaveTurbulence.Reg WaveTurbulence.PL234

/-- **The integral over a part of a unit window is at most the restricted norm.** -/
theorem rt2_lint_le_rn {θ : ℝ} (hθ : 0 ≤ θ) (a : ℝ) (f : (Fin 1 → ℝ) → ℂ) {I : Set ℝ}
    (hI : I ⊆ Icc a (a + 1)) (hIm : MeasurableSet I) (hvol : volume I ≤ 1) :
    ∫⁻ u in I, ‖f (fun _ => u)‖ₑ ≤ rn θ (win a) f := by
  rw [rn_eq_iInf]
  refine le_iInf₂ fun g hg => ?_
  by_cases hg' : timeFourierNorm θ g = ⊤
  · rw [hg']; exact le_top
  have hgf : timeFourierNorm θ g < ⊤ := lt_top_iff_ne_top.2 hg'
  obtain ⟨hc, hae, hint, hft, -⟩ := Regref.rep_props hθ hgf
  have hnorm : timeFourierNorm θ (Regref.rep g) = timeFourierNorm θ g := by
    rw [timeFourierNorm_eq_lintegral hint, timeFourierNorm_eq_lintegral (integrable_of_timeFourierNorm_lt_top hgf),
      hft]
  have hpt : ∀ t, ‖Regref.rep g t‖ₑ ≤ timeFourierNorm θ g := fun t =>
    (Regref.enorm_le_timeFourierNorm_at hθ _ t hc.continuousAt).trans hnorm.le
  have hmp : MeasurePreserving (MeasurableEquiv.funUnique (Fin 1) ℝ).symm volume volume :=
    (volume_preserving_funUnique (Fin 1) ℝ).symm
  have hφ : ∀ u : ℝ, (MeasurableEquiv.funUnique (Fin 1) ℝ).symm u = fun _ => u := fun u => rfl
  have hae' : (fun u : ℝ => Regref.rep g (fun _ => u)) =ᵐ[volume] fun u => g (fun _ => u) := by
    have := hmp.quasiMeasurePreserving.ae_eq_comp hae
    simpa only [Function.comp_def, hφ] using this
  calc ∫⁻ u in I, ‖f (fun _ => u)‖ₑ = ∫⁻ u in I, ‖g (fun _ => u)‖ₑ :=
        setLIntegral_congr_fun hIm fun u hu => by
          show ‖f (fun _ => u)‖ₑ = ‖g (fun _ => u)‖ₑ
          rw [hg _ (show (fun _ : Fin 1 => u) ∈ win a from hI hu)]
    _ = ∫⁻ u in I, ‖Regref.rep g (fun _ => u)‖ₑ :=
        lintegral_congr_ae (ae_restrict_of_ae (hae'.mono fun u hu => by
          show ‖g (fun _ => u)‖ₑ = ‖Regref.rep g (fun _ => u)‖ₑ
          rw [show Regref.rep g (fun _ => u) = g (fun _ => u) from hu]))
    _ ≤ ∫⁻ _ in I, timeFourierNorm θ g := lintegral_mono fun u => hpt _
    _ = timeFourierNorm θ g * volume I := setLIntegral_const _ _
    _ ≤ timeFourierNorm θ g * 1 := mul_le_mul' le_rfl hvol
    _ = timeFourierNorm θ g := mul_one _

/-- The windowed ambient at windows `p, p` is D3's signed ambient. -/
theorem rt2_ambS {p : ℕ} {Q : RegCpl} {LG : LayeredGarden 2} (h : MkSlotsO.CplAmbient p p p Q LG) :
    TcCplAmbS p Q LG := by
  obtain ⟨w', H, a, b, hcan, hE, hsa, hsb, hpa, hpb, hlay⟩ := h
  exact ⟨w', H, a, b, hcan, hE, hsa, hsb, hpa, hpb, hlay⟩

end WaveTurbulence.Flower.ProtRT
