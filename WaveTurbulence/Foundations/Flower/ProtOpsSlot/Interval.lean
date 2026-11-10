/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Flower.ProtOpsSlot.Slots

/-! # PROT-OPS slots: `FixedIntervalBound` (o104 Lemma 7.1 (5))

The output integrates the last slot over a unit interval; null-set changes of the input move it only on a null set
of the output variables (Fubini), so the extension is a piecewise one. -/

@[expose] public section
set_option autoImplicit false
noncomputable section
open MeasureTheory WaveTurbulence.Fourier WaveTurbulence
open scoped ENNReal ContDiff

namespace WaveTurbulence.Flower.ProtOpsSlot

open WaveTurbulence.Flower.ProtOps

theorem ae_snoc {r : ℕ} {f g : (Fin (r + 1) → ℝ) → ℂ} (h : f =ᵐ[volume] g) :
    ∀ᵐ y : Fin r → ℝ, ∀ᵐ u : ℝ, f (Fin.snoc y u) = g (Fin.snoc y u) := by
  have hmp := MeasureTheory.volume_preserving_piFinSuccAbove (fun _ : Fin (r + 1) => ℝ) (Fin.last r)
  have h1 := hmp.symm.quasiMeasurePreserving.ae h
  have h2 := (Measure.measurePreserving_swap (μ := (volume : Measure (Fin r → ℝ))) (ν := (volume : Measure ℝ))).quasiMeasurePreserving.ae
    (p := fun z : ℝ × (Fin r → ℝ) => f ((MeasurableEquiv.piFinSuccAbove (fun _ : Fin (r + 1) => ℝ) (Fin.last r)).symm z) =
      g ((MeasurableEquiv.piFinSuccAbove (fun _ : Fin (r + 1) => ℝ) (Fin.last r)).symm z)) (by
    rw [← Measure.volume_eq_prod]; exact h1)
  have h3 := Measure.ae_ae_of_ae_prod h2
  refine h3.mono fun y hy => hy.mono fun u hu => ?_
  have e : (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (r + 1) => ℝ) (Fin.last r)).symm (u, y) = Fin.snoc y u := by
    rw [MeasurableEquiv.piFinSuccAbove_symm_apply]; exact Fin.insertNth_last' u y
  rw [Prod.swap_prod_mk] at hu
  simpa only [e] using hu

theorem rep_formula {r : ℕ} (f : (Fin r → ℝ) → ℂ) (t : Fin r → ℝ) :
    timeFourier (timeFourier f) (-t) =
      ∫ l, timeFourier f l * (Real.fourierChar (timePairing r t l) : ℂ) := by
  change (∫ ξ, Real.fourierChar (-timePairing r ξ (-t)) • timeFourier f ξ) = _
  refine integral_congr_ae (ae_of_all _ fun l => ?_)
  have h1 : timePairing r l t = timePairing r t l := by simp [timePairing, dotProduct_comm]
  simp only [Circle.smul_def, smul_eq_mul, map_neg, neg_neg, h1]
  ring

end WaveTurbulence.Flower.ProtOpsSlot
