/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import Mathlib
/-! # Product integrals over boxes (S3b LADDER-DECAY) -/
@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.LadderDecay
open Finset MeasureTheory
open scoped ENNReal

/-- The lintegral of a product of nonnegative bounded measurable one-box functions over a
product of finite-measure boxes is the product of the box integrals. -/
theorem lintegral_pi_box_prod {m : ℕ} (r : Fin m → ℝ × ℝ → ℝ) (hr : ∀ k, Measurable (r k))
    (hnn : ∀ k t, 0 ≤ r k t) (C : Fin m → ℝ) (hC : ∀ k t, r k t ≤ C k)
    (box : Fin m → Set (ℝ × ℝ)) (_hbox : ∀ k, MeasurableSet (box k))
    (hfin : ∀ k, volume (box k) < ⊤) :
    ∫⁻ t in Set.pi Set.univ box, ∏ k, ENNReal.ofReal (r k (t k)) =
      ENNReal.ofReal (∏ k, ∫ t in box k, r k t) := by
  have hmeas : Measurable (fun t : Fin m → ℝ × ℝ => ∏ k, r k (t k)) :=
    Finset.measurable_prod _ (fun k _ => (hr k).comp (measurable_pi_apply k))
  have hfinpi : volume (Set.pi Set.univ box) ≠ ⊤ := by
    rw [volume_pi, Measure.pi_pi]
    exact (ENNReal.prod_lt_top (fun k _ => hfin k)).ne
  have hint : Integrable (fun t : Fin m → ℝ × ℝ => ∏ k, r k (t k))
      (volume.restrict (Set.pi Set.univ box)) := by
    refine Integrable.mono' (g := fun _ => ∏ k, max (C k) 0)
      (integrableOn_const hfinpi) hmeas.aestronglyMeasurable (ae_of_all _ (fun t => ?_))
    rw [Real.norm_of_nonneg (Finset.prod_nonneg (fun k _ => hnn k _))]
    exact Finset.prod_le_prod₀ (fun k _ => hnn k _) (fun k _ => (hC k _).trans (le_max_left _ _))
  have h1 : ∀ t : Fin m → ℝ × ℝ, ∏ k, ENNReal.ofReal (r k (t k)) =
      ENNReal.ofReal (∏ k, r k (t k)) := fun t =>
    (ENNReal.ofReal_prod_of_nonneg (fun k _ => hnn k _)).symm
  simp_rw [h1]
  rw [← ofReal_integral_eq_lintegral_ofReal hint (ae_of_all _ (fun t =>
    Finset.prod_nonneg (fun k _ => hnn k _)))]
  congr 1
  rw [volume_pi, Measure.restrict_pi_pi]
  exact integral_fintype_prod_eq_prod (fun k => fun x : ℝ × ℝ => r k x)
    |> fun h => by simpa using h

end WaveTurbulence.LadderDecay
