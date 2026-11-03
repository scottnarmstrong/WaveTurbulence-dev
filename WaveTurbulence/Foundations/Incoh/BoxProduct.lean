/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Mathlib.MeasureTheory.Integral.Pi
public import Mathlib.MeasureTheory.Integral.Bochner.Set

/-!
# Product domination on the linked time boxes

TARGET (incohproof11), (incohproof16): an arbitrary time-order domain inside
the product of link boxes is bounded by the product of the link L¹ masses.
-/

public section

noncomputable section

open MeasureTheory Set

namespace WaveTurbulence.Incoh

variable {ι : Type*} [Fintype ι] {E : ι → Type*} [∀ i, MeasurableSpace (E i)]
  {μ : ∀ i, Measure (E i)} [∀ i, SigmaFinite (μ i)]

/-- Products of the actual link integrands are integrable on the product time box. -/
theorem integrableOn_pi_product {f : ∀ i, E i → ℂ} {B : ∀ i, Set (E i)}
    (hf : ∀ i, IntegrableOn (f i) (B i) (μ i)) :
    IntegrableOn (fun t => ∏ i, f i (t i)) (univ.pi B) (Measure.pi μ) := by
  rw [IntegrableOn, Measure.restrict_pi_pi]
  exact Integrable.fintype_prod_dep hf

/-- TARGET (incohproof16), before inserting the proved single-link mass estimates. -/
theorem norm_setIntegral_pi_product_le {f : ∀ i, E i → ℂ} {B : ∀ i, Set (E i)}
    {I : Set (∀ i, E i)} (hI : I ⊆ univ.pi B)
    (hf : ∀ i, IntegrableOn (f i) (B i) (μ i)) :
    ‖∫ t in I, ∏ i, f i (t i) ∂Measure.pi μ‖ ≤ ∏ i, ∫ t in B i, ‖f i t‖ ∂μ i := by
  have hg : IntegrableOn (fun t => ∏ i, ‖f i (t i)‖) (univ.pi B) (Measure.pi μ) := by
    rw [IntegrableOn, Measure.restrict_pi_pi]
    exact Integrable.fintype_prod_dep (fun i => (hf i).norm)
  calc
    _ ≤ ∫ t in I, ∏ i, ‖f i (t i)‖ ∂Measure.pi μ := by
      simpa only [norm_prod] using norm_integral_le_integral_norm
        (fun t : ∀ i, E i => ∏ i, f i (t i)) (μ := (Measure.pi μ).restrict I)
    _ ≤ ∫ t in univ.pi B, ∏ i, ‖f i (t i)‖ ∂Measure.pi μ :=
      setIntegral_mono_set hg (ae_of_all _ fun t => Finset.prod_nonneg fun i _ => norm_nonneg _)
        (ae_of_all _ fun _ ht => hI ht)
    _ = _ := by
      rw [Measure.restrict_pi_pi]
      exact integral_fintype_prod_eq_prod (μ := fun i => (μ i).restrict (B i))
        (fun i x => ‖f i x‖)

end WaveTurbulence.Incoh
