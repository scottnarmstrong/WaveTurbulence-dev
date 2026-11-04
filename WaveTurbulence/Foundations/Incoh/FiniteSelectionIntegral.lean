/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import Mathlib.MeasureTheory.Integral.Bochner.SumMeasure
public import Mathlib.MeasureTheory.Integral.Prod

/-!
# Exact counting/Lebesgue integration with finite selected fibers

An integrable indicator-weighted family on all countable pairs equals
the countable sum over the actual selected finite fibers.
-/

public section
noncomputable section
open MeasureTheory

namespace WaveTurbulence.Incoh

/-- Conditional counting/Fubini transport for an actual finite fiber selection. -/
theorem integral_count_product_finite_selection {A B X : Type*}
    [Countable A] [Countable B] [DecidableEq B] [MeasurableSpace A] [MeasurableSpace B]
    [MeasurableSingletonClass A] [MeasurableSingletonClass B] [MeasurableSpace X]
    (ν : Measure X) [SFinite ν] (S : A → Finset B) (F : A → B → X → ℂ)
    (hF : Integrable (fun z : (A × B) × X => if z.1.2 ∈ S z.1.1 then F z.1.1 z.1.2 z.2 else 0)
      (Measure.count.prod ν)) :
    (∫ z : (A × B) × X, (if z.1.2 ∈ S z.1.1 then F z.1.1 z.1.2 z.2 else 0)
      ∂(Measure.count.prod ν)) = ∑' u : Σ a, {b : B // b ∈ S a}, ∫ x, F u.1 u.2.val x ∂ν := by
  classical
  let g := fun p : A × B => ∫ x, (if p.2 ∈ S p.1 then F p.1 p.2 x else 0) ∂ν
  have hgn : Summable (fun p => ‖g p‖) := integrable_count_iff.mp hF.integral_prod_left
  have hgs : Summable g := hgn.of_norm
  let e := fun u : Σ a, {b : B // b ∈ S a} => (u.1, u.2.val)
  have he : Function.Injective e := by
    intro ⟨a, b⟩ ⟨a', b'⟩ h
    change (a, b.val) = (a', b'.val) at h
    have ha : a = a' := congrArg Prod.fst h
    subst a'
    have hb : b = b' := Subtype.ext (congrArg Prod.snd h)
    cases hb
    rfl
  have hsn : Summable (fun u => ‖g (e u)‖) := hgn.comp_injective he
  have hss : Summable (fun u => g (e u)) := hsn.of_norm
  have hz (a : A) (b : B) (hb : b ∉ S a) : g (a, b) = 0 := by simp only [g, ite_eq_right hb, integral_zero]
  calc
    _ = ∑' p : A × B, g p := by
      rw [integral_prod _ hF, integral_countable hF.integral_prod_left]
      simp only [measureReal_def, Measure.count_singleton, ENNReal.toReal_one, one_smul]
      rfl
    _ = ∑' a : A, ∑' b : B, g (a, b) := hgs.tsum_prod
    _ = ∑' a : A, ∑' b : {b : B // b ∈ S a}, g (a, b.val) := by
      apply tsum_congr
      intro a
      rw [tsum_eq_sum (s := S a) (fun b hb => hz a b hb), tsum_fintype,
        Finset.sum_coe_sort (S a) (fun b => g (a, b))]
    _ = ∑' u : Σ a, {b : B // b ∈ S a}, g (e u) := hss.tsum_sigma.symm
    _ = _ := by
      apply tsum_congr
      intro u
      simp only [g, e, ite_eq_left u.2.property]

end WaveTurbulence.Incoh
