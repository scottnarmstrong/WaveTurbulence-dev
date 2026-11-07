/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.MeasurableSpace.Embedding
public import Mathlib.Topology.Algebra.InfiniteSum.Basic

/-! # V5 Step 4d-B: transport of the pair (integrable in `σ`, summable `L¹` norms in `x`) along equivalences -/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.VineEstS5B
open MeasureTheory

theorem sok_transport {X Y α β : Type*} [MeasurableSpace α] [MeasurableSpace β] {μ : Measure α} {ν : Measure β}
    (e : X ≃ Y) (m : α ≃ᵐ β) (hm : MeasurePreserving m μ ν) (f : X → α → ℂ) (g : Y → β → ℂ)
    (hfg : ∀ x a, g (e x) (m a) = f x a)
    (hg : (∀ y, Integrable (g y) ν) ∧ Summable fun y => ∫ b, ‖g y b‖ ∂ν) :
    (∀ x, Integrable (f x) μ) ∧ Summable fun x => ∫ a, ‖f x a‖ ∂μ := by
  refine ⟨fun x => ?_, ?_⟩
  · have : f x = g (e x) ∘ m := funext fun a => (hfg x a).symm
    rw [this]
    exact (hm.integrable_comp_emb m.measurableEmbedding).mpr (hg.1 (e x))
  · have h1 : ∀ x, ∫ a, ‖f x a‖ ∂μ = ∫ b, ‖g (e x) b‖ ∂ν := by
      intro x
      have := hm.integral_comp' (g := fun b => ‖g (e x) b‖)
      rw [← this]
      exact integral_congr_ae (Filter.Eventually.of_forall fun a => by simp only [hfg])
    simp_rw [h1]
    exact (e.summable_iff (f := fun y => ∫ b, ‖g y b‖ ∂ν)).mpr hg.2

end WaveTurbulence.VineEstS5B
