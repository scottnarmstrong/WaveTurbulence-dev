/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Mathlib.MeasureTheory.Constructions.Pi
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

/-! # Almost-everywhere statements pulled back along an injective coordinate selection -/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.VineEstS5A
open MeasureTheory

/-- A property holding a.e. in `ℝⁿ` holds a.e. in `ℝ^ι` for the injective coordinate selection `σ`. -/
theorem ae_pullback_coords {ι : Type*} [Fintype ι] {n : ℕ} (σ : Fin n → ι) (hσ : Function.Injective σ)
    {P : (Fin n → ℝ) → Prop} (h : ∀ᵐ x : Fin n → ℝ, P x) : ∀ᵐ τ : ι → ℝ, P (fun i => τ (σ i)) := by
  classical
  set p : ι → Prop := fun i => ∃ j, σ j = i with hp
  let e1 := MeasurableEquiv.piEquivPiSubtypeProd (fun _ : ι => ℝ) p
  have he1 : MeasurePreserving e1 := volume_preserving_piEquivPiSubtypeProd (fun _ : ι => ℝ) p
  let eα : Fin n ≃ {i // p i} := (Equiv.ofInjective σ hσ).trans (Equiv.subtypeEquivRight fun i => by simp [hp])
  let e2 := MeasurableEquiv.arrowCongr' eα (MeasurableEquiv.refl ℝ)
  have he2 : MeasurePreserving e2 := volume_preserving_arrowCongr' eα (MeasurableEquiv.refl ℝ) (MeasurePreserving.id _)
  have hN : volume {x : Fin n → ℝ | ¬ P x} = 0 := ae_iff.1 h
  set N2 : Set ({i // p i} → ℝ) := e2.symm ⁻¹' {x : Fin n → ℝ | ¬ P x} with hN2
  have hN2z : volume N2 = 0 := by
    rw [hN2]
    have := (he2.symm).measure_preimage_equiv {x : Fin n → ℝ | ¬ P x}
    rw [this]; exact hN
  have hprod : volume (N2 ×ˢ (Set.univ : Set ({i // ¬ p i} → ℝ))) = 0 := by
    rw [show (volume : Measure (({i // p i} → ℝ) × ({i // ¬ p i} → ℝ))) = volume.prod volume from rfl,
      Measure.prod_prod, hN2z, zero_mul]
  have hpre : volume (e1 ⁻¹' (N2 ×ˢ (Set.univ : Set ({i // ¬ p i} → ℝ)))) = 0 := by
    rw [he1.measure_preimage_equiv]; exact hprod
  rw [ae_iff]
  refine measure_mono_null (fun τ hτ => ?_) hpre
  simp only [Set.mem_ofPred_eq, Set.mem_preimage, Set.mem_prod, Set.mem_univ, and_true, hN2] at hτ ⊢
  convert hτ using 2
  funext j
  simp [e1, e2, eα, MeasurableEquiv.arrowCongr', MeasurableEquiv.piEquivPiSubtypeProd, Equiv.arrowCongr']
  rfl
