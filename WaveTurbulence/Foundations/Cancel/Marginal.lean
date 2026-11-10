/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Mathlib.MeasureTheory.Integral.Marginal
public import Mathlib.MeasureTheory.Integral.Prod
public import Mathlib.MeasureTheory.Constructions.Pi

/-!
# Integrals over finitely many of the variables `α : V → ℝ`

DH21 §7 integrates functions of a family of variables `α[W]`, `W` a finite set of nodes, the other
variables being fixed. `mint W F α₀ = ∫ F(α₀ updated on W by y) dy` over `y : W → ℝ` (the Bochner analogue
of Mathlib's `lmarginal`), and `MInt W F α₀` is the integrability of this function.

* `mint_union`: Fubini for a disjoint union `s ∪ t`.
* `mint_singleton`: one variable.
* `mint_union_singleton`: peel off one variable `v ∉ W` (innermost).
* `ae_integrable_section`: the sections in the peeled variable are integrable for almost every value of
  the other variables.
-/

public section

open MeasureTheory Set Filter Function

namespace WaveTurbulence.Cancel

variable {V : Type*} [DecidableEq V]

/-- **The integral over the variables `α[W]`**, the other variables fixed at `α₀`. -/
@[expose] noncomputable def mint (W : Finset V) (F : (V → ℝ) → ℂ) (α₀ : V → ℝ) : ℂ :=
  ∫ y : ↥W → ℝ, F (updateFinset α₀ W y)

/-- **Integrability over `α[W]`**. -/
@[expose] def MInt (W : Finset V) (F : (V → ℝ) → ℂ) (α₀ : V → ℝ) : Prop :=
  Integrable fun y : ↥W → ℝ => F (updateFinset α₀ W y)

/-- **One variable.** -/
theorem mint_singleton (v : V) (F : (V → ℝ) → ℂ) (α₀ : V → ℝ) :
    mint {v} F α₀ = ∫ x : ℝ, F (update α₀ v x) := by
  have hp := measurePreserving_piUnique (fun _ : ({v} : Finset V) => (volume : Measure ℝ))
  have h := (hp.symm _).integral_comp (MeasurableEquiv.piUnique _).symm.measurableEmbedding
    (fun y : ↥({v} : Finset V) → ℝ => F (updateFinset α₀ {v} y))
  refine h.symm.trans ?_
  refine integral_congr_ae (Eventually.of_forall fun x => ?_)
  simp only
  rw [updateFinset_singleton]
  rfl

theorem mint_empty (F : (V → ℝ) → ℂ) (α₀ : V → ℝ) : mint ∅ F α₀ = F α₀ := by
  unfold mint
  simp only [updateFinset_empty, integral_const]
  have h1 : (volume : Measure (↥(∅ : Finset V) → ℝ)) univ = 1 := by
    rw [volume_pi, Measure.pi_univ]; simp
  rw [Measure.real, h1]
  simp

end WaveTurbulence.Cancel
