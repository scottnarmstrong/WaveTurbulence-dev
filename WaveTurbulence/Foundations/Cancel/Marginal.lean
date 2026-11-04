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

/-- **Fubini over a disjoint union of variable sets.** -/
theorem mint_union {s t : Finset V} (hst : Disjoint s t) {F : (V → ℝ) → ℂ} {α₀ : V → ℝ}
    (hF : MInt (s ∪ t) F α₀) : mint (s ∪ t) F α₀ = mint s (fun α => mint t F α) α₀ := by
  have hp := measurePreserving_piFinsetUnion hst (fun _ : V => (volume : Measure ℝ))
  set e := MeasurableEquiv.piFinsetUnion (fun _ : V => ℝ) hst
  set g : (↥(s ∪ t) → ℝ) → ℂ := fun y => F (updateFinset α₀ (s ∪ t) y)
  have h1 : mint (s ∪ t) F α₀ =
      ∫ p, g (e p) ∂((Measure.pi fun _ : ↥s => (volume : Measure ℝ)).prod
        (Measure.pi fun _ : ↥t => (volume : Measure ℝ))) :=
    (hp.integral_comp e.measurableEmbedding g).symm
  have hint : Integrable (fun p => g (e p)) ((Measure.pi fun _ : ↥s => (volume : Measure ℝ)).prod
      (Measure.pi fun _ : ↥t => (volume : Measure ℝ))) :=
    (hp.integrable_comp_emb e.measurableEmbedding).2 hF
  rw [h1, integral_prod _ hint]
  unfold mint
  refine integral_congr_ae (Eventually.of_forall fun y => ?_)
  refine integral_congr_ae (Eventually.of_forall fun z => ?_)
  simp only [g]
  rw [updateFinset_updateFinset hst]
  rfl

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

theorem MInt.union_singleton {W : Finset V} {v : V} (hv : v ∉ W) {F : (V → ℝ) → ℂ}
    {α₀ : V → ℝ} (hF : MInt (W ∪ {v}) F α₀) :
    ∀ᵐ y : ↥W → ℝ ∂volume, Integrable fun x : ℝ => F (update (updateFinset α₀ W y) v x) := by
  have hst : Disjoint W {v} := Finset.disjoint_singleton_right.2 hv
  have hp := measurePreserving_piFinsetUnion hst (fun _ : V => (volume : Measure ℝ))
  set e := MeasurableEquiv.piFinsetUnion (fun _ : V => ℝ) hst
  set g : (↥(W ∪ {v}) → ℝ) → ℂ := fun y => F (updateFinset α₀ (W ∪ {v}) y)
  have hint : Integrable (fun p => g (e p)) ((Measure.pi fun _ : ↥W => (volume : Measure ℝ)).prod
      (Measure.pi fun _ : ↥({v} : Finset V) => (volume : Measure ℝ))) :=
    (hp.integrable_comp_emb e.measurableEmbedding).2 hF
  have hu := measurePreserving_piUnique (fun _ : ({v} : Finset V) => (volume : Measure ℝ))
  have hae := hint.prod_right_ae
  refine hae.mono fun y hy => ?_
  have h2 := (hu.symm _).integrable_comp_emb (MeasurableEquiv.piUnique _).symm.measurableEmbedding
    (g := fun z : ↥({v} : Finset V) → ℝ => g (e (y, z)))
  refine (h2.2 hy).congr (Eventually.of_forall fun x => ?_)
  simp only [Function.comp_apply, g]
  rw [show update (updateFinset α₀ W y) v x =
      updateFinset (updateFinset α₀ W y) {v} ((MeasurableEquiv.piUnique fun _ => ℝ).symm x) by
    rw [updateFinset_singleton]; rfl, updateFinset_updateFinset hst]
  rfl

/-- **Peeling off one variable** `v ∉ W`. -/
theorem mint_union_singleton {W : Finset V} {v : V} (hv : v ∉ W) {F : (V → ℝ) → ℂ}
    {α₀ : V → ℝ} (hF : MInt (W ∪ {v}) F α₀) :
    mint (W ∪ {v}) F α₀ = mint W (fun α => ∫ x : ℝ, F (update α v x)) α₀ := by
  rw [mint_union (Finset.disjoint_singleton_right.2 hv) hF]
  simp_rw [mint_singleton]

theorem mint_congr_ae {W : Finset V} {F G : (V → ℝ) → ℂ} {α₀ : V → ℝ}
    (h : ∀ᵐ y : ↥W → ℝ ∂volume, F (updateFinset α₀ W y) = G (updateFinset α₀ W y)) :
    mint W F α₀ = mint W G α₀ :=
  integral_congr_ae h

theorem mint_neg (W : Finset V) (F : (V → ℝ) → ℂ) (α₀ : V → ℝ) :
    mint W (fun α => -F α) α₀ = -mint W F α₀ :=
  integral_neg _

theorem mint_empty (F : (V → ℝ) → ℂ) (α₀ : V → ℝ) : mint ∅ F α₀ = F α₀ := by
  unfold mint
  simp only [updateFinset_empty, integral_const]
  have h1 : (volume : Measure (↥(∅ : Finset V) → ℝ)) univ = 1 := by
    rw [volume_pi, Measure.pi_univ]; simp
  rw [Measure.real, h1]
  simp

end WaveTurbulence.Cancel
