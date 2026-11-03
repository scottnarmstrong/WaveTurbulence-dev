/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.ClassJR.Triple
public import WaveTurbulence.Foundations.ClassJR.CompKernel
public import Mathlib.Analysis.MeanInequalitiesPow

/-!
# Set-up for the composition lemmas

* `eJJ`: the coordinate permutation `((γ₁,γ₂),((γ₃,γ₄),q)) ↦ ((γ₁,γ₄),((γ₂,γ₃),q))` from the
  natural layout of a composition (the two input symbols, then the auxiliary variables) to the
  layout `(γ', η)` of `JSym.ofGen`; it preserves Lebesgue measure.
* `JSym.ofGenE`: generalized representations through a measure-preserving equivalence.
* bundles of the composed variables (`yDiff`, `yL`, `yR`) and elementary weight inequalities.
-/

public section

open MeasureTheory Set Filter Finset
open scoped ContDiff ENNReal

namespace WaveTurbulence.ClassJR

section Equiv

variable (Q : Type*) [MeasureSpace Q] [SFinite (volume : Measure Q)]

/-- The coordinate permutation `((γ₁,γ₂),((γ₃,γ₄),q)) ↦ ((γ₁,γ₄),((γ₂,γ₃),q))`. -/
@[expose] def eJJ : (ℝ × ℝ) × ((ℝ × ℝ) × Q) ≃ᵐ (ℝ × ℝ) × ((ℝ × ℝ) × Q) where
  toFun z := ((z.1.1, z.2.1.2), ((z.1.2, z.2.1.1), z.2.2))
  invFun z := ((z.1.1, z.2.1.1), ((z.2.1.2, z.1.2), z.2.2))
  left_inv z := rfl
  right_inv z := rfl
  measurable_toFun := by
    change Measurable fun z : (ℝ × ℝ) × ((ℝ × ℝ) × Q) =>
      ((z.1.1, z.2.1.2), ((z.1.2, z.2.1.1), z.2.2))
    fun_prop
  measurable_invFun := by
    change Measurable fun z : (ℝ × ℝ) × ((ℝ × ℝ) × Q) =>
      ((z.1.1, z.2.1.1), ((z.2.1.2, z.1.2), z.2.2))
    fun_prop

omit [SFinite (volume : Measure Q)] in
@[simp] theorem eJJ_apply (z : (ℝ × ℝ) × ((ℝ × ℝ) × Q)) :
    eJJ Q z = ((z.1.1, z.2.1.2), ((z.1.2, z.2.1.1), z.2.2)) := rfl

theorem measurePreserving_eJJ : MeasurePreserving (eJJ Q) := by
  have h1 := (volume_preserving_prodAssoc (α₁ := ℝ) (β₁ := ℝ) (γ₁ := (ℝ × ℝ) × Q))
  have h2 : MeasurePreserving (Prod.map (id : ℝ → ℝ)
      (MeasurableEquiv.prodAssoc (α := ℝ) (β := ℝ × ℝ) (γ := Q)).symm) :=
    MeasurePreserving.prod (MeasurePreserving.id volume) (volume_preserving_prodAssoc.symm _)
  have h3 : MeasurePreserving (Prod.map (id : ℝ → ℝ)
      (Prod.map (MeasurableEquiv.prodAssoc (α := ℝ) (β := ℝ) (γ := ℝ)).symm (id : Q → Q))) :=
    MeasurePreserving.prod (MeasurePreserving.id volume)
      (MeasurePreserving.prod (volume_preserving_prodAssoc.symm _) (MeasurePreserving.id volume))
  have h4 : MeasurePreserving (Prod.map (id : ℝ → ℝ)
      (Prod.map (Prod.swap : (ℝ × ℝ) × ℝ → ℝ × (ℝ × ℝ)) (id : Q → Q))) :=
    MeasurePreserving.prod (MeasurePreserving.id volume)
      (MeasurePreserving.prod Measure.measurePreserving_swap (MeasurePreserving.id volume))
  have h5 : MeasurePreserving (Prod.map (id : ℝ → ℝ)
      (MeasurableEquiv.prodAssoc (α := ℝ) (β := ℝ × ℝ) (γ := Q))) :=
    MeasurePreserving.prod (MeasurePreserving.id volume) volume_preserving_prodAssoc
  have h6 := (volume_preserving_prodAssoc (α₁ := ℝ) (β₁ := ℝ) (γ₁ := (ℝ × ℝ) × Q)).symm
  have := h6.comp (h5.comp (h4.comp (h3.comp (h2.comp h1))))
  convert this using 1
  funext z
  rfl

end Equiv

section OfGenE

variable {ι : Type*} [Fintype ι]
variable {Z : Type*} [MeasureSpace Z] {Q : Type*} [MeasureSpace Q] [SFinite (volume : Measure Q)]

/-- Regularity is invariant under measure-preserving changes of the auxiliary variables. -/
theorem SymReg.comp_equiv {Z' : Type*} [MeasureSpace Z'] {m : (ι → ℝ) → Z → ℂ} (h : SymReg m)
    (E : Z' ≃ᵐ Z) (hE : MeasurePreserving E) : SymReg fun α ζ => m α (E ζ) where
  smooth ζ := h.smooth (E ζ)
  meas := h.meas.comp_measurable (measurable_fst.prodMk (E.measurable.comp measurable_snd))
  dom k := by
    have : ∀ ζ, supD k (fun α ζ => m α (E ζ)) ζ = supD k m (E ζ) := fun ζ => rfl
    simp_rw [this]
    rw [hE.lintegral_comp_emb E.measurableEmbedding]
    exact h.dom k

/-- **Generalized class `J` representations through a measure-preserving equivalence.** -/
theorem JSym.ofGenE {y : ι → ℤ} (hy : IsBundle y) {a : (ι → ℝ) → Z → ℂ} (ha : SymReg a)
    (E : Z ≃ᵐ (ℝ × ℝ) × Q) (hE : MeasurePreserving E) {b : Q → ℝ × ℝ} (hb : Measurable b)
    {θ A N : ℝ} (hN : 0 ≤ N)
    (hnorm : ∀ k, ∫⁻ α, ∫⁻ z, wJ θ α ((E z).1.1 + (b (E z).2).1) * dnorm k a α z ≤ gev N A k) :
    ∃ R : JSym ι, R.y = y ∧ R.Bound θ A N ∧ ∀ α t s, R.kernel α t s =
      ∫ z, a α z * jker (bundle y α) ((E z).1.1 + (b (E z).2).1) ((E z).1.2 + (b (E z).2).2)
        t s := by
  have ha' : SymReg fun α ζ => a α (E.symm ζ) := ha.comp_equiv E.symm (hE.symm E)
  obtain ⟨R, hRy, hRb, hRk⟩ := JSym.ofGen (θ := θ) (A := A) hy ha' hb hN (fun k => by
    refine le_trans (le_of_eq ?_) (hnorm k)
    refine lintegral_congr fun α => ?_
    rw [← hE.lintegral_comp_emb E.measurableEmbedding]
    refine lintegral_congr fun z => ?_
    have key : lift1 (fun α ζ => a α (E.symm ζ)) (E z) = lift1 a z := by
      funext β
      simp [lift1]
    simp only [dnorm, key])
  refine ⟨R, hRy, hRb, fun α t s => ?_⟩
  rw [hRk, ← hE.integral_comp' (g := fun ζ => a α (E.symm ζ) *
    jker (bundle y α) (ζ.1.1 + (b ζ.2).1) (ζ.1.2 + (b ζ.2).2) t s)]
  simp only [MeasurableEquiv.symm_apply_apply]

end OfGenE

section Bundles

variable {ι₁ ι₂ : Type*} [Fintype ι₁] [Fintype ι₂]

/-- The bundle `ℓ₂(α_B) - ℓ₁(α_A)` of `α ∈ ι₁ ⊕ ι₂ → ℝ`. -/
@[expose] def yDiff (y₁ : ι₁ → ℤ) (y₂ : ι₂ → ℤ) : ι₁ ⊕ ι₂ → ℤ := Sum.elim (fun i => -y₁ i) y₂

/-- The bundle `ℓ₁(α_A)` of `α ∈ ι₁ ⊕ ι₂ → ℝ`. -/
@[expose] def yL (y₁ : ι₁ → ℤ) : ι₁ ⊕ ι₂ → ℤ := Sum.elim y₁ 0

/-- The bundle `ℓ₂(α_B)` of `α ∈ ι₁ ⊕ ι₂ → ℝ`. -/
@[expose] def yR (y₂ : ι₂ → ℤ) : ι₁ ⊕ ι₂ → ℤ := Sum.elim 0 y₂

theorem isBundle_yDiff {y₁ : ι₁ → ℤ} {y₂ : ι₂ → ℤ} (h₁ : IsBundle y₁) (h₂ : IsBundle y₂) :
    IsBundle (yDiff y₁ y₂) := by
  rintro (i | j)
  · simpa [yDiff] using h₁ i
  · simpa [yDiff] using h₂ j

theorem isBundle_yL {y₁ : ι₁ → ℤ} (h₁ : IsBundle y₁) : IsBundle (yL (ι₂ := ι₂) y₁) := by
  rintro (i | j)
  · simpa [yL] using h₁ i
  · simp [yL]

theorem isBundle_yR {y₂ : ι₂ → ℤ} (h₂ : IsBundle y₂) : IsBundle (yR (ι₁ := ι₁) y₂) := by
  rintro (i | j)
  · simp [yR]
  · simpa [yR] using h₂ j

theorem bundle_yDiff (y₁ : ι₁ → ℤ) (y₂ : ι₂ → ℤ) (α : ι₁ ⊕ ι₂ → ℝ) :
    bundle (yDiff y₁ y₂) α =
      bundle y₂ (fun i => α (Sum.inr i)) - bundle y₁ (fun i => α (Sum.inl i)) := by
  simp [bundle, yDiff, Fintype.sum_sum_type, sub_eq_neg_add, Finset.sum_neg_distrib]

theorem bundle_yL (y₁ : ι₁ → ℤ) (α : ι₁ ⊕ ι₂ → ℝ) :
    bundle (yL y₁) α = bundle y₁ (fun i => α (Sum.inl i)) := by
  simp [bundle, yL, Fintype.sum_sum_type]

theorem bundle_yR (y₂ : ι₂ → ℤ) (α : ι₁ ⊕ ι₂ → ℝ) :
    bundle (yR y₂) α = bundle y₂ (fun i => α (Sum.inr i)) := by
  simp [bundle, yR, Fintype.sum_sum_type]

theorem abs_bundle_le {ι : Type*} [Fintype ι] {y : ι → ℤ} (hy : IsBundle y) (α : ι → ℝ) :
    ‖bundle y α‖ₑ ≤ ∑ j, ‖α j‖ₑ := by
  unfold bundle
  refine (enorm_sum_le _ _).trans (Finset.sum_le_sum fun j _ => ?_)
  rw [enorm_mul]
  calc ‖(y j : ℝ)‖ₑ * ‖α j‖ₑ ≤ 1 * ‖α j‖ₑ := by
        gcongr
        rw [← ofReal_norm, Real.norm_eq_abs]
        simpa using (show |(y j : ℝ)| ≤ 1 by exact_mod_cast hy j)
    _ = _ := one_mul _

end Bundles

section Weights

/-- Subadditivity of `x ↦ x^θ` for `0 ≤ θ ≤ 1` on `ℝ≥0∞`. -/
theorem rpow_add_le {θ : ℝ} (h0 : 0 ≤ θ) (h1 : θ ≤ 1) (a b : ℝ≥0∞) :
    (a + b) ^ θ ≤ a ^ θ + b ^ θ :=
  ENNReal.rpow_add_le_add_rpow a b h0 h1

theorem rpow_le_one_add {θ : ℝ} (h0 : 0 ≤ θ) (h1 : θ ≤ 1) (a : ℝ≥0∞) : a ^ θ ≤ 1 + a := by
  rcases le_or_gt a 1 with ha | ha
  · exact (ENNReal.rpow_le_one ha h0).trans le_self_add
  · calc a ^ θ ≤ a ^ (1 : ℝ) := ENNReal.rpow_le_rpow_of_exponent_le ha.le h1
      _ = a := ENNReal.rpow_one a
      _ ≤ 1 + a := le_add_self

theorem rpow_mono' {θ : ℝ} (h0 : 0 ≤ θ) {a b : ℝ≥0∞} (h : a ≤ b) : a ^ θ ≤ b ^ θ :=
  ENNReal.rpow_le_rpow h h0

variable {ι : Type*} [Fintype ι]

theorem one_le_wJ {θ : ℝ} (h0 : 0 ≤ θ) (α : ι → ℝ) (γ₁ : ℝ) : 1 ≤ wJ θ α γ₁ := by
  unfold wJ
  rcases h0.eq_or_lt with rfl | hθ
  · simp
  · exact ENNReal.one_le_rpow (by rw [add_assoc]; exact le_self_add) hθ

theorem sum_rpow_le_wJ {θ : ℝ} (h0 : 0 ≤ θ) (α : ι → ℝ) (γ₁ : ℝ) :
    (∑ j, ‖α j‖ₑ) ^ θ ≤ wJ θ α γ₁ := by
  unfold wJ
  exact rpow_mono' h0 (by rw [add_assoc, add_comm, add_assoc]; exact le_self_add)

theorem measurable_wJ' {θ : ℝ} :
    Measurable (Function.uncurry fun (α : ι → ℝ) (γ : ℝ × ℝ) => wJ θ α γ.1) :=
  measurable_wJ θ

end Weights

end WaveTurbulence.ClassJR
