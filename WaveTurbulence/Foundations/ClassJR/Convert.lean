/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.ClassJR.ClassDef
public import Mathlib.MeasureTheory.Group.Integral
public import Mathlib.MeasureTheory.Group.LIntegral
public import Mathlib.MeasureTheory.Integral.Prod

/-!
# Generalized representations of class `J` and `R` operators

The composition lemmas of DH21 §5.2 produce operators of the form
`∫ a(α, u, η) J_{ℓ; u + b(η)} du dη`, where `u` runs over the two (or three) coordinates of a
class `J` (or `R`) symbol, `η` over auxiliary variables, and the new coefficients `γ' = u + b(η)`
are shifted by a measurable function of `η` alone (DH21 writes the resulting symbol as an integral
over the fibres `γ' = u + b(η)`, e.g. `m^{(3)}` in the proof of Lemma 5.3, L984–L986).

This module performs that pushforward once and for all. For a symbol `a(α, ζ)`, `ζ = (u, η)`,
`pushSym a b (α, γ) = ∫ a(α, γ - b η, η) dη` (set to zero on the null set where the derivatives of
the integrand are not integrable). We show

* `pushSym_symReg`: the pushforward of a regular symbol is regular;
* `lintegral_weight_pushSym_le`: weighted norms only decrease, with the weight evaluated at
  `γ' = u + b(η)`;
* `integral_pushSym_mul`: `∫ m(α, γ) φ(γ) dγ = ∫ a(α, ζ) φ(u + b(η)) dζ` for bounded `φ`,

and deduce `JSym.ofGen` and `RSym.ofGen`.
-/

public section

open MeasureTheory Set Filter
open scoped ContDiff ENNReal

namespace WaveTurbulence.ClassJR

/-- Right invariance of a product of right-invariant volumes. -/
theorem isAddRightInvariant_volume_prod {G H : Type*} [MeasureSpace G] [MeasureSpace H]
    [AddGroup G] [AddGroup H] [MeasurableAdd G] [MeasurableAdd H]
    [(volume : Measure G).IsAddRightInvariant] [(volume : Measure H).IsAddRightInvariant]
    [SFinite (volume : Measure H)] : (volume : Measure (G × H)).IsAddRightInvariant := by
  rw [Measure.volume_eq_prod]; infer_instance

attribute [local instance] isAddRightInvariant_volume_prod

section Shift

variable {Γ : Type*} [MeasureSpace Γ] [AddGroup Γ] [MeasurableAdd₂ Γ] [MeasurableSub₂ Γ]
  [(volume : Measure Γ).IsAddRightInvariant] [SFinite (volume : Measure Γ)]
variable {Q : Type*} [MeasureSpace Q] [SFinite (volume : Measure Q)]

/-- The shear `(γ, η) ↦ (γ + b η, η)`. -/
@[expose] noncomputable def shiftEquiv (b : Q → Γ) (hb : Measurable b) : Γ × Q ≃ᵐ Γ × Q where
  toFun p := (p.1 + b p.2, p.2)
  invFun p := (p.1 - b p.2, p.2)
  left_inv p := by simp
  right_inv p := by simp
  measurable_toFun := (measurable_fst.add (hb.comp measurable_snd)).prodMk measurable_snd
  measurable_invFun := (measurable_fst.sub (hb.comp measurable_snd)).prodMk measurable_snd

omit [(volume : Measure Γ).IsAddRightInvariant] [SFinite (volume : Measure Γ)]
  [SFinite (volume : Measure Q)] in
@[simp] theorem shiftEquiv_apply (b : Q → Γ) (hb : Measurable b) (p : Γ × Q) :
    shiftEquiv b hb p = (p.1 + b p.2, p.2) := rfl

omit [(volume : Measure Γ).IsAddRightInvariant] [SFinite (volume : Measure Γ)]
  [SFinite (volume : Measure Q)] in
@[simp] theorem shiftEquiv_symm_apply (b : Q → Γ) (hb : Measurable b) (p : Γ × Q) :
    (shiftEquiv b hb).symm p = (p.1 - b p.2, p.2) := rfl

/-- The shear preserves the product measure. -/
theorem measurePreserving_shiftEquiv (b : Q → Γ) (hb : Measurable b) :
    MeasurePreserving (shiftEquiv b hb) := by
  refine ⟨(shiftEquiv b hb).measurable, ?_⟩
  ext s hs
  rw [Measure.map_apply (shiftEquiv b hb).measurable hs, Measure.volume_eq_prod,
    Measure.prod_apply_symm hs, Measure.prod_apply_symm ((shiftEquiv b hb).measurable hs)]
  refine lintegral_congr fun η => ?_
  have : (fun x => (x, η)) ⁻¹' (shiftEquiv b hb ⁻¹' s) =
      (fun x => x + b η) ⁻¹' ((fun x => (x, η)) ⁻¹' s) := rfl
  rw [this, measure_preimage_add_right]

/-- Tonelli across the shear. -/
theorem lintegral_shift (b : Q → Γ) (hb : Measurable b) {G : Γ × Q → ℝ≥0∞}
    (hG : Measurable G) : ∫⁻ ζ : Γ × Q, G (ζ.1 + b ζ.2, ζ.2) = ∫⁻ γ, ∫⁻ η, G (γ, η) := by
  rw [← lintegral_prod _ hG.aemeasurable, ← Measure.volume_eq_prod]
  exact (measurePreserving_shiftEquiv b hb).lintegral_comp_emb
    (shiftEquiv b hb).measurableEmbedding G

/-- Bochner integrals are invariant under the shear. -/
theorem integral_shift (b : Q → Γ) (hb : Measurable b) (G : Γ × Q → ℂ) :
    ∫ ζ : Γ × Q, G (ζ.1 + b ζ.2, ζ.2) = ∫ ζ, G ζ :=
  (measurePreserving_shiftEquiv b hb).integral_comp' G

end Shift

section Push

variable {ι : Type*} [Fintype ι]
variable {Γ : Type*} [MeasureSpace Γ] [AddGroup Γ] [MeasurableAdd₂ Γ] [MeasurableSub₂ Γ]
  [(volume : Measure Γ).IsAddRightInvariant] [SFinite (volume : Measure Γ)]
variable {Q : Type*} [MeasureSpace Q] [SFinite (volume : Measure Q)]
variable {a : (ι → ℝ) → Γ × Q → ℂ} {b : Q → Γ}

/-- The set of `γ` at which every derivative of the integrand of the pushforward is dominated by
an integrable function of `η`. -/
@[expose] noncomputable def goodSet (a : (ι → ℝ) → Γ × Q → ℂ) (b : Q → Γ) : Set Γ :=
  {γ | ∀ k, ∫⁻ η, supD k a (γ - b η, η) ≠ ⊤}

/-- The pushforward symbol `m(α, γ) = ∫ a(α, γ - b η, η) dη`, set to zero off `goodSet a b`. -/
@[expose] noncomputable def pushSym (a : (ι → ℝ) → Γ × Q → ℂ) (b : Q → Γ) (α : ι → ℝ)
    (γ : Γ) : ℂ :=
  (goodSet a b).indicator (fun γ => ∫ η, a α (γ - b η, η)) γ

variable (ha : SymReg a) (hb : Measurable b)
include ha hb

omit [(volume : Measure Γ).IsAddRightInvariant] [SFinite (volume : Measure Γ)]
  [SFinite (volume : Measure Q)] in
theorem measurable_supD_shift (k : ℕ) :
    Measurable fun p : Γ × Q => supD k a (p.1 - b p.2, p.2) :=
  (measurable_supD ha.smooth ha.meas k).comp (shiftEquiv b hb).symm.measurable

theorem lintegral_supD_shift (k : ℕ) :
    ∫⁻ γ, ∫⁻ η, supD k a (γ - b η, η) = ∫⁻ ζ, supD k a ζ := by
  have := lintegral_shift b hb (measurable_supD_shift ha hb k)
  simp only [add_sub_cancel_right] at this
  exact this.symm

omit [(volume : Measure Γ).IsAddRightInvariant] [SFinite (volume : Measure Γ)] in
theorem measurableSet_goodSet : MeasurableSet (goodSet a b) := by
  have : goodSet a b = ⋂ k, (fun γ => ∫⁻ η, supD k a (γ - b η, η)) ⁻¹' {⊤}ᶜ := by
    ext γ; simp [goodSet]
  rw [this]
  exact MeasurableSet.iInter fun k =>
    (measurable_supD_shift ha hb k).lintegral_prod_right' (measurableSet_singleton ⊤).compl

theorem ae_mem_goodSet : ∀ᵐ γ, γ ∈ goodSet a b := by
  have h : ∀ k, ∀ᵐ γ : Γ, ∫⁻ η, supD k a (γ - b η, η) < ⊤ := fun k =>
    ae_lt_top (measurable_supD_shift ha hb k).lintegral_prod_right'
      (by rw [lintegral_supD_shift ha hb]; exact ha.dom k)
  filter_upwards [ae_all_iff.2 h] with γ hγ k using (hγ k).ne

omit ha hb [MeasureSpace Γ] [MeasurableAdd₂ Γ] [MeasurableSub₂ Γ]
  [(volume : Measure Γ).IsAddRightInvariant] [SFinite (volume : Measure Γ)]
  [SFinite (volume : Measure Q)] in
theorem lift1_pushSym_of_mem {γ : Γ} (hγ : γ ∈ goodSet a b) :
    lift1 (pushSym a b) γ = fun β => ∫ η, lift1 a (γ - b η, η) β := by
  funext β
  simp [lift1, pushSym, Set.indicator_of_mem hγ]

omit ha hb [MeasureSpace Γ] [MeasurableAdd₂ Γ] [MeasurableSub₂ Γ]
  [(volume : Measure Γ).IsAddRightInvariant] [SFinite (volume : Measure Γ)]
  [SFinite (volume : Measure Q)] in
theorem lift1_pushSym_of_notMem {γ : Γ} (hγ : γ ∉ goodSet a b) :
    lift1 (pushSym a b) γ = fun _ => 0 := by
  funext β
  simp [lift1, pushSym, Set.indicator_of_notMem hγ]

omit hb [MeasurableAdd₂ Γ] [MeasurableSub₂ Γ] [(volume : Measure Γ).IsAddRightInvariant]
  [SFinite (volume : Measure Γ)] [SFinite (volume : Measure Q)] in
/-- At a good point the integrand of the pushforward satisfies the hypotheses of
`iteratedFDeriv_integral_param`. -/
theorem push_smooth (γ : Γ) (η : Q) : ContDiff ℝ ∞ (fun β => lift1 a (γ - b η, η) β) :=
  contDiff_lift1 (ha.smooth _)

omit [MeasurableAdd₂ Γ] [(volume : Measure Γ).IsAddRightInvariant]
  [SFinite (volume : Measure Γ)] [SFinite (volume : Measure Q)] in
theorem push_meas (γ : Γ) (k : ℕ) (β : L1 ι) :
    AEStronglyMeasurable (fun η => iteratedFDeriv ℝ k (fun β' => lift1 a (γ - b η, η) β') β)
      volume :=
  (stronglyMeasurable_iteratedFDeriv_param (f := fun (β : L1 ι) (η : Q) => lift1 a (γ - b η, η) β)
    (fun η => push_smooth ha γ η)
    (fun _ => ha.meas.comp_measurable (measurable_const.prodMk
      ((measurable_const.sub hb).prodMk measurable_id))) k β).aestronglyMeasurable

omit [(volume : Measure Γ).IsAddRightInvariant] [SFinite (volume : Measure Γ)]
  [SFinite (volume : Measure Q)] in
theorem push_dom {γ : Γ} (hγ : γ ∈ goodSet a b) (k : ℕ) :
    ∃ B : Q → ℝ, Integrable B ∧
      ∀ᵐ η, ∀ β, ‖iteratedFDeriv ℝ k (fun β => lift1 a (γ - b η, η) β) β‖ ≤ B η := by
  have hmeas' : Measurable (Function.uncurry fun γ η => supD k a (γ - b η, η)) :=
    measurable_supD_shift ha hb k
  have hmeas : Measurable fun η => supD k a (γ - b η, η) := hmeas'.of_uncurry_left
  refine ⟨fun η => (supD k a (γ - b η, η)).toReal,
    integrable_toReal_of_lintegral_ne_top hmeas.aemeasurable (hγ k), ?_⟩
  filter_upwards [ae_lt_top hmeas (hγ k)] with η hη β
  have h : ‖iteratedFDeriv ℝ k (lift1 a (γ - b η, η)) β‖ₑ ≤ supD k a (γ - b η, η) :=
    dnorm_le_supD k a (WithLp.ofLp β) (γ - b η, η)
  rw [← toReal_enorm]
  exact ENNReal.toReal_mono hη.ne h

omit [(volume : Measure Γ).IsAddRightInvariant] [SFinite (volume : Measure Γ)]
  [SFinite (volume : Measure Q)] in
/-- The pointwise derivative bound for the pushforward. -/
theorem dnorm_pushSym_le (k : ℕ) (α : ι → ℝ) (γ : Γ) :
    dnorm k (pushSym a b) α γ ≤ ∫⁻ η, dnorm k a α (γ - b η, η) := by
  by_cases hγ : γ ∈ goodSet a b
  · have hD := iteratedFDeriv_integral_param (μ := (volume : Measure Q))
      (fun η => push_smooth ha γ η) (push_meas ha hb γ) (push_dom ha hb hγ) k
    rw [dnorm, lift1_pushSym_of_mem hγ, hD]
    exact enorm_integral_le_lintegral_enorm _
  · rw [dnorm, lift1_pushSym_of_notMem hγ, iteratedFDeriv_fun_zero]
    simp

/-- **The pushforward of a regular symbol is regular.** -/
theorem pushSym_symReg : SymReg (pushSym a b) where
  smooth γ := by
    by_cases hγ : γ ∈ goodSet a b
    · have h := contDiff_integral_param (μ := (volume : Measure Q))
        (fun η => push_smooth ha γ η) (push_meas ha hb γ) (push_dom ha hb hγ)
      rw [← lift1_pushSym_of_mem hγ] at h
      exact h.comp (PiLp.continuousLinearEquiv 1 ℝ (fun _ : ι => ℝ)).symm.contDiff
    · simp only [pushSym, Set.indicator_of_notMem hγ]
      exact contDiff_const
  meas := by
    have hint : StronglyMeasurable fun p : (ι → ℝ) × Γ => ∫ η, a p.1 (p.2 - b η, η) := by
      refine StronglyMeasurable.integral_prod_right'
        (f := fun q : ((ι → ℝ) × Γ) × Q => a q.1.1 (q.1.2 - b q.2, q.2)) ?_
      exact ha.meas.comp_measurable ((measurable_fst.comp measurable_fst).prodMk
        (((measurable_snd.comp measurable_fst).sub (hb.comp measurable_snd)).prodMk
          measurable_snd))
    have heq : Function.uncurry (pushSym a b) =
        (univ ×ˢ goodSet a b).indicator fun p : (ι → ℝ) × Γ => ∫ η, a p.1 (p.2 - b η, η) := by
      funext p
      by_cases hp : p.2 ∈ goodSet a b
      · rw [Set.indicator_of_mem (Set.mem_prod.2 ⟨Set.mem_univ _, hp⟩)]
        show pushSym a b p.1 p.2 = _
        simp [pushSym, Set.indicator_of_mem hp]
      · rw [Set.indicator_of_notMem (fun h => hp (Set.mem_prod.1 h).2)]
        show pushSym a b p.1 p.2 = _
        simp [pushSym, Set.indicator_of_notMem hp]
    rw [heq]
    exact hint.indicator (MeasurableSet.univ.prod (measurableSet_goodSet ha hb))
  dom k := by
    refine ne_top_of_le_ne_top (b := ∫⁻ γ, ∫⁻ η, supD k a (γ - b η, η)) ?_ ?_
    · rw [lintegral_supD_shift ha hb]; exact ha.dom k
    · refine lintegral_mono fun γ => iSup_le fun α => (dnorm_pushSym_le ha hb k α γ).trans ?_
      exact lintegral_mono fun η => dnorm_le_supD k a α _

/-- **Weighted norms of the pushforward**: the weight is evaluated at `γ' = u + b(η)`. -/
theorem lintegral_weight_pushSym_le {w : (ι → ℝ) → Γ → ℝ≥0∞}
    (hw : Measurable (Function.uncurry w)) (k : ℕ) :
    ∫⁻ α, ∫⁻ γ, w α γ * dnorm k (pushSym a b) α γ ≤
      ∫⁻ α, ∫⁻ ζ, w α (ζ.1 + b ζ.2) * dnorm k a α ζ := by
  refine lintegral_mono fun α => ?_
  have hd0 : Measurable (dnorm k a α) := (measurable_dnorm ha.smooth ha.meas k).of_uncurry_left
  have hd : Measurable fun p : Γ × Q => dnorm k a α (p.1 - b p.2, p.2) :=
    hd0.comp (shiftEquiv b hb).symm.measurable
  have hd' : ∀ γ, Measurable fun η => dnorm k a α (γ - b η, η) := fun γ => by
    have : Measurable (Function.uncurry fun γ η => dnorm k a α (γ - b η, η)) := hd
    exact this.of_uncurry_left
  have hwα : Measurable (w α) := hw.of_uncurry_left
  calc ∫⁻ γ, w α γ * dnorm k (pushSym a b) α γ
      ≤ ∫⁻ γ, w α γ * ∫⁻ η, dnorm k a α (γ - b η, η) :=
        lintegral_mono fun γ => mul_le_mul_right (dnorm_pushSym_le ha hb k α γ) _
    _ = ∫⁻ γ, ∫⁻ η, w α γ * dnorm k a α (γ - b η, η) := by
        refine lintegral_congr fun γ => ?_
        exact (lintegral_const_mul _ (hd' γ)).symm
    _ = ∫⁻ ζ : Γ × Q, w α (ζ.1 + b ζ.2) * dnorm k a α (ζ.1 + b ζ.2 - b ζ.2, ζ.2) :=
        (lintegral_shift b hb (G := fun p => w α p.1 * dnorm k a α (p.1 - b p.2, p.2))
          ((hwα.comp measurable_fst).mul hd)).symm
    _ = _ := by simp only [add_sub_cancel_right]

/-- **Integrals against bounded functions** are unchanged by the pushforward. -/
theorem integral_pushSym_mul (α : ι → ℝ) {φ : Γ → ℂ} (hφ : AEStronglyMeasurable φ)
    {C : ℝ} (hφC : ∀ γ, ‖φ γ‖ ≤ C) :
    ∫ γ, pushSym a b α γ * φ γ = ∫ ζ, a α ζ * φ (ζ.1 + b ζ.2) := by
  have hae : (fun γ => pushSym a b α γ * φ γ) =ᵐ[volume]
      fun γ => (∫ η, a α (γ - b η, η)) * φ γ := by
    filter_upwards [ae_mem_goodSet ha hb] with γ hγ
    simp [pushSym, Set.indicator_of_mem hγ]
  rw [integral_congr_ae hae]
  -- the integrand on the product
  set G : Γ × Q → ℂ := fun p => a α (p.1 - b p.2, p.2) * φ p.1 with hG
  have hsh : Integrable (fun p : Γ × Q => a α (p.1 - b p.2, p.2)) := by
    have := ((measurePreserving_shiftEquiv b hb).symm (shiftEquiv b hb)).integrable_comp_emb
      (shiftEquiv b hb).symm.measurableEmbedding (g := a α)
    exact this.2 (ha.integrable α)
  have hGi : Integrable G := by
    refine Integrable.mono' (hsh.norm.const_mul (max C 0)) ?_ ?_
    · exact hsh.aestronglyMeasurable.mul (hφ.comp_quasiMeasurePreserving
        (Measure.quasiMeasurePreserving_fst))
    · refine Eventually.of_forall fun p => ?_
      rw [hG, norm_mul, mul_comm]
      exact mul_le_mul_of_nonneg_right ((hφC p.1).trans (le_max_left _ _)) (norm_nonneg _)
  have h1 : ∫ γ, (∫ η, a α (γ - b η, η)) * φ γ = ∫ p, G p := by
    rw [Measure.volume_eq_prod, integral_prod G hGi]
    refine integral_congr_ae (Eventually.of_forall fun γ => ?_)
    simp only [hG]
    rw [integral_mul_const]
  have h2 : ∫ ζ, a α ζ * φ (ζ.1 + b ζ.2) = ∫ p, G p := by
    rw [← integral_shift b hb G]
    simp only [hG, add_sub_cancel_right]
  rw [h1, h2]

end Push

section Corollaries

variable {ι : Type*} [Fintype ι]
variable {Q : Type*} [MeasureSpace Q] [SFinite (volume : Measure Q)]

theorem measurable_wJ (θ : ℝ) :
    Measurable (Function.uncurry fun (α : ι → ℝ) (γ : ℝ × ℝ) => wJ θ α γ.1) := by
  unfold wJ
  fun_prop

theorem measurable_wR (θ : ℝ) :
    Measurable (Function.uncurry fun (α : ι → ℝ) (γ : ℝ × ℝ × ℝ) => wR θ α γ.1 γ.2.2) := by
  unfold wR
  fun_prop

/-- **Generalized class `J` representations.** A kernel `∫ a(α, u, η) J_{ℓ; u + b(η)} du dη` with
a regular symbol `a` and the weighted bounds evaluated at `γ' = u + b(η)` is a basic class `J`
kernel with the same bound. -/
theorem JSym.ofGen {y : ι → ℤ} (hy : IsBundle y) {a : (ι → ℝ) → (ℝ × ℝ) × Q → ℂ}
    (ha : SymReg a) {b : Q → ℝ × ℝ} (hb : Measurable b) {θ A N : ℝ} (hN : 0 ≤ N)
    (hnorm : ∀ k, ∫⁻ α, ∫⁻ ζ, wJ θ α (ζ.1.1 + (b ζ.2).1) * dnorm k a α ζ ≤ gev N A k) :
    ∃ R : JSym ι, R.y = y ∧ R.Bound θ A N ∧ ∀ α t s, R.kernel α t s =
      ∫ ζ, a α ζ * jker (bundle y α) (ζ.1.1 + (b ζ.2).1) (ζ.1.2 + (b ζ.2).2) t s := by
  refine ⟨⟨y, pushSym a b⟩, rfl, ⟨hN, hy, pushSym_symReg ha hb, fun k => ?_⟩, fun α t s => ?_⟩
  · refine le_trans ?_ (hnorm k)
    have := lintegral_weight_pushSym_le ha hb (measurable_wJ (ι := ι) θ) k
    simpa only [jNorm, Prod.fst_add] using this
  · have hcont : Continuous fun γ : ℝ × ℝ => jker (bundle y α) γ.1 γ.2 t s := by
      unfold jker; fun_prop
    have := integral_pushSym_mul ha hb α hcont.aestronglyMeasurable (C := 1) (fun γ => by
      rw [jker, Complex.norm_exp]
      simp)
    simpa only [JSym.kernel, Prod.fst_add, Prod.snd_add] using this

end Corollaries

end WaveTurbulence.ClassJR
