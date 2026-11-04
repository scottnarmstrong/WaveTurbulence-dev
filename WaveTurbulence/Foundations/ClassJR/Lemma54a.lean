/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.ClassJR.CompJR2

/-!
# DH21 Lemma 5.4, first half: `𝒥^{(1)} ℛ^{(2)}` is of class `J`

`ClassJ.comp_R`: if `T₁` (variables `α ∘ inl`) has class `J` and `T₂` (variables `α ∘ inr`,
special variable `α (inr none)`) has class `R`, then `T₁ T₂` has class `J` with norm at most
`CJR θ · N₁ · N₂`, for `0 ≤ θ < 1` and `A ≥ A0`.
-/

public section

open MeasureTheory Set Filter Finset Complex
open scoped ContDiff ENNReal Real

namespace WaveTurbulence.ClassJR

open WaveTurbulence.Fourier

section Fubini

variable {Z₁ Z₂ : Type*} [MeasureSpace Z₁] [MeasureSpace Z₂] [SFinite (volume : Measure Z₁)]
  [SFinite (volume : Measure Z₂)]

/-- **Fubini for compositions of superpositions of `J` kernels.** -/
theorem kcomp_integral_jker {f₁ : Z₁ → ℂ} {f₂ : Z₂ → ℂ} (hf₁ : Integrable f₁)
    (hf₂ : Integrable f₂) (L₁ L₂ : ℝ) {u₁ v₁ : Z₁ → ℝ} {u₂ v₂ : Z₂ → ℝ} (hu₁ : Measurable u₁)
    (hv₁ : Measurable v₁) (hu₂ : Measurable u₂) (hv₂ : Measurable v₂) {t s : ℝ} (hst : s ≤ t) :
    kcomp (fun t s => ∫ p, f₁ p * jker L₁ (u₁ p) (v₁ p) t s)
        (fun t s => ∫ p, f₂ p * jker L₂ (u₂ p) (v₂ p) t s) t s =
      ∫ pp : Z₁ × Z₂, f₁ pp.1 * f₂ pp.2 *
        kcomp (jker L₁ (u₁ pp.1) (v₁ pp.1)) (jker L₂ (u₂ pp.2) (v₂ pp.2)) t s := by
  have hm : Integrable (fun pp : Z₁ × Z₂ => f₁ pp.1 * f₂ pp.2) := by
    rw [Measure.volume_eq_prod]; exact hf₁.mul_prod hf₂
  set F : ℝ → Z₁ × Z₂ → ℂ := fun z pp =>
    f₁ pp.1 * f₂ pp.2 * (jker L₁ (u₁ pp.1) (v₁ pp.1) t z * jker L₂ (u₂ pp.2) (v₂ pp.2) z s)
    with hF
  have hJ : Measurable fun q : ℝ × (Z₁ × Z₂) =>
      jker L₁ (u₁ q.2.1) (v₁ q.2.1) t q.1 * jker L₂ (u₂ q.2.2) (v₂ q.2.2) q.1 s := by
    unfold jker
    have h1 : Measurable fun q : ℝ × (Z₁ × Z₂) => u₁ q.2.1 := hu₁.comp (measurable_fst.comp
      measurable_snd)
    have h2 : Measurable fun q : ℝ × (Z₁ × Z₂) => v₁ q.2.1 := hv₁.comp (measurable_fst.comp
      measurable_snd)
    have h3 : Measurable fun q : ℝ × (Z₁ × Z₂) => u₂ q.2.2 := hu₂.comp (measurable_snd.comp
      measurable_snd)
    have h4 : Measurable fun q : ℝ × (Z₁ × Z₂) => v₂ q.2.2 := hv₂.comp (measurable_snd.comp
      measurable_snd)
    fun_prop
  have hFi : Integrable (Function.uncurry F) ((volume.restrict (Ioc s t)).prod volume) := by
    have hb : Integrable (fun q : ℝ × (Z₁ × Z₂) => ‖f₁ q.2.1 * f₂ q.2.2‖)
        ((volume.restrict (Ioc s t)).prod volume) :=
      ((integrable_const (1 : ℝ)).mul_prod hm.norm).congr (Eventually.of_forall fun q => by simp)
    refine hb.mono' ((hm.aestronglyMeasurable.comp_snd).mul hJ.aestronglyMeasurable)
      (Eventually.of_forall fun q => ?_)
    simp only [Function.uncurry, hF, norm_mul, norm_jker, mul_one]
    exact le_refl _
  calc kcomp (fun t s => ∫ p, f₁ p * jker L₁ (u₁ p) (v₁ p) t s)
        (fun t s => ∫ p, f₂ p * jker L₂ (u₂ p) (v₂ p) t s) t s
      = ∫ z in Ioc s t, ∫ pp : Z₁ × Z₂, F z pp := by
        rw [kcomp, intervalIntegral.integral_of_le hst]
        refine setIntegral_congr_fun measurableSet_Ioc fun z _ => ?_
        simp only [hF]
        have h := integral_prod_mul (μ := (volume : Measure Z₁)) (ν := (volume : Measure Z₂))
          (fun p => f₁ p * jker L₁ (u₁ p) (v₁ p) t z)
          (fun p => f₂ p * jker L₂ (u₂ p) (v₂ p) z s)
        rw [← Measure.volume_eq_prod] at h
        rw [← h]
        refine integral_congr_ae (Eventually.of_forall fun p => ?_)
        simp only
        ring
    _ = ∫ pp : Z₁ × Z₂, ∫ z in Ioc s t, F z pp := integral_integral_swap hFi
    _ = _ := by
        refine integral_congr_ae (Eventually.of_forall fun p => ?_)
        simp only [hF, kcomp]
        rw [MeasureTheory.integral_const_mul, intervalIntegral.integral_of_le hst]

end Fubini

section RKernel

variable {ι : Type*} [Fintype ι]

theorem norm_chiInvR_le (x : ℝ) : ‖(chiInvR x : ℂ)‖ ≤ CPhi := by
  have := chiInvR_gevrey 0 x
  simp only [iteratedDeriv_zero, pow_zero, mul_one, Nat.mul_zero, Nat.factorial_zero,
    Nat.cast_one] at this
  rw [Complex.norm_real]
  exact le_trans (le_mul_of_one_le_left (norm_nonneg _) (by linarith [abs_nonneg x])) this

/-- The basic class `R` kernel as a superposition of `J` kernels. -/
theorem RSym.kernel_eq (R : RSym ι) (α : Option ι → ℝ) (t s : ℝ) :
    R.kernel α t s = ∫ γ : ℝ × (ℝ × ℝ),
      (R.m (nsp α) γ * (chiInvR (bundle R.y₁ (nsp α) + R.ε * α none + γ.2.2) : ℂ)) *
        jker (bundle R.y₂ (nsp α) + R.ε * α none) γ.1 γ.2.1 t s := by
  simp only [RSym.kernel, rker]
  refine integral_congr_ae (Eventually.of_forall fun γ => ?_)
  simp only
  ring

theorem RSym.integrable_coeff (R : RSym ι) {θ A N : ℝ} (h : R.Bound θ A N) (α : Option ι → ℝ) :
    Integrable fun γ : ℝ × (ℝ × ℝ) =>
      R.m (nsp α) γ * (chiInvR (bundle R.y₁ (nsp α) + R.ε * α none + γ.2.2) : ℂ) := by
  refine ((h.reg.integrable (nsp α)).norm.const_mul CPhi).mono' ?_
    (Eventually.of_forall fun γ => ?_)
  · exact (h.reg.integrable (nsp α)).aestronglyMeasurable.mul
      ((contDiff_chiInvRc.continuous.comp (continuous_const.add
        (continuous_snd.comp continuous_snd))).aestronglyMeasurable)
  · rw [norm_mul, mul_comm]
    exact mul_le_mul_of_nonneg_right (norm_chiInvR_le _) (norm_nonneg _)

/-- Basic class `R` kernels are continuous in `(t, s)`. -/
theorem RSym.continuous_kernel (R : RSym ι) {θ A N : ℝ} (h : R.Bound θ A N)
    (α : Option ι → ℝ) : Continuous fun p : ℝ × ℝ => R.kernel α p.1 p.2 := by
  simp_rw [RSym.kernel_eq]
  refine continuous_of_dominated (bound := fun γ => ‖R.m (nsp α) γ *
      (chiInvR (bundle R.y₁ (nsp α) + R.ε * α none + γ.2.2) : ℂ)‖) (fun p => ?_) (fun p => ?_)
    (R.integrable_coeff h α).norm (Eventually.of_forall fun γ => ?_)
  · exact (R.integrable_coeff h α).aestronglyMeasurable.mul
      (by unfold jker; fun_prop : Continuous fun γ : ℝ × (ℝ × ℝ) =>
        jker (bundle R.y₂ (nsp α) + R.ε * α none) γ.1 γ.2.1 p.1 p.2).aestronglyMeasurable
  · exact Eventually.of_forall fun γ => by rw [norm_mul, norm_jker, mul_one]
  · exact continuous_const.mul (continuous_jker _ _ _)

end RKernel

section Identity

variable {ι₁ ι₂ : Type*} [Fintype ι₁] [Fintype ι₂]

/-- The variables of the class `R` operator inside `α ∈ (ι₁ ⊕ ι₂) ⊕ Unit → ℝ`. -/
@[expose] def optB (β : (ι₁ ⊕ ι₂) ⊕ Unit → ℝ) : Option ι₂ → ℝ :=
  fun o => o.elim (β (Sum.inr ())) fun j => β (Sum.inl (Sum.inr j))

omit [Fintype ι₁] [Fintype ι₂] in
theorem nsp_optB (β : (ι₁ ⊕ ι₂) ⊕ Unit → ℝ) : nsp (optB β) = vB β := rfl

omit [Fintype ι₁] [Fintype ι₂] in
theorem optB_none (β : (ι₁ ⊕ ι₂) ⊕ Unit → ℝ) : optB β none = β (Sum.inr ()) := rfl

/-- **The kernel identity of `J R`** for basic operators (DH21 L1009–L1017). -/
theorem kcomp_JR_basic_eq (R₁ : JSym ι₁) (R₂ : RSym ι₂) {θ A N₁ N₂ : ℝ}
    (h₁ : R₁.Bound θ A N₁) (h₂ : R₂.Bound θ A N₂) (α : (ι₁ ⊕ ι₂) ⊕ Unit → ℝ) {t s : ℝ}
    (hst : s ≤ t) (h1 : t - s ≤ 1) :
    kcomp (R₁.kernel (vA α)) (R₂.kernel (optB α)) t s =
      (∫ z, tripleS R₁.m R₂.m KMR (LsJR R₁ R₂) (csJR (ℝ × ℝ)) α z *
        jker (bundle (yJRL (ι₂ := ι₂) R₁) α) ((eJR (ℝ × ℝ) z).1.1 + (bMR (eJR (ℝ × ℝ) z).2).1)
          ((eJR (ℝ × ℝ) z).1.2 + (bMR (eJR (ℝ × ℝ) z).2).2) t s) +
      (∫ z, tripleS R₁.m R₂.m KPR (LsJR R₁ R₂) (csJR Unit) α z *
        jker (bundle (yJRR (ι₁ := ι₁) R₂) α) ((eJR Unit z).1.1 + (bP1R (eJR Unit z).2).1)
          ((eJR Unit z).1.2 + (bP1R (eJR Unit z).2).2) t s) +
      (∫ z, tripleS R₁.m R₂.m KPRn (LsJR R₁ R₂) (csJR Unit) α z *
        jker (bundle (yJRL (ι₂ := ι₂) R₁) α) ((eJR Unit z).1.1 + (bP2R (eJR Unit z).2).1)
          ((eJR Unit z).1.2 + (bP2R (eJR Unit z).2).2) t s) := by
  set ℓ₁ := bundle R₁.y (vA α)
  set L₂ := bundle R₂.y₂ (vB α) + R₂.ε * α (Sum.inr ())
  set dd := bundle R₂.y₁ (vB α) + R₂.ε * α (Sum.inr ())
  have hJm : ∀ (y : (ι₁ ⊕ ι₂) ⊕ Unit → ℤ) {Z : Type} [MeasureSpace Z] (u v : Z → ℝ),
      Measurable u → Measurable v →
        AEStronglyMeasurable fun z => jker (bundle y α) (u z) (v z) t s :=
    fun y Z _ u v hu hv => ((continuous_jker_coeff (bundle y α) t s).measurable.comp
      (hu.prodMk hv)).aestronglyMeasurable
  have mM1 : Measurable fun z : (ℝ × ℝ) × ((ℝ × (ℝ × ℝ)) × (ℝ × ℝ)) =>
      (eJR (ℝ × ℝ) z).1.1 + (bMR (eJR (ℝ × ℝ) z).2).1 := by simp only [eJR_apply, bMR]; fun_prop
  have mM2 : Measurable fun z : (ℝ × ℝ) × ((ℝ × (ℝ × ℝ)) × (ℝ × ℝ)) =>
      (eJR (ℝ × ℝ) z).1.2 + (bMR (eJR (ℝ × ℝ) z).2).2 := by simp only [eJR_apply, bMR]; fun_prop
  have mP11 : Measurable fun z : (ℝ × ℝ) × ((ℝ × (ℝ × ℝ)) × Unit) =>
      (eJR Unit z).1.1 + (bP1R (eJR Unit z).2).1 := by simp only [eJR_apply, bP1R]; fun_prop
  have mP12 : Measurable fun z : (ℝ × ℝ) × ((ℝ × (ℝ × ℝ)) × Unit) =>
      (eJR Unit z).1.2 + (bP1R (eJR Unit z).2).2 := by simp only [eJR_apply, bP1R]; fun_prop
  have mP21 : Measurable fun z : (ℝ × ℝ) × ((ℝ × (ℝ × ℝ)) × Unit) =>
      (eJR Unit z).1.1 + (bP2R (eJR Unit z).2).1 := by simp only [eJR_apply, bP2R]; fun_prop
  have mP22 : Measurable fun z : (ℝ × ℝ) × ((ℝ × (ℝ × ℝ)) × Unit) =>
      (eJR Unit z).1.2 + (bP2R (eJR Unit z).2).2 := by simp only [eJR_apply, bP2R]; fun_prop
  set FM : (ℝ × ℝ) × ((ℝ × (ℝ × ℝ)) × (ℝ × ℝ)) → ℂ := fun z =>
    tripleS R₁.m R₂.m KMR (LsJR R₁ R₂) (csJR (ℝ × ℝ)) α z *
      jker (bundle (yJRL (ι₂ := ι₂) R₁) α) ((eJR (ℝ × ℝ) z).1.1 + (bMR (eJR (ℝ × ℝ) z).2).1)
        ((eJR (ℝ × ℝ) z).1.2 + (bMR (eJR (ℝ × ℝ) z).2).2) t s with hFMd
  set F1 : (ℝ × ℝ) × ((ℝ × (ℝ × ℝ)) × Unit) → ℂ := fun z =>
    tripleS R₁.m R₂.m KPR (LsJR R₁ R₂) (csJR Unit) α z *
      jker (bundle (yJRR (ι₁ := ι₁) R₂) α) ((eJR Unit z).1.1 + (bP1R (eJR Unit z).2).1)
        ((eJR Unit z).1.2 + (bP1R (eJR Unit z).2).2) t s with hF1d
  set F2 : (ℝ × ℝ) × ((ℝ × (ℝ × ℝ)) × Unit) → ℂ := fun z =>
    tripleS R₁.m R₂.m KPRn (LsJR R₁ R₂) (csJR Unit) α z *
      jker (bundle (yJRL (ι₂ := ι₂) R₁) α) ((eJR Unit z).1.1 + (bP2R (eJR Unit z).2).1)
        ((eJR Unit z).1.2 + (bP2R (eJR Unit z).2).2) t s with hF2d
  have hFM : Integrable FM := integrable_mul_unimodular
    ((symReg_piece_JR_M h₁ h₂).integrable α) (hJm _ _ _ mM1 mM2) (fun z => norm_jker _ _ _ _ _)
  have hF1 : Integrable F1 := integrable_mul_unimodular
    ((symReg_piece_JR_P1 h₁ h₂).integrable α) (hJm _ _ _ mP11 mP12)
    (fun z => norm_jker _ _ _ _ _)
  have hF2 : Integrable F2 := integrable_mul_unimodular
    ((symReg_piece_JR_P2 h₁ h₂).integrable α) (hJm _ _ _ mP21 mP22)
    (fun z => norm_jker _ _ _ _ _)
  have hGM := integrable_reassoc hFM
  have hG1 := integrable_reassoc hF1
  have hG2 := integrable_reassoc hF2
  have hG12 : Integrable fun p : (ℝ × ℝ) × (ℝ × (ℝ × ℝ)) =>
      (∫ q, FM (p.1, (p.2, q))) + ∫ q, F1 (p.1, (p.2, q)) := hGM.add hG1
  have hK1 : R₁.kernel (vA α) = fun t s => ∫ γ : ℝ × ℝ, R₁.m (vA α) γ *
      jker ℓ₁ γ.1 γ.2 t s := rfl
  have hK2 : R₂.kernel (optB α) = fun t s => ∫ γ : ℝ × (ℝ × ℝ),
      (R₂.m (vB α) γ * (chiInvR (dd + γ.2.2) : ℂ)) * jker L₂ γ.1 γ.2.1 t s := by
    funext t s
    rw [RSym.kernel_eq]
    rfl
  have hf₂ : Integrable fun γ : ℝ × (ℝ × ℝ) => R₂.m (vB α) γ * (chiInvR (dd + γ.2.2) : ℂ) :=
    R₂.integrable_coeff h₂ (optB α)
  have hv₂ : Measurable fun γ : ℝ × (ℝ × ℝ) => γ.2.1 := measurable_fst.comp measurable_snd
  rw [hK1, hK2, kcomp_integral_jker (h₁.reg.integrable _) hf₂ ℓ₁ L₂
    measurable_fst measurable_snd measurable_fst hv₂ hst,
    ← integral_reassoc hFM, ← integral_reassoc hF1, ← integral_reassoc hF2,
    ← integral_add hGM hG1, ← integral_add hG12 hG2]
  refine integral_congr_ae (Eventually.of_forall fun p => ?_)
  beta_reduce
  have hx : ∀ {Q : Type} (q : Q), formsV (LsJR R₁ R₂) (csJR Q) α (p.1, (p.2, q)) 0 =
      L₂ - ℓ₁ + p.1.2 + p.2.1 := fun q => by
    rw [formsV_JR_zero]; simp only [L₂, ℓ₁]; ring
  have hw : ∀ {Q : Type} (q : Q), formsV (LsJR R₁ R₂) (csJR Q) α (p.1, (p.2, q)) 1 =
      dd + p.2.2.2 := fun q => by
    rw [formsV_JR_one]; simp only [dd]; ring
  have e1 : p.1.1 + (p.1.2 + p.2.1) = p.1.1 + p.1.2 + p.2.1 := by ring
  have e2 : p.2.2.1 + (p.1.2 + p.2.1) = p.1.2 + p.2.1 + p.2.2.1 := by ring
  have e3 : ∀ q : ℝ × ℝ, p.2.2.1 + (p.1.2 + p.2.1 - q.1) = p.1.2 + p.2.1 + p.2.2.1 - q.1 :=
    fun q => by ring
  have hyL : bundle (yJRL (ι₂ := ι₂) R₁) α = ℓ₁ := by
    simp only [ℓ₁]; rw [yJRL, bundle_y3]; simp [bundle]
  have hyR : bundle (yJRR (ι₁ := ι₁) R₂) α = L₂ := by
    simp only [L₂]; rw [yJRR, bundle_y3]; simp [bundle]
  have hqM : ∫ q, FM (p.1, (p.2, q)) = R₁.m (vA α) p.1 * R₂.m (vB α) p.2 *
      (chiInvR (dd + p.2.2.2) : ℂ) * ∫ q : ℝ × ℝ, kerM (L₂ - ℓ₁ + p.1.2 + p.2.1) q *
        jker ℓ₁ (p.1.1 + q.1) (p.1.2 + p.2.1 + p.2.2.1 - q.1) t s := by
    rw [← MeasureTheory.integral_const_mul]
    refine integral_congr_ae (Eventually.of_forall fun q => ?_)
    simp only [hFMd, tripleS, eJR_apply, bMR, KMR, hx, hw, hyL, e3]
    ring
  have hq1 : F1 (p.1, (p.2, ())) = R₁.m (vA α) p.1 * R₂.m (vB α) p.2 *
      (chiInvR (dd + p.2.2.2) : ℂ) * (phiR (L₂ - ℓ₁ + p.1.2 + p.2.1) *
        jker L₂ (p.1.1 + p.1.2 + p.2.1) p.2.2.1 t s) := by
    simp only [hF1d, tripleS, eJR_apply, bP1R, KPR, hx, hw, hyR, e1, add_zero]
    ring
  have hq2 : F2 (p.1, (p.2, ())) = -(R₁.m (vA α) p.1 * R₂.m (vB α) p.2 *
      (chiInvR (dd + p.2.2.2) : ℂ) * (phiR (L₂ - ℓ₁ + p.1.2 + p.2.1) *
        jker ℓ₁ p.1.1 (p.1.2 + p.2.1 + p.2.2.1) t s)) := by
    simp only [hF2d, tripleS, eJR_apply, bP2R, KPRn, hx, hw, hyL, e2, add_zero]
    ring
  rw [kcomp_jker_split _ _ _ _ _ _ (by linarith) h1, integral_unit, integral_unit, hqM, hq1, hq2]
  ring

end Identity

section Assembly

variable {ι₁ ι₂ : Type*} [Fintype ι₁] [Fintype ι₂]

/-- The constant of `J R` (DH21 Lemma 5.4). -/
@[expose] noncomputable def CJR (θ : ℝ) : ℝ :=
  3 * (16 * 3 * (16 * (CkM * IM) * CPhi)) + 3 * (16 * 2 * 6 * (16 * Cθ θ * (CPhi * CPhi))) +
    3 * (16 * 3 * (16 * Cθ θ * (CPhi * CPhi)))

theorem CJR_nonneg {θ : ℝ} (h0 : 0 ≤ θ) (h1 : θ < 1) : 0 ≤ CJR θ := by
  have := kerM_bound.1; have := IM_nonneg; have := CPhi_nonneg; have := Cθ_nonneg h0 h1
  unfold CJR; positivity

/-- **`J R` for basic operators.** -/
theorem jsym_comp_JR {θ A N₁ N₂ : ℝ} (h0 : 0 ≤ θ) (h1 : θ < 1) (hA : A0 ≤ A) {R₁ : JSym ι₁}
    {R₂ : RSym ι₂} (h₁ : R₁.Bound θ A N₁) (h₂ : R₂.Bound θ A N₂) :
    ∃ (S : Fin 3 → JSym ((ι₁ ⊕ ι₂) ⊕ Unit)) (c : Fin 3 → ℝ), (∀ p, (S p).Bound θ A (c p)) ∧
      ∑ p, c p = CJR θ * N₁ * N₂ ∧
      ∀ α, KEqOn (kcomp (R₁.kernel (vA α)) (R₂.kernel (optB α)))
        fun t s => ∑ p, (S p).kernel α t s := by
  obtain ⟨SM, hSM, hkM⟩ := exists_piece_JR_M h0 h1.le hA h₁ h₂
  obtain ⟨S1, hS1, hk1⟩ := exists_piece_JR_P1 h0 h1 hA h₁ h₂
  obtain ⟨S2, hS2, hk2⟩ := exists_piece_JR_P2 h0 h1 hA h₁ h₂
  refine ⟨![SM, S1, S2], ![3 * (16 * N₁ * (3 * N₂) * (16 * (CkM * IM) * CPhi)),
    3 * (16 * (2 * N₁) * (6 * N₂) * (16 * Cθ θ * (CPhi * CPhi))),
    3 * (16 * N₁ * (3 * N₂) * (16 * Cθ θ * (CPhi * CPhi)))], ?_, ?_, ?_⟩
  · intro p; fin_cases p
    · exact hSM
    · exact hS1
    · exact hS2
  · simp only [Fin.sum_univ_three, Matrix.cons_val, CJR]
    ring
  · intro α t s _ hst ht1
    simp only [Fin.sum_univ_three, Matrix.cons_val]
    rw [hkM, hk1, hk2]
    exact kcomp_JR_basic_eq _ _ h₁ h₂ α hst (by linarith)

/-- `J R` on the variables `(ι₁ ⊕ ι₂) ⊕ Unit`. -/
theorem ClassJ.comp_R' {θ A N₁ N₂ : ℝ} (h0 : 0 ≤ θ) (h1 : θ < 1) (hA : A0 ≤ A)
    {T₁ : (ι₁ → ℝ) → ℝ → ℝ → ℂ} {T₂ : (Option ι₂ → ℝ) → ℝ → ℝ → ℂ} (hT₁ : ClassJ θ A N₁ T₁)
    (hT₂ : ClassR θ A N₂ T₂) :
    ClassJ θ A (CJR θ * N₁ * N₂) fun α : (ι₁ ⊕ ι₂) ⊕ Unit → ℝ =>
      kcomp (T₁ (vA α)) (T₂ (optB α)) := by
  obtain ⟨n₁, Ra, ca, hba, hsa, hea⟩ := hT₁
  obtain ⟨n₂, Rb, cb, hbb, hsb, heb⟩ := hT₂
  choose S c hSb hcs hSk using fun i j => jsym_comp_JR h0 h1 hA (hba i) (hbb j)
  have hca : 0 ≤ ∑ i, ca i := Finset.sum_nonneg fun i _ => (hba i).nonneg
  have hcb : 0 ≤ ∑ j, cb j := Finset.sum_nonneg fun j _ => (hbb j).nonneg
  have hC := CJR_nonneg h0 h1
  refine ClassJ.of_fintype (B := Fin n₁ × Fin n₂ × Fin 3) (fun b => S b.1 b.2.1 b.2.2)
    (fun b => c b.1 b.2.1 b.2.2) (fun b => hSb _ _ _) ?_ _ ?_
  · simp_rw [Fintype.sum_prod_type, hcs]
    calc ∑ i, ∑ j, CJR θ * ca i * cb j = CJR θ * (∑ i, ca i) * ∑ j, cb j := by
          rw [mul_assoc, Finset.sum_mul_sum, Finset.mul_sum]
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun j _ => ?_
          ring
      _ ≤ CJR θ * N₁ * N₂ :=
          mul_le_mul (mul_le_mul_of_nonneg_left hsa hC) hsb hcb (mul_nonneg hC (hca.trans hsa))
  · intro α t s h0' hst ht1
    rw [KEqOn.kcomp (hea _) (heb _) t s h0' hst ht1,
      kcomp_finsetSum _ _ (fun i => JSym.continuous_kernel _ (hba i).reg _)
        (fun j => RSym.continuous_kernel _ (hbb j) _)]
    beta_reduce
    rw [Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun j _ => ?_
    exact hSk i j α t s h0' hst ht1

/-- The relabelling `(ι₁ ⊕ ι₂) ⊕ Unit ≃ ι₁ ⊕ Option ι₂`. -/
@[expose] def eJRvars : (ι₁ ⊕ ι₂) ⊕ Unit ≃ ι₁ ⊕ Option ι₂ where
  toFun x := match x with
    | Sum.inl (Sum.inl i) => Sum.inl i
    | Sum.inl (Sum.inr j) => Sum.inr (some j)
    | Sum.inr _ => Sum.inr none
  invFun y := match y with
    | Sum.inl i => Sum.inl (Sum.inl i)
    | Sum.inr (some j) => Sum.inl (Sum.inr j)
    | Sum.inr none => Sum.inr ()
  left_inv x := by rcases x with (i | j) | u <;> rfl
  right_inv y := by rcases y with i | (_ | j) <;> rfl

/-- **DH21 Lemma 5.4, `J R`** (L1006–L1017): if `T₁` has class `J` (variables `α ∘ inl`) and
`T₂` has class `R` (variables `α ∘ inr`, special variable `α (inr none)`), then `T₁ T₂` has
class `J` with norm at most `CJR θ ‖T₁‖ ‖T₂‖`, for `0 ≤ θ < 1` and `A ≥ A0`. -/
theorem ClassJ.comp_R {θ A N₁ N₂ : ℝ} (h0 : 0 ≤ θ) (h1 : θ < 1) (hA : A0 ≤ A)
    {T₁ : (ι₁ → ℝ) → ℝ → ℝ → ℂ} {T₂ : (Option ι₂ → ℝ) → ℝ → ℝ → ℂ} (hT₁ : ClassJ θ A N₁ T₁)
    (hT₂ : ClassR θ A N₂ T₂) :
    ClassJ θ A (CJR θ * N₁ * N₂) fun α : ι₁ ⊕ Option ι₂ → ℝ =>
      kcomp (T₁ fun i => α (Sum.inl i)) (T₂ fun o => α (Sum.inr o)) := by
  have h := (ClassJ.comp_R' h0 h1 hA hT₁ hT₂).reindex (eJRvars (ι₁ := ι₁) (ι₂ := ι₂))
  have e : ∀ α : ι₁ ⊕ Option ι₂ → ℝ,
      optB (fun i => α (eJRvars i)) = fun o => α (Sum.inr o) := fun α => by
    funext o; cases o <;> rfl
  simp only [e] at h
  exact h

end Assembly

end WaveTurbulence.ClassJR
