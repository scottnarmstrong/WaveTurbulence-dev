/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.ClassJR.MCCase1

/-!
# Lemma G for class `R` operators: the identity

DH21 (expandG1) (L1131–L1136): a basic class `R` operator
`∫ m(α[A∖{1}], γ) R_{ℓ₁+εα₁, ℓ₂+εα₁; γ₁,γ₂,γ₃} dγ` applied to `e^{πiλ₀s}` is, for `t ∈ [0,1]`,
`∫ aR(α; v, γ, τ) e^{πi(v+γ₁)t}` with
`aR(α; v, γ, τ) = m(α[A∖{1}], γ) · χ_∞(ℓ₁+εα₁+γ₃)/(ℓ₁+εα₁+γ₃) · gE(γ₂+λ₀-ℓ₂-εα₁; v-ℓ₂-εα₁, τ)`.

The class `R` kernel is a superposition of the kernels `J_{ℓ₂+εα₁; γ₁, γ₂}` with the coefficient
`m · χ_∞(…)/(…)`, so the identity is an instance of the general identity `volterra_gen_exp` for
superpositions `∫ m₀(γ) J_{ℓ; g₁(γ), g₂(γ)} dγ` over an arbitrary measure space of parameters
(the class `J` case is `volterra_jsym_exp`).
-/

public section

open MeasureTheory Set Filter Finset Complex
open scoped ContDiff ENNReal Real

namespace WaveTurbulence.ClassJR

section General

variable {Γ : Type*} [MeasureSpace Γ] [SFinite (volume : Measure Γ)]

/-- `J`-superposition applied to an exponential, before the `gE` representation. -/
theorem volterra_gen_exp_aux {m₀ : Γ → ℂ} (hm : Integrable m₀) {g₁ g₂ : Γ → ℝ}
    (hg₁ : Measurable g₁) (hg₂ : Measurable g₂) (ℓ L0 : ℝ) {t : ℝ} (ht : 0 ≤ t) :
    volterra (fun t s => ∫ γ, m₀ γ * jker ℓ (g₁ γ) (g₂ γ) t s)
        (fun s => cexp (π * I * (L0 * s))) t =
      ∫ γ, m₀ γ * (cexp (π * I * ((ℓ + g₁ γ) * t)) * eInt (g₂ γ + L0 - ℓ) t) := by
  have hF : Integrable (fun p : ℝ × Γ =>
      m₀ p.2 * jker ℓ (g₁ p.2) (g₂ p.2) t p.1 * cexp (π * I * (L0 * p.1)))
      ((volume.restrict (Ioc 0 t)).prod volume) := by
    have hmeas : AEStronglyMeasurable (fun p : ℝ × Γ =>
        m₀ p.2 * jker ℓ (g₁ p.2) (g₂ p.2) t p.1 * cexp (π * I * (L0 * p.1)))
        ((volume.restrict (Ioc 0 t)).prod volume) := by
      refine ((hm.aestronglyMeasurable.comp_snd).mul ?_).mul ?_
      · have : Measurable fun p : ℝ × Γ => jker ℓ (g₁ p.2) (g₂ p.2) t p.1 := by
          unfold jker
          fun_prop
        exact this.aestronglyMeasurable
      · exact (by fun_prop : Measurable fun p : ℝ × Γ =>
          cexp (π * I * (L0 * p.1))).aestronglyMeasurable
    have hI : Integrable (fun p : ℝ × Γ => ‖m₀ p.2‖)
        ((volume.restrict (Ioc 0 t)).prod volume) :=
      (integrable_const (1 : ℝ)).mul_prod hm.norm |>.congr (Eventually.of_forall fun p => by simp)
    refine hI.mono' hmeas (Eventually.of_forall fun p => ?_)
    rw [norm_mul, norm_mul, norm_jker_eq, Complex.norm_exp]
    simp
  rw [volterra, intervalIntegral.integral_of_le ht]
  have e1 : ∀ s, (∫ γ, m₀ γ * jker ℓ (g₁ γ) (g₂ γ) t s) * cexp (π * I * (L0 * s)) =
      ∫ γ, m₀ γ * jker ℓ (g₁ γ) (g₂ γ) t s * cexp (π * I * (L0 * s)) := fun s => by
    rw [← integral_mul_const]
  simp_rw [e1]
  rw [integral_integral_swap hF]
  refine integral_congr_ae (Eventually.of_forall fun γ => ?_)
  simp only
  have e2 : (fun s => m₀ γ * jker ℓ (g₁ γ) (g₂ γ) t s * cexp (π * I * (L0 * s))) =
      fun s => m₀ γ * (jker ℓ (g₁ γ) (g₂ γ) t s * cexp (π * I * (L0 * s))) := by
    funext s; ring
  rw [e2, integral_const_mul, ← intervalIntegral.integral_of_le ht, integral_jker_mul_exp]

/-- **The general Lemma G coefficient** `m₀(γ) gE(g₂(γ) + λ₀ - ℓ; v - ℓ, τ)` on `ζ = (v, (γ, τ))`. -/
@[expose] noncomputable def gG (m₀ : Γ → ℂ) (g₂ : Γ → ℝ) (ℓ L0 : ℝ) (ζ : ℝ × (Γ × ℝ)) : ℂ :=
  m₀ ζ.2.1 * gE (g₂ ζ.2.1 + L0 - ℓ) (ζ.1 - ℓ, ζ.2.2)

omit [SFinite (volume : Measure Γ)] in
theorem measurable_gG {m₀ : Γ → ℂ} (hm : Measurable m₀) {g₂ : Γ → ℝ} (hg₂ : Measurable g₂)
    (ℓ L0 : ℝ) : Measurable (gG m₀ g₂ ℓ L0) := by
  unfold gG
  exact (hm.comp (measurable_fst.comp measurable_snd)).mul (measurable_gE.comp
    (f := fun ζ : ℝ × (Γ × ℝ) => (g₂ ζ.2.1 + L0 - ℓ, (ζ.1 - ℓ, ζ.2.2))) (by fun_prop))

theorem lintegral_enorm_gG_le {m₀ : Γ → ℂ} (hm : Measurable m₀) {g₂ : Γ → ℝ}
    (hg₂ : Measurable g₂) (ℓ L0 : ℝ) :
    ∫⁻ ζ, ‖gG m₀ g₂ ℓ L0 ζ‖ₑ ≤ ENNReal.ofReal (2 * CE * Ir 2) * ∫⁻ γ, ‖m₀ γ‖ₑ := by
  have hmeas : Measurable fun ζ => ‖gG m₀ g₂ ℓ L0 ζ‖ₑ := (measurable_gG hm hg₂ ℓ L0).enorm
  have hfs := measurePreserving_frontSwap (A := Γ) (Z := ℝ) (T := ℝ)
  rw [← hfs.lintegral_comp_emb frontSwap.measurableEmbedding]
  have hm2 : Measurable fun p : Γ × (ℝ × ℝ) => ‖gG m₀ g₂ ℓ L0 (frontSwap p)‖ₑ :=
    hmeas.comp frontSwap.measurable
  rw [Measure.volume_eq_prod, lintegral_prod _ hm2.aemeasurable,
    ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  refine lintegral_mono fun γ => ?_
  simp only [frontSwap_apply, gG, enorm_mul]
  rw [lintegral_const_mul' _ _ enorm_ne_top, mul_comm]
  gcongr
  rw [lintegral_shift1 (fun q => ‖gE (g₂ γ + L0 - ℓ) q‖ₑ)]
  exact lintegral_enorm_gE_le _

theorem integrable_gG {m₀ : Γ → ℂ} (hm : Integrable m₀) (hm' : Measurable m₀) {g₂ : Γ → ℝ}
    (hg₂ : Measurable g₂) (ℓ L0 : ℝ) : Integrable (gG m₀ g₂ ℓ L0) := by
  refine ⟨(measurable_gG hm' hg₂ ℓ L0).aestronglyMeasurable, ?_⟩
  exact (lintegral_enorm_gG_le hm' hg₂ ℓ L0).trans_lt
    (ENNReal.mul_lt_top ENNReal.ofReal_lt_top hm.2)

/-- **Lemma G, general identity**: for `t ∈ [0, 1]`,
`∫ m₀(γ) J_{ℓ; g₁(γ), g₂(γ)} dγ (e^{πiλ₀s})(t) = ∫ gG(ζ) e^{πi(v + g₁(γ))t} dζ`. -/
theorem volterra_gen_exp {m₀ : Γ → ℂ} (hm : Integrable m₀) (hm' : Measurable m₀)
    {g₁ g₂ : Γ → ℝ} (hg₁ : Measurable g₁) (hg₂ : Measurable g₂) (ℓ L0 : ℝ) {t : ℝ}
    (ht : t ∈ Icc (0 : ℝ) 1) :
    volterra (fun t s => ∫ γ, m₀ γ * jker ℓ (g₁ γ) (g₂ γ) t s)
        (fun s => cexp (π * I * (L0 * s))) t =
      ∫ ζ : ℝ × (Γ × ℝ), gG m₀ g₂ ℓ L0 ζ * cexp (π * I * ((ζ.1 + g₁ ζ.2.1) * t)) := by
  have hfs := measurePreserving_frontSwap (A := Γ) (Z := ℝ) (T := ℝ)
  have hint : Integrable fun ζ : ℝ × (Γ × ℝ) =>
      gG m₀ g₂ ℓ L0 ζ * cexp (π * I * ((ζ.1 + g₁ ζ.2.1) * t)) := by
    refine (integrable_gG hm hm' hg₂ ℓ L0).norm.mono' ?_ (Eventually.of_forall fun ζ => ?_)
    · have : Measurable fun ζ : ℝ × (Γ × ℝ) => cexp (π * I * ((ζ.1 + g₁ ζ.2.1) * t)) := by
        fun_prop
      exact (measurable_gG hm' hg₂ ℓ L0).aestronglyMeasurable.mul this.aestronglyMeasurable
    · rw [norm_mul, Complex.norm_exp]
      simp
  have hint' : Integrable (fun p : Γ × (ℝ × ℝ) =>
      gG m₀ g₂ ℓ L0 (frontSwap p) * cexp (π * I * (((frontSwap p).1 +
        g₁ (frontSwap p).2.1) * t))) ((volume : Measure Γ).prod volume) :=
    (hfs.integrable_comp_emb frontSwap.measurableEmbedding).2 hint
  rw [volterra_gen_exp_aux hm hg₁ hg₂ ℓ L0 ht.1, ← hfs.integral_comp frontSwap.measurableEmbedding,
    Measure.volume_eq_prod, integral_prod _ hint']
  refine integral_congr_ae (Eventually.of_forall fun γ => ?_)
  simp only [frontSwap_apply, gG]
  rw [← integral_gE_mul_exp _ ht, ← integral_const_mul, ← integral_const_mul]
  rw [← integral_shift1 (fun q : ℝ × ℝ => m₀ γ * (cexp (π * I * ((ℓ + g₁ γ) * t)) *
      (gE (g₂ γ + L0 - ℓ) q * cexp (π * I * (q.1 * t))))) ℓ]
  refine integral_congr_ae (Eventually.of_forall fun q => ?_)
  simp only
  have e : cexp (π * I * ((ℓ + g₁ γ) * t)) * cexp (π * I * ((q.1 - ℓ : ℝ) * t)) =
      cexp (π * I * ((q.1 + g₁ γ) * t)) := by
    rw [← Complex.exp_add]; congr 1; push_cast; ring
  rw [← e]
  ring

end General

section ClassR

variable {ι : Type*} [Fintype ι]

/-- **The coefficient of Lemma G for class `R`** (DH21 (expandG1)) on `ζ = (v, (γ, τ))`,
`γ = (γ₁, γ₂, γ₃)`: `m(α[A∖{1}], γ) χ_∞(ℓ₁+εα₁+γ₃)/(ℓ₁+εα₁+γ₃) gE(γ₂+λ₀-ℓ₂-εα₁; v-ℓ₂-εα₁, τ)`. -/
@[expose] noncomputable def aR (y₁ y₂ : ι → ℤ) (ε : ℤ) (m : (ι → ℝ) → ℝ × ℝ × ℝ → ℂ) (L0 : ℝ)
    (α : Option ι → ℝ) (ζ : ℝ × ((ℝ × ℝ × ℝ) × ℝ)) : ℂ :=
  gG (fun γ => m (nsp α) γ * (chiInvR (bundle y₁ (nsp α) + ε * α none + γ.2.2) : ℂ))
    (fun γ => γ.2.1) (bundle y₂ (nsp α) + ε * α none) L0 ζ

theorem aR_apply (y₁ y₂ : ι → ℤ) (ε : ℤ) (m : (ι → ℝ) → ℝ × ℝ × ℝ → ℂ) (L0 : ℝ)
    (α : Option ι → ℝ) (ζ : ℝ × ((ℝ × ℝ × ℝ) × ℝ)) :
    aR y₁ y₂ ε m L0 α ζ = m (nsp α) ζ.2.1 *
      (chiInvR (bundle y₁ (nsp α) + ε * α none + ζ.2.1.2.2) : ℂ) *
      gE (ζ.2.1.2.1 + L0 - (bundle y₂ (nsp α) + ε * α none))
        (ζ.1 - (bundle y₂ (nsp α) + ε * α none), ζ.2.2) := rfl

theorem measurable_chiInvR : Measurable chiInvR := contDiff_chiInvR.continuous.measurable

theorem integrable_mul_chiInvR {m₀ : ℝ × ℝ × ℝ → ℂ} (hm : Integrable m₀) (c : ℝ) :
    Integrable fun γ : ℝ × ℝ × ℝ => m₀ γ * (chiInvR (c + γ.2.2) : ℂ) := by
  refine hm.mul_bdd (c := CPhi) ?_ (Eventually.of_forall fun γ => norm_chiInvR_le _)
  exact (Complex.measurable_ofReal.comp (measurable_chiInvR.comp (by fun_prop))).aestronglyMeasurable

/-- **Lemma G for class `R`, the identity** (DH21 (expandG1)): for `t ∈ [0, 1]`,
`ℛ(e^{πiλ₀s})(t) = ∫ aR(α; v, γ, τ) e^{πi(v+γ₁)t}`. -/
theorem volterra_rsym_exp (R : RSym ι) (hR : SymReg R.m) (α : Option ι → ℝ) (L0 : ℝ) {t : ℝ}
    (ht : t ∈ Icc (0 : ℝ) 1) :
    volterra (R.kernel α) (fun s => cexp (π * I * (L0 * s))) t =
      ∫ ζ, aR R.y₁ R.y₂ R.ε R.m L0 α ζ * cexp (π * I * ((ζ.1 + ζ.2.1.1) * t)) := by
  have hm := integrable_mul_chiInvR (hR.integrable (nsp α)) (bundle R.y₁ (nsp α) + R.ε * α none)
  have hm' : Measurable fun γ : ℝ × ℝ × ℝ =>
      R.m (nsp α) γ * (chiInvR (bundle R.y₁ (nsp α) + R.ε * α none + γ.2.2) : ℂ) :=
    (hR.meas.measurable.comp measurable_prodMk_left).mul
      (Complex.measurable_ofReal.comp (measurable_chiInvR.comp (by fun_prop)))
  have hk : R.kernel α = fun t s => ∫ γ : ℝ × ℝ × ℝ,
      R.m (nsp α) γ * (chiInvR (bundle R.y₁ (nsp α) + R.ε * α none + γ.2.2) : ℂ) *
        jker (bundle R.y₂ (nsp α) + R.ε * α none) γ.1 γ.2.1 t s := by
    funext t s
    simp only [RSym.kernel, rker, mul_assoc]
  rw [hk]
  exact volterra_gen_exp (g₁ := fun γ => γ.1) (g₂ := fun γ => γ.2.1) hm hm' (by fun_prop)
    (by fun_prop) _ L0 ht

end ClassR

section OneDim

/-- A pair integral with a sign: `∫ (1+|c₁+εx|)^{-p₁} (1+|c₂-εx|)^{-p₂} dx ≤ Ir(p₁+p₂)`. -/
theorem lintegral_pair_sign_le {p₁ p₂ : ℝ} (h₁ : 0 ≤ p₁) (h₂ : 0 ≤ p₂) (h : 1 < p₁ + p₂)
    {ε : ℤ} (hε : ε = 1 ∨ ε = -1) (c₁ c₂ : ℝ) :
    ∫⁻ x : ℝ, ENNReal.ofReal ((1 + |c₁ + ε * x|) ^ (-p₁) * (1 + |c₂ - ε * x|) ^ (-p₂)) ≤
      ENNReal.ofReal (Ir (p₁ + p₂)) := by
  rcases hε with hε | hε
  · have e : ∀ x : ℝ, (1 + |c₁ + ε * x|) ^ (-p₁) * (1 + |c₂ - ε * x|) ^ (-p₂) =
        (1 + |x + c₁|) ^ (-p₁) * (1 + |-x + c₂|) ^ (-p₂) := fun x => by
      rw [hε]
      push_cast
      rw [one_mul, add_comm c₁ x, sub_eq_neg_add]
    simp_rw [e]
    exact lintegral_pair_shift_le h₁ h₂ h c₁ c₂
  · have e : ∀ x : ℝ, (1 + |c₁ + ε * x|) ^ (-p₁) * (1 + |c₂ - ε * x|) ^ (-p₂) =
        (1 + |x + c₂|) ^ (-p₂) * (1 + |-x + c₁|) ^ (-p₁) := fun x => by
      rw [hε]
      push_cast
      rw [neg_one_mul, sub_neg_eq_add, add_comm c₂ x, ← sub_eq_add_neg, sub_eq_neg_add, mul_comm]
    simp_rw [e]
    refine (lintegral_pair_shift_le h₂ h₁ (by linarith) c₂ c₁).trans_eq ?_
    rw [add_comm]

/-- **The integral over the special variable of a class `R` coefficient** (DH21 (integrableterm)):
`∫ (1+|x|)^{b'} (1+|A₁+εx|)^{-1} ((1+|B+εx|)^a / (1+|D-εx|) + (1+|D-εx|)^{a-1}) dx
  ≤ 2 Ir(2-a-b') (1+|A₁|)^{b'} (1+|B-A₁|)^a` for `a + b' < 1`. -/
theorem lintegral_R1D {a b' : ℝ} (ha : 0 ≤ a) (hb' : 0 ≤ b') (hab : a + b' < 1) {ε : ℤ}
    (hε : ε = 1 ∨ ε = -1) (A₁ B D : ℝ) :
    ∫⁻ x : ℝ, ENNReal.ofReal ((1 + |x|) ^ b' * (1 + |A₁ + ε * x|)⁻¹ *
        ((1 + |B + ε * x|) ^ a / (1 + |D - ε * x|) + (1 + |D - ε * x|) ^ (a - 1))) ≤
      ENNReal.ofReal ((1 + |A₁|) ^ b' * (1 + |B - A₁|) ^ a * (2 * Ir (2 - a - b'))) := by
  set c₁ : ℝ := (1 + |A₁|) ^ b' with hc₁
  set c₂ : ℝ := (1 + |B - A₁|) ^ a with hc₂
  have hc₁0 : 0 ≤ c₁ := by positivity
  have hc₂1 : 1 ≤ c₂ := Real.one_le_rpow (by linarith [abs_nonneg (B - A₁)]) ha
  have hεx : ∀ x : ℝ, |(ε : ℝ) * x| = |x| := fun x => by
    rcases hε with h | h <;> simp [h]
  have hIr : 0 ≤ Ir (2 - a - b') := ENNReal.toReal_nonneg
  -- the pointwise bound
  have hpt : ∀ x : ℝ, (1 + |x|) ^ b' * (1 + |A₁ + ε * x|)⁻¹ *
      ((1 + |B + ε * x|) ^ a / (1 + |D - ε * x|) + (1 + |D - ε * x|) ^ (a - 1)) ≤
      c₁ * c₂ * ((1 + |A₁ + ε * x|) ^ (-(1 - a - b')) * (1 + |D - ε * x|) ^ (-(1 : ℝ)) +
        (1 + |A₁ + ε * x|) ^ (-(1 - b')) * (1 + |D - ε * x|) ^ (-(1 - a))) := by
    intro x
    set Y : ℝ := 1 + |A₁ + ε * x| with hY
    set W : ℝ := 1 + |D - ε * x| with hW
    have hY0 : 0 < Y := by positivity
    have hW0 : 0 < W := by positivity
    have h1 : (1 + |x|) ^ b' ≤ Y ^ b' * c₁ := by
      have := one_add_abs_add_rpow_le hb' (A₁ + ε * x) (-A₁)
      rwa [add_neg_cancel_comm, hεx, abs_neg] at this
    have h2 : (1 + |B + ε * x|) ^ a ≤ Y ^ a * c₂ := by
      have := one_add_abs_add_rpow_le ha (A₁ + ε * x) (B - A₁)
      rwa [show A₁ + ε * x + (B - A₁) = B + ε * x by ring] at this
    have hYi : Y⁻¹ = Y ^ (-(1 : ℝ)) := (Real.rpow_neg_one Y).symm
    have hWi : (1 : ℝ) / W = W ^ (-(1 : ℝ)) := by rw [one_div, Real.rpow_neg_one]
    have hWa : W ^ (a - 1) = W ^ (-(1 - a)) := by ring_nf
    have hY1 : Y ^ b' * Y ^ (-(1 : ℝ)) * Y ^ a = Y ^ (-(1 - a - b')) := by
      rw [← Real.rpow_add hY0, ← Real.rpow_add hY0]; ring_nf
    have hY2 : Y ^ b' * Y ^ (-(1 : ℝ)) = Y ^ (-(1 - b')) := by
      rw [← Real.rpow_add hY0]; ring_nf
    have hW' : (1 + |B + ε * x|) ^ a / W = (1 + |B + ε * x|) ^ a * W ^ (-(1 : ℝ)) := by
      rw [div_eq_mul_one_div, hWi]
    rw [hW', hYi, hWa]
    have hYp : 0 ≤ Y ^ (-(1 : ℝ)) := by positivity
    have hWp : 0 ≤ W ^ (-(1 : ℝ)) := by positivity
    have hWp' : 0 ≤ W ^ (-(1 - a)) := by positivity
    calc (1 + |x|) ^ b' * Y ^ (-(1 : ℝ)) *
          ((1 + |B + ε * x|) ^ a * W ^ (-(1 : ℝ)) + W ^ (-(1 - a)))
        ≤ (Y ^ b' * c₁) * Y ^ (-(1 : ℝ)) * ((Y ^ a * c₂) * W ^ (-(1 : ℝ)) + W ^ (-(1 - a))) := by
          gcongr
      _ = c₁ * c₂ * ((Y ^ b' * Y ^ (-(1 : ℝ)) * Y ^ a) * W ^ (-(1 : ℝ))) +
            c₁ * ((Y ^ b' * Y ^ (-(1 : ℝ))) * W ^ (-(1 - a))) := by ring
      _ ≤ c₁ * c₂ * ((Y ^ b' * Y ^ (-(1 : ℝ)) * Y ^ a) * W ^ (-(1 : ℝ))) +
            c₁ * c₂ * ((Y ^ b' * Y ^ (-(1 : ℝ))) * W ^ (-(1 - a))) := by
          gcongr
          exact le_mul_of_one_le_right hc₁0 hc₂1
      _ = _ := by rw [hY1, hY2]; ring
  have hm1 : Measurable fun x : ℝ => ENNReal.ofReal ((1 + |A₁ + ε * x|) ^ (-(1 - a - b')) *
      (1 + |D - ε * x|) ^ (-(1 : ℝ))) := by fun_prop
  calc ∫⁻ x : ℝ, ENNReal.ofReal ((1 + |x|) ^ b' * (1 + |A₁ + ε * x|)⁻¹ *
        ((1 + |B + ε * x|) ^ a / (1 + |D - ε * x|) + (1 + |D - ε * x|) ^ (a - 1)))
      ≤ ∫⁻ x : ℝ, ENNReal.ofReal (c₁ * c₂) *
          (ENNReal.ofReal ((1 + |A₁ + ε * x|) ^ (-(1 - a - b')) *
            (1 + |D - ε * x|) ^ (-(1 : ℝ))) +
          ENNReal.ofReal ((1 + |A₁ + ε * x|) ^ (-(1 - b')) * (1 + |D - ε * x|) ^ (-(1 - a)))) := by
        refine lintegral_mono fun x => ?_
        rw [← ENNReal.ofReal_add (by positivity) (by positivity),
          ← ENNReal.ofReal_mul (by positivity)]
        exact ENNReal.ofReal_le_ofReal (hpt x)
    _ = ENNReal.ofReal (c₁ * c₂) *
          ((∫⁻ x : ℝ, ENNReal.ofReal ((1 + |A₁ + ε * x|) ^ (-(1 - a - b')) *
            (1 + |D - ε * x|) ^ (-(1 : ℝ)))) +
          ∫⁻ x : ℝ, ENNReal.ofReal ((1 + |A₁ + ε * x|) ^ (-(1 - b')) *
            (1 + |D - ε * x|) ^ (-(1 - a)))) := by
        rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, lintegral_add_left hm1]
    _ ≤ ENNReal.ofReal (c₁ * c₂) *
          (ENNReal.ofReal (Ir (2 - a - b')) + ENNReal.ofReal (Ir (2 - a - b'))) := by
        gcongr
        · refine (lintegral_pair_sign_le (by linarith) zero_le_one (by linarith) hε A₁ D).trans_eq ?_
          congr 2; ring
        · refine (lintegral_pair_sign_le (by linarith) (by linarith) (by linarith) hε A₁ D).trans_eq ?_
          congr 2; ring
    _ = _ := by
        rw [← ENNReal.ofReal_add hIr hIr, ← ENNReal.ofReal_mul (by positivity)]
        congr 1; ring

end OneDim

section RSymbol

variable {ι : Type*} [Fintype ι]

/-- The bundle `ℓ(α[A∖{1}]) + εα₁` on `Option ι`. -/
@[expose] def yo (ε : ℤ) (y : ι → ℤ) : Option ι → ℤ := fun o => Option.elim o ε y

theorem bundle_yo (ε : ℤ) (y : ι → ℤ) (α : Option ι → ℝ) :
    bundle (yo ε y) α = bundle y (nsp α) + ε * α none := by
  simp only [bundle, yo, Fintype.sum_option, Option.elim, nsp]
  ring

omit [Fintype ι] in
theorem isBundle_yo {ε : ℤ} (hε : ε = 1 ∨ ε = -1) {y : ι → ℤ} (hy : IsBundle y) :
    IsBundle (yo ε y) := by
  rintro (_ | j)
  · rcases hε with h | h <;> simp [yo, h]
  · exact hy j

theorem aR_eq_gD (y₁ y₂ : ι → ℤ) (ε : ℤ) (m : (ι → ℝ) → ℝ × ℝ × ℝ → ℂ) (L0 : ℝ)
    (α : Option ι → ℝ) (ζ : ℝ × ((ℝ × ℝ × ℝ) × ℝ)) :
    aR y₁ y₂ ε m L0 α ζ = m (nsp α) ζ.2.1 * ((chiInvR (bundle (yo ε y₁) α + ζ.2.1.2.2) : ℂ) *
      gD (ζ.2.1.2.1 + L0) ζ.1 ζ.2.2 (bundle (yo ε y₂) α)) := by
  rw [aR_apply, bundle_yo, bundle_yo, mul_assoc]
  rfl

theorem contDiff_nsp : ContDiff ℝ ∞ (nsp : (Option ι → ℝ) → ι → ℝ) :=
  contDiff_pi.2 fun i => (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Option ι => ℝ)
    (some i)).contDiff

omit [Fintype ι] in
@[fun_prop] theorem measurable_nsp : Measurable (nsp : (Option ι → ℝ) → ι → ℝ) := by
  unfold nsp
  fun_prop

theorem contDiff_aR (y₁ y₂ : ι → ℤ) (ε : ℤ) {m : (ι → ℝ) → ℝ × ℝ × ℝ → ℂ}
    (hs : ∀ γ, ContDiff ℝ ∞ fun β => m β γ) (L0 : ℝ) (ζ : ℝ × ((ℝ × ℝ × ℝ) × ℝ)) :
    ContDiff ℝ ∞ fun α => aR y₁ y₂ ε m L0 α ζ := by
  simp_rw [aR_eq_gD]
  exact ((hs _).comp contDiff_nsp).mul ((contDiff_chiInvRc.comp
    ((contDiff_bundle _).add contDiff_const)).mul ((contDiff_gD _ _ _).comp (contDiff_bundle _)))

theorem measurable_aR (y₁ y₂ : ι → ℤ) (ε : ℤ) {m : (ι → ℝ) → ℝ × ℝ × ℝ → ℂ}
    (hm : StronglyMeasurable (Function.uncurry m)) (L0 : ℝ) :
    Measurable (Function.uncurry (aR y₁ y₂ ε m L0)) := by
  change Measurable fun p : (Option ι → ℝ) × (ℝ × ((ℝ × ℝ × ℝ) × ℝ)) =>
    m (nsp p.1) p.2.2.1 * (chiInvR (bundle y₁ (nsp p.1) + ε * p.1 none + p.2.2.1.2.2) : ℂ) *
      gE (p.2.2.1.2.1 + L0 - (bundle y₂ (nsp p.1) + ε * p.1 none))
        (p.2.1 - (bundle y₂ (nsp p.1) + ε * p.1 none), p.2.2.2)
  have h1 : Measurable fun p : (Option ι → ℝ) × (ℝ × ((ℝ × ℝ × ℝ) × ℝ)) => m (nsp p.1) p.2.2.1 :=
    hm.measurable.comp (f := fun p : (Option ι → ℝ) × (ℝ × ((ℝ × ℝ × ℝ) × ℝ)) =>
      (nsp p.1, p.2.2.1)) (by fun_prop)
  have h2 : Measurable fun p : (Option ι → ℝ) × (ℝ × ((ℝ × ℝ × ℝ) × ℝ)) =>
      (chiInvR (bundle y₁ (nsp p.1) + ε * p.1 none + p.2.2.1.2.2) : ℂ) :=
    Complex.measurable_ofReal.comp (measurable_chiInvR.comp (by fun_prop))
  have h3 : Measurable fun p : (Option ι → ℝ) × (ℝ × ((ℝ × ℝ × ℝ) × ℝ)) =>
      gE (p.2.2.1.2.1 + L0 - (bundle y₂ (nsp p.1) + ε * p.1 none))
        (p.2.1 - (bundle y₂ (nsp p.1) + ε * p.1 none), p.2.2.2) :=
    measurable_gE.comp (f := fun p : (Option ι → ℝ) × (ℝ × ((ℝ × ℝ × ℝ) × ℝ)) =>
      (p.2.2.1.2.1 + L0 - (bundle y₂ (nsp p.1) + ε * p.1 none),
        (p.2.1 - (bundle y₂ (nsp p.1) + ε * p.1 none), p.2.2.2))) (by fun_prop)
  exact (h1.mul h2).mul h3

/-- **The Leibniz bound for `aR`.** -/
theorem dnorm_aR_le {y₁ y₂ : ι → ℤ} (hy₁ : IsBundle y₁) (hy₂ : IsBundle y₂) {ε : ℤ}
    (hε : ε = 1 ∨ ε = -1) {m : (ι → ℝ) → ℝ × ℝ × ℝ → ℂ} (hs : ∀ γ, ContDiff ℝ ∞ fun β => m β γ)
    (L0 : ℝ) (k : ℕ) (α : Option ι → ℝ) (ζ : ℝ × ((ℝ × ℝ × ℝ) × ℝ)) :
    dnorm k (aR y₁ y₂ ε m L0) α ζ ≤ ∑ i ∈ range (k + 1), (k.choose i : ℝ≥0∞) *
      dnorm i m (nsp α) ζ.2.1 * ∑ p ∈ range (k - i + 1), ((k - i).choose p : ℝ≥0∞) *
        ‖iteratedDeriv p (fun u => (chiInvR u : ℂ)) (bundle (yo ε y₁) α + ζ.2.1.2.2)‖ₑ *
        ‖iteratedDeriv (k - i - p) (gD (ζ.2.1.2.1 + L0) ζ.1 ζ.2.2) (bundle (yo ε y₂) α)‖ₑ := by
  have hl : lift1 (aR y₁ y₂ ε m L0) ζ = fun β => (lift1 m ζ.2.1 ∘ restrSome) β *
      ((fun β => (chiInvR (bundleL (yo ε y₁) β + ζ.2.1.2.2) : ℂ)) β *
        (fun β => gD (ζ.2.1.2.1 + L0) ζ.1 ζ.2.2 (bundleL (yo ε y₂) β + 0)) β) := by
    funext β
    simp only [lift1, Function.comp, bundleL_apply, add_zero]
    exact aR_eq_gD y₁ y₂ ε m L0 _ ζ
  have hf₁ : ContDiff ℝ ∞ (lift1 m ζ.2.1 ∘ restrSome) :=
    (contDiff_lift1 (hs _)).comp (restrSome (ι := ι)).contDiff
  have hX : ContDiff ℝ ∞ fun β : L1 (Option ι) =>
      (chiInvR (bundleL (yo ε y₁) β + ζ.2.1.2.2) : ℂ) :=
    contDiff_chiInvRc.comp ((bundleL (yo ε y₁)).contDiff.add contDiff_const)
  have hY : ContDiff ℝ ∞ fun β : L1 (Option ι) =>
      gD (ζ.2.1.2.1 + L0) ζ.1 ζ.2.2 (bundleL (yo ε y₂) β + 0) :=
    (contDiff_gD _ _ _).comp ((bundleL (yo ε y₂)).contDiff.add contDiff_const)
  rw [dnorm, hl]
  refine (enorm_iteratedFDeriv_mul_le hf₁ (hX.mul hY) _ k).trans (Finset.sum_le_sum fun i _ => ?_)
  refine mul_le_mul' (mul_le_mul' le_rfl ?_) ?_
  · exact enorm_iteratedFDeriv_comp_le (contDiff_lift1 (hs _)) restrSome norm_restrSome_le _ i
  · refine (enorm_iteratedFDeriv_mul_le hX hY _ (k - i)).trans (Finset.sum_le_sum fun p _ => ?_)
    refine mul_le_mul' (mul_le_mul' le_rfl ?_) ?_
    · have h := enorm_iteratedFDeriv_scalar_le contDiff_chiInvRc (bundleL (yo ε y₁))
        (norm_bundleL_le (isBundle_yo hε hy₁)) ζ.2.1.2.2 (WithLp.toLp 1 α) p
      rw [bundleL_apply] at h
      exact h
    · have h := enorm_iteratedFDeriv_scalar_le (contDiff_gD (ζ.2.1.2.1 + L0) ζ.1 ζ.2.2)
        (bundleL (yo ε y₂)) (norm_bundleL_le (isBundle_yo hε hy₂)) 0 (WithLp.toLp 1 α) (k - i - p)
      rw [bundleL_apply, add_zero] at h
      exact h

/-- The majorant of `dnorm k aR`. -/
@[expose] noncomputable def aRbd (m : (ι → ℝ) → ℝ × ℝ × ℝ → ℂ) (y₁ y₂ : ι → ℤ) (ε : ℤ)
    (L0 : ℝ) (k : ℕ) (α : Option ι → ℝ) (ζ : ℝ × ((ℝ × ℝ × ℝ) × ℝ)) : ℝ≥0∞ :=
  ∑ i ∈ range (k + 1), (k.choose i : ℝ≥0∞) * dnorm i m (nsp α) ζ.2.1 *
    ∑ p ∈ range (k - i + 1), ((k - i).choose p : ℝ≥0∞) *
      (gev CPhi Achi p * ENNReal.ofReal ((1 + |bundle (yo ε y₁) α + ζ.2.1.2.2|)⁻¹)) *
      gEDbd (k - i - p) (ζ.2.1.2.1 + L0) (bundle (yo ε y₂) α) (ζ.1, ζ.2.2)

theorem dnorm_aR_le_bd {y₁ y₂ : ι → ℤ} (hy₁ : IsBundle y₁) (hy₂ : IsBundle y₂) {ε : ℤ}
    (hε : ε = 1 ∨ ε = -1) {m : (ι → ℝ) → ℝ × ℝ × ℝ → ℂ} (hs : ∀ γ, ContDiff ℝ ∞ fun β => m β γ)
    (L0 : ℝ) (k : ℕ) (α : Option ι → ℝ) (ζ : ℝ × ((ℝ × ℝ × ℝ) × ℝ)) :
    dnorm k (aR y₁ y₂ ε m L0) α ζ ≤ aRbd m y₁ y₂ ε L0 k α ζ := by
  refine (dnorm_aR_le hy₁ hy₂ hε hs L0 k α ζ).trans (Finset.sum_le_sum fun i _ => ?_)
  refine mul_le_mul' le_rfl (Finset.sum_le_sum fun p _ => ?_)
  exact mul_le_mul' (mul_le_mul' le_rfl (enorm_iteratedDeriv_chiInvRc_le p _))
    (enorm_iteratedDeriv_gED_le_bd (k - i - p) _ _ (ζ.1, ζ.2.2))

theorem measurable_aRbd {m : (ι → ℝ) → ℝ × ℝ × ℝ → ℂ} (hs : ∀ γ, ContDiff ℝ ∞ fun β => m β γ)
    (hm : StronglyMeasurable (Function.uncurry m)) (y₁ y₂ : ι → ℤ) (ε : ℤ) (L0 : ℝ) (k : ℕ) :
    Measurable (Function.uncurry (aRbd m y₁ y₂ ε L0 k)) := by
  change Measurable fun p : (Option ι → ℝ) × (ℝ × ((ℝ × ℝ × ℝ) × ℝ)) =>
    ∑ i ∈ range (k + 1), (k.choose i : ℝ≥0∞) * dnorm i m (nsp p.1) p.2.2.1 *
      ∑ q ∈ range (k - i + 1), ((k - i).choose q : ℝ≥0∞) *
        (gev CPhi Achi q * ENNReal.ofReal ((1 + |bundle (yo ε y₁) p.1 + p.2.2.1.2.2|)⁻¹)) *
        gEDbd (k - i - q) (p.2.2.1.2.1 + L0) (bundle (yo ε y₂) p.1) (p.2.1, p.2.2.2)
  refine Finset.measurable_sum _ fun i _ => ?_
  refine (measurable_const.mul ((measurable_dnorm hs hm i).comp
    (f := fun p : (Option ι → ℝ) × (ℝ × ((ℝ × ℝ × ℝ) × ℝ)) => (nsp p.1, p.2.2.1))
    (by fun_prop))).mul (Finset.measurable_sum _ fun q _ => ?_)
  have hc : Measurable fun p : (Option ι → ℝ) × (ℝ × ((ℝ × ℝ × ℝ) × ℝ)) =>
      ENNReal.ofReal ((1 + |bundle (yo ε y₁) p.1 + p.2.2.1.2.2|)⁻¹) := by fun_prop
  refine (measurable_const.mul (measurable_const.mul hc)).mul ?_
  exact (measurable_gEDbd (k - i - q)).comp
    (f := fun p : (Option ι → ℝ) × (ℝ × ((ℝ × ℝ × ℝ) × ℝ)) =>
      (p.2.2.1.2.1 + L0, (bundle (yo ε y₂) p.1, (p.2.1, p.2.2.2)))) (by fun_prop)

end RSymbol

section RBound

variable {ι : Type*} [Fintype ι]

/-- The extension of `β : ι → ℝ` by the special variable `x`. -/
@[expose] def optE (β : ι → ℝ) (x : ℝ) : Option ι → ℝ := fun o => Option.elim o x β

omit [Fintype ι] in
@[simp] theorem nsp_optE (β : ι → ℝ) (x : ℝ) : nsp (optE β x) = β := rfl

omit [Fintype ι] in
@[simp] theorem optE_none (β : ι → ℝ) (x : ℝ) : optE β x none = x := rfl

omit [Fintype ι] in
@[fun_prop] theorem measurable_optE (β : ι → ℝ) : Measurable (optE β) := by
  rw [measurable_pi_iff]
  intro o
  cases o
  · exact measurable_id
  · exact measurable_const

/-- `∫ F(α) dα = ∫∫ F(β, x) dx dβ` over `Option ι → ℝ`. -/
theorem lintegral_optionPi {F : (Option ι → ℝ) → ℝ≥0∞} (hF : Measurable F) :
    ∫⁻ α, F α = ∫⁻ β : ι → ℝ, ∫⁻ x : ℝ, F (optE β x) := by
  have h := Measure.pi_map_piOptionEquivProd (ι := ι) (β := fun _ => ℝ) (fun _ => volume)
  set e := MeasurableEquiv.piOptionEquivProd (fun _ : Option ι => ℝ) with he
  have hsymm : ∀ p : (ι → ℝ) × ℝ, e.symm p = optE p.1 p.2 := fun p =>
    (MeasurableEquiv.symm_apply_eq e).2 rfl
  calc ∫⁻ α, F α = ∫⁻ α, F α ∂(((Measure.pi fun _ : ι => (volume : Measure ℝ)).prod
        volume).map e.symm) := by rw [h]; rfl
    _ = ∫⁻ p, F (e.symm p) ∂((Measure.pi fun _ : ι => (volume : Measure ℝ)).prod volume) :=
        lintegral_map_equiv _ _
    _ = ∫⁻ β, ∫⁻ x, F (e.symm (β, x)) ∂volume ∂(Measure.pi fun _ : ι => (volume : Measure ℝ)) :=
        lintegral_prod _ (hF.comp e.symm.measurable).aemeasurable
    _ = _ := by simp only [hsymm]; rfl

/-- The `γ`-profile of `∫ |aR|` at fixed `α`. -/
@[expose] noncomputable def PhiR1 (ℓ₁ ℓ₂ L0 a : ℝ) (γ : ℝ × ℝ × ℝ) : ℝ :=
  (1 + |ℓ₁ + γ.2.2|)⁻¹ * ((1 + |ℓ₂ + γ.1|) ^ a / (1 + |γ.2.1 + L0 - ℓ₂|) +
    (1 + |γ.2.1 + L0 - ℓ₂|) ^ (a - 1))

theorem measurable_PhiR1 (L0 a : ℝ) :
    Measurable fun p : (ℝ × ℝ) × (ℝ × ℝ × ℝ) => PhiR1 p.1.1 p.1.2 L0 a p.2 := by
  unfold PhiR1; fun_prop

/-- **Lemma G for class `R`, the symbol bound at one `α`.** -/
theorem lintegral_weight_aRbd_pt {a : ℝ} (ha : 0 ≤ a) (ha1 : a ≤ 1)
    {m : (ι → ℝ) → ℝ × ℝ × ℝ → ℂ} (hs : ∀ γ, ContDiff ℝ ∞ fun β => m β γ)
    (hm : StronglyMeasurable (Function.uncurry m)) (y₁ y₂ : ι → ℤ) (ε : ℤ) (L0 : ℝ) (k : ℕ)
    (α : Option ι → ℝ) :
    ∫⁻ ζ, ((1 : ℝ≥0∞) + ‖ζ.1 + ζ.2.1.1‖ₑ) ^ a * aRbd m y₁ y₂ ε L0 k α ζ ≤
      ∑ i ∈ range (k + 1), ∑ p ∈ range (k - i + 1), (k.choose i : ℝ≥0∞) *
        ((k - i).choose p : ℝ≥0∞) * gev CPhi Achi p * gev (6 * CE * Ir 2) A1 (k - i - p) *
        ∫⁻ γ, dnorm i m (nsp α) γ *
          ENNReal.ofReal (PhiR1 (bundle (yo ε y₁) α) (bundle (yo ε y₂) α) L0 a γ) := by
  set ℓ₁ := bundle (yo ε y₁) α with hℓ₁
  set ℓ₂ := bundle (yo ε y₂) α with hℓ₂
  have hfs := measurePreserving_frontSwap (A := ℝ × ℝ × ℝ) (Z := ℝ) (T := ℝ)
  have hH : Measurable fun ζ : ℝ × ((ℝ × ℝ × ℝ) × ℝ) =>
      ((1 : ℝ≥0∞) + ‖ζ.1 + ζ.2.1.1‖ₑ) ^ a * aRbd m y₁ y₂ ε L0 k α ζ :=
    (by fun_prop : Measurable fun ζ : ℝ × ((ℝ × ℝ × ℝ) × ℝ) =>
      ((1 : ℝ≥0∞) + ‖ζ.1 + ζ.2.1.1‖ₑ) ^ a).mul (measurable_aRbd hs hm y₁ y₂ ε L0 k).of_uncurry_left
  have hH' : Measurable fun p : (ℝ × ℝ × ℝ) × (ℝ × ℝ) =>
      ((1 : ℝ≥0∞) + ‖(frontSwap p).1 + (frontSwap p).2.1.1‖ₑ) ^ a *
        aRbd m y₁ y₂ ε L0 k α (frontSwap p) := hH.comp frontSwap.measurable
  rw [← hfs.lintegral_comp_emb frontSwap.measurableEmbedding, Measure.volume_eq_prod,
    lintegral_prod _ hH'.aemeasurable]
  have hdm : ∀ i, Measurable fun γ : ℝ × ℝ × ℝ => dnorm i m (nsp α) γ := fun i =>
    (measurable_dnorm hs hm i).of_uncurry_left
  have hPm : Measurable fun γ : ℝ × ℝ × ℝ => ENNReal.ofReal (PhiR1 ℓ₁ ℓ₂ L0 a γ) :=
    ENNReal.measurable_ofReal.comp ((measurable_PhiR1 L0 a).comp
      (f := fun γ : ℝ × ℝ × ℝ => ((ℓ₁, ℓ₂), γ)) (by fun_prop))
  have hR : (∑ i ∈ range (k + 1), ∑ p ∈ range (k - i + 1), (k.choose i : ℝ≥0∞) *
      ((k - i).choose p : ℝ≥0∞) * gev CPhi Achi p * gev (6 * CE * Ir 2) A1 (k - i - p) *
      ∫⁻ γ, dnorm i m (nsp α) γ * ENNReal.ofReal (PhiR1 ℓ₁ ℓ₂ L0 a γ)) =
      ∫⁻ γ, ∑ i ∈ range (k + 1), ∑ p ∈ range (k - i + 1), (k.choose i : ℝ≥0∞) *
        ((k - i).choose p : ℝ≥0∞) * gev CPhi Achi p * gev (6 * CE * Ir 2) A1 (k - i - p) *
        (dnorm i m (nsp α) γ * ENNReal.ofReal (PhiR1 ℓ₁ ℓ₂ L0 a γ)) := by
    have hDP : ∀ i, Measurable fun γ : ℝ × ℝ × ℝ =>
        dnorm i m (nsp α) γ * ENNReal.ofReal (PhiR1 ℓ₁ ℓ₂ L0 a γ) := fun i => (hdm i).mul hPm
    rw [lintegral_finsetSum]
    · refine Finset.sum_congr rfl fun i _ => ?_
      rw [lintegral_finsetSum]
      · refine Finset.sum_congr rfl fun p _ => ?_
        rw [lintegral_const_mul _ (hDP i)]
      · exact fun p _ => (hDP i).const_mul _
    · exact fun i _ => Finset.measurable_sum _ fun p _ => (hDP i).const_mul _
  rw [hR]
  refine lintegral_mono fun γ => ?_
  simp only [frontSwap_apply]
  have hgm : ∀ j : ℕ, Measurable fun q : ℝ × ℝ =>
      ((1 : ℝ≥0∞) + ‖q.1 + γ.1‖ₑ) ^ a * gEDbd j (γ.2.1 + L0) ℓ₂ q := fun j =>
    (by fun_prop : Measurable fun q : ℝ × ℝ => ((1 : ℝ≥0∞) + ‖q.1 + γ.1‖ₑ) ^ a).mul
      ((measurable_gEDbd j).comp (f := fun q : ℝ × ℝ => (γ.2.1 + L0, (ℓ₂, q))) (by fun_prop))
  have hexp : ∀ q : ℝ × ℝ, ((1 : ℝ≥0∞) + ‖q.1 + γ.1‖ₑ) ^ a * aRbd m y₁ y₂ ε L0 k α (q.1, (γ, q.2)) =
      ∑ i ∈ range (k + 1), ∑ p ∈ range (k - i + 1), ((k.choose i : ℝ≥0∞) *
        dnorm i m (nsp α) γ * (((k - i).choose p : ℝ≥0∞) *
          (gev CPhi Achi p * ENNReal.ofReal ((1 + |ℓ₁ + γ.2.2|)⁻¹)))) *
        (((1 : ℝ≥0∞) + ‖q.1 + γ.1‖ₑ) ^ a * gEDbd (k - i - p) (γ.2.1 + L0) ℓ₂ q) := fun q => by
    simp only [aRbd, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun p _ => ?_
    ring
  simp_rw [hexp]
  rw [lintegral_finsetSum _ fun i _ => Finset.measurable_sum _ fun p _ => (hgm _).const_mul _]
  refine Finset.sum_le_sum fun i _ => ?_
  rw [lintegral_finsetSum _ fun p _ => (hgm _).const_mul _]
  refine Finset.sum_le_sum fun p _ => ?_
  rw [lintegral_const_mul _ (hgm _)]
  have hb := lintegral_gEDbd_le_split ha ha1 (k - i - p) (γ.2.1 + L0) ℓ₂ γ.1
  have hC : 0 ≤ 6 * CE * Ir 2 * A1 ^ (k - i - p) * (Nat.factorial (2 * (k - i - p)) : ℝ) := by
    have := CE_nonneg; have := Ir2_nonneg; have := A1_nonneg; positivity
  have hP : ENNReal.ofReal ((1 + |ℓ₁ + γ.2.2|)⁻¹) *
      ENNReal.ofReal (6 * CE * Ir 2 * A1 ^ (k - i - p) * (Nat.factorial (2 * (k - i - p)) : ℝ) *
        ((1 + |ℓ₂ + γ.1|) ^ a / (1 + |γ.2.1 + L0 - ℓ₂|) + (1 + |γ.2.1 + L0 - ℓ₂|) ^ (a - 1))) =
      gev (6 * CE * Ir 2) A1 (k - i - p) * ENNReal.ofReal (PhiR1 ℓ₁ ℓ₂ L0 a γ) := by
    rw [gev, ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul hC, PhiR1]
    congr 1
    ring
  calc ((k.choose i : ℝ≥0∞) * dnorm i m (nsp α) γ * (((k - i).choose p : ℝ≥0∞) *
        (gev CPhi Achi p * ENNReal.ofReal ((1 + |ℓ₁ + γ.2.2|)⁻¹)))) *
        ∫⁻ q : ℝ × ℝ, ((1 : ℝ≥0∞) + ‖q.1 + γ.1‖ₑ) ^ a * gEDbd (k - i - p) (γ.2.1 + L0) ℓ₂ q
      ≤ ((k.choose i : ℝ≥0∞) * dnorm i m (nsp α) γ * (((k - i).choose p : ℝ≥0∞) *
        (gev CPhi Achi p * ENNReal.ofReal ((1 + |ℓ₁ + γ.2.2|)⁻¹)))) *
        ENNReal.ofReal (6 * CE * Ir 2 * A1 ^ (k - i - p) * (Nat.factorial (2 * (k - i - p)) : ℝ) *
          ((1 + |ℓ₂ + γ.1|) ^ a / (1 + |γ.2.1 + L0 - ℓ₂|) + (1 + |γ.2.1 + L0 - ℓ₂|) ^ (a - 1))) :=
        mul_le_mul' le_rfl hb
    _ = (k.choose i : ℝ≥0∞) * ((k - i).choose p : ℝ≥0∞) * gev CPhi Achi p * dnorm i m (nsp α) γ *
        (ENNReal.ofReal ((1 + |ℓ₁ + γ.2.2|)⁻¹) *
          ENNReal.ofReal (6 * CE * Ir 2 * A1 ^ (k - i - p) * (Nat.factorial (2 * (k - i - p)) : ℝ) *
          ((1 + |ℓ₂ + γ.1|) ^ a / (1 + |γ.2.1 + L0 - ℓ₂|) +
            (1 + |γ.2.1 + L0 - ℓ₂|) ^ (a - 1)))) := by ring
    _ = _ := by rw [hP]; ring


theorem abs_bundle_le_sum {y : ι → ℤ} (hy : IsBundle y) (β : ι → ℝ) :
    |bundle y β| ≤ ∑ j, |β j| := by
  unfold bundle
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun j _ => ?_)
  rw [abs_mul]
  have : |(y j : ℝ)| ≤ 1 := by exact_mod_cast hy j
  calc |(y j : ℝ)| * |β j| ≤ 1 * |β j| := by gcongr
    _ = |β j| := one_mul _

/-- `ofReal ((1 + Σ|β_j| + |γ₁| + |γ₃|)^c) = (1 + Σ‖β_j‖ + ‖γ₁‖ + ‖γ₃‖)^c`. -/
theorem ofReal_wR_rpow (β : ι → ℝ) (γ₁ γ₃ c : ℝ) :
    ENNReal.ofReal ((1 + ∑ j, |β j| + |γ₁| + |γ₃|) ^ c) =
      ((1 : ℝ≥0∞) + ∑ j, ‖β j‖ₑ + ‖γ₁‖ₑ + ‖γ₃‖ₑ) ^ c := by
  rw [← ENNReal.ofReal_rpow_of_pos (by positivity)]
  congr 1
  rw [ENNReal.ofReal_add (by positivity) (abs_nonneg _),
    ENNReal.ofReal_add (by positivity) (abs_nonneg _),
    ENNReal.ofReal_add zero_le_one (Finset.sum_nonneg fun j _ => abs_nonneg _), ENNReal.ofReal_one,
    ENNReal.ofReal_sum_of_nonneg fun j _ => abs_nonneg _]
  simp only [Real.enorm_eq_ofReal_abs]

/-- **The integral over the special variable** (DH21 (integrableterm), (propertyG1)): at fixed
`α[A∖{1}] = β` and `γ`, `∫ (1+|x|)^{b'} Φ_R(β, x; γ) dx ≤ K (1 + Σ|β_j| + |γ₁| + |γ₃|)^{a+b'}`. -/
theorem lintegral_x_PhiR1_le {a b' : ℝ} (ha : 0 ≤ a) (hb' : 0 ≤ b') (hab : a + b' < 1) {ε : ℤ}
    (hε : ε = 1 ∨ ε = -1) {y₁ y₂ : ι → ℤ} (hy₁ : IsBundle y₁) (hy₂ : IsBundle y₂) (L0 : ℝ)
    (β : ι → ℝ) (γ : ℝ × ℝ × ℝ) :
    ∫⁻ x : ℝ, ((1 : ℝ≥0∞) + ‖x‖ₑ) ^ b' * ENNReal.ofReal (PhiR1 (bundle (yo ε y₁) (optE β x))
        (bundle (yo ε y₂) (optE β x)) L0 a γ) ≤
      ENNReal.ofReal (2 ^ (a + b') * (2 * Ir (2 - a - b'))) *
        ((1 : ℝ≥0∞) + ∑ j, ‖β j‖ₑ + ‖γ.1‖ₑ + ‖γ.2.2‖ₑ) ^ (a + b') := by
  set A₁ := bundle y₁ β + γ.2.2
  set B := bundle y₂ β + γ.1
  set D := γ.2.1 + L0 - bundle y₂ β
  have he : ∀ x : ℝ, ((1 : ℝ≥0∞) + ‖x‖ₑ) ^ b' * ENNReal.ofReal (PhiR1 (bundle (yo ε y₁) (optE β x))
      (bundle (yo ε y₂) (optE β x)) L0 a γ) = ENNReal.ofReal ((1 + |x|) ^ b' *
        (1 + |A₁ + ε * x|)⁻¹ * ((1 + |B + ε * x|) ^ a / (1 + |D - ε * x|) +
          (1 + |D - ε * x|) ^ (a - 1))) := fun x => by
    rw [one_add_enorm_rpow_eq, ← ENNReal.ofReal_mul (by positivity), PhiR1, bundle_yo, bundle_yo,
      nsp_optE, optE_none]
    congr 1
    have e1 : bundle y₁ β + ε * x + γ.2.2 = A₁ + ε * x := by ring
    have e2 : bundle y₂ β + ε * x + γ.1 = B + ε * x := by ring
    have e3 : γ.2.1 + L0 - (bundle y₂ β + ε * x) = D - ε * x := by ring
    rw [e1, e2, e3, mul_assoc]
  simp_rw [he]
  refine (lintegral_R1D ha hb' hab hε A₁ B D).trans ?_
  set W : ℝ := 1 + ∑ j, |β j| + |γ.1| + |γ.2.2| with hW
  have hX₁ := abs_bundle_le_sum hy₁ β
  have hX₂ := abs_bundle_le_sum hy₂ β
  have hW1 : 1 + |A₁| ≤ 2 * W := by
    show 1 + |bundle y₁ β + γ.2.2| ≤ 2 * (1 + ∑ j, |β j| + |γ.1| + |γ.2.2|)
    have := abs_add_le (bundle y₁ β) γ.2.2
    have := abs_nonneg γ.1
    have := abs_nonneg γ.2.2
    have : 0 ≤ ∑ j, |β j| := Finset.sum_nonneg fun j _ => abs_nonneg _
    linarith
  have hW2 : 1 + |B - A₁| ≤ 2 * W := by
    have e : B - A₁ = (bundle y₂ β - bundle y₁ β) + (γ.1 - γ.2.2) := by
      show bundle y₂ β + γ.1 - (bundle y₁ β + γ.2.2) = _
      ring
    rw [e]
    show _ ≤ 2 * (1 + ∑ j, |β j| + |γ.1| + |γ.2.2|)
    have := abs_add_le (bundle y₂ β - bundle y₁ β) (γ.1 - γ.2.2)
    have := abs_sub (bundle y₂ β) (bundle y₁ β)
    have := abs_sub γ.1 γ.2.2
    have := abs_nonneg γ.1
    have := abs_nonneg γ.2.2
    have : 0 ≤ ∑ j, |β j| := Finset.sum_nonneg fun j _ => abs_nonneg _
    linarith
  have hIr : 0 ≤ Ir (2 - a - b') := ENNReal.toReal_nonneg
  have hW0 : 0 ≤ W := by positivity
  have hK : (1 + |A₁|) ^ b' * (1 + |B - A₁|) ^ a ≤ 2 ^ (a + b') * W ^ (a + b') := by
    calc (1 + |A₁|) ^ b' * (1 + |B - A₁|) ^ a ≤ (2 * W) ^ b' * (2 * W) ^ a := by
          gcongr
      _ = 2 ^ (a + b') * W ^ (a + b') := by
          rw [← Real.rpow_add (by positivity), add_comm b' a,
            Real.mul_rpow (by norm_num) hW0]
  calc ENNReal.ofReal ((1 + |A₁|) ^ b' * (1 + |B - A₁|) ^ a * (2 * Ir (2 - a - b')))
      ≤ ENNReal.ofReal (2 ^ (a + b') * W ^ (a + b') * (2 * Ir (2 - a - b'))) :=
        ENNReal.ofReal_le_ofReal (by gcongr)
    _ = ENNReal.ofReal (2 ^ (a + b') * (2 * Ir (2 - a - b'))) * ENNReal.ofReal (W ^ (a + b')) := by
        rw [← ENNReal.ofReal_mul (by positivity)]
        congr 1; ring
    _ = _ := by rw [hW, ofReal_wR_rpow]


/-- The coefficients of the Leibniz expansion of `aR`. -/
@[expose] noncomputable def cR (k i p : ℕ) : ℝ≥0∞ :=
  (k.choose i : ℝ≥0∞) * ((k - i).choose p : ℝ≥0∞) * gev CPhi Achi p *
    gev (6 * CE * Ir 2) A1 (k - i - p)

/-- **The special-variable integration at fixed `α[A∖{1}]`.** -/
theorem lintegral_x_aR_le {θ a b' : ℝ} (ha : 0 ≤ a) (hb' : 0 ≤ b') (hab : a + b' < 1) {ε : ℤ}
    (hε : ε = 1 ∨ ε = -1) {y₁ y₂ : ι → ℤ} (hy₁ : IsBundle y₁) (hy₂ : IsBundle y₂)
    {m : (ι → ℝ) → ℝ × ℝ × ℝ → ℂ} (hs : ∀ γ, ContDiff ℝ ∞ fun β => m β γ)
    (hm : StronglyMeasurable (Function.uncurry m)) (L0 : ℝ) (k : ℕ) (β : ι → ℝ) {ρ : ℝ≥0∞}
    (hρ : ∀ γ₁ γ₃, ρ * ((1 : ℝ≥0∞) + ∑ j, ‖β j‖ₑ + ‖γ₁‖ₑ + ‖γ₃‖ₑ) ^ (a + b') ≤ wR θ β γ₁ γ₃) :
    ∫⁻ x : ℝ, ρ * ((1 : ℝ≥0∞) + ‖x‖ₑ) ^ b' * ∑ i ∈ range (k + 1), ∑ p ∈ range (k - i + 1),
        cR k i p * ∫⁻ γ, dnorm i m (nsp (optE β x)) γ * ENNReal.ofReal (PhiR1
          (bundle (yo ε y₁) (optE β x)) (bundle (yo ε y₂) (optE β x)) L0 a γ) ≤
      ∑ i ∈ range (k + 1), ∑ p ∈ range (k - i + 1),
        cR k i p * ENNReal.ofReal (2 ^ (a + b') * (2 * Ir (2 - a - b'))) *
          ∫⁻ γ, wR θ β γ.1 γ.2.2 * dnorm i m β γ := by
  set KX := ENNReal.ofReal (2 ^ (a + b') * (2 * Ir (2 - a - b'))) with hKX
  simp only [nsp_optE]
  -- the integrand in `(x, γ)`
  have hG : ∀ i, Measurable fun z : ℝ × (ℝ × ℝ × ℝ) => ((1 : ℝ≥0∞) + ‖z.1‖ₑ) ^ b' *
      (dnorm i m β z.2 * ENNReal.ofReal (PhiR1 (bundle (yo ε y₁) (optE β z.1))
        (bundle (yo ε y₂) (optE β z.1)) L0 a z.2)) := fun i => by
    refine (by fun_prop : Measurable fun z : ℝ × (ℝ × ℝ × ℝ) => ((1 : ℝ≥0∞) + ‖z.1‖ₑ) ^ b').mul
      ((((measurable_dnorm hs hm i).comp (f := fun z : ℝ × (ℝ × ℝ × ℝ) => (β, z.2))
        (by fun_prop))).mul (ENNReal.measurable_ofReal.comp ((measurable_PhiR1 L0 a).comp
          (f := fun z : ℝ × (ℝ × ℝ × ℝ) => ((bundle (yo ε y₁) (optE β z.1),
            bundle (yo ε y₂) (optE β z.1)), z.2)) (by fun_prop))))
  have hpt : ∀ x : ℝ, ρ * ((1 : ℝ≥0∞) + ‖x‖ₑ) ^ b' * ∑ i ∈ range (k + 1), ∑ p ∈ range (k - i + 1),
      cR k i p * ∫⁻ γ, dnorm i m β γ * ENNReal.ofReal (PhiR1
        (bundle (yo ε y₁) (optE β x)) (bundle (yo ε y₂) (optE β x)) L0 a γ) =
      ∑ i ∈ range (k + 1), ∑ p ∈ range (k - i + 1), cR k i p * ρ *
        ∫⁻ γ, ((1 : ℝ≥0∞) + ‖x‖ₑ) ^ b' * (dnorm i m β γ * ENNReal.ofReal (PhiR1
          (bundle (yo ε y₁) (optE β x)) (bundle (yo ε y₂) (optE β x)) L0 a γ)) := fun x => by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [lintegral_const_mul' _ _ (ENNReal.rpow_ne_top_of_nonneg hb' (by simp))]
    ring
  simp_rw [hpt]
  have hI : ∀ i, Measurable fun x : ℝ => ∫⁻ γ, ((1 : ℝ≥0∞) + ‖x‖ₑ) ^ b' * (dnorm i m β γ *
      ENNReal.ofReal (PhiR1 (bundle (yo ε y₁) (optE β x)) (bundle (yo ε y₂) (optE β x)) L0 a γ)) :=
    fun i => (hG i).lintegral_prod_right'
  rw [lintegral_finsetSum _ fun i _ => Finset.measurable_sum _ fun p _ => (hI i).const_mul _]
  refine Finset.sum_le_sum fun i _ => ?_
  rw [lintegral_finsetSum _ fun p _ => (hI i).const_mul _]
  refine Finset.sum_le_sum fun p _ => ?_
  rw [lintegral_const_mul _ (hI i), lintegral_lintegral_swap (hG i).aemeasurable]
  have hdm : Measurable fun γ : ℝ × ℝ × ℝ => dnorm i m β γ :=
    (measurable_dnorm hs hm i).of_uncurry_left
  have hin : ∀ γ : ℝ × ℝ × ℝ, ∫⁻ x : ℝ, ((1 : ℝ≥0∞) + ‖x‖ₑ) ^ b' * (dnorm i m β γ *
      ENNReal.ofReal (PhiR1 (bundle (yo ε y₁) (optE β x)) (bundle (yo ε y₂) (optE β x)) L0 a γ)) ≤
      dnorm i m β γ * (KX * ((1 : ℝ≥0∞) + ∑ j, ‖β j‖ₑ + ‖γ.1‖ₑ + ‖γ.2.2‖ₑ) ^ (a + b')) := by
    intro γ
    have e : ∀ x : ℝ, ((1 : ℝ≥0∞) + ‖x‖ₑ) ^ b' * (dnorm i m β γ *
        ENNReal.ofReal (PhiR1 (bundle (yo ε y₁) (optE β x)) (bundle (yo ε y₂) (optE β x)) L0 a γ)) =
        dnorm i m β γ * (((1 : ℝ≥0∞) + ‖x‖ₑ) ^ b' * ENNReal.ofReal (PhiR1
          (bundle (yo ε y₁) (optE β x)) (bundle (yo ε y₂) (optE β x)) L0 a γ)) := fun x => by ring
    simp_rw [e]
    rw [lintegral_const_mul' (dnorm i m β γ) _ (by unfold dnorm; exact enorm_ne_top)]
    exact mul_le_mul' le_rfl (lintegral_x_PhiR1_le ha hb' hab hε hy₁ hy₂ L0 β γ)
  have hWm : Measurable fun γ : ℝ × ℝ × ℝ =>
      dnorm i m β γ * (KX * ((1 : ℝ≥0∞) + ∑ j, ‖β j‖ₑ + ‖γ.1‖ₑ + ‖γ.2.2‖ₑ) ^ (a + b')) :=
    hdm.mul (measurable_const.mul (by fun_prop))
  have hwm : Measurable fun γ : ℝ × ℝ × ℝ => wR θ β γ.1 γ.2.2 * dnorm i m β γ :=
    (by unfold wR; fun_prop : Measurable fun γ : ℝ × ℝ × ℝ => wR θ β γ.1 γ.2.2).mul hdm
  calc cR k i p * ρ * ∫⁻ γ, ∫⁻ x : ℝ, ((1 : ℝ≥0∞) + ‖x‖ₑ) ^ b' * (dnorm i m β γ *
        ENNReal.ofReal (PhiR1 (bundle (yo ε y₁) (optE β x)) (bundle (yo ε y₂) (optE β x)) L0 a γ))
      ≤ cR k i p * ρ * ∫⁻ γ, dnorm i m β γ *
          (KX * ((1 : ℝ≥0∞) + ∑ j, ‖β j‖ₑ + ‖γ.1‖ₑ + ‖γ.2.2‖ₑ) ^ (a + b')) :=
        mul_le_mul' le_rfl (lintegral_mono hin)
    _ = cR k i p * KX * ∫⁻ γ, dnorm i m β γ *
          (ρ * ((1 : ℝ≥0∞) + ∑ j, ‖β j‖ₑ + ‖γ.1‖ₑ + ‖γ.2.2‖ₑ) ^ (a + b')) := by
        have hW2 : Measurable fun γ : ℝ × ℝ × ℝ => dnorm i m β γ *
            (ρ * ((1 : ℝ≥0∞) + ∑ j, ‖β j‖ₑ + ‖γ.1‖ₑ + ‖γ.2.2‖ₑ) ^ (a + b')) :=
          hdm.mul (measurable_const.mul (by fun_prop))
        have e1 := lintegral_const_mul (μ := volume) ρ hWm
        have e2 := lintegral_const_mul (μ := volume) KX hW2
        calc cR k i p * ρ * ∫⁻ γ, dnorm i m β γ *
              (KX * ((1 : ℝ≥0∞) + ∑ j, ‖β j‖ₑ + ‖γ.1‖ₑ + ‖γ.2.2‖ₑ) ^ (a + b'))
            = cR k i p * ∫⁻ γ, ρ * (dnorm i m β γ *
              (KX * ((1 : ℝ≥0∞) + ∑ j, ‖β j‖ₑ + ‖γ.1‖ₑ + ‖γ.2.2‖ₑ) ^ (a + b'))) := by
              rw [e1, mul_assoc]
          _ = cR k i p * ∫⁻ γ, KX * (dnorm i m β γ *
              (ρ * ((1 : ℝ≥0∞) + ∑ j, ‖β j‖ₑ + ‖γ.1‖ₑ + ‖γ.2.2‖ₑ) ^ (a + b'))) := by
              congr 1
              exact lintegral_congr fun γ => by ring
          _ = _ := by rw [e2, mul_assoc]
    _ ≤ cR k i p * KX * ∫⁻ γ, wR θ β γ.1 γ.2.2 * dnorm i m β γ := by
        refine mul_le_mul' le_rfl (lintegral_mono fun γ => ?_)
        rw [mul_comm (wR θ β γ.1 γ.2.2)]
        exact mul_le_mul' le_rfl (hρ γ.1 γ.2.2)

/-- The constant of Lemma G for class `R`. -/
@[expose] noncomputable def KR (a b' : ℝ) : ℝ :=
  4 * (4 * CPhi * (6 * CE * Ir 2 * (2 ^ (a + b') * (2 * Ir (2 - a - b')))))

theorem KR_nonneg (a b' : ℝ) : 0 ≤ KR a b' := by
  have := CPhi_nonneg; have := CE_nonneg; have := Ir2_nonneg
  have : 0 ≤ Ir (2 - a - b') := ENNReal.toReal_nonneg
  unfold KR; positivity

/-- **Lemma G for class `R`, the symbol bound** (DH21 (propertyG1), (propertyH), and the weighted
version in the proof of (maincoef2.5)): for a basic class `R` symbol of norm `≤ N`, weights
`(1 + |v + γ₁|)^a` on the new frequency, `(1 + |α₁|)^{b'}` on the special variable and `ρ(α[A∖{1}])`
on the others, with `a + b' < 1` and `ρ (1 + Σ|α_j| + |γ₁| + |γ₃|)^{a+b'} ≤ wR θ`,
`∫∫ (1+|v+γ₁|)^a ρ (1+|α₁|)^{b'} |∂_α^k aR| ≤ gev (KR a b' · N) A k`. -/
theorem lintegral_weight_aR_le {θ a b' A N : ℝ} (ha : 0 ≤ a) (hb' : 0 ≤ b') (hab : a + b' < 1)
    (hA : A1 ≤ A) {R : RSym ι} (hR : R.Bound θ A N) {ρ : (ι → ℝ) → ℝ≥0∞} (hρm : Measurable ρ)
    (hρ : ∀ β γ₁ γ₃, ρ β * ((1 : ℝ≥0∞) + ∑ j, ‖β j‖ₑ + ‖γ₁‖ₑ + ‖γ₃‖ₑ) ^ (a + b') ≤
      wR θ β γ₁ γ₃) (L0 : ℝ) (k : ℕ) :
    ∫⁻ α, ∫⁻ ζ, ((1 : ℝ≥0∞) + ‖ζ.1 + ζ.2.1.1‖ₑ) ^ a * ρ (nsp α) * ((1 : ℝ≥0∞) + ‖α none‖ₑ) ^ b' *
      dnorm k (aR R.y₁ R.y₂ R.ε R.m L0) α ζ ≤ gev (KR a b' * N) A k := by
  have hs := hR.reg.smooth
  have hm := hR.reg.meas
  have ha1 : a ≤ 1 := by linarith
  have hA0 : 0 ≤ A := A1_nonneg.trans hA
  have hIr : 0 ≤ Ir (2 - a - b') := ENNReal.toReal_nonneg
  set KX := ENNReal.ofReal (2 ^ (a + b') * (2 * Ir (2 - a - b'))) with hKX
  -- the `α`-profile after the `ζ`-integration
  set F : (Option ι → ℝ) → ℝ≥0∞ := fun α => ρ (nsp α) * ((1 : ℝ≥0∞) + ‖α none‖ₑ) ^ b' *
    ∑ i ∈ range (k + 1), ∑ p ∈ range (k - i + 1), cR k i p * ∫⁻ γ, dnorm i R.m (nsp α) γ *
      ENNReal.ofReal (PhiR1 (bundle (yo R.ε R.y₁) α) (bundle (yo R.ε R.y₂) α) L0 a γ) with hF
  have hFm : Measurable F := by
    refine ((hρm.comp measurable_nsp).mul (by fun_prop)).mul
      (Finset.measurable_sum _ fun i _ => Finset.measurable_sum _ fun p _ =>
        Measurable.const_mul ?_ _)
    refine Measurable.lintegral_prod_right' (f := fun z : (Option ι → ℝ) × (ℝ × ℝ × ℝ) =>
      dnorm i R.m (nsp z.1) z.2 * ENNReal.ofReal (PhiR1 (bundle (yo R.ε R.y₁) z.1)
        (bundle (yo R.ε R.y₂) z.1) L0 a z.2)) ?_
    exact ((measurable_dnorm hs hm i).comp (f := fun z : (Option ι → ℝ) × (ℝ × ℝ × ℝ) =>
      (nsp z.1, z.2)) (by fun_prop)).mul (ENNReal.measurable_ofReal.comp
        ((measurable_PhiR1 L0 a).comp (f := fun z : (Option ι → ℝ) × (ℝ × ℝ × ℝ) =>
          ((bundle (yo R.ε R.y₁) z.1, bundle (yo R.ε R.y₂) z.1), z.2)) (by fun_prop)))
  have hJm : ∀ i, Measurable fun β : ι → ℝ => ∫⁻ γ, wR θ β γ.1 γ.2.2 * dnorm i R.m β γ := fun i =>
    (((by unfold wR; fun_prop : Measurable fun p : (ι → ℝ) × (ℝ × ℝ × ℝ) =>
      wR θ p.1 p.2.1 p.2.2.2)).mul (measurable_dnorm hs hm i)).lintegral_prod_right'
  have hgC : 0 ≤ 6 * CE * Ir 2 * (2 ^ (a + b') * (2 * Ir (2 - a - b'))) := by
    have := CE_nonneg; have := Ir2_nonneg
    have : 0 ≤ Ir (2 - a - b') := ENNReal.toReal_nonneg
    positivity
  calc ∫⁻ α, ∫⁻ ζ, ((1 : ℝ≥0∞) + ‖ζ.1 + ζ.2.1.1‖ₑ) ^ a * ρ (nsp α) *
        ((1 : ℝ≥0∞) + ‖α none‖ₑ) ^ b' * dnorm k (aR R.y₁ R.y₂ R.ε R.m L0) α ζ
      ≤ ∫⁻ α, F α := by
        refine lintegral_mono fun α => ?_
        have hmeas : Measurable fun ζ : ℝ × ((ℝ × ℝ × ℝ) × ℝ) =>
            ((1 : ℝ≥0∞) + ‖ζ.1 + ζ.2.1.1‖ₑ) ^ a * aRbd R.m R.y₁ R.y₂ R.ε L0 k α ζ :=
          (by fun_prop : Measurable fun ζ : ℝ × ((ℝ × ℝ × ℝ) × ℝ) =>
            ((1 : ℝ≥0∞) + ‖ζ.1 + ζ.2.1.1‖ₑ) ^ a).mul
            (measurable_aRbd hs hm R.y₁ R.y₂ R.ε L0 k).of_uncurry_left
        calc ∫⁻ ζ, ((1 : ℝ≥0∞) + ‖ζ.1 + ζ.2.1.1‖ₑ) ^ a * ρ (nsp α) *
              ((1 : ℝ≥0∞) + ‖α none‖ₑ) ^ b' * dnorm k (aR R.y₁ R.y₂ R.ε R.m L0) α ζ
            ≤ ∫⁻ ζ, ρ (nsp α) * ((1 : ℝ≥0∞) + ‖α none‖ₑ) ^ b' *
                (((1 : ℝ≥0∞) + ‖ζ.1 + ζ.2.1.1‖ₑ) ^ a * aRbd R.m R.y₁ R.y₂ R.ε L0 k α ζ) := by
              refine lintegral_mono fun ζ => ?_
              calc ((1 : ℝ≥0∞) + ‖ζ.1 + ζ.2.1.1‖ₑ) ^ a * ρ (nsp α) *
                    ((1 : ℝ≥0∞) + ‖α none‖ₑ) ^ b' * dnorm k (aR R.y₁ R.y₂ R.ε R.m L0) α ζ
                  ≤ ((1 : ℝ≥0∞) + ‖ζ.1 + ζ.2.1.1‖ₑ) ^ a * ρ (nsp α) *
                    ((1 : ℝ≥0∞) + ‖α none‖ₑ) ^ b' * aRbd R.m R.y₁ R.y₂ R.ε L0 k α ζ :=
                    mul_le_mul' le_rfl (dnorm_aR_le_bd hR.bundle₁ hR.bundle₂ hR.sign hs L0 k α ζ)
                _ = _ := by ring
          _ = ρ (nsp α) * ((1 : ℝ≥0∞) + ‖α none‖ₑ) ^ b' *
                ∫⁻ ζ, ((1 : ℝ≥0∞) + ‖ζ.1 + ζ.2.1.1‖ₑ) ^ a * aRbd R.m R.y₁ R.y₂ R.ε L0 k α ζ :=
              lintegral_const_mul _ hmeas
          _ ≤ F α := mul_le_mul' le_rfl (lintegral_weight_aRbd_pt ha ha1 hs hm R.y₁ R.y₂ R.ε L0 k α)
    _ = ∫⁻ β : ι → ℝ, ∫⁻ x : ℝ, F (optE β x) := lintegral_optionPi hFm
    _ ≤ ∫⁻ β : ι → ℝ, ∑ i ∈ range (k + 1), ∑ p ∈ range (k - i + 1),
          cR k i p * KX * ∫⁻ γ, wR θ β γ.1 γ.2.2 * dnorm i R.m β γ := by
        refine lintegral_mono fun β => ?_
        simp only [hF, optE_none]
        exact lintegral_x_aR_le ha hb' hab hR.sign hR.bundle₁ hR.bundle₂ hs hm L0 k β (hρ β)
    _ = ∑ i ∈ range (k + 1), ∑ p ∈ range (k - i + 1), cR k i p * KX * rNorm θ i R.m := by
        rw [lintegral_finsetSum _ fun i _ => Finset.measurable_sum _ fun p _ => (hJm i).const_mul _]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [lintegral_finsetSum _ fun p _ => (hJm i).const_mul _]
        refine Finset.sum_congr rfl fun p _ => ?_
        rw [lintegral_const_mul _ (hJm i), rNorm]
    _ ≤ ∑ i ∈ range (k + 1), (k.choose i : ℝ≥0∞) * gev N A i *
          ∑ p ∈ range (k - i + 1), ((k - i).choose p : ℝ≥0∞) * gev CPhi A p *
            gev (6 * CE * Ir 2 * (2 ^ (a + b') * (2 * Ir (2 - a - b')))) A (k - i - p) := by
        refine Finset.sum_le_sum fun i _ => ?_
        rw [Finset.mul_sum]
        refine Finset.sum_le_sum fun p _ => ?_
        have h1 : gev CPhi Achi p ≤ gev CPhi A p :=
          gev_mono le_rfl Achi_nonneg (Achi_le_A1.trans hA) CPhi_nonneg p
        have h2 : gev (6 * CE * Ir 2) A1 (k - i - p) * KX ≤
            gev (6 * CE * Ir 2 * (2 ^ (a + b') * (2 * Ir (2 - a - b')))) A (k - i - p) := by
          rw [mul_comm, hKX, gev_mul_const _ (by positivity)]
          refine gev_mono (le_of_eq (by ring)) A1_nonneg hA hgC _
        have h3 := hR.norm i
        calc cR k i p * KX * rNorm θ i R.m = (k.choose i : ℝ≥0∞) * ((k - i).choose p : ℝ≥0∞) *
              gev CPhi Achi p * (gev (6 * CE * Ir 2) A1 (k - i - p) * KX) * rNorm θ i R.m := by
              unfold cR; ring
          _ ≤ (k.choose i : ℝ≥0∞) * ((k - i).choose p : ℝ≥0∞) * gev CPhi A p *
              gev (6 * CE * Ir 2 * (2 ^ (a + b') * (2 * Ir (2 - a - b')))) A (k - i - p) *
                gev N A i := by gcongr
          _ = _ := by ring
    _ ≤ ∑ i ∈ range (k + 1), (k.choose i : ℝ≥0∞) * gev N A i *
          gev (4 * CPhi * (6 * CE * Ir 2 * (2 ^ (a + b') * (2 * Ir (2 - a - b'))))) A (k - i) := by
        gcongr with i hi
        exact gev_conv_le CPhi_nonneg hgC hA0 (fun j => le_rfl) (fun j => le_rfl) (k - i)
    _ ≤ gev (4 * N * (4 * CPhi * (6 * CE * Ir 2 * (2 ^ (a + b') * (2 * Ir (2 - a - b')))))) A k :=
        gev_conv_le hR.nonneg (by have := CPhi_nonneg; positivity) hA0 (fun j => le_rfl)
          (fun j => le_rfl) k
    _ = gev (KR a b' * N) A k := by unfold KR; congr 1; ring


/-- **Lemma G for class `R`, regularity**: `aR` is a regular symbol. -/
theorem aR_symReg {θ A N : ℝ} (h0θ : 0 ≤ θ) (hA : A1 ≤ A) {R : RSym ι} (hR : R.Bound θ A N)
    (L0 : ℝ) : SymReg (aR R.y₁ R.y₂ R.ε R.m L0) := by
  refine SymReg.of_lintegral (contDiff_aR _ _ _ hR.reg.smooth L0)
    (measurable_aR _ _ _ hR.reg.meas L0).stronglyMeasurable fun k => ?_
  have h := lintegral_weight_aR_le (a := 0) (b' := 0) le_rfl le_rfl (by norm_num) hA hR
    (ρ := fun _ => 1) measurable_const (fun β γ₁ γ₃ => by
      simpa using one_le_wR h0θ β γ₁ γ₃) L0 k
  simp only [ENNReal.rpow_zero, one_mul, mul_one] at h
  exact ne_top_of_le_ne_top (by simp [gev]) h

end RBound

end WaveTurbulence.ClassJR
