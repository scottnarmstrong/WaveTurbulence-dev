/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.ClassJR.Lemma55

/-!
# Superpositions with arbitrary coefficient maps

DH21 removes Dirac masses in the time-frequency coefficients with (extraid) (L1054–L1060):
`e^{πiγt} = ∫ M₀(σ) e^{πi(γ+σ)t} dσ` for `t ∈ [0, 1]`. Applied to both time variables, a
superposition `∫ a(α, z) J_{ℓ; c(z)} dz` with an *arbitrary* measurable coefficient map `c`
equals, on the triangle, the generalized representation
`∫∫ M₀(u₁) M₀(u₂) a(α, z) J_{ℓ; u + c(z)} du dz` (`jker_eq_smooth`), which `JSym.ofGen` converts
into a basic class `J` operator. The price is the factor `CM0 = ∫ (1+|σ|)|M₀| · ∫ |M₀|`, since
the weight `(1 + Σ|α_j| + |u₁ + c₁|)^θ` is at most `(1 + |u₁|)` times the weight at `c₁`
(`JSym.ofAny`). The class `R` analogue (`RSym.ofAny`) keeps the third coefficient `γ₃`, which
must be one of the integration variables.
-/

public section

open MeasureTheory Set Filter Finset Complex
open scoped ContDiff ENNReal Real

namespace WaveTurbulence.ClassJR

attribute [local instance] isAddRightInvariant_volume_prod

variable {ι : Type*} [Fintype ι]

section MulFixed

theorem dnorm_mul_fixed {Y Z : Type*} (k : ℕ) (g : Y → ℂ) (a : (ι → ℝ) → Z → ℂ)
    (ha : ∀ z, ContDiff ℝ ∞ fun α => a α z) (α : ι → ℝ) (p : Y × Z) :
    dnorm k (fun α (p : Y × Z) => g p.1 * a α p.2) α p = ‖g p.1‖ₑ * dnorm k a α p.2 := by
  have e : lift1 (fun α (p : Y × Z) => g p.1 * a α p.2) p = g p.1 • lift1 a p.2 := by
    funext β; simp [lift1, smul_eq_mul]
  unfold dnorm
  rw [e, iteratedFDeriv_const_smul_apply
    ((contDiff_lift1 (ha p.2)).of_le (by exact_mod_cast le_top)).contDiffAt, enorm_smul]

/-- Multiplying a regular symbol by a fixed integrable function of new auxiliary variables. -/
theorem SymReg.mul_fixed {Y Z : Type*} [MeasureSpace Y] [MeasureSpace Z]
    [SFinite (volume : Measure Y)] [SFinite (volume : Measure Z)] {a : (ι → ℝ) → Z → ℂ}
    (ha : SymReg a) {g : Y → ℂ} (hg : Integrable g) (hgm : StronglyMeasurable g) :
    SymReg fun α (p : Y × Z) => g p.1 * a α p.2 where
  smooth p := contDiff_const.mul (ha.smooth p.2)
  meas := (hgm.comp_measurable (measurable_fst.comp measurable_snd)).mul
    (ha.meas.comp_measurable (measurable_fst.prodMk (measurable_snd.comp measurable_snd)))
  dom k := by
    have e : ∀ p : Y × Z, supD k (fun α (p : Y × Z) => g p.1 * a α p.2) p =
        ‖g p.1‖ₑ * supD k a p.2 := fun p => by
      simp only [supD, dnorm_mul_fixed k g a ha.smooth, ENNReal.mul_iSup]
    simp_rw [e]
    rw [Measure.volume_eq_prod, lintegral_prod_mul hg.aestronglyMeasurable.enorm
      (measurable_supD ha.smooth ha.meas k).aemeasurable]
    exact ENNReal.mul_ne_top hg.2.ne (ha.dom k)

end MulFixed

section Smooth

/-- **Smoothing both coefficients** (DH21 (extraid) applied to `t` and `s`). -/
theorem jker_eq_smooth (L c₁ c₂ : ℝ) {t s : ℝ} (ht : t ∈ Icc (0 : ℝ) 1)
    (hs : s ∈ Icc (0 : ℝ) 1) :
    jker L c₁ c₂ t s = ∫ u : ℝ × ℝ, M0 u.1 * M0 u.2 * jker L (u.1 + c₁) (u.2 + c₂) t s := by
  have e : ∀ u : ℝ × ℝ, M0 u.1 * M0 u.2 * jker L (u.1 + c₁) (u.2 + c₂) t s =
      (M0 u.1 * cexp (π * I * ((c₁ + u.1) * t))) * (M0 u.2 * cexp (π * I * ((c₂ + u.2) * s))) *
        cexp (π * I * (L * (t - s))) := fun u => by
    simp only [jker]
    push_cast
    rw [show (π : ℂ) * I * (L * (t - s) + (u.1 + c₁) * t + (u.2 + c₂) * s) =
      π * I * ((c₁ + u.1) * t) + π * I * ((c₂ + u.2) * s) + π * I * (L * (t - s)) by ring,
      Complex.exp_add, Complex.exp_add]
    ring
  simp_rw [e]
  rw [MeasureTheory.integral_mul_const, Measure.volume_eq_prod,
    integral_prod_mul (f := fun σ => M0 σ * cexp (π * I * ((c₁ + σ) * t)))
      (g := fun τ => M0 τ * cexp (π * I * ((c₂ + τ) * s))), ← extraid c₁ ht, ← extraid c₂ hs]
  simp only [jker]
  rw [show (π : ℂ) * I * (L * (t - s) + c₁ * t + c₂ * s) =
    π * I * (c₁ * t) + π * I * (c₂ * s) + π * I * (L * (t - s)) by ring,
    Complex.exp_add, Complex.exp_add]

/-- `∫ (1 + |σ|) |M₀(σ)| dσ < ∞`. -/
theorem lintegral_M0_weight_ne_top : ∫⁻ σ : ℝ, (1 + ‖σ‖ₑ) * ‖M0 σ‖ₑ ≠ ⊤ := by
  obtain ⟨K, hK, hb⟩ := exists_M0_bound
  have h : ∀ σ : ℝ, (1 + ‖σ‖ₑ) * ‖M0 σ‖ₑ ≤ ENNReal.ofReal K *
      ENNReal.ofReal ((1 + |σ|) ^ (-(2 : ℝ))) := fun σ => by
    rw [show (1 : ℝ≥0∞) + ‖σ‖ₑ = ENNReal.ofReal (1 + |σ|) by
      rw [ENNReal.ofReal_add zero_le_one (abs_nonneg _), ENNReal.ofReal_one, ← Real.norm_eq_abs,
        ofReal_norm], ← ofReal_norm, ← ENNReal.ofReal_mul (by positivity),
      ← ENNReal.ofReal_mul hK]
    refine ENNReal.ofReal_le_ofReal ?_
    have hp : 0 < 1 + |σ| := by positivity
    have e : (1 + |σ|) ^ (-(2 : ℝ)) = (1 + |σ|) * ((1 + |σ|) ^ 3)⁻¹ := by
      rw [Real.rpow_neg hp.le, show ((1 + |σ|) ^ (2 : ℝ)) = (1 + |σ|) ^ (2 : ℕ) by norm_cast]
      field_simp
    rw [e]
    calc (1 + |σ|) * ‖M0 σ‖ ≤ (1 + |σ|) * (K / (1 + |σ|) ^ 3) :=
          mul_le_mul_of_nonneg_left (hb σ) hp.le
      _ = K * ((1 + |σ|) * ((1 + |σ|) ^ 3)⁻¹) := by ring
  refine ne_top_of_le_ne_top ?_ (lintegral_mono h)
  rw [lintegral_const_mul _ (by fun_prop)]
  exact ENNReal.mul_ne_top (by simp) (lintegral_Ir_ne_top (by norm_num))

theorem lintegral_M0_ne_top : ∫⁻ σ : ℝ, ‖M0 σ‖ₑ ≠ ⊤ := integrable_M0.2.ne

/-- The smoothing constant `∫ (1+|σ|)|M₀| · ∫ |M₀|`. -/
@[expose] noncomputable def CM0 : ℝ :=
  ((∫⁻ σ : ℝ, (1 + ‖σ‖ₑ) * ‖M0 σ‖ₑ) * ∫⁻ σ : ℝ, ‖M0 σ‖ₑ).toReal

theorem CM0_nonneg : 0 ≤ CM0 := ENNReal.toReal_nonneg

theorem ofReal_CM0 : ENNReal.ofReal CM0 =
    (∫⁻ σ : ℝ, (1 + ‖σ‖ₑ) * ‖M0 σ‖ₑ) * ∫⁻ σ : ℝ, ‖M0 σ‖ₑ :=
  ENNReal.ofReal_toReal (ENNReal.mul_ne_top lintegral_M0_weight_ne_top lintegral_M0_ne_top)

/-- `(1 + S + |u + c|)^θ ≤ (1 + |u|) (1 + S + |c|)^θ` for `0 ≤ θ ≤ 1`. -/
theorem rpow_shift_le {θ : ℝ} (h0 : 0 ≤ θ) (h1 : θ ≤ 1) (S : ℝ≥0∞) (u c : ℝ) :
    (1 + S + ‖u + c‖ₑ) ^ θ ≤ (1 + ‖u‖ₑ) * (1 + S + ‖c‖ₑ) ^ θ := by
  have hW : (1 : ℝ≥0∞) ≤ 1 + S + ‖c‖ₑ := le_add_right le_self_add
  calc (1 + S + ‖u + c‖ₑ) ^ θ ≤ ((1 + S + ‖c‖ₑ) * (1 + ‖u‖ₑ)) ^ θ := by
        refine rpow_mono' h0 ?_
        calc 1 + S + ‖u + c‖ₑ ≤ (1 + S + ‖c‖ₑ) + ‖u‖ₑ := by
              calc 1 + S + ‖u + c‖ₑ ≤ 1 + S + (‖u‖ₑ + ‖c‖ₑ) := by
                    gcongr; exact enorm_add_le _ _
                _ = _ := by ring
          _ ≤ (1 + S + ‖c‖ₑ) + (1 + S + ‖c‖ₑ) * ‖u‖ₑ :=
              add_le_add le_rfl (le_mul_of_one_le_left bot_le hW)
          _ = (1 + S + ‖c‖ₑ) * (1 + ‖u‖ₑ) := by ring
    _ = (1 + S + ‖c‖ₑ) ^ θ * (1 + ‖u‖ₑ) ^ θ := ENNReal.mul_rpow_of_nonneg _ _ h0
    _ ≤ (1 + S + ‖c‖ₑ) ^ θ * (1 + ‖u‖ₑ) := by
        gcongr
        exact (ENNReal.rpow_le_rpow_of_exponent_le le_self_add h1).trans_eq (ENNReal.rpow_one _)
    _ = (1 + ‖u‖ₑ) * (1 + S + ‖c‖ₑ) ^ θ := mul_comm _ _

end Smooth


section OfAny

variable {Z : Type*} [MeasureSpace Z] [SFinite (volume : Measure Z)]

omit [SFinite (volume : Measure Z)] in
theorem measurable_wJ_comp {θ : ℝ} {f : Z → ℝ} (hf : Measurable f) (α : ι → ℝ) :
    Measurable fun z => wJ θ α (f z) := by
  unfold wJ; exact (measurable_const.add hf.enorm).pow_const θ

omit [SFinite (volume : Measure Z)] in
theorem measurable_wR_comp {θ : ℝ} {f g : Z → ℝ} (hf : Measurable f) (hg : Measurable g)
    (α : ι → ℝ) : Measurable fun z => wR θ α (f z) (g z) := by
  unfold wR; exact ((measurable_const.add hf.enorm).add hg.enorm).pow_const θ

theorem wJ_shift_le {θ : ℝ} (h0 : 0 ≤ θ) (h1 : θ ≤ 1) (α : ι → ℝ) (u c : ℝ) :
    wJ θ α (u + c) ≤ (1 + ‖u‖ₑ) * wJ θ α c := rpow_shift_le h0 h1 _ u c

theorem wR_shift_le {θ : ℝ} (h0 : 0 ≤ θ) (h1 : θ ≤ 1) (α : ι → ℝ) (u c g : ℝ) :
    wR θ α (u + c) g ≤ (1 + ‖u‖ₑ) * wR θ α c g := by
  have e : ∀ v : ℝ, wR θ α v g = (1 + (∑ j, ‖α j‖ₑ + ‖g‖ₑ) + ‖v‖ₑ) ^ θ := fun v => by
    unfold wR; congr 1; ring
  rw [e, e]
  exact rpow_shift_le h0 h1 _ u c

/-- The density `M₀ ⊗ M₀`. -/
@[expose] noncomputable def M00 (u : ℝ × ℝ) : ℂ := M0 u.1 * M0 u.2

theorem continuous_M00 : Continuous M00 :=
  (continuous_M0.comp continuous_fst).mul (continuous_M0.comp continuous_snd)

theorem integrable_M00 : Integrable M00 := by
  rw [Measure.volume_eq_prod]; exact integrable_M0.mul_prod integrable_M0

theorem lintegral_M00_weight :
    ∫⁻ u : ℝ × ℝ, (1 + ‖u.1‖ₑ) * ‖M00 u‖ₑ = ENNReal.ofReal CM0 := by
  rw [ofReal_CM0, Measure.volume_eq_prod]
  have : ∀ u : ℝ × ℝ, (1 + ‖u.1‖ₑ) * ‖M00 u‖ₑ = ((1 + ‖u.1‖ₑ) * ‖M0 u.1‖ₑ) * ‖M0 u.2‖ₑ :=
    fun u => by simp only [M00, enorm_mul]; ring
  simp_rw [this]
  exact lintegral_prod_mul ((measurable_const.add measurable_id.enorm).mul
    continuous_M0.measurable.enorm).aemeasurable continuous_M0.measurable.enorm.aemeasurable

/-- The smoothed generalized symbol is regular. -/
theorem SymReg.smoothed {a : (ι → ℝ) → Z → ℂ} (ha : SymReg a) :
    SymReg fun α (p : (ℝ × ℝ) × Z) => M00 p.1 * a α p.2 :=
  ha.mul_fixed integrable_M00 continuous_M00.stronglyMeasurable

/-- Fubini for the smoothed superposition. -/
theorem integral_smoothed {f : Z → ℂ} (hf : Integrable f) (L : ℝ) {c : Z → ℝ × ℝ}
    (hc : Measurable c) {t s : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) (hs : s ∈ Icc (0 : ℝ) 1)
    (φ : Z → ℂ) (hφ : AEStronglyMeasurable φ) {C : ℝ} (hφC : ∀ z, ‖φ z‖ ≤ C) :
    ∫ ζ : (ℝ × ℝ) × Z, M00 ζ.1 * f ζ.2 * (φ ζ.2 * jker L (ζ.1.1 + (c ζ.2).1)
      (ζ.1.2 + (c ζ.2).2) t s) = ∫ z, f z * (φ z * jker L (c z).1 (c z).2 t s) := by
  have hJ : Continuous fun p : ℝ × ℝ => jker L p.1 p.2 t s := by unfold jker; fun_prop
  have hint : Integrable (fun ζ : (ℝ × ℝ) × Z => M00 ζ.1 * f ζ.2 *
      (φ ζ.2 * jker L (ζ.1.1 + (c ζ.2).1) (ζ.1.2 + (c ζ.2).2) t s)) := by
    have h0 : Integrable (fun ζ : (ℝ × ℝ) × Z => M00 ζ.1 * f ζ.2) := by
      rw [Measure.volume_eq_prod]; exact integrable_M00.mul_prod hf
    refine (h0.norm.const_mul (max C 0)).mono' ?_ (Eventually.of_forall fun ζ => ?_)
    · refine h0.aestronglyMeasurable.mul ((hφ.comp_quasiMeasurePreserving
        Measure.quasiMeasurePreserving_snd).mul ?_)
      exact (hJ.measurable.comp ((measurable_fst.comp measurable_fst).add
        (measurable_fst.comp (hc.comp measurable_snd)) |>.prodMk
        ((measurable_snd.comp measurable_fst).add
          (measurable_snd.comp (hc.comp measurable_snd))))).aestronglyMeasurable
    · rw [norm_mul, norm_mul, norm_mul, norm_jker, mul_one, mul_comm]
      exact mul_le_mul_of_nonneg_right ((hφC _).trans (le_max_left _ _)) (by positivity)
  rw [Measure.volume_eq_prod] at hint ⊢
  rw [integral_prod_symm _ hint]
  refine integral_congr_ae (Eventually.of_forall fun z => ?_)
  simp only
  have e : ∀ u : ℝ × ℝ, M00 u * f z * (φ z * jker L (u.1 + (c z).1) (u.2 + (c z).2) t s) =
      f z * φ z * (M0 u.1 * M0 u.2 * jker L (u.1 + (c z).1) (u.2 + (c z).2) t s) :=
    fun u => by simp only [M00]; ring
  simp_rw [e]
  rw [MeasureTheory.integral_const_mul, ← jker_eq_smooth L _ _ ht hs]
  ring

end OfAny

section ROfGen

variable {Q : Type*} [MeasureSpace Q] [SFinite (volume : Measure Q)]

theorem norm_rker_le (a b γ₁ γ₂ γ₃ t s : ℝ) : ‖rker a b γ₁ γ₂ γ₃ t s‖ ≤ CPhi := by
  rw [rker, norm_mul, norm_jker, mul_one]; exact norm_chiInvR_le _

theorem continuous_rker_coeff (a b t s : ℝ) :
    Continuous fun γ : ℝ × ℝ × ℝ => rker a b γ.1 γ.2.1 γ.2.2 t s := by
  unfold rker
  exact (contDiff_chiInvRc.continuous.comp (continuous_const.add
    (continuous_snd.comp continuous_snd))).mul ((continuous_jker_coeff b t s).comp
      (continuous_fst.prodMk (continuous_fst.comp continuous_snd)))

/-- `((x₁,x₂),(g,η)) ↦ ((x₁,(x₂,g)),η)`. -/
@[expose] def reassocR : (ℝ × ℝ) × (ℝ × Q) ≃ᵐ (ℝ × ℝ × ℝ) × Q :=
  (MeasurableEquiv.prodAssoc (α := ℝ × ℝ) (β := ℝ) (γ := Q)).symm.trans
    (MeasurableEquiv.prodCongr MeasurableEquiv.prodAssoc (MeasurableEquiv.refl Q))

omit [SFinite (volume : Measure Q)] in
@[simp] theorem reassocR_apply (p : (ℝ × ℝ) × (ℝ × Q)) :
    reassocR p = ((p.1.1, (p.1.2, p.2.1)), p.2.2) := rfl

theorem measurePreserving_reassocR : MeasurePreserving (reassocR (Q := Q)) := by
  have h1 := (volume_preserving_prodAssoc (α₁ := ℝ × ℝ) (β₁ := ℝ) (γ₁ := Q)).symm
  have h2 : MeasurePreserving (Prod.map (MeasurableEquiv.prodAssoc (α := ℝ) (β := ℝ) (γ := ℝ))
      (id : Q → Q)) :=
    MeasurePreserving.prod volume_preserving_prodAssoc (MeasurePreserving.id volume)
  exact h2.comp h1

end ROfGen

end WaveTurbulence.ClassJR
