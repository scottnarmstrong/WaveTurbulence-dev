/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.ClassJR.MCE
public import WaveTurbulence.Foundations.ClassJR.MCSob

/-!
# Lemma G: class `J` operators applied to an exponential

DH21 Proposition 5.1, Case 2.1 (L1121–L1126, (expandG)–(propertyH)). For a basic class `J` operator
`𝒥 = ∫ m(α, γ) J_{ℓ(α); γ₁, γ₂} dγ` and `λ₀ ∈ ℝ`, the function `t ↦ 𝒥(e^{πiλ₀ s})(t)`, `t ∈ [0, 1]`, is
a superposition of exponentials `e^{πiλt}`.

Since `J_{ℓ;γ₁,γ₂}(e^{πiλ₀ s})(t) = e^{πi(ℓ+γ₁)t} ∫_0^t e^{πi(γ₂+λ₀-ℓ)u} du`, `integral_gE_mul_exp` gives
`𝒥(e^{πiλ₀ s})(t) = ∫ aG(α; v, γ, τ) e^{πi(v + γ₁) t} dv dγ dτ` (`volterra_jsym_exp`), where
`aG(α; v, γ, τ) = m(α, γ) gE(γ₂ + λ₀ - ℓ(α); v - ℓ(α), τ)`.

The main variable `v` is translated by the bundle `ℓ(α)`. This keeps the shift `b(v, γ, τ) = γ₁` of the
frequency `v + γ₁` independent of `α`, so the `α`-derivatives fall on `gE` along the diagonal
(`lintegral_gED_le`) and never on `γ`. This is DH21's remark "if part of the weight is
`|γ₂ + λ₀ - ℓ|^{1/4}`, it can be treated by exploiting the denominator" (L1124).

The symbol bounds (`lintegral_weight_aG_le`) are DH21 (propertyG) combined with (typeJ2):
`∫ (1 + |v + γ₁|)^a ρ(α) |∂_α^k aG| ≤ gev (12 C_E Ir(2) N) A k`, whenever the weight
`ρ(α) (1 + |ℓ(α) + γ₁|)^a` is dominated by the class `J` weight `wJ θ α γ₁`.
-/

public section

open MeasureTheory Set Filter Finset Complex
open scoped ContDiff ENNReal Real

namespace WaveTurbulence.ClassJR

open WaveTurbulence.Fourier

attribute [local instance] isAddRightInvariant_volume_prod

section Identity

variable {ι : Type*} [Fintype ι]

theorem norm_jker_eq (ℓ γ₁ γ₂ t s : ℝ) : ‖jker ℓ γ₁ γ₂ t s‖ = 1 := by
  rw [jker, Complex.norm_exp]
  simp

/-- `J_{ℓ;γ₁,γ₂}(e^{πiλ₀ s})(t) = e^{πi(ℓ+γ₁)t} ∫_0^t e^{πi(γ₂+λ₀-ℓ)u} du`. -/
theorem integral_jker_mul_exp (ℓ γ₁ γ₂ L0 t : ℝ) :
    ∫ s in (0 : ℝ)..t, jker ℓ γ₁ γ₂ t s * cexp (π * I * (L0 * s)) =
      cexp (π * I * ((ℓ + γ₁) * t)) * eInt (γ₂ + L0 - ℓ) t := by
  rw [eInt, ← intervalIntegral.integral_const_mul]
  refine intervalIntegral.integral_congr fun s _ => ?_
  simp only [jker]
  rw [← Complex.exp_add, ← Complex.exp_add]
  congr 1
  push_cast
  ring

/-- **The class `J` operator applied to an exponential**, before the superposition:
`𝒥(e^{πiλ₀s})(t) = ∫ m(α,γ) e^{πi(ℓ+γ₁)t} ∫_0^t e^{πi(γ₂+λ₀-ℓ)u} du dγ`. -/
theorem volterra_jsym_exp_aux (R : JSym ι) (hR : SymReg R.m) (α : ι → ℝ) (L0 : ℝ) {t : ℝ}
    (ht : 0 ≤ t) :
    volterra (R.kernel α) (fun s => cexp (π * I * (L0 * s))) t =
      ∫ γ : ℝ × ℝ, R.m α γ * (cexp (π * I * ((bundle R.y α + γ.1) * t)) *
        eInt (γ.2 + L0 - bundle R.y α) t) := by
  set ℓ := bundle R.y α
  have hm := hR.integrable α
  have hF : Integrable (fun p : ℝ × (ℝ × ℝ) =>
      R.m α p.2 * jker ℓ p.2.1 p.2.2 t p.1 * cexp (π * I * (L0 * p.1)))
      ((volume.restrict (Ioc 0 t)).prod volume) := by
    have hmeas : AEStronglyMeasurable (fun p : ℝ × (ℝ × ℝ) =>
        R.m α p.2 * jker ℓ p.2.1 p.2.2 t p.1 * cexp (π * I * (L0 * p.1)))
        ((volume.restrict (Ioc 0 t)).prod volume) := by
      refine ((hm.aestronglyMeasurable.comp_snd).mul ?_).mul ?_
      · exact (by unfold jker; fun_prop : Continuous fun p : ℝ × (ℝ × ℝ) =>
          jker ℓ p.2.1 p.2.2 t p.1).aestronglyMeasurable
      · exact (by fun_prop : Continuous fun p : ℝ × (ℝ × ℝ) =>
          cexp (π * I * (L0 * p.1))).aestronglyMeasurable
    have hI : Integrable (fun p : ℝ × (ℝ × ℝ) => ‖R.m α p.2‖)
        ((volume.restrict (Ioc 0 t)).prod volume) :=
      (integrable_const (1 : ℝ)).mul_prod hm.norm |>.congr (Eventually.of_forall fun p => by simp)
    refine hI.mono' hmeas (Eventually.of_forall fun p => ?_)
    rw [norm_mul, norm_mul, norm_jker_eq, Complex.norm_exp]
    simp
  rw [volterra, intervalIntegral.integral_of_le ht]
  have e1 : ∀ s, R.kernel α t s * cexp (π * I * (L0 * s)) =
      ∫ γ, R.m α γ * jker ℓ γ.1 γ.2 t s * cexp (π * I * (L0 * s)) := fun s => by
    rw [JSym.kernel, ← integral_mul_const]
  simp_rw [e1]
  rw [integral_integral_swap hF]
  refine integral_congr_ae (Eventually.of_forall fun γ => ?_)
  simp only
  have e2 : (fun s => R.m α γ * jker ℓ γ.1 γ.2 t s * cexp (π * I * (L0 * s))) =
      fun s => R.m α γ * (jker ℓ γ.1 γ.2 t s * cexp (π * I * (L0 * s))) := by
    funext s; ring
  rw [e2, integral_const_mul, ← intervalIntegral.integral_of_le ht, integral_jker_mul_exp]

/-- **The coefficient of Lemma G**: `aG(α; v, γ, τ) = m(α, γ) gE(γ₂ + λ₀ - ℓ(α); v - ℓ(α), τ)`,
on the main variable `v` and the auxiliary variables `(γ, τ)`. -/
@[expose] noncomputable def aG (y : ι → ℤ) (m : (ι → ℝ) → ℝ × ℝ → ℂ) (L0 : ℝ) (α : ι → ℝ)
    (ζ : ℝ × ((ℝ × ℝ) × ℝ)) : ℂ :=
  m α ζ.2.1 * gE (ζ.2.1.2 + L0 - bundle y α) (ζ.1 - bundle y α, ζ.2.2)

end Identity

section Reorder

/-- The relabelling `(γ, (v, τ)) ↦ (v, (γ, τ))`. -/
@[expose] noncomputable def eGV : (ℝ × ℝ) × (ℝ × ℝ) ≃ᵐ ℝ × ((ℝ × ℝ) × ℝ) :=
  (MeasurableEquiv.prodAssoc.symm.trans
    ((MeasurableEquiv.prodComm).prodCongr (MeasurableEquiv.refl ℝ))).trans
    MeasurableEquiv.prodAssoc

theorem eGV_apply (p : (ℝ × ℝ) × (ℝ × ℝ)) : eGV p = (p.2.1, (p.1, p.2.2)) := rfl

theorem measurePreserving_eGV : MeasurePreserving eGV := by
  have h1 : MeasurePreserving (MeasurableEquiv.prodAssoc.symm :
      (ℝ × ℝ) × (ℝ × ℝ) ≃ᵐ ((ℝ × ℝ) × ℝ) × ℝ) := volume_preserving_prodAssoc.symm _
  have h2 : MeasurePreserving ((MeasurableEquiv.prodComm).prodCongr (MeasurableEquiv.refl ℝ) :
      ((ℝ × ℝ) × ℝ) × ℝ ≃ᵐ (ℝ × (ℝ × ℝ)) × ℝ) := by
    have := (Measure.measurePreserving_swap (μ := (volume : Measure (ℝ × ℝ)))
      (ν := (volume : Measure ℝ))).prod (MeasurePreserving.id (volume : Measure ℝ))
    exact this
  have h3 : MeasurePreserving (MeasurableEquiv.prodAssoc :
      (ℝ × (ℝ × ℝ)) × ℝ ≃ᵐ ℝ × ((ℝ × ℝ) × ℝ)) := volume_preserving_prodAssoc
  exact (h3.comp h2).comp h1

theorem integral_eGV (F : ℝ × ((ℝ × ℝ) × ℝ) → ℂ) :
    ∫ ζ, F ζ = ∫ p : (ℝ × ℝ) × (ℝ × ℝ), F (p.2.1, (p.1, p.2.2)) :=
  (measurePreserving_eGV.integral_comp' F).symm

theorem lintegral_eGV (F : ℝ × ((ℝ × ℝ) × ℝ) → ℝ≥0∞) :
    ∫⁻ ζ, F ζ = ∫⁻ p : (ℝ × ℝ) × (ℝ × ℝ), F (p.2.1, (p.1, p.2.2)) :=
  (measurePreserving_eGV.lintegral_comp_emb eGV.measurableEmbedding F).symm

/-- `∫ F(ζ) dζ = ∫_γ ∫_q F(q.1, γ, q.2)`. -/
theorem lintegral_eGV_iter {F : ℝ × ((ℝ × ℝ) × ℝ) → ℝ≥0∞} (hF : Measurable F) :
    ∫⁻ ζ, F ζ = ∫⁻ γ : ℝ × ℝ, ∫⁻ q : ℝ × ℝ, F (q.1, (γ, q.2)) := by
  rw [lintegral_eGV]
  exact lintegral_prod (fun p : (ℝ × ℝ) × (ℝ × ℝ) => F (p.2.1, (p.1, p.2.2)))
    (hF.comp eGV.measurable).aemeasurable

end Reorder

section Identity2

variable {ι : Type*} [Fintype ι]

theorem lintegral_enorm_gE_le (x : ℝ) : ∫⁻ q : ℝ × ℝ, ‖gE x q‖ₑ ≤ ENNReal.ofReal (2 * CE * Ir 2) := by
  have h := lintegral_gE_le (a := 0) le_rfl zero_le_one 0 x
  simp only [ENNReal.rpow_zero, one_mul, iteratedDeriv_zero, pow_zero, mul_zero,
    Nat.factorial_zero, Nat.cast_one, mul_one] at h
  refine h.trans (ENNReal.ofReal_le_ofReal ?_)
  have hp : (1 + |x|) ^ ((0 : ℝ) - 1) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by linarith [abs_nonneg x]) (by norm_num)
  have := CE_nonneg; have := Ir2_nonneg
  exact mul_le_of_le_one_right (by positivity) hp

theorem integrable_gE (x : ℝ) : Integrable (gE x) := by
  refine ⟨(measurable_gE.comp measurable_prodMk_left).aestronglyMeasurable, ?_⟩
  exact (lintegral_enorm_gE_le x).trans_lt ENNReal.ofReal_lt_top

theorem sub_shift1 (q : ℝ × ℝ) (c : ℝ) : q - (c, 0) = (q.1 - c, q.2) := by
  ext <;> simp

/-- Translation in the first coordinate of `ℝ²`. -/
theorem lintegral_shift1 (F : ℝ × ℝ → ℝ≥0∞) (c : ℝ) :
    ∫⁻ q : ℝ × ℝ, F (q.1 - c, q.2) = ∫⁻ q, F q := by
  have := lintegral_sub_right_eq_self (μ := (volume : Measure (ℝ × ℝ))) F (c, 0)
  simpa only [sub_shift1] using this

/-- Translation in the first coordinate of `ℝ²`. -/
theorem integral_shift1 (F : ℝ × ℝ → ℂ) (c : ℝ) :
    ∫ q : ℝ × ℝ, F (q.1 - c, q.2) = ∫ q, F q := by
  have := integral_sub_right_eq_self (μ := (volume : Measure (ℝ × ℝ))) F (c, 0)
  simpa only [sub_shift1] using this

@[fun_prop] theorem measurable_bundle (y : ι → ℤ) : Measurable (bundle y) :=
  (continuous_bundle y).measurable

theorem measurable_aG (y : ι → ℤ) {m : (ι → ℝ) → ℝ × ℝ → ℂ}
    (hm : StronglyMeasurable (Function.uncurry m)) (L0 : ℝ) :
    Measurable (Function.uncurry (aG y m L0)) := by
  show Measurable fun p : (ι → ℝ) × (ℝ × ((ℝ × ℝ) × ℝ)) =>
    m p.1 p.2.2.1 * gE (p.2.2.1.2 + L0 - bundle y p.1) (p.2.1 - bundle y p.1, p.2.2.2)
  have h1 : Measurable fun p : (ι → ℝ) × (ℝ × ((ℝ × ℝ) × ℝ)) => m p.1 p.2.2.1 :=
    hm.measurable.comp (f := fun p : (ι → ℝ) × (ℝ × ((ℝ × ℝ) × ℝ)) => (p.1, p.2.2.1))
      (by fun_prop)
  have h2 : Measurable fun p : (ι → ℝ) × (ℝ × ((ℝ × ℝ) × ℝ)) =>
      gE (p.2.2.1.2 + L0 - bundle y p.1) (p.2.1 - bundle y p.1, p.2.2.2) :=
    measurable_gE.comp (f := fun p : (ι → ℝ) × (ℝ × ((ℝ × ℝ) × ℝ)) =>
      (p.2.2.1.2 + L0 - bundle y p.1, (p.2.1 - bundle y p.1, p.2.2.2))) (by fun_prop)
  exact h1.mul h2

/-- `∫ |aG(α; ζ)| dζ ≤ 2 C_E Ir(2) ∫ |m(α, γ)| dγ`. -/
theorem lintegral_enorm_aG_le (y : ι → ℤ) {m : (ι → ℝ) → ℝ × ℝ → ℂ}
    (hm : StronglyMeasurable (Function.uncurry m)) (L0 : ℝ) (α : ι → ℝ) :
    ∫⁻ ζ, ‖aG y m L0 α ζ‖ₑ ≤ ENNReal.ofReal (2 * CE * Ir 2) * ∫⁻ γ, ‖m α γ‖ₑ := by
  have hmeas : Measurable fun ζ => ‖aG y m L0 α ζ‖ₑ :=
    ((measurable_aG y hm L0).comp measurable_prodMk_left).enorm
  have hm2 : Measurable fun p : (ℝ × ℝ) × (ℝ × ℝ) => ‖aG y m L0 α (p.2.1, (p.1, p.2.2))‖ₑ :=
    hmeas.comp eGV.measurable
  rw [lintegral_eGV]
  rw [show (∫⁻ p : (ℝ × ℝ) × (ℝ × ℝ), ‖aG y m L0 α (p.2.1, (p.1, p.2.2))‖ₑ) =
      ∫⁻ γ : ℝ × ℝ, ∫⁻ q : ℝ × ℝ, ‖aG y m L0 α (q.1, (γ, q.2))‖ₑ from
    lintegral_prod _ hm2.aemeasurable, ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  refine lintegral_mono fun γ => ?_
  simp only [aG, enorm_mul]
  rw [lintegral_const_mul' _ _ enorm_ne_top, mul_comm]
  gcongr
  rw [lintegral_shift1 (fun q => ‖gE (γ.2 + L0 - bundle y α) q‖ₑ)]
  exact lintegral_enorm_gE_le _

theorem integrable_aG (y : ι → ℤ) {m : (ι → ℝ) → ℝ × ℝ → ℂ} (hR : SymReg m) (L0 : ℝ)
    (α : ι → ℝ) : Integrable (aG y m L0 α) := by
  refine ⟨((measurable_aG y hR.meas L0).comp
    measurable_prodMk_left).aestronglyMeasurable, ?_⟩
  refine (lintegral_enorm_aG_le y hR.meas L0 α).trans_lt (ENNReal.mul_lt_top ENNReal.ofReal_lt_top ?_)
  exact (hR.integrable α).2

/-- **Lemma G, the identity** (DH21 (expandG), (expandH)): for `t ∈ [0, 1]`,
`𝒥(e^{πiλ₀s})(t) = ∫ aG(α; v, γ, τ) e^{πi(v+γ₁)t}`. -/
theorem volterra_jsym_exp (R : JSym ι) (hR : SymReg R.m) (α : ι → ℝ) (L0 : ℝ) {t : ℝ}
    (ht : t ∈ Icc (0 : ℝ) 1) :
    volterra (R.kernel α) (fun s => cexp (π * I * (L0 * s))) t =
      ∫ ζ, aG R.y R.m L0 α ζ * cexp (π * I * ((ζ.1 + ζ.2.1.1) * t)) := by
  have hint : Integrable fun ζ : ℝ × ((ℝ × ℝ) × ℝ) =>
      aG R.y R.m L0 α ζ * cexp (π * I * ((ζ.1 + ζ.2.1.1) * t)) := by
    refine (integrable_aG R.y hR L0 α).mul_bdd (c := 1) (by fun_prop)
      (Eventually.of_forall fun ζ => ?_)
    rw [Complex.norm_exp]; simp
  have hint' : Integrable (fun p : (ℝ × ℝ) × (ℝ × ℝ) =>
      aG R.y R.m L0 α (p.2.1, (p.1, p.2.2)) * cexp (π * I * ((p.2.1 + p.1.1) * t)))
      ((volume : Measure (ℝ × ℝ)).prod volume) := by
    have := (measurePreserving_eGV.integrable_comp_emb eGV.measurableEmbedding).2 hint
    exact this
  have hsplit : (∫ p : (ℝ × ℝ) × (ℝ × ℝ),
      aG R.y R.m L0 α (p.2.1, (p.1, p.2.2)) * cexp (π * I * ((p.2.1 + p.1.1) * t))) =
      ∫ γ : ℝ × ℝ, ∫ q : ℝ × ℝ,
        aG R.y R.m L0 α (q.1, (γ, q.2)) * cexp (π * I * ((q.1 + γ.1) * t)) :=
    integral_prod _ hint'
  rw [volterra_jsym_exp_aux R hR α L0 ht.1, integral_eGV]
  dsimp only
  rw [hsplit]
  refine integral_congr_ae (Eventually.of_forall fun γ => ?_)
  simp only [aG]
  rw [← integral_gE_mul_exp _ ht, ← integral_const_mul, ← integral_const_mul]
  rw [← integral_shift1 (fun q : ℝ × ℝ => R.m α γ * (cexp (π * I * ((bundle R.y α + γ.1) * t)) *
      (gE (γ.2 + L0 - bundle R.y α) q * cexp (π * I * (q.1 * t))))) (bundle R.y α)]
  refine integral_congr_ae (Eventually.of_forall fun q => ?_)
  simp only
  have e : cexp (π * I * ((bundle R.y α + γ.1) * t)) *
      cexp (π * I * ((q.1 - bundle R.y α : ℝ) * t)) = cexp (π * I * ((q.1 + γ.1) * t)) := by
    rw [← Complex.exp_add]; congr 1; push_cast; ring
  rw [← e]
  ring

end Identity2

section Bounds

variable {ι : Type*} [Fintype ι]

/-- The diagonal profile `gD c v τ u = gE (c - u) (v - u, τ)`. -/
@[expose] noncomputable def gD (c v τ : ℝ) (u : ℝ) : ℂ := gE (c - u) (v - u, τ)

theorem contDiff_gD (c v τ : ℝ) : ContDiff ℝ ∞ (gD c v τ) := by
  by_cases hτ : τ ∈ Icc (0 : ℝ) 1
  · have e : gD c v τ = fun y => (chi0 (c - y) : ℂ) * ftπ phiM (v - τ * c - (1 - τ) * y) +
        (phiR (c - y) * M0 (v - c) - phiR (c - y) * M0 (v - y)) := gE_diag_eq hτ c v
    rw [e]
    have hP : ContDiff ℝ ∞ fun y => phiR (c - y) :=
      contDiff_phiR.comp (contDiff_const.sub contDiff_id)
    exact ((contDiff_chi0c.comp (contDiff_const.sub contDiff_id)).mul
      (contDiff_FP.comp (contDiff_const.sub (contDiff_const.mul contDiff_id)))).add
      ((hP.mul contDiff_const).sub (hP.mul (contDiff_M0.comp (contDiff_const.sub contDiff_id))))
  · have e : gD c v τ = fun _ => 0 := gE_diag_eq_zero hτ c v
    rw [e]
    exact contDiff_const

theorem aG_eq_gD (y : ι → ℤ) (m : (ι → ℝ) → ℝ × ℝ → ℂ) (L0 : ℝ) (α : ι → ℝ)
    (ζ : ℝ × ((ℝ × ℝ) × ℝ)) :
    aG y m L0 α ζ = m α ζ.2.1 * gD (ζ.2.1.2 + L0) ζ.1 ζ.2.2 (bundle y α) := by
  simp only [aG, gD]

theorem contDiff_aG (y : ι → ℤ) {m : (ι → ℝ) → ℝ × ℝ → ℂ}
    (hs : ∀ γ, ContDiff ℝ ∞ fun α => m α γ) (L0 : ℝ) (ζ : ℝ × ((ℝ × ℝ) × ℝ)) :
    ContDiff ℝ ∞ fun α => aG y m L0 α ζ := by
  simp_rw [aG_eq_gD]
  exact (hs _).mul ((contDiff_gD _ _ _).comp (contDiff_bundle y))

/-- **The pointwise Leibniz bound for `aG`**. -/
theorem dnorm_aG_le {y : ι → ℤ} (hy : IsBundle y) {m : (ι → ℝ) → ℝ × ℝ → ℂ}
    (hs : ∀ γ, ContDiff ℝ ∞ fun α => m α γ) (L0 : ℝ) (k : ℕ) (α : ι → ℝ)
    (ζ : ℝ × ((ℝ × ℝ) × ℝ)) :
    dnorm k (aG y m L0) α ζ ≤ ∑ i ∈ range (k + 1), (k.choose i : ℝ≥0∞) * dnorm i m α ζ.2.1 *
      ‖iteratedDeriv (k - i) (gD (ζ.2.1.2 + L0) ζ.1 ζ.2.2) (bundle y α)‖ₑ := by
  have hl : lift1 (aG y m L0) ζ = fun β => lift1 m ζ.2.1 β *
      gD (ζ.2.1.2 + L0) ζ.1 ζ.2.2 (bundleL y β + 0) := by
    funext β
    simp only [lift1, bundleL_apply, add_zero]
    exact aG_eq_gD y m L0 _ ζ
  rw [dnorm, hl]
  refine (enorm_iteratedFDeriv_mul_le (contDiff_lift1 (hs _))
    ((contDiff_gD _ _ _).comp ((bundleL y).contDiff.add contDiff_const)) _ k).trans ?_
  refine Finset.sum_le_sum fun i _ => ?_
  refine mul_le_mul' le_rfl ?_
  refine (enorm_iteratedFDeriv_scalar_le (contDiff_gD _ _ _) (bundleL y) (norm_bundleL_le hy) 0 _
    (k - i)).trans_eq ?_
  simp [bundleL_apply]

theorem one_le_wJ_of {θ : ℝ} (h0 : 0 ≤ θ) (α : ι → ℝ) (γ₁ : ℝ) : 1 ≤ wJ θ α γ₁ := by
  unfold wJ
  rcases eq_or_lt_of_le h0 with h | h
  · rw [← h, ENNReal.rpow_zero]
  · exact ENNReal.one_le_rpow (by simp only [add_assoc]; exact le_self_add) h

/-- The majorant of `dnorm k aG` (`dnorm_aG_le` with `enorm_iteratedDeriv_gED_le_bd`). -/
@[expose] noncomputable def aGbd (m : (ι → ℝ) → ℝ × ℝ → ℂ) (y : ι → ℤ) (L0 : ℝ) (k : ℕ)
    (α : ι → ℝ) (ζ : ℝ × ((ℝ × ℝ) × ℝ)) : ℝ≥0∞ :=
  ∑ i ∈ range (k + 1), (k.choose i : ℝ≥0∞) * dnorm i m α ζ.2.1 *
    gEDbd (k - i) (ζ.2.1.2 + L0) (bundle y α) (ζ.1, ζ.2.2)

theorem dnorm_aG_le_bd {y : ι → ℤ} (hy : IsBundle y) {m : (ι → ℝ) → ℝ × ℝ → ℂ}
    (hs : ∀ γ, ContDiff ℝ ∞ fun α => m α γ) (L0 : ℝ) (k : ℕ) (α : ι → ℝ)
    (ζ : ℝ × ((ℝ × ℝ) × ℝ)) : dnorm k (aG y m L0) α ζ ≤ aGbd m y L0 k α ζ := by
  refine (dnorm_aG_le hy hs L0 k α ζ).trans (Finset.sum_le_sum fun i _ => ?_)
  exact mul_le_mul' le_rfl (enorm_iteratedDeriv_gED_le_bd (k - i) _ _ (ζ.1, ζ.2.2))

theorem measurable_aGbd {y : ι → ℤ} {m : (ι → ℝ) → ℝ × ℝ → ℂ}
    (hs : ∀ γ, ContDiff ℝ ∞ fun α => m α γ) (hm : StronglyMeasurable (Function.uncurry m))
    (L0 : ℝ) (k : ℕ) : Measurable (Function.uncurry (aGbd m y L0 k)) := by
  show Measurable fun p : (ι → ℝ) × (ℝ × ((ℝ × ℝ) × ℝ)) =>
    ∑ i ∈ range (k + 1), (k.choose i : ℝ≥0∞) * dnorm i m p.1 p.2.2.1 *
      gEDbd (k - i) (p.2.2.1.2 + L0) (bundle y p.1) (p.2.1, p.2.2.2)
  refine Finset.measurable_sum _ fun i _ => ?_
  refine (measurable_const.mul ((measurable_dnorm hs hm i).comp
    (measurable_fst.prodMk (measurable_fst.comp (measurable_snd.comp measurable_snd))))).mul ?_
  exact (measurable_gEDbd (k - i)).comp (f := fun p : (ι → ℝ) × (ℝ × ((ℝ × ℝ) × ℝ)) =>
    (p.2.2.1.2 + L0, (bundle y p.1, (p.2.1, p.2.2.2)))) (by fun_prop)

/-- An elementary inequality: `ρ · (K X Y) ≤ K · w` when `ρ X ≤ w` and `Y ≤ 1`. -/
theorem rel_aux {Kc X Y : ℝ} {ρ w : ℝ≥0∞} (hK : 0 ≤ Kc) (hX0 : 0 ≤ X) (hY : Y ≤ 1)
    (h : ρ * ENNReal.ofReal X ≤ w) : ρ * ENNReal.ofReal (Kc * (X * Y)) ≤ ENNReal.ofReal Kc * w := by
  rw [ENNReal.ofReal_mul hK, ENNReal.ofReal_mul hX0]
  calc ρ * (ENNReal.ofReal Kc * (ENNReal.ofReal X * ENNReal.ofReal Y))
      ≤ ρ * (ENNReal.ofReal Kc * (ENNReal.ofReal X * 1)) := by
        gcongr; exact ENNReal.ofReal_le_one.2 hY
    _ = ENNReal.ofReal Kc * (ρ * ENNReal.ofReal X) := by ring
    _ ≤ _ := mul_le_mul' le_rfl h

/-- **Lemma G, the symbol bound at one `α`** (DH21 (propertyG) with (typeJ2)). -/
theorem lintegral_weight_aGbd_le_pt {θ a : ℝ} (h0a : 0 ≤ a) (ha1 : a ≤ 1) {y : ι → ℤ}
    {m : (ι → ℝ) → ℝ × ℝ → ℂ} (hs : ∀ γ, ContDiff ℝ ∞ fun α => m α γ)
    (hm : StronglyMeasurable (Function.uncurry m)) {ρ : (ι → ℝ) → ℝ≥0∞}
    (hρ : ∀ α γ₁, ρ α * ((1 : ℝ≥0∞) + ‖bundle y α + γ₁‖ₑ) ^ a ≤ wJ θ α γ₁)
    (L0 : ℝ) (k : ℕ) (α : ι → ℝ) :
    ∫⁻ ζ, ((1 : ℝ≥0∞) + ‖ζ.1 + ζ.2.1.1‖ₑ) ^ a * ρ α * aGbd m y L0 k α ζ ≤
      ∑ i ∈ range (k + 1), (k.choose i : ℝ≥0∞) *
        ENNReal.ofReal (3 * CE * Ir 2 * A1 ^ (k - i) * (Nat.factorial (2 * (k - i)) : ℝ)) *
          ∫⁻ γ, wJ θ α γ.1 * dnorm i m α γ := by
  set ℓ := bundle y α with hℓ
  have hdm : ∀ i, Measurable fun γ : ℝ × ℝ => dnorm i m α γ := fun i =>
    (measurable_dnorm hs hm i).of_uncurry_left
  have hgm : ∀ (j : ℕ) (γ : ℝ × ℝ), Measurable fun q : ℝ × ℝ => gEDbd j (γ.2 + L0) ℓ q :=
    fun j γ => (measurable_gEDbd j).comp (f := fun q : ℝ × ℝ => (γ.2 + L0, (ℓ, q)))
      (by fun_prop)
  have hH : Measurable fun ζ : ℝ × ((ℝ × ℝ) × ℝ) =>
      ((1 : ℝ≥0∞) + ‖ζ.1 + ζ.2.1.1‖ₑ) ^ a * ρ α * aGbd m y L0 k α ζ :=
    (by fun_prop : Measurable fun ζ : ℝ × ((ℝ × ℝ) × ℝ) =>
      ((1 : ℝ≥0∞) + ‖ζ.1 + ζ.2.1.1‖ₑ) ^ a * ρ α).mul
      (measurable_aGbd hs hm L0 k).of_uncurry_left
  rw [lintegral_eGV_iter hH]
  have hDi : ∀ i, Measurable fun γ : ℝ × ℝ => wJ θ α γ.1 * dnorm i m α γ := fun i =>
    (by unfold wJ; fun_prop : Measurable fun γ : ℝ × ℝ => wJ θ α γ.1).mul (hdm i)
  have hR : (∑ i ∈ range (k + 1), (k.choose i : ℝ≥0∞) *
      ENNReal.ofReal (3 * CE * Ir 2 * A1 ^ (k - i) * (Nat.factorial (2 * (k - i)) : ℝ)) *
        ∫⁻ γ, wJ θ α γ.1 * dnorm i m α γ) = ∫⁻ γ, ∑ i ∈ range (k + 1), (k.choose i : ℝ≥0∞) *
      ENNReal.ofReal (3 * CE * Ir 2 * A1 ^ (k - i) * (Nat.factorial (2 * (k - i)) : ℝ)) *
        (wJ θ α γ.1 * dnorm i m α γ) := by
    rw [lintegral_finsetSum _ fun i _ => (hDi i).const_mul _]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [lintegral_const_mul _ (hDi i)]
  rw [hR]
  dsimp only
  refine lintegral_mono fun γ => ?_
  -- the inner integral at fixed `γ`
  have hexp : ∀ q : ℝ × ℝ, ((1 : ℝ≥0∞) + ‖q.1 + γ.1‖ₑ) ^ a * ρ α *
      aGbd m y L0 k α (q.1, (γ, q.2)) = ∑ i ∈ range (k + 1), (k.choose i : ℝ≥0∞) *
        dnorm i m α γ * ρ α * (((1 : ℝ≥0∞) + ‖q.1 + γ.1‖ₑ) ^ a *
          gEDbd (k - i) (γ.2 + L0) ℓ q) := fun q => by
    simp only [aGbd, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    ring
  simp_rw [hexp]
  have hterm : ∀ i, Measurable fun q : ℝ × ℝ => (k.choose i : ℝ≥0∞) * dnorm i m α γ * ρ α *
      (((1 : ℝ≥0∞) + ‖q.1 + γ.1‖ₑ) ^ a * gEDbd (k - i) (γ.2 + L0) ℓ q) := fun i =>
    measurable_const.mul ((by fun_prop : Measurable fun q : ℝ × ℝ =>
      ((1 : ℝ≥0∞) + ‖q.1 + γ.1‖ₑ) ^ a).mul (hgm (k - i) γ))
  rw [lintegral_finsetSum _ fun i _ => hterm i]
  refine Finset.sum_le_sum fun i _ => ?_
  have hq : Measurable fun q : ℝ × ℝ =>
      ((1 : ℝ≥0∞) + ‖q.1 + γ.1‖ₑ) ^ a * gEDbd (k - i) (γ.2 + L0) ℓ q :=
    (by fun_prop : Measurable fun q : ℝ × ℝ => ((1 : ℝ≥0∞) + ‖q.1 + γ.1‖ₑ) ^ a).mul
      (hgm (k - i) γ)
  rw [lintegral_const_mul _ hq]
  have hb := lintegral_gEDbd_le h0a ha1 (k - i) (γ.2 + L0) ℓ γ.1
  have hC : 0 ≤ 3 * CE * Ir 2 * A1 ^ (k - i) * (Nat.factorial (2 * (k - i)) : ℝ) := by
    have := CE_nonneg; have := Ir2_nonneg; have := A1_nonneg; positivity
  have hrel : ρ α * ENNReal.ofReal (3 * CE * Ir 2 * A1 ^ (k - i) *
      (Nat.factorial (2 * (k - i)) : ℝ) * ((1 + |ℓ + γ.1|) ^ a *
        (1 + |γ.2 + L0 - ℓ|) ^ (a - 1))) ≤
      ENNReal.ofReal (3 * CE * Ir 2 * A1 ^ (k - i) * (Nat.factorial (2 * (k - i)) : ℝ)) *
        wJ θ α γ.1 := by
    have hY : (1 + |γ.2 + L0 - ℓ|) ^ (a - 1) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos
      (by linarith [abs_nonneg (γ.2 + L0 - ℓ)]) (by linarith)
    have hX : ρ α * ENNReal.ofReal ((1 + |ℓ + γ.1|) ^ a) ≤ wJ θ α γ.1 := by
      rw [← one_add_enorm_rpow_eq]; exact hρ α γ.1
    exact rel_aux hC (by positivity) hY hX
  calc (k.choose i : ℝ≥0∞) * dnorm i m α γ * ρ α *
        ∫⁻ q : ℝ × ℝ, ((1 : ℝ≥0∞) + ‖q.1 + γ.1‖ₑ) ^ a * gEDbd (k - i) (γ.2 + L0) ℓ q
      ≤ (k.choose i : ℝ≥0∞) * dnorm i m α γ * (ρ α *
          ENNReal.ofReal (3 * CE * Ir 2 * A1 ^ (k - i) * (Nat.factorial (2 * (k - i)) : ℝ) *
            ((1 + |ℓ + γ.1|) ^ a * (1 + |γ.2 + L0 - ℓ|) ^ (a - 1)))) := by
        rw [mul_assoc]
        exact mul_le_mul' le_rfl (mul_le_mul' le_rfl hb)
    _ ≤ (k.choose i : ℝ≥0∞) * dnorm i m α γ * (ENNReal.ofReal (3 * CE * Ir 2 *
          A1 ^ (k - i) * (Nat.factorial (2 * (k - i)) : ℝ)) * wJ θ α γ.1) :=
        mul_le_mul' le_rfl hrel
    _ = _ := by ring

/-- **Lemma G, the symbol bound** (DH21 (propertyG), (propertyH)): for a basic class `J` symbol of
norm `≤ N` and a weight `ρ(α)` with `ρ(α)(1 + |ℓ(α) + γ₁|)^a ≤ wJ θ α γ₁`,
`∫∫ (1 + |v + γ₁|)^a ρ(α) |∂_α^k aG| ≤ gev (12 C_E Ir(2) N) A k` for `A ≥ A₁`. -/
theorem lintegral_weight_aG_le {θ a A N : ℝ} (h0a : 0 ≤ a) (ha1 : a ≤ 1) (hA : A1 ≤ A)
    {R : JSym ι} (hR : R.Bound θ A N) {ρ : (ι → ℝ) → ℝ≥0∞}
    (hρ : ∀ α γ₁, ρ α * ((1 : ℝ≥0∞) + ‖bundle R.y α + γ₁‖ₑ) ^ a ≤ wJ θ α γ₁)
    (L0 : ℝ) (k : ℕ) :
    ∫⁻ α, ∫⁻ ζ, ((1 : ℝ≥0∞) + ‖ζ.1 + ζ.2.1.1‖ₑ) ^ a * ρ α * dnorm k (aG R.y R.m L0) α ζ ≤
      gev (12 * CE * Ir 2 * N) A k := by
  have hs := hR.reg.smooth
  have hm := hR.reg.meas
  have hJm : ∀ i, Measurable fun α : ι → ℝ => ∫⁻ γ, wJ θ α γ.1 * dnorm i R.m α γ := fun i =>
    (((by unfold wJ; fun_prop : Measurable fun p : (ι → ℝ) × (ℝ × ℝ) => wJ θ p.1 p.2.1)).mul
      (measurable_dnorm hs hm i)).lintegral_prod_right'
  calc ∫⁻ α, ∫⁻ ζ, ((1 : ℝ≥0∞) + ‖ζ.1 + ζ.2.1.1‖ₑ) ^ a * ρ α * dnorm k (aG R.y R.m L0) α ζ
      ≤ ∫⁻ α, ∫⁻ ζ, ((1 : ℝ≥0∞) + ‖ζ.1 + ζ.2.1.1‖ₑ) ^ a * ρ α * aGbd R.m R.y L0 k α ζ :=
        lintegral_mono fun α => lintegral_mono fun ζ =>
          mul_le_mul' le_rfl (dnorm_aG_le_bd hR.bundle hs L0 k α ζ)
    _ ≤ ∫⁻ α, ∑ i ∈ range (k + 1), (k.choose i : ℝ≥0∞) *
          ENNReal.ofReal (3 * CE * Ir 2 * A1 ^ (k - i) * (Nat.factorial (2 * (k - i)) : ℝ)) *
            ∫⁻ γ, wJ θ α γ.1 * dnorm i R.m α γ :=
        lintegral_mono fun α => lintegral_weight_aGbd_le_pt h0a ha1 hs hm hρ L0 k α
    _ = ∑ i ∈ range (k + 1), (k.choose i : ℝ≥0∞) * jNorm θ i R.m *
          gev (3 * CE * Ir 2) A1 (k - i) := by
        rw [lintegral_finsetSum _ fun i _ => (hJm i).const_mul _]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [lintegral_const_mul _ (hJm i), jNorm, gev]
        ring_nf
    _ ≤ ∑ i ∈ range (k + 1), (k.choose i : ℝ≥0∞) * jNorm θ i R.m *
          gev (3 * CE * Ir 2) A (k - i) := by
        gcongr with i hi
        exact gev_mono le_rfl A1_nonneg hA (by have := CE_nonneg; have := Ir2_nonneg; positivity) _
    _ ≤ gev (4 * N * (3 * CE * Ir 2)) A k :=
        gev_conv_le hR.nonneg (by have := CE_nonneg; have := Ir2_nonneg; positivity)
          (A1_nonneg.trans hA) (fun j => hR.norm j) (fun j => le_rfl) k
    _ = gev (12 * CE * Ir 2 * N) A k := by congr 1; ring

/-- **Lemma G, regularity**: the coefficient `aG` is a regular symbol on `ℝ × ((ℝ × ℝ) × ℝ)`. -/
theorem aG_symReg {θ A N : ℝ} (h0θ : 0 ≤ θ) (hA : A1 ≤ A) {R : JSym ι} (hR : R.Bound θ A N)
    (L0 : ℝ) : SymReg (aG R.y R.m L0) := by
  refine SymReg.of_lintegral (contDiff_aG R.y hR.reg.smooth L0)
    (measurable_aG R.y hR.reg.meas L0).stronglyMeasurable fun k => ?_
  have h := lintegral_weight_aG_le (a := 0) le_rfl zero_le_one hA hR (ρ := fun _ => 1)
    (fun α γ₁ => by simpa using one_le_wJ_of h0θ α γ₁) L0 k
  simp only [ENNReal.rpow_zero, one_mul, mul_one] at h
  exact ne_top_of_le_ne_top (by simp [gev]) h

end Bounds

end WaveTurbulence.ClassJR
