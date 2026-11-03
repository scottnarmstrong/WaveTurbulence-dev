/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.ClassJR.InvBounds

/-!
# DH21 Lemma 5.8: `I_{εα₁} I_{μ₁-εα₁}`

`I_{εα₁} I_{μ₁-εα₁} = χ_∞(α₁)/(επiα₁) 𝒥_{α[ ],μ₁} + 𝒥_{α₁,μ₁} + ℛ_{α₁,μ₁}` (DH21 L1086–L1106).
The kernel is `e^{πiμ₁s} E(εα₁, t-s)`, and splitting `E` with `χ₀ + χ_∞` gives
* I = `∫ M(εα₁, q) J_{0;σ,μ₁-σ} dq` (class `J` in `α₁`: `M` has compact support in `α₁`);
* II = `-Φ(εα₁) J_{0;0,μ₁}`, where `Φ(εα₁) = χ_∞(α₁)/(επiα₁)` (`phiR_sign`);
* III = `Φ(εα₁) J_{εα₁;0,μ₁}`: replacing `χ_∞(εα₁)/(εα₁)` by its average
  `∫ ρ(g) χ_∞(εα₁+g)/(εα₁+g) dg`, `ρ = ½ 1_{[-1,1]}`, gives a class `R` operator, and the
  error is a class `J` operator (`norm_chiInvR_diff_le`).

The variables are `α : Option Empty → ℝ` (`α₁ = α none`), so the class `R` part has special
variable `α₁` and no other variables; `𝒥_{α[ ],μ₁}` has the variables `Empty`. All bounds are
uniform in `μ₁`; the class `J` bound needs `θ < 1` (the error decays like `(1+|α₁|)^{-2}`).
-/

public section

open MeasureTheory Set Filter Finset Complex
open scoped ContDiff ENNReal Real

namespace WaveTurbulence.ClassJR

open WaveTurbulence.Fourier

section General

variable {ι : Type*} [Fintype ι]

theorem dnorm_const_le {Z : Type*} (k : ℕ) (f : Z → ℂ) (α : ι → ℝ) (z : Z) :
    dnorm k (fun _ z => f z) α z ≤ if k = 0 then ‖f z‖ₑ else 0 := by
  unfold dnorm
  have e : lift1 (fun (_ : ι → ℝ) z => f z) z = fun _ => f z := rfl
  rw [e]
  split_ifs with hk
  · subst hk; rw [← ofReal_norm, norm_iteratedFDeriv_zero, ofReal_norm]
  · rw [iteratedFDeriv_const_of_ne hk]; simp

/-- A symbol independent of `α`. -/
theorem SymReg.const {Z : Type*} [MeasureSpace Z] {f : Z → ℂ} (hf : Integrable f)
    (hfm : StronglyMeasurable f) : SymReg (fun (_ : ι → ℝ) z => f z) where
  smooth z := contDiff_const
  meas := hfm.comp_measurable measurable_snd
  dom k := by
    refine ne_top_of_le_ne_top hf.2.ne (lintegral_mono fun z => iSup_le fun α =>
      (dnorm_const_le k f α z).trans ?_)
    split_ifs <;> simp

/-- Derivatives of a function of one bundle. -/
theorem dnorm_comp_bundle_le {Z : Type*} {y : ι → ℤ} (hy : IsBundle y) {F : ℝ → Z → ℂ}
    (hF : ∀ z, ContDiff ℝ ∞ fun x => F x z) (k : ℕ) (α : ι → ℝ) (z : Z) :
    dnorm k (fun α z => F (bundle y α) z) α z ≤
      ‖iteratedDeriv k (fun x => F x z) (bundle y α)‖ₑ := by
  unfold dnorm
  have e : lift1 (fun α z => F (bundle y α) z) z = (fun x => F x z) ∘ bundleL y := by
    funext β; rfl
  rw [e]
  refine (enorm_iteratedFDeriv_comp_le (hF z) (bundleL y) (norm_bundleL_le hy) _ k).trans_eq ?_
  rw [← ofReal_norm, ← ofReal_norm, norm_iteratedFDeriv_eq_norm_iteratedDeriv]
  rfl

end General

section OneVar

theorem lintegral_optE {G : ℝ → ℝ≥0∞} : ∫⁻ α : Option Empty → ℝ, G (α none) = ∫⁻ t, G t :=
  (volume_preserving_funUnique (Option Empty) ℝ).lintegral_comp_emb
    (MeasurableEquiv.funUnique (Option Empty) ℝ).measurableEmbedding G

theorem lintegral_emptyFun (G : (Empty → ℝ) → ℝ≥0∞) : ∫⁻ α, G α = G isEmptyElim := by
  rw [show (volume : Measure (Empty → ℝ)) = Measure.pi fun _ => volume from rfl,
    Measure.pi_of_empty, lintegral_dirac]

theorem lintegral_unit (G : Unit → ℝ≥0∞) : ∫⁻ z, G z = G () := by
  rw [show (volume : Measure Unit) = Measure.dirac () from rfl, lintegral_dirac]

theorem bundle_emptyFun (y : Empty → ℤ) (α : Empty → ℝ) : bundle y α = 0 := by
  simp [bundle]

theorem bundle_optE (y : Option Empty → ℤ) (α : Option Empty → ℝ) :
    bundle y α = y none * α none := by
  simp [bundle]; rfl

theorem wJ_emptyFun (θ : ℝ) (α : Empty → ℝ) (γ : ℝ) : wJ θ α γ = (1 + ‖γ‖ₑ) ^ θ := by
  simp [wJ]

theorem wR_emptyFun (θ : ℝ) (α : Empty → ℝ) (γ₁ γ₃ : ℝ) :
    wR θ α γ₁ γ₃ = (1 + ‖γ₁‖ₑ + ‖γ₃‖ₑ) ^ θ := by
  simp [wR]

theorem wJ_optE (θ : ℝ) (α : Option Empty → ℝ) (γ : ℝ) :
    wJ θ α γ = (1 + ‖α none‖ₑ + ‖γ‖ₑ) ^ θ := by
  simp [wJ]; rfl

theorem one_add_rpow_le_self {θ : ℝ} (h1 : θ ≤ 1) (u : ℝ≥0∞) : (1 + u) ^ θ ≤ 1 + u :=
  (ENNReal.rpow_le_rpow_of_exponent_le le_self_add h1).trans_eq (ENNReal.rpow_one _)

/-- The sign bundle `εα₁` on `Option Empty`. -/
@[expose] def yE (ε : ℤ) : Option Empty → ℤ := fun _ => ε

theorem isBundle_yE {ε : ℤ} (hε : ε = 1 ∨ ε = -1) : IsBundle (yE ε) := fun _ => abs_sign_le hε

theorem bundle_yE (ε : ℤ) (α : Option Empty → ℝ) : bundle (yE ε) α = ε * α none := by
  rw [bundle_optE]; rfl

theorem abs_sign_mul {ε : ℤ} (hε : ε = 1 ∨ ε = -1) (x : ℝ) : |(ε : ℝ) * x| = |x| := by
  rcases hε with rfl | rfl <;> simp

theorem lintegral_indicator_sign {ε : ℤ} (hε : ε = 1 ∨ ε = -1) :
    ∫⁻ t : ℝ, (Icc (-1 : ℝ) 1).indicator (fun _ => (1 : ℝ≥0∞)) (ε * t) = 2 := by
  have h := lintegral_affine_one (sign_real hε) 0
    (f := (Icc (-1 : ℝ) 1).indicator (fun _ => (1 : ℝ≥0∞)))
  simp only [zero_add] at h
  rw [h, lintegral_indicator measurableSet_Icc, setLIntegral_const, Real.volume_Icc, one_mul]
  norm_num

end OneVar

section Pieces

variable {θ A : ℝ}

/-- `ρ/(πi)` with `ρ = ½ 1_{[-1,1]}`. -/
@[expose] noncomputable def rhoc (g : ℝ) : ℂ :=
  (Icc (-1 : ℝ) 1).indicator (fun _ => (1 / 2 : ℂ)) g * (π * I)⁻¹

theorem measurable_rhoc : Measurable rhoc :=
  (measurable_const.indicator measurableSet_Icc).mul measurable_const

theorem norm_pi_I_inv_le : ‖((π : ℂ) * I)⁻¹‖ ≤ 1 := by
  rw [norm_inv, norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos Real.pi_pos]
  exact inv_le_one_of_one_le₀ (by linarith [Real.two_le_pi])

theorem enorm_rhoc_le (g : ℝ) :
    ‖rhoc g‖ₑ ≤ (Icc (-1 : ℝ) 1).indicator (fun _ => (1 / 2 : ℝ≥0∞)) g := by
  unfold rhoc
  by_cases hg : g ∈ Icc (-1 : ℝ) 1
  · rw [Set.indicator_of_mem hg, Set.indicator_of_mem hg, enorm_mul]
    calc ‖(1 / 2 : ℂ)‖ₑ * ‖((π : ℂ) * I)⁻¹‖ₑ ≤ (1 / 2 : ℝ≥0∞) * 1 := by
          gcongr
          · rw [← ofReal_norm, show ‖(1 / 2 : ℂ)‖ = 1 / 2 by simp]
            rw [ENNReal.ofReal_div_of_pos (by norm_num)]; simp
          · rw [← ofReal_norm, ← ENNReal.ofReal_one]
            exact ENNReal.ofReal_le_ofReal norm_pi_I_inv_le
      _ = 1 / 2 := mul_one _
  · rw [Set.indicator_of_notMem hg, Set.indicator_of_notMem hg]; simp

theorem integrable_rhoc : Integrable rhoc := by
  have h : IntegrableOn (fun _ : ℝ => (1 / 2 : ℂ)) (Icc (-1 : ℝ) 1) :=
    integrableOn_const (by simp [Real.volume_Icc])
  exact (h.integrable_indicator measurableSet_Icc).mul_const _

theorem integral_rhoc : ∫ g, rhoc g = (π * I)⁻¹ := by
  unfold rhoc
  rw [MeasureTheory.integral_mul_const, integral_indicator measurableSet_Icc,
    setIntegral_const, Real.volume_real_Icc_of_le (by norm_num)]
  norm_num

theorem lintegral_rhoc_le : ∫⁻ g, ‖rhoc g‖ₑ ≤ 1 := by
  calc ∫⁻ g, ‖rhoc g‖ₑ ≤ ∫⁻ g, (Icc (-1 : ℝ) 1).indicator (fun _ => (1 / 2 : ℝ≥0∞)) g :=
        lintegral_mono enorm_rhoc_le
    _ = 1 := by
        rw [lintegral_indicator measurableSet_Icc, setLIntegral_const, Real.volume_Icc]
        norm_num
        exact ENNReal.inv_mul_cancel (by norm_num) (by norm_num)

end Pieces

section PieceLemmas

variable {θ A : ℝ}

theorem isFiniteMeasure_volume_unit : IsFiniteMeasure (volume : Measure Unit) := by
  rw [show (volume : Measure Unit) = Measure.dirac () from rfl]; infer_instance

attribute [local instance] isFiniteMeasure_volume_unit

theorem ind_le_one (x : ℝ) : (Icc (-1 : ℝ) 1).indicator (fun _ => (1 : ℝ≥0∞)) x ≤ 1 := by
  by_cases h : x ∈ Icc (-1 : ℝ) 1 <;> simp [h]

theorem lintegral_prodUnit (G : ℝ × Unit → ℝ≥0∞) : ∫⁻ z, G z = ∫⁻ g, G (g, ()) := by
  rw [Measure.volume_eq_prod, show (volume : Measure Unit) = Measure.dirac () from rfl,
    Measure.prod_dirac]
  exact lintegral_map_equiv G (MeasurableEquiv.prodPUnit (α := ℝ)).symm

theorem integral_prodUnit (f : ℝ × Unit → ℂ) : ∫ z, f z = ∫ g, f (g, ()) := by
  rw [Measure.volume_eq_prod, show (volume : Measure Unit) = Measure.dirac () from rfl,
    Measure.prod_dirac]
  exact integral_map_equiv (MeasurableEquiv.prodPUnit (α := ℝ)).symm f

theorem gev_zero_eq (N A : ℝ) : gev N A 0 = ENNReal.ofReal N := by simp [gev]

/-- **The piece `-J_{0;0,μ}`** (no variables). -/
theorem exists_piece_58_0 (h0 : 0 ≤ θ) (h1 : θ ≤ 1) (μ : ℝ) :
    ∃ S : JSym Empty, S.Bound θ A CM0 ∧ ∀ α t s, t ∈ Icc (0 : ℝ) 1 → s ∈ Icc (0 : ℝ) 1 →
      S.kernel α t s = -jker 0 0 μ t s := by
  obtain ⟨S, -, hS, hk⟩ := JSym.ofAny (ι := Empty) (y := 0) isBundle_zero
    (a := fun _ (_ : Unit) => (-1 : ℂ)) (SymReg.const (integrable_const _)
      stronglyMeasurable_const) (c := fun _ => ((0 : ℝ), μ)) measurable_const h0 h1
      (A := A) zero_le_one (fun k => by
        rw [lintegral_emptyFun, lintegral_unit, wJ_emptyFun,
          show (1 + ‖((0 : ℝ), μ).1‖ₑ) ^ θ = 1 by simp, one_mul]
        refine (dnorm_const_le k _ _ _).trans ?_
        split_ifs with hk
        · subst hk; simp [gev]
        · simp)
  refine ⟨S, by simpa using hS, fun α t s ht hs => ?_⟩
  rw [hk α t s ht hs, integral_unit, bundle_emptyFun]
  simp

/-- **Piece I of Lemma 5.8**: `∫ M(εα₁, q) J_{0;σ,μ-σ} dq`. -/
theorem exists_piece_58_M (h0 : 0 ≤ θ) (h1 : θ ≤ 1) (hA : A0 ≤ A) {ε : ℤ}
    (hε : ε = 1 ∨ ε = -1) (μ : ℝ) :
    ∃ S : JSym (Option Empty), S.Bound θ A (CM0 * (4 * (CkM * IM))) ∧ ∀ α t s,
      t ∈ Icc (0 : ℝ) 1 → s ∈ Icc (0 : ℝ) 1 →
      S.kernel α t s = ∫ q : ℝ × ℝ, kerM (ε * α none) q * jker 0 q.1 (μ - q.1) t s := by
  have hA0 : 0 ≤ A := A0_nonneg.trans hA
  have hC : 0 ≤ CkM * IM := mul_nonneg kerM_bound.1 IM_nonneg
  have hb := isBundle_yE hε
  have hd : ∀ k (α : Option Empty → ℝ) (q : ℝ × ℝ),
      dnorm k (fun α q => kerM (bundle (yE ε) α) q) α q ≤
        (Icc (-1 : ℝ) 1).indicator (fun _ => (1 : ℝ≥0∞)) (ε * α none) * gM k q :=
    fun k α q => by
      have := (dnorm_comp_bundle_le hb (F := kerM) contDiff_kerM k α q).trans
        (enorm_iteratedDeriv_kerM_le_ind k _ q)
      rwa [bundle_yE] at this
  have hreg : SymReg fun (α : Option Empty → ℝ) (q : ℝ × ℝ) => kerM (bundle (yE ε) α) q :=
    { smooth := fun q => (contDiff_kerM q).comp (contDiff_bundle (yE ε))
      meas := (measurable_kerM.comp ((((contDiff_bundle (yE ε)).continuous.measurable).comp
        measurable_fst).prodMk measurable_snd)).stronglyMeasurable
      dom := fun k => ne_top_of_le_ne_top
        (ne_top_of_le_ne_top (by simp [gev]) (lintegral_gM_le k))
        (lintegral_mono fun q => iSup_le fun α => (hd k α q).trans
          (mul_le_of_le_one_left bot_le (ind_le_one _))) }
  have hN : 0 ≤ 4 * (CkM * IM) := by positivity
  obtain ⟨S, -, hS, hk⟩ := JSym.ofAny (y := (0 : Option Empty → ℤ)) (θ := θ) (A := A)
    (N := 4 * (CkM * IM)) isBundle_zero hreg
    (c := fun q : ℝ × ℝ => (q.1, μ - q.1)) (by fun_prop) h0 h1 hN (fun k => by
      have hmq : Measurable fun q : ℝ × ℝ => (1 + ‖q.1‖ₑ) * gM k q :=
        (measurable_const.add measurable_fst.enorm).mul (measurable_gM k)
      calc ∫⁻ α, ∫⁻ q, wJ θ α (q.1, μ - q.1).1 *
            dnorm k (fun α q => kerM (bundle (yE ε) α) q) α q
          ≤ ∫⁻ α : Option Empty → ℝ, ∫⁻ q : ℝ × ℝ,
              2 * (Icc (-1 : ℝ) 1).indicator (fun _ => (1 : ℝ≥0∞)) (ε * α none) *
                ((1 + ‖q.1‖ₑ) * gM k q) := by
            refine lintegral_mono fun α => lintegral_mono fun q => ?_
            refine (mul_le_mul' le_rfl (hd k α q)).trans ?_
            by_cases hm : (ε : ℝ) * α none ∈ Icc (-1 : ℝ) 1
            · rw [Set.indicator_of_mem hm]
              have hα : ‖α none‖ₑ ≤ 1 := by
                rw [← ofReal_norm, Real.norm_eq_abs, ← abs_sign_mul hε, ← ENNReal.ofReal_one]
                exact ENNReal.ofReal_le_ofReal (abs_le.2 hm)
              rw [wJ_optE]
              calc (1 + ‖α none‖ₑ + ‖(q.1, μ - q.1).1‖ₑ) ^ θ * (1 * gM k q)
                  ≤ (1 + ‖α none‖ₑ + ‖q.1‖ₑ) * (1 * gM k q) := by
                    gcongr
                    rw [add_assoc]; exact one_add_rpow_le_self h1 _
                _ ≤ (2 * (1 + ‖q.1‖ₑ)) * (1 * gM k q) := by
                    gcongr
                    calc 1 + ‖α none‖ₑ + ‖q.1‖ₑ ≤ 1 + 1 + ‖q.1‖ₑ := by gcongr
                      _ ≤ 2 * (1 + ‖q.1‖ₑ) := by
                          rw [mul_add, mul_one, one_add_one_eq_two]
                          gcongr
                          exact le_mul_of_one_le_left bot_le one_le_two
                _ = _ := by ring
            · rw [Set.indicator_of_notMem hm]; simp
        _ = ∫⁻ α : Option Empty → ℝ, 2 * (Icc (-1 : ℝ) 1).indicator (fun _ => (1 : ℝ≥0∞))
              (ε * α none) * gev (CkM * IM) AkM k := by
            refine lintegral_congr fun α => ?_
            rw [lintegral_const_mul _ hmq, lintegral_gM_weight]
        _ = 2 * 2 * gev (CkM * IM) AkM k := by
            have hmi : Measurable fun α : Option Empty → ℝ =>
                (Icc (-1 : ℝ) 1).indicator (fun _ => (1 : ℝ≥0∞)) (ε * α none) :=
              (measurable_const.indicator measurableSet_Icc).comp
                (measurable_const.mul (measurable_pi_apply none))
            rw [lintegral_mul_const _ (hmi.const_mul 2), lintegral_const_mul _ hmi,
              lintegral_optE (G := fun t => (Icc (-1 : ℝ) 1).indicator (fun _ => (1 : ℝ≥0∞))
                (ε * t)), lintegral_indicator_sign hε]
        _ ≤ gev (4 * (CkM * IM)) A k := by
            rw [show (2 : ℝ≥0∞) * 2 = ENNReal.ofReal 4 by norm_num, gev_mul_const _ (by norm_num)]
            exact gev_mono le_rfl kerM_bound.2.1 (AkM_le_A0.trans hA) (by positivity) k)
  refine ⟨S, hS, fun α t s ht hs => ?_⟩
  rw [hk α t s ht hs]
  simp only [bundle_optE, yE, Pi.zero_apply, Int.cast_zero, zero_mul]

end PieceLemmas

end WaveTurbulence.ClassJR
