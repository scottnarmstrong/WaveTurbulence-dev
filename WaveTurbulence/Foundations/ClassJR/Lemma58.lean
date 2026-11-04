/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.ClassJR.InvBounds
public import WaveTurbulence.Foundations.ClassJR.Param

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

The pieces are parametric in `μ₁` (`JSymP ℝ`, `RSymP ℝ`): their symbols do not depend on `μ₁`, which
only enters the coefficient maps, so they are jointly measurable (`iker_comp_decompP`, consumed in
DH21 Proposition 5.1 where `μ₁` is a sum of integration variables).
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
theorem exists_piece_58_0 (h0 : 0 ≤ θ) (h1 : θ ≤ 1) :
    ∃ S : JSymP ℝ Empty, S.Bound θ A CM0 ∧ ∀ μ α t s, t ∈ Icc (0 : ℝ) 1 →
      s ∈ Icc (0 : ℝ) 1 → (S.get μ).kernel α t s = -jker 0 0 μ t s := by
  obtain ⟨S, -, hS, hk⟩ := JSymP.ofAny (P := ℝ) (ι := Empty) (y := 0) isBundle_zero
    (a := fun _ _ (_ : Unit) => (-1 : ℂ)) (fun _ => SymReg.const (integrable_const _)
      stronglyMeasurable_const) stronglyMeasurable_const (c := fun μ _ => ((0 : ℝ), μ))
      (show Measurable fun x : ℝ × Unit => ((0 : ℝ), x.1) from
        measurable_const.prodMk measurable_fst) h0 h1
      (A := A) zero_le_one (fun μ k => by
        rw [lintegral_emptyFun, lintegral_unit, wJ_emptyFun,
          show (1 + ‖((0 : ℝ), μ).1‖ₑ) ^ θ = 1 by simp, one_mul]
        refine (dnorm_const_le k _ _ _).trans ?_
        split_ifs with hk
        · subst hk; simp [gev]
        · simp)
  refine ⟨S, by simpa using hS, fun μ α t s ht hs => ?_⟩
  rw [hk μ α t s ht hs, integral_unit, bundle_emptyFun]
  simp

/-- **Piece I of Lemma 5.8**: `∫ M(εα₁, q) J_{0;σ,μ-σ} dq`. -/
theorem exists_piece_58_M (h0 : 0 ≤ θ) (h1 : θ ≤ 1) (hA : A0 ≤ A) {ε : ℤ}
    (hε : ε = 1 ∨ ε = -1) :
    ∃ S : JSymP ℝ (Option Empty), S.Bound θ A (CM0 * (4 * (CkM * IM))) ∧ ∀ μ α t s,
      t ∈ Icc (0 : ℝ) 1 → s ∈ Icc (0 : ℝ) 1 →
      (S.get μ).kernel α t s = ∫ q : ℝ × ℝ, kerM (ε * α none) q * jker 0 q.1 (μ - q.1) t s := by
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
  have hm : StronglyMeasurable fun x : ℝ × ((Option Empty → ℝ) × (ℝ × ℝ)) =>
      kerM (bundle (yE ε) x.2.1) x.2.2 :=
    hreg.meas.comp_measurable
      (measurable_snd : Measurable (Prod.snd : ℝ × ((Option Empty → ℝ) × (ℝ × ℝ)) → _))
  obtain ⟨S, -, hS, hk⟩ := JSymP.ofAny (P := ℝ) (y := (0 : Option Empty → ℤ)) (θ := θ) (A := A)
    (N := 4 * (CkM * IM)) isBundle_zero (a := fun _ α q => kerM (bundle (yE ε) α) q)
    (fun _ => hreg) hm (c := fun μ (q : ℝ × ℝ) => (q.1, μ - q.1))
    (show Measurable fun x : ℝ × (ℝ × ℝ) => (x.2.1, x.1 - x.2.1) from
      (measurable_fst.comp measurable_snd).prodMk
        (measurable_fst.sub (measurable_fst.comp measurable_snd))) h0 h1 hN (fun μ k => by
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
  refine ⟨S, hS, fun μ α t s ht hs => ?_⟩
  rw [hk μ α t s ht hs]
  simp only [bundle_optE, yE, Pi.zero_apply, Int.cast_zero, zero_mul]

end PieceLemmas

section PieceLemmas2

variable {θ A : ℝ}

attribute [local instance] isFiniteMeasure_volume_unit

/-- **The class `R` part of piece III**: `∫ ρ(g)/(πi) χ_∞(εα₁+g)/(εα₁+g) J_{εα₁;0,μ} dg`. -/
theorem exists_piece_58_R (h0 : 0 ≤ θ) (h1 : θ ≤ 1) {ε : ℤ} (hε : ε = 1 ∨ ε = -1) :
    ∃ S : RSymP ℝ Empty, S.Bound θ A (CM0 * 2) ∧ ∀ μ α t s, t ∈ Icc (0 : ℝ) 1 →
      s ∈ Icc (0 : ℝ) 1 → (S.get μ).kernel α t s =
        ∫ g, rhoc g * ((chiInvR (ε * α none + g) : ℂ) * jker (ε * α none) 0 μ t s) := by
  have hint : Integrable fun z : ℝ × Unit => rhoc z.1 := by
    rw [Measure.volume_eq_prod]; exact integrable_rhoc.comp_fst _
  obtain ⟨S, -, -, -, hS, hk⟩ := RSymP.ofAny (P := ℝ) (ι := Empty) (Q := Unit) (θ := θ)
    (A := A) (N := 2) hε (y₁ := 0) (y₂ := 0) isBundle_zero isBundle_zero
    (a := fun _ _ (z : ℝ × Unit) => rhoc z.1)
    (fun _ => SymReg.const hint (measurable_rhoc.comp measurable_fst).stronglyMeasurable)
    ((measurable_rhoc.comp (measurable_fst.comp (measurable_snd.comp
      measurable_snd))).stronglyMeasurable)
    (c := fun μ _ => ((0 : ℝ), μ))
    (show Measurable fun x : ℝ × (ℝ × Unit) => ((0 : ℝ), x.1) from
      measurable_const.prodMk measurable_fst) h0 h1 zero_le_two (fun μ k => by
      rw [lintegral_emptyFun, lintegral_prodUnit]
      by_cases hk : k = 0
      · subst hk
        calc ∫⁻ g : ℝ, wR θ isEmptyElim ((0 : ℝ), μ).1 (g, ()).1 *
              dnorm 0 (fun _ (z : ℝ × Unit) => rhoc z.1) isEmptyElim (g, ())
            ≤ ∫⁻ g : ℝ, 2 * ‖rhoc g‖ₑ := by
              refine lintegral_mono fun g => ?_
              refine (mul_le_mul' le_rfl (dnorm_const_le 0 _ _ _)).trans ?_
              simp only [ite_true, wR_emptyFun]
              by_cases hg : g ∈ Icc (-1 : ℝ) 1
              · gcongr
                calc (1 + ‖((0 : ℝ), μ).1‖ₑ + ‖(g, ()).1‖ₑ) ^ θ
                    ≤ 1 + ‖((0 : ℝ), μ).1‖ₑ + ‖(g, ()).1‖ₑ := by
                      rw [add_assoc]; exact one_add_rpow_le_self h1 _
                  _ ≤ 2 := by
                      have : ‖g‖ₑ ≤ 1 := by
                        rw [← ofReal_norm, Real.norm_eq_abs, ← ENNReal.ofReal_one]
                        exact ENNReal.ofReal_le_ofReal (abs_le.2 hg)
                      simp only [enorm_zero, add_zero]
                      calc 1 + ‖g‖ₑ ≤ 1 + 1 := by gcongr
                        _ = 2 := one_add_one_eq_two
              · rw [show rhoc g = 0 by simp [rhoc, Set.indicator_of_notMem hg]]; simp
          _ = 2 * ∫⁻ g : ℝ, ‖rhoc g‖ₑ := lintegral_const_mul _ measurable_rhoc.enorm
          _ ≤ 2 * 1 := by gcongr; exact lintegral_rhoc_le
          _ = gev 2 A 0 := by rw [gev_zero_eq]; simp
      · calc ∫⁻ g : ℝ, wR θ isEmptyElim ((0 : ℝ), μ).1 (g, ()).1 *
              dnorm k (fun _ (z : ℝ × Unit) => rhoc z.1) isEmptyElim (g, ())
            ≤ ∫⁻ g : ℝ, 0 := by
              refine lintegral_mono fun g => ?_
              refine (mul_le_mul' le_rfl (dnorm_const_le k _ _ _)).trans ?_
              simp [hk]
          _ ≤ gev 2 A k := by simp)
  refine ⟨S, hS, fun μ α t s ht hs => ?_⟩
  rw [hk μ α t s ht hs, integral_prodUnit]
  simp only [rker, bundle_emptyFun, zero_add]

/-- The averaging error `χ_∞(x)/x - χ_∞(x+g)/(x+g)`. -/
@[expose] noncomputable def errE (x g : ℝ) : ℝ := chiInvR x - chiInvR (x + g)

theorem contDiff_errE (g : ℝ) : ContDiff ℝ ∞ fun x => errE x g :=
  contDiff_chiInvR.sub (contDiff_chiInvR.comp (contDiff_id.add contDiff_const))

theorem iteratedDeriv_errE (k : ℕ) (x g : ℝ) :
    iteratedDeriv k (fun x => errE x g) x =
      iteratedDeriv k chiInvR x - iteratedDeriv k chiInvR (x + g) := by
  have h1 : ContDiffAt ℝ k chiInvR x :=
    contDiff_chiInvR.contDiffAt.of_le (by exact_mod_cast le_top)
  have h2 : ContDiffAt ℝ k (fun x => chiInvR (x + g)) x :=
    (contDiff_chiInvR.comp (contDiff_id.add contDiff_const)).contDiffAt.of_le
      (by exact_mod_cast le_top)
  rw [show (fun x => errE x g) = chiInvR - fun x => chiInvR (x + g) from rfl,
    iteratedDeriv_sub h1 h2, iteratedDeriv_comp_add_const]

/-- The symbol of the error piece. -/
@[expose] noncomputable def FE (x g : ℝ) : ℂ := rhoc g * ((errE x g : ℝ) : ℂ)

theorem contDiff_FE (g : ℝ) : ContDiff ℝ ∞ fun x => FE x g :=
  contDiff_const.mul (Complex.ofRealCLM.contDiff.comp (contDiff_errE g))

theorem enorm_iteratedDeriv_FE (k : ℕ) (x g : ℝ) :
    ‖iteratedDeriv k (fun x => FE x g) x‖ₑ =
      ‖rhoc g‖ₑ * ENNReal.ofReal ‖iteratedDeriv k chiInvR x - iteratedDeriv k chiInvR (x + g)‖ := by
  have e : (fun x => FE x g) = fun x => rhoc g • ((errE x g : ℝ) : ℂ) := rfl
  rw [e, iteratedDeriv_fun_const_smul_field, enorm_smul, ← ofReal_norm (iteratedDeriv _ _ _),
    norm_iteratedDeriv_ofReal (contDiff_errE g), iteratedDeriv_errE]

theorem exists_errE_bound (k : ℕ) (x g : ℝ) :
    ENNReal.ofReal ‖iteratedDeriv k chiInvR x - iteratedDeriv k chiInvR (x + g)‖ ≤
      ENNReal.ofReal (2 * CPhi * Achi ^ k * ((2 * k).factorial : ℝ)) := by
  refine ENNReal.ofReal_le_ofReal ((norm_sub_le _ _).trans ?_)
  have := norm_iteratedDeriv_chiInvR_le k x
  have := norm_iteratedDeriv_chiInvR_le k (x + g)
  linarith

theorem rpow_mul_inv_sq {θ : ℝ} (t : ℝ) :
    (1 + |t|) ^ θ * ((1 + |t|) ^ 2)⁻¹ = (1 + |t|) ^ (-(2 - θ)) := by
  have hp : 0 < 1 + |t| := by positivity
  rw [show -(2 - θ) = θ - 2 by ring, Real.rpow_sub hp, Real.rpow_two, div_eq_mul_inv]

/-- **The class `J` error of piece III.** -/
theorem exists_piece_58_E (h0 : 0 ≤ θ) (h1 : θ < 1) (hA : A0 ≤ A) {ε : ℤ}
    (hε : ε = 1 ∨ ε = -1) :
    ∃ S : JSymP ℝ (Option Empty), S.Bound θ A (CM0 * ((32 * CPhi + 8) * Ir (2 - θ))) ∧
      ∀ μ α t s, t ∈ Icc (0 : ℝ) 1 → s ∈ Icc (0 : ℝ) 1 → (S.get μ).kernel α t s =
        ∫ g, rhoc g * (((chiInvR (ε * α none) : ℂ) - chiInvR (ε * α none + g)) *
          jker (ε * α none) 0 μ t s) := by
  have hb := isBundle_yE hε
  have hCP := CPhi_nonneg
  have hI : 0 ≤ Ir (2 - θ) := ENNReal.toReal_nonneg
  have hd : ∀ k (α : Option Empty → ℝ) (g : ℝ),
      dnorm k (fun α g => FE (bundle (yE ε) α) g) α g ≤ ‖rhoc g‖ₑ *
        ENNReal.ofReal ‖iteratedDeriv k chiInvR (ε * α none) -
          iteratedDeriv k chiInvR (ε * α none + g)‖ := fun k α g => by
    have := dnorm_comp_bundle_le hb (F := FE) contDiff_FE k α g
    rwa [enorm_iteratedDeriv_FE, bundle_yE] at this
  have hcb : Continuous (bundle (yE ε)) := (contDiff_bundle _).continuous
  have hce : Continuous fun p : (Option Empty → ℝ) × ℝ => errE (bundle (yE ε) p.1) p.2 :=
    (contDiff_chiInvR.continuous.comp (hcb.comp continuous_fst)).sub
      (contDiff_chiInvR.continuous.comp ((hcb.comp continuous_fst).add continuous_snd))
  have hreg : SymReg fun (α : Option Empty → ℝ) (g : ℝ) => FE (bundle (yE ε) α) g :=
    { smooth := fun g => (contDiff_FE g).comp (contDiff_bundle (yE ε))
      meas := ((measurable_rhoc.comp measurable_snd).mul
        (Complex.continuous_ofReal.comp hce).measurable).stronglyMeasurable
      dom := fun k => by
        refine ne_top_of_le_ne_top (b := (∫⁻ g, ‖rhoc g‖ₑ) *
          ENNReal.ofReal (2 * CPhi * Achi ^ k * ((2 * k).factorial : ℝ))) ?_ ?_
        · exact ENNReal.mul_ne_top (ne_top_of_le_ne_top ENNReal.one_ne_top lintegral_rhoc_le)
            ENNReal.ofReal_ne_top
        · rw [← lintegral_mul_const _ measurable_rhoc.enorm]
          exact lintegral_mono fun g => iSup_le fun α => (hd k α g).trans
            (mul_le_mul' le_rfl (exists_errE_bound k _ _)) }
  have hN : 0 ≤ (32 * CPhi + 8) * Ir (2 - θ) := by positivity
  have hm : StronglyMeasurable fun x : ℝ × ((Option Empty → ℝ) × ℝ) =>
      FE (bundle (yE ε) x.2.1) x.2.2 :=
    hreg.meas.comp_measurable
      (measurable_snd : Measurable (Prod.snd : ℝ × ((Option Empty → ℝ) × ℝ) → _))
  obtain ⟨S, -, hS, hk⟩ := JSymP.ofAny (P := ℝ) (y := yE ε) (θ := θ) (A := A)
    (N := (32 * CPhi + 8) * Ir (2 - θ)) hb (a := fun _ α g => FE (bundle (yE ε) α) g)
    (fun _ => hreg) hm (c := fun μ (_ : ℝ) => ((0 : ℝ), μ))
    (show Measurable fun x : ℝ × ℝ => ((0 : ℝ), x.1) from
      measurable_const.prodMk measurable_fst) h0 h1.le hN (fun μ k => by
      have hK0 : 0 ≤ (32 * CPhi + 8) * (Achi ^ k * ((2 * k).factorial : ℝ)) :=
        mul_nonneg (by linarith) (mul_nonneg (pow_nonneg Achi_nonneg k) (by positivity))
      set C := ENNReal.ofReal ((32 * CPhi + 8) * (Achi ^ k * ((2 * k).factorial : ℝ)))
      have hw : Measurable fun α : Option Empty → ℝ =>
          ENNReal.ofReal ((1 + |α none|) ^ (-(2 - θ))) := by fun_prop
      calc ∫⁻ α, ∫⁻ g, wJ θ α ((fun μ (_ : ℝ) => ((0 : ℝ), μ)) μ g).1 *
            dnorm k (fun α g => FE (bundle (yE ε) α) g) α g
          ≤ ∫⁻ α : Option Empty → ℝ, ∫⁻ g : ℝ, ‖rhoc g‖ₑ *
              (C * ENNReal.ofReal ((1 + |α none|) ^ (-(2 - θ)))) := by
            refine lintegral_mono fun α => lintegral_mono fun g => ?_
            refine (mul_le_mul' le_rfl (hd k α g)).trans ?_
            rw [wJ_optE, enorm_zero, add_zero, one_add_enorm_eq,
              ENNReal.ofReal_rpow_of_nonneg (by positivity) h0]
            by_cases hg : g ∈ Icc (-1 : ℝ) 1
            · have hdiff := norm_chiInvR_diff_le k (ε * α none) g (abs_le.2 hg)
              rw [abs_sign_mul hε] at hdiff
              calc ENNReal.ofReal ((1 + |α none|) ^ θ) * (‖rhoc g‖ₑ * ENNReal.ofReal
                    ‖iteratedDeriv k chiInvR (ε * α none) -
                      iteratedDeriv k chiInvR (ε * α none + g)‖)
                  ≤ ENNReal.ofReal ((1 + |α none|) ^ θ) * (‖rhoc g‖ₑ * ENNReal.ofReal
                    ((32 * CPhi + 8) * (Achi ^ k * ((2 * k).factorial : ℝ)) *
                      ((1 + |α none|) ^ 2)⁻¹)) := by
                    gcongr
                _ = ‖rhoc g‖ₑ * (C * ENNReal.ofReal ((1 + |α none|) ^ (-(2 - θ)))) := by
                    rw [← rpow_mul_inv_sq, ENNReal.ofReal_mul hK0,
                      ENNReal.ofReal_mul (show 0 ≤ (1 + |α none|) ^ θ by positivity),
                      show C = ENNReal.ofReal ((32 * CPhi + 8) *
                        (Achi ^ k * ((2 * k).factorial : ℝ))) from rfl]
                    ring
            · rw [show rhoc g = 0 by simp [rhoc, Set.indicator_of_notMem hg]]; simp
        _ = ∫⁻ α : Option Empty → ℝ, (∫⁻ g : ℝ, ‖rhoc g‖ₑ) *
              (C * ENNReal.ofReal ((1 + |α none|) ^ (-(2 - θ)))) :=
            lintegral_congr fun α => lintegral_mul_const _ measurable_rhoc.enorm
        _ ≤ ∫⁻ α : Option Empty → ℝ, C * ENNReal.ofReal ((1 + |α none|) ^ (-(2 - θ))) :=
            lintegral_mono fun α => (mul_le_mul' lintegral_rhoc_le le_rfl).trans_eq (one_mul _)
        _ = C * ENNReal.ofReal (Ir (2 - θ)) := by
            rw [lintegral_const_mul _ hw,
              lintegral_optE (G := fun t => ENNReal.ofReal ((1 + |t|) ^ (-(2 - θ)))),
              lintegral_Ir_eq (by linarith)]
        _ = gev ((32 * CPhi + 8) * Ir (2 - θ)) Achi k := by
            rw [← ENNReal.ofReal_mul hK0, gev]
            congr 1; ring
        _ ≤ gev ((32 * CPhi + 8) * Ir (2 - θ)) A k :=
            gev_mono le_rfl Achi_nonneg (Achi_le_A0.trans hA) hN k)
  refine ⟨S, hS, fun μ α t s ht hs => ?_⟩
  rw [hk μ α t s ht hs]
  simp only [FE, errE, bundle_yE]
  push_cast
  refine integral_congr_ae (Eventually.of_forall fun g => ?_)
  ring

end PieceLemmas2

section Assembly

variable {θ A : ℝ}

theorem iker_eq_jker (β : ℝ) : iker β = jker 0 0 β := by
  funext t s; simp [iker, jker]

/-- `Φ(εx) = χ_∞(x)/(επix)`, the factor of DH21 Lemma 5.8. -/
theorem phiR_sign {ε : ℤ} (hε : ε = 1 ∨ ε = -1) (x : ℝ) :
    phiR (ε * x) = (chiInfinity x : ℂ) / (ε * π * I * x) := by
  have hc : chiInfinity (ε * x) = chiInfinity x := by
    rcases hε with rfl | rfl
    · simp
    · simp [chiInfinity, chi0_even]
  rw [phiR, chiInvR, hc, Complex.ofReal_div, div_div]
  congr 1
  push_cast
  ring

theorem phiR_jker_eq (x μ t s : ℝ) :
    phiR x * jker 0 x (μ - x) t s =
      (∫ g, rhoc g * (((chiInvR x : ℂ) - chiInvR (x + g)) * jker x 0 μ t s)) +
        ∫ g, rhoc g * ((chiInvR (x + g) : ℂ) * jker x 0 μ t s) := by
  have hJ : jker 0 x (μ - x) t s = jker x 0 μ t s := by
    simp only [jker]; congr 1; push_cast; ring
  have hc : Continuous fun g : ℝ => (chiInvR (x + g) : ℂ) :=
    contDiff_chiInvRc.continuous.comp (continuous_const.add continuous_id)
  have hi1 : Integrable fun g => rhoc g *
      (((chiInvR x : ℂ) - chiInvR (x + g)) * jker x 0 μ t s) := by
    refine (integrable_rhoc.norm.mul_const (2 * CPhi)).mono'
      (integrable_rhoc.aestronglyMeasurable.mul
        ((continuous_const.sub hc).mul continuous_const).aestronglyMeasurable)
      (Eventually.of_forall fun g => ?_)
    rw [norm_mul, norm_mul, norm_jker, mul_one]
    refine mul_le_mul_of_nonneg_left ((norm_sub_le _ _).trans ?_) (norm_nonneg _)
    linarith [norm_chiInvR_le x, norm_chiInvR_le (x + g)]
  have hi2 : Integrable fun g => rhoc g * ((chiInvR (x + g) : ℂ) * jker x 0 μ t s) := by
    refine (integrable_rhoc.norm.mul_const CPhi).mono'
      (integrable_rhoc.aestronglyMeasurable.mul (hc.mul continuous_const).aestronglyMeasurable)
      (Eventually.of_forall fun g => ?_)
    rw [norm_mul, norm_mul, norm_jker, mul_one]
    exact mul_le_mul_of_nonneg_left (norm_chiInvR_le _) (norm_nonneg _)
  rw [← integral_add hi1 hi2]
  have e : ∀ g, rhoc g * (((chiInvR x : ℂ) - chiInvR (x + g)) * jker x 0 μ t s) +
      rhoc g * ((chiInvR (x + g) : ℂ) * jker x 0 μ t s) =
        rhoc g * ((chiInvR x : ℂ) * jker x 0 μ t s) := fun g => by ring
  simp_rw [e]
  rw [MeasureTheory.integral_mul_const, integral_rhoc, phiR, hJ]
  ring

/-- The class `J` constant of Lemma 5.8. -/
@[expose] noncomputable def C58J (θ : ℝ) : ℝ :=
  CM0 * (4 * (CkM * IM)) + CM0 * ((32 * CPhi + 8) * Ir (2 - θ))

/-- **DH21 Lemma 5.8 with the parameter `μ₁`** (L1086–L1106): `I_{εα₁} I_{μ₁-εα₁} =
Φ(εα₁) 𝒥_{α[ ],μ₁} + 𝒥_{α₁,μ₁} + ℛ_{α₁,μ₁}` on the triangle, where `Φ(εα₁) = χ_∞(α₁)/(επiα₁)`
(`phiR_sign`), `𝒥_{α[ ]}` has no variables, `𝒥_{α₁}` has the variable `α₁ = α none` and `ℛ_{α₁}`
has the special variable `α₁`; the three operators are parametric (jointly measurable) in `μ₁` with
norms bounded uniformly in `μ₁` (`0 ≤ θ < 1`, `A ≥ A0`). Explicitly `𝒥_{α[ ],μ₁} = -I_{μ₁}` on the
triangle (DH21 term II is `-Φ(εα₁) J_{0;0,μ₁}`). -/
theorem iker_comp_decompP (h0 : 0 ≤ θ) (h1 : θ < 1) (hA : A0 ≤ A) {ε : ℤ}
    (hε : ε = 1 ∨ ε = -1) :
    ∃ (T₀ : ℝ → (Empty → ℝ) → ℝ → ℝ → ℂ) (TJ TR : ℝ → (Option Empty → ℝ) → ℝ → ℝ → ℂ),
      ClassJP θ A CM0 T₀ ∧ ClassJP θ A (C58J θ) TJ ∧ ClassRP θ A (CM0 * 2) TR ∧
      (∀ (μ : ℝ) (α : Empty → ℝ), KEqOn (T₀ μ α) fun t s => -iker μ t s) ∧
      ∀ (μ : ℝ) (α : Option Empty → ℝ),
        KEqOn (kcomp (iker (ε * α none)) (iker (μ - ε * α none)))
          fun t s => phiR (ε * α none) * T₀ μ isEmptyElim t s + TJ μ α t s + TR μ α t s := by
  obtain ⟨S0, hS0, hk0⟩ := exists_piece_58_0 (A := A) h0 h1.le
  obtain ⟨SM, hSM, hkM⟩ := exists_piece_58_M h0 h1.le hA hε
  obtain ⟨SR, hSR, hkR⟩ := exists_piece_58_R (A := A) h0 h1.le hε
  obtain ⟨SE, hSE, hkE⟩ := exists_piece_58_E h0 h1 hA hε
  refine ⟨fun μ => (S0.get μ).kernel,
    fun μ α t s => (SM.get μ).kernel α t s + (SE.get μ).kernel α t s,
    fun μ => (SR.get μ).kernel,
    ⟨1, ![S0], ![CM0], fun i => by fin_cases i; exact hS0, by simp,
      fun μ α t s _ _ _ => by simp⟩,
    ⟨2, ![SM, SE], ![CM0 * (4 * (CkM * IM)), CM0 * ((32 * CPhi + 8) * Ir (2 - θ))],
      fun i => by fin_cases i; exacts [hSM, hSE], by simp [C58J, Fin.sum_univ_two],
      fun μ α t s _ _ _ => by simp [Fin.sum_univ_two]⟩,
    ⟨1, ![SR], ![CM0 * 2], fun i => by fin_cases i; exact hSR, by simp,
      fun μ α t s _ _ _ => by simp⟩, fun μ α t s hs0 hst ht1 => ?_, ?_⟩
  · rw [hk0 μ α t s ⟨hs0.trans hst, ht1⟩ ⟨hs0, hst.trans ht1⟩, iker_eq_jker]
  intro μ α t s hs0 hst ht1
  have ht : t ∈ Icc (0 : ℝ) 1 := ⟨hs0.trans hst, ht1⟩
  have hs : s ∈ Icc (0 : ℝ) 1 := ⟨hs0, hst.trans ht1⟩
  rw [iker_eq_jker, iker_eq_jker, kcomp_jker_split _ _ _ _ _ _ (by linarith) (by linarith)]
  beta_reduce
  rw [hk0 μ _ t s ht hs, hkM μ α t s ht hs, hkE μ α t s ht hs, hkR μ α t s ht hs]
  simp only [sub_self, zero_add, add_zero, add_sub_cancel]
  rw [phiR_jker_eq]
  ring

/-- **DH21 Lemma 5.8** at a fixed `μ₁` (the specialization of `iker_comp_decompP`). -/
theorem iker_comp_decomp (h0 : 0 ≤ θ) (h1 : θ < 1) (hA : A0 ≤ A) {ε : ℤ}
    (hε : ε = 1 ∨ ε = -1) (μ : ℝ) :
    ∃ (T₀ : (Empty → ℝ) → ℝ → ℝ → ℂ) (TJ TR : (Option Empty → ℝ) → ℝ → ℝ → ℂ),
      ClassJ θ A CM0 T₀ ∧ ClassJ θ A (C58J θ) TJ ∧ ClassR θ A (CM0 * 2) TR ∧
      ∀ α : Option Empty → ℝ, KEqOn (kcomp (iker (ε * α none)) (iker (μ - ε * α none)))
        fun t s => phiR (ε * α none) * T₀ isEmptyElim t s + TJ α t s + TR α t s := by
  obtain ⟨T₀, TJ, TR, h₀, hJ, hR, -, he⟩ := iker_comp_decompP h0 h1 hA hε
  exact ⟨T₀ μ, TJ μ, TR μ, h₀.classJ μ, hJ.classJ μ, hR.classR μ, he μ⟩

end Assembly

end WaveTurbulence.ClassJR
