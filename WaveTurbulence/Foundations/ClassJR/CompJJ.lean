/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.ClassJR.CompJJSetup

/-!
# DH21 Lemma 5.3: the composition of two class `J` operators

DH21 Lemma 5.3 (L966–L1003): `𝒥^{(1)} 𝒥^{(2)}` is of class `J` and
`‖𝒥^{(1)} 𝒥^{(2)}‖ ≤ C ‖𝒥^{(1)}‖ ‖𝒥^{(2)}‖`.

For basic operators the composition kernel splits (`kcomp_jker_split`) into the `χ₀` part
(`J'`, DH21 L976–L991) and the two `χ_∞` parts (`J''`, (formula1)–(formula2), L997–L1003). Each part
is a generalized representation `∫ a(α, z) J_{ℓ; γ'(z)} dz` with a product symbol
`a = m^{(1)} m^{(2)} K` (`Triple.lean`), converted to a basic class `J` symbol by `JSym.ofGenE`.

The variables of the composition are `α ∈ ι₁ ⊕ ι₂ → ℝ` (DH21: "the variables `α_j` involved in
different operators are different").
-/

public section

open MeasureTheory Set Filter Finset Complex
open scoped ContDiff ENNReal Real

namespace WaveTurbulence.ClassJR

open WaveTurbulence.Fourier

section Constants

/-- The constants of the `χ₀` kernel (`exists_kerM_bound`). -/
@[expose] noncomputable def CkM : ℝ := exists_kerM_bound.choose

/-- The Gevrey radius of the `χ₀` kernel. -/
@[expose] noncomputable def AkM : ℝ := exists_kerM_bound.choose_spec.choose

theorem kerM_bound : 0 ≤ CkM ∧ 0 ≤ AkM ∧ ∀ (c : ℕ) (x : ℝ) (q : ℝ × ℝ),
    ‖iteratedDeriv c (fun x => kerM x q) x‖ ≤
      (Icc (0 : ℝ) 1).indicator (fun _ => (1 : ℝ)) q.2 *
        (CkM * AkM ^ c * (Nat.factorial (2 * c) : ℝ)) / (1 + |q.1|) ^ 3 :=
  exists_kerM_bound.choose_spec.choose_spec

/-- The constant of `Φ`. -/
@[expose] noncomputable def CPhi : ℝ := 12 * (1 + Real.exp 4)

theorem CPhi_nonneg : 0 ≤ CPhi := by unfold CPhi; positivity

/-- The Gevrey radius `A₀` above which the class `J`/`R` calculus closes. -/
@[expose] noncomputable def A0 : ℝ := max Achi AkM

theorem Achi_le_A0 : Achi ≤ A0 := le_max_left _ _
theorem AkM_le_A0 : AkM ≤ A0 := le_max_right _ _
theorem A0_nonneg : 0 ≤ A0 := Achi_nonneg.trans Achi_le_A0

/-- `∫ (1 + |σ|)^{-2} dσ` (finite). -/
@[expose] noncomputable def IM : ℝ :=
  (∫⁻ σ : ℝ, ENNReal.ofReal (1 / (1 + |σ|) ^ 2)).toReal

theorem lintegral_decay2_ne_top : ∫⁻ σ : ℝ, ENNReal.ofReal (1 / (1 + |σ|) ^ 2) ≠ ⊤ := by
  have h := integrable_one_add_norm (E := ℝ) (μ := volume) (r := 2) (by norm_num)
  rw [← lt_top_iff_ne_top]
  refine lt_of_le_of_lt (le_of_eq ?_) h.2
  refine lintegral_congr fun σ => ?_
  have e : (1 + ‖σ‖) ^ (-2 : ℝ) = 1 / (1 + |σ|) ^ 2 := by
    rw [Real.norm_eq_abs, Real.rpow_neg (by positivity),
      show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast, one_div]
  simp only
  rw [e, ← ofReal_norm, Real.norm_of_nonneg (by positivity)]

theorem lintegral_decay2_eq : ∫⁻ σ : ℝ, ENNReal.ofReal (1 / (1 + |σ|) ^ 2) = ENNReal.ofReal IM :=
  (ENNReal.ofReal_toReal lintegral_decay2_ne_top).symm

theorem IM_nonneg : 0 ≤ IM := ENNReal.toReal_nonneg

end Constants

section Phi

theorem contDiff_phiR : ContDiff ℝ ∞ phiR := by
  unfold phiR
  exact (Complex.ofRealCLM.contDiff.comp contDiff_chiInvR).div_const _

theorem phiR_gevrey (c : ℕ) (x : ℝ) :
    (1 + |x|) * ‖iteratedDeriv c phiR x‖ ≤ CPhi * Achi ^ c * (Nat.factorial (2 * c) : ℝ) := by
  have h : phiR = ((π : ℂ) * I)⁻¹ • (Complex.ofRealCLM ∘ chiInvR) := by
    funext x; simp [phiR, div_eq_inv_mul]
  have hc : ContDiff ℝ ∞ (Complex.ofRealCLM ∘ chiInvR) :=
    Complex.ofRealCLM.contDiff.comp contDiff_chiInvR
  rw [← norm_iteratedFDeriv_eq_norm_iteratedDeriv, h,
    iteratedFDeriv_const_smul_apply (hc.contDiffAt.of_le (by exact_mod_cast le_top)), norm_smul,
    norm_iteratedFDeriv_eq_norm_iteratedDeriv]
  have h1 : ‖((π : ℂ) * I)⁻¹‖ ≤ 1 := by
    rw [norm_inv, norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos Real.pi_pos]
    exact inv_le_one_of_one_le₀ (by linarith [Real.two_le_pi])
  have h2 : ‖iteratedDeriv c (Complex.ofRealCLM ∘ chiInvR) x‖ = ‖iteratedDeriv c chiInvR x‖ :=
    norm_iteratedDeriv_ofReal contDiff_chiInvR c x
  rw [h2]
  calc (1 + |x|) * (‖((π : ℂ) * I)⁻¹‖ * ‖iteratedDeriv c chiInvR x‖)
      ≤ (1 + |x|) * (1 * ‖iteratedDeriv c chiInvR x‖) := by gcongr
    _ = (1 + |x|) * ‖iteratedDeriv c chiInvR x‖ := by ring
    _ ≤ _ := chiInvR_gevrey c x

theorem norm_iteratedDeriv_phiR_le (c : ℕ) (x : ℝ) :
    ‖iteratedDeriv c phiR x‖ ≤ CPhi * Achi ^ c * (Nat.factorial (2 * c) : ℝ) :=
  le_trans (le_mul_of_one_le_left (norm_nonneg _) (by linarith [abs_nonneg x])) (phiR_gevrey c x)

end Phi

section Couplings

/-- The `χ₀`-kernel bound `1_{[0,1]}(τ) C A^c (2c)! (1+|σ|)^{-3}` in `ℝ≥0∞`. -/
@[expose] noncomputable def gM (c : ℕ) (q : ℝ × ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal ((Icc (0 : ℝ) 1).indicator (fun _ => (1 : ℝ)) q.2 *
    (CkM * AkM ^ c * (Nat.factorial (2 * c) : ℝ)) / (1 + |q.1|) ^ 3)

theorem measurable_gM (c : ℕ) : Measurable (gM c) := by
  unfold gM
  refine ENNReal.measurable_ofReal.comp (Measurable.div ?_ (by fun_prop))
  exact ((measurable_const.indicator measurableSet_Icc).comp measurable_snd).mul measurable_const

theorem enorm_iteratedDeriv_kerM_le (c : ℕ) (x : ℝ) (q : ℝ × ℝ) :
    ‖iteratedDeriv c (fun x => kerM x q) x‖ₑ ≤ gM c q := by
  rw [← ofReal_norm]
  exact ENNReal.ofReal_le_ofReal (kerM_bound.2.2 c x q)

theorem one_add_mul_gM (c : ℕ) (q : ℝ × ℝ) :
    (1 + ‖q.1‖ₑ) * gM c q = ENNReal.ofReal (CkM * AkM ^ c * (Nat.factorial (2 * c) : ℝ)) *
      (ENNReal.ofReal (1 / (1 + |q.1|) ^ 2) *
        (Icc (0 : ℝ) 1).indicator (fun _ => (1 : ℝ≥0∞)) q.2) := by
  have hC : 0 ≤ CkM * AkM ^ c * (Nat.factorial (2 * c) : ℝ) := by
    have := kerM_bound.1; have := kerM_bound.2.1; positivity
  have h1 : (1 : ℝ≥0∞) + ‖q.1‖ₑ = ENNReal.ofReal (1 + |q.1|) := by
    rw [ENNReal.ofReal_add zero_le_one (abs_nonneg _), ENNReal.ofReal_one, ← Real.norm_eq_abs,
      ofReal_norm]
  by_cases hq : q.2 ∈ Icc (0 : ℝ) 1
  · simp only [gM, Set.indicator_of_mem hq, one_mul, mul_one, h1]
    rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul hC]
    congr 1
    have : 0 < 1 + |q.1| := by positivity
    field_simp
  · simp [gM, Set.indicator_of_notMem hq]

theorem lintegral_gM_weight (c : ℕ) :
    ∫⁻ q : ℝ × ℝ, (1 + ‖q.1‖ₑ) * gM c q = gev (CkM * IM) AkM c := by
  simp_rw [one_add_mul_gM]
  rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, Measure.volume_eq_prod,
    lintegral_prod_mul (f := fun σ : ℝ => ENNReal.ofReal (1 / (1 + |σ|) ^ 2))
      (g := (Icc (0 : ℝ) 1).indicator (fun _ => (1 : ℝ≥0∞))) (by fun_prop)
      ((measurable_const.indicator measurableSet_Icc).aemeasurable),
    lintegral_decay2_eq, lintegral_indicator measurableSet_Icc, setLIntegral_const,
    Real.volume_Icc, sub_zero, ENNReal.ofReal_one, one_mul, mul_one, gev,
    ← ENNReal.ofReal_mul (by have := kerM_bound.1; have := kerM_bound.2.1; positivity)]
  congr 1
  ring

theorem lintegral_gM_le (c : ℕ) : ∫⁻ q : ℝ × ℝ, gM c q ≤ gev (CkM * IM) AkM c := by
  rw [← lintegral_gM_weight]
  exact lintegral_mono fun q => le_mul_of_one_le_left (by positivity) le_self_add

/-- The coupling `Φ` (no auxiliary variable). -/
@[expose] noncomputable def kPhi (x : ℝ) (_ : Unit) : ℂ := phiR x

/-- The coupling `-Φ` (no auxiliary variable). -/
@[expose] noncomputable def kPhiNeg (x : ℝ) (_ : Unit) : ℂ := -phiR x

/-- The bound `C_Φ A^c (2c)!` of `(1 + |x|) |∂^c Φ(x)|`. -/
@[expose] noncomputable def gPhi (c : ℕ) (_ : Unit) : ℝ≥0∞ :=
  ENNReal.ofReal (CPhi * Achi ^ c * (Nat.factorial (2 * c) : ℝ))

theorem enorm_weight_phiR_le (c : ℕ) (x : ℝ) :
    (1 + ‖x‖ₑ) * ‖iteratedDeriv c phiR x‖ₑ ≤ gPhi c () := by
  rw [← ofReal_norm (iteratedDeriv c phiR x), show (1 : ℝ≥0∞) + ‖x‖ₑ = ENNReal.ofReal (1 + |x|) by
    rw [ENNReal.ofReal_add zero_le_one (abs_nonneg _), ENNReal.ofReal_one, ← Real.norm_eq_abs,
      ofReal_norm], ← ENNReal.ofReal_mul (by positivity)]
  exact ENNReal.ofReal_le_ofReal (phiR_gevrey c x)

theorem iteratedDeriv_kPhiNeg (c : ℕ) (x : ℝ) (q : Unit) :
    ‖iteratedDeriv c (fun x => kPhiNeg x q) x‖ₑ = ‖iteratedDeriv c phiR x‖ₑ := by
  have : (fun x => kPhiNeg x q) = fun x => -phiR x := rfl
  rw [this, iteratedDeriv_fun_neg, enorm_neg]

theorem lintegral_gPhi (c : ℕ) : ∫⁻ q : Unit, gPhi c q = gev CPhi Achi c := by
  rw [show (volume : Measure Unit) = Measure.dirac () from rfl, lintegral_dirac]
  rfl

end Couplings

section WeightSplit

theorem rpow_add3_le {θ : ℝ} (h0 : 0 ≤ θ) (h1 : θ ≤ 1) (a b c : ℝ≥0∞) :
    (a + b + c) ^ θ ≤ a ^ θ + b ^ θ + c ^ θ :=
  (rpow_add_le h0 h1 _ _).trans (add_le_add (rpow_add_le h0 h1 _ _) le_rfl)

variable {ι₁ ι₂ : Type*} [Fintype ι₁] [Fintype ι₂]

theorem sum_enorm_sumType (α : ι₁ ⊕ ι₂ → ℝ) :
    ∑ j, ‖α j‖ₑ = ∑ i, ‖α (Sum.inl i)‖ₑ + ∑ i, ‖α (Sum.inr i)‖ₑ :=
  Fintype.sum_sum_type _

/-- The weight split for the `χ₀` piece (`γ₁' = γ₁ + σ`). -/
theorem wJ_split_M {θ : ℝ} (h0 : 0 ≤ θ) (h1 : θ ≤ 1) (α : ι₁ ⊕ ι₂ → ℝ) (γ₁ γ₃ σ : ℝ) :
    wJ θ α (γ₁ + σ) ≤ wJ θ (fun i => α (Sum.inl i)) γ₁ + wJ θ (fun i => α (Sum.inr i)) γ₃ +
      (1 + ‖σ‖ₑ) := by
  unfold wJ
  rw [sum_enorm_sumType]
  set a := ∑ i, ‖α (Sum.inl i)‖ₑ
  set b := ∑ i, ‖α (Sum.inr i)‖ₑ
  calc (1 + (a + b) + ‖γ₁ + σ‖ₑ) ^ θ ≤ ((1 + a + ‖γ₁‖ₑ) + b + ‖σ‖ₑ) ^ θ := by
        refine rpow_mono' h0 ?_
        calc 1 + (a + b) + ‖γ₁ + σ‖ₑ ≤ 1 + (a + b) + (‖γ₁‖ₑ + ‖σ‖ₑ) := by
              gcongr; exact enorm_add_le _ _
          _ = _ := by ring
    _ ≤ (1 + a + ‖γ₁‖ₑ) ^ θ + b ^ θ + ‖σ‖ₑ ^ θ := rpow_add3_le h0 h1 _ _ _
    _ ≤ _ := by
        have hb : b ^ θ ≤ (1 + b + ‖γ₃‖ₑ) ^ θ := rpow_mono' h0 (le_add_right (le_add_left le_rfl))
        exact add_le_add (add_le_add le_rfl hb) (rpow_le_one_add h0 h1 _)

/-- The weight split for the `χ_∞` piece with `γ₁' = γ₁ + γ₂ + γ₃`: the part `|γ₂ + γ₃|^θ` is
replaced by `|x|^θ + |ℓ₂ - ℓ₁|^θ` with `x = ℓ₂ - ℓ₁ + γ₂ + γ₃` (DH21 L1003). -/
theorem wJ_split_P1 {θ : ℝ} (h0 : 0 ≤ θ) (h1 : θ ≤ 1) {y : ι₁ ⊕ ι₂ → ℤ} (hy : IsBundle y)
    (α : ι₁ ⊕ ι₂ → ℝ) (γ₁ γ₂ γ₃ : ℝ) :
    wJ θ α (γ₁ + (γ₂ + γ₃)) ≤ 2 * wJ θ (fun i => α (Sum.inl i)) γ₁ +
      2 * wJ θ (fun i => α (Sum.inr i)) γ₃ + (1 + ‖bundle y α + (γ₂ + γ₃)‖ₑ) := by
  set x := bundle y α + (γ₂ + γ₃)
  have hx : ‖γ₂ + γ₃‖ₑ ≤ ‖x‖ₑ + ∑ j, ‖α j‖ₑ := by
    have : γ₂ + γ₃ = x + -bundle y α := by simp only [x]; ring
    rw [this]
    refine (enorm_add_le _ _).trans ?_
    rw [enorm_neg]
    gcongr
    exact abs_bundle_le hy α
  unfold wJ
  rw [sum_enorm_sumType] at hx ⊢
  set a := ∑ i, ‖α (Sum.inl i)‖ₑ
  set b := ∑ i, ‖α (Sum.inr i)‖ₑ
  have ha : a ^ θ ≤ (1 + a + ‖γ₁‖ₑ) ^ θ := rpow_mono' h0 (le_add_right (le_add_left le_rfl))
  have hb : b ^ θ ≤ (1 + b + ‖γ₃‖ₑ) ^ θ := rpow_mono' h0 (le_add_right (le_add_left le_rfl))
  calc (1 + (a + b) + ‖γ₁ + (γ₂ + γ₃)‖ₑ) ^ θ
      ≤ ((1 + a + ‖γ₁‖ₑ) + (b + b) + (‖x‖ₑ + a)) ^ θ := by
        refine rpow_mono' h0 ?_
        calc 1 + (a + b) + ‖γ₁ + (γ₂ + γ₃)‖ₑ ≤ 1 + (a + b) + (‖γ₁‖ₑ + ‖γ₂ + γ₃‖ₑ) := by
              gcongr; exact enorm_add_le _ _
          _ ≤ 1 + (a + b) + (‖γ₁‖ₑ + (‖x‖ₑ + (a + b))) := by gcongr
          _ = _ := by ring
    _ ≤ (1 + a + ‖γ₁‖ₑ) ^ θ + (b + b) ^ θ + (‖x‖ₑ + a) ^ θ := rpow_add3_le h0 h1 _ _ _
    _ ≤ (1 + a + ‖γ₁‖ₑ) ^ θ + (b ^ θ + b ^ θ) + (‖x‖ₑ ^ θ + a ^ θ) :=
        add_le_add (add_le_add le_rfl (rpow_add_le h0 h1 _ _)) (rpow_add_le h0 h1 _ _)
    _ ≤ (1 + a + ‖γ₁‖ₑ) ^ θ + ((1 + b + ‖γ₃‖ₑ) ^ θ + (1 + b + ‖γ₃‖ₑ) ^ θ) +
          ((1 + ‖x‖ₑ) + (1 + a + ‖γ₁‖ₑ) ^ θ) :=
        add_le_add (add_le_add le_rfl (add_le_add hb hb))
          (add_le_add (rpow_le_one_add h0 h1 _) ha)
    _ = _ := by ring

/-- The weight split for the `χ_∞` piece with `γ₁' = γ₁`. -/
theorem wJ_split_P2 {θ : ℝ} (h0 : 0 ≤ θ) (h1 : θ ≤ 1) (α : ι₁ ⊕ ι₂ → ℝ) (γ₁ γ₃ : ℝ) :
    wJ θ α γ₁ ≤ wJ θ (fun i => α (Sum.inl i)) γ₁ + wJ θ (fun i => α (Sum.inr i)) γ₃ := by
  unfold wJ
  rw [sum_enorm_sumType]
  set a := ∑ i, ‖α (Sum.inl i)‖ₑ
  set b := ∑ i, ‖α (Sum.inr i)‖ₑ
  calc (1 + (a + b) + ‖γ₁‖ₑ) ^ θ = ((1 + a + ‖γ₁‖ₑ) + b) ^ θ := by ring_nf
    _ ≤ (1 + a + ‖γ₁‖ₑ) ^ θ + b ^ θ := rpow_add_le h0 h1 _ _
    _ ≤ _ := add_le_add le_rfl (rpow_mono' h0 (le_add_right (le_add_left le_rfl)))

end WeightSplit

section GevAux

theorem gev_add3 {a b c A : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hA : 0 ≤ A) (k : ℕ) :
    gev a A k + gev b A k + gev c A k = gev (a + b + c) A k := by
  unfold gev
  rw [← ENNReal.ofReal_add (by positivity) (by positivity),
    ← ENNReal.ofReal_add (by positivity) (by positivity)]
  congr 1
  ring

theorem gev_two_mul (N A : ℝ) (k : ℕ) : 2 * gev N A k = gev (2 * N) A k := by
  rw [show (2 : ℝ≥0∞) = ENNReal.ofReal 2 by simp, gev_mul_const 2 (by norm_num)]

variable {ι : Type*} [Fintype ι]

theorem lintegral_one_dnorm_le {θ : ℝ} (h0 : 0 ≤ θ) (m : (ι → ℝ) → ℝ × ℝ → ℂ) (j : ℕ) :
    ∫⁻ a, ∫⁻ γ : ℝ × ℝ, 1 * dnorm j m a γ ≤ jNorm θ j m :=
  lintegral_mono fun a => lintegral_mono fun γ =>
    mul_le_mul' (one_le_wJ h0 a γ.1) le_rfl

theorem lintegral_two_wJ_dnorm (θ : ℝ) (m : (ι → ℝ) → ℝ × ℝ → ℂ) (j : ℕ) :
    ∫⁻ a, ∫⁻ γ : ℝ × ℝ, 2 * wJ θ a γ.1 * dnorm j m a γ = 2 * jNorm θ j m := by
  unfold jNorm
  simp_rw [mul_assoc]
  rw [← lintegral_const_mul' _ _ (by simp)]
  refine lintegral_congr fun a => ?_
  rw [lintegral_const_mul' _ _ (by simp)]

end GevAux

section Pieces

variable {ι₁ ι₂ : Type*} [Fintype ι₁] [Fintype ι₂]

/-- `γ₂ + γ₃` in the natural layout. -/
@[expose] def cJJ {Q : Type*} (z : (ℝ × ℝ) × ((ℝ × ℝ) × Q)) : ℝ := z.1.2 + z.2.1.1

theorem measurable_cJJ {Q : Type*} [MeasurableSpace Q] : Measurable (cJJ (Q := Q)) := by
  unfold cJJ; fun_prop

/-- The shift of the `χ₀` piece: `γ' = (γ₁ + σ, γ₄ + γ₂ + γ₃ - σ)`. -/
@[expose] def bM (η : (ℝ × ℝ) × (ℝ × ℝ)) : ℝ × ℝ := (η.2.1, η.1.1 + η.1.2 - η.2.1)

/-- The shift of the first `χ_∞` piece: `γ' = (γ₁ + γ₂ + γ₃, γ₄)`. -/
@[expose] def bP1 (η : (ℝ × ℝ) × Unit) : ℝ × ℝ := (η.1.1 + η.1.2, 0)

/-- The shift of the second `χ_∞` piece: `γ' = (γ₁, γ₄ + γ₂ + γ₃)`. -/
@[expose] def bP2 (η : (ℝ × ℝ) × Unit) : ℝ × ℝ := (0, η.1.1 + η.1.2)

theorem measurable_bM : Measurable bM := by unfold bM; fun_prop
theorem measurable_bP1 : Measurable bP1 := by unfold bP1; fun_prop
theorem measurable_bP2 : Measurable bP2 := by unfold bP2; fun_prop

variable {θ A N₁ N₂ : ℝ} {R₁ : JSym ι₁} {R₂ : JSym ι₂}

/-- Bounds for the three factors of a product symbol from the class `J` bounds. -/
theorem S_bounds (h0 : 0 ≤ θ) (h₁ : R₁.Bound θ A N₁) (j : ℕ) :
    (∫⁻ a, ∫⁻ γ : ℝ × ℝ, wJ θ a γ.1 * dnorm j R₁.m a γ ≤ gev N₁ A j) ∧
    (∫⁻ a, ∫⁻ γ : ℝ × ℝ, 1 * dnorm j R₁.m a γ ≤ gev N₁ A j) ∧
    (∫⁻ a, ∫⁻ γ : ℝ × ℝ, 2 * wJ θ a γ.1 * dnorm j R₁.m a γ ≤ gev (2 * N₁) A j) := by
  refine ⟨h₁.norm j, (lintegral_one_dnorm_le h0 _ j).trans (h₁.norm j), ?_⟩
  rw [lintegral_two_wJ_dnorm, ← gev_two_mul]
  exact mul_le_mul' le_rfl (h₁.norm j)

/-- Summing three Gevrey bounds of a common profile. -/
theorem sum_fin3_le_gev {T : Fin 3 → ℝ≥0∞} {N A : ℝ} (hN : 0 ≤ N) (hA : 0 ≤ A) {k : ℕ}
    (hT : ∀ p, T p ≤ gev N A k) : ∑ p, T p ≤ gev (3 * N) A k := by
  rw [Fin.sum_univ_three, show 3 * N = N + N + N by ring, ← gev_add3 hN hN hN hA]
  exact add_le_add (add_le_add (hT 0) (hT 1)) (hT 2)

/-- **The `χ₀` piece of `J^{(1)} J^{(2)}`: weighted Gevrey bounds** (DH21 L987–L996). -/
theorem norm_piece_M (h0 : 0 ≤ θ) (h1 : θ ≤ 1) (hA : A0 ≤ A) (h₁ : R₁.Bound θ A N₁)
    (h₂ : R₂.Bound θ A N₂) (k : ℕ) :
    ∫⁻ α, ∫⁻ z, wJ θ α ((eJJ (ℝ × ℝ) z).1.1 + (bM (eJJ (ℝ × ℝ) z).2).1) *
      dnorm k (triple R₁.m R₂.m kerM (yDiff R₁.y R₂.y) cJJ) α z ≤
        gev (3 * (16 * N₁ * N₂ * (CkM * IM))) A k := by
  have hA0 : 0 ≤ A := A0_nonneg.trans hA
  have hC : 0 ≤ CkM * IM := mul_nonneg kerM_bound.1 IM_nonneg
  set w₁ : Fin 3 → (ι₁ → ℝ) → ℝ × ℝ → ℝ≥0∞ :=
    ![fun a γ => wJ θ a γ.1, fun _ _ => 1, fun _ _ => 1] with hw₁d
  set w₂ : Fin 3 → (ι₂ → ℝ) → ℝ × ℝ → ℝ≥0∞ :=
    ![fun _ _ => 1, fun b γ => wJ θ b γ.1, fun _ _ => 1] with hw₂d
  set w₃ : Fin 3 → ℝ → ℝ × ℝ → ℝ≥0∞ :=
    ![fun _ _ => 1, fun _ _ => 1, fun _ q => 1 + ‖q.1‖ₑ] with hw₃d
  set G : Fin 3 → ℕ → ℝ × ℝ → ℝ≥0∞ := ![gM, gM, fun c q => (1 + ‖q.1‖ₑ) * gM c q] with hGd
  clear_value w₁ w₂ w₃ G
  have hw₁ : ∀ p, Measurable (Function.uncurry (w₁ p)) := by
    intro p; subst hw₁d; fin_cases p
    · exact measurable_wJ θ
    · exact measurable_const
    · exact measurable_const
  have hw₂ : ∀ p, Measurable (Function.uncurry (w₂ p)) := by
    intro p; subst hw₂d; fin_cases p
    · exact measurable_const
    · exact measurable_wJ θ
    · exact measurable_const
  have hGm : ∀ p c, Measurable (G p c) := by
    intro p c; subst hGd; fin_cases p
    · exact measurable_gM c
    · exact measurable_gM c
    · exact (measurable_const.add (measurable_fst.enorm)).mul (measurable_gM c)
  have hW : ∀ α z, wJ θ α ((eJJ (ℝ × ℝ) z).1.1 + (bM (eJJ (ℝ × ℝ) z).2).1) ≤
      ∑ p, w₁ p (fun i => α (Sum.inl i)) z.1 * w₂ p (fun i => α (Sum.inr i)) z.2.1 *
        w₃ p (bundle (yDiff R₁.y R₂.y) α + cJJ z) z.2.2 := fun α z => by
    simp only [eJJ_apply, bM, Fin.sum_univ_three, hw₁d, hw₂d, hw₃d, Matrix.cons_val, mul_one,
      one_mul]
    exact wJ_split_M h0 h1 α z.1.1 z.2.1.1 z.2.2.1
  have hG : ∀ p c x q, w₃ p x q * ‖iteratedDeriv c (fun x => kerM x q) x‖ₑ ≤ G p c q := by
    intro p c x q; subst hw₃d hGd; fin_cases p
    · simpa using enorm_iteratedDeriv_kerM_le c x q
    · simpa using enorm_iteratedDeriv_kerM_le c x q
    · simpa using mul_le_mul' le_rfl (enorm_iteratedDeriv_kerM_le c x q)
  have hN₁ := h₁.nonneg
  have hN₂ := h₂.nonneg
  have key := lintegral_triple_le (m₁ := R₁.m) (m₂ := R₂.m) (K := kerM)
    (y := yDiff R₁.y R₂.y) (c := cJJ) (isBundle_yDiff h₁.bundle h₂.bundle) h₁.reg h₂.reg
    contDiff_kerM (fun α z => wJ θ α ((eJJ (ℝ × ℝ) z).1.1 + (bM (eJJ (ℝ × ℝ) z).2).1))
    w₁ w₂ w₃ hw₁ hw₂ hW G hGm hG k
  refine key.trans (sum_fin3_le_gev (by positivity) hA0 fun p => ?_)
  refine gev_conv3_le (S₁ := fun j => ∫⁻ a, ∫⁻ z₁, w₁ p a z₁ * dnorm j R₁.m a z₁)
    (S₂ := fun j => ∫⁻ b, ∫⁻ z₂, w₂ p b z₂ * dnorm j R₂.m b z₂)
    (S₃ := fun j => ∫⁻ q, G p j q) hN₁ hN₂ hC hA0 (fun j => ?_) (fun j => ?_) (fun j => ?_) k
  · subst hw₁d; fin_cases p
    · exact (S_bounds h0 h₁ j).1
    · exact (S_bounds h0 h₁ j).2.1
    · exact (S_bounds h0 h₁ j).2.1
  · subst hw₂d; fin_cases p
    · exact (S_bounds h0 h₂ j).2.1
    · exact (S_bounds h0 h₂ j).1
    · exact (S_bounds h0 h₂ j).2.1
  · have hmono := gev_mono (le_refl (CkM * IM)) kerM_bound.2.1 (AkM_le_A0.trans hA) hC j
    subst hGd; fin_cases p
    · exact (lintegral_gM_le j).trans hmono
    · exact (lintegral_gM_le j).trans hmono
    · exact (lintegral_gM_weight j).le.trans hmono

/-- Summed three-group Gevrey convolution over three weight pieces. -/
theorem sum_conv3_le {S₁ S₂ S₃ : Fin 3 → ℕ → ℝ≥0∞} {N₁' N₂' N₃ A' : ℝ} (hN₁ : 0 ≤ N₁')
    (hN₂ : 0 ≤ N₂') (hN₃ : 0 ≤ N₃) (hA : 0 ≤ A') (h₁ : ∀ p j, S₁ p j ≤ gev N₁' A' j)
    (h₂ : ∀ p j, S₂ p j ≤ gev N₂' A' j) (h₃ : ∀ p j, S₃ p j ≤ gev N₃ A' j) (k : ℕ) :
    ∑ p, ∑ j ∈ range (k + 1), (k.choose j : ℝ≥0∞) * S₁ p j *
      ∑ i ∈ range (k - j + 1), ((k - j).choose i : ℝ≥0∞) * S₂ p i * S₃ p (k - j - i) ≤
      gev (3 * (16 * N₁' * N₂' * N₃)) A' k :=
  sum_fin3_le_gev (by positivity) hA fun p =>
    gev_conv3_le (S₁ := S₁ p) (S₂ := S₂ p) (S₃ := S₃ p) hN₁ hN₂ hN₃ hA (h₁ p) (h₂ p) (h₃ p) k

theorem gPhi_le (c : ℕ) {A : ℝ} (hA : A0 ≤ A) : ∫⁻ q : Unit, gPhi c q ≤ gev CPhi A c := by
  rw [lintegral_gPhi]
  exact gev_mono le_rfl Achi_nonneg (Achi_le_A0.trans hA) CPhi_nonneg c

theorem enorm_iteratedDeriv_phiR_le_gPhi (c : ℕ) (x : ℝ) :
    ‖iteratedDeriv c phiR x‖ₑ ≤ gPhi c () :=
  (le_mul_of_one_le_left (by positivity) le_self_add).trans (enorm_weight_phiR_le c x)

/-- **The first `χ_∞` piece: weighted Gevrey bounds** (DH21 (formula1), L1001–L1003). -/
theorem norm_piece_P1 (h0 : 0 ≤ θ) (h1 : θ ≤ 1) (hA : A0 ≤ A) (h₁ : R₁.Bound θ A N₁)
    (h₂ : R₂.Bound θ A N₂) (k : ℕ) :
    ∫⁻ α, ∫⁻ z, wJ θ α ((eJJ Unit z).1.1 + (bP1 (eJJ Unit z).2).1) *
      dnorm k (triple R₁.m R₂.m kPhi (yDiff R₁.y R₂.y) cJJ) α z ≤
        gev (3 * (16 * (2 * N₁) * (2 * N₂) * CPhi)) A k := by
  have hA0 : 0 ≤ A := A0_nonneg.trans hA
  have hN₁ := h₁.nonneg
  have hN₂ := h₂.nonneg
  set w₁ : Fin 3 → (ι₁ → ℝ) → ℝ × ℝ → ℝ≥0∞ :=
    ![fun a γ => 2 * wJ θ a γ.1, fun _ _ => 1, fun _ _ => 1] with hw₁d
  set w₂ : Fin 3 → (ι₂ → ℝ) → ℝ × ℝ → ℝ≥0∞ :=
    ![fun _ _ => 1, fun b γ => 2 * wJ θ b γ.1, fun _ _ => 1] with hw₂d
  set w₃ : Fin 3 → ℝ → Unit → ℝ≥0∞ := ![fun _ _ => 1, fun _ _ => 1, fun x _ => 1 + ‖x‖ₑ]
    with hw₃d
  set G : Fin 3 → ℕ → Unit → ℝ≥0∞ := ![gPhi, gPhi, gPhi] with hGd
  clear_value w₁ w₂ w₃ G
  have hw₁ : ∀ p, Measurable (Function.uncurry (w₁ p)) := by
    intro p; subst hw₁d; fin_cases p
    · exact measurable_const.mul (measurable_wJ θ)
    · exact measurable_const
    · exact measurable_const
  have hw₂ : ∀ p, Measurable (Function.uncurry (w₂ p)) := by
    intro p; subst hw₂d; fin_cases p
    · exact measurable_const
    · exact measurable_const.mul (measurable_wJ θ)
    · exact measurable_const
  have hGm : ∀ p c, Measurable (G p c) := by
    intro p c; subst hGd; fin_cases p <;> exact measurable_const
  have hW : ∀ α z, wJ θ α ((eJJ Unit z).1.1 + (bP1 (eJJ Unit z).2).1) ≤
      ∑ p, w₁ p (fun i => α (Sum.inl i)) z.1 * w₂ p (fun i => α (Sum.inr i)) z.2.1 *
        w₃ p (bundle (yDiff R₁.y R₂.y) α + cJJ z) z.2.2 := fun α z => by
    simp only [eJJ_apply, bP1, Fin.sum_univ_three, hw₁d, hw₂d, hw₃d, Matrix.cons_val, mul_one,
      one_mul, cJJ]
    exact wJ_split_P1 h0 h1 (isBundle_yDiff h₁.bundle h₂.bundle) α z.1.1 z.1.2 z.2.1.1
  have hG : ∀ p c x q, w₃ p x q * ‖iteratedDeriv c (fun x => kPhi x q) x‖ₑ ≤ G p c q := by
    intro p c x q; subst hw₃d hGd
    have hq : q = () := rfl
    subst hq
    fin_cases p
    · simpa [kPhi] using enorm_iteratedDeriv_phiR_le_gPhi c x
    · simpa [kPhi] using enorm_iteratedDeriv_phiR_le_gPhi c x
    · simpa [kPhi] using enorm_weight_phiR_le c x
  have key := lintegral_triple_le (m₁ := R₁.m) (m₂ := R₂.m) (K := kPhi)
    (y := yDiff R₁.y R₂.y) (c := cJJ) (isBundle_yDiff h₁.bundle h₂.bundle) h₁.reg h₂.reg
    (fun _ => contDiff_phiR)
    (fun α z => wJ θ α ((eJJ Unit z).1.1 + (bP1 (eJJ Unit z).2).1))
    w₁ w₂ w₃ hw₁ hw₂ hW G hGm hG k
  refine key.trans (sum_conv3_le (S₁ := fun p j => ∫⁻ a, ∫⁻ z₁, w₁ p a z₁ * dnorm j R₁.m a z₁)
    (S₂ := fun p j => ∫⁻ b, ∫⁻ z₂, w₂ p b z₂ * dnorm j R₂.m b z₂)
    (S₃ := fun p j => ∫⁻ q, G p j q) (by positivity) (by positivity) CPhi_nonneg hA0
    (fun p j => ?_) (fun p j => ?_) (fun p j => ?_) k)
  · subst hw₁d; fin_cases p
    · exact (S_bounds h0 h₁ j).2.2
    · exact (S_bounds h0 h₁ j).2.1.trans (gev_mono (by linarith) hA0 le_rfl (by positivity) j)
    · exact (S_bounds h0 h₁ j).2.1.trans (gev_mono (by linarith) hA0 le_rfl (by positivity) j)
  · subst hw₂d; fin_cases p
    · exact (S_bounds h0 h₂ j).2.1.trans (gev_mono (by linarith) hA0 le_rfl (by positivity) j)
    · exact (S_bounds h0 h₂ j).2.2
    · exact (S_bounds h0 h₂ j).2.1.trans (gev_mono (by linarith) hA0 le_rfl (by positivity) j)
  · subst hGd; fin_cases p <;> exact gPhi_le j hA

/-- **The second `χ_∞` piece: weighted Gevrey bounds** (DH21 (formula2), L1001–L1003). -/
theorem norm_piece_P2 (h0 : 0 ≤ θ) (h1 : θ ≤ 1) (hA : A0 ≤ A) (h₁ : R₁.Bound θ A N₁)
    (h₂ : R₂.Bound θ A N₂) (k : ℕ) :
    ∫⁻ α, ∫⁻ z, wJ θ α ((eJJ Unit z).1.1 + (bP2 (eJJ Unit z).2).1) *
      dnorm k (triple R₁.m R₂.m kPhiNeg (yDiff R₁.y R₂.y) cJJ) α z ≤
        gev (3 * (16 * N₁ * N₂ * CPhi)) A k := by
  have hA0 : 0 ≤ A := A0_nonneg.trans hA
  have hN₁ := h₁.nonneg
  have hN₂ := h₂.nonneg
  set w₁ : Fin 3 → (ι₁ → ℝ) → ℝ × ℝ → ℝ≥0∞ :=
    ![fun a γ => wJ θ a γ.1, fun _ _ => 1, fun _ _ => 1] with hw₁d
  set w₂ : Fin 3 → (ι₂ → ℝ) → ℝ × ℝ → ℝ≥0∞ :=
    ![fun _ _ => 1, fun b γ => wJ θ b γ.1, fun _ _ => 1] with hw₂d
  set w₃ : Fin 3 → ℝ → Unit → ℝ≥0∞ := ![fun _ _ => 1, fun _ _ => 1, fun _ _ => 0] with hw₃d
  set G : Fin 3 → ℕ → Unit → ℝ≥0∞ := ![gPhi, gPhi, fun _ _ => 0] with hGd
  clear_value w₁ w₂ w₃ G
  have hw₁ : ∀ p, Measurable (Function.uncurry (w₁ p)) := by
    intro p; subst hw₁d; fin_cases p
    · exact measurable_wJ θ
    · exact measurable_const
    · exact measurable_const
  have hw₂ : ∀ p, Measurable (Function.uncurry (w₂ p)) := by
    intro p; subst hw₂d; fin_cases p
    · exact measurable_const
    · exact measurable_wJ θ
    · exact measurable_const
  have hGm : ∀ p c, Measurable (G p c) := by
    intro p c; subst hGd; fin_cases p <;> exact measurable_const
  have hW : ∀ α z, wJ θ α ((eJJ Unit z).1.1 + (bP2 (eJJ Unit z).2).1) ≤
      ∑ p, w₁ p (fun i => α (Sum.inl i)) z.1 * w₂ p (fun i => α (Sum.inr i)) z.2.1 *
        w₃ p (bundle (yDiff R₁.y R₂.y) α + cJJ z) z.2.2 := fun α z => by
    simp only [eJJ_apply, bP2, Fin.sum_univ_three, hw₁d, hw₂d, hw₃d, Matrix.cons_val, mul_one,
      one_mul, mul_zero, add_zero]
    exact wJ_split_P2 h0 h1 α z.1.1 z.2.1.1
  have hG : ∀ p c x q, w₃ p x q * ‖iteratedDeriv c (fun x => kPhiNeg x q) x‖ₑ ≤ G p c q := by
    intro p c x q; subst hw₃d hGd
    have hq : q = () := rfl
    subst hq
    fin_cases p
    · simpa [iteratedDeriv_kPhiNeg] using enorm_iteratedDeriv_phiR_le_gPhi c x
    · simpa [iteratedDeriv_kPhiNeg] using enorm_iteratedDeriv_phiR_le_gPhi c x
    · simp
  have hK : ∀ q : Unit, ContDiff ℝ ∞ fun x => kPhiNeg x q := fun _ => contDiff_phiR.neg
  have key := lintegral_triple_le (m₁ := R₁.m) (m₂ := R₂.m) (K := kPhiNeg)
    (y := yDiff R₁.y R₂.y) (c := cJJ) (isBundle_yDiff h₁.bundle h₂.bundle) h₁.reg h₂.reg hK
    (fun α z => wJ θ α ((eJJ Unit z).1.1 + (bP2 (eJJ Unit z).2).1))
    w₁ w₂ w₃ hw₁ hw₂ hW G hGm hG k
  refine key.trans (sum_conv3_le (S₁ := fun p j => ∫⁻ a, ∫⁻ z₁, w₁ p a z₁ * dnorm j R₁.m a z₁)
    (S₂ := fun p j => ∫⁻ b, ∫⁻ z₂, w₂ p b z₂ * dnorm j R₂.m b z₂)
    (S₃ := fun p j => ∫⁻ q, G p j q) hN₁ hN₂ CPhi_nonneg hA0
    (fun p j => ?_) (fun p j => ?_) (fun p j => ?_) k)
  · subst hw₁d; fin_cases p
    · exact (S_bounds h0 h₁ j).1
    · exact (S_bounds h0 h₁ j).2.1
    · exact (S_bounds h0 h₁ j).2.1
  · subst hw₂d; fin_cases p
    · exact (S_bounds h0 h₂ j).2.1
    · exact (S_bounds h0 h₂ j).1
    · exact (S_bounds h0 h₂ j).2.1
  · subst hGd; fin_cases p
    · exact gPhi_le j hA
    · exact gPhi_le j hA
    · simp

end Pieces

section Regular

variable {ι₁ ι₂ : Type*} [Fintype ι₁] [Fintype ι₂]
variable {θ A N₁ N₂ : ℝ} {R₁ : JSym ι₁} {R₂ : JSym ι₂}

theorem gev_ne_top (N A : ℝ) (k : ℕ) : gev N A k ≠ ⊤ := ENNReal.ofReal_ne_top

theorem symReg_piece_M (h₁ : R₁.Bound θ A N₁) (h₂ : R₂.Bound θ A N₂) :
    SymReg (triple R₁.m R₂.m kerM (yDiff R₁.y R₂.y) cJJ) :=
  triple_symReg (isBundle_yDiff h₁.bundle h₂.bundle) h₁.reg h₂.reg contDiff_kerM
    measurable_kerM.stronglyMeasurable measurable_cJJ gM measurable_gM
    enorm_iteratedDeriv_kerM_le (fun k => ne_top_of_le_ne_top (gev_ne_top _ _ k) (lintegral_gM_le k))

theorem stronglyMeasurable_kPhi : StronglyMeasurable (Function.uncurry kPhi) :=
  (contDiff_phiR.continuous.comp continuous_fst).stronglyMeasurable

theorem stronglyMeasurable_kPhiNeg : StronglyMeasurable (Function.uncurry kPhiNeg) :=
  (contDiff_phiR.continuous.comp continuous_fst).neg.stronglyMeasurable

theorem symReg_piece_P1 (h₁ : R₁.Bound θ A N₁) (h₂ : R₂.Bound θ A N₂) :
    SymReg (triple R₁.m R₂.m kPhi (yDiff R₁.y R₂.y) cJJ) :=
  triple_symReg (isBundle_yDiff h₁.bundle h₂.bundle) h₁.reg h₂.reg (fun _ => contDiff_phiR)
    stronglyMeasurable_kPhi measurable_cJJ gPhi (fun _ => measurable_const)
    (fun c x q => by simpa [kPhi] using enorm_iteratedDeriv_phiR_le_gPhi c x)
    (fun k => by rw [lintegral_gPhi]; exact gev_ne_top _ _ k)

theorem symReg_piece_P2 (h₁ : R₁.Bound θ A N₁) (h₂ : R₂.Bound θ A N₂) :
    SymReg (triple R₁.m R₂.m kPhiNeg (yDiff R₁.y R₂.y) cJJ) :=
  triple_symReg (isBundle_yDiff h₁.bundle h₂.bundle) h₁.reg h₂.reg
    (fun _ => contDiff_phiR.neg) stronglyMeasurable_kPhiNeg measurable_cJJ gPhi
    (fun _ => measurable_const)
    (fun c x q => by
      rw [iteratedDeriv_kPhiNeg]
      exact enorm_iteratedDeriv_phiR_le_gPhi c x)
    (fun k => by rw [lintegral_gPhi]; exact gev_ne_top _ _ k)

/-- The basic class `J` operator of the `χ₀` piece. -/
theorem exists_piece_M (h0 : 0 ≤ θ) (h1 : θ ≤ 1) (hA : A0 ≤ A) (h₁ : R₁.Bound θ A N₁)
    (h₂ : R₂.Bound θ A N₂) :
    ∃ S : JSym (ι₁ ⊕ ι₂), S.Bound θ A (3 * (16 * N₁ * N₂ * (CkM * IM))) ∧ ∀ α t s,
      S.kernel α t s = ∫ z, triple R₁.m R₂.m kerM (yDiff R₁.y R₂.y) cJJ α z *
        jker (bundle (yL R₁.y) α) ((eJJ (ℝ × ℝ) z).1.1 + (bM (eJJ (ℝ × ℝ) z).2).1)
          ((eJJ (ℝ × ℝ) z).1.2 + (bM (eJJ (ℝ × ℝ) z).2).2) t s := by
  have hN₁ := h₁.nonneg
  have hN₂ := h₂.nonneg
  have hC : 0 ≤ CkM * IM := mul_nonneg kerM_bound.1 IM_nonneg
  obtain ⟨S, -, hS, hk⟩ := JSym.ofGenE (isBundle_yL h₁.bundle) (symReg_piece_M h₁ h₂)
    (eJJ (ℝ × ℝ)) (measurePreserving_eJJ _) measurable_bM (by positivity)
    (norm_piece_M h0 h1 hA h₁ h₂)
  exact ⟨S, hS, hk⟩

/-- The basic class `J` operator of the first `χ_∞` piece. -/
theorem exists_piece_P1 (h0 : 0 ≤ θ) (h1 : θ ≤ 1) (hA : A0 ≤ A) (h₁ : R₁.Bound θ A N₁)
    (h₂ : R₂.Bound θ A N₂) :
    ∃ S : JSym (ι₁ ⊕ ι₂), S.Bound θ A (3 * (16 * (2 * N₁) * (2 * N₂) * CPhi)) ∧ ∀ α t s,
      S.kernel α t s = ∫ z, triple R₁.m R₂.m kPhi (yDiff R₁.y R₂.y) cJJ α z *
        jker (bundle (yR R₂.y) α) ((eJJ Unit z).1.1 + (bP1 (eJJ Unit z).2).1)
          ((eJJ Unit z).1.2 + (bP1 (eJJ Unit z).2).2) t s := by
  have hN₁ := h₁.nonneg
  have hN₂ := h₂.nonneg
  have hC := CPhi_nonneg
  obtain ⟨S, -, hS, hk⟩ := JSym.ofGenE (isBundle_yR h₂.bundle) (symReg_piece_P1 h₁ h₂)
    (eJJ Unit) (measurePreserving_eJJ _) measurable_bP1 (by positivity)
    (norm_piece_P1 h0 h1 hA h₁ h₂)
  exact ⟨S, hS, hk⟩

/-- The basic class `J` operator of the second `χ_∞` piece. -/
theorem exists_piece_P2 (h0 : 0 ≤ θ) (h1 : θ ≤ 1) (hA : A0 ≤ A) (h₁ : R₁.Bound θ A N₁)
    (h₂ : R₂.Bound θ A N₂) :
    ∃ S : JSym (ι₁ ⊕ ι₂), S.Bound θ A (3 * (16 * N₁ * N₂ * CPhi)) ∧ ∀ α t s,
      S.kernel α t s = ∫ z, triple R₁.m R₂.m kPhiNeg (yDiff R₁.y R₂.y) cJJ α z *
        jker (bundle (yL R₁.y) α) ((eJJ Unit z).1.1 + (bP2 (eJJ Unit z).2).1)
          ((eJJ Unit z).1.2 + (bP2 (eJJ Unit z).2).2) t s := by
  have hN₁ := h₁.nonneg
  have hN₂ := h₂.nonneg
  have hC := CPhi_nonneg
  obtain ⟨S, -, hS, hk⟩ := JSym.ofGenE (isBundle_yL h₁.bundle) (symReg_piece_P2 h₁ h₂)
    (eJJ Unit) (measurePreserving_eJJ _) measurable_bP2 (by positivity)
    (norm_piece_P2 h0 h1 hA h₁ h₂)
  exact ⟨S, hS, hk⟩

end Regular

end WaveTurbulence.ClassJR
