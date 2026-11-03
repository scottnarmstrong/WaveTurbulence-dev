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

end WaveTurbulence.ClassJR
