/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Flower.ProtOpsFold.Atom
public import WaveTurbulence.Foundations.Sumint.FourierFubini
public import WaveTurbulence.Foundations.Sumint.ParametricFourierMeasurability
public import WaveTurbulence.Foundations.Fourier.TimeEuclidean
public import WaveTurbulence.Foundations.Fourier.SchwartzNorm

/-! # D1b-F FOLD 3: synthesis over Fourier atoms, and the generic fold estimate

* `synth2_norm_le`: if `‖atom l‖_{𝔛^θ} ≤ C_w ⟨l⟩^{θ'}` for a continuous family with a common integrable majorant,
  then `y ↦ ∫ Ĥ(l) atom l y` has `𝔛^θ` norm `≤ C_w ‖H‖_{𝔛^{θ'}}` (o82 §17: "integration against the input Fourier
  measure"). Two exponents: the fold loses `θ' - θ`.
* `fold_norm_le`: for continuous `H`, `k · (H ∘ P) = ∫ Ĥ(l) k e(l · P) dl` (Fourier inversion), so the fold obeys the
  atom bound of `foldAtom k P l = k · e(l · P)`.
* The fold weights `foldK ℓ₁ ℓ₂ = foldCut · e^{ℓ₁+ℓ₂} · e^{-|ℓ₁|-|ℓ₂|}` (equal to one where `foldCut = 1`, `ℓ₁, ℓ₂ ≥ 0`;
  bounded by `|foldCut|`) and `foldAtom_norm_le`: when the fold atom is `foldN · c · (kink ⊗ kink) ∘ g` with
  `g ∈ {id, shear}`, `|c| = 1` and parameters `≤ |l₀| + |l₁|`, its norm is `≤ C ⟨l⟩^{s+2ε}`. -/

@[expose] public section
set_option autoImplicit false
noncomputable section
open MeasureTheory Set WaveTurbulence.Fourier
open scoped ENNReal Real ContDiff

namespace WaveTurbulence.Flower.ProtOpsFold

/-! ## Synthesis -/

/-- Scalar Fourier synthesis `y ↦ ∫ Ĥ(l) atom l y`. -/
def synth2 (atom : (Fin 2 → ℝ) → (Fin 2 → ℝ) → ℂ) (H : (Fin 2 → ℝ) → ℂ) (y : Fin 2 → ℝ) : ℂ :=
  ∫ l, timeFourier H l * atom l y

variable {atom : (Fin 2 → ℝ) → (Fin 2 → ℝ) → ℂ}

theorem synth2_prod_integrable (hc : Continuous (fun q : (Fin 2 → ℝ) × (Fin 2 → ℝ) => atom q.1 q.2))
    {Ψ : (Fin 2 → ℝ) → ℝ} (hΨ : Integrable Ψ) (hbd : ∀ l y, ‖atom l y‖ ≤ Ψ y)
    {H : (Fin 2 → ℝ) → ℂ} (hH : Integrable H) (hhat : Integrable (timeFourier H)) :
    Integrable (fun q : (Fin 2 → ℝ) × (Fin 2 → ℝ) => timeFourier H q.1 * atom q.1 q.2)
      (volume.prod volume) := by
  have h1 := Integrable.mul_prod (f := fun l => ‖timeFourier H l‖) (g := Ψ) hhat.norm hΨ
  refine h1.mono' ?_ (ae_of_all _ fun q => ?_)
  · exact (((timeFourier_continuous hH).comp continuous_fst).mul hc).aestronglyMeasurable
  · simp only [norm_mul]
    exact mul_le_mul_of_nonneg_left (hbd _ _) (norm_nonneg _)

/-- **Synthesis with a loss of `θ' - θ`.** -/
theorem synth2_norm_le {θ θ' : ℝ} (hθ' : 0 ≤ θ')
    (hc : Continuous (fun q : (Fin 2 → ℝ) × (Fin 2 → ℝ) => atom q.1 q.2))
    {Ψ : (Fin 2 → ℝ) → ℝ} (hΨ : Integrable Ψ) (hbd : ∀ l y, ‖atom l y‖ ≤ Ψ y)
    {Cw : ℝ≥0∞} (hCw : ∀ l, timeFourierNorm θ (atom l) ≤ Cw * timeWeight θ' l)
    {H : (Fin 2 → ℝ) → ℂ} (hH : timeFourierNorm θ' H < ⊤) :
    timeFourierNorm θ (synth2 atom H) ≤ Cw * timeFourierNorm θ' H := by
  have hHi := integrable_of_timeFourierNorm_lt_top hH
  have hhat := integrable_timeFourier_of_norm_lt_top hθ' hH
  have hj := synth2_prod_integrable hc hΨ hbd hHi hhat
  have hG : Integrable (synth2 atom H) := hj.integral_prod_right
  have hai : ∀ l, Integrable (atom l) := fun l =>
    hΨ.mono' (hc.comp (by fun_prop : Continuous fun y : Fin 2 → ℝ => (l, y))).aestronglyMeasurable
      (ae_of_all _ (hbd l))
  have hFT : ∀ m, timeFourier (synth2 atom H) m = ∫ l, timeFourier H l * timeFourier (atom l) m := by
    intro m
    have h := Sumint.timeFourier_integral (μ := (volume : Measure (Fin 2 → ℝ)))
      (fun l y => timeFourier H l * atom l y) hj m
    refine h.trans (integral_congr_ae (ae_of_all _ fun l => ?_))
    exact congrFun (timeFourier_smul (timeFourier H l) (atom l)) m
  have hAm : Measurable (fun q : (Fin 2 → ℝ) × (Fin 2 → ℝ) => ‖timeFourier (atom q.2) q.1‖ₑ) := by
    have := Sumint.measurable_parametric_timeFourier (fun (l y : Fin 2 → ℝ) => atom l y) hc.measurable
    exact (this.comp measurable_swap).enorm
  have hHm : Measurable (fun l => ‖timeFourier H l‖ₑ) := (timeFourier_continuous hHi).measurable.enorm
  rw [timeFourierNorm_eq_lintegral hG, timeFourierNorm_eq_lintegral hHi]
  calc ∫⁻ m, timeWeight θ m * ‖timeFourier (synth2 atom H) m‖ₑ
      ≤ ∫⁻ m, ∫⁻ l, timeWeight θ m * (‖timeFourier H l‖ₑ * ‖timeFourier (atom l) m‖ₑ) := by
        refine lintegral_mono fun m => ?_
        rw [hFT, lintegral_const_mul' (timeWeight θ m) _ ENNReal.ofReal_ne_top]
        gcongr
        refine (enorm_integral_le_lintegral_enorm _).trans (le_of_eq ?_)
        simp only [enorm_mul]
    _ = ∫⁻ l, ∫⁻ m, timeWeight θ m * (‖timeFourier H l‖ₑ * ‖timeFourier (atom l) m‖ₑ) :=
        lintegral_lintegral_swap (((timeWeight_measurable θ).comp measurable_fst).mul
          ((hHm.comp measurable_snd).mul hAm)).aemeasurable
    _ = ∫⁻ l, ‖timeFourier H l‖ₑ * timeFourierNorm θ (atom l) := by
        refine lintegral_congr fun l => ?_
        rw [timeFourierNorm_eq_lintegral (hai l), ← lintegral_const_mul'']
        · exact lintegral_congr fun m => by ring
        · exact ((timeWeight_measurable θ).mul
            ((timeFourier_continuous (hai l)).measurable.enorm)).aemeasurable
    _ ≤ ∫⁻ l, ‖timeFourier H l‖ₑ * (Cw * timeWeight θ' l) :=
        lintegral_mono fun l => by gcongr; exact hCw l
    _ = Cw * ∫⁻ l, timeWeight θ' l * ‖timeFourier H l‖ₑ := by
        rw [← lintegral_const_mul'' Cw (f := fun l => timeWeight θ' l * ‖timeFourier H l‖ₑ)
          ((timeWeight_measurable θ').mul hHm).aemeasurable]
        exact lintegral_congr fun l => by ring

/-! ## The generic fold -/

/-- The fold atom `k(x) e(l · P x)`. -/
def foldAtom (k : (Fin 2 → ℝ) → ℂ) (P : (Fin 2 → ℝ) → (Fin 2 → ℝ)) (l x : Fin 2 → ℝ) : ℂ :=
  k x * (Real.fourierChar (timePairing 2 l (P x)) : ℂ)

theorem fold_eq_synth {k : (Fin 2 → ℝ) → ℂ} {P : (Fin 2 → ℝ) → (Fin 2 → ℝ)} {H : (Fin 2 → ℝ) → ℂ}
    (hHi : Integrable H) (hhat : Integrable (timeFourier H)) (hHc : Continuous H) (x : Fin 2 → ℝ) :
    k x * H (P x) = synth2 (foldAtom k P) H x := by
  have hinv : H (P x) = ∫ l, (Real.fourierChar (timePairing 2 l (P x)) : ℂ) * timeFourier H l := by
    rw [← timeFourier_inversion hHi hhat hHc (P x)]
    change (∫ l, Real.fourierChar (-timePairing 2 l (-P x)) • timeFourier H l) = _
    apply integral_congr_ae
    refine ae_of_all _ fun l => ?_
    show Real.fourierChar (-timePairing 2 l (-P x)) • timeFourier H l =
      (Real.fourierChar (timePairing 2 l (P x)) : ℂ) * timeFourier H l
    rw [(timePairing 2 l).map_neg, neg_neg, Circle.smul_def, smul_eq_mul]
  rw [hinv, ← integral_const_mul]
  unfold synth2 foldAtom
  apply integral_congr_ae
  exact ae_of_all _ fun l => by ring

theorem foldAtom_continuous {k : (Fin 2 → ℝ) → ℂ} (hk : Continuous k)
    {P : (Fin 2 → ℝ) → (Fin 2 → ℝ)} (hP : Continuous P) :
    Continuous (fun q : (Fin 2 → ℝ) × (Fin 2 → ℝ) => foldAtom k P q.1 q.2) := by
  unfold foldAtom
  refine (hk.comp continuous_snd).mul (continuous_subtype_val.comp (Real.continuous_fourierChar.comp ?_))
  change Continuous fun q : (Fin 2 → ℝ) × (Fin 2 → ℝ) => q.1 ⬝ᵥ P q.2
  simp only [dotProduct]
  have hPi : ∀ i : Fin 2, Continuous fun q : (Fin 2 → ℝ) × (Fin 2 → ℝ) => P q.2 i :=
    fun i => (continuous_apply (A := fun _ : Fin 2 => ℝ) i).comp (hP.comp continuous_snd)
  fun_prop

theorem norm_foldAtom (k : (Fin 2 → ℝ) → ℂ) (P : (Fin 2 → ℝ) → (Fin 2 → ℝ)) (l x : Fin 2 → ℝ) :
    ‖foldAtom k P l x‖ = ‖k x‖ := by
  simp [foldAtom]

/-- **The generic fold estimate.** -/
theorem fold_norm_le {θ θ' : ℝ} (hθ' : 0 ≤ θ') {k : (Fin 2 → ℝ) → ℂ} (hk : Continuous k)
    (hki : Integrable k) {P : (Fin 2 → ℝ) → (Fin 2 → ℝ)} (hP : Continuous P) {Cw : ℝ≥0∞}
    (hCw : ∀ l, timeFourierNorm θ (foldAtom k P l) ≤ Cw * timeWeight θ' l)
    {H : (Fin 2 → ℝ) → ℂ} (hHc : Continuous H) (hH : timeFourierNorm θ' H < ⊤) :
    timeFourierNorm θ (fun x => k x * H (P x)) ≤ Cw * timeFourierNorm θ' H := by
  have hHi := integrable_of_timeFourierNorm_lt_top hH
  have hhat := integrable_timeFourier_of_norm_lt_top hθ' hH
  have he : (fun x => k x * H (P x)) = synth2 (foldAtom k P) H := funext (fold_eq_synth hHi hhat hHc)
  rw [he]
  exact synth2_norm_le hθ' (foldAtom_continuous hk hP) hki.norm
    (fun l y => (norm_foldAtom k P l y).le) hCw hH

/-! ## The fold cutoff and weights -/

/-- The bump `1` on `[0,1]²`, supported in `(-1/2, 3/2)²`. -/
def foldBump : ContDiffBump (fun _ : Fin 2 => (1 / 2 : ℝ)) := ⟨1 / 2, 1, by norm_num, by norm_num⟩

/-- The fold cutoff. -/
def foldCut (x : Fin 2 → ℝ) : ℂ := ((foldBump x : ℝ) : ℂ)

theorem foldCut_contDiff : ContDiff ℝ ∞ foldCut :=
  Complex.ofRealCLM.contDiff.comp foldBump.contDiff

theorem foldCut_compact : HasCompactSupport foldCut :=
  foldBump.hasCompactSupport.comp_left (g := fun x : ℝ => (x : ℂ)) Complex.ofReal_zero

theorem norm_foldCut_le (x : Fin 2 → ℝ) : ‖foldCut x‖ ≤ 1 := by
  simp only [foldCut, Complex.norm_real, Real.norm_eq_abs]
  rw [abs_of_nonneg (foldBump.nonneg)]
  exact foldBump.le_one

theorem foldCut_one {x : Fin 2 → ℝ} (h : ∀ i, 0 ≤ x i ∧ x i ≤ 1) : foldCut x = 1 := by
  unfold foldCut
  have : x ∈ Metric.closedBall (fun _ : Fin 2 => (1 / 2 : ℝ)) foldBump.rIn := by
    rw [mem_closedBall_iff_norm]
    show ‖x - fun _ => (1 / 2 : ℝ)‖ ≤ 1 / 2
    rw [pi_norm_le_iff_of_nonneg (by norm_num)]
    intro i
    simp only [Pi.sub_apply, Real.norm_eq_abs, abs_le]
    obtain ⟨h1, h2⟩ := h i
    constructor <;> linarith
  rw [foldBump.one_of_mem_closedBall this]
  simp

theorem mem_of_foldCut_ne_zero {x : Fin 2 → ℝ} (h : foldCut x ≠ 0) (i : Fin 2) :
    -1 / 2 < x i ∧ x i < 3 / 2 := by
  have hx : x ∈ Function.support foldBump := by
    intro h0; apply h; simp [foldCut, h0]
  rw [foldBump.support_eq, Metric.mem_ball, dist_eq_norm] at hx
  have := (norm_le_pi_norm (x - fun _ => (1 / 2 : ℝ)) i).trans_lt hx
  simp only [Pi.sub_apply, Real.norm_eq_abs, abs_lt] at this
  rw [show foldBump.rOut = 1 from rfl] at this
  constructor <;> linarith [this.1, this.2]

theorem foldCut_integrable : Integrable foldCut :=
  foldCut_contDiff.continuous.integrable_of_hasCompactSupport foldCut_compact

/-- `foldN ℓ = foldCut · e^{ℓ}` (smooth, compactly supported for smooth `ℓ`). -/
def foldN (ℓ : (Fin 2 → ℝ) → ℝ) (x : Fin 2 → ℝ) : ℂ := foldCut x * (Real.exp (ℓ x) : ℂ)

theorem foldN_contDiff {ℓ : (Fin 2 → ℝ) → ℝ} (hℓ : ContDiff ℝ ∞ ℓ) : ContDiff ℝ ∞ (foldN ℓ) := by
  unfold foldN
  exact foldCut_contDiff.mul (Complex.ofRealCLM.contDiff.comp (Real.contDiff_exp.comp hℓ))

theorem foldN_compact (ℓ : (Fin 2 → ℝ) → ℝ) : HasCompactSupport (foldN ℓ) :=
  foldCut_compact.mul_right

/-- The fold weight `foldN (ℓ₁ + ℓ₂) · e^{-|ℓ₁| - |ℓ₂|}`. -/
def foldK (ℓ₁ ℓ₂ : (Fin 2 → ℝ) → ℝ) (x : Fin 2 → ℝ) : ℂ :=
  foldN (fun y => ℓ₁ y + ℓ₂ y) x * (Real.exp (-|ℓ₁ x| - |ℓ₂ x|) : ℂ)

theorem foldK_continuous {ℓ₁ ℓ₂ : (Fin 2 → ℝ) → ℝ} (h₁ : Continuous ℓ₁) (h₂ : Continuous ℓ₂) :
    Continuous (foldK ℓ₁ ℓ₂) := by
  unfold foldK foldN
  have := foldCut_contDiff.continuous
  fun_prop

theorem norm_foldK_le (ℓ₁ ℓ₂ : (Fin 2 → ℝ) → ℝ) (x : Fin 2 → ℝ) : ‖foldK ℓ₁ ℓ₂ x‖ ≤ ‖foldCut x‖ := by
  unfold foldK foldN
  beta_reduce
  rw [norm_mul, norm_mul, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs,
    abs_of_pos (Real.exp_pos _), abs_of_pos (Real.exp_pos _), mul_assoc, ← Real.exp_add]
  have : ℓ₁ x + ℓ₂ x + (-|ℓ₁ x| - |ℓ₂ x|) ≤ 0 := by linarith [le_abs_self (ℓ₁ x), le_abs_self (ℓ₂ x)]
  have h1 := Real.exp_le_one_iff.mpr this
  have h2 := norm_nonneg (foldCut x)
  nlinarith [Real.exp_pos (ℓ₁ x + ℓ₂ x + (-|ℓ₁ x| - |ℓ₂ x|))]

theorem foldK_integrable {ℓ₁ ℓ₂ : (Fin 2 → ℝ) → ℝ} (h₁ : Continuous ℓ₁) (h₂ : Continuous ℓ₂) :
    Integrable (foldK ℓ₁ ℓ₂) :=
  foldCut_integrable.norm.mono' (foldK_continuous h₁ h₂).aestronglyMeasurable
    (ae_of_all _ fun x => norm_foldK_le ℓ₁ ℓ₂ x)

theorem foldK_one {ℓ₁ ℓ₂ : (Fin 2 → ℝ) → ℝ} {x : Fin 2 → ℝ} (hc : foldCut x = 1) (h₁ : 0 ≤ ℓ₁ x)
    (h₂ : 0 ≤ ℓ₂ x) : foldK ℓ₁ ℓ₂ x = 1 := by
  unfold foldK foldN
  beta_reduce
  rw [hc, abs_of_nonneg h₁, abs_of_nonneg h₂, one_mul, ← Complex.ofReal_mul, ← Real.exp_add,
    show ℓ₁ x + ℓ₂ x + (-ℓ₁ x - ℓ₂ x) = 0 by ring, Real.exp_zero, Complex.ofReal_one]

/-! ## The generic fold-atom bound -/

/-- The fold-atom constant. -/
def foldC (s ε : ℝ) (ℓ : (Fin 2 → ℝ) → ℝ) : ℝ≥0∞ :=
  cutoffMultiplierConstant s (foldN ℓ) * ENNReal.ofReal (2 ^ s) *
    ENNReal.ofReal (kinkKC s ε * 4 ^ (s + 2 * ε))

theorem foldC_lt_top (s ε : ℝ) {ℓ : (Fin 2 → ℝ) → ℝ} (hℓ : ContDiff ℝ ∞ ℓ) : foldC s ε ℓ < ⊤ := by
  unfold foldC
  exact ENNReal.mul_lt_top (ENNReal.mul_lt_top
    (cutoffMultiplierConstant_lt_top s (foldN_compact ℓ) (foldN_contDiff hℓ)) ENNReal.ofReal_lt_top)
    ENNReal.ofReal_lt_top

theorem one_add_abs_add_le_four_timeBracket (l : Fin 2 → ℝ) :
    1 + |l 0| + |l 1| ≤ 4 * timeBracket l := by
  have h0 := (one_add_abs_le_two_sqrt (l 0)).trans (by linarith [bracket_le_timeBracket l 0] :
    2 * Real.sqrt (1 + l 0 ^ 2) ≤ 2 * timeBracket l)
  have h1 := (one_add_abs_le_two_sqrt (l 1)).trans (by linarith [bracket_le_timeBracket l 1] :
    2 * Real.sqrt (1 + l 1 ^ 2) ≤ 2 * timeBracket l)
  linarith

/-- **The fold atom bound**, from an exact factorization through a kink tensor. -/
theorem foldAtom_norm_le {s ε : ℝ} (hs : 0 ≤ s) (hε : 0 < ε) (hse : s + ε ≤ 1)
    {ℓ : (Fin 2 → ℝ) → ℝ} (hℓ : ContDiff ℝ ∞ ℓ) {k : (Fin 2 → ℝ) → ℂ} {P : (Fin 2 → ℝ) → (Fin 2 → ℝ)}
    {g : (Fin 2 → ℝ) → (Fin 2 → ℝ)} (hg : g = id ∨ g = shear) (l : Fin 2 → ℝ) {c : ℂ} (hc : ‖c‖ = 1)
    (a0 α0 β0 a1 α1 β1 : ℝ) (hα0 : |α0| ≤ |l 0| + |l 1|) (hβ0 : |β0| ≤ |l 0| + |l 1|)
    (hα1 : |α1| ≤ |l 0| + |l 1|) (hβ1 : |β1| ≤ |l 0| + |l 1|)
    (heq : ∀ x, foldAtom k P l x =
      foldN ℓ x * (c * tensor2 (kinkAtom a0 α0 β0) (kinkAtom a1 α1 β1) (g x))) :
    timeFourierNorm s (foldAtom k P l) ≤ foldC s ε ℓ * timeWeight (s + 2 * ε) l := by
  set R := 1 + |l 0| + |l 1|
  set T := tensor2 (kinkAtom a0 α0 β0) (kinkAtom a1 α1 β1)
  have hT := tensorKink_norm_le hs hε hse a0 α0 β0 a1 α1 β1 R (by linarith) (by linarith)
    (by linarith) (by linarith)
  have hTg : timeFourierNorm s (fun x => T (g x)) ≤
      ENNReal.ofReal (2 ^ s) * ENNReal.ofReal (kinkKC s ε * R ^ (s + 2 * ε)) := by
    rcases hg with rfl | rfl
    · refine hT.trans (le_mul_of_one_le_left (by positivity) ?_)
      rw [← ENNReal.ofReal_one]
      exact ENNReal.ofReal_le_ofReal (Real.one_le_rpow (by norm_num) hs)
    · exact (timeFourierNorm_shear_le hs T).trans (by gcongr)
  have hTgf : timeFourierNorm s (fun x => c • T (g x)) < ⊤ := by
    rw [timeFourierNorm_smul]
    exact ENNReal.mul_lt_top (by simp) (hTg.trans_lt (ENNReal.mul_lt_top ENNReal.ofReal_lt_top
      ENNReal.ofReal_lt_top))
  have hfun : foldAtom k P l = fun x => (c • T (g x)) * foldN ℓ x := by
    funext x; rw [heq, smul_eq_mul]; ring
  rw [hfun]
  refine (timeFourierNorm_mul_cutoff_le s hTgf (foldN_compact ℓ) (foldN_contDiff hℓ)).trans ?_
  rw [timeFourierNorm_smul, show ‖c‖ₑ = 1 by rw [← ofReal_norm, hc, ENNReal.ofReal_one], one_mul]
  have hR1 : 0 ≤ R := by positivity
  have hRw : ENNReal.ofReal (kinkKC s ε * R ^ (s + 2 * ε)) ≤
      ENNReal.ofReal (kinkKC s ε * 4 ^ (s + 2 * ε)) * timeWeight (s + 2 * ε) l := by
    unfold timeWeight
    rw [← ENNReal.ofReal_mul (by have := kinkKC_nonneg s ε; positivity)]
    apply ENNReal.ofReal_le_ofReal
    rw [mul_assoc, ← Real.mul_rpow (by norm_num) (timeBracket_pos l).le]
    have := kinkKC_nonneg s ε
    gcongr
    exact one_add_abs_add_le_four_timeBracket l
  calc cutoffMultiplierConstant s (foldN ℓ) * timeFourierNorm s (fun x => T (g x))
      ≤ cutoffMultiplierConstant s (foldN ℓ) *
          (ENNReal.ofReal (2 ^ s) * ENNReal.ofReal (kinkKC s ε * R ^ (s + 2 * ε))) := by gcongr
    _ ≤ cutoffMultiplierConstant s (foldN ℓ) * (ENNReal.ofReal (2 ^ s) *
          (ENNReal.ofReal (kinkKC s ε * 4 ^ (s + 2 * ε)) * timeWeight (s + 2 * ε) l)) := by gcongr
    _ = foldC s ε ℓ * timeWeight (s + 2 * ε) l := by unfold foldC; ring

end WaveTurbulence.Flower.ProtOpsFold
