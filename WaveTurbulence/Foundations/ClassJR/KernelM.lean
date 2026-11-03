/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.ClassJR.Coupling

/-!
# The `χ₀` kernel and the function `M₀`

* `kerM x (σ, τ) = χ₀(x) ftπ φ(σ - τx) 1_{[0,1]}(τ)` with `φ(v) = v χ₀(v - 1/2)`. For `v ∈ [0, 1]`,
  `∫∫ kerM x (σ, τ) e^{πiσv} dσ dτ = χ₀(x) ∫_0^v e^{πixu} du` (`integral_kerM_mul_exp`); this is the
  function `M` of DH21 L978, with the variable `τ` kept so that the `x`-derivatives are explicit.
  Bound: `|∂_x^c kerM x (σ, τ)| ≤ 1_{[0,1]}(τ) C A^c (2c)! (1 + |σ|)^{-3}` (`exists_kerM_bound`).
* `M0 = ftπ (χ₀(· - 1/2))` satisfies DH21 (extraid) (L1037): `e^{πiμs} = ∫ M0(σ) e^{πi(μ+σ)s} dσ`
  for `s ∈ [0, 1]` (`extraid`).
-/

public section

open MeasureTheory Set Complex Filter Topology
open scoped ContDiff Real

namespace WaveTurbulence.ClassJR

open WaveTurbulence.Fourier

/-- `ψ₀(v) = χ₀(v - 1/2)`, equal to `1` on `[0, 1]`. -/
@[expose] noncomputable def psi0 (v : ℝ) : ℂ := (chi0 (v - 1 / 2) : ℂ)

/-- `φ(v) = v χ₀(v - 1/2)`, equal to `v` on `[0, 1]`. -/
@[expose] noncomputable def phiM (v : ℝ) : ℂ := (v : ℂ) * psi0 v

theorem contDiff_psi0 : ContDiff ℝ ∞ psi0 :=
  Complex.ofRealCLM.contDiff.comp ((chi0_contDiff (n := ⊤)).comp (contDiff_id.sub contDiff_const))

theorem hasCompactSupport_psi0 : HasCompactSupport psi0 := by
  refine HasCompactSupport.intro (K := Icc (-1 / 2 : ℝ) (3 / 2)) isCompact_Icc fun v hv => ?_
  have : 1 ≤ |v - 1 / 2| := by
    rw [Set.mem_Icc, not_and_or, not_le, not_le] at hv
    rcases hv with h | h
    · rw [abs_of_neg (by linarith)]; linarith
    · rw [abs_of_pos (by linarith)]; linarith
  simp only [psi0]
  rw [chi0_eq_zero this, Complex.ofReal_zero]

theorem psi0_eq_one {v : ℝ} (hv : v ∈ Icc (0 : ℝ) 1) : psi0 v = 1 := by
  have : |v - 1 / 2| ≤ 1 / 2 := by
    rw [abs_le]; constructor <;> linarith [hv.1, hv.2]
  simp only [psi0]
  rw [chi0_eq_one this, Complex.ofReal_one]

theorem contDiff_phiM : ContDiff ℝ ∞ phiM :=
  Complex.ofRealCLM.contDiff.mul contDiff_psi0

theorem hasCompactSupport_phiM : HasCompactSupport phiM :=
  hasCompactSupport_psi0.mul_left

theorem phiM_eq {v : ℝ} (hv : v ∈ Icc (0 : ℝ) 1) : phiM v = v := by
  simp [phiM, psi0_eq_one hv]

/-- The function `M₀` of DH21 (extraid). -/
@[expose] noncomputable def M0 : ℝ → ℂ := ftπ psi0

/-- **DH21 (extraid)** (L1037): `e^{πiμs} = ∫ M₀(σ) e^{πi(μ+σ)s} dσ` for `s ∈ [0, 1]`. -/
theorem extraid (μ : ℝ) {s : ℝ} (hs : s ∈ Icc (0 : ℝ) 1) :
    cexp (π * I * (μ * s)) = ∫ σ, M0 σ * cexp (π * I * ((μ + σ) * s)) := by
  have h := integral_ftπ_mul_exp contDiff_psi0 hasCompactSupport_psi0 s
  rw [psi0_eq_one hs] at h
  have : (fun σ => M0 σ * cexp (π * I * ((μ + σ) * s))) =
      fun σ => cexp (π * I * (μ * s)) * (ftπ psi0 σ * cexp (π * I * σ * s)) := by
    funext σ
    have e : (π : ℂ) * I * ((μ + σ) * s) = π * I * (μ * s) + π * I * σ * s := by ring
    rw [M0, e, Complex.exp_add]
    ring
  rw [this, integral_const_mul, h, mul_one]

theorem exists_M0_bound : ∃ K : ℝ, 0 ≤ K ∧ ∀ σ, ‖M0 σ‖ ≤ K / (1 + |σ|) ^ 3 := by
  obtain ⟨K, B, hK, _, h⟩ := exists_norm_iteratedDeriv_ftπ_le contDiff_psi0 hasCompactSupport_psi0
  exact ⟨K, hK, fun σ => by simpa [M0] using h 0 σ⟩

theorem integrable_M0 : Integrable M0 := integrable_ftπ contDiff_psi0 hasCompactSupport_psi0

theorem continuous_M0 : Continuous M0 := (contDiff_ftπ contDiff_psi0 hasCompactSupport_psi0).continuous

/-- The `χ₀` kernel `kerM x (σ, τ) = χ₀(x) ftπ φ(σ - τx) 1_{[0,1]}(τ)`. -/
@[expose] noncomputable def kerM (x : ℝ) (q : ℝ × ℝ) : ℂ :=
  (chi0 x : ℂ) * ftπ phiM (q.1 - q.2 * x) * (Icc (0 : ℝ) 1).indicator (fun _ => (1 : ℂ)) q.2

theorem continuous_ftπ_phiM : Continuous (ftπ phiM) :=
  (contDiff_ftπ contDiff_phiM hasCompactSupport_phiM).continuous

theorem measurable_kerM : Measurable (Function.uncurry kerM) := by
  have h1 : Continuous fun p : ℝ × (ℝ × ℝ) => (chi0 p.1 : ℂ) * ftπ phiM (p.2.1 - p.2.2 * p.1) :=
    (Complex.continuous_ofReal.comp ((chi0_contDiff (n := 0)).continuous.comp continuous_fst)).mul
      (continuous_ftπ_phiM.comp ((continuous_fst.comp continuous_snd).sub
        ((continuous_snd.comp continuous_snd).mul continuous_fst)))
  have h2 : Measurable fun p : ℝ × (ℝ × ℝ) =>
      (Icc (0 : ℝ) 1).indicator (fun _ => (1 : ℂ)) p.2.2 :=
    (measurable_const.indicator measurableSet_Icc).comp (measurable_snd.comp measurable_snd)
  exact h1.measurable.mul h2

theorem contDiff_kerM (q : ℝ × ℝ) : ContDiff ℝ ∞ fun x => kerM x q := by
  unfold kerM
  refine ContDiff.mul (ContDiff.mul (Complex.ofRealCLM.contDiff.comp (chi0_contDiff (n := ⊤)))
    ((contDiff_ftπ contDiff_phiM hasCompactSupport_phiM).comp
      (contDiff_const.sub (contDiff_const.mul contDiff_id)))) contDiff_const

theorem norm_kerM_le (x : ℝ) (q : ℝ × ℝ) :
    ‖kerM x q‖ ≤ (Icc (0 : ℝ) 1).indicator (fun _ => (1 : ℝ)) q.2 * ‖ftπ phiM (q.1 - q.2 * x)‖ := by
  unfold kerM
  rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (chi0_nonneg x)]
  by_cases hq : q.2 ∈ Icc (0 : ℝ) 1
  · simp only [Set.indicator_of_mem hq, norm_one, mul_one, one_mul]
    exact mul_le_of_le_one_left (norm_nonneg _) (chi0_le_one x)
  · simp [Set.indicator_of_notMem hq]

/-- The `χ₀` kernel is integrable in `(σ, τ)` for every `x`. -/
theorem integrable_kerM_mul (x : ℝ) {φ : ℝ × ℝ → ℂ} (hφ : AEStronglyMeasurable φ)
    (hφ1 : ∀ q, ‖φ q‖ ≤ 1) : Integrable fun q => kerM x q * φ q := by
  have hb : Measurable fun τ : ℝ => τ * x := measurable_id.mul measurable_const
  have hH : Integrable fun p : ℝ × ℝ =>
      ‖ftπ phiM p.1‖ * (Icc (0 : ℝ) 1).indicator (fun _ => (1 : ℝ)) p.2 := by
    rw [Measure.volume_eq_prod]
    refine (integrable_ftπ contDiff_phiM hasCompactSupport_phiM).norm.mul_prod ?_
    exact (integrable_indicator_iff measurableSet_Icc).2 (integrableOn_const (by simp))
  have hH' : Integrable fun p : ℝ × ℝ =>
      ‖ftπ phiM (p.1 - p.2 * x)‖ * (Icc (0 : ℝ) 1).indicator (fun _ => (1 : ℝ)) p.2 := by
    have := ((measurePreserving_shiftEquiv (fun τ : ℝ => τ * x) hb).symm
      (shiftEquiv (fun τ : ℝ => τ * x) hb)).integrable_comp_emb
      (shiftEquiv (fun τ : ℝ => τ * x) hb).symm.measurableEmbedding
      (g := fun p : ℝ × ℝ => ‖ftπ phiM p.1‖ * (Icc (0 : ℝ) 1).indicator (fun _ => (1 : ℝ)) p.2)
    exact this.2 hH
  refine hH'.mono' ((measurable_kerM.comp measurable_prodMk_left).aestronglyMeasurable.mul hφ)
    (Eventually.of_forall fun q => ?_)
  rw [norm_mul]
  calc ‖kerM x q‖ * ‖φ q‖ ≤ ‖kerM x q‖ * 1 := mul_le_mul_of_nonneg_left (hφ1 q) (norm_nonneg _)
    _ ≤ _ := by rw [mul_one, mul_comm]; exact norm_kerM_le x q

/-- **The `χ₀` part of `∫_0^v e^{πixu} du`** (DH21 L976–L978). -/
theorem integral_kerM_mul_exp (x : ℝ) {v : ℝ} (hv : v ∈ Icc (0 : ℝ) 1) :
    ∫ q : ℝ × ℝ, kerM x q * cexp (π * I * (q.1 * v)) = (chi0 x : ℂ) * eInt x v := by
  have hcont : Continuous fun q : ℝ × ℝ => cexp (π * I * (q.1 * v)) := by fun_prop
  have hint := integrable_kerM_mul x hcont.aestronglyMeasurable (fun q => by
    rw [Complex.norm_exp]; simp)
  rw [Measure.volume_eq_prod, integral_prod_symm _ hint]
  have hinner : ∀ τ : ℝ, ∫ σ, kerM x (σ, τ) * cexp (π * I * (σ * v)) =
      (Icc (0 : ℝ) 1).indicator (fun τ => (chi0 x : ℂ) * (v * cexp (π * I * (x * v * τ)))) τ := by
    intro τ
    by_cases hτ : τ ∈ Icc (0 : ℝ) 1
    · rw [Set.indicator_of_mem hτ]
      have h1 : (fun σ => kerM x (σ, τ) * cexp (π * I * (σ * v))) = fun σ =>
          (chi0 x : ℂ) * ((fun σ' => ftπ phiM σ' * cexp (π * I * ((σ' + τ * x) * v)))
            (σ - τ * x)) := by
        funext σ
        simp only [kerM, Set.indicator_of_mem hτ, mul_one]
        push_cast
        ring_nf
      rw [h1, integral_const_mul, integral_sub_right_eq_self
        (fun σ' => ftπ phiM σ' * cexp (π * I * ((σ' + τ * x) * v))) (τ * x)]
      have h2 : (fun σ' => ftπ phiM σ' * cexp (π * I * ((σ' + τ * x) * v))) = fun σ' =>
          cexp (π * I * (x * v * τ)) * (ftπ phiM σ' * cexp (π * I * σ' * v)) := by
        funext σ'
        have e : (π : ℂ) * I * ((σ' + τ * x) * v) = π * I * (x * v * τ) + π * I * σ' * v := by
          ring
        rw [e, Complex.exp_add]
        ring
      rw [h2, integral_const_mul, integral_ftπ_mul_exp contDiff_phiM hasCompactSupport_phiM,
        phiM_eq hv]
      ring
    · rw [Set.indicator_of_notMem hτ]
      simp [kerM, Set.indicator_of_notMem hτ]
  simp_rw [hinner]
  rw [integral_indicator measurableSet_Icc, integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le zero_le_one, intervalIntegral.integral_const_mul]
  congr 1
  rw [eInt]
  have := intervalIntegral.smul_integral_comp_mul_left (a := 0) (b := 1)
    (fun u : ℝ => cexp (π * I * (x * u))) v
  simp only [mul_zero, mul_one, Complex.real_smul] at this
  rw [← this, ← intervalIntegral.integral_const_mul]
  refine intervalIntegral.integral_congr fun τ _ => ?_
  congr 2
  push_cast
  ring

end WaveTurbulence.ClassJR
