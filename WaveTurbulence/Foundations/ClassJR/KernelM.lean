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

/-- Derivatives of `y ↦ f(σ - τ y)` for `|τ| ≤ 1`. -/
theorem norm_iteratedDeriv_comp_affine_le {f : ℝ → ℂ} (hf : ContDiff ℝ ∞ f) {τ : ℝ}
    (hτ : |τ| ≤ 1) (σ x : ℝ) (m : ℕ) :
    ‖iteratedDeriv m (fun y => f (σ - τ * y)) x‖ ≤ ‖iteratedDeriv m f (σ - τ * x)‖ := by
  have hL : ‖(-τ) • ContinuousLinearMap.id ℝ ℝ‖ ≤ 1 := by
    rw [norm_smul, norm_neg, Real.norm_eq_abs]
    exact (mul_le_of_le_one_right (abs_nonneg _) ContinuousLinearMap.norm_id_le).trans hτ
  have h := enorm_iteratedFDeriv_scalar_le hf ((-τ) • ContinuousLinearMap.id ℝ ℝ) hL σ x m
  simp only [smul_apply, ContinuousLinearMap.id_apply, smul_eq_mul] at h
  have e : (fun y => f (σ - τ * y)) = fun y => f (-τ * y + σ) := by
    funext y; congr 1; ring
  rw [e, show σ - τ * x = -τ * x + σ by ring, ← norm_iteratedFDeriv_eq_norm_iteratedDeriv]
  exact enorm_le_iff_norm_le.1 h

theorem norm_iteratedDeriv_chi0c_le (j : ℕ) (x : ℝ) :
    ‖iteratedDeriv j (fun y => (chi0 y : ℂ)) x‖ ≤
      Real.exp 4 * Achi ^ j * (Nat.factorial (2 * j) : ℝ) := by
  rw [norm_iteratedDeriv_ofReal (chi0_contDiff (n := ⊤)), Real.norm_eq_abs]
  exact chi0_gevreyTwoBound j x

theorem iteratedDeriv_chi0c_eq_zero {x : ℝ} (hx : 1 < |x|) (j : ℕ) :
    iteratedDeriv j (fun y => (chi0 y : ℂ)) x = 0 :=
  iteratedDeriv_eq_zero_of_eventuallyEq_zero (by
    filter_upwards [chi0_eventually_zero hx] with y hy
    simp [hy]) j

/-- **Derivative bounds for the `χ₀` kernel.** -/
theorem exists_kerM_bound : ∃ C A : ℝ, 0 ≤ C ∧ 0 ≤ A ∧ ∀ (c : ℕ) (x : ℝ) (q : ℝ × ℝ),
    ‖iteratedDeriv c (fun x => kerM x q) x‖ ≤
      (Icc (0 : ℝ) 1).indicator (fun _ => (1 : ℝ)) q.2 *
        (C * A ^ c * (Nat.factorial (2 * c) : ℝ)) / (1 + |q.1|) ^ 3 := by
  obtain ⟨K, B, hK, hB, hF⟩ := exists_norm_iteratedDeriv_ftπ_le contDiff_phiM hasCompactSupport_phiM
  set A := max Achi B
  have hA : 0 ≤ A := le_max_of_le_left Achi_nonneg
  have hFc : ContDiff ℝ ∞ (ftπ phiM) := contDiff_ftπ contDiff_phiM hasCompactSupport_phiM
  refine ⟨32 * Real.exp 4 * K, A, by positivity, hA, fun c x q => ?_⟩
  obtain ⟨σ, τ⟩ := q
  by_cases hτ : τ ∈ Icc (0 : ℝ) 1
  · simp only [Set.indicator_of_mem hτ, one_mul]
    have hτ1 : |τ| ≤ 1 := by rw [abs_le]; constructor <;> linarith [hτ.1, hτ.2]
    have hfun : (fun x => kerM x (σ, τ)) =
        (fun y => (chi0 y : ℂ)) * fun y => ftπ phiM (σ - τ * y) := by
      funext y
      simp [kerM, Set.indicator_of_mem hτ]
    have hc1 : ContDiff ℝ ∞ (fun y => (chi0 y : ℂ)) :=
      Complex.ofRealCLM.contDiff.comp (chi0_contDiff (n := ⊤))
    have hc2 : ContDiff ℝ ∞ (fun y => ftπ phiM (σ - τ * y)) :=
      hFc.comp (contDiff_const.sub (contDiff_const.mul contDiff_id))
    rw [hfun, iteratedDeriv_mul (hc1.of_le (by simp)).contDiffAt (hc2.of_le (by simp)).contDiffAt]
    have hpos : 0 < (1 + |σ|) ^ 3 := by positivity
    by_cases hx : 1 < |x|
    · simp only [iteratedDeriv_chi0c_eq_zero hx, mul_zero, zero_mul, Finset.sum_const_zero,
        norm_zero]
      positivity
    · push Not at hx
      have hdecay : ∀ m : ℕ, ‖iteratedDeriv m (fun y => ftπ phiM (σ - τ * y)) x‖ ≤
          8 * K * B ^ m / (1 + |σ|) ^ 3 := fun m => by
        refine (norm_iteratedDeriv_comp_affine_le hFc hτ1 σ x m).trans ((hF m _).trans ?_)
        have h1 : 1 + |σ| ≤ 2 * (1 + |σ - τ * x|) := by
          have : |σ| ≤ |σ - τ * x| + |τ * x| := by
            calc |σ| = |(σ - τ * x) + τ * x| := by ring_nf
              _ ≤ _ := abs_add_le _ _
          have h2 : |τ * x| ≤ 1 := by
            rw [abs_mul]; exact (mul_le_mul hτ1 hx (abs_nonneg _) zero_le_one).trans_eq (one_mul 1)
          linarith [abs_nonneg (σ - τ * x)]
        have h3 : (1 + |σ|) ^ 3 ≤ 8 * (1 + |σ - τ * x|) ^ 3 := by
          calc (1 + |σ|) ^ 3 ≤ (2 * (1 + |σ - τ * x|)) ^ 3 := by gcongr
            _ = 8 * (1 + |σ - τ * x|) ^ 3 := by ring
        rw [div_le_div_iff₀ (by positivity) hpos]
        calc K * B ^ m * (1 + |σ|) ^ 3 ≤ K * B ^ m * (8 * (1 + |σ - τ * x|) ^ 3) := by gcongr
          _ = 8 * K * B ^ m * (1 + |σ - τ * x|) ^ 3 := by ring
      calc ‖∑ i ∈ Finset.range (c + 1), (c.choose i : ℂ) * iteratedDeriv i (fun y => (chi0 y : ℂ)) x *
            iteratedDeriv (c - i) (fun y => ftπ phiM (σ - τ * y)) x‖
          ≤ ∑ i ∈ Finset.range (c + 1), (c.choose i : ℝ) *
              (Real.exp 4 * A ^ i * (Nat.factorial (2 * i) : ℝ)) *
              (8 * K * (A ^ (c - i) * (Nat.factorial (2 * (c - i)) : ℝ)) / (1 + |σ|) ^ 3) := by
            refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => ?_)
            rw [norm_mul, norm_mul, Complex.norm_natCast]
            have h1 := norm_iteratedDeriv_chi0c_le i x
            have h1' : Real.exp 4 * Achi ^ i * (Nat.factorial (2 * i) : ℝ) ≤
                Real.exp 4 * A ^ i * (Nat.factorial (2 * i) : ℝ) := by
              gcongr
              · exact Achi_nonneg
              · exact le_max_left _ _
            have h2 := hdecay (c - i)
            have h2' : 8 * K * B ^ (c - i) / (1 + |σ|) ^ 3 ≤
                8 * K * (A ^ (c - i) * (Nat.factorial (2 * (c - i)) : ℝ)) / (1 + |σ|) ^ 3 := by
              gcongr
              calc B ^ (c - i) ≤ A ^ (c - i) := pow_le_pow_left₀ hB (le_max_right _ _) _
                _ = A ^ (c - i) * 1 := (mul_one _).symm
                _ ≤ _ := by gcongr; exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Nat.factorial_ne_zero _)
            gcongr
            · exact h1.trans h1'
            · exact h2.trans h2'
        _ = 8 * Real.exp 4 * K * A ^ c / (1 + |σ|) ^ 3 * ∑ i ∈ Finset.range (c + 1),
              ((c.choose i : ℝ) * (Nat.factorial (2 * i) : ℝ) *
                (Nat.factorial (2 * (c - i)) : ℝ)) := by
            rw [Finset.mul_sum]
            refine Finset.sum_congr rfl fun i hi => ?_
            have hic : i ≤ c := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
            have : A ^ c = A ^ i * A ^ (c - i) := by rw [← pow_add, Nat.add_sub_cancel' hic]
            rw [this]
            field_simp
        _ ≤ 8 * Real.exp 4 * K * A ^ c / (1 + |σ|) ^ 3 * (4 * (Nat.factorial (2 * c) : ℝ)) := by
            gcongr
            exact Combinatorics.sum_choose_factorial_le c
        _ = 32 * Real.exp 4 * K * A ^ c * (Nat.factorial (2 * c) : ℝ) / (1 + |σ|) ^ 3 := by ring
  · have : (fun x => kerM x (σ, τ)) = fun _ => 0 := by
      funext y
      simp [kerM, Set.indicator_of_notMem hτ]
    rw [this, iteratedDeriv_eq_zero_of_eventuallyEq_zero (Eventually.of_forall fun _ => rfl) c]
    simp only [norm_zero, Set.indicator_of_notMem hτ, zero_mul, zero_div, le_refl]

end WaveTurbulence.ClassJR
