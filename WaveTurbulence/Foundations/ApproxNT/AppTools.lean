/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.ApproxNT.DeltaCell
public import WaveTurbulence.Foundations.ApproxNT.Profile

/-!
# Tools for the approximation `I_app` (packet NT6)

* A Hölder bound at the origin for `Ψ̂₁`, from the second half of DH23 (propertypsi2):
  `|Ψ̂₁(w) - Ψ̂₁(0)| ≤ 4π (∑ᵢ |wᵢ|^θ) ‖max_i ⟨Ωᵢ⟩^θ Ψ₁‖_{L¹}`, `θ = 1 - η/2`.
* For a kernel `k(u) = ∫ k̂(t) e(tu) dt`, `∫∫ k(μ⟨x,y⟩) P = ∫ k̂(t) cellInt(μt) dt`.
* The `J`-factor: with the truncated kernel `m_K`, `∫ m̂_K(t) cellInt(μt) dt = μ⁻¹ pvTrunc_μ(P)`.
-/

public section

noncomputable section

open MeasureTheory Finset WithLp Filter Topology
open scoped ContDiff FourierTransform SchwartzMap ENNReal

namespace WaveTurbulence.ApproxNT

variable {d : ℕ}

theorem norm_le_of_thetaMom_ne_zero' {x p : Mom d} (h : thetaMom d (x - p) ≠ 0) :
    ‖x‖ ≤ ‖p‖ + Real.sqrt d := by
  have h1 := thetaMom_support_subset (d := d) h
  rw [Metric.mem_closedBall, dist_zero_right] at h1
  calc ‖x‖ = ‖(x - p) + p‖ := by rw [sub_add_cancel]
    _ ≤ ‖x - p‖ + ‖p‖ := norm_add_le _ _
    _ ≤ _ := by linarith

theorem min_le_rpow_mul_rpow {a b θ : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1) :
    min a b ≤ a ^ (1 - θ) * b ^ θ := by
  rcases le_total a b with h | h
  · rw [min_eq_left h]
    calc a = a ^ (1 - θ) * a ^ θ := by
          rcases eq_or_lt_of_le ha with h0 | h0
          · subst h0
            rcases eq_or_lt_of_le hθ0 with hθ | hθ
            · subst hθ; simp
            · rw [Real.zero_rpow hθ.ne', mul_zero]
          · rw [← Real.rpow_add h0]; simp
      _ ≤ a ^ (1 - θ) * b ^ θ :=
          mul_le_mul_of_nonneg_left (Real.rpow_le_rpow ha h hθ0) (Real.rpow_nonneg ha _)
  · rw [min_eq_right h]
    calc b = b ^ (1 - θ) * b ^ θ := by
          rcases eq_or_lt_of_le hb with h0 | h0
          · subst h0
            rcases eq_or_lt_of_le hθ0 with hθ | hθ
            · subst hθ; simp
            · rw [Real.zero_rpow hθ.ne', mul_zero]
          · rw [← Real.rpow_add h0]; simp
      _ ≤ a ^ (1 - θ) * b ^ θ :=
          mul_le_mul_of_nonneg_right (Real.rpow_le_rpow hb h (by linarith)) (Real.rpow_nonneg hb _)

theorem norm_fourierChar_sub_one_le_rpow {θ : ℝ} (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1) (t : ℝ) :
    ‖(𝐞 t : ℂ) - 1‖ ≤ 4 * Real.pi * |t| ^ θ := by
  have h1 : ‖(𝐞 t : ℂ) - 1‖ ≤ 2 := by
    refine (norm_sub_le _ _).trans ?_
    simp; norm_num
  have h2 : ‖(𝐞 t : ℂ) - 1‖ ≤ 2 * Real.pi * |t| := by
    have := NTSP.norm_fourierChar_sub_le t 0
    simpa using this
  have hpi : (1 : ℝ) ≤ 2 * Real.pi := by nlinarith [Real.pi_gt_three]
  calc ‖(𝐞 t : ℂ) - 1‖ ≤ min 2 (2 * Real.pi * |t|) := le_min h1 h2
    _ ≤ 2 ^ (1 - θ) * (2 * Real.pi * |t|) ^ θ :=
        min_le_rpow_mul_rpow (by norm_num) (by positivity) hθ0 hθ1
    _ = 2 ^ (1 - θ) * (2 * Real.pi) ^ θ * |t| ^ θ := by
        rw [Real.mul_rpow (by positivity) (abs_nonneg _)]; ring
    _ ≤ 2 * (2 * Real.pi) * |t| ^ θ := by
        have e1 : (2 : ℝ) ^ (1 - θ) ≤ 2 := by
          simpa using Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2)
            (by linarith : 1 - θ ≤ 1)
        have e2 : (2 * Real.pi) ^ θ ≤ 2 * Real.pi := by
          simpa using Real.rpow_le_rpow_of_exponent_le hpi hθ1
        have e3 : 0 ≤ |t| ^ θ := Real.rpow_nonneg (abs_nonneg _) _
        have e4 : 0 ≤ (2 * Real.pi) ^ θ := Real.rpow_nonneg (by positivity) _
        gcongr
    _ = 4 * Real.pi * |t| ^ θ := by ring

theorem sum_rpow_le {ι : Type*} (s : Finset ι) {a : ι → ℝ} (ha : ∀ i, 0 ≤ a i) {θ : ℝ}
    (hθ0 : 0 < θ) (hθ1 : θ ≤ 1) : (∑ i ∈ s, a i) ^ θ ≤ ∑ i ∈ s, a i ^ θ := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [Real.zero_rpow hθ0.ne']
  | insert j s hj ih =>
      rw [sum_insert hj, sum_insert hj]
      exact (Real.rpow_add_le_add_rpow (ha j) (sum_nonneg fun i _ => ha i) hθ0.le hθ1).trans
        (add_le_add le_rfl ih)

variable {κ : Type} [Fintype κ]

/-- The weight `max_i ⟨Ω_i⟩^θ` of DH23 (propertypsi2). -/
@[expose] def wmax (θ : ℝ) (Ω : κ → ℝ) : ℝ := ⨆ i, Real.sqrt (1 + Ω i ^ 2) ^ θ

theorem le_wmax {θ : ℝ} (hθ : 0 ≤ θ) (Ω : κ → ℝ) (i : κ) : |Ω i| ^ θ ≤ wmax θ Ω := by
  refine le_trans ?_ (le_ciSup (Set.finite_range _).bddAbove i)
  refine Real.rpow_le_rpow (abs_nonneg _) ?_ hθ
  rw [Real.le_sqrt (abs_nonneg _) (by positivity), sq_abs]
  linarith

/-- A Hölder bound at the origin for the Fourier transform. -/
theorem norm_fourier_sub_fourier_zero_le {f : EuclideanSpace ℝ κ → ℂ} (hfi : Integrable f)
    {θ : ℝ} (hθ0 : 0 < θ) (hθ1 : θ ≤ 1) {H : ℝ} (hH0 : 0 ≤ H)
    (hH : ∫⁻ Ω, ENNReal.ofReal (wmax θ (fun i => Ω i)) * ‖f Ω‖ₑ ≤ ENNReal.ofReal H)
    (w : EuclideanSpace ℝ κ) :
    ‖𝓕 f w - 𝓕 f 0‖ ≤ 4 * Real.pi * (∑ i, |w i| ^ θ) * H := by
  have hint : ∀ v : EuclideanSpace ℝ κ, Integrable (fun Ω => 𝐞 (-inner ℝ Ω v) • f Ω) := by
    intro v
    refine hfi.norm.mono' ?_ (Filter.Eventually.of_forall fun Ω => by rw [Circle.norm_smul])
    exact ((Real.continuous_fourierChar.comp
      (continuous_id.inner continuous_const).neg).aestronglyMeasurable).smul hfi.aestronglyMeasurable
  rw [Real.fourier_eq, Real.fourier_eq, ← integral_sub (hint w) (hint 0)]
  have hS : 0 ≤ 4 * Real.pi * ∑ i, |w i| ^ θ :=
    mul_nonneg (by positivity) (sum_nonneg fun i _ => Real.rpow_nonneg (abs_nonneg _) _)
  have hpt : ∀ Ω : EuclideanSpace ℝ κ, ‖𝐞 (-inner ℝ Ω w) • f Ω -
      𝐞 (-inner ℝ Ω (0 : EuclideanSpace ℝ κ)) • f Ω‖ₑ ≤
      ENNReal.ofReal (4 * Real.pi * ∑ i, |w i| ^ θ) *
        (ENNReal.ofReal (wmax θ (fun i => Ω i)) * ‖f Ω‖ₑ) := by
    intro Ω
    simp only [inner_zero_right, neg_zero, AddChar.map_zero_eq_one, one_smul]
    rw [Circle.smul_def, smul_eq_mul, ← sub_one_mul, enorm_mul, ← mul_assoc,
      ← ENNReal.ofReal_mul hS]
    refine mul_le_mul_of_nonneg_right ?_ zero_le
    rw [← ofReal_norm]
    refine ENNReal.ofReal_le_ofReal ?_
    have h1 : |inner ℝ Ω w| ≤ ∑ i, |Ω i| * |w i| := by
      rw [PiLp.inner_apply]
      refine (abs_sum_le_sum_abs _ _).trans (le_of_eq (sum_congr rfl fun i _ => ?_))
      simp [abs_mul, mul_comm]
    have hkey : |inner ℝ Ω w| ^ θ ≤ (∑ i, |w i| ^ θ) * wmax θ (fun i => Ω i) := by
      calc |inner ℝ Ω w| ^ θ ≤ (∑ i, |Ω i| * |w i|) ^ θ :=
            Real.rpow_le_rpow (abs_nonneg _) h1 hθ0.le
        _ ≤ ∑ i, (|Ω i| * |w i|) ^ θ :=
            sum_rpow_le _ (fun i => mul_nonneg (abs_nonneg _) (abs_nonneg _)) hθ0 hθ1
        _ ≤ ∑ i, wmax θ (fun i => Ω i) * |w i| ^ θ := by
            refine sum_le_sum fun i _ => ?_
            rw [Real.mul_rpow (abs_nonneg _) (abs_nonneg _)]
            exact mul_le_mul_of_nonneg_right (le_wmax hθ0.le (fun i => Ω i) i)
              (Real.rpow_nonneg (abs_nonneg _) _)
        _ = (∑ i, |w i| ^ θ) * wmax θ (fun i => Ω i) := by rw [← mul_sum]; ring
    calc ‖(𝐞 (-inner ℝ Ω w) : ℂ) - 1‖ ≤ 4 * Real.pi * |-inner ℝ Ω w| ^ θ :=
          norm_fourierChar_sub_one_le_rpow hθ0.le hθ1 _
      _ = 4 * Real.pi * |inner ℝ Ω w| ^ θ := by rw [abs_neg]
      _ ≤ 4 * Real.pi * ((∑ i, |w i| ^ θ) * wmax θ (fun i => Ω i)) :=
          mul_le_mul_of_nonneg_left hkey (by positivity)
      _ = 4 * Real.pi * (∑ i, |w i| ^ θ) * wmax θ (fun i => Ω i) := by ring
  have hle1 := enorm_integral_le_lintegral_enorm (μ := (volume : Measure (EuclideanSpace ℝ κ)))
    (fun Ω : EuclideanSpace ℝ κ => 𝐞 (-inner ℝ Ω w) • f Ω -
      𝐞 (-inner ℝ Ω (0 : EuclideanSpace ℝ κ)) • f Ω)
  have hle2 := lintegral_mono (μ := (volume : Measure (EuclideanSpace ℝ κ))) hpt
  rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top] at hle2
  have hle3 := hle1.trans (hle2.trans (mul_le_mul_of_nonneg_left hH zero_le))
  rw [← ENNReal.ofReal_mul hS, ← ofReal_norm] at hle3
  exact (ENNReal.ofReal_le_ofReal_iff (mul_nonneg hS hH0)).1 hle3

/-- For a kernel with a Fourier representation, `∫∫ k(μ⟨x,y⟩) P = ∫ k̂(t) cellInt(μt) dt`. -/
theorem integral_kernel_cellFn {k kh : ℝ → ℂ} (hkh : Integrable kh) (hkhc : Continuous kh)
    (hk : ∀ u, k u = ∫ t, kh t * (𝐞 (t * u) : ℂ)) (hkc : Continuous k) (μ : ℝ) (p q ξ η : Mom d) :
    ∫ x, ∫ y, k (μ * inner ℝ x y) * cellFn p q ξ η x y = ∫ t, kh t * cellInt p q ξ η (μ * t) := by
  have hGc : Continuous (Function.uncurry fun x y : Mom d => k (μ * inner ℝ x y)) :=
    hkc.comp (continuous_const.mul (continuous_fst.inner continuous_snd))
  rw [integral_cellFn_prod p q ξ η hGc]
  have hjoint : Integrable (Function.uncurry fun (z : Mom d × Mom d) (τ : ℝ) =>
      kh τ * ((𝐞 (τ * (μ * inner ℝ z.1 z.2)) : ℂ) * cellFn p q ξ η z.1 z.2))
      ((volume : Measure (Mom d × Mom d)).prod volume) := by
    have hp := (integrable_cellAmp p q).mul_prod hkh
    refine hp.norm.mono' ?_ (Filter.Eventually.of_forall fun w => ?_)
    · refine Continuous.aestronglyMeasurable ?_
      refine (hkhc.comp continuous_snd).mul (Continuous.mul ?_ ?_)
      · exact (continuous_subtype_val.comp Real.continuous_fourierChar).comp
          (continuous_snd.mul (continuous_const.mul
            ((continuous_fst.comp continuous_fst).inner (continuous_snd.comp continuous_fst))))
      · exact ((contDiff_cellIntegrand p q ξ η 0).continuous.congr (fun z => by
          simp [pairAmp])).comp continuous_fst
    · obtain ⟨z, τ⟩ := w
      simp only [Function.uncurry_apply_pair, norm_mul, cellFn, pairAmp, Circle.norm_smul,
        Circle.norm_coe, one_mul]
      rw [mul_comm]
  calc ∫ z : Mom d × Mom d, k (μ * inner ℝ z.1 z.2) * cellFn p q ξ η z.1 z.2
      = ∫ z : Mom d × Mom d, ∫ τ, kh τ *
          ((𝐞 (τ * (μ * inner ℝ z.1 z.2)) : ℂ) * cellFn p q ξ η z.1 z.2) := by
        refine integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
        simp only
        rw [hk, ← integral_mul_const]
        refine integral_congr_ae (Filter.Eventually.of_forall fun τ => ?_)
        simp only; ring
    _ = ∫ τ, ∫ z : Mom d × Mom d, kh τ *
          ((𝐞 (τ * (μ * inner ℝ z.1 z.2)) : ℂ) * cellFn p q ξ η z.1 z.2) :=
        integral_integral_swap hjoint
    _ = ∫ τ, kh τ * cellInt p q ξ η (μ * τ) := by
        refine integral_congr_ae (Filter.Eventually.of_forall fun τ => ?_)
        simp only
        rw [integral_const_mul, cellInt_eq_prod]
        congr 1
        refine integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
        simp only [cellFn, pairAmp, Circle.smul_def, smul_eq_mul]
        rw [← mul_assoc, ← Circle.coe_mul, ← AddChar.map_add_eq_mul]
        congr 3
        ring

theorem continuous_mKer (K : ℕ) : Continuous (mKer K) :=
  continuous_finsetSum _ fun _ _ => continuous_const.mul
    (psiS.continuous.comp (continuous_id.div_const _))

theorem pvTrunc_eq_integral (ν : ℝ) (F : Mom d → Mom d → ℂ) :
    pvTrunc ν F = ∫ x, ∫ y, (((1 - Fourier.chi0 (ν * inner ℝ x y)) / inner ℝ x y : ℝ) : ℂ) * F x y := by
  simp only [pvTrunc, Resonant.bilinearFourierTruncation, Resonant.bilinearInvFourierInner,
    inner_zero_left, Resonant.unitPhase, mul_zero, Complex.ofReal_zero, zero_mul, Complex.exp_zero,
    one_mul, mul_one]

/-- The `J`-factor: with the truncated kernel, `∫ m̂_K(t) cellInt(μt) dt = μ⁻¹ pvTrunc_μ(P)`. -/
theorem jfactor_eq {K : ℕ} {μ : ℝ} (hμ : 0 < μ) {p q : Mom d}
    (hK : μ * ((‖p‖ + Real.sqrt d) * (‖q‖ + Real.sqrt d)) ≤ 2 ^ K) (ξ η : Mom d) :
    ∫ t, mKerHat K t * cellInt p q ξ η (μ * t) = (μ⁻¹ : ℂ) * pvTrunc μ (cellFn p q ξ η) := by
  rw [← integral_kernel_cellFn (integrable_mKerHat (d := 1) le_rfl K) (continuous_mKerHat K)
    (mKer_eq_integral K) (continuous_mKer K) μ p q ξ η, pvTrunc_eq_integral, ← integral_const_mul]
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  simp only
  rw [← integral_const_mul]
  refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
  simp only
  by_cases h0 : cellFn p q ξ η x y = 0
  · rw [h0, mul_zero, mul_zero, mul_zero]
  have hxy : thetaMom d (x - p) ≠ 0 ∧ thetaMom d (y - q) ≠ 0 := by
    constructor <;> intro h <;> apply h0 <;> simp [cellFn, pairAmp, cellAmp, thetaC, h]
  have hx := norm_le_of_thetaMom_ne_zero' hxy.1
  have hy := norm_le_of_thetaMom_ne_zero' hxy.2
  have hbd : |μ * inner ℝ x y| ≤ 2 ^ K := by
    calc |μ * inner ℝ x y| = μ * |inner ℝ x y| := by rw [abs_mul, abs_of_pos hμ]
      _ ≤ μ * (‖x‖ * ‖y‖) := mul_le_mul_of_nonneg_left (abs_real_inner_le_norm _ _) hμ.le
      _ ≤ μ * ((‖p‖ + Real.sqrt d) * (‖q‖ + Real.sqrt d)) :=
          mul_le_mul_of_nonneg_left (mul_le_mul hx hy (norm_nonneg _) (by positivity)) hμ.le
      _ ≤ 2 ^ K := hK
  rw [mKer_eq hbd, ← mul_assoc]
  congr 1
  rw [← Complex.ofReal_inv, ← Complex.ofReal_mul]
  congr 1
  rw [Fourier.chiInfinity]
  by_cases hΩ : inner ℝ x y = 0
  · simp [hΩ]
  · field_simp

end WaveTurbulence.ApproxNT
