/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Flower.Stage1WNoVine.Jets
public import WaveTurbulence.Foundations.Stage1.Represents.RepSup1
public import WaveTurbulence.Foundations.Spine.WeightedSmoothMultiplier
public import WaveTurbulence.Foundations.VineEst.VineEstS3.SNormAux
public import WaveTurbulence.Foundations.Stage1.RepAnalytic.CentreAux

/-! # STAGE1W-O4: the SNorm multiplier lemma and superposition transports (row O4c)

* `snorm_value_mul_le`: a Fourier-presented weight `g = M.value` with `J`-th moment mass `≤ c` is a bounded multiplier
  on `𝔖^{A,0}`, `A ≤ J`: `SNorm A 0 (g a) ≤ 2^A d^A (2π)^A c · SNorm A 0 a`.
* `CenSup.mul_left`, `Sup.mul_left`: a superposition times a bounded multiplier of the momentum.
* `CenSup.update0`, `Sup.update0`: freezing the first time coordinate at a constant (the clamp used at slots whose
  root is a garden root). -/

@[expose] public section
set_option autoImplicit false
noncomputable section
open MeasureTheory Real
open scoped ENNReal NNReal

namespace WaveTurbulence.Flower.Stage1WNoVine
open WaveTurbulence WaveTurbulence.Represents WaveTurbulence.VineEstS3.FS

variable {d : ℕ}

/-- The multiplier constant of a weight with moment mass `c`. -/
def multC (d A : ℕ) (c : ℝ) : ℝ := 2 ^ A * (d : ℝ) ^ A * ((2 * π) ^ A * c)

theorem multC_pos (d A : ℕ) (hd : 1 ≤ d) {c : ℝ} (hc : 0 < c) : 0 < multC d A c := by
  unfold multC
  have : (0 : ℝ) < d := by exact_mod_cast hd
  positivity

/-- **The SNorm multiplier lemma** for a Fourier-presented weight. -/
theorem snorm_value_mul_le {α : Type*} [MeasurableSpace α] (M : Cut2A.SpatialMeasure (Mom d) α)
    (hd : 1 ≤ d) {J A : ℕ} (hAJ : A ≤ J) {c : ℝ} (hc : 0 < c)
    (hM : ∫⁻ a, ENNReal.ofReal ((1 + ‖M.frequency a‖) ^ J) * ‖M.amplitude a‖ₑ ∂M.μ ≤ ENNReal.ofReal c)
    (a : Mom d → ℂ) (ha : ContDiff ℝ A a) :
    SNorm A 0 (fun k => M.value k * a k) ≤ ENNReal.ofReal (multC d A c) * SNorm A 0 a := by
  by_cases htop : SNorm A 0 a = ⊤
  · rw [htop, ENNReal.mul_top (by simpa using multC_pos d A hd hc)]
    exact le_top
  set CF : ℝ := (SNorm A 0 a).toReal with hCF
  have hF : SNorm A (0 + 0) a ≤ ENNReal.ofReal CF := by
    rw [zero_add, hCF, ENNReal.ofReal_toReal htop]
  have hgd : ContDiff ℝ A M.value := (contDiff_value M hM).of_le (by exact_mod_cast hAJ)
  have hjet : ∀ r ≤ A, ∀ x, ‖iteratedFDeriv ℝ r M.value x‖ ≤ ((2 * π) ^ A * c) * jbr x ^ 0 := by
    intro r hr x
    rw [pow_zero, mul_one]
    refine (norm_iteratedFDeriv_value_le M hc.le hM r (hr.trans hAJ) x).trans ?_
    exact mul_le_mul_of_nonneg_right (pow_le_pow_right₀ (by linarith [pi_gt_three]) hr) hc.le
  have key := LGSpine.SNorm_mul_of_polynomial_jet_bound (A := A) (B := 0) (M := 0) hd M.value a hgd ha
    ((2 * π) ^ A * c) CF (by positivity) ENNReal.toReal_nonneg hjet hF
  refine key.trans (le_of_eq ?_)
  rw [hCF, ← ENNReal.ofReal_toReal htop, ← ENNReal.ofReal_mul (multC_pos d A hd hc).le, ENNReal.toReal_ofReal
    ENNReal.toReal_nonneg]
  unfold multC
  ring_nf

/-- A bounded multiplier of the momentum preserves centred superpositions. -/
theorem CenSup.mul_left {r A : ℕ} {B : Set (Fin r → ℝ)} {f : (Fin r → ℝ) → Mom d → ℂ} {μ : ℝ≥0∞}
    (h : CenSup A B f μ) (c : Mom d → ℂ) (K : ℝ) (hK : 0 < K)
    (hc : ∀ a : Mom d → ℂ, SNorm A 0 a ≤ 1 → SNorm A 0 (fun k => c k * a k) ≤ ENNReal.ofReal K) :
    CenSup A B (fun t k => c k * f t k) (ENNReal.ofReal K * μ) := by
  obtain ⟨Λ, hcnt, w, m, n, a, h1, h2, h3, h4, h5, h6⟩ := h
  refine ⟨Λ, hcnt, fun l => K * w l, m, n, fun l k => (K⁻¹ : ℂ) * (c k * a l k), fun l => ?_, h2.mul_left K,
    fun l => ?_, fun l k hk => ?_, fun t ht k => ?_, ?_⟩
  · exact mul_nonneg hK.le (h1 l)
  · refine (VineEstS3.Eng.SNorm_smul_le A 0 _ _).trans ?_
    have e : ‖(K⁻¹ : ℂ)‖ₑ = ENNReal.ofReal K⁻¹ := by
      rw [← ofReal_norm_eq_enorm, ← Complex.ofReal_inv, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos (inv_pos.mpr hK)]
    rw [e]
    calc ENNReal.ofReal K⁻¹ * SNorm A 0 (fun k => c k * a l k) ≤ ENNReal.ofReal K⁻¹ * ENNReal.ofReal K :=
          mul_le_mul_right (hc _ (h3 l)) _
      _ = 1 := by rw [← ENNReal.ofReal_mul (inv_pos.mpr hK).le, inv_mul_cancel₀ hK.ne', ENNReal.ofReal_one]
  · refine h4 l k ?_
    intro h0
    apply hk
    simp [h0]
  · have hs := (h5 t ht k).mul_left (c k)
    convert hs using 1
    funext l
    have hK' : (K : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hK.ne'
    push_cast
    field_simp
  · have e : ∀ l, ENNReal.ofReal (K * w l) = ENNReal.ofReal K * ENNReal.ofReal (w l) :=
      fun l => ENNReal.ofReal_mul hK.le
    simp_rw [e]
    rw [ENNReal.tsum_mul_left]
    exact mul_le_mul_right h6 _

/-- A bounded multiplier of the momentum preserves superpositions. -/
theorem Sup.mul_left {r A : ℕ} {B : Set (Fin r → ℝ)} {f : (Fin r → ℝ) → Mom d → ℂ} {μ : ℝ≥0∞}
    (h : Sup A B f μ) (c : Mom d → ℂ) (K : ℝ) (hK : 0 < K)
    (hc : ∀ a : Mom d → ℂ, SNorm A 0 a ≤ 1 → SNorm A 0 (fun k => c k * a k) ≤ ENNReal.ofReal K) :
    Sup A B (fun t k => c k * f t k) (ENNReal.ofReal K * μ) := by
  obtain ⟨Λ, hcnt, w, m, a, h1, h2, h3, h5, h6⟩ := h
  refine ⟨Λ, hcnt, fun l => K * w l, m, fun l k => (K⁻¹ : ℂ) * (c k * a l k), fun l => ?_, h2.mul_left K,
    fun l => ?_, fun t ht k => ?_, ?_⟩
  · exact mul_nonneg hK.le (h1 l)
  · refine (VineEstS3.Eng.SNorm_smul_le A 0 _ _).trans ?_
    have e : ‖(K⁻¹ : ℂ)‖ₑ = ENNReal.ofReal K⁻¹ := by
      rw [← ofReal_norm_eq_enorm, ← Complex.ofReal_inv, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos (inv_pos.mpr hK)]
    rw [e]
    calc ENNReal.ofReal K⁻¹ * SNorm A 0 (fun k => c k * a l k) ≤ ENNReal.ofReal K⁻¹ * ENNReal.ofReal K :=
          mul_le_mul_right (hc _ (h3 l)) _
      _ = 1 := by rw [← ENNReal.ofReal_mul (inv_pos.mpr hK).le, inv_mul_cancel₀ hK.ne', ENNReal.ofReal_one]
  · have hs := (h5 t ht k).mul_left (c k)
    convert hs using 1
    funext l
    have hK' : (K : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hK.ne'
    push_cast
    field_simp
  · have e : ∀ l, ENNReal.ofReal (K * w l) = ENNReal.ofReal K * ENNReal.ofReal (w l) :=
      fun l => ENNReal.ofReal_mul hK.le
    simp_rw [e]
    rw [ENNReal.tsum_mul_left]
    exact mul_le_mul_right h6 _

theorem timePairing_two (x y : Fin 2 → ℝ) : Fourier.timePairing 2 x y = x 0 * y 0 + x 1 * y 1 := by
  show dotProduct x y = _
  simp [dotProduct, Fin.sum_univ_two]

/-- The mode at a time vector whose first coordinate is frozen. -/
theorem fsPhase_update0 (m : Fin 2 → ℤ) (t : Fin 2 → ℝ) (c : ℝ) :
    fsPhase m (Function.update t 0 c) =
      (Real.fourierChar (c * ((m 0 : ℝ) / 2)) : ℂ) * fsPhase (Function.update m 0 0) t := by
  unfold fsPhase
  have e1 : Fourier.timePairing 2 (Function.update t 0 c) (fun i => (m i : ℝ) / 2) =
      c * ((m 0 : ℝ) / 2) + Fourier.timePairing 2 t (fun i => ((Function.update m 0 0 i : ℤ) : ℝ) / 2) := by
    rw [timePairing_two, timePairing_two]
    simp
  rw [e1, AddChar.map_add_eq_mul, Circle.coe_mul]

/-- A unimodular amplitude factor. -/
theorem snorm_unit_mul_le {A : ℕ} (u : ℂ) (hu : ‖u‖ = 1) (a : Mom d → ℂ) :
    SNorm A 0 (fun k => u * a k) ≤ SNorm A 0 a := by
  refine (VineEstS3.Eng.SNorm_smul_le A 0 u a).trans ?_
  rw [← ofReal_norm_eq_enorm, hu, ENNReal.ofReal_one, one_mul]

/-- **Freezing the first time coordinate** of a centred superposition. -/
theorem CenSup.update0 {A : ℕ} {B B' : Set (Fin 2 → ℝ)} {f : (Fin 2 → ℝ) → Mom d → ℂ} {μ : ℝ≥0∞}
    (h : CenSup A B f μ) (c : ℝ) (hB : ∀ t ∈ B', Function.update t 0 c ∈ B) :
    CenSup A B' (fun t k => f (Function.update t 0 c) k) μ := by
  obtain ⟨Λ, hcnt, w, m, n, a, h1, h2, h3, h4, h5, h6⟩ := h
  refine ⟨Λ, hcnt, w, fun l => Function.update (m l) 0 0, n,
    fun l k => (Real.fourierChar (c * ((m l 0 : ℝ) / 2)) : ℂ) * a l k, h1, h2, fun l => ?_, fun l k hk => ?_,
    fun t ht k => ?_, h6⟩
  · exact (snorm_unit_mul_le _ (Circle.norm_coe _) _).trans (h3 l)
  · refine h4 l k ?_
    intro h0
    apply hk
    simp [h0]
  · have hs := h5 _ (hB t ht) k
    convert hs using 1
    funext l
    rw [fsPhase_update0]
    ring

/-- **Freezing the first time coordinate** of a superposition. -/
theorem Sup.update0 {A : ℕ} {B B' : Set (Fin 2 → ℝ)} {f : (Fin 2 → ℝ) → Mom d → ℂ} {μ : ℝ≥0∞}
    (h : Sup A B f μ) (c : ℝ) (hB : ∀ t ∈ B', Function.update t 0 c ∈ B) :
    Sup A B' (fun t k => f (Function.update t 0 c) k) μ := by
  obtain ⟨Λ, hcnt, w, m, a, h1, h2, h3, h5, h6⟩ := h
  refine ⟨Λ, hcnt, w, fun l => Function.update (m l) 0 0,
    fun l k => (Real.fourierChar (c * ((m l 0 : ℝ) / 2)) : ℂ) * a l k, h1, h2, fun l => ?_,
    fun t ht k => ?_, h6⟩
  · exact (snorm_unit_mul_le _ (Circle.norm_coe _) _).trans (h3 l)
  · have hs := h5 _ (hB t ht) k
    convert hs using 1
    funext l
    rw [fsPhase_update0]
    ring


/-- The mode at a time vector whose second coordinate is frozen. -/
theorem fsPhase_update1 (m : Fin 2 → ℤ) (t : Fin 2 → ℝ) (c : ℝ) :
    fsPhase m (Function.update t 1 c) =
      (Real.fourierChar (c * ((m 1 : ℝ) / 2)) : ℂ) * fsPhase (Function.update m 1 0) t := by
  unfold fsPhase
  have e1 : Fourier.timePairing 2 (Function.update t 1 c) (fun i => (m i : ℝ) / 2) =
      c * ((m 1 : ℝ) / 2) + Fourier.timePairing 2 t (fun i => ((Function.update m 1 0 i : ℤ) : ℝ) / 2) := by
    rw [timePairing_two, timePairing_two]
    simp
    ring
  rw [e1, AddChar.map_add_eq_mul, Circle.coe_mul]

/-- **Freezing the second time coordinate** of a centred superposition. -/
theorem CenSup.update1 {A : ℕ} {B B' : Set (Fin 2 → ℝ)} {f : (Fin 2 → ℝ) → Mom d → ℂ} {μ : ℝ≥0∞}
    (h : CenSup A B f μ) (c : ℝ) (hB : ∀ t ∈ B', Function.update t 1 c ∈ B) :
    CenSup A B' (fun t k => f (Function.update t 1 c) k) μ := by
  obtain ⟨Λ, hcnt, w, m, n, a, h1, h2, h3, h4, h5, h6⟩ := h
  refine ⟨Λ, hcnt, w, fun l => Function.update (m l) 1 0, n,
    fun l k => (Real.fourierChar (c * ((m l 1 : ℝ) / 2)) : ℂ) * a l k, h1, h2, fun l => ?_, fun l k hk => ?_,
    fun t ht k => ?_, h6⟩
  · exact (snorm_unit_mul_le _ (Circle.norm_coe _) _).trans (h3 l)
  · refine h4 l k ?_
    intro h0
    apply hk
    simp [h0]
  · have hs := h5 _ (hB t ht) k
    convert hs using 1
    funext l
    rw [fsPhase_update1]
    ring

/-- Agreement on the box transports a centred superposition. -/
theorem CenSup.congr' {r A : ℕ} {B : Set (Fin r → ℝ)} {f g : (Fin r → ℝ) → Mom d → ℂ} {μ : ℝ≥0∞}
    (h : CenSup A B f μ) (hfg : ∀ t ∈ B, ∀ k, f t k = g t k) : CenSup A B g μ := by
  obtain ⟨Λ, hcnt, w, m, n, a, h1, h2, h3, h4, h5, h6⟩ := h
  exact ⟨Λ, hcnt, w, m, n, a, h1, h2, h3, h4, fun t ht k => (hfg t ht k) ▸ h5 t ht k, h6⟩

/-- Agreement on the box transports a superposition. -/
theorem Sup.congr' {r A : ℕ} {B : Set (Fin r → ℝ)} {f g : (Fin r → ℝ) → Mom d → ℂ} {μ : ℝ≥0∞}
    (h : Sup A B f μ) (hfg : ∀ t ∈ B, ∀ k, f t k = g t k) : Sup A B g μ := by
  obtain ⟨Λ, hcnt, w, m, a, h1, h2, h3, h5, h6⟩ := h
  exact ⟨Λ, hcnt, w, m, a, h1, h2, h3, fun t ht k => (hfg t ht k) ▸ h5 t ht k, h6⟩

end WaveTurbulence.Flower.Stage1WNoVine
