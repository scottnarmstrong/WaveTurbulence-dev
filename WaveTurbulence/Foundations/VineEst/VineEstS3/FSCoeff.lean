/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.VineEst.VineEstS3.FSKernelBound
public import WaveTurbulence.Foundations.Sumint.TimeBridge
public import WaveTurbulence.Foundations.Regref.Trace00
public import WaveTurbulence.Foundations.Fourier.TimeInterpolation

/-! # Fourier-series coefficients of an extension and the value identity (B2, step 4)

For an extension `G` (finite `𝔛^{θ,0,0}` norm) of a time-continuous `f` on `B ⊆ Q_q`, the coefficients
`c_m(k) = ∫ a_m(λ) Ĝ(λ,k) dλ` satisfy `f(t,k) = ∑_m c_m(k) e^{πi m·t}` for `t ∈ closure (interior B)`.
-/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.VineEstS3.FS
open WaveTurbulence WaveTurbulence.Fourier MeasureTheory Set
open scoped SchwartzMap ENNReal

variable {r d : ℕ}

/-- The Fourier-series coefficient of the extension `G`. -/
noncomputable def coeff (q : Fin r → ℝ) (G : (Fin r → ℝ) → Mom d → ℂ) (m : Fin r → ℤ) (k : Mom d) : ℂ :=
  ∫ lam, kern q m lam * timeFT G lam k

theorem cutQ_integrable (q : Fin r → ℝ) : Integrable (cutQ q) :=
  (cutQ_contDiff q).continuous.integrable_of_hasCompactSupport (cutQ_hasCompactSupport q)

theorem continuous_kern (q : Fin r → ℝ) (m : Fin r → ℤ) : Continuous (kern q m) := by
  unfold kern
  refine continuous_const.mul ((timeFourier_continuous (cutQ_integrable q)).comp ?_)
  fun_prop

/-- `‖a_m(λ)‖` is bounded by a constant. -/
theorem norm_kern_le (q : Fin r → ℝ) (m : Fin r → ℤ) (lam : Fin r → ℝ) :
    ‖kern q m lam‖ ≤ ((2 : ℝ) ^ r)⁻¹ * ∫ u, ‖cutQ q u‖ := by
  unfold kern
  rw [norm_mul, norm_inv, norm_pow]
  simp only [RCLike.norm_ofNat]
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  unfold timeFourier
  exact VectorFourier.norm_fourierIntegral_le_integral_norm _ _ _ _ _

theorem timePairing_comm (x y : Fin r → ℝ) : timePairing r x y = timePairing r y x := by
  change x ⬝ᵥ y = y ⬝ᵥ x
  exact dotProduct_comm _ _

/-- The value identity in the slice at a fixed momentum. -/
theorem hasSum_coeff_slice {θ : ℝ} (hθ : 0 ≤ θ) (q : Fin r → ℝ) {B : Set (Fin r → ℝ)}
    (hB : B ⊆ cell q) {g h : (Fin r → ℝ) → ℂ} (hgn : timeFourierNorm θ g < ⊤)
    (hgh : ∀ t ∈ B, g t = h t) (hh : Continuous h) {t : Fin r → ℝ}
    (ht : t ∈ closure (interior B)) :
    HasSum (fun m : Fin r → ℤ => (∫ lam, kern q m lam * timeFourier g lam) * fsPhase m t) (h t) := by
  have hint : Integrable g := integrable_of_timeFourierNorm_lt_top hgn
  have hĝ : Integrable (timeFourier g) := integrable_timeFourier_of_norm_lt_top hθ hgn
  have hrep := Regref.rep_eq_of_mem_closure_interior hθ hgn hgh hh ht
  -- the cell condition
  have hcl : IsClosed (cell q) := by
    unfold cell
    simp only [Set.ofPred_forall]
    exact isClosed_iInter fun i => isClosed_Icc.preimage (continuous_apply i)
  have htcell : t ∈ cell q := closure_minimal (interior_subset.trans hB) hcl ht
  have hrepval : Regref.rep g t =
      ∫ lam, timeFourier g lam * (Real.fourierChar (timePairing r t lam) : ℂ) := by
    change timeFourier (timeFourier g) (-t) = _
    unfold timeFourier VectorFourier.fourierIntegral
    refine integral_congr_ae (ae_of_all _ fun lam => ?_)
    simp only [map_neg, neg_neg, Circle.smul_def, smul_eq_mul]
    rw [timePairing_comm, mul_comm]
  set K0 : ℝ := ((2 : ℝ) ^ r)⁻¹ * ∫ u, ‖cutQ q u‖ with hK0
  have hFint : ∀ m : Fin r → ℤ, Integrable
      (fun lam => kern q m lam * timeFourier g lam * fsPhase m t) := by
    intro m
    refine Integrable.mono' ((hĝ.norm.mul_const K0)) ?_ (ae_of_all _ fun lam => ?_)
    · exact (((continuous_kern q m).mul (timeFourier_continuous hint)).mul_const _).aestronglyMeasurable
    · have hph : ‖fsPhase m t‖ = 1 := by unfold fsPhase; exact Circle.norm_coe _
      calc ‖kern q m lam * timeFourier g lam * fsPhase m t‖ =
            ‖kern q m lam‖ * ‖timeFourier g lam‖ := by rw [norm_mul, norm_mul, hph, mul_one]
        _ ≤ K0 * ‖timeFourier g lam‖ :=
            mul_le_mul_of_nonneg_right (norm_kern_le q m lam) (norm_nonneg _)
        _ = ‖timeFourier g lam‖ * K0 := mul_comm _ _
  obtain ⟨C0, hC0, hC0b⟩ := sum_kern_weight_le q (le_refl (0 : ℝ))
  have hnormF : ∀ (m : Fin r → ℤ) (lam : Fin r → ℝ),
      ‖kern q m lam * timeFourier g lam * fsPhase m t‖ = ‖kern q m lam‖ * ‖timeFourier g lam‖ := by
    intro m lam
    have hph : ‖fsPhase m t‖ = 1 := by unfold fsPhase; exact Circle.norm_coe _
    rw [norm_mul, norm_mul, hph, mul_one]
  have hFsum : Summable fun m : Fin r → ℤ =>
      ∫ lam, ‖kern q m lam * timeFourier g lam * fsPhase m t‖ := by
    refine summable_of_sum_le (c := C0 * ∫ lam, ‖timeFourier g lam‖)
      (fun m => integral_nonneg fun lam => norm_nonneg _) fun S => ?_
    rw [← integral_finsetSum _ (fun m _ => (hFint m).norm)]
    rw [← integral_const_mul]
    refine integral_mono (integrable_finsetSum _ fun m _ => (hFint m).norm)
      (hĝ.norm.const_mul _) fun lam => ?_
    simp only [hnormF]
    rw [← Finset.sum_mul]
    refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
    obtain ⟨hs, hsum⟩ := hC0b lam
    have := hsum
    simp only [Real.rpow_zero, mul_one, one_mul] at hs this
    exact (hs.sum_le_tsum S (fun m _ => norm_nonneg _)).trans this
  have hHS := hasSum_integral_of_summable_integral_norm hFint hFsum
  have hform : (fun m : Fin r → ℤ => ∫ lam, kern q m lam * timeFourier g lam * fsPhase m t) =
      fun m => (∫ lam, kern q m lam * timeFourier g lam) * fsPhase m t := by
    funext m; exact integral_mul_const _ _
  have hint2 : ∫ lam, (∑' m : Fin r → ℤ, kern q m lam * timeFourier g lam * fsPhase m t) = h t := by
    rw [← hrep, hrepval]
    refine integral_congr_ae (ae_of_all _ fun lam => ?_)
    have : ∀ m : Fin r → ℤ, kern q m lam * timeFourier g lam * fsPhase m t =
        (kern q m lam * fsPhase m t) * timeFourier g lam := fun m => by ring
    simp only [this]
    rw [tsum_mul_right, tsum_kern_phase htcell lam, timePairing_comm, mul_comm]
  rw [hform] at hHS
  rw [hint2] at hHS
  exact hHS


/-- **Value identity** for an extension `G` of a time-continuous `f` on `B ⊆ Q_q`, at one momentum. -/
theorem hasSum_coeff_at {θ : ℝ} (hθ : 0 ≤ θ) (q : Fin r → ℝ) {B : Set (Fin r → ℝ)} (hB : B ⊆ cell q)
    {G f : (Fin r → ℝ) → Mom d → ℂ} {k : Mom d} (hGf : ∀ t ∈ B, G t k = f t k)
    (hfc : Continuous fun t => f t k) (hG : XNorm00 θ G < ⊤) {t : Fin r → ℝ}
    (ht : t ∈ closure (interior B)) :
    HasSum (fun m : Fin r → ℤ => coeff q G m k * fsPhase m t) (f t k) := by
  have hgn : timeFourierNorm θ (fun s => G s k) < ⊤ := by
    refine lt_of_le_of_lt ((timeFourierNorm_slice_le_mixedFourierNorm00 θ G k).trans_eq ?_) hG
    exact (NormBridgeScratch.XNorm00_eq_mixedFourierNorm00 θ G).symm
  have := hasSum_coeff_slice hθ q hB hgn hGf hfc ht
  simpa only [coeff, NormBridgeScratch.timeFT_eq_timeFourier] using this

/-- **Value identity** for an extension `G` of a time-continuous `f` on `B ⊆ Q_q`. -/
theorem hasSum_coeff {θ : ℝ} (hθ : 0 ≤ θ) (q : Fin r → ℝ) {B : Set (Fin r → ℝ)} (hB : B ⊆ cell q)
    {G f : (Fin r → ℝ) → Mom d → ℂ} (hGf : ∀ t ∈ B, ∀ k, G t k = f t k)
    (hfc : ∀ k, Continuous fun t => f t k) (hG : XNorm00 θ G < ⊤) {t : Fin r → ℝ}
    (ht : t ∈ closure (interior B)) (k : Mom d) :
    HasSum (fun m : Fin r → ℤ => coeff q G m k * fsPhase m t) (f t k) :=
  hasSum_coeff_at hθ q hB (fun t htB => hGf t htB k) (hfc k) hG ht

end WaveTurbulence.VineEstS3.FS
