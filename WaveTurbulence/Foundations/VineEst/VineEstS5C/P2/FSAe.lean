/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.VineEst.VineEstS3.FSCoeff
public import WaveTurbulence.Foundations.VineEst.VineEstS3.FSMain

/-! # P2: the Fourier-series expansion of a restriction-norm bounded kernel that is continuous only up to a null set of times

Variants of `VineEstS3.FS.hasSum_coeff_slice`, `hasSum_coeff_at`, `fs_expansion` (copied, with only the hypotheses
changed): the kernel `f` is only required to agree, for a.e. time `t ∈ B` and all `k`, with a function `f̃` that is continuous in `t`
for every `k`.  The expansion then sums to `f̃`.  (The remainder rows `K* - app` are of this form: `K*` is continuous in time, the
approximant is a finite sum of separated terms whose time factors are continuous representatives a.e.) -/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.VineEstS5C.P2
open WaveTurbulence WaveTurbulence.Fourier WaveTurbulence.VineEstS3.FS MeasureTheory Set
open scoped ENNReal

variable {r d : ℕ}

theorem rep_eq_ae {θ : ℝ} (hθ : 0 ≤ θ) {B : Set (Fin r → ℝ)} {g h : (Fin r → ℝ) → ℂ}
    (hg : timeFourierNorm θ g < ⊤) (hgh : ∀ᵐ t, t ∈ B → g t = h t) (hh : Continuous h) {t : Fin r → ℝ}
    (ht : t ∈ closure (interior B)) : Regref.rep g t = h t := by
  obtain ⟨hc, hae, -⟩ := Regref.rep_props hθ hg
  have hint : ∀ x ∈ interior B, Regref.rep g x = h x := by
    have hU : IsOpen ({x | Regref.rep g x ≠ h x} ∩ interior B) :=
      (isOpen_ne_fun hc hh).inter isOpen_interior
    have hnull : volume ({x | Regref.rep g x ≠ h x} ∩ interior B) = 0 := by
      have h1 := ae_iff.1 hae
      have h2 := ae_iff.1 hgh
      refine measure_mono_null (fun x hx => ?_) (measure_union_null h1 h2)
      by_contra hn
      simp only [mem_union, mem_setOf_eq, not_or, not_not] at hn
      exact hx.1 (hn.1.trans (hn.2 (interior_subset hx.2)))
    have hemp := hU.measure_eq_zero_iff volume |>.1 hnull
    intro x hx
    by_contra hne
    exact (Set.eq_empty_iff_forall_notMem.1 hemp) x ⟨hne, hx⟩
  have hcl : IsClosed {x | Regref.rep g x = h x} := isClosed_eq hc hh
  exact closure_minimal hint hcl ht

theorem hasSum_coeff_slice_ae {θ : ℝ} (hθ : 0 ≤ θ) (q : Fin r → ℝ) {B : Set (Fin r → ℝ)}
    (hB : B ⊆ cell q) {g h : (Fin r → ℝ) → ℂ} (hgn : timeFourierNorm θ g < ⊤)
    (hgh : ∀ᵐ t, t ∈ B → g t = h t) (hh : Continuous h) {t : Fin r → ℝ}
    (ht : t ∈ closure (interior B)) :
    HasSum (fun m : Fin r → ℤ => (∫ lam, kern q m lam * timeFourier g lam) * fsPhase m t) (h t) := by
  have hint : Integrable g := integrable_of_timeFourierNorm_lt_top hgn
  have hĝ : Integrable (timeFourier g) := integrable_timeFourier_of_norm_lt_top hθ hgn
  have hrep := rep_eq_ae hθ hgn hgh hh ht
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


end WaveTurbulence.VineEstS5C.P2
