/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Torus.Derivative
public import Mathlib.Analysis.PSeries

/-!
# Fourier inversion, uniqueness and Parseval on `𝕋_L^d`

For the coefficients `torusFourierCoeff L f n` of TARGET (1.2) (L286), transported from Mathlib's
`UnitAddTorus` theory through `torusFourierCoeff_eq_mFourierCoeff`:

* `IsRapidDecay.summable_norm_mul_pow`: rapidly decaying families are absolutely summable against
  every polynomial weight `(1 + ‖n‖)^k`;
* `hasSum_torusFourier_series_of_summable`, `hasSum_torusFourier_series`: a continuous periodic
  function with summable coefficients (in particular a smooth periodic function) equals its
  absolutely convergent Fourier series `L^{-d/2} ∑ₙ f̂(n) e^{2πi (n/L)·x}` (the second identity of
  TARGET (1.2));
* `eq_of_torusFourierCoeff_eq`: continuous periodic functions with equal coefficients are equal;
* `hasSum_sq_torusFourierCoeff`, `hasSum_inner_torusFourierCoeff`: Parseval's identities
  `∑ₙ |f̂(n)|² = ∫_{[0,L]^d} |f|²` and `∑ₙ conj f̂(n) ĝ(n) = ∫_{[0,L]^d} conj f g`;
* `torusFourierCoeff_torusChar`: orthogonality of the characters;
* `torusFourierCoeff_tsum`: coefficients of an absolutely convergent series of functions.
-/

public section

noncomputable section

open MeasureTheory Complex Set
open scoped ContDiff

namespace WaveTurbulence

attribute [local instance] instMeasureSpaceUnitAddCircle instIsAddHaarMeasureUnitAddCircleVolume
  instIsProbabilityMeasureUnitAddCircleVolume

variable {d : ℕ} {L : ℝ}

/-! ### Summability over `ℤ^d` -/

section Summable

theorem summable_inv_one_add_abs_int_sq :
    Summable fun m : ℤ => ((1 + |(m : ℝ)|) ^ 2)⁻¹ := by
  refine Summable.of_norm_bounded_eventually (g := fun m : ℤ => 1 / (m : ℝ) ^ 2)
    (Real.summable_one_div_int_pow.2 one_lt_two) ?_
  filter_upwards [Filter.eventually_cofinite_ne 0] with m hm
  have hm' : (m : ℝ) ≠ 0 := Int.cast_ne_zero.2 hm
  rw [Real.norm_of_nonneg (by positivity), one_div]
  apply inv_anti₀ (by positivity)
  rw [← sq_abs]
  gcongr
  linarith [abs_nonneg (m : ℝ)]

theorem summable_prod_inv_one_add_abs_sq :
    Summable fun n : Fin d → ℤ => ∏ j, ((1 + |(n j : ℝ)|) ^ 2)⁻¹ := by
  classical
  set g : ℤ → ℝ := fun m => ((1 + |(m : ℝ)|) ^ 2)⁻¹ with hgdef
  have hg : Summable g := summable_inv_one_add_abs_int_sq
  have hg0 : ∀ m, 0 ≤ g m := fun m => by positivity
  refine summable_of_sum_le (c := (∑' m, g m) ^ d)
    (fun n => Finset.prod_nonneg fun j _ => hg0 _) fun u => ?_
  set t : Fin d → Finset ℤ := fun j => u.image (fun n => n j)
  calc ∑ n ∈ u, ∏ j, g (n j) ≤ ∑ n ∈ Fintype.piFinset t, ∏ j, g (n j) :=
        Finset.sum_le_sum_of_subset_of_nonneg
          (fun n hn => Fintype.mem_piFinset.2 fun j => Finset.mem_image_of_mem _ hn)
          (fun _ _ _ => Finset.prod_nonneg fun j _ => hg0 _)
    _ = ∏ j, ∑ m ∈ t j, g m := (Finset.prod_univ_sum t fun _ m => g m).symm
    _ ≤ ∏ _j : Fin d, ∑' m, g m :=
        Finset.prod_le_prod₀ (fun j _ => Finset.sum_nonneg fun _ _ => hg0 _)
          fun j _ => hg.sum_le_tsum _ (fun _ _ => hg0 _)
    _ = (∑' m, g m) ^ d := by simp

/-- `∑_{n ∈ ℤ^d} (1 + ‖n‖)^{-2d} < ∞`. -/
theorem summable_one_add_norm_zpow :
    Summable fun n : Fin d → ℤ => (1 + ‖n‖) ^ (-((2 * d : ℕ) : ℤ)) := by
  refine Summable.of_nonneg_of_le (fun n => by positivity) (fun n => ?_)
    summable_prod_inv_one_add_abs_sq
  rw [zpow_neg, zpow_natCast, Finset.prod_inv_distrib]
  apply inv_anti₀ (Finset.prod_pos fun j _ => by positivity)
  calc ∏ j, (1 + |(n j : ℝ)|) ^ 2 ≤ ∏ _j : Fin d, (1 + ‖n‖) ^ 2 :=
        Finset.prod_le_prod₀ (fun j _ => by positivity) fun j _ => by
          gcongr
          rw [← Int.norm_eq_abs]
          exact norm_le_pi_norm n j
    _ = (1 + ‖n‖) ^ (2 * d) := by
        rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin, ← pow_mul]

theorem IsRapidDecay.summable_norm_mul_pow {c : (Fin d → ℤ) → ℂ} (hc : IsRapidDecay c) (k : ℕ) :
    Summable fun n => ‖c n‖ * (1 + ‖n‖) ^ k := by
  obtain ⟨C, hC⟩ := hc (k + 2 * d)
  refine Summable.of_nonneg_of_le (fun n => by positivity) (fun n => ?_)
    (summable_one_add_norm_zpow.mul_left C)
  have hpos : 0 < 1 + ‖n‖ := by positivity
  calc ‖c n‖ * (1 + ‖n‖) ^ k ≤ C * (1 + ‖n‖) ^ (-((k + 2 * d : ℕ) : ℤ)) * (1 + ‖n‖) ^ k := by
        gcongr
        exact hC n
    _ = C * (1 + ‖n‖) ^ (-((2 * d : ℕ) : ℤ)) := by
        rw [mul_assoc, ← zpow_natCast (1 + ‖n‖) k, ← zpow_add₀ hpos.ne']
        congr 2
        push_cast
        ring

theorem IsRapidDecay.summable_norm {c : (Fin d → ℤ) → ℂ} (hc : IsRapidDecay c) :
    Summable fun n => ‖c n‖ :=
  (hc.summable_norm_mul_pow 0).congr fun n => by simp

theorem IsRapidDecay.summable {c : (Fin d → ℤ) → ℂ} (hc : IsRapidDecay c) : Summable c :=
  Summable.of_norm hc.summable_norm

end Summable

/-! ### Inversion and uniqueness -/

section Inversion

theorem torusLift_torusChar_apply (hL : L ≠ 0) (n : Fin d → ℤ) (x : Fin d → ℝ) :
    UnitAddTorus.mFourier n (torusProj L x) = torusChar L n x := by
  rw [← congrFun (torusLift_torusChar hL n) (torusProj L x),
    torusLift_torusProj hL (isTorusPeriodic_torusChar hL n)]

theorem mFourierCoeff_torusLift (hL : 0 < L) (f : (Fin d → ℝ) → ℂ) (n : Fin d → ℤ) :
    UnitAddTorus.mFourierCoeff (torusLift L f) n =
      ((L ^ ((d : ℝ) / 2) : ℝ) : ℂ)⁻¹ * torusFourierCoeff L f n := by
  have hne : ((L ^ ((d : ℝ) / 2) : ℝ) : ℂ) ≠ 0 :=
    ofReal_ne_zero.2 (Real.rpow_pos_of_pos hL _).ne'
  rw [torusFourierCoeff_eq_mFourierCoeff hL, inv_mul_cancel_left₀ hne]

/-- Fourier inversion (TARGET (1.2), second identity): a continuous `L`-periodic `f` with summable
coefficients is the sum of its Fourier series `L^{-d/2} ∑ₙ f̂(n) e^{2πi (n/L)·x}` at every `x`. -/
theorem hasSum_torusFourier_series_of_summable (hL : 0 < L) {f : (Fin d → ℝ) → ℂ}
    (hf : Continuous f) (hp : IsTorusPeriodic L f) (hs : Summable (torusFourierCoeff L f))
    (x : Fin d → ℝ) :
    HasSum (fun n => ((L ^ ((d : ℝ) / 2) : ℝ) : ℂ)⁻¹ * torusFourierCoeff L f n * torusChar L n x)
      (f x) := by
  set g : C(UnitAddTorus (Fin d), ℂ) := ⟨torusLift L f, continuous_torusLift hL.ne' hf hp⟩
  have hsg : Summable (UnitAddTorus.mFourierCoeff g) := by
    change Summable fun n => UnitAddTorus.mFourierCoeff (torusLift L f) n
    simp_rw [mFourierCoeff_torusLift hL]
    exact hs.mul_left _
  have h := UnitAddTorus.hasSum_mFourier_series_apply_of_summable hsg (torusProj L x)
  change HasSum (fun i => UnitAddTorus.mFourierCoeff (torusLift L f) i •
    UnitAddTorus.mFourier i (torusProj L x)) (torusLift L f (torusProj L x)) at h
  simp only [mFourierCoeff_torusLift hL, torusLift_torusChar_apply hL.ne', smul_eq_mul,
    torusLift_torusProj hL.ne' hp] at h
  exact h

/-- Fourier inversion for smooth periodic `f` (TARGET (1.2)): `f` is the sum of its absolutely
convergent Fourier series. -/
theorem hasSum_torusFourier_series (hL : 0 < L) {f : (Fin d → ℝ) → ℂ} (hf : ContDiff ℝ ∞ f)
    (hp : IsTorusPeriodic L f) (x : Fin d → ℝ) :
    HasSum (fun n => ((L ^ ((d : ℝ) / 2) : ℝ) : ℂ)⁻¹ * torusFourierCoeff L f n * torusChar L n x)
      (f x) :=
  hasSum_torusFourier_series_of_summable hL hf.continuous hp
    (isRapidDecay_torusFourierCoeff hL hf hp).summable x

/-- The coefficients of a smooth periodic function are absolutely summable. -/
theorem summable_norm_torusFourierCoeff (hL : 0 < L) {f : (Fin d → ℝ) → ℂ} (hf : ContDiff ℝ ∞ f)
    (hp : IsTorusPeriodic L f) : Summable fun n => ‖torusFourierCoeff L f n‖ :=
  (isRapidDecay_torusFourierCoeff hL hf hp).summable_norm

/-- Uniqueness: continuous `L`-periodic functions with the same coefficients are equal. -/
theorem eq_of_torusFourierCoeff_eq (hL : 0 < L) {f g : (Fin d → ℝ) → ℂ} (hf : Continuous f)
    (hg : Continuous g) (hpf : IsTorusPeriodic L f) (hpg : IsTorusPeriodic L g)
    (h : ∀ n, torusFourierCoeff L f n = torusFourierCoeff L g n) : f = g := by
  set F : C(UnitAddTorus (Fin d), ℂ) := ⟨torusLift L f, continuous_torusLift hL.ne' hf hpf⟩
  set G : C(UnitAddTorus (Fin d), ℂ) := ⟨torusLift L g, continuous_torusLift hL.ne' hg hpg⟩
  have hcoef : ∀ n, UnitAddTorus.mFourierCoeff F n = UnitAddTorus.mFourierCoeff G n := by
    intro n
    change UnitAddTorus.mFourierCoeff (torusLift L f) n =
      UnitAddTorus.mFourierCoeff (torusLift L g) n
    rw [mFourierCoeff_torusLift hL, mFourierCoeff_torusLift hL, h n]
  have hLp : ContinuousMap.toLp 2 volume ℂ F = ContinuousMap.toLp 2 volume ℂ G := by
    apply UnitAddTorus.mFourierBasis.repr.injective
    refine lp.ext (funext fun n => ?_)
    rw [UnitAddTorus.mFourierBasis_repr, UnitAddTorus.mFourierBasis_repr,
      UnitAddTorus.mFourierCoeff_toLp, UnitAddTorus.mFourierCoeff_toLp]
    exact hcoef n
  have hFG : F = G := ContinuousMap.toLp_injective volume (𝕜 := ℂ) hLp
  funext x
  rw [← torusLift_torusProj hL.ne' hpf x, ← torusLift_torusProj hL.ne' hpg x]
  exact congrArg (fun H : C(UnitAddTorus (Fin d), ℂ) => H (torusProj L x)) hFG

/-- Orthogonality of the characters: `(e^{2πi (m/L)·x})^(n) = L^{d/2} δₘₙ`. -/
theorem torusFourierCoeff_torusChar (hL : 0 < L) (m n : Fin d → ℤ) :
    torusFourierCoeff L (torusChar L m) n =
      if m = n then ((L ^ ((d : ℝ) / 2) : ℝ) : ℂ) else 0 := by
  classical
  rw [torusFourierCoeff_eq_mFourierCoeff hL, torusLift_torusChar hL.ne']
  have h1 : UnitAddTorus.mFourierCoeff (UnitAddTorus.mFourier m) n =
      UnitAddTorus.mFourierBasis.repr (UnitAddTorus.mFourierBasis m) n := by
    rw [UnitAddTorus.mFourierBasis_repr, UnitAddTorus.coe_mFourierBasis,
      UnitAddTorus.mFourierCoeff_toLp]
  rw [h1, HilbertBasis.repr_self, lp.single_apply, Pi.single_apply]
  by_cases hmn : m = n
  · subst hmn; simp
  · simp [hmn, Ne.symm hmn]

end Inversion

/-! ### Parseval -/

section Parseval

theorem rpow_half_sq (hL : 0 < L) : (L ^ ((d : ℝ) / 2)) ^ 2 = L ^ d := by
  rw [← Real.rpow_natCast (L ^ _) 2, ← Real.rpow_mul hL.le,
    show (d : ℝ) / 2 * ((2 : ℕ) : ℝ) = ((d : ℕ) : ℝ) by push_cast; ring, Real.rpow_natCast]

/-- Parseval's identity (polarized): for continuous `L`-periodic `f, g`,
`∑ₙ conj f̂(n) ĝ(n) = ∫_{[0,L]^d} conj f g`. -/
theorem hasSum_inner_torusFourierCoeff (hL : 0 < L) {f g : (Fin d → ℝ) → ℂ} (hf : Continuous f)
    (hg : Continuous g) (hpf : IsTorusPeriodic L f) (hpg : IsTorusPeriodic L g) :
    HasSum (fun n => (starRingEnd ℂ) (torusFourierCoeff L f n) * torusFourierCoeff L g n)
      (∫ x in Icc (0 : Fin d → ℝ) (fun _ => L), (starRingEnd ℂ) (f x) * g x) := by
  set F : C(UnitAddTorus (Fin d), ℂ) := ⟨torusLift L f, continuous_torusLift hL.ne' hf hpf⟩
  set G : C(UnitAddTorus (Fin d), ℂ) := ⟨torusLift L g, continuous_torusLift hL.ne' hg hpg⟩
  have h := UnitAddTorus.hasSum_prod_mFourierCoeff (ContinuousMap.toLp 2 volume ℂ F)
    (ContinuousMap.toLp 2 volume ℂ G)
  simp only [UnitAddTorus.mFourierCoeff_toLp] at h
  have hint : ∫ t, (starRingEnd ℂ) ((ContinuousMap.toLp 2 volume ℂ F) t) *
      (ContinuousMap.toLp 2 volume ℂ G) t = ∫ t, (starRingEnd ℂ) (F t) * G t := by
    refine integral_congr_ae ?_
    filter_upwards [ContinuousMap.coeFn_toLp (p := 2) (𝕜 := ℂ) volume F,
      ContinuousMap.coeFn_toLp (p := 2) (𝕜 := ℂ) volume G] with t hF hG
    rw [hF, hG]
  rw [hint] at h
  change HasSum (fun i => (starRingEnd ℂ) (UnitAddTorus.mFourierCoeff (torusLift L f) i) *
    UnitAddTorus.mFourierCoeff (torusLift L g) i)
    (∫ t, (starRingEnd ℂ) (torusLift L f t) * torusLift L g t) at h
  have hbox : ∫ x in Icc (0 : Fin d → ℝ) (fun _ => L), (starRingEnd ℂ) (f x) * g x =
      ((L ^ d : ℝ) : ℂ) * ∫ t, (starRingEnd ℂ) (torusLift L f t) * torusLift L g t := by
    rw [setIntegral_Icc_eq_smul_integral_torusLift hL, Complex.real_smul]
    rfl
  have hcoef : ∀ n, (starRingEnd ℂ) (torusFourierCoeff L f n) * torusFourierCoeff L g n =
      ((L ^ d : ℝ) : ℂ) * ((starRingEnd ℂ) (UnitAddTorus.mFourierCoeff (torusLift L f) n) *
        UnitAddTorus.mFourierCoeff (torusLift L g) n) := by
    intro n
    rw [torusFourierCoeff_eq_mFourierCoeff hL, torusFourierCoeff_eq_mFourierCoeff hL, map_mul,
      conj_ofReal, ← rpow_half_sq (d := d) hL]
    push_cast
    ring
  simp_rw [hcoef, hbox]
  exact h.mul_left _

/-- Parseval's identity (TARGET (1.2)): `∑ₙ |f̂(n)|² = ∫_{[0,L]^d} |f|²` for continuous
`L`-periodic `f`. -/
theorem hasSum_sq_torusFourierCoeff (hL : 0 < L) {f : (Fin d → ℝ) → ℂ} (hf : Continuous f)
    (hp : IsTorusPeriodic L f) :
    HasSum (fun n => ‖torusFourierCoeff L f n‖ ^ 2)
      (∫ x in Icc (0 : Fin d → ℝ) (fun _ => L), ‖f x‖ ^ 2) := by
  have h := hasSum_inner_torusFourierCoeff hL hf hf hp hp
  simp_rw [Complex.conj_mul', ← Complex.ofReal_pow] at h
  rw [integral_complex_ofReal] at h
  exact Complex.hasSum_ofReal.1 h

end Parseval

/-! ### Coefficients of absolutely convergent series -/

section Tsum

/-- Coefficients commute with absolutely convergent series of functions. -/
theorem torusFourierCoeff_tsum {ι : Type*} [Countable ι] {F : ι → (Fin d → ℝ) → ℂ}
    (hFi : ∀ m, IntegrableOn (F m) (Icc (0 : Fin d → ℝ) (fun _ => L)))
    (hFs : Summable fun m => ∫ x in Icc (0 : Fin d → ℝ) (fun _ => L), ‖F m x‖)
    (n : Fin d → ℤ) :
    torusFourierCoeff L (fun x => ∑' m, F m x) n = ∑' m, torusFourierCoeff L (F m) n := by
  simp only [torusFourierCoeff_eq_integral, ← tsum_mul_right]
  rw [← integral_tsum_of_summable_integral_norm (fun m => integrableOn_mul_torusChar (hFi m) _)
    (hFs.congr fun m => by simp only [norm_mul, norm_torusChar, mul_one]), tsum_mul_left]

end Tsum

end WaveTurbulence
