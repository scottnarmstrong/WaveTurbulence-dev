/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Flower.FiltCoh.CrudeCore
public import WaveTurbulence.Foundations.Cut2A.Chirp

/-! # FILT-COH (c4a): a one-dimensional filter multiplies a Fourier representation

If `Φ(Ω) = ∫ Φh(s) ∏ᵢ e(sᵢ Ωᵢ) ds` (main's `ApproxNT.IsFourierRep`) and `f(u) = ∫ fh(t) e(t u) dt`, then
`Ω ↦ Φ(Ω) f(Ω_j)` is represented by the sheared convolution `s ↦ ∫ fh(t) Φh(s - t e_j) dt` (`shearConv`;
translation invariance in `s`, then Fubini). Its weighted Fourier bounds are those of `Φh` times
`2^d ∫ ‖fh‖ (1 + t²)^d` (Peetre's inequality `1 + s² ≤ 2 (1 + (s - t)²)(1 + t²)` in coordinate `j`). This is the
analytic input for the resonance filters on the coherent link energies (o82 Prop. 15.1: the filters enter the
profile of Thm 10.1 with their Fourier-measure costs). -/

public section
noncomputable section
namespace WaveTurbulence.Flower.FiltCoh
open MeasureTheory WaveTurbulence.ApproxNT Finset
open scoped ENNReal FourierTransform SchwartzMap

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- The coordinate vector `t e_j`. -/
@[expose] def ej (j : ι) (t : ℝ) : ι → ℝ := Pi.single j t

omit [Fintype ι] in
theorem ej_same (j : ι) (t : ℝ) : ej j t j = t := Pi.single_eq_same _ _

omit [Fintype ι] in
theorem ej_ne {i j : ι} (h : i ≠ j) (t : ℝ) : ej j t i = 0 := Pi.single_eq_of_ne h _

/-- The sheared convolution of a Fourier density with a one-dimensional density in coordinate `j`. -/
@[expose] def shearConv (Φh : (ι → ℝ) → ℂ) (fh : ℝ → ℂ) (j : ι) (s : ι → ℝ) : ℂ :=
  ∫ t, fh t * Φh (s - ej j t)

omit [Fintype ι] in
theorem continuous_single_coord (j : ι) : Continuous (fun t : ℝ => ej j t) := by
  refine continuous_pi fun i => ?_
  by_cases hi : i = j
  · subst hi
    simpa only [ej_same] using continuous_id'
  · simpa only [ej_ne hi] using continuous_const

/-- The shear `(t, s) ↦ (t, s - t e_j)` preserves Lebesgue measure. -/
theorem measurePreserving_shear (j : ι) :
    MeasurePreserving (fun p : ℝ × (ι → ℝ) => (p.1, p.2 - ej j p.1))
      ((volume : Measure ℝ).prod (volume : Measure (ι → ℝ))) ((volume : Measure ℝ).prod volume) := by
  refine (MeasurePreserving.id volume).skew_product (g := fun t s => s - ej j t) ?_ ?_
  · exact (continuous_snd.sub ((continuous_single_coord j).comp continuous_fst)).measurable
  · exact ae_of_all _ fun t => (measurePreserving_sub_right volume (ej j t)).map_eq

theorem integrable_shear {Φh : (ι → ℝ) → ℂ} (hΦ : Integrable Φh) {fh : ℝ → ℂ} (hfh : Integrable fh) (j : ι) :
    Integrable (fun p : ℝ × (ι → ℝ) => fh p.1 * Φh (p.2 - ej j p.1))
      ((volume : Measure ℝ).prod (volume : Measure (ι → ℝ))) := by
  have h := (measurePreserving_shear j).integrable_comp_of_integrable (hfh.mul_prod hΦ)
  exact h

/-- The phase identity: a translation in coordinate `j` is compensated by the filter character. -/
theorem prod_char_shift (Ω s : ι → ℝ) (j : ι) (t : ℝ) :
    (∏ i, (Real.fourierChar ((s - ej j t) i * Ω i) : ℂ)) * (Real.fourierChar (t * Ω j) : ℂ) =
      ∏ i, (Real.fourierChar (s i * Ω i) : ℂ) := by
  have he (i : ι) : (Real.fourierChar ((s - ej j t) i * Ω i) : ℂ) =
      (Real.fourierChar (s i * Ω i) : ℂ) * (Real.fourierChar (-(ej j t i * Ω i)) : ℂ) := by
    rw [← Circle.coe_mul, ← AddChar.map_add_eq_mul]
    congr 2
    simp only [Pi.sub_apply]
    ring
  simp_rw [he]
  rw [Finset.prod_mul_distrib, mul_assoc]
  have hs : (∏ i, (Real.fourierChar (-(ej j t i * Ω i)) : ℂ)) =
      (Real.fourierChar (-(t * Ω j)) : ℂ) := by
    rw [Finset.prod_eq_single j (fun i _ hi => by
      rw [ej_ne hi, zero_mul, neg_zero, AddChar.map_zero_eq_one, Circle.coe_one])
      (fun h => absurd (Finset.mem_univ j) h)]
    rw [ej_same]
  rw [hs, ← Circle.coe_mul, ← AddChar.map_add_eq_mul, neg_add_cancel, AddChar.map_zero_eq_one,
    Circle.coe_one, mul_one]

/-- **A one-dimensional filter multiplies a Fourier representation.** -/
theorem isFourierRep_mul_filter {Φ Φh : (ι → ℝ) → ℂ} (hrep : IsFourierRep Φ Φh)
    {f fh : ℝ → ℂ} (hfh : Integrable fh) (hf : ∀ u, f u = ∫ t, fh t * (Real.fourierChar (t * u) : ℂ))
    (j : ι) :
    IsFourierRep (fun Ω => Φ Ω * f (Ω j)) (shearConv Φh fh j) := by
  have hG := integrable_shear hrep.1 hfh j
  refine ⟨?_, fun Ω => ?_⟩
  · exact hG.integral_prod_right
  · have hEc : Continuous (fun s : ι → ℝ => ∏ i, (Real.fourierChar (s i * Ω i) : ℂ)) :=
      continuous_finsetProd _ fun i _ =>
        Cut2A.character_smooth.continuous.comp ((continuous_apply i).mul continuous_const)
    have hGE : Integrable (fun p : ℝ × (ι → ℝ) =>
        fh p.1 * Φh (p.2 - ej j p.1) * ∏ i, (Real.fourierChar (p.2 i * Ω i) : ℂ))
        ((volume : Measure ℝ).prod (volume : Measure (ι → ℝ))) :=
      hG.mul_bdd (c := 1) ((hEc.comp continuous_snd).aestronglyMeasurable)
        (ae_of_all _ fun p => by simp only [norm_prod, Circle.norm_coe,
          Finset.prod_const_one, le_refl])
    have hin (t : ℝ) : (fh t * (Real.fourierChar (t * Ω j) : ℂ)) *
        ∫ s, Φh s * ∏ i, (Real.fourierChar (s i * Ω i) : ℂ) =
        ∫ s, fh t * Φh (s - ej j t) * ∏ i, (Real.fourierChar (s i * Ω i) : ℂ) := by
      rw [← integral_sub_right_eq_self (fun s => Φh s * ∏ i, (Real.fourierChar (s i * Ω i) : ℂ))
        (ej j t), ← integral_const_mul]
      refine integral_congr_ae (ae_of_all _ fun s => ?_)
      dsimp only
      rw [← prod_char_shift Ω s j t]
      ring
    dsimp only
    rw [hrep.2 Ω, hf (Ω j), mul_comm, ← integral_mul_const]
    simp_rw [hin]
    rw [integral_integral_swap (f := fun t s =>
      fh t * Φh (s - ej j t) * ∏ i, (Real.fourierChar (s i * Ω i) : ℂ)) hGE]
    refine integral_congr_ae (ae_of_all _ fun s => ?_)
    simp only [shearConv]
    rw [← integral_mul_const]

/-- Peetre's inequality in one coordinate. -/
theorem one_add_sq_le_peetre (s t : ℝ) : 1 + s ^ 2 ≤ 2 * ((1 + (s - t) ^ 2) * (1 + t ^ 2)) := by
  nlinarith [sq_nonneg (s - 2 * t), sq_nonneg ((s - t) * t), sq_nonneg t, sq_nonneg (s - t)]

omit [Fintype ι] in
theorem weight_shift_le (d : ℕ) (F : Finset ι) (s : ι → ℝ) (j : ι) (t : ℝ) :
    ∏ i ∈ F, (1 + s i ^ 2) ^ d ≤
      2 ^ d * (∏ i ∈ F, (1 + (s - ej j t) i ^ 2) ^ d) * (1 + t ^ 2) ^ d := by
  by_cases hj : j ∈ F
  · rw [← Finset.mul_prod_erase F _ hj, ← Finset.mul_prod_erase F (fun i => (1 + (s - ej j t) i ^ 2) ^ d) hj]
    have hrest : ∏ i ∈ F.erase j, (1 + (s - ej j t) i ^ 2) ^ d = ∏ i ∈ F.erase j, (1 + s i ^ 2) ^ d :=
      Finset.prod_congr rfl fun i hi => by
        rw [Pi.sub_apply, ej_ne (Finset.ne_of_mem_erase hi), sub_zero]
    rw [hrest]
    have hp : 0 ≤ ∏ i ∈ F.erase j, (1 + s i ^ 2) ^ d := Finset.prod_nonneg fun _ _ => by positivity
    have hpe := one_add_sq_le_peetre (s j) t
    have hpow : (1 + s j ^ 2) ^ d ≤ (2 * ((1 + (s j - t) ^ 2) * (1 + t ^ 2))) ^ d :=
      pow_le_pow_left₀ (by positivity) hpe d
    rw [Pi.sub_apply, ej_same]
    calc (1 + s j ^ 2) ^ d * ∏ i ∈ F.erase j, (1 + s i ^ 2) ^ d
        ≤ (2 * ((1 + (s j - t) ^ 2) * (1 + t ^ 2))) ^ d * ∏ i ∈ F.erase j, (1 + s i ^ 2) ^ d :=
          mul_le_mul_of_nonneg_right hpow hp
      _ = _ := by rw [mul_pow, mul_pow]; ring
  · have hrest : ∏ i ∈ F, (1 + (s - ej j t) i ^ 2) ^ d = ∏ i ∈ F, (1 + s i ^ 2) ^ d :=
      Finset.prod_congr rfl fun i hi => by
        rw [Pi.sub_apply, ej_ne (fun (h : i = j) => hj (h ▸ hi)), sub_zero]
    rw [hrest]
    have hp : 0 ≤ ∏ i ∈ F, (1 + s i ^ 2) ^ d := Finset.prod_nonneg fun _ _ => by positivity
    have h1 : (1:ℝ) ≤ 2 ^ d * (1 + t ^ 2) ^ d := one_le_mul_of_one_le_of_one_le (one_le_pow₀ (by norm_num))
      (one_le_pow₀ (by nlinarith [sq_nonneg t]))
    nlinarith

omit [Fintype ι] in
/-- **Weighted Fourier bounds of the sheared convolution.** -/
theorem shearConv_weight_le (d : ℕ) {Φh : (ι → ℝ) → ℂ} {fh : ℝ → ℂ}
    (hfw : Integrable (fun t => ‖fh t‖ * (1 + t ^ 2) ^ d)) {Kf : ℝ}
    (hKf : ∫ t, ‖fh t‖ * (1 + t ^ 2) ^ d ≤ Kf) (A : Finset ι → ℝ)
    (hA : ∀ F s, ‖Φh s‖ * ∏ i ∈ F, (1 + s i ^ 2) ^ d ≤ A F) (j : ι) (F : Finset ι) (s : ι → ℝ) :
    ‖shearConv Φh fh j s‖ * ∏ i ∈ F, (1 + s i ^ 2) ^ d ≤ 2 ^ d * A F * Kf := by
  have hw0 : 0 ≤ ∏ i ∈ F, (1 + s i ^ 2) ^ d := Finset.prod_nonneg fun _ _ => by positivity
  have hAF : 0 ≤ A F := (mul_nonneg (norm_nonneg _) (Finset.prod_nonneg fun _ _ => by positivity)).trans
    (hA F 0)
  unfold shearConv
  calc ‖∫ t, fh t * Φh (s - ej j t)‖ * ∏ i ∈ F, (1 + s i ^ 2) ^ d
      ≤ (∫ t, ‖fh t * Φh (s - ej j t)‖) * ∏ i ∈ F, (1 + s i ^ 2) ^ d :=
        mul_le_mul_of_nonneg_right (norm_integral_le_integral_norm _) hw0
    _ = ∫ t, ‖fh t * Φh (s - ej j t)‖ * ∏ i ∈ F, (1 + s i ^ 2) ^ d := (integral_mul_const _ _).symm
    _ ≤ ∫ t, (2 ^ d * A F) * (‖fh t‖ * (1 + t ^ 2) ^ d) := by
        refine integral_mono_of_nonneg (ae_of_all _ fun t => by positivity) (hfw.const_mul _)
          (ae_of_all _ fun t => ?_)
        dsimp only
        have hws := weight_shift_le d F s j t
        have hAt := hA F (s - ej j t)
        rw [norm_mul]
        calc ‖fh t‖ * ‖Φh (s - ej j t)‖ * ∏ i ∈ F, (1 + s i ^ 2) ^ d
            ≤ ‖fh t‖ * ‖Φh (s - ej j t)‖ *
              (2 ^ d * (∏ i ∈ F, (1 + (s - ej j t) i ^ 2) ^ d) * (1 + t ^ 2) ^ d) :=
              mul_le_mul_of_nonneg_left hws (by positivity)
          _ = (2 ^ d * (1 + t ^ 2) ^ d * ‖fh t‖) *
              (‖Φh (s - ej j t)‖ * ∏ i ∈ F, (1 + (s - ej j t) i ^ 2) ^ d) := by ring
          _ ≤ (2 ^ d * (1 + t ^ 2) ^ d * ‖fh t‖) * A F := mul_le_mul_of_nonneg_left hAt (by positivity)
          _ = _ := by ring
    _ = 2 ^ d * A F * ∫ t, ‖fh t‖ * (1 + t ^ 2) ^ d := integral_const_mul _ _
    _ ≤ 2 ^ d * A F * Kf := mul_le_mul_of_nonneg_left hKf (by positivity)

/-! ### Dilated Schwartz filters -/

/-- A weighted Schwartz mass is finite. -/
theorem integrable_schwartz_weight (φ : 𝓢(ℝ, ℂ)) (d : ℕ) :
    Integrable (fun v : ℝ => ‖φ v‖ * (1 + v ^ 2) ^ d) := by
  have he (v : ℝ) : ‖φ v‖ * (1 + v ^ 2) ^ d =
      ∑ k ∈ Finset.range (d + 1), ((d.choose k : ℝ)) * (‖v‖ ^ (2 * k) * ‖φ v‖) := by
    rw [add_comm (1:ℝ), add_pow, Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [one_pow, mul_one, pow_mul, Real.norm_eq_abs, sq_abs]
    ring
  simp_rw [he]
  exact integrable_finsetSum _ fun k _ => (φ.integrable_pow_mul volume (2 * k)).const_mul _

/-- **Dilation**: `φ(u/S) = ∫ S 𝓕φ(St) e(tu) dt`. -/
theorem dilate_eq_integral (φ : 𝓢(ℝ, ℂ)) {S : ℝ} (hS : 0 < S) (u : ℝ) :
    φ (u / S) = ∫ t, ((S : ℂ) * 𝓕 φ (S * t)) * (Real.fourierChar (t * u) : ℂ) := by
  have h := Continuous.fourierInv_fourier_eq φ.continuous φ.integrable
    (by rw [← SchwartzMap.fourier_coe]; exact (𝓕 φ).integrable)
  have h2 := congrFun h (u / S)
  rw [Real.fourierInv_eq] at h2
  rw [← h2]
  have hsub := Measure.integral_comp_mul_left
    (fun v : ℝ => (Real.fourierChar (v * (u / S)) : ℂ) * (𝓕 (φ : ℝ → ℂ)) v) S
  have hS' : |S⁻¹| = S⁻¹ := abs_of_pos (inv_pos.mpr hS)
  rw [hS'] at hsub
  have hlhs : (∫ v, 𝐞 (inner ℝ v (u / S)) • (𝓕 (φ : ℝ → ℂ)) v) =
      ∫ v, (Real.fourierChar (v * (u / S)) : ℂ) * (𝓕 (φ : ℝ → ℂ)) v := by
    refine integral_congr_ae (Filter.Eventually.of_forall fun v => ?_)
    simp [Circle.smul_def, RCLike.inner_apply, mul_comm]
  rw [hlhs]
  have hrhs : (∫ t, ((S : ℂ) * 𝓕 φ (S * t)) * (Real.fourierChar (t * u) : ℂ)) =
      (S : ℂ) * ∫ t, (Real.fourierChar ((S * t) * (u / S)) : ℂ) * (𝓕 (φ : ℝ → ℂ)) (S * t) := by
    rw [← integral_const_mul]
    refine integral_congr_ae (Filter.Eventually.of_forall fun t => ?_)
    have ht : (S * t) * (u / S) = t * u := by field_simp
    dsimp only
    rw [ht, SchwartzMap.fourier_coe]
    ring
  rw [hrhs, hsub, Complex.real_smul, ← mul_assoc, ← Complex.ofReal_mul, mul_inv_cancel₀ hS.ne',
    Complex.ofReal_one, one_mul]

/-- **The weighted mass of a dilated filter density is uniform in the scale `S ≥ 1`.** -/
theorem dilate_weight_le (φ : 𝓢(ℝ, ℂ)) {S : ℝ} (hS : 1 ≤ S) (d : ℕ) :
    Integrable (fun t : ℝ => ‖(S : ℂ) * 𝓕 φ (S * t)‖ * (1 + t ^ 2) ^ d) ∧
      ∫ t, ‖(S : ℂ) * 𝓕 φ (S * t)‖ * (1 + t ^ 2) ^ d ≤ ∫ v, ‖𝓕 φ v‖ * (1 + v ^ 2) ^ d := by
  have hS0 : 0 < S := zero_lt_one.trans_le hS
  have hw := integrable_schwartz_weight (𝓕 φ) d
  let g : ℝ → ℝ := fun v => ‖𝓕 φ v‖ * (1 + (v / S) ^ 2) ^ d
  have hg (t : ℝ) : ‖(S : ℂ) * 𝓕 φ (S * t)‖ * (1 + t ^ 2) ^ d = S * g (S * t) := by
    simp only [g, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hS0]
    rw [show S * t / S = t by field_simp]
    ring
  have hgle (v : ℝ) : g v ≤ ‖𝓕 φ v‖ * (1 + v ^ 2) ^ d := by
    refine mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) ?_ d) (norm_nonneg _)
    have : (v / S) ^ 2 ≤ v ^ 2 := by
      rw [div_pow]
      exact div_le_self (sq_nonneg v) (one_le_pow₀ hS)
    linarith
  have hgm : AEStronglyMeasurable g volume :=
    ((𝓕 φ).continuous.norm.mul ((continuous_const.add ((continuous_id.div_const S).pow 2)).pow d)).aestronglyMeasurable
  have hgi : Integrable g := hw.mono' hgm (Filter.Eventually.of_forall fun v => by
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    exact hgle v)
  have hcomp : Integrable (fun t : ℝ => S * g (S * t)) := (hgi.comp_mul_left' hS0.ne').const_mul S
  refine ⟨hcomp.congr (Filter.Eventually.of_forall fun t => (hg t).symm), ?_⟩
  simp_rw [hg]
  rw [integral_const_mul, Measure.integral_comp_mul_left g S, abs_of_pos (inv_pos.mpr hS0), smul_eq_mul,
    ← mul_assoc, mul_inv_cancel₀ hS0.ne', one_mul]
  exact integral_mono hgi hw hgle

end WaveTurbulence.Flower.FiltCoh
