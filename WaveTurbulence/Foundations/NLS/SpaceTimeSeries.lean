/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.NLS.GoodCurve

/-!
# Smoothness of space–time Fourier series on `[0, T] × ℝ^d`

`stSeries L b (t, x) = ∑ₙ bₙ(t) e^{2πi (n/L)·x}`. If the coefficient curve `b` is
`GoodCurve T m b` (its first `m` time derivatives decay rapidly, uniformly on `[0, T]`), then
`stSeries L b` is `C^m` on the closed slab `[0, T] × ℝ^d` (`contDiffOn_stSeries`); if this holds for
every `m`, it is `C^∞` there (`contDiffOn_stSeries_infty`).

The first derivative is computed termwise within the convex slab
(`hasFDerivWithinAt_stSeries`, via `hasFDerivWithinAt_tsum_of_convex`); it is again a combination
of space–time series of good curves (the time derivative and the curves `(2πi nⱼ/L) bₙ`), which
drives the induction on `m`.
-/

public section

noncomputable section

open MeasureTheory Complex Set Filter Topology
open scoped ContDiff

namespace WaveTurbulence.NLS

variable {d : ℕ}

/-- The space–time Fourier series `∑ₙ bₙ(t) e^{2πi (n/L)·x}`. -/
@[expose] def stSeries (L : ℝ) (b : ℝ → (Fin d → ℤ) → ℂ) (p : ℝ × (Fin d → ℝ)) : ℂ :=
  ∑' n, b p.1 n * torusChar L n p.2

/-- The multiplier `2πi nⱼ / L` of `∂ⱼ`. -/
@[expose] def phaseWeight (L : ℝ) (j : Fin d) (n : Fin d → ℤ) : ℂ :=
  ((2 * Real.pi * ((n j : ℝ) / L) : ℝ) : ℂ) * I

theorem norm_phaseWeight_le {L : ℝ} (hL : 0 < L) (j : Fin d) (n : Fin d → ℤ) :
    ‖phaseWeight L j n‖ ≤ (2 * Real.pi / L) * (1 + ‖n‖) ^ 1 := by
  rw [phaseWeight, norm_mul, norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs, pow_one,
    abs_mul, abs_div, abs_of_pos hL, abs_of_pos (by positivity : (0 : ℝ) < 2 * Real.pi)]
  have hj : |(n j : ℝ)| ≤ ‖n‖ := by
    rw [← Int.norm_eq_abs]
    exact norm_le_pi_norm n j
  calc 2 * Real.pi * (|(n j : ℝ)| / L) = (2 * Real.pi / L) * |(n j : ℝ)| := by ring
    _ ≤ (2 * Real.pi / L) * (1 + ‖n‖) := by gcongr; linarith

theorem torusPhase_apply_eq_sum (L : ℝ) (n : Fin d → ℤ) (v : Fin d → ℝ) :
    torusPhase L n v = ∑ j, phaseWeight L j n * v j := by
  rw [torusPhase_apply]
  simp only [phaseWeight]
  push_cast
  rw [Finset.mul_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun j _ => ?_
  ring

theorem hasFDerivAt_torusChar (L : ℝ) (n : Fin d → ℤ) (x : Fin d → ℝ) :
    HasFDerivAt (torusChar L n) (torusChar L n x • torusPhase L n) x := by
  have h := (torusPhase L n).hasFDerivAt.cexp (x := x)
  have he : (fun y => exp (torusPhase L n y)) = torusChar L n :=
    funext fun y => (torusChar_eq_exp_torusPhase L n y).symm
  rw [he] at h
  rwa [← torusChar_eq_exp_torusPhase] at h

/-- The coordinate maps `(t, x) ↦ t` and `(t, x) ↦ xⱼ` as real-linear maps into `ℂ`. -/
@[expose] def timeCLM : ℝ × (Fin d → ℝ) →L[ℝ] ℂ :=
  Complex.ofRealCLM.comp (ContinuousLinearMap.fst ℝ ℝ (Fin d → ℝ))

@[expose] def spaceCLM (j : Fin d) : ℝ × (Fin d → ℝ) →L[ℝ] ℂ :=
  Complex.ofRealCLM.comp ((ContinuousLinearMap.proj j).comp
    (ContinuousLinearMap.snd ℝ ℝ (Fin d → ℝ)))

/-- The derivative of `stSeries L b` given the time derivative `b'`. -/
@[expose] def stDeriv (L : ℝ) (b b' : ℝ → (Fin d → ℤ) → ℂ) (p : ℝ × (Fin d → ℝ)) :
    ℝ × (Fin d → ℝ) →L[ℝ] ℂ :=
  stSeries L b' p • timeCLM + ∑ j, stSeries L (fun t n => phaseWeight L j n * b t n) p • spaceCLM j

variable {L T : ℝ}

theorem summable_stSeries {b : ℝ → (Fin d → ℤ) → ℂ} (hb : UnifRapid T b) {t : ℝ}
    (ht : t ∈ Icc 0 T) (x : Fin d → ℝ) : Summable fun n => b t n * torusChar L n x := by
  obtain ⟨C, -, hC⟩ := hb.exists_bound
  exact Summable.of_norm_bounded (summable_inv_one_add_norm_pow.mul_left C)
    fun n => by rw [norm_mul, norm_torusChar, mul_one]; exact hC t ht n

theorem continuousOn_stSeries {b : ℝ → (Fin d → ℤ) → ℂ}
    (hc : ∀ n, ContinuousOn (fun t => b t n) (Icc 0 T)) (hb : UnifRapid T b) :
    ContinuousOn (stSeries L b) (Icc 0 T ×ˢ univ) := by
  obtain ⟨C, -, hC⟩ := hb.exists_bound
  refine continuousOn_tsum (fun n => ?_) (summable_inv_one_add_norm_pow.mul_left C)
    (fun n p hp => ?_)
  · exact ((hc n).comp continuousOn_fst (fun p hp => hp.1)).mul
      ((continuous_torusChar L n).comp continuous_snd).continuousOn
  · rw [norm_mul, norm_torusChar, mul_one]
    exact hC p.1 hp.1 n

theorem hasFDerivWithinAt_stSeries (hL : 0 < L) {b b' : ℝ → (Fin d → ℤ) → ℂ}
    (hb : UnifRapid T b) (hb' : UnifRapid T b')
    (hd : ∀ n, ∀ t ∈ Icc 0 T, HasDerivWithinAt (fun s => b s n) (b' t n) (Icc 0 T) t)
    {p : ℝ × (Fin d → ℝ)} (hp : p ∈ Icc 0 T ×ˢ univ) :
    HasFDerivWithinAt (stSeries L b) (stDeriv L b b' p) (Icc 0 T ×ˢ univ) p := by
  obtain ⟨C1, hC1, hC1'⟩ := hb.exists_majorant 1
  obtain ⟨C0, hC0, hC0'⟩ := hb'.exists_majorant 0
  set S := Icc 0 T ×ˢ (univ : Set (Fin d → ℝ))
  set T' : (Fin d → ℤ) → ℝ × (Fin d → ℝ) → ℝ × (Fin d → ℝ) →L[ℝ] ℂ := fun n q =>
    b q.1 n • ((torusChar L n q.2 • torusPhase L n).comp (ContinuousLinearMap.snd ℝ ℝ _)) +
      torusChar L n q.2 • ((ContinuousLinearMap.toSpanSingleton ℝ (b' q.1 n)).comp
        (ContinuousLinearMap.fst ℝ ℝ _)) with hT'
  refine hasFDerivWithinAt_tsum_of_convex ((convex_Icc 0 T).prod convex_univ)
    (T := fun n q => b q.1 n * torusChar L n q.2) (T' := T')
    (u := fun n => C1 * ((1 + ‖n‖) ^ (d + 1))⁻¹ * (2 * Real.pi * d / L) +
      C0 * ((1 + ‖n‖) ^ (d + 1))⁻¹)
    (((summable_inv_one_add_norm_pow.mul_left C1).mul_right _).add
      (summable_inv_one_add_norm_pow.mul_left C0))
    (fun n q hq => ?_) (fun n q hq => ?_) (fun q hq => summable_stSeries hb hq.1 q.2) hp
    (fun w => ?_)
  · -- termwise derivative
    have h1 : HasFDerivWithinAt (fun q : ℝ × (Fin d → ℝ) => b q.1 n)
        ((ContinuousLinearMap.toSpanSingleton ℝ (b' q.1 n)).comp
          (ContinuousLinearMap.fst ℝ ℝ _)) S q :=
      (hd n q.1 hq.1).hasFDerivWithinAt.comp q hasFDerivWithinAt_fst (fun r hr => hr.1)
    have h2 : HasFDerivWithinAt (fun q : ℝ × (Fin d → ℝ) => torusChar L n q.2)
        ((torusChar L n q.2 • torusPhase L n).comp (ContinuousLinearMap.snd ℝ ℝ _)) S q :=
      ((hasFDerivAt_torusChar L n q.2).comp q hasFDerivAt_snd).hasFDerivWithinAt
    exact h1.mul h2
  · -- the bound
    have hb1 := hC1' q.1 hq.1 n
    have hb0 := hC0' q.1 hq.1 n
    rw [pow_one] at hb1
    rw [pow_zero, one_mul] at hb0
    refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
    · refine (norm_smul_le (b q.1 n) ((torusChar L n q.2 • torusPhase L n).comp
        (ContinuousLinearMap.snd ℝ ℝ (Fin d → ℝ)))).trans ?_
      refine (mul_le_mul_of_nonneg_left (ContinuousLinearMap.opNorm_comp_le _ _)
        (norm_nonneg _)).trans ?_
      have hphase := norm_torusPhase_le hL n
      calc ‖b q.1 n‖ * (‖torusChar L n q.2 • torusPhase L n‖ *
            ‖ContinuousLinearMap.snd ℝ ℝ (Fin d → ℝ)‖)
          ≤ ‖b q.1 n‖ * ((1 * (2 * Real.pi * d / L * ‖n‖)) * 1) := by
            gcongr
            · refine (norm_smul_le (torusChar L n q.2) (torusPhase L n)).trans ?_
              rw [norm_torusChar]
              gcongr
            · exact ContinuousLinearMap.norm_snd_le ℝ ℝ _
        _ ≤ ‖b q.1 n‖ * (1 + ‖n‖) * (2 * Real.pi * d / L) := by
            have : 0 ≤ 2 * Real.pi * d / L := by positivity
            nlinarith [norm_nonneg (b q.1 n), norm_nonneg n]
        _ ≤ C1 * ((1 + ‖n‖) ^ (d + 1))⁻¹ * (2 * Real.pi * d / L) :=
            mul_le_mul_of_nonneg_right (by rw [mul_comm]; exact hb1) (by positivity)
    · refine (norm_smul_le (torusChar L n q.2) ((ContinuousLinearMap.toSpanSingleton ℝ
        (b' q.1 n)).comp (ContinuousLinearMap.fst ℝ ℝ (Fin d → ℝ)))).trans ?_
      rw [norm_torusChar, one_mul]
      refine (ContinuousLinearMap.opNorm_comp_le _ _).trans ?_
      rw [ContinuousLinearMap.norm_toSpanSingleton]
      exact (mul_le_of_le_one_right (norm_nonneg _) (ContinuousLinearMap.norm_fst_le ℝ ℝ _)).trans
        hb0
  · -- the value of the derivative
    have h0 := ((summable_stSeries (L := L) hb' hp.1 p.2).hasSum).mul_right ((w.1 : ℝ) : ℂ)
    have hj : ∀ j, HasSum (fun n => phaseWeight L j n * b p.1 n * torusChar L n p.2 *
        ((w.2 j : ℝ) : ℂ))
        (stSeries L (fun t n => phaseWeight L j n * b t n) p * ((w.2 j : ℝ) : ℂ)) := by
      intro j
      have hs : Summable fun n => phaseWeight L j n * b p.1 n * torusChar L n p.2 :=
        summable_stSeries (L := L) (b := fun t n => phaseWeight L j n * b t n)
          (hb.of_norm_le (A := 2 * Real.pi / L) (k := 1) fun t _ n => by
            rw [norm_mul]
            exact mul_le_mul_of_nonneg_right (norm_phaseWeight_le hL j n) (norm_nonneg _))
          hp.1 p.2
      exact hs.hasSum.mul_right _
    have hsum := h0.add (hasSum_sum (s := Finset.univ) fun j _ => hj j)
    convert hsum using 1
    · funext n
      simp only [hT', add_apply, smul_apply,
        ContinuousLinearMap.comp_apply, ContinuousLinearMap.toSpanSingleton_apply,
        ContinuousLinearMap.coe_fst', ContinuousLinearMap.coe_snd', smul_eq_mul,
        torusPhase_apply_eq_sum, Complex.real_smul]
      rw [Finset.mul_sum, Finset.mul_sum, add_comm]
      congr 1
      · ring
      · exact Finset.sum_congr rfl fun j _ => by ring
    · simp only [stDeriv, add_apply, FunLike.coe_sum,
        Finset.sum_apply, smul_apply, timeCLM, spaceCLM,
        ContinuousLinearMap.comp_apply, ContinuousLinearMap.coe_fst', ContinuousLinearMap.coe_snd',
        ContinuousLinearMap.proj_apply, Complex.ofRealCLM_apply, smul_eq_mul]
      rfl

theorem GoodCurve.phaseWeight (hL : 0 < L) {m : ℕ} {b : ℝ → (Fin d → ℤ) → ℂ}
    (hb : GoodCurve T m b) (j : Fin d) :
    GoodCurve T m (fun t n => WaveTurbulence.NLS.phaseWeight L j n * b t n) :=
  hb.weight _ (A := 2 * Real.pi / L) (k := 1) (norm_phaseWeight_le hL j)

/-- A space–time Fourier series with `GoodCurve T m` coefficients is `C^m` on `[0, T] × ℝ^d`. -/
theorem contDiffOn_stSeries (hL : 0 < L) (hT : 0 < T) :
    ∀ (m : ℕ) {b : ℝ → (Fin d → ℤ) → ℂ}, GoodCurve T m b →
      ContDiffOn ℝ m (stSeries L b) (Icc 0 T ×ˢ univ)
  | 0, b, hb => contDiffOn_zero.2 (continuousOn_stSeries hb.continuousOn hb.unifRapid)
  | m + 1, b, hb => by
    obtain ⟨hc, hr, b', hb', hd⟩ := hb
    have hS : UniqueDiffOn ℝ (Icc 0 T ×ˢ (univ : Set (Fin d → ℝ))) :=
      (uniqueDiffOn_Icc hT).prod uniqueDiffOn_univ
    have hbm : GoodCurve T m b :=
      GoodCurve.mono (show GoodCurve T (m + 1) b from ⟨hc, hr, b', hb', hd⟩)
    have hder : ∀ p ∈ Icc 0 T ×ˢ (univ : Set (Fin d → ℝ)),
        HasFDerivWithinAt (stSeries L b) (stDeriv L b b' p) (Icc 0 T ×ˢ univ) p :=
      fun p hp => hasFDerivWithinAt_stSeries hL hr hb'.unifRapid hd hp
    have hcd : ContDiffOn ℝ m (stDeriv L b b') (Icc 0 T ×ˢ univ) := by
      have h1 := (contDiffOn_stSeries hL hT m hb').smul
        (contDiffOn_const (c := (timeCLM : ℝ × (Fin d → ℝ) →L[ℝ] ℂ)))
      have h2 := ContDiffOn.sum (s := Finset.univ) (f := fun j p =>
        stSeries L (fun t n => WaveTurbulence.NLS.phaseWeight L j n * b t n) p • spaceCLM j)
        (fun j _ => (contDiffOn_stSeries hL hT m (hbm.phaseWeight hL j)).smul contDiffOn_const)
      exact h1.add h2
    rw [show ((m + 1 : ℕ) : WithTop ℕ∞) = (m : WithTop ℕ∞) + 1 by push_cast; rfl,
      contDiffOn_succ_iff_fderivWithin hS]
    exact ⟨fun p hp => (hder p hp).differentiableWithinAt, fun h => by simp at h,
      hcd.congr fun p hp => (hder p hp).fderivWithin (hS p hp)⟩

/-- A space–time Fourier series whose coefficient curve is `GoodCurve T m` for every `m` is `C^∞`
on `[0, T] × ℝ^d`. -/
theorem contDiffOn_stSeries_infty (hL : 0 < L) (hT : 0 < T) {b : ℝ → (Fin d → ℤ) → ℂ}
    (hb : ∀ m, GoodCurve T m b) : ContDiffOn ℝ ∞ (stSeries L b) (Icc 0 T ×ˢ univ) :=
  contDiffOn_infty.2 fun m => contDiffOn_stSeries hL hT m (hb m)

/-- The time derivative of a space–time series, termwise, within `[0, T]`. -/
theorem hasDerivWithinAt_stSeries_time (hL : 0 < L) {b b' : ℝ → (Fin d → ℤ) → ℂ}
    (hb : UnifRapid T b) (hb' : UnifRapid T b')
    (hd : ∀ n, ∀ t ∈ Icc 0 T, HasDerivWithinAt (fun s => b s n) (b' t n) (Icc 0 T) t)
    {t : ℝ} (ht : t ∈ Icc 0 T) (x : Fin d → ℝ) :
    HasDerivWithinAt (fun s => stSeries L b (s, x)) (stSeries L b' (t, x)) (Icc 0 T) t := by
  have h := (hasFDerivWithinAt_stSeries (L := L) hL hb hb' hd (p := (t, x)) ⟨ht, mem_univ _⟩).comp_hasDerivWithinAt
    t ((hasDerivWithinAt_id t (Icc 0 T)).prodMk (hasDerivWithinAt_const t (Icc 0 T) x))
    (fun s hs => Set.mk_mem_prod hs (mem_univ x))
  refine h.congr_deriv ?_
  simp [stDeriv, timeCLM, spaceCLM]

end WaveTurbulence.NLS
