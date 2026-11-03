/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Fourier.CutoffPhase
public import WaveTurbulence.Frozen.Defs.Mom

/-!
# Oscillatory bilinear integrals with localized amplitudes (packet NT5)

Notation for DH23 Lemmas 6.5, 6.7 and TARGET Lemma 5.2. We write `e(z) = exp(2πiz)`
(`Real.fourierChar`), `χ₀` for the fixed tensor cutoff of TARGET L617–L623
(`Fourier.chi0MomSchwartz`), and `λ` (`lam`, since `λ` is a Lean keyword) for the localization
scale.

* `chiScaled lam x = χ₀(x / λ)`;
* `ntIntegral lam Φ a b ξ ζ s = ∫∫ χ₀((x-a)/λ) χ₀((y-b)/λ) Φ(x,y) e(ξ·x + ζ·y + s⟨x,y⟩) dx dy`
  (iterated, `y` outer, as the landed `Fourier.bilinearPhaseIntegral`);
* `NTBounds N D Φ`: the derivative bounds (NTphibounds) of DH23 L1016, in the form used here:
  `Φ(·, y)` and `Φ(x, ·)` are `C^N` with `‖D^k Φ‖ ≤ D` for `k ≤ N` (the pure `x`- and
  `y`-derivatives; the source bounds all `∂_x^α ∂_y^β`, `|α|, |β| ≤ 10d`, coordinatewise, which
  implies this with `D` replaced by `d^N D`).
-/

public section

noncomputable section

open MeasureTheory Metric WithLp
open scoped SchwartzMap ContDiff

namespace WaveTurbulence.NTSP

variable {d : ℕ}

/-- The integer vector `g ∈ ℤ^d` as a point of `ℝ^d`. -/
@[expose] def intVec (g : Fin d → ℤ) : Mom d := toLp 2 (fun i => (g i : ℝ))

/-- The rescaled cutoff `χ₀(x / λ)`. -/
@[expose] def chiScaled (lam : ℝ) (x : Mom d) : ℂ := Fourier.chi0MomSchwartz d (lam⁻¹ • x)

/-- The localized bilinear oscillatory integral of DH23 Lemma 6.5 (DH23 L1019, L1027):
`∫∫ χ₀((x-a)/λ) χ₀((y-b)/λ) Φ(x,y) e(ξ·x + ζ·y + s⟨x,y⟩) dx dy`. -/
@[expose] def ntIntegral (lam : ℝ) (Φ : Mom d → Mom d → ℂ) (a b ξ ζ : Mom d) (s : ℝ) : ℂ :=
  ∫ y, ∫ x, Real.fourierChar (inner ℝ x ξ + inner ℝ y ζ + s * inner ℝ x y) •
    (chiScaled lam (x - a) * chiScaled lam (y - b) * Φ x y)

/-- The derivative bounds (NTphibounds) of DH23 L1016 for a function of `(x, y)`, through order
`N`, in each variable separately. -/
structure NTBounds (N : ℕ) (D : ℝ) (Φ : Mom d → Mom d → ℂ) : Prop where
  contDiff_left : ∀ y, ContDiff ℝ N (fun x => Φ x y)
  contDiff_right : ∀ x, ContDiff ℝ N (fun y => Φ x y)
  bound_left : ∀ k ≤ N, ∀ x y, ‖iteratedFDeriv ℝ k (fun x => Φ x y) x‖ ≤ D
  bound_right : ∀ k ≤ N, ∀ x y, ‖iteratedFDeriv ℝ k (fun y => Φ x y) y‖ ≤ D

/-! ### The integer embedding -/

theorem intVec_apply (g : Fin d → ℤ) (i : Fin d) : intVec g i = (g i : ℝ) := rfl

theorem intVec_add (g h : Fin d → ℤ) : intVec (g + h) = intVec g + intVec h := by
  ext i
  simp [intVec]

theorem intVec_sub (g h : Fin d → ℤ) : intVec (g - h) = intVec g - intVec h := by
  ext i
  simp [intVec]

theorem intVec_zero : intVec (0 : Fin d → ℤ) = 0 := by
  ext i
  simp [intVec]

/-- The Euclidean norm of an integer vector dominates its sup norm. -/
theorem norm_le_norm_intVec (g : Fin d → ℤ) : (‖g‖ : ℝ) ≤ ‖intVec g‖ := by
  refine (pi_norm_le_iff_of_nonneg (norm_nonneg _)).2 fun i => ?_
  have h := PiLp.norm_apply_le (intVec g) i
  rw [intVec_apply, Real.norm_eq_abs, ← Int.cast_abs] at h
  rw [Int.norm_eq_abs]
  exact_mod_cast h

/-- A nonzero integer vector has Euclidean norm at least `1`. -/
theorem one_le_norm_intVec {g : Fin d → ℤ} (hg : g ≠ 0) : 1 ≤ ‖intVec g‖ := by
  obtain ⟨i, hi⟩ := Function.ne_iff.1 hg
  have h := PiLp.norm_apply_le (intVec g) i
  rw [intVec_apply, Real.norm_eq_abs] at h
  have : (1 : ℝ) ≤ |(g i : ℝ)| := by
    rw [← Int.cast_abs]
    exact_mod_cast Int.one_le_abs hi
  linarith

/-! ### The rescaled cutoff -/

theorem chiScaled_apply (lam : ℝ) (x : Mom d) :
    chiScaled lam x = (Fourier.chi0Tensor (ofLp (lam⁻¹ • x)) : ℂ) := rfl

theorem norm_chiScaled_le_one (lam : ℝ) (x : Mom d) : ‖chiScaled lam x‖ ≤ 1 := by
  rw [chiScaled_apply, Complex.norm_real, Real.norm_of_nonneg (Fourier.chi0Tensor_nonneg _)]
  exact Fourier.chi0Tensor_le_one _

/-- `χ₀(x/λ)` vanishes unless `‖x‖ ≤ λ √d`. -/
theorem norm_le_of_chiScaled_ne_zero {lam : ℝ} (hlam : 0 < lam) {x : Mom d}
    (hx : chiScaled lam x ≠ 0) : ‖x‖ ≤ lam * Real.sqrt d := by
  have hi : ∀ i, |x i| ≤ lam := fun i => by
    by_contra hcon
    apply hx
    rw [chiScaled_apply]
    have h1 : 1 ≤ |ofLp (lam⁻¹ • x) i| := by
      rw [ofLp_smul, Pi.smul_apply, smul_eq_mul, abs_mul, abs_inv, abs_of_pos hlam,
        inv_mul_eq_div, le_div_iff₀ hlam, one_mul]
      exact (not_le.1 hcon).le
    rw [Fourier.chi0Tensor_eq_zero i h1, Complex.ofReal_zero]
  rw [EuclideanSpace.norm_eq, ← Real.sqrt_sq hlam.le, ← Real.sqrt_mul (sq_nonneg _)]
  refine Real.sqrt_le_sqrt ?_
  calc ∑ i, ‖x i‖ ^ 2 ≤ ∑ _i : Fin d, lam ^ 2 := by
        refine Finset.sum_le_sum fun i _ => ?_
        rw [Real.norm_eq_abs]
        exact pow_le_pow_left₀ (abs_nonneg _) (hi i) 2
    _ = lam ^ 2 * d := by simp [mul_comm]

theorem contDiff_chiScaled (lam : ℝ) : ContDiff ℝ ∞ (chiScaled (d := d) lam) := by
  have h : chiScaled (d := d) lam =
      fun x => Fourier.chi0MomSchwartz d ((lam⁻¹ • ContinuousLinearMap.id ℝ (Mom d)) x) := by
    funext x
    rfl
  rw [h]
  exact (Fourier.chi0MomSchwartz d).smooth ⊤ |>.comp (ContinuousLinearMap.contDiff _)

/-- The derivative bound constants of the fixed cutoff. -/
@[expose] def chiDerivConst (d n : ℕ) : ℝ :=
  SchwartzMap.seminorm ℝ 0 n (Fourier.chi0MomSchwartz d)

theorem chiDerivConst_nonneg (d n : ℕ) : 0 ≤ chiDerivConst d n := apply_nonneg _ _

/-- Derivatives of `x ↦ χ₀((x - a)/λ)` are bounded independently of `λ ≥ 1` and `a`. -/
theorem norm_iteratedFDeriv_chiScaled_le {lam : ℝ} (hlam : 1 ≤ lam) (a : Mom d) (n : ℕ)
    (x : Mom d) :
    ‖iteratedFDeriv ℝ n (fun x => chiScaled lam (x - a)) x‖ ≤ chiDerivConst d n := by
  have h0 : 0 < lam := lt_of_lt_of_le one_pos hlam
  set g : Mom d →L[ℝ] Mom d := lam⁻¹ • ContinuousLinearMap.id ℝ (Mom d)
  have hfun : (fun x => chiScaled lam (x - a)) =
      fun x => ((Fourier.chi0MomSchwartz d : Mom d → ℂ) ∘ g) (x - a) := by
    funext x
    rfl
  rw [hfun, iteratedFDeriv_comp_sub]
  have hg : ‖g‖ ≤ 1 := by
    refine (norm_smul_le (lam⁻¹) (ContinuousLinearMap.id ℝ (Mom d))).trans ?_
    rw [Real.norm_of_nonneg (inv_nonneg.2 h0.le)]
    calc lam⁻¹ * ‖ContinuousLinearMap.id ℝ (Mom d)‖ ≤ lam⁻¹ * 1 :=
          mul_le_mul_of_nonneg_left ContinuousLinearMap.norm_id_le (inv_nonneg.2 h0.le)
      _ ≤ 1 := by rw [mul_one]; exact inv_le_one_of_one_le₀ hlam
  rw [g.iteratedFDeriv_comp_right ((Fourier.chi0MomSchwartz d).smooth ⊤) _ (by simp)]
  refine (ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _).trans ?_
  calc ‖iteratedFDeriv ℝ n (Fourier.chi0MomSchwartz d) (g (x - a))‖ * ∏ _i : Fin n, ‖g‖
      ≤ chiDerivConst d n * 1 := by
        refine mul_le_mul ((Fourier.chi0MomSchwartz d).norm_iteratedFDeriv_le_seminorm ℝ n _)
          ?_ (Finset.prod_nonneg fun _ _ => norm_nonneg _) (chiDerivConst_nonneg d n)
        rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
        exact pow_le_one₀ (norm_nonneg _) hg
    _ = chiDerivConst d n := mul_one _

/-! ### Integrals over the support -/

/-- The volume of the unit ball of `ℝ^d`. -/
@[expose] def ballVol (d : ℕ) : ℝ := (volume (ball (0 : Mom d) 1)).toReal

theorem ballVol_nonneg (d : ℕ) : 0 ≤ ballVol d := ENNReal.toReal_nonneg

/-- A function bounded by `B` and vanishing off `closedBall a r` has `∫ ‖f‖ ≤ B r^d |B₁|`. -/
theorem integral_norm_le_of_support {E : Type*} [NormedAddCommGroup E] {f : Mom d → E}
    {a : Mom d} {r B : ℝ} (hr : 0 ≤ r)
    (hB : ∀ x, ‖f x‖ ≤ B) (hf : ∀ x, f x ≠ 0 → x ∈ closedBall a r) :
    ∫ x, ‖f x‖ ≤ B * (r ^ d * ballVol d) := by
  have hB0 : 0 ≤ B := (norm_nonneg _).trans (hB 0)
  have hfin : volume (closedBall a r) ≠ ⊤ := measure_closedBall_lt_top.ne
  have hle : ∀ x, ‖f x‖ ≤ (closedBall a r).indicator (fun _ => B) x := fun x => by
    by_cases hx : x ∈ closedBall a r
    · rw [Set.indicator_of_mem hx]; exact hB x
    · rw [Set.indicator_of_notMem hx]
      have : f x = 0 := by by_contra h; exact hx (hf x h)
      rw [this, norm_zero]
  have hint : Integrable ((closedBall a r).indicator (fun _ : Mom d => B)) :=
    (integrableOn_const hfin).integrable_indicator measurableSet_closedBall
  calc ∫ x, ‖f x‖ ≤ ∫ x, (closedBall a r).indicator (fun _ => B) x :=
        integral_mono_of_nonneg (Filter.Eventually.of_forall fun _ => norm_nonneg _) hint
          (Filter.Eventually.of_forall hle)
    _ = B * (r ^ d * ballVol d) := by
        rw [integral_indicator_const _ measurableSet_closedBall, smul_eq_mul, mul_comm,
          measureReal_def, Measure.addHaar_closedBall _ _ hr, ENNReal.toReal_mul,
          ENNReal.toReal_ofReal (by positivity), finrank_euclideanSpace_fin, ballVol]

theorem integral_norm_chiScaled_le {lam : ℝ} (hlam : 0 < lam) (a : Mom d) :
    ∫ y, ‖chiScaled lam (y - a)‖ ≤ (Real.sqrt d) ^ d * ballVol d * lam ^ d := by
  have h := integral_norm_le_of_support (f := fun y => chiScaled lam (y - a)) (a := a)
    (r := lam * Real.sqrt d) (by positivity) (fun y => norm_chiScaled_le_one lam _)
    (fun y hy => by
      rw [mem_closedBall, dist_eq_norm]
      exact norm_le_of_chiScaled_ne_zero hlam hy)
  calc ∫ y, ‖chiScaled lam (y - a)‖ ≤ 1 * ((lam * Real.sqrt d) ^ d * ballVol d) := h
    _ = (Real.sqrt d) ^ d * ballVol d * lam ^ d := by ring

theorem integrable_chiScaled {lam : ℝ} (hlam : 0 < lam) (a : Mom d) :
    Integrable (fun y => chiScaled lam (y - a)) := by
  have hfin : volume (closedBall a (lam * Real.sqrt d)) ≠ ⊤ := measure_closedBall_lt_top.ne
  refine Integrable.mono' ((integrableOn_const hfin).integrable_indicator
    measurableSet_closedBall (f := fun _ => (1 : ℝ)))
    ((contDiff_chiScaled lam).continuous.comp (continuous_sub_right a)).aestronglyMeasurable
    (Filter.Eventually.of_forall fun y => ?_)
  by_cases hy : chiScaled lam (y - a) = 0
  · rw [hy, norm_zero]
    exact Set.indicator_nonneg (fun _ _ => zero_le_one) _
  · have hm : y ∈ closedBall a (lam * Real.sqrt d) := by
      rw [mem_closedBall, dist_eq_norm]
      exact norm_le_of_chiScaled_ne_zero hlam hy
    rw [Set.indicator_of_mem hm]
    exact norm_chiScaled_le_one lam _

end WaveTurbulence.NTSP
