/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.NTSP.Decay

/-!
# Per-term bounds for the localized bilinear integral

For `Φ` with the bounds `NTBounds N D Φ` (`N ≥ d + 1`) and `λ ≥ 1`, the integral
`J = ntIntegral λ Φ a b ξ ζ s` satisfies (`norm_ntIntegral_le`)

  `|J| ≤ C D λ^{2d} · min(⟨s⟩^{-d}, (1 + (|ξ + s b| - λ√d|s|)₊)^{-N}, (1 + (|ζ + s a| - λ√d|s|)₊)^{-N})`

with `⟨s⟩ = 1 + |s|` and `C` depending only on `d, N`. The first bound is stationary phase for
`e(s⟨x,y⟩)` (integrate `x` first: the Fourier transform of the amplitude at `-(ξ + s y)` decays
like `⟨ξ + s y⟩^{-(d+1)}`, and `∫ ⟨ξ + s y⟩^{-(d+1)} dy = |s|^{-d} ∫ ⟨w⟩^{-(d+1)} dw`). The other two
are non-stationary phase in `x` (resp. `y`): on the support, `|y - b| ≤ λ√d`, so the frequency
`ξ + s y` has size at least `|ξ + s b| - λ√d|s|` (resp. after exchanging the order of integration).
These are the bounds used in DH23 L1033–L1072 and TARGET L964–L968.
-/

public section

noncomputable section

open MeasureTheory Metric
open scoped ContDiff

namespace WaveTurbulence.NTSP

variable {d : ℕ}

/-! ### Joint continuity -/

theorem NTBounds.norm_sub_le_left {N : ℕ} {D : ℝ} {Φ : Mom d → Mom d → ℂ}
    (hΦ : NTBounds N D Φ) (hN : 1 ≤ N) (x x' y : Mom d) :
    ‖Φ x y - Φ x' y‖ ≤ D * ‖x - x'‖ := by
  have hdiff : Differentiable ℝ (fun x => Φ x y) :=
    (hΦ.contDiff_left y).differentiable (by exact_mod_cast (by omega : N ≠ 0))
  refine (convex_univ.norm_image_sub_le_of_norm_fderiv_le (fun z _ => hdiff z)
    (fun z _ => ?_) (Set.mem_univ x') (Set.mem_univ x))
  rw [← norm_iteratedFDeriv_one]
  exact hΦ.bound_left 1 hN z y

theorem NTBounds.norm_sub_le_right {N : ℕ} {D : ℝ} {Φ : Mom d → Mom d → ℂ}
    (hΦ : NTBounds N D Φ) (hN : 1 ≤ N) (x y y' : Mom d) :
    ‖Φ x y - Φ x y'‖ ≤ D * ‖y - y'‖ := by
  have hdiff : Differentiable ℝ (fun y => Φ x y) :=
    (hΦ.contDiff_right x).differentiable (by exact_mod_cast (by omega : N ≠ 0))
  refine (convex_univ.norm_image_sub_le_of_norm_fderiv_le (fun z _ => hdiff z)
    (fun z _ => ?_) (Set.mem_univ y') (Set.mem_univ y))
  rw [← norm_iteratedFDeriv_one]
  exact hΦ.bound_right 1 hN x z

theorem NTBounds.nonneg {N : ℕ} {D : ℝ} {Φ : Mom d → Mom d → ℂ} (hΦ : NTBounds N D Φ) :
    0 ≤ D :=
  (norm_nonneg _).trans (hΦ.bound_left 0 (Nat.zero_le _) 0 0)

theorem NTBounds.norm_le {N : ℕ} {D : ℝ} {Φ : Mom d → Mom d → ℂ} (hΦ : NTBounds N D Φ)
    (x y : Mom d) : ‖Φ x y‖ ≤ D := by
  have h := hΦ.bound_left 0 (Nat.zero_le _) x y
  rwa [norm_iteratedFDeriv_zero] at h

theorem NTBounds.continuous {N : ℕ} {D : ℝ} {Φ : Mom d → Mom d → ℂ} (hΦ : NTBounds N D Φ)
    (hN : 1 ≤ N) : Continuous (fun p : Mom d × Mom d => Φ p.1 p.2) := by
  refine (LipschitzWith.of_dist_le_mul (K := Real.toNNReal (2 * D)) fun p q => ?_).continuous
  rw [dist_eq_norm, dist_eq_norm, Real.coe_toNNReal _ (by linarith [hΦ.nonneg])]
  have h1 := hΦ.norm_sub_le_left hN p.1 q.1 p.2
  have h2 := hΦ.norm_sub_le_right hN q.1 p.2 q.2
  have hx : ‖p.1 - q.1‖ ≤ ‖p - q‖ := norm_fst_le (p - q)
  have hy : ‖p.2 - q.2‖ ≤ ‖p - q‖ := norm_snd_le (p - q)
  have hD := hΦ.nonneg
  calc ‖Φ p.1 p.2 - Φ q.1 q.2‖ ≤ ‖Φ p.1 p.2 - Φ q.1 p.2‖ + ‖Φ q.1 p.2 - Φ q.1 q.2‖ :=
        norm_sub_le_norm_sub_add_norm_sub _ _ _
    _ ≤ D * ‖p - q‖ + D * ‖p - q‖ := add_le_add (h1.trans (mul_le_mul_of_nonneg_left hx hD))
          (h2.trans (mul_le_mul_of_nonneg_left hy hD))
    _ = 2 * D * ‖p - q‖ := by ring

/-! ### The inner integrals -/

theorem inner_integral_eq (lam : ℝ) (Φ : Mom d → Mom d → ℂ) (a b ξ ζ y : Mom d) (s : ℝ) :
    ∫ x, Real.fourierChar (inner ℝ x ξ + inner ℝ y ζ + s * inner ℝ x y) •
        (chiScaled lam (x - a) * chiScaled lam (y - b) * Φ x y) =
      (Real.fourierChar (inner ℝ y ζ) : ℂ) * chiScaled lam (y - b) *
        ∫ x, Real.fourierChar (inner ℝ x (ξ + s • y)) • (chiScaled lam (x - a) * Φ x y) := by
  simp only [Circle.smul_def, smul_eq_mul]
  rw [← integral_const_mul]
  congr 1
  funext x
  have he : inner ℝ x ξ + inner ℝ y ζ + s * inner ℝ x y = inner ℝ y ζ + inner ℝ x (ξ + s • y) := by
    rw [inner_add_right, real_inner_smul_right]; ring
  rw [he, AddChar.map_add_eq_mul, Circle.coe_mul]
  ring

theorem inner_integral_eq' (lam : ℝ) (Φ : Mom d → Mom d → ℂ) (a b ξ ζ x : Mom d) (s : ℝ) :
    ∫ y, Real.fourierChar (inner ℝ x ξ + inner ℝ y ζ + s * inner ℝ x y) •
        (chiScaled lam (x - a) * chiScaled lam (y - b) * Φ x y) =
      (Real.fourierChar (inner ℝ x ξ) : ℂ) * chiScaled lam (x - a) *
        ∫ y, Real.fourierChar (inner ℝ y (ζ + s • x)) • (chiScaled lam (y - b) * Φ x y) := by
  simp only [Circle.smul_def, smul_eq_mul]
  rw [← integral_const_mul]
  congr 1
  funext y
  have he : inner ℝ x ξ + inner ℝ y ζ + s * inner ℝ x y = inner ℝ x ξ + inner ℝ y (ζ + s • x) := by
    rw [inner_add_right, real_inner_smul_right, real_inner_comm x y]; ring
  rw [he, AddChar.map_add_eq_mul, Circle.coe_mul]
  ring

/-- Exchanging the order of integration. -/
theorem ntIntegral_eq_swap {N : ℕ} {D lam : ℝ} {Φ : Mom d → Mom d → ℂ} (hΦ : NTBounds N D Φ)
    (hN : 1 ≤ N) (hlam : 0 < lam) (a b ξ ζ : Mom d) (s : ℝ) :
    ntIntegral lam Φ a b ξ ζ s = ∫ x, ∫ y, Real.fourierChar
      (inner ℝ x ξ + inner ℝ y ζ + s * inner ℝ x y) •
        (chiScaled lam (x - a) * chiScaled lam (y - b) * Φ x y) := by
  rw [ntIntegral]
  symm
  refine integral_integral_swap ?_
  have hprod : Integrable (fun p : Mom d × Mom d =>
      (D : ℂ) * (chiScaled lam (p.1 - a) * chiScaled lam (p.2 - b))) (volume.prod volume) :=
    ((integrable_chiScaled hlam a).mul_prod (integrable_chiScaled hlam b)).const_mul _
  refine hprod.norm.mono' ?_ (Filter.Eventually.of_forall fun p => ?_)
  · have hc : Continuous fun p : Mom d × Mom d => Real.fourierChar
        (inner ℝ p.1 ξ + inner ℝ p.2 ζ + s * inner ℝ p.1 p.2) •
        (chiScaled lam (p.1 - a) * chiScaled lam (p.2 - b) * Φ p.1 p.2) := by
      have h1 := (contDiff_chiScaled (d := d) lam).continuous
      have h2 := hΦ.continuous hN
      refine Continuous.smul ?_ (((h1.comp (continuous_fst.sub continuous_const)).mul
        (h1.comp (continuous_snd.sub continuous_const))).mul h2)
      have hfst : Continuous fun p : Mom d × Mom d => p.1 := continuous_fst
      have hsnd : Continuous fun p : Mom d × Mom d => p.2 := continuous_snd
      exact continuous_subtype_val.comp (Real.continuous_fourierChar.comp
        (((hfst.inner continuous_const).add (hsnd.inner continuous_const)).add
          (continuous_const.mul (hfst.inner hsnd))))
    exact hc.aestronglyMeasurable
  · obtain ⟨x, y⟩ := p
    simp only [Function.uncurry_apply_pair, Circle.norm_smul, norm_mul, Complex.norm_real,
      Real.norm_of_nonneg hΦ.nonneg]
    set p : Mom d × Mom d := (x, y)
    have := hΦ.norm_le p.1 p.2
    have h1 := norm_nonneg (chiScaled lam (p.1 - a))
    have h2 := norm_nonneg (chiScaled lam (p.2 - b))
    calc ‖chiScaled lam (p.1 - a)‖ * ‖chiScaled lam (p.2 - b)‖ * ‖Φ p.1 p.2‖
        ≤ ‖chiScaled lam (p.1 - a)‖ * ‖chiScaled lam (p.2 - b)‖ * D := by gcongr
      _ = D * (‖chiScaled lam (p.1 - a)‖ * ‖chiScaled lam (p.2 - b)‖) := by ring

/-! ### The bounds -/

/-- The decay weight `(1 + r₊)^{-N}`. -/
@[expose] def decayW (N : ℕ) (r : ℝ) : ℝ := ((1 + max r 0) ^ N)⁻¹

theorem decayW_nonneg (N : ℕ) (r : ℝ) : 0 ≤ decayW N r := by
  unfold decayW; positivity

theorem decayW_anti (N : ℕ) {r r' : ℝ} (h : r ≤ r') : decayW N r' ≤ decayW N r := by
  unfold decayW
  gcongr

/-- The per-term majorant: `min(⟨s⟩^{-d}, ω(|P| - λ√d|s|), ω(|Q| - λ√d|s|))`. -/
@[expose] def termBound (d N : ℕ) (lam s : ℝ) (P Q : Mom d) : ℝ :=
  min (((1 + |s|) ^ d)⁻¹)
    (min (decayW N (‖P‖ - |s| * (lam * Real.sqrt d))) (decayW N (‖Q‖ - |s| * (lam * Real.sqrt d))))

theorem termBound_nonneg (d N : ℕ) (lam s : ℝ) (P Q : Mom d) : 0 ≤ termBound d N lam s P Q :=
  le_min (by positivity) (le_min (decayW_nonneg _ _) (decayW_nonneg _ _))

/-- `∫ ⟨w⟩^{-(d+1)} dw` over `ℝ^d`. -/
@[expose] def decayInt (d : ℕ) : ℝ := ∫ w : Mom d, (1 + ‖w‖) ^ (-((d : ℝ) + 1))

theorem integrable_decay (d : ℕ) : Integrable (fun w : Mom d => (1 + ‖w‖) ^ (-((d : ℝ) + 1))) :=
  integrable_one_add_norm (by rw [finrank_euclideanSpace_fin]; linarith)

theorem decayInt_nonneg (d : ℕ) : 0 ≤ decayInt d :=
  integral_nonneg fun _ => by positivity

/-- The constant of `norm_ntIntegral_le`. -/
@[expose] def termConst (d N : ℕ) : ℝ :=
  2 ^ d * ampConst d N * ((Real.sqrt d) ^ d * ballVol d + decayInt d)

theorem termConst_nonneg (d N : ℕ) : 0 ≤ termConst d N := by
  unfold termConst
  have := ampConst_nonneg d N
  have := ballVol_nonneg d
  have := decayInt_nonneg d
  positivity

theorem min_one_le_two_pow (d : ℕ) {s : ℝ} (hs : s ≠ 0) :
    min 1 ((|s| ^ d)⁻¹) ≤ 2 ^ d * ((1 + |s|) ^ d)⁻¹ := by
  have hs0 : 0 < |s| := abs_pos.2 hs
  rcases le_total |s| 1 with h | h
  · refine (min_le_left _ _).trans ?_
    rw [← div_eq_mul_inv, le_div_iff₀ (by positivity), one_mul]
    exact pow_le_pow_left₀ (by positivity) (by linarith) d
  · refine (min_le_right _ _).trans ?_
    have h1 : (1 + |s|) ^ d ≤ (2 * |s|) ^ d := pow_le_pow_left₀ (by positivity) (by linarith) d
    calc (|s| ^ d)⁻¹ = 2 ^ d * ((2 * |s|) ^ d)⁻¹ := by
          rw [mul_pow, mul_inv, ← mul_assoc, mul_inv_cancel₀ (by positivity), one_mul]
      _ ≤ 2 ^ d * ((1 + |s|) ^ d)⁻¹ := by gcongr

theorem inv_pow_le_rpow {N : ℕ} (hN : d + 1 ≤ N) (w : Mom d) :
    ((1 + ‖w‖) ^ N)⁻¹ ≤ (1 + ‖w‖) ^ (-((d : ℝ) + 1)) := by
  rw [Real.rpow_neg (by positivity), show ((d : ℝ) + 1) = ((d + 1 : ℕ) : ℝ) by push_cast; ring,
    Real.rpow_natCast]
  exact inv_anti₀ (by positivity) (pow_le_pow_right₀ (le_add_of_nonneg_right (norm_nonneg _)) hN)

/-- Pointwise bound of the inner `x`-integral. -/
theorem norm_inner_le {N : ℕ} {D lam : ℝ} {Φ : Mom d → Mom d → ℂ} (hΦ : NTBounds N D Φ)
    (hlam : 1 ≤ lam) (a w y : Mom d) :
    ‖∫ x, Real.fourierChar (inner ℝ x w) • (chiScaled lam (x - a) * Φ x y)‖ ≤
      ampConst d N * D * lam ^ d * ((1 + ‖w‖) ^ N)⁻¹ := by
  have h := norm_integral_amplitude_le hlam (hΦ.contDiff_left y)
    (fun k hk x => hΦ.bound_left k hk x y) a w
  rw [← div_eq_mul_inv, le_div_iff₀ (by positivity), mul_comm]
  exact h

theorem norm_inner_le' {N : ℕ} {D lam : ℝ} {Φ : Mom d → Mom d → ℂ} (hΦ : NTBounds N D Φ)
    (hlam : 1 ≤ lam) (b w x : Mom d) :
    ‖∫ y, Real.fourierChar (inner ℝ y w) • (chiScaled lam (y - b) * Φ x y)‖ ≤
      ampConst d N * D * lam ^ d * ((1 + ‖w‖) ^ N)⁻¹ := by
  have h := norm_integral_amplitude_le hlam (hΦ.contDiff_right x)
    (fun k hk y => hΦ.bound_right k hk x y) b w
  rw [← div_eq_mul_inv, le_div_iff₀ (by positivity), mul_comm]
  exact h

/-- Stationary phase: `|J| ≤ C D λ^{2d} ⟨s⟩^{-d}`. -/
theorem norm_ntIntegral_le_stat {N : ℕ} (hN : d + 1 ≤ N) {D lam : ℝ}
    {Φ : Mom d → Mom d → ℂ} (hΦ : NTBounds N D Φ) (hlam : 1 ≤ lam) (a b ξ ζ : Mom d)
    (s : ℝ) :
    ‖ntIntegral lam Φ a b ξ ζ s‖ ≤ termConst d N * D * lam ^ (2 * d) * ((1 + |s|) ^ d)⁻¹ := by
  have h0 : 0 < lam := lt_of_lt_of_le one_pos hlam
  have hD := hΦ.nonneg
  set A := ampConst d N * D * lam ^ d
  have hA : 0 ≤ A := by have := ampConst_nonneg d N; positivity
  have hlamd : 1 ≤ lam ^ d := one_le_pow₀ hlam
  -- pointwise bound on the outer integrand
  have hpt : ∀ y, ‖∫ x, Real.fourierChar (inner ℝ x ξ + inner ℝ y ζ + s * inner ℝ x y) •
      (chiScaled lam (x - a) * chiScaled lam (y - b) * Φ x y)‖ ≤
      ‖chiScaled lam (y - b)‖ * (A * (1 + ‖ξ + s • y‖) ^ (-((d : ℝ) + 1))) := fun y => by
    rw [inner_integral_eq, norm_mul, norm_mul, Circle.norm_coe, one_mul]
    gcongr
    refine (norm_inner_le hΦ hlam a _ y).trans ?_
    exact mul_le_mul_of_nonneg_left (inv_pow_le_rpow hN _) hA
  have hV : ∫ y, ‖chiScaled lam (y - b)‖ ≤ (Real.sqrt d) ^ d * ballVol d * lam ^ d :=
    integral_norm_chiScaled_le h0 b
  -- first bound: trivial
  have hb1 : ‖ntIntegral lam Φ a b ξ ζ s‖ ≤ A * ((Real.sqrt d) ^ d * ballVol d * lam ^ d) := by
    refine (norm_integral_le_integral_norm _).trans ?_
    calc _ ≤ ∫ y, ‖chiScaled lam (y - b)‖ * A :=
          integral_mono_of_nonneg (Filter.Eventually.of_forall fun _ => norm_nonneg _)
            ((integrable_chiScaled h0 b).norm.mul_const A) (Filter.Eventually.of_forall fun y =>
              (hpt y).trans (mul_le_mul_of_nonneg_left (mul_le_of_le_one_right hA
                (Real.rpow_le_one_of_one_le_of_nonpos (by linarith [norm_nonneg (ξ + s • y)])
                  (by linarith))) (norm_nonneg _)))
      _ = A * ∫ y, ‖chiScaled lam (y - b)‖ := by rw [integral_mul_const, mul_comm]
      _ ≤ _ := mul_le_mul_of_nonneg_left hV hA
  have hVI : ampConst d N * ((Real.sqrt d) ^ d * ballVol d) ≤
      2 ^ d * ampConst d N * ((Real.sqrt d) ^ d * ballVol d + decayInt d) := by
    have ha := ampConst_nonneg d N
    have hI := decayInt_nonneg d
    have h3 : ampConst d N * ((Real.sqrt d) ^ d * ballVol d) ≤
        ampConst d N * ((Real.sqrt d) ^ d * ballVol d + decayInt d) :=
      mul_le_mul_of_nonneg_left (by linarith) ha
    have h4 : ampConst d N * ((Real.sqrt d) ^ d * ballVol d + decayInt d) ≤
        2 ^ d * (ampConst d N * ((Real.sqrt d) ^ d * ballVol d + decayInt d)) :=
      le_mul_of_one_le_left (by have := ballVol_nonneg d; positivity) (one_le_pow₀ (by norm_num))
    linarith [mul_assoc (2 ^ d : ℝ) (ampConst d N) ((Real.sqrt d) ^ d * ballVol d + decayInt d)]
  rcases eq_or_ne s 0 with hs | hs
  · subst hs
    refine hb1.trans ?_
    simp only [abs_zero, add_zero, one_pow, inv_one, mul_one]
    rw [termConst, two_mul, pow_add]
    calc A * ((Real.sqrt d) ^ d * ballVol d * lam ^ d)
        = ampConst d N * ((Real.sqrt d) ^ d * ballVol d) * D * (lam ^ d * lam ^ d) := by
          simp only [A]; ring
      _ ≤ 2 ^ d * ampConst d N * ((Real.sqrt d) ^ d * ballVol d + decayInt d) * D *
          (lam ^ d * lam ^ d) := by gcongr
  -- second bound: change of variables
  have hb2 : ‖ntIntegral lam Φ a b ξ ζ s‖ ≤ A * ((|s| ^ d)⁻¹ * decayInt d) := by
    refine (norm_integral_le_integral_norm _).trans ?_
    have hint : Integrable (fun y : Mom d => A * (1 + ‖ξ + s • y‖) ^ (-((d : ℝ) + 1))) := by
      have h1 := (integrable_decay d).comp_add_left ξ
      exact (h1.comp_smul hs).const_mul A
    calc _ ≤ ∫ y, A * (1 + ‖ξ + s • y‖) ^ (-((d : ℝ) + 1)) :=
          integral_mono_of_nonneg (Filter.Eventually.of_forall fun _ => norm_nonneg _) hint
            (Filter.Eventually.of_forall fun y => (hpt y).trans (by
              have := norm_chiScaled_le_one lam (y - b)
              have : 0 ≤ A * (1 + ‖ξ + s • y‖) ^ (-((d : ℝ) + 1)) := by positivity
              nlinarith))
      _ = A * ((|s| ^ d)⁻¹ * decayInt d) := by
          rw [integral_const_mul]
          congr 1
          have h1 := MeasureTheory.Measure.integral_comp_smul (μ := (volume : Measure (Mom d)))
            (fun z : Mom d => (1 + ‖ξ + z‖) ^ (-((d : ℝ) + 1))) s
          simp only [finrank_euclideanSpace_fin] at h1
          rw [h1, integral_add_left_eq_self (fun z : Mom d => (1 + ‖z‖) ^ (-((d : ℝ) + 1))) ξ,
            smul_eq_mul, abs_inv, abs_pow, decayInt]
  have hmin : ‖ntIntegral lam Φ a b ξ ζ s‖ ≤
      A * lam ^ d * ((Real.sqrt d) ^ d * ballVol d + decayInt d) * min 1 ((|s| ^ d)⁻¹) := by
    have := ballVol_nonneg d
    have := decayInt_nonneg d
    have hV0 : 0 ≤ (Real.sqrt d) ^ d * ballVol d := by positivity
    rcases le_total 1 ((|s| ^ d)⁻¹) with h | h
    · rw [min_eq_left h, mul_one]
      refine hb1.trans ?_
      calc A * ((Real.sqrt d) ^ d * ballVol d * lam ^ d)
          = A * lam ^ d * ((Real.sqrt d) ^ d * ballVol d) := by ring
        _ ≤ _ := by gcongr; linarith
    · rw [min_eq_right h]
      refine hb2.trans ?_
      calc A * ((|s| ^ d)⁻¹ * decayInt d) = A * 1 * decayInt d * (|s| ^ d)⁻¹ := by ring
        _ ≤ A * lam ^ d * ((Real.sqrt d) ^ d * ballVol d + decayInt d) * (|s| ^ d)⁻¹ := by
          gcongr
          · linarith
  refine hmin.trans ?_
  have hm := min_one_le_two_pow d hs
  have hB : 0 ≤ A * lam ^ d * ((Real.sqrt d) ^ d * ballVol d + decayInt d) := by
    have := ballVol_nonneg d; have := decayInt_nonneg d; positivity
  calc A * lam ^ d * ((Real.sqrt d) ^ d * ballVol d + decayInt d) * min 1 ((|s| ^ d)⁻¹)
      ≤ A * lam ^ d * ((Real.sqrt d) ^ d * ballVol d + decayInt d) *
          (2 ^ d * ((1 + |s|) ^ d)⁻¹) := mul_le_mul_of_nonneg_left hm hB
    _ = termConst d N * D * lam ^ (2 * d) * ((1 + |s|) ^ d)⁻¹ := by
        rw [termConst, two_mul, pow_add]
        ring

theorem ampConst_mul_le_termConst (d N : ℕ) :
    ampConst d N * ((Real.sqrt d) ^ d * ballVol d) ≤ termConst d N := by
  have ha := ampConst_nonneg d N
  have hI := decayInt_nonneg d
  have hV : 0 ≤ (Real.sqrt d) ^ d * ballVol d := by have := ballVol_nonneg d; positivity
  have h3 : ampConst d N * ((Real.sqrt d) ^ d * ballVol d) ≤
      ampConst d N * ((Real.sqrt d) ^ d * ballVol d + decayInt d) :=
    mul_le_mul_of_nonneg_left (by linarith) ha
  have h4 : ampConst d N * ((Real.sqrt d) ^ d * ballVol d + decayInt d) ≤
      2 ^ d * (ampConst d N * ((Real.sqrt d) ^ d * ballVol d + decayInt d)) :=
    le_mul_of_one_le_left (by positivity) (one_le_pow₀ (by norm_num))
  rw [termConst]
  linarith [mul_assoc (2 ^ d : ℝ) (ampConst d N) ((Real.sqrt d) ^ d * ballVol d + decayInt d)]

/-- The generic non-stationary estimate for an outer integral over the support of `χ₀((y-b)/λ)`. -/
theorem norm_integral_le_decayW {N : ℕ} {lam A : ℝ} (hlam : 1 ≤ lam) (hA : 0 ≤ A)
    {G : Mom d → ℂ} (b P : Mom d) (s : ℝ)
    (hG : ∀ y, ‖G y‖ ≤ ‖chiScaled lam (y - b)‖ * (A * ((1 + ‖P + s • (y - b)‖) ^ N)⁻¹)) :
    ‖∫ y, G y‖ ≤ A * ((Real.sqrt d) ^ d * ballVol d * lam ^ d) *
      decayW N (‖P‖ - |s| * (lam * Real.sqrt d)) := by
  have h0 : 0 < lam := lt_of_lt_of_le one_pos hlam
  set w := decayW N (‖P‖ - |s| * (lam * Real.sqrt d))
  have hw0 : 0 ≤ w := decayW_nonneg _ _
  have hpt : ∀ y, ‖G y‖ ≤ ‖chiScaled lam (y - b)‖ * (A * w) := fun y => by
    refine (hG y).trans ?_
    by_cases hy : chiScaled lam (y - b) = 0
    · rw [hy, norm_zero, zero_mul, zero_mul]
    · gcongr
      have hyb := norm_le_of_chiScaled_ne_zero h0 hy
      have hlow : ‖P‖ - |s| * (lam * Real.sqrt d) ≤ ‖P + s • (y - b)‖ := by
        have h1 := norm_sub_norm_le P (-(s • (y - b)))
        rw [sub_neg_eq_add, norm_neg, norm_smul, Real.norm_eq_abs] at h1
        have h2 : |s| * ‖y - b‖ ≤ |s| * (lam * Real.sqrt d) :=
          mul_le_mul_of_nonneg_left hyb (abs_nonneg s)
        linarith
      unfold w decayW
      gcongr
      exact max_le hlow (norm_nonneg _)
  refine (norm_integral_le_integral_norm _).trans ?_
  calc ∫ y, ‖G y‖ ≤ ∫ y, ‖chiScaled lam (y - b)‖ * (A * w) :=
        integral_mono_of_nonneg (Filter.Eventually.of_forall fun _ => norm_nonneg _)
          ((integrable_chiScaled h0 b).norm.mul_const _) (Filter.Eventually.of_forall hpt)
    _ = (A * w) * ∫ y, ‖chiScaled lam (y - b)‖ := by rw [integral_mul_const, mul_comm]
    _ ≤ (A * w) * ((Real.sqrt d) ^ d * ballVol d * lam ^ d) :=
        mul_le_mul_of_nonneg_left (integral_norm_chiScaled_le h0 b) (mul_nonneg hA hw0)
    _ = _ := by ring

/-- Non-stationary phase in `x`. -/
theorem norm_ntIntegral_le_left {N : ℕ} {D lam : ℝ} {Φ : Mom d → Mom d → ℂ}
    (hΦ : NTBounds N D Φ) (hlam : 1 ≤ lam) (a b ξ ζ : Mom d) (s : ℝ) :
    ‖ntIntegral lam Φ a b ξ ζ s‖ ≤
      termConst d N * D * lam ^ (2 * d) * decayW N (‖ξ + s • b‖ - |s| * (lam * Real.sqrt d)) := by
  have hD := hΦ.nonneg
  set A := ampConst d N * D * lam ^ d
  have hA : 0 ≤ A := by have := ampConst_nonneg d N; positivity
  have h := norm_integral_le_decayW (N := N) hlam hA (G := fun y => ∫ x,
    Real.fourierChar (inner ℝ x ξ + inner ℝ y ζ + s * inner ℝ x y) •
      (chiScaled lam (x - a) * chiScaled lam (y - b) * Φ x y)) b (ξ + s • b) s (fun y => by
    rw [inner_integral_eq, norm_mul, norm_mul, Circle.norm_coe, one_mul]
    gcongr
    have he : ξ + s • b + s • (y - b) = ξ + s • y := by rw [smul_sub]; abel
    rw [he]
    exact norm_inner_le hΦ hlam a _ y)
  refine h.trans ?_
  have hc := ampConst_mul_le_termConst d N
  have hw := decayW_nonneg N (‖ξ + s • b‖ - |s| * (lam * Real.sqrt d))
  calc A * ((Real.sqrt d) ^ d * ballVol d * lam ^ d) *
        decayW N (‖ξ + s • b‖ - |s| * (lam * Real.sqrt d))
      = (ampConst d N * ((Real.sqrt d) ^ d * ballVol d)) * D * lam ^ (2 * d) *
          decayW N (‖ξ + s • b‖ - |s| * (lam * Real.sqrt d)) := by
        simp only [A]; rw [two_mul, pow_add]; ring
    _ ≤ _ := by gcongr

/-- Non-stationary phase in `y`. -/
theorem norm_ntIntegral_le_right {N : ℕ} (hN : 1 ≤ N) {D lam : ℝ} {Φ : Mom d → Mom d → ℂ}
    (hΦ : NTBounds N D Φ) (hlam : 1 ≤ lam) (a b ξ ζ : Mom d) (s : ℝ) :
    ‖ntIntegral lam Φ a b ξ ζ s‖ ≤
      termConst d N * D * lam ^ (2 * d) * decayW N (‖ζ + s • a‖ - |s| * (lam * Real.sqrt d)) := by
  have h0 : 0 < lam := lt_of_lt_of_le one_pos hlam
  have hD := hΦ.nonneg
  set A := ampConst d N * D * lam ^ d
  have hA : 0 ≤ A := by have := ampConst_nonneg d N; positivity
  rw [ntIntegral_eq_swap hΦ hN h0]
  have h := norm_integral_le_decayW (N := N) hlam hA (G := fun x => ∫ y,
    Real.fourierChar (inner ℝ x ξ + inner ℝ y ζ + s * inner ℝ x y) •
      (chiScaled lam (x - a) * chiScaled lam (y - b) * Φ x y)) a (ζ + s • a) s (fun x => by
    rw [inner_integral_eq', norm_mul, norm_mul, Circle.norm_coe, one_mul]
    gcongr
    have he : ζ + s • a + s • (x - a) = ζ + s • x := by rw [smul_sub]; abel
    rw [he]
    exact norm_inner_le' hΦ hlam b _ x)
  refine h.trans ?_
  have hc := ampConst_mul_le_termConst d N
  have hw := decayW_nonneg N (‖ζ + s • a‖ - |s| * (lam * Real.sqrt d))
  calc A * ((Real.sqrt d) ^ d * ballVol d * lam ^ d) *
        decayW N (‖ζ + s • a‖ - |s| * (lam * Real.sqrt d))
      = (ampConst d N * ((Real.sqrt d) ^ d * ballVol d)) * D * lam ^ (2 * d) *
          decayW N (‖ζ + s • a‖ - |s| * (lam * Real.sqrt d)) := by
        simp only [A]; rw [two_mul, pow_add]; ring
    _ ≤ _ := by gcongr

/-- **The per-term bound** (stationary and non-stationary phase): for `N ≥ d + 1` and `λ ≥ 1`,
`|J| ≤ C D λ^{2d} min(⟨s⟩^{-d}, ω(|ξ + s b| - λ√d|s|), ω(|ζ + s a| - λ√d|s|))`. -/
theorem norm_ntIntegral_le {N : ℕ} (hN : d + 1 ≤ N) {D lam : ℝ} {Φ : Mom d → Mom d → ℂ}
    (hΦ : NTBounds N D Φ) (hlam : 1 ≤ lam) (a b ξ ζ : Mom d) (s : ℝ) :
    ‖ntIntegral lam Φ a b ξ ζ s‖ ≤
      termConst d N * D * lam ^ (2 * d) * termBound d N lam s (ξ + s • b) (ζ + s • a) := by
  have hK : 0 ≤ termConst d N * D * lam ^ (2 * d) := by
    have := termConst_nonneg d N; have := hΦ.nonneg
    have : 0 ≤ lam := by linarith
    positivity
  rw [termBound, mul_min_of_nonneg _ _ hK, mul_min_of_nonneg _ _ hK]
  exact le_min (norm_ntIntegral_le_stat hN hΦ hlam a b ξ ζ s)
    (le_min (norm_ntIntegral_le_left hΦ hlam a b ξ ζ s)
      (norm_ntIntegral_le_right (by omega) hΦ hlam a b ξ ζ s))

end WaveTurbulence.NTSP
