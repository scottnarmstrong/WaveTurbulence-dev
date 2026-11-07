/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.VineEst.VineEstS3.FSKernel
public import WaveTurbulence.Foundations.VineEst.VineEstS3.FSLattice

/-! # The weighted coefficient-kernel sums are uniformly bounded (B2, step 3)

`∑_m ⟨m/2⟩^θ |a_m(λ)| ≤ C ⟨λ⟩^θ` for `θ ≥ 0`, uniformly in `λ ∈ ℝ^r` (Peetre's inequality and the uniform
lattice sums of `FSLattice`), where `⟨ξ⟩ = timeBracket ξ = max(1, max_i (1+ξ_i²)^{1/2})`.
-/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.VineEstS3.FS
open WaveTurbulence WaveTurbulence.Fourier MeasureTheory Set
open scoped SchwartzMap

variable {r : ℕ}

theorem timeBracket_le_one_add_norm (ξ : Fin r → ℝ) : timeBracket ξ ≤ 1 + ‖ξ‖ := by
  unfold timeBracket
  rw [Finset.sup'_le_iff]
  intro i _
  rcases i with _ | j
  · simp
  · have h1 : |ξ j| ≤ ‖ξ‖ := by simpa using norm_le_pi_norm ξ j
    have : Real.sqrt (1 + ξ j ^ 2) ≤ 1 + |ξ j| := by
      rw [Real.sqrt_le_left (by positivity)]
      nlinarith [abs_nonneg (ξ j), sq_abs (ξ j)]
    show Real.sqrt (1 + ξ j ^ 2) ≤ 1 + ‖ξ‖
    linarith

theorem one_le_timeBracket' (ξ : Fin r → ℝ) : 1 ≤ timeBracket ξ := by
  unfold timeBracket
  exact Finset.le_sup' (fun i : Option (Fin r) => match i with
    | none => (1 : ℝ) | some j => Real.sqrt (1 + ξ j ^ 2)) (Finset.mem_univ none)

theorem one_add_norm_le_timeBracket (ξ : Fin r → ℝ) : 1 + ‖ξ‖ ≤ Real.sqrt 2 * timeBracket ξ := by
  have h1 := one_le_timeBracket' ξ
  have hs : (1 : ℝ) ≤ Real.sqrt 2 := by
    rw [Real.one_le_sqrt]; norm_num
  have hcoord : ∀ j, 1 + |ξ j| ≤ Real.sqrt 2 * timeBracket ξ := by
    intro j
    have hj : Real.sqrt (1 + ξ j ^ 2) ≤ timeBracket ξ := by
      unfold timeBracket
      exact Finset.le_sup' (fun i : Option (Fin r) => match i with
        | none => (1 : ℝ) | some j => Real.sqrt (1 + ξ j ^ 2)) (Finset.mem_univ (some j))
    have h2 : 1 + |ξ j| ≤ Real.sqrt 2 * Real.sqrt (1 + ξ j ^ 2) := by
      rw [← Real.sqrt_mul (by norm_num)]
      apply Real.le_sqrt_of_sq_le
      nlinarith [abs_nonneg (ξ j), sq_abs (ξ j), sq_nonneg (1 - |ξ j|)]
    exact h2.trans (mul_le_mul_of_nonneg_left hj (Real.sqrt_nonneg 2))
  have hn : ‖ξ‖ ≤ Real.sqrt 2 * timeBracket ξ - 1 := by
    apply (pi_norm_le_iff_of_nonneg (by nlinarith)).mpr
    intro j
    have := hcoord j
    simpa using (by linarith : |ξ j| ≤ Real.sqrt 2 * timeBracket ξ - 1)
  linarith

/-- Peetre: `⟨a⟩ ≤ √2 ⟨b⟩ (1 + ‖a - b‖)`. -/
theorem timeBracket_peetre (a b : Fin r → ℝ) :
    timeBracket a ≤ Real.sqrt 2 * timeBracket b * (1 + ‖a - b‖) := by
  have h1 := timeBracket_le_one_add_norm a
  have h2 := one_add_norm_le_timeBracket b
  have h3 : ‖a‖ ≤ ‖b‖ + ‖a - b‖ := by
    have := norm_le_norm_add_norm_sub' a b
    linarith
  have h4 : (1 + ‖a‖) ≤ (1 + ‖b‖) * (1 + ‖a - b‖) := by
    nlinarith [norm_nonneg b, norm_nonneg (a - b)]
  calc timeBracket a ≤ 1 + ‖a‖ := h1
    _ ≤ (1 + ‖b‖) * (1 + ‖a - b‖) := h4
    _ ≤ (Real.sqrt 2 * timeBracket b) * (1 + ‖a - b‖) :=
        mul_le_mul_of_nonneg_right h2 (by positivity)
    _ = _ := by ring


/-- The half-integer frequency `m/2`. -/
noncomputable def half (m : Fin r → ℤ) : Fin r → ℝ := fun i => (m i : ℝ) / 2

/-- The cutoff as a Schwartz function, dilated so that its Fourier transform is sampled at the lattice. -/
noncomputable def kernSchwartz (q : Fin r → ℝ) : 𝓢((Fin r → ℝ), ℂ) :=
  schwartzCoordinateDilate (L := 2) two_ne_zero
    (coordinateFourierSchwartz ((cutQ_hasCompactSupport q).toSchwartzMap (cutQ_contDiff q)))

theorem kernSchwartz_apply (q : Fin r → ℝ) (u : Fin r → ℝ) :
    kernSchwartz q u = timeFourier (cutQ q) ((2 : ℝ)⁻¹ • u) := by
  unfold kernSchwartz
  rw [schwartzCoordinateDilate_apply, coordinateFourierSchwartz_apply]
  rfl

theorem norm_kern_eq (q : Fin r → ℝ) (m : Fin r → ℤ) (lam : Fin r → ℝ) :
    ‖kern q m lam‖ = (1 / 2 : ℝ) ^ r * ‖kernSchwartz q (zvec m - (2 : ℝ) • lam)‖ := by
  rw [kernSchwartz_apply]
  have : (2 : ℝ)⁻¹ • (zvec m - (2 : ℝ) • lam) = fun i => (m i : ℝ) / 2 - lam i := by
    funext i; simp only [zvec, Pi.smul_apply, Pi.sub_apply, smul_eq_mul]; ring
  rw [this]
  unfold kern
  rw [norm_mul, norm_inv, norm_pow]
  simp

/-- **Uniform weighted bound for the coefficient kernel.** -/
theorem sum_kern_weight_le (q : Fin r → ℝ) {θ : ℝ} (hθ : 0 ≤ θ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ lam : Fin r → ℝ,
      Summable (fun m : Fin r → ℤ => timeBracket (half m) ^ θ * ‖kern q m lam‖) ∧
      ∑' m : Fin r → ℤ, timeBracket (half m) ^ θ * ‖kern q m lam‖ ≤ C * timeBracket lam ^ θ := by
  obtain ⟨CH, hCH0, hCH⟩ := schwartz_shifted_sum_bound (kernSchwartz q) hθ
  have hper : ∀ (lam : Fin r → ℝ) (m : Fin r → ℤ),
      timeBracket (half m) ^ θ * ‖kern q m lam‖ ≤
        ((1 / 2 : ℝ) ^ r * Real.sqrt 2 ^ θ * timeBracket lam ^ θ) *
          ((1 + ‖zvec m - (2 : ℝ) • lam‖) ^ θ * ‖kernSchwartz q (zvec m - (2 : ℝ) • lam)‖) := by
    intro lam m
    rw [norm_kern_eq]
    have hP := timeBracket_peetre (half m) lam
    have hd : ‖half m - lam‖ ≤ ‖zvec m - (2 : ℝ) • lam‖ := by
      have : half m - lam = (2 : ℝ)⁻¹ • (zvec m - (2 : ℝ) • lam) := by
        funext i; simp only [half, zvec, Pi.smul_apply, Pi.sub_apply, smul_eq_mul]; ring
      rw [this, norm_smul]
      have h2 : ‖(2 : ℝ)⁻¹‖ ≤ 1 := by norm_num
      calc _ ≤ 1 * ‖zvec m - (2 : ℝ) • lam‖ :=
            mul_le_mul_of_nonneg_right h2 (norm_nonneg _)
        _ = _ := one_mul _
    have hb0 : 0 ≤ timeBracket lam := by linarith [one_le_timeBracket' lam]
    have hn0 : 0 ≤ ‖zvec m - (2 : ℝ) • lam‖ := norm_nonneg _
    have h1 : timeBracket (half m) ≤ Real.sqrt 2 * timeBracket lam * (1 + ‖zvec m - (2 : ℝ) • lam‖) :=
      hP.trans (mul_le_mul_of_nonneg_left (by linarith)
        (mul_nonneg (Real.sqrt_nonneg 2) hb0))
    have h2 : timeBracket (half m) ^ θ ≤ (Real.sqrt 2 * timeBracket lam *
        (1 + ‖zvec m - (2 : ℝ) • lam‖)) ^ θ :=
      Real.rpow_le_rpow (by linarith [one_le_timeBracket' (half m)]) h1 hθ
    rw [Real.mul_rpow (mul_nonneg (Real.sqrt_nonneg 2) hb0) (by linarith),
      Real.mul_rpow (Real.sqrt_nonneg 2) hb0] at h2
    calc _ ≤ ((Real.sqrt 2 ^ θ * timeBracket lam ^ θ) * (1 + ‖zvec m - (2 : ℝ) • lam‖) ^ θ) *
          ((1 / 2 : ℝ) ^ r * ‖kernSchwartz q (zvec m - (2 : ℝ) • lam)‖) :=
          mul_le_mul_of_nonneg_right h2 (mul_nonneg (by positivity) (norm_nonneg _))
      _ = _ := by ring
  refine ⟨(1 / 2 : ℝ) ^ r * Real.sqrt 2 ^ θ * CH, by positivity, fun lam => ?_⟩
  obtain ⟨hs, hsum⟩ := hCH ((2 : ℝ) • lam)
  have hnn : ∀ m : Fin r → ℤ, 0 ≤ timeBracket (half m) ^ θ * ‖kern q m lam‖ := fun m =>
    mul_nonneg (Real.rpow_nonneg (by linarith [one_le_timeBracket' (half m)]) _) (norm_nonneg _)
  have hs' : Summable (fun m : Fin r → ℤ => ((1 / 2 : ℝ) ^ r * Real.sqrt 2 ^ θ * timeBracket lam ^ θ) *
      ((1 + ‖zvec m - (2 : ℝ) • lam‖) ^ θ * ‖kernSchwartz q (zvec m - (2 : ℝ) • lam)‖)) :=
    hs.mul_left _
  refine ⟨Summable.of_nonneg_of_le hnn (hper lam) hs', ?_⟩
  refine ((Summable.of_nonneg_of_le hnn (hper lam) hs').tsum_le_tsum (hper lam) hs').trans ?_
  rw [tsum_mul_left]
  calc _ ≤ ((1 / 2 : ℝ) ^ r * Real.sqrt 2 ^ θ * timeBracket lam ^ θ) * CH :=
        mul_le_mul_of_nonneg_left hsum (mul_nonneg (mul_nonneg (by positivity)
          (Real.rpow_nonneg (Real.sqrt_nonneg 2) _))
          (Real.rpow_nonneg (by linarith [one_le_timeBracket' lam]) _))
    _ = _ := by ring


theorem cutQ_eq_translate (q : Fin r → ℝ) : cutQ q = fun u => cutQ 0 (u + (-q)) := by
  funext u
  simp [cutQ, sub_eq_add_neg]

theorem norm_kern_translate (q : Fin r → ℝ) (m : Fin r → ℤ) (lam : Fin r → ℝ) :
    ‖kern q m lam‖ = ‖kern 0 m lam‖ := by
  have h : timeFourier (cutQ q) = fun ξ => Real.fourierChar (timePairing r (-q) ξ) • timeFourier (cutQ 0) ξ := by
    rw [cutQ_eq_translate q]
    exact timeFourier_translate (cutQ 0) (-q)
  unfold kern
  rw [h]
  simp only [norm_mul, Circle.smul_def, smul_eq_mul, Circle.norm_coe, one_mul]

/-- **Uniform weighted bound for the coefficient kernel, uniform in the cell.** -/
theorem sum_kern_weight_le_uniform {θ : ℝ} (hθ : 0 ≤ θ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (q lam : Fin r → ℝ),
      Summable (fun m : Fin r → ℤ => timeBracket (half m) ^ θ * ‖kern q m lam‖) ∧
      ∑' m : Fin r → ℤ, timeBracket (half m) ^ θ * ‖kern q m lam‖ ≤ C * timeBracket lam ^ θ := by
  obtain ⟨C, hC, h⟩ := sum_kern_weight_le (0 : Fin r → ℝ) hθ
  refine ⟨C, hC, fun q lam => ?_⟩
  simp only [norm_kern_translate q]
  exact h lam

end WaveTurbulence.VineEstS3.FS
