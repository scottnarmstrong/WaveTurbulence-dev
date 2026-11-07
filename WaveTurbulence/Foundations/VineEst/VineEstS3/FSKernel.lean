/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Fourier.PoissonMultidimensional
public import WaveTurbulence.Foundations.Fourier.CoordinateCutoff
public import WaveTurbulence.Foundations.Layered.RestrictionCalculus
public import WaveTurbulence.Foundations.Layered.InverseFourier

/-! # Fourier series on a unit time cell: the coefficient kernel (B2, step 1)

For a unit cell `Q_q = ∏ [q_i, q_i+1]` and the cutoff `χ_q(u) = ∏ χ₀(u_i - q_i)` (`χ₀ = 1` on `[0,1]`,
supported in `(-1/2, 3/2)`), the kernel
`a_m(λ) = 2^{-r} \hat χ_q(m/2 - λ)` (`m ∈ ℤ^r`) represents the phases `e^{2πi λ·t}`, `t ∈ Q_q`, as
period-2 Fourier series `e^{2πi λ·t} = ∑_m a_m(λ) e^{πi m·t}` (Poisson summation with period 2: the translates
of the support of `χ_q` by `2ℤ^r` miss the cell `Q_q`).  These are the modes `e^{πi λ t}` of TARGET's (tildeK2).
-/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.VineEstS3.FS
open WaveTurbulence WaveTurbulence.Fourier WaveTurbulence.Layered MeasureTheory Set
open scoped ContDiff

variable {r : ℕ}

/-- The cutoff centred at the cell `q`. -/
noncomputable def cutQ (q : Fin r → ℝ) (u : Fin r → ℝ) : ℂ := coordinateCutoff chiUnit (u - q)

/-- The unit cell `∏ [q_i, q_i + 1]`. -/
def cell (q : Fin r → ℝ) : Set (Fin r → ℝ) := {t | ∀ i, t i ∈ Icc (q i) (q i + 1)}

/-- The Fourier coefficient kernel `a_m(λ) = 2^{-r} (cutQ q)^(m/2 - λ)`. -/
noncomputable def kern (q : Fin r → ℝ) (m : Fin r → ℤ) (lam : Fin r → ℝ) : ℂ :=
  ((2 : ℂ) ^ r)⁻¹ * timeFourier (cutQ q) (fun i => (m i : ℝ) / 2 - lam i)

/-- The mode `e^{πi m·t} = e^{2πi (m/2)·t}`. -/
noncomputable def fsPhase (m : Fin r → ℤ) (t : Fin r → ℝ) : ℂ :=
  (Real.fourierChar (timePairing r t (fun i => (m i : ℝ) / 2)) : ℂ)

theorem cutQ_contDiff (q : Fin r → ℝ) : ContDiff ℝ ∞ (cutQ q) :=
  (coordinateCutoff_contDiff chiUnit_contDiff).comp (contDiff_id.sub contDiff_const)

theorem chiUnit_eq_zero {x : ℝ} (hx : x ≤ -1 / 2 ∨ 3 / 2 ≤ x) : chiUnit x = 0 := by
  apply unitBump.zero_of_le_dist
  rw [Real.dist_eq]
  change (1 : ℝ) ≤ |x - 1 / 2|
  rcases hx with hx | hx
  · rw [abs_of_nonpos (by linarith)]; linarith
  · rw [abs_of_nonneg (by linarith)]; linarith

theorem cutQ_hasCompactSupport (q : Fin r → ℝ) : HasCompactSupport (cutQ q) :=
  (coordinateCutoff_hasCompactSupport chiUnit_hasCompactSupport).comp_homeomorph
    (Homeomorph.subRight q)

theorem cutQ_eq_one {q t : Fin r → ℝ} (ht : t ∈ cell q) : cutQ q t = 1 :=
  coordinateCutoff_chiUnit_eq_one (fun i => by
    have := ht i; simp only [Pi.sub_apply, mem_Icc] at this ⊢; constructor <;> linarith [this.1, this.2])

/-- Translates of the cutoff by `2n`, `n ≠ 0`, vanish on the cell. -/
theorem cutQ_translate_eq_zero {q t : Fin r → ℝ} (ht : t ∈ cell q) {n : Fin r → ℤ} (hn : n ≠ 0) :
    cutQ q (t + fun i => 2 * (n i : ℝ)) = 0 := by
  obtain ⟨i, hi⟩ : ∃ i, n i ≠ 0 := by
    by_contra h; exact hn (funext fun i => by_contra fun hi => h ⟨i, hi⟩)
  unfold cutQ coordinateCutoff
  refine Finset.prod_eq_zero (Finset.mem_univ i) ?_
  have h1 := ht i
  simp only [mem_Icc] at h1
  have : chiUnit (t i + 2 * (n i : ℝ) - q i) = 0 := by
    apply chiUnit_eq_zero
    rcases lt_or_gt_of_ne hi with h | h
    · left
      have : (n i : ℝ) ≤ -1 := by exact_mod_cast Int.le_sub_one_of_lt h
      linarith [h1.1, h1.2]
    · right
      have : (1 : ℝ) ≤ n i := by exact_mod_cast h
      linarith [h1.1, h1.2]
  simp [this]


theorem fourierChar_pairing_eq (t lam : Fin r → ℝ) :
    (Real.fourierChar (timePairing r t lam) : ℂ) =
      Complex.exp (((2 * Real.pi * ∑ i, lam i * t i : ℝ) : ℂ) * Complex.I) := by
  rw [Real.fourierChar_apply]
  have : timePairing r t lam = ∑ i, lam i * t i := by
    change t ⬝ᵥ lam = _
    exact Finset.sum_congr rfl fun i _ => mul_comm _ _
  rw [this]

/-- **Period-2 Fourier series of the phases on the cell** (Poisson summation). -/
theorem tsum_kern_phase {q t : Fin r → ℝ} (ht : t ∈ cell q) (lam : Fin r → ℝ) :
    ∑' m : Fin r → ℤ, kern q m lam * fsPhase m t = (Real.fourierChar (timePairing r t lam) : ℂ) := by
  set g : (Fin r → ℝ) → ℂ := fun u => (Real.fourierChar (timePairing r u lam) : ℂ) * cutQ q u with hg
  set f : (Fin r → ℝ) → ℂ := fun u => g (u + t) with hf
  have hgs : ContDiff ℝ ∞ g := by
    have h1 : ContDiff ℝ ∞ (fun u : Fin r → ℝ => (Real.fourierChar (timePairing r u lam) : ℂ)) := by
      have : (fun u : Fin r → ℝ => (Real.fourierChar (timePairing r u lam) : ℂ)) =
          fun u => Complex.exp (((2 * Real.pi * ∑ i, lam i * u i : ℝ) : ℂ) * Complex.I) :=
        funext fun u => fourierChar_pairing_eq u lam
      rw [this]
      apply ContDiff.cexp
      apply ContDiff.mul _ contDiff_const
      exact Complex.ofRealCLM.contDiff.comp (contDiff_const.mul (by fun_prop))
    exact h1.mul (cutQ_contDiff q)
  have hfs : ContDiff ℝ ∞ f := hgs.comp (contDiff_id.add contDiff_const)
  have hgc : HasCompactSupport g := (cutQ_hasCompactSupport q).mul_left
  have hfc : HasCompactSupport f := hgc.comp_homeomorph (Homeomorph.addRight t)
  have hP := poisson_scaled_smooth_compact hfs hfc (L := 1 / 2) (by norm_num)
  have hgmod : g = fun u => Real.fourierChar (timePairing r u lam) • cutQ q u := by
    funext u; simp [hg, Circle.smul_def]
  have hFT : ∀ ξ : Fin r → ℝ, timeFourier f ξ =
      (Real.fourierChar (timePairing r t ξ) : ℂ) * timeFourier (cutQ q) (ξ - lam) := by
    intro ξ
    have h1 : timeFourier f = fun ξ => Real.fourierChar (timePairing r t ξ) • timeFourier g ξ :=
      timeFourier_translate g t
    have h2 : timeFourier g = fun ξ => timeFourier (cutQ q) (ξ - lam) := by
      rw [hgmod]; exact timeFourier_modulate (cutQ q) lam
    rw [h1]; simp [h2, Circle.smul_def]
  have hL : ∑' n : Fin r → ℤ, f (fun i => (n i : ℝ) / (1 / 2)) =
      (Real.fourierChar (timePairing r t lam) : ℂ) := by
    rw [tsum_eq_single 0]
    · simp only [hf, hg]
      have : ((fun i => ((0 : Fin r → ℤ) i : ℝ) / (1 / 2)) + t) = t := by
        funext i; simp
      rw [this, cutQ_eq_one ht, mul_one]
    · intro n hn
      simp only [hf, hg]
      have : ((fun i => (n i : ℝ) / (1 / 2)) + t) = t + fun i => 2 * (n i : ℝ) := by
        funext i; simp only [Pi.add_apply]; rw [add_comm]; congr 1; field_simp
      rw [this, cutQ_translate_eq_zero ht hn, mul_zero]
  rw [hL] at hP
  rw [hP]
  rw [← tsum_mul_left]
  refine tsum_congr fun m => ?_
  rw [hFT]
  have hx : (fun i => (1 / 2 : ℝ) * (m i : ℝ)) = fun i => (m i : ℝ) / 2 := by funext i; ring
  have hy : (fun i => (1 / 2 : ℝ) * (m i : ℝ)) - lam = fun i => (m i : ℝ) / 2 - lam i := by
    funext i; simp only [Pi.sub_apply]; ring
  rw [hy, hx]
  simp only [kern, fsPhase]
  have : (((1 : ℝ) / 2) ^ r : ℝ) = (((2 : ℝ) ^ r)⁻¹) := by rw [one_div, inv_pow]
  push_cast
  rw [one_div, inv_pow]
  ring

end WaveTurbulence.VineEstS3.FS
