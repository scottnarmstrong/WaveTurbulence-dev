/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Flower.MkSlotsT.Weight
public import WaveTurbulence.Foundations.Flower.FiltNT.Pole

/-! # B3s-HELPER5 (γ) T4: the atom filters as Schwartz profiles (`filt`)

A stem node with radii `r :: rs` (one or more layers) becomes ONE atom filter `(r₀, ψ)` of the piece
(`PieceRestB3s.filt`, read by the engine as `ψ(Ω / r₀)`), with `r₀` the given base radius and the profile
`ψ(u) = ∏_{r' ∈ r :: rs} χ₀(u · r₀ / r')` (`stemProfile`): smooth, compactly supported (hence Schwartz),
`[0,1]`-valued.

* `stemProfile_apply_div`: `ψ(Ω / r₀) = ∏ χ₀(|Ω| / r') = radProd (r :: rs) Ω` (for `r₀ ≠ 0`; χ₀ is even);
* `norm_stemProfile_le`: `‖ψ u‖ ≤ 1` (the `filt_ok` bound);
* `stemProfile_single`: ONE layer at the base radius is χ₀ itself (`FiltNT.chiS`), so its `𝔟`-norm is
  `filterB χ₀` (the brief's `cθ ≥ filterB χ₀`);
* `stemProfile_two_of_le_half`: TWO layers whose second radius is at least twice the base radius collapse to ONE
  layer (`χ₀(u)χ₀(λu) = χ₀(u)` for `λ ≤ 1/2`), so again `𝔟 = filterB χ₀`. The two-layer bound for ratios
  `λ = r₀/r' ∈ (1/2, 1]` is the open analytic item recorded in `PROGRESS.md`. -/

@[expose] public section
set_option autoImplicit false
noncomputable section
open scoped Classical ContDiff SchwartzMap
open WaveTurbulence

namespace WaveTurbulence.Flower.MkSlotsT

/-- The profile function `u ↦ ∏_{r ∈ rs} χ₀(u · r₀ / r)`. -/
def profFun (rs : List ℝ) (r₀ : ℝ) (u : ℝ) : ℂ := (rs.map fun r => Fourier.chi0Complex (u * (r₀ / r))).prod

theorem profFun_contDiff (rs : List ℝ) (r₀ : ℝ) : ContDiff ℝ ∞ (profFun rs r₀) := by
  induction rs with
  | nil => exact contDiff_const
  | cons r rs ih =>
    have h : profFun (r :: rs) r₀ = fun u => Fourier.chi0Complex (u * (r₀ / r)) * profFun rs r₀ u := by
      funext u; simp [profFun]
    rw [h]
    exact (Fourier.chi0Complex_contDiff.comp (contDiff_id.mul contDiff_const)).mul ih

theorem chi0Complex_hasCompactSupport : HasCompactSupport Fourier.chi0Complex :=
  Fourier.chi0_hasCompactSupport.comp_left Complex.ofReal_zero

theorem profFun_hasCompactSupport (r : ℝ) (rs : List ℝ) (r₀ : ℝ) (h : r₀ / r ≠ 0) :
    HasCompactSupport (profFun (r :: rs) r₀) := by
  have hf : profFun (r :: rs) r₀ = (fun u => Fourier.chi0Complex ((r₀ / r) • u)) * profFun rs r₀ := by
    funext u; simp [profFun, smul_eq_mul, mul_comm]
  rw [hf]
  exact (chi0Complex_hasCompactSupport.comp_smul h).mul_right

/-- **The stem profile** (a Schwartz function), for a nonempty radius list and `r₀ / r ≠ 0`. -/
def stemProfile (r : ℝ) (rs : List ℝ) (r₀ : ℝ) (h : r₀ / r ≠ 0) : 𝓢(ℝ, ℂ) :=
  (profFun_hasCompactSupport r rs r₀ h).toSchwartzMap (profFun_contDiff (r :: rs) r₀)

theorem stemProfile_apply (r : ℝ) (rs : List ℝ) (r₀ : ℝ) (h : r₀ / r ≠ 0) (u : ℝ) :
    stemProfile r rs r₀ h u = profFun (r :: rs) r₀ u := rfl

theorem chi0_abs_div (x r : ℝ) : chi0 (|x| / r) = Fourier.chi0 (x / r) := by
  rw [WaveBBridges.chi0_eq_fourier_chi0]
  rcases le_total 0 x with hx | hx
  · rw [abs_of_nonneg hx]
  · rw [abs_of_nonpos hx, neg_div, Fourier.chi0_even]

/-- **The profile at `Ω / r₀` is the product of the node's filters.** -/
theorem profFun_div (rs : List ℝ) (r₀ : ℝ) (hr₀ : r₀ ≠ 0) (x : ℝ) :
    profFun rs r₀ (x / r₀) = (radProd rs x : ℂ) := by
  unfold profFun radProd
  induction rs with
  | nil => simp
  | cons r rs ih =>
    simp only [List.map_cons, List.prod_cons, Complex.ofReal_mul]
    rw [ih]
    congr 1
    rw [chi0_abs_div]
    unfold Fourier.chi0Complex
    congr 2
    field_simp

theorem stemProfile_apply_div (r : ℝ) (rs : List ℝ) (r₀ : ℝ) (h : r₀ / r ≠ 0) (hr₀ : r₀ ≠ 0) (x : ℝ) :
    stemProfile r rs r₀ h (x / r₀) = (radProd (r :: rs) x : ℂ) :=
  profFun_div (r :: rs) r₀ hr₀ x

theorem norm_profFun_le (rs : List ℝ) (r₀ u : ℝ) : ‖profFun rs r₀ u‖ ≤ 1 := by
  unfold profFun
  induction rs with
  | nil => simp
  | cons r rs ih =>
    simp only [List.map_cons, List.prod_cons, norm_mul]
    have h1 : ‖Fourier.chi0Complex (u * (r₀ / r))‖ ≤ 1 := by
      unfold Fourier.chi0Complex
      rw [Complex.norm_real, Real.norm_of_nonneg (Fourier.chi0_nonneg _)]
      exact Fourier.chi0_le_one _
    calc _ ≤ 1 * 1 := mul_le_mul h1 ih (norm_nonneg _) zero_le_one
      _ = 1 := one_mul 1

/-- **`filt_ok`'s bound** `‖ψ u‖ ≤ 1`. -/
theorem norm_stemProfile_le (r : ℝ) (rs : List ℝ) (r₀ : ℝ) (h : r₀ / r ≠ 0) (u : ℝ) :
    ‖stemProfile r rs r₀ h u‖ ≤ 1 :=
  norm_profFun_le (r :: rs) r₀ u

/-- **One layer at the base radius is χ₀ itself.** -/
theorem stemProfile_single (r : ℝ) (h : r / r ≠ 0) : (stemProfile r [] r h : ℝ → ℂ) = FiltNT.chiS := by
  funext u
  rw [stemProfile_apply, FiltNT.chiS_apply]
  have hr : r ≠ 0 := by rintro rfl; simp at h
  simp [profFun, div_self hr, Fourier.chi0Complex]

/-- Hence its `𝔟`-norm is `filterB χ₀`. -/
theorem filterB_stemProfile_single (r : ℝ) (h : r / r ≠ 0) :
    MkDefs.filterB ⇑(stemProfile r [] r h) = MkDefs.filterB ⇑FiltNT.chiS := by
  rw [stemProfile_single]

/-- **Two layers with ratio at most `1/2` collapse to one layer**: if `r₀ ≤ r' / 2` then
`χ₀(u) · χ₀(u r₀ / r') = χ₀(u)`. -/
theorem stemProfile_two_of_le_half (r₀ r' : ℝ) (h : r₀ / r₀ ≠ 0) (hr₀ : 0 < r₀) (hr' : 2 * r₀ ≤ r') :
    (stemProfile r₀ [r'] r₀ h : ℝ → ℂ) = FiltNT.chiS := by
  funext u
  rw [stemProfile_apply, FiltNT.chiS_apply]
  simp only [profFun, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one,
    div_self hr₀.ne', Fourier.chi0Complex]
  by_cases hu : |u| < 1
  · have hr'0 : 0 < r' := by linarith
    have hsmall : |u * (r₀ / r')| ≤ 1 / 2 := by
      rw [abs_mul, abs_of_pos (div_pos hr₀ hr'0)]
      have h1 : r₀ / r' ≤ 1 / 2 := by rw [div_le_iff₀ hr'0]; linarith
      calc |u| * (r₀ / r') ≤ 1 * (1 / 2) :=
            mul_le_mul hu.le h1 (div_pos hr₀ hr'0).le zero_le_one
        _ = 1 / 2 := one_mul _
    rw [Fourier.chi0_eq_one hsmall]
    simp
  · rw [Fourier.chi0_eq_zero (not_lt.mp hu)]
    simp

end WaveTurbulence.Flower.MkSlotsT
