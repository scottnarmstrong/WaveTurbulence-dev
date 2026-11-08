/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Flower.MkSlotsT.Piece
public import WaveTurbulence.Foundations.Flower.FiltLink.Filters
public import Mathlib.Analysis.SpecialFunctions.JapaneseBracket

/-! # B3s-HELPER5 (γ) T4: the `𝔟`-norm of two-layer atom filters is uniformly bounded

`twoProf lam u = χ₀(u) · χ₀(lam u)`. For `|lam| ≤ 1`:
* the derivatives of order `≤ 4` are bounded uniformly in `lam` (Leibniz, `iteratedDeriv_comp_const_smul`);
* they vanish off `[-1, 1]`, so their `L¹` norms are bounded uniformly;
* integrating by parts four times (`Real.fourier_iteratedDeriv`), `(1 + |ξ|)² ‖𝓕 twoProf ξ‖ ≤ K (1 + |ξ|)⁻²`;
* hence **`filterB_twoProf_le`**: `∃ K, ∀ lam, |lam| ≤ 1 → filterB (twoProf lam) ≤ K`.
With the base radius the smallest radius (`Piece.rmin`), every two-layer atom filter has this form
(`stemProfile_two_eq_twoProf`), so `cθ ≥ max (filterB χ₀) K` covers one- and two-layer stem filters. -/

@[expose] public section
set_option autoImplicit false
noncomputable section
open scoped FourierTransform ContDiff
open MeasureTheory Set Real

namespace WaveTurbulence.Flower.MkSlotsT

/-- The two-layer profile `χ₀(u) χ₀(lam u)`. -/
def twoProf (lam : ℝ) (u : ℝ) : ℂ := Fourier.chi0Complex u * Fourier.chi0Complex (lam * u)

theorem chi0Complex_eq_zero {x : ℝ} (hx : 1 ≤ |x|) : Fourier.chi0Complex x = 0 := by
  unfold Fourier.chi0Complex
  rw [Fourier.chi0_eq_zero hx, Complex.ofReal_zero]

theorem twoProf_contDiff (lam : ℝ) : ContDiff ℝ ∞ (twoProf lam) :=
  Fourier.chi0Complex_contDiff.mul (Fourier.chi0Complex_contDiff.comp (contDiff_const.mul contDiff_id))

theorem twoProf_eq_zero (lam : ℝ) {x : ℝ} (hx : x ∉ Icc (-1 : ℝ) 1) : twoProf lam x = 0 := by
  unfold twoProf
  rw [chi0Complex_eq_zero, zero_mul]
  by_contra h
  have ha := abs_lt.mp (lt_of_not_ge h)
  exact hx ⟨ha.1.le, ha.2.le⟩

theorem tsupport_twoProf (lam : ℝ) : tsupport (twoProf lam) ⊆ Icc (-1 : ℝ) 1 := by
  apply closure_minimal _ isClosed_Icc
  intro x hx
  by_contra hh
  exact hx (twoProf_eq_zero lam hh)

theorem hasCompactSupport_twoProf (lam : ℝ) : HasCompactSupport (twoProf lam) :=
  HasCompactSupport.intro (isCompact_Icc (a := (-1 : ℝ)) (b := 1)) fun x hx => by
    by_contra h
    exact hx (tsupport_twoProf lam (subset_closure h))

/-- Uniform bounds of the derivatives of χ₀. -/
theorem exists_bound_iteratedDeriv_chi0 (n : ℕ) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ x, ‖iteratedDeriv n Fourier.chi0Complex x‖ ≤ M := by
  obtain ⟨C, hC⟩ := (Fourier.chi0Complex_contDiff.continuous_iteratedDeriv n (by simp)).bounded_above_of_compact_support
    (FiltLink.hasCompactSupport_iteratedDeriv chi0Complex_hasCompactSupport n)
  exact ⟨max C 0, le_max_right _ _, fun x => (hC x).trans (le_max_left _ _)⟩

/-- The bound function. -/
def chiM (n : ℕ) : ℝ := (exists_bound_iteratedDeriv_chi0 n).choose

theorem chiM_nonneg (n : ℕ) : 0 ≤ chiM n := (exists_bound_iteratedDeriv_chi0 n).choose_spec.1

theorem norm_iteratedDeriv_chi0_le (n : ℕ) (x : ℝ) : ‖iteratedDeriv n Fourier.chi0Complex x‖ ≤ chiM n :=
  (exists_bound_iteratedDeriv_chi0 n).choose_spec.2 x

/-- The Leibniz constant of order `n`. -/
def leibK (n : ℕ) : ℝ := ∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) * chiM i * chiM (n - i)

theorem leibK_nonneg (n : ℕ) : 0 ≤ leibK n :=
  Finset.sum_nonneg fun i _ => mul_nonneg (mul_nonneg (by positivity) (chiM_nonneg i)) (chiM_nonneg _)

/-- **Uniform derivative bounds** of the two-layer profile. -/
theorem norm_iteratedDeriv_twoProf_le (lam : ℝ) (hl : |lam| ≤ 1) (n : ℕ) (x : ℝ) :
    ‖iteratedDeriv n (twoProf lam) x‖ ≤ leibK n := by
  rw [← norm_iteratedFDeriv_eq_norm_iteratedDeriv]
  have hg : ContDiff ℝ ∞ (fun y => Fourier.chi0Complex (lam * y)) :=
    Fourier.chi0Complex_contDiff.comp (contDiff_const.mul contDiff_id)
  refine (norm_iteratedFDeriv_mul_le (𝕜 := ℝ) Fourier.chi0Complex_contDiff hg x (n := n) (by simp)).trans ?_
  refine Finset.sum_le_sum fun i _ => ?_
  rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv, norm_iteratedFDeriv_eq_norm_iteratedDeriv,
    iteratedDeriv_comp_const_smul (Fourier.chi0Complex_contDiff.of_le (by simp)) lam]
  simp only [norm_smul, norm_pow, Real.norm_eq_abs]
  have h1 : |lam| ^ (n - i) ≤ 1 := pow_le_one₀ (abs_nonneg _) hl
  have h2 := norm_iteratedDeriv_chi0_le (n - i) (lam * x)
  have h3 := norm_iteratedDeriv_chi0_le i x
  have h4 : |lam| ^ (n - i) * ‖iteratedDeriv (n - i) Fourier.chi0Complex (lam * x)‖ ≤ chiM (n - i) :=
    calc _ ≤ 1 * chiM (n - i) := mul_le_mul h1 h2 (norm_nonneg _) zero_le_one
      _ = chiM (n - i) := one_mul _
  have hb : 0 ≤ |lam| ^ (n - i) * ‖iteratedDeriv (n - i) Fourier.chi0Complex (lam * x)‖ :=
    mul_nonneg (pow_nonneg (abs_nonneg _) _) (norm_nonneg _)
  have hc : (0 : ℝ) ≤ (n.choose i : ℝ) := by positivity
  exact mul_le_mul (mul_le_mul_of_nonneg_left h3 hc) h4 hb (mul_nonneg hc (chiM_nonneg i))

theorem iteratedDeriv_twoProf_eq_zero (lam : ℝ) (n : ℕ) {x : ℝ} (hx : x ∉ Icc (-1 : ℝ) 1) :
    iteratedDeriv n (twoProf lam) x = 0 := by
  have h : x ∉ Function.support (iteratedFDeriv ℝ n (twoProf lam)) := fun h =>
    hx (tsupport_twoProf lam (support_iteratedFDeriv_subset n h))
  rw [Function.notMem_support] at h
  rw [iteratedDeriv_eq_iteratedFDeriv, h]
  rfl

/-- `L¹` bound for a function bounded by `K` and vanishing off `[-1, 1]`. -/
theorem integral_norm_le_of_supp (F : ℝ → ℂ) (K : ℝ) (hK : 0 ≤ K) (hF : ∀ x, ‖F x‖ ≤ K)
    (hs : ∀ x, x ∉ Icc (-1 : ℝ) 1 → F x = 0) : ∫ x, ‖F x‖ ≤ 2 * K := by
  have hle : ∀ x, ‖F x‖ ≤ (Icc (-1 : ℝ) 1).indicator (fun _ => K) x := by
    intro x
    by_cases hx : x ∈ Icc (-1 : ℝ) 1
    · rw [indicator_of_mem hx]; exact hF x
    · rw [indicator_of_notMem hx, hs x hx, norm_zero]
  have hint : Integrable ((Icc (-1 : ℝ) 1).indicator (fun _ => K)) :=
    (integrableOn_const (μ := volume) (s := Icc (-1 : ℝ) 1) (C := K)
      (by rw [Real.volume_Icc]; exact ENNReal.ofReal_ne_top)).integrable_indicator₀
      measurableSet_Icc.nullMeasurableSet
  calc ∫ x, ‖F x‖ ≤ ∫ x, (Icc (-1 : ℝ) 1).indicator (fun _ => K) x :=
        integral_mono_of_nonneg (Filter.Eventually.of_forall fun x => norm_nonneg _) hint
          (Filter.Eventually.of_forall hle)
    _ = 2 * K := by
        rw [integral_indicator_const _ measurableSet_Icc, Real.volume_real_Icc]
        norm_num [smul_eq_mul]


theorem integrable_iteratedDeriv_twoProf (lam : ℝ) (n : ℕ) : Integrable (iteratedDeriv n (twoProf lam)) :=
  ((twoProf_contDiff lam).continuous_iteratedDeriv n (by simp)).integrable_of_hasCompactSupport
    (FiltLink.hasCompactSupport_iteratedDeriv (hasCompactSupport_twoProf lam) n)

theorem integral_norm_iteratedDeriv_twoProf_le (lam : ℝ) (hl : |lam| ≤ 1) (n : ℕ) :
    ∫ x, ‖iteratedDeriv n (twoProf lam) x‖ ≤ 2 * leibK n :=
  integral_norm_le_of_supp _ _ (leibK_nonneg n) (norm_iteratedDeriv_twoProf_le lam hl n)
    fun _ hx => iteratedDeriv_twoProf_eq_zero lam n hx

/-- **The Fourier transform of the two-layer profile**: bounded, and `|ξ|⁻⁴`-decaying, uniformly in `lam`. -/
theorem fourier_twoProf_bounds (lam : ℝ) (hl : |lam| ≤ 1) (ξ : ℝ) :
    ‖𝓕 (twoProf lam) ξ‖ ≤ 2 * leibK 0 ∧ (2 * π * |ξ|) ^ 4 * ‖𝓕 (twoProf lam) ξ‖ ≤ 2 * leibK 4 := by
  constructor
  · refine (Real.norm_fourier_le_integral_norm (twoProf lam) ξ).trans ?_
    have := integral_norm_iteratedDeriv_twoProf_le lam hl 0
    simpa only [iteratedDeriv_zero] using this
  · have he := Real.fourier_iteratedDeriv (N := (⊤ : ℕ∞)) (twoProf_contDiff lam)
      (fun m _ => integrable_iteratedDeriv_twoProf lam m) (n := 4) (by simp)
    have hh := (Real.norm_fourier_le_integral_norm (iteratedDeriv 4 (twoProf lam)) ξ).trans
      (integral_norm_iteratedDeriv_twoProf_le lam hl 4)
    rw [he, norm_smul, norm_pow] at hh
    simpa [Complex.norm_mul, Complex.norm_ofNat, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos Real.pi_pos, mul_assoc, mul_pow] using hh

/-- The constant of the pointwise bound. -/
def twoKc : ℝ := 32 * (1 + leibK 0 + leibK 4)

theorem pointwise_twoProf (lam : ℝ) (hl : |lam| ≤ 1) (ξ : ℝ) :
    (1 + |ξ|) ^ 4 * ‖𝓕 (twoProf lam) ξ‖ ≤ twoKc := by
  obtain ⟨h0, h4⟩ := fourier_twoProf_bounds lam hl ξ
  have hA := norm_nonneg (𝓕 (twoProf lam) ξ)
  have hk0 := leibK_nonneg 0
  have hk4 := leibK_nonneg 4
  have ha := abs_nonneg ξ
  unfold twoKc
  rcases le_total |ξ| 1 with h | h
  · have h1 : (1 + |ξ|) ^ 4 ≤ 16 := by
      have : 1 + |ξ| ≤ 2 := by linarith
      calc (1 + |ξ|) ^ 4 ≤ 2 ^ 4 := pow_le_pow_left₀ (by linarith) this 4
        _ = 16 := by norm_num
    calc (1 + |ξ|) ^ 4 * ‖𝓕 (twoProf lam) ξ‖ ≤ 16 * (2 * leibK 0) :=
          mul_le_mul h1 h0 hA (by norm_num)
      _ ≤ _ := by nlinarith
  · have hpi : (1 : ℝ) ≤ 2 * π := by linarith [Real.pi_gt_three]
    have h1 : (1 + |ξ|) ^ 4 ≤ 16 * (2 * π * |ξ|) ^ 4 := by
      have e1 : 1 + |ξ| ≤ 2 * |ξ| := by linarith
      have e2 : 2 * |ξ| ≤ 2 * (2 * π * |ξ|) := by nlinarith
      calc (1 + |ξ|) ^ 4 ≤ (2 * (2 * π * |ξ|)) ^ 4 := pow_le_pow_left₀ (by linarith) (e1.trans e2) 4
        _ = 16 * (2 * π * |ξ|) ^ 4 := by ring
    calc (1 + |ξ|) ^ 4 * ‖𝓕 (twoProf lam) ξ‖ ≤ 16 * (2 * π * |ξ|) ^ 4 * ‖𝓕 (twoProf lam) ξ‖ :=
          mul_le_mul_of_nonneg_right h1 hA
      _ = 16 * ((2 * π * |ξ|) ^ 4 * ‖𝓕 (twoProf lam) ξ‖) := by ring
      _ ≤ 16 * (2 * leibK 4) := by gcongr
      _ ≤ _ := by nlinarith

/-- The uniform bound of the `𝔟`-norm of two-layer profiles. -/
def twoK : ℝ := twoKc * ∫ ξ : ℝ, (1 + ‖ξ‖) ^ (-(2 : ℝ))

/-- **The `𝔟`-norm of the two-layer profiles is bounded uniformly in the layer ratio.** -/
theorem filterB_twoProf_le (lam : ℝ) (hl : |lam| ≤ 1) : MkDefs.filterB (twoProf lam) ≤ twoK := by
  unfold MkDefs.filterB twoK
  rw [← integral_const_mul]
  have hint : Integrable (fun ξ : ℝ => twoKc * (1 + ‖ξ‖) ^ (-(2 : ℝ))) :=
    (integrable_one_add_norm (E := ℝ) (μ := volume) (r := 2) (by simp)).const_mul twoKc
  refine integral_mono_of_nonneg (Filter.Eventually.of_forall fun ξ => by positivity) hint
    (Filter.Eventually.of_forall fun ξ => ?_)
  have hp := pointwise_twoProf lam hl ξ
  have hpos : 0 < 1 + |ξ| := by linarith [abs_nonneg ξ]
  show (1 + |ξ|) ^ 2 * ‖𝓕 (twoProf lam) ξ‖ ≤ twoKc * (1 + ‖ξ‖) ^ (-(2 : ℝ))
  rw [Real.norm_eq_abs, Real.rpow_neg hpos.le, show ((2 : ℝ)) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
  rw [le_mul_inv_iff₀ (by positivity)]
  calc (1 + |ξ|) ^ 2 * ‖𝓕 (twoProf lam) ξ‖ * (1 + |ξ|) ^ 2 = (1 + |ξ|) ^ 4 * ‖𝓕 (twoProf lam) ξ‖ := by ring
    _ ≤ twoKc := hp

/-- A two-layer stem profile with base radius the smaller radius is `twoProf` at the layer ratio `≤ 1`. -/
theorem stemProfile_two_eq (r r' : ℝ) (hr : 0 < r) (hr' : 0 < r') (h : rmin r [r'] / r ≠ 0) :
    ∃ lam : ℝ, |lam| ≤ 1 ∧ (stemProfile r [r'] (rmin r [r']) h : ℝ → ℂ) = twoProf lam := by
  have hmin : rmin r [r'] = min r r' := rfl
  rcases le_total r r' with hle | hle
  · refine ⟨r / r', ?_, ?_⟩
    · rw [abs_of_pos (div_pos hr hr')]; exact (div_le_one hr').mpr hle
    · funext u
      rw [stemProfile_apply]
      simp only [profFun, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one, hmin,
        min_eq_left hle, div_self hr.ne', twoProf]
      ring_nf
  · refine ⟨r' / r, ?_, ?_⟩
    · rw [abs_of_pos (div_pos hr' hr)]; exact (div_le_one hr).mpr hle
    · funext u
      rw [stemProfile_apply]
      simp only [profFun, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one, hmin,
        min_eq_right hle, div_self hr'.ne', twoProf]
      ring_nf

/-- **`filt_ok`'s `𝔟`-norm bound for one- and two-layer atom filters.** -/
theorem filterB_filtOfRad_le (rs : List ℝ) (hrs : ∀ x ∈ rs, 1 ≤ x) (hlen : rs.length ≤ 2)
    (q : ℝ × SchwartzMap ℝ ℂ) (hq : filtOfRad rs hrs = some q) :
    MkDefs.filterB ⇑q.2 ≤ max (MkDefs.filterB ⇑FiltNT.chiS) twoK := by
  match rs, hrs, hlen, hq with
  | [r], hrs, _, hq =>
    simp only [filtOfRad, Option.some.injEq] at hq
    subst hq
    have h := filterB_stemProfile_single r (by
      have := hrs r (List.mem_singleton_self r); exact div_ne_zero (by linarith) (by linarith))
    exact le_max_of_le_left (le_of_eq (by simpa [rmin] using h))
  | [r, r'], hrs, _, hq =>
    simp only [filtOfRad, Option.some.injEq] at hq
    subst hq
    have h1 : 1 ≤ r := hrs r (by simp)
    have h2 : 1 ≤ r' := hrs r' (by simp)
    obtain ⟨lam, hl, he⟩ := stemProfile_two_eq r r' (by linarith) (by linarith) _
    exact le_max_of_le_right (by rw [he]; exact filterB_twoProf_le lam hl)

end WaveTurbulence.Flower.MkSlotsT
