/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Fourier.CutoffFourierDecay
public import WaveTurbulence.Foundations.Flower.MkSlotsT.Piece

/-! # B3s-HELPER6 G2 (analytic part): the `𝔟`-norm of one- and two-layer stem profiles

A stem node with radii `r :: rs` carries γ's atom filter `(r₀, stemProfile r rs r₀)` with `r₀ = rmin r rs` and
profile `u ↦ ∏_{r' ∈ r :: rs} χ₀(u r₀ / r')`. With at most two radii (σ's `2^{σ j} L` and the selection shell
`Rs j`) the profile is `χ₀(u)·χ₀(uλ)` for a ratio `λ ∈ [0,1]` (`λ = 0`: one layer, since `χ₀(0) = 1`), the
two-layer profile `twoProf λ`. This file proves the uniform bound left open by helper γ:

* `twoR_gevrey`: `χ₀(x)χ₀(xλ)` satisfies main's Gevrey-2 bound with constants `(e⁴)², 2(16 + 16e²)` for `|λ| ≤ 1`
  (`Fourier.chi0_gevreyTwoBound`, `GevreyTwoBound.comp_affine`, `.mul`, `.mono`);
* `twoProf_integral_norm_iteratedDeriv_le`: the `L¹` norms of its derivatives (support in `[-1,1]`);
* `twoProf_fourier_le`: `(1 + |u|⁴) ‖𝓕 (twoProf λ) u‖ ≤ twoK` (Mathlib's `Real.one_add_pow_mul_norm_fourier_le`);
* **`filterB_twoProf_le`**: `filterB (twoProf λ) ≤ twoLayerB := 8 · twoK · ∫ (1+|s|)⁻²` for every `|λ| ≤ 1`;
* **`filterB_stemProfile_le`**, **`filterB_filtOfRad_le`**: γ's atom filters with at most two radii (all `≥ 1`)
  have `filterB ≤ twoLayerB`.

The derivative/support lemmas `iteratedDeriv_ofReal`, `compact_iteratedDeriv'`, `tsupport_iteratedDeriv'` and the
proof of `twoProf_integral_norm_iteratedDeriv_le` are copied by source from main's
`Fourier/CutoffFourierDecay.lean` (private there; see `COPIED-SHA256SUMS`). -/

@[expose] public section
set_option autoImplicit false
noncomputable section
open MeasureTheory Set
open scoped FourierTransform ContDiff

namespace WaveTurbulence.Flower.MkSlotsG

/-! ## The profile and its Gevrey bound -/

/-- The Gevrey prefactor of χ₀ (main's `chi0_gevreyTwoBound`). -/
def gC : ℝ := Real.exp 4

/-- The Gevrey exponential constant of χ₀. -/
def gA : ℝ := 16 + 16 * Real.exp 2

theorem gC_pos : 0 < gC := Real.exp_pos 4

theorem gA_pos : 0 < gA := by unfold gA; positivity

/-- The real two-layer profile `χ₀(x)·χ₀(xλ)`. -/
def twoR (lam x : ℝ) : ℝ := Fourier.chi0 x * Fourier.chi0 (x * lam)

/-- **The two-layer profile** `χ₀(u)·χ₀(uλ)` (complex, as γ's `profFun`). -/
def twoProf (lam u : ℝ) : ℂ := Fourier.chi0Complex u * Fourier.chi0Complex (u * lam)

theorem twoProf_eq (lam : ℝ) : twoProf lam = fun x => ((twoR lam x : ℝ) : ℂ) := by
  funext x
  simp [twoProf, twoR, Fourier.chi0Complex]

theorem twoR_contDiff (lam : ℝ) : ContDiff ℝ ∞ (twoR lam) := by
  unfold twoR
  exact Fourier.chi0_contDiff.mul (Fourier.chi0_contDiff.comp (contDiff_id.mul contDiff_const))

theorem twoProf_contDiff (lam : ℝ) : ContDiff ℝ ∞ (twoProf lam) := by
  rw [twoProf_eq]
  exact Complex.ofRealCLM.contDiff.comp (twoR_contDiff lam)

/-- **Gevrey bound of the two-layer profile**, uniformly in `|λ| ≤ 1`. -/
theorem twoR_gevrey (lam : ℝ) (hlam : |lam| ≤ 1) : Fourier.GevreyTwoBound (twoR lam) (gC * gC) (gA + gA) := by
  have h1 : Fourier.GevreyTwoBound Fourier.chi0 gC gA := Fourier.chi0_gevreyTwoBound
  have h2 := h1.comp_affine Fourier.chi0_contDiff lam 0
  have h2' : Fourier.GevreyTwoBound (fun x => Fourier.chi0 (lam * x + 0)) gC gA :=
    h2.mono gC_pos.le (by have := gA_pos; positivity) le_rfl (mul_le_of_le_one_left gA_pos.le hlam)
  have hs : ContDiff ℝ ∞ (fun x => Fourier.chi0 (lam * x + 0)) :=
    Fourier.chi0_contDiff.comp ((contDiff_const.mul contDiff_id).add contDiff_const)
  have hm := h1.mul h2' Fourier.chi0_contDiff hs gC_pos.le gC_pos.le gA_pos.le gA_pos.le
  have he : twoR lam = fun x => Fourier.chi0 x * Fourier.chi0 (lam * x + 0) := by
    funext x
    rw [twoR, add_zero, mul_comm lam x]
  rw [he]
  exact hm

/-! ## Derivatives and support (copied by source from main's `CutoffFourierDecay`) -/

-- [copied] main Fourier/CutoffFourierDecay.lean (sha256 in COPIED-SHA256SUMS) L34-44, generalized from
-- `chi0Complex` to the complex cast of any smooth real function.
theorem iteratedDeriv_ofReal {f : ℝ → ℝ} (hf : ContDiff ℝ ∞ f) (n : ℕ) :
    iteratedDeriv n (fun x => (f x : ℂ)) = fun x => ((iteratedDeriv n f x : ℝ) : ℂ) := by
  induction n with
  | zero => funext x; simp
  | succ n ih =>
    rw [iteratedDeriv_succ, ih]
    funext x
    have hd := (hf.differentiable_iteratedDeriv n
      (by exact_mod_cast (ENat.natCast_lt_top n)) x).hasDerivAt
    simpa only [iteratedDeriv_succ] using hd.ofReal_comp.deriv

-- [copied] main Fourier/CutoffFourierDecay.lean L46-49 (`compact_iteratedDeriv`, private there).
theorem compact_iteratedDeriv' {f : ℝ → ℂ} (hf : HasCompactSupport f) (n : ℕ) :
    HasCompactSupport (iteratedDeriv n f) := by
  induction n with
  | zero => exact hf
  | succ n ih => simpa only [iteratedDeriv_succ] using ih.deriv

-- [copied] main Fourier/CutoffFourierDecay.lean L51-57 (`tsupport_iteratedDeriv`, private there).
theorem tsupport_iteratedDeriv' {f : ℝ → ℂ} (n : ℕ) :
    tsupport (iteratedDeriv n f) ⊆ tsupport f := by
  induction n with
  | zero => exact subset_rfl
  | succ n ih =>
    rw [iteratedDeriv_succ]
    exact tsupport_deriv_subset.trans ih
-- [end copied]

theorem twoProf_eq_zero (lam : ℝ) {x : ℝ} (hx : 1 ≤ |x|) : twoProf lam x = 0 := by
  simp [twoProf, Fourier.chi0Complex, Fourier.chi0_eq_zero hx]

theorem twoProf_tsupport (lam : ℝ) : tsupport (twoProf lam) ⊆ Icc (-1 : ℝ) 1 := by
  apply closure_minimal _ isClosed_Icc
  intro x hx
  by_contra hh
  apply hx
  refine twoProf_eq_zero lam ?_
  by_contra h
  have ha := abs_lt.mp (lt_of_not_ge h)
  exact hh ⟨ha.1.le, ha.2.le⟩

theorem twoProf_hasCompactSupport (lam : ℝ) : HasCompactSupport (twoProf lam) :=
  HasCompactSupport.intro (isCompact_Icc (a := (-1 : ℝ)) (b := 1)) (fun x hx => by
    by_contra h
    exact hx (twoProf_tsupport lam (subset_closure h)))

theorem twoProf_iteratedDeriv_integrable (lam : ℝ) (n : ℕ) : Integrable (iteratedDeriv n (twoProf lam)) :=
  ((twoProf_contDiff lam).continuous_iteratedDeriv n (by simp)).integrable_of_hasCompactSupport
    (compact_iteratedDeriv' (twoProf_hasCompactSupport lam) n)

-- [copied] main Fourier/CutoffFourierDecay.lean L81-103 (proof of `chi0Complex_integral_norm_iteratedDeriv_le`),
-- `chi0Complex` → `twoProf lam`, Gevrey constants → `(gC * gC, gA + gA)`.
/-- The `L¹` norms of the derivatives of the two-layer profile. -/
theorem twoProf_integral_norm_iteratedDeriv_le (lam : ℝ) (hlam : |lam| ≤ 1) (n : ℕ) :
    (∫ x, ‖iteratedDeriv n (twoProf lam) x‖) ≤
      2 * ((gC * gC) * (gA + gA) ^ n * (Nat.factorial (2 * n) : ℝ)) := by
  have hb (x : ℝ) : ‖iteratedDeriv n (twoProf lam) x‖ ≤ (gC * gC) * (gA + gA) ^ n * (Nat.factorial (2 * n) : ℝ) := by
    rw [twoProf_eq, iteratedDeriv_ofReal (twoR_contDiff lam)]
    simpa only [Complex.norm_real, Real.norm_eq_abs] using twoR_gevrey lam hlam n x
  have hs : Function.support (fun x => ‖iteratedDeriv n (twoProf lam) x‖) ⊆ Icc (-1 : ℝ) 1 := by
    intro x hx
    apply twoProf_tsupport lam
    apply tsupport_iteratedDeriv' n
    apply subset_closure
    simpa only [Function.mem_support, norm_ne_zero_iff] using hx
  rw [← setIntegral_eq_integral_of_forall_compl_eq_zero (s := Icc (-1 : ℝ) 1)
    (fun x hx => by by_contra h; exact hx (hs h))]
  have h := norm_setIntegral_le_of_norm_le_const_ae
    (μ := (volume : Measure ℝ)) (s := Icc (-1 : ℝ) 1)
    (f := fun x => ‖iteratedDeriv n (twoProf lam) x‖) (by simp)
    (ae_of_all _ (fun x => (by simpa only [Real.norm_of_nonneg (norm_nonneg _)] using hb x)))
  have hn : 0 ≤ ∫ x in Icc (-1 : ℝ) 1, ‖iteratedDeriv n (twoProf lam) x‖ :=
    integral_nonneg (fun _ => norm_nonneg _)
  rw [Real.norm_of_nonneg hn] at h
  have hv : (volume : Measure ℝ).real (Icc (-1 : ℝ) 1) = 2 := by
    simp [Real.volume_Icc, Measure.real]
    norm_num
  rw [hv] at h
  linarith
-- [end copied]

/-! ## The Fourier bound and the `𝔟`-norm -/

/-- The constant of the quartic Fourier decay. -/
def twoK : ℝ :=
  2 * ((gC * gC) * (gA + gA) ^ 0 * (Nat.factorial (2 * 0) : ℝ)) +
    ((2 * Real.pi) ^ 4)⁻¹ * (2 * ((gC * gC) * (gA + gA) ^ 4 * (Nat.factorial (2 * 4) : ℝ)))

theorem twoProf_fourier_le (lam : ℝ) (hlam : |lam| ≤ 1) (u : ℝ) :
    (1 + |u| ^ 4) * ‖𝓕 (twoProf lam) u‖ ≤ twoK := by
  have h := Real.one_add_pow_mul_norm_fourier_le (n := 4) ((twoProf_contDiff lam).of_le (by simp))
    (fun k _ => twoProf_iteratedDeriv_integrable lam k) u
  refine h.trans (add_le_add ?_ (mul_le_mul_of_nonneg_left (twoProf_integral_norm_iteratedDeriv_le lam hlam 4)
    (by positivity)))
  have h0 := twoProf_integral_norm_iteratedDeriv_le lam hlam 0
  simpa only [iteratedDeriv_zero] using h0

theorem one_add_pow_four_le (a : ℝ) (ha : 0 ≤ a) : (1 + a) ^ 4 ≤ 8 * (1 + a ^ 4) := by
  nlinarith [mul_nonneg (sq_nonneg (a - 1)) (show (0 : ℝ) ≤ 7 * a ^ 2 + 10 * a + 7 by positivity)]

theorem twoProf_weighted_le (lam : ℝ) (hlam : |lam| ≤ 1) (u : ℝ) :
    (1 + |u|) ^ 2 * ‖𝓕 (twoProf lam) u‖ ≤ 8 * twoK * ((1 + |u|) ^ 2)⁻¹ := by
  have hpos : 0 < (1 + |u|) ^ 2 := by positivity
  rw [← div_eq_mul_inv, le_div_iff₀ hpos]
  have h4 := one_add_pow_four_le |u| (abs_nonneg u)
  have hF := twoProf_fourier_le lam hlam u
  have hn := norm_nonneg (𝓕 (twoProf lam) u)
  calc (1 + |u|) ^ 2 * ‖𝓕 (twoProf lam) u‖ * (1 + |u|) ^ 2 = (1 + |u|) ^ 4 * ‖𝓕 (twoProf lam) u‖ := by ring
    _ ≤ 8 * (1 + |u| ^ 4) * ‖𝓕 (twoProf lam) u‖ := mul_le_mul_of_nonneg_right h4 hn
    _ = 8 * ((1 + |u| ^ 4) * ‖𝓕 (twoProf lam) u‖) := by ring
    _ ≤ 8 * twoK := by linarith

/-- `∫ (1 + |s|)⁻²`. -/
def invSqInt : ℝ := ∫ s : ℝ, ((1 + |s|) ^ 2)⁻¹

theorem integrable_invSq : Integrable (fun s : ℝ => ((1 + |s|) ^ 2)⁻¹) := by
  have h := integrable_one_add_norm (E := ℝ) (μ := volume) (r := 2)
    (by rw [Module.finrank_self]; norm_num)
  refine h.congr (Filter.Eventually.of_forall fun s => ?_)
  simp only [Real.norm_eq_abs]
  rw [Real.rpow_neg (by positivity)]
  norm_cast

/-- **The uniform `𝔟`-bound of one- and two-layer stem profiles.** -/
def twoLayerB : ℝ := 8 * twoK * invSqInt

/-- **`filterB (χ₀ · χ₀(λ ·)) ≤ twoLayerB`** for every `|λ| ≤ 1`. -/
theorem filterB_twoProf_le (lam : ℝ) (hlam : |lam| ≤ 1) : MkDefs.filterB (twoProf lam) ≤ twoLayerB := by
  unfold MkDefs.filterB twoLayerB invSqInt
  rw [← integral_const_mul]
  exact integral_mono_of_nonneg (ae_of_all _ fun ξ => by positivity) (integrable_invSq.const_mul _)
    (ae_of_all _ fun ξ => twoProf_weighted_le lam hlam ξ)

/-! ## γ's atom filters -/

theorem chi0Complex_zero : Fourier.chi0Complex 0 = 1 := by
  simp [Fourier.chi0Complex, Fourier.chi0_eq_one (show |(0 : ℝ)| ≤ 1 / 2 by norm_num)]

/-- **One layer**: γ's profile is `twoProf 0` (= χ₀). -/
theorem stemProfile_one (r : ℝ) (h : MkSlotsT.rmin r [] / r ≠ 0) (hr : 1 ≤ r) :
    (MkSlotsT.stemProfile r [] (MkSlotsT.rmin r []) h : ℝ → ℂ) = twoProf 0 := by
  funext u
  have hr0 : r ≠ 0 := by linarith
  have hm : MkSlotsT.rmin r [] = r := rfl
  rw [MkSlotsT.stemProfile_apply]
  simp only [MkSlotsT.profFun, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one, hm,
    div_self hr0, twoProf, mul_zero, chi0Complex_zero]

/-- **Two layers**: γ's profile is a two-layer profile `twoProf λ` with `|λ| ≤ 1`. -/
theorem stemProfile_two (r r' : ℝ) (h : MkSlotsT.rmin r [r'] / r ≠ 0) (hr : 1 ≤ r) (hr' : 1 ≤ r') :
    ∃ lam : ℝ, |lam| ≤ 1 ∧ (MkSlotsT.stemProfile r [r'] (MkSlotsT.rmin r [r']) h : ℝ → ℂ) = twoProf lam := by
  have hm : MkSlotsT.rmin r [r'] = min r r' := rfl
  have hr0 : r ≠ 0 := by linarith
  have hr'0 : r' ≠ 0 := by linarith
  rcases le_total r r' with hle | hle
  · refine ⟨r / r', ?_, ?_⟩
    · rw [abs_of_nonneg (by positivity), div_le_one (by linarith)]
      exact hle
    · funext u
      rw [MkSlotsT.stemProfile_apply]
      simp only [MkSlotsT.profFun, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one, hm,
        min_eq_left hle, div_self hr0, twoProf]
  · refine ⟨r' / r, ?_, ?_⟩
    · rw [abs_of_nonneg (by positivity), div_le_one (by linarith)]
      exact hle
    · funext u
      rw [MkSlotsT.stemProfile_apply]
      simp only [MkSlotsT.profFun, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one, hm,
        min_eq_right hle, div_self hr'0, twoProf]
      ring

/-- **The `𝔟`-norm of a stem profile with one or two radii** (all `≥ 1`). -/
theorem filterB_stemProfile_le (r : ℝ) (rs : List ℝ) (hrs : ∀ x ∈ r :: rs, 1 ≤ x) (hlen : rs.length ≤ 1) :
    MkDefs.filterB ⇑(MkSlotsT.stemProfile r rs (MkSlotsT.rmin r rs) (MkSlotsT.rmin_div_ne_zero r rs hrs)) ≤
      twoLayerB := by
  have hr : 1 ≤ r := hrs r (List.mem_cons_self ..)
  match rs, hrs, hlen with
  | [], hrs, _ =>
    rw [stemProfile_one r _ hr]
    exact filterB_twoProf_le 0 (by simp)
  | [r'], hrs, _ =>
    have hr' : 1 ≤ r' := hrs r' (List.mem_cons_of_mem _ (List.mem_cons_self ..))
    obtain ⟨lam, hlam, he⟩ := stemProfile_two r r' (MkSlotsT.rmin_div_ne_zero r [r'] hrs) hr hr'
    rw [he]
    exact filterB_twoProf_le lam hlam
  | _ :: _ :: _, _, hlen => simp at hlen

/-- **γ's atom filter of a node with at most two radii** has `filterB ≤ twoLayerB`. -/
theorem filterB_filtOfRad_le (rs : List ℝ) (hrs : ∀ x ∈ rs, 1 ≤ x) (hlen : rs.length ≤ 2)
    (q : ℝ × SchwartzMap ℝ ℂ) (hq : MkSlotsT.filtOfRad rs hrs = some q) : MkDefs.filterB ⇑q.2 ≤ twoLayerB := by
  cases rs with
  | nil => cases hq
  | cons r rs =>
    simp only [MkSlotsT.filtOfRad, Option.some.injEq] at hq
    subst hq
    exact filterB_stemProfile_le r rs hrs (by simp at hlen; omega)

end WaveTurbulence.Flower.MkSlotsG
