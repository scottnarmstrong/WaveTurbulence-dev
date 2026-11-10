/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.NLS.FourierEquation
public import WaveTurbulence.Frozen.Defs.SolvableEvent

/-!
# Energy identities for smooth NLS solutions: mass conservation and uniqueness

For smooth solutions of (NLS) `(i∂ₜ - Δ)u + α|u|²u = 0` on `𝕋_L^d` (TARGET L278–L283, frozen
`IsSmoothNLSSolution`):

* `IsSmoothNLSSolution.integral_normSq_eq` and `IsSmoothNLSSolution.hasSum_normSq_torusFourierCoeff`:
  **mass conservation** `∫_{[0,L]^d} |u(t)|² = ∫ |u(0)|²`, i.e. `∑ₙ |û(t,n)|² = ∑ₙ |c n|²`
  (TARGET L540, L818–L820);
* `IsSmoothNLSSolution.norm_torusFourierCoeff_sq_le`: `|û(t,n)|² ≤ ∑ₘ |c m|²`;
* `IsSmoothNLSSolution.eq_of_eq`: **uniqueness** of smooth solutions with the same data, by the
  `L²` energy estimate for the difference and Gronwall;
* `eq_of_mem_solvableEvent`: on `solvableEvent`, any two selections of solutions agree on
  `[0, T] × ℝ^d`.

The energy `E(t) = ∫ conj(e) e` of `e = u - w` has `E' = i(conj A - A) - iα(conj B - B)` with
`A = ∫ conj(e) Δe` real (Parseval) and `|B| ≤ 3 B₀² E` (`B₀` a bound for `|u|, |w|`).
-/

public section

noncomputable section

open MeasureTheory Complex Set Filter Topology
open scoped ContDiff

namespace WaveTurbulence.NLS

variable {d : ℕ}

/-! ### General identities -/

section General

theorem hasDerivWithinAt_integral_conj_mul_self {L T : ℝ} {w : ℝ → (Fin d → ℝ) → ℂ}
    (hw : ContDiffOn ℝ 1 (fun p : ℝ × (Fin d → ℝ) => w p.1 p.2) (Icc 0 T ×ˢ univ))
    {t : ℝ} (ht : t ∈ Icc 0 T) :
    HasDerivWithinAt
      (fun s => ∫ x in Icc (0 : Fin d → ℝ) (fun _ => L), (starRingEnd ℂ) (w s x) * w s x)
      (∫ x in Icc (0 : Fin d → ℝ) (fun _ => L),
        ((starRingEnd ℂ) (derivWithin (fun s => w s x) (Icc 0 T) t) * w t x +
          (starRingEnd ℂ) (w t x) * derivWithin (fun s => w s x) (Icc 0 T) t))
      (Icc 0 T) t := by
  rcases (ht.1.trans ht.2).lt_or_eq with hT | hT
  swap
  · subst hT
    obtain rfl : t = 0 := le_antisymm ht.2 ht.1
    rw [Icc_self]
    exact hasDerivWithinAt_singleton_self _ _ _
  have hconj : ContDiffOn ℝ 1 (fun p : ℝ × (Fin d → ℝ) => (starRingEnd ℂ) (w p.1 p.2))
      (Icc 0 T ×ˢ univ) :=
    (Complex.conjCLE.contDiff.comp_contDiffOn hw).congr fun p _ => rfl
  have h := hasDerivWithinAt_setIntegral_of_contDiffOn
    (F := fun s x => (starRingEnd ℂ) (w s x) * w s x)
    (isCompact_Icc (a := (0 : Fin d → ℝ)) (b := fun _ => L)) (hconj.mul hw) ht
  convert h using 1
  refine integral_congr_ae (Eventually.of_forall fun x => ?_)
  have hdiff : DifferentiableWithinAt ℝ (fun s => w s x) (Icc 0 T) t :=
    ((hw.differentiableOn one_ne_zero) (t, x) ⟨ht, mem_univ _⟩).comp t
      (differentiableWithinAt_id.prodMk (differentiableWithinAt_const x))
      (fun _ hr => Set.mk_mem_prod hr (mem_univ x))
  have hD := hdiff.hasDerivWithinAt
  exact ((hD.star.mul hD).derivWithin (uniqueDiffOn_Icc hT t ht)).symm

theorem integral_conj_mul_self (s : Set (Fin d → ℝ)) (e : (Fin d → ℝ) → ℂ) :
    ∫ x in s, (starRingEnd ℂ) (e x) * e x = ((∫ x in s, ‖e x‖ ^ 2 : ℝ) : ℂ) := by
  simp_rw [Complex.conj_mul', ← ofReal_pow]
  exact integral_complex_ofReal

/-- A continuous periodic function with `∫_{[0,L]^d} |e|² = 0` vanishes. -/
theorem eq_zero_of_integral_normSq_eq_zero {L : ℝ} (hL : 0 < L) {e : (Fin d → ℝ) → ℂ}
    (he : Continuous e) (hp : IsTorusPeriodic L e)
    (h : ∫ x in Icc (0 : Fin d → ℝ) (fun _ => L), ‖e x‖ ^ 2 = 0) : e = 0 := by
  have hs := hasSum_sq_torusFourierCoeff hL he hp
  rw [h, hasSum_zero_iff_of_nonneg (fun n => by positivity)] at hs
  refine eq_of_torusFourierCoeff_eq hL he continuous_const hp (IsTorusPeriodic.const 0)
    fun n => ?_
  have hn := congrFun hs n
  simp only [Pi.zero_apply, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, pow_eq_zero_iff,
    norm_eq_zero] at hn
  rw [hn]
  simp [torusFourierCoeff_eq_integral]

/-- `∫ conj(e) g` is real when `ĝ = r ê` with `r` real (e.g. `g = Δe`). -/
theorem im_integral_conj_mul_eq_zero {L : ℝ} (hL : 0 < L) {e g : (Fin d → ℝ) → ℂ}
    (he : Continuous e) (hg : Continuous g) (hpe : IsTorusPeriodic L e)
    (hpg : IsTorusPeriodic L g) {r : (Fin d → ℤ) → ℝ}
    (hr : ∀ n, torusFourierCoeff L g n = (r n : ℂ) * torusFourierCoeff L e n) :
    (∫ x in Icc (0 : Fin d → ℝ) (fun _ => L), (starRingEnd ℂ) (e x) * g x).im = 0 := by
  have h := Complex.hasSum_im (hasSum_inner_torusFourierCoeff hL he hg hpe hpg)
  have h0 : ∀ n, ((starRingEnd ℂ) (torusFourierCoeff L e n) * torusFourierCoeff L g n).im = 0 := by
    intro n
    rw [hr n, mul_left_comm, Complex.conj_mul', ← ofReal_pow, ← ofReal_mul, ofReal_im]
  simp_rw [h0] at h
  exact h.unique hasSum_zero

/-- The integrated energy derivative: with `D = -i (G - α N)`,
`∫ (conj D · e + conj e · D) = i (conj A - A) - iα (conj B - B)`, `A = ∫ conj e G`,
`B = ∫ conj e N`. -/
theorem integral_energy_deriv {L α : ℝ} {e G N : (Fin d → ℝ) → ℂ} (he : Continuous e)
    (hG : Continuous G) (hN : Continuous N) :
    ∫ x in Icc (0 : Fin d → ℝ) (fun _ => L),
        ((starRingEnd ℂ) (-I * (G x - α * N x)) * e x +
          (starRingEnd ℂ) (e x) * (-I * (G x - α * N x))) =
      I * ((starRingEnd ℂ) (∫ x in Icc (0 : Fin d → ℝ) (fun _ => L),
          (starRingEnd ℂ) (e x) * G x) -
          ∫ x in Icc (0 : Fin d → ℝ) (fun _ => L), (starRingEnd ℂ) (e x) * G x) -
        I * α * ((starRingEnd ℂ) (∫ x in Icc (0 : Fin d → ℝ) (fun _ => L),
          (starRingEnd ℂ) (e x) * N x) -
          ∫ x in Icc (0 : Fin d → ℝ) (fun _ => L), (starRingEnd ℂ) (e x) * N x) := by
  set s := Icc (0 : Fin d → ℝ) (fun _ => L)
  have hX : Continuous fun x => (starRingEnd ℂ) (e x) * G x := (continuous_conj.comp he).mul hG
  have hY : Continuous fun x => (starRingEnd ℂ) (e x) * N x := (continuous_conj.comp he).mul hN
  have hpt : ∀ x, (starRingEnd ℂ) (-I * (G x - α * N x)) * e x +
      (starRingEnd ℂ) (e x) * (-I * (G x - α * N x)) =
      (I * (starRingEnd ℂ) ((starRingEnd ℂ) (e x) * G x) - I * ((starRingEnd ℂ) (e x) * G x)) -
        (I * α * (starRingEnd ℂ) ((starRingEnd ℂ) (e x) * N x) -
          I * α * ((starRingEnd ℂ) (e x) * N x)) := by
    intro x
    simp only [map_mul, map_sub, map_neg, conj_I, conj_ofReal, Complex.conj_conj]
    ring
  simp_rw [hpt]
  have i1 : IntegrableOn (fun x => I * (starRingEnd ℂ) ((starRingEnd ℂ) (e x) * G x)) s :=
    (continuous_const.mul (continuous_conj.comp hX)).integrableOn_Icc
  have i2 : IntegrableOn (fun x => I * ((starRingEnd ℂ) (e x) * G x)) s :=
    (continuous_const.mul hX).integrableOn_Icc
  have i3 : IntegrableOn (fun x => I * α * (starRingEnd ℂ) ((starRingEnd ℂ) (e x) * N x)) s :=
    (continuous_const.mul (continuous_conj.comp hY)).integrableOn_Icc
  have i4 : IntegrableOn (fun x => I * α * ((starRingEnd ℂ) (e x) * N x)) s :=
    (continuous_const.mul hY).integrableOn_Icc
  rw [integral_sub (f := fun x => I * (starRingEnd ℂ) ((starRingEnd ℂ) (e x) * G x) -
      I * ((starRingEnd ℂ) (e x) * G x))
      (g := fun x => I * α * (starRingEnd ℂ) ((starRingEnd ℂ) (e x) * N x) -
      I * α * ((starRingEnd ℂ) (e x) * N x)) (i1.sub i2) (i3.sub i4),
    integral_sub i1 i2, integral_sub i3 i4,
    integral_const_mul, integral_const_mul, integral_const_mul, integral_const_mul, integral_conj,
    integral_conj]
  ring

/-- `| |z|²z - |w|²w | ≤ 3B² |z - w|` for `|z|, |w| ≤ B`. -/
theorem norm_cubic_sub_le {z w : ℂ} {B : ℝ} (hz : ‖z‖ ≤ B) (hw : ‖w‖ ≤ B) :
    ‖((‖z‖ ^ 2 : ℝ) : ℂ) * z - ((‖w‖ ^ 2 : ℝ) : ℂ) * w‖ ≤ 3 * B ^ 2 * ‖z - w‖ := by
  have hB : 0 ≤ B := (norm_nonneg _).trans hz
  have h1 : ((‖z‖ ^ 2 : ℝ) : ℂ) * z - ((‖w‖ ^ 2 : ℝ) : ℂ) * w =
      ((‖z‖ ^ 2 : ℝ) : ℂ) * (z - w) + ((‖z‖ ^ 2 - ‖w‖ ^ 2 : ℝ) : ℂ) * w := by
    push_cast
    ring
  have h2 : |‖z‖ ^ 2 - ‖w‖ ^ 2| ≤ 2 * B * ‖z - w‖ := by
    rw [sq_sub_sq, abs_mul]
    have h3 := abs_norm_sub_norm_le z w
    have h4 : |‖z‖ + ‖w‖| ≤ 2 * B := by
      rw [abs_of_nonneg (by positivity)]
      linarith
    calc |‖z‖ + ‖w‖| * |‖z‖ - ‖w‖| ≤ (2 * B) * ‖z - w‖ := by gcongr
      _ = 2 * B * ‖z - w‖ := by ring
  rw [h1]
  calc ‖((‖z‖ ^ 2 : ℝ) : ℂ) * (z - w) + ((‖z‖ ^ 2 - ‖w‖ ^ 2 : ℝ) : ℂ) * w‖
      ≤ ‖z‖ ^ 2 * ‖z - w‖ + |‖z‖ ^ 2 - ‖w‖ ^ 2| * ‖w‖ := by
        refine (norm_add_le _ _).trans ?_
        rw [norm_mul, norm_mul, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs,
          Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    _ ≤ B ^ 2 * ‖z - w‖ + (2 * B * ‖z - w‖) * B := by gcongr
    _ = 3 * B ^ 2 * ‖z - w‖ := by ring

/-- Gronwall: `f(0) = 0` and `‖f'‖ ≤ K ‖f‖` on `[0, T]` force `f = 0` on `[0, T]`. -/
theorem eq_zero_of_hasDerivWithinAt_Icc {f f' : ℝ → ℂ} {K T : ℝ}
    (hf : ∀ t ∈ Icc 0 T, HasDerivWithinAt f (f' t) (Icc 0 T) t) (h0 : f 0 = 0)
    (hb : ∀ t ∈ Icc 0 T, ‖f' t‖ ≤ K * ‖f t‖) : ∀ t ∈ Icc 0 T, f t = 0 :=
  eq_zero_of_abs_deriv_le_mul_abs_self_of_eq_zero_right (fun t ht => (hf t ht).continuousWithinAt)
    (fun t ht => (hf t (Ico_subset_Icc_self ht)).mono_of_mem_nhdsWithin
      (Icc_mem_nhdsGE_of_mem ht)) h0 (fun t ht => hb t (Ico_subset_Icc_self ht))

theorem _root_.WaveTurbulence.IsTorusPeriodic.normLaplacian {L : ℝ} {f : (Fin d → ℝ) → ℂ} (hp : IsTorusPeriodic L f) :
    IsTorusPeriodic L (WaveTurbulence.normLaplacian f) := by
  intro j x
  have h : ∀ i, WaveTurbulence.partialDeriv i (WaveTurbulence.partialDeriv i f) (x + Pi.single j L) =
      WaveTurbulence.partialDeriv i (WaveTurbulence.partialDeriv i f) x := fun i =>
    ((hp.partialDeriv i).partialDeriv i) j x
  simp only [WaveTurbulence.normLaplacian, h]

end General

/-! ### Smooth NLS solutions -/

section Solutions

variable {L α T : ℝ} {c : (Fin d → ℤ) → ℂ} {u : ℝ → (Fin d → ℝ) → ℂ}

theorem _root_.WaveTurbulence.IsSmoothNLSSolution.contDiffOn_one (hu : IsSmoothNLSSolution L α T c u) :
    ContDiffOn ℝ 1 (fun p : ℝ × (Fin d → ℝ) => u p.1 p.2) (Icc 0 T ×ˢ univ) :=
  hu.1.of_le (by exact_mod_cast le_top)

theorem _root_.WaveTurbulence.IsSmoothNLSSolution.differentiableWithinAt (hu : IsSmoothNLSSolution L α T c u)
    {t : ℝ} (ht : t ∈ Icc 0 T) (x : Fin d → ℝ) :
    DifferentiableWithinAt ℝ (fun s => u s x) (Icc 0 T) t :=
  ((hu.contDiffOn_one.differentiableOn one_ne_zero) (t, x) ⟨ht, mem_univ _⟩).comp t
    (differentiableWithinAt_id.prodMk (differentiableWithinAt_const x))
    (fun _ hr => Set.mk_mem_prod hr (mem_univ x))

theorem _root_.WaveTurbulence.IsSmoothNLSSolution.continuous_normLaplacian (hu : IsSmoothNLSSolution L α T c u)
    {t : ℝ} (ht : t ∈ Icc 0 T) : Continuous (normLaplacian (u t)) :=
  WaveTurbulence.NLS.continuous_normLaplacian ((hu.contDiff ht).of_le (by norm_cast))

theorem _root_.WaveTurbulence.IsSmoothNLSSolution.continuous_cubic (hu : IsSmoothNLSSolution L α T c u)
    {t : ℝ} (ht : t ∈ Icc 0 T) : Continuous fun x => ((‖u t x‖ ^ 2 : ℝ) : ℂ) * u t x := by
  have hc : Continuous (u t) := (hu.contDiff ht).continuous
  fun_prop

theorem _root_.WaveTurbulence.IsSmoothNLSSolution.torusFourierCoeff_normLaplacian (hL : 0 < L)
    (hu : IsSmoothNLSSolution L α T c u) {t : ℝ} (ht : t ∈ Icc 0 T) (n : Fin d → ℤ) :
    torusFourierCoeff L (normLaplacian (u t)) n =
      ((-(2 * Real.pi * ‖latticePoint L n‖ ^ 2) : ℝ) : ℂ) * torusFourierCoeff L (u t) n := by
  rw [torusFourierCoeff_normLaplacian' hL ((hu.contDiff ht).of_le (by norm_cast))
    (hu.isTorusPeriodic ht)]
  push_cast
  ring

theorem _root_.WaveTurbulence.IsSmoothNLSSolution.exists_bound (hu : IsSmoothNLSSolution L α T c u) :
    ∃ B, ∀ t ∈ Icc 0 T, ∀ x ∈ Icc (0 : Fin d → ℝ) (fun _ => L), ‖u t x‖ ≤ B := by
  obtain ⟨B, hB⟩ := (isCompact_Icc.prod (isCompact_Icc (a := (0 : Fin d → ℝ))
    (b := fun _ => L))).exists_bound_of_continuousOn
    (hu.1.continuousOn.mono (prod_mono subset_rfl (subset_univ _)))
  exact ⟨B, fun t ht x hx => hB (t, x) ⟨ht, hx⟩⟩

/-- The mass `∫_{[0,L]^d} |u(t)|²` has zero derivative on `[0, T]`. -/
theorem _root_.WaveTurbulence.IsSmoothNLSSolution.hasDerivWithinAt_mass (hL : 0 < L)
    (hu : IsSmoothNLSSolution L α T c u) {t : ℝ} (ht : t ∈ Icc 0 T) :
    HasDerivWithinAt
      (fun s => ∫ x in Icc (0 : Fin d → ℝ) (fun _ => L), (starRingEnd ℂ) (u s x) * u s x)
      0 (Icc 0 T) t := by
  have h := hasDerivWithinAt_integral_conj_mul_self (L := L) hu.contDiffOn_one ht
  simp_rw [hu.derivWithin_eq ht] at h
  rw [integral_energy_deriv (hu.contDiff ht).continuous (hu.continuous_normLaplacian ht)
    (hu.continuous_cubic ht)] at h
  have hA := im_integral_conj_mul_eq_zero hL (hu.contDiff ht).continuous
    (hu.continuous_normLaplacian ht) (hu.isTorusPeriodic ht) (hu.isTorusPeriodic ht).normLaplacian
    (hu.torusFourierCoeff_normLaplacian hL ht)
  have hB : (∫ x in Icc (0 : Fin d → ℝ) (fun _ => L),
      (starRingEnd ℂ) (u t x) * (((‖u t x‖ ^ 2 : ℝ) : ℂ) * u t x)).im = 0 := by
    have hpt : ∀ x, (starRingEnd ℂ) (u t x) * (((‖u t x‖ ^ 2 : ℝ) : ℂ) * u t x) =
        ((‖u t x‖ ^ 4 : ℝ) : ℂ) := by
      intro x
      rw [mul_left_comm, Complex.conj_mul']
      push_cast
      ring
    simp_rw [hpt]
    rw [integral_complex_ofReal, ofReal_im]
  rw [(Complex.conj_eq_iff_im).2 hA, (Complex.conj_eq_iff_im).2 hB] at h
  simpa using h

/-- **Mass conservation** (TARGET L540, L818–L820): `∫_{[0,L]^d} |u(t)|² = ∫ |u(0)|²`. -/
theorem _root_.WaveTurbulence.IsSmoothNLSSolution.integral_normSq_eq (hL : 0 < L)
    (hu : IsSmoothNLSSolution L α T c u) {t : ℝ} (ht : t ∈ Icc 0 T) :
    ∫ x in Icc (0 : Fin d → ℝ) (fun _ => L), ‖u t x‖ ^ 2 =
      ∫ x in Icc (0 : Fin d → ℝ) (fun _ => L), ‖u 0 x‖ ^ 2 := by
  set E : ℝ → ℂ := fun s =>
    ∫ x in Icc (0 : Fin d → ℝ) (fun _ => L), (starRingEnd ℂ) (u s x) * u s x
  have h := eq_zero_of_hasDerivWithinAt_Icc (f := fun s => E s - E 0) (f' := fun _ => 0) (K := 0)
    (fun s hs => (hu.hasDerivWithinAt_mass hL hs).sub_const (E 0)) (sub_self _)
    (fun s _ => by simp) t ht
  have h' : E t = E 0 := sub_eq_zero.1 h
  simp only [E, integral_conj_mul_self] at h'
  exact_mod_cast h'

/-- Mass conservation on the Fourier side: `∑ₙ |û(t, n)|² = ∑ₙ |c n|²`. -/
theorem _root_.WaveTurbulence.IsSmoothNLSSolution.hasSum_normSq_torusFourierCoeff (hL : 0 < L)
    (hu : IsSmoothNLSSolution L α T c u) {t : ℝ} (ht : t ∈ Icc 0 T) :
    HasSum (fun n => ‖torusFourierCoeff L (u t) n‖ ^ 2) (∑' n, ‖c n‖ ^ 2) := by
  have h0 : (0 : ℝ) ∈ Icc 0 T := ⟨le_rfl, ht.1.trans ht.2⟩
  have hs0 := hasSum_sq_torusFourierCoeff hL (hu.contDiff h0).continuous (hu.isTorusPeriodic h0)
  simp only [hu.2.2.1] at hs0
  rw [hs0.tsum_eq, ← hu.integral_normSq_eq hL ht]
  exact hasSum_sq_torusFourierCoeff hL (hu.contDiff ht).continuous (hu.isTorusPeriodic ht)

/-- The bound used at TARGET L818–L820: `|û(t, n)|² ≤ ∑ₘ |c m|²`. -/
theorem _root_.WaveTurbulence.IsSmoothNLSSolution.norm_torusFourierCoeff_sq_le (hL : 0 < L)
    (hu : IsSmoothNLSSolution L α T c u) {t : ℝ} (ht : t ∈ Icc 0 T) (n : Fin d → ℤ) :
    ‖torusFourierCoeff L (u t) n‖ ^ 2 ≤ ∑' m, ‖c m‖ ^ 2 := by
  have h := hu.hasSum_normSq_torusFourierCoeff hL ht
  rw [← h.tsum_eq]
  exact h.summable.le_tsum n (fun m _ => by positivity)

/-- **Uniqueness** of smooth solutions of (NLS) with the same data, by the `L²` energy estimate
and Gronwall. -/
theorem _root_.WaveTurbulence.IsSmoothNLSSolution.eq_of_eq (hL : 0 < L) {w : ℝ → (Fin d → ℝ) → ℂ}
    (hu : IsSmoothNLSSolution L α T c u) (hw : IsSmoothNLSSolution L α T c w) {t : ℝ}
    (ht : t ∈ Icc 0 T) : u t = w t := by
  have h0 : (0 : ℝ) ∈ Icc 0 T := ⟨le_rfl, ht.1.trans ht.2⟩
  set box := Icc (0 : Fin d → ℝ) (fun _ => L) with hbox
  have huw0 : u 0 = w 0 := eq_of_torusFourierCoeff_eq hL (hu.contDiff h0).continuous
    (hw.contDiff h0).continuous (hu.isTorusPeriodic h0) (hw.isTorusPeriodic h0)
    fun n => by rw [hu.2.2.1 n, hw.2.2.1 n]
  obtain ⟨Bu, hBu⟩ := hu.exists_bound
  obtain ⟨Bw, hBw⟩ := hw.exists_bound
  set B := max Bu Bw
  set e : ℝ → (Fin d → ℝ) → ℂ := fun s x => u s x - w s x with hedef
  have he : ContDiffOn ℝ 1 (fun p : ℝ × (Fin d → ℝ) => e p.1 p.2) (Icc 0 T ×ˢ univ) :=
    hu.contDiffOn_one.sub hw.contDiffOn_one
  set E : ℝ → ℂ := fun s => ∫ x in box, (starRingEnd ℂ) (e s x) * e s x with hEdef
  set G : ℝ → (Fin d → ℝ) → ℂ := fun s x => normLaplacian (u s) x - normLaplacian (w s) x
  set N : ℝ → (Fin d → ℝ) → ℂ := fun s x =>
    ((‖u s x‖ ^ 2 : ℝ) : ℂ) * u s x - ((‖w s x‖ ^ 2 : ℝ) : ℂ) * w s x
  set E' : ℝ → ℂ := fun s => -(I * α) * ((starRingEnd ℂ) (∫ x in box, (starRingEnd ℂ) (e s x) * N s x) -
    ∫ x in box, (starRingEnd ℂ) (e s x) * N s x)
  have hcont : ∀ s ∈ Icc 0 T, Continuous (e s) ∧ Continuous (G s) ∧ Continuous (N s) := by
    intro s hs
    exact ⟨(hu.contDiff hs).continuous.sub (hw.contDiff hs).continuous,
      (hu.continuous_normLaplacian hs).sub (hw.continuous_normLaplacian hs),
      (hu.continuous_cubic hs).sub (hw.continuous_cubic hs)⟩
  have hderiv : ∀ s ∈ Icc 0 T, HasDerivWithinAt E (E' s) (Icc 0 T) s := by
    intro s hs
    obtain ⟨hce, hcG, hcN⟩ := hcont s hs
    have h := hasDerivWithinAt_integral_conj_mul_self (L := L) he hs
    have hD : ∀ x, derivWithin (fun r => e r x) (Icc 0 T) s = -I * (G s x - α * N s x) := by
      intro x
      rw [hedef]
      simp only
      rw [derivWithin_fun_sub (hu.differentiableWithinAt hs x) (hw.differentiableWithinAt hs x),
        hu.derivWithin_eq hs, hw.derivWithin_eq hs]
      ring
    simp_rw [hD] at h
    rw [integral_energy_deriv hce hcG hcN] at h
    have hA := im_integral_conj_mul_eq_zero (L := L) hL hce hcG
      (fun j x => by simp only [e, hu.isTorusPeriodic hs j x, hw.isTorusPeriodic hs j x])
      (by intro j x; simp only [G, (hu.isTorusPeriodic hs).normLaplacian j x,
        (hw.isTorusPeriodic hs).normLaplacian j x])
      (r := fun n => -(2 * Real.pi * ‖latticePoint L n‖ ^ 2)) (fun n => by
        rw [torusFourierCoeff_sub (hu.continuous_normLaplacian hs).integrableOn_Icc
            (hw.continuous_normLaplacian hs).integrableOn_Icc,
          torusFourierCoeff_sub (hu.contDiff hs).continuous.integrableOn_Icc
            (hw.contDiff hs).continuous.integrableOn_Icc,
          hu.torusFourierCoeff_normLaplacian hL hs, hw.torusFourierCoeff_normLaplacian hL hs]
        ring)
    rw [(Complex.conj_eq_iff_im).2 hA] at h
    convert h using 1
    simp only [E']
    ring
  have hbound : ∀ s ∈ Icc 0 T, ‖E' s‖ ≤ (2 * |α| * (3 * B ^ 2)) * ‖E s‖ := by
    intro s hs
    obtain ⟨hce, -, hcN⟩ := hcont s hs
    set Bint := ∫ x in box, (starRingEnd ℂ) (e s x) * N s x
    have hEs : ‖E s‖ = ∫ x in box, ‖e s x‖ ^ 2 := by
      simp only [E, integral_conj_mul_self, Complex.norm_real, Real.norm_eq_abs]
      exact abs_of_nonneg (setIntegral_nonneg measurableSet_Icc fun x _ => by positivity)
    have hBint : ‖Bint‖ ≤ 3 * B ^ 2 * ∫ x in box, ‖e s x‖ ^ 2 := by
      calc ‖Bint‖ ≤ ∫ x in box, ‖(starRingEnd ℂ) (e s x) * N s x‖ :=
            norm_integral_le_integral_norm _
        _ ≤ ∫ x in box, 3 * B ^ 2 * ‖e s x‖ ^ 2 := by
            refine setIntegral_mono_on ((continuous_conj.comp hce).mul hcN).norm.integrableOn_Icc
              (continuous_const.mul (hce.norm.pow 2)).integrableOn_Icc measurableSet_Icc
              fun x hx => ?_
            rw [norm_mul, Complex.norm_conj]
            have hN := norm_cubic_sub_le ((hBu s hs x hx).trans (le_max_left Bu Bw))
              ((hBw s hs x hx).trans (le_max_right Bu Bw))
            calc ‖e s x‖ * ‖N s x‖ ≤ ‖e s x‖ * (3 * B ^ 2 * ‖e s x‖) := by
                  gcongr
              _ = 3 * B ^ 2 * ‖e s x‖ ^ 2 := by ring
        _ = 3 * B ^ 2 * ∫ x in box, ‖e s x‖ ^ 2 := integral_const_mul _ _
    calc ‖E' s‖ = |α| * ‖(starRingEnd ℂ) Bint - Bint‖ := by
          simp only [E', norm_mul, norm_neg, norm_I, one_mul, Complex.norm_real, Real.norm_eq_abs]
          rfl
      _ ≤ |α| * (‖Bint‖ + ‖Bint‖) := by
          gcongr
          exact (norm_sub_le _ _).trans (by rw [Complex.norm_conj])
      _ ≤ |α| * (2 * (3 * B ^ 2 * ∫ x in box, ‖e s x‖ ^ 2)) := by gcongr; linarith
      _ = (2 * |α| * (3 * B ^ 2)) * ‖E s‖ := by rw [hEs]; ring
  have hE0 : E 0 = 0 := by
    simp only [E, e, huw0, sub_self, map_zero, zero_mul, integral_zero]
  have hEt := eq_zero_of_hasDerivWithinAt_Icc hderiv hE0 hbound t ht
  simp only [E, integral_conj_mul_self, ofReal_eq_zero] at hEt
  have hz := eq_zero_of_integral_normSq_eq_zero hL (hcont t ht).1
    (fun j x => by simp only [e, hu.isTorusPeriodic ht j x, hw.isTorusPeriodic ht j x]) hEt
  funext x
  exact sub_eq_zero.1 (congrFun hz x)

end Solutions

end WaveTurbulence.NLS
