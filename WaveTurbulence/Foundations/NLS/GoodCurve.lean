/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.NLS.AkPersistence
public import WaveTurbulence.Foundations.NLS.SeriesDeriv

/-!
# Coefficient curves with uniformly rapidly decaying time derivatives

For `b : ℝ → ℤ^d → ℂ` (a curve of coefficient families) on `[0, T]`:

* `UnifRapid T b`: `|bₙ(t)| ≤ C_N (1 + ‖n‖)^{-N}` for all `N`, uniformly in `t ∈ [0, T]`;
* `GoodCurve T m b`: each `bₙ` is continuous on `[0, T]`, `b` is `UnifRapid`, and (for `m > 0`)
  `b` has a time derivative (within `[0, T]`, coordinatewise) which is `GoodCurve T (m - 1)`.

`GoodCurve` is closed under coordinatewise multiplication by polynomially bounded weights, sums,
conjugation and the cubic convolution `cubicCurve f g h` (`GoodCurve.cubicCurve`). These closure
properties give all time derivatives of a solution of the Fourier-side NLS system without explicit
Leibniz formulas (`NLS/SpaceTimeSeries`, `NLS/Backward`).
-/

public section

noncomputable section

open MeasureTheory Complex Set Filter Topology
open scoped ENNReal

namespace WaveTurbulence.NLS

variable {d : ℕ}

/-- Uniform rapid decay on `[0, T]`. -/
@[expose] def UnifRapid (T : ℝ) (b : ℝ → (Fin d → ℤ) → ℂ) : Prop :=
  ∀ N : ℕ, ∃ C, ∀ t ∈ Icc 0 T, ∀ n, ‖b t n‖ ≤ C * (1 + ‖n‖) ^ (-(N : ℤ))

/-- Coefficient curves whose first `m` time derivatives exist and decay rapidly, uniformly on
`[0, T]`. -/
@[expose] def GoodCurve (T : ℝ) : ℕ → (ℝ → (Fin d → ℤ) → ℂ) → Prop
  | 0, b => (∀ n, ContinuousOn (fun t => b t n) (Icc 0 T)) ∧ UnifRapid T b
  | m + 1, b => (∀ n, ContinuousOn (fun t => b t n) (Icc 0 T)) ∧ UnifRapid T b ∧
      ∃ b', GoodCurve T m b' ∧
        ∀ n, ∀ t ∈ Icc 0 T, HasDerivWithinAt (fun s => b s n) (b' t n) (Icc 0 T) t

/-- The cubic convolution of coefficient curves (no conjugation, no normalization). -/
@[expose] def cubicCurve (f g h : ℝ → (Fin d → ℤ) → ℂ) (t : ℝ) (n : Fin d → ℤ) : ℂ :=
  ∑' q : (Fin d → ℤ) × (Fin d → ℤ), f t q.1 * g t q.2 * h t (n - q.1 + q.2)

variable {T : ℝ}

/-! ### Uniform rapid decay -/

theorem UnifRapid.exists_majorant {b : ℝ → (Fin d → ℤ) → ℂ} (hb : UnifRapid T b) (k : ℕ) :
    ∃ C, 0 ≤ C ∧ ∀ t ∈ Icc 0 T, ∀ n,
      (1 + ‖n‖) ^ k * ‖b t n‖ ≤ C * ((1 + ‖n‖) ^ (d + 1))⁻¹ := by
  obtain ⟨C, hC⟩ := hb (k + (d + 1))
  refine ⟨max C 0, le_max_right _ _, fun t ht n => ?_⟩
  have hpos : 0 < 1 + ‖n‖ := by positivity
  have h := hC t ht n
  rw [zpow_neg, zpow_natCast, pow_add] at h
  calc (1 + ‖n‖) ^ k * ‖b t n‖ ≤ (1 + ‖n‖) ^ k * (C * ((1 + ‖n‖) ^ k * (1 + ‖n‖) ^ (d + 1))⁻¹) :=
        mul_le_mul_of_nonneg_left h (by positivity)
    _ = C * ((1 + ‖n‖) ^ (d + 1))⁻¹ := by field_simp
    _ ≤ max C 0 * ((1 + ‖n‖) ^ (d + 1))⁻¹ := by gcongr; exact le_max_left _ _

theorem UnifRapid.summable_weight {b : ℝ → (Fin d → ℤ) → ℂ} (hb : UnifRapid T b) (k : ℕ) :
    ∃ P : (Fin d → ℤ) → ℝ, Summable P ∧ ∀ t ∈ Icc 0 T, ∀ n, (1 + ‖n‖) ^ k * ‖b t n‖ ≤ P n := by
  obtain ⟨C, -, hC⟩ := hb.exists_majorant k
  exact ⟨_, summable_inv_one_add_norm_pow.mul_left C, hC⟩

theorem UnifRapid.of_norm_le {b c : ℝ → (Fin d → ℤ) → ℂ} (hb : UnifRapid T b) {A : ℝ} {k : ℕ}
    (h : ∀ t ∈ Icc 0 T, ∀ n, ‖c t n‖ ≤ A * (1 + ‖n‖) ^ k * ‖b t n‖) : UnifRapid T c := by
  intro N
  obtain ⟨C, hC⟩ := hb (N + k)
  refine ⟨|A| * C, fun t ht n => ?_⟩
  have hpos : 0 < 1 + ‖n‖ := by positivity
  have h1 := hC t ht n
  calc ‖c t n‖ ≤ A * (1 + ‖n‖) ^ k * ‖b t n‖ := h t ht n
    _ ≤ |A| * (1 + ‖n‖) ^ k * ‖b t n‖ := by gcongr; exact le_abs_self A
    _ ≤ |A| * (1 + ‖n‖) ^ k * (C * (1 + ‖n‖) ^ (-((N + k : ℕ) : ℤ))) := by gcongr
    _ = |A| * C * (1 + ‖n‖) ^ (-(N : ℤ)) := by
        rw [show (-((N + k : ℕ) : ℤ)) = -(N : ℤ) + -(k : ℤ) by push_cast; ring,
          zpow_add₀ hpos.ne', zpow_neg (1 + ‖n‖) (k : ℤ), zpow_natCast]
        field_simp

theorem UnifRapid.add {b c : ℝ → (Fin d → ℤ) → ℂ} (hb : UnifRapid T b) (hc : UnifRapid T c) :
    UnifRapid T (b + c) := by
  intro N
  obtain ⟨Cb, hCb⟩ := hb N
  obtain ⟨Cc, hCc⟩ := hc N
  exact ⟨Cb + Cc, fun t ht n => (norm_add_le _ _).trans
    (le_of_le_of_eq (add_le_add (hCb t ht n) (hCc t ht n)) (by ring))⟩

/-- The real tame weighted bound for the cubic convolution of curves. -/
theorem UnifRapid.cubicCurve {f g h : ℝ → (Fin d → ℤ) → ℂ} (hf : UnifRapid T f)
    (hg : UnifRapid T g) (hh : UnifRapid T h) : UnifRapid T (cubicCurve f g h) := by
  intro N
  -- `ℓ¹_N` bounds of the three factors, uniform in time
  have hw : ∀ {b : ℝ → (Fin d → ℤ) → ℂ}, UnifRapid T b → ∀ k : ℕ, ∃ B : ℝ≥0∞, B ≠ ∞ ∧
      ∀ t ∈ Icc 0 T, wnorm k (b t) ≤ B := by
    intro b hb k
    obtain ⟨C, hC0, hC⟩ := hb.exists_majorant k
    refine ⟨ENNReal.ofReal (C * ∑' n : Fin d → ℤ, ((1 + ‖n‖) ^ (d + 1))⁻¹), ENNReal.ofReal_ne_top,
      fun t ht => ?_⟩
    rw [← tsum_mul_left, ENNReal.ofReal_tsum_of_nonneg (fun n => by positivity)
      (summable_inv_one_add_norm_pow.mul_left C)]
    refine ENNReal.tsum_le_tsum fun n => ?_
    rw [wt, ← ofReal_norm, ← ENNReal.ofReal_pow (by positivity), ← ENNReal.ofReal_mul
      (by positivity)]
    exact ENNReal.ofReal_le_ofReal (hC t ht n)
  obtain ⟨Bf, hBf, hBf'⟩ := hw hf N
  obtain ⟨Bg, hBg, hBg'⟩ := hw hg N
  obtain ⟨Bh, hBh, hBh'⟩ := hw hh N
  obtain ⟨Bf0, hBf0, hBf0'⟩ := hw hf 0
  obtain ⟨Bg0, hBg0, hBg0'⟩ := hw hg 0
  obtain ⟨Bh0, hBh0, hBh0'⟩ := hw hh 0
  set B : ℝ≥0∞ := 3 ^ N * (Bf * Bg0 * Bh0 + Bf0 * Bg * Bh0 + Bf0 * Bg0 * Bh) with hBdef
  have hB : B ≠ ∞ := by
    refine ENNReal.mul_ne_top (ENNReal.pow_ne_top (by norm_num)) ?_
    exact ENNReal.add_ne_top.2 ⟨ENNReal.add_ne_top.2 ⟨ENNReal.mul_ne_top (ENNReal.mul_ne_top hBf
      hBg0) hBh0, ENNReal.mul_ne_top (ENNReal.mul_ne_top hBf0 hBg) hBh0⟩,
      ENNReal.mul_ne_top (ENNReal.mul_ne_top hBf0 hBg0) hBh⟩
  refine ⟨B.toReal, fun t ht n => ?_⟩
  have hpos : 0 < (1 + ‖n‖) ^ N := by positivity
  rw [zpow_neg, zpow_natCast, ← div_eq_mul_inv, le_div_iff₀ hpos, mul_comm]
  have hE : wt N n * ‖WaveTurbulence.NLS.cubicCurve f g h t n‖ₑ ≤ B := by
    calc wt N n * ‖WaveTurbulence.NLS.cubicCurve f g h t n‖ₑ ≤ wt N n * tripleAbs (f t) (g t) (h t) n := by
          gcongr
          refine enorm_tsum_le_tsum_enorm.trans (ENNReal.tsum_le_tsum fun q => ?_)
          simp only [enorm_mul, le_refl]
      _ ≤ ∑' m, wt N m * tripleAbs (f t) (g t) (h t) m :=
          ENNReal.le_tsum (f := fun m => wt N m * tripleAbs (f t) (g t) (h t) m) n
      _ ≤ 3 ^ N * (wnorm N (f t) * wnorm 0 (g t) * wnorm 0 (h t) +
            wnorm 0 (f t) * wnorm N (g t) * wnorm 0 (h t) +
            wnorm 0 (f t) * wnorm 0 (g t) * wnorm N (h t)) := tsum_wt_mul_tripleAbs_le_tame _ _ _ _
      _ ≤ B := by
          rw [hBdef]
          gcongr
          · exact hBf' t ht
          · exact hBg0' t ht
          · exact hBh0' t ht
          · exact hBf0' t ht
          · exact hBg' t ht
          · exact hBh0' t ht
          · exact hBf0' t ht
          · exact hBg0' t ht
          · exact hBh' t ht
  have h1 := ENNReal.toReal_mono hB hE
  rwa [ENNReal.toReal_mul, toReal_enorm, wt, ENNReal.toReal_pow,
    ENNReal.toReal_ofReal (by positivity)] at h1

/-! ### Closure properties of `GoodCurve` -/

theorem GoodCurve.continuousOn {m : ℕ} {b : ℝ → (Fin d → ℤ) → ℂ} (hb : GoodCurve T m b)
    (n : Fin d → ℤ) : ContinuousOn (fun t => b t n) (Icc 0 T) := by
  cases m with
  | zero => exact hb.1 n
  | succ m => exact hb.1 n

theorem GoodCurve.unifRapid {m : ℕ} {b : ℝ → (Fin d → ℤ) → ℂ} (hb : GoodCurve T m b) :
    UnifRapid T b := by
  cases m with
  | zero => exact hb.2
  | succ m => exact hb.2.1

theorem GoodCurve.mono {m : ℕ} {b : ℝ → (Fin d → ℤ) → ℂ} (hb : GoodCurve T (m + 1) b) :
    GoodCurve T m b := by
  induction m generalizing b with
  | zero => exact ⟨hb.1, hb.2.1⟩
  | succ m ih =>
    obtain ⟨hc, hr, b', hb', hd⟩ := hb
    exact ⟨hc, hr, b', ih hb', hd⟩

theorem GoodCurve.of_le {m k : ℕ} (hmk : k ≤ m) {b : ℝ → (Fin d → ℤ) → ℂ}
    (hb : GoodCurve T m b) : GoodCurve T k b := by
  induction m with
  | zero => obtain rfl : k = 0 := by omega
            exact hb
  | succ m ih =>
    rcases Nat.lt_or_ge k (m + 1) with h | h
    · exact ih (by omega) hb.mono
    · obtain rfl : k = m + 1 := by omega
      exact hb

/-- Multiplication by a polynomially bounded weight. -/
theorem GoodCurve.weight {m : ℕ} {b : ℝ → (Fin d → ℤ) → ℂ} (hb : GoodCurve T m b)
    (p : (Fin d → ℤ) → ℂ) {A : ℝ} {k : ℕ} (hp : ∀ n, ‖p n‖ ≤ A * (1 + ‖n‖) ^ k) :
    GoodCurve T m (fun t n => p n * b t n) := by
  have hr : ∀ {c : ℝ → (Fin d → ℤ) → ℂ}, UnifRapid T c → UnifRapid T (fun t n => p n * c t n) :=
    fun hc => hc.of_norm_le (A := A) (k := k) fun t _ n => by
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_right (hp n) (norm_nonneg _)
  induction m generalizing b with
  | zero => exact ⟨fun n => continuousOn_const.mul (hb.1 n), hr hb.2⟩
  | succ m ih =>
    obtain ⟨hc, hrb, b', hb', hd⟩ := hb
    exact ⟨fun n => continuousOn_const.mul (hc n), hr hrb, fun t n => p n * b' t n, ih hb',
      fun n t ht => (hd n t ht).const_mul (p n)⟩

theorem GoodCurve.const_mul {m : ℕ} {b : ℝ → (Fin d → ℤ) → ℂ} (hb : GoodCurve T m b) (z : ℂ) :
    GoodCurve T m (fun t n => z * b t n) :=
  hb.weight (fun _ => z) (A := ‖z‖) (k := 0) fun n => by simp

theorem GoodCurve.add {m : ℕ} {b c : ℝ → (Fin d → ℤ) → ℂ} (hb : GoodCurve T m b)
    (hc : GoodCurve T m c) : GoodCurve T m (fun t n => b t n + c t n) := by
  induction m generalizing b c with
  | zero => exact ⟨fun n => (hb.1 n).add (hc.1 n), hb.2.add hc.2⟩
  | succ m ih =>
    obtain ⟨hcb, hrb, b', hb', hdb⟩ := hb
    obtain ⟨hcc, hrc, c', hc', hdc⟩ := hc
    exact ⟨fun n => (hcb n).add (hcc n), hrb.add hrc, fun t n => b' t n + c' t n, ih hb' hc',
      fun n t ht => (hdb n t ht).add (hdc n t ht)⟩

theorem GoodCurve.conj {m : ℕ} {b : ℝ → (Fin d → ℤ) → ℂ} (hb : GoodCurve T m b) :
    GoodCurve T m (fun t n => (starRingEnd ℂ) (b t n)) := by
  have hr : ∀ {c : ℝ → (Fin d → ℤ) → ℂ}, UnifRapid T c →
      UnifRapid T (fun t n => (starRingEnd ℂ) (c t n)) :=
    fun hc => hc.of_norm_le (A := 1) (k := 0) fun t _ n => by simp
  induction m generalizing b with
  | zero => exact ⟨fun n => continuous_conj.comp_continuousOn (hb.1 n), hr hb.2⟩
  | succ m ih =>
    obtain ⟨hc, hrb, b', hb', hd⟩ := hb
    exact ⟨fun n => continuous_conj.comp_continuousOn (hc n), hr hrb,
      fun t n => (starRingEnd ℂ) (b' t n), ih hb', fun n t ht => (hd n t ht).star⟩

/-! ### The cubic convolution of good curves -/

theorem UnifRapid.exists_bound {b : ℝ → (Fin d → ℤ) → ℂ} (hb : UnifRapid T b) :
    ∃ C, 0 ≤ C ∧ ∀ t ∈ Icc 0 T, ∀ n, ‖b t n‖ ≤ C * ((1 + ‖n‖) ^ (d + 1))⁻¹ := by
  obtain ⟨C, hC0, hC⟩ := hb.exists_majorant 0
  exact ⟨C, hC0, fun t ht n => by simpa using hC t ht n⟩

theorem summable_cubic_bound {Cf Cg Ch : ℝ} (hf : 0 ≤ Cf) (hg : 0 ≤ Cg) :
    Summable fun q : (Fin d → ℤ) × (Fin d → ℤ) =>
      Cf * ((1 + ‖q.1‖) ^ (d + 1))⁻¹ * (Cg * ((1 + ‖q.2‖) ^ (d + 1))⁻¹) * Ch := by
  have h := summable_inv_one_add_norm_pow (d := d)
  exact ((h.mul_left Cf).mul_of_nonneg (h.mul_left Cg) (fun _ => by positivity)
    (fun _ => by positivity)).mul_right Ch

theorem norm_cubic_term_le {f g h : ℝ → (Fin d → ℤ) → ℂ} {Cf Cg Ch : ℝ} (hCf : 0 ≤ Cf)
    (hCg : 0 ≤ Cg) (hCh : 0 ≤ Ch)
    (hf : ∀ t ∈ Icc 0 T, ∀ n, ‖f t n‖ ≤ Cf * ((1 + ‖n‖) ^ (d + 1))⁻¹)
    (hg : ∀ t ∈ Icc 0 T, ∀ n, ‖g t n‖ ≤ Cg * ((1 + ‖n‖) ^ (d + 1))⁻¹)
    (hh : ∀ t ∈ Icc 0 T, ∀ n, ‖h t n‖ ≤ Ch * ((1 + ‖n‖) ^ (d + 1))⁻¹)
    {t : ℝ} (ht : t ∈ Icc 0 T) (n : Fin d → ℤ) (q : (Fin d → ℤ) × (Fin d → ℤ)) :
    ‖f t q.1 * g t q.2 * h t (n - q.1 + q.2)‖ ≤
      Cf * ((1 + ‖q.1‖) ^ (d + 1))⁻¹ * (Cg * ((1 + ‖q.2‖) ^ (d + 1))⁻¹) * Ch := by
  rw [norm_mul, norm_mul]
  exact mul_le_mul (mul_le_mul (hf t ht _) (hg t ht _) (norm_nonneg _) (by positivity))
    ((hh t ht _).trans (mul_le_of_le_one_right hCh (inv_one_add_norm_pow_le_one _)))
    (norm_nonneg _) (by positivity)

theorem continuousOn_cubicCurve {f g h : ℝ → (Fin d → ℤ) → ℂ}
    (hcf : ∀ n, ContinuousOn (fun t => f t n) (Icc 0 T))
    (hcg : ∀ n, ContinuousOn (fun t => g t n) (Icc 0 T))
    (hch : ∀ n, ContinuousOn (fun t => h t n) (Icc 0 T))
    (hf : UnifRapid T f) (hg : UnifRapid T g) (hh : UnifRapid T h) (n : Fin d → ℤ) :
    ContinuousOn (fun t => cubicCurve f g h t n) (Icc 0 T) := by
  obtain ⟨Cf, hCf, hCf'⟩ := hf.exists_bound
  obtain ⟨Cg, hCg, hCg'⟩ := hg.exists_bound
  obtain ⟨Ch, hCh, hCh'⟩ := hh.exists_bound
  exact continuousOn_tsum (fun q => ((hcf q.1).mul (hcg q.2)).mul (hch _))
    (summable_cubic_bound hCf hCg) (fun q t ht => norm_cubic_term_le hCf hCg hCh hCf' hCg' hCh' ht n q)

theorem summable_cubicCurve_terms {f g h : ℝ → (Fin d → ℤ) → ℂ} (hf : UnifRapid T f)
    (hg : UnifRapid T g) (hh : UnifRapid T h) {t : ℝ} (ht : t ∈ Icc 0 T) (n : Fin d → ℤ) :
    Summable fun q : (Fin d → ℤ) × (Fin d → ℤ) => f t q.1 * g t q.2 * h t (n - q.1 + q.2) := by
  obtain ⟨Cf, hCf, hCf'⟩ := hf.exists_bound
  obtain ⟨Cg, hCg, hCg'⟩ := hg.exists_bound
  obtain ⟨Ch, hCh, hCh'⟩ := hh.exists_bound
  exact Summable.of_norm_bounded (summable_cubic_bound hCf hCg)
    (fun q => norm_cubic_term_le hCf hCg hCh hCf' hCg' hCh' ht n q)

/-- The time derivative of the cubic convolution (product rule, termwise within `[0, T]`). -/
theorem hasDerivWithinAt_cubicCurve {f g h f' g' h' : ℝ → (Fin d → ℤ) → ℂ}
    (hf : UnifRapid T f) (hg : UnifRapid T g) (hh : UnifRapid T h)
    (hf' : UnifRapid T f') (hg' : UnifRapid T g') (hh' : UnifRapid T h')
    (hdf : ∀ n, ∀ t ∈ Icc 0 T, HasDerivWithinAt (fun s => f s n) (f' t n) (Icc 0 T) t)
    (hdg : ∀ n, ∀ t ∈ Icc 0 T, HasDerivWithinAt (fun s => g s n) (g' t n) (Icc 0 T) t)
    (hdh : ∀ n, ∀ t ∈ Icc 0 T, HasDerivWithinAt (fun s => h s n) (h' t n) (Icc 0 T) t)
    {t : ℝ} (ht : t ∈ Icc 0 T) (n : Fin d → ℤ) :
    HasDerivWithinAt (fun s => cubicCurve f g h s n)
      (cubicCurve f' g h t n + cubicCurve f g' h t n + cubicCurve f g h' t n) (Icc 0 T) t := by
  obtain ⟨Cf, hCf, hCf'⟩ := hf.exists_bound
  obtain ⟨Cg, hCg, hCg'⟩ := hg.exists_bound
  obtain ⟨Ch, hCh, hCh'⟩ := hh.exists_bound
  obtain ⟨Df, hDf, hDf'⟩ := hf'.exists_bound
  obtain ⟨Dg, hDg, hDg'⟩ := hg'.exists_bound
  obtain ⟨Dh, hDh, hDh'⟩ := hh'.exists_bound
  set term : (Fin d → ℤ) × (Fin d → ℤ) → ℝ → ℂ := fun q s =>
    f' s q.1 * g s q.2 * h s (n - q.1 + q.2) + f s q.1 * g' s q.2 * h s (n - q.1 + q.2) +
      f s q.1 * g s q.2 * h' s (n - q.1 + q.2) with hterm
  have hD := hasFDerivWithinAt_tsum_of_convex (convex_Icc 0 T)
    (T := fun q s => f s q.1 * g s q.2 * h s (n - q.1 + q.2))
    (T' := fun q s => ContinuousLinearMap.toSpanSingleton ℝ (term q s))
    (u := fun q => Df * ((1 + ‖q.1‖) ^ (d + 1))⁻¹ * (Cg * ((1 + ‖q.2‖) ^ (d + 1))⁻¹) * Ch +
      Cf * ((1 + ‖q.1‖) ^ (d + 1))⁻¹ * (Dg * ((1 + ‖q.2‖) ^ (d + 1))⁻¹) * Ch +
      Cf * ((1 + ‖q.1‖) ^ (d + 1))⁻¹ * (Cg * ((1 + ‖q.2‖) ^ (d + 1))⁻¹) * Dh)
    (((summable_cubic_bound hDf hCg).add (summable_cubic_bound hCf hDg)).add
      (summable_cubic_bound hCf hCg))
    (fun q s hs => ?_) (fun q s hs => ?_)
    (fun s hs => summable_cubicCurve_terms hf hg hh hs n) ht
    (D := ContinuousLinearMap.toSpanSingleton ℝ
      (cubicCurve f' g h t n + cubicCurve f g' h t n + cubicCurve f g h' t n)) (fun v => ?_)
  · exact hD
  · have h1 := ((hdf q.1 s hs).mul (hdg q.2 s hs)).mul (hdh (n - q.1 + q.2) s hs)
    have h2 : HasDerivWithinAt (fun s => f s q.1 * g s q.2 * h s (n - q.1 + q.2)) (term q s)
        (Icc 0 T) s := h1.congr_deriv (by simp only [hterm, Pi.mul_apply]; ring)
    exact h2
  · rw [ContinuousLinearMap.norm_toSpanSingleton]
    simp only [hterm]
    refine (norm_add_le _ _).trans (add_le_add ((norm_add_le _ _).trans (add_le_add ?_ ?_)) ?_)
    · exact norm_cubic_term_le hDf hCg hCh hDf' hCg' hCh' hs n q
    · exact norm_cubic_term_le hCf hDg hCh hCf' hDg' hCh' hs n q
    · exact norm_cubic_term_le hCf hCg hDh hCf' hCg' hDh' hs n q
  · simp only [ContinuousLinearMap.toSpanSingleton_apply, hterm, smul_add]
    exact ((((summable_cubicCurve_terms hf' hg hh ht n).hasSum.const_smul v).add
      ((summable_cubicCurve_terms hf hg' hh ht n).hasSum.const_smul v)).add
      ((summable_cubicCurve_terms hf hg hh' ht n).hasSum.const_smul v))

/-- `GoodCurve` is closed under the cubic convolution. -/
theorem GoodCurve.cubicCurve {m : ℕ} {f g h : ℝ → (Fin d → ℤ) → ℂ} (hf : GoodCurve T m f)
    (hg : GoodCurve T m g) (hh : GoodCurve T m h) :
    GoodCurve T m (WaveTurbulence.NLS.cubicCurve f g h) := by
  induction m generalizing f g h with
  | zero =>
    exact ⟨continuousOn_cubicCurve hf.1 hg.1 hh.1 hf.2 hg.2 hh.2, hf.2.cubicCurve hg.2 hh.2⟩
  | succ m ih =>
    obtain ⟨hcf, hrf, f', hf', hdf⟩ := hf
    obtain ⟨hcg, hrg, g', hg', hdg⟩ := hg
    obtain ⟨hch, hrh, h', hh', hdh⟩ := hh
    have hfm : GoodCurve T m f := GoodCurve.mono (show GoodCurve T (m + 1) f from
      ⟨hcf, hrf, f', hf', hdf⟩)
    have hgm : GoodCurve T m g := GoodCurve.mono (show GoodCurve T (m + 1) g from
      ⟨hcg, hrg, g', hg', hdg⟩)
    have hhm : GoodCurve T m h := GoodCurve.mono (show GoodCurve T (m + 1) h from
      ⟨hch, hrh, h', hh', hdh⟩)
    refine ⟨continuousOn_cubicCurve hcf hcg hch hrf hrg hrh, hrf.cubicCurve hrg hrh,
      fun t n => WaveTurbulence.NLS.cubicCurve f' g h t n + WaveTurbulence.NLS.cubicCurve f g' h t n +
        WaveTurbulence.NLS.cubicCurve f g h' t n,
      ((ih hf' hgm hhm).add (ih hfm hg' hhm)).add (ih hfm hgm hh'),
      fun n t ht => hasDerivWithinAt_cubicCurve hrf hrg hrh hf'.unifRapid hg'.unifRapid
        hh'.unifRapid hdf hdg hdh ht n⟩

end WaveTurbulence.NLS
