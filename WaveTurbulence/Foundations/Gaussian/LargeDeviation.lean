/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Gaussian.Hypercontractivity

/-!
# Large deviation bounds for Gaussian polynomials

Consequences of Gaussian hypercontractivity (DH21 Lemma A.3) in the form used by DH21
Props 12.1–12.2 (L2707–L2756), DH21-2 Prop 4.8 and the target's Prop `fixedpoint`: `p`-th moment
bounds followed by Chebyshev's inequality.

## Main results

* `measureReal_le_norm_le_integral_rpow_div`: Chebyshev's inequality with a `q`-th moment.
* `integral_norm_rpow_multiGauss_le_of_le`: `𝔼|X|^q ≤ (q-1)^{nq/2} σ^q` when `𝔼|X|² ≤ σ²`.
* `measureReal_multiGauss_le`: `P(|X| ≥ R) ≤ (q-1)^{nq/2} σ^q / R^q`.
* `measureReal_multiGauss_ge_le_exp`: the exponential tail
  `P(|X| ≥ λσ) ≤ exp(n/2 - (n/(2e)) λ^{2/n})` for `n ≥ 1`, `λ > 0`.
* `moment_le_of_tendsto_ae`: the hypercontractive moment bound passes to almost-sure limits along
  which second moments converge (used for the infinite sums `∑_{k ∈ ℤ_L^d}` of DH21).
-/

public section

open MeasureTheory ProbabilityTheory Filter Finset
open scoped Topology

namespace WaveTurbulence

open Gaussian

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]

omit [IsProbabilityMeasure P] in
/-- **Chebyshev's inequality** with a `q`-th moment: `P(|Y| ≥ R) ≤ 𝔼|Y|^q / R^q`. -/
theorem measureReal_le_norm_le_integral_rpow_div {Y : Ω → ℂ} {q : ℝ} (hq : 0 < q)
    (hint : Integrable (fun ω => ‖Y ω‖ ^ q) P) {R : ℝ} (hR : 0 < R) :
    P.real {ω | R ≤ ‖Y ω‖} ≤ (∫ ω, ‖Y ω‖ ^ q ∂P) / R ^ q := by
  have hRq : 0 < R ^ q := Real.rpow_pos_of_pos hR q
  have hset : {ω | R ≤ ‖Y ω‖} = {ω | R ^ q ≤ ‖Y ω‖ ^ q} := by
    ext ω
    exact (Real.rpow_le_rpow_iff hR.le (norm_nonneg _) hq).symm
  rw [hset, le_div_iff₀ hRq, mul_comm]
  exact mul_meas_ge_le_integral_of_nonneg
    (Eventually.of_forall fun ω => Real.rpow_nonneg (norm_nonneg _) q) hint _

variable {ι : Type*} {η : ι → Ω → ℂ}

/-- Hypercontractive moment bound under an upper bound `𝔼|X|² ≤ σ²` on the variance. -/
theorem integral_norm_rpow_multiGauss_le_of_le (hind : iIndepFun η P)
    (hlaw : ∀ i, HasLaw (η i) stdComplexGaussian P) {n : ℕ} (ζ : Fin n → Bool)
    (s : Finset (Fin n → ι)) (a : (Fin n → ι) → ℂ) {q : ℝ} (hq : 2 ≤ q) {σ : ℝ} (hσ : 0 ≤ σ)
    (h2 : ∫ ω, ‖multiGauss ζ s a (fun i => η i ω)‖ ^ 2 ∂P ≤ σ ^ 2) :
    ∫ ω, ‖multiGauss ζ s a (fun i => η i ω)‖ ^ q ∂P ≤ (q - 1) ^ ((n : ℝ) * q / 2) * σ ^ q := by
  refine (integral_norm_rpow_multiGauss_le hind hlaw ζ s a hq).trans ?_
  have hC : 0 ≤ (q - 1) ^ ((n : ℝ) * q / 2) := Real.rpow_nonneg (by linarith) _
  refine mul_le_mul_of_nonneg_left ?_ hC
  calc (∫ ω, ‖multiGauss ζ s a (fun i => η i ω)‖ ^ 2 ∂P) ^ (q / 2) ≤ (σ ^ 2) ^ (q / 2) :=
        Real.rpow_le_rpow (integral_nonneg fun _ => sq_nonneg _) h2 (by linarith)
    _ = σ ^ q := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul hσ]
        congr 1
        push_cast
        ring

/-- **Large deviation bound** (Chebyshev form): if `𝔼|X|² ≤ σ²` then
`P(|X| ≥ R) ≤ (q-1)^{nq/2} σ^q / R^q` for every `q ≥ 2` and `R > 0`. -/
theorem measureReal_multiGauss_le (hind : iIndepFun η P)
    (hlaw : ∀ i, HasLaw (η i) stdComplexGaussian P) {n : ℕ} (ζ : Fin n → Bool)
    (s : Finset (Fin n → ι)) (a : (Fin n → ι) → ℂ) {q : ℝ} (hq : 2 ≤ q) {σ : ℝ} (hσ : 0 ≤ σ)
    (h2 : ∫ ω, ‖multiGauss ζ s a (fun i => η i ω)‖ ^ 2 ∂P ≤ σ ^ 2) {R : ℝ} (hR : 0 < R) :
    P.real {ω | R ≤ ‖multiGauss ζ s a (fun i => η i ω)‖} ≤
      (q - 1) ^ ((n : ℝ) * q / 2) * σ ^ q / R ^ q := by
  refine (measureReal_le_norm_le_integral_rpow_div (by linarith)
    (integrable_norm_rpow_multiGauss hind hlaw ζ s a hq) hR).trans ?_
  exact div_le_div_of_nonneg_right
    (integral_norm_rpow_multiGauss_le_of_le hind hlaw ζ s a hq hσ h2)
    (Real.rpow_nonneg hR.le q)

/-- **Exponential large deviation bound** (DH21, consequence of Lemma A.3): if `n ≥ 1` and
`𝔼|X|² ≤ σ²` with `σ > 0`, then for every `λ > 0`,
`P(|X| ≥ λ σ) ≤ exp(n/2 - (n/(2e)) λ^{2/n})`. -/
theorem measureReal_multiGauss_ge_le_exp (hind : iIndepFun η P)
    (hlaw : ∀ i, HasLaw (η i) stdComplexGaussian P) {n : ℕ} (hn : 1 ≤ n) (ζ : Fin n → Bool)
    (s : Finset (Fin n → ι)) (a : (Fin n → ι) → ℂ) {σ : ℝ} (hσ : 0 < σ)
    (h2 : ∫ ω, ‖multiGauss ζ s a (fun i => η i ω)‖ ^ 2 ∂P ≤ σ ^ 2) {l : ℝ} (hl : 0 < l) :
    P.real {ω | l * σ ≤ ‖multiGauss ζ s a (fun i => η i ω)‖} ≤
      Real.exp (n / 2 - n / (2 * Real.exp 1) * l ^ (2 / (n : ℝ))) := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have he : 0 < Real.exp 1 := Real.exp_pos 1
  set t : ℝ := l ^ (2 / (n : ℝ)) with ht
  have ht0 : 0 < t := Real.rpow_pos_of_pos hl _
  rcases le_or_gt t (Real.exp 1) with hsmall | hbig
  · -- the bound is at least `1`
    refine measureReal_le_one.trans ?_
    rw [Real.one_le_exp_iff]
    have : n / (2 * Real.exp 1) * t ≤ n / 2 := by
      rw [div_mul_eq_mul_div, div_le_div_iff₀ (by positivity) (by positivity)]
      nlinarith
    linarith
  · -- choose `q - 1 = t / e`
    set q : ℝ := 1 + t / Real.exp 1 with hqdef
    have hq : 2 ≤ q := by
      rw [hqdef]
      have : 1 ≤ t / Real.exp 1 := by rw [le_div_iff₀ he]; linarith
      linarith
    have hlσ : 0 < l * σ := mul_pos hl hσ
    have hT := measureReal_multiGauss_le hind hlaw ζ s a hq hσ.le h2 hlσ
    have hq1 : q - 1 = t / Real.exp 1 := by rw [hqdef]; ring
    have hbase : (q - 1) ^ ((n : ℝ) / 2) = l * Real.exp (-(n : ℝ) / 2) := by
      rw [hq1, Real.div_rpow ht0.le he.le, ht, ← Real.rpow_mul hl.le,
        show 2 / (n : ℝ) * (n / 2) = 1 by field_simp, Real.rpow_one, ← Real.exp_mul,
        div_eq_mul_inv, ← Real.exp_neg]
      congr 2
      ring
    have hpow : (q - 1) ^ ((n : ℝ) * q / 2) = l ^ q * Real.exp (-(n : ℝ) * q / 2) := by
      rw [show (n : ℝ) * q / 2 = (n : ℝ) / 2 * q by ring,
        Real.rpow_mul (by rw [hq1]; positivity), hbase,
        Real.mul_rpow hl.le (Real.exp_pos _).le, ← Real.exp_mul]
      congr 2
      ring
    have heq : (q - 1) ^ ((n : ℝ) * q / 2) * σ ^ q / (l * σ) ^ q =
        Real.exp (-(n : ℝ) * q / 2) := by
      rw [hpow, Real.mul_rpow hl.le hσ.le]
      have hlq : 0 < l ^ q := Real.rpow_pos_of_pos hl q
      have hσq : 0 < σ ^ q := Real.rpow_pos_of_pos hσ q
      field_simp
    have hexp : -(n : ℝ) * q / 2 ≤ n / 2 - n / (2 * Real.exp 1) * t := by
      have : (n : ℝ) / (2 * Real.exp 1) * t = (n : ℝ) / 2 * (t / Real.exp 1) := by
        field_simp
      rw [this, hqdef]
      nlinarith
    calc P.real {ω | l * σ ≤ ‖multiGauss ζ s a (fun i => η i ω)‖}
        ≤ (q - 1) ^ ((n : ℝ) * q / 2) * σ ^ q / (l * σ) ^ q := hT
      _ = Real.exp (-(n : ℝ) * q / 2) := heq
      _ ≤ _ := Real.exp_le_exp.2 hexp

/-- **The moment bound passes to almost-sure limits.** If `X m → Y` almost surely, the second
moments converge, and each `X m` has `|X m|^q` integrable and satisfies
`𝔼|X m|^q ≤ C (𝔼|X m|²)^{q/2}`, then `|Y|^q` is
integrable and `𝔼|Y|^q ≤ C (𝔼|Y|²)^{q/2}`. This applies the hypercontractive bound to the
infinite (`L²`-convergent) sums of DH21 via their finite partial sums. -/
theorem moment_le_of_tendsto_ae {X : ℕ → Ω → ℂ} {Y : Ω → ℂ}
    (hX : ∀ m, AEStronglyMeasurable (X m) P) (hY : AEStronglyMeasurable Y P)
    (hlim : ∀ᵐ ω ∂P, Tendsto (fun m => X m ω) atTop (𝓝 (Y ω)))
    (h2 : Tendsto (fun m => ∫ ω, ‖X m ω‖ ^ 2 ∂P) atTop (𝓝 (∫ ω, ‖Y ω‖ ^ 2 ∂P)))
    {q C : ℝ} (hq : 0 < q) (hint : ∀ m, Integrable (fun ω => ‖X m ω‖ ^ q) P)
    (hmom : ∀ m, ∫ ω, ‖X m ω‖ ^ q ∂P ≤ C * (∫ ω, ‖X m ω‖ ^ 2 ∂P) ^ (q / 2)) :
    Integrable (fun ω => ‖Y ω‖ ^ q) P ∧
      ∫ ω, ‖Y ω‖ ^ q ∂P ≤ C * (∫ ω, ‖Y ω‖ ^ 2 ∂P) ^ (q / 2) := by
  have hcq : Continuous fun z : ℂ => ‖z‖ ^ q :=
    continuous_norm.rpow_const fun _ => Or.inr hq.le
  refine integrable_and_integral_le_of_forall_integral_min_le
    (hcq.comp_aestronglyMeasurable hY) (fun ω => Real.rpow_nonneg (norm_nonneg _) q) fun N => ?_
  have hmeas : ∀ m, AEStronglyMeasurable (fun ω => min (‖X m ω‖ ^ q) (N : ℝ)) P := fun m =>
    ((hcq.min continuous_const).comp_aestronglyMeasurable (hX m))
  have hdom : Tendsto (fun m => ∫ ω, min (‖X m ω‖ ^ q) (N : ℝ) ∂P) atTop
      (𝓝 (∫ ω, min (‖Y ω‖ ^ q) (N : ℝ) ∂P)) := by
    refine tendsto_integral_of_dominated_convergence (fun _ => (N : ℝ)) hmeas
      (integrable_const _) (fun m => Eventually.of_forall fun ω => ?_) ?_
    · rw [Real.norm_of_nonneg (le_min (Real.rpow_nonneg (norm_nonneg _) q) (Nat.cast_nonneg N))]
      exact min_le_right _ _
    · filter_upwards [hlim] with ω hω
      exact ((hcq.min continuous_const).tendsto _).comp hω
  have hrhs : Tendsto (fun m => C * (∫ ω, ‖X m ω‖ ^ 2 ∂P) ^ (q / 2)) atTop
      (𝓝 (C * (∫ ω, ‖Y ω‖ ^ 2 ∂P) ^ (q / 2))) :=
    (h2.rpow_const (Or.inr (by positivity))).const_mul C
  refine le_of_tendsto_of_tendsto' hdom hrhs fun m => ?_
  refine le_trans ?_ (hmom m)
  exact integral_mono_of_nonneg (Eventually.of_forall fun ω =>
    le_min (Real.rpow_nonneg (norm_nonneg _) q) (Nat.cast_nonneg N)) (hint m)
    (Eventually.of_forall fun ω => min_le_left _ _)

end WaveTurbulence
