/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Gaussian.FiniteAverage
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Integral.IntegrableOn
public import Mathlib.MeasureTheory.Integral.Lebesgue.Add
public import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
public import Mathlib.Analysis.SpecificLimits.Basic

/-!
# Passing moment inequalities to a limit

* `integrable_and_integral_le_of_forall_integral_min_le`: a nonnegative function whose
  truncations `min f N` have integrals bounded by `B` is integrable with integral at most `B`.
* `moment_le_of_tendsto_favg`: if finite random variables `X M` converge in law to `Ψ` (tested
  against bounded continuous functions), have uniformly bounded second and fourth moments, and
  satisfy `𝔼|X M|^q ≤ C (𝔼|X M|²)^{q/2}`, then so does `Ψ` (with integrability). The fourth
  moment bound gives the uniform integrability of `|X M|²` that makes second moments converge.
-/

public section

open MeasureTheory Filter
open scoped Topology ENNReal

namespace WaveTurbulence.Gaussian

/-- A nonnegative function whose truncations `min f N` have integrals at most `B` is integrable,
with integral at most `B`. -/
theorem integrable_and_integral_le_of_forall_integral_min_le {Y : Type*} [MeasurableSpace Y]
    {Γ : Measure Y} [IsFiniteMeasure Γ] {f : Y → ℝ} (hf : AEStronglyMeasurable f Γ)
    (h0 : ∀ y, 0 ≤ f y) {B : ℝ} (hB : ∀ N : ℕ, ∫ y, min (f y) N ∂Γ ≤ B) :
    Integrable f Γ ∧ ∫ y, f y ∂Γ ≤ B := by
  have hmin_int : ∀ N : ℕ, Integrable (fun y => min (f y) N) Γ := fun N =>
    Integrable.of_bound (hf.inf aestronglyMeasurable_const) N (Eventually.of_forall fun y => by
      rw [Real.norm_of_nonneg (le_min (h0 y) (Nat.cast_nonneg N))]
      exact min_le_right _ _)
  have hB0 : 0 ≤ B := by
    have h := hB 0
    simp only [Nat.cast_zero] at h
    have hz : ∀ y, min (f y) 0 = 0 := fun y => min_eq_right (h0 y)
    simpa [hz] using h
  have hlim : Tendsto (fun N : ℕ => ∫⁻ y, ENNReal.ofReal (min (f y) N) ∂Γ) atTop
      (𝓝 (∫⁻ y, ENNReal.ofReal (f y) ∂Γ)) := by
    refine lintegral_tendsto_of_tendsto_of_monotone
      (fun N => (hmin_int N).aemeasurable.ennreal_ofReal) ?_ ?_
    · exact Eventually.of_forall fun y N M hNM =>
        ENNReal.ofReal_le_ofReal (min_le_min_left _ (Nat.cast_le.2 hNM))
    · refine Eventually.of_forall fun y => ?_
      refine (ENNReal.continuous_ofReal.tendsto _).comp ?_
      refine tendsto_atTop_of_eventually_const (i₀ := ⌈f y⌉₊) fun N hN => ?_
      exact min_eq_left ((Nat.le_ceil _).trans (Nat.cast_le.2 hN))
  have hle : ∫⁻ y, ENNReal.ofReal (f y) ∂Γ ≤ ENNReal.ofReal B := by
    refine le_of_tendsto' hlim fun N => ?_
    rw [← ofReal_integral_eq_lintegral_ofReal (hmin_int N)
      (Eventually.of_forall fun y => le_min (h0 y) (Nat.cast_nonneg N))]
    exact ENNReal.ofReal_le_ofReal (hB N)
  have hint : Integrable f Γ := by
    refine ⟨hf, ?_⟩
    rw [hasFiniteIntegral_iff_ofReal (Eventually.of_forall h0)]
    exact hle.trans_lt ENNReal.ofReal_lt_top
  refine ⟨hint, ?_⟩
  rw [integral_eq_lintegral_of_nonneg_ae (Eventually.of_forall h0) hf]
  exact ENNReal.toReal_le_of_le_ofReal hB0 hle

/-- The elementary uniform-integrability bound `y ≤ min y R + y² / (4R)` for `R > 0`. -/
theorem le_min_add_sq_div {R : ℝ} (y : ℝ) (hR : 0 < R) :
    y ≤ min y R + y ^ 2 / (4 * R) := by
  rcases le_total y R with h | h
  · rw [min_eq_left h]
    have : 0 ≤ y ^ 2 / (4 * R) := by positivity
    linarith
  · rw [min_eq_right h]
    have : y - R ≤ y ^ 2 / (4 * R) := by
      rw [le_div_iff₀ (by positivity)]
      nlinarith [sq_nonneg (y - 2 * R)]
    linarith

/-- **Moment inequalities pass to limits in law.** Let `X M` be complex random variables on finite
uniform spaces that converge in law to `Ψ` under `Γ`, in the sense that cube averages of bounded
continuous functions of `X M` converge to the `Γ`-integral of the same function of `Ψ`. If the
second and fourth moments of `X M` are uniformly bounded and `𝔼|X M|^q ≤ C (𝔼|X M|²)^{q/2}` for
every `M`, then `|Ψ|^q` is integrable and `𝔼|Ψ|^q ≤ C (𝔼|Ψ|²)^{q/2}`. -/
theorem moment_le_of_tendsto_favg {Y : Type*} [MeasurableSpace Y] {Γ : Measure Y}
    [IsProbabilityMeasure Γ] {Ψ : Y → ℂ} (hΨ : AEStronglyMeasurable Ψ Γ)
    {Ω : ℕ → Type*} [∀ M, Fintype (Ω M)] {X : ∀ M, Ω M → ℂ}
    (hconv : ∀ h : ℂ → ℝ, Continuous h → ∀ C : ℝ, (∀ z, |h z| ≤ C) →
      Tendsto (fun M => favg (fun ω => h (X M ω))) atTop (𝓝 (∫ y, h (Ψ y) ∂Γ)))
    {B B4 : ℝ} (hB2 : ∀ M, favg (fun ω => ‖X M ω‖ ^ 2) ≤ B)
    (hB4 : ∀ M, favg (fun ω => (‖X M ω‖ ^ 2) ^ 2) ≤ B4)
    {q C : ℝ} (hq : 0 < q) (hC : 0 ≤ C)
    (hmom : ∀ M, favg (fun ω => ‖X M ω‖ ^ q) ≤ C * favg (fun ω => ‖X M ω‖ ^ 2) ^ (q / 2)) :
    Integrable (fun y => ‖Ψ y‖ ^ q) Γ ∧
      ∫ y, ‖Ψ y‖ ^ q ∂Γ ≤ C * (∫ y, ‖Ψ y‖ ^ 2 ∂Γ) ^ (q / 2) := by
  have hcq : Continuous fun z : ℂ => ‖z‖ ^ q :=
    continuous_norm.rpow_const fun _ => Or.inr hq.le
  have hc2 : Continuous fun z : ℂ => ‖z‖ ^ 2 := continuous_norm.pow 2
  have hmeas2 : AEStronglyMeasurable (fun y => ‖Ψ y‖ ^ 2) Γ := hc2.comp_aestronglyMeasurable hΨ
  have hmeasq : AEStronglyMeasurable (fun y => ‖Ψ y‖ ^ q) Γ := hcq.comp_aestronglyMeasurable hΨ
  -- convergence of truncations of nonnegative continuous functions
  have htrunc : ∀ g : ℂ → ℝ, Continuous g → (∀ z, 0 ≤ g z) → ∀ R : ℝ, 0 ≤ R →
      Tendsto (fun M => favg (fun ω => min (g (X M ω)) R)) atTop
        (𝓝 (∫ y, min (g (Ψ y)) R ∂Γ)) := fun g hg hg0 R hR =>
    hconv (fun z => min (g z) R) (hg.min continuous_const) R fun z => by
      rw [abs_of_nonneg (le_min (hg0 z) hR)]
      exact min_le_right _ _
  -- Step A: the second moment of `Ψ` is finite
  have hint2 : Integrable (fun y => ‖Ψ y‖ ^ 2) Γ :=
    (integrable_and_integral_le_of_forall_integral_min_le hmeas2 (fun y => sq_nonneg _)
      (B := B) fun N => le_of_tendsto' (htrunc (fun z => ‖z‖ ^ 2) hc2 (fun z => sq_nonneg _) N
        (Nat.cast_nonneg N)) fun M => (favg_mono fun ω => min_le_left _ _).trans (hB2 M)).1
  set L := ∫ y, ‖Ψ y‖ ^ 2 ∂Γ with hLdef
  have hL0 : 0 ≤ L := integral_nonneg fun y => sq_nonneg _
  -- Step B: for `K ≥ 0`, `R > 0`, a bound on the truncated `q`-th moment
  have hstep : ∀ K R : ℝ, 0 ≤ K → 0 < R →
      ∫ y, min (‖Ψ y‖ ^ q) K ∂Γ ≤ C * (L + B4 / (4 * R)) ^ (q / 2) := by
    intro K R hK hR
    have h1 := htrunc (fun z => ‖z‖ ^ q) hcq (fun z => Real.rpow_nonneg (norm_nonneg z) q) K hK
    have h2 := htrunc (fun z => ‖z‖ ^ 2) hc2 (fun z => sq_nonneg _) R hR.le
    have hc0 : 0 ≤ B4 / (4 * R) := by
      have := (favg_nonneg (fun ω => sq_nonneg (‖X 0 ω‖ ^ 2))).trans (hB4 0)
      positivity
    have h2' : Tendsto (fun M => C * (favg (fun ω => min (‖X M ω‖ ^ 2) R) + B4 / (4 * R)) ^ (q / 2))
        atTop (𝓝 (C * (∫ y, min (‖Ψ y‖ ^ 2) R ∂Γ + B4 / (4 * R)) ^ (q / 2))) :=
      ((h2.add_const _).rpow_const (Or.inr (by positivity))).const_mul C
    have hmono : ∀ M, favg (fun ω => min (‖X M ω‖ ^ q) K) ≤
        C * (favg (fun ω => min (‖X M ω‖ ^ 2) R) + B4 / (4 * R)) ^ (q / 2) := by
      intro M
      have hui : favg (fun ω => ‖X M ω‖ ^ 2) ≤
          favg (fun ω => min (‖X M ω‖ ^ 2) R) + B4 / (4 * R) := by
        calc favg (fun ω => ‖X M ω‖ ^ 2)
            ≤ favg (fun ω => min (‖X M ω‖ ^ 2) R + (4 * R)⁻¹ * (‖X M ω‖ ^ 2) ^ 2) :=
              favg_mono fun ω => by
                have := le_min_add_sq_div (‖X M ω‖ ^ 2) hR
                rwa [div_eq_inv_mul] at this
          _ = favg (fun ω => min (‖X M ω‖ ^ 2) R) +
                (4 * R)⁻¹ * favg (fun ω => (‖X M ω‖ ^ 2) ^ 2) := by
              rw [favg_add, favg_mul_left]
          _ ≤ favg (fun ω => min (‖X M ω‖ ^ 2) R) + B4 / (4 * R) := by
              rw [div_eq_inv_mul]
              gcongr
              exact hB4 M
      calc favg (fun ω => min (‖X M ω‖ ^ q) K) ≤ favg (fun ω => ‖X M ω‖ ^ q) :=
            favg_mono fun ω => min_le_left _ _
        _ ≤ C * favg (fun ω => ‖X M ω‖ ^ 2) ^ (q / 2) := hmom M
        _ ≤ C * (favg (fun ω => min (‖X M ω‖ ^ 2) R) + B4 / (4 * R)) ^ (q / 2) := by
            gcongr
            exact favg_nonneg fun ω => sq_nonneg _
    have hlim := le_of_tendsto_of_tendsto' h1 h2' hmono
    refine hlim.trans ?_
    have hminL : ∫ y, min (‖Ψ y‖ ^ 2) R ∂Γ ≤ L :=
      integral_mono_of_nonneg (Eventually.of_forall fun y => le_min (sq_nonneg _) hR.le) hint2
        (Eventually.of_forall fun y => min_le_left _ _)
    have hmin0 : 0 ≤ ∫ y, min (‖Ψ y‖ ^ 2) R ∂Γ :=
      integral_nonneg fun y => le_min (sq_nonneg _) hR.le
    gcongr
  -- Step C: let `R → ∞`
  have hK : ∀ N : ℕ, ∫ y, min (‖Ψ y‖ ^ q) N ∂Γ ≤ C * L ^ (q / 2) := by
    intro N
    have hT : Tendsto (fun R : ℕ => C * (L + B4 / 4 / R) ^ (q / 2)) atTop
        (𝓝 (C * (L + 0) ^ (q / 2))) :=
      (((tendsto_const_div_atTop_nhds_zero_nat (B4 / 4)).const_add L).rpow_const
        (Or.inr (by positivity))).const_mul C
    rw [add_zero] at hT
    refine ge_of_tendsto hT (eventually_atTop.2 ⟨1, fun R hR => ?_⟩)
    have hR : (0 : ℝ) < R := by exact_mod_cast hR
    rw [div_div]
    exact hstep N R (Nat.cast_nonneg N) hR
  exact integrable_and_integral_le_of_forall_integral_min_le hmeasq
    (fun y => Real.rpow_nonneg (norm_nonneg _) q) hK

end WaveTurbulence.Gaussian
