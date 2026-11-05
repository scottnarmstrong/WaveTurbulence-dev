/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.XChain.MeasurableCoefficient
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Order
/-! A measurable coefficient functional of the initial array, agreeing with every rapid-data
classed solution. Componentwise limsup supplies a total extension outside the solution set. -/
@[expose] public section
namespace WaveTurbulence.Induct
open MeasureTheory Set Filter Topology
open NLS
open scoped ENNReal

noncomputable def truncatedCoeff {d : ℕ} (L γ δ T t : ℝ) (n : Fin d → ℤ) (R : ℕ)
    (c : (Fin d → ℤ) → ℂ) : ℂ :=
  {c : (Fin d → ℤ) → ℂ | IsRapidDecay c}.indicator
    (fun c => lp.evalCLM ℝ (fun _ : Fin d → ℤ => ℂ) 1 n
      (truncFlow L γ δ R T (L1.ofFun (weightUp c)) t) / (flowWeight n : ℂ)) c

noncomputable def canonicalCoeff {d : ℕ} (L γ δ T t : ℝ) (n : Fin d → ℤ)
    (c : (Fin d → ℤ) → ℂ) : ℂ :=
  ((limsup (fun R : ℕ => (truncatedCoeff L γ δ T t n R c).re) atTop : ℝ) : ℂ) +
    ((limsup (fun R : ℕ => (truncatedCoeff L γ δ T t n R c).im) atTop : ℝ) : ℂ) * Complex.I

theorem measurable_truncatedCoeff {d : ℕ} (L γ δ T : ℝ) {t : ℝ} (ht : t ∈ Icc 0 T)
    (n : Fin d → ℤ) (R : ℕ) : Measurable (truncatedCoeff L γ δ T t n R) :=
  measurable_indicator_complex_comp_ofFun
    (((lp.evalCLM ℝ (fun _ : Fin d → ℤ => ℂ) 1 n).continuous.comp
      (continuous_truncFlow_data (Nat.cast_nonneg R) ht)).div_const _)

theorem measurable_canonicalCoeff {d : ℕ} (L γ δ T : ℝ) {t : ℝ} (ht : t ∈ Icc 0 T)
    (n : Fin d → ℤ) : Measurable (canonicalCoeff L γ δ T t n) := by
  have hre := Measurable.limsup (fun R => Complex.continuous_re.measurable.comp
    (measurable_truncatedCoeff L γ δ T ht n R))
  have him := Measurable.limsup (fun R => Complex.continuous_im.measurable.comp
    (measurable_truncatedCoeff L γ δ T ht n R))
  exact (Complex.continuous_ofReal.measurable.comp hre).add
    ((Complex.continuous_ofReal.measurable.comp him).mul_const _)

/-- The canonical functional recovers any classed solution with rapidly decreasing initial data. -/
theorem canonicalCoeff_eq {d : ℕ} {L γ δ T : ℝ} (hL : 0 < L)
    {c : (Fin d → ℤ) → ℂ} (hc : IsRapidDecay c) {a : ℝ → (Fin d → ℤ) → ℂ}
    (ha : IsASolution L γ δ T c a) {t : ℝ} (ht : t ∈ Icc 0 T) (n : Fin d → ℤ) :
    canonicalCoeff L γ δ T t n c = a t n := by
  have hsol := SysAPI.IsASolution.toNLS ha
  obtain ⟨Y, hY⟩ := hsol.exists_norm_ofFun_le hL hc
  have hev : ∀ᶠ R : ℕ in atTop, truncatedCoeff L γ δ T t n R c = a t n := by
    filter_upwards [eventually_ge_atTop ⌈Y⌉₊] with R hR
    have hRY : ∀ s ∈ Icc 0 T, ‖(L1.ofFun (weightUp (a s)) : L1 d)‖ ≤ (R : ℝ) :=
      fun s hs => (hY s hs).trans ((Nat.le_ceil Y).trans (Nat.cast_le.mpr hR))
    unfold truncatedCoeff
    rw [indicator_of_mem hc, hsol.truncFlow_eq hL hc hRY t ht]
    change (L1.ofFun (weightUp (a t)) : L1 d) n / (flowWeight n : ℂ) = a t n
    rw [L1.ofFun_apply (hsol.summable_norm_weightUp hL hc ht), weightUp,
      mul_div_cancel_left₀ _ (Complex.ofReal_ne_zero.mpr (flowWeight_pos n).ne')]
  unfold canonicalCoeff
  rw [limsup_congr (hev.mono fun R hR => congrArg Complex.re hR),
    limsup_congr (hev.mono fun R hR => congrArg Complex.im hR), limsup_const, limsup_const]
  exact Complex.re_add_im _

end WaveTurbulence.Induct
