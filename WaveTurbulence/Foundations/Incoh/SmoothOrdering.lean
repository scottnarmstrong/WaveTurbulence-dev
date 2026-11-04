/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Incoh.SmoothIntervalLimit
public import WaveTurbulence.Foundations.Incoh.CoordinateFactorDerivative

/-!
# Translation-invariant smoothing of the causal clock ordering

The ordering weight depends only on adjacent clock differences. Its
common-clock derivative is exactly zero for every smoothing width.
-/

public section
noncomputable section
open MeasureTheory Set Filter
open scoped ContDiff Topology

namespace WaveTurbulence.Incoh

/-- Smooth approximation to strict descendant ordering of `n+1` clocks. -/
@[expose] def smoothOrderingWeight (n : ℕ) (ε : ℝ) (v : Fin (n + 1) → ℝ) : ℂ :=
  ∏ i : Fin n, (Real.smoothTransition ((v i.castSucc - v i.succ) / ε) : ℂ)

/-- The literal strict ordering indicator, written as a product over adjacent clocks. -/
@[expose] def strictOrderingWeight (n : ℕ) (v : Fin (n + 1) → ℝ) : ℂ :=
  ∏ i : Fin n, (((Ioi (0 : ℝ)).indicator (fun _ => (1 : ℝ)) (v i.castSucc - v i.succ) : ℝ) : ℂ)

@[fun_prop] theorem contDiff_smoothOrderingWeight (n : ℕ) (ε : ℝ) :
    ContDiff ℝ ∞ (smoothOrderingWeight n ε) := by
  apply contDiff_prod
  intro i _
  exact Complex.ofRealCLM.contDiff.comp (Real.smoothTransition.contDiff.comp (by fun_prop))

theorem norm_smoothOrderingWeight_le (n : ℕ) (ε : ℝ) (v : Fin (n + 1) → ℝ) :
    ‖smoothOrderingWeight n ε v‖ ≤ 1 := by
  rw [smoothOrderingWeight, norm_prod]
  apply (Finset.prod_le_prod₀ (fun _ _ => norm_nonneg _) (fun i _ => ?_)).trans_eq
    (Finset.prod_const_one)
  rw [Complex.norm_real, Real.norm_of_nonneg (Real.smoothTransition.nonneg _)]
  exact Real.smoothTransition.le_one _

theorem smoothOrderingWeight_translate (n : ℕ) (ε : ℝ) (v : Fin (n + 1) → ℝ) (c : ℝ) :
    smoothOrderingWeight n ε (fun j => v j + c) = smoothOrderingWeight n ε v := by
  unfold smoothOrderingWeight
  apply Finset.prod_congr rfl
  intro i _
  rw [show (v i.castSucc + c) - (v i.succ + c) = v i.castSucc - v i.succ by ring]

/-- A smooth transition converges pointwise to the positive-half-line indicator. -/
theorem tendsto_smoothTransition_div {ε : ℕ → ℝ} (hε : ∀ n, 0 < ε n)
    (hlim : Tendsto ε atTop (𝓝 0)) (x : ℝ) :
    Tendsto (fun n => Real.smoothTransition (x / ε n)) atTop
      (𝓝 ((Ioi (0 : ℝ)).indicator (fun _ => (1 : ℝ)) x)) := by
  by_cases hx : x ≤ 0
  · have he (n : ℕ) : Real.smoothTransition (x / ε n) = 0 :=
      Real.smoothTransition.zero_of_nonpos (div_nonpos_of_nonpos_of_nonneg hx (hε n).le)
    simp only [he, indicator_of_notMem (s := Ioi (0 : ℝ)) (a := x) (not_lt_of_ge hx)]
    exact tendsto_const_nhds
  · have hxp : 0 < x := lt_of_not_ge hx
    have he : (fun n => Real.smoothTransition (x / ε n)) =ᶠ[atTop] fun _ => (1 : ℝ) := by
      filter_upwards [hlim.eventually_lt_const hxp] with n hn
      exact Real.smoothTransition.one_of_one_le ((le_div_iff₀ (hε n)).mpr (by linarith))
    rw [indicator_of_mem (s := Ioi (0 : ℝ)) (a := x) hxp]
    exact tendsto_const_nhds.congr' he.symm

/-- Exact pointwise convergence includes coincident clocks, where the strict indicator is zero. -/
theorem tendsto_smoothOrderingWeight (n : ℕ) {ε : ℕ → ℝ} (hε : ∀ j, 0 < ε j)
    (hlim : Tendsto ε atTop (𝓝 0)) (v : Fin (n + 1) → ℝ) :
    Tendsto (fun j => smoothOrderingWeight n (ε j) v) atTop (𝓝 (strictOrderingWeight n v)) := by
  apply tendsto_finsetProd
  intro i _
  exact (Complex.continuous_ofReal.tendsto _).comp
    (tendsto_smoothTransition_div hε hlim (v i.castSucc - v i.succ))

end WaveTurbulence.Incoh
