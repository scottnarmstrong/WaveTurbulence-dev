/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Incoh.SmoothInterval
public import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
# Exact pointwise limit of the interval windows

The half-open convention gives convergence even at the interval endpoints.
The convention does not change any of the Lebesgue time integrals.
-/

public section
noncomputable section
open Set MeasureTheory Filter
open scoped Topology

namespace WaveTurbulence.Incoh

/-- At each fixed clock the window is eventually the literal half-open indicator. -/
theorem smoothInterval_eventually_eq_indicator {ι : Type*} {l : Filter ι}
    {ε : ι → ℝ} (hε : ∀ i, 0 < ε i) (hlim : Tendsto ε l (𝓝 0))
    {a b : ℝ} (hab : a ≤ b) (t : ℝ) :
    (fun i => smoothInterval (ε i) a b t) =ᶠ[l] fun _ => (Ioc a b).indicator (fun _ => (1 : ℝ)) t := by
  by_cases ha : t ≤ a
  · apply Filter.Eventually.of_forall
    intro i
    change smoothInterval (ε i) a b t = (Ioc a b).indicator (fun _ => (1 : ℝ)) t
    rw [smoothInterval_eq_zero_of_le (hε i) hab ha, indicator_of_notMem]
    exact fun ht => (not_lt_of_ge ha) ht.1
  · have hat : a < t := lt_of_not_ge ha
    by_cases hb : t ≤ b
    · filter_upwards [hlim.eventually_lt_const (sub_pos.mpr hat)] with i hi
      change smoothInterval (ε i) a b t = (Ioc a b).indicator (fun _ => (1 : ℝ)) t
      rw [smoothInterval_eq_one (hε i) (by linarith) hb, indicator_of_mem (s := Ioc a b) (a := t) ⟨hat, hb⟩]
    · have hbt : b < t := lt_of_not_ge hb
      filter_upwards [hlim.eventually_lt_const (sub_pos.mpr hbt)] with i hi
      change smoothInterval (ε i) a b t = (Ioc a b).indicator (fun _ => (1 : ℝ)) t
      rw [smoothInterval_eq_zero_of_ge (hε i) hab (by linarith), indicator_of_notMem]
      exact fun ht => hb ht.2

/-- Positive smoothing widths tending to zero recover the interval indicator pointwise. -/
theorem tendsto_smoothInterval {ι : Type*} {l : Filter ι} {ε : ι → ℝ}
    (hε : ∀ i, 0 < ε i) (hlim : Tendsto ε l (𝓝 0))
    {a b : ℝ} (hab : a ≤ b) (t : ℝ) :
    Tendsto (fun i => smoothInterval (ε i) a b t) l
      (𝓝 ((Ioc a b).indicator (fun _ => (1 : ℝ)) t)) :=
  tendsto_const_nhds.congr' (smoothInterval_eventually_eq_indicator hε hlim hab t).symm

end WaveTurbulence.Incoh
