/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Incoh.TreeRootCellSupport
public import Mathlib.Analysis.Calculus.ContDiff.Operations

/-! # Actual finite local models for root-cutoff spectral amplitude sums -/

public section
noncomputable section
open MeasureTheory Filter Set Metric
open scoped Topology ContDiff

namespace WaveTurbulence.Incoh

/-- A fixed finite set of root cells controlling the whole unit neighborhood of a momentum. -/
@[expose] def rootLocalCover {d : ℕ} (p : Mom d) : Finset (Fin d → ℤ) :=
  ApproxNT.intBox p (treeRootCutoffRadius d + 1)

/-- Actual locally finite root-amplitude sum. -/
@[expose] def rootAmplitudeSum {d : ℕ} {U : Type*}
    (B : (Fin d → ℤ) → Mom d → U → ℂ) (k : Mom d) (u : U) : ℂ := ∑' q, B q k u

/-- The actual finite model valid on the unit neighborhood of its base point. -/
@[expose] def rootAmplitudeModel {d : ℕ} {U : Type*}
    (B : (Fin d → ℤ) → Mom d → U → ℂ) (p k : Mom d) (u : U) : ℂ :=
  ∑ q ∈ rootLocalCover p, B q k u

/-- Its actual finite derivative envelope; no summability over all root momenta is imposed. -/
@[expose] def rootAmplitudeModelEnvelope {d : ℕ} {U : Type*}
    (v : (Fin d → ℤ) → U → ℝ) (p : Mom d) (_j : ℕ) (u : U) : ℝ :=
  ∑ q ∈ rootLocalCover p, v q u

/-- One actual finite root model agrees simultaneously for all spectral variables nearby. -/
theorem rootAmplitudeSum_eventuallyEq_model {d : ℕ} {U : Type*}
    (B : (Fin d → ℤ) → Mom d → U → ℂ)
    (hz : ∀ q k u, treeRootCutoff q k = 0 → B q k u = 0) (p : Mom d) :
    ∀ᶠ k in 𝓝 p, ∀ u, rootAmplitudeSum B k u = rootAmplitudeModel B p k u := by
  filter_upwards [ball_mem_nhds p (by norm_num : (0 : ℝ) < 1)] with k hk
  intro u
  exact tsum_eq_sum (fun q hq => hz q k u (treeRootCutoff_eq_zero_on_ball_of_notMem p q hq hk))

/-- Actual finite models retain the finite source momentum smoothness. -/
theorem contDiff_rootAmplitudeModel {d N : ℕ} {U : Type*}
    (B : (Fin d → ℤ) → Mom d → U → ℂ)
    (hB : ∀ q u, ContDiff ℝ N (fun k => B q k u)) (p : Mom d) (u : U) :
    ContDiff ℝ N (fun k => rootAmplitudeModel B p k u) :=
  ContDiff.sum (fun q _ => hB q u)

/-- Actual derivatives of the finite root model are the corresponding finite sums. -/
theorem iteratedFDeriv_rootAmplitudeModel {d N j : ℕ} {U : Type*}
    (B : (Fin d → ℤ) → Mom d → U → ℂ)
    (hB : ∀ q u, ContDiff ℝ N (fun k => B q k u)) (hj : j ≤ N) (p k : Mom d) (u : U) :
    iteratedFDeriv ℝ j (fun k => rootAmplitudeModel B p k u) k =
      ∑ q ∈ rootLocalCover p, iteratedFDeriv ℝ j (fun k => B q k u) k := by
  exact iteratedFDeriv_fun_sum_apply
    (fun q _ => ((hB q u).of_le (by exact_mod_cast hj)).contDiffAt)

/-- Conditional actual model derivative bound by the finite sum of individual root envelopes. -/
theorem norm_iteratedFDeriv_rootAmplitudeModel_le {d N j : ℕ} {U : Type*}
    (B : (Fin d → ℤ) → Mom d → U → ℂ) (v : (Fin d → ℤ) → U → ℝ)
    (hB : ∀ q u, ContDiff ℝ N (fun k => B q k u))
    (hb : ∀ q j, j ≤ N → ∀ k u, ‖iteratedFDeriv ℝ j (fun k => B q k u) k‖ ≤ v q u)
    (hj : j ≤ N) (p k : Mom d) (u : U) :
    ‖iteratedFDeriv ℝ j (fun k => rootAmplitudeModel B p k u) k‖ ≤
      rootAmplitudeModelEnvelope v p j u := by
  rw [iteratedFDeriv_rootAmplitudeModel B hB hj]
  exact (norm_sum_le _ _).trans (Finset.sum_le_sum (fun q _ => hb q j hj k u))

/-- Actual derivatives of the finite model are strongly measurable on the spectral space. -/
theorem stronglyMeasurable_rootAmplitudeModel_derivative {d N j : ℕ} {U : Type*} [MeasurableSpace U]
    (B : (Fin d → ℤ) → Mom d → U → ℂ)
    (hB : ∀ q u, ContDiff ℝ N (fun k => B q k u))
    (hm : ∀ q j, j ≤ N → ∀ k, StronglyMeasurable
      (fun u => iteratedFDeriv ℝ j (fun k => B q k u) k))
    (hj : j ≤ N) (p k : Mom d) :
    StronglyMeasurable (fun u => iteratedFDeriv ℝ j (fun k => rootAmplitudeModel B p k u) k) := by
  simp_rw [iteratedFDeriv_rootAmplitudeModel B hB hj]
  exact Finset.stronglyMeasurable_fun_sum (rootLocalCover p) (fun q _ => hm q j hj k)

/-- Every finite actual model envelope is integrable whenever each individual envelope is. -/
theorem integrable_rootAmplitudeModelEnvelope {d : ℕ} {U : Type*} [MeasurableSpace U]
    (μ : Measure U) (v : (Fin d → ℤ) → U → ℝ) (hv : ∀ q, Integrable (v q) μ) (p : Mom d) (j : ℕ) :
    Integrable (rootAmplitudeModelEnvelope v p j) μ :=
  integrable_finsetSum (rootLocalCover p) (fun q _ => hv q)

/-- The actual root sum's finite derivative agrees with the corresponding local model derivative. -/
theorem iteratedFDeriv_rootAmplitudeSum_eq_model {d : ℕ} {U : Type*}
    (B : (Fin d → ℤ) → Mom d → U → ℂ)
    (hz : ∀ q k u, treeRootCutoff q k = 0 → B q k u = 0)
    (j : ℕ) (p : Mom d) (u : U) :
    iteratedFDeriv ℝ j (fun k => rootAmplitudeSum B k u) p =
      iteratedFDeriv ℝ j (fun k => rootAmplitudeModel B p k u) p := by
  have he : (fun k => rootAmplitudeSum B k u) =ᶠ[𝓝 p] (fun k => rootAmplitudeModel B p k u) :=
    (rootAmplitudeSum_eventuallyEq_model B hz p).mono (fun k hk => hk u)
  exact (he.iteratedFDeriv ℝ j).self_of_nhds

end WaveTurbulence.Incoh
