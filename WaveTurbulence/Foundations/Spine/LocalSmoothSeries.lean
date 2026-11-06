/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import Mathlib.Analysis.Calculus.SmoothSeries
public import Mathlib.Analysis.Normed.Group.FunctionSeries
/-! Local smoothness of series under summable derivative bounds on an open preconnected set. -/
public section
set_option autoImplicit false
namespace WaveTurbulence.LGSpine
open Set Filter
open scoped Topology

variable {ι E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
  {f : ι → E → F} {v : ℕ → ι → ℝ} {U : Set E} {N : ℕ∞}

theorem local_iteratedFDeriv_tsum (hU : IsOpen U) (hUc : IsPreconnected U)
    (hf : ∀ i, ContDiff ℝ N (f i)) (hv : ∀ k : ℕ, (k : ℕ∞) ≤ N → Summable (v k))
    (hbound : ∀ (k : ℕ) (i : ι) (x : E), x ∈ U → (k : ℕ∞) ≤ N → ‖iteratedFDeriv ℝ k (f i) x‖ ≤ v k i)
    {k : ℕ} (hk : (k : ℕ∞) ≤ N) {x : E} (hx : x ∈ U) :
    iteratedFDeriv ℝ k (fun y => ∑' i, f i y) x = ∑' i, iteratedFDeriv ℝ k (f i) x := by
  induction k generalizing x with
  | zero =>
    simp_rw [iteratedFDeriv_zero_eq_comp]
    exact (continuousMultilinearCurryFin0 ℝ E F).symm.toContinuousLinearEquiv.map_tsum
  | succ k ih =>
    have hkn : (k : ℕ∞) < N := lt_of_lt_of_le (WithTop.coe_lt_coe.mpr (Nat.lt_succ_self k)) hk
    have he : (iteratedFDeriv ℝ k fun y => ∑' i, f i y) =ᶠ[𝓝 x]
        (fun y => ∑' i, iteratedFDeriv ℝ k (f i) y) := by
      filter_upwards [hU.mem_nhds hx] with y hy
      exact ih hkn.le hy
    have h0 : Summable (fun i => iteratedFDeriv ℝ k (f i) x) :=
      Summable.of_norm_bounded (hv k hkn.le) (fun i => hbound k i x hx hkn.le)
    have hD := hasFDerivAt_tsum_of_isPreconnected (hv (k + 1) hk) hU hUc
      (fun i y (_ : y ∈ U) =>
        ((hf i).differentiable_iteratedFDeriv (mod_cast hkn)).differentiableAt.hasFDerivAt)
      (fun i y (hy : y ∈ U) => by
        simpa only [iteratedFDeriv_succ_eq_comp_left, Function.comp_apply,
          LinearIsometryEquiv.norm_map] using hbound (k + 1) i y hy hk)
      hx h0 hx
    simp_rw [iteratedFDeriv_succ_eq_comp_left, Function.comp_apply]
    rw [he.fderiv_eq, hD.fderiv]
    exact (continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (k + 1) => E) F).symm.toContinuousLinearEquiv.map_tsum

/-- The localized smooth-series theorem needed for a momentum neighborhood. Derivative
bounds need only hold on U; no global bound in the common momentum is imposed. -/
theorem local_contDiffOn_tsum (hU : IsOpen U) (hUc : IsPreconnected U)
    (hf : ∀ i, ContDiff ℝ N (f i)) (hv : ∀ k : ℕ, (k : ℕ∞) ≤ N → Summable (v k))
    (hbound : ∀ (k : ℕ) (i : ι) (x : E), x ∈ U → (k : ℕ∞) ≤ N →
      ‖iteratedFDeriv ℝ k (f i) x‖ ≤ v k i) :
    ContDiffOn ℝ N (fun x => ∑' i, f i x) U := by
  have huniq : UniqueDiffOn ℝ U := hU.uniqueDiffOn
  have heq (k : ℕ) (hk : (k : ℕ∞) ≤ N) :
      U.EqOn (iteratedFDerivWithin ℝ k (fun x => ∑' i, f i x) U)
        (fun x => ∑' i, iteratedFDeriv ℝ k (f i) x) := by
    intro x hx
    rw [iteratedFDerivWithin_of_isOpen k hU hx]
    exact local_iteratedFDeriv_tsum hU hUc hf hv hbound hk hx
  rw [contDiffOn_iff_continuousOn_differentiableOn huniq]
  constructor
  · intro k hk
    have hc := continuousOn_tsum
      (fun i => ((hf i).continuous_iteratedFDeriv (mod_cast hk)).continuousOn)
      (hv k hk) (fun i x hx => hbound k i x hx hk)
    exact hc.congr (heq k hk)
  · intro k hk x hx
    have hk1 : ((k + 1 : ℕ) : ℕ∞) ≤ N := by
      simpa only [ENat.natCast_add, ENat.natCast_one] using Order.add_one_le_of_lt hk
    have h0 : Summable (fun i => iteratedFDeriv ℝ k (f i) x) :=
      Summable.of_norm_bounded (hv k hk.le) (fun i => hbound k i x hx hk.le)
    have hD := hasFDerivAt_tsum_of_isPreconnected (hv (k + 1) hk1) hU hUc
      (fun i y (_ : y ∈ U) =>
        ((hf i).differentiable_iteratedFDeriv (mod_cast hk)).differentiableAt.hasFDerivAt)
      (fun i y (hy : y ∈ U) => by
        simpa only [iteratedFDeriv_succ_eq_comp_left, Function.comp_apply,
          LinearIsometryEquiv.norm_map] using hbound (k + 1) i y hy hk1)
      hx h0 hx
    have hevent : (iteratedFDerivWithin ℝ k (fun y => ∑' i, f i y) U) =ᶠ[𝓝 x]
        (fun y => ∑' i, iteratedFDeriv ℝ k (f i) y) := by
      filter_upwards [hU.mem_nhds hx] with y hy
      exact heq k hk.le hy
    exact (hD.congr_of_eventuallyEq hevent).differentiableAt.differentiableWithinAt

end WaveTurbulence.LGSpine
