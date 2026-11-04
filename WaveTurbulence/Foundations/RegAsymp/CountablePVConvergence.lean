/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.RegAsymp.CountablePVCellMixture

/-! # Actual cutoff convergence for countable Fourier-cell mixtures -/

public section
noncomputable section
namespace WaveTurbulence.RegAsymp
open MeasureTheory ApproxNT Filter Topology

variable {d : ℕ} {U : Type*} [MeasurableSpace U] (ν : Measure U) [SFinite ν]

/-- Absolute coefficient mass gives actual cutoff convergence, not only
a value assigned by limUnder. This supports scalar extraction in recursive
singular integrations without assuming unrestricted PV linearity. -/
theorem tendsto_pvTrunc_countableCellMixture {I : Type*} [Countable I] (hd : 3 ≤ d)
    (p q : I → Mom d) (ξ η : I → U → Mom d)
    (hξ : ∀ i, Measurable (ξ i)) (hη : ∀ i, Measurable (η i))
    (h : I → U → ℂ) (hsm : ∀ i, StronglyMeasurable (h i))
    (hi : ∀ i, Integrable (h i) ν) (hsum : Summable (fun i => ∫ u, ‖h i u‖ ∂ν)) :
    Tendsto (fun s : ℝ => pvTrunc s (fun x y => ∑' i,
      cellMixture ν (p i) (q i) (ξ i) (η i) (h i) x y)) atTop
      (𝓝 (∑' i, ∫ u, h i u*pvOp (cellFn (p i) (q i) (ξ i u) (η i u)) ∂ν)) := by
  obtain ⟨M,hM,hcell⟩ := exists_pvCell hd
  have hb (i : I) {s : ℝ} (hs : 1 < s) :
      ‖∫ u, h i u*pvTrunc s (cellFn (p i) (q i) (ξ i u) (η i u)) ∂ν‖ ≤
        M*(∫ u, ‖h i u‖ ∂ν) := by
    apply (norm_integral_le_integral_norm _).trans
    have hiA := (pv_term (p i) (q i) (hξ i) (hη i) (hi i) (zero_lt_one.trans hs)).2.1.norm
    calc
      _ ≤ ∫ u, M*‖h i u‖ ∂ν := by
        apply integral_mono hiA ((hi i).norm.const_mul M)
        intro u
        change ‖h i u*pvTrunc s (cellFn (p i) (q i) (ξ i u) (η i u))‖ ≤ M*‖h i u‖
        rw [norm_mul,mul_comm M]
        exact mul_le_mul_of_nonneg_left ((hcell _ _ _ _).1 s hs) (norm_nonneg _)
      _ = _ := integral_const_mul _ _
  have ht (i : I) : Tendsto (fun s : ℝ =>
      ∫ u, h i u*pvTrunc s (cellFn (p i) (q i) (ξ i u) (η i u)) ∂ν) atTop
      (𝓝 (∫ u, h i u*pvOp (cellFn (p i) (q i) (ξ i u) (η i u)) ∂ν)) := by
    refine (tendsto_pv_term hd (p i) (q i) (hξ i) (hη i) (hi i)).congr' ?_
    filter_upwards [eventually_gt_atTop (0:ℝ)] with s hs
    exact (pv_term (p i) (q i) (hξ i) (hη i) (hi i) hs).2.2
  have hlim : Tendsto (fun s : ℝ => ∑' i,
      ∫ u, h i u*pvTrunc s (cellFn (p i) (q i) (ξ i u) (η i u)) ∂ν) atTop
      (𝓝 (∑' i, ∫ u, h i u*pvOp (cellFn (p i) (q i) (ξ i u) (η i u)) ∂ν)) := by
    apply tendsto_tsum_of_dominated_convergence (hsum.mul_left M) ht
    filter_upwards [eventually_gt_atTop (1:ℝ)] with s hs
    exact fun i => hb i hs
  have hfull : Tendsto (fun s : ℝ => pvTrunc s
      (fun x y => ∑' i, cellMixture ν (p i) (q i) (ξ i) (η i) (h i) x y)) atTop
      (𝓝 (∑' i, ∫ u, h i u*pvOp (cellFn (p i) (q i) (ξ i u) (η i u)) ∂ν)) := by
    refine hlim.congr' ?_
    filter_upwards [eventually_gt_atTop (0:ℝ)] with s hs
    exact (pvTrunc_tsum_cellMixture ν p q ξ η hξ hη h hsm hi hsum hs).symm
  exact hfull

/-- Scalar extraction at every finite cutoff is unconditional. -/
theorem pvTrunc_const_mul (s : ℝ) (c : ℂ) (F : Mom d → Mom d → ℂ) :
    pvTrunc s (fun x y => c*F x y) = c*pvTrunc s F := by
  rw [pvTrunc_eq_integral,pvTrunc_eq_integral,← integral_const_mul]
  apply integral_congr_ae
  apply ae_of_all
  intro x
  dsimp only
  rw [← integral_const_mul]
  apply integral_congr_ae
  apply ae_of_all
  intro y
  dsimp only
  ring

/-- Conditional analytic transport: scalar extraction is lawful when the
original cutoffs converge. Source applications derive this convergence
from the countable-cell mass rather than assuming a source conclusion. -/
theorem pvOp_const_mul_of_tendsto (c : ℂ) {F : Mom d → Mom d → ℂ} {v : ℂ}
    (ht : Tendsto (fun s : ℝ => pvTrunc s F) atTop (𝓝 v)) :
    pvOp (fun x y => c*F x y) = c*pvOp F := by
  have ht' : Tendsto (fun s : ℝ => pvTrunc s (fun x y => c*F x y)) atTop (𝓝 (c*v)) :=
    (ht.const_mul c).congr (fun s => (pvTrunc_const_mul s c F).symm)
  rw [show pvOp F = v from ht.limUnder_eq]
  exact ht'.limUnder_eq

/-- Scalar extraction for the actual countable Fourier-cell class,
with convergence supplied solely by the original absolute coefficient mass. -/
theorem pvOp_const_mul_countableCellMixture {I : Type*} [Countable I] (hd : 3 ≤ d)
    (p q : I → Mom d) (ξ η : I → U → Mom d)
    (hξ : ∀ i, Measurable (ξ i)) (hη : ∀ i, Measurable (η i))
    (h : I → U → ℂ) (hsm : ∀ i, StronglyMeasurable (h i))
    (hi : ∀ i, Integrable (h i) ν) (hsum : Summable (fun i => ∫ u, ‖h i u‖ ∂ν)) (c : ℂ) :
    pvOp (fun x y => c*(∑' i, cellMixture ν (p i) (q i) (ξ i) (η i) (h i) x y)) =
      c*pvOp (fun x y => ∑' i, cellMixture ν (p i) (q i) (ξ i) (η i) (h i) x y) :=
  pvOp_const_mul_of_tendsto c
    (tendsto_pvTrunc_countableCellMixture ν hd p q ξ η hξ hη h hsm hi hsum)

end WaveTurbulence.RegAsymp
